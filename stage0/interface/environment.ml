(* The interfaces of definitions, as queries.

   [lowered] lowers a definition's outward-facing part and keeps what
   lowering reported. The other queries project one interface out of it by
   path, so a definition's diagnostics changing never re-checks a
   definition that reads its interface. *)

open Syntax
module T = Types
module Names = Resolve.Names

type interface =
  | Function_interface of T.signature
  | Type_interface of T.type_interface
  | Trait_interface of T.trait_interface
  | Impl_interface of T.impl_interface
  | Constant_interface of T.constant_interface
  | Test_interface of T.capability list
  | Theorem_interface of T.signature
  | Law_proof_interface of { trait : T.trait_reference; law : string; for_type : T.ty }
      (** What a law's proof is of: the law of a trait, as a type's [impl] keeps it. *)
  | Error_interface of Diagnostic.reported
      (** A definition whose header did not parse: everything is accepted of it. *)

type lowered = {
  interface : interface;
  diagnostics : Diagnostic.t list;
  named : (span * T.ty) list;  (** Each named type written, for checking its bounds. *)
  bounds : (T.parameter * T.trait_reference list) list;  (** The generic parameters' bounds. *)
}

(* The type a head names, and the generic parameters it declares, which
   are in scope after it whether or not the type is known. *)
let head_type context owner (head : type_head) =
  let generics = Lower.generics context owner head.generics in
  match Lower.target context head.path.last with
  | Some (Definition (Type, type_path)) ->
      (match Query.demand context.database Summary.generics_of type_path with
      | Some expected when List.length expected <> List.length generics ->
          Lower.report context Arity head.span
            (Printf.sprintf "`%s` takes %d generic %s, and this head names %d."
               (Names.spell_path head.path) (List.length expected)
               (if List.length expected = 1 then "parameter" else "parameters")
               (List.length generics))
      | _ -> ());
      let arguments =
        List.map
          (fun (generic : T.generic) ->
            match generic.kind with
            | Value_generic -> T.Value (T.Value_parameter generic.generic)
            | Type_generic _ -> T.Type (T.Parameter generic.generic)
            | Capability_generic -> T.Capabilities [ T.Capability_parameter generic.generic ])
          generics
      in
      let type_ =
        match Intrinsic.builtin_of_path type_path with
        | Some Never -> T.Never
        | Some Integer -> T.Integer
        | _ -> T.Named { path = type_path; arguments }
      in
      (generics, type_)
  | Some (Definition (((Trait | Capability) as kind), _)) ->
      ( generics,
        Lower.error context Not_a_type head.span
          (Printf.sprintf "`%s` is %s, not a type, so it has no methods, constants, or `impl`s."
             (Names.spell_path head.path)
             (Names.kind_name (Names.kind_of_named kind))) )
  | Some (Unknown report) -> (generics, T.Error report)
  | _ -> Lower.bug "the type head `%s` is not resolved" (Names.spell_path head.path)

let trait_self_parameter trait : T.parameter = { owner = trait; name = "Self" }

let generic_arguments generics =
  List.map
    (fun (generic : T.generic) ->
      match generic.kind with
      | Value_generic -> T.Value (T.Value_parameter generic.generic)
      | Type_generic _ -> T.Type (T.Parameter generic.generic)
      | Capability_generic -> T.Capabilities [ T.Capability_parameter generic.generic ])
    generics

let fields context (written : field list) =
  List.filter_map
    (fun (field : field) ->
      match field.kind with
      | Field_declaration { name; type_; default } ->
          Some
            {
              T.field_name = name.text;
              field_type = Lower.type_ context type_;
              field_has_default = Option.is_some default;
            }
      | Field_error -> None)
    written

(* What a trait, an [impl], or a capability says for itself, apart from the
   methods written inside it. *)
type container =
  | Trait_parts of {
      trait_generics : T.generic list;
      requires : T.trait_reference list;
      associated_types : T.associated_type list;
    }
  | Capability_parts
  | Impl_parts of {
      impl_generics : T.generic list;
      implements : T.trait_reference;
      for_type : T.ty;
      impl_uses : T.capability list;
    }
  | Broken of Diagnostic.reported  (** An [impl] of what is no trait. *)

(* A trait's, an [impl]'s, or a capability's own parts, and the context
   what is written inside it is lowered in: what [Self] and its associated
   types mean there, and its generic parameters' bounds. *)
let lower_container (context : Lower.context) (path : Path.t) (definition : definition) =
  match definition.kind with
  | Trait { generics; requires; members; _ } ->
      let trait_generics = Lower.generics context path generics in
      let self_parameter = trait_self_parameter path in
      let self_trait : T.trait_reference =
        { trait = path; trait_arguments = generic_arguments trait_generics; associated = [] }
      in
      Hashtbl.replace context.bounds self_parameter [ self_trait ];
      let context =
        { context with self_type = Some (T.Parameter self_parameter); self_trait = Some self_trait }
      in
      let requires = Lower.trait_bounds context requires in
      let associated_types =
        List.filter_map
          (fun (line : trait_member line) ->
            match line.kind with
            | Associated_type (name, bounds) ->
                Some
                  {
                    T.associated_name = name.text;
                    associated_bounds = Lower.trait_bounds context bounds;
                  }
            | Law _ | Trait_member_error -> None)
          members
      in
      (Trait_parts { trait_generics; requires; associated_types }, context)
  | Impl { trait_; type_ = head; uses; members } -> (
      let impl_generics, for_type = head_type context path head in
      match Lower.trait_reference ~capability:true context trait_ with
      | Error report -> (Broken report, context)
      | Ok implements ->
          let associated =
            List.sort compare
              (List.filter_map
                 (fun (line : impl_member line) ->
                   match line.kind with
                   | Associated_definition (name, written) ->
                       Some
                         (name.text, Lower.type_ { context with self_type = Some for_type } written)
                   | Impl_member_error -> None)
                 members)
          in
          let implements = { implements with associated } in
          let context =
            {
              context with
              self_type = Some for_type;
              self_trait = Some implements;
              self_associated = associated;
            }
          in
          ( Impl_parts
              { impl_generics; implements; for_type; impl_uses = Lower.capabilities context uses },
            context ))
  | _ -> (Capability_parts, context)

(* What a trait, an [impl], or a capability gives each method written
   inside it, or the report of why it gives nothing, when its own header
   did not parse or it is an [impl] of what is no trait. *)
type header = {
  self_type : T.ty option;
  self_trait : T.trait_reference option;
  self_associated : (string * T.ty) list;
  header_bounds : (T.parameter * T.trait_reference list) list;
  header_generics : T.generic list;
      (** An [impl]'s own generic parameters, which come before those of a method written inside it.
          A trait's are given where its method is called, with [Self]. *)
  header_uses : T.capability list;  (** An [impl]'s [uses], which are each of its methods' too. *)
}

let bounds_of (context : Lower.context) =
  List.sort compare
    (Hashtbl.fold (fun parameter bounds found -> (parameter, bounds) :: found) context.bounds [])

let header =
  Query.query ~name:"header" ~phase:Interfaces ~show:Names.show_key (fun database key ->
      match
        (Query.demand database Names.definition key, Query.demand database Resolve.resolved key)
      with
      | Some definition, Some resolved -> (
          match Resolve.Parts.reported definition Header with
          | Some report -> Some (Error report)
          | None -> (
              match lower_container (Lower.create database resolved) key.path definition with
              | Broken report, _ -> Some (Error report)
              | parts, context ->
                  let header_generics, header_uses =
                    match parts with
                    | Impl_parts { impl_generics; impl_uses; _ } -> (impl_generics, impl_uses)
                    | _ -> ([], [])
                  in
                  Some
                    (Ok
                       {
                         self_type = context.self_type;
                         self_trait = context.self_trait;
                         self_associated = context.self_associated;
                         header_bounds = bounds_of context;
                         header_generics;
                         header_uses;
                       })))
      | _ -> None)

(* [interface_of] gives the interface of a method written inside the
   definition, by its key. *)
let lower_definition database ~interface_of (key : Names.key) (definition : definition)
    (resolved : Resolve.resolved) =
  let context = Lower.create database resolved in
  let path = key.path in
  (* The methods written inside a trait, an [impl], or a capability, each
     with its name, its receiver, its interface, and whether it has a
     body. *)
  let methods () =
    List.filter_map
      (fun (member : Names.key) ->
        match (member.path, interface_of member) with
        | Method { name; receiver; _ }, Some interface ->
            let provided =
              match Query.demand database Names.definition member with
              | Some { kind = Function _; _ } -> true
              | _ -> false
            in
            Some (name, receiver, interface, provided)
        | _ -> None)
      (Query.demand database Names.contained key)
  in
  let trait_methods ~is_capability =
    List.filter_map
      (fun (name, receiver, interface, provided) ->
        match interface with
        | Function_interface signature ->
            Some
              {
                T.method_name = name;
                method_receiver = (if is_capability then Path.Static else receiver);
                method_signature = signature;
                provided;
              }
        | _ -> None)
      (methods ())
  in
  let broken_methods () =
    List.filter_map
      (fun (name, _, interface, _) ->
        match interface with Error_interface report -> Some (name, report) | _ -> None)
      (methods ())
  in
  (* Each kind of definition gives its interface, and the context its bodies
     are checked in: what [Self] and its associated types mean there. *)
  let interface, context =
    match
      ( Resolve.Parts.reported definition Header,
        Option.bind (Query.demand database Names.container key) (Query.demand database header) )
    with
    | Some report, _ | None, Some (Error report) -> (Error_interface report, context)
    | None, Some (Ok within) -> (
        (* A method written inside a trait, an [impl], or a capability:
           [Self], its associated types, and the generic parameters around
           it are that one's. *)
        List.iter
          (fun (parameter, bounds) -> Hashtbl.replace context.bounds parameter bounds)
          within.header_bounds;
        let context =
          {
            context with
            self_type = within.self_type;
            self_trait = within.self_trait;
            self_associated = within.self_associated;
          }
        in
        match definition.kind with
        | Function { signature; _ } | Method_declaration signature ->
            let lowered =
              T.inside ~generics:within.header_generics ~uses:within.header_uses
                (Lower.signature context ~owner:path ~head:[] ~self_type:within.self_type signature)
            in
            (* An [impl]'s method ends when its trait's does, since it keeps the
               trait's [time] clause. *)
            let terminates =
              lowered.terminates
              ||
              match (path, within.self_trait) with
              | Method { name; receiver; _ }, Some (implements : T.trait_reference) -> (
                  match
                    Summary.definition database
                      (Method { owner = implements.trait; name; receiver })
                  with
                  | Some (_, { kind = Function { signature; _ } | Method_declaration signature; _ })
                    ->
                      Lower.terminates signature.clauses
                  | _ -> false)
              | _ -> false
            in
            (Function_interface { lowered with terminates }, context)
        | _ -> (Error_interface (Resolve.Parts.error_node definition.span), context))
    | None, None -> (
        match definition.kind with
        | Method_declaration _ ->
            (Error_interface (Resolve.Parts.error_node definition.span), context)
        | Function { signature; _ } ->
            let head, self_type =
              match signature.name with
              | Plain_name _ -> ([], None)
              | Member_name (head, _) ->
                  let generics, self = head_type context path head in
                  (generics, Some self)
            in
            let context = { context with self_type } in
            ( Function_interface (Lower.signature context ~owner:path ~head ~self_type signature),
              context )
        | Type_definition { generics; body; clauses; _ } ->
            let type_generics = Lower.generics context path generics in
            let self = T.Named { path; arguments = generic_arguments type_generics } in
            let context = { context with self_type = Some self } in
            let shape =
              match body with
              | Fields written -> T.Record (fields context written)
              | Variants variants ->
                  T.Sum
                    (List.map
                       (fun (variant : variant) ->
                         {
                           T.variant_name = variant.name.text;
                           fields = Option.map (fields context) variant.fields;
                           indirect = variant.indirect;
                         })
                       variants)
              | Type_todo -> T.Todo_type
            in
            let derives =
              List.concat_map
                (fun (clause : type_clause) ->
                  match clause.kind with
                  | Derives traits ->
                      List.filter_map
                        (fun (trait : path_type) ->
                          match Lower.target context trait.path.last with
                          | Some (Definition (_, trait)) -> Some trait
                          | _ -> None)
                        traits
                  | Type_invariant _ | Potential _ -> [])
                clauses
            in
            ( Type_interface
                { type_generics; shape; opaque = definition.visibility = Public_opaque; derives },
              context )
        | Trait _ | Capability _ | Impl _ -> (
            match lower_container context path definition with
            | Broken report, context -> (Error_interface report, context)
            | Trait_parts { trait_generics; requires; associated_types }, context ->
                ( Trait_interface
                    {
                      trait_generics;
                      requires;
                      associated_types;
                      methods = trait_methods ~is_capability:false;
                      is_capability = false;
                      broken_methods = broken_methods ();
                    },
                  context )
            | Capability_parts, context ->
                ( Trait_interface
                    {
                      trait_generics = [];
                      requires = [];
                      associated_types = [];
                      methods = trait_methods ~is_capability:true;
                      is_capability = true;
                      broken_methods = broken_methods ();
                    },
                  context )
            | Impl_parts { impl_generics; implements; for_type; impl_uses }, context ->
                ( Impl_interface
                    {
                      impl_generics;
                      implements;
                      for_type;
                      impl_uses;
                      impl_methods =
                        List.filter_map
                          (fun (name, receiver, interface, _) ->
                            match interface with
                            | Function_interface signature -> Some (name, receiver, signature)
                            | _ -> None)
                          (methods ());
                      impl_broken = false;
                    },
                  context ))
        | Constant { name; type_; _ } ->
            let context =
              match name with
              | Plain_name _ -> context
              | Member_name (head, _) ->
                  let _, self_type = head_type context path head in
                  { context with self_type = Some self_type }
            in
            (Constant_interface { constant_type = Lower.type_ context type_ }, context)
        | Test { uses; _ } -> (Test_interface (Lower.capabilities context uses), context)
        | Theorem { generics; parameters; clauses; _ } ->
            let signature : signature =
              {
                name = Plain_name { text = ""; span = definition.span; id = definition.id };
                generics;
                parameters;
                result = None;
                clauses;
              }
            in
            ( Theorem_interface
                (Lower.signature context ~owner:path ~head:[] ~self_type:None signature),
              context )
        | Law_proof { trait_; law; type_; _ } -> (
            match Lower.trait_reference context trait_ with
            | Ok trait ->
                ( Law_proof_interface { trait; law = law.text; for_type = Lower.type_ context type_ },
                  context )
            | Error report -> (Error_interface report, context))
        | Definition_error _ -> (Error_interface (Resolve.Parts.error_node definition.span), context)
        )
  in
  ( {
      interface;
      diagnostics = List.rev !(context.diagnostics);
      named = List.rev !(context.named);
      bounds = bounds_of context;
    },
    context )

(* A definition lowered, with the context its bodies are checked in. A
   trait's, an [impl]'s, or a capability's interface is put together from
   its own parts and the interface of each method written inside it, which
   reads only the header, so neither waits on the other. *)
let rec lowered =
  lazy
    (Query.query ~name:"lowered" ~phase:Interfaces ~show:Names.show_key (fun database key ->
         match
           (Query.demand database Names.definition key, Query.demand database Resolve.resolved key)
         with
         | Some definition, Some resolved ->
             Compiler_bug.within ~stage:"Interface" (Names.show_key key) (fun () ->
                 Some (fst (lower database key definition resolved)))
         | _ -> None))

and lower database key definition resolved =
  lower_definition database
    ~interface_of:(fun member ->
      Option.map
        (fun (lowered : lowered) -> lowered.interface)
        (Query.demand database (Lazy.force lowered) member))
    key definition resolved

let lowered = Lazy.force lowered

(* The interface a path names, from its definition with ordinal 0. *)
let interface =
  Query.query ~name:"interface" ~phase:Interfaces ~show:Path.show ~saved:true
    ~about:(fun path -> Some { Query.path; part = Some "interface" })
    (fun database path ->
      match Query.demand database Summary.key path with
      | Some key ->
          Option.map (fun lowered -> lowered.interface) (Query.demand database lowered key)
      | None -> None)

(* Built-in types *)

let builtin_shape builtin : T.type_interface =
  let element : T.parameter = { owner = Intrinsic.builtin_path builtin; name = "Element" } in
  let count : T.parameter = { owner = Intrinsic.builtin_path builtin; name = "count" } in
  let type_generics : T.generic list =
    match builtin with
    | Array ->
        [ { generic = element; kind = Type_generic [] }; { generic = count; kind = Value_generic } ]
    | Storage | View -> [ { generic = element; kind = Type_generic [] } ]
    | _ -> []
  in
  { type_generics; shape = Builtin_type builtin; opaque = true; derives = [] }

(* A type's interface, a built-in's included. [None] for a path that is not
   a type, and the [Error] shape for a type whose definition did not
   parse. *)
let type_interface =
  Query.query ~name:"type_interface" ~phase:Interfaces ~show:Path.show ~saved:true
    ~about:(fun path -> Some { Query.path; part = Some "shape" })
    (fun database path ->
      match Intrinsic.builtin_of_path path with
      | Some builtin -> Some (builtin_shape builtin)
      | None -> (
          match Query.demand database interface path with
          | Some (Type_interface type_) -> Some type_
          | Some (Error_interface report) ->
              Some { type_generics = []; shape = Error_shape report; opaque = false; derives = [] }
          | _ -> None))

(* The signature of a function or a method, wherever it is written. *)
let signature =
  Query.query ~name:"signature" ~phase:Interfaces ~show:Path.show ~saved:true
    ~about:(fun path -> Some { Query.path; part = Some "signature" })
    (fun database (path : Path.t) ->
      match Query.demand database interface path with
      | Some (Function_interface signature | Theorem_interface signature) -> Some signature
      | _ -> None)

(* A function's signature for checking a use of it, or, when its header or
   its member of a trait did not parse, the report of that, since everything
   is accepted of it. *)
let signature_or_report database (path : Path.t) =
  let broken path =
    match Query.demand database interface path with
    | Some (Error_interface report) -> Some (Error report)
    | _ -> None
  in
  match Query.demand database signature path with
  | Some signature -> Some (Ok signature)
  | None -> (
      match path with
      | Method { owner; name; _ } -> (
          match Query.demand database interface owner with
          | Some (Error_interface report) -> Some (Error report)
          | Some (Trait_interface trait) ->
              Option.map (fun report -> Error report) (List.assoc_opt name trait.broken_methods)
          | _ -> broken path)
      | _ -> broken path)

let trait_interface =
  Query.query ~name:"trait_interface" ~phase:Interfaces ~show:Path.show (fun database path ->
      match Query.demand database interface path with
      | Some (Trait_interface trait) -> Some trait
      | _ -> None)

let impl_interface =
  Query.query ~name:"impl_interface" ~phase:Interfaces ~show:Path.show (fun database path ->
      match Query.demand database interface path with
      | Some (Impl_interface impl) -> Some impl
      | Some (Error_interface report) ->
          Some
            {
              T.impl_generics = [];
              implements = { trait = path; trait_arguments = []; associated = [] };
              for_type = T.Error report;
              impl_uses = [];
              impl_methods = [];
              impl_broken = true;
            }
      | _ -> None)

let constant_type =
  Query.query ~name:"constant_type" ~phase:Interfaces ~show:Path.show (fun database path ->
      match Query.demand database interface path with
      | Some (Constant_interface constant) -> Some constant.constant_type
      | Some (Error_interface report) -> Some (T.Error report)
      | _ -> None)
