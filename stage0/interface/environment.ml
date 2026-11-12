open Syntax
module Names = Resolve.Names

type interface =
  | Function_interface of Types.signature
  | Type_interface of Types.type_interface
  | Trait_interface of Types.trait_interface
  | Impl_interface of Types.impl_interface
  | Constant_interface of Types.constant_interface
  | Test_interface of Types.capability list
  | Theorem_interface of Types.signature
  | Law_proof_interface of {
      generics : Types.generic list;
      trait : Types.trait_reference;
      law : string;
      for_type : Types.ty;
    }
  | Error_interface of Diagnostic.reported

type lowered_interface = {
  interface : interface;
  diagnostics : Syntax.diagnostic list;
  named : (span * Types.ty) list;
  bounds : (Types.parameter * Types.trait_reference list) list;
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
      let arguments = Types.generic_arguments generics in
      let type_ =
        match Intrinsic.builtin_of_path type_path with
        | Some Never -> Types.Never
        | Some Integer -> Types.Integer
        | _ -> Types.Named { path = type_path; arguments }
      in
      (generics, type_)
  | Some (Definition (((Trait | Capability) as kind), _)) ->
      ( generics,
        Lower.error context Not_a_type head.span
          (Printf.sprintf "`%s` is %s, not a type, so it has no methods, constants, or `impl`s."
             (Names.spell_path head.path)
             (Names.kind_name (Names.kind_of_named kind))) )
  | Some (Unknown report) -> (generics, Types.Error report)
  | _ -> Lower.bug "the type head `%s` is not resolved" (Names.spell_path head.path)

let trait_self_parameter trait : Types.parameter = { owner = trait; name = "Self" }

(* The fields of a shape, in the order of their names. The order of
   declaration is not part of a shape, so reordering a type's fields changes
   no result that reads the shape. *)
let fields context (written : field list) =
  List.stable_sort
    (fun (left : Types.field) (right : Types.field) ->
      String.compare left.field_name right.field_name)
    (List.filter_map
       (fun (field : field) ->
         match field.kind with
         | Field_declaration { name; type_; default } ->
             Some
               {
                 Types.field_name = name.text;
                 field_type = Lower.type_ context type_;
                 field_has_default = Option.is_some default;
               }
         | Field_error -> None)
       written)

(* The header of a trait, an [impl], or a capability: its own declarations,
   without the methods written inside it. *)
type container =
  | Trait_parts of {
      trait_generics : Types.generic list;
      requires : Types.trait_reference list;
      associated_types : Types.associated_type list;
      associated_capabilities : string list;
      laws : (string * (string * Types.ty) list) list;
    }
  | Capability_parts
  | Impl_parts of {
      impl_generics : Types.generic list;
      implements : Types.trait_reference;
      for_type : Types.ty;
      impl_uses : Types.capability list;
      capability_sets : (string * Types.capability list) list;
    }
  | Broken of Diagnostic.reported  (** An [impl] whose trait name does not resolve to a trait. *)

(* The header of a trait, an [impl], or a capability, and the context in
   which its members are lowered: the meaning of [Self] and of its
   associated types, and the bounds of its generic parameters. *)
let lower_container (context : Lower.context) (path : Path.t) (definition : definition) =
  match definition.kind with
  | Trait { generics; requires; members; _ } ->
      let trait_generics = Lower.generics context path generics in
      let self_parameter = trait_self_parameter path in
      let self_trait : Types.trait_reference =
        { trait = path; trait_arguments = Types.generic_arguments trait_generics; associated = [] }
      in
      Hashtbl.replace context.bounds self_parameter [ self_trait ];
      let context =
        {
          context with
          self_type = Some (Types.Parameter self_parameter);
          self_trait = Some self_trait;
        }
      in
      let requires = Lower.trait_bounds context requires in
      let associated_types =
        List.filter_map
          (fun (line : trait_member line) ->
            match line.kind with
            | Associated_type (name, bounds) ->
                Some
                  {
                    Types.associated_name = name.text;
                    associated_bounds = Lower.trait_bounds context bounds;
                  }
            | Associated_capability _ | Law _ | Trait_member_error -> None)
          members
      in
      let associated_capabilities =
        List.filter_map
          (fun (line : trait_member line) ->
            match line.kind with Associated_capability name -> Some name.text | _ -> None)
          members
      in
      let laws =
        List.filter_map
          (fun (line : trait_member line) ->
            match line.kind with
            | Law law ->
                Some
                  ( law.name.text,
                    List.filter_map
                      (fun (parameter : parameter) ->
                        match parameter.kind with
                        | Named_parameter { name; type_; _ } ->
                            Some (name.text, Lower.type_ context type_)
                        | Self_parameter _ | Parameter_error -> None)
                      law.parameters )
            | Associated_type _ | Associated_capability _ | Trait_member_error -> None)
          members
      in
      ( Trait_parts { trait_generics; requires; associated_types; associated_capabilities; laws },
        context )
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
                   | Capability_definition _ | Impl_member_error -> None)
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
          (* A set can name the sets defined before it. A set that named
             itself, or a set defined after it, would have no value. *)
          let capability_sets =
            List.fold_left
              (fun sets (line : impl_member line) ->
                match line.kind with
                | Capability_definition (name, written) ->
                    let set =
                      Lower.capabilities { context with self_capabilities = sets } written
                    in
                    let defined_by_this_impl = function
                      | Types.Capability_projection { base; trait; _ } ->
                          Types.equal base for_type && Path.equal trait.trait implements.trait
                      | _ -> false
                    in
                    if List.exists defined_by_this_impl set then begin
                      Lower.report context Unknown_associated_capability name.span
                        (Printf.sprintf
                           "`%s` is defined from itself, or from a set that this `impl` defines \
                            after it."
                           name.text);
                      sets
                    end
                    else if List.mem_assoc name.text sets then sets
                    else (name.text, set) :: sets
                | Associated_definition _ | Impl_member_error -> sets)
              [] members
          in
          let declared =
            match Query.demand context.database Summary.trait_header implements.trait with
            | Some header -> header.capabilities
            | None -> []
          in
          let context =
            {
              context with
              self_capabilities =
                List.map
                  (fun name ->
                    (name, Option.value ~default:[] (List.assoc_opt name capability_sets)))
                  declared;
            }
          in
          ( Impl_parts
              {
                impl_generics;
                implements;
                for_type;
                impl_uses = Lower.capabilities context uses;
                capability_sets =
                  List.sort compare
                    (List.filter (fun (name, _) -> List.mem name declared) capability_sets);
              },
            context ))
  | _ -> (Capability_parts, context)

(* The context that a trait, an [impl], or a capability gives to each method
   written inside it. It is a report instead when the header of the
   enclosing declaration did not parse, or when it is an [impl] whose trait
   name does not resolve to a trait. *)
type header = {
  self_type : Types.ty option;
  self_trait : Types.trait_reference option;
  self_associated : (string * Types.ty) list;
  self_capabilities : (string * Types.capability list) list;
  header_bounds : (Types.parameter * Types.trait_reference list) list;
  header_generics : Types.generic list;
      (** The generic parameters of an [impl], which precede those of a method written inside it. A
          trait's parameters are supplied at each call of its method, with [Self]. *)
  header_uses : Types.capability list;
      (** An [impl]'s [uses], which are each of its methods' too. *)
}

let bounds_of (context : Lower.context) =
  List.sort compare
    (Hashtbl.fold
       (fun parameter bounds bounds_by_parameter -> (parameter, bounds) :: bounds_by_parameter)
       context.bounds [])

let header =
  Query.query ~name:"header" ~phase:Phases.interfaces ~show:Names.show_key (fun database key ->
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
                         self_capabilities = context.self_capabilities;
                         header_bounds = bounds_of context;
                         header_generics;
                         header_uses;
                       })))
      | _ -> None)

(* [interface_of] returns the interface of a method written inside the
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
                Types.method_name = name;
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
  (* Lowers each kind of definition to its interface and to the context in
     which its bodies are checked: the meaning of [Self] and of its
     associated types. *)
  let interface, context =
    match
      ( Resolve.Parts.reported definition Header,
        Option.bind (Query.demand database Names.container key) (Query.demand database header) )
    with
    | Some report, _ | None, Some (Error report) -> (Error_interface report, context)
    | None, Some (Ok container) -> (
        (* A method written inside a trait, an [impl], or a capability:
           [Self], its associated types, and the generic parameters around
           it are that one's. *)
        List.iter
          (fun (parameter, bounds) -> Hashtbl.replace context.bounds parameter bounds)
          container.header_bounds;
        let context =
          {
            context with
            self_type = container.self_type;
            self_trait = container.self_trait;
            self_associated = container.self_associated;
            self_capabilities = container.self_capabilities;
          }
        in
        match definition.kind with
        | Function { signature; _ } | Method_declaration signature ->
            let lowered =
              Types.method_in_impl ~impl_generics:container.header_generics
                ~impl_uses:container.header_uses
                (Lower.signature context ~owner:path ~head:[] ~self_type:container.self_type
                   signature)
            in
            (* An [impl]'s method ends when its trait's does, since it keeps the
               trait's [time] clause. *)
            let terminates =
              lowered.terminates
              ||
              match (path, container.self_trait) with
              | Method { name; receiver; _ }, Some (implements : Types.trait_reference) -> (
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
        | _ -> (Error_interface (Resolve.Parts.recovery_report definition.span), context))
    | None, None -> (
        match definition.kind with
        | Method_declaration _ ->
            (Error_interface (Resolve.Parts.recovery_report definition.span), context)
        | Function { signature; _ } ->
            let head, self_type =
              match signature.name with
              | Plain_name _ -> ([], None)
              | Member_name (head, _) ->
                  let generics, self = head_type context path head in
                  (generics, Some self)
            in
            let context = { context with self_type } in
            ( Function_interface
                {
                  (Lower.signature context ~owner:path ~head ~self_type signature) with
                  transparent = definition.visibility = Public_transparent;
                },
              context )
        | Type_definition { generics; body; clauses; _ } ->
            let type_generics = Lower.generics context path generics in
            let self = Types.Named { path; arguments = Types.generic_arguments type_generics } in
            let context = { context with self_type = Some self } in
            let shape =
              match body with
              | Fields written -> Types.Record (fields context written)
              | Variants variants ->
                  Types.Sum
                    (List.map
                       (fun (variant : variant) ->
                         {
                           Types.variant_name = variant.name.text;
                           fields = Option.map (fields context) variant.fields;
                           indirect = variant.indirect;
                         })
                       variants)
              | Type_todo -> Types.Todo_type
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
            | ( Trait_parts
                  { trait_generics; requires; associated_types; associated_capabilities; laws },
                context ) ->
                ( Trait_interface
                    {
                      trait_generics;
                      requires;
                      associated_types;
                      associated_capabilities;
                      laws;
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
                      associated_capabilities = [];
                      laws = [];
                      methods = trait_methods ~is_capability:true;
                      is_capability = true;
                      broken_methods = broken_methods ();
                    },
                  context )
            | ( Impl_parts { impl_generics; implements; for_type; impl_uses; capability_sets },
                context ) ->
                ( Impl_interface
                    {
                      impl_generics;
                      implements;
                      for_type;
                      impl_uses;
                      capability_sets;
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
            let generics, for_type = head_type context path type_ in
            match Lower.trait_reference context trait_ with
            | Ok trait ->
                (Law_proof_interface { generics; trait; law = law.text; for_type }, context)
            | Error report -> (Error_interface report, context))
        | Definition_error _ ->
            (Error_interface (Resolve.Parts.recovery_report definition.span), context))
  in
  ( {
      interface;
      diagnostics = List.rev !(context.diagnostics);
      named = List.rev !(context.named);
      bounds = bounds_of context;
    },
    context )

(* The lowered interface of a definition, with lowering's diagnostics. The
   interface of a trait, an [impl], or a capability is assembled from its
   header and from the interface of each method written inside it. Each
   method's interface reads only the header, so neither query depends on
   the other. *)
let rec lowered_interface =
  lazy
    (Query.query ~name:"lowered_interface" ~phase:Phases.interfaces ~show:Names.show_key
       (fun database key ->
         match
           (Query.demand database Names.definition key, Query.demand database Resolve.resolved key)
         with
         | Some definition, Some resolved ->
             Compiler_bug.while_doing ~stage:"Interface" (Names.show_key key) (fun () ->
                 Some (fst (lower database key definition resolved)))
         | _ -> None))

and lower database key definition resolved =
  lower_definition database
    ~interface_of:(fun member ->
      Option.map
        (fun (lowered : lowered_interface) -> lowered.interface)
        (Query.demand database (Lazy.force lowered_interface) member))
    key definition resolved

let lowered_interface = Lazy.force lowered_interface

let interface =
  Query.query ~name:"interface" ~phase:Phases.interfaces ~show:Path.show ~saved:true
    ~about:(fun path -> Some { Query.path; part = Some "interface" })
    (fun database path ->
      match Query.demand database Summary.key path with
      | Some key ->
          Option.map
            (fun lowered -> lowered.interface)
            (Query.demand database lowered_interface key)
      | None -> None)

(* The names of a type's fields in declaration order: of a record under
   [None], and of each variant of a sum type under its name. A derived
   [Ordered] compares fields in this order, and nothing else reads it. *)
let declared_fields =
  Query.query ~name:"declared_fields" ~phase:Phases.interfaces ~show:Path.show (fun database path ->
      let names (written : field list) =
        List.filter_map
          (fun (field : field) ->
            match field.kind with
            | Field_declaration { name; _ } -> Some name.text
            | Field_error -> None)
          written
      in
      match
        Option.bind
          (Query.demand database Summary.key path)
          (Query.demand database Names.definition)
      with
      | Some { kind = Type_definition { body = Fields written; _ }; _ } -> [ (None, names written) ]
      | Some { kind = Type_definition { body = Variants variants; _ }; _ } ->
          List.map
            (fun (variant : variant) ->
              (Some variant.name.text, names (Option.value ~default:[] variant.fields)))
            variants
      | _ -> [])

let in_declared_order database path ~variant ~name fields =
  match List.assoc_opt variant (Query.demand database declared_fields path) with
  | Some declared ->
      let position field =
        let rec find index = function
          | [] -> index
          | declared_name :: rest ->
              if declared_name = name field then index else find (index + 1) rest
        in
        find 0 declared
      in
      List.stable_sort (fun left right -> compare (position left) (position right)) fields
  | None -> fields

let builtin_shape builtin : Types.type_interface =
  let element : Types.parameter = { owner = Intrinsic.builtin_path builtin; name = "Element" } in
  let count : Types.parameter = { owner = Intrinsic.builtin_path builtin; name = "count" } in
  let type_generics : Types.generic list =
    match builtin with
    | Array ->
        [ { generic = element; kind = Type_generic [] }; { generic = count; kind = Value_generic } ]
    | Storage | View -> [ { generic = element; kind = Type_generic [] } ]
    | Shared ->
        let storable : Types.trait_reference =
          { trait = Well_known.path Storable; trait_arguments = []; associated = [] }
        in
        [
          {
            generic = { owner = Intrinsic.builtin_path builtin; name = "Value" };
            kind = Type_generic [ storable ];
          };
        ]
    | _ -> []
  in
  { type_generics; shape = Builtin_type builtin; opaque = true; derives = [] }

let type_interface =
  Query.query ~name:"type_interface" ~phase:Phases.interfaces ~show:Path.show ~saved:true
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

let signature =
  Query.query ~name:"signature" ~phase:Phases.interfaces ~show:Path.show ~saved:true
    ~about:(fun path -> Some { Query.path; part = Some "signature" })
    (fun database (path : Path.t) ->
      match Query.demand database interface path with
      | Some (Function_interface signature | Theorem_interface signature) -> Some signature
      | _ -> None)

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
  Query.query ~name:"trait_interface" ~phase:Phases.interfaces ~show:Path.show (fun database path ->
      match Query.demand database interface path with
      | Some (Trait_interface trait) -> Some trait
      | _ -> None)

let impl_interface =
  Query.query ~name:"impl_interface" ~phase:Phases.interfaces ~show:Path.show (fun database path ->
      match Query.demand database interface path with
      | Some (Impl_interface impl) -> Some impl
      | Some (Error_interface report) ->
          Some
            {
              Types.impl_generics = [];
              implements = { trait = path; trait_arguments = []; associated = [] };
              for_type = Types.Error report;
              impl_uses = [];
              capability_sets = [];
              impl_methods = [];
              impl_broken = true;
            }
      | _ -> None)

let constant_type =
  Query.query ~name:"constant_type" ~phase:Phases.interfaces ~show:Path.show (fun database path ->
      match Query.demand database interface path with
      | Some (Constant_interface constant) -> Some constant.constant_type
      | Some (Error_interface report) -> Some (Types.Error report)
      | _ -> None)
