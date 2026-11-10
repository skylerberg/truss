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
  | Law_proof_interface
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
  | Some (Definition type_path) ->
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

let receiver_of (signature : signature) = Names.receiver signature.parameters

let lower_definition database (key : Names.key) (definition : definition)
    (resolved : Resolve.resolved) =
  let context = Lower.create database resolved in
  let broken part = Resolve.Parts.broken definition part in
  let path = key.path in
  (* Each kind of definition gives its interface, and the context its bodies
     are checked in: what [Self] and its associated types mean there. *)
  let interface, context =
    match Resolve.Parts.reported definition Header with
    | Some report -> (Error_interface report, context)
    | None -> (
        match definition.kind with
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
                          | Some (Definition trait) -> Some trait
                          | _ -> None)
                        traits
                  | Type_invariant _ | Potential _ -> [])
                clauses
            in
            ( Type_interface
                { type_generics; shape; opaque = definition.visibility = Public_opaque; derives },
              context )
        | Trait { generics; requires; members; _ } ->
            let trait_generics = Lower.generics context path generics in
            let self_parameter = trait_self_parameter path in
            let self_trait : T.trait_reference =
              { trait = path; trait_arguments = generic_arguments trait_generics; associated = [] }
            in
            Hashtbl.replace context.bounds self_parameter [ self_trait ];
            let context =
              {
                context with
                self_type = Some (T.Parameter self_parameter);
                self_trait = Some self_trait;
              }
            in
            let requires = Lower.trait_bounds context requires in
            let broken_methods = ref [] in
            let methods = ref [] and associated = ref [] in
            List.iteri
              (fun index (line : trait_member line) ->
                match line.kind with
                | Trait_method { signature; body } ->
                    let name =
                      match signature.name with
                      | Plain_name name | Member_name (_, name) -> name.text
                    in
                    begin match Resolve.Parts.reported definition (Member_header index) with
                    | Some report -> broken_methods := (name, report) :: !broken_methods
                    | None ->
                        let receiver = receiver_of signature in
                        let owner : Path.t = Method { owner = path; name; receiver } in
                        methods :=
                          {
                            T.method_name = name;
                            method_receiver = receiver;
                            method_signature =
                              Lower.signature context ~owner ~head:[]
                                ~self_type:(Some (T.Parameter self_parameter)) signature;
                            provided = Option.is_some body;
                          }
                          :: !methods
                    end
                | Associated_type (name, bounds) ->
                    associated :=
                      {
                        T.associated_name = name.text;
                        associated_bounds = Lower.trait_bounds context bounds;
                      }
                      :: !associated
                | Law _ | Trait_member_error -> ())
              members;
            ( Trait_interface
                {
                  trait_generics;
                  requires;
                  associated_types = List.rev !associated;
                  methods = List.rev !methods;
                  is_capability = false;
                  broken_methods = List.rev !broken_methods;
                },
              context )
        | Capability { members; _ } ->
            let broken_methods = ref [] and methods = ref [] in
            List.iteri
              (fun index (line : capability_member line) ->
                match line.kind with
                | Capability_method signature ->
                    let name =
                      match signature.name with
                      | Plain_name name | Member_name (_, name) -> name.text
                    in
                    begin match Resolve.Parts.reported definition (Member_header index) with
                    | Some report -> broken_methods := (name, report) :: !broken_methods
                    | None ->
                        let owner : Path.t = Method { owner = path; name; receiver = Static } in
                        methods :=
                          {
                            T.method_name = name;
                            method_receiver = Static;
                            method_signature =
                              Lower.signature context ~owner ~head:[] ~self_type:None signature;
                            provided = false;
                          }
                          :: !methods
                    end
                | Capability_member_error -> ())
              members;
            ( Trait_interface
                {
                  trait_generics = [];
                  requires = [];
                  associated_types = [];
                  methods = List.rev !methods;
                  is_capability = true;
                  broken_methods = List.rev !broken_methods;
                },
              context )
        | Impl { trait_; type_ = head; uses; members } -> (
            let impl_generics, for_type = head_type context path head in
            match Lower.trait_reference ~capability:true context trait_ with
            | Error report -> (Error_interface report, context)
            | Ok implements ->
                let associated =
                  List.sort compare
                    (List.filter_map
                       (fun (line : impl_member line) ->
                         match line.kind with
                         | Associated_definition (name, written) ->
                             Some
                               ( name.text,
                                 Lower.type_ { context with self_type = Some for_type } written )
                         | Impl_method _ | Impl_member_error -> None)
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
                let methods =
                  List.concat
                    (List.mapi
                       (fun index (line : impl_member line) ->
                         match line.kind with
                         | Impl_method { signature; _ } when not (broken (Member_header index)) ->
                             let name =
                               match signature.name with
                               | Plain_name name | Member_name (_, name) -> name.text
                             in
                             let receiver = receiver_of signature in
                             let owner : Path.t = Method { owner = path; name; receiver } in
                             [
                               ( name,
                                 receiver,
                                 Lower.signature context ~owner ~head:[] ~self_type:(Some for_type)
                                   signature );
                             ]
                         | _ -> [])
                       members)
                in
                ( Impl_interface
                    {
                      impl_generics;
                      implements;
                      for_type;
                      impl_uses = Lower.capabilities context uses;
                      impl_methods = methods;
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
        | Law_proof _ -> (Law_proof_interface, context)
        | Definition_error _ -> (Error_interface (Resolve.Parts.error_node definition.span), context)
        )
  in
  ( {
      interface;
      diagnostics = List.rev !(context.diagnostics);
      named = List.rev !(context.named);
      bounds =
        List.sort compare
          (Hashtbl.fold (fun parameter bounds acc -> (parameter, bounds) :: acc) context.bounds []);
    },
    context )

let lowered =
  Query.query ~name:"lowered" ~phase:Interfaces ~show:Names.show_key (fun database key ->
      match
        (Query.demand database Names.definition key, Query.demand database Resolve.resolved key)
      with
      | Some definition, Some resolved ->
          Compiler_bug.within ~stage:"Interface" (Names.show_key key) (fun () ->
              Some (fst (lower_definition database key definition resolved)))
      | _ -> None)

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

(* The signature of a function or method. For a method of a trait, a
   capability, or an [impl], it is found in the owner's interface. *)
let signature =
  Query.query ~name:"signature" ~phase:Interfaces ~show:Path.show ~saved:true
    ~about:(fun path -> Some { Query.path; part = Some "signature" })
    (fun database (path : Path.t) ->
      let from_owner owner name receiver =
        match Query.demand database interface owner with
        | Some (Trait_interface trait) ->
            List.find_map
              (fun (method_ : T.trait_method) ->
                if method_.method_name = name && method_.method_receiver = receiver then
                  Some method_.method_signature
                else None)
              trait.methods
        | Some (Impl_interface impl) ->
            List.find_map
              (fun (method_name, method_receiver, signature) ->
                if method_name = name && method_receiver = receiver then Some signature else None)
              impl.impl_methods
        | _ -> None
      in
      match path with
      | Method { owner = Impl _ as owner; name; receiver } -> from_owner owner name receiver
      | Method { owner; name; receiver } -> (
          match Summary.kind_of database owner with
          | Some (Trait | Capability) -> from_owner owner name receiver
          | _ -> (
              match Query.demand database interface path with
              | Some (Function_interface signature | Theorem_interface signature) -> Some signature
              | _ -> None))
      | _ -> (
          match Query.demand database interface path with
          | Some (Function_interface signature | Theorem_interface signature) -> Some signature
          | _ -> None))

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
