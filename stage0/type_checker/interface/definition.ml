open Syntax
open Environment
module Names = Resolve.Names

let head_type context owner (head : type_head) =
  let generics = Lower.generics context owner head.generics in
  match Lower.target context head.path.last with
  | Some (Definition (Type, type_path)) ->
      (match Names.generics_of context.lookups.names type_path with
      | Some expected when List.length expected <> List.length generics ->
          Lower.report context Arity context.spans.(head.id)
            (Printf.sprintf "`%s` takes %d generic %s, and this head names %d."
               (Lower.show_path head.path) (List.length expected)
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
        Lower.error context Not_a_type context.spans.(head.id)
          (Printf.sprintf "`%s` is %s, not a type, so it has no methods, constants, or `impl`s."
             (Lower.show_path head.path)
             (Names.kind_name (Names.kind_of_named kind))) )
  | Some (Unknown report) -> (generics, Types.Error report)
  | _ -> Lower.bug "the type head `%s` is not resolved" (Lower.show_path head.path)

let trait_self_parameter trait : Types.parameter = { owner = trait; name = "Self" }

let fields context (written : field list) =
  List.stable_sort
    (fun (left : Types.field) (right : Types.field) ->
      String.compare left.field_name right.field_name)
    (List.filter_map
       (fun (field : field) ->
         match field.kind with
         | Field_declaration { name; type_; default } ->
             let field_type = Lower.type_ context type_ in
             let field_type =
               match Types.find_specification_only_type field_type with
               | None -> field_type
               | Some specification_type ->
                   Lower.error context Specification_only context.spans.(type_.id)
                     (Printf.sprintf
                        "`%s` exists only in specifications and has no representation in code that \
                         runs, so it is not the type of a field."
                        (Types.show specification_type))
             in
             Some
               {
                 Types.field_name = name.text;
                 field_type;
                 field_has_default = Option.is_some default;
               }
         | Field_error -> None)
       written)

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
      impl_uses : Types.capability_set;
      capability_sets : (string * Types.capability_set) list;
    }
  | Broken of Diagnostic.reported

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
          (fun (line : trait_member node) ->
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
          (fun (line : trait_member node) ->
            match line.kind with Associated_capability name -> Some name.text | _ -> None)
          members
      in
      let laws =
        List.filter_map
          (fun (line : trait_member node) ->
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
                 (fun (line : impl_member node) ->
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
          let capability_sets =
            List.fold_left
              (fun sets (line : impl_member node) ->
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
                    if List.exists defined_by_this_impl (set :> Types.capability list) then begin
                      Lower.report context Unknown_associated_capability context.spans.(name.id)
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
            match context.lookups.trait_header implements.trait with
            | Some header -> header.capabilities
            | None -> []
          in
          let context =
            {
              context with
              self_capabilities =
                List.map
                  (fun name ->
                    ( name,
                      Option.value ~default:Types.no_capabilities
                        (List.assoc_opt name capability_sets) ))
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

let header (lookups : Lookups.t) (key : Names.key) =
  match lookups.resolved Interface key with
  | Some resolved -> (
      if Names.is_broken lookups.names key Header then Some (Error [])
      else
        match
          lower_container
            (Lower.create lookups resolved ~spans:(lookups.names.spans key) empty_scope)
            key.path (lookups.names.definition key)
        with
        | _, context when !(context.diagnostics) <> [] ->
            Some (Error (List.rev !(context.diagnostics)))
        | Broken _, _ -> Some (Error [])
        | parts, context ->
            let header_generics, header_uses =
              match parts with
              | Impl_parts { impl_generics; impl_uses; _ } -> (impl_generics, impl_uses)
              | _ -> ([], Types.no_capabilities)
            in
            Some (Ok { container_scope = Lower.scope context; header_generics; header_uses }))
  | None -> None

let lower_definition (lookups : Lookups.t) (key : Names.key) (definition : definition) ~spans
    (resolved : Resolve.resolved) =
  let context = Lower.create lookups resolved ~spans empty_scope in
  let path = key.path in
  let methods () =
    List.filter_map
      (fun (member : Names.key) ->
        match (member.path, lookups.names.definition member) with
        | Method { name; receiver; _ }, { kind = Function _; _ } ->
            Some { Types.method_name = name; method_receiver = receiver; provided = true }
        | Method { name; receiver; _ }, { kind = Method_declaration _; _ } ->
            Some { Types.method_name = name; method_receiver = receiver; provided = false }
        | _ -> None)
      (lookups.names.contained key)
  in
  let interface, context =
    match
      ( Names.recovery_report lookups.names key Header,
        Option.map lookups.header (lookups.names.container key) )
    with
    | Some report, _ -> (Error_interface report, context)
    | None, Some None ->
        (Error_interface (Resolve.Parts.recovery_report spans.(definition.id)), context)
    | None, Some (Some container) -> (
        let context = Lower.create lookups resolved ~spans container.container_scope in
        match definition.kind with
        | Function { signature; _ } | Method_declaration signature ->
            let lowered =
              Types.method_in_impl ~impl_generics:container.header_generics
                ~impl_uses:container.header_uses
                (Lower.signature context ~owner:path ~head:[]
                   ~self_type:container.container_scope.self_type signature)
            in
            let terminates =
              lowered.terminates
              ||
              match (path, container.container_scope.self_trait) with
              | Method { name; receiver; _ }, Some (implements : Types.trait_reference) -> (
                  match
                    Option.map lookups.names.definition
                      (lookups.names.key (Method { owner = implements.trait; name; receiver }))
                  with
                  | Some { kind = Function { signature; _ } | Method_declaration signature; _ } ->
                      Lower.terminates signature.clauses
                  | _ -> false)
              | _ -> false
            in
            (Function_interface { lowered with terminates }, context)
        | _ -> (Error_interface (Resolve.Parts.recovery_report spans.(definition.id)), context))
    | None, None -> (
        match definition.kind with
        | Method_declaration _ ->
            (Error_interface (Resolve.Parts.recovery_report spans.(definition.id)), context)
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
                      methods = methods ();
                      is_capability = false;
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
                      methods = methods ();
                      is_capability = true;
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
                        List.map
                          (fun (method_ : Types.trait_method) ->
                            (method_.method_name, method_.method_receiver))
                          (methods ());
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
                name = Plain_name { text = ""; id = definition.id };
                generics;
                parameters;
                result = None;
                clauses;
              }
            in
            ( Theorem_interface
                {
                  (Lower.signature context ~owner:path ~head:[] ~self_type:None signature) with
                  specification_only = true;
                },
              context )
        | Law_proof { trait_; law; type_; _ } -> (
            let generics, for_type = head_type context path type_ in
            match Lower.trait_reference context trait_ with
            | Ok trait ->
                (Law_proof_interface { generics; trait; law = law.text; for_type }, context)
            | Error report -> (Error_interface report, context))
        | Definition_error _ ->
            (Error_interface (Resolve.Parts.recovery_report spans.(definition.id)), context))
  in
  {
    interface;
    diagnostics = List.rev !(context.diagnostics);
    named = List.rev !(context.named);
    scope = Lower.scope context;
  }

let lower (lookups : Lookups.t) key =
  match lookups.resolved Interface key with
  | Some resolved ->
      Compiler_bug.while_doing ~stage:"Interface" (Names.show_key key) (fun () ->
          Some
            (lower_definition lookups key (lookups.names.definition key)
               ~spans:(lookups.names.spans key) resolved))
  | None -> None

let interface (lookups : Lookups.t) path =
  Option.bind (lookups.names.key path) (fun key ->
      Option.map
        (fun (lowered : lowered_interface) -> lowered.interface)
        (lookups.lowered_interface key))

let declared_fields (lookups : Lookups.t) path =
  let names (written : field list) =
    List.filter_map
      (fun (field : field) ->
        match field.kind with
        | Field_declaration { name; _ } -> Some name.text
        | Field_error -> None)
      written
  in
  match Option.map lookups.names.definition (lookups.names.key path) with
  | Some { kind = Type_definition { body = Fields written; _ }; _ } -> [ (None, names written) ]
  | Some { kind = Type_definition { body = Variants variants; _ }; _ } ->
      List.map
        (fun (variant : variant) ->
          (Some variant.name.text, names (Option.value ~default:[] variant.fields)))
        variants
  | _ -> []

let in_declared_order lookups path ~variant ~name fields =
  match List.assoc_opt variant (declared_fields lookups path) with
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

let type_interface lookups (path : Path.t) =
  match Intrinsic.builtin_of_path path with
  | Some builtin -> Some (builtin_shape builtin)
  | None -> (
      match interface lookups path with Some (Type_interface type_) -> Some type_ | _ -> None)

let signature lookups (path : Path.t) =
  match interface lookups path with
  | Some (Function_interface signature | Theorem_interface signature) -> Some signature
  | _ -> None

let trait_interface lookups (path : Path.t) =
  match interface lookups path with Some (Trait_interface trait) -> Some trait | _ -> None

let impl_interface lookups (path : Path.t) =
  match interface lookups path with Some (Impl_interface impl) -> Some impl | _ -> None

let test_uses lookups path =
  match interface lookups path with Some (Test_interface uses) -> Some uses | _ -> None

let constant_type lookups (path : Path.t) =
  match interface lookups path with
  | Some (Constant_interface constant) -> Some constant.constant_type
  | _ -> None

let method_signature lookups ~owner (method_ : Types.trait_method) =
  let path =
    Path.Method { owner; name = method_.method_name; receiver = method_.method_receiver }
  in
  match signature lookups path with
  | Some signature -> signature
  | None -> Lower.bug "the method `%s` has no signature" (Path.show path)
