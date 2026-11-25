let make ?(fixes = []) code location message : Nodes.description =
  { code = Resolve code; severity = Error; location; message; notes = []; fixes }

let say text : _ Description.piece list = [ Text text ]

let show_expected = function
  | Resolve.In_module module_ -> Printf.sprintf "in `%s`" (Path.show_module module_)
  | Type_here -> "a type here"
  | Value_here -> "a value here"
  | Constant_in_module_here -> "a constant in a module here"

let show_kind : Language.Definition_kind.t -> string = function
  | Function -> "a function"
  | Type -> "a type"
  | Trait -> "a trait"
  | Capability -> "a capability"
  | Constant | Member_constant -> "a constant"
  | Theorem -> "a theorem"
  | Method -> "a method"
  | Impl -> "an `impl`"
  | Test -> "a test"
  | Law_proof -> "a law's proof"

let show_binding = function
  | Resolve.Local -> "a local here"
  | Parameter -> "a parameter"
  | Generic_parameter -> "a generic parameter"
  | Generic_parameter_here -> "a generic parameter here"
  | Field -> "a field"
  | Law_parameter -> "a parameter of the law"
  | Module_definition kind -> show_kind kind ^ " of this module"
  | Prelude_name -> "a name in the prelude"

let show_names = function [] -> "none" | names -> "`" ^ String.concat "`, `" names ^ "`"

let describe_path_start module_ =
  Printf.sprintf
    "Every path starts with a package name, even inside the package. This file's module is `%s`."
    (Path.show_module module_)

let restricted_module = "Only the `standard` package can use `standard.intrinsic`."

let describe : Resolve.t -> Nodes.description = function
  | Unknown { name; written; expected; candidates } ->
      make Unknown_name (Build.at name)
        ~fixes:(Build.list_spelling_fixes name ~written candidates)
        (say (Printf.sprintf "Nothing named `%s` is %s." written (show_expected expected)))
  | Unknown_value_or_module { name; written; candidates } ->
      make Unknown_name (Build.at name)
        ~fixes:(Build.list_spelling_fixes name ~written candidates)
        (say (Printf.sprintf "Nothing named `%s` is a value or a module here." written))
  | Bare_variant { name; written; owner; other_owners } ->
      let qualify owner = owner ^ "." ^ written in
      make Unknown_name (Build.at name)
        ~fixes:
          (List.map
             (fun owner ->
               {
                 Description.title = say (Printf.sprintf "Write `%s`." (qualify owner));
                 edits = [ Build.replace name [ Text (qualify owner) ] ];
               })
             (owner :: other_owners))
        (say
           (Printf.sprintf
              "`%s` is a variant of %s, and in an expression a variant is written under its type, \
               as in `%s`."
              written
              (String.concat " and "
                 (List.map (fun owner -> "`" ^ owner ^ "`") (owner :: other_owners)))
              (qualify owner)))
  | Capability_parameter_without_generic { name; written } ->
      make Unknown_name (Build.at name)
        ~fixes:
          [
            {
              title = say (Printf.sprintf "Write `generic %s`." written);
              edits = [ Build.replace name [ Text ("generic " ^ written) ] ];
            };
          ]
        (say
           (Printf.sprintf
              "`%s` is a capability parameter of this signature, which is written `generic %s` at \
               each use."
              written written))
  | Unknown_generic_capability { reference; written } ->
      make Unknown_name (Build.at reference)
        (say
           (Printf.sprintf
              "`generic %s` names no capability parameter here. A capability parameter belongs to \
               a function, a method, or a theorem, whose signature names it."
              written))
  | Loop_element { name; written } ->
      make Unknown_name (Build.at name)
        (say
           (Printf.sprintf
              "`%s` is the loop's element, which is bound only in the loop's body: the loop's \
               clauses hold before the first element and after the last. Name the elements so far \
               with `visited`."
              written))
  | Not_visible { name; path; visibility } ->
      make Not_visible (Build.at name) (say (Build.write_hidden path visibility))
  | Intrinsic_import { name } -> make Intrinsic_import (Build.at name) (say restricted_module)
  | Import_or_package { name; written; imported; package } ->
      make Ambiguous_module (Build.at name)
        (say
           (Printf.sprintf
              "`%s` could be the imported module `%s` or the module `%s`. Write the imported one's \
               full path, or remove its `use`."
              written (Path.show_module imported) (Path.show_module package)))
  | Definition_or_package { name; written; module_; member } ->
      make Ambiguous_module (Build.at name)
        (say
           (Printf.sprintf
              "`%s` is a definition of `%s` and the first name of a package's path, so `%s.%s` \
               could name either. Rename the definition, or import the module and write its last \
               name."
              written (Path.show_module module_) written member))
  | No_module { name; written; path_start } ->
      let missing = Printf.sprintf "No module `%s` is imported or exists." written in
      make Unknown_module (Build.at name)
        (say
           (match path_start with
           | Some module_ -> missing ^ " " ^ describe_path_start module_
           | None -> missing))
  | Not_a_generic_parameter { base; written; member; associated } ->
      make Not_a_generic_parameter (Build.at base)
        (say
           (Printf.sprintf
              "`%s.%s` names an associated %s, so `%s` must be a generic parameter here." written
              member
              (match associated with
              | Associated_type -> "type"
              | Associated_capability_set -> "capability set")
              written))
  | Not_a_constant { name; written } ->
      make Not_a_constant (Build.at name)
        (say
           (Printf.sprintf
              "`%s` in a type argument must be a value generic parameter or a constant." written))
  | Null { name; written } ->
      make Null (Build.at name)
        ~fixes:[ { title = say "Write `None`."; edits = [ Build.replace name [ Text "None" ] ] } ]
        (say
           (Printf.sprintf
              "Truss has no `%s`. A value that may be missing is an `Option`, and `None` is its \
               empty case."
              written))
  | Not_generic { value; function_ } ->
      make Not_generic (Build.at value)
        (say
           (Printf.sprintf
              "`%s` is a function without generic parameters, so `[...]` cannot give it type \
               arguments, and a function cannot be indexed."
              function_))
  | Not_a_place { written; inner } ->
      make Not_a_place (Build.at written)
        ~fixes:
          [
            {
              title = say "Remove the keyword.";
              edits = [ Build.delete (Start written) (Start inner) ];
            };
          ]
        (say
           "Only a place, such as a variable, a field, or an element, can take `mut` or `own`. A \
            temporary value is always passed as owned.")
  | Shadowed { name; written; existing } ->
      make Shadowed_name (Build.at name)
        (say
           (Printf.sprintf
              "`%s` is already %s, and a name cannot shadow another. Choose another name." written
              (show_binding existing)))
  | Shadowed_in_branch { branch; block; written } ->
      make Shadowed_name (Build.at branch)
        (say
           (Printf.sprintf
              "Another branch of this `%s` block already binds `%s`, and a name cannot shadow \
               another. Choose another name."
              block written))
  | Prelude_definition { name; written } ->
      make Shadowed_name (Build.at name)
        (say
           (Printf.sprintf
              "`%s` is a name in the prelude, and a name cannot shadow another. Choose another \
               name."
              written))
  | Alternative_bindings { alternative; first; this } ->
      make Alternative_bindings (Build.at alternative)
        (say
           (Printf.sprintf
              "Every alternative of a pattern must bind the same names. The first binds %s, and \
               this one binds %s."
              (show_names first) (show_names this)))
  | Unconstrained_capability_parameter { name; written } ->
      make Unconstrained_capability_parameter (Build.at name)
        (say
           (Printf.sprintf
              "`generic %s` appears only in the function's own `uses`, so no argument gives it \
               capabilities, and it stands for none. Name it in the type of a parameter, as in \
               `visit: (fn() uses generic %s)`."
              written written))
  | Redefined { name; path; first } ->
      make Duplicate_definition
        (match name with Some name -> Build.at name | None -> Before Definition)
        (say
           (Printf.sprintf "`%s` is already defined in %s, so this definition is never used."
              (Path.show path)
              (match first with Some file -> Path.show_file file | None -> "this file")))
  | Module_name_clash { name; written; submodule; module_ } ->
      make Duplicate_definition (Build.at name)
        (say
           (Printf.sprintf
              "`%s` is a module, so no definition of `%s` can be named `%s`: `%s.x` would name \
               either."
              (Path.show_module submodule) (Path.show_module module_) written
              (Path.show_module submodule)))

let make_import ?(fixes = []) code item message =
  {
    Description.code = Resolve code;
    severity = Error;
    location = At item;
    message = say message;
    notes = [];
    fixes;
  }

let describe_import = function
  | Resolve.Intrinsic_module { item } -> make_import Intrinsic_import item restricted_module
  | Missing_module { item; module_; path_start } ->
      let missing = Printf.sprintf "No module `%s` exists." (Path.show_module module_) in
      make_import Unknown_module item
        (match path_start with
        | Some current -> missing ^ " " ^ describe_path_start current
        | None -> missing)
  | Imported_twice { item; last } ->
      make_import Duplicate_import item
        (Printf.sprintf
           "Another `use` already imports a module named `%s`. Write one of them by its full path \
            instead."
           last)
  | Definition_named_like { item; last; module_ } ->
      make_import Duplicate_import item
        (Printf.sprintf
           "`%s` is a definition of `%s`, so this file cannot import a module named `%s`: `%s.x` \
            would name either. Rename the definition, or write the module's full path."
           last (Path.show_module module_) last last)
  | Unused_import { item; module_ } ->
      make_import Unused_import item
        ~fixes:
          [ { title = say "Delete the `use`."; edits = [ Remove_lines { covering = [ item ] } ] } ]
        (Printf.sprintf "Nothing in this file uses `%s`." (Path.show_module module_))
