type expected = In_module of Path.module_ | Type_here | Value_here | Constant_in_module_here

type binding =
  | Local
  | Parameter
  | Generic_parameter
  | Generic_parameter_here
  | Field
  | Law_parameter
  | Module_definition of Language.Definition_kind.t
  | Prelude_name

type associated = Associated_type | Associated_capability_set

type t =
  | Unknown of {
      name : Core.origin;
      written : string;
      expected : expected;
      candidates : string list;
    }
  | Unknown_value_or_module of { name : Core.origin; written : string; candidates : string list }
  | Bare_variant of {
      name : Core.origin;
      written : string;
      owner : string;
      other_owners : string list;
    }
  | Capability_parameter_without_generic of { name : Core.origin; written : string }
  | Unknown_generic_capability of { reference : Core.origin; written : string }
  | Loop_element of { name : Core.origin; written : string }
  | Not_visible of { name : Core.origin; path : Path.t; visibility : Language.Visibility.t }
  | Intrinsic_import of { name : Core.origin }
  | Import_or_package of {
      name : Core.origin;
      written : string;
      imported : Path.module_;
      package : Path.module_;
    }
  | Definition_or_package of {
      name : Core.origin;
      written : string;
      module_ : Path.module_;
      member : string;
    }
  | No_module of { name : Core.origin; written : string; path_start : Path.module_ option }
  | Not_a_generic_parameter of {
      base : Core.origin;
      written : string;
      member : string;
      associated : associated;
    }
  | Not_a_constant of { name : Core.origin; written : string }
  | Null of { name : Core.origin; written : string }
  | Not_generic of { value : Core.origin; function_ : string }
  | Not_a_place of { written : Core.origin; inner : Core.origin }
  | Shadowed of { name : Core.origin; written : string; existing : binding }
  | Shadowed_in_branch of { branch : Core.origin; block : string; written : string }
  | Prelude_definition of { name : Core.origin; written : string }
  | Alternative_bindings of { alternative : Core.origin; first : string list; this : string list }
  | Unconstrained_capability_parameter of { name : Core.origin; written : string }
  | Redefined of { name : Core.origin option; path : Path.t; first : Path.file option }
  | Module_name_clash of {
      name : Core.origin;
      written : string;
      submodule : Path.module_;
      module_ : Path.module_;
    }

type import =
  | Intrinsic_module of { item : Source.span }
  | Missing_module of {
      item : Source.span;
      module_ : Path.module_;
      path_start : Path.module_ option;
    }
  | Imported_twice of { item : Source.span; last : string }
  | Definition_named_like of { item : Source.span; last : string; module_ : Path.module_ }
  | Unused_import of { item : Source.span; module_ : Path.module_ }

let make ?(fixes = []) code location message : Nodes.description =
  { code = Resolve code; severity = Error; location; message; notes = []; fixes }

let say text : _ Description.piece list = [ Text text ]

let show_expected = function
  | In_module module_ -> Printf.sprintf "in `%s`" (Path.show_module module_)
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
  | Local -> "a local here"
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

let describe = function
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
           (Printf.sprintf "%s is already defined in %s, so this definition is never used."
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
  | Intrinsic_module { item } -> make_import Intrinsic_import item restricted_module
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

let name = Build.example "name"
let inner = Build.example "inner"
let app_main : Path.module_ = { package = { owner = None; name = "app" }; modules = [ "main" ] }
let core_module = Path.make_standard_module [ "core" ]
let example_path = Path.Top { module_ = app_main; name = "helper" }
let item = Source.make_span 0 12

let list_examples : Diagnostic.Code.resolve -> t list = function
  | Unknown_name ->
      [
        Unknown { name; written = "lenght"; expected = Value_here; candidates = [ "length" ] };
        Unknown { name; written = "Pont"; expected = Type_here; candidates = [] };
        Unknown { name; written = "helper"; expected = In_module app_main; candidates = [] };
        Unknown { name; written = "limit"; expected = Constant_in_module_here; candidates = [] };
        Unknown_value_or_module { name; written = "lenght"; candidates = [ "length" ] };
        Bare_variant { name; written = "Some"; owner = "Option"; other_owners = [] };
        Capability_parameter_without_generic { name; written = "Granted" };
        Unknown_generic_capability { reference = name; written = "Granted" };
        Loop_element { name; written = "item" };
      ]
  | Not_visible -> [ Not_visible { name; path = example_path; visibility = Private } ]
  | Ambiguous_module ->
      [
        Import_or_package { name; written = "core"; imported = app_main; package = core_module };
        Definition_or_package { name; written = "core"; module_ = app_main; member = "max" };
      ]
  | Duplicate_import -> []
  | Unused_import -> []
  | Intrinsic_import -> [ Intrinsic_import { name } ]
  | Unknown_module ->
      [
        No_module { name; written = "lists"; path_start = None };
        No_module { name; written = "lists"; path_start = Some app_main };
      ]
  | Shadowed_name ->
      [
        Shadowed { name; written = "count"; existing = Parameter };
        Shadowed_in_branch { branch = name; block = "parallel"; written = "count" };
        Prelude_definition { name; written = "Option" };
      ]
  | Duplicate_definition ->
      [
        Redefined { name = Some name; path = example_path; first = None };
        Module_name_clash { name; written = "lists"; submodule = app_main; module_ = app_main };
      ]
  | Not_a_place -> [ Not_a_place { written = name; inner } ]
  | Not_generic -> [ Not_generic { value = name; function_ = "double" } ]
  | Not_a_constant -> [ Not_a_constant { name; written = "size" } ]
  | Alternative_bindings ->
      [ Alternative_bindings { alternative = name; first = [ "x" ]; this = [] } ]
  | Not_a_generic_parameter ->
      [
        Not_a_generic_parameter
          { base = name; written = "Item"; member = "Output"; associated = Associated_type };
      ]
  | Unconstrained_capability_parameter ->
      [ Unconstrained_capability_parameter { name; written = "Granted" } ]
  | Null -> [ Null { name; written = "null" } ]

let list_import_examples : Diagnostic.Code.resolve -> import list = function
  | Intrinsic_import -> [ Intrinsic_module { item } ]
  | Unknown_module -> [ Missing_module { item; module_ = app_main; path_start = Some app_main } ]
  | Duplicate_import ->
      [
        Imported_twice { item; last = "lists" };
        Definition_named_like { item; last = "lists"; module_ = app_main };
      ]
  | Unused_import -> [ Unused_import { item; module_ = app_main } ]
  | _ -> []
