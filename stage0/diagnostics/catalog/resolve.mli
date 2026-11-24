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
