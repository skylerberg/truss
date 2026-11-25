type version = int * int * int

type manifest =
  | Unexpected_character of char
  | Unclosed_string
  | List_separator_expected
  | Unclosed_list
  | List_item_not_string
  | Unclosed_inline_table
  | Value_expected
  | Line_end_expected
  | Statement_expected
  | Entry_outside_table of string
  | Not_a_string of string
  | Not_a_number of string
  | Unknown_capability of string
  | Not_a_package_name of string
  | Unquoted_owned_name of string
  | Inline_table_dependency of string
  | Text_dependency of string
  | Number_dependency
  | Repeated_table of string
  | Repeated_key of string
  | Unknown_table of string
  | Bad_package_name
  | Bad_truss_version of { toolchain : string }
  | Package_version
  | Unknown_package_key of string
  | Bad_time_limit
  | Unknown_test_key of string
  | Unknown_build_key of string
  | Not_an_x86_64_level
  | Unknown_project_key of string
  | Unnamed_package
  | Dependencies_without_package
  | Neither_table

type lock =
  | Not_a_registry_name of string
  | Version_major_mismatch of { written : string; major : int }
  | Not_a_version of string
  | Not_a_hash of string
  | Not_a_capability of string
  | Unexpected_after_hash
  | Malformed_line
  | Repeated_line of Path.package
  | Missing_header of string

type unavailable =
  | No_registry of { variable : string }
  | Missing_from_registry of { registry : string; name : Path.package; version : version }
  | Changed_in_registry of { registry : string; name : Path.package; version : version }
  | Unwritable of { directory : string }

type load_failure =
  | Unfetched
  | Unavailable of unavailable
  | Unreadable_manifest of { line : int; problem : manifest }
  | Unreadable_lock of { line : int; problem : lock }
  | Misnamed_manifest of Path.package

type selection =
  | No_version of { name : Path.package; wanted_by : Path.package }
  | Cannot_load of { name : Path.package; version : version; failure : load_failure }
  | Two_contents of { name : Path.package; version : version; recorded_by : Path.package }

type difference =
  | Unlisted of { name : Path.package; version : version }
  | Other_version of { name : Path.package; written : version; current : version }
  | Other_hash of { name : Path.package; version : version }
  | Other_holds of {
      name : Path.package;
      written : Grant.capability list;
      current : Grant.capability list;
    }
  | Unused of Path.package

type project_setting = Time_limit | X86_64_level
type unfinished = Todo | Echo
type unshippable = Reached of unfinished | Unfinished_proof
type located = { path : string; line : int; column : int }

type t =
  | Manifest of manifest
  | Lock of lock
  | Selection of selection
  | Stale_lock of difference list
  | Registry_toolchain of {
      name : Path.package;
      version : version;
      truss : string;
      toolchain : string;
    }
  | Project_toolchain of { name : Path.package; truss : string; toolchain : string }
  | Missing_truss_version of { toolchain : string }
  | Nested_project_setting of project_setting
  | Standard_name
  | Name_in_use of { name : Path.package; manifest : string }
  | Owner_named_like of { name : string; other : Path.package }
  | Not_a_project_package of Path.package
  | Self_dependency of Path.package
  | Dependency_cycle of Path.package list
  | Ungranted_capability of { dependency : Path.package; capability : Grant.capability }
  | Unused_dependency of { package : Path.package; dependency : Path.package }
  | Failed_dependency of {
      name : Path.package;
      version : version;
      is_loaded : bool;
      errors : int;
      path : string;
      line : int;
      column : int;
      first : string;
    }
  | Unset_registry of { variable : string }
  | Unregistered_package of Path.package
  | Unregistered_version of { name : Path.package; version : version }
  | Unpublished_dependency of Path.package
  | Ownerless_name of { name : string }
  | Major_mismatch of { name : Path.package; major : int; next : Path.package }
  | Release_not_newer of { name : Path.package; newest : version }
  | Unfinished_code of { unfinished : unfinished; location : located }
  | Unshippable of { unshippable : unshippable; location : located; way : Path.t list }
