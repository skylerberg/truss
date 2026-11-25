module Problem = Problem

let show_version ((major, minor, patch) : Problem.version) =
  Printf.sprintf "%d.%d.%d" major minor patch

let show = Path.show_package

let name_expected =
  "a `lower_snake_case` name, or an owner and a name joined by `.`, such as `weather` or \
   `acme.geometry`"

let describe_manifest_problem : Problem.manifest -> string = function
  | Unexpected_character character -> Printf.sprintf "`%c` cannot be written here." character
  | Unclosed_string -> "This string is not closed on its line."
  | List_separator_expected -> "Expected `,` or `]` after a list's item."
  | Unclosed_list -> "This list is not closed with `]`."
  | List_item_not_string -> "A list holds strings in quotes, with `,` between them."
  | Unclosed_inline_table -> "This table is not closed with `}`."
  | Value_expected ->
      "Expected a value after `=`: a string in quotes, a whole number, or a list in brackets."
  | Line_end_expected -> "Expected the line to end here."
  | Statement_expected ->
      "Expected a table, such as `[package]`, or a line of the form `key = value`."
  | Entry_outside_table key ->
      Printf.sprintf "`%s` is in no table. A manifest starts with a table, such as `[package]`." key
  | Not_a_string key -> Printf.sprintf "`%s` is a string in quotes." key
  | Not_a_number key -> Printf.sprintf "`%s` is a whole number." key
  | Unknown_capability written ->
      Printf.sprintf
        "`%s` names no capability. A grant names a capability of the prelude by its name, such as \
         `Clock`, and any other by its full path."
        written
  | Not_a_package_name key ->
      Printf.sprintf "`%s` is not a package's name, which is %s." key name_expected
  | Unquoted_owned_name key ->
      Printf.sprintf "A name with `.` is written in quotes: `\"%s\" = []`." key
  | Inline_table_dependency key ->
      Printf.sprintf
        "A dependency's entry is the list of capabilities it is granted, as in `%s = []`. A \
         manifest holds no versions: `truss add` writes them in `truss.lock`."
        key
  | Text_dependency key ->
      Printf.sprintf
        "A dependency's entry is the list of capabilities it is granted, as in `%s = []`, not a \
         version. `truss add` writes versions in `truss.lock`."
        key
  | Number_dependency -> "A dependency's entry is the list of capabilities it is granted."
  | Repeated_table name -> Printf.sprintf "The table `[%s]` is already written above." name
  | Repeated_key key -> Printf.sprintf "`%s` is already written above." key
  | Unknown_table name ->
      Printf.sprintf
        "A manifest has no table `[%s]`. Its tables are `[package]`, `[dependencies]`, \
         `[project]`, `[test]`, and `[build]`."
        name
  | Bad_package_name -> Printf.sprintf "A package's name is %s." name_expected
  | Bad_truss_version { toolchain } ->
      Printf.sprintf
        "`truss` is the version of Truss the package is written for, as two numbers, such as \
         `\"%s\"`."
        toolchain
  | Package_version ->
      "A manifest holds no version. The registry gives a package its version when it is published. \
       Delete this line."
  | Unknown_package_key key ->
      Printf.sprintf "`[package]` has no key `%s`. Its keys are `name` and `truss`." key
  | Bad_time_limit -> "`time_limit` is a whole number of seconds, more than 0."
  | Unknown_test_key key -> Printf.sprintf "`[test]` has no key `%s`. Its key is `time_limit`." key
  | Unknown_build_key key ->
      Printf.sprintf "`[build]` has no key `%s`. Its key is `x86_64_level`." key
  | Not_an_x86_64_level ->
      Printf.sprintf "`x86_64_level` is the level of x86-64 CPU that programs are built for: %s."
        (String.concat ", "
           (List.map
              (fun level -> Printf.sprintf "`%S`" (X86_64_level.show level))
              X86_64_level.all))
  | Unknown_project_key key -> Printf.sprintf "`[project]` has no key `%s`." key
  | Unnamed_package -> "`[package]` names its package, with `name = \"...\"` under it."
  | Dependencies_without_package ->
      "`[dependencies]` are a package's, and this manifest has no `[package]`."
  | Neither_table -> "A manifest has a `[package]` table, a `[project]` table, or both."

let describe_lock_problem : Problem.lock -> string = function
  | Not_a_registry_name written ->
      Printf.sprintf
        "`%s` is not a registry package's name, which is an owner and a name joined by `.`." written
  | Version_major_mismatch { written; major } ->
      Printf.sprintf
        "A version of `%s` starts with %d, the number at the end of its name, or 1 for a name \
         without one."
        written major
  | Not_a_version written ->
      Printf.sprintf "`%s` is not a version, which is three numbers, such as 1.4.2." written
  | Not_a_hash hash -> Printf.sprintf "`%s` is not a hash, which is 64 hexadecimal digits." hash
  | Not_a_capability written ->
      Printf.sprintf
        "`%s` is not a capability's name or full path. The capabilities after `holds` have `, ` \
         between them."
        written
  | Unexpected_after_hash ->
      "After a package's hash comes nothing, or `holds` and the capabilities it holds."
  | Malformed_line -> "A line is a package's name, its version, and its hash."
  | Repeated_line name -> Printf.sprintf "`%s` already has a line above." (show name)
  | Missing_header header -> Printf.sprintf "A lock file starts with the line `%s`." header

let describe_load_failure : Problem.load_failure -> string = function
  | Unfetched -> "its files are not fetched yet"
  | Unavailable reason -> reason
  | Unreadable_manifest { line; problem } ->
      Printf.sprintf "its manifest cannot be read: line %d: %s" line
        (describe_manifest_problem problem)
  | Unreadable_lock { line; problem } ->
      Printf.sprintf "its lock file cannot be read: line %d: %s" line
        (describe_lock_problem problem)
  | Misnamed_manifest name ->
      Printf.sprintf "its manifest does not name the package `%s`" (show name)

let describe_selection_problem : Problem.selection -> string = function
  | No_version { name; wanted_by } ->
      Printf.sprintf
        "`%s` depends on `%s`, which is not a package of this project and has no line in \
         `truss.lock`. Run `truss add %s`."
        (show wanted_by) (show name) (show name)
  | Cannot_load { name; version; failure } ->
      Printf.sprintf "`truss.lock` names `%s` %s, whose files are not in the store, and %s."
        (show name) (show_version version) (describe_load_failure failure)
  | Two_contents { name; version; recorded_by } ->
      Printf.sprintf
        "`%s` was published with `%s` %s under another hash than the build has for it. One version \
         has one content, so one of the two is wrong."
        (show recorded_by) (show name) (show_version version)

let show_capabilities = function
  | [] -> "nothing"
  | held -> String.concat ", " (List.map Grant.show_capability held)

let describe_difference : Problem.difference -> string = function
  | Unlisted { name; version } ->
      Printf.sprintf "`%s` %s is in the build and has no line." (show name) (show_version version)
  | Other_version { name; written; current } ->
      Printf.sprintf "`%s` is %s, and a package of the build was published with %s." (show name)
        (show_version written) (show_version current)
  | Other_hash { name; version } ->
      Printf.sprintf "`%s` %s has another hash." (show name) (show_version version)
  | Other_holds { name; written; current } ->
      Printf.sprintf "`%s` is said to hold %s, and the manifests grant it %s." (show name)
        (show_capabilities written) (show_capabilities current)
  | Unused name -> Printf.sprintf "Nothing in the build uses `%s`." (show name)

let describe : Problem.t -> string = function
  | Manifest problem -> describe_manifest_problem problem
  | Lock problem -> describe_lock_problem problem
  | Selection problem -> describe_selection_problem problem
  | Stale_lock differences ->
      Printf.sprintf "This is not the lock file the manifests give. %sRun `truss check --fix`."
        (String.concat ""
           (List.map (fun difference -> describe_difference difference ^ " ") differences))
  | Registry_toolchain { name; version; truss; toolchain } ->
      Printf.sprintf "`%s` %s is written for Truss %s, and this toolchain is Truss %s." (show name)
        (show_version version) truss toolchain
  | Project_toolchain { name; truss; toolchain } ->
      Printf.sprintf "`%s` is written for Truss %s, and this toolchain is Truss %s." (show name)
        truss toolchain
  | Missing_truss_version { toolchain } ->
      Printf.sprintf
        "`[package]` needs `truss = \"%s\"`, the version of Truss the package is written for."
        toolchain
  | Nested_project_setting setting ->
      let owner, table =
        match setting with
        | Time_limit -> ("A test's time limit", "test")
        | X86_64_level -> ("A build's x86-64 level", "build")
      in
      Printf.sprintf
        "%s is its project's. Write `[%s]` in the project's manifest, `truss.toml` at its root."
        owner table
  | Standard_name -> "The package name `standard` is the standard library's."
  | Name_in_use { name; manifest } ->
      Printf.sprintf "The package name `%s` is already used by %s." (show name) manifest
  | Owner_named_like { name; other } ->
      Printf.sprintf
        "The package name `%s` is the owner in `%s`, so a path that starts with it could be read \
         two ways. Give one of them another name."
        name (show other)
  | Not_a_project_package name ->
      Printf.sprintf "`%s` is not a package of this project." (show name)
  | Self_dependency name -> Printf.sprintf "`%s` cannot depend on itself." (show name)
  | Dependency_cycle cycle ->
      Printf.sprintf "Packages cannot depend on each other in a cycle: %s."
        (String.concat " -> "
           (List.map (fun package -> Printf.sprintf "`%s`" (show package)) cycle))
  | Ungranted_capability { dependency; capability } ->
      Printf.sprintf
        "`%s`, in the entry for `%s`, names no capability. A grant names a capability of the \
         prelude by its name, such as `Clock`, and any other by its full path."
        (Grant.show_capability capability)
        (show dependency)
  | Unused_dependency { package; dependency } ->
      Printf.sprintf "Nothing in `%s` uses `%s`. Delete its entry." (show package) (show dependency)
  | Failed_dependency { name; version; is_loaded; errors; path; line; column; first } ->
      Printf.sprintf "`%s` %s does not check %s. It has %d %s; the first is at %s:%d:%d: %s"
        (show name) (show_version version)
        (if is_loaded then "with this toolchain" else "against this project's packages")
        errors
        (if errors = 1 then "error" else "errors")
        path line column first
