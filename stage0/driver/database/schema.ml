type index = { index_name : string; indexed : string; condition : string option }
type table = { name : string; columns : string; without_rowid : bool; indexes : index list }

let index_every_row (index_name, indexed) = { index_name; indexed; condition = None }

let keyed_by_id name columns indexes =
  { name; columns; without_rowid = false; indexes = List.map index_every_row indexes }

let keyed_by_columns name columns indexes =
  { name; columns; without_rowid = true; indexes = List.map index_every_row indexes }

let fact_of_definition ?(has_index_without_value = false) name columns =
  {
    (keyed_by_id name ("definition INTEGER PRIMARY KEY, " ^ columns) []) with
    indexes =
      (if has_index_without_value then
         [
           {
             index_name = name ^ "_without_value";
             indexed = "definition";
             condition = Some "state != 0";
           };
         ]
       else []);
  }

let state = "state INTEGER NOT NULL"

let tables =
  [
    keyed_by_columns "meta" "name TEXT PRIMARY KEY, value BLOB NOT NULL" [];
    keyed_by_columns "package" "name TEXT PRIMARY KEY, id INTEGER NOT NULL" [];
    keyed_by_id "dependency"
      "id INTEGER PRIMARY KEY, package TEXT NOT NULL, position INTEGER NOT NULL, dependency TEXT \
       NOT NULL, capabilities BLOB NOT NULL"
      [ ("dependency_package", "package, position") ];
    keyed_by_id "module"
      "id INTEGER PRIMARY KEY, package TEXT NOT NULL, name TEXT NOT NULL, key BLOB NOT NULL"
      [ ("module_package", "package") ];
    keyed_by_id "file"
      "id INTEGER PRIMARY KEY, package TEXT NOT NULL, module INTEGER NOT NULL, name TEXT NOT NULL, \
       key BLOB NOT NULL, text BLOB NOT NULL"
      [ ("file_module", "module"); ("file_package", "package") ];
    keyed_by_columns "entry"
      "file INTEGER NOT NULL, position INTEGER NOT NULL, module INTEGER NOT NULL, file_name TEXT \
       NOT NULL, name TEXT NOT NULL, kind INTEGER NOT NULL, visibility INTEGER NOT NULL, \
       is_generic INTEGER NOT NULL, PRIMARY KEY (file, position)"
      [ ("entry_name", "module, name, file_name, position") ];
    keyed_by_id "definition"
      "id INTEGER PRIMARY KEY, key BLOB NOT NULL, package TEXT NOT NULL, module INTEGER NOT NULL, \
       path INTEGER NOT NULL, ordinal INTEGER NOT NULL, name TEXT NOT NULL, owner INTEGER, member \
       TEXT, kind INTEGER NOT NULL, visibility INTEGER NOT NULL, is_generic INTEGER NOT NULL, \
       origin INTEGER NOT NULL, supplied_from INTEGER, container INTEGER, file INTEGER, position \
       INTEGER, base INTEGER, stop INTEGER, text_hash INTEGER"
      [
        ("definition_module", "module");
        ("definition_file", "file, position");
        ("definition_member", "owner, member");
        ("definition_path", "path");
        ("definition_container", "container, position");
        ("definition_package", "package, member");
      ];
    keyed_by_id "syntax"
      "definition INTEGER PRIMARY KEY, tree BLOB NOT NULL, spans BLOB NOT NULL, syntax_errors BLOB \
       NOT NULL"
      [];
    keyed_by_columns "import"
      "file INTEGER NOT NULL, position INTEGER NOT NULL, name TEXT NOT NULL, module BLOB NOT NULL, \
       PRIMARY KEY (file, position)"
      [];
    keyed_by_id "impl"
      "definition INTEGER PRIMARY KEY, package TEXT NOT NULL, module INTEGER NOT NULL, position \
       INTEGER NOT NULL, trait INTEGER NOT NULL, type INTEGER NOT NULL, entry BLOB NOT NULL"
      [
        ("impl_trait", "package, trait"); ("impl_type", "package, type"); ("impl_module", "module");
      ];
    keyed_by_id "law_proof"
      "definition INTEGER PRIMARY KEY, package TEXT NOT NULL, module INTEGER NOT NULL, trait \
       INTEGER NOT NULL, law TEXT NOT NULL, type INTEGER NOT NULL"
      [ ("law_proof_name", "package, trait, law, type"); ("law_proof_module", "module") ];
    keyed_by_columns "resolved"
      ("definition INTEGER NOT NULL, section INTEGER NOT NULL, " ^ state
     ^ ", names BLOB, brackets BLOB, holes BLOB, PRIMARY KEY (definition, section)")
      [];
    fact_of_definition "header" (state ^ ", value BLOB");
    fact_of_definition "trait_header" (state ^ ", value BLOB");
    fact_of_definition "interface" (state ^ ", value BLOB, named BLOB, scope BLOB");
    fact_of_definition "signature_check" state;
    keyed_by_id "type_facts"
      ("path INTEGER PRIMARY KEY, " ^ state
     ^ ", generics BLOB, copyable BLOB, plain BLOB, view BLOB, holds_function BLOB, contains BLOB")
      [];
    keyed_by_id "constant_value" ("path INTEGER PRIMARY KEY, " ^ state ^ ", value TEXT") [];
    keyed_by_id "derived_interface" ("path INTEGER PRIMARY KEY, " ^ state ^ ", value BLOB") [];
    fact_of_definition "contract" (state ^ ", form BLOB");
    fact_of_definition ~has_index_without_value:true "body"
      (state
     ^ ", form BLOB, tables BLOB, requires_run_forever INTEGER, places_without_keyword BLOB, \
        mode_keywords BLOB");
    fact_of_definition "body_mir" (state ^ ", graph BLOB");
    fact_of_definition "contract_mir" (state ^ ", graph BLOB");
    keyed_by_id "generated_mir"
      ("path INTEGER PRIMARY KEY, " ^ state ^ ", body BLOB, contract BLOB")
      [];
    keyed_by_id "call_node"
      ("path INTEGER PRIMARY KEY, " ^ state ^ ", kind INTEGER, callees BLOB")
      [];
    keyed_by_id "recursion_group"
      ("path INTEGER PRIMARY KEY, " ^ state ^ ", representative INTEGER, members BLOB")
      [ ("recursion_group_representative", "representative") ];
    fact_of_definition "usage_check" state;
    fact_of_definition "ownership" (state ^ ", must_be_disjoint BLOB");
    fact_of_definition ~has_index_without_value:true "proof" (state ^ ", value BLOB");
    keyed_by_columns "hole"
      "definition INTEGER NOT NULL, position INTEGER NOT NULL, home INTEGER NOT NULL, start \
       INTEGER NOT NULL, stop INTEGER NOT NULL, PRIMARY KEY (definition, position)"
      [];
    keyed_by_columns "verdict"
      "definition INTEGER NOT NULL, position INTEGER NOT NULL, code TEXT NOT NULL, start INTEGER \
       NOT NULL, stop INTEGER NOT NULL, shows TEXT NOT NULL, proven INTEGER NOT NULL, \
       trusts_compiled_code INTEGER NOT NULL, failure BLOB, cited INTEGER, cited_start INTEGER, \
       cited_stop INTEGER, PRIMARY KEY (definition, position)"
      [];
    keyed_by_id "grant"
      ("dependency INTEGER PRIMARY KEY, " ^ state ^ ", capabilities BLOB, unknown BLOB")
      [];
    keyed_by_id "dependency_use"
      ("dependency INTEGER PRIMARY KEY, " ^ state ^ ", is_used INTEGER")
      [];
    keyed_by_id "item"
      "id INTEGER PRIMARY KEY, definition INTEGER, key BLOB NOT NULL, label TEXT NOT NULL"
      [ ("item_definition", "definition") ];
    keyed_by_id "lowered"
      ("item INTEGER PRIMARY KEY, " ^ state ^ ", code BLOB, is_evaluated INTEGER, sites BLOB")
      [];
    keyed_by_id "test_key" ("item INTEGER PRIMARY KEY, " ^ state ^ ", key BLOB") [];
    keyed_by_id "evaluation" ("item INTEGER PRIMARY KEY, " ^ state ^ ", value BLOB") [];
    keyed_by_columns "unit"
      ("item INTEGER NOT NULL, profile INTEGER NOT NULL, " ^ state
     ^ ", text_hash BLOB, PRIMARY KEY (item, profile)")
      [];
    keyed_by_columns "diagnostic"
      "stage INTEGER NOT NULL, unit INTEGER NOT NULL, position INTEGER NOT NULL, package TEXT NOT \
       NULL, definition INTEGER, file INTEGER, severity TEXT NOT NULL, code TEXT NOT NULL, start \
       INTEGER NOT NULL, stop INTEGER NOT NULL, message TEXT NOT NULL, detail BLOB NOT NULL, \
       PRIMARY KEY (stage, unit, position)"
      [
        ("diagnostic_definition", "definition");
        ("diagnostic_file", "file");
        ("diagnostic_package", "package, severity");
      ];
    keyed_by_columns "edge"
      "source_kind INTEGER NOT NULL, source INTEGER NOT NULL, target_kind INTEGER NOT NULL, target \
       INTEGER NOT NULL, name TEXT NOT NULL, markers INTEGER NOT NULL, PRIMARY KEY (source_kind, \
       source, target_kind, target, name)"
      [ ("edge_target", "target_kind, target, name") ];
    keyed_by_columns "stale" "stage INTEGER NOT NULL, id INTEGER NOT NULL, PRIMARY KEY (stage, id)"
      [];
  ]

let make_script ~schema =
  String.concat "\n"
    (List.concat_map
       (fun { name; columns; without_rowid; indexes } ->
         Printf.sprintf "CREATE TABLE %s.\"%s\" (%s)%s;" schema name columns
           (if without_rowid then " WITHOUT ROWID" else "")
         :: List.map
              (fun { index_name; indexed; condition } ->
                Printf.sprintf "CREATE INDEX %s.\"%s\" ON \"%s\" (%s)%s;" schema index_name name
                  indexed
                  (match condition with Some condition -> " WHERE " ^ condition | None -> ""))
              indexes)
       tables)

let list_table_names () = List.map (fun (table : table) -> table.name) tables
