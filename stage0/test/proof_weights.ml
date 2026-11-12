(* What each module of the standard library costs to prove, for dealing the modules out to the
   processes that prove them. `TRUSS_PROOF_WEIGHTS=all ./standard_library_tests.exe` prints this file's
   definitions again, and a list of module names in place of `all` measures those modules only. *)

let weights =
  [
    ("standard::arguments", 167);
    ("standard::base64", 102);
    ("standard::binary", 68);
    ("standard::capabilities", 5);
    ("standard::checksum", 5);
    ("standard::collections", 2);
    ("standard::collections::bit_set", 421);
    ("standard::collections::deque", 127);
    ("standard::collections::heap", 46);
    ("standard::collections::lru_cache", 273);
    ("standard::collections::sorted_map", 536);
    ("standard::collections::sorted_set", 506);
    ("standard::compression", 933);
    ("standard::console", 41);
    ("standard::core", 23);
    ("standard::core::range", 5);
    ("standard::cryptography", 3298);
    ("standard::cryptography::elliptic", 247);
    ("standard::cryptography::modular", 201);
    ("standard::csv", 45);
    ("standard::cursors", 4);
    ("standard::environment", 68);
    ("standard::files", 893);
    ("standard::growth", 2);
    ("standard::hex", 21);
    ("standard::html", 102);
    ("standard::http", 524);
    ("standard::json", 1513);
    ("standard::list", 104);
    ("standard::list::array", 43);
    ("standard::list::array_views", 42);
    ("standard::list::slice", 723);
    ("standard::list::views", 50);
    ("standard::log", 7);
    ("standard::map", 822);
    ("standard::math", 2280);
    ("standard::network", 98);
    ("standard::numbers::float_math", 68);
    ("standard::numbers::floats", 7);
    ("standard::numbers::integer_arithmetic", 106);
    ("standard::numbers::integer_bits", 42);
    ("standard::numbers::integer_text", 24);
    ("standard::numbers::integers", 523);
    ("standard::numbers::signed", 38);
    ("standard::numbers::unsigned", 40);
    ("standard::option", 1);
    ("standard::processes", 12);
    ("standard::random", 61);
    ("standard::regex", 197);
    ("standard::result", 1);
    ("standard::serialization", 28);
    ("standard::set", 320);
    ("standard::simulation", 1911);
    ("standard::specification", 3);
    ("standard::streams", 33);
    ("standard::system::calls", 7);
    ("standard::system::clock", 1);
    ("standard::system::console", 1);
    ("standard::system::directories", 3);
    ("standard::system::environment", 5);
    ("standard::system::file_read", 1);
    ("standard::system::file_write", 1);
    ("standard::system::handles", 3);
    ("standard::system::lines", 2);
    ("standard::system::log", 1);
    ("standard::system::network_client", 1);
    ("standard::system::network_server", 1);
    ("standard::system::processes", 19);
    ("standard::system::random", 1);
    ("standard::system::signals", 1);
    ("standard::system::sockets", 11);
    ("standard::system::tasks", 1);
    ("standard::system::terminals", 4);
    ("standard::system::test_runner", 28);
    ("standard::tasks", 74);
    ("standard::text", 152);
    ("standard::text::character", 21);
    ("standard::text::grapheme_breaks", 1);
    ("standard::text::string_slice", 197);
    ("standard::text::string_views", 30);
    ("standard::text::unicode_data", 184);
    ("standard::text::unicode_tables", 296);
    ("standard::time", 553);
    ("standard::toml", 1453);
    ("standard::unicode", 18);
    ("standard::url", 102);
    ("standard::uuid", 31);
    ("standard::writing", 5);
  ]

let letters_for_one = 43
