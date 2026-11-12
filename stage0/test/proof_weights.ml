(* What each module of the standard library costs to prove, for dealing the modules out to the
   jobs that prove them. `TRUSS_PROOF_WEIGHTS=all ./standard_library_tests.exe` prints this file's
   definitions again, and a list of module names in place of `all` measures those modules only. *)

let weights =
  [
    ("standard::arguments", 634);
    ("standard::base64", 661);
    ("standard::binary", 427);
    ("standard::capabilities", 9);
    ("standard::checksum", 62);
    ("standard::collections", 61);
    ("standard::collections::bit_set", 2405);
    ("standard::collections::deque", 756);
    ("standard::collections::heap", 252);
    ("standard::collections::lru_cache", 307);
    ("standard::collections::sorted_map", 1526);
    ("standard::collections::sorted_set", 1317);
    ("standard::compression", 1171);
    ("standard::console", 108);
    ("standard::core", 32);
    ("standard::core::range", 30);
    ("standard::cryptography", 9004);
    ("standard::csv", 271);
    ("standard::cursors", 11);
    ("standard::environment", 134);
    ("standard::files", 2748);
    ("standard::growth", 18);
    ("standard::hex", 163);
    ("standard::html", 103);
    ("standard::http", 883);
    ("standard::json", 2708);
    ("standard::list", 1021);
    ("standard::list::array", 328);
    ("standard::list::array_views", 587);
    ("standard::list::slice", 3596);
    ("standard::list::views", 639);
    ("standard::log", 19);
    ("standard::map", 1465);
    ("standard::math", 5899);
    ("standard::network", 987);
    ("standard::numbers::float_math", 942);
    ("standard::numbers::floats", 64);
    ("standard::numbers::integer_arithmetic", 2244);
    ("standard::numbers::integer_bits", 350);
    ("standard::numbers::integer_text", 313);
    ("standard::numbers::integers", 872);
    ("standard::numbers::signed", 486);
    ("standard::numbers::unsigned", 380);
    ("standard::option", 54);
    ("standard::processes", 96);
    ("standard::random", 365);
    ("standard::regex", 1135);
    ("standard::result", 34);
    ("standard::serialization", 397);
    ("standard::set", 997);
    ("standard::simulation", 4907);
    ("standard::specification", 1);
    ("standard::streams", 257);
    ("standard::system::calls", 208);
    ("standard::system::clock", 10);
    ("standard::system::console", 4);
    ("standard::system::directories", 66);
    ("standard::system::environment", 22);
    ("standard::system::file_read", 7);
    ("standard::system::file_write", 8);
    ("standard::system::handles", 43);
    ("standard::system::lines", 58);
    ("standard::system::log", 2);
    ("standard::system::network_client", 1);
    ("standard::system::network_server", 1);
    ("standard::system::processes", 161);
    ("standard::system::random", 1);
    ("standard::system::signals", 11);
    ("standard::system::sockets", 174);
    ("standard::system::tasks", 1);
    ("standard::system::terminals", 41);
    ("standard::system::test_runner", 257);
    ("standard::tasks", 325);
    ("standard::text", 1051);
    ("standard::text::character", 359);
    ("standard::text::grapheme_breaks", 30);
    ("standard::text::string_slice", 2275);
    ("standard::text::string_views", 340);
    ("standard::text::unicode_data", 339);
    ("standard::text::unicode_tables", 926);
    ("standard::time", 4013);
    ("standard::toml", 1481);
    ("standard::unicode", 186);
    ("standard::url", 939);
    ("standard::uuid", 138);
    ("standard::writing", 122);
  ]

let letters_for_one = 11
