type entry = Space | Spelled of string | Opening_quote of string

let table =
  [
    (0x00A0, Space);
    (0x1680, Space);
    (0x202F, Space);
    (0x205F, Space);
    (0x3000, Space);
    (0x201C, Opening_quote "\u{201D}");
    (0x2018, Opening_quote "\u{2019}");
    (0xFF08, Spelled "(");
    (0xFF09, Spelled ")");
    (0xFF3B, Spelled "[");
    (0xFF3D, Spelled "]");
    (0xFF5B, Spelled "{");
    (0xFF5D, Spelled "}");
    (0xFF0C, Spelled ",");
    (0xFF1A, Spelled ":");
    (0xFF1D, Spelled "=");
    (0x2013, Spelled "-");
    (0x2014, Spelled "-");
    (0x2264, Spelled "<=");
    (0x2265, Spelled ">=");
    (0x2260, Spelled "!=");
    (0x2192, Spelled "->");
    (0x21D2, Spelled "=>");
    (0x2200, Spelled "forall");
    (0x2203, Spelled "exists");
  ]

let find code_point : entry option =
  if code_point >= 0x2000 && code_point <= 0x200A then Some Space
  else List.assoc_opt code_point table
