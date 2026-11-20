import os
import random
import sys

snippets = [
    ";", "// note", "/* block */", "# hash", "#[derive(Debug)]", "'a'", "'x", "`text ${a}`", "b'z'",
    "++", "--", "**", ":=", "|>", "...", "..<", "<>", "===", "!==", "x++", "a ?: b", "a ?? b", "c ? d : e",
    "f\"value {x}\"", "r\"raw\"", "r#\"hash\"#", "@\"verbatim\"", "$\"dollar\"", "b\"bytes\"",
    "elif x {", "let mut y = 1", "&x", "&mut y", "|x| x + 1", "|| 3", "Point { x: 1 }", "Vec<Int64>",
    "List<String>", "parse::<Int64>(t)", "x as UInt8", "println!(\"hi\")", "vec![1, 2]", "todo!()",
    "loop {", "const k: Int64 = 1", "static s: Int64 = 2", "impl<T> Show for Box", "Shape::Circle",
    "items.it { it }", "(1, 2)", "pair.0", "\u201cquoted\u201d", "\uff08", "\u2014", "\u00a0", "\u2264",
    "\u2192", "\u200b", "\u202e", "\"\\x41\"", "\"\\u0041\"", "\"\\(name)\"", "\"\\'\"", "\"\\q\"",
    "\"unterminated", "\"\"\"", "0x", "1e", "1_", "08", "0X1F", "12u8", "3.f", ".5", "1.", "fooBar",
    "Foo_Bar", "_name", "name_", "a__b", "\u00e9t\u00e9", "fn f(self) {", "fn ( {", "type T = ", "{", "}",
    "(", ")", "[", "]", "match x { 1 => a, 2 => b }", "x is !y", "a < b < c", "a && b || c", "a & b | c",
    "1 << 2 + 3", "-forall x in s => x", "items[..2,]", "items[1..,2]", "for i in 0.. {", "let x = {",
]


def boundary(text, position):
    while 0 < position < len(text) and (ord(text[position]) & 0xC0) == 0x80:
        position -= 1
    return position


def mutate(text, generator):
    encoded = text.encode()
    choice = generator.randrange(4)
    if not encoded:
        return generator.choice(snippets).encode()
    position = generator.randrange(len(encoded) + 1)
    while 0 < position < len(encoded) and (encoded[position] & 0xC0) == 0x80:
        position -= 1
    if choice == 0:
        stop = position + 1
        while stop < len(encoded) and (encoded[stop] & 0xC0) == 0x80:
            stop += 1
        return encoded[:position] + encoded[stop:]
    if choice == 1:
        return encoded[:position]
    snippet = generator.choice(snippets).encode()
    if choice == 2:
        line_start = encoded.rfind(b"\n", 0, position) + 1
        return encoded[:line_start] + snippet + b"\n" + encoded[line_start:]
    return encoded[:position] + snippet + encoded[position:]


def main():
    corpus_path, output_directory, count = sys.argv[1], sys.argv[2], int(sys.argv[3])
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 20261119
    stacked = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    os.makedirs(output_directory, exist_ok=True)
    generator = random.Random(seed)
    paths = [line.strip() for line in open(corpus_path) if line.strip()]
    written = []
    for index, path in enumerate(paths):
        text = open(path, encoding="utf-8").read()
        for variant in range(count):
            mutated = text.encode()
            for _ in range(stacked):
                mutated = mutate(mutated.decode("utf-8", errors="ignore"), generator)
            try:
                mutated.decode("utf-8")
            except UnicodeDecodeError:
                continue
            name = os.path.join(output_directory, "%05d_%d.truss" % (index, variant))
            with open(name, "wb") as output:
                output.write(mutated)
            written.append(name)
    with open(os.path.join(output_directory, "corpus.txt"), "w") as listing:
        listing.write("\n".join(written) + "\n")


main()
