#!/usr/bin/env python3
import argparse
import json
import posixpath
import re
import subprocess
from collections import Counter
from dataclasses import dataclass, field

SECTION_BEGIN = "<!-- change summary -->"
SECTION_END = "<!-- /change summary -->"

PARTS = [
    "Source",
    "Tests",
    "Fixtures",
    "Standard library",
    "Experimental",
    "Documents",
    "Other",
]

DUNE_TOKEN = re.compile(r'[()]|"(?:[^"\\]|\\.)*"|[^\s()"]+')


@dataclass(frozen=True)
class Library:
    name: str
    directory: str
    includes_subdirectories: bool
    dependencies: frozenset[str]


@dataclass
class LineCount:
    added: int = 0
    removed: int = 0

    def add(self, other: "LineCount") -> None:
        self.added += other.added
        self.removed += other.removed


@dataclass
class LibraryRow:
    name: str
    note: str = ""
    lines: LineCount = field(default_factory=LineCount)


def run(command: list[str], stdin: bytes | None = None) -> str:
    return subprocess.run(command, input=stdin, stdout=subprocess.PIPE, check=True).stdout.decode()


def find_part(path: str) -> str:
    if path.startswith("experimental/"):
        return "Experimental"
    if path.endswith(".md"):
        return "Documents"
    if path.startswith("stage0/test/"):
        is_test_code = path.endswith((".ml", ".mli")) or posixpath.basename(path) == "dune"
        return "Tests" if is_test_code else "Fixtures"
    if path.startswith("stage0/"):
        return "Source"
    if path.startswith("standard/"):
        return "Standard library"
    return "Other"


def parse_line_count(numstat_field: str) -> int:
    return 0 if numstat_field == "-" else int(numstat_field)


def list_line_counts(merge_base: str, head: str) -> list[tuple[str, LineCount]]:
    numstat = run(["git", "diff", "--numstat", "-z", "--no-renames", merge_base, head])
    counts = []
    for record in filter(None, numstat.split("\0")):
        added, removed, path = record.split("\t", 2)
        counts.append((path, LineCount(parse_line_count(added), parse_line_count(removed))))
    return counts


def list_renamed_files(merge_base: str, head: str) -> list[tuple[str, str]]:
    name_status = run(["git", "diff", "--name-status", "-z", "-M", merge_base, head, "--", "stage0"])
    fields = name_status.split("\0")
    renamed = []
    index = 0
    while index < len(fields) and fields[index]:
        if fields[index].startswith("R"):
            renamed.append((fields[index + 1], fields[index + 2]))
            index += 3
        else:
            index += 2
    return renamed


def parse_dune(text: str) -> list:
    stack: list[list] = [[]]
    for token in DUNE_TOKEN.findall(text):
        if token == "(":
            stack.append([])
        elif token == ")":
            completed = stack.pop()
            stack[-1].append(completed)
        else:
            stack[-1].append(token)
    return stack[0]


def read_dependency(entry) -> str | None:
    if isinstance(entry, str):
        return entry
    if entry[:1] == ["re_export"]:
        return entry[1]
    return None


def read_libraries(revision: str) -> dict[str, Library]:
    tree = run(["git", "ls-tree", "-r", "-z", "--name-only", revision, "--", "stage0"])
    libraries = {}
    for path in filter(None, tree.split("\0")):
        if posixpath.basename(path) != "dune":
            continue
        dune_file = parse_dune(run(["git", "show", f"{revision}:{path}"]))
        stanzas = [stanza for stanza in dune_file if isinstance(stanza, list) and stanza]
        includes_subdirectories = any(
            stanza[0] == "include_subdirs" and stanza[1:] != ["no"] for stanza in stanzas
        )
        for stanza in stanzas:
            if stanza[0] != "library":
                continue
            fields = {entry[0]: entry[1:] for entry in stanza[1:] if isinstance(entry, list) and entry}
            dependencies = map(read_dependency, fields.get("libraries", []))
            library = Library(
                name=fields["name"][0],
                directory=posixpath.dirname(path),
                includes_subdirectories=includes_subdirectories,
                dependencies=frozenset(filter(None, dependencies)),
            )
            libraries[library.name] = library
    return libraries


def index_by_directory(libraries: dict[str, Library]) -> dict[str, Library]:
    return {library.directory: library for library in libraries.values()}


def find_owner(path: str, by_directory: dict[str, Library]) -> Library | None:
    directory = posixpath.dirname(path)
    if directory in by_directory:
        return by_directory[directory]
    while directory:
        directory = posixpath.dirname(directory)
        if directory in by_directory:
            enclosing = by_directory[directory]
            return enclosing if enclosing.includes_subdirectories else None
    return None


def format_net(count: LineCount) -> str:
    net = count.added - count.removed
    return f"{net:+d}" if net else "0"


def format_count_row(label: str, count: LineCount) -> str:
    return f"| {label} | {count.added} | {count.removed} | {format_net(count)} |"


def format_names(names: frozenset[str]) -> str:
    return ", ".join(f"`{name}`" for name in sorted(names))


def summarize_size(line_counts: list[tuple[str, LineCount]]) -> list[str]:
    by_part = {part: LineCount() for part in PARTS}
    total = LineCount()
    for path, count in line_counts:
        by_part[find_part(path)].add(count)
        total.add(count)
    changed_parts = [part for part in PARTS if by_part[part].added or by_part[part].removed]
    if not changed_parts:
        return ["## Size", "", "No lines changed."]
    lines = ["## Size", "", "| Part | Added | Removed | Net |", "|---|--:|--:|--:|"]
    lines += [format_count_row(part, by_part[part]) for part in changed_parts]
    if len(changed_parts) > 1:
        lines.append(format_count_row("Total", total))
    return lines


def pair_renamed_libraries(
    base_libraries: dict[str, Library],
    head_libraries: dict[str, Library],
    renamed_files: list[tuple[str, str]],
) -> dict[str, str]:
    names_only_in_head = head_libraries.keys() - base_libraries.keys()
    names_only_in_base = base_libraries.keys() - head_libraries.keys()
    base_by_directory = index_by_directory(base_libraries)
    head_by_directory = index_by_directory(head_libraries)
    evidence: Counter[tuple[str, str]] = Counter()
    for name in names_only_in_head:
        predecessor = base_by_directory.get(head_libraries[name].directory)
        if predecessor is not None and predecessor.name in names_only_in_base:
            evidence[(name, predecessor.name)] += 1
    for old_path, new_path in renamed_files:
        successor = find_owner(new_path, head_by_directory)
        predecessor = find_owner(old_path, base_by_directory)
        if (
            successor is not None
            and predecessor is not None
            and successor.name in names_only_in_head
            and predecessor.name in names_only_in_base
        ):
            evidence[(successor.name, predecessor.name)] += 1
    former_names: dict[str, str] = {}
    for (name, former), _ in evidence.most_common():
        if name not in former_names and former not in former_names.values():
            former_names[name] = former
    return former_names


def summarize_libraries(
    line_counts: list[tuple[str, LineCount]],
    base_libraries: dict[str, Library],
    head_libraries: dict[str, Library],
    former_names: dict[str, str],
) -> list[str]:
    names_only_in_head = head_libraries.keys() - base_libraries.keys()
    names_only_in_base = base_libraries.keys() - head_libraries.keys()
    base_by_directory = index_by_directory(base_libraries)
    head_by_directory = index_by_directory(head_libraries)
    renamed_to = {former: name for name, former in former_names.items()}
    new_names = names_only_in_head - former_names.keys()
    removed_names = names_only_in_base - renamed_to.keys()

    rows = {name: LibraryRow(name, "new") for name in new_names}
    rows |= {name: LibraryRow(name, "removed") for name in removed_names}
    rows |= {name: LibraryRow(name, f"renamed from `{former}`") for name, former in former_names.items()}
    for name in head_libraries.keys() & base_libraries.keys():
        if head_libraries[name].directory != base_libraries[name].directory:
            rows[name] = LibraryRow(name, f"moved from `{base_libraries[name].directory}`")

    for path, count in line_counts:
        owner = find_owner(path, head_by_directory) or find_owner(path, base_by_directory)
        if owner is not None:
            name = renamed_to.get(owner.name, owner.name)
            rows.setdefault(name, LibraryRow(name)).lines.add(count)

    lines = []
    if rows:
        lines += ["## Libraries", "", "| Library | Added | Removed | Net |", "|---|--:|--:|--:|"]
        for row in sorted(rows.values(), key=lambda row: (-(row.lines.added + row.lines.removed), row.name)):
            label = f"`{row.name}` ({row.note})" if row.note else f"`{row.name}`"
            lines.append(format_count_row(label, row.lines))

    dependency_rows = []
    for name in sorted(head_libraries):
        base_name = former_names.get(name, name)
        before = base_libraries[base_name].dependencies if base_name in base_libraries else frozenset()
        after = head_libraries[name].dependencies
        if before != after:
            dependency_rows.append(f"| `{name}` | {format_names(after - before)} | {format_names(before - after)} |")
    if dependency_rows:
        if lines:
            lines.append("")
        lines += ["## Library dependencies", "", "| Library | Added | Removed |", "|---|---|---|"]
        lines += dependency_rows
    return lines


def summarize(base: str, head: str) -> str:
    merge_base = run(["git", "merge-base", base, head]).strip()
    line_counts = list_line_counts(merge_base, head)
    base_libraries = read_libraries(merge_base)
    head_libraries = read_libraries(head)
    former_names = pair_renamed_libraries(base_libraries, head_libraries, list_renamed_files(merge_base, head))
    lines = summarize_size(line_counts)
    library_lines = summarize_libraries(line_counts, base_libraries, head_libraries, former_names)
    if library_lines:
        lines += [""] + library_lines
    return "\n".join(lines)


def splice(body: str, section: str) -> str:
    begin = body.find(SECTION_BEGIN)
    if begin == -1:
        text = body.rstrip()
        return f"{text}\n\n{section}" if text else section
    end = body.find(SECTION_END, begin)
    suffix = "" if end == -1 else body[end + len(SECTION_END) :]
    return body[:begin] + section + suffix


def write_into_description(pull_request: str, summary: str) -> None:
    endpoint = f"repos/{{owner}}/{{repo}}/pulls/{pull_request}"
    body = json.loads(run(["gh", "api", endpoint]))["body"] or ""
    updated = splice(body, f"{SECTION_BEGIN}\n{summary}\n{SECTION_END}")
    if updated != body:
        request = json.dumps({"body": updated}).encode()
        run(["gh", "api", "--method", "PATCH", endpoint, "--input", "-", "--silent"], request)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Summarize the lines and the stage0 libraries that a change adds and removes, "
        "from the merge base of BASE and HEAD to HEAD."
    )
    parser.add_argument("base")
    parser.add_argument("head")
    parser.add_argument(
        "--pull-request",
        help="write the summary into this pull request's description instead of printing it",
    )
    arguments = parser.parse_args()
    summary = summarize(arguments.base, arguments.head)
    if arguments.pull_request:
        write_into_description(arguments.pull_request, summary)
    else:
        print(summary)


if __name__ == "__main__":
    main()
