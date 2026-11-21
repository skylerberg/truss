import argparse
import datetime
import json
import os
import resource
import secrets
import shlex
import socket
import statistics
import subprocess
import sys
import tempfile
import time

corpus_rounds = 5
rounds_per_file = 3
worst_case_count = 20000
short_case_scale = 10
worst_case_rounds = 2
deepest_probe_limit = 10000

worst_cases = [
    ("unclosed_openers", lambda count: "let x: Int64 = " + "(" * count + "\n"),
    ("closers_with_no_opener", lambda count: "let x: Int64 = " + "(" * count + "]" * count + "\n"),
    ("unclosed_openers_before_a_closer", lambda count: "let x: Int64 = (((((" + "([)" * count + "\n"),
    ("trailing_zeros_of_a_float", lambda count: "let x: Float64 = 1" + "0" * (count * short_case_scale) + ".0\n"),
    ("digits_of_an_integer", lambda count: "let x: Int64 = " + "7" * (count * short_case_scale) + "\n"),
    ("an_integer_before_a_point", lambda count: "let x: Float64 = 1" + "0" * (count * short_case_scale) + ".\n"),
    ("three_dots", lambda count: "let x: Int64 = a" + " ..." * count + "\n"),
    ("touching_semicolons", lambda count: "let x: Int64 = a" + ";" * count + "b\n"),
    ("a_semicolon_on_every_line", lambda count: "fn f() {\n" + "  a = 1;\n" * count + "}\n"),
    ("binary_operators", lambda count: "let x: Int64 = 1" + " + 1" * count + "\n"),
    ("postfix_operations", lambda count: "let x: Int64 = a" + ".b" * count + "\n"),
    ("nested_loop_bodies", lambda count: "fn f() {\n" + "while x {\n" * count),
    ("interpolations", lambda count: "let x: String = \"" + "${a}" * count + "\"\n"),
    ("comparisons_in_a_list", lambda count: "let x: List[Bool] = [" + "A < B, " * count + "]\n"),
    ("a_fixable_habit_on_every_line", lambda count: "fn f() {\n" + "  a++\n" * count + "}\n"),
    ("path_separators", lambda count: "let x: Int64 = A" + "::B" * count + "\n"),
    ("a_chain_of_comparisons", lambda count: "let x: Bool = a" + " < a" * count + "\n"),
    ("rest_fields_in_a_pattern", lambda count: "fn f() {\n  let P(" + ".., " * count + ") = x\n}\n"),
]


def make_else_if_chain(depth):
    branches = "".join(" else if x == %d { %d }" % (index, index) for index in range(1, depth))
    return "fn f(x: Int64) -> Int64 {\n  if x == 0 { 0 }" + branches + " else { 1 }\n}\n"


def find_root():
    return os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def run_command(command, directory, environment=None, check=True, timeout=None):
    return subprocess.run(
        command, cwd=directory, env=environment, capture_output=True, text=True, check=check, timeout=timeout
    )


def list_corpus(root):
    paths = run_command(["git", "ls-files", "*.truss"], root).stdout.split()
    return [path for path in paths if not path.startswith("experimental/")]


def read_timings(text):
    files = {}
    for line in text.splitlines():
        parts = line.split()
        if len(parts) == 4:
            files[parts[3]] = [int(parts[0]), int(parts[1]), int(parts[2])]
    return files


class Executables:
    def __init__(self, root):
        self.truss = os.path.join(root, "_build/default/stage0/driver/truss/truss.exe")
        self.ocaml = os.path.join(root, "_build/default/experimental/compare/compare.exe")
        self.port = os.path.join(root, "experimental/frontend/frontend")

    def program(self, language):
        return self.ocaml if language == "ocaml" else self.port


def build(root, executables):
    started = time.monotonic()
    run_command(["dune", "build", "stage0/driver/truss/truss.exe", "experimental/compare/compare.exe"], root)
    dune_seconds = time.monotonic() - started
    started = time.monotonic()
    environment = dict(os.environ, TRUSS_NO_SERVER="1")
    built = run_command([executables.truss, "build"], os.path.join(root, "experimental/frontend"), environment, check=False)
    if built.returncode != 0:
        sys.exit("truss build failed:\n" + built.stdout + built.stderr)
    return {"dune_seconds": dune_seconds, "port_seconds": time.monotonic() - started}


def time_corpus(root, executables, corpus):
    runs = []
    best = {"ocaml": {}, "truss": {}}
    for round_index in range(corpus_rounds):
        order = ["ocaml", "truss"] if round_index % 2 == 0 else ["truss", "ocaml"]
        sums = {}
        for language in order:
            output = run_command([executables.program(language), "time", str(rounds_per_file)] + corpus, root).stdout
            timings = read_timings(output)
            sums[language] = [sum(row[0] for row in timings.values()), sum(row[1] for row in timings.values())]
            for path, row in timings.items():
                previous = best[language].get(path)
                best[language][path] = row if previous is None else [min(previous[0], row[0]), min(previous[1], row[1]), row[2]]
        runs.append(sums)
    files = {path: {"bytes": best["ocaml"][path][2], "ocaml": best["ocaml"][path][:2], "truss": best["truss"][path][:2]} for path in best["ocaml"]}
    return runs, files


def time_worst_cases(root, executables, directory):
    results = {}
    for name, make_input in worst_cases:
        path = os.path.join(directory, name + ".truss")
        with open(path, "w") as output:
            output.write(make_input(worst_case_count))
        entry = {}
        for language in ("ocaml", "truss"):
            completed = run_command([executables.program(language), "time", str(worst_case_rounds), path], root, check=False, timeout=300)
            timings = read_timings(completed.stdout)
            if completed.returncode == 0 and path in timings:
                entry[language] = timings[path][:2]
            else:
                lines = (completed.stdout + completed.stderr).strip().splitlines()
                entry[language] = lines[-1] if lines else "exit %d" % completed.returncode
        results[name] = entry
    return results


def find_deepest_else_if(root, executables, directory):
    path = os.path.join(directory, "else_if.truss")

    def parses(depth):
        with open(path, "w") as output:
            output.write(make_else_if_chain(depth))
        return run_command([executables.port, "time", "1", path], root, check=False, timeout=120).returncode == 0

    passing = 0
    failing = None
    depth = 500
    while depth <= deepest_probe_limit:
        if not parses(depth):
            failing = depth
            break
        passing = depth
        depth *= 2
    if failing is None:
        if passing < deepest_probe_limit and parses(deepest_probe_limit):
            passing = deepest_probe_limit
        return {"depth": passing, "is_limited_by_probe": True}
    while failing - passing > 50:
        middle = (passing + failing) // 2
        if parses(middle):
            passing = middle
        else:
            failing = middle
    return {"depth": passing, "is_limited_by_probe": False}


def measure(arguments):
    root = find_root()
    executables = Executables(root)
    if arguments.corpus:
        corpus = [line.strip() for line in open(arguments.corpus) if line.strip()]
    else:
        corpus = list_corpus(root)
    started = datetime.datetime.now(datetime.timezone.utc)
    clock = time.monotonic()
    build_seconds = build(root, executables)
    measured = time.monotonic()
    ocaml_trees = run_command([executables.ocaml, "print"] + corpus, root).stdout
    truss_trees = run_command([executables.port, "print"] + corpus, root).stdout
    runs, files = time_corpus(root, executables, corpus)
    with tempfile.TemporaryDirectory() as directory:
        worst = time_worst_cases(root, executables, directory)
        deepest = find_deepest_else_if(root, executables, directory)
    result = {
        "label": arguments.label,
        "host": socket.gethostname(),
        "commit": arguments.commit or run_command(["git", "rev-parse", "HEAD"], root).stdout.strip(),
        "has_uncommitted_changes": arguments.has_uncommitted_changes,
        "started": started.isoformat(timespec="seconds"),
        "stack_limit": resource.getrlimit(resource.RLIMIT_STACK)[0],
        "build": build_seconds,
        "measuring_seconds": time.monotonic() - measured,
        "total_seconds": time.monotonic() - clock,
        "trees_identical": ocaml_trees == truss_trees,
        "corpus_runs": runs,
        "corpus_files": files,
        "worst_cases": worst,
        "worst_case_count": worst_case_count,
        "short_case_scale": short_case_scale,
        "deepest_else_if": deepest,
    }
    with open(arguments.output, "w") as output:
        json.dump(result, output)


def find_results_directory(label):
    cache = os.environ.get("XDG_CACHE_HOME") or os.path.expanduser("~/.cache")
    return os.path.join(cache, "truss-frontend-benchmark", label)


def find_latest_result(directory):
    if not os.path.isdir(directory):
        return None
    names = sorted(name for name in os.listdir(directory) if name.endswith(".json"))
    return os.path.join(directory, names[-1]) if names else None


def describe_change(new, old):
    if old == 0:
        return ""
    return "%+.1f%%" % ((new - old) * 100.0 / old)


def sum_stage(files, paths, language, stage):
    return sum(files[path][language][stage] for path in paths)


def format_milliseconds(nanoseconds):
    return "%.1f ms" % (nanoseconds / 1e6)


def describe_spread(runs, language, stage):
    values = [run[language][stage] for run in runs]
    median = statistics.median(values)
    return "%.1f%%" % ((max(values) - min(values)) * 100.0 / median) if median else ""


def print_table(rows):
    widths = [max(len(row[column]) for row in rows) for column in range(len(rows[0]))]
    for index, row in enumerate(rows):
        print("  ".join(cell.ljust(widths[column]) if column == 0 else cell.rjust(widths[column]) for column, cell in enumerate(row)).rstrip())
        if index == 0:
            print("  ".join("-" * width for width in widths))


def report(result, baseline):
    commit = result["commit"][:10] + (" with uncommitted changes" if result["has_uncommitted_changes"] else "")
    print("Front-end benchmark on %s (%s), %s, %s" % (result["label"], result["host"], commit, result["started"]))
    if baseline:
        old_commit = baseline["commit"][:10] + (" with uncommitted changes" if baseline["has_uncommitted_changes"] else "")
        print("Compared with the run of %s, %s" % (baseline["started"], old_commit))
    print(
        "Build %.0f s (dune %.0f s, the port %.0f s); measuring %.0f s"
        % (result["build"]["dune_seconds"] + result["build"]["port_seconds"], result["build"]["dune_seconds"], result["build"]["port_seconds"], result["measuring_seconds"])
    )
    print("Syntax trees and diagnostics: %s" % ("identical to stage0" if result["trees_identical"] else "DIFFERENT from stage0"))
    print()
    files = result["corpus_files"]
    paths = sorted(files)
    old_files = baseline["corpus_files"] if baseline else {}
    shared = [path for path in paths if path in old_files]
    small = [path for path in paths if files[path]["bytes"] < 2000]
    large = [path for path in paths if files[path]["bytes"] >= 2000]
    header = ["Corpus, best of %d per file" % (corpus_rounds * rounds_per_file), "OCaml", "Truss", "Truss/OCaml", "spread"]
    if baseline:
        header += ["Truss change", "OCaml change", "ratio change"]
    rows = [header]
    groups = [("all %d files" % len(paths), paths), ("%d files under 2 KB" % len(small), small), ("%d files of 2 KB or more" % len(large), large)]
    for stage, stage_name in ((0, "lexing"), (1, "parsing")):
        for group_name, group in groups:
            ocaml = sum_stage(files, group, "ocaml", stage)
            truss = sum_stage(files, group, "truss", stage)
            row = ["%s, %s" % (stage_name, group_name), format_milliseconds(ocaml), format_milliseconds(truss), "%.3f" % (truss / ocaml if ocaml else 0)]
            row.append(describe_spread(result["corpus_runs"], "truss", stage) if group is paths else "")
            if baseline:
                common = [path for path in group if path in old_files]
                new_ocaml = sum_stage(files, common, "ocaml", stage)
                new_truss = sum_stage(files, common, "truss", stage)
                old_ocaml = sum_stage(old_files, common, "ocaml", stage)
                old_truss = sum_stage(old_files, common, "truss", stage)
                new_ratio = new_truss / new_ocaml if new_ocaml else 0
                old_ratio = old_truss / old_ocaml if old_ocaml else 0
                row += [describe_change(new_truss, old_truss), describe_change(new_ocaml, old_ocaml), describe_change(new_ratio, old_ratio)]
            rows.append(row)
    print_table(rows)
    if baseline and len(shared) != len(paths):
        print("Changes are over the %d files both runs timed." % len(shared))
    print()
    scale = result.get("short_case_scale", 1)
    header = ["Worst case, %d repetitions; numbers %d times as many" % (result["worst_case_count"], scale), "OCaml lex", "OCaml parse", "Truss lex", "Truss parse"]
    if baseline:
        header.append("Truss change")
    rows = [header]
    for name, entry in result["worst_cases"].items():
        row = [name.replace("_", " ")]
        for language in ("ocaml", "truss"):
            value = entry[language]
            if isinstance(value, list):
                row += [format_milliseconds(value[0]), format_milliseconds(value[1])]
            else:
                row += [value, ""]
        if baseline:
            old = baseline["worst_cases"].get(name, {}).get("truss")
            new = entry["truss"]
            is_comparable = baseline.get("short_case_scale", 1) == scale and baseline["worst_case_count"] == result["worst_case_count"]
            row.append(describe_change(sum(new), sum(old)) if is_comparable and isinstance(new, list) and isinstance(old, list) else "")
        rows.append(row)
    print_table(rows)
    print()
    deepest = result["deepest_else_if"]
    depth = ("at least %d" if deepest["is_limited_by_probe"] else "%d") % deepest["depth"]
    line = "Deepest else-if chain the Truss port parses, with a stack of %d KB: %s" % (result["stack_limit"] // 1024, depth)
    if baseline:
        line += " (was %d)" % baseline["deepest_else_if"]["depth"]
    print(line)
    if baseline and shared:
        movements = []
        for path in shared:
            new = sum(files[path]["truss"])
            old = sum(old_files[path]["truss"])
            movements.append((abs(new - old), new - old, old, path))
        movements.sort(reverse=True)
        print()
        print("Files whose Truss time moved most:")
        for _, change, old, path in movements[:5]:
            print("  %+.2f ms (%s) %s" % (change / 1e6, describe_change(old + change, old), path))


def save_and_report(result_path, label, baseline_path):
    with open(result_path) as source:
        result = json.load(source)
    directory = find_results_directory(label)
    os.makedirs(directory, exist_ok=True)
    if baseline_path is None:
        baseline_path = find_latest_result(directory)
    baseline = None
    if baseline_path:
        with open(baseline_path) as source:
            baseline = json.load(source)
    name = "%s-%s.json" % (result["started"].replace(":", ""), result["commit"][:10])
    saved = os.path.join(directory, name)
    with open(saved, "w") as output:
        json.dump(result, output)
    report(result, baseline)
    print()
    print("Saved %s" % saved)


def read_commit(root):
    commit = run_command(["git", "rev-parse", "HEAD"], root).stdout.strip()
    status = run_command(["git", "status", "--porcelain", "--untracked-files=no"], root).stdout.strip()
    return commit, bool(status)


def run_locally(arguments):
    root = find_root()
    commit, has_changes = read_commit(root)
    with tempfile.TemporaryDirectory() as directory:
        output = os.path.join(directory, "result.json")
        measure_arguments = argparse.Namespace(
            corpus=None, output=output, label=arguments.label, commit=commit, has_uncommitted_changes=has_changes
        )
        measure(measure_arguments)
        save_and_report(output, arguments.label, arguments.baseline)


def run_remotely(arguments):
    root = find_root()
    commit, has_changes = read_commit(root)
    label = arguments.label or arguments.host
    remote_directory = "benchmark/frontend-benchmark-%s" % secrets.token_hex(4)
    with tempfile.TemporaryDirectory() as directory:
        corpus_path = os.path.join(directory, "corpus.txt")
        with open(corpus_path, "w") as output:
            output.write("\n".join(list_corpus(root)) + "\n")
        try:
            run_command(
                ["rsync", "-a", "--exclude", "_build", "--exclude", ".git", "--exclude", ".truss",
                 "--exclude", "/experimental/frontend/frontend", "--exclude", "*.dSYM", root + "/", "%s:%s/" % (arguments.host, remote_directory)],
                root,
            )
            run_command(["scp", "-q", corpus_path, "%s:%s/corpus.txt" % (arguments.host, remote_directory)], root)
            measure_command = " ".join(
                shlex.quote(part)
                for part in ["python3", "-I", "experimental/tools/benchmark.py", "measure", "--corpus", "corpus.txt", "--output", "result.json",
                             "--label", label, "--commit", commit] + (["--has-uncommitted-changes"] if has_changes else [])
            )
            remote_command = "eval $(opam env --switch=default) && cd ~/%s && flock -w 900 ~/benchmark/truss.lock timeout 1500 %s" % (
                remote_directory, measure_command)
            completed = run_command(["ssh", arguments.host, remote_command], root, check=False)
            if completed.returncode != 0:
                sys.exit("the remote measurement failed:\n" + completed.stdout + completed.stderr)
            result_path = os.path.join(directory, "result.json")
            run_command(["scp", "-q", "%s:%s/result.json" % (arguments.host, remote_directory), result_path], root)
        finally:
            run_command(["ssh", arguments.host, "rm -rf ~/%s" % remote_directory], root, check=False)
        save_and_report(result_path, label, arguments.baseline)


def main():
    parser = argparse.ArgumentParser(description="Time stage0's front end against its Truss port.")
    commands = parser.add_subparsers(dest="command", required=True)
    remote = commands.add_parser("remote", help="build and measure on HOST under its benchmark lock, then report here")
    remote.add_argument("host")
    remote.add_argument("--label")
    remote.add_argument("--baseline", help="a saved result to compare with, instead of the label's latest")
    local = commands.add_parser("local", help="build and measure in this checkout")
    local.add_argument("--label", default="local")
    local.add_argument("--baseline", help="a saved result to compare with, instead of the label's latest")
    measured = commands.add_parser("measure", help="build and measure, and write the result as JSON")
    measured.add_argument("--corpus")
    measured.add_argument("--output", required=True)
    measured.add_argument("--label", required=True)
    measured.add_argument("--commit")
    measured.add_argument("--has-uncommitted-changes", action="store_true")
    show = commands.add_parser("show", help="report a saved result")
    show.add_argument("result")
    show.add_argument("--baseline")
    arguments = parser.parse_args()
    if arguments.command == "remote":
        run_remotely(arguments)
    elif arguments.command == "local":
        run_locally(arguments)
    elif arguments.command == "measure":
        measure(arguments)
    else:
        with open(arguments.result) as source:
            result = json.load(source)
        baseline = None
        if arguments.baseline:
            with open(arguments.baseline) as source:
                baseline = json.load(source)
        report(result, baseline)


main()
