#!/bin/sh
set -eu

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
cd "$root"

for tool in odoc dune-deps dot tred neato jq; do
  if ! command -v "$tool" > /dev/null; then
    echo "$tool is not on the path. Install the documentation tools with" >&2
    echo "  opam install odoc dune-deps" >&2
    echo "  brew install graphviz jq" >&2
    exit 1
  fi
done

dune build @check @doc-new ./stage0/tools/docs/library_uses.exe

odoc_html=_build/default/_doc_new/html/docs
docs=_build/docs
rm -rf "$docs"
cp -R "$odoc_html" "$docs"
chmod -R u+w "$docs"

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

find stage0 -name dune -not -path '*/_build/*' -exec awk '
  /\(library/ { in_library = 1 }
  in_library && match($0, /\(name [A-Za-z0-9_]+/) {
    dir = FILENAME
    sub(/\/dune$/, "", dir)
    print substr($0, RSTART + 6, RLENGTH - 6), dir
    in_library = 0
  }' {} + | sort > "$work/directories"
while read -r library dir; do
  area=${dir#stage0/}
  area=${area%%/*}
  page=
  for library_dir in "$docs/$library"@*; do
    [ -d "$library_dir" ] || continue
    page=${library_dir#"$docs"/}
    module_dirs=$(find "$library_dir" -mindepth 1 -maxdepth 1 -type d)
    if [ -n "$module_dirs" ] && [ "$(printf '%s\n' "$module_dirs" | wc -l)" -eq 1 ]; then
      page=$page/${module_dirs##*/}
    fi
    page=$page/index.html
  done
  echo "$library $dir $area $page"
done < "$work/directories" > "$work/libraries"
printf '%s\n' test tools > "$work/test_and_tools"
awk 'FNR == NR { hidden[$1] = 1; next } !($3 in hidden)' "$work/test_and_tools" "$work/libraries" \
  > "$work/libraries_without_test_and_tools"
find _build/default/stage0 -type d -name '.*.eobjs' | sort | while read -r objects; do
  objects=${objects#_build/default/}
  area=${objects#stage0/}
  area=${area%%/*}
  echo "$objects $area"
done > "$work/executables"

dune-deps stage0 --no-exe --no-ext > "$work/dependencies.dot"

{
  cut -d ' ' -f 3 "$work/libraries_without_test_and_tools" | sort -u
  cut -d ' ' -f 3 "$work/libraries" | sort -u
  cut -d ' ' -f 2 "$work/executables" | sort -u
} | awk '!seen[$0]++' > "$work/areas"
awk '
  { areas = areas (NR == 1 ? "" : ", ") "\"" $0 "\"" }
  END { print "const AREAS = [" areas "];" }' "$work/areas" > "$docs/graph_data.js"
awk '
  FNR == NR { dir[$1] = $2; area[$1] = $3; page[$1] = $4; next }
  /->/ {
    gsub(/[";]/, "")
    sub(/^[[:space:]]*lib:/, "")
    split($0, ends, /[[:space:]]*->[[:space:]]*lib:/)
    deps[ends[1]] = deps[ends[1]] (deps[ends[1]] == "" ? "" : ", ") "\"" ends[2] "\""
  }
  END {
    print "const LIBRARIES = ["
    for (library in dir) {
      printf "  { name: \"%s\", dir: \"%s\", area: \"%s\", page: \"%s\", deps: [%s] },\n",
        library, dir[library], area[library], page[library], deps[library]
    }
    print "];"
  }' "$work/libraries" "$work/dependencies.dot" >> "$docs/graph_data.js"

while read -r library _ _ page; do
  printf 's|^\\([[:space:]]*"lib:%s"[[:space:]]*\\[\\)|\\1tooltip="%s", URL="%s", |\n' \
    "$library" "$library" "$page"
done < "$work/libraries" > "$work/node_attributes.sed"
graph_attributes='  node [shape=box, style=rounded, fontname="Menlo, monospace", fontsize=10, height=0.24, margin="0.07,0.02"];
  edge [arrowsize=0.5, penwidth=0.8];'

draw_libraries() {
  awk '
    FNR == NR { drawn["\"lib:" $1 "\""] = 1; next }
    {
      for (i = 1; i <= NF; i++) if ($i ~ /^"lib:/ && !($i in drawn)) next
      print
    }' "$1" "$work/dependencies.dot" > "$work/drawn.dot"
  tred "$work/drawn.dot" | {
    read -r _
    echo 'digraph {'
    echo '  graph [nodesep=0.12, ranksep=0.45];'
    echo "$graph_attributes"
    cat
  } | dot -Tplain > "$work/layout.plain"
  sed -f "$work/node_attributes.sed" "$work/drawn.dot" | {
    read -r _
    echo 'digraph {'
    echo "  graph [id=\"$2\", bgcolor=transparent, splines=true];"
    echo "$graph_attributes"
    awk '$1 == "node" {
      gsub(/"/, "", $2)
      printf "  \"%s\" [pos=\"%.1f,%.1f\", width=%s, height=%s];\n", $2, $3 * 72, $4 * 72, $5, $6
    }' "$work/layout.plain"
    cat
  } | neato -n2 -Tsvg | sed -n '/^<svg/,$p'
}

draw_areas() {
  awk -v id="$2" '
    FNR == NR { area_of[$1] = $3; libraries[$3]++; next }
    /->/ {
      gsub(/[";]/, "")
      sub(/^[[:space:]]*lib:/, "")
      split($0, ends, /[[:space:]]*->[[:space:]]*lib:/)
      from = area_of[ends[1]]
      to = area_of[ends[2]]
      if (from != "" && to != "" && from != to) count[from SUBSEP to]++
    }
    END {
      print "digraph {"
      printf "  graph [id=\"%s\", bgcolor=transparent, nodesep=0.3, ranksep=0.6];\n", id
      print "  node [shape=box, style=rounded, fontname=\"Menlo, monospace\", fontsize=11, margin=\"0.12,0.05\"];"
      print "  edge [arrowsize=0.6, fontname=\"Menlo, monospace\", fontsize=9];"
      for (area in libraries) {
        noun = libraries[area] == 1 ? "library" : "libraries"
        printf "  \"%s\" [label=\"%s\\n%d %s\"];\n", area, area, libraries[area], noun
      }
      for (pair in count) {
        split(pair, ends, SUBSEP)
        printf "  \"%s\" -> \"%s\" [label=\" %d\", penwidth=%.2f];\n", ends[1], ends[2], count[pair], 0.6 + log(count[pair]) / 2
      }
      print "}"
    }' "$1" "$work/dependencies.dot" | dot -Tsvg | sed -n '/^<svg/,$p'
}

draw_libraries "$work/libraries_without_test_and_tools" without-test-and-tools > "$work/graph.svg"
draw_libraries "$work/libraries" with-test-and-tools >> "$work/graph.svg"
draw_areas "$work/libraries_without_test_and_tools" without-test-and-tools > "$work/areas.svg"
draw_areas "$work/libraries" with-test-and-tools >> "$work/areas.svg"

insert_after() {
  content=$(cat "$1")
  case $content in
    *"$2"*) ;;
    *)
      echo "$1 has no $2." >&2
      exit 1
      ;;
  esac
  printf '%s%s%s%s\n' "${content%%"$2"*}" "$2" "$3" "${content#*"$2"}" > "$1"
}

find _build/default/_doc_new/odoc -name '*.odocl' > "$work/odocl_files"
odoc compile-index --json --file-list="$work/odocl_files" -o "$work/index.json"
jq -r '.[] | select(.kind.kind != "Doc")
  | [.kind.kind, (.display.url | ltrimstr("docs/"))] + (.id | map(.name)) | @tsv' \
  "$work/index.json" > "$work/index"
_build/default/stage0/tools/docs/library_uses.exe \
  "$work/libraries" "$work/executables" "$work/areas" "$work/test_and_tools" "$work/index" \
  _build/default "$docs"

cp "$here/graph.html" "$here/graph.css" "$here/graph.js" "$here/areas.html" "$here/areas.js" \
  "$here/area_colors.css" "$here/library_uses.css" "$here/library_uses.js" "$docs/"
insert_after "$docs/graph.html" '<div id="canvas">' "$(cat "$work/graph.svg")"
insert_after "$docs/areas.html" '<div id="canvas">' "$(cat "$work/areas.svg")"
insert_after "$docs/index.html" '<nav class="odoc-toc odoc-local-toc"><ul>' \
  '<li><a href="#dependency-graph">Dependency graph</a></li>'
insert_after "$docs/index.html" '<div class="odoc-content">' \
  '<h2 id="dependency-graph"><a href="#dependency-graph" class="anchor"></a>Dependency graph</h2><p><a href="graph.html">The library dependency graph</a> shows which library depends on which. Each library in it links to its documentation. <a href="areas.html">The area graph</a> shows how many dependencies each area of stage0 has on each other area. Both leave out the libraries of stage0/test and stage0/tools until you show them.</p><p>The page of each library lists the names it uses from other libraries and the names other libraries use from it. After each definition, a list names the modules that use it, in any library or executable. Both leave out the libraries and modules of stage0/test and stage0/tools until you check Show test and tools.</p>'

echo "$root/$docs/index.html"
