#!/bin/sh
# Builds the documentation of every library under stage0 into _build/docs,
# with a page of the library dependency graph and a page of the dependencies
# between areas, both linked from the index. Each library in the graph links
# to its documentation. Prints the path of the
# index page, so `open "$(stage0/tools/docs/build.sh)"` builds the
# documentation and opens it.
#
# Needs odoc, dune-deps, and Graphviz:
#   opam install odoc dune-deps
#   brew install graphviz
set -eu

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
cd "$root"

for tool in odoc dune-deps dot tred neato; do
  if ! command -v "$tool" > /dev/null; then
    echo "$tool is not on the path. Install the documentation tools with" >&2
    echo "  opam install odoc dune-deps" >&2
    echo "  brew install graphviz" >&2
    exit 1
  fi
done

dune build @doc-new

odoc_html=_build/default/_doc_new/html/docs
docs=_build/docs
rm -rf "$docs"
cp -R "$odoc_html" "$docs"
chmod -R u+w "$docs"

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# One line per library: its name, its directory, and its documentation page.
# Each library's documentation holds exactly one module, the library's main
# module, so the page is that module's. A library with any other layout links
# to its own page.
find stage0 -name dune -not -path '*/_build/*' -exec awk '
  /\(library/ { in_library = 1 }
  in_library && match($0, /\(name [A-Za-z0-9_]+/) {
    dir = FILENAME
    sub(/\/dune$/, "", dir)
    print substr($0, RSTART + 6, RLENGTH - 6), dir
    in_library = 0
  }' {} + | sort > "$work/directories"
while read -r library dir; do
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
  echo "$library $dir $page"
done < "$work/directories" > "$work/libraries"

dune-deps stage0 --no-exe --no-ext > "$work/dependencies.dot"

# The pages' scripts read every declared dependency from graph_data.js.
awk '
  FNR == NR { dir[$1] = $2; page[$1] = $3; next }
  /->/ {
    gsub(/[";]/, "")
    sub(/^[[:space:]]*lib:/, "")
    split($0, ends, /[[:space:]]*->[[:space:]]*lib:/)
    deps[ends[1]] = deps[ends[1]] (deps[ends[1]] == "" ? "" : ", ") "\"" ends[2] "\""
  }
  END {
    print "const LIBRARIES = ["
    for (library in dir) {
      area = dir[library]
      sub(/^stage0\/?/, "", area)
      area = (area ~ /\//) ? substr(area, 1, index(area, "/") - 1) : ""
      printf "  { name: \"%s\", dir: \"%s\", area: \"%s\", page: \"%s\", deps: [%s] },\n",
        library, dir[library], area, page[library], deps[library]
    }
    print "];"
  }' "$work/libraries" "$work/dependencies.dot" > "$docs/graph_data.js"

# The drawing has every declared dependency, an edge that a longer path
# implies included: such an edge is a dependency of its own, which a change
# to either library must keep or remove. dot gives an edge a place on each
# rank it crosses, so laying out every edge spreads the drawing several times
# wider. The libraries are placed by a layout of the edges that tred keeps,
# those no longer path implies, and neato then routes every edge between
# them.
while read -r library _ page; do
  printf 's|^\\([[:space:]]*"lib:%s"[[:space:]]*\\[\\)|\\1id="lib-%s", tooltip="%s", URL="%s", |\n' \
    "$library" "$library" "$library" "$page"
done < "$work/libraries" > "$work/node_attributes.sed"
graph_attributes='  node [shape=box, style=rounded, fontname="Menlo, monospace", fontsize=10, height=0.24, margin="0.07,0.02"];
  edge [arrowsize=0.5, penwidth=0.8];'
tred "$work/dependencies.dot" | {
  read -r _
  echo 'digraph {'
  echo '  graph [nodesep=0.12, ranksep=0.45];'
  echo "$graph_attributes"
  cat
} | dot -Tplain > "$work/layout.plain"
# A node line of the plain format is: node, name, x, y, width, height, in
# inches from the bottom left.
sed -f "$work/node_attributes.sed" "$work/dependencies.dot" | {
  read -r _
  echo 'digraph {'
  echo '  graph [bgcolor=transparent, splines=true];'
  echo "$graph_attributes"
  awk '$1 == "node" {
    gsub(/"/, "", $2)
    printf "  \"%s\" [pos=\"%.1f,%.1f\", width=%s, height=%s];\n", $2, $3 * 72, $4 * 72, $5, $6
  }' "$work/layout.plain"
  cat
} | neato -n2 -Tsvg | sed -n '/^<svg/,$p' > "$work/graph.svg"

# The areas: one node for each directory under stage0 that holds libraries,
# and one for each library directly under stage0, which puts the areas
# together. An edge from one area to another is labeled with the number of
# dependencies of a library in the first on a library in the second. The
# tests and the tools are left out: they depend on every area.
awk '
  FNR == NR {
    area = $2
    sub(/^stage0\/?/, "", area)
    area = (area ~ /\//) ? substr(area, 1, index(area, "/") - 1) : $1
    if (area == "test" || area == "tools") next
    of[$1] = area
    libraries[area]++
    next
  }
  /->/ {
    gsub(/[";]/, "")
    sub(/^[[:space:]]*lib:/, "")
    split($0, ends, /[[:space:]]*->[[:space:]]*lib:/)
    from = of[ends[1]]
    to = of[ends[2]]
    if (from != "" && to != "" && from != to) count[from SUBSEP to]++
  }
  END {
    print "digraph {"
    print "  graph [bgcolor=transparent, nodesep=0.3, ranksep=0.6];"
    print "  node [shape=box, style=rounded, fontname=\"Menlo, monospace\", fontsize=11, margin=\"0.12,0.05\"];"
    print "  edge [arrowsize=0.6, fontname=\"Menlo, monospace\", fontsize=9];"
    for (area in libraries) {
      noun = libraries[area] == 1 ? "library" : "libraries"
      printf "  \"%s\" [id=\"area-%s\", label=\"%s\\n%d %s\"];\n", area, area, area, libraries[area], noun
    }
    for (pair in count) {
      split(pair, ends, SUBSEP)
      printf "  \"%s\" -> \"%s\" [label=\" %d\", penwidth=%.2f];\n", ends[1], ends[2], count[pair], 0.6 + log(count[pair]) / 2
    }
    print "}"
  }' "$work/libraries" "$work/dependencies.dot" | dot -Tsvg | sed -n '/^<svg/,$p' > "$work/areas.svg"

# Splices $3 into the file $1 after the first occurrence of $2.
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

cp "$here/graph.html" "$here/graph.css" "$here/graph.js" "$here/areas.html" "$here/areas.js" "$docs/"
insert_after "$docs/graph.html" '<div id="canvas">' "$(cat "$work/graph.svg")"
insert_after "$docs/areas.html" '<div id="canvas">' "$(cat "$work/areas.svg")"
insert_after "$docs/index.html" '<nav class="odoc-toc odoc-local-toc"><ul>' \
  '<li><a href="#dependency-graph">Dependency graph</a></li>'
insert_after "$docs/index.html" '<div class="odoc-content">' \
  '<h2 id="dependency-graph"><a href="#dependency-graph" class="anchor"></a>Dependency graph</h2><p><a href="graph.html">The library dependency graph</a> shows which library depends on which. Each library in it links to its documentation. <a href="areas.html">The areas</a> shows how many dependencies each area of stage0 has on each other area.</p>'

echo "$root/$docs/index.html"
