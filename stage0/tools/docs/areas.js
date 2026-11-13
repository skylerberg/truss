// Colors the Graphviz drawing of areas in #canvas as graph.js colors the
// libraries, and on hover highlights an area's dependencies and dependents.
// A node is an area, or a library directly under stage0; an edge's label is
// the number of dependencies of a library in one on a library in the other.
(() => {
  const svg = document.querySelector("#canvas svg");
  const byName = (a, b) => a.localeCompare(b);

  // The same colors as graph.js: an area takes its place in the sorted list
  // of named areas, and a library directly under stage0 takes the first.
  const namedAreas = [...new Set(LIBRARIES.map((library) => library.area))]
    .filter((area) => area !== "")
    .sort(byName);
  const areaColor = (name) => {
    const index = namedAreas.indexOf(name);
    return index < 0 ? "var(--area-0)" : `var(--area-${(index % 13) + 1})`;
  };

  const nodes = new Map();
  for (const node of svg.querySelectorAll("g.node")) {
    const name = node.querySelector("title").textContent;
    nodes.set(name, node);
    node.style.setProperty("--area", areaColor(name));
  }
  const edges = [...svg.querySelectorAll("g.edge")].map((edge) => {
    const [source, target] = edge.querySelector("title").textContent.split("->");
    return { edge, source, target };
  });

  const show = (name) => {
    svg.classList.toggle("focused", name !== null);
    for (const [other, node] of nodes) node.classList.toggle("focus", other === name);
    for (const { edge, source, target } of edges) {
      edge.classList.toggle("dependency", source === name);
      edge.classList.toggle("dependent", target === name);
    }
    for (const [other, node] of nodes) {
      node.classList.toggle("dependency", edges.some((e) => e.source === name && e.target === other));
      node.classList.toggle("dependent", edges.some((e) => e.target === name && e.source === other));
    }
  };
  for (const [name, node] of nodes) {
    node.addEventListener("mouseenter", () => show(name));
    node.addEventListener("mouseleave", () => show(null));
  }
})();
