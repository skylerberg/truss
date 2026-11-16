(() => {
  const testAndToolsToggle = document.getElementById("show-test-and-tools");

  const loadDrawing = (graph) => {
    const svg = graph.ownerSVGElement;
    const nodes = new Map();
    for (const node of graph.querySelectorAll("g.node")) {
      const name = node.querySelector("title").textContent;
      nodes.set(name, node);
      node.classList.add(`area-${AREAS.indexOf(name)}`);
    }
    const edges = [...graph.querySelectorAll("g.edge")].map((edge) => {
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
        node.classList.toggle("dependency", edges.some(({ source, target }) => source === name && target === other));
        node.classList.toggle("dependent", edges.some(({ source, target }) => target === name && source === other));
      }
    };
    for (const [name, node] of nodes) {
      node.addEventListener("mouseenter", () => show(name));
      node.addEventListener("mouseleave", () => show(null));
    }
    return svg;
  };
  const withoutTestAndTools = loadDrawing(document.getElementById("without-test-and-tools"));
  const withTestAndTools = loadDrawing(document.getElementById("with-test-and-tools"));

  const switchDrawing = () => {
    withTestAndTools.toggleAttribute("hidden", !testAndToolsToggle.checked);
    withoutTestAndTools.toggleAttribute("hidden", testAndToolsToggle.checked);
  };
  testAndToolsToggle.addEventListener("change", switchDrawing);
  switchDrawing();
})();
