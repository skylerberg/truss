// Draws the page around the Graphviz drawing in #canvas. LIBRARIES, from
// graph_data.js, lists every declared dependency. The drawing omits edges that
// a longer path implies, so the highlighting and the panel read LIBRARIES.
(() => {
  const canvas = document.getElementById("canvas");
  const panel = document.getElementById("panel");
  const find = document.getElementById("find");
  const svg = canvas.querySelector("svg");

  const libraries = new Map(LIBRARIES.map((library) => [library.name, library]));
  const dependents = new Map(LIBRARIES.map((library) => [library.name, []]));
  for (const library of LIBRARIES) {
    for (const dependency of library.deps) dependents.get(dependency)?.push(library.name);
  }
  const dependencies = new Map(LIBRARIES.map((library) => [library.name, library.deps]));
  const byName = (a, b) => a.localeCompare(b);

  const reachable = (start, adjacency) => {
    const seen = new Set();
    const stack = [start];
    while (stack.length > 0) {
      for (const next of adjacency.get(stack.pop()) ?? []) {
        if (!seen.has(next)) {
          seen.add(next);
          stack.push(next);
        }
      }
    }
    return seen;
  };

  // A library directly under stage0 has the area "". Every other area takes a
  // color by its place in the sorted list of areas.
  const areas = [...new Set(LIBRARIES.map((library) => library.area))].sort(byName);
  const namedAreas = areas.filter((area) => area !== "");
  const areaColor = (area) =>
    area === "" ? "var(--area-0)" : `var(--area-${(namedAreas.indexOf(area) % 8) + 1})`;
  const areaLabel = (area) => (area === "" ? "stage0" : `stage0/${area}`);

  const nodes = new Map();
  for (const node of svg.querySelectorAll("g.node")) {
    const name = node.id.replace(/^lib-/, "");
    nodes.set(name, node);
    node.style.setProperty("--area", areaColor(libraries.get(name)?.area ?? ""));
  }
  const edges = [...svg.querySelectorAll("g.edge")].map((edge) => {
    const [source, target] = edge
      .querySelector("title")
      .textContent.split("->")
      .map((end) => end.replace(/^lib:/, ""));
    return { edge, source, target };
  });

  // The panel and the highlighting

  const escape = (text) =>
    String(text).replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" })[c]);

  const chip = (name) => {
    const library = libraries.get(name);
    const color = areaColor(library?.area ?? "");
    const label = `<span class="dot" style="--area: ${color}"></span>${escape(name)}`;
    return library?.page
      ? `<a class="chip" href="${escape(library.page)}">${label}</a>`
      : `<span class="chip">${label}</span>`;
  };

  const chips = (names) =>
    names.length === 0
      ? '<p class="muted">None</p>'
      : `<div class="chips">${[...names].sort(byName).map(chip).join("")}</div>`;

  const overview = () => {
    const counts = new Map(areas.map((area) => [area, 0]));
    for (const library of LIBRARIES) counts.set(library.area, counts.get(library.area) + 1);
    return `
      <h2>${LIBRARIES.length} libraries</h2>
      <p>An arrow points from a library to a library it depends on. An arrow
      that a longer path implies is not drawn.</p>
      <p>Hover over a library to highlight its
      <b class="dependency-key">dependencies</b> and its
      <b class="dependent-key">dependents</b> and list them here. Click a
      library to open its documentation. Drag to pan and scroll to zoom.</p>
      <h3>Directories</h3>
      <div class="areas">${areas
        .map(
          (area) =>
            `<div><span class="dot" style="--area: ${areaColor(area)}"></span>` +
            `${escape(areaLabel(area))}<span class="count">${counts.get(area)}</span></div>`,
        )
        .join("")}</div>`;
  };

  const details = (name) => {
    const library = libraries.get(name);
    const allDependencies = reachable(name, dependencies);
    const allDependents = reachable(name, dependents);
    const title = library.page
      ? `<a href="${escape(library.page)}">${escape(name)}</a>`
      : escape(name);
    return `
      <h2>${title}</h2>
      <p class="muted">${escape(library.dir)}</p>
      <h3><span class="dependency-key">Depends on</span> · ${library.deps.length} directly,
      ${allDependencies.size} in total</h3>
      ${chips(library.deps)}
      <h3><span class="dependent-key">Used by</span> · ${dependents.get(name).length} directly,
      ${allDependents.size} in total</h3>
      ${chips(dependents.get(name))}`;
  };

  let shown = null;

  const show = (name) => {
    shown = name;
    for (const element of svg.querySelectorAll(".focus, .dependency, .dependent")) {
      element.classList.remove("focus", "dependency", "dependent");
    }
    svg.classList.toggle("focused", name !== null);
    if (name === null) {
      panel.innerHTML = overview();
      return;
    }
    const allDependencies = reachable(name, dependencies);
    const allDependents = reachable(name, dependents);
    nodes.get(name)?.classList.add("focus");
    for (const dependency of allDependencies) nodes.get(dependency)?.classList.add("dependency");
    for (const dependent of allDependents) nodes.get(dependent)?.classList.add("dependent");
    for (const { edge, source, target } of edges) {
      if (source === name || allDependencies.has(source)) edge.classList.add("dependency");
      else if (target === name || allDependents.has(target)) edge.classList.add("dependent");
    }
    panel.innerHTML = details(name);
  };

  for (const [name, node] of nodes) {
    node.addEventListener("mouseenter", () => {
      if (name !== shown && !canvas.classList.contains("panning")) show(name);
    });
  }

  // The view: a center in drawing coordinates and a scale in pixels per unit

  const drawing = svg.viewBox.baseVal;
  const bounds = { x: drawing.x, y: drawing.y, width: drawing.width, height: drawing.height };
  svg.removeAttribute("width");
  svg.removeAttribute("height");
  const graph = svg.querySelector("g.graph");
  const view = { x: 0, y: 0, scale: 1 };
  let fitScale = 1;

  const apply = () => {
    const width = canvas.clientWidth / view.scale;
    const height = canvas.clientHeight / view.scale;
    svg.setAttribute("viewBox", `${view.x - width / 2} ${view.y - height / 2} ${width} ${height}`);
  };

  const fit = () => {
    fitScale = 0.97 * Math.min(canvas.clientWidth / bounds.width, canvas.clientHeight / bounds.height);
    view.x = bounds.x + bounds.width / 2;
    view.y = bounds.y + bounds.height / 2;
    view.scale = fitScale;
    apply();
  };

  const zoomAt = (factor, px, py) => {
    const scale = Math.min(4, Math.max(fitScale / 2, view.scale * factor));
    const dx = px - canvas.clientWidth / 2;
    const dy = py - canvas.clientHeight / 2;
    view.x += dx / view.scale - dx / scale;
    view.y += dy / view.scale - dy / scale;
    view.scale = scale;
    apply();
  };

  const center = (name) => {
    const box = nodes.get(name).getBBox();
    const point = new DOMPoint(box.x + box.width / 2, box.y + box.height / 2).matrixTransform(
      graph.transform.baseVal.consolidate()?.matrix ?? new DOMMatrix(),
    );
    view.x = point.x;
    view.y = point.y;
    view.scale = Math.max(view.scale, 1.2);
    apply();
  };

  canvas.addEventListener(
    "wheel",
    (event) => {
      event.preventDefault();
      const rect = canvas.getBoundingClientRect();
      const speed = event.ctrlKey ? 0.01 : 0.0015;
      zoomAt(Math.exp(-event.deltaY * speed), event.clientX - rect.left, event.clientY - rect.top);
    },
    { passive: false },
  );

  // A drag pans. The pointer is captured only once it moves, so a click on a
  // node still reaches the node's link.
  let drag = null;
  canvas.addEventListener("pointerdown", (event) => {
    if (event.button !== 0) return;
    drag = { id: event.pointerId, x: event.clientX, y: event.clientY, moved: false };
  });
  canvas.addEventListener("pointermove", (event) => {
    if (drag === null || event.pointerId !== drag.id) return;
    const dx = event.clientX - drag.x;
    const dy = event.clientY - drag.y;
    if (!drag.moved && Math.hypot(dx, dy) < 4) return;
    if (!drag.moved) {
      drag.moved = true;
      canvas.setPointerCapture(event.pointerId);
      canvas.classList.add("panning");
    }
    view.x -= dx / view.scale;
    view.y -= dy / view.scale;
    drag.x = event.clientX;
    drag.y = event.clientY;
    apply();
  });
  const endDrag = (event) => {
    if (drag === null || event.pointerId !== drag.id) return;
    canvas.classList.remove("panning");
    if (!drag.moved && event.type === "pointerup" && !event.target.closest(".node")) show(null);
    drag.dragged = drag.moved;
    setTimeout(() => (drag = null));
  };
  canvas.addEventListener("pointerup", endDrag);
  canvas.addEventListener("pointercancel", endDrag);
  canvas.addEventListener(
    "click",
    (event) => {
      if (drag?.dragged) {
        event.preventDefault();
        event.stopPropagation();
      }
    },
    true,
  );

  const zoomAtCenter = (factor) => zoomAt(factor, canvas.clientWidth / 2, canvas.clientHeight / 2);
  document.getElementById("zoom-in").addEventListener("click", () => zoomAtCenter(1.3));
  document.getElementById("zoom-out").addEventListener("click", () => zoomAtCenter(1 / 1.3));
  document.getElementById("fit").addEventListener("click", fit);
  new ResizeObserver(apply).observe(canvas);

  // Search

  document.getElementById("library-names").innerHTML = [...nodes.keys()]
    .sort(byName)
    .map((name) => `<option value="${escape(name)}">`)
    .join("");

  const select = (query) => {
    const text = query.trim().toLowerCase();
    if (text === "") return;
    const names = [...nodes.keys()].sort(byName);
    const match =
      names.find((name) => name === text) ??
      names.find((name) => name.startsWith(text)) ??
      names.find((name) => name.includes(text));
    if (match === undefined) return;
    show(match);
    center(match);
    find.value = "";
  };
  find.addEventListener("change", () => {
    if (nodes.has(find.value.trim())) select(find.value);
  });
  find.addEventListener("keydown", (event) => {
    if (event.key === "Enter") select(find.value);
  });
  document.addEventListener("keydown", (event) => {
    if (event.key === "Escape") show(null);
  });

  fit();
  show(null);
})();
