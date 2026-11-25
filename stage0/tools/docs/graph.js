(() => {
  const canvas = document.getElementById("canvas");
  const panel = document.getElementById("panel");
  const find = document.getElementById("find");
  const testAndToolsToggle = document.getElementById("show-test-and-tools");

  const libraries = new Map(LIBRARIES.map((library) => [library.name, library]));
  const dependents = new Map(LIBRARIES.map((library) => [library.name, []]));
  for (const library of LIBRARIES) {
    for (const dependency of library.deps) dependents.get(dependency)?.push(library.name);
  }
  const dependencies = new Map(LIBRARIES.map((library) => [library.name, library.deps]));
  const compareNames = (a, b) => a.localeCompare(b);

  const findReachable = (start, adjacency) => {
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

  const toAreaClass = (area) => `area-${AREAS.indexOf(area)}`;

  let shown = null;

  const loadDrawing = (graph) => {
    const svg = graph.ownerSVGElement;
    const viewBox = svg.viewBox.baseVal;
    svg.removeAttribute("width");
    svg.removeAttribute("height");
    const nodes = new Map();
    for (const node of graph.querySelectorAll("g.node")) {
      const name = node.querySelector("title").textContent.replace(/^lib:/, "");
      nodes.set(name, node);
      node.classList.add(toAreaClass(libraries.get(name).area));
      node.addEventListener("mouseenter", () => {
        if (name !== shown && !canvas.classList.contains("panning")) show(name);
      });
    }
    const edges = [...graph.querySelectorAll("g.edge")].map((edge) => {
      const [source, target] = edge
        .querySelector("title")
        .textContent.split("->")
        .map((end) => end.replace(/^lib:/, ""));
      return { edge, source, target };
    });
    const bounds = { x: viewBox.x, y: viewBox.y, width: viewBox.width, height: viewBox.height };
    return { svg, graph, nodes, edges, bounds };
  };
  const withoutTestAndTools = loadDrawing(document.getElementById("without-test-and-tools"));
  const withTestAndTools = loadDrawing(document.getElementById("with-test-and-tools"));
  let drawing = withoutTestAndTools;

  const filterToDrawing = (names) => [...names].filter((name) => drawing.nodes.has(name));

  const escape = (text) =>
    String(text).replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" })[c]);

  const renderChip = (name) => {
    const library = libraries.get(name);
    const label = `<span class="dot ${toAreaClass(library.area)}"></span>${escape(name)}`;
    return library.page
      ? `<a class="chip" href="${escape(library.page)}">${label}</a>`
      : `<span class="chip">${label}</span>`;
  };

  const renderChips = (names) =>
    names.length === 0
      ? '<p class="muted">None</p>'
      : `<div class="chips">${[...names].sort(compareNames).map(renderChip).join("")}</div>`;

  const renderOverview = () => {
    const counts = new Map();
    for (const name of drawing.nodes.keys()) {
      const area = libraries.get(name).area;
      counts.set(area, (counts.get(area) ?? 0) + 1);
    }
    return `
      <h2>${drawing.nodes.size} libraries</h2>
      <p>An arrow points from a library to a library it depends on.</p>
      <p>Hover over a library to highlight its direct
      <b class="dependency-key">dependencies</b> and its direct
      <b class="dependent-key">dependents</b> and list them here. Click a
      library to open its documentation. Hover over a directory to highlight
      its libraries. Drag to pan and scroll to zoom.</p>
      <h3>Directories</h3>
      <div class="areas">${AREAS.filter((area) => counts.has(area))
        .map(
          (area) =>
            `<div data-area="${escape(area)}"><span class="dot ${toAreaClass(area)}"></span>` +
            `stage0/${escape(area)}<span class="count">${counts.get(area)}</span></div>`,
        )
        .join("")}</div>`;
  };

  const renderDetails = (name) => {
    const library = libraries.get(name);
    const directDependencies = filterToDrawing(library.deps);
    const directDependents = filterToDrawing(dependents.get(name));
    const allDependencies = filterToDrawing(findReachable(name, dependencies));
    const allDependents = filterToDrawing(findReachable(name, dependents));
    const title = library.page
      ? `<a href="${escape(library.page)}">${escape(name)}</a>`
      : escape(name);
    return `
      <h2>${title}</h2>
      <p class="muted">${escape(library.dir)}</p>
      <h3><span class="dependency-key">Depends on</span> · ${directDependencies.length} directly,
      ${allDependencies.length} in total</h3>
      ${renderChips(directDependencies)}
      <h3><span class="dependent-key">Used by</span> · ${directDependents.length} directly,
      ${allDependents.length} in total</h3>
      ${renderChips(directDependents)}`;
  };

  const clearHighlight = () => {
    for (const element of drawing.svg.querySelectorAll(".focus, .dependency, .dependent, .member")) {
      element.classList.remove("focus", "dependency", "dependent", "member");
    }
    drawing.svg.classList.remove("focused");
  };

  const highlightArea = (area) => {
    clearHighlight();
    drawing.svg.classList.add("focused");
    for (const [name, node] of drawing.nodes) {
      if (libraries.get(name).area === area) node.classList.add("member");
    }
    for (const { edge, source, target } of drawing.edges) {
      if (libraries.get(source).area === area && libraries.get(target).area === area) {
        edge.classList.add("member");
      }
    }
  };

  const show = (name) => {
    shown = name;
    clearHighlight();
    if (name === null) {
      panel.innerHTML = renderOverview();
      for (const row of panel.querySelectorAll("[data-area]")) {
        row.addEventListener("mouseenter", () => highlightArea(row.dataset.area));
        row.addEventListener("mouseleave", clearHighlight);
      }
      return;
    }
    drawing.svg.classList.add("focused");
    drawing.nodes.get(name).classList.add("focus");
    for (const dependency of libraries.get(name).deps) {
      drawing.nodes.get(dependency)?.classList.add("dependency");
    }
    for (const dependent of dependents.get(name)) drawing.nodes.get(dependent)?.classList.add("dependent");
    for (const { edge, source, target } of drawing.edges) {
      if (source === name) edge.classList.add("dependency");
      else if (target === name) edge.classList.add("dependent");
    }
    panel.innerHTML = renderDetails(name);
  };

  const view = { x: 0, y: 0, scale: 1 };
  let fitScale = 1;

  const apply = () => {
    const width = canvas.clientWidth / view.scale;
    const height = canvas.clientHeight / view.scale;
    drawing.svg.setAttribute("viewBox", `${view.x - width / 2} ${view.y - height / 2} ${width} ${height}`);
  };

  const fit = () => {
    const { bounds } = drawing;
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
    const box = drawing.nodes.get(name).getBBox();
    const point = new DOMPoint(box.x + box.width / 2, box.y + box.height / 2).matrixTransform(
      drawing.graph.transform.baseVal.consolidate()?.matrix ?? new DOMMatrix(),
    );
    view.x = point.x;
    view.y = point.y;
    view.scale = Math.max(view.scale, 1.2);
    apply();
  };

  const switchDrawing = () => {
    clearHighlight();
    drawing = testAndToolsToggle.checked ? withTestAndTools : withoutTestAndTools;
    withTestAndTools.svg.toggleAttribute("hidden", drawing !== withTestAndTools);
    withoutTestAndTools.svg.toggleAttribute("hidden", drawing !== withoutTestAndTools);
    fit();
    show(shown !== null && drawing.nodes.has(shown) ? shown : null);
  };
  testAndToolsToggle.addEventListener("change", switchDrawing);

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

  const names = [...libraries.keys()].sort(compareNames);
  document.getElementById("library-names").innerHTML = names
    .map((name) => `<option value="${escape(name)}">`)
    .join("");

  const select = (query) => {
    const text = query.trim().toLowerCase();
    if (text === "") return;
    const match =
      names.find((name) => name === text) ??
      names.find((name) => name.startsWith(text)) ??
      names.find((name) => name.includes(text));
    if (match === undefined) return;
    if (!drawing.nodes.has(match)) {
      testAndToolsToggle.checked = true;
      switchDrawing();
    }
    show(match);
    center(match);
    find.value = "";
  };
  find.addEventListener("change", () => {
    if (libraries.has(find.value.trim())) select(find.value);
  });
  find.addEventListener("keydown", (event) => {
    if (event.key === "Enter") select(find.value);
  });
  document.addEventListener("keydown", (event) => {
    if (event.key === "Escape") show(null);
  });

  switchDrawing();
})();
