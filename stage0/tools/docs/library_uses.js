(() => {
  const toggle = document.getElementById("show-test-and-tools");
  if (toggle === null) return;
  try {
    toggle.checked = localStorage.getItem(toggle.id) === "true";
  } catch {}
  toggle.addEventListener("change", () => {
    try {
      localStorage.setItem(toggle.id, String(toggle.checked));
    } catch {}
  });
})();
