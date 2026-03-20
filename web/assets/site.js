const root = document.documentElement;
const storedTheme = localStorage.getItem("deppy-theme");
if (storedTheme) root.setAttribute("data-theme", storedTheme);
const toggle = document.querySelector("[data-theme-toggle]");
if (toggle) {
  const syncLabel = () => {
    const current = root.getAttribute("data-theme") === "light" ? "dark" : "light";
    toggle.textContent = "Switch to " + current + " theme";
  };
  syncLabel();
  toggle.addEventListener("click", () => {
    const next = root.getAttribute("data-theme") === "light" ? "dark" : "light";
    root.setAttribute("data-theme", next);
    localStorage.setItem("deppy-theme", next);
    syncLabel();
  });
}
const toc = document.querySelector("[data-generated-toc]");
if (toc) {
  const headings = Array.from(document.querySelectorAll("article h2, article h3"));
  if (!headings.length) {
    toc.remove();
  } else {
    const ul = document.createElement("ul");
    headings.forEach((heading) => {
      if (!heading.id) {
        heading.id = heading.textContent.toLowerCase().replace(/[^a-z0-9]+/g, "-").replace(/(^-|-$)/g, "");
      }
      const li = document.createElement("li");
      li.style.marginLeft = heading.tagName === "H3" ? "1rem" : "0";
      const a = document.createElement("a");
      a.href = "#" + heading.id;
      a.textContent = heading.textContent;
      li.appendChild(a);
      ul.appendChild(li);
    });
    toc.appendChild(ul);
  }
}
const current = window.location.pathname.replace(/index\.html$/, "");
document.querySelectorAll("nav a[data-slug]").forEach((link) => {
  const href = link.getAttribute("href");
  if (!href) return;
  const normalizedHref = new URL(href, window.location.href).pathname.replace(/index\.html$/, "");
  if (normalizedHref === current) link.classList.add("active");
});
