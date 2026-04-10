document.querySelectorAll(".copy-button").forEach((button) => {
  button.addEventListener("click", async () => {
    const targetId = button.getAttribute("data-copy-target");
    const target = targetId ? document.getElementById(targetId) : null;
    if (!target) {
      return;
    }

    try {
      await navigator.clipboard.writeText(target.textContent ?? "");
      const originalLabel = button.textContent;
      button.textContent = "Copied";
      button.classList.add("copied");
      window.setTimeout(() => {
        button.textContent = originalLabel;
        button.classList.remove("copied");
      }, 1600);
    } catch (error) {
      console.error("Failed to copy snippet", error);
    }
  });
});
