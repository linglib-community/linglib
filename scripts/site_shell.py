"""The chrome every page of linglib.io outside the API docs shares.

A page's template carries four placeholders, which `render` fills: `<!--SITE_HEAD-->` (favicon,
saved theme, the stylesheet `site.css`), `<!--SITE_HEADER-->` (logo, theme toggle and the menu with
the current page marked), `<!--SITE_FOOTER-->` (build date and commit, back-to-top link) and
`<!--SITE_SCRIPT-->` (theme toggle, back-to-top). A page added to the site is added to `MENU`.
`scripts/SITE.md` says what a page may add to this chrome.
"""

import datetime
import html
import os
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CSS = ROOT / "scripts" / "site.css"
REPO = "https://github.com/linglib-community/linglib"
# Label and address of each menu item, relative to the site's root unless absolute.
MENU = [("Docs", "docs/"), ("Evaluations", "eval/"), ("Bibliography", "bibliography/"),
        ("GitHub", REPO)]

TOGGLE = """<button id="theme-toggle" type="button" aria-label="Toggle dark mode" title="Toggle dark mode">
        <svg id="moon" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M21 12.79A9 9 0 1111.21 3 7 7 0 0021 12.79z"/></svg>
        <svg id="sun" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="12" r="5"/><path d="M12 1v2M12 21v2M4.22 4.22l1.42 1.42M18.36 18.36l1.42 1.42M1 12h2M21 12h2M4.22 19.78l1.42-1.42M18.36 5.64l1.42-1.42"/></svg>
      </button>"""

SCRIPT = """<script>
document.getElementById("theme-toggle").addEventListener("click", () => {
  const root = document.documentElement;
  const dark = root.dataset.theme ? root.dataset.theme === "dark" : matchMedia("(prefers-color-scheme: dark)").matches;
  root.dataset.theme = dark ? "light" : "dark";
  try { localStorage.setItem("pref-theme", root.dataset.theme); } catch (e) {}
});
const topLink = document.getElementById("top-link");
addEventListener("scroll", () => topLink.classList.toggle("on", scrollY > 800), { passive: true });
</script>"""


def git_commit():
    """The commit the site is built from: GitHub's, else the checkout's `HEAD`, else none."""
    sha = os.environ.get("GITHUB_SHA")
    if not sha:
        try:
            sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True,
                                 text=True, check=True).stdout.strip()
        except (OSError, subprocess.CalledProcessError):
            sha = ""
    return sha


def head(root):
    return (f'<link rel="icon" href="{root}docs/favicon.svg">\n'
            '<script>try { var t = localStorage.getItem("pref-theme"); '
            'if (t) document.documentElement.dataset.theme = t; } catch (e) {}</script>\n'
            f'<style>\n{CSS.read_text(encoding="utf-8")}</style>')


def header(root, current):
    items = []
    for label, href in MENU:
        href = href if href.startswith("https:") else root + href
        mark = ' aria-current="page"' if label == current else ""
        items.append(f'      <li><a href="{href}"{mark}>{html.escape(label)}</a></li>')
    items = "\n".join(items)
    return f"""<header>
  <nav class="nav" aria-label="Site">
    <div class="logo">
      <a href="{root}">Linglib</a>
      {TOGGLE}
    </div>
    <ul class="menu">
{items}
    </ul>
  </nav>
</header>"""


def footer(sha):
    built = datetime.date.today().isoformat()
    commit = f' from <a href="{REPO}/tree/{sha}">{sha[:9]}</a>' if sha else ""
    return (f'<footer class="footer">Built {built}{commit}</footer>\n'
            '<a href="#top" class="top-link" id="top-link" aria-label="Back to top" '
            'title="Back to top"><svg viewBox="0 0 12 6" fill="currentColor" aria-hidden="true">'
            '<path d="M12 6H0l6-6z"/></svg></a>')


def render(template, root, current, sha):
    """Fill the chrome of a page `template`. `root` is the site's root relative to the page
    (`./`, `../`), `current` the label of the page's menu item, if it has one."""
    for mark in ("<!--SITE_HEAD-->", "<!--SITE_HEADER-->", "<!--SITE_FOOTER-->",
                 "<!--SITE_SCRIPT-->"):
        assert template.count(mark) == 1, f"the template needs exactly one {mark}"
    assert current is None or current in dict(MENU), f"{current} is not in the menu"
    return (template.replace("<!--SITE_HEAD-->", head(root))
            .replace("<!--SITE_HEADER-->", header(root, current))
            .replace("<!--SITE_FOOTER-->", footer(sha))
            .replace("<!--SITE_SCRIPT-->", SCRIPT))
