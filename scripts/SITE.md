# The pages of linglib.io

The home page and `/bibliography/` are written by `gen_home_page.py` and `gen_bibliography_page.py`.
They share one chrome: `site.css` for the look, and `site_shell.py` for the header, menu, footer and
theme toggle, which it fills into the placeholders of each template. A new page uses
`site_shell.render` and adds itself to `MENU`; it does not copy the header or bring its own
stylesheet. The API docs under `/docs/` are doc-gen4's, except the landing page and the study and
theory pages, which `gen_docs_pages.py` writes over doc-gen4's.

The look is that of Hugo's PaperMod theme, which the site began on:

- System fonts, and no web fonts.
- Prose in the 720px column. Content wider than that, such as a table, takes the header's width
  (`.wide`) and scrolls inside it.
- Headings, links and code as `site.css` sets them. Color only where it carries data, such as a
  verdict mark or a bibliography role, defined as a variable with a dark-mode value.
- A page's text is its title and at most a line under it. No paragraphs on how the page is built,
  no uppercase or eyebrow labels, badges, pills, cards or rows of counts.
- The build date and commit in the footer only.

Mockups are read for structure and copy, not for type or color. Check a page at 1440px and 390px
wide, in light and dark mode, before opening a PR.

## The docs pages

`gen_docs_pages.py` rebuilds doc-gen4's study and theory pages from its output (read by
`docgen_index.py`) and writes them over doc-gen4's at the same addresses, `/docs/Studies/` and
`/docs/Linglib/{Semantics,Syntax,Pragmatics,Morphology,Phonology,Processing,Discourse,Logic}/`, so
links to a page keep landing. Core, Data and Fragments stay doc-gen4's. `/docs-new/`, where the study
pages were previewed, forwards to them. They depart from the rules above where a reference page
needs it:

- Three columns up to 1340px wide, prose still at 720px: the file's map at left, the declarations
  in the middle, where the file sits in the library at right. Readers scan and jump.
- A page's headline declarations are open cards. Every other declaration is a one-line row that
  opens in place. A study's headlines are its theorems with a docstring. A theory file's are the
  declarations its module docstring links to outside `Implementation notes`, `TODO`,
  `Notation` and `References`, as a mathlib header names a file's main definitions and results; a
  docstring linking to none falls back on the theorems with a docstring.
- A theory page's title is its docstring's first heading, with the `import` and the namespace under
  it, and its names print without that namespace. Its crumbs fold open the page's directory on the
  landing page.
- The graph has the same nodes on both kinds of page. On a study page, theory above, papers on a year
  axis with the study among them, languages below. On a theory page the file is in the middle,
  with the theory it builds on above it and what uses it below, down through the theory, the papers
  on their axis and the languages. Its right column lists the same, with the names each one uses,
  then the rest of the file's directory, then every import and importer.
- A study's right column has the theorems whose statements name another paper's definitions, with
  their sentences: this page's about other papers, and other pages' about this one. Say "about",
  never "uses" or "cites": a theorem may name a definition to argue against it.
- Color for the kind of node (study, theory, fragment) and solid against dashed for formalized
  or proved against not yet, the same vocabulary as the bibliography's roles.
- Every entry of a References list links to its bibliography entry, the study's own paper too;
  a paper another study formalizes adds a "formalized" link to that study.
- A study's definition's docstring that opens with a paper locator shows it as a tag naming the paper
  on hover. A bare number is a numbered example; any other display names its kind (`Eq. (12)`).
- The page's own styles and script are the shared files `docs_page/docs.css` and `docs.js`, since
  two thousand pages carry them.

Addresses are per page, relative to its depth under `/docs/`. A docstring's path to a file, which
doc-gen4 links from the site's root, is resolved to the file if there is one and left as text if
not; a page's links to mathlib and its dependencies, which the site does not carry, go to mathlib's
docs.

`/docs/random.html`, in the menu as Random, opens a study page at a theorem, a paper first so that
long files do not dominate. The page shows that theorem's sentence under the citation, labelled as
one result from the paper, with a link to the Lean statement. Don't call a sentence proved: Lean
checks the statement, not that the sentence says the same thing.

The landing page at `/docs/` (`docs_page/index.html`, where `/docs/Studies/` forwards) is the
page's title, one box that filters the page as you type and sends Enter to doc-gen4's search, and
every module in folds: theory by area, studies by decade, then fragments, data and core.

Every declaration doc-gen4 indexes keeps its anchor on the rebuilt page, so search and `find/`
links still land. `--check` confirms it, and that every relative link on a rebuilt page lands on a
file; either failing fails the deploy.
