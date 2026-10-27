# The pages of linglib.io

The home page, `/eval/` and `/bibliography/` are written by `gen_home_page.py`,
`gen_eval_page.py` and `gen_bibliography_page.py`. They share one chrome: `site.css` for the look,
and `site_shell.py` for the header, menu, footer and theme toggle, which it fills into the
placeholders of each template. A new page uses `site_shell.render` and adds itself to `MENU`; it
does not copy the header or bring its own stylesheet. The API docs under `/docs/` are doc-gen4's.

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

`gen_docs_pages.py` rebuilds doc-gen4's study pages from its output (read by `docgen_index.py`)
into `/docs-new/`, beside doc-gen4's `/docs/` until they replace it. They depart from the rules
above where a reference page needs it:

- Three columns up to 1340px wide, prose still at 720px: the file's map at left, the declarations
  in the middle, where the file sits in the library at right. Readers scan and jump.
- A study's headline theorems, the theorems with a docstring, are open cards. Every other
  declaration is a one-line row that opens in place.
- Color for the kind of node (study, theory, fragment) and solid against dashed for formalized
  or proved against not yet, the same vocabulary as the bibliography's roles.
- The page's own styles and script are the shared files `docs_page/docs.css` and `docs.js`, since
  a thousand pages carry them.

Every declaration doc-gen4 indexes keeps its anchor on the rebuilt page, so search and `find/`
links still land; `--check` confirms it.
