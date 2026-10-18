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
