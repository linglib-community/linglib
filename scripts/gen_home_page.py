#!/usr/bin/env python3
"""Generate the landing page published at linglib.io/.

The page links the API documentation, the evaluations, the bibliography and the repository.

Usage, from the repository root:

    python3 scripts/gen_home_page.py            # write .lake/build/doc-site/index.html
    python3 scripts/gen_home_page.py --out DIR  # write DIR/index.html
"""

import argparse
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import site_shell  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
TEMPLATE = ROOT / "scripts" / "home_page" / "template.html"
DEFAULT_OUT = ROOT / ".lake" / "build" / "doc-site"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--out", type=Path, default=DEFAULT_OUT, help="directory for index.html")
    args = ap.parse_args()

    page = site_shell.render(TEMPLATE.read_text(encoding="utf-8"), "./", None,
                             site_shell.git_commit())
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "index.html").write_text(page, encoding="utf-8")
    print(f"wrote {args.out / 'index.html'}")


if __name__ == "__main__":
    main()
