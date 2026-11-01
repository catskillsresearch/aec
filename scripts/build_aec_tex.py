#!/usr/bin/env python3
"""Build aec.tex from flattened markdown using the DomainTheory TeX pipeline."""

from __future__ import annotations

import importlib.util
import os
import re
import textwrap
from pathlib import Path

AEC_ROOT = Path(__file__).resolve().parent.parent
DT_SCRIPTS = AEC_ROOT.parent / "DomainTheory" / "scripts"
ABSTRACT_MD = AEC_ROOT / "Abstract.md"

TITLE = "Lean formalization of OpenAI English proof of AEC eventual categoricity"
AUTHOR = "Lars Ericson"
DEFAULT_REPO_URL = "https://github.com/catskillsresearch/aec"

ABSTRACT_INTRO = (
    "This is a Lean 4 formalization using Grok 4.7 of the English text of the "
    "OpenAI paper with the following abstract:"
)
ABSTRACT_OUTRO = (
    "The paper quotes the original language throughout and adds the Lean translation "
    "alongside."
)
ABSTRACT_WIP = r"\textbf{Work in Progress: currently 74 holes.}"


def load_domain_theory_builder():
    path = DT_SCRIPTS / "build_arxiv_tex.py"
    spec = importlib.util.spec_from_file_location("build_arxiv_tex", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def read_openai_paper_abstract() -> str:
    if not ABSTRACT_MD.is_file():
        return ""
    text = ABSTRACT_MD.read_text(encoding="utf-8")
    m = re.search(
        r"^##\s+Paper abstract\s*\n+(.*?)(?=^##\s|\Z)",
        text,
        re.MULTILINE | re.DOTALL,
    )
    return m.group(1).strip() if m else ""


def compose_front_matter_abstract_md() -> str:
    paper = read_openai_paper_abstract()
    if not paper:
        return ""
    return f"{ABSTRACT_INTRO}\n\n*{paper}*\n\n{ABSTRACT_OUTRO}"


def extract_abstract_for_aec(text: str) -> tuple[str, str]:
    abstract_md = compose_front_matter_abstract_md()
    m = re.search(r"^##\s+Abstract\s*\n(.*?)(?=^##\s)", text, re.DOTALL | re.MULTILINE)
    if not m:
        return abstract_md, text
    body = text[: m.start()] + text[m.end() :]
    return abstract_md, body


def paper_abstract_latex(barx) -> str:
    paper_raw = read_openai_paper_abstract()
    if not paper_raw:
        return ""
    one_para = re.sub(r"\s*\n\s*", " ", paper_raw.strip())
    tex = barx.pandoc_to_latex(
        barx.github_math_to_tex(f"*{one_para}*"),
        shift=False,
    ).strip()
    tex = re.sub(r"\\tightlist\s*", "", tex)
    return tex


def build_title_page(barx, _abstract_latex: str, *, repo_url: str) -> str:
    abstract_block = ""
    segments = [ABSTRACT_INTRO]
    paper_tex = paper_abstract_latex(barx)
    if paper_tex:
        segments.append(paper_tex)
    segments.append(ABSTRACT_OUTRO)
    segments.append(ABSTRACT_WIP)
    body = " ".join(segments)
    if body.strip():
        abstract_block = f"\n\\begin{{abstract}}\n{body}\n\\end{{abstract}}\n"
    return textwrap.dedent(
        f"""
        \\title{{{TITLE}}}

        \\author{{{AUTHOR}\\\\\\url{{{repo_url}}}}}
        \\date{{\\today}}
        \\hypersetup{{
          pdftitle={{{TITLE}}},
          pdfauthor={{{AUTHOR}}}
        }}

        \\begin{{document}}

        \\maketitle
        {abstract_block}
        """
    ).strip()


def main() -> int:
    if not DT_SCRIPTS.is_dir():
        print(f"error: missing DomainTheory scripts at {DT_SCRIPTS}", flush=True)
        return 1

    os.environ.setdefault("ARXIV_TEX", str(AEC_ROOT / "aec.tex"))
    src = Path(os.environ["ARXIV_WITH_CODE"])
    if not src.is_file():
        print(
            f"error: missing {src}; run scripts/build_aec_tex.sh first",
            flush=True,
        )
        return 1

    import sys

    sys.path.insert(0, str(DT_SCRIPTS))
    import ai_model_cards as dt_model_cards  # noqa: E402

    import aec_model_cards  # noqa: E402

    aec_github = os.environ.get("AEC_GITHUB_URL", DEFAULT_REPO_URL)

    dt_model_cards.MODEL_CARDS = aec_model_cards.MODEL_CARDS
    dt_model_cards.ACKNOWLEDGMENTS_MARKDOWN = (
        aec_model_cards.ACKNOWLEDGMENTS_MARKDOWN.replace(
            aec_model_cards.DEFAULT_REPO_URL,
            aec_github,
        )
    )

    from lean_listing_sanitize import sanitize_lean_for_arxiv  # noqa: E402
    from strip_lean_comments import strip_lean_comments  # noqa: E402

    barx = load_domain_theory_builder()
    barx.extract_abstract = extract_abstract_for_aec

    aec_preamble = AEC_ROOT / "scripts" / "tex_preamble.tex"

    def write_listing_aec(code: str, listing_name: str) -> tuple[str, int]:
        barx.LISTINGS_DIR.mkdir(parents=True, exist_ok=True)
        if listing_name.endswith(".lean"):
            code = strip_lean_comments(code.rstrip("\n") + "\n").rstrip("\n")
        source = sanitize_lean_for_arxiv(
            code.rstrip("\n"),
            preamble_path=aec_preamble,
        )
        listing_path = barx.LISTINGS_DIR / listing_name
        barx.write_if_changed(listing_path, source + "\n")
        barx._WRITTEN_LISTINGS.add(listing_path.resolve())
        rel_path = listing_path.relative_to(barx.ROOT).as_posix()
        return rel_path, (len(source.splitlines()) if source else 0)

    barx.write_listing = write_listing_aec

    barx.GITHUB_URL = aec_github

    def canon_lean_hrefs_aec(md: str) -> str:
        by_name: dict[str, list[str]] = {}
        for path in AEC_ROOT.rglob("*.lean"):
            rel = path.relative_to(AEC_ROOT).as_posix()
            by_name.setdefault(path.name, []).append(rel)
        lean_href_re = re.compile(r"\]\(([^)]+\.lean)\)")

        def repl(m: re.Match[str]) -> str:
            href = m.group(1)
            if href.startswith("AEC/"):
                return m.group(0)
            name = Path(href).name
            cands = by_name.get(name, [])
            if len(cands) == 1:
                return f"]({cands[0]})"
            return m.group(0)

        return lean_href_re.sub(repl, md)

    def lean_file_href_aec(repo_rel: str) -> str:
        rel = repo_rel.lstrip("./")
        if rel.startswith("DomainTheory/"):
            rel = rel.removeprefix("DomainTheory/")
        if not rel.startswith("AEC/") and rel.endswith(".lean"):
            rel = f"AEC/{rel}"
        return f"{aec_github}/blob/main/{rel}"

    barx.canon_lean_hrefs_in_markdown = canon_lean_hrefs_aec
    barx.lean_file_href = lean_file_href_aec

    _lean_block_latex = barx.lean_block_latex

    def lean_block_latex_aec(
        code: str,
        listing_name: str,
        *,
        link_label: str | None = None,
        link_href: str | None = None,
    ) -> str:
        if link_href and link_href.startswith("DomainTheory/"):
            link_href = link_href.removeprefix("DomainTheory/")
        if (
            link_href is None
            and not listing_name.startswith("AEC/")
            and not listing_name.startswith("DomainTheory/")
        ):
            listing_name = f"AEC/{listing_name}"
        return _lean_block_latex(
            code,
            listing_name,
            link_label=link_label,
            link_href=link_href,
        )

    barx.lean_block_latex = lean_block_latex_aec

    barx.ROOT = AEC_ROOT
    barx.SCRIPTS = DT_SCRIPTS
    barx.LISTINGS_DIR = AEC_ROOT / "lean-listings"
    barx.FIGURES_DIR = AEC_ROOT / "figures"
    barx.PREAMBLE = AEC_ROOT / "scripts" / "tex_preamble.tex"
    barx.SRC = src
    barx.OUT = Path(os.environ["ARXIV_TEX"])
    barx.TITLE = TITLE
    barx.PDF_AUTHORS = AUTHOR
    barx.build_title_page = lambda abstract_latex: build_title_page(  # noqa: ARG005
        barx,
        abstract_latex,
        repo_url=aec_github,
    )

    def insert_front_matter_lists(latex: str) -> str:
        block = (
            "{\\pagestyle{empty}\n"
            "\\tableofcontents\n"
            "\\clearpage\n"
            "\\listoffigures\n"
            "\\clearpage\n"
            "}\n"
            "\\pagestyle{plain}\n\n"
        )
        return block + latex

    barx.insert_front_matter_lists = insert_front_matter_lists

    from repair_aec_latex import repair_aec_latex  # noqa: E402

    rc = barx.main()
    out = barx.OUT
    if out.is_file():
        out.write_text(repair_aec_latex(out.read_text(encoding="utf-8")), encoding="utf-8")
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
