"""Model-card registry for the AEC PDF acknowledgements (section 15.1)."""

from __future__ import annotations

import re
from dataclasses import dataclass

from ai_model_cards import (  # DomainTheory/scripts on sys.path
    REFERENCES_BEGIN,
    REFERENCES_END,
    TOOL_BULLETS_BEGIN,
    TOOL_BULLETS_END,
    _replace_between,
)


@dataclass(frozen=True)
class ModelCard:
    label: str
    cite_key: str
    tool_note: str
    bib_entry_type: str
    bib_fields: dict[str, str]


MODEL_CARDS: tuple[ModelCard, ...] = (
    ModelCard(
        label="Cursor Composer 2.5",
        cite_key="Cmp25",
        tool_note=(
            "editing and build tooling in Cursor, medium proof obligations where the "
            "strategy was already fixed, and maintenance of the markdown-to-TeX pipeline "
            "(`composer-2.5`)."
        ),
        bib_entry_type="misc",
        bib_fields={
            "author": "{Anysphere, Inc.}",
            "title": "Composer 2.5",
            "howpublished": (
                "Model announcement and documentation, "
                "\\url{https://cursor.com/blog/composer-2-5}; "
                "model card as integrated in Cursor, "
                "\\url{https://cursor.com/docs/models}"
            ),
            "year": "2026",
            "note": "accessed 2026",
        },
    ),
    ModelCard(
        label="Cursor Grok 4.7",
        cite_key="Grk47",
        tool_note=(
            "primary agent model for this formalization: Lean 4 proof development, "
            "English proof notes aligned with the OpenAI paper, dependency-ordered "
            "module wiring under `AEC/`, and constructivity checks. Used via the "
            "Cursor agent environment."
        ),
        bib_entry_type="misc",
        bib_fields={
            "author": "xAI and {Anysphere, Inc.}",
            "title": "Grok 4.7",
            "howpublished": (
                "Model documentation, \\url{https://docs.x.ai/docs/models}; "
                "Cursor model catalog, \\url{https://cursor.com/docs/models}"
            ),
            "year": "2026",
            "note": "accessed 2026",
        },
    ),
)

ACKNOWLEDGMENTS_MARKDOWN = r"""## Acknowledgments

### AI-assisted development

The human author retains sole responsibility for the mathematical content, the choice of
formalization route, and every formal claim in this work. Following standard publisher practice
(e.g., COPE guidance on authorship and AI tools \cite{COPE24}), **no large language model is listed
as a co-author** — authorship implies an accountability that automated systems cannot bear.

We gratefully acknowledge assistance from the following tools in this revision
(auto-generated from `scripts/aec_model_cards.py` when building `aec.tex`):

<!-- AI_MODEL_TOOL_BULLETS -->
<!-- /AI_MODEL_TOOL_BULLETS -->

All definitions, constructivity audits, and final prose were reviewed by the human author, who takes
full responsibility for them.

### Artifact availability and reproducibility

The Lean development lives in this repository. Build locally:

```bash
lake exe cache get
lake build AEC
```

Rebuild the PDF from the note tree rooted at `aec.md`:

```bash
bash scripts/build_aec_pdf.sh
```

"""


def render_tool_bullets() -> str:
    return "\n".join(
        f"- **{card.label}** \\cite{{{card.cite_key}}} — {card.tool_note}"
        for card in MODEL_CARDS
    )


def render_model_bibtex() -> str:
    blocks: list[str] = []
    for card in MODEL_CARDS:
        lines = [f"@{card.bib_entry_type}{{{card.cite_key},"]
        for key, value in card.bib_fields.items():
            lines.append(f"  {key} = {{{value}}},")
        lines.append("}")
        blocks.append("\n".join(lines))
    return "\n\n".join(blocks)


def inject_acknowledgments(text: str) -> str:
    if re.search(r"^##\s+Acknowledgments\s*$", text, re.MULTILINE):
        return text
    m = re.search(r"^##\s+References\s*$", text, re.MULTILINE)
    if not m:
        raise RuntimeError(
            "missing ## References in narrative; needed to place Acknowledgments before it"
        )
    return text[: m.start()] + ACKNOWLEDGMENTS_MARKDOWN + "\n" + text[m.start() :]


def inject_model_cards(text: str) -> str:
    text = inject_acknowledgments(text)
    if TOOL_BULLETS_BEGIN not in text:
        raise RuntimeError(
            f"missing {TOOL_BULLETS_BEGIN} after Acknowledgments injection"
        )
    text = _replace_between(text, TOOL_BULLETS_BEGIN, TOOL_BULLETS_END, render_tool_bullets())
    if REFERENCES_BEGIN in text and REFERENCES_END in text:
        text = _replace_between(text, REFERENCES_BEGIN, REFERENCES_END, "")
    return text
