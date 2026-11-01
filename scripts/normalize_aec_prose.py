#!/usr/bin/env python3
"""Normalize OCR English prose in AEC text.md for Pandoc → pdfLaTeX."""

from __future__ import annotations

import re


# Figure 1 OCR debris accidentally merged into Lemma 2.1 proof (Section 2).
_FIGURE_JUNK_BLOCK = re.compile(
    r"\nIf the original\n\nUnbounded categoricity.*?"
    r"The small-code reduction then gives the uniform threshold of Theorem 1\.2\.\n\n",
    re.DOTALL,
)


def _fix_glued_dollar_math(text: str) -> str:
    """Insert spaces when OCR glued words to ``$...$`` (not inside math)."""
    text = re.sub(r"([A-Za-z0-9\)])(\$[_\\{A-Za-z])", r"\1 \2", text)
    text = re.sub(r"(\$[^$]+\$)([A-Za-z])", r"\1 \2", text)
    return text


def _unicode_replacements_outside_listings(text: str) -> str:
    text = text.replace("⇐⇒", "$\\Leftrightarrow$")
    text = text.replace("=⇒", "$\\Rightarrow$")
    text = text.replace("7−→", "$\\mapsto$")
    text = text.replace("7-→", "$\\mapsto$")
    text = text.replace("−→", "→")
    text = text.replace("$\\longrightarrow$", "→")
    return text


def _fix_set_and_logic_glue(text: str) -> str:
    text = re.sub(
        r"\$\s*D_\{i\}\s*=\$\{x ∈ L:",
        r"$D_i = \\{x \\in L :",
        text,
    )
    text = re.sub(
        r"U_\{i\} = L \$\$ D_\{i\}",
        r"U_i = L \\setminus D_i",
        text,
    )
    text = re.sub(
        r"W_\{i\} = L \$\$ V_\{i\}",
        r"W_i = L \\setminus V_i",
        text,
    )
    text = re.sub(
        r"\$\s*\\\(\s*\\\s*\)\s*V_\{i\}",
        r"\\setminus V_i",
        text,
    )
    text = re.sub(
        r"\$S_\{L\} \(A\^\{-}, A\^\{\+\}\) =\$\{x ∈ L \\ A:",
        r"$$S_L(A^-, A^+) = \\{x \\in L \\setminus A :",
        text,
    )
    text = re.sub(
        r"A\^\{-} < x < A\^\{\+\} \}\.\$",
        r"A^- < x < A^+\\}.$$",
        text,
    )
    text = re.sub(
        r"\$p D_\{F\} q\$⇐⇒\$",
        r"$p D_F q \\Leftrightarrow ",
        text,
    )
    text = re.sub(
        r"\$p D_\{F\} q\$\\Leftrightarrow\$",
        r"$p D_F q \\Leftrightarrow ",
        text,
    )
    return text


def _fix_kappa_closure_block(text: str) -> str:
    old = (
        "$κ_{n+1} > 2^{κ_{n}}$and$κ_{n+1} > sup{u_{i}$"
        "(θ):$θ ≤ κ_{n}, i ∈$A},"
    )
    new = (
        "$\\kappa_{n+1} > 2^{\\kappa_n}$ and "
        "$\\kappa_{n+1} > \\sup\\{ u_i(\\theta) : \\theta \\le \\kappa_n,\\, i \\in A \\},$"
    )
    return text.replace(old, new)


def _fix_star_superscripts(text: str) -> str:
    """``J^*`` outside ``{...}`` breaks Pandoc (``*`` opens emphasis)."""
    # Non-raw ``"^{\\ast}"`` parses ``\\a`` as bell; use a raw literal for TeX ``\ast``.
    star = r"^{\ast}"
    text = text.replace("^{∗}", star)
    text = re.sub(r"\^\{\*\}", lambda _m, s=star: s, text)
    text = re.sub(r"\^\{\\ast\}", lambda _m, s=star: s, text)
    for base in ("J", "T", "z", "A", "S", "R", "P", "Q", "X", "U", "V", "W", "K"):
        text = re.sub(
            rf"\$({base})\^(\*|\{{\*}}|\{{\\ast}})",
            lambda m, b=base, s=star: "$" + b + s,
            text,
        )
        text = re.sub(
            rf"(?<=[^\\])({base})\^(\*|\{{\*}}|\{{\\ast}})(?=[^*])",
            lambda m, b=base, s=star: b + s,
            text,
        )
    text = re.sub(r"J\^\*", lambda m: "J" + star, text)
    text = re.sub(r"T\^\*", lambda m: "T" + star, text)
    text = re.sub(r"z\^\*", lambda m: "z" + star, text)
    text = re.sub(r"K\^\*", lambda m: "K" + star, text)
    text = text.replace("$\\ $", "$\\setminus$")
    text = text.replace("$\\setminus$", " $\\setminus$ ")  # noop loop guard below
    text = text.replace(" $\\setminus$ ", " $\\setminus$ ")
    text = re.sub(r"\$\s*\\\$\s*", r"$\\setminus$ ", text)
    return text


def normalize_aec_prose(text: str) -> str:
    text = _FIGURE_JUNK_BLOCK.sub("\nIf the original ", text)
    text = _unicode_replacements_outside_listings(text)
    text = _fix_glued_dollar_math(text)
    text = _fix_set_and_logic_glue(text)
    text = _fix_kappa_closure_block(text)
    text = _fix_star_superscripts(text)
    text = re.sub(r"\$≤_\{K\}\$", r"$\\leq_K$", text)
    text = re.sub(r"\$≤_\{K\}\),", r"$\\leq_K$),", text)
    text = re.sub(
        r"that is,\$2\^\{κ\} < 2\^\{κ\^\{\+\}\}\$",
        r"that is, $2^{\\kappa} < 2^{\\kappa^+}$",
        text,
    )
    text = re.sub(
        r"not at\$ℶ_\{\(2\^\{ℵ_\{0\}\}\} \+ = ℶ_\{ω_\{2\}\},",
        r"not at $\\beth_{(2^{\\aleph_0})^+} = \\beth_{\\omega_2}$,",
        text,
    )
    text = text.replace("for )\n\narbitrary AECs.", "for arbitrary AECs.")
    return text
