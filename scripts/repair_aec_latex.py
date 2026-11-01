#!/usr/bin/env python3
"""Fix recurring Pandoc/pdfLaTeX breakage in AEC narrative math."""

from __future__ import annotations

import re


def _fix_pandoc_textsuperscript(tex: str) -> str:
    """Pandoc turns ``2^{\kappa^+}`` into ``2\\textsuperscript{\\{\\kappa}+}``."""
    tex = re.sub(
        r"\(2\\textsuperscript\{\\\{a_\{ξ\}\)\}\\{\+\}",
        r"(2^{a_{\\xi}})^{+}",
        tex,
    )
    tex = re.sub(
        r"\(2\\textsuperscript\{\\\{a_\{\\xi\}\)\}\\{\+\}",
        r"(2^{a_{\\xi}})^{+}",
        tex,
    )
    tex = re.sub(
        r"2\\textsuperscript\{\\\{([^}]+)\+\}\}",
        r"2^{\1^+}",
        tex,
    )
    tex = re.sub(
        r"2\\textsuperscript\{\\\{([^}]+)\}\+\}",
        r"2^{\1^+}",
        tex,
    )
    tex = re.sub(r"2\^\{\}\\\{([^}]+)\\\}", r"2^{\1}", tex)
    tex = tex.replace(
        "\\lt 2\\textsuperscript{\\{\\kappa}+\\}",
        "\\lt 2^{\\kappa^+}",
    )
    return tex


def _fix_pandoc_superscripts(tex: str) -> str:
    """Pandoc ``\\^{}\\{x\\}`` / ``\\^{}x`` → ``^{x}`` (pdfLaTeX math)."""
    prev = None
    while prev != tex:
        prev = tex
        tex = re.sub(r"\^\{\}\\{([^\\]+)\\\}", r"^{\1}", tex)
    tex = re.sub(r"\^\{\}([+\-*])", r"^{\1}", tex)
    tex = re.sub(r"\^\{\}([A-Za-z0-9])", r"^{\1}", tex)
    tex = tex.replace("\\^{", "^{")
    return tex


def _fix_textless_in_math(tex: str) -> str:
    """Pandoc ``\\textless{}`` inside ``$...$`` → ``<``."""

    def fix_segment(m: re.Match[str]) -> str:
        body = m.group(1)
        body = body.replace("\\textless{}", "<")
        body = body.replace("\\textgreater{}", ">")
        return f"${body}$"

    return re.sub(r"\$([^$]+)\$", fix_segment, tex)


def _fix_subscript_artifacts(tex: str) -> str:
    """Pandoc splits ``M_{2}`` into ``M\\}\\{2\\}`` and escapes ``\\leq_K``."""
    tex = re.sub(r"_\\\{([^}]+)\\\}", r"_{\1}", tex)
    tex = re.sub(r"\\_\{([^}]+)\}", r"_{\1}", tex)
    tex = re.sub(r"([A-Za-z])\}\\\{([^}]+)\\\}", r"\1_{\2}", tex)
    tex = tex.replace("\\leq\\_K", "\\leq_K")
    tex = tex.replace("\\leq\\emph{K", "\\leq_K")
    tex = tex.replace("\\le\\emph{K", "\\leq_K")
    tex = re.sub(r"\(b\\_i\)\}\\{i < \\delta\\}", r"(b_i)_{i < \\delta}", tex)
    tex = re.sub(r"\$ M \\leq_K", r"$M \\leq_K", tex)
    tex = re.sub(r"\\emph\{\\{([^}]+)\\\}\.", r"_{\1}.", tex)
    tex = re.sub(r"\\emph\{\\{([^}]+)\\\}\$", r"_{\1}$", tex)
    tex = re.sub(r"\\emph\{\\{([^}]+)\\\}", r"_{\1}", tex)
    tex = re.sub(r"\\aleph\\emph\{(\d+)\)", r"\\aleph_\1)", tex)
    tex = re.sub(r"\)\}\{([^}]+)\}", r")_{\1}", tex)
    tex = re.sub(r"\(M\\_i\)\}\\{i \\le \\delta\\}", r"(M_i)_{i \\le \\delta}", tex)
    tex = re.sub(
        r"\(\\kappa_\{n\}\)\}\\{n < \\omega\\}",
        r"(\\kappa_{n})_{n < \\omega}",
        tex,
    )
    tex = re.sub(r"\$ \$\(\\kappa_\{n\}\)_\{n < \\omega\}\)\$", r"$(\\kappa_{n})_{n < \\omega}$", tex)
    tex = re.sub(r"2\^\{\}\\{\\lambda\\}", r"2^{\\lambda}", tex)
    tex = re.sub(r"2\^\{\}\\{\\kappa_\{n\}\}", r"2^{\\kappa_{n}}", tex)
    tex = re.sub(
        r"X_\{a\\_\\\{L\\\}\}\$ \(t\)",
        r"X_{a_L(t)}",
        tex,
    )
    tex = tex.replace(
        "\\(\\lVert X_{t}\\rVert\\).$ It",
        "$\\|X_t\\|$. It",
    )
    tex = re.sub(r"([UX])\}\{t\^\{-\}\}", r"\1_{t,-}", tex)
    tex = re.sub(r"([UX])\}\{t\^\{\+\}\}", r"\1_{t,+}", tex)
    tex = re.sub(r"2\^\{\}\\{κ_\{n\}\}", r"2^{\\kappa_{n}}", tex)
    tex = re.sub(r"\(([A-Za-z])\\_i\)\}\\{([^}]+)\\}", r"(\1_i)_{\2}", tex)
    tex = tex.replace(
        "$ S_{L} (A^{-}, A^{+}) =\\({x ∈ L \\ A:\\) A^{-} < x < A^{+} \\}.$",
        "\\[ S_L(A^{-}, A^{+}) = \\{x \\in L \\setminus A : A^{-} < x < A^{+}\\}.\\]",
    )
    tex = tex.replace(
        "$ D_{i} =$\\{x ∈ L: (∃j \\textless{} i) $ x ≤ p_{j} \\}, "
        "U_{i} = L \\(\\$ D_{i}, c_{i} = (D_{i}, U_{i}), B_{i} = (c_{i}, p_{i}].\\)",
        "$D_i = \\{x \\in L : (\\exists j < i)\\, x \\le p_j\\},\\ "
        "U_i = L \\setminus D_i,\\ c_i = (D_i, U_i),\\ B_i = (c_i, p_i].$",
    )
    tex = tex.replace("$ B_{0} = \\{p_{0} \\}, B_{j+1} = (p_{j}, p_{j+1}{]}.$", 
        "$B_0 = \\{p_0\\},\\ B_{j+1} = (p_j, p_{j+1}].$")
    tex = tex.replace("\\(\\$", "\\setminus ")
    tex = re.sub(r"L \\\\\\ \\\\ V_\{i\}", r"L \\setminus V_i", tex)
    tex = re.sub(r"L \(\s*\\\s*\) V_\{i\}", r"L \\setminus V_i", tex)
    tex = tex.replace("= $\\{", "= \\{")
    tex = tex.replace(
        "They satisfy \\(θ^{+} ≤\\) a,$ a^{θ} ≤\\(µ,\\)τ_{µ} \\textgreater$ a.",
        "They satisfy $\\theta^{+} \\le a$, $a^{\\theta} \\le \\mu$, $\\tau_{\\mu} > a$.",
    )
    tex = re.sub(
        r"_\\\{i\\textless{} ([^}]+)\\\}",
        r"_{i < \1}",
        tex,
    )
    tex = tex.replace(
        "\\(κ_{n+1} > 2^{κ_{n}}\\) and \\(κ_{n+1} > sup{u_{i}\\) "
        "(θ):\\(θ ≤ κ_{n}, i ∈\\) A\\},",
        "\\( \\kappa_{n+1} > 2^{\\kappa_n} \\) and "
        "\\( \\kappa_{n+1} > \\sup\\{ u_i(\\theta) : \\theta \\le \\kappa_n,\\, i \\in A \\} \\),",
    )
    tex = tex.replace(
        "$ I_{µ,η} =\\(α<µ.η+\\) Q_{η},$",
        "$I_{\\mu,\\eta} = (\\alpha < \\mu \\cdot \\eta) + Q_{\\eta},$",
    )
    tex = re.sub(r"\$ N \\leq_K", r"$N \\leq_K", tex)
    tex = re.sub(r"\$ \(([a-z])\\_\{", r"$(\1_{", tex)
    return tex


def _fix_broken_star_superscripts(tex: str) -> str:
    """Pandoc emphasis on ``*`` in ``J^*`` → ``J^{}\\emph{$``."""
    tex = tex.replace("J^{}\\emph{$", "J^{*}")
    tex = tex.replace("T^{}\\emph{$", "T^{*}")
    tex = tex.replace("z^{}\\emph{$", "z^{*}")
    tex = re.sub(
        r"\$ z\^\{\*\} in a presentation \$ E\(J\^",
        r"$z^{\\ast}$ in a presentation $E(J^{",
        tex,
    )
    tex = re.sub(r"E\(J\^\{\*\}\)", r"E(J^{\\ast})", tex)
    tex = tex.replace("X^{}\\{\\emph{\\}$", "X^{*}")
    tex = tex.replace("X^{}\\{\\emph{\\}", "X^{*}")
    tex = tex.replace("K^{}\\{\\emph{\\}$", "K^{*}")
    tex = tex.replace("K^{}\\{\\emph{\\},", "K^{*},")
    tex = re.sub(r"\$ K\^\{\*\} of K", r"$K^{*}$ of $K$", tex)
    tex = re.sub(r"\$ K\^\{\*\},", r"$K^{*}$,", tex)
    tex = re.sub(r"in \$ K\^\{\*\},", r"in $K^{*}$,", tex)
    tex = re.sub(
        r"\$ X \\to X\^\{\*\} and a \$ D \$",
        r"$X \\to X^{*}$ and a $D$",
        tex,
    )
    tex = re.sub(r"\$ Z \\to PX\^\{\*\}\$", r"$Z \\to P(X^{*})$", tex)
    tex = re.sub(
        r"\$ K \\to K\^\{\*\}, \$ J \\to K\^\{\*\}\$",
        r"$K \\to K^{*}$, $J \\to K^{*}$",
        tex,
    )
    tex = re.sub(
        r"K\^\{\}\\{\\emph\{\\\}, J \\longrightarrow K\^\{\*\}",
        r"$K \\to K^{*}$, $J \\to K^{*}$",
        tex,
    )
    tex = re.sub(
        r"\$\\lVert M \\\(\\rVert\\\) ≥ λ\}\{0\},",
        r"$\\|M\\| \\ge \\lambda_0$,",
        tex,
    )
    tex = re.sub(r"∈ B \\A", r"$\\in B \\setminus A$", tex)
    tex = re.sub(r"a ∈ B \\A", r"$a \\in B \\setminus A$", tex)
    tex = re.sub(r"2\^\{\}\\{κ\}\{n\}\}", r"2^{\\kappa_n}", tex)
    tex = re.sub(r"\(\\kappa\\emph\{n\)\}", r"(\\kappa_{n})", tex)
    tex = re.sub(r"2\^\{\}\\{\\lambda\}", r"2^{\\lambda}", tex)
    tex = re.sub(r"2\^\{\}\\{κ\\emph\{n\\}", r"2^{\\kappa_{n}}", tex)
    tex = re.sub(r"2\^\{\}\\{κ_\{n\}\}", r"2^{\\kappa_n}", tex)
    tex = re.sub(
        r"\\simeq\\emph\{\\{X_\{\\emptyset\}\} U_\{\\emptyset\}\$",
        r"\\simeq_{X_{\\emptyset}} U_{\\emptyset}$",
        tex,
    )
    tex = re.sub(
        r"\\simeq\\emph\{\\{X_\{∅\}\}",
        r"\\simeq_{X_{\\emptyset}}",
        tex,
    )
    tex = tex.replace("J^{}}", "J^{*}")
    tex = re.sub(
        r"\$ J \\subseteq J\^\{\}\\emph\{\$",
        r"$J \\subseteq J^{*}$",
        tex,
    )
    tex = re.sub(
        r"\\subseteq J\^\{\}\\emph\{\$",
        r"\\subseteq J^{*}$",
        tex,
    )
    tex = re.sub(
        r"T\\textsuperscript\{\* \\subseteq J\}\*",
        r"$T^{*} \\subseteq J^{*}$",
        tex,
    )
    tex = re.sub(r"(\w)\^\{\}\}", r"\1^{*}", tex)
    tex = re.sub(
        r"\\emph\{\\{X\^\{fr\}\}\\{i\}\}",
        r"_{X^{\\mathrm{fr}}_i}",
        tex,
    )
    tex = re.sub(
        r"tp\(b/X_\{i\}\) = tp\(b/X_\{0\}\)\\emph\{\\{X\^\{fr\}\}\\{i\}\}",
        r"\\mathrm{tp}(b/X_i) = \\mathrm{tp}(b/X_0)^{\\mathrm{fr}}_{X_i}",
        tex,
    )
    tex = re.sub(
        r"\\emph\{\\{M\^\{fr\}\}\\{i\}\}",
        r"^{\\mathrm{fr}}_{M_i}",
        tex,
    )
    tex = re.sub(
        r"tp\(b_\{i\} /M_\{i\}\) = tp\(b_\{i\} /A\)\\emph\{\\{M\^\{fr\}\}\\{i\}\}",
        r"\\mathrm{tp}(b_i/M_i) = \\mathrm{tp}(b_i/A)^{\\mathrm{fr}}_{M_i}",
        tex,
    )
    return tex


def _fix_split_longrightarrow(tex: str) -> str:
    pat = re.compile(
        r"\$\s*([^$]+)\$\\longrightarrow\s*\$\s*([^$]+)\$",
    )

    def merge(m: re.Match[str]) -> str:
        left, right = m.group(1).strip(), m.group(2).strip()
        if len(left) > 48 or len(right) > 48:
            return m.group(0)
        if any(x in left for x in (".", "For ", "for ", "embedding")):
            return m.group(0)
        return f"${left} \\longrightarrow {right}$"

    prev = None
    while prev != tex:
        prev = tex
        tex = pat.sub(merge, tex)
    return tex


def _fix_nested_math_delimiters(tex: str) -> str:
    """Pandoc sometimes emits ``$\\(...\\)`` (extra ``$`` before ``\\(``)."""
    tex = tex.replace("$\\(", "\\(")
    tex = re.sub(
        r"\\textless\$([^\s$]+)\.",
        r"\\(< \1\\).",
        tex,
    )
    tex = re.sub(
        r"\\\(\\lVert M_\{n\}\\rVert\\\) \\textless\$?\s*µ",
        r"\\(\\lVert M_n\\rVert < \\mu\\)",
        tex,
    )
    return tex


def _fix_inline_math_wrappers(tex: str) -> str:
    """``\\(⊔\\)`` inside ``$...$`` → ``\\sqcup``."""
    for ch, cmd in (
        ("⊔", r"\sqcup"),
        ("⊕", r"\oplus"),
        ("⊗", r"\otimes"),
    ):
        tex = tex.replace(f"\\({ch}\\)", cmd)
    return tex


def repair_aec_latex(tex: str) -> str:
    marker = "\\begin{document}"
    idx = tex.find(marker)
    if idx < 0:
        return tex
    head, tail = tex[: idx + len(marker)], tex[idx + len(marker) :]
    tail = _fix_pandoc_textsuperscript(tail)
    tail = _fix_pandoc_superscripts(tail)
    tail = _fix_textless_in_math(tail)
    tail = _fix_subscript_artifacts(tail)
    tail = _fix_inline_math_wrappers(tail)
    tail = _fix_nested_math_delimiters(tail)
    tail = _fix_split_longrightarrow(tail)
    tail = _fix_broken_star_superscripts(tail)
    return head + tail
