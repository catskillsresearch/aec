#!/usr/bin/env bash
# Regenerate aec.tex from aec.md, then compile aec.pdf with pdfLaTeX (latexmk).
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=paths.sh
source "${SCRIPT_DIR}/paths.sh"

cd "${ROOT}"

if [[ "${1:-}" != "--pdf-only" ]]; then
  bash "${SCRIPT_DIR}/build_aec_tex.sh"
else
  shift
fi

TEX="${ARXIV_TEX}"
PDF="${ROOT}/aec.pdf"

if [[ ! -f "${TEX}" ]]; then
  echo "error: missing ${TEX}; run scripts/build_aec_tex.sh" >&2
  exit 1
fi

echo "==> Compiling ${PDF}"
latexmk -C "${TEX}" >/dev/null 2>&1 || true
if ! latexmk -pdf -interaction=nonstopmode -halt-on-error "${TEX}"; then
  echo "pdflatex failed; log tail:" >&2
  tail -n 50 "${ROOT}/aec.log" >&2 || true
  exit 1
fi

if [[ ! -f "${PDF}" ]]; then
  echo "error: ${PDF} missing after latexmk" >&2
  exit 1
fi

echo "wrote ${PDF} ($(du -h "${PDF}" | cut -f1), $(pdfinfo "${PDF}" 2>/dev/null | awk '/^Pages:/ {print $2}') pages)"
