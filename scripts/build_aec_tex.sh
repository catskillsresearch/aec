#!/usr/bin/env bash
# Flatten aec.md → aec.tex (+ lean-listings/, figures/).
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
# shellcheck source=paths.sh
source "${SCRIPT_DIR}/paths.sh"

if [[ ! -d "${DOMAIN_THEORY}/scripts" ]]; then
  echo "error: expected DomainTheory at ${DOMAIN_THEORY}" >&2
  exit 1
fi

mkdir -p "${BUILD}"

echo "==> Flattening aec.md → ${ARXIV_MD}"
python3 "${SCRIPT_DIR}/flatten_aec_md.py" \
  --root "${ARXIV_ROOT_MD}" \
  --out "${ARXIV_MD}"

echo "==> Preparing ${ARXIV_WITH_CODE}"
python3 "${DOMAIN_THEORY}/scripts/generate_arxiv_with_code.py"

echo "==> Building ${ARXIV_TEX}"
python3 "${SCRIPT_DIR}/build_aec_tex.py"
python3 "${SCRIPT_DIR}/verify_lean_listings.py"
