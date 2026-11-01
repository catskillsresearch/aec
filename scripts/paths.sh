# Shared paths for aec.md → aec.tex → aec.pdf (DomainTheory pipeline).
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DOMAIN_THEORY="$(cd "${ROOT}/../DomainTheory" && pwd)"
BUILD="${ROOT}/.build/aec"

export ARXIV_ROOT_MD="${ROOT}/aec.md"
export ARXIV_MD="${BUILD}/flatten.md"
export ARXIV_WITH_CODE="${BUILD}/with_code.md"
export ARXIV_TEX="${ROOT}/aec.tex"
export TEXINPUTS="${ROOT}//:${TEXINPUTS:-}"
