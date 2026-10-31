#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
lake build
python3 scripts/proof_status.py --strict
audit_log=$(mktemp /tmp/affine_dual_jt_audit.XXXXXX)
trap 'rm -f -- "$audit_log"' EXIT
lake env lean AffineDualJT/Audit.lean > "$audit_log" 2>&1
cat -- "$audit_log"
if rg -q 'sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler|declared as an axiom' "$audit_log"; then
  printf '%s\n' 'Formalization audit failed: untrusted axiom dependency.' >&2
  exit 1
fi
