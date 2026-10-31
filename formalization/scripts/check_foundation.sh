#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
lake build AffineDualJT
audit_log=$(mktemp /tmp/affine_dual_jt_foundation.XXXXXX)
trap 'rm -f -- "$audit_log"' EXIT
lake env lean AffineDualJT/FoundationAudit.lean > "$audit_log" 2>&1
cat -- "$audit_log"
if rg -q 'sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler|declared as an axiom' "$audit_log"; then
  printf '%s\n' 'Completed-foundation audit failed: untrusted axiom dependency.' >&2
  exit 1
fi
