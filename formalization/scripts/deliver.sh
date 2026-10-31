#!/usr/bin/env bash
# Validate the sources, verify a fresh extraction, and replace the delivery ZIP.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
project_root=$PWD
archive_name=affine_dual_jt_complete-source.zip
stage_dir=
verification_dir=

cleanup() {
  local status=$?
  trap - EXIT
  if [[ -n "$stage_dir" ]]; then rm -rf -- "$stage_dir"; fi
  if [[ -n "$verification_dir" ]]; then rm -rf -- "$verification_dir"; fi
  if (( status != 0 )); then
    printf '\nDelivery failed. Do not send files from this run. See delivery_logs/.\n' >&2
  fi
  exit "$status"
}
trap cleanup EXIT

if (( $# != 0 )); then
  printf 'Usage: bash scripts/deliver.sh\n' >&2
  exit 2
fi
mkdir -p dist delivery_logs
for log in environment build foundation formalization verification; do
  : > "delivery_logs/$log.log"
done
for tool in bash python3 git rg lean lake sha256sum unzip mktemp tee; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    printf 'Missing required command: %s. Install the prerequisites in README.md first.\n' "$tool" >&2
    printf 'Missing required command: %s.\n' "$tool" >> delivery_logs/environment.log
    exit 127
  fi
done

record_environment() {
  local lean_version expected_version
  uname -sm
  python3 --version
  git --version
  rg --version
  lean_version=$(lean --version)
  printf '%s\n' "$lean_version"
  lake --version
  expected_version=$(< lean-toolchain)
  expected_version=${expected_version##*:v}
  if [[ "$lean_version" != *"version $expected_version,"* ]]; then
    printf 'Lean version does not match lean-toolchain.\n' >&2
    return 1
  fi
}

run_checks() (
  cd -- "$1"
  mkdir -p delivery_logs
  for log in environment build foundation formalization; do
    : > "delivery_logs/$log.log"
  done
  record_environment 2>&1 | tee delivery_logs/environment.log
  python3 scripts/proof_status.py --write --strict 2>&1 | tee delivery_logs/formalization.log
  lake build 2>&1 | tee delivery_logs/build.log
  bash scripts/check_foundation.sh 2>&1 | tee delivery_logs/foundation.log
  bash scripts/check_formalization.sh 2>&1 | tee -a delivery_logs/formalization.log
)

stage_dir=$(mktemp -d "$project_root/dist/.delivery.XXXXXX")
verification_dir=$(mktemp -d "${TMPDIR:-/tmp}/affine_dual_jt_verify.XXXXXX")
sha256sum lean-toolchain lakefile.toml lake-manifest.json > "$stage_dir/locked-files.sha256"

printf '\n[1/4] Build, refresh STATIC_CHECK.json, and audit the project.\n'
run_checks "$project_root"

printf '\n[2/4] Package the checked sources in a staging directory.\n'
python3 scripts/package_delivery.py --output "$stage_dir/$archive_name"

printf '\n[3/4] Check the ZIP and rebuild a fresh extraction (requires network access).\n'
verify_delivery() (
  cd -- "$stage_dir"
  python3 -m zipfile -t "$archive_name"
  sha256sum -c "$archive_name.sha256"
  unzip -l "$archive_name"
  unzip -q "$archive_name" -d "$verification_dir"
  cd -- "$verification_dir/affine_dual_jt_complete"
  sha256sum -c DELIVERY_MANIFEST.sha256
  # Restore dependencies from the locked manifest, without the original .lake/.
  test ! -e .lake
  lake exe cache get
  sha256sum -c "$stage_dir/locked-files.sha256"
  run_checks "$PWD"
)
verify_delivery 2>&1 | tee delivery_logs/verification.log
sha256sum -c "$stage_dir/locked-files.sha256"

printf '\n[4/4] Replace the default delivery ZIP and checksum.\n'
python3 - "$stage_dir" "$project_root/dist" "$archive_name" <<'PY'
import sys
from pathlib import Path

staging, destination = map(Path, sys.argv[1:3])
for name in (sys.argv[3], sys.argv[3] + ".sha256"):
    (staging / name).replace(destination / name)
PY
printf '\nDelivery passed. Send both files:\n  dist/%s\n  dist/%s.sha256\n' "$archive_name" "$archive_name"
