#!/usr/bin/env bash
set -euo pipefail
cp lean-toolchain.rc3 lean-toolchain
cp lakefile.rc3.toml lakefile.toml
lake update
lake exe cache get
lake build
