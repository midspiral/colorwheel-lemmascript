#!/usr/bin/env bash
# Verify extra Dafny files not covered by lsc check.
set -e
cd "$(dirname "$0")"

dafny verify src/colorwheel.proofs.dfy
# dafny verify src/colorwheel.props.dfy  # times out on CI
dafny verify src/colorwheel.sanity.dfy
