#!/usr/bin/env bash
# 05-tee-keygen.sh -- Generate transport key pair inside the TEE
#
# Run this INSIDE the Confidential VM.
# Requires the safetee-demo binary (built from the golden-rs workspace).
#
# Outputs:
#   tpk.json -- Transport public key (safe to transfer to local machine)
#   tsk.json -- Transport secret key (SECRET -- stays on TEE!)
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ARTIFACTS_DIR="${ARTIFACTS_DIR:-$HOME/safetee-artifacts}"
SAFETEE_BIN="${SAFETEE_BIN:-safetee-demo}"

mkdir -p "$ARTIFACTS_DIR"

echo "=== SAFE-TEE: Transport Key Generation ==="
echo "  Artifacts dir: $ARTIFACTS_DIR"
echo ""

# Check if binary exists, if not try to build it
if ! command -v "$SAFETEE_BIN" &>/dev/null; then
  if [ -f "$SCRIPT_DIR/../../target/release/safetee-demo" ]; then
    SAFETEE_BIN="$SCRIPT_DIR/../../target/release/safetee-demo"
  else
    echo "Building safetee-demo..."
    cd "$SCRIPT_DIR/../.."
    cargo build --release --bin safetee-demo
    SAFETEE_BIN="$SCRIPT_DIR/../../target/release/safetee-demo"
  fi
fi

"$SAFETEE_BIN" keygen --output "$ARTIFACTS_DIR"

echo ""
echo "=== Transfer tpk.json to local machine: ==="
echo "  gcloud compute scp \$(hostname):$ARTIFACTS_DIR/tpk.json . --zone=\$ZONE"
