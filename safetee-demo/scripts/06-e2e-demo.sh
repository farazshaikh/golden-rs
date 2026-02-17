#!/usr/bin/env bash
# 06-e2e-demo.sh -- End-to-end SAFE-TEE demo orchestration
#
# This script orchestrates the full key delivery flow:
#   1. SSH to VM, generate transport key, SCP tpk back
#   2. Run local SAFE-TEE network (DKG + vetKey derivation)
#   3. SCP encrypted vetkey + ciphertext to VM
#   4. SSH to VM, decrypt and print the secret
#
# Prerequisites:
#   - VM is running with CC mode ON (scripts 01-03 completed)
#   - safetee-demo binary is built locally
#   - safetee-demo binary is available on the VM (or Rust toolchain installed)
set -euo pipefail

PROJECT_ID="${PROJECT_ID:-sedona-dev-deployment}"
ZONE="${ZONE:-us-central1-a}"
INSTANCE="${INSTANCE:-cc-h100-tdx-1}"
IDENTITY="${IDENTITY:-tee://$INSTANCE@$ZONE}"
SECRET="${SECRET:-SAFE-TEE: This secret was delivered via vetKeys IBE to a GCP Confidential VM with H100 CC-On.}"
NODES="${NODES:-10}"
THRESHOLD="${THRESHOLD:-7}"

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LOCAL_ARTIFACTS="/tmp/safetee-demo-$$"
REMOTE_ARTIFACTS="\$HOME/safetee-artifacts"
SAFETEE_BIN="$SCRIPT_DIR/../../target/release/safetee-demo"

mkdir -p "$LOCAL_ARTIFACTS"

echo "================================================================"
echo "  SAFE-TEE End-to-End Demo"
echo "  GCP Confidential VM + NVIDIA H100 CC + vetKeys IBE"
echo "================================================================"
echo ""
echo "  Instance:  $INSTANCE"
echo "  Zone:      $ZONE"
echo "  Identity:  $IDENTITY"
echo "  Nodes:     $NODES (threshold: $THRESHOLD)"
echo ""

# Check local binary exists
if [ ! -f "$SAFETEE_BIN" ]; then
  echo "Building safetee-demo locally..."
  cd "$SCRIPT_DIR/../.."
  cargo build --release --bin safetee-demo
fi

# ── Step 1: Generate transport key on TEE ──
echo "━━━ Step 1: Generate transport key on TEE ━━━"
echo ""

# Copy binary to VM if needed, then run keygen
gcloud compute ssh "$INSTANCE" --zone="$ZONE" --project="$PROJECT_ID" -- \
  "mkdir -p ~/safetee-artifacts"

gcloud compute scp "$SAFETEE_BIN" "$INSTANCE":~/safetee-demo \
  --zone="$ZONE" --project="$PROJECT_ID"

gcloud compute ssh "$INSTANCE" --zone="$ZONE" --project="$PROJECT_ID" -- \
  "chmod +x ~/safetee-demo && ~/safetee-demo keygen --output ~/safetee-artifacts"

# SCP tpk back
gcloud compute scp "$INSTANCE":~/safetee-artifacts/tpk.json "$LOCAL_ARTIFACTS/tpk.json" \
  --zone="$ZONE" --project="$PROJECT_ID"

echo ""
echo "  tpk.json retrieved from TEE."
echo ""

# ── Step 2: Run SAFE-TEE network locally ──
echo "━━━ Step 2: Run SAFE-TEE network (DKG + vetKey derivation) ━━━"
echo ""

"$SAFETEE_BIN" network \
  --tpk-file "$LOCAL_ARTIFACTS/tpk.json" \
  --identity "$IDENTITY" \
  --secret "$SECRET" \
  --nodes "$NODES" \
  --threshold "$THRESHOLD" \
  --output "$LOCAL_ARTIFACTS"

echo ""

# ── Step 3: Transfer artifacts to TEE ──
echo "━━━ Step 3: Transfer encrypted artifacts to TEE ━━━"
echo ""

gcloud compute scp "$LOCAL_ARTIFACTS/network_artifacts.json" \
  "$INSTANCE":~/safetee-artifacts/network_artifacts.json \
  --zone="$ZONE" --project="$PROJECT_ID"

echo "  network_artifacts.json sent to TEE."
echo ""

# ── Step 4: Decrypt on TEE ──
echo "━━━ Step 4: Decrypt on TEE ━━━"
echo ""

gcloud compute ssh "$INSTANCE" --zone="$ZONE" --project="$PROJECT_ID" -- \
  "~/safetee-demo decrypt --artifacts ~/safetee-artifacts"

# Retrieve result
gcloud compute scp "$INSTANCE":~/safetee-artifacts/decryption_result.json \
  "$LOCAL_ARTIFACTS/decryption_result.json" \
  --zone="$ZONE" --project="$PROJECT_ID" 2>/dev/null || true

echo ""
echo "================================================================"
echo "  SAFE-TEE Demo Complete"
echo "  Local artifacts: $LOCAL_ARTIFACTS"
echo "================================================================"
