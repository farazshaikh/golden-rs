#!/usr/bin/env bash
# 03-verify-cc.sh -- Verify NVIDIA Confidential Computing is ON
#
# Run this INSIDE the Confidential VM after reboot (post 02-setup-gpu-cc.sh).
#
# Checks:
#   A. nvidia-persistenced is running with --uvm-persistence-mode
#   B. CC status is ON (nvidia-smi conf-compute -f)
#   C. Set GPU ready state and confirm ready
#
# WARNING: Do NOT restart nvidia-persistenced after enabling uvm-persistence-mode.
# GCP warns this can break the secure SPDM connection and require a full reboot.
set -euo pipefail

echo "=== SAFE-TEE: Verifying Confidential Computing Status ==="
echo ""

# ── A. Check nvidia-persistenced ──
echo "[A] Checking nvidia-persistenced..."
if ps aux | grep nvidia-persistenced | grep -q uvm-persistence-mode; then
  echo "  PASS: nvidia-persistenced running with --uvm-persistence-mode"
else
  echo "  FAIL: nvidia-persistenced not running with --uvm-persistence-mode"
  echo "  Running processes:"
  ps aux | grep nvidia-persistenced | grep -v grep || true
  echo ""
  echo "  You may need to reboot or re-run 02-setup-gpu-cc.sh"
fi

# ── B. Check CC status ──
echo ""
echo "[B] Checking Confidential Compute status..."
CC_STATUS=$(sudo nvidia-smi conf-compute -f 2>&1) || true
echo "  $CC_STATUS"

if echo "$CC_STATUS" | grep -qi "ON"; then
  echo "  PASS: CC status is ON"
else
  echo "  FAIL: CC status is not ON"
fi

# ── C. Set GPU ready state ──
echo ""
echo "[C] Setting GPU ready state..."
sudo nvidia-smi conf-compute -srs 1
READY_STATUS=$(sudo nvidia-smi conf-compute -grs 2>&1) || true
echo "  $READY_STATUS"

if echo "$READY_STATUS" | grep -qi "ready"; then
  echo "  PASS: GPUs are in ready state"
else
  echo "  FAIL: GPUs not in ready state"
fi

# ── Summary ──
echo ""
echo "=== Verification Complete ==="
echo ""
echo "Proof artifacts for your records:"
echo "  sudo nvidia-smi conf-compute -f"
echo "  sudo nvidia-smi conf-compute -grs"
echo ""
echo "Next: run 04-install-vllm.sh to install vLLM."
