#!/usr/bin/env bash
# 02-setup-gpu-cc.sh -- Enable NVIDIA Confidential Computing on the VM
#
# Run this INSIDE the Confidential VM after SSH-ing in.
# This script:
#   A. Installs build deps + kernel headers
#   B. Installs NVIDIA driver (575-open, Secure Boot compatible)
#   C. Enables Linux Kernel Crypto API for secure GPU<->driver comms
#   D. Enables nvidia-persistenced with --uvm-persistence-mode (SPDM)
#   E. Reboots the VM
#
# After reboot, run 03-verify-cc.sh to confirm CC status: ON.
#
# Reference: GCP GPU CC enablement workflow
set -euo pipefail

echo "=== SAFE-TEE: Setting up NVIDIA Confidential Computing ==="
echo ""

# ── A. Install build deps + kernel headers ──
echo "[A] Installing build dependencies and kernel headers..."
sudo apt-get update --yes
sudo apt-get install -y \
  linux-headers-"$(uname -r)" \
  build-essential \
  libxml2 \
  libncurses5-dev \
  pkg-config \
  libvulkan1 \
  gcc-12

# ── B. Install NVIDIA driver ──
echo ""
echo "[B] Installing NVIDIA driver 575-open..."

# Add NVIDIA package repository
if ! dpkg -l cuda-keyring 2>/dev/null | grep -q '^ii'; then
  wget -q https://developer.download.nvidia.com/compute/cuda/repos/ubuntu2404/x86_64/cuda-keyring_1.1-1_all.deb
  sudo dpkg -i cuda-keyring_1.1-1_all.deb
  rm -f cuda-keyring_1.1-1_all.deb
  sudo apt-get update --yes
fi

sudo apt-get install -y nvidia-driver-575-open

# ── C. Enable Linux Kernel Crypto API for secure GPU<->driver comms ──
echo ""
echo "[C] Enabling Linux Kernel Crypto API (ECDSA/ECDH for SPDM)..."

echo "install nvidia /sbin/modprobe ecdsa_generic; /sbin/modprobe ecdh; /sbin/modprobe --ignore-install nvidia" \
  | sudo tee /etc/modprobe.d/nvidia-lkca.conf

sudo update-initramfs -u

# ── D. Enable persistence mode (SPDM secure channel setup) ──
echo ""
echo "[D] Enabling nvidia-persistenced with --uvm-persistence-mode..."

if sudo test -f /usr/lib/systemd/system/nvidia-persistenced.service; then
  sudo sed -i "s/no-persistence-mode/uvm-persistence-mode/g" \
    /usr/lib/systemd/system/nvidia-persistenced.service
  sudo systemctl daemon-reload
  echo "  nvidia-persistenced.service updated."
else
  echo "  WARNING: nvidia-persistenced.service not found. Driver may not be installed yet."
fi

# ── E. Reboot ──
echo ""
echo "=== Setup complete. Rebooting in 5 seconds... ==="
echo "After reboot, SSH back in and run 03-verify-cc.sh"
echo ""
sleep 5
sudo reboot
