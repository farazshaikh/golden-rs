#!/usr/bin/env bash
# 01-create-vm.sh -- Create GCP Confidential VM with TDX + H100 (a3-highgpu-1g)
#
# Prerequisites:
#   - gcloud CLI installed and authenticated
#   - Quota: regional preemptible H100 GPU + global GPUs all regions
#   - Project must have Compute Engine API enabled
#
# Reference: GCP Confidential VM + NVIDIA H100 CC documentation
set -euo pipefail

PROJECT_ID="${PROJECT_ID:-sedona-dev-deployment}"
ZONE="${ZONE:-us-central1-a}"
INSTANCE="${INSTANCE:-cc-h100-tdx-1}"

echo "=== SAFE-TEE: Creating Confidential VM ==="
echo "  Project:  $PROJECT_ID"
echo "  Zone:     $ZONE"
echo "  Instance: $INSTANCE"
echo "  Machine:  a3-highgpu-1g (8x H100 80GB)"
echo "  TEE:      Intel TDX"
echo "  Spot:     yes"
echo ""

gcloud config set project "$PROJECT_ID"

gcloud compute instances create "$INSTANCE" \
  --provisioning-model=SPOT \
  --confidential-compute-type=TDX \
  --machine-type=a3-highgpu-1g \
  --maintenance-policy=TERMINATE \
  --zone="$ZONE" \
  --image-project=ubuntu-os-cloud \
  --image-family=ubuntu-2404-lts-amd64 \
  --boot-disk-size=200G \
  --shielded-secure-boot

echo ""
echo "=== VM created. SSH in with: ==="
echo "  gcloud compute ssh $INSTANCE --zone=$ZONE"
echo ""
echo "Then run 02-setup-gpu-cc.sh on the VM."
