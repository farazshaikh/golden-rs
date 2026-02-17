#!/usr/bin/env bash
# 04-install-vllm.sh -- Install vLLM and serve Qwen3-VL vision model on the H100
#
# Run this INSIDE the Confidential VM after CC is verified (03-verify-cc.sh).
#
# This proves the H100 GPU is fully usable inside the TDX + CC environment
# by serving a production vision-language model (Qwen3-VL-30B-A3B).
#
# The served model is compatible with the osrs .env VLM configuration:
#   VLM_PROVIDER=vllm
#   VLM_MODEL=Qwen/Qwen3-VL-30B-A3B-Instruct
#   VLM_PROVIDER_URL=http://<VM_IP>:8000/v1
#
# Prerequisites:
#   - NVIDIA driver installed and CC mode ON
#   - Internet access for pip packages and model download
#   - HuggingFace token (for gated models -- set HF_TOKEN env var)
set -euo pipefail

# Qwen3-VL-30B-A3B is the MoE vision model matching the osrs .env SVLM config.
# For the full 235B model, change to Qwen/Qwen3-VL-235B-A22B-Instruct (needs more GPUs).
MODEL="${MODEL:-Qwen/Qwen3-VL-30B-A3B-Instruct}"
PORT="${PORT:-8000}"
MAX_MODEL_LEN="${MAX_MODEL_LEN:-4096}"
TENSOR_PARALLEL="${TENSOR_PARALLEL:-8}"

echo "=== SAFE-TEE: Installing vLLM + Vision Model on Confidential VM ==="
echo "  Model:           $MODEL"
echo "  Port:            $PORT"
echo "  Max model len:   $MAX_MODEL_LEN"
echo "  Tensor parallel: $TENSOR_PARALLEL"
echo ""

# ── Install Python + system deps ──
echo "[1] Installing Python 3 and system dependencies..."
sudo apt-get update --yes
sudo apt-get install -y python3 python3-pip python3-venv

# Create a venv to avoid PEP 668 issues on Ubuntu 24.04
if [ ! -d "$HOME/vllm-env" ]; then
  python3 -m venv "$HOME/vllm-env"
fi
source "$HOME/vllm-env/bin/activate"

# ── Install vLLM ──
echo ""
echo "[2] Installing vLLM..."
pip install --upgrade pip
pip install vllm

# ── Install Rust toolchain (for safetee-demo binary) ──
echo ""
echo "[3] Installing Rust toolchain (for transport key generation)..."
if ! command -v rustup &>/dev/null; then
  curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
  source "$HOME/.cargo/env"
fi

# ── Verify GPU is visible to PyTorch ──
echo ""
echo "[4] Verifying GPU access from Python..."
python3 -c "
import torch
print(f'  CUDA available: {torch.cuda.is_available()}')
print(f'  GPU count: {torch.cuda.device_count()}')
for i in range(torch.cuda.device_count()):
    print(f'  GPU {i}: {torch.cuda.get_device_name(i)}')
"

# ── Serve the vision model ──
echo ""
echo "=== vLLM installed. To serve the vision model: ==="
echo ""
echo "  source ~/vllm-env/bin/activate"
echo "  vllm serve $MODEL \\"
echo "    --dtype auto \\"
echo "    --max-model-len $MAX_MODEL_LEN \\"
echo "    --port $PORT \\"
echo "    --tensor-parallel-size $TENSOR_PARALLEL \\"
echo "    --trust-remote-code"
echo ""
echo "  # Test vision endpoint:"
echo "  curl http://localhost:$PORT/v1/chat/completions \\"
echo "    -H 'Content-Type: application/json' \\"
echo "    -d '{"
echo "      \"model\": \"$MODEL\","
echo "      \"messages\": [{"
echo "        \"role\": \"user\","
echo "        \"content\": [{"
echo "          \"type\": \"text\","
echo "          \"text\": \"Describe this image.\""
echo "        }, {"
echo "          \"type\": \"image_url\","
echo "          \"image_url\": {\"url\": \"https://upload.wikimedia.org/wikipedia/commons/thumb/4/47/PNG_transparency_demonstration_1.png/280px-PNG_transparency_demonstration_1.png\"}"
echo "        }]"
echo "      }]"
echo "    }'"
echo ""
echo "  # osrs .env update (point VLM to this TEE):"
echo "  # VLM_PROVIDER=vllm"
echo "  # VLM_MODEL=$MODEL"
echo "  # VLM_PROVIDER_URL=http://<VM_EXTERNAL_IP>:$PORT/v1"
echo ""
echo "Next: run 05-tee-keygen.sh to generate transport keys."
