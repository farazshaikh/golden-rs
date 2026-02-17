# SAFE-TEE Demo Makefile
#
# Usage:
#   make build    -- build all binaries (server, sidecar, demo CLI)
#   make install  -- deploy binaries + install vLLM on inference VM
#   make          -- start all services (server + sidecar + vLLM)
#   make stop     -- stop all services
#   make status   -- show status of all components
#
# Configuration: edit .env or override on command line:
#   make SAFETEE_SERVER_HOST=1.2.3.4 INFERENCE_HOST=5.6.7.8

.PHONY: all build install start stop status deploy-server deploy-sidecar \
        start-server start-sidecar start-vllm stop-server stop-sidecar stop-vllm \
        logs-server logs-sidecar logs-vllm clean help

# ── Load .env (defaults), then .env.local (real values, gitignored) ──
include .env
-include .env.local
export

WORKSPACE := $(shell cd .. && pwd)
BIN_DIR   := $(WORKSPACE)/target/release

# SSH helpers using gcloud compute ssh (handles key management)
SSH_SERVER = gcloud compute ssh $(SAFETEE_SERVER_INSTANCE) --zone=$(SAFETEE_SERVER_ZONE) --project=$(GCP_PROJECT) --command
SSH_INFER  = gcloud compute ssh $(INFERENCE_INSTANCE) --zone=$(INFERENCE_ZONE) --project=$(GCP_PROJECT) --command
SCP_SERVER = gcloud compute scp --zone=$(SAFETEE_SERVER_ZONE) --project=$(GCP_PROJECT)
SCP_INFER  = gcloud compute scp --zone=$(INFERENCE_ZONE) --project=$(GCP_PROJECT)

# ── Default target: start everything ──
all: start

# ── Help ──
help:
	@echo "SAFE-TEE Demo"
	@echo ""
	@echo "  make build     Build all Rust binaries"
	@echo "  make install   Deploy binaries to VMs + install vLLM"
	@echo "  make           Start all services (server + sidecar + vLLM)"
	@echo "  make stop      Stop all services"
	@echo "  make status    Show status of all components"
	@echo ""
	@echo "  make start-server    Start SAFE-TEE server only"
	@echo "  make start-sidecar   Start inference sidecar only"
	@echo "  make start-vllm      Start vLLM only"
	@echo "  make stop-server     Stop SAFE-TEE server only"
	@echo "  make stop-sidecar    Stop inference sidecar only"
	@echo "  make stop-vllm       Stop vLLM only"
	@echo ""
	@echo "  make logs-server     Tail SAFE-TEE server logs"
	@echo "  make logs-sidecar    Tail sidecar logs"
	@echo "  make logs-vllm       Tail vLLM logs"
	@echo ""
	@echo "Configuration: .env"
	@echo "  SAFETEE_SERVER_HOST = $(SAFETEE_SERVER_HOST)"
	@echo "  INFERENCE_HOST      = $(INFERENCE_HOST)"
	@echo "  VLLM_MODEL          = $(VLLM_MODEL)"

# ============================================================================
# BUILD
# ============================================================================

build:
	@echo "=== Building SAFE-TEE binaries ==="
	cd $(WORKSPACE) && cargo build --release --bin safetee-server --bin safetee-sidecar --bin safetee-demo
	@echo ""
	@ls -lh $(BIN_DIR)/safetee-server $(BIN_DIR)/safetee-sidecar $(BIN_DIR)/safetee-demo
	@echo ""
	@echo "Build complete."

# ============================================================================
# INSTALL (deploy binaries + vLLM)
# ============================================================================

install: build deploy-server deploy-sidecar install-vllm
	@echo ""
	@echo "=== Install complete ==="
	@echo "  Server:  $(SAFETEE_SERVER_HOST) ($(SAFETEE_SERVER_INSTANCE))"
	@echo "  Sidecar: $(INFERENCE_HOST) ($(INFERENCE_INSTANCE))"
	@echo ""
	@echo "Run 'make' to start all services."

deploy-server:
	@echo "=== Deploying SAFE-TEE server to $(SAFETEE_SERVER_HOST) ==="
	$(SCP_SERVER) $(BIN_DIR)/safetee-server $(SAFETEE_SERVER_INSTANCE):~/safetee-server
	$(SSH_SERVER) "mkdir -p ~/static"
	$(SCP_SERVER) static/index.html $(SAFETEE_SERVER_INSTANCE):~/static/index.html
	$(SSH_SERVER) "chmod +x ~/safetee-server"
	@echo "  Done."

deploy-sidecar:
	@echo "=== Deploying sidecar to $(INFERENCE_HOST) ==="
	$(SCP_INFER) $(BIN_DIR)/safetee-sidecar $(INFERENCE_INSTANCE):~/safetee-sidecar
	$(SSH_INFER) "chmod +x ~/safetee-sidecar"
	@echo "  Done."

install-vllm:
	@echo "=== Installing vLLM on $(INFERENCE_HOST) ==="
	$(SSH_INFER) 'if [ ! -d ~/vllm-env ]; then sudo apt-get update -qq && sudo apt-get install -y -qq python3 python3-pip python3-venv && python3 -m venv ~/vllm-env && source ~/vllm-env/bin/activate && pip install --upgrade pip && pip install vllm; else echo "vLLM already installed"; fi'
	@echo "  Done."

# ============================================================================
# START
# ============================================================================

start: start-server start-sidecar start-vllm
	@echo ""
	@echo "============================================"
	@echo "  SAFE-TEE Encrypted Inference Demo"
	@echo "============================================"
	@echo ""
	@echo "  Browser UI:  http://$(SAFETEE_SERVER_HOST):$(SAFETEE_SERVER_PORT)/index.html"
	@echo "  Server API:  http://$(SAFETEE_SERVER_HOST):$(SAFETEE_SERVER_PORT)"
	@echo "  Sidecar:     http://$(INFERENCE_HOST):$(INFERENCE_SIDECAR_PORT)"
	@echo "  vLLM:        http://$(INFERENCE_HOST):$(VLLM_PORT)"
	@echo ""

start-server:
	@echo "=== Starting SAFE-TEE server on $(SAFETEE_SERVER_HOST):$(SAFETEE_SERVER_PORT) ==="
	@TLS_ARGS=""; CURL_SCHEME="http"; \
	if [ -n "$(TLS_CERT)" ] && [ -n "$(TLS_KEY)" ]; then \
		TLS_ARGS="--tls-cert $(TLS_CERT) --tls-key $(TLS_KEY)"; \
		CURL_SCHEME="https"; \
	fi; \
	printf '#!/bin/bash\npkill -f "safetee-server --listen" 2>/dev/null || true\nsleep 1\ncd ~ && nohup ~/safetee-server --listen 0.0.0.0:%s --nodes %s --threshold %s %s </dev/null > ~/safetee-server.log 2>&1 &\nsleep 5\ncurl -sfk %s://localhost:%s/health > /dev/null && echo "  Server: OK" || echo "  Server: FAILED"\n' \
		"$(SAFETEE_SERVER_PORT)" "$(SAFETEE_NODES)" "$(SAFETEE_THRESHOLD)" "$$TLS_ARGS" "$$CURL_SCHEME" "$(SAFETEE_SERVER_PORT)" > /tmp/_safetee_start_server.sh
	@$(SCP_SERVER) /tmp/_safetee_start_server.sh $(SAFETEE_SERVER_INSTANCE):~/_start_server.sh
	@$(SSH_SERVER) "bash ~/_start_server.sh"

start-sidecar:
	@echo "=== Starting sidecar on $(INFERENCE_HOST):$(INFERENCE_SIDECAR_PORT) ==="
	@TLS_ARGS=""; CURL_K=""; CURL_SCHEME="http"; \
	if [ -n "$(TLS_CERT)" ] && [ -n "$(TLS_KEY)" ]; then \
		TLS_ARGS="--tls-cert $(TLS_CERT) --tls-key $(TLS_KEY)"; \
		CURL_K="-k"; CURL_SCHEME="https"; \
	fi; \
	printf '#!/bin/bash\npkill -f "safetee-sidecar --vllm" 2>/dev/null || true\nsleep 1\nnohup ~/safetee-sidecar --vllm-url http://localhost:%s --model "%s" --listen 0.0.0.0:%s %s </dev/null > ~/sidecar.log 2>&1 &\nsleep 2\ncurl -sf %s %s://localhost:%s/health > /dev/null && echo "  Sidecar: OK" || echo "  Sidecar: FAILED"\n' \
		"$(VLLM_PORT)" "$(VLLM_MODEL)" "$(INFERENCE_SIDECAR_PORT)" "$$TLS_ARGS" "$$CURL_K" "$$CURL_SCHEME" "$(INFERENCE_SIDECAR_PORT)" > /tmp/_safetee_start_sidecar.sh
	@$(SCP_INFER) /tmp/_safetee_start_sidecar.sh $(INFERENCE_INSTANCE):~/_start_sidecar.sh
	@$(SSH_INFER) "bash ~/_start_sidecar.sh"

start-vllm:
	@echo "=== Starting vLLM on $(INFERENCE_HOST):$(VLLM_PORT) ==="
	@printf '#!/bin/bash\nif curl -sf http://localhost:%s/health > /dev/null 2>&1; then\n  echo "  vLLM: already running"\nelse\n  pkill -f "vllm serve" 2>/dev/null || true\n  sleep 1\n  source ~/vllm-env/bin/activate 2>/dev/null\n  nohup vllm serve "%s" --dtype auto --max-model-len %s --port %s --trust-remote-code </dev/null > ~/vllm-serve.log 2>&1 &\n  echo "  vLLM: starting (model loading takes ~3 min)"\nfi\n' \
		$(VLLM_PORT) "$(VLLM_MODEL)" $(VLLM_MAX_MODEL_LEN) $(VLLM_PORT) > /tmp/_safetee_start_vllm.sh
	@$(SCP_INFER) /tmp/_safetee_start_vllm.sh $(INFERENCE_INSTANCE):~/_start_vllm.sh
	@$(SSH_INFER) "bash ~/_start_vllm.sh"

# ============================================================================
# STOP
# ============================================================================

stop: stop-vllm stop-sidecar stop-server
	@echo "All services stopped."

stop-server:
	@echo "=== Stopping SAFE-TEE server ==="
	-@$(SSH_SERVER) "pkill -f safetee-server 2>/dev/null && echo Stopped || echo Not_running"

stop-sidecar:
	@echo "=== Stopping sidecar ==="
	-@$(SSH_INFER) "pkill -f safetee-sidecar 2>/dev/null && echo Stopped || echo Not_running"

stop-vllm:
	@echo "=== Stopping vLLM ==="
	-@$(SSH_INFER) "pkill -f vllm 2>/dev/null && echo Stopped || echo Not_running"

# ============================================================================
# STATUS
# ============================================================================

status:
	@echo "============================================"
	@echo "  SAFE-TEE Demo Status"
	@echo "============================================"
	@echo ""
	@SCHEME="http"; [ -n "$(TLS_CERT)" ] && SCHEME="https"; \
	echo "--- SAFE-TEE Server ($(SAFETEE_SERVER_INSTANCE) @ $$SCHEME://$(SAFETEE_SERVER_HOST):$(SAFETEE_SERVER_PORT)) ---"; \
	curl -sfk --connect-timeout 3 $$SCHEME://$(SAFETEE_SERVER_HOST):$(SAFETEE_SERVER_PORT)/health > /dev/null 2>&1 \
		&& echo "  API:     UP" || echo "  API:     DOWN"; \
	curl -sfk --connect-timeout 3 $$SCHEME://$(SAFETEE_SERVER_HOST):$(SAFETEE_SERVER_PORT)/index.html > /dev/null 2>&1 \
		&& echo "  Web UI:  UP" || echo "  Web UI:  DOWN"; \
	MPK=$$(curl -sfk --connect-timeout 3 $$SCHEME://$(SAFETEE_SERVER_HOST):$(SAFETEE_SERVER_PORT)/mpk 2>/dev/null) && \
		echo "  MPK:     $$(echo $$MPK | python3 -c 'import sys,json; d=json.load(sys.stdin); print(d["group_pk_hex"][:32]+"... (n="+str(d["num_nodes"])+", t="+str(d["threshold"])+")")' 2>/dev/null)" \
		|| echo "  MPK:     unavailable"
	@echo ""
	@SSCHEME="http"; [ -n "$(TLS_CERT)" ] && SSCHEME="https"; \
	echo "--- Inference Sidecar ($(INFERENCE_INSTANCE) @ $$SSCHEME://$(INFERENCE_HOST):$(INFERENCE_SIDECAR_PORT)) ---"; \
	curl -sfk --connect-timeout 3 $$SSCHEME://$(INFERENCE_HOST):$(INFERENCE_SIDECAR_PORT)/health > /dev/null 2>&1 \
		&& echo "  Sidecar: UP" || echo "  Sidecar: DOWN"
	@echo ""
	@echo "--- vLLM ($(INFERENCE_INSTANCE) @ $(INFERENCE_HOST):$(VLLM_PORT)) ---"
	@curl -sf --connect-timeout 3 http://$(INFERENCE_HOST):$(VLLM_PORT)/health > /dev/null 2>&1 \
		&& echo "  vLLM:    UP ($(VLLM_MODEL))" || echo "  vLLM:    DOWN or loading"
	@echo ""
	@echo "--- GCP VM Status ---"
	@gcloud compute instances describe $(SAFETEE_SERVER_INSTANCE) --zone=$(SAFETEE_SERVER_ZONE) --project=$(GCP_PROJECT) --format="value(status)" 2>/dev/null | \
		xargs -I{} echo "  $(SAFETEE_SERVER_INSTANCE): {}" || echo "  $(SAFETEE_SERVER_INSTANCE): unknown"
	@gcloud compute instances describe $(INFERENCE_INSTANCE) --zone=$(INFERENCE_ZONE) --project=$(GCP_PROJECT) --format="value(status)" 2>/dev/null | \
		xargs -I{} echo "  $(INFERENCE_INSTANCE): {}" || echo "  $(INFERENCE_INSTANCE): unknown"
	@echo ""
	@echo "--- CC Status ($(INFERENCE_INSTANCE)) ---"
	-@$(SSH_INFER) 'sudo nvidia-smi conf-compute -f 2>/dev/null || echo "  CC: unavailable"'
	@echo ""
	@SCHEME="http"; [ -n "$(TLS_CERT)" ] && SCHEME="https"; \
	echo "Browser UI: $$SCHEME://$(SAFETEE_SERVER_HOST):$(SAFETEE_SERVER_PORT)/index.html"

# ============================================================================
# LOGS
# ============================================================================

logs-server:
	$(SSH_SERVER) "tail -50 ~/safetee-server.log"

logs-sidecar:
	$(SSH_INFER) "tail -50 ~/sidecar.log"

logs-vllm:
	$(SSH_INFER) "tail -50 ~/vllm-serve.log"

# ============================================================================
# CLEAN
# ============================================================================

clean:
	cd $(WORKSPACE) && cargo clean
	@echo "Build artifacts cleaned."
