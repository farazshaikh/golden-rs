# SAFE-TEE Private AI Demo
#
# make install  -- build + deploy to VMs + install vLLM
# make start    -- start all services
# make stop     -- stop all services
# make status   -- check what's running

.PHONY: all install start stop status clean
.ONESHELL:
SHELL := /bin/bash

include .env
-include .env.local
export

WORKSPACE := $(shell cd .. && pwd)
BIN_DIR   := $(WORKSPACE)/target/release
SSH       := ssh -o StrictHostKeyChecking=no -o ConnectTimeout=10 -o LogLevel=ERROR -T
SCP       := scp -o StrictHostKeyChecking=no -o ConnectTimeout=10 -o LogLevel=ERROR
SERVER    := $(SAFETEE_SERVER_USER)@$(SAFETEE_SERVER_HOST)
INFER     := $(INFERENCE_USER)@$(INFERENCE_HOST)
SCHEME    := $(if $(TLS_CERT),https,http)
TLS_FLAGS := $(if $(TLS_CERT),--tls-cert $(TLS_CERT) --tls-key $(TLS_KEY))

all: start

install:
	set -e
	echo "=== Stopping running services ==="
	-$(SSH) $(INFER) "pkill -f vllm; pkill -f safetee-sidecar" 2>/dev/null || true
	-$(SSH) $(SERVER) "pkill -f safetee-server" 2>/dev/null || true
	sleep 1
	echo "=== Building ==="
	cd $(WORKSPACE) && cargo build --release --bin safetee-server --bin safetee-sidecar --bin safetee-demo
	echo ""
	echo "=== Deploying server ==="
	$(SCP) $(BIN_DIR)/safetee-server $(SERVER):~/safetee-server
	$(SSH) $(SERVER) "mkdir -p ~/static && chmod +x ~/safetee-server"
	$(SCP) $(WORKSPACE)/safetee-demo/static/index.html $(WORKSPACE)/safetee-demo/static/setup.html $(SERVER):~/static/
	echo ""
	echo "=== Deploying sidecar ==="
	$(SCP) $(BIN_DIR)/safetee-sidecar $(INFER):~/safetee-sidecar
	$(SSH) $(INFER) "chmod +x ~/safetee-sidecar"
	echo ""
	echo "=== Installing vLLM ==="
	$(SSH) $(INFER) 'test -d ~/vllm-env && echo "already installed" || (sudo apt-get update -qq && sudo apt-get install -y -qq python3 python3-pip python3-venv && python3 -m venv ~/vllm-env && . ~/vllm-env/bin/activate && pip install -q --upgrade pip && pip install -q vllm)'
	echo ""
	echo "=== Done ==="

start:
	@# Generate start scripts locally, SCP them, run via SSH
	@cat > /tmp/_safetee_start_server.sh << 'SCRIPT'
	#!/bin/bash
	pkill -f "safetee-server --listen" 2>/dev/null || true
	sleep 1
	nohup ~/safetee-server --listen 0.0.0.0:$(SAFETEE_SERVER_PORT) --nodes $(SAFETEE_NODES) --threshold $(SAFETEE_THRESHOLD) $(TLS_FLAGS) </dev/null >~/safetee-server.log 2>&1 &
	sleep 5
	curl -sfk $(SCHEME)://localhost:$(SAFETEE_SERVER_PORT)/health >/dev/null && echo "  Server: OK" || echo "  Server: FAILED"
	SCRIPT
	@cat > /tmp/_safetee_start_sidecar.sh << 'SCRIPT'
	#!/bin/bash
	pkill -f "safetee-sidecar --vllm" 2>/dev/null || true
	sleep 1
	nohup ~/safetee-sidecar --vllm-url http://localhost:$(VLLM_PORT) --model "$(VLLM_MODEL)" --listen 0.0.0.0:$(INFERENCE_SIDECAR_PORT) $(TLS_FLAGS) </dev/null >~/sidecar.log 2>&1 &
	sleep 2
	curl -sfk $(SCHEME)://localhost:$(INFERENCE_SIDECAR_PORT)/health >/dev/null && echo "  Sidecar: OK" || echo "  Sidecar: FAILED"
	SCRIPT
	@cat > /tmp/_safetee_start_vllm.sh << 'SCRIPT'
	#!/bin/bash
	if curl -sf http://localhost:$(VLLM_PORT)/health >/dev/null 2>&1; then
	  echo "  vLLM: already running"
	else
	  pkill -f "vllm serve" 2>/dev/null || true; sleep 1
	  . ~/vllm-env/bin/activate 2>/dev/null
	  nohup vllm serve "$(VLLM_MODEL)" --dtype auto --max-model-len $(VLLM_MAX_MODEL_LEN) --port $(VLLM_PORT) --trust-remote-code </dev/null >~/vllm-serve.log 2>&1 &
	  echo "  vLLM: starting (~3 min)"
	fi
	SCRIPT
	@echo "=== Starting server ==="
	@$(SCP) /tmp/_safetee_start_server.sh $(SERVER):~/_st.sh
	@$(SSH) $(SERVER) "bash ~/_st.sh"
	@echo "=== Starting sidecar ==="
	@$(SCP) /tmp/_safetee_start_sidecar.sh $(INFER):~/_st.sh
	@$(SSH) $(INFER) "bash ~/_st.sh"
	@echo "=== Starting vLLM ==="
	@$(SCP) /tmp/_safetee_start_vllm.sh $(INFER):~/_st.sh
	@$(SSH) $(INFER) "bash ~/_st.sh"
	@echo ""
	@echo "  $(SCHEME)://$(SAFETEE_SERVER_HOST):$(SAFETEE_SERVER_PORT)"

stop:
	-$(SSH) $(INFER) "pkill -f vllm; pkill -f safetee-sidecar; echo '  Inference: stopped'" 2>/dev/null || true
	-$(SSH) $(SERVER) "pkill -f safetee-server; echo '  Server: stopped'" 2>/dev/null || true

status:
	@echo ""
	@echo "  SAFE-TEE Private AI"
	@echo ""
	@curl -sfk --connect-timeout 3 $(SCHEME)://$(SAFETEE_SERVER_HOST):$(SAFETEE_SERVER_PORT)/health >/dev/null 2>&1 \
		&& echo "  Server:   UP   $(SCHEME)://$(SAFETEE_SERVER_HOST):$(SAFETEE_SERVER_PORT)" \
		|| echo "  Server:   DOWN $(SCHEME)://$(SAFETEE_SERVER_HOST):$(SAFETEE_SERVER_PORT)"
	@curl -sfk --connect-timeout 3 $(SCHEME)://$(INFERENCE_HOST):$(INFERENCE_SIDECAR_PORT)/health >/dev/null 2>&1 \
		&& echo "  Sidecar:  UP   $(SCHEME)://$(INFERENCE_HOST):$(INFERENCE_SIDECAR_PORT)" \
		|| echo "  Sidecar:  DOWN $(SCHEME)://$(INFERENCE_HOST):$(INFERENCE_SIDECAR_PORT)"
	@curl -sf --connect-timeout 3 http://$(INFERENCE_HOST):$(VLLM_PORT)/health >/dev/null 2>&1 \
		&& echo "  vLLM:     UP   http://$(INFERENCE_HOST):$(VLLM_PORT)" \
		|| echo "  vLLM:     DOWN http://$(INFERENCE_HOST):$(VLLM_PORT)"
	@echo ""

clean:
	cd $(WORKSPACE) && cargo clean
