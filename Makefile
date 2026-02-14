# Golden DKG top-level Makefile
#
# Usage:
#   make verify        -- full formal verification (tests + Lean + hax + F*)
#   make verify-quick  -- quick check (tests + Lean only)
#   make test          -- cargo test only
#   make build         -- cargo build
#   make clean         -- clean all artifacts

.PHONY: verify verify-quick test build clean

verify:
	$(MAKE) -C formal_verification verify

verify-quick:
	$(MAKE) -C formal_verification verify-quick

test:
	cargo test --workspace

build:
	cargo build --workspace

clean:
	cargo clean
	$(MAKE) -C formal_verification clean
