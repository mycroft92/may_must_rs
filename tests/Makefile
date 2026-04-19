.PHONY: ir smoke clean

TEST_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
REPO_ROOT := $(abspath $(TEST_DIR)/..)
OUT_DIR ?= $(TEST_DIR)/out

ir:
	cd $(REPO_ROOT) && ./tests/build_ir.sh --out-dir $(OUT_DIR)

smoke:
	cd $(REPO_ROOT) && ./tests/smash_smoke.sh

clean:
	rm -rf $(OUT_DIR)
