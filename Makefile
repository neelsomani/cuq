PYTHON ?= python3
RUSTC ?= rustc

MIR_DUMP_DIR ?= mir_dump
SAXPY_SRC := examples/saxpy.rs
ATOMIC_SRC := examples/atomic_flag.rs

COQ_DIR := coq

.PHONY: demo translate mir-saxpy mir-atomic coq

demo: mir-saxpy mir-atomic translate coq

translate: coq/examples/saxpy_gen.v coq/examples/atomic_flag_gen.v

mir-saxpy:
	@mkdir -p $(MIR_DUMP_DIR)
	RUSTFLAGS="-Zunstable-options" $(RUSTC) --crate-type=lib -Z dump-mir=all $(SAXPY_SRC)

mir-atomic:
	@mkdir -p $(MIR_DUMP_DIR)
	RUSTFLAGS="-Zunstable-options" $(RUSTC) --crate-type=lib -Z dump-mir=all $(ATOMIC_SRC)

coq:
	$(MAKE) -C $(COQ_DIR) all

coq/examples/saxpy_gen.v: tools/mir2coq.py $(wildcard $(MIR_DUMP_DIR)/saxpy.saxpy.*.PreCodegen.after.mir)
	@SAXPY_MIR=`ls -t $(MIR_DUMP_DIR)/saxpy.saxpy.*.PreCodegen.after.mir 2>/dev/null | head -n 1`; \
	if [ -z "$$SAXPY_MIR" ]; then \
	  echo "error: no saxpy PreCodegen MIR dump found" >&2; \
	  exit 1; \
	fi; \
	$(PYTHON) tools/mir2coq.py $$SAXPY_MIR $@

coq/examples/atomic_flag_gen.v: tools/mir2coq.py $(wildcard $(MIR_DUMP_DIR)/atomic_flag.acquire_release.*.PreCodegen.after.mir)
	@ATOMIC_MIR=`ls -t $(MIR_DUMP_DIR)/atomic_flag.acquire_release.*.PreCodegen.after.mir 2>/dev/null | head -n 1`; \
	if [ -z "$$ATOMIC_MIR" ]; then \
	  echo "error: no atomic_flag PreCodegen MIR dump found" >&2; \
	  exit 1; \
	fi; \
	$(PYTHON) tools/mir2coq.py $$ATOMIC_MIR $@

