PYTHON ?= python3
RUSTC ?= rustc

MIR_DUMP_DIR ?= mir_dump
SAXPY_SRC := examples/saxpy.rs
ATOMIC_SRC := examples/atomic_flag.rs

COQ_DIR := coq

.PHONY: demo translate mir-saxpy mir-atomic coq bad-demo

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

bad-demo: examples/atomic_bad.rs tools/mir2coq.py
	@mkdir -p $(MIR_DUMP_DIR)
	RUSTFLAGS="-Zunstable-options" $(RUSTC) --crate-type=lib -Z dump-mir=all examples/atomic_bad.rs
	@BAD_MIR=`ls -t $(MIR_DUMP_DIR)/atomic_bad.*.PreCodegen.after.mir 2>/dev/null | head -n 1`; \
	if [ -z "$$BAD_MIR" ]; then \
	  echo "error: no atomic_bad PreCodegen MIR dump found" >&2; exit 1; \
	fi; \
	if $(PYTHON) tools/mir2coq.py $$BAD_MIR coq/examples/atomic_bad_gen.v; then \
	  echo "ERROR: translator accepted atomic_bad ordering (expected failure)"; \
	  rm -f coq/examples/atomic_bad_gen.v; \
	  exit 1; \
	else \
	  echo "[ok] translator rejected atomic_bad ordering as expected"; \
	fi
	@rm -f coq/examples/atomic_bad_gen.v
