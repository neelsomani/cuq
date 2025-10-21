# Cuq: A MIR-to-Coq Framework Targeting PTX for Formal Semantics and Verified Translation of Rust GPU Kernels

## Abstract

Rust's rise as a systems language has extended into GPU programming through projects like Rust-CUDA and rust-gpu, which compile Rust kernels to NVIDIA's PTX or SPIR-V backends. Yet despite Rust's strong safety guarantees, there is currently no formal semantics for Rust's GPU subset, nor any verified mapping from Rust's compiler IR to PTX's formally defined execution model.

This project introduces the first framework for **formally verifying the semantics of Rust GPU kernels** by translating Rust's Mid-level Intermediate Representation (MIR) into Coq and connecting it to the existing Coq formalization of the PTX memory model (Lustig et al., ASPLOS 2019).
Rather than modeling Rust's ownership and borrowing rules directly, this work focuses on defining a mechanized operational semantics for a realistic subset of MIR and establishing memory-model soundness: proving that MIR atomic and synchronization operations compile soundly to PTX instructions under the PTX memory model.

**Cuq = CUDA + Coq**.

## Motivation

1. **No formal semantics for Rust GPU code:**
   Although Rust compilers can emit GPU code via NVVM or SPIR-V, the semantics of such kernels are defined only informally through the compiler's behavior. There is no mechanized model of MIR execution for GPU targets.

2. **Disconnect between high-level Rust and verified GPU models:**
   NVIDIA's PTX memory model has a complete Coq specification, but that model has never been linked to a high-level language. Existing proofs connect only C++ atomics to PTX atomics.

3. **MIR as a verification sweet spot:**
   MIR is a well-typed SSA IR that preserves Rust's structured control flow and side-effect information while stripping away syntax. It provides a precise, implementation-independent level at which to define semantics and translate to Coq.

## Technical Approach

1. **Define a mechanized semantics for MIR:**
   Implement a Coq formalization of a simplified MIR subset sufficient to express GPU kernels: variable assignment, arithmetic, control flow, memory loads/stores, and synchronization intrinsics.

2. **Translate MIR to Coq:**
   Develop a translation tool that consumes `rustc`'s `-Z dump-mir` output and produces corresponding Gallina definitions. The translation captures MIR basic blocks, terminators, and memory actions as Coq terms.

3. **Connect to PTX semantics:**
   Use the existing Coq formalization of PTX to define a *memory-model correspondence* between MIR and PTX traces. The initial goal is to prove *soundness* in the same sense as Lustig et al. (ASPLOS 2019):

   > If a MIR kernel is data-race-free under the MIR memory model, its compiled PTX program admits only executions consistent with the PTX memory model.

4. **Property verification:**
   Leverage this semantics to verify kernel-level properties such as:

   * Absence of divergent barrier synchronization;
   * Preservation of sequential equivalence (e.g., for reductions or scans);
   * Conformance to the PTX consistency model under shared-memory interactions.

5. **Prototype toolchain:**
   Deliver a prototype that automatically translates Rust-CUDA kernels into Coq terms, evaluates their semantics within Coq, and interfaces with PTX proofs.

## Expected Outcomes

* A **Coq formalization of Rust MIR semantics** for GPU kernels using Rust nightly-2025-03-02.
* A **MIR→PTX memory-model correspondence theorem**, establishing soundness of atomic and synchronization operations for a well-defined kernel subset.
* A **prototype translator** generating Coq verification artifacts from Rust code.
* **Case studies** on standard CUDA benchmarks (e.g., SAXPY, reductions) verifying barrier correctness and dataflow soundness.

## Future Work

While this first phase omits Rust's ownership and lifetime reasoning, the framework is designed to incorporate it later. Future extensions can integrate ownership types or affine resource logics into the MIR semantics, enabling end-to-end proofs of data-race freedom and alias safety.

## Impact

This project establishes the missing formal bridge between Rust's compiler infrastructure and the only existing mechanized model of GPU execution.
By defining verified semantics for MIR and connecting it to PTX, it provides the foundation for future CompCert-style verified compilation of GPU code and opens the door to ownership-aware proofs of safety and correctness for massively parallel Rust programs.
