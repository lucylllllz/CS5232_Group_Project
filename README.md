# Sliding Window Verification (Veil + Dafny)

This project provides a formal verification of the sliding window algorithm for computing the longest substring with at most `k` distinct characters.

The verification is carried out primarily using **Veil (Lean-based)**, with an additional implementation in **Dafny** for comparison.

---

## 📂 Project Structure

### `veil/`
Contains the Veil model and proofs:
- State definition  
- Transition relation (`StepRel`)  
- Invariants and correctness theorems  

### `dafny/`
Contains the Dafny implementation:
- Sliding window algorithm  
- Loop invariants  
- Postconditions (safety and optimality)  

---

## ⚙️ Requirements

### For Veil / Lean
- Lean 4  
- Veil framework (installed or included)  

### For Dafny
- Dafny (version ≥ 3.0 recommended)  
- Z3 SMT solver (usually bundled with Dafny)  

---

## ▶️ How to Run

### 1. Veil Verification

Navigate to the Veil directory:

```bash
cd veil

Build and verify:

lake build

Expected behavior:

The proof compiles successfully
All theorems (invariants, safety, optimality) are verified

Typical runtime:

A few seconds on a standard machine
2. Dafny Verification

Navigate to the Dafny directory:

cd dafny

Run the verifier:

dafny /compile:0 sliding_window.dfy

