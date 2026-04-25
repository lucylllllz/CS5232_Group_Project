# Sliding Window Verification (Veil + Dafny)

This project provides a formal verification of the sliding window algorithm for computing the longest substring with at most `k` distinct characters.

The verification is carried out primarily using **Veil (Lean-based)**, with an additional implementation in **Dafny** for comparison.

---

## 📂 Project Structure

```
.
├── dafny/
│   └── SlidingWindow.dfy
├── lean/
│   └── SlidingWindow.lean
```

- `dafny/SlidingWindow.dfy`  
  Dafny implementation of the sliding window algorithm, including:
  - Loop invariants  
  - Safety and optimality specifications  

- `lean/SlidingWindow.lean`  
  Veil/Lean formalisation, including:
  - State-transition model  
  - Invariants  
  - Proofs of correctness  

---

## ⚙️ Requirements

### For Lean / Veil
- Lean 4  
- Veil framework (installed or included)  

### For Dafny
- Dafny (version ≥ 3.0 recommended)  
- Z3 SMT solver (usually bundled with Dafny)  

---

## ▶️ How to Run

### 1. Lean / Veil Verification

Navigate to the Lean directory:

```bash
cd lean
```

Run verification:

```bash
lake build
```

Expected behavior:
- The file compiles successfully  
- All proofs are verified  

Typical runtime:
- A few seconds  

---

### 2. Dafny Verification

Navigate to the Dafny directory:

```bash
cd dafny
```

Run the verifier:

```bash
dafny /compile:0 SlidingWindow.dfy
```

Expected behavior:
- All verification conditions are discharged  
- No assertion failures  
