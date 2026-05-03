# Verified Sliding Window for k-Distinct Substring

This project investigates the classical problem of finding the longest substring
with at most k distinct characters, and focuses on formally verifying a sliding
window solution using Lean.

---

## Overview 😊

Given a string `s` and an integer `k`, the goal is to compute the maximum length
of a substring such that the number of distinct characters in the substring
does not exceed `k`.

Instead of relying solely on testing, we provide a formal specification and
prove correctness properties of the optimized algorithm.

---

# Build Guide 🌍

Start with:

```bash
lake build Project
```

## If Error 1: ProofWidgets not up-to-date

Run:

```bash
lake exe cache get
lake build Project
```

---

## Run Demo ✨ 👋

```bash
lake env lean Project/Demo.lean
```


## Examples

The following examples illustrate the expected behavior:

| Input String | k | Output | Description |
| --- | --- | --- | --- |
| `"eceba"` | 2 | 3 | Standard case with expansion and shrink |
| `"aa"` | 1 | 2 | Repeated characters, no shrinking needed |
| `"abcabcbb"` | 2 | 4 | Frequent expansion and contraction |
| `""` | 2 | 0 | Empty string edge case |
| `"a"` | 1 | 1 | Minimal non-empty input |
| `"abc"` | 0 | 0 | No valid substring when k = 0 |
| `"abc"` | 10 | 3 | Entire string is valid when k is large |
| `"abcdef"` | 2 | 2 | All distinct characters, frequent shrink |

These test cases cover typical usage patterns as well as edge and corner cases.

## Expected Results

Running the demo file produces the following outputs:

```
3
2
4
0
1
0
3
3
2
2
4
4
0
0
0
0
[(3, 3), (2, 2), (4, 4), (0, 0), (1, 1), (0, 0)]
```

The first group of numbers corresponds to the results of the sliding window algorithm on the test cases.

The second group shows the outputs of both the brute-force baseline and the sliding window algorithm, printed in pairs. Each pair `(x, y)` indicates that both implementations return the same result.

The final list summarizes all comparisons, confirming that the optimized algorithm is consistent with the reference implementation across all tested inputs.

## Summary

This project demonstrates how a widely used algorithmic technique can be formally verified using invariant-based reasoning, and how executable testing can complement formal proofs to increase confidence in correctness.
