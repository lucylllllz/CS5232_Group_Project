# Verified Sliding Window for k-Distinct Substring

This project investigates the classical problem of finding the longest substring
with at most k distinct characters, and focuses on formally verifying a sliding
window solution using Lean.

---

## Overview

Given a string `s` and an integer `k`, the goal is to compute the maximum length
of a substring such that the number of distinct characters in the substring
does not exceed `k`.

Instead of relying solely on testing, we provide a formal specification and
prove correctness properties of the optimized algorithm.

---

## Formal Specification

We model substrings using index intervals `s[i:j]`. A substring is valid if:

- `i ≤ j ≤ s.length`
- the number of distinct characters in `s[i:j]` is at most `k`

The desired result is the maximum length among all valid substrings.

---

## Reference Implementation

We include a simple brute-force algorithm that:

- enumerates all substrings
- checks the validity condition directly
- returns the maximum length

Although inefficient, this implementation closely follows the mathematical
definition and serves as a reliable reference for validation.

---

## Sliding Window Algorithm

The optimized solution maintains a dynamic window over the string. The state
consists of:

- `l`: left boundary of the window
- `r`: right boundary
- `max_len`: best length found so far
- `counts`: character frequency information

At each step:

- the window expands by moving `r`
- if the validity condition is violated, the window shrinks by moving `l`
- `max_len` is updated whenever a valid window is observed

---

## Proof Strategy

We verify correctness by reasoning about the evolution of the algorithm state.

The proof relies on maintaining invariants that guarantee:

- **Safety**: the recorded `max_len` is always an upper bound for all valid substrings
- **Tightness**: there exists a valid substring whose length equals `max_len`

Together, these properties ensure that the algorithm computes the optimal result.

---

## Demo and Validation

We provide an executable implementation (`solve`) that simulates the algorithm.

To validate correctness:

- we run the sliding window algorithm on multiple test cases
- we compare the outputs with the brute-force reference implementation

The results match across all tested inputs, demonstrating consistency between
the optimized algorithm and the specification.

---

## Limitations

Some low-level properties connecting the concrete data structure (`counts`)
and the abstract definition of distinct elements are assumed as axioms.

For example:

- the correspondence between the size of `counts` and the distinct character count
- monotonicity properties of substring distinctness

A fully constructive proof of these properties is left for future work.

---

## Project Structure

| File | Description |
| --- | --- |
| `lean/SlidingWindow.lean` | Core definitions, state transitions, and proofs |
| `lean/Baseline.lean` | Brute-force reference implementation |
| `Demo/Demo.lean` | Executable tests and cross-checks |

---

## How to Run Examples

```bash
lake build Project
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
