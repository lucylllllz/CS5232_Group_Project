import Project.SlidingWindow
import Project.BruteForce_Base

-- ----------------------------------------
-- Run sliding window
-- ----------------------------------------

def run_steps (s : List Char) (k : Nat) (fuel : Nat) : WindowState :=
  Nat.iterate (next_step s k) fuel ⟨0, 0, 0, []⟩

def solve (s : List Char) (k : Nat) : Nat :=
  let st := run_steps s k (2 * s.length + 5)
  st.max_len


-- ----------------------------------------
-- Examples (LeetCode-style)
-- ----------------------------------------

#eval solve "eceba".data 2      -- expect 3
#eval solve "aa".data 1         -- expect 2
#eval solve "abcabcbb".data 2   -- expect 4

-- edge cases
#eval solve "".data 2
#eval solve "a".data 1
#eval solve "abc".data 0


-- ----------------------------------------
-- Cross-check with baseline
-- ----------------------------------------

#eval brute_force "eceba".data 2
#eval solve       "eceba".data 2

#eval brute_force "aa".data 1
#eval solve       "aa".data 1

#eval brute_force "abcabcbb".data 2
#eval solve       "abcabcbb".data 2

#eval brute_force "".data 2
#eval solve       "".data 2

#eval brute_force "abc".data 0
#eval solve       "abc".data 0


-- ----------------------------------------
-- Batch comparison
-- ----------------------------------------

def examples : List (List Char × Nat) :=
  [
    ("eceba".data, 2),
    ("aa".data, 1),
    ("abcabcbb".data, 2),
    ("".data, 2),
    ("a".data, 1),
    ("abc".data, 0)
  ]

#eval examples.map (fun (s, k) => (brute_force s k, solve s k))
