import Project.SlidingWindow

-- ----------------------------------------
-- Brute-force baseline implementation
-- ----------------------------------------

def brute_force (s : List Char) (k : Nat) : Nat :=
  let n := s.length
  (List.range (n + 1)).foldl
    (fun acc i =>
      (List.range (n + 1)).foldl
        (fun acc j =>
          if h : i ≤ j ∧ j ≤ n ∧ distinct_count s i j ≤ k then
            Nat.max acc (j - i)
          else acc)
        acc)
    0


-- ----------------------------------------
-- Simple examples for baseline
-- ----------------------------------------

#eval brute_force "eceba".data 2      -- expect 3
#eval brute_force "aa".data 1         -- expect 2
#eval brute_force "abcabcbb".data 2   -- expect 4
#eval brute_force "".data 2           -- expect 0
#eval brute_force "a".data 1          -- expect 1
#eval brute_force "abc".data 0        -- expect 0
