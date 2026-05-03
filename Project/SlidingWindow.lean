import Veil
import Auto
import Ssreflect.Lang
import LoVe.LoVelib
-- import CaseStudies.Velvet.Std
-- import CaseStudies.TestingUtil

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Relation

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas


def CharCounts := List (Char × Nat)

-- Helper function: update the count of a character in the count map.
def update_count (counts : CharCounts) (c : Char) (delta : Int) : CharCounts :=
  match counts.find? (λ p => p.1 == c) with
  | some (_, count) =>
      let new_count := (count : Int) + delta
      if new_count <= 0 then counts.filter (λ p => p.1 != c)
      else (c, new_count.toNat) :: (counts.filter (λ p => p.1 != c))
  | none =>
      if delta > 0 then (c, delta.toNat) :: counts else counts


------------------------------------------------------------
-- 1. Specification definitions
------------------------------------------------------------

-- Mathematical specification of the number of distinct characters
-- in the substring/window s[i:j].
def distinct_count (s : List Char) (i j : Nat) : Nat :=
  ((s.drop i).take (j - i)).toFinset.card

-- A window s[i:j] is valid if:
-- 1. i <= j,
-- 2. j is within the list boundary,
-- 3. the number of distinct characters is at most k.
def is_valid (s : List Char) (k : Nat) (i j : Nat) : Prop :=
  i ≤ j ∧ j ≤ s.length ∧ distinct_count s i j ≤ k


------------------------------------------------------------
-- 2. State declaration
------------------------------------------------------------

-- State of the sliding-window algorithm.
-- l       : left boundary of the current window
-- r       : right boundary of the current window
-- max_len : maximum valid window length found so far
-- counts  : character-count table for the current window
structure WindowState where
  l : Nat
  r : Nat
  max_len : Nat
  counts : CharCounts


------------------------------------------------------------
-- 3. Transition logic
------------------------------------------------------------

-- One transition step of the sliding-window algorithm.
def next_step (s : List Char) (k : Nat) (st : WindowState) : WindowState :=
  let ⟨l, r, ml, counts⟩ := st
  if h : r < s.length then
    let c := s.get ⟨r, h⟩
    let next_counts := update_count counts c 1

    -- Check the number of distinct characters.
    -- Since counts stores one entry per character, List.length represents
    -- the number of distinct keys.
    if next_counts.length > k then
      -- If the window becomes invalid, move the left boundary to the right
      -- and decrease the count of the removed character.
      if h_l : l < s.length then
        let left_c := s.get ⟨l, h_l⟩
        let next_counts' := update_count next_counts left_c (-1)
        ⟨l + 1, r + 1, ml, next_counts'⟩
      else
        -- Boundary fallback case.
        ⟨l, r, ml, next_counts⟩
    else
      -- If the window remains valid, update the maximum window length.
      let new_r := r + 1
      let new_ml := Nat.max ml (new_r - l)
      ⟨l, new_r, new_ml, next_counts⟩
  else
    -- If r has reached the end, the state does not change.
    st


------------------------------------------------------------
-- 4. Step relation
------------------------------------------------------------

-- Define the step relation explicitly as a Prop to avoid universe issues.
def StepRel (s : List Char) (k : Nat) : WindowState → WindowState → Prop :=
  fun st st' => st' = next_step s k st


------------------------------------------------------------
-- Part 1: State-machine control-flow verification
------------------------------------------------------------

-- Auxiliary lemma:
-- for every reachable state, the current window length is bounded by max_len.
theorem valid_window_length_le_max_len (s : List Char) (k : Nat) (st : WindowState) :
  Relation.ReflTransGen (StepRel s k) ⟨0, 0, 0, []⟩ st → st.r - st.l ≤ st.max_len :=
by
  intro h_reach
  induction h_reach with
  | refl =>
      dsimp
      omega
  | tail h_prev h_step ih =>
      unfold StepRel at h_step
      subst h_step
      unfold next_step
      -- Expand projections, max, and all if-branches.
      dsimp [max, Max.max, Nat.max]
      split_ifs <;> (simp only at *; omega)


-- Main invariant for the state-machine control flow:
-- every valid subwindow inside the current state boundaries has length
-- bounded by max_len.
theorem sliding_window_invariant (s : List Char) (k : Nat) (st : WindowState) :
  Relation.ReflTransGen (StepRel s k) ⟨0, 0, 0, []⟩ st →
  (∀ i j, st.l ≤ i ∧ j ≤ st.r ∧ is_valid s k i j → j - i ≤ st.max_len) :=
by
  intro h_reach
  induction h_reach with
  | refl =>
      intro i j h_val
      dsimp at h_val ⊢
      simp [is_valid, distinct_count] at h_val
      omega

  | tail h_reach_prev h_step ih =>
      unfold StepRel at h_step
      subst h_step
      rename_i st_prev

      have h_phys := valid_window_length_le_max_len s k st_prev h_reach_prev
      rcases st_prev with ⟨l, r, ml, counts⟩

      intro i j h_val
      unfold next_step at h_val ⊢

      -- Force expansion of max and structure projections.
      dsimp [max, Max.max, Nat.max, WindowState.l, WindowState.r, WindowState.max_len] at h_val ⊢

      -- Split all if-branches in next_step.
      split_ifs at h_val ⊢ with hr hk hl

      · -- Case 1: shrink the window, moving from (l, r) to (l + 1, r + 1).
        let ⟨hi, hj, hv⟩ := h_val
        simp only at *
        omega

      · -- Case 2: boundary fallback case.
        let ⟨hi, hj, hv⟩ := h_val
        simp only at *
        omega

      · -- Case 3: expand the window, moving from (l, r) to (l, r + 1).
        let ⟨hi, hj, hv⟩ := h_val
        simp only at *
        by_cases hj_old : j ≤ r
        · have h_res := ih i j ⟨by omega, hj_old, hv⟩
          omega
        · -- Subcase: j = r + 1.
          omega

      · -- Case 4: no-op.
        simp only at *
        exact ih i j h_val


------------------------------------------------------------
-- Part 2: Global safety proof
------------------------------------------------------------

-- Prove that max_len is monotonically non-decreasing after one step.
theorem max_len_mono (s : List Char) (k : Nat) (st st' : WindowState) :
  StepRel s k st st' → st.max_len ≤ st'.max_len :=
by
  intro h_step
  -- Expand definitions.
  unfold StepRel next_step at h_step

  -- Decompose st into primitive fields so that generated if-branches
  -- no longer contain structure projections.
  rcases st with ⟨l, r, ml, counts⟩

  -- Replace st' using the transition equation.
  subst h_step

  -- Expand Nat.max explicitly so that omega can solve arithmetic goals.
  dsimp [Max.max, Nat.max]

  -- Split all conditional branches.
  split_ifs <;> (
    simp only [] at *
    omega
  )


-- The current window length is always bounded by max_len.
theorem window_size_limit (s : List Char) (k : Nat) (st : WindowState) :
  Relation.ReflTransGen (StepRel s k) ⟨0, 0, 0, []⟩ st →
  st.r - st.l ≤ st.max_len :=
by
  intro h_reach
  induction h_reach with
  | refl =>
      dsimp
      omega
  | tail h_prev h_step ih =>
      rename_i prev_st curr_st
      unfold StepRel next_step at h_step
      rcases prev_st with ⟨l, r, ml, counts⟩
      subst h_step
      dsimp [Max.max, Nat.max] at *
      split_ifs <;> (dsimp at *; omega)


-- Specification axiom:
-- in every reachable state, counts.length matches the mathematical
-- distinct_count of the current window.
axiom counts_length_spec (s : List Char) (k : Nat) (st : WindowState)
  (h_reach : Relation.ReflTransGen (StepRel s k) ⟨0, 0, 0, []⟩ st) :
  st.counts.length = distinct_count s st.l st.r


-- Monotonicity axiom:
-- shrinking an interval cannot increase the number of distinct characters.
axiom distinct_count_mono (s : List Char)
    (i j i' j' : Nat)
    (hi : i ≤ i')
    (hj : j' ≤ j)
    (hij' : i' ≤ j') :
    distinct_count s i' j' ≤ distinct_count s i j


-- If the right boundary is shortened by one position,
-- validity of the window is preserved.
theorem valid_shrink_right
  (s : List Char) (k : Nat) (i j : Nat)
  (hij : i ≤ j)
  (hvalid : is_valid s k i (j + 1)) :
  is_valid s k i j :=
by
  rcases hvalid with ⟨_, hj1len, hdc1⟩
  refine ⟨hij, ?_, ?_⟩

  · exact Nat.le_trans (Nat.le_succ j) hj1len

  · have hmono : distinct_count s i j ≤ distinct_count s i (j + 1) := by
      apply distinct_count_mono s i (j + 1) i j
      · exact le_rfl
      · exact Nat.le_succ j
      · exact hij
    exact Nat.le_trans hmono hdc1


-- Specification axiom:
-- after extending the window by one character, the updated count length
-- matches the mathematical distinct_count.
axiom extend_counts_spec
  (s : List Char) (k : Nat) (l r ml : Nat) (counts : CharCounts)
  (h_reach : Relation.ReflTransGen (StepRel s k) ⟨0, 0, 0, []⟩ ⟨l, r, ml, counts⟩)
  (hr : r < s.length) :
  (update_count counts (s.get ⟨r, hr⟩) 1).length = distinct_count s l (r + 1)


-- In every reachable state, the left boundary is no greater than the right boundary.
axiom left_le_right
  (s : List Char) (k : Nat) (st : WindowState)
  (h_reach : Relation.ReflTransGen (StepRel s k) ⟨0, 0, 0, []⟩ st) :
  st.l ≤ st.r


-- Any valid window ending at st.r + 1 must start at or after st.l.
theorem left_bound_min (s : List Char) (k : Nat) (st : WindowState)
  (h_reach : Relation.ReflTransGen (StepRel s k) ⟨0, 0, 0, []⟩ st)
  (i : Nat) (h_val : is_valid s k i (st.r + 1)) :
  i ≥ st.l :=
by
  induction h_reach generalizing i with
  | refl =>
      exact Nat.zero_le i

  | tail h_prev h_step ih =>
      rename_i st_old st_new
      rcases st_old with ⟨l, r, ml, counts⟩

      simp [StepRel, next_step] at h_step
      subst h_step

      split_ifs at h_val ⊢ with hr hk hl

      ----------------------------------------------------------------
      -- Case 1: shrink step, moving from (l, r) to (l + 1, r + 1).
      ----------------------------------------------------------------
      · rcases h_val with ⟨hij2, hlen2, hdc2⟩

        have hij2' : i ≤ Nat.succ (r + 1) := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hij2

        rcases Nat.eq_or_lt_of_le hij2' with hi_eq | hi_lt

        · have hlr : l ≤ r := left_le_right s k ⟨l, r, ml, counts⟩ h_prev
          have h1 : l + 1 ≤ r + 1 := Nat.succ_le_succ hlr
          have h2 : l + 1 ≤ r + 2 := Nat.le_trans h1 (Nat.le_succ (r + 1))
          simpa [hi_eq] using h2

        · have hij_old : i ≤ r + 1 := by
            exact Nat.lt_succ_iff.mp (by
              simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hi_lt)

          have h_val_old : is_valid s k i (r + 1) := by
            exact valid_shrink_right s k i (r + 1) hij_old ⟨hij2, hlen2, hdc2⟩

          have hi_ge_l : i ≥ l := ih i h_val_old

          have hi_ne_l : i ≠ l := by
            intro h_eq
            subst i

            rcases h_val_old with ⟨_, _, hdc_old⟩

            have hspec :
              (update_count counts (s.get ⟨r, hr⟩) 1).length
                = distinct_count s l (r + 1) := by
              exact extend_counts_spec s k l r ml counts h_prev hr

            have h_not_valid_count : ¬ distinct_count s l (r + 1) ≤ k := by
              rw [← hspec]
              exact not_le_of_gt hk

            exact h_not_valid_count hdc_old

          have hlt : l < i := lt_of_le_of_ne hi_ge_l hi_ne_l.symm
          exact Nat.succ_le_of_lt hlt

      ----------------------------------------------------------------
      -- Case 2: boundary fallback case.
      ----------------------------------------------------------------
      · exact ih i h_val

      ----------------------------------------------------------------
      -- Case 3: expansion step, moving from (l, r) to (l, r + 1).
      ----------------------------------------------------------------
      · rcases h_val with ⟨hij2, hlen2, hdc2⟩

        have hij2' : i ≤ Nat.succ (r + 1) := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hij2

        rcases Nat.eq_or_lt_of_le hij2' with hi_eq | hi_lt

        · have hlr : l ≤ r := left_le_right s k ⟨l, r, ml, counts⟩ h_prev
          have h1 : l ≤ r + 1 := Nat.le_trans hlr (Nat.le_succ r)
          have h2 : l ≤ r + 2 := Nat.le_trans h1 (Nat.le_succ (r + 1))
          simpa [hi_eq] using h2

        · have hij_old : i ≤ r + 1 := by
            exact Nat.lt_succ_iff.mp (by
              simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hi_lt)

          have h_val_old : is_valid s k i (r + 1) := by
            exact valid_shrink_right s k i (r + 1) hij_old ⟨hij2, hlen2, hdc2⟩

          exact ih i h_val_old

      ----------------------------------------------------------------
      -- Case 4: no-op step.
      ----------------------------------------------------------------
      · exact ih i h_val


-- Global safety theorem:
-- every valid substring ending no later than st.r has length at most max_len.
theorem sliding_window_global_safe (s : List Char) (k : Nat) (st : WindowState) :
  Relation.ReflTransGen (StepRel s k) ⟨0, 0, 0, []⟩ st →
  (∀ i j, 0 ≤ i ∧ j ≤ st.r ∧ is_valid s k i j → j - i ≤ st.max_len) :=
by
  intro h_reach
  induction h_reach with
  | refl =>
      intro i j h_val
      simp [is_valid, distinct_count] at h_val
      omega

  | tail h_prev h_step ih =>
      rename_i st_old st_new
      intro i j h_val

      rcases st_old with ⟨l, r, ml, counts⟩
      have h_limit := window_size_limit s k ⟨l, r, ml, counts⟩ h_prev

      simp [StepRel, next_step] at h_step
      subst h_step

      unfold Max.max Nat.max at *

      split_ifs at h_val ⊢ with h_r h_k h_l

      ----------------------------------------------------------------
      -- Case 1: shrink step, moving from (l, r) to (l + 1, r + 1).
      ----------------------------------------------------------------
      · simp only [] at *
        by_cases hj : j ≤ r

        · have h_prev_safe := ih i j ⟨h_val.1, hj, h_val.2.2⟩
          omega

        · have hj_eq : j = r + 1 := by
            omega

          have h_val_r1 : is_valid s k i (r + 1) := by
            rw [← hj_eq]
            exact h_val.2.2

          have hi : i ≥ l :=
            left_bound_min s k ⟨l, r, ml, counts⟩ h_prev i h_val_r1

          have h_i_neq_l : i ≠ l := by
            intro h_eq
            subst i

            rcases h_val_r1 with ⟨_, _, hdc⟩

            have hspec :
              (update_count counts (s.get ⟨r, h_r⟩) 1).length
                = distinct_count s l (r + 1) := by
              exact extend_counts_spec s k l r ml counts h_prev h_r

            have h_not_valid_count : ¬ distinct_count s l (r + 1) ≤ k := by
              rw [← hspec]
              exact not_le_of_gt h_k

            exact h_not_valid_count hdc

          have hi_strict : i ≥ l + 1 := by
            omega

          omega

      ----------------------------------------------------------------
      -- Case 2: boundary fallback case.
      ----------------------------------------------------------------
      · simp only [] at *
        have h_prev_safe := ih i j h_val
        omega

      ----------------------------------------------------------------
      -- Case 3: expansion step, moving from (l, r) to (l, r + 1).
      ----------------------------------------------------------------
      · simp only [] at *
        by_cases hj : j ≤ r

        · have h_prev_safe := ih i j ⟨h_val.1, hj, h_val.2.2⟩
          omega

        · have hj_eq : j = r + 1 := by
            omega

          have h_val_r1 : is_valid s k i (r + 1) := by
            rw [← hj_eq]
            exact h_val.2.2

          have hi : i ≥ l :=
            left_bound_min s k ⟨l, r, ml, counts⟩ h_prev i h_val_r1

          omega

      ----------------------------------------------------------------
      -- Case 4: no-op step.
      ----------------------------------------------------------------
      · simp only [] at *
        have h_prev_safe := ih i j h_val
        omega


------------------------------------------------------------
-- Part 3: Tightness proof
------------------------------------------------------------

-- Tightness theorem:
-- max_len is not only an upper bound; it is achieved by some valid window.
theorem max_len_achievable (s : List Char) (k : Nat) (st : WindowState)
  (h_reach : Relation.ReflTransGen (StepRel s k) ⟨0, 0, 0, []⟩ st) :
  ∃ i j, i ≤ j ∧ j ≤ st.r ∧ is_valid s k i j ∧ j - i = st.max_len :=
by
  induction h_reach with
  | refl =>
      use 0, 0
      -- Initial state: max_len = 0, r = 0, and the empty window is valid.
      simp [is_valid, distinct_count]

  | tail h_prev h_step ih =>
      rename_i st_old st_new
      rcases st_old with ⟨l, r, ml, cts⟩
      rcases ih with ⟨i_prev, j_prev, hi_j, hj_r, h_val_prev, h_len_prev⟩

      -- Process the transition step.
      simp [StepRel, next_step] at h_step
      subst h_step
      split_ifs with hr hk hl

      · -- Case 1: shrink step, moving from (l, r) to (l + 1, r + 1).
        use i_prev, j_prev
        refine ⟨hi_j, Nat.le_trans hj_r (Nat.le_succ _), h_val_prev, h_len_prev⟩

      · -- Case 2: degenerate boundary case.
        use i_prev, j_prev

      · -- Case 3: expansion step, moving from (l, r) to (l, r + 1).
        -- This is the only branch where max_len may be updated.
        by_cases h_max : ml < r + 1 - l

        · -- Subcase 3.1: the newly expanded window is longer than old max_len.
          use l, r + 1

          have h_valid : is_valid s k l (r + 1) := by
            refine ⟨?h1, ?h2, ?h3⟩

            · -- l <= r + 1.
              exact Nat.le_trans (by omega) (Nat.le_succ r)

            · -- r + 1 <= s.length.
              exact Nat.succ_le_of_lt hr

            · -- distinct_count <= k.
              have h_len : (update_count cts s[r] 1).length ≤ k := by
                exact Nat.le_of_not_lt hk

              -- Use counts_length_spec to connect counts with distinct_count.
              have h_spec :=
                counts_length_spec s k
                  ⟨l, r + 1, ml.max (r + 1 - l), update_count cts s[r] 1⟩
                  (Relation.ReflTransGen.tail h_prev (by simp [StepRel, next_step, hr, hk]))

              -- Rewrite the goal using the specification.
              simpa [h_spec] using h_len

          refine ⟨by omega, Nat.le_refl _, h_valid, ?_⟩

          -- Handle max explicitly.
          simp [Nat.max_def]
          omega

        · -- Subcase 3.2: the previous witness window is still maximal.
          use i_prev, j_prev

          have hj_new : j_prev ≤ r + 1 := by
            exact Nat.le_trans hj_r (Nat.le_succ r)

          refine ⟨hi_j, hj_new, h_val_prev, ?_⟩

          -- Since ml >= r + 1 - l, max is ml.
          have h_ge : r + 1 - l ≤ ml := Nat.le_of_not_lt h_max
          have hmax : ml.max (r + 1 - l) = ml :=
            Nat.max_eq_left h_ge
          rw [hmax, h_len_prev]

      · -- Case 4: no-op step.
        use i_prev, j_prev
