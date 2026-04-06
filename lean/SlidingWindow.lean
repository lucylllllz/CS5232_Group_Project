import Std

open Std

--------------------------------------------------
-- substring
--------------------------------------------------
def substring (s : List Char) (lo hi : Nat) : List Char :=
(s.drop lo).take (hi - lo)

--------------------------------------------------
-- distinct characters（用 List 表示）
--------------------------------------------------
def distinctChars (s : List Char) (lo hi : Nat) : List Char :=
(substring s lo hi).eraseDups

--------------------------------------------------
-- “集合大小”
--------------------------------------------------
def distinctCount (s : List Char) (lo hi : Nat) : Nat :=
(distinctChars s lo hi).length

--------------------------------------------------
-- valid interval
--------------------------------------------------
def validInterval (s : List Char) (k lo hi : Nat) : Prop :=
lo ≤ hi ∧ hi ≤ s.length ∧ distinctCount s lo hi ≤ k

--------------------------------------------------
-- Lemma 1: extend window（弱版本）
--------------------------------------------------
theorem extend_window_subset
(s : List Char) (lo hi : Nat)
(h : hi < s.length) :
∀ x, x ∈ distinctChars s lo hi →
      x ∈ distinctChars s lo (hi + 1) := by
  intro x hx
  unfold distinctChars substring at *
  simp at *
  -- 核心直觉：旧窗口元素仍在新窗口中
  admit

--------------------------------------------------
-- Lemma 2: shrink window
--------------------------------------------------
theorem shrink_window_subset
(s : List Char) (lo hi : Nat)
(h : lo < hi) :
∀ x, x ∈ distinctChars s (lo + 1) hi →
      x ∈ distinctChars s lo hi := by
  intro x hx
  unfold distinctChars substring at *
  simp at *
  admit

--------------------------------------------------
-- Lemma 3: bound（可证明）
--------------------------------------------------
theorem distinct_bound
(s : List Char) (lo hi : Nat) :
distinctCount s lo hi ≤ hi - lo := by
  unfold distinctCount distinctChars substring

  -- eraseDups 长度 ≤ 原 list
  have h₁ :
    ((s.drop lo).take (hi - lo)).eraseDups.length
    ≤ ((s.drop lo).take (hi - lo)).length := by
    apply List.length_eraseDups_le

  -- take 长度 ≤ hi - lo
  have h₂ :
    ((s.drop lo).take (hi - lo)).length ≤ hi - lo := by
    simp

  exact Nat.le_trans h₁ h₂
