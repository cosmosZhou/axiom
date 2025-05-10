import Lemma.Algebra.LeSubS.of.Le
open Algebra


@[main]
private lemma nat
  {a b c : ℕ}
-- given
  (h : c ≤ a + b) :
-- imply
  c - b ≤ a :=
-- proof
  Nat.sub_le_iff_le_add.mpr h


@[main]
private lemma nat.left
  {a b c : ℕ}
-- given
  (h : c ≤ a + b) :
-- imply
  c - a ≤ b :=
-- proof
  Nat.sub_le_iff_le_add'.mpr h


@[main]
private lemma left
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : c ≤ a + b) :
-- imply
  c - a ≤ b := by
-- proof
  have h := LeSubS.of.Le h a
  simp at h
  simp
  exact h


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : c ≤ a + b) :
-- imply
  c - b ≤ a := by
-- proof
  have h := LeSubS.of.Le h b
  simp at h
  simp
  exact h


-- created on 2024-11-27
-- updated on 2025-05-09
