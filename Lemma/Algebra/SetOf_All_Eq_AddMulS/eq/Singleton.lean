import Lemma.Algebra.Mul_Sub.eq.SubMulS
import Lemma.Algebra.GeSubSMul.of.Ge
import Lemma.Algebra.SubSub.eq.Sub_Add
import Lemma.Algebra.AddAdd.comm
import Lemma.Algebra.Add.eq.Mul2
import Lemma.Algebra.EqAdd.of.Eq_Sub
import Lemma.Algebra.EqAdd.of.Eq_Sub.Le
import Lemma.Algebra.SubAdd.eq.AddSub
import Lemma.Algebra.SubAdd.eq.AddSub.of.Le
import Lemma.Algebra.SubMul.eq.MulSub_1
import Lemma.Algebra.Mul_Add.eq.AddMulS
import Lemma.Algebra.SubMulS.eq.MulSub
import Lemma.Algebra.AddAdd.eq.Add_Add
import Lemma.Algebra.Eq_Add.of.EqSub.Le
open Algebra


def fib (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n


def G (n : ℕ) := fib (3 * n)


private lemma fib_recurrence
  {n : ℕ}
-- given
  (h : n ≥ 2) :
-- imply
  fib n = fib (n - 1) + fib (n - 2) := by
-- proof
  match n with
  | 0 =>
    contradiction
  | 1 =>
    contradiction
  | n + 2 =>
    rfl


-- Modus Ponens
private lemma mp
  {a b : ℤ}
-- given
  (h : ∀ n ≥ 2, G n = a * G (n - 1) + b * G (n - 2)) :
-- imply
  a = 4 ∧ b = 1 := by
-- proof
  have h₀ := h 2 (by rfl)
  have h₁ := h 3 (by decide)
  simp [G, fib] at h₀ h₁
  constructor <;> omega


-- Modus Ponens Reverse
private lemma mpr
  {a b : ℤ}
-- given
  (h : a = 4 ∧ b = 1) :
-- imply
  ∀ n ≥ 2, G n = a * G (n - 1) + b * G (n - 2) := by
-- proof
  let ⟨h₀, h₁⟩ := h
  rw [h₀, h₁]
  intro n hn
  simp [G, fib]
  norm_cast
  rw [Mul_Sub.eq.SubMulS.nat, Mul_Sub.eq.SubMulS.nat]
  norm_num
  norm_num
  rw [fib_recurrence (n := 3 * n)]
  ·
    rw [fib_recurrence (n := 3 * n - 1)]
    ·
      rw [SubSub.eq.Sub_Add.nat, SubSub.eq.Sub_Add.nat]
      norm_num
      rw [AddAdd.comm]
      rw [Add.eq.Mul2]
      rw [EqAdd.of.Eq_Sub.Le]
      ·
        rw [SubAdd.eq.AddSub.of.Le]
        ·
          rw [SubMul.eq.MulSub_1.nat]
          norm_num
          have := GeSubSMul.of.Ge hn 3 2
          rw [fib_recurrence (n := 3 * n - 2)]
          ·
            rw [SubSub.eq.Sub_Add.nat, SubSub.eq.Sub_Add.nat]
            norm_num
            rw [Mul_Add.eq.AddMulS]
            rw [EqAdd.of.Eq_Sub.Le.left]
            ·
              rw [SubAdd.eq.AddSub.of.Le]
              ·
                rw [SubMulS.eq.MulSub.nat]
                norm_num
                rw [fib_recurrence (n := 3 * n - 3)]
                ·
                  rw [SubSub.eq.Sub_Add.nat, SubSub.eq.Sub_Add.nat]
                  norm_num
                  rw [AddAdd.eq.Add_Add]
                  apply Eq_Add.of.EqSub.Le.left
                  ·
                    rw [SubMul.eq.MulSub_1.nat]
                    norm_num
                    rw [fib_recurrence (n := 3 * n - 4)]
                    ·
                      rw [SubSub.eq.Sub_Add.nat, SubSub.eq.Sub_Add.nat]
                    ·
                      have := GeSubSMul.of.Ge hn 3 4
                      linarith
                  ·
                    linarith
                ·
                  have := GeSubSMul.of.Ge hn 3 3
                  linarith
              ·
                linarith
            linarith
          ·
            linarith
        ·
          linarith
      ·
        linarith
    ·
      have := GeSubSMul.of.Ge hn 3 1
      linarith
  ·
    linarith


@[main]
private lemma main:
-- imply
  {((a : ℤ), (b : ℤ)) | ∀ n ≥ 2, G n = a * G (n - 1) + b * G (n - 2)} = {(4, 1)} := by
-- proof
  ext ⟨a, b⟩
  constructor <;>
    rintro h
  -- Forward direction: If (a, b) satisfies the recurrence, then (a, b) = (4, 1)
  ·
    have := mp h
    simp_all
  -- Reverse direction: If (a, b) = (4, 1), then the recurrence holds
  ·
    apply mpr
    -- simp at h
    simp_all


-- created on 2025-03-31
