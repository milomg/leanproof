import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Basic

theorem l1 (x : Nat) : (∃ y: Nat, x = 2 * y) ∨ (∃ y : Nat, x = 2 * y + 1) := by
  induction x with
  | zero =>
    apply Or.inl (Exists.intro 0 (by simp))
  | succ z hz =>
    cases hz with
    | inl a =>
      apply Or.inr
      simp
      apply a
    | inr a =>
      apply Or.inl
      simp
      apply Exists.elim a
      intro b
      intro hb
      apply Exists.intro (b + 1)
      rw [hb, Nat.succ_eq_add_one, left_distrib]

theorem one_not_even : ¬(∃ y : Nat, 1 = 2 * y) := by
  simp
  intro x
  cases x with
  | zero => simp
  | succ y =>
    rw [Nat.succ_eq_add_one, left_distrib]
    simp
    intro x
    contradiction

theorem l1' (x : Nat): ¬(∃ y : Nat, x = 2 * y) ∨  ¬(∃ y : Nat, x = 2 * y + 1) := by
  induction x with
  | zero =>
    apply by_contradiction
    simp
    intros
    contradiction
  | succ z hz =>
    rw [Nat.succ_eq_add_one]
    simp
    cases hz with
    | inl a =>
      apply Or.inr
      simp at a
      apply a
    | inr _ =>
      apply Or.inl
      intro m
      intro qy
      cases (l1 z) with
      | inl qa =>
        apply Exists.elim qa
        intro m2
        intro qy2
        rw [qy2] at qy
        have one_is_even : ∃ z : Nat, 1 = 2 * z := by
          apply Exists.intro (m - m2)
          rw [Nat.mul_sub_left_distrib, ← qy]
          simp
        have _ := one_not_even
        contradiction
      | inr b => contradiction

theorem l5 (q : Nat) : (∃ y: Nat, q * q = 2 * y + 1) -> (∃ y: Nat, q = 2 * y + 1) := by
  rw [← not_imp_not]
  intro hnp
  have hp : (∃ y : Nat, q = 2 * y) := by
    apply Or.elim (l1 q)
    intros
    assumption
    intros
    contradiction
  apply Exists.elim hp
  intro x
  intro y
  have _ : (∃ z : Nat, q * q = 2 * z) := by
    apply Exists.intro (2 * x * x)
    rw [y]
    ring
  apply Or.elim (l1' (q * q))
  intros
  contradiction
  simp

theorem q3 (n : Nat) : (∃ q: Nat, q * q = 2 * n + 1) -> (∃ y: Nat, n + 1 = y * y + (y + 1) * (y + 1)) := by
  intro q
  apply Exists.elim q
  intro q
  intro y
  apply Exists.elim (l5 q (Exists.intro n y))
  intro r
  intro hr
  conv at y =>
    rw [hr, right_distrib, one_mul, ← add_assoc]
    simp
    rw [mul_assoc, ← left_distrib]
    simp
  apply Exists.intro r
  rw [← y]
  ring

def main : IO Unit :=
  IO.println s!"Hello, world!"
