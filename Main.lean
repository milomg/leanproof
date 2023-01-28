import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Basic

theorem one_not_even : ¬(∃ y : Nat, 1 = 2 * y) := by
  simp
  intro y
  cases y with
  | zero => simp
  | succ y =>
    rw [Nat.succ_eq_add_one, left_distrib]
    simp
    intro
    contradiction
  
theorem l1 (x : Nat) : Xor' (∃ y: Nat, x = 2 * y) (∃ y : Nat, x = 2 * y + 1) := by
  induction x with
  | zero =>
    simp
    intro _ _
    contradiction
  | succ _ hx =>
    rw [Nat.succ_eq_add_one]
    cases hx with
    | inl a =>
      apply Or.inr
      simp
      constructor
      . apply (And.left a)
      . intro x
        intro hx
        match (And.left a) with
        | Exists.intro y hy =>
          have one_is_even : ∃ z : Nat, 1 = 2 * z := by
            apply Exists.intro (x - y)
            rw [Nat.mul_sub_left_distrib, ← hx, hy]
            simp
          have one_not_even := one_not_even
          contradiction
    | inr a =>
      apply Or.inl
      simp
      constructor
      . have c := (And.left a)
        match c with
        | Exists.intro y hy =>
          apply Exists.intro (y + 1)
          rw [hy, left_distrib]
      . have b := (And.right a)
        simp at b
        apply b

theorem l5 (q : Nat) : (∃ y: Nat, q * q = 2 * y + 1) -> (∃ y: Nat, q = 2 * y + 1) := by
  rw [← not_imp_not]
  intro hnp
  match (l1 (q * q)) with
  | Or.inl xi =>
    have _ := And.right xi
    intro _
    contradiction
  | Or.inr h1 =>
    simp
    intro x
    match (l1 q) with
    | Or.inr h3 =>
      have _ := (And.left h3)
      contradiction
    | Or.inl x1 =>
      have q_squared_not_even := And.right h1
      match (And.left x1) with
      | Exists.intro x q_even => 
        have q_squared_even : ∃ z : Nat, q * q = 2 * z := by
          apply Exists.intro (2 * x * x)
          rw [q_even]
          ring
        contradiction

theorem q3 (n : Nat) : (∃ q: Nat, q * q = 2 * n + 1) -> (∃ y: Nat, n + 1 = y * y + (y + 1) * (y + 1)) := by
  intro q
  match q with
  | Exists.intro q y =>
    match (l5 q (Exists.intro n y)) with
    | Exists.intro r hr =>
      conv at y =>
        simp
        rw [hr, right_distrib, one_mul, ← add_assoc, 
            add_right_cancel_iff, mul_assoc, ← left_distrib]
        simp
      apply Exists.intro r
      rw [← y]
      ring

def main : IO Unit :=
  IO.println s!"Hello, world!"
