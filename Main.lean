import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Basic

theorem contrapositive (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P) := by
  apply Iff.intro 
  . intro h
    intro q
    intro s
    have q2 : Q := h s
    contradiction
  . intro h
    intro p
    apply by_contradiction
    intro s
    have p2 : ¬ P := h s
    contradiction

theorem l1 (x : Nat) : (∃ y: Nat, x = 2 * y) ∨ (∃ y : Nat, x = 2 * y + 1) := by
  induction x with
  | zero => 
    apply Or.inl (Exists.intro 0 (by simp))
  | succ z hz =>
    cases hz with 
    | inl a =>
    apply Or.inr
    . simp
      apply a
    | inr a => 
      apply Or.inl
      . simp
        apply Exists.elim a (fun b => by
          intro hb
          apply Exists.intro (b + 1)
          . rw [hb]
            rw [Nat.succ_eq_add_one]
            rw [left_distrib]
        )

theorem one_not_even : ¬ (∃ y : Nat, 1 = 2 * y) := by
  simp
  intro x
  cases x with 
  | zero => simp
  | succ y => 
  rw [Nat.succ_eq_add_one]
  rw [left_distrib]
  intro x
  have z : 1 < 2 * y + 2 * 1 := by simp
  have a := ne_of_lt z  
  contradiction

theorem l1' (x:Nat): ¬(∃ y:Nat, x=2*y) ∨  ¬(∃ y : Nat, x= 2 * y + 1) := by
  induction x with
  | zero => 
    apply by_contradiction
    simp
    intros
    contradiction
  | succ z hz =>
    cases hz with 
    | inl a =>
    apply Or.inr
    . simp
      simp at a
      apply a
    | inr a => 
    apply Or.inl
    . rw [Nat.succ_eq_add_one]
      have qa: (∃ y : Nat, z = 2 * y) := by 
        cases (l1 z) with
        | inl b => apply b
        | inr b => contradiction
      intro y
      apply Exists.elim y
      intro m
      intro qy
      apply Exists.elim qa
      intro m2
      intro qy2
      rw [qy2] at qy
      have qy3 : 1 = 2 * m - 2 * m2 := by
        rw [← qy]
        rw [add_comm]
        simp
      have qy4 : ∃ z : Nat, 1 = 2 * z := by
        apply Exists.intro (m - m2)
        . rw [qy3]
          rw [eq_comm]
          rw [Nat.mul_sub_left_distrib]
      have o := one_not_even
      contradiction

theorem l5 (q : Nat) : (∃ y: Nat, q * q = 2 * y + 1) -> (∃ y: Nat, q = 2 * y + 1) := by
  apply (Iff.mpr (contrapositive (∃ y: Nat, q * q = 2 * y + 1) (∃ y: Nat, q = 2 * y + 1)))
  intro hnp
  have hp : (∃ y : Nat, q = 2 * y) := by
    apply Or.elim (l1 q) (fun _ => by assumption)
    intro hp
    contradiction
  apply Exists.elim hp (fun x => by
    intro y
    have qb : (∃ z : Nat, q * q = 2 * z) := by
      apply Exists.intro (2 * x * x) 
      . rw [y]
        rw [mul_assoc]
        rw [mul_comm (x) (2 * x)]
    apply Or.elim (l1' (q * q)) (fun _ => by contradiction)
    simp
  )

theorem q3 (n : Nat) : (∃ q: Nat, q*q=2*n+1) -> (∃ y: Nat, n + 1 = y * y + (y + 1) * (y + 1)) := by
  intro q
  apply Exists.elim q (fun q => by
    intro y
    have z : (∃ y: Nat, q * q = 2 * y + 1) := Exists.intro n y
    have r := l5 q z
    apply Exists.elim r (fun r => by
      intro hr
      have t : (2 * r + 1) * (2 * r + 1) - 1 = 2 * n := by
        rw [← hr]
        rw [y]
        simp
      rw [right_distrib] at t
      simp at t
      rw [mul_assoc] at t
      rw [← left_distrib] at t
      simp at t
      apply Exists.intro r
      . rw [← t]
        rw [right_distrib]
        rw [left_distrib]
        simp
        rw [left_distrib]
        simp
        rw [← add_assoc]
        rw [← add_assoc]
        rw [← add_assoc]
        rw [two_mul]
        rw [left_distrib]
    )
  )

def main : IO Unit :=
  IO.println s!"Hello, world!"
