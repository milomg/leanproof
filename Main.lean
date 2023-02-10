import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Free

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
      . match (And.left a) with
        | Exists.intro y hy =>
          intro x hx
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
      . match (And.left a) with
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


variable {α : Type u}
theorem a4 : (∀ x y: FreeMagma α, (x*(x*y)=y)∧ ((y*x)*x=y)) -> (∀ x y: FreeMagma α, x*y=y*x) := by
  intro h1 x y
  rw [← (And.left (h1 y (x * y)))]
  conv in (y * (x * y)) =>
    arg 1
    rw [← And.left (h1 x y)]
  rw [And.right (h1 (x * y) x)]


theorem q5 (F : Nat → Nat → Nat) : (∀ n : ℕ, (F 0 n) = n + 1) -> (∀m : ℕ, F (m + 1) 0 = F m 1) -> (∀ m : ℕ , ∀ n : ℕ , F (m + 1) (n + 1) = F m (F (m + 1) n)) -> (∀ m : ℕ, ∀ n : ℕ, F m n > n) := by
  intros C1 C2 C3 m
  induction m with
  | zero =>
    intro n
    rw [C1 n]
    apply Nat.lt_succ_self
  | succ m ha =>
    intro n
    induction n with
    | zero =>
      rw [C2 m]
      have hb := ha 1
      apply Nat.lt_trans Nat.zero_lt_one hb
    | succ n hb =>
      rw [C3 m n]
      have hc := ha (F (m + 1) n)
      have hd := Nat.succ_le_of_lt hb
      apply Nat.lt_of_le_of_lt hd hc


def main : IO Unit :=
  IO.println s!"Hello, world!"
