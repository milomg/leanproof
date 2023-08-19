import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Free

lemma l1 (x : Nat) : Xor' (Even x) (Odd x) := by simp

lemma l5 (q : Nat) : (Odd (q * q)) -> (Odd q) := by
  intro h
  exact Nat.Odd.of_mul_left h

theorem q3 (n : Nat) : (∃ q: Nat, q * q = 2 * n + 1) -> (∃ y: Nat, n + 1 = y * y + (y + 1) * (y + 1)) := by
  intro hq
  match hq with
  | ⟨q, y⟩ =>
    match (l5 q (Exists.intro n y)) with
    | ⟨r, hr⟩ =>
      apply Exists.intro r
      conv at y =>
        simp
        rw [hr, right_distrib, one_mul, ← add_assoc,
            add_right_cancel_iff, mul_assoc, ← left_distrib]
        simp
      rw [← y]
      ring

variable {α : Type u}
theorem a4 : (∀ x y : FreeMagma α, (x * (x * y) = y) ∧ ((y * x) * x = y)) -> (∀ x y : FreeMagma α, x * y = y * x) := by
  intro h1 x y
  rw [← (And.left (h1 y (x * y)))]
  conv in (y * (x * y)) =>
    arg 1
    rw [← And.left (h1 x y)]
  rw [And.right (h1 (x * y) x)]

def F (m n : Nat) : Nat := 
  match m, n with
    | 0, n => n + 1
    | m + 1, 0 => F m 1
    | m + 1, n + 1 => F m (F (m + 1) n)
  termination_by F m n => (m, n)

theorem q5 (m n: ℕ) : (F m n > n) := by
  revert n
  induction m with
  | zero =>
    intro n
    rw [F]
    exact Nat.lt.base n
  | succ m ha =>
    intro n
    induction n with
    | zero =>
      apply Nat.lt_trans Nat.zero_lt_one (ha 1)
    | succ n hb =>
      exact Nat.lt_of_le_of_lt hb (ha (F (m + 1) n))

def main : IO Unit :=
  IO.println s!"Hello, world!"
