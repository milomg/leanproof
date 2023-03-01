import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Free

lemma l1 (x : Nat) : Xor' (Even x) (Odd x) := by simp

lemma l5 (q : Nat) : (Odd (q * q)) -> (Odd q) := by
  rw [← not_imp_not]
  simp
  intro hnp
  match (l1 (q * q)) with
  | Or.inl xi =>
    rw [Nat.even_iff_not_odd]
    apply And.right xi
  | Or.inr h1 =>
    rw [Nat.even_mul]
    tauto

theorem q3 (n : Nat) : (∃ q: Nat, q * q = 2 * n + 1) -> (∃ y: Nat, n + 1 = y * y + (y + 1) * (y + 1)) := by
  intro hq
  match hq with
  | ⟨q, y⟩ =>
    match (l5 q (Exists.intro n y)) with
    | ⟨r, hr⟩ =>
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
