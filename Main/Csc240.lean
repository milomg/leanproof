import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Free

lemma l1 (x : Nat) : Xor' (Even x) (Odd x) := Nat.even_xor_odd x

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
        rw [hr, right_distrib, one_mul, ← add_assoc,
            add_right_cancel_iff, mul_assoc, ← left_distrib]
        simp only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]
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
  termination_by (m, n)

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
      rw [F]
      apply Nat.lt_trans Nat.zero_lt_one (ha 1)
    | succ n hb =>
      rw [F]
      exact Nat.lt_of_le_of_lt hb (ha (F (m + 1) n))

def f (n : Nat) : Nat :=
  if n = 0 then 0
  else if Odd n then f (n - 1) + 1
  else f (n / 2)
  termination_by n
  decreasing_by
    simp only [tsub_lt_self_iff, Nat.lt_one_iff, pos_of_gt, and_true, gt_iff_lt]
    have h : n ≠ 0 := by assumption
    exact Nat.zero_lt_of_ne_zero h
    have h : n ≠ 0 := by assumption
    exact Nat.bitwise_rec_lemma h

def g (n : Nat) : Nat :=
  if n = 0 then 0
  else g (n - 2 ^ (Nat.log 2 n)) + 1
  termination_by n
  decreasing_by
    simp only [tsub_lt_self_iff, zero_lt_two, pow_pos, and_true, gt_iff_lt]
    have h : n ≠ 0 := by assumption
    exact Nat.zero_lt_of_ne_zero h

lemma log2_of_2kj (k : ℕ) (j : ℕ) (h : j < 2 ^ k): Nat.log 2 (2 ^ k + j) = k := by
  apply Nat.log_eq_of_pow_le_of_lt_pow
  simp only [le_add_iff_nonneg_right, zero_le]
  rw [Nat.pow_succ, Nat.mul_two]
  exact Nat.add_lt_add_left h (2 ^ k)

theorem can_split (n : ℕ) : (∃ k : ℕ, ∃ j : ℕ, j < 2 ^ k ∧ Nat.succ n = 2 ^ k + j) := by
  apply Exists.intro (Nat.log 2 (Nat.succ n))
  apply Exists.intro (Nat.succ n - 2 ^ (Nat.log 2 (Nat.succ n)))
  apply And.intro
  . apply Nat.lt_of_add_lt_add_right (m:=2 ^ Nat.log 2 (n + 1))
    rw [Nat.sub_add_cancel, ← Nat.two_mul, ← pow_succ']
    . apply Nat.lt_pow_succ_log_self
      simp only [Nat.one_lt_ofNat]
    . apply Nat.pow_log_le_self 2
      simp only [Nat.succ_eq_add_one, ne_eq, Nat.add_eq_zero, one_ne_zero, and_false,
        not_false_eq_true]
  . rw [Nat.add_comm (2 ^ Nat.log 2 (n + 1))]
    rw [Nat.sub_add_cancel]
    apply Nat.pow_log_le_self 2
    simp only [Nat.succ_eq_add_one, ne_eq, Nat.add_eq_zero, one_ne_zero, and_false,
      not_false_eq_true]

lemma pow2_inc (n m : ℕ) (h : 2 ^ n < 2^m) : n < m := by
  rw [Nat.pow_lt_pow_iff_right] at h
  apply h
  simp

lemma pow2p_nz (n j : ℕ) : 2^n+j ≠ 0 := by
  apply Nat.ne_of_gt
  apply Nat.add_pos_left
  exact NeZero.pos (2 ^ n)

theorem q6 (n : ℕ) : f n = g n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      rw [f, g]
      simp only [↓reduceIte]
    | succ n =>
      have x := can_split n
      match x with
      | ⟨k, j, lhs, rhs⟩ =>
        rw [← Nat.succ_eq_add_one, rhs]
        match k with
        | Nat.zero =>
          simp at lhs
          rw [lhs, f, g, f, g]
          simp
        | Nat.succ k =>
          match (Nat.even_or_odd j) with
          | Or.inl je =>
            have x : Even (2^Nat.succ k) := by
              simp [Nat.even_pow]
            have ne : Even (2^Nat.succ k+j) := by
              rw [Nat.even_add]
              exact iff_of_true x je
            rw [f]
            simp
            split_ifs
            . rw [Nat.succ_eq_add_one] at ne
              have : ¬ Even (2 ^ (k + 1) + j) := by
                apply Nat.not_even_iff_odd.mpr
                assumption
              contradiction
            . rw [ih ((2 ^ Nat.succ k + j) / 2)]
              have twopos : 2>0:=by simp
              have div: (2 ^ Nat.succ k + j) / 2  = (2 ^ Nat.succ k/2 + j/2) := by
                rw [← mul_right_cancel_iff_of_pos twopos]
                rw [Nat.div_two_mul_two_of_even ne, add_mul, Nat.div_two_mul_two_of_even x, Nat.div_two_mul_two_of_even je]
              conv at div =>
                rhs
                rw [Nat.pow_succ]
              rw [div]
              rw [g]
              have _ := NeZero.ne (2^k)
              simp
              have lt: j/2*2<2^k*2:= by
                rw [Nat.div_two_mul_two_of_even je]
                rw [← Nat.pow_succ]
                exact lhs
              simp at lt
              simp [log2_of_2kj k (j / 2) lt]
              apply Eq.symm
              rw [g]
              simp [log2_of_2kj (Nat.succ k) (j) lhs]
              rw [← ih j]
              rw [f]
              split_ifs with j0
              simp [j0]
              rw [g]
              simp
              have jo :¬Even j:= by
                rw [Nat.not_even_iff_odd]
                assumption
              contradiction
              have lt1 : 2 ^ k < 2 ^ Nat.succ k + j := by
                rw [Nat.pow_succ]
                apply (Nat.lt_add_right (a:=2 ^ k) (b:=2 ^ k * 2) j)
                simp
              rw [← rhs] at lt1
              rw [ih (j/2) (Nat.lt_trans lt lt1)]
              rw [← Nat.succ_eq_add_one, rhs]
              simp
              rw [← rhs]
              exact Nat.div_lt_self' n 0
          | Or.inr jo =>
            rw [f]
            simp
            have k2 : (2 ^ Nat.succ k) > 1 := by simp
            have ke: Even (2 ^ Nat.succ k) := by
              simp [Nat.even_pow]
            have kjo : Odd (2 ^ Nat.succ k + j) := by
              rw [add_comm, Nat.odd_add]
              tauto
            split_ifs
            rw [f]
            have jg0 : j > 0 := by
              contrapose jo
              simp at jo
              simp [jo]
            have oo : Odd 1 := by simp
            have jm1e : Even (j - 1) := by
              rw [Nat.even_sub']
              exact iff_of_true jo oo
              exact jg0
            split_ifs
            have wrong:2 ^ Nat.succ k + j - 1 = 0 := by assumption
            simp at wrong
            have right:=Nat.lt_of_lt_of_le k2 (Nat.le_add_right (2^Nat.succ k) j)
            have _: ¬ (1 < 2 ^ k.succ + j) := by
              rw [Nat.sub_eq_zero_iff_le] at wrong
              intro
              exact Nat.not_le_of_gt right wrong
            contradiction
            have kj1e : Even (2 ^ Nat.succ k + j - 1) := by
              rw [Nat.even_sub']
              exact iff_of_true kjo oo
              apply Nat.le_trans (Nat.le_of_lt k2) (Nat.le_add_right (2 ^ Nat.succ k) j)
            rw [← Nat.not_odd_iff_even] at kj1e
            contradiction
            have reduce : (2 ^ Nat.succ k + j - 1) / 2*2 = (2 ^ Nat.succ k / 2 + (j-1)/2)*2:=by
              rw [Nat.div_two_mul_two_of_even, add_mul, Nat.div_two_mul_two_of_even ke, Nat.div_two_mul_two_of_even jm1e]
              have t : 2 ^ Nat.succ k + j - 1+1 = 2 ^ Nat.succ k + (j - 1)+1:= by
                rw [add_assoc, Nat.sub_add_cancel jg0]
                apply Nat.succ_pred
                simp
              simp at t
              apply t
              exact Nat.Odd.sub_odd kjo oo
            simp at reduce
            conv at reduce =>
              rhs
              rw [Nat.pow_succ]
              simp
            rw [reduce]
            rw [ih (2 ^ k + (j - 1) / 2)]
            rw [g]
            split_ifs
            have _:= pow2p_nz k ((j-1)/2)
            contradiction
            have j1lt2k : (j-1)/2*2<2^k*2:= by
              rw [Nat.div_two_mul_two_of_even jm1e]
              rw [← Nat.pow_succ]
              exact tsub_lt_of_lt lhs
            simp at j1lt2k
            have l2 := log2_of_2kj k ((j-1)/2) j1lt2k
            rw [l2]
            simp only [add_tsub_cancel_left]
            apply Eq.symm
            rw [g]
            simp
            have l2 := log2_of_2kj (Nat.succ k) (j) lhs
            rw [l2]
            simp only [Nat.succ_eq_add_one, add_tsub_cancel_left]
            rw [← ih j]
            rw [f]
            split_ifs
            have jn0 := Nat.ne_of_gt jg0
            contradiction
            rw [f]
            split_ifs with j1e0
            rw [j1e0]
            simp only [zero_add, Nat.zero_div, right_eq_add]
            rw [g]
            simp only [↓reduceIte]
            rw [← Nat.not_odd_iff_even] at jm1e
            contradiction
            rw [ih ((j-1)/2)]
            have x:2^k<Nat.succ n:= by
              have x:2^k<2^Nat.succ k:= by
                rw [Nat.pow_succ]
                simp only [zero_lt_two, pow_pos, lt_mul_iff_one_lt_right, Nat.one_lt_ofNat]
              apply Nat.lt_of_lt_of_le x (Nat.le.intro (Eq.symm rhs))
            apply Nat.lt_trans j1lt2k x
            apply Nat.lt_of_lt_of_le lhs (Nat.le.intro (Eq.symm rhs))
            have p1: 2 ^ k + (j - 1) / 2< 2 ^ Nat.succ k + j:= by
              rw [Nat.pow_succ]
              have x:2 ^ k < 2 ^ k * 2:= by simp
              have y:(j-1)/2*2 < j*2 := by
                rw [Nat.div_two_mul_two_of_even]
                have tg0: 2>1:= by simp
                have jj2:= lt_mul_right jg0 tg0
                apply Nat.lt_of_le_of_lt (Nat.pred_le j) jj2
                assumption
              simp only [zero_lt_two, mul_lt_mul_right] at y
              apply Nat.add_lt_add x y
            rw [← rhs] at p1
            apply p1
            rw [← Nat.not_even_iff_odd] at kjo
            have _: Even (2 ^ k.succ + j) := by
              apply Nat.not_odd_iff_even.mp
              assumption
            contradiction
