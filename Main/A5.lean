import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Pow
import Mathlib.Tactic.Ring

def f (n : Nat) : Nat :=
  if n = 0 then 0
  else if Odd n then f (n - 1) + 1
  else f (n / 2)
  termination_by f n => n
  decreasing_by
      simp_wf
      have h : n ≠ 0 := by assumption
      first | apply Nat.pred_lt h
            | have k : 2 > 1 := by simp
              apply Nat.div_lt_self (Nat.zero_lt_of_ne_zero h) k

def g (n : Nat) : Nat :=
  if n = 0 then 0
  else g (n - 2 ^ (Nat.log2 n)) + 1
  termination_by _ n => n
  decreasing_by
      simp_wf
      have h : n ≠ 0 := by assumption
      apply Nat.sub_lt (Nat.zero_lt_of_ne_zero h)
      apply Nat.pos_pow_of_pos
      simp

theorem log2_of_2kj (k : ℕ) (j : ℕ) (h : j<2^k): Nat.log2 (2 ^ k+j) = k := by
  revert j
  induction k with
  | zero =>
    intros j h
    simp at h
    rw [h]
    simp
  | succ k ih =>
    intros j h
    unfold Nat.log2
    simp
    split_ifs
    simp [Nat.pow_succ]
    have _ : Even (2^k*2) := by
      simp [Nat.even_pow]
    have h2 : (2^k*2+j)/2=(2^k+(j/2)) := by
      match (Nat.even_or_odd j) with
      | Or.inl a => 
        have _ : Even (2^k*2+j) := by
          rw [Nat.even_add]
          tauto
        have h4:(2^k*2+j)/2*2=(2^k+(j/2))*2 := by
          rw [Nat.div_two_mul_two_of_even, add_mul, Nat.div_two_mul_two_of_even]
          assumption
          assumption
        simp at h4
        apply h4
      | Or.inr a => 
        have _ : Odd (2^k*2+j) := by
          rw [add_comm, Nat.odd_add]
          tauto
        have h4:(2^k*2+j)/2*2+1=(2^k+(j/2))*2+1 := by
          rw [Nat.div_two_mul_two_add_one_of_odd, add_mul]
          rw [add_assoc, Nat.div_two_mul_two_add_one_of_odd]
          assumption
          assumption
        simp at h4
        apply h4
    rw [h2]
    apply ih
    rw [Nat.pow_succ] at h
    apply by_contradiction
    simp
    intro h3
    have h4: j/2*2≥2^k*2 := by
      simp
      assumption 
    have h5: j/2*2≤ j := by
      match (Nat.even_or_odd j) with
      | Or.inl a => 
        rw [Nat.div_two_mul_two_of_even]
        simp
        apply a
      | Or.inr a =>
        have b := Nat.div_two_mul_two_add_one_of_odd a
        have c := Nat.le_succ j
        conv at c => 
          lhs 
          rw [← b]
        rw [Nat.succ_eq_add_one] at c
        simp at c
        apply c
    have _ := Nat.lt_of_le_of_lt (Nat.le_trans h4 h5) h
    have _ := Nat.lt_irrefl (2^k*2)
    contradiction
    have h2: 2≤2^Nat.succ k := by 
      rw [Nat.pow_succ]
      simp
      apply Nat.pos_pow_of_pos
      simp
    have h3 := Nat.le_trans h2 (Nat.le_add_right (2^Nat.succ k) j)
    contradiction

theorem can_split (n:ℕ): (∃ k:ℕ,∃j:ℕ , j<2^k∧ Nat.succ n=2^k+j ):= by
  induction n with
  | zero => 
    apply Exists.intro 0
    apply Exists.intro 0
    simp
  | succ n ih =>
    match ih with 
    | Exists.intro k tmp =>
      match tmp with
      | Exists.intro j tmp =>
        match tmp with
        | And.intro lhs rhs =>
          have j1leq2k : j+1≤2^k := by
            apply Nat.le_of_lt_succ
            rw [Nat.succ_eq_add_one]
            simp
            apply lhs
          have mycases : j+1<2^k ∨ j+1=2^k := by
            rw [← le_iff_lt_or_eq]
            apply j1leq2k
          match mycases with
          | Or.inl lt =>
            apply Exists.intro k
            apply Exists.intro (j+1)
            apply And.intro lt
            rw [rhs]
            rw [Nat.succ_eq_add_one]
            rw [add_assoc]
          | Or.inr eq =>
            apply Exists.intro (Nat.succ k)
            apply Exists.intro 0
            apply And.intro
            simp
            rw [Nat.pow_succ, Nat.add_zero]
            have two_eq_one_plus_one : 2=1+1 := by simp
            conv =>
              rhs
              congr
              rfl
              rw [two_eq_one_plus_one]
            rw [Nat.mul_add, Nat.mul_one]
            conv =>
              rhs
              congr
              rfl
              rw [← eq]
            rw [rhs]
            rw [Nat.succ_eq_add_one]
            rw [add_assoc]

theorem pow2_inc (n m : ℕ) (h : 2 ^ n < 2^m) : n < m := by
  apply by_contradiction
  simp
  intro h2
  have h3:2^n≥2^m := by
    match (Nat.le.dest h2) with
    | Exists.intro k hk =>
      rw [← hk]
      rw [pow_add]
      simp
      apply Nat.pos_pow_of_pos
      simp
  have _:= Nat.lt_irrefl (2^m)
  have _:= Nat.lt_of_le_of_lt h3 h
  contradiction

theorem pow2_nz (n : ℕ) : 2^n ≠ 0 := by
  apply Nat.ne_of_gt
  apply Nat.pos_pow_of_pos n
  simp

theorem pow2p_nz (n j : ℕ) : 2^n+j ≠ 0 := by
  apply Nat.ne_of_gt
  apply Nat.lt_of_lt_of_le _ (Nat.le_add_right (2^n) j)
  apply Nat.pos_pow_of_pos n
  simp

theorem q6 (n : ℕ) : f n = g n := by
  apply Nat.strong_rec_on n
  intro n ih
  cases n with
  | zero => simp
  | succ n =>
    have x := can_split n
    apply Exists.elim x
    intros k x
    apply Exists.elim x
    intros j x
    match x with
    | And.intro lhs rhs =>
      rw [rhs]
      match k with
      | Nat.zero =>
        simp at lhs
        rw [lhs]
        rw [f, g]
        simp
      | Nat.succ k => 
        match (Nat.even_or_odd j) with
        | Or.inl je =>
          have x : Even (2^Nat.succ k) := by
              simp [Nat.even_pow]
          have ne : Even (2^Nat.succ k+j) := by 
            rw [Nat.even_add]
            tauto
          rw [f]
          simp
          split_ifs
          . rw [ih ((2 ^ Nat.succ k + j) / 2)]
            have div: (2 ^ Nat.succ k + j) / 2 *2 = (2 ^ Nat.succ k/2 + j/2)*2 := by
              rw [Nat.div_two_mul_two_of_even, add_mul, Nat.div_two_mul_two_of_even, Nat.div_two_mul_two_of_even]
              assumption
              assumption
              assumption
            conv at div =>
              rhs
              rw [Nat.pow_succ]
            simp at div
            rw [div]
            rw [g]
            have _ := pow2_nz (k)
            simp
            split_ifs
            tauto
            have lt: j/2*2<2^k*2:= by
              rw [Nat.div_two_mul_two_of_even]
              rw [← Nat.pow_succ]
              assumption
              assumption
            simp at lt
            have reduce := log2_of_2kj k (j / 2) lt
            rw [reduce]
            simp
            apply Eq.symm
            rw [g]
            simp
            have reduce := log2_of_2kj (Nat.succ k) (j) lhs
            rw [reduce]
            simp
            rw [← ih j]
            rw [f]
            split_ifs
            have j0 :j=0:= by assumption
            rw [j0]
            simp
            have jo :Odd j:= by assumption
            rw [Nat.even_iff_not_odd] at je
            contradiction
            have lt1:2^k<2^Nat.succ k + j:= by
              rw [Nat.pow_succ]
              have x:2 ^ k < 2 ^ k * 2:= by
                simp
              apply Nat.lt_of_lt_of_le x (Nat.le_add_right (2^k*2) j)
            rw [← rhs] at lt1
            rw [ih (j/2) (Nat.lt_trans lt lt1)]
            rw [rhs]
            simp
            rw [← rhs]
            apply Nat.div_lt_self
            simp
            simp
          . contradiction
        | Or.inr jo =>
          rw [f]
          simp
          have k2 :(2^Nat.succ k)>1:= by simp
          have ke: Even (2^Nat.succ k) := by
            simp [Nat.even_pow]
          have kjo : Odd (2^Nat.succ k+j):= by 
            rw [add_comm]
            rw [Nat.odd_add]
            tauto
          split_ifs
          rw [Nat.odd_iff_not_even] at kjo
          contradiction
          rw [f]
          have jg0:j>0:= by
            apply by_contradiction
            simp
            intro jz
            rw [jz] at jo
            contradiction
          have oo : Odd 1:= by simp
          have jm1e : Even (j-1) := by
            rw [Nat.even_sub']
            tauto
            have x := Nat.succ_lt_succ jg0
            rw [Nat.succ_eq_add_one] at x
            simp at x
            apply Nat.le_of_lt_succ x
          split_ifs
          have wrong:2 ^ Nat.succ k + j - 1 = 0:=by assumption
          simp at wrong
          have right:=Nat.lt_of_lt_of_le k2 (Nat.le_add_right (2^Nat.succ k) j)
          have _ := Nat.not_le_of_gt right
          contradiction
          have kj1e : Even (2^Nat.succ k+j-1):= by
            rw [Nat.even_sub']
            tauto
            apply Nat.le_trans (Nat.le_of_lt k2) (Nat.le_add_right (2^Nat.succ k) j)
          rw [Nat.even_iff_not_odd] at kj1e
          contradiction
          have reduce : (2 ^ Nat.succ k + j - 1) / 2*2 = (2 ^ Nat.succ k / 2 + (j-1)/2)*2:=by
            rw [Nat.div_two_mul_two_of_even, add_mul, Nat.div_two_mul_two_of_even, Nat.div_two_mul_two_of_even]
            have jsp:j-1+1=j:= by 
              apply Nat.succ_pred
              simp
              apply Nat.ne_of_gt
              apply jg0
            have t : 2 ^ Nat.succ k + j - 1+1 = 2 ^ Nat.succ k + (j - 1)+1:= by
              rw [add_assoc]
              rw [jsp]
              apply Nat.succ_pred
              simp
            simp at t
            apply t
            rw [Nat.even_sub']
            tauto
            apply (Nat.succ_le_of_lt jg0)
            assumption
            have x : ¬Odd (2 ^ Nat.succ k + j - 1):= by assumption
            rw [← Nat.even_iff_not_odd] at x
            apply x
          simp at reduce
          conv at reduce =>
            rhs
            rw [Nat.pow_succ]
            simp
          rw [reduce]
          rw [ih (2^k+(j-1)/2)]
          rw [g]
          split_ifs
          have _:= pow2p_nz k ((j-1)/2)
          contradiction
          have j1lt2k : (j-1)/2*2<2^k*2:= by 
            rw [Nat.div_two_mul_two_of_even]
            rw [← Nat.pow_succ]
            have x:j-1≤ j:= by simp
            apply Nat.lt_of_le_of_lt x lhs
            assumption
          simp at j1lt2k
          have l2 := log2_of_2kj k ((j-1)/2) j1lt2k
          rw [l2]
          simp
          apply Eq.symm
          rw [g]
          simp
          have l2 := log2_of_2kj (Nat.succ k) (j) lhs
          rw [l2]
          simp
          rw [← ih j]
          rw [f]
          split_ifs
          have jn0 :¬ j=0:= Nat.ne_of_gt jg0
          contradiction
          rw [f]
          split_ifs
          have j1e0: j-1=0:= by assumption
          rw [j1e0]
          simp
          rw [Nat.even_iff_not_odd] at jm1e
          contradiction
          rw [ih ((j-1)/2)]
          have x:2^k<Nat.succ n:= by
            have x:2^k<2^Nat.succ k:= by
              rw [Nat.pow_succ]
              simp
            apply Nat.lt_of_lt_of_le x (Nat.le.intro (Eq.symm rhs))
          apply Nat.lt_trans j1lt2k x
          apply Nat.lt_of_lt_of_le lhs (Nat.le.intro (Eq.symm rhs))
          have p1: 2 ^ k + (j - 1) / 2< 2 ^ Nat.succ k + j:= by
            rw [Nat.pow_succ]
            simp
            have x:2 ^ k < 2 ^ k * 2:= by simp
            have y:(j-1)/2*2 < j*2 := by 
              rw [Nat.div_two_mul_two_of_even]
              have tg0: 2>1:= by simp
              have jj2:= lt_mul_right jg0 tg0
              apply Nat.lt_of_le_of_lt (Nat.pred_le j) jj2
              assumption
            simp at y
            apply Nat.add_lt_add x y
          rw [← rhs] at p1
          apply p1
