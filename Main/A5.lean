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
  apply Exists.intro (Nat.log2 (Nat.succ  n))
  apply Exists.intro (Nat.succ n-2^Nat.log2 (Nat.succ n))
  have x:Nat.succ n≥ 2^Nat.log2 (Nat.succ n) := by
    apply Nat.strong_rec_on n
    simp
    intros n ih
    simp [Nat.succ_eq_add_one]
    ring
    unfold Nat.log2
    split_ifs
    . have h:((1 + n) / 2 )*2 < n*2 := by 
        match (Nat.even_or_odd n) with
        | Or.inl a => 
          sorry
        | Or.inr a =>
          sorry
      simp at h
      have h1 : (1+n)/2-1<n:= by 
        sorry
      have h2 := ih ((1+n)/2 - 1) h1
      simp at h2
      have h3 := Nat.lt_of_le_of_lt h2 (Nat.succ_lt_succ h1)
      rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one] at h3
      conv => 
        rhs
        rw [add_comm]
      -- apply Nat.le_of_lt h3
      sorry
    . simp
  apply And.intro
  . sorry
  . match (Nat.le.dest x) with
    | Exists.intro k hk =>
      conv => 
        rhs
        congr
        rfl
        congr
        rw [← hk]
      simp
      rw [hk]

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

theorem q6a : ∀ k:ℕ,∀ j:ℕ,j<2^k→ f (2^k+j) = g (2^k+j) := by
  intro k
  apply Nat.strong_rec_on k
  intro k ih
  cases k with
  | zero =>
    simp
    rw [f, g]
    simp
  | succ k =>
    intros j ij
    rw [f]
    match (Nat.even_or_odd j) with
    | Or.inl a => 
      have h : Even (2 ^ Nat.succ k) := by
        rw [Nat.even_pow]
        simp
      have i : Even (2^Nat.succ k + j) := by
        rw [Nat.even_add]
        tauto
      simp
      split_ifs
      . rw [Nat.pow_succ]
        simp
        have b : ((2 ^ k * 2 + j) / 2) * 2 = (2^k)*2+(j/2)*2 := by
          rw [Nat.div_two_mul_two_of_even, Nat.div_two_mul_two_of_even]
          assumption
          assumption
        rw [← add_mul] at b
        simp at b
        rw [b]
        have c : (j/2)*2<2^k*2 := by 
          rw [Nat.div_two_mul_two_of_even]
          apply ij
          apply a
        simp at c
        rw [ih k (Nat.lt_succ_self k) (j/2) c]
        rw [g]
        split_ifs
        . have d : 2^k+j/2>0:= by
            have e : 2^k>0:= Nat.pos_pow_of_pos k (Nat.zero_lt_succ 1)
            simp
          have _ := Nat.ne_of_gt d
          contradiction
        have d:2^k>0:= Nat.pos_pow_of_pos k (Nat.zero_lt_succ 1)
        have e:2^k+j/2>0:= by
          simp
        simp
        have f2 := Nat.ne_of_lt e
        rw [log2_of_2kj k (j/2) c]
        simp
        apply Eq.symm
        rw [g]
        split_ifs
        . have f2:2 ^ k * 2 + j > 0:= by
            have g:2^k*2>0*2:= by
              rw [Nat.zero_mul]
              rw [← Nat.pow_succ]
              apply Nat.pos_pow_of_pos
              simp
            simp
          have _ := Nat.ne_of_gt f2
          contradiction
        rw [← Nat.pow_succ]
        rw [log2_of_2kj (Nat.succ k) (j) ij]
        simp
        cases j with
        | zero =>
          simp
        | succ j =>
          have h2 := can_split j
          match h2 with
          | Exists.intro k1 asdf2 =>
            simp at asdf2
            match asdf2 with
            | Exists.intro j1 asdf4 =>
              simp at asdf4
              match asdf4 with
              | And.intro lh rh =>
                rw [rh]
                have x: k1<Nat.succ k := by 
                  have t := Nat.le.intro (Eq.symm rh)
                  have bla:= Nat.lt_of_le_of_lt t ij
                  apply pow2_inc k1 (Nat.succ k) bla
                rw [← ih k1 x j1 lh]
                rw [f]
                split_ifs
                have _ : 2^k1+j1≠ 0 := by
                  have _ : 2^k1>0 := Nat.pos_pow_of_pos k1 (Nat.zero_lt_succ 1)
                  apply Nat.ne_of_gt
                  simp
                contradiction
                have x1 :Odd (2 ^ k1 + j1):= by assumption
                rw [← rh] at x1
                rw [Nat.even_iff_not_odd] at a
                contradiction
                rw [← rh]
                revert c
                cases (Nat.succ j / 2) with
                | zero =>
                  simp
                | succ j2 =>
                  intro c
                  have h3 := can_split (j2)
                  match h3 with
                  | Exists.intro k2 asdf =>
                    match asdf with
                    | Exists.intro j2 asdf =>
                      simp at asdf
                      match asdf with
                      | And.intro lh1 rh1 =>
                        rw [rh1]
                        apply ih
                        have t := Nat.le.intro (Eq.symm rh1)
                        have bla:= Nat.lt_of_le_of_lt t c
                        have bla1:= pow2_inc k2 (k) bla
                        have bla2:=Nat.le_succ k
                        apply Nat.le_trans bla1 bla2
                        assumption
      . contradiction
    | Or.inr a =>
      have h : Even (2 ^ Nat.succ k) := by
        rw [Nat.even_pow]
        simp
      have i : Odd (2^Nat.succ k + j) := by
        rw [add_comm, Nat.odd_add]
        tauto
      simp
      split_ifs
      . rw [Nat.odd_iff_not_even] at i
        contradiction
      . rw [Nat.pow_succ]
        rw [f]
        split_ifs
        . have p : 2^k*2≥ 2 := by
            simp
            apply Nat.pos_pow_of_pos k
            simp
          have p2 : 2^k*2+j-1>0 := by
            simp
            apply Nat.le_trans p (Nat.le_add_right (2^k*2) j)
          have _ := Nat.ne_of_gt p2
          contradiction
        . have z : 2 ^ k * 2 + j - 1 + 1 = 2 ^ k * 2 + j := by
            apply Nat.succ_pred
            rw [Nat.sub]
            apply Nat.ne_of_gt

            have x : 2^k*2≥ 2:= by
              simp
              apply Nat.pos_pow_of_pos k
              simp
            have x2 := Nat.le_add_right (2^k*2) j
            have x3 := Nat.le_trans x x2
            have x4 : 0<2 := by simp
            apply Nat.lt_of_lt_of_le x4 x3
          have h : Odd (2 ^ k * 2 + j - 1) := by assumption
          rw [Nat.odd_iff_not_even, ← Nat.even_add_one] at h
          rw [z] at h
          contradiction
        . have jm1e : Even (j-1) := by
            have b : Odd 1 := by simp
            apply Nat.Odd.sub_odd a b

          have h : (2 ^ k * 2 + j - 1) / 2 * 2 = (2 ^ k + (j - 1) / 2)*2 := by
            rw [Nat.div_two_mul_two_of_even]
            rw [add_mul]
            rw [Nat.div_two_mul_two_of_even]
            sorry
            
            apply jm1e
            have h2: ¬Odd (2 ^ k * 2 + j - 1) := by assumption
            rw [Nat.odd_iff_not_even] at h2
            simp at h2
            apply h2
          simp at h
          rw [h]
          rw [ih]
          apply Eq.symm
          rw [g]
          split_ifs
          . have t : 2^k*2+j>0 := by 
              have x : 2^k*2≥ 2 := by
                simp
                apply Nat.pos_pow_of_pos k
                simp
              have x1 := Nat.le_add_right (2^k*2) j
              have x2 : 0<2 := by simp
              apply Nat.lt_of_lt_of_le x2 (Nat.le_trans x x1)
            have _ := Nat.ne_of_gt t
            contradiction
            
          . rw [← Nat.pow_succ]
            rw [log2_of_2kj (Nat.succ k) (j) ij]
            simp
            apply Eq.symm
            rw [g]
            split_ifs
            have _ : 2^k+(j-1)/2≠ 0 := by
              have _ : 2^k≥1 := by
                simp
                apply Nat.pos_pow_of_pos k
                simp
              apply Nat.ne_of_gt
              simp
            contradiction
            have ij2 : (j-1)/2 < 2^k := by
              sorry
            rw [log2_of_2kj (k) ((j-1)/2) ij2]
            simp
            sorry
          simp
          rw [Nat.pow_succ] at ij
          have x:(j-1)/2*2<2^k*2 := by
            rw [Nat.div_two_mul_two_of_even]
            have y:(j-1)≤ j := by simp
            apply Nat.lt_of_le_of_lt y ij
            apply jm1e
          simp at x
          apply x
    