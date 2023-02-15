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
  have two_eq_succ_one : Nat.succ 1=2 := by simp
  have x:Nat.succ n≥ 2^Nat.log2 (Nat.succ n) := by
    apply Nat.strong_rec_on n
    simp
    intros n ih
    simp [Nat.succ_eq_add_one]
    unfold Nat.log2
    split_ifs
    . have h1 : (n+1)/2-1<n:= by 
        have ngz : n>0:= by 
          apply by_contradiction
          have t:n+1≥2:= by assumption
          simp
          intro nz
          rw [nz] at t
          contradiction 
        match (Nat.even_or_odd n) with
        | Or.inl a => 
          have _ : Odd (n+1) := by
            apply by_contradiction
            simp
            rw [Nat.even_add_one]
            tauto
          have thing : ((n+1) / 2 )*2+1 < n*2+1:=by
            rw [Nat.div_two_mul_two_add_one_of_odd]
            simp
            apply lt_mul_right
            assumption
            simp
            assumption
          simp at thing
          have t:= Nat.sub_le ((n+1)/2) 1
          apply Nat.lt_of_le_of_lt t thing
        | Or.inr a =>
          have _ : Even (n+1) := by
            rw [Nat.even_add_one]
            rw [← Nat.odd_iff_not_even]
            assumption
          have thing : ((n+1) / 2  - 1)*2 < n*2:=by
            rw [Nat.mul_sub_right_distrib]
            rw [Nat.div_two_mul_two_of_even]
            simp
            have z1 : 0<1:= by simp
            have t := Nat.sub_lt (ngz) z1
            have t2:n≤n*2 := by 
              simp
              rw [← two_eq_succ_one, Nat.mul_succ]
              apply Nat.le_add_left (n)
            apply Nat.lt_of_lt_of_le t t2 
            assumption
          simp at thing
          apply thing
      have h2 := ih ((n+1)/2 - 1) h1
      simp at h2
      rw [Nat.succ_eq_add_one] at h2
      conv => 
        rhs
        rw [add_comm]
      have posadd:(n+1)/2-1+1= (n+1)/2 := by
        apply Nat.succ_pred
        simp
        have t: n+1≥ 2:= by assumption
        have t2:2>0:= by simp
        have t3:(n+1)/2>0:= Nat.div_pos t t2
        apply Nat.ne_of_gt t3
      rw [posadd] at h2
      have h3 : 2^Nat.log2 ((n+1)/2) *2 ≤(n+1)/2 *2:= by
        simp
        apply h2
      match (Nat.even_or_odd (n+1)) with
      | Or.inl a =>
        rw [Nat.div_two_mul_two_of_even,mul_comm,← pow_succ] at h3
        conv => 
          rhs
          rw [add_comm]
        apply h3
        assumption
      | Or.inr a =>
        have h3 : 2^Nat.log2 ((n+1)/2) *2+1 ≤(n+1)/2 *2+1:= by
          simp
          apply h2
        rw [Nat.div_two_mul_two_add_one_of_odd,mul_comm,← pow_succ] at h3
        conv => 
          rhs
          rw [add_comm]
        have lts := Nat.lt_succ_self (2 ^ (Nat.log2 ((n + 1) / 2) + 1))
        rw [Nat.succ_eq_add_one] at lts
        apply Nat.le_trans (Nat.le_of_lt lts) h3
        assumption
    . simp
  apply And.intro
  . have x: Nat.succ n - 2 ^ Nat.log2 (Nat.succ n) + 2 ^ Nat.log2 (Nat.succ n) < 2 ^ Nat.log2 (Nat.succ n) + 2 ^ Nat.log2 (Nat.succ n) := by
      have y:Nat.succ n - 2 ^ Nat.log2 (Nat.succ n) + 2 ^ Nat.log2 (Nat.succ n)=Nat.succ n := by
        rw [Nat.sub_add_cancel x]
      rw [y]
      ring
      apply Nat.strong_rec_on n
      intros n ih
      cases n with
      | zero => simp
      | succ n =>
        unfold Nat.log2
        have ooe: Even (1+1) := by simp
        split_ifs
        . match (Nat.even_or_odd n) with
          | Or.inl a =>
            have n2n : n/2<Nat.succ n := by 
              have t: n<Nat.succ n := by simp
              have t2: n/2*2≤  n*2 := by
                rw [Nat.div_two_mul_two_of_even]
                cases n with
                | zero => simp
                | succ n => 
                  apply Nat.le_of_lt
                  apply lt_mul_right
                  simp
                  simp
                apply a              
              simp at t2
              apply Nat.lt_of_le_of_lt t2 t
            
            have t := ih (n/2) n2n
            
            have o: Nat.succ (Nat.succ n) / 2*2 = Nat.succ (n/2)*2 := by
              rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one]
              rw [add_assoc]
              have n2 : Even (n+(1+1)):= by
                rw [Nat.even_add]
                tauto
              
              rw [Nat.div_two_mul_two_of_even]
              simp
              rw [add_mul]
              rw [Nat.div_two_mul_two_of_even]
              assumption
              assumption
            simp at o
            rw [pow_succ]
            rw [← o] at t
            have p := Nat.add_lt_add t t
            have m : Even (Nat.succ (Nat.succ n)) := by 
              rw [Nat.succ_eq_add_one, add_assoc]
              rw [Nat.even_add]
              tauto
            conv at p => 
              ring
              rw [Nat.div_two_mul_two_of_even]
              rfl
              apply m
            ring
            apply p
          | Or.inr a =>
            have o: Nat.succ (Nat.succ n) / 2*2+1 = Nat.succ (n/2)*2+1 := by
              rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one]
              rw [Nat.div_two_mul_two_add_one_of_odd]
              rw [add_mul]
              conv =>
                rhs
                rw [add_assoc]
                congr
                rfl
                rw [add_comm]
              rw [← add_assoc]
              rw [Nat.div_two_mul_two_add_one_of_odd]
              apply a
              have n2 : Odd (n+(1+1)):= by
                rw [Nat.odd_add]
                tauto
              rw [add_assoc]
              apply n2
            simp at o
            rw [o]

            have n2n : n/2<Nat.succ n := by 
              have t: n<Nat.succ n := by simp
              have t2: n/2*2+1≤  n*2 := by
                rw [Nat.div_two_mul_two_add_one_of_odd]
                cases n with
                | zero => simp
                | succ n => 
                  apply Nat.le_of_lt
                  apply lt_mul_right
                  simp
                  simp
                apply a
              have t3 := Nat.le_trans t2 (Nat.le_add_right (n*2) 1)
              simp at t3
              apply Nat.lt_of_le_of_lt t3 t
            
            have t := ih (n/2) n2n
            have t2:= Nat.succ_le_of_lt t
            rw [pow_succ]
            rw [← o] at t
            have p := Nat.add_le_add t2 t2
            have m : Odd (Nat.succ (Nat.succ n)) := by 
              rw [Nat.succ_eq_add_one, add_assoc]
              rw [Nat.odd_add]
              tauto
            conv at p => ring
            rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, add_mul, add_mul] at p
            have ot : 1 * 2 = 1 + 1 := by simp
            rw [ot] at p
            rw [← add_assoc, ← add_assoc, Nat.div_two_mul_two_add_one_of_odd] at p
            simp at p
            conv at p => ring
            have x:3+n=Nat.succ (2+n):=by 
              rw [Nat.succ_eq_add_one]
              ring
            rw [x] at p
            have p2 := Nat.lt_of_succ_le p
            rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one]
            ring
            apply p2
            assumption
        . have t: ¬Nat.succ (Nat.succ n) ≥ 2 := by assumption
          rw [Nat.succ_eq_add_one] at t
          simp at t
          conv at t => ring
          simp at t
    simp at x
    apply x
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
        . have d : 2^k+j/2>0:= by simp
          have _ := Nat.ne_of_gt d
          contradiction
        have e:2^k+j/2>0:= by simp
        simp
        have f2 := Nat.ne_of_lt e
        rw [log2_of_2kj k (j/2) c]
        simp
        apply Eq.symm
        rw [g]
        split_ifs
        . have f2:2 ^ k * 2 + j > 0:= by simp
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

            have h2 : j>0:= by
              apply by_contradiction
              simp
              intro jz
              have ej : Even j := by
                rw [jz]
                simp
              rw [Nat.even_iff_not_odd] at ej
              contradiction
            
            cases j with
            | zero =>
              contradiction
            | succ j =>
              simp
            
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
            have ij2 : (j-1)/2*2 < 2^k*2 := by
              rw [← Nat.pow_succ]
              rw [Nat.div_two_mul_two_of_even]
              have x : j-1≤j := by simp
              apply Nat.lt_of_le_of_lt x ij
              have oneOdd : Odd 1 := by simp
              apply Nat.Odd.sub_odd a oneOdd
            simp at ij2
            rw [log2_of_2kj (k) ((j-1)/2) ij2]
            simp
            apply Eq.symm
            cases j with
            | zero =>
              contradiction
            | succ j1 =>
              have h2 := can_split (j1)
              apply Exists.elim h2
              intros k1 h2
              apply Exists.elim h2
              intros j2 h2
              match h2 with
              | And.intro lhs rhs =>
                rw [rhs]
                let bla : k1<Nat.succ k:=by
                  have t := Nat.le.intro (Eq.symm rhs)
                  have bla:= Nat.lt_of_le_of_lt t ij
                  apply pow2_inc k1 (Nat.succ k) bla
                rw [← ih k1 bla j2 lhs]
                unfold f
                split_ifs
                have _ : 2^k1+j2≠ 0 := by
                  have _ : 2^k1≥1 := by
                    simp
                    apply Nat.pos_pow_of_pos k1
                    simp
                  apply Nat.ne_of_gt
                  simp
                contradiction
                simp at jm1e
                
                unfold f
                split_ifs
                . simp
                  have x:2 ^ k1 + j2 - 1 = 0:= by assumption
                  rw [x]
                  simp
                . have x : Odd (2 ^ k1 + j2 - 1) := by assumption
                  rw [Nat.odd_iff_not_even, ← Nat.even_add_one] at x
                  rw [← rhs] at x
                  simp at x
                  rw [Nat.even_iff_not_odd] at x
                  contradiction
                . rw [← rhs]
                  simp
                  have ej3 : ∃ j3 : ℕ, j3 = (j1)/2 := by simp
                  apply Exists.elim ej3
                  intros j3 h3t
                  rw [←h3t ]
                  cases (j3) with
                  | zero =>
                    simp
                  | succ j3 =>
                    have h3 := can_split j3
                    apply Exists.elim h3
                    intros k2 h3
                    apply Exists.elim h3
                    intros j4 h3
                    match h3 with
                    | And.intro lhs2 rhs2 =>
                      rw [rhs2]
                      have thingy:(j1/2)<2^Nat.succ k := by
                        simp
                        have tmp: j1/2*2<Nat.succ j1*2 := by 
                          cases j1 with
                          | zero => simp
                          | succ j1 =>
                            rw [Nat.div_two_mul_two_of_even]
                            rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one]
                            have two_eq_succ_one : Nat.succ 1=2 := by simp
                            rw [← two_eq_succ_one]
                            rw [add_assoc]
                            rw [add_mul]
                            conv =>
                              rhs
                              congr
                              rw [Nat.mul_succ]
                            simp
                            rw [Nat.add_comm]
                            conv =>
                              rhs
                              rw [Nat.add_comm, ← Nat.add_assoc]
                            simp
                            rw [two_eq_succ_one]
                            have asdf : 1<(1+1)*2 := by simp
                            apply Nat.lt_of_lt_of_le asdf (Nat.le_add_right ((1+1)*2) j1)
                            assumption
                        simp at tmp
                        apply Nat.lt_trans tmp ij
                      rw [← h3t] at thingy
                      have bla2 : k2<Nat.succ k:= by
                        have t := Nat.le.intro (Eq.symm rhs2)
                        have bla := Nat.lt_of_le_of_lt t thingy
                        apply pow2_inc k2 (Nat.succ k) bla
                      rw [ih k2 bla2 j4 lhs2]
                      
                rw [rhs] at a
                contradiction
          simp
          rw [Nat.pow_succ] at ij
          have x:(j-1)/2*2<2^k*2 := by
            rw [Nat.div_two_mul_two_of_even]
            have y:(j-1)≤ j := by simp
            apply Nat.lt_of_le_of_lt y ij
            apply jm1e
          simp at x
          apply x

theorem q6 (n : ℕ) : f n = g n := by
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
      apply q6a k j lhs
