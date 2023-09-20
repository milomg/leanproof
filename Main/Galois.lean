import Mathlib.RingTheory.QuotientNoetherian
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib

theorem PigeonholeNatOrds (n : Nat) : ∀ f: ({m : ℕ // m ≤ Nat.succ n} -> {m : ℕ // m < Nat.succ n}), ¬ Function.Injective f := by
  unfold Function.Injective
  simp
  induction n with
  | zero =>
    intros f
    apply Exists.intro 0
    simp
    apply Exists.intro 1
    simp
    have olt1 : 0 < 1 := by
      apply Nat.zero_lt_one
    have olteq1 : 0 ≤ Nat.succ Nat.zero := by
      apply Nat.zero_le
    have lhs : f { val := 0, property := olteq1} = ⟨0, olt1⟩ := by
      simp
      have j := Subtype.property (f { val := 0, property := olteq1})
      simp at j
      apply Subtype.eq
      apply j
    
    have rhs : f { val := 1, property := Nat.succ_pos Nat.zero} = ⟨0, olt1⟩ := by
      simp
      have j := Subtype.property (f { val := 1, property := Nat.succ_pos Nat.zero})
      simp at j
      apply Subtype.eq
      apply j
    rw [lhs, rhs]

  | succ n ih =>
    intro f
    apply by_contradiction
    simp
    intro x
    sorry

theorem obviously (a b:Nat) (h:a≤3) (h2:b>0) (h4:a>0) (h3:a+b=3): a=1∨ a=2 := by
  have ale3:a<3 := by
    contrapose h2
    simp at h2 ⊢
    rw [Nat.le_antisymm h h2] at h3
    simp at h3
    apply h3
  rw [Decidable.or_iff_not_imp_right]
  intro aneq2
  rw [Nat.lt_succ] at ale3
  have alt2 := Nat.lt_of_le_of_ne ale3 aneq2
  have zlta := Nat.succ_lt_succ h4
  rw [Nat.lt_succ] at alt2 zlta
  exact Nat.le_antisymm alt2 h4


open Classical

open BigOperators Polynomial

universe u v w

-- variable {R : Type u} [CommRing R]

open Ideal DoubleQuot Polynomial
/--
theorem complicatedFromGauss (I : Ideal R) (f : R[X])  (proof1 : ¬ ∃ (g h : (R ⧸ I)[X]), g * h = Polynomial.map (Ideal.Quotient.mk I) f) : Irreducible f := by 
  contrapose proof1
  simp
  simp at proof1

  sorry
--Polynomial.Monic.irreducible_of_irreducible_map
--/
-- x^3 + x + 1 has no rational roots
noncomputable def f : ℤ[X] := Polynomial.X ^ 3 + Polynomial.X + 1



variable (φ := Int.castRingHom (ZMod 2))
theorem thisPolyNoRatRoots [CommSemiring ℤ]: ¬ ∃ (x : ℚ),  (f.map (Int.castRingHom ℚ)).eval x = 0 := by
  -- have fprim : f.IsPrimitive := by 
  --   simp
  let phi := Int.castRingHom (ZMod 2)
  apply @Classical.by_contradiction
  simp
  intro x
  rw [← Polynomial.IsRoot.def]
  rw [← Polynomial.dvd_iff_isRoot]
  rw [dvd_iff_exists_eq_mul_left]
  have fIrr : Irreducible f := by
    have _ : IsDomain (ZMod 2) := by 
      apply ZMod.instIsDomainZModToSemiringToDivisionSemiringToSemifieldInstFieldZMod 2
    
    apply (Polynomial.Monic.irreducible_of_irreducible_map phi)
    unfold Monic
    unfold Polynomial.leadingCoeff
    have deg3 : natDegree f = 3 := by
      rw [f]
      apply natDegree_eq_of_degree_eq_some
      apply degree_eq_of_le_of_coeff_ne_zero
      apply degree_le_of_natDegree_le
      rw [natDegree_le_iff_coeff_eq_zero]
      simp
      intros N h
      rw [coeff_X, ← monomial_zero_one, coeff_monomial]
      have nneq3 : ¬(N = 3) := Nat.ne_of_gt h
      have nneq1 : ¬(1 = N) := by 
        apply Nat.ne_of_lt
        apply Nat.lt_trans (Nat.one_lt_succ_succ 1) h
      have nneq0 : ¬(0 = N) := by 
        apply Nat.ne_of_lt
        apply Nat.lt_trans (Nat.succ_pos 2) h
      split_ifs <;> try contradiction
      simp
      simp
      rw [coeff_X, ← monomial_zero_one, coeff_monomial]
      simp
    rw [deg3, f]
    simp
    rw [coeff_X, ← monomial_zero_one, coeff_monomial]
    simp
    unfold f
    simp
    apply Irreducible.mk
    rw [Polynomial.Monic.isUnit_iff]
    simp
    have fac1 : ((Polynomial.X :(ZMod 2)[X]) ^ 3 + X) = (X ^ 2 + 1)*X := by
      ring
    rw [fac1]
    simp
    rw [not_or]
    apply And.intro
    
    . 
      apply Polynomial.X_pow_add_C_ne_zero
      simp
    . apply Polynomial.X_ne_zero
    
    . sorry
    
    . 
      intros a b h
      have fz2deg3 : natDegree ((X : (ZMod 2)[X])^3 + X + 1) = 3 := by
        apply natDegree_eq_of_degree_eq_some
        apply degree_eq_of_le_of_coeff_ne_zero
        apply degree_le_of_natDegree_le
        rw [natDegree_le_iff_coeff_eq_zero]
        simp
        intros N h
        rw [coeff_X, ← monomial_zero_one, coeff_monomial]
        have nneq3 : ¬(N = 3) := Nat.ne_of_gt h
        have nneq1 : ¬(1 = N) := by 
          apply Nat.ne_of_lt
          apply Nat.lt_trans (Nat.one_lt_succ_succ 1) h
        have nneq0 : ¬(0 = N) := by 
          apply Nat.ne_of_lt
          apply Nat.lt_trans (Nat.succ_pos 2) h
        split_ifs <;> try contradiction
        simp
        simp
        rw [coeff_X, ← monomial_zero_one, coeff_monomial]
        simp
      have ane0 : a≠0 := by
        intro a0
        rw [a0] at h
        simp at h
        rw [h] at fz2deg3
        simp at fz2deg3
      have bne0 : b≠0 := by
        intro b0
        rw [b0] at h
        simp at h
        rw [h] at fz2deg3
        simp at fz2deg3
      have tempname : natDegree (a) + natDegree (b) = 3 := by
        rw [← Polynomial.natDegree_mul ane0 bne0]
        rw [← h]
        apply fz2deg3
      
      match Nat.eq_zero_or_pos (natDegree b) with
      | Or.inl h =>
        apply Or.inr
        rw [← degree_eq_iff_natDegree_eq bne0] at h
        have := eq_C_of_degree_eq_zero h
        rw [this]
        rw [Polynomial.isUnit_iff]
        apply Exists.intro (coeff b 0)
        simp at this ⊢
        sorry
      | Or.inr bge0 =>
        match Nat.eq_zero_or_pos (natDegree a) with
        | Or.inl h =>
          apply Or.inr
          sorry
        | Or.inr age0 =>
          have aeq1or2 : natDegree a = 1 ∨ natDegree a = 2 := by
            have ale3 : natDegree a ≤ 3 := by
              rw [le_iff_exists_add]
              apply Exists.intro (natDegree b)
              apply Eq.symm tempname
            apply obviously (natDegree a) (natDegree b) ale3 bge0 age0 tempname


          sorry
      
  --have deg3 : Polynomial. (Polynomial.map (Int.castRingHom ℚ f))
  --rw [Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast]
  sorry
