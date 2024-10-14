import Mathlib.Tactic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.GCDMonoid.Basic

lemma dvd_coprime_implies_natAbs_one (a b : ℤ) (h : a ∣ b) (h2 : (Int.gcd a b) = 1) : Int.natAbs a = 1 := by
  rw [← Nat.dvd_one, ← Int.ofNat_dvd_right]
  exact Int.dvd_of_dvd_mul_right_of_gcd_one (Dvd.dvd.mul_right h 1) h2

theorem x3x1norat : ¬ ∃ (x : ℚ), x*x * x + x + 1=0 := by
  simp [Rat.add_def, Rat.mul_def]
  intro x
  unfold Rat.normalize
  simp [← pow_two]
  have twoone_three: 2 + 1 = 3 := by simp
  have threeone_four: 3 + 1 = 4 := by simp
  simp [Int.natAbs_pow, Nat.Coprime.pow _ _ x.reduced, ← pow_succ, twoone_three, threeone_four]
  have asdf : Nat.gcd (Int.natAbs (x.num ^ 3 * (x.den:ℤ) + x.num * ((x.den:ℤ)^3))) (x.den ^ 4) = x.den := by
    rw [pow_succ x.den 3, pow_succ (x.den:ℤ), ← mul_assoc, ← Int.add_mul, Int.natAbs_mul]
    simp [Nat.gcd_mul_right]
    rw [pow_succ', ← mul_add, Int.natAbs_mul]
    rw [Nat.coprime_mul_iff_left]
    apply And.intro x.reduced
    rw [Int.natAbs_add_of_nonneg (sq_nonneg _) (sq_nonneg _)]
    simp [Int.natAbs_pow, pow_two (x.den)]
    exact x.reduced
  simp [asdf]
  have dnz2 : (↑x.den ≠ (0:ℤ)) := by
    simp
  conv in ((x.den:ℤ)^3) => rw [pow_succ]
  rw [← mul_assoc, ← add_mul, Int.mul_div_cancel _ dnz2]
  rw [pow_succ _ 3, Int.mul_ediv_cancel _ dnz2]
  intro num
  have dendvdnum3: ((x.den:ℤ) ∣ (x.num ^ 3)) := by
    have bla := Int.dvd_zero (x.den : ℤ)
    rw [← num, Int.add_assoc] at bla
    rw [Int.dvd_iff_dvd_of_dvd_add bla]
    simp [pow_succ', ← mul_assoc, ←Int.add_mul]
  have numdvdden3: (x.num ∣ ((x.den:ℤ) ^ 3)) := by
    have bla := Int.dvd_zero x.num
    rw [← num] at bla
    rw [← Int.dvd_iff_dvd_of_dvd_add bla, pow_succ', ← mul_add]
    apply Int.dvd_mul_right
  have numden3gcd1 : Int.gcd x.num ((x.den : ℤ)^3) = 1:= by
    simp [Int.gcd_eq_natAbs, Int.natAbs_pow]
    apply x.reduced
  have numNatAbseq1 := dvd_coprime_implies_natAbs_one x.num ((x.den : ℤ)^3) numdvdden3 numden3gcd1
  have dennum3gcd1 : Int.gcd (x.den:ℤ) (x.num^3) = 1 := by
    simp [Int.gcd_eq_natAbs, Int.natAbs_pow]
    rw [Nat.coprime_comm]
    exact x.reduced
  have deneq1 := dvd_coprime_implies_natAbs_one (x.den:ℤ) (x.num^3) dendvdnum3 dennum3gcd1
  simp at deneq1
  simp [deneq1] at num
  let l := x.num
  have leqxnum : x.num = l := by rfl
  rw [leqxnum] at num numNatAbseq1
  match l with
  | Int.ofNat m =>
    simp at numNatAbseq1
    simp [numNatAbseq1] at num
  | Int.negSucc m =>
    simp at numNatAbseq1
    simp [numNatAbseq1] at num
