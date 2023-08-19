import Mathlib

variable {E: Type _} [NormedAddCommGroup E]

theorem oneoneonea (x: E) : ‖x‖ ≥ 0 := by
  exact norm_nonneg x

theorem oneononeb (x: E) : ‖x‖ = 0 ↔ x = 0 := by
  exact norm_eq_zero

theorem oneonetwoa [InnerProductSpace ℝ E] (x y: E) : ⟪x, y⟫_ℝ ≤ ‖x‖ * ‖y‖ := by
  exact real_inner_le_norm x y

theorem oneonetwob [InnerProductSpace ℝ E] (x y : E) : (‖⟪x, y⟫_ℝ‖ = ‖x‖ * ‖y‖) ↔ (∃ a b : ℝ, a • x = b • y ∧ (a≠0 ∨ b≠0)) := by
  apply Iff.intro
  intro h
  cases em (‖x‖=0) with
  | inl h2 => 
    simp at h2
    use 1
    use 0
    simp [h2]
  | inr h2 =>
    simp at h2
    have := (@norm_inner_eq_norm_tfae ℝ _ _ _ _ x y).out 0 2
    rw [this] at h
    match h with
    | Or.inl _ => contradiction
    | Or.inr (⟨r,h⟩) => 
      use r
      use 1
      simp [h]
  intro h
  let ⟨a,b,h1,h2⟩ := h
  have := (@norm_inner_eq_norm_tfae ℝ _ _ _ _ x y).out 0 2
  rw [this]
  cases em (x=0) with
  | inl h3 => tauto
  | inr h3 =>
    apply Or.inr
    use a/b
    rw [@division_def]
    rw [mul_comm]
    rw [@mul_smul]
    rw [h1]
    apply Eq.symm (inv_smul_smul₀ _ y)
    match h2 with
    | Or.inl h2 =>
      contrapose h2
      simp at h2
      simp [h2, h3] at h1
      simp [h1]
    | Or.inr h2 =>
      apply h2
      
theorem oneonethree (x y: E) : (‖x+y‖≤‖x‖+‖y‖):= by
  exact norm_add_le x y

theorem oneonefour [InnerProductSpace ℝ E] (a:ℝ) (x: E) : ‖a • x‖ = ‖a‖ * ‖x‖ := by
  exact norm_smul a x

theorem onetwoone  [InnerProductSpace ℝ E] (x y: E):⟪x, y⟫_ℝ = ⟪y,x⟫_ℝ := by
  exact real_inner_comm y x


-- onetwotwo
-- ontwothree
-- onetwofour

theorem onetwofive [InnerProductSpace ℝ E] (x y: E) :⟪x, y⟫_ℝ = (‖x+y‖^2 - ‖x-y‖^2)/4 := by
  rw [inner_eq_sum_norm_sq_div_four]
  simp

theorem onethree (a b : ℝ) : IsCompact (Set.Icc a b) := by
  have : CompactIccSpace ℝ:= by exact ConditionallyCompleteLinearOrder.toCompactIccSpace ℝ
  exact isCompact_Icc
