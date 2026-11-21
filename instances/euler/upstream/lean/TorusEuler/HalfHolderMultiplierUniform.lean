import TorusEuler.HalfHolderFourierMultiplier

/-! Cutoff-dependent multiplier estimates uniform in the Banach value spaces. -/

open ContinuousLinearMap MeasureTheory Set UnitAddTorus
open scoped ContDiff FourierTransform RealInnerProductSpace SchwartzMap

universe u v

namespace TorusEuler

noncomputable section

local instance uniformMultiplierCircleMeasure : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance uniformMultiplierCircleHaar :
    (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance uniformMultiplierCircleProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The localization mass constant depends on the cutoff alone. -/
theorem exists_annularLocalize_mass_universal_le {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) (hout : ∀ ξ, 2 ≤ ‖ξ‖ → ψ ξ = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
        [NormedAddCommGroup F] [NormedSpace ℂ F],
      ∀ {A : Vec3 → E →L[ℂ] F}, ContDiffOn ℝ ∞ A ({0}ᶜ : Set Vec3) →
        ∀ {M : ℝ}, 0 ≤ M →
          (∀ n ≤ 5, ∀ ξ : Vec3, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 2 →
            ‖iteratedFDeriv ℝ n A ξ‖ ≤ M) →
          multiplierDerivativeMass (annularLocalize ψ A) ≤ C * M := by
  let χ := fun ξ : Vec3 => ψ ξ - ψ ((2 : ℝ) • ξ)
  have hχ : ContDiff ℝ ∞ χ := hψ.sub (hψ.comp (contDiff_id.const_smul (2 : ℝ)))
  let ball := Metric.closedBall (0 : Vec3) 2
  have hχjet (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ ∈ ball, ‖iteratedFDeriv ℝ n χ ξ‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Vec3) 2).bddAbove_image
      (hχ.continuous_iteratedFDeriv (m := n) (by simp)).norm.continuousOn
    exact ⟨max 0 C, le_max_left _ _, fun ξ hξ =>
      (hC ⟨ξ, hξ, rfl⟩).trans (le_max_right _ _)⟩
  choose cutoffJet hcutoffJet hχbound using hχjet
  let K := ∑ n ∈ Finset.range 6, cutoffJet n
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ => hcutoffJet i
  have hKbound (n : ℕ) (hn : n ≤ 5) (ξ : Vec3) (hξ : ξ ∈ ball) :
      ‖iteratedFDeriv ℝ n χ ξ‖ ≤ K :=
    (hχbound n ξ hξ).trans (Finset.single_le_sum (fun i _ => hcutoffJet i)
      (Finset.mem_range.mpr (by omega)))
  let C : ℝ := 12 * max 1 2 * (2 ^ (5 : ℕ) * K) * volume.real ball
  refine ⟨C, by unfold C; positivity, ?_⟩
  intro E F iE iEc iF iFc A hA M hM hjet
  let σ := annularLocalize ψ A
  let annulus : Set Vec3 := (fun ξ : Vec3 => ‖ξ‖) ⁻¹' Icc (1 / 2 : ℝ) 2
  have hsupp : tsupport σ ⊆ annulus := by
    apply closure_minimal _ (isClosed_Icc.preimage continuous_norm)
    intro ξ hξ
    refine ⟨le_of_not_gt ?_, le_of_not_gt ?_⟩
    · intro h
      exact hξ (annularLocalize_zero_of_small hunit A ξ h.le)
    · intro h
      exact hξ (annularLocalize_zero_of_large hout A ξ h.le)
  have hball : tsupport σ ⊆ ball := fun ξ hξ => by
    simpa only [ball, Metric.mem_closedBall, dist_zero_right] using (hsupp hξ).2
  have hderiv (n : ℕ) (hn : n ≤ 5) (ξ : Vec3) :
      ‖iteratedFDeriv ℝ n σ ξ‖ ≤ (2 ^ (5 : ℕ) * K) * M := by
    by_cases hξ : ξ ∈ annulus
    · have hmin : (1 / 2 : ℝ) ≤ ‖ξ‖ := hξ.1
      have hmax : ‖ξ‖ ≤ 2 := hξ.2
      have hξb : ξ ∈ ball := by simpa only [ball, Metric.mem_closedBall, dist_zero_right]
      let s : Set Vec3 := {0}ᶜ
      have hs : IsOpen s := isOpen_compl_singleton
      have hξs : ξ ∈ s := by
        change ξ ∉ ({0} : Set Vec3)
        simp only [mem_singleton_iff]
        exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le (by norm_num) hmin))
      have hAs : ContDiffOn ℝ ∞ A s := hA
      have h := norm_iteratedFDerivWithin_smul_le hχ.contDiffOn hAs hs.uniqueDiffOn hξs
        (n := n) (by simp)
      rw [iteratedFDerivWithin_of_isOpen n hs hξs] at h
      have hχwithin (i : ℕ) : iteratedFDerivWithin ℝ i χ s ξ = iteratedFDeriv ℝ i χ ξ :=
        iteratedFDerivWithin_of_isOpen i hs hξs
      have hAwithin (i : ℕ) : iteratedFDerivWithin ℝ i A s ξ = iteratedFDeriv ℝ i A ξ :=
        iteratedFDerivWithin_of_isOpen i hs hξs
      simp only [hχwithin, hAwithin] at h
      refine h.trans ?_
      calc
        _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * K * M := by
          apply Finset.sum_le_sum
          intro i hi
          have hin := Finset.mem_range.mp hi
          gcongr
          · exact hKbound i (by omega) ξ hξb
          · exact hjet (n - i) ((Nat.sub_le _ _).trans hn) ξ hmin hmax
        _ = ((2 : ℝ) ^ n * K) * M := by
          have hchoose : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
            exact_mod_cast Nat.sum_range_choose n
          rw [← Finset.sum_mul, ← Finset.sum_mul, hchoose]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hK) hM
    · rw [Function.notMem_support.mp (fun h => hξ (hsupp (support_iteratedFDeriv_subset n h))),
        norm_zero]
      positivity
  refine (multiplierDerivativeMass_le_of_support hball hderiv).trans_eq ?_
  unfold C
  ring

/-- The homogeneous multiplier bound uses a constant independent of its value spaces. -/
theorem exists_norm_universal_homogeneousHalfHolderMultiplier_le_mass
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1)
    (hout : ∀ ξ, 2 ≤ ‖ξ‖ → ψ ξ = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
        [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [CompleteSpace E],
      ∀ {A : Vec3 → E →L[ℂ] F} (hA : ContDiffOn ℝ ∞ A ({0}ᶜ : Set Vec3)),
        ‖homogeneousHalfHolderMultiplier hψ hunit hout hA‖ ≤
          C * multiplierDerivativeMass (annularLocalize ψ A) + ‖A 0‖ := by
  let B := ∫ y, ‖iteratedFDeriv ℝ 1
    (cutoffSchwartzKernel (fun ξ h => hout ξ h.le) hψ : Vec3 → ℂ) y‖
  let J := ∫ y : Vec3, (1 + ‖y‖) ^ (-(4 : ℝ))
  let C₀ : ℝ := 32 * ((1 + 2 * Real.pi) * (4 : ℝ) ^ 5)
  let C : ℝ := 14 * max 1 (8 * B) * C₀ * J
  have hJ : 0 ≤ J := integral_nonneg fun _ => by positivity
  have hmax : 0 ≤ max 1 (8 * B) := zero_le_one.trans (le_max_left _ _)
  refine ⟨C, by unfold C C₀; positivity, ?_⟩
  intro E F iE iEc iF iFc iCF iCE A hA
  apply (norm_homogeneousHalfHolderMultiplier_le hψ hunit hout hA).trans
  apply add_le_add_left
  let σ := annularLocalize ψ A
  let hc := annularLocalize_compact hout A
  let hs := annularLocalize_smooth hψ hunit hA
  have hmoment := compactMultiplierKernel_halfMoment_le hc hs
  change 14 * (max 1 (8 * B) * ∫ y, ‖compactMultiplierKernel hc hs y‖ * Real.sqrt ‖y‖) ≤
    C * multiplierDerivativeMass σ
  calc
    _ ≤ 14 * (max 1 (8 * B) * ((32 * ((1 + 2 * Real.pi) * (4 : ℝ) ^ 5 *
        multiplierDerivativeMass σ)) * J)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmoment hmax) (by norm_num)
    _ = _ := by dsimp only [C, C₀]; ring

end

end TorusEuler
