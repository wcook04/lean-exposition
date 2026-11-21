import Breakdown.Torus.HeatComparisonStatements
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

open MeasureTheory Set Real
open scoped ENNReal ContDiff SchwartzMap

noncomputable section

namespace Breakdown.Periodic.FreeDensity.Internal

open Breakdown.Periodic

theorem exists_rapid (φ : Space → Space) (hφ : IsTestField φ) :
    ∃ S : 𝓢(Space, Coef), ∀ ξ, freqTrVec φ ξ = S ξ := by
  have h1 : ContDiff ℝ ∞ (fun x => Freq.complexifyVec (φ x)) :=
    Freq.complexifyVec.contDiff.comp hφ.1
  have h2 : HasCompactSupport (fun x => Freq.complexifyVec (φ x)) :=
    hφ.2.1.comp_left (map_zero _)
  refine ⟨FourierTransform.fourier (h2.toSchwartzMap h1), fun ξ => ?_⟩
  rw [SchwartzMap.fourier_coe]
  rfl

theorem rapid_decay (S : 𝓢(Space, Coef)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ, (1 + ‖ξ‖) ^ 5 * ‖S ξ‖ ≤ C := by
  refine ⟨2 ^ 5 * (Finset.Iic ((5 : ℕ), (0 : ℕ))).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) S,
    by positivity, fun ξ => ?_⟩
  have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((5 : ℕ), (0 : ℕ)))
    (k := 5) (n := 0) le_rfl le_rfl S ξ
  rwa [norm_iteratedFDeriv_zero] at this

theorem rapid_slope (S : 𝓢(Space, Coef)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ ξ ξ', ‖S ξ - S ξ'‖ ≤ L * ‖ξ - ξ'‖ := by
  refine ⟨SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.fderivCLM ℝ Space Coef S), by positivity,
    fun ξ ξ' => ?_⟩
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fun x => S x) (s := Set.univ)
    (x := ξ') (y := ξ) (fun x _ => S.differentiableAt)
    (fun x _ => by
      have := SchwartzMap.norm_le_seminorm ℝ (SchwartzMap.fderivCLM ℝ Space Coef S) x
      rwa [SchwartzMap.fderivCLM_apply] at this) convex_univ (mem_univ _) (mem_univ _)

theorem freqTr_bounds (φ : Space → Space) (hφ : IsTestField φ) :
    ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧ (∀ ξ, (1 + ‖ξ‖) ^ 5 * ‖freqTrVec φ ξ‖ ≤ C) ∧
      (∀ ξ ξ', ‖freqTrVec φ ξ - freqTrVec φ ξ'‖ ≤ L * ‖ξ - ξ'‖) := by
  obtain ⟨S, hS⟩ := exists_rapid φ hφ
  obtain ⟨C, hC, hd⟩ := rapid_decay S
  obtain ⟨L, hL, hl⟩ := rapid_slope S
  exact ⟨C, L, hC, hL, fun ξ => by rw [hS]; exact hd ξ, fun ξ ξ' => by rw [hS, hS]; exact hl ξ ξ'⟩

theorem norm_le_of_pow_five (C : ℝ) (ξ : Space) (v : Coef) (h : (1 + ‖ξ‖) ^ 5 * ‖v‖ ≤ C) :
    ‖v‖ ≤ C := by
  have h1 : 1 ≤ (1 + ‖ξ‖) ^ 5 := one_le_pow₀ (by linarith [norm_nonneg ξ])
  nlinarith [norm_nonneg v]

theorem norm_expChar (y ξ : Space) : ‖expChar y ξ‖ = 1 := by
  unfold expChar
  have : 2 * π * Complex.I * ((inner ℝ ξ y : ℝ) : ℂ) = ((2 * π * inner ℝ ξ y : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem norm_expChar_sub (y ξ ξ' : Space) :
    ‖expChar y ξ - expChar y ξ'‖ ≤ 2 * π * ‖y‖ * ‖ξ - ξ'‖ := by
  have key : expChar y ξ = expChar y ξ' *
      Complex.exp (Complex.I * ((2 * π * (inner ℝ ξ y - inner ℝ ξ' y) : ℝ) : ℂ)) := by
    unfold expChar
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [key, ← mul_sub_one, norm_mul, norm_expChar, one_mul]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
  rw [← inner_sub_left, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
  have := abs_real_inner_le_norm (ξ - ξ') y
  nlinarith [pi_pos]

theorem heatFactor_pos (τ : ℝ) (ξ : Space) : 0 < Freq.heatFactor τ ξ := Real.exp_pos _

theorem heatFactor_le_one (τ : ℝ) (ξ : Space) : Freq.heatFactor τ ξ ≤ 1 := by
  unfold Freq.heatFactor
  rw [Real.exp_le_one_iff, neg_nonpos]
  have := le_max_right τ 0
  positivity

theorem abs_exp_neg_sub_le (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |Real.exp (-s) - Real.exp (-t)| ≤ |s - t| := by
  rcases le_total s t with hst | hst
  · have h1 := Real.add_one_le_exp (-(t - s))
    have h2 : Real.exp (-t) = Real.exp (-s) * Real.exp (-(t - s)) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h4 : 0 < Real.exp (-s) := Real.exp_pos _
    have h5 : Real.exp (-t) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    nlinarith
  · have h1 := Real.add_one_le_exp (-(s - t))
    have h2 : Real.exp (-s) = Real.exp (-t) * Real.exp (-(s - t)) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h4 : 0 < Real.exp (-t) := Real.exp_pos _
    have h5 : Real.exp (-s) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    nlinarith

theorem heatFactor_sub (τ ε R : ℝ) (hε : 0 < ε) (hτ : τ ≤ ε⁻¹) (ξ ξ' : Space)
    (hξ : ‖ξ‖ ≤ R) (hξ' : ‖ξ'‖ ≤ R) :
    |Freq.heatFactor τ ξ - Freq.heatFactor τ ξ'| ≤ 4 * π ^ 2 * ε⁻¹ * (2 * R) * ‖ξ - ξ'‖ := by
  unfold Freq.heatFactor
  have hm0 : 0 ≤ max τ 0 := le_max_right τ 0
  have hm1 : max τ 0 ≤ ε⁻¹ := max_le hτ (inv_nonneg.mpr hε.le)
  refine (abs_exp_neg_sub_le _ _ (by positivity) (by positivity)).trans ?_
  have hd : |‖ξ‖ - ‖ξ'‖| ≤ ‖ξ - ξ'‖ := abs_norm_sub_norm_le ξ ξ'
  have hsq : |‖ξ‖ ^ 2 - ‖ξ'‖ ^ 2| ≤ 2 * R * ‖ξ - ξ'‖ := by
    have : ‖ξ‖ ^ 2 - ‖ξ'‖ ^ 2 = (‖ξ‖ - ‖ξ'‖) * (‖ξ‖ + ‖ξ'‖) := by ring
    rw [this, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖ξ‖ + ‖ξ'‖)]
    have h0 : 0 ≤ |‖ξ‖ - ‖ξ'‖| := abs_nonneg _
    nlinarith [norm_nonneg ξ, norm_nonneg ξ']
  have : 4 * π ^ 2 * max τ 0 * ‖ξ‖ ^ 2 - 4 * π ^ 2 * max τ 0 * ‖ξ'‖ ^ 2 =
      (4 * π ^ 2 * max τ 0) * (‖ξ‖ ^ 2 - ‖ξ'‖ ^ 2) := by ring
  rw [this, abs_mul, abs_of_nonneg (by positivity)]
  have hp : 0 ≤ 4 * π ^ 2 := by positivity
  have hab : 0 ≤ |‖ξ‖ ^ 2 - ‖ξ'‖ ^ 2| := abs_nonneg _
  calc 4 * π ^ 2 * max τ 0 * |‖ξ‖ ^ 2 - ‖ξ'‖ ^ 2|
      ≤ 4 * π ^ 2 * ε⁻¹ * |‖ξ‖ ^ 2 - ‖ξ'‖ ^ 2| := by gcongr
    _ ≤ 4 * π ^ 2 * ε⁻¹ * (2 * R * ‖ξ - ξ'‖) := by gcongr
    _ = _ := by ring

theorem norm_coord_factor (j : Fin 3) (ξ : Space) :
    ‖(2 * π * Complex.I * ((ξ j : ℝ) : ℂ))‖ = 2 * π * |ξ j| := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  simp [abs_of_pos pi_pos]

theorem abs_coord_le (j : Fin 3) (ξ : Space) : |ξ j| ≤ ‖ξ‖ := by
  have := PiLp.norm_apply_le ξ j
  rwa [Real.norm_eq_abs] at this

theorem le_mul_rpow_of (K a : ℝ) (ξ : Space) (h : (1 + ‖ξ‖) ^ 4 * a ≤ K) :
    a ≤ K * (1 + ‖ξ‖) ^ (-4 : ℝ) := by
  have hp : 0 < 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
  rw [Real.rpow_neg hp.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    le_mul_inv_iff₀ (by positivity)]
  linarith

theorem norm_freeDensity_le (τ : ℝ) (φ : Space → Space) (y ξ : Space) :
    ‖freeDensity τ φ y ξ‖ ≤ ‖freqTrVec φ ξ‖ := by
  unfold freeDensity
  rw [norm_smul, norm_smul, norm_expChar, one_mul, Real.norm_eq_abs,
    abs_of_pos (heatFactor_pos τ ξ)]
  have := heatFactor_le_one τ ξ
  nlinarith [norm_nonneg (freqTrVec φ ξ)]

theorem norm_freeGradDensity_le (j : Fin 3) (τ : ℝ) (φ : Space → Space) (y ξ : Space) :
    ‖freeGradDensity j τ φ y ξ‖ ≤ 2 * π * ‖ξ‖ * ‖freqTrVec φ ξ‖ := by
  unfold freeGradDensity
  rw [norm_smul, norm_coord_factor]
  have h1 := norm_freeDensity_le τ φ y ξ
  have h2 := abs_coord_le j ξ
  have h3 : 0 ≤ 2 * π := by positivity
  calc 2 * π * |ξ j| * ‖freeDensity τ φ y ξ‖ ≤ 2 * π * ‖ξ‖ * ‖freqTrVec φ ξ‖ := by gcongr

end Breakdown.Periodic.FreeDensity.Internal

namespace Breakdown.Periodic

open FreeDensity.Internal

theorem freeDensityBounds : FreeDensityBounds := by
  intro φ hφ b ε hε
  obtain ⟨C, L, hC, hL, hd, hl⟩ := freqTr_bounds φ hφ
  refine ⟨C + 2 * π * C, fun y hy τ hτ ξ => ⟨?_, fun j => ?_⟩⟩
  · refine le_mul_rpow_of _ _ ξ ?_
    have h1 := norm_freeDensity_le τ φ y ξ
    have h2 := hd ξ
    have hp : 1 ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
    have h3 : (1 + ‖ξ‖) ^ 4 ≤ (1 + ‖ξ‖) ^ 5 := pow_le_pow_right₀ hp (by norm_num)
    have h4 : 0 ≤ (1 + ‖ξ‖) ^ 4 := by positivity
    have h5 : 0 ≤ 2 * π * C := by positivity
    calc (1 + ‖ξ‖) ^ 4 * ‖freeDensity τ φ y ξ‖ ≤ (1 + ‖ξ‖) ^ 4 * ‖freqTrVec φ ξ‖ := by gcongr
      _ ≤ (1 + ‖ξ‖) ^ 5 * ‖freqTrVec φ ξ‖ := by gcongr
      _ ≤ C + 2 * π * C := by linarith
  · refine le_mul_rpow_of _ _ ξ ?_
    have h1 := norm_freeGradDensity_le j τ φ y ξ
    have h2 := hd ξ
    have h4 : 0 ≤ (1 + ‖ξ‖) ^ 4 := by positivity
    have h6 : ‖ξ‖ ≤ 1 + ‖ξ‖ := by linarith
    have hn := norm_nonneg (freqTrVec φ ξ)
    calc (1 + ‖ξ‖) ^ 4 * ‖freeGradDensity j τ φ y ξ‖
        ≤ (1 + ‖ξ‖) ^ 4 * (2 * π * ‖ξ‖ * ‖freqTrVec φ ξ‖) := by gcongr
      _ ≤ (1 + ‖ξ‖) ^ 4 * (2 * π * (1 + ‖ξ‖) * ‖freqTrVec φ ξ‖) := by gcongr
      _ = 2 * π * ((1 + ‖ξ‖) ^ 5 * ‖freqTrVec φ ξ‖) := by ring
      _ ≤ 2 * π * C := by gcongr
      _ ≤ C + 2 * π * C := by linarith

end Breakdown.Periodic

namespace Breakdown.Periodic.FreeDensity.Internal

open Breakdown.Periodic

theorem norm_heat_smul_le (τ : ℝ) (ξ : Space) (v : Coef) : ‖Freq.heatFactor τ ξ • v‖ ≤ ‖v‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (heatFactor_pos τ ξ)]
  have := heatFactor_le_one τ ξ
  nlinarith [norm_nonneg v]

theorem freeDensity_sub (φ : Space → Space) (C LF B ε R τ : ℝ) (hε : 0 < ε) (hτ : τ ≤ ε⁻¹)
    (hC : ∀ ξ, ‖freqTrVec φ ξ‖ ≤ C) (hl : ∀ ξ ξ', ‖freqTrVec φ ξ - freqTrVec φ ξ'‖ ≤ LF * ‖ξ - ξ'‖)
    (y ξ ξ' : Space) (hy : ‖y‖ ≤ B) (hξ : ‖ξ‖ ≤ R) (hξ' : ‖ξ'‖ ≤ R) :
    ‖freeDensity τ φ y ξ - freeDensity τ φ y ξ'‖ ≤
      (2 * π * B * C + 4 * π ^ 2 * ε⁻¹ * (2 * R) * C + LF) * ‖ξ - ξ'‖ := by
  unfold freeDensity
  set e := expChar y ξ
  set e' := expChar y ξ'
  set h := Freq.heatFactor τ ξ
  set h' := Freq.heatFactor τ ξ'
  set F := freqTrVec φ ξ
  set F' := freqTrVec φ ξ'
  have hid : e • (h • F) - e' • (h' • F') =
      (e - e') • (h • F) + e' • ((h - h') • F) + e' • (h' • (F - F')) := by
    simp only [sub_smul, smul_sub]; abel
  rw [hid]
  have hd := norm_nonneg (ξ - ξ')
  have t1 : ‖(e - e') • (h • F)‖ ≤ 2 * π * B * C * ‖ξ - ξ'‖ := by
    rw [norm_smul]
    have a1 := norm_expChar_sub y ξ ξ'
    have a2 : ‖h • F‖ ≤ C := (norm_heat_smul_le τ ξ F).trans (hC ξ)
    have a3 := norm_nonneg (h • F)
    have a4 : 0 ≤ 2 * π := by positivity
    calc ‖e - e'‖ * ‖h • F‖ ≤ (2 * π * ‖y‖ * ‖ξ - ξ'‖) * ‖h • F‖ := by gcongr
      _ ≤ (2 * π * B * ‖ξ - ξ'‖) * C := by
        have : 0 ≤ 2 * π * ‖y‖ * ‖ξ - ξ'‖ := by positivity
        have hB : 0 ≤ B := (norm_nonneg y).trans hy
        gcongr
      _ = _ := by ring
  have t2 : ‖e' • ((h - h') • F)‖ ≤ 4 * π ^ 2 * ε⁻¹ * (2 * R) * C * ‖ξ - ξ'‖ := by
    rw [norm_smul, norm_expChar, one_mul, norm_smul, Real.norm_eq_abs]
    have a1 := heatFactor_sub τ ε R hε hτ ξ ξ' hξ hξ'
    have a2 := hC ξ
    have hR : 0 ≤ R := (norm_nonneg ξ).trans hξ
    have a3 : 0 ≤ 4 * π ^ 2 * ε⁻¹ * (2 * R) * ‖ξ - ξ'‖ := by positivity
    calc |h - h'| * ‖F‖ ≤ (4 * π ^ 2 * ε⁻¹ * (2 * R) * ‖ξ - ξ'‖) * C := by
          gcongr
      _ = _ := by ring
  have t3 : ‖e' • (h' • (F - F'))‖ ≤ LF * ‖ξ - ξ'‖ := by
    rw [norm_smul, norm_expChar, one_mul]
    exact (norm_heat_smul_le τ ξ' _).trans (hl ξ ξ')
  calc ‖(e - e') • (h • F) + e' • ((h - h') • F) + e' • (h' • (F - F'))‖
      ≤ ‖(e - e') • (h • F)‖ + ‖e' • ((h - h') • F)‖ + ‖e' • (h' • (F - F'))‖ :=
        norm_add₃_le
    _ ≤ _ := by linarith

theorem freeGradDensity_sub (j : Fin 3) (φ : Space → Space) (C LD R τ : ℝ)
    (y ξ ξ' : Space) (hC : ‖freeDensity τ φ y ξ‖ ≤ C)
    (hD : ‖freeDensity τ φ y ξ - freeDensity τ φ y ξ'‖ ≤ LD * ‖ξ - ξ'‖) (hξ' : ‖ξ'‖ ≤ R) :
    ‖freeGradDensity j τ φ y ξ - freeGradDensity j τ φ y ξ'‖ ≤
      (2 * π * C + 2 * π * R * LD) * ‖ξ - ξ'‖ := by
  unfold freeGradDensity
  set c := (2 * π * Complex.I * ((ξ j : ℝ) : ℂ))
  set c' := (2 * π * Complex.I * ((ξ' j : ℝ) : ℂ))
  set D := freeDensity τ φ y ξ
  set D' := freeDensity τ φ y ξ'
  have hid : c • D - c' • D' = (c - c') • D + c' • (D - D') := by
    simp only [sub_smul, smul_sub]; abel
  rw [hid]
  have hcc : c - c' = 2 * π * Complex.I * (((ξ - ξ') j : ℝ) : ℂ) := by
    simp only [c, c', PiLp.sub_apply, Complex.ofReal_sub]; ring
  have hd := norm_nonneg (ξ - ξ')
  have hpi : 0 ≤ 2 * π := by positivity
  have t1 : ‖(c - c') • D‖ ≤ 2 * π * C * ‖ξ - ξ'‖ := by
    rw [norm_smul, hcc, norm_coord_factor]
    have a1 := abs_coord_le j (ξ - ξ')
    calc 2 * π * |(ξ - ξ') j| * ‖D‖ ≤ 2 * π * ‖ξ - ξ'‖ * C := by gcongr
      _ = _ := by ring
  have t2 : ‖c' • (D - D')‖ ≤ 2 * π * R * LD * ‖ξ - ξ'‖ := by
    rw [norm_smul, norm_coord_factor]
    have a1 := (abs_coord_le j ξ').trans hξ'
    have a2 : 0 ≤ 2 * π * |ξ' j| := by positivity
    have hR : 0 ≤ R := (abs_nonneg _).trans a1
    calc 2 * π * |ξ' j| * ‖D - D'‖ ≤ 2 * π * R * (LD * ‖ξ - ξ'‖) := by gcongr
      _ = _ := by ring
  calc ‖(c - c') • D + c' • (D - D')‖ ≤ ‖(c - c') • D‖ + ‖c' • (D - D')‖ := norm_add_le _ _
    _ ≤ _ := by linarith

end Breakdown.Periodic.FreeDensity.Internal

namespace Breakdown.Periodic

open FreeDensity.Internal

theorem freeDensitySlope : FreeDensitySlope := by
  intro φ hφ b ε r R hε hr
  obtain ⟨C, LF, hC, hLF, hd, hl⟩ := freqTr_bounds φ hφ
  have hC' : ∀ ξ, ‖freqTrVec φ ξ‖ ≤ C := fun ξ => norm_le_of_pow_five C ξ _ (hd ξ)
  set LD := 2 * π * |b| * C + 4 * π ^ 2 * ε⁻¹ * (2 * |R|) * C + LF
  have hLD : 0 ≤ LD := by positivity
  refine ⟨LD + (2 * π * C + 2 * π * |R| * LD), fun y hy τ hτ ξ ξ' _ hξ _ hξ' => ?_⟩
  have hy' : ‖y‖ ≤ |b| := hy.trans (le_abs_self b)
  have hξR : ‖ξ‖ ≤ |R| := hξ.trans (le_abs_self R)
  have hξR' : ‖ξ'‖ ≤ |R| := hξ'.trans (le_abs_self R)
  have hD := freeDensity_sub φ C LF |b| ε |R| τ hε hτ.2 hC' hl y ξ ξ' hy' hξR hξR'
  have hdn := norm_nonneg (ξ - ξ')
  have hG : 0 ≤ (2 * π * C + 2 * π * |R| * LD) := by positivity
  refine ⟨?_, fun j => ?_⟩
  · nlinarith
  · have := freeGradDensity_sub j φ C LD |R| τ y ξ ξ'
      ((norm_freeDensity_le τ φ y ξ).trans (hC' ξ)) hD hξR'
    nlinarith

end Breakdown.Periodic
