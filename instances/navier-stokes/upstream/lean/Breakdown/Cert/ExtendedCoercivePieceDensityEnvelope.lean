import Breakdown.Cert.ExtendedCoerciveStatement
import Breakdown.Cert.CoercivePieceAbsorb

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.PieceDensity

theorem lower_envelope_le_ae {c c' q : Space → ℝ} {e : Space → ℝ≥0∞} (hc'm : Measurable c')
    (hq : Measurable q) (hq0 : ∀ y, 0 < q y) (hc' : ∀ y, c' y ≤ c y) (hc'0 : ∀ y, 0 ≤ c' y)
    (hee : ∀ y, e y = ENNReal.ofReal (c' y * q y))
    (hint : ∫⁻ y, ENNReal.ofReal (c y * q y) = ∫⁻ y, e y)
    (hfin : ∫⁻ y, e y ≠ ⊤) {h : Space → ℝ} (hh : Measurable h) (hhc : ∀ y, h y ≤ c y) :
    ∀ᵐ y ∂(volume : Measure Space), h y ≤ c' y := by
  set e' : Space → ℝ≥0∞ := fun y => ENNReal.ofReal (max (h y) (c' y) * q y) with he'
  have he'm : Measurable e' :=
    ENNReal.measurable_ofReal.comp ((hh.max hc'm).mul hq)
  have hle : e ≤ᵐ[volume] e' := Filter.Eventually.of_forall fun y => by
    rw [hee y]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _) (hq0 y).le)
  have hle2 : ∫⁻ y, e' y ≤ ∫⁻ y, e y := by
    rw [← hint]
    exact lintegral_mono fun y => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (max_le (hhc y) (hc' y)) (hq0 y).le)
  have hae := ae_eq_of_ae_le_of_lintegral_le hle hfin he'm.aemeasurable hle2
  filter_upwards [hae] with y hy
  rw [hee y, he'] at hy
  have hmax : max (h y) (c' y) ≥ c' y := le_max_right _ _
  have h0 : 0 ≤ c' y * q y := mul_nonneg (hc'0 y) (hq0 y).le
  have h1 : 0 ≤ max (h y) (c' y) * q y :=
    h0.trans (mul_le_mul_of_nonneg_right hmax (hq0 y).le)
  have h2 := (ENNReal.ofReal_eq_ofReal_iff h0 h1).1 hy
  have h3 : c' y = max (h y) (c' y) := mul_right_cancel₀ (hq0 y).ne' h2
  rw [h3]
  exact le_max_left _ _

theorem exists_lower_envelope {c : Space → ℝ} (h0 : ∀ y, 0 ≤ c y) {B : ℝ} (hB : ∀ y, c y ≤ B) :
    ∃ c' : Space → ℝ, Measurable c' ∧ (∀ y, 0 ≤ c' y) ∧ (∀ y, c' y ≤ c y) ∧
      ∀ g : Space → ℝ, Measurable g → ∫⁻ y, ENNReal.ofReal ((c y - c' y) * g y) = 0 := by
  set q : Space → ℝ := fun y => (1 + ‖y‖) ^ (-(4 : ℝ)) with hqdef
  have hq0 : ∀ y, 0 < q y := fun y => Real.rpow_pos_of_pos (by positivity) _
  have hqm : Measurable q := (measurable_const.add measurable_norm).pow_const _
  have hqi : Integrable q (volume : Measure Space) := by
    refine integrable_one_add_norm ?_
    rw [finrank_euclideanSpace_fin]
    norm_num
  have hB0 : 0 ≤ B := (h0 0).trans (hB 0)
  obtain ⟨e, hem, heF, hint⟩ := exists_measurable_le_lintegral_eq (volume : Measure Space)
    (fun y => ENNReal.ofReal (c y * q y))
  have hFfin : ∫⁻ y, ENNReal.ofReal (c y * q y) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun y => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (hB y) (hq0 y).le)) ?_
    exact (hqi.const_mul B).lintegral_lt_top
  have hfin : ∫⁻ y, e y ≠ ⊤ := by
    rw [← hint]
    exact hFfin.ne
  have heT : ∀ y, e y ≠ ⊤ := fun y => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (heF y)
  have heR : ∀ y, (e y).toReal ≤ c y * q y := fun y =>
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg (h0 y) (hq0 y).le) (heF y)
  set c' : Space → ℝ := fun y => (e y).toReal / q y with hc'def
  have hc'm : Measurable c' := hem.ennreal_toReal.div hqm
  have hc'0 : ∀ y, 0 ≤ c' y := fun y => div_nonneg ENNReal.toReal_nonneg (hq0 y).le
  have hc'c : ∀ y, c' y ≤ c y := fun y => by
    show (e y).toReal / q y ≤ c y
    rw [div_le_iff₀ (hq0 y)]
    exact heR y
  have hee : ∀ y, e y = ENNReal.ofReal (c' y * q y) := fun y => by
    show e y = ENNReal.ofReal ((e y).toReal / q y * q y)
    rw [div_mul_cancel₀ _ (hq0 y).ne', ENNReal.ofReal_toReal (heT y)]
  have key := fun (h : Space → ℝ) (hh : Measurable h) (hhc : ∀ y, h y ≤ c y) =>
    lower_envelope_le_ae hc'm hqm hq0 hc'c hc'0 hee hint hfin hh hhc
  refine ⟨c', hc'm, hc'0, hc'c, fun g hg => ?_⟩
  obtain ⟨k, hkm, hkF, hkint⟩ := exists_measurable_le_lintegral_eq (volume : Measure Space)
    (fun y => ENNReal.ofReal ((c y - c' y) * g y))
  rw [hkint]
  have hkT : ∀ y, k y ≠ ⊤ := fun y => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hkF y)
  set hfun : Space → ℝ := fun y => if 0 < g y then c' y + (k y).toReal / g y else c' y with hfdef
  have hfm : Measurable hfun :=
    Measurable.ite (measurableSet_lt measurable_const hg) (hc'm.add (hkm.ennreal_toReal.div hg)) hc'm
  have hfc : ∀ y, hfun y ≤ c y := fun y => by
    simp only [hfdef]
    split_ifs with hgy
    · have h1 : (k y).toReal ≤ (c y - c' y) * g y :=
        ENNReal.toReal_le_of_le_ofReal (mul_nonneg (sub_nonneg.2 (hc'c y)) hgy.le) (hkF y)
      have h2 : (k y).toReal / g y ≤ c y - c' y := by
        rw [div_le_iff₀ hgy]
        exact h1
      linarith
    · exact hc'c y
  have hae := key hfun hfm hfc
  have hk0 : k =ᵐ[volume] 0 := by
    filter_upwards [hae] with y hy
    simp only [hfdef] at hy
    show k y = 0
    split_ifs at hy with hgy
    · have h1 : (k y).toReal / g y ≤ 0 := by linarith
      have h2 : (k y).toReal ≤ 0 := by
        rwa [div_le_iff₀ hgy, zero_mul] at h1
      have h3 : (k y).toReal = 0 := le_antisymm h2 ENNReal.toReal_nonneg
      rcases (ENNReal.toReal_eq_zero_iff _).1 h3 with h4 | h4
      · exact h4
      · exact absurd h4 (hkT y)
    · replace hgy := not_lt.mp hgy
      have h1 : (c y - c' y) * g y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (hc'c y)) hgy
      have h2 := hkF y
      simp only [ENNReal.ofReal_of_nonpos h1] at h2
      exact le_antisymm h2 zero_le
  rw [lintegral_congr_ae hk0]
  simp

theorem lintegral_iter_envelope_eq_zero {c c' : Space → ℝ}
    (henv : ∀ g : Space → ℝ, Measurable g → ∫⁻ y, ENNReal.ofReal ((c y - c' y) * g y) = 0)
    {g : ℝ → Space → ℝ} (hg : AEMeasurable (fun z : ℝ × Space => g z.1 z.2) Coercive.Internal.PieceAbsorb.slabMeasure) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal ((c y - c' y) * g σ y) = 0 := by
  obtain ⟨g', hg'm, hgg'⟩ := hg
  have hae : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ᵐ y ∂(volume : Measure Space),
      g σ y = g' (σ, y) := Measure.ae_ae_of_ae_prod hgg'
  have h1 : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∫⁻ y, ENNReal.ofReal ((c y - c' y) * g σ y) = 0 := by
    filter_upwards [hae] with σ hσ
    have hc : (fun y => ENNReal.ofReal ((c y - c' y) * g σ y)) =ᵐ[volume]
        fun y => ENNReal.ofReal ((c y - c' y) * g' (σ, y)) :=
      hσ.mono fun y hy => by simp only [hy]
    rw [lintegral_congr_ae hc]
    exact henv _ (hg'm.comp measurable_prodMk_left)
  rw [lintegral_congr_ae h1]
  simp

theorem vortGradSupWith_nonneg (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (y : Space) :
    0 ≤ vortGradSupWith HW y :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem abs_alternatingSymbol_le (i j l : Fin 3) : |alternatingSymbol i j l| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> norm_num [alternatingSymbol]

theorem norm_unitVector_eq_one (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem abs_vortGrad_le (A : Space →L[ℝ] Space →L[ℝ] Space) (j m : Fin 3) :
    |vortGrad A j m| ≤ 9 * ‖A‖ := by
  unfold vortGrad
  have hterm : ∀ a b : Fin 3, |alternatingSymbol j a b * A (unitVector m) (unitVector a) b| ≤ ‖A‖ := by
    intro a b
    rw [abs_mul]
    have h1 := abs_alternatingSymbol_le j a b
    have h2 : |A (unitVector m) (unitVector a) b| ≤ ‖A‖ := by
      have h3 : ‖A (unitVector m) (unitVector a) b‖ ≤ ‖A (unitVector m) (unitVector a)‖ :=
        PiLp.norm_apply_le _ _
      have h4 := A.le_opNorm₂ (unitVector m) (unitVector a)
      rw [norm_unitVector_eq_one, norm_unitVector_eq_one, mul_one, mul_one] at h4
      rw [← Real.norm_eq_abs]
      exact h3.trans h4
    calc |alternatingSymbol j a b| * |A (unitVector m) (unitVector a) b| ≤ 1 * ‖A‖ :=
          mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = ‖A‖ := one_mul _
  calc |∑ a : Fin 3, ∑ b : Fin 3, alternatingSymbol j a b * A (unitVector m) (unitVector a) b|
      ≤ ∑ a : Fin 3, ∑ b : Fin 3, |alternatingSymbol j a b * A (unitVector m) (unitVector a) b| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _a : Fin 3, ∑ _b : Fin 3, ‖A‖ := Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
    _ = 9 * ‖A‖ := by simp; ring

theorem norm_vortGradMap_le (A : Space →L[ℝ] Space →L[ℝ] Space) : ‖vortGradMap A‖ ≤ 81 * ‖A‖ := by
  unfold vortGradMap
  have hin : ∀ m : Fin 3, ‖∑ j : Fin 3, vortGrad A j m • unitVector j‖ ≤ 27 * ‖A‖ := by
    intro m
    calc ‖∑ j : Fin 3, vortGrad A j m • unitVector j‖ ≤ ∑ j : Fin 3, ‖vortGrad A j m • unitVector j‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3, 9 * ‖A‖ := Finset.sum_le_sum fun j _ => by
          rw [norm_smul, norm_unitVector_eq_one, mul_one, Real.norm_eq_abs]
          exact abs_vortGrad_le A j m
      _ = 27 * ‖A‖ := by simp; ring
  calc ‖∑ m : Fin 3, (innerSL ℝ (unitVector m)).smulRight (∑ j : Fin 3, vortGrad A j m • unitVector j)‖
      ≤ ∑ m : Fin 3, ‖(innerSL ℝ (unitVector m)).smulRight (∑ j : Fin 3, vortGrad A j m • unitVector j)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _m : Fin 3, 27 * ‖A‖ := Finset.sum_le_sum fun m _ => by
        rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, norm_unitVector_eq_one, one_mul]
        exact hin m
    _ = 81 * ‖A‖ := by simp; ring

theorem vortGradSupWith_le {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {D : ℝ} (hW : IsWeakSecondDerivState W HW D) (y : Space) : vortGradSupWith HW y ≤ 81 * |D| := by
  unfold vortGradSupWith
  refine Real.iSup_le (fun p => ?_) (by positivity)
  refine (norm_vortGradMap_le _).trans ?_
  have h1 := (hW.decay p.1 (axialRot p.2 y)).2.2
  have ht : 1 ≤ (1 + ‖axialRot p.2 y‖) ^ 3 := one_le_pow₀ (by linarith [norm_nonneg (axialRot p.2 y)])
  have h2 : D / (1 + ‖axialRot p.2 y‖) ^ 3 ≤ |D| := by
    calc D / (1 + ‖axialRot p.2 y‖) ^ 3 ≤ |D| / (1 + ‖axialRot p.2 y‖) ^ 3 :=
          div_le_div_of_nonneg_right (le_abs_self D) (by positivity)
      _ ≤ |D| := div_le_self (abs_nonneg D) ht
  linarith

end Internal.PieceDensity

end CoerciveWeak

end Breakdown
