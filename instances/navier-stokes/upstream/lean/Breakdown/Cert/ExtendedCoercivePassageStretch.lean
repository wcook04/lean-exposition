import Breakdown.Cert.CoercivePassageCommon
import Breakdown.Cert.ExtendedCoerciveStatement
import Breakdown.Cert.CoercivePieceDensityPassageSubsequenceModes
import Breakdown.Cert.CoercivePieceAbsorbMeasure

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.PassageStretch

open Coercive Coercive.Internal Coercive.Internal.PassageCommon

variable {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}

theorem norm_fderiv_le_abs (hW : IsWeakSecondDerivState W HW D) (σ : ℝ) (y : Space) :
    ‖fderiv ℝ (W σ) y‖ ≤ |D| := by
  have h1 := (hW.decay σ y).2.1
  have hr : (1 : ℝ) ≤ (1 + ‖y‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg y])
  refine h1.trans ?_
  rcases le_or_gt 0 D with hD0 | hD0
  · exact (div_le_self hD0 hr).trans (le_abs_self D)
  · exact (div_neg_of_neg_of_pos hD0 (by positivity)).le.trans (abs_nonneg D)

theorem norm_secondDeriv_mul_le_abs (hW : IsWeakSecondDerivState W HW D) (σ : ℝ) (y : Space) :
    ‖HW σ y‖ * (1 + ‖y‖) ≤ |D| := by
  have h3 := (hW.decay σ y).2.2
  have hr : (1 : ℝ) ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
  have hr0 : (0 : ℝ) < 1 + ‖y‖ := lt_of_lt_of_le one_pos hr
  have hD : 0 ≤ D := by
    by_contra h
    have := div_neg_of_neg_of_pos (not_le.mp h) (pow_pos hr0 3)
    linarith [norm_nonneg (HW σ y)]
  calc ‖HW σ y‖ * (1 + ‖y‖) ≤ D / (1 + ‖y‖) ^ 3 * (1 + ‖y‖) := mul_le_mul_of_nonneg_right h3 hr0.le
    _ = D / (1 + ‖y‖) ^ 2 := by
      field_simp
    _ ≤ D := div_le_self hD (one_le_pow₀ hr)
    _ ≤ |D| := le_abs_self D

theorem abs_stretchFormWith_le {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hW : IsWeakSecondDerivState W HW D) (σ : ℝ) (y : Space) :
    |stretchFormWith W HW v G σ y| ≤ 729 * |D| * (6 * matSq (G σ y) + ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) := by
  have e : stretchFormWith W HW v G σ y = stretchPair (G σ y) (G σ y) (fderiv ℝ (W σ) y)
      (HW σ y) (v σ y) (v σ y) := rfl
  rw [e]
  have hb := abs_stretchPair_le (G σ y) (G σ y) (fderiv ℝ (W σ) y) (HW σ y) (v σ y) (v σ y)
  have h1 := norm_fderiv_le_abs hW σ y
  have h2 := norm_secondDeriv_mul_le_abs hW σ y
  have hf := norm_sq_le_matSq (G σ y)
  set gg := ‖G σ y‖
  set dd := ‖fderiv ℝ (W σ) y‖
  set hh := ‖HW σ y‖
  set vv := ‖v σ y‖
  set r := 1 + ‖y‖ with hr
  have hr0 : 0 < r := by rw [hr]; linarith [norm_nonneg y]
  have g0 : 0 ≤ gg := norm_nonneg _
  have d0 : 0 ≤ dd := norm_nonneg _
  have h0 : 0 ≤ hh := norm_nonneg _
  have vfix : 0 ≤ vv := norm_nonneg _
  set q := vv / r with hq
  have q0 : 0 ≤ q := div_nonneg vfix hr0.le
  have hvq : vv = q * r := by rw [hq]; field_simp
  have hhv : hh * vv ≤ |D| * q := by
    rw [hvq, show hh * (q * r) = (hh * r) * q by ring]
    exact mul_le_mul_of_nonneg_right h2 q0
  have t1 : dd * gg * gg ≤ |D| * (gg * gg) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have t2 : hh * vv * gg ≤ |D| * q * gg := mul_le_mul_of_nonneg_right hhv g0
  have t3 : hh * gg * vv ≤ |D| * q * gg := by
    rw [show hh * gg * vv = hh * vv * gg by ring]; exact t2
  have hq2 : q ^ 2 = vv ^ 2 / r ^ 2 := by rw [hq, div_pow]
  have hD0 := abs_nonneg D
  have key : 2 * q * gg ≤ gg ^ 2 + q ^ 2 := by nlinarith [sq_nonneg (gg - q)]
  have k2 := mul_le_mul_of_nonneg_left key hD0
  refine hb.trans ?_
  have s1 : 729 * dd * gg * gg + 729 * hh * vv * gg + 729 * hh * gg * vv
      ≤ 729 * |D| * (2 * gg ^ 2 + q ^ 2) := by
    nlinarith [t1, t2, t3, k2]
  refine s1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [← hq2]
  linarith

theorem stretchFormWith_finite {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (hW : IsWeakSecondDerivState W HW D)
    (hvw : periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) < ⊤) :
    periodLIntegral (fun σ y => |stretchFormWith W HW v G σ y|) < ⊤ := by
  refine lt_of_le_of_lt (PassageLimit.periodLIntegral_le_mul (by positivity)
    fun σ y => abs_stretchFormWith_le hW σ y) ?_
  have hm1 : AEMeasurable (fun z : ℝ × Space => 6 * matSq (G z.1 z.2)) volume :=
    ((continuous_matSq.comp_aestronglyMeasurable hv.measurable_gradient).aemeasurable).const_mul 6
  have hr : Continuous (fun z : ℝ × Space => (1 + ‖z.2‖) ^ 2) := by fun_prop
  have hm2 : AEMeasurable (fun z : ℝ × Space => ‖v z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 2) volume :=
    (hv.measurable_velocity.norm.aemeasurable.pow_const 2).div hr.aemeasurable
  rw [PassageLimit.periodLIntegral_add hm1 hm2 (fun _ _ => mul_nonneg (by norm_num) (matSq_nonneg _))
    (fun _ _ => by positivity)]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨?_, hvw⟩)
  exact lt_of_le_of_lt (PassageLimit.periodLIntegral_le_mul (C := 6) (by norm_num)
    (g := fun σ y => matSq (G σ y)) fun σ y => le_refl _)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hv.gradient_finite)

theorem stretchFormWith_sub_eq (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (v v' : ℝ → Space → Space) (G G' : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (y : Space) :
    stretchFormWith W HW v G σ y - stretchFormWith W HW v' G' σ y =
      stretchPair (G σ y - G' σ y) (G σ y) (fderiv ℝ (W σ) y) (HW σ y)
          (v σ y - v' σ y) (v σ y)
        + stretchPair (G' σ y) (G σ y - G' σ y) (fderiv ℝ (W σ) y) (HW σ y)
          (v' σ y) (v σ y - v' σ y) := by
  unfold stretchFormWith stretchPair
  simp only [curlVec_sub, ContinuousLinearMap.sub_apply, PiLp.sub_apply, Fin.sum_univ_three]
  ring

theorem abs_stretchFormWith_sub_le {W u v : ℝ → Space → Space} {Gu G : ℝ → Space → (Space →L[ℝ] Space)} {D : ℝ}
    (hW : IsWeakSecondDerivState W HW D) (σ : ℝ) (y : Space) :
    |stretchFormWith W HW u Gu σ y - stretchFormWith W HW v G σ y| ≤
      729 * |D| * ((‖Gu σ y - G σ y‖ + ‖u σ y - v σ y‖ / (1 + ‖y‖)) ^ 2
        + (‖Gu σ y - G σ y‖ + ‖u σ y - v σ y‖ / (1 + ‖y‖)) * (2 * ‖G σ y‖ + 2 * (‖v σ y‖ / (1 + ‖y‖)))) := by
  rw [stretchFormWith_sub_eq]
  have hb1 := abs_stretchPair_le (Gu σ y - G σ y) (Gu σ y) (fderiv ℝ (W σ) y) (HW σ y)
    (u σ y - v σ y) (u σ y)
  have hb2 := abs_stretchPair_le (G σ y) (Gu σ y - G σ y) (fderiv ℝ (W σ) y) (HW σ y)
    (v σ y) (u σ y - v σ y)
  have h1 := norm_fderiv_le_abs hW σ y
  have h2 := norm_secondDeriv_mul_le_abs hW σ y
  have hgn : ‖Gu σ y‖ ≤ ‖Gu σ y - G σ y‖ + ‖G σ y‖ := by
    have := norm_add_le (Gu σ y - G σ y) (G σ y); simpa using this
  have hun : ‖u σ y‖ ≤ ‖u σ y - v σ y‖ + ‖v σ y‖ := by
    have := norm_add_le (u σ y - v σ y) (v σ y); simpa using this
  have hab := abs_add_le (stretchPair (Gu σ y - G σ y) (Gu σ y) (fderiv ℝ (W σ) y)
      (HW σ y) (u σ y - v σ y) (u σ y))
    (stretchPair (G σ y) (Gu σ y - G σ y) (fderiv ℝ (W σ) y) (HW σ y)
      (v σ y) (u σ y - v σ y))
  set e := ‖Gu σ y - G σ y‖
  set gn := ‖Gu σ y‖
  set g := ‖G σ y‖
  set dd := ‖fderiv ℝ (W σ) y‖
  set hh := ‖HW σ y‖
  set dv := ‖u σ y - v σ y‖
  set nu := ‖u σ y‖
  set nv := ‖v σ y‖
  set r := 1 + ‖y‖ with hr
  have hr0 : 0 < r := by rw [hr]; linarith [norm_nonneg y]
  have e0 : 0 ≤ e := norm_nonneg _
  have g0 : 0 ≤ g := norm_nonneg _
  have gn0 : 0 ≤ gn := norm_nonneg _
  have d0 : 0 ≤ dd := norm_nonneg _
  have h0 : 0 ≤ hh := norm_nonneg _
  have dv0 : 0 ≤ dv := norm_nonneg _
  have nu0 : 0 ≤ nu := norm_nonneg _
  have nv0 : 0 ≤ nv := norm_nonneg _
  have hD0 := abs_nonneg D
  set f := dv / r with hf
  set q := nv / r with hq
  have f0 : 0 ≤ f := div_nonneg dv0 hr0.le
  have q0 : 0 ≤ q := div_nonneg nv0 hr0.le
  have hdv : hh * dv ≤ |D| * f := by
    rw [show hh * dv = (hh * r) * f by rw [hf]; field_simp]
    exact mul_le_mul_of_nonneg_right h2 f0
  have hnv : hh * nv ≤ |D| * q := by
    rw [show hh * nv = (hh * r) * q by rw [hq]; field_simp]
    exact mul_le_mul_of_nonneg_right h2 q0
  have hnu : hh * nu ≤ |D| * (f + q) := by
    have := mul_le_mul_of_nonneg_left hun h0
    linarith
  have a1 : dd * e * gn ≤ |D| * (e * (e + g)) := by
    have := mul_le_mul h1 (mul_le_mul_of_nonneg_left hgn e0) (by positivity) hD0
    nlinarith
  have a2 : hh * dv * gn ≤ |D| * f * (e + g) := mul_le_mul hdv hgn gn0 (by positivity)
  have a3 : hh * e * nu ≤ |D| * (f + q) * e := by
    rw [show hh * e * nu = hh * nu * e by ring]; exact mul_le_mul_of_nonneg_right hnu e0
  have b1 : dd * g * e ≤ |D| * g * e := by
    rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have b2 : hh * nv * e ≤ |D| * q * e := mul_le_mul_of_nonneg_right hnv e0
  have b3 : hh * g * dv ≤ |D| * f * g := by
    rw [show hh * g * dv = hh * dv * g by ring]; exact mul_le_mul_of_nonneg_right hdv g0
  have hsum : e * (e + g) + f * (e + g) + (f + q) * e + g * e + q * e + f * g
      ≤ (e + f) ^ 2 + (e + f) * (2 * g + 2 * q) := by nlinarith [mul_nonneg f0 q0, sq_nonneg f]
  have hfin := mul_le_mul_of_nonneg_left hsum hD0
  refine hab.trans ?_
  nlinarith [hb1, hb2, a1, a2, a3, b1, b2, b3, hfin]

theorem stretchFormWith_tendsto (hSP : SmoothPerturbationIsPerturbationHolds) {Γ : Set Symmetry} {P : ℝ}
    {W v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} {u : ℕ → ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u)
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ} (hW : IsWeakSecondDerivState W HW D) :
    Tendsto (fun n => periodLIntegral (fun σ y =>
      |stretchFormWith W HW (u n) (gradField (u n)) σ y - stretchFormWith W HW v G σ y|)) atTop (𝓝 0) := by
  obtain ⟨hs, hA, -, hF, -⟩ := hu
  have hP : ∀ n, IsPerturbation ∅ P (u n) (gradField (u n)) (secondDerivField (u n)) (transportPart P (u n)) :=
    fun n => hSP P (u n) (hs n)
  have hc0 : (0 : ℝ) ≤ 4374 * |D| := by positivity
  have hpt : ∀ δ : ℝ, 0 < δ → ∀ n σ y,
      |stretchFormWith W HW (u n) (gradField (u n)) σ y - stretchFormWith W HW v G σ y|
        ≤ 4374 * |D| * (1 + δ⁻¹) * (matSq (gradField (u n) σ y - G σ y)
            + ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)
          + 4374 * |D| * δ * (matSq (G σ y) + ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) := by
    intro δ hδ n σ y
    have hb := abs_stretchFormWith_sub_le (HW := HW) (u := u n) (Gu := gradField (u n)) (v := v) (G := G)
      hW σ y
    have ha := norm_sq_le_matSq (gradField (u n) σ y - G σ y)
    have hg := norm_sq_le_matSq (G σ y)
    have hr0 : (0 : ℝ) < 1 + ‖y‖ := by positivity
    have hf2 : ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 = (‖u n σ y - v σ y‖ / (1 + ‖y‖)) ^ 2 := by
      rw [div_pow]
    have hq2 : ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 = (‖v σ y‖ / (1 + ‖y‖)) ^ 2 := by
      rw [div_pow]
    rw [hf2, hq2]
    have f0 : 0 ≤ ‖u n σ y - v σ y‖ / (1 + ‖y‖) := div_nonneg (norm_nonneg _) hr0.le
    have q0 : 0 ≤ ‖v σ y‖ / (1 + ‖y‖) := div_nonneg (norm_nonneg _) hr0.le
    set e := ‖gradField (u n) σ y - G σ y‖
    set g := ‖G σ y‖
    set f := ‖u n σ y - v σ y‖ / (1 + ‖y‖)
    set q := ‖v σ y‖ / (1 + ‖y‖)
    set a := matSq (gradField (u n) σ y - G σ y)
    set b := matSq (G σ y)
    have e0 : 0 ≤ e := norm_nonneg _
    have g0 : 0 ≤ g := norm_nonneg _
    have t0 : 0 ≤ δ⁻¹ := inv_nonneg.2 hδ.le
    have hδt : δ * δ⁻¹ = 1 := mul_inv_cancel₀ hδ.ne'
    have heq : δ⁻¹ * (e + f) ^ 2 + δ * (2 * g + 2 * q) ^ 2 / 4 - (e + f) * (2 * g + 2 * q)
        = δ * (δ⁻¹ * (e + f) - (2 * g + 2 * q) / 2) ^ 2 := by
      linear_combination ((e + f) * (2 * g + 2 * q) - δ⁻¹ * (e + f) ^ 2) * hδt
    have hsq := mul_nonneg hδ.le (sq_nonneg (δ⁻¹ * (e + f) - (2 * g + 2 * q) / 2))
    have amgm : (e + f) * (2 * g + 2 * q) ≤ δ⁻¹ * (e + f) ^ 2 + δ * (2 * g + 2 * q) ^ 2 / 4 := by
      linarith
    have hx2 : (e + f) ^ 2 ≤ 6 * (a + f ^ 2) := by
      nlinarith [sq_nonneg (e - f), sq_nonneg f]
    have hz2 : (2 * g + 2 * q) ^ 2 ≤ 24 * (b + q ^ 2) := by
      nlinarith [sq_nonneg (g - q), sq_nonneg q]
    have hx2t := mul_le_mul_of_nonneg_left hx2 t0
    have hz2d := mul_le_mul_of_nonneg_left hz2 hδ.le
    have hsum : (e + f) ^ 2 + (e + f) * (2 * g + 2 * q)
        ≤ 6 * (1 + δ⁻¹) * (a + f ^ 2) + 6 * δ * (b + q ^ 2) := by
      linarith only [amgm, hx2, hz2, hx2t, hz2d]
    have hfin := mul_le_mul_of_nonneg_left hsum (abs_nonneg D)
    exact hb.trans (by linarith only [hfin])
  have hrc : Continuous (fun z : ℝ × Space => (1 + ‖z.2‖) ^ 2) := by fun_prop
  have mA : ∀ n, AEMeasurable (fun z : ℝ × Space => matSq (gradField (u n) z.1 z.2 - G z.1 z.2)) volume :=
    fun n => (continuous_matSq.comp_aestronglyMeasurable
      ((hP n).measurable_gradient.sub hv.measurable_gradient)).aemeasurable
  have mF : ∀ n, AEMeasurable
      (fun z : ℝ × Space => ‖u n z.1 z.2 - v z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 2) volume :=
    fun n => ((((hP n).measurable_velocity.sub hv.measurable_velocity).norm.aemeasurable.pow_const 2).div
      hrc.aemeasurable)
  have mU : ∀ n, AEMeasurable (fun z : ℝ × Space => ‖u n z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 2) volume :=
    fun n => (((hP n).measurable_velocity.norm.aemeasurable.pow_const 2).div hrc.aemeasurable)
  have mB : AEMeasurable (fun z : ℝ × Space => matSq (G z.1 z.2)) volume :=
    (continuous_matSq.comp_aestronglyMeasurable hv.measurable_gradient).aemeasurable
  have mQ : AEMeasurable (fun z : ℝ × Space => ‖v z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 2) volume :=
    (hv.measurable_velocity.norm.aemeasurable.pow_const 2).div hrc.aemeasurable
  have hX : ∀ n, periodLIntegral (fun σ y => matSq (gradField (u n) σ y - G σ y)
      + ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)
      = periodLIntegral (fun σ y => matSq (gradField (u n) σ y - G σ y))
        + periodLIntegral (fun σ y => ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) :=
    fun n => PassageLimit.periodLIntegral_add (mA n) (mF n) (fun _ _ => matSq_nonneg _)
      (fun _ _ => by positivity)
  have hXt : Tendsto (fun n => periodLIntegral (fun σ y => matSq (gradField (u n) σ y - G σ y)
      + ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)) atTop (𝓝 0) := by
    simp_rw [hX]
    simpa using hA.add hF
  obtain ⟨N, hN⟩ := (hF.eventually (gt_mem_nhds (zero_lt_one' ℝ≥0∞))).exists
  have hQfin : periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) < ⊤ := by
    have hle : ∀ σ y, ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2
        ≤ 2 * (‖u N σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 + ‖u N σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) := by
      intro σ y
      have hr : (0 : ℝ) < (1 + ‖y‖) ^ 2 := by positivity
      have h1 : ‖v σ y‖ ≤ ‖u N σ y‖ + ‖u N σ y - v σ y‖ := by
        calc ‖v σ y‖ = ‖u N σ y - (u N σ y - v σ y)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖u N σ y‖ + ‖u N σ y - v σ y‖ := norm_sub_le _ _
      have h2 : ‖v σ y‖ ^ 2 ≤ 2 * (‖u N σ y‖ ^ 2 + ‖u N σ y - v σ y‖ ^ 2) := by
        nlinarith [norm_nonneg (v σ y), norm_nonneg (u N σ y), norm_nonneg (u N σ y - v σ y),
          sq_nonneg (‖u N σ y‖ - ‖u N σ y - v σ y‖)]
      have h3 : 2 * (‖u N σ y‖ ^ 2 / (1 + ‖y‖) ^ 2 + ‖u N σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)
          = 2 * (‖u N σ y‖ ^ 2 + ‖u N σ y - v σ y‖ ^ 2) / (1 + ‖y‖) ^ 2 := by ring
      rw [h3]
      exact div_le_div_of_nonneg_right h2 hr.le
    refine lt_of_le_of_lt (PassageLimit.periodLIntegral_le_mul (by norm_num) hle) ?_
    rw [PassageLimit.periodLIntegral_add (mU N) (mF N) (fun _ _ => by positivity) (fun _ _ => by positivity)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.2 ⟨(hs N).weighted_finite, hN.trans ENNReal.one_lt_top⟩)
  have hYfin : periodLIntegral (fun σ y => matSq (G σ y) + ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) < ⊤ := by
    rw [PassageLimit.periodLIntegral_add mB mQ (fun _ _ => matSq_nonneg _) (fun _ _ => by positivity)]
    exact ENNReal.add_lt_top.2 ⟨hv.gradient_finite, hQfin⟩
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεt
  · exact Eventually.of_forall fun _ => le_top
  have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
  have hk0 : 0 ≤ (periodLIntegral (fun σ y => matSq (G σ y) + ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)).toReal :=
    ENNReal.toReal_nonneg
  set k := (periodLIntegral (fun σ y => matSq (G σ y) + ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)).toReal with hk
  have hden : 0 < 2 * (4374 * |D| * k + 1) := by
    have := mul_nonneg hc0 hk0
    linarith
  set δ := ε.toReal / (2 * (4374 * |D| * k + 1)) with hδdef
  have hδ : 0 < δ := div_pos hεr hden
  have hδm : δ * (2 * (4374 * |D| * k + 1)) = ε.toReal := div_mul_cancel₀ _ hden.ne'
  have hsecond : ENNReal.ofReal (4374 * |D| * δ)
      * periodLIntegral (fun σ y => matSq (G σ y) + ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) ≤ ε / 2 := by
    rw [← ENNReal.ofReal_toReal hYfin.ne, ← hk, ← ENNReal.ofReal_mul (mul_nonneg hc0 hδ.le)]
    have hle : 4374 * |D| * δ * k ≤ ε.toReal / 2 := by nlinarith [hδm, hδ]
    calc ENNReal.ofReal (4374 * |D| * δ * k) ≤ ENNReal.ofReal (ε.toReal / 2) := ENNReal.ofReal_le_ofReal hle
      _ = ε / 2 := by
        rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_toReal hεt, ENNReal.ofReal_ofNat]
  have hfirst : Tendsto (fun n => ENNReal.ofReal (4374 * |D| * (1 + δ⁻¹))
      * periodLIntegral (fun σ y => matSq (gradField (u n) σ y - G σ y)
        + ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul hXt (Or.inr (ENNReal.ofReal_ne_top (r := 4374 * |D| * (1 + δ⁻¹))))
    rwa [mul_zero] at h
  have hev := (tendsto_order.1 hfirst).2 (ε / 2) (ENNReal.half_pos hε.ne')
  filter_upwards [hev] with n hn
  calc periodLIntegral (fun σ y =>
        |stretchFormWith W HW (u n) (gradField (u n)) σ y - stretchFormWith W HW v G σ y|)
      ≤ periodLIntegral (fun σ y => 4374 * |D| * (1 + δ⁻¹) * (matSq (gradField (u n) σ y - G σ y)
            + ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)
          + 4374 * |D| * δ * (matSq (G σ y) + ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)) :=
        PassageLimit.periodLIntegral_mono (hpt δ hδ n)
    _ = periodLIntegral (fun σ y => 4374 * |D| * (1 + δ⁻¹) * (matSq (gradField (u n) σ y - G σ y)
            + ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2))
        + periodLIntegral (fun σ y => 4374 * |D| * δ * (matSq (G σ y) + ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)) :=
        PassageLimit.periodLIntegral_add (((mA n).add (mF n)).const_mul _) ((mB.add mQ).const_mul _)
          (fun _ _ => mul_nonneg (by positivity) (add_nonneg (matSq_nonneg _) (by positivity)))
          (fun _ _ => mul_nonneg (mul_nonneg hc0 hδ.le) (add_nonneg (matSq_nonneg _) (by positivity)))
    _ ≤ ENNReal.ofReal (4374 * |D| * (1 + δ⁻¹)) * periodLIntegral (fun σ y =>
          matSq (gradField (u n) σ y - G σ y) + ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2)
        + ENNReal.ofReal (4374 * |D| * δ)
          * periodLIntegral (fun σ y => matSq (G σ y) + ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) :=
        add_le_add (PassageLimit.periodLIntegral_le_mul (by positivity) fun _ _ => le_refl _)
          (PassageLimit.periodLIntegral_le_mul (mul_nonneg hc0 hδ.le) fun _ _ => le_refl _)
    _ ≤ ε / 2 + ε / 2 := add_le_add hn.le hsecond
    _ = ε := ENNReal.add_halves ε

section Modes

open Coercive.Internal.PiecePassageModes Coercive.Internal.DensityPassageModes

theorem piece_limits_weak {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    {U : ℕ → ℝ → Space → Space} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {σ : ℝ} {y : Space}
    (hV : ∀ κ, Tendsto (fun n => modeVel κ (U n) σ y) atTop (𝓝 (modeVel κ v σ y)))
    (hG : ∀ κ, Tendsto (fun n => modeGrad κ (gradField (U n)) σ y) atTop (𝓝 (modeGrad κ G σ y)))
    (hH : ∀ κ, Tendsto (fun n => modeSecondDeriv κ (secondDerivField (U n)) σ y) atTop (𝓝 (modeSecondDeriv κ H σ y)))
    (hu0 : Tendsto (fun n => U n σ y) atTop (𝓝 (v σ y)))
    (hg0 : Tendsto (fun n => gradField (U n) σ y) atTop (𝓝 (G σ y))) :
    (∀ ι, Tendsto (fun n => piecePos m P (U n) (gradField (U n)) ι σ y) atTop
        (𝓝 (piecePos m P v G ι σ y))) ∧
      (∀ ι, Tendsto (fun n => pieceRestWith m h w W HW (U n) (gradField (U n)) (secondDerivField (U n)) ι σ y)
        atTop (𝓝 (pieceRestWith m h w W HW v G H ι σ y))) ∧
      Tendsto (fun n => stretchFormWith W HW (U n) (gradField (U n)) σ y) atTop
        (𝓝 (stretchFormWith W HW v G σ y)) := by
  have hc1 : Continuous (fun x : Fin 3 → ℂ => Real.sqrt (cnormSq x)) :=
    Real.continuous_sqrt.comp FieldModes.continuous_cnormSq
  have hc2 : Continuous (fun x : Fin 3 × Fin 3 → ℂ => Real.sqrt (cnormSq x)) :=
    Real.continuous_sqrt.comp FieldModes.continuous_cnormSq
  have hc3 : Continuous (fun x : Fin 3 × Fin 3 × Fin 3 → ℂ => Real.sqrt (cnormSq x)) :=
    Real.continuous_sqrt.comp FieldModes.continuous_cnormSq
  have hcurl : Continuous (fun x : Fin 3 × Fin 3 → ℂ => curlOfGrad x) :=
    continuous_pi fun i => by
      simp only [curlOfGrad]
      fun_prop
  have hcurlH : Continuous (fun x : Fin 3 × Fin 3 × Fin 3 → ℂ => curlGradOfSecondDeriv x) :=
    continuous_pi fun i => by
      simp only [curlGradOfSecondDeriv]
      fun_prop
  have hva : ∀ κ, Tendsto (fun n => velAmp (U n) κ σ y) atTop (𝓝 (velAmp v κ σ y)) := fun κ =>
    (hc1.tendsto _).comp (hV κ)
  have hga : ∀ κ, Tendsto (fun n => gradAmp (gradField (U n)) κ σ y) atTop (𝓝 (gradAmp G κ σ y)) :=
    fun κ => (hc2.tendsto _).comp (hG κ)
  have hta : ∀ κ, Tendsto (fun n => vortAmp (gradField (U n)) κ σ y) atTop (𝓝 (vortAmp G κ σ y)) :=
    fun κ => ((Real.continuous_sqrt.comp FieldModes.continuous_cnormSq).comp hcurl |>.tendsto _).comp (hG κ)
  have hha : ∀ κ, Tendsto (fun n => secondDerivAmp (secondDerivField (U n)) κ σ y) atTop (𝓝 (secondDerivAmp H κ σ y)) :=
    fun κ => (hc3.tendsto _).comp (hH κ)
  have hwa : ∀ κ, Tendsto (fun n => vortGradAmp (secondDerivField (U n)) κ σ y) atTop (𝓝 (vortGradAmp H κ σ y)) :=
    fun κ => ((Real.continuous_sqrt.comp FieldModes.continuous_cnormSq).comp hcurlH |>.tendsto _).comp (hH κ)
  refine ⟨fun ι => ?_, fun ι => ?_, ?_⟩
  · unfold piecePos pieceEpsPos pieceMuPos
    exact (tendsto_finsetSum _ fun β _ => ((hta ι).pow 2).const_mul _).add
      (tendsto_finsetSum _ fun β _ => ((hva ι).pow 2).const_mul _)
  · unfold pieceRestWith modeVals pieceEpsRestModeWith pieceMuRestMode
    have hb : Continuous (fun p : ℝ × ℝ × ℝ × ℝ × ℝ =>
        baseDensity m.convD m.convZ (m.classOf ι) m.c w y p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
      unfold baseDensity
      fun_prop
    refine ((((hb.tendsto _).comp ((hha ι).prodMk_nhds ((hwa ι).prodMk_nhds ((hga ι).prodMk_nhds
      ((hta ι).prodMk_nhds (hva ι))))))).add (tendsto_finsetSum _ fun β _ => ?_)).add
      (tendsto_finsetSum _ fun β _ => ?_)
    · exact (((hta ι).const_mul _).mul ((((tendsto_edgeSum h _ _ hwa ι).add (tendsto_edgeSum h _ _ hta ι)).add
        (tendsto_edgeSum h _ _ hva ι)).add (tendsto_edgeSum h _ _ hga ι))).neg
    · exact (((hva ι).const_mul _).mul (tendsto_edgeSum h _ _ hga ι)).neg.sub
        (((((tendsto_finsetSum _ fun α _ => (hva _).const_mul _).pow 2).div_const _).add
          (((hva ι).pow 2).const_mul _)).const_mul _)
  · exact ((Coercive.Internal.PieceAbsorb.continuous_stretchOfData.tendsto _).comp
      (hg0.prodMk_nhds (tendsto_const_nhds.prodMk_nhds (tendsto_const_nhds.prodMk_nhds hu0))) :)

end Modes

end Internal.PassageStretch

end CoerciveWeak

end Breakdown
