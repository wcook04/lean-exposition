import TorusEuler.PeriodicEnergyCancellation
import TorusEuler.TruncatedParentAdmissibility
import TorusEuler.TorusLabelFlow
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.ODE.Gronwall

/-! Classical velocity uniqueness for smooth periodic Euler flow. -/

open Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

noncomputable section

private theorem IsEulerSolution.continuousOn_timeDerivative_of_prefix
    {T S : ℝ} {U : Velocity} {p : Pressure} (h : IsEulerSolution T U p) (hS : 0 < S) (hST : S < T) :
    ContinuousOn (Function.uncurry (timeDerivative T U)) (Icc 0 S ×ˢ (univ : Set Vec3)) := by
  let J := Icc 0 S ×ˢ (univ : Set Vec3)
  have hSub : Icc 0 S ⊆ Ico 0 T := fun _ ht => ⟨ht.1, ht.2.trans_lt hST⟩
  have hU : ContDiffOn ℝ ∞ (Function.uncurry U) J := h.smooth_velocity.mono (prod_mono_left hSub)
  have hUnique : UniqueDiffOn ℝ J := (uniqueDiffOn_Icc hS).prod uniqueDiffOn_univ
  let d := fun z : ℝ × Vec3 => fderivWithin ℝ (Function.uncurry U) J z (1, 0)
  have hd : ContinuousOn d J :=
    (hU.continuousOn_fderivWithin hUnique (by simp)).clm_apply continuousOn_const
  refine hd.congr ?_
  rintro ⟨t, x⟩ hz
  have hmap : MapsTo (fun r : ℝ => (r, x)) (Icc 0 S) J :=
    fun _ hr => ⟨hr, mem_univ x⟩
  have hIn : HasDerivWithinAt (fun r : ℝ => (r, x)) (1, 0) (Icc 0 S) t :=
    (hasDerivWithinAt_id t (Icc 0 S)).prodMk (hasDerivWithinAt_const t _ x)
  have hFrom := ((hU.differentiableOn (by simp) (t, x) hz).hasFDerivWithinAt).comp_hasDerivWithinAt
    t hIn hmap
  have hTo := (h.hasDerivWithinAt_velocity (hSub hz.1) x).mono hSub
  exact (hTo.derivWithin (uniqueDiffOn_Icc hS t hz.1)).symm.trans
    (hFrom.derivWithin (uniqueDiffOn_Icc hS t hz.1))

private theorem continuous_pressure_slice {T : ℝ} {U : Velocity} {p : Pressure}
    (h : IsEulerSolution T U p) {r : ℝ} (hr : r ∈ Ico 0 T) : ContDiff ℝ ∞ (p r) :=
  contDiffOn_univ.mp (h.smooth_pressure.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    fun _ _ => ⟨hr, mem_univ _⟩)

private theorem timeDerivative_eq_neg_momentum {T : ℝ} {u : Velocity} {p : Pressure}
    (h : IsEulerSolution T u p) {t : ℝ} (ht : t ∈ Ico 0 T) (x : Vec3) :
    timeDerivative T u t x = -(fderiv ℝ (u t) x (u t x)) - gradient (p t) x := by
  calc
    _ = timeDerivative T u t x + fderiv ℝ (u t) x (u t x) + gradient (p t) x -
        fderiv ℝ (u t) x (u t x) - gradient (p t) x := by abel
    _ = _ := by rw [h.momentum t ht x, zero_sub]

/-- Smooth periodic Euler solutions with the same data have the same
velocity throughout their common lifespan. -/
theorem IsEulerSolution.velocity_eq_on_common_interval
    {T₁ T₂ : ℝ} {u v : Velocity} {p q : Pressure}
    (hu : IsEulerSolution T₁ u p) (hv : IsEulerSolution T₂ v q) (h0 : u 0 = v 0) :
    ∀ t ∈ Ico 0 (min T₁ T₂), u t = v t := by
  intro t ht
  obtain ⟨S, htS, hS⟩ := exists_between ht.2
  have hS₀ : 0 < S := ht.1.trans_lt htS
  have hS₁ : S < T₁ := hS.trans_le (min_le_left _ _)
  have hS₂ : S < T₂ := hS.trans_le (min_le_right _ _)
  have hSub₁ : Icc 0 S ⊆ Ico 0 T₁ := fun _ hr => ⟨hr.1, hr.2.trans_lt hS₁⟩
  have hSub₂ : Icc 0 S ⊆ Ico 0 T₂ := fun _ hr => ⟨hr.1, hr.2.trans_lt hS₂⟩
  let w (r : ℝ) (x : Vec3) := u r x - v r x
  let Q (r : ℝ) (x : Vec3) := p r x - q r x
  let d (r : ℝ) (x : Vec3) := timeDerivative T₁ u r x - timeDerivative T₂ v r x
  let J := Icc 0 S ×ˢ (univ : Set Vec3)
  have huJ : ContDiffOn ℝ ∞ (Function.uncurry u) J := hu.smooth_velocity.mono (prod_mono_left hSub₁)
  have hvJ : ContDiffOn ℝ ∞ (Function.uncurry v) J := hv.smooth_velocity.mono (prod_mono_left hSub₂)
  have hwJ : ContDiffOn ℝ ∞ (Function.uncurry w) J := huJ.sub hvJ
  have hdJ : ContinuousOn (Function.uncurry d) J :=
    (hu.continuousOn_timeDerivative_of_prefix hS₀ hS₁).sub
      (hv.continuousOn_timeDerivative_of_prefix hS₀ hS₂)
  obtain ⟨C, hLip⟩ := exists_lipschitzWith_of_contDiffOn_periodic hS₀
    (huJ.of_le (by simp)) (fun r hr => hu.periodic_velocity r (hSub₁ hr))
  let energy (r : ℝ) := ∫ x in centeredCell, ‖w r x‖ ^ 2
  let energyRate (r : ℝ) := ∫ x in centeredCell, 2 * ⟪w r x, d r x⟫_ℝ
  have hEnergy (r : ℝ) (hr : r ∈ Icc 0 S) :
      HasDerivWithinAt energy (energyRate r) (Icc 0 S) r :=
    hasDerivWithinAt_integral_prod_Icc
      (F := fun s x => ‖w s x‖ ^ 2) (D := fun s x => 2 * ⟪w s x, d s x⟫_ℝ)
      isCompact_centeredCell hr
      ((hwJ.continuousOn.norm.pow 2).mono (prod_mono_right (subset_univ _)))
      ((continuousOn_const.mul (hwJ.continuousOn.inner hdJ)).mono (prod_mono_right (subset_univ _)))
      (fun s hs x _ => (((hu.hasDerivWithinAt_velocity (hSub₁ hs) x).mono hSub₁).sub
        ((hv.hasDerivWithinAt_velocity (hSub₂ hs) x).mono hSub₂)).norm_sq)
  have hEnergy0 : energy 0 = 0 := by simp [energy, w, h0]
  have hwPer (r : ℝ) (hr : r ∈ Icc 0 S) : SpatiallyPeriodic (w r) := by
    intro n x
    simp only [w, hu.periodic_velocity r (hSub₁ hr) n x, hv.periodic_velocity r (hSub₂ hr) n x]
  have hRate (r : ℝ) (hr : r ∈ Icc 0 S) : ‖energyRate r‖ ≤ 2 * (C : ℝ) * ‖energy r‖ := by
    have hu1 := (hu.contDiff_velocity_slice (hSub₁ hr)).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
    have hv1 := (hv.contDiff_velocity_slice (hSub₂ hr)).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
    have hp1 := (continuous_pressure_slice hu (hSub₁ hr)).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
    have hq1 := (continuous_pressure_slice hv (hSub₂ hr)).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
    have hw1 : ContDiff ℝ 1 (w r) := hu1.sub hv1
    have hQ1 : ContDiff ℝ 1 (Q r) := hp1.sub hq1
    have hQPer : SpatiallyPeriodic (Q r) := by
      intro n x
      simp only [Q, hu.periodic_pressure r (hSub₁ hr) n x, hv.periodic_pressure r (hSub₂ hr) n x]
    have hwDiv (x : Vec3) : divergence (w r) x = 0 := by
      have huD := hu1.differentiable (by simp) x
      have hvD := hv1.differentiable (by simp) x
      simp only [w, divergence, fderiv_fun_sub huD hvD,
        _root_.sub_apply, PiLp.sub_apply, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr ((hu.incompressible r (hSub₁ hr) x).trans
        (hv.incompressible r (hSub₂ hr) x).symm)
    let A (x : Vec3) := ⟪w r x, fderiv ℝ (u r) x (w r x)⟫_ℝ
    let B (x : Vec3) := ⟪w r x, fderiv ℝ (w r) x (v r x)⟫_ℝ
    let D (x : Vec3) := ⟪w r x, gradient (Q r) x⟫_ℝ
    have hMomentum (x : Vec3) : d r x =
        -(fderiv ℝ (u r) x (w r x) + fderiv ℝ (w r) x (v r x) + gradient (Q r) x) := by
      have huD := hu1.differentiable (by simp) x
      have hvD := hv1.differentiable (by simp) x
      have hpD := hp1.differentiable (by simp) x
      have hqD := hq1.differentiable (by simp) x
      dsimp only [d, w, Q]
      rw [timeDerivative_eq_neg_momentum hu (hSub₁ hr), timeDerivative_eq_neg_momentum hv (hSub₂ hr),
        fderiv_fun_sub huD hvD]
      simp only [gradient, fderiv_fun_sub hpD hqD, map_sub, _root_.sub_apply]
      abel
    have hAc : Continuous A := hw1.continuous.inner
      ((hu1.continuous_fderiv (by simp)).clm_apply hw1.continuous)
    have hBc : Continuous B := hw1.continuous.inner
      ((hw1.continuous_fderiv (by simp)).clm_apply hv1.continuous)
    have hDc : Continuous D := hw1.continuous.inner
      ((InnerProductSpace.toDual ℝ Vec3).symm.continuous.comp (hQ1.continuous_fderiv (by simp)))
    have hAi : IntegrableOn A centeredCell := hAc.continuousOn.integrableOn_compact isCompact_centeredCell
    have hBi : IntegrableOn B centeredCell := hBc.continuousOn.integrableOn_compact isCompact_centeredCell
    have hDi : IntegrableOn D centeredCell := hDc.continuousOn.integrableOn_compact isCompact_centeredCell
    have hB0 : (∫ x in centeredCell, B x) = 0 :=
      integral_inner_advection_centeredCell_eq_zero hw1 hv1 (hwPer r hr)
        (hv.periodic_velocity r (hSub₂ hr)) (hv.incompressible r (hSub₂ hr))
    have hD0 : (∫ x in centeredCell, D x) = 0 :=
      integral_inner_gradient_centeredCell_eq_zero hw1 hQ1 (hwPer r hr) hQPer hwDiv
    have hReplace : (∫ x in centeredCell, ⟪w r x, d r x⟫_ℝ) =
        ∫ x in centeredCell, -(A x + B x + D x) := by
      apply integral_congr_ae (Eventually.of_forall _)
      intro x
      rw [hMomentum, inner_neg_right, inner_add_right, inner_add_right]
    have hRateEq : energyRate r = -2 * (∫ x in centeredCell, A x) := by
      unfold energyRate
      rw [integral_const_mul, hReplace, integral_neg, integral_add (f := fun x => A x + B x) (hAi.add hBi) hDi,
        integral_add hAi hBi, hB0, hD0, add_zero, add_zero]
      ring
    have hBound (x : Vec3) : ‖A x‖ ≤ (C : ℝ) * ‖w r x‖ ^ 2 := by
      have hDer : ‖fderiv ℝ (u r) x‖ ≤ (C : ℝ) := norm_fderiv_le_of_lipschitz ℝ (hLip r hr)
      calc
        _ ≤ ‖w r x‖ * ‖fderiv ℝ (u r) x (w r x)‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖w r x‖ * ((C : ℝ) * ‖w r x‖) :=
          mul_le_mul_of_nonneg_left
            (((fderiv ℝ (u r) x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hDer (norm_nonneg _)))
            (norm_nonneg _)
        _ = _ := by ring
    rw [hRateEq, norm_mul, Real.norm_eq_abs, abs_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0), neg_neg,
      mul_assoc]
    refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm A).trans ?_) (by norm_num)
    have hInt : IntegrableOn (fun x => (C : ℝ) * ‖w r x‖ ^ 2) centeredCell :=
      ((hw1.continuous.norm.pow 2).const_mul C).continuousOn.integrableOn_compact isCompact_centeredCell
    calc
      _ ≤ ∫ x in centeredCell, (C : ℝ) * ‖w r x‖ ^ 2 :=
        integral_mono hAi.norm hInt hBound
      _ = (C : ℝ) * energy r := integral_const_mul _ _
      _ ≤ (C : ℝ) * ‖energy r‖ :=
        mul_le_mul_of_nonneg_left (le_abs_self _) C.coe_nonneg
  have hGr := norm_le_gronwallBound_of_norm_deriv_right_le (K := 2 * (C : ℝ)) (ε := 0)
    (HasDerivWithinAt.continuousOn hEnergy)
    (fun r hr => (hEnergy r (Ico_subset_Icc_self hr)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hr))
    (show ‖energy 0‖ ≤ 0 by simp [hEnergy0])
    (fun r hr => by simpa only [add_zero] using hRate r (Ico_subset_Icc_self hr))
    t ⟨ht.1, htS.le⟩
  rw [gronwallBound_ε0_δ0, norm_le_zero_iff] at hGr
  have ht' : t ∈ Icc 0 S := ⟨ht.1, htS.le⟩
  have hwCont : Continuous (w t) :=
    (hu.contDiff_velocity_slice (hSub₁ ht')).continuous.sub
      (hv.contDiff_velocity_slice (hSub₂ ht')).continuous
  funext x
  exact sub_eq_zero.mp (eq_zero_of_integral_norm_sq_centeredCell_eq_zero (hwPer t ht') hwCont hGr x)

end

end TorusEuler
