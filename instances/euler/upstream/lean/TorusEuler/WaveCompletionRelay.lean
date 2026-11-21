import TorusEuler.MovingFrame
import TorusEuler.WaveCompletion
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Order.ProjIcc

/-! Time differentiation of the curl potential in the relay estimate of Section 5. -/

open MeasureTheory Set
open scoped Interval
open scoped InnerProductSpace

namespace TorusEuler

local notation "V₃" => EuclideanSpace ℝ (Fin 3)

noncomputable section

private theorem cross3_neg_left (k v : V₃) : cross3 (-k) v = -cross3 k v := by
  apply WithLp.ofLp_injective
  simp only [cross3, WithLp.ofLp_toLp, WithLp.ofLp_neg]
  rw [map_neg, LinearMap.neg_apply]

private theorem cross3_self_smul (k : V₃) (r : ℝ) : cross3 k (r • k) = 0 := by
  apply WithLp.ofLp_injective
  simp [cross3, cross_self]

private theorem cross3_sub_right (k v w : V₃) :
    cross3 k (v - w) = cross3 k v - cross3 k w := by
  apply WithLp.ofLp_injective
  simp only [cross3, WithLp.ofLp_toLp, WithLp.ofLp_sub, map_sub]

/-- The inverse squared length in the curl potential evolves without a derivative of
the strain. The derivative is valid within the entire closed time slab. -/
theorem hasDerivWithinAt_inverse_normsq_waveCovector
    {J : Set ℝ} {t : ℝ} {κ : ℝ → V₃} (M : V₃ →L[ℝ] V₃)
    (hκ : HasDerivWithinAt κ (-(M.adjoint (κ t))) J t) (hn : κ t ≠ 0) :
    HasDerivWithinAt (fun r => (‖κ r‖ ^ 2)⁻¹)
      (2 * ⟪κ t, M (κ t)⟫_ℝ / (‖κ t‖ ^ 2) ^ 2) J t := by
  have h := hκ.norm_sq.inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn))
  refine h.congr_deriv ?_
  have hinner : ⟪κ t, M.adjoint (κ t)⟫_ℝ = ⟪κ t, M (κ t)⟫_ℝ := by
    calc
      _ = ⟪M.adjoint (κ t), κ t⟫_ℝ := real_inner_comm _ _
      _ = _ := M.adjoint_inner_left _ _
  simp only [inner_neg_right, hinner, mul_neg, neg_neg]

/-- This is the integrand of the paper's formula for `∂t Q[V]`. The pressure
component of the source drops out because it is parallel to the covector. -/
def wavePotentialTimeSource (M : V₃ →L[ℝ] V₃) (κ v f : V₃) : V₃ :=
  (‖κ‖ ^ 2)⁻¹ • (cross3 (M.adjoint κ) v + cross3 κ (M v) - cross3 κ f) -
    (2 * ⟪κ, M κ⟫_ℝ / (‖κ‖ ^ 2) ^ 2) • cross3 κ v

theorem hasDerivWithinAt_wavePotentialIntegrand
    {J : Set ℝ} {t q : ℝ} {κ v : ℝ → V₃} {f : V₃} (M : V₃ →L[ℝ] V₃)
    (hκ : HasDerivWithinAt κ (-(M.adjoint (κ t))) J t) (hn : κ t ≠ 0)
    (hv : HasDerivWithinAt v (f - M (v t) - q • κ t) J t) :
    HasDerivWithinAt (fun r => (-(‖κ r‖ ^ 2)⁻¹) • cross3 (κ r) (v r))
      (wavePotentialTimeSource M (κ t) (v t) f) J t := by
  have hInv := (hasDerivWithinAt_inverse_normsq_waveCovector M hκ hn).fun_neg
  have hCross := hasDerivWithinAt_cross3 hκ hv
  refine (hInv.smul hCross).congr_deriv ?_
  simp only [wavePotentialTimeSource, cross3_neg_left, cross3_sub_right, cross3_self_smul,
    sub_zero, neg_smul, smul_add, smul_sub, smul_neg, neg_neg]
  abel

section PhaseTimeDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem continuous_phaseAnchoredIntegral {f : ℝ → ℝ → E}
    (hf : Continuous (Function.uncurry f)) :
    Continuous (fun z : ℝ × ℝ => ∫ s in (0 : ℝ)..z.2, f z.1 s) := by
  have hchange (z : ℝ × ℝ) :
      (∫ s in (0 : ℝ)..z.2, f z.1 s) =
        z.2 • ∫ s in (0 : ℝ)..1, f z.1 (s * z.2) := by
    simpa only [zero_mul, one_mul] using
      (intervalIntegral.smul_integral_comp_mul_right (a := 0) (b := 1) (f z.1) z.2).symm
  simp only [hchange, intervalIntegral.integral_of_le zero_le_one]
  apply continuous_snd.smul
  refine continuous_parametric_integral_of_continuous
    (μ := (volume : Measure ℝ)) (f := fun (z : ℝ × ℝ) s => f z.1 (s * z.2))
    (?_) (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    |>.congr ?_
  · exact hf.comp (continuous_fst.fst.prodMk (continuous_snd.mul continuous_fst.snd))
  · intro z
    exact integral_Icc_eq_integral_Ioc

private theorem continuousOn_phaseAnchoredIntegral {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → ℝ → E} (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ univ)) :
    ContinuousOn (fun z : ℝ × ℝ => ∫ s in (0 : ℝ)..z.2, f z.1 s) (Icc a b ×ˢ univ) := by
  let clamp := fun u => (projIcc a b hab u : ℝ)
  have hclamp : Continuous clamp := continuous_subtype_val.comp continuous_projIcc
  have hExt : Continuous (Function.uncurry (fun u s => f (clamp u) s)) :=
    hf.comp_continuous (hclamp.prodMap continuous_id) (fun _ => ⟨(projIcc a b hab _).property,
      mem_univ _⟩)
  refine (continuous_phaseAnchoredIntegral hExt).continuousOn.congr ?_
  intro z hz
  change (∫ s in (0 : ℝ)..z.2, f z.1 s) = ∫ s in (0 : ℝ)..z.2, f (clamp z.1) s
  rw [show clamp z.1 = z.1 from congrArg Subtype.val (projIcc_of_mem hab hz.1)]

variable [CompleteSpace E]

/-- Time differentiation passes through integration over a fixed phase interval on a
closed time slab, including at its endpoints. -/
theorem hasDerivWithinAt_phaseInterval {a b t : ℝ} (ht : t ∈ Icc a b)
    {f d : ℝ → ℝ → E}
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ univ))
    (hd : ContinuousOn (Function.uncurry d) (Icc a b ×ˢ univ))
    (hD : ∀ u ∈ Icc a b, ∀ s, HasDerivWithinAt (fun r => f r s) (d u s) (Icc a b) u)
    (c e : ℝ) :
    HasDerivWithinAt (fun r => ∫ s in c..e, f r s) (∫ s in c..e, d t s) (Icc a b) t := by
  have hab := ht.1.trans ht.2
  let clamp := fun u => (projIcc a b hab u : ℝ)
  let dExt := fun u s => d (clamp u) s
  have clamp_eq {u : ℝ} (hu : u ∈ Icc a b) : clamp u = u :=
    congrArg Subtype.val (projIcc_of_mem hab hu)
  have hclamp : Continuous clamp := continuous_subtype_val.comp continuous_projIcc
  have hExt : Continuous (Function.uncurry dExt) :=
    hd.comp_continuous (hclamp.prodMap continuous_id)
      (fun z => ⟨(projIcc a b hab z.1).property, mem_univ _⟩)
  have hInt : Continuous (fun u => ∫ s in c..e, dExt u s) := by
    have hconvert (u : ℝ) : (∫ s in c..e, dExt u s) =
        (∫ s in 0..e, dExt u s) - ∫ s in 0..c, dExt u s := by
      have hc : Continuous (dExt u) := hExt.comp (continuous_const.prodMk continuous_id)
      apply eq_sub_of_add_eq
      rw [add_comm]
      exact intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable 0 c) (hc.intervalIntegrable c e)
    simp only [hconvert]
    exact ((continuous_phaseAnchoredIntegral hExt).comp (continuous_id.prodMk continuous_const)).sub
      ((continuous_phaseAnchoredIntegral hExt).comp (continuous_id.prodMk continuous_const))
  have hFTC : ∀ u ∈ Icc a b, ∀ s, (∫ r in t..u, dExt r s) = f u s - f t s := by
    intro u hu s
    have hsub := uIcc_subset_Icc ht hu
    have hfps : ContinuousOn (fun r => f r s) (uIcc t u) :=
      hf.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun _ hr => ⟨hsub hr, mem_univ _⟩)
    have hcs : Continuous (fun r => dExt r s) := hExt.comp (continuous_id.prodMk continuous_const)
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right hfps _ (hcs.intervalIntegrable t u)
    intro r hr
    have hrJ : r ∈ Icc a b := hsub ⟨hr.1.le, hr.2.le⟩
    have hrI : r ∈ Ioo a b :=
      ⟨(le_min ht.1 hu.1).trans_lt hr.1,
        hr.2.trans_le (max_le ht.2 hu.2)⟩
    have hrN : Icc a b ∈ nhds r := Icc_mem_nhds hrI.1 hrI.2
    simpa only [dExt, clamp_eq hrJ] using ((hD r hrJ s).hasDerivAt hrN).hasDerivWithinAt (s := Ioi r)
  have hIntegralRep (u : ℝ) (hu : u ∈ Icc a b) :
      (∫ r in t..u, ∫ s in c..e, dExt r s) + (∫ s in c..e, f t s) =
        ∫ s in c..e, f u s := by
    rw [intervalIntegral_intervalIntegral_swap, show (fun s => ∫ r in t..u, dExt r s) =
      (fun s => f u s - f t s) from funext (hFTC u hu)]
    · have hfPhase {x : ℝ} (hx : x ∈ Icc a b) : Continuous (f x) :=
        hf.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hx, mem_univ _⟩)
      rw [intervalIntegral.integral_sub ((hfPhase hu).intervalIntegrable c e)
        ((hfPhase ht).intervalIntegrable c e), sub_add_cancel]
    · exact (hExt.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
        (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hderiv := intervalIntegral.integral_hasDerivAt_right (hInt.intervalIntegrable t t)
    hInt.aestronglyMeasurable.stronglyMeasurableAtFilter hInt.continuousAt
  refine ((hderiv.add_const _).hasDerivWithinAt.congr_of_mem
    (fun u hu => (hIntegralRep u hu).symm) ht).congr_deriv ?_
  simp only [dExt, clamp_eq ht]

/-- The phase primitive and its zero-mean normalization commute with the time derivative
within a closed slab. -/
theorem hasDerivWithinAt_phasePrimitive_time {a b t : ℝ} (ht : t ∈ Icc a b)
    {f d : ℝ → ℝ → E}
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ univ))
    (hd : ContinuousOn (Function.uncurry d) (Icc a b ×ˢ univ))
    (hD : ∀ u ∈ Icc a b, ∀ s, HasDerivWithinAt (fun r => f r s) (d u s) (Icc a b) u)
    (s : ℝ) :
    HasDerivWithinAt (fun r => phasePrimitive (f r) s) (phasePrimitive (d t) s) (Icc a b) t := by
  have hab := ht.1.trans ht.2
  exact (hasDerivWithinAt_phaseInterval ht hf hd hD 0 s).sub
    (hasDerivWithinAt_phaseInterval ht
      (f := fun r σ => ∫ z in (0 : ℝ)..σ, f r z)
      (d := fun r σ => ∫ z in (0 : ℝ)..σ, d r z)
      (continuousOn_phaseAnchoredIntegral hab hf)
      (continuousOn_phaseAnchoredIntegral hab hd)
      (fun r hr σ => hasDerivWithinAt_phaseInterval hr hf hd hD 0 σ) 0 1)

end PhaseTimeDerivative

/-- The time derivative of the actual normalized periodic curl potential in Section 5.
Only the strain, covector, amplitude and transverse forcing appear in the integrand. -/
theorem hasDerivWithinAt_wavePotential_time {a b t : ℝ} (ht : t ∈ Icc a b)
    {κ : ℝ → V₃} {V f : ℝ → ℝ → V₃} {q : ℝ → ℝ → ℝ} {M : ℝ → V₃ →L[ℝ] V₃}
    (hn : ∀ u ∈ Icc a b, κ u ≠ 0)
    (hκ : ∀ u ∈ Icc a b, HasDerivWithinAt κ (-((M u).adjoint (κ u))) (Icc a b) u)
    (hV : ∀ u ∈ Icc a b, ∀ s, HasDerivWithinAt (fun r => V r s)
      (f u s - M u (V u s) - q u s • κ u) (Icc a b) u)
    (hIntegrand : ContinuousOn (fun z : ℝ × ℝ => (-(‖κ z.1‖ ^ 2)⁻¹) •
      cross3 (κ z.1) (V z.1 z.2)) (Icc a b ×ˢ univ))
    (hSource : ContinuousOn (fun z : ℝ × ℝ => wavePotentialTimeSource (M z.1) (κ z.1)
      (V z.1 z.2) (f z.1 z.2)) (Icc a b ×ˢ univ))
    (s : ℝ) :
    HasDerivWithinAt (fun r => wavePotential (κ r) (V r) s)
      (phasePrimitive (fun σ => wavePotentialTimeSource (M t) (κ t) (V t σ) (f t σ)) s)
      (Icc a b) t :=
  hasDerivWithinAt_phasePrimitive_time ht
    (f := fun u σ => (-(‖κ u‖ ^ 2)⁻¹) • cross3 (κ u) (V u σ))
    (d := fun u σ => wavePotentialTimeSource (M u) (κ u) (V u σ) (f u σ))
    hIntegrand hSource
    (fun u hu σ => hasDerivWithinAt_wavePotentialIntegrand (M u) (hκ u hu) (hn u hu)
      (hV u hu σ)) s

end

end TorusEuler
