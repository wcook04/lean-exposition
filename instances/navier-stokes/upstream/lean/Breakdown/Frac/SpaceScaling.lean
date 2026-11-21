import Breakdown.Frac.StSpace
import Breakdown.Frac.OpCovariance

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

namespace FracSpaceScalingInternal

theorem contDiff_slice_of_contDiffOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → Space → F}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Ici 0 ×ˢ univ))
    {s : ℝ} (hs : 0 ≤ s) : ContDiff ℝ ∞ (f s) := by
  have h : ContDiffOn ℝ ∞ ((fun z : ℝ × Space => f z.1 z.2) ∘ (fun x : Space => (s, x))) univ :=
    hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => ⟨hs, mem_univ _⟩)
  exact contDiffOn_univ.mp h

theorem differentiableAt_time_of_contDiffOn {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ → Space → F}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Ici 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (x : Space) : DifferentiableAt ℝ (fun τ => f τ x) s := by
  have hmem : Ici (0 : ℝ) ×ˢ (univ : Set Space) ∈ nhds (s, x) :=
    prod_mem_nhds (Ici_mem_nhds hs) Filter.univ_mem
  have h1 : DifferentiableAt ℝ (fun z : ℝ × Space => f z.1 z.2) (s, x) :=
    (hf.contDiffAt hmem).differentiableAt (by simp)
  have h2 : DifferentiableAt ℝ (fun τ : ℝ => (τ, x)) s :=
    differentiableAt_id.prodMk (differentiableAt_const x)
  exact h1.comp s h2

theorem contDiffOn_rescale {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → Space → F}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Ici 0 ×ˢ univ))
    {ν : ℝ} (hν : 0 < ν) (c : ℝ) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => c • f (z.1 / ν) z.2) (Ici 0 ×ˢ univ) := by
  have hL : ContDiff ℝ ∞ (fun z : ℝ × Space => (z.1 / ν, z.2)) :=
    (contDiff_fst.div_const ν).prodMk contDiff_snd
  have hmaps : MapsTo (fun z : ℝ × Space => (z.1 / ν, z.2)) (Ici 0 ×ˢ univ) (Ici 0 ×ˢ univ) :=
    fun z hz => ⟨div_nonneg (mem_Ici.mp (mem_prod.mp hz).1) hν.le, mem_univ _⟩
  exact (hf.comp hL.contDiffOn hmaps).const_smul c

theorem divergenceAt_const_smul {v : Space → Space} {x : Space}
    (hv : DifferentiableAt ℝ v x) (c : ℝ) :
    divergenceAt (fun y => c • v y) x = c * divergenceAt v x := by
  simp [divergenceAt, fderiv_fun_const_smul hv, Finset.mul_sum]

theorem advectionAt_const_smul {v : Space → Space} {x : Space}
    (hv : DifferentiableAt ℝ v x) (c : ℝ) :
    advectionAt (fun y => c • v y) x = (c * c) • advectionAt v x := by
  simp [advectionAt, fderiv_fun_const_smul hv, map_smul, smul_smul]

theorem gradientAt_const_mul {q : Space → ℝ} {x : Space}
    (hq : DifferentiableAt ℝ q x) (c : ℝ) :
    gradientAt (fun y => c * q y) x = c • gradientAt q x := by
  simp [gradientAt, fderiv_const_mul hq, Finset.smul_sum, smul_smul]

theorem hasDerivAt_rescale_time {g : ℝ → Space} {ν t : ℝ}
    (hg : DifferentiableAt ℝ g (t / ν)) (c : ℝ) :
    HasDerivAt (fun τ => c • g (τ / ν)) (c • (1 / ν) • deriv g (t / ν)) t := by
  have hh : HasDerivAt (fun τ : ℝ => τ / ν) (1 / ν) t := (hasDerivAt_id' t).div_const ν
  exact (hg.hasDerivAt.scomp t hh).const_smul c

end FracSpaceScalingInternal

open FracSpaceScalingInternal in
theorem fracScaling : FracScalingStatement := by
  intro α h ν hν
  obtain ⟨u₀, hsm, hcs, hdiv, hno⟩ := h
  refine ⟨fun x => ν • u₀ x, hsm.const_smul ν, hcs.smul_left (f := fun _ => ν), ?_, ?_⟩
  · intro x
    rw [divergenceAt_const_smul ((hsm.differentiable (by simp)) x), hdiv x, mul_zero]
  rintro ⟨u, p, hs, C, hC⟩
  apply hno
  have hν0 : ν ≠ 0 := hν.ne'
  refine ⟨fun t x => ν⁻¹ • u (t / ν) x, fun t x => (ν⁻¹) ^ 2 * p (t / ν) x, ⟨?_, ?_, ?_, ?_, ?_⟩,
    (ν⁻¹) ^ 2 * C, ?_⟩
  · exact contDiffOn_rescale hs.smooth_velocity hν ν⁻¹
  · exact contDiffOn_rescale hs.smooth_pressure hν ((ν⁻¹) ^ 2)
  · intro x
    simp [hs.initial, smul_smul, inv_mul_cancel₀ hν0]
  · intro t ht x
    have hst : 0 < t / ν := div_pos ht hν
    have hu : ContDiff ℝ ∞ (u (t / ν)) := contDiff_slice_of_contDiffOn hs.smooth_velocity hst.le
    have hp : ContDiff ℝ ∞ (p (t / ν)) := contDiff_slice_of_contDiffOn hs.smooth_pressure hst.le
    have hud : DifferentiableAt ℝ (u (t / ν)) x := (hu.differentiable (by simp)) x
    have hpd : DifferentiableAt ℝ (p (t / ν)) x := (hp.differentiable (by simp)) x
    have hgt := differentiableAt_time_of_contDiffOn hs.smooth_velocity hst x
    have hu2 : ContDiff ℝ 2 (u (t / ν)) := hu.of_le (WithTop.coe_le_coe.mpr le_top)
    rw [(hasDerivAt_rescale_time hgt ν⁻¹).deriv, advectionAt_const_smul hud,
      (covariance α (u (t / ν)) hu2).2.1 ν⁻¹ x, gradientAt_const_mul hpd]
    have key := congrArg (fun w : Space => (ν⁻¹) ^ 2 • w) (hs.momentum (t / ν) hst x)
    simp only [smul_add, smul_neg, smul_smul] at key
    have hc : (ν⁻¹) ^ 2 * ν = ν⁻¹ := by field_simp
    rw [hc] at key
    rw [one_smul, smul_smul, one_div, ← sq]
    convert key using 2
  · intro t ht x
    have hst : 0 < t / ν := div_pos ht hν
    have hu : ContDiff ℝ ∞ (u (t / ν)) := contDiff_slice_of_contDiffOn hs.smooth_velocity hst.le
    rw [divergenceAt_const_smul ((hu.differentiable (by simp)) x),
      hs.incompressible (t / ν) hst x, mul_zero]
  · intro t ht
    have hst : 0 ≤ t / ν := div_nonneg ht hν.le
    have hpt : ∀ x, ENNReal.ofReal (‖ν⁻¹ • u (t / ν) x‖ ^ 2) =
        ENNReal.ofReal ((ν⁻¹) ^ 2) * ENNReal.ofReal (‖u (t / ν) x‖ ^ 2) := by
      intro x
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ENNReal.ofReal_mul (sq_nonneg _)]
    simp only [hpt]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (sq_nonneg _)]
    gcongr
    exact hC (t / ν) hst

end Breakdown
