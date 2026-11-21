import TorusEuler.ResidualGradient
import Mathlib.Analysis.Calculus.MeanValue

open Set
open scoped ContDiff

namespace TorusEuler

private theorem parentPressure_even_fderiv_of_odd {f : Vec3 → Vec3} (hf : Function.Odd f) :
    Function.Even (fderiv ℝ f) := by
  intro x
  let N : Vec3 ≃L[ℝ] Vec3 :=
    (LinearIsometryEquiv.neg ℝ : Vec3 ≃ₗᵢ[ℝ] Vec3).toContinuousLinearEquiv
  have hfun : f ∘ N = -f := funext hf
  have h := N.comp_right_fderiv (f := f) (x := x)
  rw [hfun, fderiv_neg] at h
  apply ContinuousLinearMap.ext
  intro v
  have hv := DFunLike.congr_fun h v
  change -(fderiv ℝ f x v) = fderiv ℝ f (-x) (-v) at hv
  rw [map_neg] at hv
  exact (neg_injective hv).symm

/-- Odd velocity and momentum residual on a time slice force the pressure to be even. -/
theorem even_pressure_of_odd_momentumResidual {I : Set ℝ} {U : Velocity} {p : Pressure}
    {t : ℝ} (ht : t ∈ I) (hU : ∀ r ∈ I, Function.Odd (U r))
    (hR : Function.Odd (momentumResidual I U p t)) (hp : Differentiable ℝ (p t)) :
    Function.Even (p t) := by
  have hacc : Function.Odd (materialAcceleration I U t) := by
    intro x
    have htime : derivWithin (fun r => U r (-x)) I t = -derivWithin (fun r => U r x) I t :=
      (derivWithin_congr (fun r hr => hU r hr x) (hU t ht x)).trans derivWithin.neg
    simp only [materialAcceleration, htime, parentPressure_even_fderiv_of_odd (hU t ht) x, hU t ht x,
      map_neg, neg_add]
  have hgrad (x : Vec3) : gradient (p t) (-x) = -gradient (p t) x := by
    have h := hR x
    change materialAcceleration I U t (-x) + gradient (p t) (-x) =
      -(materialAcceleration I U t x + gradient (p t) x) at h
    rw [hacc x, neg_add] at h
    exact add_left_cancel h
  have hD (x : Vec3) : fderiv ℝ (p t) (-x) = -fderiv ℝ (p t) x := by
    apply (InnerProductSpace.toDual ℝ Vec3).symm.injective
    simpa only [gradient, map_neg] using hgrad x
  let N : Vec3 ≃L[ℝ] Vec3 :=
    (LinearIsometryEquiv.neg ℝ : Vec3 ≃ₗᵢ[ℝ] Vec3).toContinuousLinearEquiv
  have hneg : Differentiable ℝ (fun x => p t (-x)) := hp.comp N.differentiable
  let q : Vec3 → ℝ := fun x => p t (-x) - p t x
  have hq : Differentiable ℝ q := hneg.sub hp
  have hqD (x : Vec3) : fderiv ℝ q x = 0 := by
    change fderiv ℝ (fun y => p t (-y) - p t y) x = 0
    rw [fderiv_fun_sub (hneg x) (hp x)]
    have h := N.comp_right_fderiv (f := p t) (x := x)
    apply ContinuousLinearMap.ext
    intro v
    have hv := DFunLike.congr_fun h v
    change fderiv ℝ (fun y => p t (-y)) x v = fderiv ℝ (p t) (-x) (-v) at hv
    simp only [_root_.sub_apply, hv, hD x, map_neg, neg_apply, neg_neg, sub_self, zero_apply]
  intro x
  have hx := is_const_of_fderiv_eq_zero hq hqD x 0
  change p t (-x) - p t x = p t (-(0 : Vec3)) - p t 0 at hx
  simpa only [neg_zero, sub_self, sub_eq_zero] using hx

/-- Pressure parity holds throughout a closed slab when the actual residual and velocity are odd. -/
theorem even_pressure_on_closedSlab_of_odd_momentumResidual {l r : ℝ} {U : Velocity} {p : Pressure}
    (hp : ContDiffOn ℝ ∞ (Function.uncurry p) (Icc l r ×ˢ (univ : Set Vec3)))
    (hU : ∀ t ∈ Icc l r, Function.Odd (U t))
    (hR : ∀ t ∈ Icc l r, Function.Odd (momentumResidual (Icc l r) U p t))
    (t : ℝ) (ht : t ∈ Icc l r) : Function.Even (p t) := by
  apply even_pressure_of_odd_momentumResidual ht hU (hR t ht)
  have hs := hp.comp (contDiffOn_const.prodMk contDiffOn_id :
    ContDiffOn ℝ ∞ (fun x : Vec3 => (t, x)) univ) (fun x _ => ⟨ht, mem_univ x⟩)
  exact (contDiffOn_univ.mp hs).differentiable (by simp)

end TorusEuler
