import Breakdown.CertCell.BridgeStatements
import Breakdown.Cert.ExtendedCoerciveStatement
import Breakdown.CertCell.StatementDefs

open MeasureTheory

noncomputable section

open Classical

namespace Breakdown

namespace CertCell

namespace KnotZero

def IsMirrorClosed (N : Set (ℝ × ℝ)) : Prop := ∀ p : ℝ × ℝ, p ∈ N ↔ (p.1, -p.2) ∈ N

theorem planeOf_axialRot (φ : ℝ) (y : Space) : planeOf (axialRot φ y) = planeOf y := by
  have h0 : axialRot φ y 0 = Real.cos φ * y 0 - Real.sin φ * y 1 := by simp [axialRot, unitVector]
  have h1 : axialRot φ y 1 = Real.sin φ * y 0 + Real.cos φ * y 1 := by simp [axialRot, unitVector]
  have h2 : axialRot φ y 2 = y 2 := by simp [axialRot, unitVector]
  have e : (Real.cos φ * y 0 - Real.sin φ * y 1) ^ 2 + (Real.sin φ * y 0 + Real.cos φ * y 1) ^ 2 =
      (Real.sin φ ^ 2 + Real.cos φ ^ 2) * (y 0 ^ 2 + y 1 ^ 2) := by ring
  simp only [planeOf, h0, h1, h2, e, Real.sin_sq_add_cos_sq, one_mul]

theorem planeOf_flipPoint (y : Space) : planeOf (flipPoint y) = ((planeOf y).1, -(planeOf y).2) := by
  have h0 : flipPoint y 0 = y 0 := by simp [flipPoint, unitVector]
  have h1 : flipPoint y 1 = -y 1 := by simp [flipPoint, unitVector]
  have h2 : flipPoint y 2 = -y 2 := by simp [flipPoint, unitVector]
  simp only [planeOf, h0, h1, h2, neg_sq]

theorem axialRot_zero (φ : ℝ) : axialRot φ (0 : Space) = 0 := by
  simp [axialRot]

theorem flipPoint_zero : flipPoint (0 : Space) = 0 := by
  simp [flipPoint]

theorem modeHess_zeroOn (N : Set (ℝ × ℝ)) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeSecondDeriv ι (zeroOn N HW) σ y = if planeOf y ∈ N then 0 else modeSecondDeriv ι HW σ y := by
  by_cases hy : planeOf y ∈ N
  · rw [if_pos hy]
    funext ijl
    simp [modeSecondDeriv, modeAverage, zeroOn, planeOf_axialRot, hy, axialRot_zero]
  · rw [if_neg hy]
    funext ijl
    simp [modeSecondDeriv, zeroOn, planeOf_axialRot, hy]

theorem flipModel_zeroOn {N : Set (ℝ × ℝ)} (hN : IsMirrorClosed N) {W : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : Bridge.IsFlipInvariantModel W HW) :
    Bridge.IsFlipInvariantModel W (zeroOn N HW) where
  field_flip := h.field_flip
  hessian_flip σ y a b := by
    have hm : planeOf (flipPoint y) ∈ N ↔ planeOf y ∈ N := by
      rw [planeOf_flipPoint]
      exact (hN (planeOf y)).symm
    by_cases hy : planeOf y ∈ N
    · simp only [zeroOn, if_pos hy, if_pos (hm.mpr hy), ContinuousLinearMap.zero_apply, flipPoint_zero]
    · simp only [zeroOn, if_neg hy, if_neg (mt hm.mp hy)]
      exact h.hessian_flip σ y a b

theorem harmonicExpansion_zeroOn (N : Set (ℝ × ℝ)) {S : Finset (ℤ × ℤ)} {W : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : Bridge.IsHarmonicExpansion S W HW) :
    Bridge.IsHarmonicExpansion S W (zeroOn N HW) where
  symmetric := h.symmetric
  field_span := h.field_span
  gradient_span := h.gradient_span
  hessian_span σ y i j l := by
    simp only [modeHess_zeroOn]
    by_cases hy : planeOf y ∈ N
    · simp [zeroOn, hy]
    · simp only [zeroOn, if_neg hy]
      exact h.hessian_span σ y i j l

theorem ae_not_knot {N : Set (ℝ × ℝ)} (hnull : volume {y : Space | planeOf y ∈ N} = 0) :
    ∀ᵐ y : Space, planeOf y ∉ N :=
  ae_iff.mpr (by simpa using hnull)

theorem zeroOn_ae_eq {N : Set (ℝ × ℝ)} (hnull : volume {y : Space | planeOf y ∈ N} = 0)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) :
    (fun y => zeroOn N HW σ y) =ᵐ[volume] (fun y => HW σ y) := by
  filter_upwards [ae_not_knot hnull] with y hy
  simp [zeroOn, hy]

theorem weakHessianState_zeroOn {N : Set (ℝ × ℝ)} (hnull : volume {y : Space | planeOf y ∈ N} = 0)
    {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {B : ℝ}
    (h : CoerciveWeak.IsWeakSecondDerivState W HW B) : CoerciveWeak.IsWeakSecondDerivState W (zeroOn N HW) B where
  smooth := h.smooth
  periodic := h.periodic
  divergence_free := h.divergence_free
  secondDeriv_measurable := by
    refine h.secondDeriv_measurable.congr ?_
    have e : {z : ℝ × Space | planeOf z.2 ∈ N} = Set.univ ×ˢ {y : Space | planeOf y ∈ N} := by
      ext z
      simp
    have h0 : volume {z : ℝ × Space | planeOf z.2 ∈ N} = 0 := by
      rw [e, Measure.volume_eq_prod, Measure.prod_prod, hnull, mul_zero]
    have h1 : ∀ᵐ z : ℝ × Space, planeOf z.2 ∉ N := ae_iff.mpr (by simpa using h0)
    filter_upwards [h1] with z hz
    simp [zeroOn, hz]
  secondDeriv_periodic σ y := by
    simp only [zeroOn]
    rw [h.secondDeriv_periodic]
  secondDeriv_weak σ j := by
    obtain ⟨h1, h2, h3⟩ := h.secondDeriv_weak σ j
    have hae : (fun y => (HW σ y).flip (unitVector j)) =ᵐ[volume]
        (fun y => (zeroOn N HW σ y).flip (unitVector j)) := by
      filter_upwards [zeroOn_ae_eq hnull HW σ] with y hy
      rw [hy]
    refine ⟨h1, h2.congr hae, fun φ hφ i => ?_⟩
    rw [← h3 φ hφ i]
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    rw [hy]
  decay σ y := by
    obtain ⟨d1, d2, d3⟩ := h.decay σ y
    refine ⟨d1, d2, ?_⟩
    by_cases hy : planeOf y ∈ N
    · simp only [zeroOn, if_pos hy, norm_zero]
      exact (norm_nonneg _).trans d3
    · simp only [zeroOn, if_neg hy]
      exact d3

end KnotZero

end CertCell

end Breakdown
