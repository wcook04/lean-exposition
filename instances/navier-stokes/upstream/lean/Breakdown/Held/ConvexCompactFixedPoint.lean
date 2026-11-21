import Breakdown.Held.Statements
import Breakdown.Cert.FixedPointBox

noncomputable section

open Set

namespace Breakdown.FracInternal

theorem nearestPoint_nonexpansive {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {K : Set F} (p : F → F) (hpK : ∀ u, p u ∈ K)
    (hvi : ∀ u, ∀ w ∈ K, inner ℝ (u - p u) (w - p u) ≤ 0) :
    LipschitzWith 1 p := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  have h1 := hvi x (p y) (hpK y)
  have h2 := hvi y (p x) (hpK x)
  have e1 : inner ℝ (x - y) (p x - p y) - inner ℝ (p x - p y) (p x - p y)
      = inner ℝ (x - p x) (p x - p y) - inner ℝ (y - p y) (p x - p y) := by
    rw [← inner_sub_left, ← inner_sub_left]
    congr 1
    abel
  have e2 : inner ℝ (x - p x) (p y - p x) = - inner ℝ (x - p x) (p x - p y) := by
    rw [← inner_neg_right, neg_sub]
  have key : ‖p x - p y‖ ^ 2 ≤ inner ℝ (x - y) (p x - p y) := by
    rw [← real_inner_self_eq_norm_sq]
    linarith
  have hcs : inner ℝ (x - y) (p x - p y) ≤ ‖x - y‖ * ‖p x - p y‖ := real_inner_le_norm _ _
  by_contra hlt
  push Not at hlt
  nlinarith [norm_nonneg (p x - p y), norm_nonneg (x - y)]

end Breakdown.FracInternal

namespace Breakdown.Held

theorem convexCompactFixedPoint : ConvexCompactFixedPointStatement := by
  intro k K hconv hcomp hne f hf hmaps
  classical
  let e := EuclideanSpace.equiv (Fin k) ℝ
  let K' : Set (EuclideanSpace ℝ (Fin k)) := e ⁻¹' K
  have hK'conv : Convex ℝ K' := hconv.linear_preimage (e : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] Fin k → ℝ)
  have hK'comp : IsCompact K' := e.toHomeomorph.isCompact_preimage.2 hcomp
  obtain ⟨x0, hx0⟩ := hne
  have hne' : K'.Nonempty := ⟨e.symm x0, by simpa [K'] using hx0⟩
  choose p hpK hpmin using exists_norm_eq_iInf_of_complete_convex hne' hK'comp.isComplete hK'conv
  have hvi : ∀ u, ∀ w ∈ K', inner ℝ (u - p u) (w - p u) ≤ 0 := fun u =>
    (norm_eq_iInf_iff_real_inner_le_zero hK'conv (hpK u)).1 (hpmin u)
  have hslope : LipschitzWith 1 p := Breakdown.FracInternal.nearestPoint_nonexpansive p hpK hvi
  have hfix : ∀ u ∈ K', p u = u := by
    intro u hu
    have h := hvi u u hu
    rw [real_inner_self_nonpos, sub_eq_zero] at h
    exact h.symm
  obtain ⟨R, hR⟩ := hcomp.isBounded.subset_closedBall 0
  have hbox : ∀ x ∈ K, x ∈ Icc (fun _ : Fin k => -R) (fun _ => R) := by
    intro x hx
    have hn : ‖x‖ ≤ R := mem_closedBall_zero_iff.1 (hR hx)
    have hi : ∀ i, |x i| ≤ R := fun i => by
      have h := norm_le_pi_norm x i
      rw [Real.norm_eq_abs] at h
      exact h.trans hn
    exact ⟨fun i => (abs_le.1 (hi i)).1, fun i => (abs_le.1 (hi i)).2⟩
  have hab : (fun _ : Fin k => -R) ≤ fun _ => R := (hbox x0 hx0).1.trans (hbox x0 hx0).2
  have hq : ∀ z, e (p (e.symm z)) ∈ K := fun z => hpK _
  have hqc : Continuous fun z => e (p (e.symm z)) :=
    e.continuous.comp (hslope.continuous.comp e.symm.continuous)
  have hgc : Continuous fun z => f (e (p (e.symm z))) := hf.comp_continuous hqc hq
  obtain ⟨x, -, hx⟩ := Breakdown.exists_fixedPoint_box _ _ hab (fun z => f (e (p (e.symm z))))
    hgc.continuousOn (fun z _ => hbox _ (hmaps (hq z)))
  have hxK : x ∈ K := hx ▸ hmaps (hq x)
  have hpx : p (e.symm x) = e.symm x := hfix _ (by simpa [K'] using hxK)
  have h2 : e (p (e.symm x)) = x := by
    rw [hpx]
    exact e.apply_symm_apply x
  refine ⟨x, hxK, ?_⟩
  have hx' : f (e (p (e.symm x))) = x := hx
  rwa [h2] at hx'

end Breakdown.Held
