import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.UniformSpace.UniformApproximation

open Filter Set
open scoped ContDiff Topology

namespace TorusEuler

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Uniform convergence of spatial differentials on an open set identifies the
differential of the velocity limit there. -/
theorem hasFDerivAt_of_uniform_spatial_limits
    {s : Set E} (hs : IsOpen s) {U : ℕ → E → G} {u : E → G}
    {DU : ℕ → E → (E →L[ℝ] G)} {D : E → (E →L[ℝ] G)}
    (hU : TendstoUniformlyOn U u atTop s) (hD : TendstoUniformlyOn DU D atTop s)
    (hderiv : ∀ j x, x ∈ s → HasFDerivAt (U j) (DU j x) x)
    {x : E} (hx : x ∈ s) :
    HasFDerivAt u (D x) x :=
  hasFDerivAt_of_tendstoUniformlyOn hs hD hderiv (fun _ hy => hU.tendsto_at hy) hx

/-- Uniform limits of the spatial derivatives of smooth approximants through
a finite order are the corresponding derivatives of the limit on an open set.
Here `p x k` is the candidate limit of the order-`k` derivative at `x`. -/
theorem contDiffOn_of_uniform_spatial_derivatives
    {s : Set E} (hs : IsOpen s) (m : ℕ) {U : ℕ → E → G} {u : E → G}
    {p : E → FormalMultilinearSeries ℝ E G}
    (hU : ∀ j, ContDiffOn ℝ m (U j) s) (hu : TendstoUniformlyOn U u atTop s)
    (hp : ∀ k ≤ m, TendstoUniformlyOn (fun j => iteratedFDeriv ℝ k (U j))
      (fun x => p x k) atTop s) :
    ContDiffOn ℝ m u s ∧ ∀ k ≤ m, EqOn (iteratedFDeriv ℝ k u) (fun x => p x k) s := by
  have hWithin (k : ℕ) (hk : k ≤ m) :
      TendstoUniformlyOn (fun j => iteratedFDerivWithin ℝ k (U j) s)
        (fun x => p x k) atTop s :=
    (hp k hk).congr (Eventually.of_forall fun j =>
      (iteratedFDerivWithin_of_isOpen (f := U j) k hs).symm)
  have hTaylor (j : ℕ) :
      HasFTaylorSeriesUpToOn m (U j) (ftaylorSeriesWithin ℝ (U j) s) s :=
    (hU j).ftaylorSeriesWithin hs.uniqueDiffOn
  have hpTaylor : HasFTaylorSeriesUpToOn m u p s := by
    constructor
    · intro x hx
      let evalZero := continuousMultilinearCurryFin0 (𝕜 := ℝ) (G := E) (G' := G)
      have hz := evalZero.continuous.continuousAt.tendsto.comp
        ((hWithin 0 (Nat.zero_le m)).tendsto_at hx)
      exact tendsto_nhds_unique_of_eventuallyEq hz (hu.tendsto_at hx)
        (Eventually.of_forall fun j => (hTaylor j).zero_eq x hx)
    · intro k hk x hx
      have hk' : k < m := by exact_mod_cast hk
      let curry := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin k.succ => E) G
      have hD := curry.isometry.uniformContinuous.comp_tendstoUniformlyOn
        (hWithin k.succ (Nat.succ_le_of_lt hk'))
      have hderiv (j : ℕ) (y : E) (hy : y ∈ s) :
          HasFDerivAt (iteratedFDerivWithin ℝ k (U j) s)
            ((iteratedFDerivWithin ℝ k.succ (U j) s y).curryLeft) y :=
        ((hTaylor j).fderivWithin k hk y hy).hasFDerivAt (hs.mem_nhds hy)
      exact (hasFDerivAt_of_uniform_spatial_limits hs (hWithin k hk'.le)
        hD hderiv hx).hasFDerivWithinAt
    · intro k hk
      have hk' : k ≤ m := by exact_mod_cast hk
      exact (hWithin k hk').continuousOn (Frequently.of_forall fun j => (hTaylor j).cont k hk)
  refine ⟨hpTaylor.contDiffOn, fun k hk x hx => ?_⟩
  rw [← iteratedFDerivWithin_of_isOpen k hs hx]
  exact (hpTaylor.eq_iteratedFDerivWithin_of_uniqueDiffOn
    (by exact_mod_cast hk) hs.uniqueDiffOn hx).symm

/-- Uniform convergence on a product set gives spatial differentiability and
identifies the derivatives on each fixed-parameter slice. The parameter set
may be a closed time slab. -/
theorem contDiffOn_slice_of_uniform_spatial_derivatives
    {A : Type*} {I : Set A} {s : Set E} (hs : IsOpen s) (m : ℕ)
    {U : ℕ → A → E → G} {u : A → E → G} {p : A → E → FormalMultilinearSeries ℝ E G}
    (hU : ∀ j t, t ∈ I → ContDiffOn ℝ m (U j t) s)
    (hu : TendstoUniformlyOn (fun j => Function.uncurry (U j))
      (Function.uncurry u) atTop (I ×ˢ s))
    (hp : ∀ k ≤ m, TendstoUniformlyOn
      (fun j (tx : A × E) => iteratedFDeriv ℝ k (U j tx.1) tx.2)
      (fun tx : A × E => p tx.1 tx.2 k) atTop (I ×ˢ s))
    {t : A} (ht : t ∈ I) :
    ContDiffOn ℝ m (u t) s ∧
      ∀ k ≤ m, EqOn (iteratedFDeriv ℝ k (u t)) (fun x => p t x k) s := by
  refine contDiffOn_of_uniform_spatial_derivatives hs m (fun j => hU j t ht) ?_ ?_
  · exact (hu.comp (fun x : E => (t, x))).mono (fun _ hx => ⟨ht, hx⟩)
  · intro k hk
    exact ((hp k hk).comp (fun x : E => (t, x))).mono (fun _ hx => ⟨ht, hx⟩)

end TorusEuler
