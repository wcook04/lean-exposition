import Mathlib

open Filter Topology

namespace WeakCompact.Internal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem limit_in_closed_span (u : ℕ → E) (C : ℝ) (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (x : E), StrictMono φ ∧ ‖x‖ ≤ C ∧
      ∀ y : E, Tendsto (fun n => inner ℝ (u (φ n)) y) atTop (𝓝 (inner ℝ x y)) := by
  set M : Submodule ℝ E := (Submodule.span ℝ (Set.range u)).topologicalClosure with hM
  have hsep : TopologicalSpace.IsSeparable (M : Set E) := by
    rw [hM, Submodule.topologicalClosure_coe]
    exact (Set.countable_range u).isSeparable.span.closure
  have : TopologicalSpace.SeparableSpace M := hsep.separableSpace
  have : CompleteSpace M :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hmem : ∀ n, u n ∈ M := fun n =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)
  let w : ℕ → M := fun n => ⟨u n, hmem n⟩
  let v : ℕ → WeakDual ℝ M := fun n => StrongDual.toWeakDual (InnerProductSpace.toDual ℝ M (w n))
  have hv : ∀ n, v n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ M) C := by
    intro n
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    have : WeakDual.toStrongDual (v n) = InnerProductSpace.toDual ℝ M (w n) := rfl
    rw [this, LinearIsometryEquiv.norm_map]
    exact hu n
  obtain ⟨f, hf, φ, hφ, hlim⟩ := WeakDual.isSeqCompact_closedBall ℝ M 0 C hv
  refine ⟨φ, ((InnerProductSpace.toDual ℝ M).symm (WeakDual.toStrongDual f) : E), hφ, ?_, ?_⟩
  · have h1 : ‖((InnerProductSpace.toDual ℝ M).symm (WeakDual.toStrongDual f) : E)‖
        = ‖WeakDual.toStrongDual f‖ := by
      exact (InnerProductSpace.toDual ℝ M).symm.norm_map (WeakDual.toStrongDual f)
    rw [h1]
    simpa [Metric.mem_closedBall, dist_zero_right] using hf
  · intro y
    rw [tendsto_iff_forall_eval_tendsto_topDualPairing] at hlim
    have h := hlim (M.orthogonalProjectionOnto y)
    have e1 : ∀ n, topDualPairing ℝ M (v (φ n)) (M.orthogonalProjectionOnto y)
        = inner ℝ (u (φ n)) y := by
      intro n
      show inner ℝ (w (φ n)) (M.orthogonalProjectionOnto y) = _
      exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (w (φ n)) y
    have e2 : topDualPairing ℝ M f (M.orthogonalProjectionOnto y)
        = inner ℝ ((InnerProductSpace.toDual ℝ M).symm (WeakDual.toStrongDual f) : E) y := by
      rw [← Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, InnerProductSpace.toDual_symm_apply]
      rfl
    simp only [Function.comp_apply, e1, e2] at h
    exact h

end WeakCompact.Internal

open WeakCompact.Internal in
theorem exists_weakly_convergent_subseq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (u : ℕ → E) (C : ℝ) (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (x : E), StrictMono φ ∧ ‖x‖ ≤ C ∧
      ∀ y : E, Filter.Tendsto (fun n => inner ℝ (u (φ n)) y) Filter.atTop (nhds (inner ℝ x y)) :=
  limit_in_closed_span u C hu

theorem mem_of_weak_limit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hK : Convex ℝ K) (hKc : IsClosed K) (u : ℕ → E) (hu : ∀ n, u n ∈ K) (x : E)
    (hx : ∀ y : E, Filter.Tendsto (fun n => inner ℝ (u n) y) Filter.atTop (nhds (inner ℝ x y))) :
    x ∈ K := by
  by_contra hxK
  obtain ⟨f, c, hfx, hfK⟩ := geometric_hahn_banach_point_closed hK hKc hxK
  set z : E := (InnerProductSpace.toDual ℝ E).symm f
  have hz : ∀ a : E, f a = inner ℝ a z := fun a => by
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  have hge : c ≤ inner ℝ x z :=
    ge_of_tendsto (hx z) (Eventually.of_forall fun n => by
      rw [← hz]; exact (hfK _ (hu n)).le)
  rw [hz] at hfx
  linarith
