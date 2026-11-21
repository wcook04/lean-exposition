import TorusEuler.Paper.S34A.Statements
import TorusEuler.PaperAppendixAFreezingBounded

/-! Glue for the proof of **Lemma A.2** (package S34A): assembling the higher-order
clause of `FreezingConclusion` from a restriction statement, a bounded forward map and
a bounded inverse. No numbered result is used. -/

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S34A

/-- Assembly of the higher-order clause of `FreezingConclusion` (the last sentence of
Lemma A.2, sections/appA_mean_regularity.tex:87–89) for a fixed isomorphism `e = R B`
of the fixed space: if `R B` maps `R C^{k,1/2}` into itself with a norm bound, every
datum in `R C^{k,1/2}` has a unique preimage in `R C^{k,1/2}`, and `e⁻¹` maps
`R C^{k,1/2}` into itself with a norm bound, then `v ∈ C^{k,1/2}` exactly when
`e v ∈ C^{k,1/2}`, and the two `C^{k,1/2}` norms are comparable. Pure bookkeeping. -/
theorem freezingConclusion_higher {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (R : HalfHolder (UnitAddTorus (Fin 3)) H →L[ℝ] HalfHolder (UnitAddTorus (Fin 3)) H)
    (hR : ∀ f, R (R f) = R f) (B : HalfHolder (UnitAddTorus (Fin 3)) (H →L[ℝ] H))
    (e : freezingFixedSpace R ≃L[ℝ] freezingFixedSpace R)
    (he : (e : freezingFixedSpace R →L[ℝ] freezingFixedSpace R) =
      freezingCompression R B.coefficientMul hR) (k : ℕ)
    (hfwd : ∀ v : freezingFixedSpace R,
      SpatialHolderHalf k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) v.val) →
      SpatialHolderHalf k
        (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) (R (B.coefficientMul v.val))))
    (huniq : ∀ f : freezingFixedSpace R,
      SpatialHolderHalf k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) f.val) →
      ∃! v : freezingFixedSpace R, R (B.coefficientMul v.val) = f.val ∧
        SpatialHolderHalf k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) v.val))
    (Cf : ℝ) (hCf : 0 ≤ Cf)
    (hf : ∀ v : freezingFixedSpace R,
      SpatialHolderHalf k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) v.val) →
      SpatialHolderHalf k
          (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) (R (B.coefficientMul v.val))) ∧
        spatialHolderHalfNorm k
            (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) (R (B.coefficientMul v.val))) ≤
          Cf * spatialHolderHalfNorm k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) v.val))
    (Ci : ℝ)
    (hi : ∀ f : freezingFixedSpace R,
      SpatialHolderHalf k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) f.val) →
      SpatialHolderHalf k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) (e.symm f).val) ∧
        spatialHolderHalfNorm k
            (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) (e.symm f).val) ≤
          Ci * spatialHolderHalfNorm k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) f.val)) :
    (∀ v : freezingFixedSpace R,
        SpatialHolderHalf k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) v.val) ↔
          SpatialHolderHalf k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) (e v).val)) ∧
      ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ v : freezingFixedSpace R,
        SpatialHolderHalf k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) v.val) →
        spatialHolderHalfNorm k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) (e v).val) ≤
            Ck * spatialHolderHalfNorm k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) v.val) ∧
          spatialHolderHalfNorm k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) v.val) ≤
            Ck * spatialHolderHalfNorm k
              (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) (e v).val) := by
  have hval (v : freezingFixedSpace R) : (e v).val = R (B.coefficientMul v.val) := by
    have := congrArg (fun g : freezingFixedSpace R →L[ℝ] freezingFixedSpace R => (g v).val) he
    simpa using this
  have hiff (v : freezingFixedSpace R) :
      SpatialHolderHalf k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) v.val) ↔
        SpatialHolderHalf k (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) (e v).val) := by
    constructor
    · intro hv
      rw [hval]
      exact hfwd v hv
    · intro hv
      obtain ⟨w, ⟨hw1, hw2⟩, _⟩ := huniq (e v) hv
      have hew : e w = e v := Subtype.ext (by rw [hval]; exact hw1)
      rw [← e.injective hew]
      exact hw2
  refine ⟨hiff, max Cf Ci, le_max_of_le_left hCf, fun v hv => ⟨?_, ?_⟩⟩
  · have h := (hf v hv).2
    rw [← hval] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (nonneg_spatialHolderHalfNorm _ _ hv))
  · have h := (hi (e v) ((hiff v).1 hv)).2
    rw [e.symm_apply_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (nonneg_spatialHolderHalfNorm _ _ ((hiff v).1 hv)))

end TorusEuler.Paper.Lib.S34A
