import TorusEuler.PhysicalCutoffEstimates

/-! # Glue for the proof of Lemma B.1: contractions preserve `C^{m,1/2}`

Public copy (namespace `TorusEuler.Paper.Lib.SBD`) of the private glue lemma
`spatialHolderHalf_comp_contraction` (TorusEuler/PhysicalCutoffEstimates.lean:345).
The proof of Lemma B.1 uses it to transfer the complex `C^{0,1/2}` bound of
the cutoff to real velocity fields (complexify, cut off, take the real part).
The copy is verbatim except for the name and visibility. -/

open Set
open scoped ContDiff

namespace TorusEuler.Paper.Lib.SBD

/-- A continuous linear map of norm at most one preserves `C^{m,1/2}` and does
not increase `spatialHolderHalfNorm m`. Copy of the private
`spatialHolderHalf_comp_contraction` (PhysicalCutoffEstimates.lean:345). -/
theorem spatialHolderHalf_comp_contraction'
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : ∀ a, ‖L a‖ ≤ ‖a‖)
    {f : Vec3 → E} {m : ℕ} (hf : SpatialHolderHalf m f) :
    SpatialHolderHalf m (L ∘ f) ∧
      spatialHolderHalfNorm m (L ∘ f) ≤ spatialHolderHalfNorm m f := by
  have hnorm : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun a => by simpa only [one_mul] using hL a)
  have hjets (j : ℕ) (hj : j ≤ m) (x : Vec3) :
      iteratedFDeriv ℝ j (L ∘ f) x = L.compContinuousMultilinearMap (iteratedFDeriv ℝ j f x) :=
    L.iteratedFDeriv_comp_left hf.1.contDiffAt (by exact_mod_cast hj)
  have hmap (j : ℕ) (q : Vec3 [×j]→L[ℝ] E) :
      ‖L.compContinuousMultilinearMap q‖ ≤ ‖q‖ :=
    (L.norm_compContinuousMultilinearMap_le q).trans
      (mul_le_of_le_one_left (norm_nonneg _) hnorm)
  have hpoint (j : ℕ) (hj : j ≤ m) (x : Vec3) :
      ‖iteratedFDeriv ℝ j (L ∘ f) x‖ ≤ ‖iteratedFDeriv ℝ j f x‖ := by
    rw [hjets j hj]
    exact hmap _ _
  have hinc (j : ℕ) (hj : j ≤ m) (p : Vec3 × Vec3) :
      spatialHolderHalfQuotient (iteratedFDeriv ℝ j (L ∘ f)) p ≤
        spatialHolderHalfQuotient (iteratedFDeriv ℝ j f) p := by
    unfold spatialHolderHalfQuotient
    rw [hjets j hj, hjets j hj]
    let T := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => Vec3) E F L
    change ‖T (iteratedFDeriv ℝ j f (p.1 + p.2)) - T (iteratedFDeriv ℝ j f p.1)‖ /
      Real.sqrt ‖p.2‖ ≤ _
    rw [← map_sub]
    exact div_le_div_of_nonneg_right (hmap _ _) (Real.sqrt_nonneg _)
  have hsup (j : ℕ) (hj : j ≤ m) (x : Vec3) :
      ‖iteratedFDeriv ℝ j (L ∘ f) x‖ ≤ spatialSupNorm (iteratedFDeriv ℝ j f) :=
    (hpoint j hj x).trans (norm_le_spatialSupNorm (hf.2 j hj).1 x)
  have hsemi (j : ℕ) (hj : j ≤ m) (p : Vec3 × Vec3) :
      spatialHolderHalfQuotient (iteratedFDeriv ℝ j (L ∘ f)) p ≤
        spatialHolderHalfSeminorm (iteratedFDeriv ℝ j f) :=
    (hinc j hj p).trans (le_ciSup (hf.2 j hj).2 p)
  constructor
  · exact ⟨L.contDiff.comp hf.1, fun j hj =>
      ⟨⟨_, forall_mem_range.mpr (hsup j hj)⟩, ⟨_, forall_mem_range.mpr (hsemi j hj)⟩⟩⟩
  · unfold spatialHolderHalfNorm
    apply Finset.sum_le_sum
    intro j hj
    have hj' : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    exact add_le_add (ciSup_le (hsup j hj')) (ciSup_le (hsemi j hj'))

end TorusEuler.Paper.Lib.SBD
