import TorusEuler.FourierHolderTail
import TorusEuler.PeriodicLift
import TorusEuler.PhaseJetBounds

/-! Uniform spatial Hölder bounds for smooth periodic fields on a closed slab. -/

open Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform adjacent spatial jet bounds control the lift half-Hölder norm. -/
theorem spatialHolderHalf_of_bounded_jets {f : Vec3 → E} {m : ℕ}
    (hf : ContDiff ℝ ∞ f) (B : ℕ → ℝ)
    (hB : ∀ j ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B j) :
    SpatialHolderHalf m f ∧ spatialHolderHalfNorm m f ≤
      ∑ j ∈ Finset.range (m + 1), (B j + Real.sqrt (2 * B j * B (j + 1))) := by
  have hb (j : ℕ) (hj : j ≤ m + 1) : 0 ≤ B j := (norm_nonneg _).trans (hB j hj 0)
  have hsup (j : ℕ) (hj : j ≤ m) (x : Vec3) : ‖iteratedFDeriv ℝ j f x‖ ≤ B j :=
    hB j (hj.trans (Nat.le_succ _)) x
  have hquot (j : ℕ) (hj : j ≤ m) (p : Vec3 × Vec3) :
      spatialHolderHalfQuotient (iteratedFDeriv ℝ j f) p ≤ Real.sqrt (2 * B j * B (j + 1)) := by
    rcases p with ⟨x, v⟩
    by_cases hv : v = 0
    · simp [spatialHolderHalfQuotient, hv]
    · apply (div_le_iff₀ (Real.sqrt_pos.2 (norm_pos_iff.2 hv))).2
      simpa only [add_sub_cancel_left] using norm_iteratedFDeriv_sub_le_sqrt hf
        (hb j (hj.trans (Nat.le_succ _))) (hb (j + 1) (Nat.succ_le_succ hj))
        (hsup j hj) (hB (j + 1) (Nat.succ_le_succ hj)) (x + v) x
  refine ⟨⟨hf.of_le (by simp), fun j hj =>
    ⟨⟨B j, forall_mem_range.mpr (hsup j hj)⟩, ⟨_, forall_mem_range.mpr (hquot j hj)⟩⟩⟩, ?_⟩
  unfold spatialHolderHalfNorm
  apply Finset.sum_le_sum
  intro j hj
  exact add_le_add (ciSup_le (hsup j (Finset.mem_range_succ_iff.mp hj)))
    (ciSup_le (hquot j (Finset.mem_range_succ_iff.mp hj)))

/-- Restricting the joint Taylor series to the spatial directions gives the joint continuity
of each spatial jet, including at the time endpoints. -/
theorem continuousOn_spatial_jet_of_contDiffOn_Icc {a b : ℝ} (hab : a < b)
    {F : ℝ → Vec3 → E}
    (hF : ContDiffOn ℝ ∞ (Function.uncurry F) (Icc a b ×ˢ (univ : Set Vec3))) (j : ℕ) :
    ContinuousOn (fun p : ℝ × Vec3 => iteratedFDeriv ℝ j (F p.1) p.2)
      (Icc a b ×ˢ (univ : Set Vec3)) := by
  let S : Set (ℝ × Vec3) := Icc a b ×ˢ univ
  let i := ContinuousLinearMap.inr ℝ ℝ Vec3
  let C := ContinuousMultilinearMap.compContinuousLinearMapL (F := E) (fun _ : Fin j => i)
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Icc hab).prod uniqueDiffOn_univ
  have hEq : EqOn (fun p : ℝ × Vec3 => iteratedFDeriv ℝ j (F p.1) p.2)
      (fun p => C (iteratedFDerivWithin ℝ j (Function.uncurry F) S p)) S := by
    rintro ⟨t, x⟩ hp
    let g : Vec3 →ᴬ[ℝ] (ℝ × Vec3) := i.toContinuousAffineMap + ContinuousAffineMap.const ℝ Vec3 (t, 0)
    have hg (y : Vec3) : g y = (t, y) := by
      change (0 + t, y + 0) = (t, y)
      simp
    have hgi : g.contLinear = i := by
      simp [g, ContinuousAffineMap.add_contLinear]
    have hpre : g ⁻¹' S = univ := by
      apply eq_univ_of_forall
      intro y
      change g y ∈ S
      rw [hg]
      exact ⟨hp.1, mem_univ y⟩
    have hx : x ∈ g ⁻¹' S := hpre ▸ mem_univ x
    have hpreDiff : UniqueDiffOn ℝ (g ⁻¹' S) := hpre ▸ uniqueDiffOn_univ
    have HG := (hF.ftaylorSeriesWithin hS).comp_continuousAffineMap g
    have H := HG.eq_iteratedFDerivWithin_of_uniqueDiffOn (show (j : ℕ∞ω) ≤ ∞ by simp) hpreDiff hx
    change (iteratedFDerivWithin ℝ j (Function.uncurry F) S (g x)).compContinuousLinearMap
      (fun _ => g.contLinear) = iteratedFDerivWithin ℝ j (Function.uncurry F ∘ g) (g ⁻¹' S) x at H
    rw [hpre, iteratedFDerivWithin_univ, hg, hgi, show Function.uncurry F ∘ g = F t from
      funext fun y => by rw [Function.comp_apply, hg]; rfl] at H
    exact H.symm
  exact (C.continuous.comp_continuousOn (hF.continuousOn_iteratedFDerivWithin (by simp) hS)).congr hEq

/-- Each spatial jet of a jointly smooth periodic field is uniformly bounded on the closed slab. -/
theorem exists_bound_spatial_jet_of_contDiffOn_periodic {a b : ℝ} (hab : a < b)
    {F : ℝ → Vec3 → E}
    (hF : ContDiffOn ℝ ∞ (Function.uncurry F) (Icc a b ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc a b, SpatiallyPeriodic (F t)) (j : ℕ) :
    ∃ B : ℝ, ∀ t ∈ Icc a b, ∀ x, ‖iteratedFDeriv ℝ j (F t) x‖ ≤ B := by
  let f := fun p : ℝ × Vec3 => iteratedFDeriv ℝ j (F p.1) p.2
  have hK : IsCompact (Icc a b ×ˢ centeredCell) := isCompact_Icc.prod isCompact_centeredCell
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (f := f)
    ((continuousOn_spatial_jet_of_contDiffOn_Icc hab hF j).mono (prod_mono_right (subset_univ _)))
  refine ⟨B, fun t ht x => ?_⟩
  obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell x
  have hj : iteratedFDeriv ℝ j (F t) x = iteratedFDeriv ℝ j (F t) (x - latticeVector n) := by
    calc
      _ = iteratedFDeriv ℝ j (F t) (x - latticeVector n + latticeVector n) := by rw [sub_add_cancel]
      _ = iteratedFDeriv ℝ j (fun y => F t (y + latticeVector n)) (x - latticeVector n) :=
        (iteratedFDeriv_comp_add_right j (latticeVector n) (x - latticeVector n)).symm
      _ = _ := by rw [show (fun y => F t (y + latticeVector n)) = F t from funext (hper t ht n)]
  rw [hj]
  exact hB (t, x - latticeVector n) ⟨ht, hn⟩

/-- Smooth spatially periodic fields on a nondegenerate compact time slab have a
uniform spatial half-Hölder norm at every finite order. -/
theorem exists_spatialHolderHalfNorm_bound_of_contDiffOn_periodic {a b : ℝ} (hab : a < b)
    {F : ℝ → Vec3 → E}
    (hF : ContDiffOn ℝ ∞ (Function.uncurry F) (Icc a b ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc a b, SpatiallyPeriodic (F t)) (m : ℕ) :
    ∃ K : ℝ, ∀ t ∈ Icc a b, SpatialHolderHalf m (F t) ∧ spatialHolderHalfNorm m (F t) ≤ K := by
  choose B hB using exists_bound_spatial_jet_of_contDiffOn_periodic hab hF hper
  refine ⟨∑ j ∈ Finset.range (m + 1), (B j + Real.sqrt (2 * B j * B (j + 1))), fun t ht => ?_⟩
  have hslice : ContDiff ℝ ∞ (F t) := contDiffOn_univ.mp
    (hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => ⟨ht, mem_univ x⟩))
  exact spatialHolderHalf_of_bounded_jets hslice B (fun j _ x => hB j t ht x)

/-- A smooth periodic lift has finite spatial half-Hölder norm at every order. -/
theorem spatialHolderHalf_of_contDiff_periodic {f : Vec3 → E}
    (hf : ContDiff ℝ ∞ f) (hper : SpatiallyPeriodic f) (m : ℕ) : SpatialHolderHalf m f := by
  have hF : ContDiffOn ℝ ∞ (Function.uncurry (fun _ : ℝ => f))
      (Icc (0 : ℝ) 1 ×ˢ (univ : Set Vec3)) := (hf.comp contDiff_snd).contDiffOn
  obtain ⟨_, h⟩ := exists_spatialHolderHalfNorm_bound_of_contDiffOn_periodic
    (by norm_num) hF (fun _ _ => hper) m
  exact (h 0 (by norm_num)).1

end

end TorusEuler
