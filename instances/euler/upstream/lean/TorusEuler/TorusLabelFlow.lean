import TorusEuler.PeriodicLift
import Mathlib.Analysis.ODE.ExistUnique

open Filter Set
open scoped NNReal

namespace TorusEuler

/-- A pointwise two-time flow on the lift. `X s t a` is the position at time `t`
of the particle at `a` at time `s`. -/
structure IsLabelFlowOn (U : Velocity) (X : ℝ → Velocity) (I : Set ℝ) : Prop where
  initial (s : ℝ) (hs : s ∈ I) (a : Vec3) : X s s a = a
  trajectory (s : ℝ) (hs : s ∈ I) (a : Vec3) (t : ℝ) (ht : t ∈ I) :
    HasDerivWithinAt (fun r => X s r a) (U t (X s t a)) I t

private theorem labelPaths_eqOn {U : Velocity} {l r s : ℝ} {K : ℝ≥0}
    {f g : ℝ → Vec3} (hs : s ∈ Icc l r)
    (hLip : ∀ t ∈ Icc l r, LipschitzWith K (U t))
    (hf : ∀ t ∈ Icc l r, HasDerivWithinAt f (U t (f t)) (Icc l r) t)
    (hg : ∀ t ∈ Icc l r, HasDerivWithinAt g (U t (g t)) (Icc l r) t)
    (hfg : f s = g s) : EqOn f g (Icc l r) := by
  intro t ht
  rcases le_total s t with hst | hts
  · have hsub : Icc s r ⊆ Icc l r := Icc_subset_Icc_left hs.1
    exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ)
      (fun u hu => (hLip u (hsub (Ico_subset_Icc_self hu))).lipschitzOnWith)
      ((HasDerivWithinAt.continuousOn hf).mono hsub)
      (fun u hu => ((hf u (hsub (Ico_subset_Icc_self hu))).mono hsub).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hu))
      (fun _ _ => mem_univ _)
      ((HasDerivWithinAt.continuousOn hg).mono hsub)
      (fun u hu => ((hg u (hsub (Ico_subset_Icc_self hu))).mono hsub).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hu))
      (fun _ _ => mem_univ _) hfg ⟨hst, ht.2⟩
  · have hsub : Icc l s ⊆ Icc l r := Icc_subset_Icc_right hs.2
    exact ODE_solution_unique_of_mem_Icc_left (s := fun _ => univ)
      (fun u hu => (hLip u (hsub (Ioc_subset_Icc_self hu))).lipschitzOnWith)
      ((HasDerivWithinAt.continuousOn hf).mono hsub)
      (fun u hu => ((hf u (hsub (Ioc_subset_Icc_self hu))).mono hsub).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem hu))
      (fun _ _ => mem_univ _)
      ((HasDerivWithinAt.continuousOn hg).mono hsub)
      (fun u hu => ((hg u (hsub (Ioc_subset_Icc_self hu))).mono hsub).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem hu))
      (fun _ _ => mem_univ _) hfg ⟨ht.1, hts⟩

/-- Uniform boundedness and a spatial Lipschitz bound give trajectories from every
time and label on the full closed interval. -/
theorem exists_labelFlow_on_Icc {U : Velocity} {l r : ℝ} {C K : ℝ≥0}
    (hU : ContinuousOn (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hbound : ∀ t ∈ Icc l r, ∀ a : Vec3, ‖U t a‖ ≤ C)
    (hLip : ∀ t ∈ Icc l r, LipschitzWith K (U t)) :
    ∃ X : ℝ → Velocity, IsLabelFlowOn U X (Icc l r) := by
  classical
  have hpaths (s : ℝ) (a : Vec3) : ∃ f : ℝ → Vec3, s ∈ Icc l r →
      f s = a ∧ ∀ t ∈ Icc l r, HasDerivWithinAt f (U t (f t)) (Icc l r) t := by
    by_cases hs : s ∈ Icc l r
    · let D : ℝ≥0 := ⟨r - l, sub_nonneg.mpr (hs.1.trans hs.2)⟩
      have hPicard : IsPicardLindelof U (⟨s, hs⟩ : Icc l r) a (C * D) 0 C K := by
        constructor
        · exact fun t ht => (hLip t ht).lipschitzOnWith
        · intro x _
          exact hU.comp (continuous_id.prodMk continuous_const).continuousOn
            (fun t ht => ⟨ht, mem_univ x⟩)
        · exact fun t ht x _ => hbound t ht x
        · change (C : ℝ) * max (r - s) (s - l) ≤ (C : ℝ) * (r - l) - 0
          rw [sub_zero]
          exact mul_le_mul_of_nonneg_left
            (max_le (sub_le_sub_left hs.1 r) (sub_le_sub_right hs.2 l)) C.coe_nonneg
      obtain ⟨f, hf, hderiv⟩ := hPicard.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
      exact ⟨f, fun _ => ⟨hf, hderiv⟩⟩
    · exact ⟨fun _ => a, fun h => (hs h).elim⟩
  choose f hf using hpaths
  exact ⟨fun s t a => f s a t,
    ⟨fun s hs a => (hf s a hs).1, fun s hs a => (hf s a hs).2⟩⟩

/-- A continuous periodic field has the uniform velocity bound needed for Picard–Lindelöf. -/
theorem exists_labelFlow_on_Icc_of_periodic {U : Velocity} {l r : ℝ} {K : ℝ≥0}
    (hU : ContinuousOn (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hperiodic : ∀ t ∈ Icc l r, SpatiallyPeriodic (U t))
    (hLip : ∀ t ∈ Icc l r, LipschitzWith K (U t)) :
    ∃ X : ℝ → Velocity, IsLabelFlowOn U X (Icc l r) := by
  have hc : IsCompact (Icc l r ×ˢ centeredCell) := isCompact_Icc.prod isCompact_centeredCell
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn
    (hU.mono (prod_subset_prod_right (subset_univ _)))
  refine exists_labelFlow_on_Icc (C := Real.toNNReal C) hU (fun t ht a => ?_) hLip
  obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell a
  have heq : U t a = U t (a - latticeVector n) := by
    simpa only [sub_add_cancel] using hperiodic t ht n (a - latticeVector n)
  rw [heq]
  exact (hC (t, a - latticeVector n) ⟨ht, hn⟩).trans (Real.le_coe_toNNReal C)

/-- A jointly (C^1) periodic velocity on a nondegenerate closed slab has a
uniform spatial Lipschitz bound, including at the temporal endpoints. -/
theorem exists_lipschitzWith_of_contDiffOn_periodic {U : Velocity} {l r : ℝ}
    (hlr : l < r) (hU : ContDiffOn ℝ 1 (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hperiodic : ∀ t ∈ Icc l r, SpatiallyPeriodic (U t)) :
    ∃ K : ℝ≥0, ∀ t ∈ Icc l r, LipschitzWith K (U t) := by
  let S := Icc l r ×ˢ (univ : Set Vec3)
  let space := ContinuousLinearMap.inr ℝ ℝ Vec3
  let D := fun q => (fderivWithin ℝ (Function.uncurry U) S q).comp space
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Icc hlr).prod uniqueDiffOn_univ
  have hD : ContinuousOn D S :=
    (hU.continuousOn_fderivWithin hS (by norm_num)).clm_comp continuousOn_const
  have hspace (t : ℝ) (ht : t ∈ Icc l r) (a : Vec3) :
      HasFDerivAt (U t) (D (t, a)) a := by
    have hU' := (hU.differentiableOn (by norm_num) (t, a) ⟨ht, mem_univ a⟩).hasFDerivWithinAt
    exact hU'.comp_hasFDerivAt a (hasFDerivAt_prodMk_right (𝕜 := ℝ) t a)
      (Eventually.of_forall fun x => ⟨ht, mem_univ x⟩)
  have hc : IsCompact (Icc l r ×ˢ centeredCell) := isCompact_Icc.prod isCompact_centeredCell
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn
    (hD.mono (prod_subset_prod_right (subset_univ _)))
  refine ⟨Real.toNNReal C, fun t ht => lipschitzWith_of_nnnorm_fderiv_le
    (fun a => (hspace t ht a).differentiableAt) (fun a => ?_)⟩
  obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell a
  have hshift : (fun x => U t (x + latticeVector n)) = U t :=
    funext (hperiodic t ht n)
  have heq := congrArg (fun f => fderiv ℝ f (a - latticeVector n)) hshift
  rw [fderiv_comp_add_right, sub_add_cancel, (hspace t ht (a - latticeVector n)).fderiv] at heq
  change ‖fderiv ℝ (U t) a‖ ≤ (Real.toNNReal C : ℝ)
  rw [heq]
  exact (hC (t, a - latticeVector n) ⟨ht, hn⟩).trans (Real.le_coe_toNNReal C)

/-- A jointly (C^1) periodic velocity has a pointwise flow on the full closed slab. -/
theorem exists_labelFlow_on_Icc_of_contDiffOn_periodic {U : Velocity} {l r : ℝ}
    (hlr : l < r) (hU : ContDiffOn ℝ 1 (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hperiodic : ∀ t ∈ Icc l r, SpatiallyPeriodic (U t)) :
    ∃ (K : ℝ≥0) (X : ℝ → Velocity), (∀ t ∈ Icc l r, LipschitzWith K (U t)) ∧
      IsLabelFlowOn U X (Icc l r) := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hlr hU hperiodic
  obtain ⟨X, hX⟩ := exists_labelFlow_on_Icc_of_periodic hU.continuousOn hperiodic hK
  exact ⟨K, X, hK, hX⟩

variable {U : Velocity} {X : ℝ → Velocity} {l r : ℝ} {K : ℝ≥0}

/-- Restarting a trajectory at any intermediate time gives the same trajectory. -/
theorem IsLabelFlowOn.restart (hX : IsLabelFlowOn U X (Icc l r))
    (hLip : ∀ t ∈ Icc l r, LipschitzWith K (U t))
    {s t u : ℝ} (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) (hu : u ∈ Icc l r) (a : Vec3) :
    X t u (X s t a) = X s u a :=
  labelPaths_eqOn ht hLip (hX.trajectory t ht (X s t a)) (hX.trajectory s hs a)
    (hX.initial t ht (X s t a)) hu

/-- The transition map is inverted by exchanging its start and end times. -/
theorem IsLabelFlowOn.inverse (hX : IsLabelFlowOn U X (Icc l r))
    (hLip : ∀ t ∈ Icc l r, LipschitzWith K (U t))
    {s t : ℝ} (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) :
    Function.LeftInverse (X t s) (X s t) ∧ Function.RightInverse (X t s) (X s t) := by
  exact ⟨fun a => (hX.restart hLip hs ht hs a).trans (hX.initial s hs a),
    fun a => (hX.restart hLip ht hs ht a).trans (hX.initial t ht a)⟩

/-- Periodicity of the velocity gives lattice equivariance on the lift. -/
theorem IsLabelFlowOn.add_latticeVector (hX : IsLabelFlowOn U X (Icc l r))
    (hLip : ∀ t ∈ Icc l r, LipschitzWith K (U t))
    (hperiodic : ∀ t ∈ Icc l r, SpatiallyPeriodic (U t))
    {s t : ℝ} (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) (n : Fin 3 → ℤ) (a : Vec3) :
    X s t (a + latticeVector n) = X s t a + latticeVector n := by
  refine labelPaths_eqOn hs hLip (hX.trajectory s hs (a + latticeVector n))
    (g := fun u => X s u a + latticeVector n) (fun u hu => ?_) ?_ ht
  · simpa only [hperiodic u hu n] using (hX.trajectory s hs a u hu).add_const (latticeVector n)
  · simp only [hX.initial s hs]

/-- An odd velocity has odd transition maps. -/
theorem IsLabelFlowOn.odd (hX : IsLabelFlowOn U X (Icc l r))
    (hLip : ∀ t ∈ Icc l r, LipschitzWith K (U t))
    (hodd : ∀ t ∈ Icc l r, Function.Odd (U t))
    {s t : ℝ} (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) : Function.Odd (X s t) := by
  intro a
  refine labelPaths_eqOn hs hLip (hX.trajectory s hs (-a))
    (g := fun u => -(X s u a)) (fun u hu => ?_) ?_ ht
  · rw [hodd u hu (X s u a)]
    exact (hX.trajectory s hs a u hu).neg
  · simp only [hX.initial s hs]

end TorusEuler
