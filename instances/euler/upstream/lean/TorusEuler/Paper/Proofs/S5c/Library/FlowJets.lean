import TorusEuler.Paper.Proofs.S5Bridge.Norms
import TorusEuler.Paper.Proofs.S5Bridge.Operators
import TorusEuler.PaperFlowBounds

/-!
# Glue for Lemma 5.10: scaled jets, label flows, the profile divergence

* `scaledJets_of_wNorm`, `scaledJets_of_uNorm`: the pointwise jets of the scaled profile
  `(x, s) ↦ f(t, ℓ_* x, h s)` at one time are bounded by the finite norms (D.1) (`S5.wNorm`
  with a weight `γ ≤ 1`, `S5.uNorm`), through the library
  `scaledPhaseProfile_jetBound_of_actual_weightedWordNorm`.
* `scaledJets_apply`: the scaled jets of `G(a) F(a,s)` for a label-dependent operator `G` and
  a profile `F` (Leibniz' rule for the evaluation map, Mathlib's
  `ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear`).
* `labelPaths_eqOn` (copy of the private lemma of `TorusLabelFlow.lean:18`, unchanged) and
  `labelFlow_eq`: label flows of a field that is Lipschitz in space are unique.
* `profileDivergence_pointwise`: the vanishing of the total divergence `𝐝̃·W` of a profile,
  read along the parent flow, in the form used by the flow estimate of Lemma 5.10 (the
  computation of the library proof `assemble_of_mean_divergence`,
  `HierarchyPhysicalApproximation.lean:370-401`, for an arbitrary profile).
-/

open Set
open scoped ContDiff InnerProductSpace NNReal

namespace TorusEuler.Paper.Lib.S5c

open HierarchyTwistedProfile

noncomputable section

/-! ## Scaled jets from the finite norms (D.1) -/

/-- The scaled jets of a twisted profile at a time `t ∈ [t₀,T]` are bounded by its weighted
norm (D.1), for a weight `0 < γ ≤ 1`. -/
theorem scaledJets_of_wNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} {k : Vec3} (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) {γ : ℝ → ℝ}
    (hγc : ContinuousOn γ (Icc t₀ T)) (hγp : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγ1 : ∀ t ∈ Icc t₀ T, γ t ≤ 1) {B : ℝ} (hB : ∀ t ∈ Icc t₀ T, ‖(γ t)⁻¹‖ ≤ B)
    (ℓ h : ℝ) (n : ℕ) (f : HierarchyTwistedProfile T k E) {t : ℝ} (ht : t ∈ Icc t₀ T) :
    PhaseJetBound n (4 ^ n * S5.wNorm ℓ h t₀ γ n f)
      (scaledPhaseProfile ℓ h (fun a s => f.val.val.val (t, a, s))) := by
  have hfin := Bridge.fieldNormFinite_weighted hT ℓ h n ht₀ htT hγc hγp f
  have hsl := Bridge.fieldNormFinite_slices hT ℓ h n (Icc_subset_Icc_left ht₀) f
  have hJ := scaledPhaseProfile_jetBound_of_actual_weightedWordNorm
    (f := fun (r : Icc t₀ T) (a : Vec3) (s : ℝ) => f.val.val.val (r.1, a, s))
    (gamma := fun r => γ r.1) (ell := ℓ) (h := h) (n := n) hfin.2 ⟨t, ht⟩ (hγp t ht)
    (hsl.1 ⟨t, ht⟩)
  have hnn : 0 ≤ S5.wNorm ℓ h t₀ γ n f := Bridge.wNorm_nonneg ℓ h n hT ht₀ γ hB f
  intro j hj z
  refine (hJ j hj z).trans ?_
  change γ t * (4 ^ n * S5.wNorm ℓ h t₀ γ n f) ≤ 4 ^ n * S5.wNorm ℓ h t₀ γ n f
  exact mul_le_of_le_one_left (by positivity) (hγ1 t ht)

/-- The scaled jets of a twisted profile at a time `t ∈ [0,T]` are bounded by its
unweighted norm (D.1). -/
theorem scaledJets_of_uNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} {k : Vec3} (hT : 0 < T) (ℓ h : ℝ) (n : ℕ) (f : HierarchyTwistedProfile T k E)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    PhaseJetBound n (4 ^ n * S5.uNorm ℓ h n f)
      (scaledPhaseProfile ℓ h (fun a s => f.val.val.val (t, a, s))) := by
  have hγc : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc 0 T) := continuousOn_const
  have hfin := Bridge.fieldNormFinite_weighted hT ℓ h n le_rfl hT.le hγc (fun _ _ => one_pos) f
  have hsl := Bridge.fieldNormFinite_slices hT ℓ h n subset_rfl f
  have hJ := scaledPhaseProfile_jetBound_of_actual_weightedWordNorm
    (f := fun (r : Icc 0 T) (a : Vec3) (s : ℝ) => f.val.val.val (r.1, a, s))
    (gamma := fun _ => (1 : ℝ)) (ell := ℓ) (h := h) (n := n) hfin.2 ⟨t, ht⟩ one_pos
    (hsl.1 ⟨t, ht⟩)
  have hw : hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n
      (fun (r : Icc 0 T) => (1 : ℝ)⁻¹ •
        Function.uncurry (fun (a : Vec3) (s : ℝ) => f.val.val.val (r.1, a, s))) =
      S5.uNorm ℓ h n f := by
    rw [inv_one]
    rfl
  intro j hj z
  refine (hJ j hj z).trans (le_of_eq ?_)
  rw [hw, one_mul]

/-- Scaled jets of `G(a) F(a,s)`: Leibniz' rule for the evaluation of a label-dependent
operator `G` on a profile `F`, with `|ℓ| ≤ 1`. -/
theorem scaledJets_apply {ℓ h : ℝ} (hℓ : |ℓ| ≤ 1) {G : Vec3 → Vec3 →L[ℝ] Vec3}
    {F : Vec3 → ℝ → Vec3} (hG : ContDiff ℝ ∞ G) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    {n : ℕ} {AG AF : ℝ} (hAG : 0 ≤ AG) (hAF : 0 ≤ AF)
    (hGj : ∀ j ≤ n, ∀ a, ‖iteratedFDeriv ℝ j G a‖ ≤ AG)
    (hFj : PhaseJetBound n AF (scaledPhaseProfile ℓ h F)) :
    PhaseJetBound n (2 ^ n * AG * AF) (scaledPhaseProfile ℓ h (fun a s => G a (F a s))) := by
  let L : Vec3 × ℝ →L[ℝ] Vec3 := ℓ • ContinuousLinearMap.fst ℝ Vec3 ℝ
  have hL : ‖L‖ ≤ 1 := by
    change ‖ℓ • ContinuousLinearMap.fst ℝ Vec3 ℝ‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg ℓ) (ContinuousLinearMap.norm_fst_le _ _ _)).trans hℓ
  let Gs : Vec3 × ℝ → Vec3 →L[ℝ] Vec3 := G ∘ L
  let Fs := scaledPhaseProfile ℓ h F
  have hGs : ContDiff ℝ ∞ Gs := hG.comp L.contDiff
  have hFs : ContDiff ℝ ∞ Fs := hF.comp (labelPhaseScale ℓ h).contDiff
  have hprof : scaledPhaseProfile ℓ h (fun a s => G a (F a s)) =
      fun z => (ContinuousLinearMap.id ℝ (Vec3 →L[ℝ] Vec3)) (Gs z) (Fs z) := rfl
  have hGsj (i : ℕ) (hi : i ≤ n) (z : Vec3 × ℝ) : ‖iteratedFDeriv ℝ i Gs z‖ ≤ AG := by
    rw [L.iteratedFDeriv_comp_right hG z (by exact_mod_cast le_top)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (mul_le_mul (hGj i hi (L z)) (pow_le_one₀ (norm_nonneg _) hL)
      (pow_nonneg (norm_nonneg _) _) hAG).trans_eq (mul_one AG)
  intro j hj z
  rw [hprof]
  refine ((ContinuousLinearMap.id ℝ (Vec3 →L[ℝ] Vec3)).norm_iteratedFDeriv_le_of_bilinear
    hGs hFs z (by exact_mod_cast le_top)).trans ?_
  have hid : ‖ContinuousLinearMap.id ℝ (Vec3 →L[ℝ] Vec3)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hsum : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i Gs z‖ *
      ‖iteratedFDeriv ℝ (j - i) Fs z‖ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * AG * AF :=
    Finset.sum_le_sum fun i hi => by
      have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hGsj i (hij.trans hj) z) (Nat.cast_nonneg _))
        (hFj (j - i) ((Nat.sub_le j i).trans hj) z) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hAG)
  have hchoose : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * AG * AF = 2 ^ j * AG * AF := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    congr 2
    exact_mod_cast Nat.sum_range_choose j
  have h2 : (2 : ℝ) ^ j ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hj
  calc
    _ ≤ 1 * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i Gs z‖ *
        ‖iteratedFDeriv ℝ (j - i) Fs z‖ :=
      mul_le_mul_of_nonneg_right hid (Finset.sum_nonneg fun i _ => by positivity)
    _ ≤ 1 * (2 ^ j * AG * AF) := by rw [← hchoose]; exact mul_le_mul_of_nonneg_left hsum zero_le_one
    _ ≤ _ := by
      rw [one_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hAG) hAF

/-! ## Uniqueness of label flows -/

/-- Copy of the private `labelPaths_eqOn` (`TorusLabelFlow.lean:18`). -/
theorem labelPaths_eqOn {U : Velocity} {l r s : ℝ} {K : ℝ≥0}
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

/-- Two label flows of a field that is uniformly Lipschitz in space on `[0,T]` agree on
`[0,T]`. -/
theorem labelFlow_eq {u : Velocity} {T : ℝ} {K : ℝ≥0}
    (hLip : ∀ t ∈ Icc 0 T, LipschitzWith K (u t)) {Y Z : ℝ → Velocity}
    (hY : IsLabelFlowOn u Y (Icc 0 T)) (hZ : IsLabelFlowOn u Z (Icc 0 T))
    {s : ℝ} (hs : s ∈ Icc 0 T) {t : ℝ} (ht : t ∈ Icc 0 T) : Z s t = Y s t := by
  funext a
  exact labelPaths_eqOn hs hLip (fun r hr => hZ.trajectory s hs a r hr)
    (fun r hr => hY.trajectory s hs a r hr) ((hZ.initial s hs a).trans (hY.initial s hs a).symm) ht

/-! ## The total divergence along the parent flow -/

/-- The vanishing of the total divergence `𝐝̃·W` of a profile, read along the parent flow:
`div_y W(t, X(t,0)y, s) + ((D_aX)^{-T} k_*)·∂_s W = 0` at `y = X(0,t)a`. This is the computation
of `HierarchyPhysicalApproximation.lean:370-401` for an arbitrary twisted profile. -/
theorem profileDivergence_pointwise {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity}
    {k : Vec3} (d : ParentGeometry hT U X k) (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t))
    (W : HierarchyTwistedProfile T k Vec3) (hW : S5.totalDivergence d W = 0) :
    ∀ t ∈ Icc 0 T, ∀ a s,
      divergence (fun y => W.val.val.val (t, X t 0 y, s)) (X 0 t a) +
        ⟪(fderiv ℝ (X t 0) (X 0 t a)).adjoint k,
          deriv (fun r => W.val.val.val (t, a, r)) s⟫_ℝ = 0 := by
  intro t ht a s
  have hA : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => X z.1 0 z.2) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hX.contDiffOn_inverseLabelFlow hT hU hper
  have hAslice : ContDiff ℝ ∞ (X t 0) :=
    contDiffOn_univ.mp (hA.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  obtain ⟨_, hChart⟩ := d.inverseGraph_values hX hU hper
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by simp)) hper
  have hInv : X t 0 (X 0 t a) = a := (hX.inverse hK (left_mem_Icc.mpr hT.le) ht).1 a
  have hA' := hAslice.differentiable (by simp) (X 0 t a)
  have hWs : ContDiff ℝ ∞ (fun x => W.val.val.val (t, x, s)) := by
    have hsm := HierarchySmoothProfile.smooth W.val.val
    exact contDiffOn_univ.mp (hsm.comp (contDiff_const.prodMk
      (contDiff_id.prodMk contDiff_const)).contDiffOn (fun x _ => ⟨ht, mem_univ _⟩))
  have hLabel : DifferentiableAt ℝ (fun x => W.val.val.val (t, x, s)) a :=
    hWs.differentiable (by simp) a
  have hLabel' : HasFDerivAt (fun x => W.val.val.val (t, x, s))
      (fderiv ℝ (fun x => W.val.val.val (t, x, s)) a) (X t 0 (X 0 t a)) := by
    rw [hInv]
    exact hLabel.hasFDerivAt
  have hD := hLabel'.comp (X 0 t a) hA'.hasFDerivAt
  change HasFDerivAt (fun y => W.val.val.val (t, X t 0 y, s))
    ((fderiv ℝ (fun x => W.val.val.val (t, x, s)) a).comp (fderiv ℝ (X t 0) (X 0 t a)))
    (X 0 t a) at hD
  have hZero : (HierarchySmoothProfile.profileTotalDivergence hT d.inverse.val.val
      d.covector.val.val W.val.val).val (t, a, s) = 0 := by
    have h := congrArg (fun F : HierarchySmoothProfile T ℝ => F.val (t, a, s)) hW
    exact h
  rw [show divergence (fun y => W.val.val.val (t, X t 0 y, s)) (X 0 t a) =
    LinearMap.trace ℝ Vec3 ((fderiv ℝ (fun x => W.val.val.val (t, x, s)) a).comp
      (fderiv ℝ (X t 0) (X 0 t a))).toLinearMap by
    rw [divergence_eq_trace_fderiv, hD.fderiv]]
  have hG' := (hChart t ht (X 0 t a) s).1
  have hκ' := (hChart t ht (X 0 t a) s).2
  rw [hInv] at hG' hκ'
  simpa only [HierarchySmoothProfile.profileTotalDivergence, LinearMap.add_apply,
    Submodule.coe_add, Pi.add_apply,
    HierarchySmoothProfile.profileLabelDivergence_apply hT d.inverse.val.val W.val.val ht,
    HierarchySmoothProfile.profilePhaseDivergence_apply hT d.covector.val.val W.val.val ht,
    hG', hκ'] using hZero

end

end TorusEuler.Paper.Lib.S5c
