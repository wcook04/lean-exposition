import TorusEuler.LabelVariational
import TorusEuler.Piola
import TorusEuler.TransportedPhase

open Asymptotics ContinuousLinearMap Filter Set
open scoped InnerProductSpace NNReal Topology

namespace TorusEuler

variable {U : Velocity} {X : ℝ → Velocity} {l r s t : ℝ}

/-- Each transition map of a jointly (C^2) periodic field is differentiable in
the label. -/
theorem IsLabelFlowOn.differentiableAt_transition (hX : IsLabelFlowOn U X (Icc l r))
    (hlr : l < r) (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hper : ∀ u ∈ Icc l r, SpatiallyPeriodic (U u)) (hs : s ∈ Icc l r) (ht : t ∈ Icc l r)
    (a : Vec3) : DifferentiableAt ℝ (X s t) a := by
  obtain ⟨F, _, _, hF⟩ := hX.exists_variationalSolution_of_contDiffOn_periodic hlr hU hper hs a
  exact (hF t ht).differentiableAt

/-- The variational equation for the actual spatial derivative of the label flow. -/
theorem IsLabelFlowOn.labelDerivative_evolves (hX : IsLabelFlowOn U X (Icc l r))
    (hlr : l < r) (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hper : ∀ u ∈ Icc l r, SpatiallyPeriodic (U u)) (hs : s ∈ Icc l r) (a : Vec3) :
    fderiv ℝ (X s s) a = .id ℝ Vec3 ∧
      ∀ t ∈ Icc l r, HasDerivWithinAt (fun u => fderiv ℝ (X s u) a)
        ((fderiv ℝ (U t) (X s t a)).comp (fderiv ℝ (X s t) a)) (Icc l r) t := by
  obtain ⟨F, hFs, hF, hD⟩ := hX.exists_variationalSolution_of_contDiffOn_periodic hlr hU hper hs a
  have hEq (u : ℝ) (hu : u ∈ Icc l r) : fderiv ℝ (X s u) a = F u := (hD u hu).fderiv
  refine ⟨(hEq s hs).trans hFs, fun t ht => ?_⟩
  rw [hEq t ht]
  exact (hF t ht).congr_of_mem hEq ht

/-- The Jacobians of the forward and reverse transitions are inverse linear maps. -/
theorem IsLabelFlowOn.labelDerivative_inverse (hX : IsLabelFlowOn U X (Icc l r))
    (hlr : l < r) (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hper : ∀ u ∈ Icc l r, SpatiallyPeriodic (U u)) (hs : s ∈ Icc l r) (ht : t ∈ Icc l r)
    (a : Vec3) :
    let F := fderiv ℝ (X s t) a
    let G := fderiv ℝ (X t s) (X s t a)
    G.comp F = .id ℝ Vec3 ∧ F.comp G = .id ℝ Vec3 := by
  dsimp only
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hlr
    (hU.of_le (by norm_num)) hper
  obtain ⟨hLeft, hRight⟩ := hX.inverse hK hs ht
  have hF := (hX.differentiableAt_transition hlr hU hper hs ht a).hasFDerivAt
  have hG := (hX.differentiableAt_transition hlr hU hper ht hs (X s t a)).hasFDerivAt
  have hF' : HasFDerivAt (X s t) (fderiv ℝ (X s t) a) (X t s (X s t a)) := by
    rwa [hLeft a]
  have hGF := (hG.comp a hF).congr_of_eventuallyEq (Eventually.of_forall fun x => (hLeft x).symm)
  have hFG := (hF'.comp (X s t a) hG).congr_of_eventuallyEq
    (Eventually.of_forall fun x => (hRight x).symm)
  exact ⟨hGF.unique (hasFDerivAt_id a), hFG.unique (hasFDerivAt_id (X s t a))⟩

/-- The label Jacobian of the divergence-free parent flow has determinant one. -/
theorem IsLabelFlowOn.det_labelDerivative (hX : IsLabelFlowOn U X (Icc l r))
    (hlr : l < r) (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hper : ∀ u ∈ Icc l r, SpatiallyPeriodic (U u))
    (hdiv : ∀ u ∈ Icc l r, ∀ x, divergence (U u) x = 0)
    (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) (a : Vec3) :
    LinearMap.det (fderiv ℝ (X s t) a).toLinearMap = 1 := by
  obtain ⟨h₀, hd⟩ := hX.labelDerivative_evolves hlr hU hper hs a
  refine det_flow_eq_one ordConnected_Icc hs hd (fun u hu => ?_) h₀ t ht
  rw [← divergence_eq_trace_fderiv]
  exact hdiv u hu _

private theorem norm_flow_displacement_le (hX : IsLabelFlowOn U X (Icc l r))
    {C : ℝ} (hC : ∀ u ∈ Icc l r, ∀ x, ‖U u x‖ ≤ C)
    (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) (x : Vec3) :
    ‖X s t x - x‖ ≤ C * ‖t - s‖ := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (hX.trajectory s hs x)
    (fun u hu => hC u hu _) (convex_Icc l r) hs ht
  simpa only [hX.initial s hs x] using h

private theorem hasDerivWithinAt_reverse_at_start (hX : IsLabelFlowOn U X (Icc l r))
    {C : ℝ} (hC : ∀ u ∈ Icc l r, ∀ x, ‖U u x‖ ≤ C)
    {K : ℝ≥0} (hK : ∀ u ∈ Icc l r, LipschitzWith K (U u))
    (ht : t ∈ Icc l r) (x : Vec3)
    (hU : ContinuousWithinAt (fun u => U u x) (Icc l r) t) :
    HasDerivWithinAt (fun u => X u t x) (-(U t x)) (Icc l r) t := by
  rw [hasDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, htime⟩ := Metric.continuousWithinAt_iff.mp hU (c / 2) (half_pos hc)
  have hcont : Continuous (fun u : ℝ => (K : ℝ) * C * ‖u - t‖) := by fun_prop
  have hlim : Tendsto (fun u : ℝ => (K : ℝ) * C * ‖u - t‖) (𝓝[Icc l r] t) (𝓝 0) := by
    have h := (hcont.continuousAt (x := t)).tendsto
    rw [sub_self, norm_zero, mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds t hδ),
    hlim (Iio_mem_nhds (half_pos hc))] with u hu huδ hsmall
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC t ht x)
  have hsub : uIcc u t ⊆ Icc l r := uIcc_subset_Icc hu ht
  have hnear (q : ℝ) (hq : q ∈ uIcc u t) : ‖U q (X u q x) - U t x‖ ≤ c := by
    have hqδ := (Real.dist_right_le_of_mem_uIcc hq).trans_lt (Metric.mem_ball.mp huδ)
    have htime' : ‖U q x - U t x‖ < c / 2 := by
      simpa only [dist_eq_norm] using htime (hsub hq) hqδ
    have hspace : ‖U q (X u q x) - U q x‖ ≤ (K : ℝ) * ‖X u q x - x‖ := by
      simpa only [dist_eq_norm] using (hK q (hsub hq)).dist_le_mul (X u q x) x
    have hdist : ‖q - u‖ ≤ ‖u - t‖ := by
      simpa only [dist_eq_norm, norm_sub_rev u q] using Real.dist_left_le_of_mem_uIcc hq
    have hmove := norm_flow_displacement_le hX hC hu (hsub hq) x
    have hsmall' : (K : ℝ) * C * ‖u - t‖ < c / 2 := hsmall
    calc
      ‖U q (X u q x) - U t x‖ ≤ ‖U q (X u q x) - U q x‖ + ‖U q x - U t x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (K : ℝ) * (C * ‖u - t‖) + c / 2 :=
        add_le_add (hspace.trans (mul_le_mul_of_nonneg_left
          (hmove.trans (mul_le_mul_of_nonneg_left hdist hC₀)) K.coe_nonneg)) htime'.le
      _ ≤ c := by rw [← mul_assoc]; linarith
  let Y (q : ℝ) := X u q x - (q - u) • U t x
  have hY (q : ℝ) (hq : q ∈ uIcc u t) :
      HasDerivWithinAt Y (U q (X u q x) - U t x) (uIcc u t) q := by
    have hlinear : HasDerivWithinAt (fun v : ℝ => (v - u) • U t x) (U t x) (uIcc u t) q := by
      simpa only [one_smul, id_eq] using
        ((hasDerivWithinAt_id q (uIcc u t)).sub_const u).smul_const (U t x)
    exact ((hX.trajectory u hu x q (hsub hq)).mono hsub).sub hlinear
  have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hY hnear (convex_uIcc u t)
    left_mem_uIcc right_mem_uIcc
  have hEq : X u t x - X t t x - (u - t) • -(U t x) = Y t - Y u := by
    simp only [Y, hX.initial u hu x, hX.initial t ht x, sub_self, zero_smul, sub_zero,
      smul_neg, ← neg_smul, neg_sub]
    abel
  rw [hEq]
  simpa only [norm_sub_rev t u] using hmean

/-- At a fixed Eulerian position, the time derivative of the inverse label is
minus its spatial derivative applied to the velocity. -/
theorem IsLabelFlowOn.hasDerivWithinAt_inverseLabel (hX : IsLabelFlowOn U X (Icc l r))
    (hlr : l < r) (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hper : ∀ u ∈ Icc l r, SpatiallyPeriodic (U u)) (hs : s ∈ Icc l r) (ht : t ∈ Icc l r)
    (x : Vec3) :
    HasDerivWithinAt (fun u => X u s x)
      (-((fderiv ℝ (X t s) x) (U t x))) (Icc l r) t := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hlr
    (hU.of_le (by norm_num)) hper
  have hc : IsCompact (Icc l r ×ˢ centeredCell) := isCompact_Icc.prod isCompact_centeredCell
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn
    (hU.continuousOn.mono (prod_subset_prod_right (subset_univ _)))
  have hUbound (u : ℝ) (hu : u ∈ Icc l r) (y : Vec3) : ‖U u y‖ ≤ C := by
    obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell y
    have h := hper u hu n (y - latticeVector n)
    rw [sub_add_cancel] at h
    rw [h]
    exact hC (u, y - latticeVector n) ⟨hu, hn⟩
  have hTime : ContinuousOn (fun u => U u x) (Icc l r) :=
    hU.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hu => ⟨hu, mem_univ _⟩)
  have hBack := hasDerivWithinAt_reverse_at_start hX hUbound hK ht x (hTime t ht)
  have hOuter : HasFDerivAt (X t s) (fderiv ℝ (X t s) x) (X t t x) := by
    rw [hX.initial t ht x]
    exact (hX.differentiableAt_transition hlr hU hper ht hs x).hasFDerivAt
  have hComp := hOuter.comp_hasDerivWithinAt t hBack
  have hActual := hComp.congr_of_mem (fun u hu => (hX.restart hK hu ht hs x).symm) ht
  simpa only [map_neg] using hActual

/-- The inverse-transpose image of the prescribed label covector along a trajectory. -/
noncomputable def labelWaveVector (X : ℝ → Velocity) (s : ℝ) (a k : Vec3) (t : ℝ) : Vec3 :=
  (fderiv ℝ (X t s) (X s t a)).adjoint k

/-- The phase composed with the reverse transition has the stated spatial gradient. -/
theorem IsLabelFlowOn.hasGradientAt_labelPhase (hX : IsLabelFlowOn U X (Icc l r))
    (hlr : l < r) (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hper : ∀ u ∈ Icc l r, SpatiallyPeriodic (U u)) (hs : s ∈ Icc l r) (ht : t ∈ Icc l r)
    (a k : Vec3) :
    HasGradientAt (fun y => ⟪k, X t s y⟫_ℝ) (labelWaveVector X s a k t) (X s t a) :=
  hasGradientAt_transportedPhase (A := fun u => X u s)
    (hX.differentiableAt_transition hlr hU hper ht hs (X s t a)).hasFDerivAt

/-- The gradient of the transported phase satisfies the covector equation along
the actual trajectory, including the time-slab endpoints. -/
theorem IsLabelFlowOn.hasDerivWithinAt_labelWaveVector (hX : IsLabelFlowOn U X (Icc l r))
    (hlr : l < r) (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hper : ∀ u ∈ Icc l r, SpatiallyPeriodic (U u)) (hs : s ∈ Icc l r) (ht : t ∈ Icc l r)
    (a k : Vec3) :
    HasDerivWithinAt (labelWaveVector X s a k)
      (-((fderiv ℝ (U t) (X s t a)).adjoint (labelWaveVector X s a k t))) (Icc l r) t := by
  classical
  let F (u : ℝ) := fderiv ℝ (X s u) a
  let G (u : ℝ) := fderiv ℝ (X u s) (X s u a)
  let E (u : ℝ) : Vec3 ≃L[ℝ] Vec3 :=
    if hu : u ∈ Icc l r then
      ContinuousLinearEquiv.equivOfInverse' (F u) (G u) (hX.labelDerivative_inverse hlr hU hper hs hu a).2
        (hX.labelDerivative_inverse hlr hU hper hs hu a).1
    else ContinuousLinearEquiv.refl ℝ Vec3
  have hEF (u : ℝ) (hu : u ∈ Icc l r) : (E u).toContinuousLinearMap = F u := by
    simp only [E, dite_eq_left hu]
    rfl
  have hEG (u : ℝ) (hu : u ∈ Icc l r) : (E u).symm.toContinuousLinearMap = G u := by
    simp only [E, dite_eq_left hu]
    rfl
  have hE : HasDerivWithinAt (fun u => (E u).toContinuousLinearMap)
      ((fderiv ℝ (U t) (X s t a)).comp (E t).toContinuousLinearMap) (Icc l r) t := by
    rw [hEF t ht]
    exact ((hX.labelDerivative_evolves hlr hU hper hs a).2 t ht).congr_of_mem hEF ht
  have hκ := hasDerivWithinAt_transportedWaveVector (k := k) hE
  rw [hEG t ht] at hκ
  exact hκ.congr_of_mem (fun u hu => by rw [hEG u hu]; rfl) ht

/-- At a fixed left endpoint the spatial Jacobian of the flow is jointly
continuous, with a uniform Lipschitz bound in the starting label. -/
theorem IsLabelFlowOn.continuousOn_labelDerivative_from_left
    (hX : IsLabelFlowOn U X (Icc l r)) (hlr : l < r)
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hper : ∀ u ∈ Icc l r, SpatiallyPeriodic (U u))
    {K L : ℝ≥0} (hK : ∀ u ∈ Icc l r, LipschitzWith K (U u))
    (hL : ∀ u ∈ Icc l r, LipschitzWith L (fderiv ℝ (U u))) :
    ContinuousOn (fun p : ℝ × Vec3 => fderiv ℝ (X l p.1) p.2)
      (Icc l r ×ˢ (univ : Set Vec3)) := by
  let F (u : ℝ) (a : Vec3) := fderiv ℝ (X l u) a
  let M (u : ℝ) (a : Vec3) := fderiv ℝ (U u) (X l u a)
  let B := Real.exp ((K : ℝ) * (r - l))
  let C := (L : ℝ) * B ^ 2
  let Q := gronwallBound 0 K C (r - l)
  have hl : l ∈ Icc l r := left_mem_Icc.2 hlr.le
  have hC₀ : 0 ≤ C := mul_nonneg L.coe_nonneg (sq_nonneg B)
  have hQ₀ : 0 ≤ Q := by
    have h := gronwallBound_mono (δ := (0 : ℝ)) le_rfl hC₀ K.coe_nonneg (sub_nonneg.mpr hlr.le)
    simpa only [gronwallBound_x0] using h
  have hF (a : Vec3) : F l a = .id ℝ Vec3 ∧
      ∀ u ∈ Icc l r, HasDerivWithinAt (fun v => F v a)
        ((M u a).comp (F u a)) (Icc l r) u :=
    hX.labelDerivative_evolves hlr hU hper hl a
  have hNorm (u : ℝ) (hu : u ∈ Icc l r) (a : Vec3) : ‖F u a‖ ≤ B := by
    simpa only [Real.coe_toNNReal _ (Real.exp_pos _).le] using
      (norm_fderiv_le_of_lipschitz ℝ (x₀ := a) (hX.lipschitzWith_labels hK hl hu))
  have hLipF (u : ℝ) (hu : u ∈ Icc l r) : LipschitzWith (Real.toNNReal Q) (F u) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hQ₀]
    let err (v : ℝ) := F v a - F v b
    let rate (v : ℝ) := (M v a).comp (err v) + (M v a - M v b).comp (F v b)
    have hDeriv (v : ℝ) (hv : v ∈ Icc l r) : HasDerivWithinAt err (rate v) (Icc l r) v := by
      refine (((hF a).2 v hv).sub ((hF b).2 v hv)).congr_deriv ?_
      simp only [rate, err, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
      abel
    have hRate (v : ℝ) (hv : v ∈ Icc l r) :
        ‖rate v‖ ≤ (K : ℝ) * ‖err v‖ + C * ‖a - b‖ := by
      have hM : ‖M v a‖ ≤ (K : ℝ) := norm_fderiv_le_of_lipschitz ℝ (hK v hv)
      have hflow : ‖X l v a - X l v b‖ ≤ B * ‖a - b‖ := by
        simpa only [dist_eq_norm, Real.coe_toNNReal _ (Real.exp_pos _).le] using
          (hX.lipschitzWith_labels hK hl hv).dist_le_mul a b
      have hMdiff : ‖M v a - M v b‖ ≤ (L : ℝ) * (B * ‖a - b‖) := by
        have h := (hL v hv).dist_le_mul (X l v a) (X l v b)
        rw [dist_eq_norm, dist_eq_norm] at h
        exact h.trans (mul_le_mul_of_nonneg_left hflow L.coe_nonneg)
      calc
        ‖rate v‖ ≤ ‖(M v a).comp (err v)‖ + ‖(M v a - M v b).comp (F v b)‖ :=
          norm_add_le _ _
        _ ≤ ‖M v a‖ * ‖err v‖ + ‖M v a - M v b‖ * ‖F v b‖ :=
          add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
        _ ≤ (K : ℝ) * ‖err v‖ + (L : ℝ) * (B * ‖a - b‖) * B :=
          add_le_add (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
            (mul_le_mul hMdiff (hNorm v hv b) (norm_nonneg _) (by positivity [Real.exp_pos]))
        _ = _ := by dsimp only [C]; ring
    have hb := norm_le_gronwallBound_of_norm_deriv_right_le (HasDerivWithinAt.continuousOn hDeriv)
      (fun v hv => (hDeriv v (Ico_subset_Icc_self hv)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hv))
      (show ‖err l‖ ≤ 0 by simp [err, (hF a).1, (hF b).1])
      (fun v hv => hRate v (Ico_subset_Icc_self hv)) u hu
    refine hb.trans <| (gronwallBound_mono le_rfl
      (mul_nonneg hC₀ (norm_nonneg (a - b))) K.coe_nonneg (sub_le_sub_right hu.2 l)).trans_eq ?_
    dsimp only [Q]
    by_cases h : (K : ℝ) = 0 <;> simp only [gronwallBound, h, ↓reduceIte, zero_mul, zero_add] <;> ring
  exact continuousOn_prod_of_continuousOn_lipschitzOnWith' _ (Real.toNNReal Q)
    (fun _ hu => (hLipF _ hu).lipschitzOnWith)
    (fun a _ => HasDerivWithinAt.continuousOn (hF a).2)

end TorusEuler
