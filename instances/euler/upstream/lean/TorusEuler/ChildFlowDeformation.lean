import TorusEuler.FlowHigherVariations
import TorusEuler.PhaseJetBounds
import TorusEuler.PhaseProfileEstimates
import TorusEuler.WaveCompletion

/-! The lifted label–phase flow and the child deformation in Lemma 5.10. -/

open Asymptotics ContinuousLinearMap Filter Set
open scoped ContDiff InnerProductSpace NNReal Topology

namespace TorusEuler

/-- The actual label flow has its joint time–label derivative on the closed slab. -/
theorem IsLabelFlowOn.hasFDerivWithinAt_time_label
    {U : Velocity} {X : ℝ → Velocity} {l r s t : ℝ} {a : Vec3}
    {F : Vec3 →L[ℝ] Vec3} {K : ℝ≥0}
    (hX : IsLabelFlowOn U X (Icc l r))
    (hU : ContinuousOn (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hLip : ∀ u ∈ Icc l r, LipschitzWith K (U u))
    (hs : s ∈ Icc l r) (ht : t ∈ Icc l r)
    (hspace : HasFDerivAt (X s t) F a) :
    HasFDerivWithinAt (Function.uncurry (X s))
      ((toSpanSingleton ℝ (U t (X s t a))).coprod F)
      (Icc l r ×ˢ (univ : Set Vec3)) (t, a) := by
  let S : Set (ℝ × Vec3) := Icc l r ×ˢ univ
  let V : ℝ × Vec3 → Vec3 := fun p => U p.1 (X s p.1 p.2)
  let v : Vec3 := V (t, a)
  have hV : ContinuousOn V S :=
    hU.comp (continuous_fst.continuousOn.prodMk (hX.continuousOn_time_label hLip hs))
      (fun p hp => ⟨hp.1, mem_univ _⟩)
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hV (t, a) ⟨ht, mem_univ a⟩)
    (ε / 2) (half_pos hε)
  have hsp := (isLittleO_iff.mp (hasFDerivAt_iff_isLittleO.mp hspace)) (half_pos hε)
  have hsp' : ∀ᶠ p in 𝓝[S] (t, a),
      ‖X s t p.2 - X s t a - F (p.2 - a)‖ ≤ ε / 2 * ‖p.2 - a‖ := by
    have h := (continuous_snd.continuousWithinAt (s := S) (x := (t, a))).tendsto
    exact h.eventually hsp
  filter_upwards [self_mem_nhdsWithin (s := S),
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (t, a) hδ), hsp'] with p hp hpδ hsp
  have hsub : uIcc t p.1 ⊆ Icc l r := uIcc_subset_Icc ht hp.1
  let Z (u : ℝ) := X s u p.2 - (u - t) • v
  have hZ (u : ℝ) (hu : u ∈ uIcc t p.1) :
      HasDerivWithinAt Z (V (u, p.2) - v) (uIcc t p.1) u := by
    have hlin : HasDerivWithinAt (fun w : ℝ => (w - t) • v) v (uIcc t p.1) u := by
      simpa only [one_smul, id_eq] using ((hasDerivWithinAt_id u _).sub_const t).smul_const v
    exact ((hX.trajectory s hs p.2 u (hsub hu)).mono hsub).sub hlin
  have hZbound (u : ℝ) (hu : u ∈ uIcc t p.1) : ‖V (u, p.2) - v‖ ≤ ε / 2 := by
    have hdist : dist (u, p.2) (t, a) ≤ dist p (t, a) := by
      rw [Prod.dist_eq, Prod.dist_eq]
      exact max_le_max (by
        simpa only [dist_comm t u, dist_comm t p.1] using Real.dist_left_le_of_mem_uIcc hu) le_rfl
    exact (by
      simpa only [dist_eq_norm, v] using hclose (show (u, p.2) ∈ S from
        ⟨hsub hu, mem_univ _⟩) (hdist.trans_lt (Metric.mem_ball.mp hpδ)) : _ < ε / 2).le
  have htime : ‖X s p.1 p.2 - X s t p.2 - (p.1 - t) • v‖ ≤ ε / 2 * ‖p.1 - t‖ := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hZ hZbound
      (convex_uIcc t p.1) left_mem_uIcc right_mem_uIcc
    convert h using 1
    dsimp only [Z]
    rw [sub_self, zero_smul, sub_zero, sub_right_comm]
  change ‖X s p.1 p.2 - X s t a - ((p.1 - t) • v + F (p.2 - a))‖ ≤
    ε * ‖p - (t, a)‖
  have hsplit : X s p.1 p.2 - X s t a - ((p.1 - t) • v + F (p.2 - a)) =
      (X s p.1 p.2 - X s t p.2 - (p.1 - t) • v) +
      (X s t p.2 - X s t a - F (p.2 - a)) := by abel
  rw [hsplit]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ ε / 2 * ‖p.1 - t‖ + ε / 2 * ‖p.2 - a‖ := add_le_add htime hsp
    _ ≤ ε / 2 * ‖p - (t, a)‖ + ε / 2 * ‖p - (t, a)‖ := by
      apply add_le_add <;> apply mul_le_mul_of_nonneg_left _ (half_pos hε).le
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = _ := by ring

/-- For a smooth periodic parent, the joint derivative uses the actual spatial
flow derivative and the parent velocity along the trajectory. -/
theorem IsLabelFlowOn.hasFDerivWithinAt_time_label_of_contDiffOn_periodic
    {U : Velocity} {X : ℝ → Velocity} {l r s t : ℝ} {a : Vec3}
    (hX : IsLabelFlowOn U X (Icc l r)) (hlr : l < r)
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc l r ×ˢ (univ : Set Vec3)))
    (hper : ∀ u ∈ Icc l r, SpatiallyPeriodic (U u))
    (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) :
    HasFDerivWithinAt (Function.uncurry (X s))
      ((toSpanSingleton ℝ (U t (X s t a))).coprod (fderiv ℝ (X s t) a))
      (Icc l r ×ˢ (univ : Set Vec3)) (t, a) := by
  obtain ⟨K, hLip⟩ := exists_lipschitzWith_of_contDiffOn_periodic hlr
    (hU.of_le (by norm_num)) hper
  exact hX.hasFDerivWithinAt_time_label hU.continuousOn hLip hs ht
    (hX.differentiableAt_transition hlr hU hper hs ht a).hasFDerivAt

private noncomputable def labelDivergenceMap : (Vec3 →L[ℝ] Vec3) →L[ℝ] ℝ :=
  ∑ i : Fin 3, (EuclideanSpace.proj i).comp
    (ContinuousLinearMap.apply ℝ Vec3 (EuclideanSpace.single i 1))

private theorem labelDivergenceMap_fderiv (c : Vec3 → Vec3) (a : Vec3) :
    labelDivergenceMap (fderiv ℝ c a) = divergence c a := by
  simp only [labelDivergenceMap, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, divergence]
  rfl

/-- The oscillatory part of the phase velocity in the pulled-back particle field is
the negative zero-mean primitive of its label divergence. The label divergence of
the phase mean vanishes separately. -/
theorem phaseOscillation_longitudinal_of_slope_divergence
    {c : Vec3 → ℝ → Vec3} (hc : ContDiff ℝ ∞ (Function.uncurry c))
    (hper : ∀ a, Function.Periodic (c a) 1) (k a : Vec3)
    (hdiv : ∀ s, divergence (fun b => c b s) a + ⟪k, deriv (c a) s⟫_ℝ = 0) :
    divergence (fun b => phaseMean (c b)) a = 0 ∧
      ∀ s, ⟪k, phaseOscillation (c a) s⟫_ℝ =
        -phasePrimitive (fun σ => divergence (fun b => phaseOscillation (c b) σ) a) s := by
  let A := (continuousMultilinearCurryFin1 ℝ Vec3 Vec3).toLinearIsometry.toContinuousLinearMap
  let L := labelDivergenceMap.comp A
  have hA (v : Vec3 → Vec3) : A (iteratedFDeriv ℝ 1 v a) = fderiv ℝ v a := by
    apply ContinuousLinearMap.ext
    intro w
    change (iteratedFDeriv ℝ 1 v a) (fun _ : Fin 1 => w) = fderiv ℝ v a w
    exact iteratedFDeriv_one_apply (fun _ : Fin 1 => w)
  have hL (v : Vec3 → Vec3) :
      L (iteratedFDeriv ℝ 1 v a) = divergence v a := by
    simp only [L, ContinuousLinearMap.comp_apply, hA, labelDivergenceMap_fderiv]
  have hJ : Continuous (fun s => iteratedFDeriv ℝ 1 (fun b => c b s) a) := by
    let w : ℝ → Vec3 → Vec3 := fun s b => c b s
    have hw : ContDiff ℝ ∞ (Function.uncurry w) :=
      hc.comp (contDiff_snd.prodMk contDiff_fst)
    have hlin : Continuous (fun s => fderiv ℝ (w s) a) :=
      (hw.fderiv (n := 0) (g := fun _ => a) contDiff_const (by simp)).continuous
    have heq : (fun s => iteratedFDeriv ℝ 1 (fun b => c b s) a) =
        fun s => (continuousMultilinearCurryFin1 ℝ Vec3 Vec3).symm (fderiv ℝ (w s) a) := by
      funext s
      apply (continuousMultilinearCurryFin1 ℝ Vec3 Vec3).injective
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact hA _
    rw [heq]
    exact (continuousMultilinearCurryFin1 ℝ Vec3 Vec3).symm.continuous.comp hlin
  let divc : ℝ → ℝ := fun s => divergence (fun b => c b s) a
  have hdivc : Continuous divc := by
    simpa only [divc, Function.comp_def, hL] using L.continuous.comp hJ
  have hcA : ContDiff ℝ ∞ (c a) := hc.comp (contDiff_const.prodMk contDiff_id)
  have hfast (s : ℝ) : HasDerivAt (fun σ => ⟪k, c a σ⟫_ℝ) (-divc s) s := by
    have h := (innerSL ℝ k).hasFDerivAt.comp_hasDerivAt s
      ((hcA.differentiable (by simp) s).hasDerivAt)
    have hs : ⟪k, deriv (c a) s⟫_ℝ = -divc s := eq_neg_of_add_eq_zero_right (hdiv s)
    exact h.congr_deriv hs
  have hdivcMean : phaseMean divc = 0 := by
    have hneg := phaseMean_deriv hfast hdivc.neg
      (fun s => congrArg (innerSL ℝ k) (hper a s))
    rw [phaseMean, intervalIntegral.integral_neg, ← phaseMean, neg_eq_zero] at hneg
    exact hneg
  have hmean : divergence (fun b => phaseMean (c b)) a = phaseMean divc := by
    rw [← hL, iteratedFDeriv_phaseMean hc]
    exact (by
      simpa only [divc, phaseMean, hL] using
        (L.intervalIntegral_comp_comm (hJ.intervalIntegrable 0 1)).symm)
  have hOsc (s : ℝ) : divergence (fun b => phaseOscillation (c b) s) a = divc s := by
    rw [← hL, iteratedFDeriv_phaseOscillation hc, phaseOscillation, map_sub, hL]
    have hzero : L (phaseMean (fun σ => iteratedFDeriv ℝ 1 (fun b => c b σ) a)) = 0 := by
      rw [← iteratedFDeriv_phaseMean hc, hL, hmean, hdivcMean]
    rw [hzero, sub_zero]
  refine ⟨hmean.trans hdivcMean, fun s => ?_⟩
  simp_rw [hOsc]
  have hoscDeriv (σ : ℝ) :
      HasDerivAt (fun z => ⟪k, phaseOscillation (c a) z⟫_ℝ) (-divc σ) σ := by
    simpa only [phaseOscillation, inner_sub_right] using
      (hfast σ).sub_const ⟪k, phaseMean (c a)⟫_ℝ
  exact waveCorrection_longitudinal_of_mean_zero hoscDeriv hdivc
    (hcA.continuous.sub continuous_const) (phaseMean_phaseOscillation hcA.continuous) s

/-- Pulling the divergence of a label–phase profile back by a volume-preserving
parent preserves its combined label and phase divergence. -/
theorem divergence_phase_piola
    {X Y : Vec3 → Vec3} {F : Vec3 → Vec3 →L[ℝ] Vec3}
    {DF : Vec3 →L[ℝ] Vec3 →L[ℝ] Vec3} {G Da : Vec3 →L[ℝ] Vec3}
    {c : Vec3 → ℝ → Vec3} {a k Ds : Vec3} {s : ℝ}
    (hX : HasFDerivAt X (F a) a) (hF : HasFDerivAt F DF a)
    (hsym : ∀ w z : Vec3, DF w z = DF z w)
    (hY : HasFDerivAt Y G (X a)) (hYX : Y ∘ X =ᶠ[𝓝 a] id)
    (hdet : ∀ᶠ b in 𝓝 a, LinearMap.det (F b).toLinearMap = 1)
    (hca : HasFDerivAt (fun b => c b s) Da a) (hcs : HasDerivAt (c a) Ds s) :
    divergence (fun x => F (Y x) (c (Y x) s)) (X a) +
        ⟪G.adjoint k, deriv (fun z => F a (c a z)) s⟫_ℝ =
      divergence (fun b => c b s) a + ⟪k, deriv (c a) s⟫_ℝ := by
  have hFs : HasDerivAt (fun z => F a (c a z)) (F a Ds) s :=
    (F a).hasFDerivAt.comp_hasDerivAt s hcs
  rw [divergence_piola hX hF hsym hY hYX hdet hca,
    hFs.deriv, hcs.deriv,
    ContinuousLinearMap.adjoint_inner_left]
  have hGF : G.comp (F a) = ContinuousLinearMap.id ℝ Vec3 :=
    ((hY.comp a hX).congr_of_eventuallyEq hYX.symm).unique (hasFDerivAt_id a)
  change _ + ⟪k, (G.comp (F a)) Ds⟫_ℝ = _
  rw [hGF, ContinuousLinearMap.id_apply]

/-- The scalar weight conversion for the scaled vector field in Lemma 5.10.
The reciprocal label radius has a fixed polynomial bound in the parent
parameter, and only the phase scale depends directly on the frequency. -/
theorem child_flow_scaled_gradient_le {D freq ell h K A B : ℝ} {a c : ℕ}
    (hD : 1 ≤ D) (hfreq : 1 ≤ freq)
    (hell : ell⁻¹ ≤ D ^ a) (hh : h = freq ^ (-1 / 2 : ℝ))
    (hA₀ : 0 ≤ A) (hB₀ : 0 ≤ B)
    (hA : A ≤ K * D ^ c * freq ^ (-5 / 4 : ℝ))
    (hB : B ≤ K * D ^ c * freq ^ (-5 / 4 : ℝ)) :
    ell⁻¹ * A + h⁻¹ * B ≤ 2 * K * D ^ (a + c) * freq ^ (-3 / 4 : ℝ) := by
  have hf : 0 < freq := zero_lt_one.trans_le hfreq
  have hone : 1 ≤ D ^ a := one_le_pow₀ hD
  have hr : h⁻¹ = freq ^ (1 / 2 : ℝ) := by
    rw [hh, show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hf.le, inv_inv]
  have hell' : ell⁻¹ ≤ D ^ a * freq ^ (1 / 2 : ℝ) :=
    hell.trans ((le_mul_iff_one_le_right (by positivity)).2
      (Real.one_le_rpow hfreq (by norm_num)))
  have hh' : h⁻¹ ≤ D ^ a * freq ^ (1 / 2 : ℝ) := by
    rw [hr]
    exact le_mul_of_one_le_left (Real.rpow_nonneg hf.le _) hone
  have hX : 0 ≤ D ^ a * freq ^ (1 / 2 : ℝ) := by positivity
  calc
    ell⁻¹ * A + h⁻¹ * B ≤
        D ^ a * freq ^ (1 / 2 : ℝ) * (K * D ^ c * freq ^ (-5 / 4 : ℝ)) +
        D ^ a * freq ^ (1 / 2 : ℝ) * (K * D ^ c * freq ^ (-5 / 4 : ℝ)) :=
      add_le_add ((mul_le_mul_of_nonneg_right hell' hA₀).trans
        (mul_le_mul_of_nonneg_left hA hX))
        ((mul_le_mul_of_nonneg_right hh' hB₀).trans (mul_le_mul_of_nonneg_left hB hX))
    _ = 2 * K * D ^ (a + c) * freq ^ (-3 / 4 : ℝ) := by
      rw [pow_add,
        show (-3 / 4 : ℝ) = 1 / 2 + (-5 / 4) by norm_num, Real.rpow_add hf]
      ring

/-- The step smallness assumption converts the scaled derivative bound to any
fixed positive budget by choosing the depth-dependent prefactor large enough. -/
theorem child_flow_scaled_gradient_small {D freq C Γ δ G : ℝ} {p b : ℕ}
    (hD : 1 ≤ D) (hfreq : 1 ≤ freq) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hp : p ≤ b) (hΓ : C ≤ δ * Γ)
    (hsmall : Γ * D ^ b * freq ^ (-1 / 12 : ℝ) ≤ 1)
    (hG : G ≤ C * D ^ p * freq ^ (-3 / 4 : ℝ)) :
    G ≤ δ := by
  have hf : 0 ≤ freq := zero_le_one.trans hfreq
  calc
    G ≤ C * D ^ p * freq ^ (-3 / 4 : ℝ) := hG
    _ ≤ C * D ^ b * freq ^ (-1 / 12 : ℝ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hp) hC)
        (Real.rpow_le_rpow_of_exponent_le hfreq (by norm_num))
        (Real.rpow_nonneg hf _) (by positivity)
    _ ≤ δ * Γ * D ^ b * freq ^ (-1 / 12 : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΓ (by positivity)) (by positivity)
    _ = δ * (Γ * D ^ b * freq ^ (-1 / 12 : ℝ)) := by ring
    _ ≤ δ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsmall hδ

/-- The last scalar estimate of Lemma 5.10, including the parent coframe factor.
The same bound applies to the forward and inverse derivatives. -/
theorem child_flow_deformation_scale_le {D freq ell h k B K Γ : ℝ} {a c b : ℕ}
    (hD : 1 ≤ D) (hfreq : 1 ≤ freq) (hK : 0 ≤ K) (hB₀ : 0 ≤ B)
    (hell : ell⁻¹ ≤ D ^ a) (hh : h = freq ^ (-1 / 2 : ℝ))
    (hk : k ≤ D * freq) (hB : B ≤ K * D ^ c * freq ^ (-5 / 4 : ℝ))
    (hb : max a 1 + c + 1 ≤ b) (hΓ : 1 + 2 * K ≤ Γ) :
    D * (1 + (ell⁻¹ + k * h⁻¹) * B) ≤ Γ * D ^ b * freq ^ (1 / 4 : ℝ) := by
  have hf : 0 < freq := zero_lt_one.trans_le hfreq
  have hm₁ : a ≤ max a 1 := le_max_left _ _
  have hm₂ : 1 ≤ max a 1 := le_max_right _ _
  have hpow : D ≤ D ^ max a 1 := by
    simpa only [pow_one] using pow_le_pow_right₀ hD hm₂
  have hi : h⁻¹ = freq ^ (1 / 2 : ℝ) := by
    rw [hh, show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hf.le, inv_inv]
  have hBase₁ : 1 ≤ freq ^ (3 / 2 : ℝ) := Real.one_le_rpow hfreq (by norm_num)
  have hBase₂ : 1 ≤ freq ^ (1 / 4 : ℝ) := Real.one_le_rpow hfreq (by norm_num)
  have hlabel : ell⁻¹ ≤ D ^ max a 1 * freq ^ (3 / 2 : ℝ) :=
    (hell.trans (pow_le_pow_right₀ hD hm₁)).trans
      (le_mul_of_one_le_right (by positivity) hBase₁)
  have hphase : k * h⁻¹ ≤ D ^ max a 1 * freq ^ (3 / 2 : ℝ) := by
    rw [hi]
    calc
      k * freq ^ (1 / 2 : ℝ) ≤ (D ^ max a 1 * freq) * freq ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right
          (hk.trans (mul_le_mul_of_nonneg_right hpow hf.le)) (by positivity)
      _ = _ := by
        rw [mul_assoc]
        nth_rw 1 [← Real.rpow_one freq]
        rw [← Real.rpow_add hf]
        norm_num
  have hsum : ell⁻¹ + k * h⁻¹ ≤ 2 * (D ^ max a 1 * freq ^ (3 / 2 : ℝ)) := by
    simpa only [two_mul] using add_le_add hlabel hphase
  have hscaled : (ell⁻¹ + k * h⁻¹) * B ≤
      2 * K * D ^ (max a 1 + c) * freq ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ 2 * (D ^ max a 1 * freq ^ (3 / 2 : ℝ)) *
          (K * D ^ c * freq ^ (-5 / 4 : ℝ)) :=
        (mul_le_mul_of_nonneg_right hsum hB₀).trans
          (mul_le_mul_of_nonneg_left hB (by positivity))
      _ = _ := by
        rw [pow_add,
          show (1 / 4 : ℝ) = 3 / 2 + (-5 / 4) by norm_num, Real.rpow_add hf]
        ring
  have hpow₁ : 1 ≤ D ^ (max a 1 + c) * freq ^ (1 / 4 : ℝ) :=
    (one_le_pow₀ hD).trans (le_mul_of_one_le_right (by positivity) hBase₂)
  calc
    D * (1 + (ell⁻¹ + k * h⁻¹) * B) ≤
        D * ((D ^ (max a 1 + c) * freq ^ (1 / 4 : ℝ)) +
          2 * K * D ^ (max a 1 + c) * freq ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hpow₁ hscaled) (by positivity)
    _ = (1 + 2 * K) * D ^ (max a 1 + c + 1) * freq ^ (1 / 4 : ℝ) := by
      rw [pow_succ]
      ring
    _ ≤ Γ * D ^ b * freq ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hΓ (pow_le_pow_right₀ hD hb) (by positivity)
          ((by positivity : 0 ≤ 1 + 2 * K).trans hΓ)) (by positivity)

/-- The phase primitive costs the inverse label scale on the oscillation.
The factor of the wave number is spent only on the smaller phase mean. -/
theorem child_flow_pullback_profile_scales_le
    {D freq ell h k K : ℝ} {a p : ℕ}
    (hD : 1 ≤ D) (hfreq : 1 ≤ freq) (hell : 0 < ell) (hK : 0 ≤ K)
    (hellSize : ell⁻¹ ≤ D ^ a) (hh : h = freq ^ (-1 / 2 : ℝ))
    (hk : k ≤ D * freq) :
    let osc := K * D ^ p * freq ^ (-5 / 4 : ℝ)
    let avg := K * D ^ p * freq ^ (-5 / 2 : ℝ)
    let B := 10 * K * D ^ (max a 1 + p) * freq ^ (-5 / 4 : ℝ)
    osc + avg ≤ B ∧ (2 + h) * (3 * ell⁻¹ * osc) + k * avg ≤ B := by
  dsimp only
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hf := zero_lt_one.trans_le hfreq
  have hhi : h ≤ 1 := by
    rw [hh]
    exact Real.rpow_le_one_of_one_le_of_nonpos hfreq (by norm_num)
  have hOsc : 0 ≤ K * D ^ p * freq ^ (-5 / 4 : ℝ) := by positivity
  have hAvg : 0 ≤ K * D ^ p * freq ^ (-5 / 2 : ℝ) := by positivity
  have hv : K * D ^ p * freq ^ (-5 / 2 : ℝ) ≤ K * D ^ p * freq ^ (-5 / 4 : ℝ) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hfreq (by norm_num))
      (by positivity)
  have hpow : D ^ p ≤ D ^ (max a 1 + p) := pow_le_pow_right₀ hD (by omega)
  have hm : K * D ^ p * freq ^ (-5 / 4 : ℝ) ≤
      K * D ^ (max a 1 + p) * freq ^ (-5 / 4 : ℝ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hK) (Real.rpow_nonneg hf.le _)
  constructor
  · calc
      _ ≤ 2 * (K * D ^ (max a 1 + p) * freq ^ (-5 / 4 : ℝ)) := by linarith
      _ ≤ _ := by
        have hnonneg : 0 ≤ K * D ^ (max a 1 + p) * freq ^ (-5 / 4 : ℝ) := by positivity
        linarith only [hnonneg]
  · have he : ell⁻¹ ≤ D ^ max a 1 := hellSize.trans
      (pow_le_pow_right₀ hD (le_max_left _ _))
    have hOsc' : (2 + h) * (3 * ell⁻¹ * (K * D ^ p * freq ^ (-5 / 4 : ℝ))) ≤
        9 * (K * D ^ (max a 1 + p) * freq ^ (-5 / 4 : ℝ)) := by
      calc
        _ ≤ 3 * (3 * D ^ max a 1 * (K * D ^ p * freq ^ (-5 / 4 : ℝ))) :=
          mul_le_mul (by linarith)
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num)) hOsc)
            (by positivity) (by norm_num)
        _ = _ := by rw [pow_add]; ring
    have hMean : k * (K * D ^ p * freq ^ (-5 / 2 : ℝ)) ≤
        K * D ^ (max a 1 + p) * freq ^ (-5 / 4 : ℝ) := by
      have hd : D ≤ D ^ max a 1 := by
        simpa only [pow_one] using pow_le_pow_right₀ hD (le_max_right a 1)
      calc
        _ ≤ (D ^ max a 1 * freq) * (K * D ^ p * freq ^ (-5 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (hk.trans (mul_le_mul_of_nonneg_right hd hf.le)) hAvg
        _ = K * D ^ (max a 1 + p) * freq ^ (-3 / 2 : ℝ) := by
          rw [pow_add, show (-3 / 2 : ℝ) = 1 + (-5 / 2) by norm_num, Real.rpow_add hf,
            Real.rpow_one]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hfreq (by norm_num)) (by positivity)
    linarith only [hOsc', hMean]

/-- Step smallness also absorbs the loss in the next parent's coframe bound. -/
theorem child_flow_deformation_scale_le_frequency {freq Cstep : ℝ}
    (hfreq : 1 ≤ freq) (hsmall : Cstep * freq ^ (-1 / 12 : ℝ) ≤ 1) :
    Cstep * freq ^ (1 / 4 : ℝ) ≤ freq := by
  have hf : 0 < freq := zero_lt_one.trans_le hfreq
  calc
    Cstep * freq ^ (1 / 4 : ℝ) =
        (Cstep * freq ^ (-1 / 12 : ℝ)) * freq ^ (1 / 3 : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add hf]
      norm_num
    _ ≤ freq ^ (1 / 3 : ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hsmall
        (Real.rpow_nonneg hf.le (1 / 3 : ℝ))
    _ ≤ freq := by
      nth_rw 2 [← Real.rpow_one freq]
      exact Real.rpow_le_rpow_of_exponent_le hfreq (by norm_num)

private theorem norm_fderiv_prod_le_of_partials
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} {x : E} {s A B : ℝ}
    (hf : DifferentiableAt ℝ f (x, s))
    (hx : ‖fderiv ℝ (fun y => f (y, s)) x‖ ≤ A)
    (hs : ‖deriv (fun u => f (x, u)) s‖ ≤ B) :
    ‖fderiv ℝ f (x, s)‖ ≤ A + B := by
  let D := fderiv ℝ f (x, s)
  have hA : 0 ≤ A := (norm_nonneg _).trans hx
  have hB : 0 ≤ B := (norm_nonneg _).trans hs
  have hleft : HasFDerivAt (fun y => f (y, s)) (D.comp (inl ℝ E ℝ)) x :=
    hf.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x s)
  have hright : HasDerivAt (fun u => f (x, u)) (D (0, 1)) s :=
    (hf.hasFDerivAt.comp s (hasFDerivAt_prodMk_right x s)).hasDerivAt
  rw [hleft.fderiv] at hx
  rw [hright.deriv] at hs
  apply D.opNorm_le_bound (add_nonneg hA hB)
  intro v
  have hv : v = (v.1, 0) + v.2 • ((0, 1) : E × ℝ) := by
    simp
  calc
    ‖D v‖ ≤ ‖D (v.1, 0)‖ + ‖v.2 • D (0, 1)‖ := by
      conv_lhs => rw [hv, map_add, map_smul]
      exact norm_add_le _ _
    _ ≤ A * ‖v.1‖ + B * ‖v.2‖ := by
      rw [norm_smul, mul_comm B]
      apply add_le_add
      · simpa only [comp_apply, inl_apply] using (D.comp (inl ℝ E ℝ)).le_of_opNorm_le hx v.1
      · exact mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    _ ≤ (A + B) * ‖v‖ := by
      rw [add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hA)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hB)

private theorem norm_fderiv_prod_left_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} {x : E} {s M : ℝ}
    (hf : DifferentiableAt ℝ f (x, s))
    (hD : ‖fderiv ℝ f (x, s)‖ ≤ M) :
    ‖fderiv ℝ (fun y => f (y, s)) x‖ ≤ M := by
  have h : HasFDerivAt (fun y => f (y, s))
      ((fderiv ℝ f (x, s)).comp (inl ℝ E ℝ)) x :=
    hf.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x s)
  rw [h.fderiv]
  apply opNorm_le_bound _ ((norm_nonneg _).trans hD)
  intro u
  simpa only [comp_apply, inl_apply, Prod.norm_def, norm_zero,
    max_eq_left (norm_nonneg _)] using
    (fderiv ℝ f (x, s)).le_of_opNorm_le hD (inl ℝ E ℝ u)

/-- A periodic phase primitive costs at most twice the bound for the label
derivative. After the phase rescaling, its phase derivative costs the factor
h, because differentiating the primitive recovers its input. -/
theorem phaseJetBound_scaled_phasePrimitive {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : Vec3 → ℝ → E} {ell h M : ℝ} (hh : 0 < h)
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    (hper : ∀ a, Function.Periodic (g a) 1) (hmean : ∀ a, phaseMean (g a) = 0)
    (hprim : Differentiable ℝ (scaledPhaseProfile ell h (fun a => phasePrimitive (g a))))
    (hG : PhaseJetBound 1 M (scaledPhaseProfile ell h g)) :
    PhaseJetBound 1 ((2 + h) * M)
      (scaledPhaseProfile ell h (fun a => phasePrimitive (g a))) := by
  let g₁ (a : Vec3) (s : ℝ) := g (ell • a) s
  let G := scaledPhaseProfile ell h g
  let U := scaledPhaseProfile ell h (fun a => phasePrimitive (g a))
  have hg₁ : ContDiff ℝ ∞ (Function.uncurry g₁) :=
    hg.comp ((contDiff_fst.const_smul ell).prodMk contDiff_snd)
  have hG₀ (p : Vec3 × ℝ) : ‖G p‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_zero] using hG 0 (by decide) p
  have hG₁ (p : Vec3 × ℝ) : ‖fderiv ℝ G p‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_one] using hG 1 le_rfl p
  have hM : 0 ≤ M := (norm_nonneg _).trans (hG₀ (0, 0))
  have hcomp (a : Vec3) (s : ℝ) : G (a, s / h) = g₁ a s := by
    change g (ell • a) (h * (s / h)) = _
    field_simp
    rfl
  have hbase (a : Vec3) (s : ℝ) : ‖g₁ a s‖ ≤ M := hcomp a s ▸ hG₀ (a, s / h)
  have hlabel (a : Vec3) (s : ℝ) : ‖fderiv ℝ (fun b => g₁ b s) a‖ ≤ M := by
    have heq : (fun b => G (b, s / h)) = fun b => g₁ b s := funext fun b => hcomp b s
    rw [← heq]
    exact norm_fderiv_prod_left_le ((hg.comp (labelPhaseScale ell h).contDiff).differentiable
      (by simp) (a, s / h)) (hG₁ (a, s / h))
  have hmean₁ (a : Vec3) : phaseMean (g₁ a) = 0 := hmean (ell • a)
  have hcont (a : Vec3) : Continuous (g₁ a) :=
    hg₁.continuous.comp (continuous_const.prodMk continuous_id)
  intro j hj p
  obtain ⟨a, s⟩ := p
  have hcases : j = 0 ∨ j = 1 := by omega
  rcases hcases with rfl | rfl
  · rw [norm_iteratedFDeriv_zero]
    change ‖phasePrimitive (g₁ a) (h * s)‖ ≤ _
    exact (norm_phasePrimitive_le (hcont a) (hper (ell • a)) (hmean₁ a)
      (fun σ _ => hbase a σ) (h * s)).trans (by nlinarith)
  · rw [norm_iteratedFDeriv_one]
    change ‖fderiv ℝ U (a, s)‖ ≤ _
    have hDx : ‖fderiv ℝ (fun b => U (b, s)) a‖ ≤ 2 * M := by
      let L := ContinuousLinearMap.id ℝ (Vec3 [×1]→L[ℝ] E)
      have hJ (σ : ℝ) : ‖L (mixedPhaseJet g₁ 1 0 a σ)‖ ≤ M := by
        simpa only [L, id_apply, mixedPhaseJet, iteratedDeriv_zero, norm_iteratedFDeriv_one]
          using hlabel a σ
      have hb := (norm_map_mixedPhaseJet_phaseOps_le hg₁ (fun b => hper (ell • b))
        1 0 a (h * s) L hJ).2.2 hmean₁
      simpa only [L, id_apply, mixedPhaseJet, iteratedDeriv_zero, norm_iteratedFDeriv_one,
        U, scaledPhaseProfile, Function.comp_def, Function.uncurry, labelPhaseScale_apply, g₁]
        using hb
    have hDs : ‖deriv (fun u => U (a, u)) s‖ ≤ h * M := by
      have hderiv : HasDerivAt (fun u => U (a, u)) (h • g₁ a (h * s)) s :=
        (hasDerivAt_phasePrimitive (hcont a) (h * s)).scomp s
          (by simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul h)
      rw [hderiv.deriv, norm_smul, Real.norm_of_nonneg hh.le]
      exact mul_le_mul_of_nonneg_left (hbase a (h * s)) hh.le
    exact (norm_fderiv_prod_le_of_partials (hprim (a, s)) hDx hDs).trans_eq (by ring)

private noncomputable def scaledLabelDivergenceMap :
    ((Vec3 × ℝ) →L[ℝ] Vec3) →L[ℝ] ℝ :=
  ∑ i : Fin 3, (EuclideanSpace.proj i).comp
    (ContinuousLinearMap.apply ℝ Vec3 (coordinateDirection i, (0 : ℝ)))

private theorem scaledLabelDivergenceMap_apply (D : (Vec3 × ℝ) →L[ℝ] Vec3) :
    scaledLabelDivergenceMap D = ∑ i : Fin 3, (D (coordinateDirection i, 0)) i := by
  simp only [scaledLabelDivergenceMap, sum_apply, comp_apply, apply_apply]
  rfl

private theorem norm_scaledLabelDivergenceMap_le : ‖scaledLabelDivergenceMap‖ ≤ 3 := by
  apply opNorm_le_bound _ (by norm_num)
  intro D
  rw [scaledLabelDivergenceMap_apply]
  calc
    _ ≤ ∑ i : Fin 3, ‖(D (coordinateDirection i, 0)) i‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, ‖D‖ := by
      refine Finset.sum_le_sum fun i _ => ?_
      refine (PiLp.norm_apply_le (D (coordinateDirection i, 0)) i).trans ?_
      have hi : ‖(coordinateDirection i, (0 : ℝ))‖ = 1 := by
        simp [coordinateDirection, EuclideanSpace.single, PiLp.norm_single, Prod.norm_def]
      simpa only [hi, mul_one] using D.le_opNorm (coordinateDirection i, 0)
    _ = _ := by simp

/-- A label divergence costs one inverse envelope scale and one derivative of
the scaled profile. The three coordinate traces contribute the factor three. -/
theorem phaseJetBound_scaled_labelDivergence {c : Vec3 → ℝ → Vec3} {ell h M : ℝ}
    (hell : 0 < ell) (hc : ContDiff ℝ ∞ (Function.uncurry c))
    (hC : PhaseJetBound 2 M (scaledPhaseProfile ell h c)) :
    PhaseJetBound 1 (3 * ell⁻¹ * M)
      (scaledPhaseProfile ell h (fun a s => divergence (fun b => c b s) a)) := by
  let C := scaledPhaseProfile ell h c
  let L := ell⁻¹ • scaledLabelDivergenceMap
  have hL : ‖L‖ ≤ 3 * ell⁻¹ := by
    apply opNorm_le_bound _ (by positivity)
    intro D
    change ‖ell⁻¹ • scaledLabelDivergenceMap D‖ ≤ (3 * ell⁻¹) * ‖D‖
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hell.le), mul_comm 3]
    exact (mul_le_mul_of_nonneg_left
      (scaledLabelDivergenceMap.le_of_opNorm_le norm_scaledLabelDivergenceMap_le D)
      (inv_nonneg.mpr hell.le)).trans_eq (by ring)
  have hCs : ContDiff ℝ ∞ C := hc.comp (labelPhaseScale ell h).contDiff
  have hD (j : ℕ) (hj : j ≤ 1) (p : Vec3 × ℝ) :
      ‖iteratedFDeriv ℝ j (fderiv ℝ C) p‖ ≤ M := by
    rw [norm_iteratedFDeriv_fderiv]
    exact hC (j + 1) (by omega) p
  have heq :
      scaledPhaseProfile ell h (fun a s => divergence (fun b => c b s) a) =
        L ∘ fderiv ℝ C := by
    funext p
    obtain ⟨a, s⟩ := p
    have hCd : HasFDerivAt C (fderiv ℝ C (a, s)) (a, s) :=
      (hCs.differentiable (by simp) (a, s)).hasFDerivAt
    have hleft : HasFDerivAt (fun b => C (b, s))
        ((fderiv ℝ C (a, s)).comp (inl ℝ Vec3 ℝ)) a := by
      have hd := hCd.comp (f := fun b : Vec3 => (b, s)) a (hasFDerivAt_prodMk_left a s)
      exact hd
    have hlabel : ContDiff ℝ ∞ (fun b => c b (h * s)) :=
      hc.comp (contDiff_id.prodMk contDiff_const)
    have hscaled : HasFDerivAt (fun b => C (b, s))
        ((fderiv ℝ (fun b => c b (h * s)) (ell • a)).comp
          (ell • ContinuousLinearMap.id ℝ Vec3)) a :=
      (hlabel.differentiable (by simp) (ell • a)).hasFDerivAt.comp a
        (ell • ContinuousLinearMap.id ℝ Vec3).hasFDerivAt
    have hd := hleft.unique hscaled
    have hei (i : Fin 3) :
        fderiv ℝ C (a, s) (coordinateDirection i, 0) =
          ell • fderiv ℝ (fun b => c b (h * s)) (ell • a) (coordinateDirection i) := by
      simpa only [comp_apply, inl_apply, smul_apply, id_apply, map_smul] using
        congrArg (fun D : Vec3 →L[ℝ] Vec3 => D (coordinateDirection i)) hd
    change (∑ i : Fin 3, (fderiv ℝ (fun b => c b (h * s)) (ell • a)
      (coordinateDirection i)) i) = L (fderiv ℝ C (a, s))
    simp only [L, smul_apply, scaledLabelDivergenceMap_apply, hei, PiLp.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hell.ne', one_mul]
  rw [heq]
  intro j hj p
  have hcases : j = 0 ∨ j = 1 := by omega
  rcases hcases with rfl | rfl
  · rw [norm_iteratedFDeriv_zero]
    refine (L.le_opNorm _).trans (mul_le_mul hL ?_ (norm_nonneg _) (by positivity))
    simpa only [norm_iteratedFDeriv_zero] using hD 0 (by decide) p
  · rw [norm_iteratedFDeriv_one]
    have hdiff := (hCs.fderiv_right (m := 1) (by simp)).differentiable (by simp) p
    rw [(L.hasFDerivAt.comp p hdiff.hasFDerivAt).fderiv]
    refine (L.opNorm_comp_le _).trans (mul_le_mul hL ?_ (norm_nonneg _) (by positivity))
    simpa only [norm_iteratedFDeriv_one] using hD 1 le_rfl p

/-- The combined label–phase divergence removes the large phase covector from
the oscillatory part of the scaled first derivative of the phase velocity.
Only the phase mean pays the full norm of the covector. -/
theorem phaseJetBound_scaled_longitudinal_of_slope_divergence
    {c : Vec3 → ℝ → Vec3} {ell h Mosc Mmean : ℝ} (hell : 0 < ell) (hh : 0 < h)
    (hc : ContDiff ℝ ∞ (Function.uncurry c)) (hper : ∀ a, Function.Periodic (c a) 1)
    (k : Vec3)
    (hdiv : ∀ a s, divergence (fun b => c b s) a + ⟪k, deriv (c a) s⟫_ℝ = 0)
    (hosc : PhaseJetBound 2 Mosc
      (scaledPhaseProfile ell h (fun a => phaseOscillation (c a))))
    (hmean : PhaseJetBound 1 Mmean
      (scaledPhaseProfile ell h (fun a _ => phaseMean (c a)))) :
    PhaseJetBound 1 ((2 + h) * (3 * ell⁻¹ * Mosc) + ‖k‖ * Mmean)
      (scaledPhaseProfile ell h (fun a s => ⟪k, c a s⟫_ℝ)) := by
  let Cosc (a : Vec3) := phaseOscillation (c a)
  let Cm (a : Vec3) (_ : ℝ) := phaseMean (c a)
  let g (a : Vec3) (s : ℝ) := divergence (fun b => Cosc b s) a
  let H (a : Vec3) := phasePrimitive (g a)
  have hCm : ContDiff ℝ ∞ (Function.uncurry Cm) :=
    (contDiff_and_iteratedFDeriv_phaseInterval hc 0 1).1.comp contDiff_fst
  have hCosc : ContDiff ℝ ∞ (Function.uncurry Cosc) := hc.sub hCm
  have hg : ContDiff ℝ ∞ (Function.uncurry g) := by
    let f (p : Vec3 × ℝ) (b : Vec3) := Cosc b p.2
    have hf : ContDiff ℝ ∞ (Function.uncurry f) :=
      hCosc.comp (contDiff_snd.prodMk contDiff_fst.snd)
    have hfD : ContDiff ℝ ∞ (fun p : Vec3 × ℝ => fderiv ℝ (f p) p.1) :=
      hf.fderiv contDiff_fst (by simp)
    change ContDiff ℝ ∞ (fun p : Vec3 × ℝ => divergence (fun b => Cosc b p.2) p.1)
    simpa only [Function.comp_def, f, labelDivergenceMap_fderiv]
      using labelDivergenceMap.contDiff.comp hfD
  have hCper (a : Vec3) : Function.Periodic (Cosc a) 1 :=
    periodic_phaseOscillation (hper a)
  have hgper (a : Vec3) : Function.Periodic (g a) 1 := by
    intro s
    exact congrArg (fun f => divergence f a) (funext fun b => hCper b s)
  have hH (a : Vec3) (s : ℝ) : H a s = -⟪k, Cosc a s⟫_ℝ := by
    have hEq := (phaseOscillation_longitudinal_of_slope_divergence hc hper k a (hdiv a)).2 s
    change ⟪k, Cosc a s⟫_ℝ = -H a s at hEq
    rw [hEq, neg_neg]
  have hgzero (a : Vec3) : phaseMean (g a) = 0 := by
    have hgC : Continuous (g a) := hg.continuous.comp (continuous_const.prodMk continuous_id)
    have hHper : Function.Periodic (H a) 1 := by
      intro s
      simp only [hH, hCper a s]
    exact phaseMean_deriv (hasDerivAt_phasePrimitive hgC) hgC hHper
  have hHs : ContDiff ℝ ∞ (scaledPhaseProfile ell h H) := by
    have hEq : Function.uncurry H = fun p : Vec3 × ℝ => -⟪k, Cosc p.1 p.2⟫_ℝ :=
      funext fun p => hH p.1 p.2
    have hreg : ContDiff ℝ ∞ (Function.uncurry H) := by
      rw [hEq]
      exact ((innerSL ℝ k).contDiff.comp hCosc).neg
    exact hreg.comp (labelPhaseScale ell h).contDiff
  let Mf := scaledPhaseProfile ell h Cm
  let Hf := scaledPhaseProfile ell h H
  let L := innerSL ℝ k
  let G := (2 + h) * (3 * ell⁻¹ * Mosc)
  have hB : PhaseJetBound 1 G Hf :=
    phaseJetBound_scaled_phasePrimitive hh hg hgper hgzero (hHs.differentiable (by simp))
      (phaseJetBound_scaled_labelDivergence hell hCosc hosc)
  have hMs : ContDiff ℝ ∞ Mf := hCm.comp (labelPhaseScale ell h).contDiff
  have hL : ‖L‖ ≤ ‖k‖ := by rw [show L = innerSL ℝ k from rfl, innerSL_apply_norm]
  have heq : scaledPhaseProfile ell h (fun a s => ⟪k, c a s⟫_ℝ) =
      fun p => L (Mf p) - Hf p := by
    funext p
    obtain ⟨a, s⟩ := p
    change ⟪k, c (ell • a) (h * s)⟫_ℝ =
      ⟪k, Cm (ell • a) (h * s)⟫_ℝ - H (ell • a) (h * s)
    rw [hH, sub_neg_eq_add]
    simp only [Cm, Cosc, phaseOscillation, inner_sub_right]
    ring
  rw [heq]
  intro j hj p
  have hcases : j = 0 ∨ j = 1 := by omega
  rcases hcases with rfl | rfl
  · rw [norm_iteratedFDeriv_zero]
    have hM := hmean 0 (by decide) p
    have hH := hB 0 (by decide) p
    rw [norm_iteratedFDeriv_zero] at hM hH
    exact (norm_sub_le _ _).trans <| (add_le_add
      ((L.le_opNorm _).trans (mul_le_mul hL hM (norm_nonneg _) (norm_nonneg _))) hH).trans_eq
      (add_comm _ _)
  · rw [norm_iteratedFDeriv_one]
    have hMd : HasFDerivAt Mf (fderiv ℝ Mf p) p :=
      (hMs.differentiable (by simp) p).hasFDerivAt
    have hHd : HasFDerivAt Hf (fderiv ℝ Hf p) p :=
      (hHs.differentiable (by simp) p).hasFDerivAt
    have hderiv : HasFDerivAt (fun p => L (Mf p) - Hf p)
        (L.comp (fderiv ℝ Mf p) - fderiv ℝ Hf p) p :=
      (L.hasFDerivAt.comp p hMd).sub hHd
    rw [hderiv.fderiv]
    have hM := hmean 1 le_rfl p
    have hH := hB 1 le_rfl p
    rw [norm_iteratedFDeriv_one] at hM hH
    exact (norm_sub_le _ _).trans <| (add_le_add
      ((L.opNorm_comp_le _).trans (mul_le_mul hL hM (norm_nonneg _) (norm_nonneg _))) hH).trans_eq
      (add_comm _ _)

section ScaledFlow

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem scaledFlow_pathNorm_le_exp_of_left
    {x d : ℝ → E} {a b K : ℝ}
    (hx : ∀ t ∈ Icc a b, HasDerivWithinAt x (d t) (Icc a b) t)
    (hd : ∀ t ∈ Icc a b, ‖d t‖ ≤ K * ‖x t‖) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖x t‖ ≤ ‖x a‖ * Real.exp (K * (t - a)) := by
  rw [← gronwallBound_ε0]
  exact norm_le_gronwallBound_of_norm_deriv_right_le (HasDerivWithinAt.continuousOn hx)
    (fun u hu => (hx u (Ico_subset_Icc_self hu)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hu)) le_rfl
    (fun u hu => by simpa only [add_zero] using hd u (Ico_subset_Icc_self hu)) t ht

private theorem scaledFlow_pathNorm_le_exp
    {x d : ℝ → E} {l r s t K : ℝ}
    (hx : ∀ u ∈ Icc l r, HasDerivWithinAt x (d u) (Icc l r) u)
    (hd : ∀ u ∈ Icc l r, ‖d u‖ ≤ K * ‖x u‖)
    (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) :
    ‖x t‖ ≤ ‖x s‖ * Real.exp (K * |t - s|) := by
  rcases le_total s t with hst | hts
  · have hsub : Icc s r ⊆ Icc l r := Icc_subset_Icc_left hs.1
    rw [abs_of_nonneg (sub_nonneg.mpr hst)]
    exact scaledFlow_pathNorm_le_exp_of_left
      (fun u hu => (hx u (hsub hu)).mono hsub) (fun u hu => hd u (hsub hu)) ⟨hst, ht.2⟩
  · have hmap : MapsTo (fun u : ℝ => -u) (Icc (-s) (-l)) (Icc l r) := by
      intro u hu
      exact ⟨le_neg.mp hu.2, (neg_le.mp hu.1).trans hs.2⟩
    have hrev (u : ℝ) (hu : u ∈ Icc (-s) (-l)) :
        HasDerivWithinAt (fun v => x (-v)) (-d (-u)) (Icc (-s) (-l)) u := by
      simpa only [Function.comp_def, neg_one_smul] using
        (hx (-u) (hmap hu)).scomp u (hasDerivWithinAt_neg u _) hmap
    have hnorm (u : ℝ) (hu : u ∈ Icc (-s) (-l)) :
        ‖-d (-u)‖ ≤ K * ‖x (-u)‖ := by
      simpa only [norm_neg] using hd (-u) (hmap hu)
    rw [abs_of_nonpos (sub_nonpos.mpr hts), neg_sub]
    have harg : -t - -s = s - t := by ring
    simpa only [neg_neg, harg] using scaledFlow_pathNorm_le_exp_of_left hrev hnorm
      (t := -t) ⟨neg_le_neg hts, neg_le_neg ht.1⟩

private theorem scaledFlow_exp_le_two {K w : ℝ}
    (hKw : K * w ≤ 1 / 2) : Real.exp (K * w) ≤ 2 := by
  refine (Real.exp_le_exp.mpr hKw).trans ?_
  exact (Real.exp_le_two_add_div_two_sub (x := 1 / 2) (by norm_num) (by norm_num)).trans
    (by norm_num)

/-- On a slab with small scaled velocity gradient, a two-time flow has
Lipschitz constant at most two for every transition. Its projected
displacement has Lipschitz constant controlled by the Lipschitz bound of the
projected velocity and the elapsed time. The estimates hold backward in time. -/
theorem scaledFlow_lipschitz_and_displacement_le
    {F : ℝ → E → E} {Φ : ℝ → ℝ → E → E} {l r s t : ℝ} {K M : ℝ≥0}
    (π : E →L[ℝ] G)
    (hInit : ∀ u ∈ Icc l r, ∀ z, Φ u u z = z)
    (hTraj : ∀ u ∈ Icc l r, ∀ z v, v ∈ Icc l r →
      HasDerivWithinAt (fun w => Φ u w z) (F v (Φ u v z)) (Icc l r) v)
    (hF : ∀ u ∈ Icc l r, LipschitzWith K (F u))
    (hProj : ∀ u ∈ Icc l r, LipschitzWith M (π ∘ F u))
    (hSmall : (K : ℝ) * (r - l) ≤ 1 / 2)
    (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) :
    LipschitzWith 2 (Φ s t) ∧
      LipschitzWith (2 * M * Real.toNNReal |t - s|)
        (fun z => π (Φ s t z) - π z) := by
  have hTwo (u : ℝ) (hu : u ∈ Icc l r) (x y : E) :
      ‖Φ s u x - Φ s u y‖ ≤ 2 * ‖x - y‖ := by
    have htime : |u - s| ≤ r - l := abs_le.mpr
      ⟨by linarith [hs.2, hu.1], by linarith [hs.1, hu.2]⟩
    have hExp : Real.exp ((K : ℝ) * |u - s|) ≤ 2 :=
      scaledFlow_exp_le_two ((mul_le_mul_of_nonneg_left htime K.coe_nonneg).trans hSmall)
    have h := scaledFlow_pathNorm_le_exp
      (fun v hv => (hTraj s hs x v hv).sub (hTraj s hs y v hv))
      (fun v hv => by simpa only [dist_eq_norm, Pi.sub_apply] using
        (hF v hv).dist_le_mul (Φ s v x) (Φ s v y)) hs hu
    simpa only [Pi.sub_apply, hInit s hs x, hInit s hs y, mul_comm ‖x - y‖ (2 : ℝ)] using
      h.trans (mul_le_mul_of_nonneg_left hExp (norm_nonneg (Φ s s x - Φ s s y)))
  constructor
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simpa only [dist_eq_norm, NNReal.coe_ofNat] using hTwo t ht x y
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    let d (v : ℝ) := π (Φ s v x) - π (Φ s v y)
    let d' (v : ℝ) := π (F v (Φ s v x)) - π (F v (Φ s v y))
    have hDeriv (v : ℝ) (hv : v ∈ Icc l r) : HasDerivWithinAt d (d' v) (Icc l r) v :=
      (π.hasFDerivAt.comp_hasDerivWithinAt v (hTraj s hs x v hv)).sub
        (π.hasFDerivAt.comp_hasDerivWithinAt v (hTraj s hs y v hv))
    have hRate (v : ℝ) (hv : v ∈ Icc l r) : ‖d' v‖ ≤ 2 * (M : ℝ) * ‖x - y‖ := by
      have hProjDiff : ‖d' v‖ ≤ (M : ℝ) * ‖Φ s v x - Φ s v y‖ := by
        simpa only [d', Function.comp_apply, dist_eq_norm] using
          (hProj v hv).dist_le_mul (Φ s v x) (Φ s v y)
      exact hProjDiff.trans ((mul_le_mul_of_nonneg_left (hTwo v hv x y) M.coe_nonneg).trans_eq
        (by ring))
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hDeriv hRate
      (convex_Icc l r) hs ht
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_ofNat,
      Real.coe_toNNReal _ (abs_nonneg _)]
    have heq : π (Φ s t x) - π x - (π (Φ s t y) - π y) = d t - d s := by
      simp only [d, hInit s hs]
      abel
    rw [heq]
    exact h.trans_eq (by rw [Real.norm_eq_abs]; ring)

/-- Any two-time trajectory family for a uniformly Lipschitz field satisfies
the restart identity. Reversing a transition yields its inverse. -/
theorem scaledFlow_restart
    {F : ℝ → E → E} {Φ : ℝ → ℝ → E → E} {l r s t u : ℝ} {K : ℝ≥0}
    (hInit : ∀ v ∈ Icc l r, ∀ z, Φ v v z = z)
    (hTraj : ∀ v ∈ Icc l r, ∀ z w, w ∈ Icc l r →
      HasDerivWithinAt (fun q => Φ v q z) (F w (Φ v w z)) (Icc l r) w)
    (hF : ∀ v ∈ Icc l r, LipschitzWith K (F v))
    (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) (hu : u ∈ Icc l r) (z : E) :
    Φ t u (Φ s t z) = Φ s u z := by
  have h := scaledFlow_pathNorm_le_exp
    (fun v hv => (hTraj t ht (Φ s t z) v hv).sub (hTraj s hs z v hv))
    (fun v hv => by simpa only [dist_eq_norm, Pi.sub_apply] using
      (hF v hv).dist_le_mul (Φ t v (Φ s t z)) (Φ s v z)) ht hu
  have hzero : ‖Φ t u (Φ s t z) - Φ s u z‖ ≤ 0 := by
    simpa only [Pi.sub_apply, hInit t ht, sub_self, norm_zero, zero_mul] using h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hzero)

/-- The scaled derivative and projected displacement estimates follow from
the uniform spatial gradient bounds via the mean value inequality. -/
theorem scaledFlow_fderiv_and_displacement_le
    {F : ℝ → E → E} {Φ : ℝ → ℝ → E → E} {l r s t : ℝ} {K M : ℝ≥0}
    (π : E →L[ℝ] G)
    (hInit : ∀ u ∈ Icc l r, ∀ z, Φ u u z = z)
    (hTraj : ∀ u ∈ Icc l r, ∀ z v, v ∈ Icc l r →
      HasDerivWithinAt (fun w => Φ u w z) (F v (Φ u v z)) (Icc l r) v)
    (hF : ∀ u ∈ Icc l r, Differentiable ℝ (F u))
    (hGrad : ∀ u ∈ Icc l r, ∀ z, ‖fderiv ℝ (F u) z‖ ≤ K)
    (hProj : ∀ u ∈ Icc l r, ∀ z, ‖fderiv ℝ (π ∘ F u) z‖ ≤ M)
    (hSmall : (K : ℝ) * (r - l) ≤ 1 / 2)
    (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) (z : E) :
    ‖fderiv ℝ (Φ s t) z‖ ≤ 2 ∧
      ‖fderiv ℝ (fun y => π (Φ s t y) - π y) z‖ ≤ 2 * M * |t - s| := by
  have hFLip (u : ℝ) (hu : u ∈ Icc l r) : LipschitzWith K (F u) :=
    lipschitzWith_of_nnnorm_fderiv_le (hF u hu) (fun y => by exact_mod_cast hGrad u hu y)
  have hProjLip (u : ℝ) (hu : u ∈ Icc l r) : LipschitzWith M (π ∘ F u) :=
    lipschitzWith_of_nnnorm_fderiv_le (π.differentiable.comp (hF u hu))
      (fun y => by exact_mod_cast hProj u hu y)
  obtain ⟨hL, hD⟩ := scaledFlow_lipschitz_and_displacement_le π hInit hTraj hFLip hProjLip
    hSmall hs ht
  exact ⟨by simpa only [NNReal.coe_ofNat] using norm_fderiv_le_of_lipschitz ℝ hL (x₀ := z),
    by simpa only [NNReal.coe_mul, NNReal.coe_ofNat, Real.coe_toNNReal _ (abs_nonneg _)]
      using norm_fderiv_le_of_lipschitz ℝ hD (x₀ := z)⟩

/-- A bounded field that is continuous in time and space and uniformly
Lipschitz in space has a two-time flow on the full slab. -/
theorem exists_scaledFlow_on_Icc [CompleteSpace E]
    {F : ℝ → E → E} {l r : ℝ} {C K : ℝ≥0}
    (hF : ContinuousOn (Function.uncurry F) (Icc l r ×ˢ (univ : Set E)))
    (hBound : ∀ t ∈ Icc l r, ∀ z, ‖F t z‖ ≤ C)
    (hLip : ∀ t ∈ Icc l r, LipschitzWith K (F t)) :
    ∃ Φ : ℝ → ℝ → E → E, (∀ s ∈ Icc l r, ∀ z, Φ s s z = z) ∧
      (∀ s ∈ Icc l r, ∀ z t, t ∈ Icc l r →
        HasDerivWithinAt (fun u => Φ s u z) (F t (Φ s t z)) (Icc l r) t) := by
  classical
  have hPaths (s : ℝ) (z : E) : ∃ x : ℝ → E, s ∈ Icc l r →
      x s = z ∧ ∀ t ∈ Icc l r, HasDerivWithinAt x (F t (x t)) (Icc l r) t := by
    by_cases hs : s ∈ Icc l r
    · let D : ℝ≥0 := ⟨r - l, sub_nonneg.mpr (hs.1.trans hs.2)⟩
      have hPicard : IsPicardLindelof F (⟨s, hs⟩ : Icc l r) z (C * D) 0 C K := by
        constructor
        · exact fun t ht => (hLip t ht).lipschitzOnWith
        · intro x _
          exact hF.comp (continuous_id.prodMk continuous_const).continuousOn
            (fun t ht => ⟨ht, mem_univ x⟩)
        · exact fun t ht x _ => hBound t ht x
        · change (C : ℝ) * max (r - s) (s - l) ≤ (C : ℝ) * (r - l) - 0
          rw [sub_zero]
          exact mul_le_mul_of_nonneg_left
            (max_le (sub_le_sub_left hs.1 r) (sub_le_sub_right hs.2 l)) C.coe_nonneg
      obtain ⟨x, hx, hxDeriv⟩ := hPicard.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
      exact ⟨x, fun _ => ⟨hx, hxDeriv⟩⟩
    · exact ⟨fun _ => z, fun h => (hs h).elim⟩
  choose x hx using hPaths
  exact ⟨fun s t z => x s z t, fun s hs z => (hx s z hs).1, fun s hs z => (hx s z hs).2⟩

/-- A smooth finite-dimensional scaled field has differentiable transitions
in either time direction. -/
theorem scaledFlow_differentiable_transition [FiniteDimensional ℝ E]
    {F : ℝ → E → E} {Φ : ℝ → ℝ → E → E} {l r s t : ℝ} {K : ℝ≥0}
    (hInit : ∀ v ∈ Icc l r, ∀ z, Φ v v z = z)
    (hTraj : ∀ v ∈ Icc l r, ∀ z u, u ∈ Icc l r →
      HasDerivWithinAt (fun w => Φ v w z) (F u (Φ v u z)) (Icc l r) u)
    (hF : ContDiffOn ℝ ∞ (Function.uncurry F) (Icc l r ×ˢ (univ : Set E)))
    (hLip : ∀ v ∈ Icc l r, LipschitzWith K (F v))
    (hSmall : (K : ℝ) * (r - l) ≤ 1 / 2)
    (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) : Differentiable ℝ (Φ s t) := by
  let θ (v : ℝ) : ℝ := s + (t - s) * v
  have hθ (v : ℝ) : HasDerivAt θ (t - s) v := by
    simpa only [θ, id_eq, mul_one] using ((hasDerivAt_id v).const_mul (t - s)).const_add s
  have hMaps : MapsTo θ (Icc 0 1) (Icc l r) := by
    intro u hu
    rw [show θ u = (1 - u) • s + u • t by dsimp only [θ, smul_eq_mul]; ring]
    exact convex_Icc l r hs ht (sub_nonneg.mpr hu.2) hu.1 (sub_add_cancel 1 u)
  let f (v : ℝ) (z : E) := (t - s) • F (θ v) z
  have hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 1 ×ˢ (univ : Set E)) := by
    have hθsmooth : ContDiff ℝ ∞ θ := by
      unfold θ
      fun_prop
    have hθpair : ContDiff ℝ ∞ (fun q : ℝ × E => (θ q.1, q.2)) :=
      (hθsmooth.comp contDiff_fst).prodMk contDiff_snd
    exact (hF.comp hθpair.contDiffOn (fun q hq => ⟨hMaps hq.1, mem_univ q.2⟩)).const_smul _
  let Y (v : ℝ) := Φ s (θ v)
  have hYt (p : E) (v : ℝ) (hv : v ∈ Icc 0 1) :
      HasDerivWithinAt (fun w => Y w p) (f v (Y v p)) (Icc 0 1) v :=
    (hTraj s hs p (θ v) (hMaps hv)).scomp v (hθ v).hasDerivWithinAt hMaps
  have hYc : ContinuousOn (Function.uncurry Y) (Icc 0 1 ×ˢ (univ : Set E)) := by
    refine continuousOn_prod_of_continuousOn_lipschitzOnWith' _ 2 (fun v hv => ?_)
      (fun p _ => HasDerivWithinAt.continuousOn (hYt p))
    have hLipV := (scaledFlow_lipschitz_and_displacement_le (0 : E →L[ℝ] E)
      hInit hTraj hLip (M := 0) (fun u hu => by simp) hSmall hs (hMaps hv)).1
    exact hLipV.lipschitzOnWith
  have hY₀ : ContDiff ℝ ∞ (Y 0) := by
    have heq : Y 0 = id := by
      funext z
      simp [Y, θ, hInit s hs]
    rw [heq]
    exact contDiff_id
  have hY₁ : Y 1 = Φ s t := by simp [Y, θ]
  rw [← hY₁]
  exact (trajectoryFamily_spatialDerivative (T := 1) (by norm_num) hf hYc hYt hY₀).1 1
    ⟨by norm_num, le_rfl⟩

/-- A bounded smooth scaled field with a small scaled gradient has an actual
two-time flow, and its projected displacement satisfies the derivative bound
for both the forward and reverse transitions. -/
theorem exists_scaledFlow_with_deformation_bounds [FiniteDimensional ℝ E]
    {F : ℝ → E → E} {l r : ℝ} {C K M : ℝ≥0} (π : E →L[ℝ] G)
    (hF : ContDiffOn ℝ ∞ (Function.uncurry F) (Icc l r ×ˢ (univ : Set E)))
    (hBound : ∀ t ∈ Icc l r, ∀ z, ‖F t z‖ ≤ C)
    (hGrad : ∀ t ∈ Icc l r, ∀ z, ‖fderiv ℝ (F t) z‖ ≤ K)
    (hProj : ∀ t ∈ Icc l r, ∀ z, ‖fderiv ℝ (π ∘ F t) z‖ ≤ M)
    (hSmall : (K : ℝ) * (r - l) ≤ 1 / 2) :
    ∃ Φ : ℝ → ℝ → E → E, (∀ s ∈ Icc l r, ∀ z, Φ s s z = z) ∧
      (∀ s ∈ Icc l r, ∀ z t, t ∈ Icc l r →
        HasDerivWithinAt (fun u => Φ s u z) (F t (Φ s t z)) (Icc l r) t) ∧
      (∀ s ∈ Icc l r, ∀ t ∈ Icc l r, ∀ u ∈ Icc l r, ∀ z,
        Φ t u (Φ s t z) = Φ s u z) ∧
      (∀ s ∈ Icc l r, ∀ t ∈ Icc l r, Differentiable ℝ (Φ s t)) ∧
      ∀ s ∈ Icc l r, ∀ t ∈ Icc l r, ∀ z,
        ‖fderiv ℝ (Φ s t) z‖ ≤ 2 ∧
          ‖fderiv ℝ (fun y => π (Φ s t y) - π y) z‖ ≤ 2 * M * |t - s| := by
  have hDiff (t : ℝ) (ht : t ∈ Icc l r) : Differentiable ℝ (F t) := by
    have hSlice : ContDiffOn ℝ ∞ (F t) (univ : Set E) :=
      hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun z hz => ⟨ht, hz⟩)
    exact differentiableOn_univ.mp (hSlice.differentiableOn (by simp))
  have hLip (t : ℝ) (ht : t ∈ Icc l r) : LipschitzWith K (F t) :=
    lipschitzWith_of_nnnorm_fderiv_le (hDiff t ht) (fun z => by exact_mod_cast hGrad t ht z)
  obtain ⟨Φ, hInit, hTraj⟩ := exists_scaledFlow_on_Icc hF.continuousOn hBound hLip
  exact ⟨Φ, hInit, hTraj,
    fun s hs t ht u hu z => scaledFlow_restart hInit hTraj hLip hs ht hu z,
    fun s hs t ht => scaledFlow_differentiable_transition hInit hTraj hF hLip hSmall hs ht,
    fun s hs t ht z =>
      scaledFlow_fderiv_and_displacement_le π hInit hTraj hDiff hGrad hProj hSmall hs ht z⟩

end ScaledFlow

end TorusEuler

namespace TorusEuler.ChildFlow

abbrev PhaseState := Vec3 × ℝ

/-- Recover the unscaled label from the first scaled coordinate. -/
noncomputable def labelProjection (ell : ℝ) : PhaseState →L[ℝ] Vec3 :=
  ell • fst ℝ Vec3 ℝ

/-- The conserved difference of phase and linear label phase. -/
noncomputable def phaseDefect (ell h : ℝ) (k : Vec3) : PhaseState →L[ℝ] ℝ :=
  h • snd ℝ Vec3 ℝ - (innerSL ℝ k).comp (labelProjection ell)

/-- The lifted particle field, with the label and phase treated independently. -/
noncomputable def scaledField (ell h : ℝ) (k : Vec3) (c : ℝ → PhaseState → Vec3)
    (t : ℝ) (z : PhaseState) : PhaseState :=
  let w := c t (labelPhaseScale ell h z)
  (ell⁻¹ • w, h⁻¹ * ⟪k, w⟫_ℝ)

/-- Restriction of the label field to the original phase graph. -/
noncomputable def graphField (k : Vec3) (c : ℝ → PhaseState → Vec3) : Velocity :=
  fun t a => c t (a, ⟪k, a⟫_ℝ)

@[simp] theorem labelProjection_scaledGraph {ell h : ℝ} (hell : ell ≠ 0)
    (k a : Vec3) : labelProjection ell (labelPhaseSlope ell h k a) = a := by
  simp [labelProjection, labelPhaseSlope_apply, smul_smul, mul_inv_cancel₀ hell]

@[simp] theorem defect_scaledGraph {ell h : ℝ} (hell : ell ≠ 0) (hh : h ≠ 0)
    (k a : Vec3) : phaseDefect ell h k (labelPhaseSlope ell h k a) = 0 := by
  simp [phaseDefect, labelPhaseSlope_apply, labelProjection, ← mul_assoc,
    mul_inv_cancel₀ hell, mul_inv_cancel₀ hh]

theorem scaledGraph_labelProjection_of_defect_eq_zero {ell h : ℝ}
    (hell : ell ≠ 0) (hh : h ≠ 0) {k : Vec3} {z : PhaseState}
    (hz : phaseDefect ell h k z = 0) :
    labelPhaseSlope ell h k (labelProjection ell z) = z := by
  have hs : h * z.2 = ⟪k, labelProjection ell z⟫_ℝ := by
    exact sub_eq_zero.mp (by simpa [phaseDefect] using hz)
  apply Prod.ext
  · simp [labelPhaseSlope_apply, labelProjection, smul_smul, mul_inv_cancel₀ hell]
  · simp [labelPhaseSlope_apply, ← hs, ← mul_assoc, inv_mul_cancel₀ hh]

@[simp] theorem defect_scaledField {ell h : ℝ} (hell : ell ≠ 0) (hh : h ≠ 0)
    (k : Vec3) (c : ℝ → PhaseState → Vec3) (t : ℝ) (z : PhaseState) :
    phaseDefect ell h k (scaledField ell h k c t z) = 0 := by
  simp [phaseDefect, scaledField, labelProjection, ← mul_assoc,
    mul_inv_cancel₀ hell, mul_inv_cancel₀ hh]

theorem labelProjection_scaledField {ell h : ℝ} (hell : ell ≠ 0) {k : Vec3}
    {c : ℝ → PhaseState → Vec3} {t : ℝ} {z : PhaseState}
    (hz : phaseDefect ell h k z = 0) :
    labelProjection ell (scaledField ell h k c t z) =
      graphField k c t (labelProjection ell z) := by
  have hs : h * z.2 = ⟪k, labelProjection ell z⟫_ℝ := by
    exact sub_eq_zero.mp (by simpa [phaseDefect] using hz)
  simp [labelProjection, scaledField, labelPhaseScale_apply, graphField,
    show h * z.2 = ⟪k, ell • z.1⟫_ℝ from hs, smul_smul, mul_inv_cancel₀ hell]

/-- Conversion from the weighted coordinate derivatives to the norm of the
first Fréchet derivative after rescaling. -/
theorem norm_fderiv_scaledPhaseProfile_le_of_coordinateBounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : PhaseState → E}
    {M ell h : ℝ} (hf : ContDiff ℝ ∞ f) (hM : 0 ≤ M)
    (hcoord : ∀ j ≤ 1, ∀ (p : PhaseState) (i : Fin j → Fin 3 ⊕ Unit),
      ‖(∏ r, phaseCoordinateWeight ell h (i r)) •
        iteratedFDeriv ℝ j f p (fun r => phaseCoordinateDirection (i r))‖ ≤ M)
    (z : PhaseState) :
    ‖fderiv ℝ (f ∘ labelPhaseScale ell h) z‖ ≤ 4 * M := by
  let g : Vec3 → ℝ → E := fun a s => f (a, s)
  have hg : ContDiff ℝ ∞ (Function.uncurry g) := hf
  have hj := scaledPhaseProfile_jetBound_of_coordinateBounds hg hM ell h hcoord
    1 le_rfl z
  rw [norm_iteratedFDeriv_one, pow_one] at hj
  exact hj

/-- The phase component of the scaled field is the scaled derivative of the
scalar phase speed, so the norm bound retains the phase cancellation input. -/
theorem hasFDerivAt_scaledField {ell h t : ℝ} {k : Vec3}
    {c : ℝ → PhaseState → Vec3} {z : PhaseState}
    {C : PhaseState →L[ℝ] Vec3} {G : PhaseState →L[ℝ] ℝ}
    (hC : HasFDerivAt (c t ∘ labelPhaseScale ell h) C z)
    (hG : HasFDerivAt ((fun w => ⟪k, c t w⟫_ℝ) ∘ labelPhaseScale ell h) G z) :
    HasFDerivAt (scaledField ell h k c t) ((ell⁻¹ • C).prod (h⁻¹ • G)) z := by
  exact (hC.const_smul ell⁻¹).prodMk (hG.const_smul h⁻¹)

/-- The scaled field gradient is controlled by the two scaled profile gradients
divided by their respective physical scales. -/
theorem norm_fderiv_scaledField_le {ell h t A B : ℝ} {k : Vec3}
    {c : ℝ → PhaseState → Vec3} {z : PhaseState}
    {C : PhaseState →L[ℝ] Vec3} {G : PhaseState →L[ℝ] ℝ}
    (hell : 0 < ell) (hh : 0 < h)
    (hC : HasFDerivAt (c t ∘ labelPhaseScale ell h) C z)
    (hG : HasFDerivAt ((fun w => ⟪k, c t w⟫_ℝ) ∘ labelPhaseScale ell h) G z)
    (hA : ‖C‖ ≤ A) (hB : ‖G‖ ≤ B) :
    ‖fderiv ℝ (scaledField ell h k c t) z‖ ≤ ell⁻¹ * A + h⁻¹ * B := by
  have hℓi := inv_nonneg.mpr hell.le
  have hhi := inv_nonneg.mpr hh.le
  rw [(hasFDerivAt_scaledField hC hG).fderiv, ContinuousLinearMap.opNorm_prod, Prod.norm_def,
    norm_smul, norm_smul, Real.norm_of_nonneg hℓi, Real.norm_of_nonneg hhi]
  have hA₀ := (norm_nonneg C).trans hA
  have hB₀ := (norm_nonneg G).trans hB
  exact max_le ((mul_le_mul_of_nonneg_left hA hℓi).trans
      (le_add_of_nonneg_right (mul_nonneg hhi hB₀)))
    ((mul_le_mul_of_nonneg_left hB hhi).trans
      (le_add_of_nonneg_left (mul_nonneg hℓi hA₀)))

/-- A uniform bound on the scaled label profile also bounds the lifted field. -/
theorem norm_scaledField_le_of_label_value_bound {ell h t A : ℝ} {k : Vec3}
    {c : ℝ → PhaseState → Vec3} {z : PhaseState}
    (hell : 0 < ell) (hh : 0 < h) (hA : ‖c t (labelPhaseScale ell h z)‖ ≤ A) :
    ‖scaledField ell h k c t z‖ ≤ ell⁻¹ * A + h⁻¹ * (‖k‖ * A) := by
  have hA₀ := (norm_nonneg _).trans hA
  have helli := inv_nonneg.mpr hell.le
  have hhi := inv_nonneg.mpr hh.le
  have hphase : ‖⟪k, c t (labelPhaseScale ell h z)⟫_ℝ‖ ≤ ‖k‖ * A := by
    calc
      _ ≤ ‖innerSL ℝ k‖ * ‖c t (labelPhaseScale ell h z)‖ := le_opNorm _ _
      _ ≤ _ := by rw [innerSL_apply_norm]; exact mul_le_mul_of_nonneg_left hA (norm_nonneg _)
  rw [scaledField, Prod.norm_def, norm_smul, norm_mul, Real.norm_of_nonneg helli,
    Real.norm_of_nonneg hhi]
  exact max_le ((mul_le_mul_of_nonneg_left hA helli).trans (le_add_of_nonneg_right (by positivity)))
    ((mul_le_mul_of_nonneg_left hphase hhi).trans (le_add_of_nonneg_left (by positivity)))

/-- Recovering the physical label from the scaled particle velocity removes
the reciprocal-label factor from the displacement estimate. -/
theorem hasFDerivAt_labelProjection_scaledField {ell h t : ℝ} {k : Vec3}
    {c : ℝ → PhaseState → Vec3} {z : PhaseState}
    {C : PhaseState →L[ℝ] Vec3} (hell : ell ≠ 0)
    (hC : HasFDerivAt (c t ∘ labelPhaseScale ell h) C z) :
    HasFDerivAt (labelProjection ell ∘ scaledField ell h k c t) C z := by
  have heq : labelProjection ell ∘ scaledField ell h k c t = c t ∘ labelPhaseScale ell h := by
    funext w
    simp [scaledField, labelPhaseScale_apply, labelProjection, Function.comp_apply,
      smul_smul, mul_inv_cancel₀ hell]
  rwa [heq]

variable {ell h l r : ℝ} {k : Vec3} {c : ℝ → PhaseState → Vec3}
  {Φ : ℝ → ℝ → PhaseState → PhaseState}

/-- The label of the lifted transition started on the phase graph. -/
noncomputable def labelTransition (ell h : ℝ) (k : Vec3)
    (Φ : ℝ → ℝ → PhaseState → PhaseState) : ℝ → Velocity :=
  fun s t a => labelProjection ell (Φ s t (labelPhaseSlope ell h k a))

/-- The lifted flow preserves the phase defect, in either time direction. -/
theorem phaseDefect_transition (hell : ell ≠ 0) (hh : h ≠ 0)
    (hinit : ∀ s ∈ Icc l r, ∀ z, Φ s s z = z)
    (htraj : ∀ s ∈ Icc l r, ∀ z t, t ∈ Icc l r →
      HasDerivWithinAt (fun u => Φ s u z) (scaledField ell h k c t (Φ s t z)) (Icc l r) t)
    {s t : ℝ} (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) (z : PhaseState) :
    phaseDefect ell h k (Φ s t z) = phaseDefect ell h k z := by
  have hd (u : ℝ) (hu : u ∈ Icc l r) :
      HasDerivWithinAt (fun v => phaseDefect ell h k (Φ s v z)) 0 (Icc l r) u := by
    simpa only [Function.comp_def, defect_scaledField hell hh] using
      (phaseDefect ell h k).hasFDerivAt.comp_hasDerivWithinAt u (htraj s hs z u hu)
  have hn := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd
    (fun _ _ => norm_zero.le) (convex_Icc l r) hs ht
  rw [hinit s hs z, zero_mul] at hn
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))

/-- Restriction to the invariant graph is the actual two-time label flow. -/
theorem isLabelFlowOn_labelTransition (hell : ell ≠ 0) (hh : h ≠ 0)
    (hinit : ∀ s ∈ Icc l r, ∀ z, Φ s s z = z)
    (htraj : ∀ s ∈ Icc l r, ∀ z t, t ∈ Icc l r →
      HasDerivWithinAt (fun u => Φ s u z) (scaledField ell h k c t (Φ s t z)) (Icc l r) t) :
    IsLabelFlowOn (graphField k c) (labelTransition ell h k Φ) (Icc l r) := by
  refine ⟨fun s hs a => ?_, fun s hs a t ht => ?_⟩
  · simp [labelTransition, hinit s hs, hell]
  · have hd := phaseDefect_transition hell hh hinit htraj hs ht (labelPhaseSlope ell h k a)
    rw [defect_scaledGraph hell hh] at hd
    simpa only [Function.comp_def, labelTransition, labelProjection_scaledField hell hd] using
      (labelProjection ell).hasFDerivAt.comp_hasDerivWithinAt t
        (htraj s hs (labelPhaseSlope ell h k a) t ht)

/-- Deviation of the graph transition from the identity. The derivative formula
uses the displacement of the projected, unscaled label in the scaled domain. -/
theorem hasFDerivAt_labelTransition_sub_id {s t : ℝ} {a : Vec3}
    (hell : ell ≠ 0) {D : PhaseState →L[ℝ] Vec3}
    (hD : HasFDerivAt (fun z => labelProjection ell (Φ s t z) - labelProjection ell z)
      D (labelPhaseSlope ell h k a)) :
    HasFDerivAt (fun x => labelTransition ell h k Φ s t x - x)
      (D.comp (labelPhaseSlope ell h k)) a := by
  simpa only [Function.comp_def, labelTransition, labelProjection_scaledGraph hell] using
    hD.comp a (labelPhaseSlope ell h k).hasFDerivAt

/-- The derivative on the graph is the sum of the label and phase derivatives. -/
theorem graphDerivative_apply (ell h : ℝ) (k : Vec3)
    (D : PhaseState →L[ℝ] Vec3) (v : Vec3) :
    (D.comp (labelPhaseSlope ell h k)) v =
      D (ell⁻¹ • v, 0) + (h⁻¹ * ⟪k, v⟫_ℝ) • D (0, 1) := by
  have hsplit : labelPhaseSlope ell h k v =
      (ell⁻¹ • v, 0) + (h⁻¹ * ⟪k, v⟫_ℝ) • (0, 1) := by
    ext <;> simp [labelPhaseSlope_apply]
  rw [ContinuousLinearMap.comp_apply, hsplit, map_add, map_smul]

theorem norm_scaledGraph_le {ell h : ℝ} (hell : 0 < ell) (hh : 0 < h) (k : Vec3) :
    ‖labelPhaseSlope ell h k‖ ≤ ell⁻¹ + ‖k‖ * h⁻¹ := by
  calc
    ‖labelPhaseSlope ell h k‖ = max (‖ell⁻¹ • ContinuousLinearMap.id ℝ Vec3‖)
        (‖h⁻¹ • innerSL ℝ k‖) := by
      have heq : labelPhaseSlope ell h k =
          (ell⁻¹ • ContinuousLinearMap.id ℝ Vec3).prod (h⁻¹ • innerSL ℝ k) := by
        ext v <;> simp [labelPhaseSlope_apply]
      rw [heq, ContinuousLinearMap.opNorm_prod, Prod.norm_def]
    _ ≤ ell⁻¹ + ‖k‖ * h⁻¹ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hell.le),
        Real.norm_of_nonneg (inv_nonneg.mpr hh.le), norm_id, mul_one, innerSL_apply_norm,
        mul_comm h⁻¹ ‖k‖]
      exact max_le (le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr hh.le)))
        (le_add_of_nonneg_left (inv_nonneg.mpr hell.le))

/-- Operator norm of the derivative of the unscaled graph transition. -/
theorem norm_fderiv_labelTransition_le {s t : ℝ} {a : Vec3}
    (hell : 0 < ell) (hh : 0 < h) {D : PhaseState →L[ℝ] Vec3} {B : ℝ}
    (hD : HasFDerivAt (fun z => labelProjection ell (Φ s t z) - labelProjection ell z)
      D (labelPhaseSlope ell h k a))
    (hB : ‖D‖ ≤ B) :
    HasFDerivAt (labelTransition ell h k Φ s t)
      (D.comp (labelPhaseSlope ell h k) + ContinuousLinearMap.id ℝ Vec3) a ∧
    ‖fderiv ℝ (labelTransition ell h k Φ s t) a‖ ≤
      1 + (ell⁻¹ + ‖k‖ * h⁻¹) * B := by
  have hA : HasFDerivAt (labelTransition ell h k Φ s t)
      (D.comp (labelPhaseSlope ell h k) + ContinuousLinearMap.id ℝ Vec3) a := by
    simpa only [Pi.add_def, id_eq, sub_add_cancel] using
      (hasFDerivAt_labelTransition_sub_id hell.ne' hD).add (hasFDerivAt_id a)
  refine ⟨hA, ?_⟩
  have hB₀ := (norm_nonneg _).trans hB
  rw [hA.fderiv, add_comm 1]
  calc
    ‖D.comp (labelPhaseSlope ell h k) + ContinuousLinearMap.id ℝ Vec3‖ ≤
        ‖D.comp (labelPhaseSlope ell h k)‖ + 1 := by
        simpa only [norm_id] using norm_add_le (D.comp (labelPhaseSlope ell h k))
          (ContinuousLinearMap.id ℝ Vec3)
    _ ≤ (ell⁻¹ + ‖k‖ * h⁻¹) * B + 1 := by
      gcongr
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul hB (norm_scaledGraph_le hell hh k) (norm_nonneg _) hB₀).trans_eq
          (mul_comm _ _))


/-- Pull back the Eulerian perturbation by the inverse parent deformation. -/
noncomputable def pullbackField (X : ℝ → Velocity) (W : ℝ → Vec3 → ℝ → Vec3)
    (v : Velocity) (t : ℝ) (z : PhaseState) : Vec3 :=
  (fderiv ℝ (X t 0) (X 0 t z.1)) (W t z.1 z.2 + v t (X 0 t z.1))

/-- The parent pullback preserves label–phase lattice translations. -/
theorem pullbackField_skewPeriodic {X : ℝ → Velocity} {W : ℝ → Vec3 → ℝ → Vec3}
    {v : Velocity} {k : Vec3} {t : ℝ} (n : Fin 3 → ℤ)
    (hXf : ∀ x, X 0 t (x + latticeVector n) = X 0 t x + latticeVector n)
    (hXr : ∀ x, X t 0 (x + latticeVector n) = X t 0 x + latticeVector n)
    (hW : ∀ a s, W t (a + latticeVector n) (s + ⟪k, latticeVector n⟫_ℝ) = W t a s)
    (hv : SpatiallyPeriodic (v t)) (a : Vec3) (s : ℝ) :
    pullbackField X W v t (a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ) =
      pullbackField X W v t (a, s) := by
  have heq : (fun x => X t 0 (x + latticeVector n)) =
      (fun x => X t 0 x + latticeVector n) := funext hXr
  have hD (x : Vec3) :
      fderiv ℝ (X t 0) (x + latticeVector n) = fderiv ℝ (X t 0) x := by
    rw [← fderiv_comp_add_right (latticeVector n), heq, fderiv_add_const]
  simp only [pullbackField, hXf, hD, hW, hv n]

/-- The physical label field is periodic when the profiles obey the
label–phase lattice rule and the perturbation is periodic. -/
theorem graphField_pullback_spatiallyPeriodic
    {U v : Velocity} {X : ℝ → Velocity} {W : ℝ → Vec3 → ℝ → Vec3}
    {T t : ℝ} {k : Vec3} {K : ℝ≥0}
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hK : ∀ u ∈ Icc 0 T, LipschitzWith K (U u))
    (hper : ∀ u ∈ Icc 0 T, SpatiallyPeriodic (U u))
    (h₀ : (0 : ℝ) ∈ Icc 0 T) (ht : t ∈ Icc 0 T)
    (hW : ∀ (n : Fin 3 → ℤ) a s,
      W t (a + latticeVector n) (s + ⟪k, latticeVector n⟫_ℝ) = W t a s)
    (hv : SpatiallyPeriodic (v t)) :
    SpatiallyPeriodic (graphField k (pullbackField X W v) t) := by
  intro n a
  simpa only [graphField, inner_add_right] using
    pullbackField_skewPeriodic n (hX.add_latticeVector hK hper h₀ ht n)
      (hX.add_latticeVector hK hper ht h₀ n) (hW n) hv a ⟪k, a⟫_ℝ

/-- The Piola identity applies to the actual inverse deformation used in the
particle field. Here the phase derivative is taken before graph evaluation. -/
theorem slope_divergence_pullbackField
    {U v : Velocity} {X : ℝ → Velocity} {W : ℝ → Vec3 → ℝ → Vec3}
    {T t s : ℝ} {a k : Vec3} {K : ℝ≥0}
    (hT : 0 < T) (ht : t ∈ Icc 0 T)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t))
    (hK : ∀ t ∈ Icc 0 T, LipschitzWith K (U t))
    (hUdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (U t) x = 0)
    (hX₂ : ContDiffAt ℝ 2 (X 0 t) a)
    (hc : DifferentiableAt ℝ (pullbackField X W v t) (a, s))
    (hW : DifferentiableAt ℝ (W t a) s)
    (hdiv : divergence (fun x => W t (X t 0 x) s + v t x) (X 0 t a) +
      ⟪(fderiv ℝ (X t 0) (X 0 t a)).adjoint k, deriv (W t a) s⟫_ℝ = 0) :
    divergence (fun z => pullbackField X W v t (z, s)) a +
      ⟪k, deriv (fun z => pullbackField X W v t (a, z)) s⟫_ℝ = 0 := by
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hInv := hX.inverse hK h₀ ht
  have hA (z : Vec3) : HasFDerivAt (X t 0) (fderiv ℝ (X t 0) z) z :=
    (hX.differentiableAt_transition hT hU hper ht h₀ z).hasFDerivAt
  have hdet : ∀ᶠ z in 𝓝 a, LinearMap.det (fderiv ℝ (X 0 t) z).toLinearMap = 1 :=
    Eventually.of_forall (hX.det_labelDerivative hT hU hper hUdiv h₀ ht)
  let c (z : Vec3) (q : ℝ) := pullbackField X W v t (z, q)
  have hca := hc.hasFDerivAt.comp a (hasFDerivAt_prodMk_left (𝕜 := ℝ) a s)
  have hcs := hc.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_const s a).prodMk (hasDerivAt_id s))
  have hpi := divergence_phase_piola (c := c) (k := k)
    (hX₂.differentiableAt (by simp)).hasFDerivAt
    ((hX₂.fderiv_right (m := 1) (by norm_num)).differentiableAt_one.hasFDerivAt)
    (hX₂.isSymmSndFDerivAt (by simp)) (hA (X 0 t a))
    (Eventually.of_forall hInv.1) hdet hca hcs
  have hPush (z : Vec3) (q : ℝ) :
      (fderiv ℝ (X 0 t) z) (c z q) = W t z q + v t (X 0 t z) := by
    simpa only [c, pullbackField, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun L : Vec3 →L[ℝ] Vec3 => L (W t z q + v t (X 0 t z)))
        (hX.labelDerivative_inverse hT hU hper h₀ ht z).2
  have hspace :
      (fun x => (fderiv ℝ (X 0 t) (X t 0 x)) (c (X t 0 x) s)) =
        fun x => W t (X t 0 x) s + v t x := funext fun x => by
    rw [hPush, hInv.2]
  have hphase :
      (fun z => (fderiv ℝ (X 0 t) a) (c a z)) = fun z => W t a z + v t (X 0 t a) :=
    funext (hPush a)
  rw [hspace, hphase, (hW.hasDerivAt.add_const _).deriv, hdiv] at hpi
  exact hpi.symm

/-- The physical velocity of the perturbed child. -/
noncomputable def childVelocity (U : Velocity) (X : ℝ → Velocity) (k : Vec3)
    (W : ℝ → Vec3 → ℝ → Vec3) (v : Velocity) : Velocity :=
  fun t x => U t x + transportedProfile (fun u => X u 0) k W t x + v t x

/-- Conjugate a transition in label variables by the physical parent flow. -/
noncomputable def physicalTransition (X A : ℝ → Velocity) : ℝ → Velocity :=
  fun s t x => X 0 t (A s t (X s 0 x))

theorem physicalTransition_from_zero {X A : ℝ → Velocity} {U : Velocity} {T : ℝ}
    (hX : IsLabelFlowOn U X (Icc 0 T)) (h₀ : 0 ∈ Icc (0 : ℝ) T)
    (t : ℝ) (x : Vec3) : physicalTransition X A 0 t x = X 0 t (A 0 t x) := by
  simp only [physicalTransition, hX.initial 0 h₀]

theorem physicalTransition_to_zero {X A : ℝ → Velocity} {U : Velocity} {T : ℝ}
    (hX : IsLabelFlowOn U X (Icc 0 T)) (h₀ : 0 ∈ Icc (0 : ℝ) T)
    (t : ℝ) (x : Vec3) : physicalTransition X A t 0 x = A t 0 (X t 0 x) := by
  simp only [physicalTransition, hX.initial 0 h₀]

/-- Conjugating the actual graph field by the parent gives a physical flow
for the parent plus the transported wave and the Eulerian perturbation. -/
theorem isLabelFlowOn_physicalTransition
    {U v : Velocity} {X A : ℝ → Velocity} {T : ℝ}
    {W : ℝ → Vec3 → ℝ → Vec3} {K : ℝ≥0} (hT : 0 < T)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t))
    (hK : ∀ t ∈ Icc 0 T, LipschitzWith K (U t))
    (hA : IsLabelFlowOn (graphField k (pullbackField X W v)) A (Icc 0 T)) :
    IsLabelFlowOn (childVelocity U X k W v) (physicalTransition X A) (Icc 0 T) := by
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  refine ⟨fun s hs x => ?_, fun s hs x t ht => ?_⟩
  · exact (congrArg (X 0 s) (hA.initial s hs (X s 0 x))).trans
      ((hX.inverse hK hs h₀).1 x)
  · let a (u : ℝ) := A s u (X s 0 x)
    have ha := hA.trajectory s hs (X s 0 x) t ht
    have h := (hX.hasFDerivWithinAt_time_label_of_contDiffOn_periodic hT hU hper h₀ ht (a := a t)).comp_hasDerivWithinAt t
      ((hasDerivWithinAt_id t (Icc 0 T)).prodMk ha)
      (fun _ hu => mem_prod.mpr ⟨hu, mem_univ _⟩)
    have hInv := (hX.labelDerivative_inverse hT hU hper h₀ ht (a t)).2
    have hApply := congrArg (fun L : Vec3 →L[ℝ] Vec3 =>
      L (W t (a t) ⟪k, a t⟫_ℝ + v t (X 0 t (a t)))) hInv
    have hVel :
        (fderiv ℝ (X 0 t) (a t)) (graphField k (pullbackField X W v) t (a t)) =
          W t (a t) ⟪k, a t⟫_ℝ + v t (X 0 t (a t)) := by
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        graphField, pullbackField] using hApply
    have hWave := transportedProfile_on_trajectory (A := fun u => X u 0)
      (X := X 0) k W ((hX.inverse hK h₀ ht).1 (a t))
    change HasDerivWithinAt (fun u => X 0 u (a u))
      (((toSpanSingleton ℝ (U t (X 0 t (a t)))).coprod (fderiv ℝ (X 0 t) (a t)))
        (1, graphField k (pullbackField X W v) t (a t))) (Icc 0 T) t at h
    change HasDerivWithinAt (fun u => X 0 u (a u))
      (U t (X 0 t (a t)) +
        transportedProfile (fun u => X u 0) k W t (X 0 t (a t)) +
        v t (X 0 t (a t))) (Icc 0 T) t
    simpa only [ContinuousLinearMap.coprod_apply, toSpanSingleton_apply, one_smul, hVel,
      hWave, add_assoc] using h

/-- The reverse physical transition is the inverse map of the forward transition. -/
theorem physicalTransition_inverse {X A : ℝ → Velocity} {U C : Velocity} {T : ℝ}
    {K L : ℝ≥0} (hX : IsLabelFlowOn U X (Icc 0 T)) (hA : IsLabelFlowOn C A (Icc 0 T))
    (hK : ∀ t ∈ Icc 0 T, LipschitzWith K (U t))
    (hL : ∀ t ∈ Icc 0 T, LipschitzWith L (C t))
    (h₀ : (0 : ℝ) ∈ Icc 0 T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Function.LeftInverse (physicalTransition X A t 0) (physicalTransition X A 0 t) ∧
    Function.RightInverse (physicalTransition X A t 0) (physicalTransition X A 0 t) := by
  have hXi := hX.inverse hK h₀ ht
  have hAi := hA.inverse hL h₀ ht
  constructor
  · intro x
    rw [physicalTransition_to_zero hX h₀, physicalTransition_from_zero hX h₀,
      hXi.1, hAi.1]
  · intro x
    rw [physicalTransition_from_zero hX h₀, physicalTransition_to_zero hX h₀,
      hAi.2, hXi.2]

/-- The two physical derivatives have the parent deformation bound times the
bound for the two label transitions. -/
theorem physicalTransition_fderiv_bounds
    {U : Velocity} {X A : ℝ → Velocity} {T D B : ℝ}
    (hX : IsLabelFlowOn U X (Icc 0 T)) (h₀ : (0 : ℝ) ∈ Icc 0 T)
    {t : ℝ}
    (hXf : ∀ a, DifferentiableAt ℝ (X 0 t) a ∧ ‖fderiv ℝ (X 0 t) a‖ ≤ D)
    (hXr : ∀ a, DifferentiableAt ℝ (X t 0) a ∧ ‖fderiv ℝ (X t 0) a‖ ≤ D)
    (hAf : ∀ a, DifferentiableAt ℝ (A 0 t) a ∧ ‖fderiv ℝ (A 0 t) a‖ ≤ B)
    (hAr : ∀ a, DifferentiableAt ℝ (A t 0) a ∧ ‖fderiv ℝ (A t 0) a‖ ≤ B) :
    (∀ a, DifferentiableAt ℝ (physicalTransition X A 0 t) a ∧
      ‖fderiv ℝ (physicalTransition X A 0 t) a‖ ≤ D * B) ∧
    (∀ a, DifferentiableAt ℝ (physicalTransition X A t 0) a ∧
      ‖fderiv ℝ (physicalTransition X A t 0) a‖ ≤ D * B) := by
  have hD := (norm_nonneg _).trans (hXf 0).2
  have hB := (norm_nonneg _).trans (hAf 0).2
  constructor
  · intro a
    have hf := ((hXf (A 0 t a)).1.hasFDerivAt.comp a (hAf a).1.hasFDerivAt)
    have hf' := hf.congr_of_eventuallyEq (Eventually.of_forall fun x =>
      physicalTransition_from_zero hX h₀ t x)
    refine ⟨hf'.differentiableAt, ?_⟩
    rw [hf'.fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hXf (A 0 t a)).2 (hAf a).2 (norm_nonneg _) hD)
  · intro a
    have hr := ((hAr (X t 0 a)).1.hasFDerivAt.comp a (hXr a).1.hasFDerivAt)
    have hr' := hr.congr_of_eventuallyEq (Eventually.of_forall fun x =>
      physicalTransition_to_zero hX h₀ t x)
    refine ⟨hr'.differentiableAt, ?_⟩
    rw [hr'.fderiv, mul_comm D B]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hAr (X t 0 a)).2 (hXr a).2 (norm_nonneg _) hB)


/-- A torus flow with a bound on the forward and inverse deformation from
the initial time. The operators are evaluated at all points of the lift. -/
structure DeformationOn (u : Velocity) (Y : ℝ → Velocity) (T C : ℝ) : Prop where
  flow : IsLabelFlowOn u Y (Icc 0 T)
  lattice : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ (n : Fin 3 → ℤ) x,
    Y s t (x + latticeVector n) = Y s t x + latticeVector n
  bounds : ∀ t ∈ Icc 0 T, (Function.LeftInverse (Y t 0) (Y 0 t) ∧
      Function.RightInverse (Y t 0) (Y 0 t)) ∧
    (∀ x, DifferentiableAt ℝ (Y 0 t) x ∧ ‖fderiv ℝ (Y 0 t) x‖ ≤ C) ∧
    ∀ x, DifferentiableAt ℝ (Y t 0) x ∧ ‖fderiv ℝ (Y t 0) x‖ ≤ C

/-- The derivative of the inverse transition is the inverse of the forward
derivative, evaluated at the corresponding point. -/
theorem DeformationOn.fderiv_inverse {u : Velocity} {Y : ℝ → Velocity} {T C t : ℝ}
    (hY : DeformationOn u Y T C) (ht : t ∈ Icc 0 T) (x : Vec3) :
    let F := fderiv ℝ (Y 0 t) x
    let G := fderiv ℝ (Y t 0) (Y 0 t x)
    G.comp F = .id ℝ Vec3 ∧ F.comp G = .id ℝ Vec3 := by
  dsimp only
  obtain ⟨⟨hLeft, hRight⟩, hF, hG⟩ := hY.bounds t ht
  have hdF := (hF x).1.hasFDerivAt
  have hdG := (hG (Y 0 t x)).1.hasFDerivAt
  have hdF' : HasFDerivAt (Y 0 t) (fderiv ℝ (Y 0 t) x) (Y t 0 (Y 0 t x)) := by
    rwa [hLeft]
  exact ⟨((hdG.comp x hdF).congr_of_eventuallyEq
      (Eventually.of_forall fun y => (hLeft y).symm)).unique (hasFDerivAt_id x),
    ((hdF'.comp (Y 0 t x) hdG).congr_of_eventuallyEq
      (Eventually.of_forall fun y => (hRight y).symm)).unique (hasFDerivAt_id _)⟩

/-- The child velocity has a physical flow whose forward and inverse derivatives
satisfy the deformation estimate in Lemma 5.10. The two first-derivative inputs
are on the actual pulled-back label velocity and its scalar phase velocity. -/
theorem exists_childFlow_of_scaled_bounds
    {U v : Velocity} {X : ℝ → Velocity} {W : ℝ → Vec3 → ℝ → Vec3}
    {T D freq ell h B Γ : ℝ} {a p b : ℕ} {C : ℝ≥0} {k : Vec3}
    (hT : 0 < T) (hT₁ : T ≤ 1)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t))
    (hParent : ∀ t ∈ Icc 0 T, ∀ x : Vec3,
      ‖fderiv ℝ (X 0 t) x‖ ≤ D ∧ ‖fderiv ℝ (X t 0) x‖ ≤ D)
    (hD : 1 ≤ D) (hfreq : 1 ≤ freq) (hell : 0 < ell) (hB : 0 ≤ B)
    (hellSize : ell⁻¹ ≤ D ^ a) (hh : h = freq ^ (-1 / 2 : ℝ))
    (hk : ‖k‖ ≤ D * freq)
    (hb : max a 1 + p + 1 ≤ b) (hΓ : 1 + 4 * B ≤ Γ)
    (hsmall : Γ * D ^ b * freq ^ (-1 / 12 : ℝ) ≤ 1)
    (hc : ContDiffOn ℝ ∞ (Function.uncurry (pullbackField X W v))
      (Icc 0 T ×ˢ (univ : Set PhaseState)))
    (hMagnitude : ∀ t ∈ Icc 0 T, ∀ z,
      ‖scaledField ell h k (pullbackField X W v) t z‖ ≤ C)
    (hCper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (graphField k (pullbackField X W v) t))
    (hLabel : ∀ t ∈ Icc 0 T, ∀ z,
      ‖fderiv ℝ (pullbackField X W v t ∘ labelPhaseScale ell h) z‖ ≤
        B * D ^ p * freq ^ (-5 / 4 : ℝ))
    (hPhase : ∀ t ∈ Icc 0 T, ∀ z,
      ‖fderiv ℝ ((fun q => ⟪k, pullbackField X W v t q⟫_ℝ) ∘ labelPhaseScale ell h) z‖ ≤
        B * D ^ p * freq ^ (-5 / 4 : ℝ)) :
    ∃ Y : ℝ → Velocity,
      DeformationOn (childVelocity U X k W v) Y T (Γ * D ^ b * freq ^ (1 / 4 : ℝ)) := by
  let c := pullbackField X W v
  let F := scaledField ell h k c
  have hh₀ : 0 < h := hh ▸ Real.rpow_pos_of_pos (zero_lt_one.trans_le hfreq) _
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  let m : ℝ := B * D ^ p * freq ^ (-5 / 4 : ℝ)
  have hm : 0 ≤ m := by dsimp only [m]; positivity
  let M : ℝ≥0 := ⟨m, hm⟩
  have hf (t : ℝ) (ht : t ∈ Icc 0 T) : Differentiable ℝ (c t ∘ labelPhaseScale ell h) := by
    apply differentiableOn_univ.mp
    exact (hc.comp (contDiff_const.prodMk (labelPhaseScale ell h).contDiff).contDiffOn
      (fun _ _ => mem_prod.mpr ⟨ht, mem_univ _⟩)).differentiableOn (by simp)
  have hF : ContDiffOn ℝ ∞ (Function.uncurry F) (Icc 0 T ×ˢ (univ : Set PhaseState)) := by
    let L : Vec3 →L[ℝ] PhaseState :=
      (ell⁻¹ • ContinuousLinearMap.id ℝ Vec3).prod (h⁻¹ • innerSL ℝ k)
    have hc' : ContDiffOn ℝ ∞ (fun z : ℝ × PhaseState =>
        c z.1 (labelPhaseScale ell h z.2)) (Icc 0 T ×ˢ univ) :=
      hc.comp (contDiff_fst.prodMk ((labelPhaseScale ell h).contDiff.comp contDiff_snd)).contDiffOn
        (fun z hz => mem_prod.mpr ⟨(mem_prod.mp hz).1, mem_univ _⟩)
    exact L.contDiff.comp_contDiffOn hc'
  have hgrad (t : ℝ) (ht : t ∈ Icc 0 T) (z : PhaseState) :
      ‖fderiv ℝ (F t) z‖ ≤ (1 / 2 : ℝ≥0) := by
    have hC := (hf t ht z).hasFDerivAt
    have hP := ((innerSL ℝ k).differentiable.comp (hf t ht) z).hasFDerivAt
    have hscale := norm_fderiv_scaledField_le hell hh₀ hC hP (hLabel t ht z) (hPhase t ht z)
    have hp : a + p ≤ b := by omega
    have hGamma : 2 * B ≤ (1 / 2 : ℝ) * Γ := by linarith
    have hupper := child_flow_scaled_gradient_le hD hfreq hellSize hh hm hm
      (le_refl m) (le_refl m)
    have hhalf := child_flow_scaled_gradient_small hD hfreq (by positivity : 0 ≤ 2 * B)
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) hp hGamma hsmall (hscale.trans hupper)
    exact_mod_cast hhalf
  have hproj (t : ℝ) (ht : t ∈ Icc 0 T) (z : PhaseState) :
      ‖fderiv ℝ (labelProjection ell ∘ F t) z‖ ≤ M := by
    rw [(hasFDerivAt_labelProjection_scaledField (k := k) hell.ne'
      (hf t ht z).hasFDerivAt).fderiv]
    exact hLabel t ht z
  have htime : ((1 / 2 : ℝ≥0) : ℝ) * (T - 0) ≤ 1 / 2 := by
    push_cast
    linarith
  obtain ⟨Φ, hinit, htraj, hrestart, hdiff, hnorm⟩ :=
    exists_scaledFlow_with_deformation_bounds (labelProjection ell) hF hMagnitude hgrad hproj htime
  let A := labelTransition ell h k Φ
  have hA : IsLabelFlowOn (graphField k c) A (Icc 0 T) :=
    isLabelFlowOn_labelTransition hell.ne' hh₀.ne' hinit htraj
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by norm_num)) hper
  let Y := physicalTransition X A
  have hY : IsLabelFlowOn (childVelocity U X k W v) Y (Icc 0 T) :=
    isLabelFlowOn_physicalTransition hT hX hU hper hK hA
  have hAnorm {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : Vec3) :
      DifferentiableAt ℝ (A s t) x ∧
      ‖fderiv ℝ (A s t) x‖ ≤ 1 + (ell⁻¹ + ‖k‖ * h⁻¹) * (2 * m) := by
    let z := labelPhaseSlope ell h k x
    have hd := (((labelProjection ell).differentiable.comp (hdiff s hs t ht)).sub
      (labelProjection ell).differentiable z).hasFDerivAt
    have hdt : |t - s| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1, hs.2], by linarith [hs.1, ht.2]⟩
    have hdnorm := (hnorm s hs t ht z).2.trans
      (mul_le_of_le_one_right (by positivity : 0 ≤ 2 * (M : ℝ)) hdt)
    obtain ⟨hderiv, hbound⟩ := norm_fderiv_labelTransition_le hell hh₀ hd hdnorm
    exact ⟨hderiv.differentiableAt, hbound⟩
  have hgraph {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : Vec3) :
      labelPhaseSlope ell h k (A s t x) = Φ s t (labelPhaseSlope ell h k x) := by
    have hzero := phaseDefect_transition hell.ne' hh₀.ne' hinit htraj
      hs ht (labelPhaseSlope ell h k x)
    rw [defect_scaledGraph hell.ne' hh₀.ne'] at hzero
    exact scaledGraph_labelProjection_of_defect_eq_zero hell.ne' hh₀.ne' hzero
  have hAi {t : ℝ} (ht : t ∈ Icc 0 T) :
      Function.LeftInverse (A t 0) (A 0 t) ∧ Function.RightInverse (A t 0) (A 0 t) := by
    constructor
    · intro x
      change labelProjection ell (Φ t 0 (labelPhaseSlope ell h k (A 0 t x))) = x
      rw [hgraph h₀ ht x, hrestart 0 h₀ t ht 0 h₀, hinit 0 h₀,
        labelProjection_scaledGraph hell.ne']
    · intro x
      change labelProjection ell (Φ 0 t (labelPhaseSlope ell h k (A t 0 x))) = x
      rw [hgraph ht h₀ x, hrestart t ht 0 h₀ t ht, hinit t ht,
        labelProjection_scaledGraph hell.ne']
  have hCLip (t : ℝ) (ht : t ∈ Icc 0 T) :
      LipschitzWith (M * ‖labelPhaseSlope ell h k‖₊) (graphField k c t) := by
    have hprojEq : (labelProjection ell ∘ F t) = c t ∘ labelPhaseScale ell h := by
      funext z
      simp [F, scaledField, labelProjection, Function.comp_apply, smul_smul, mul_inv_cancel₀ hell.ne']
    have hpl : LipschitzWith M (labelProjection ell ∘ F t) :=
      lipschitzWith_of_nnnorm_fderiv_le (hprojEq.symm ▸ hf t ht)
        (fun z => by exact_mod_cast hproj t ht z)
    have hfield : (labelProjection ell ∘ F t) ∘ labelPhaseSlope ell h k = graphField k c t := by
      funext x
      change labelProjection ell (F t (labelPhaseSlope ell h k x)) = graphField k c t x
      rw [show F = scaledField ell h k c from rfl,
        labelProjection_scaledField hell.ne' (defect_scaledGraph hell.ne' hh₀.ne' k x),
        labelProjection_scaledGraph hell.ne']
    rw [← hfield]
    exact hpl.comp (labelPhaseSlope ell h k).lipschitzWith
  have hYper (s : ℝ) (hs : s ∈ Icc 0 T) (t : ℝ) (ht : t ∈ Icc 0 T)
      (n : Fin 3 → ℤ) (x : Vec3) :
      Y s t (x + latticeVector n) = Y s t x + latticeVector n := by
    change X 0 t (A s t (X s 0 (x + latticeVector n))) = _
    rw [hX.add_latticeVector hK hper hs h₀, hA.add_latticeVector hCLip hCper hs ht,
      hX.add_latticeVector hK hper h₀ ht]
    rfl
  refine ⟨Y, ⟨hY, hYper, fun t ht => ?_⟩⟩
  have hP := hX.inverse hK h₀ ht
  have hAi' := hAi ht
  have hYinv : Function.LeftInverse (Y t 0) (Y 0 t) ∧
      Function.RightInverse (Y t 0) (Y 0 t) := by
    constructor
    · intro x
      change physicalTransition X A t 0 (physicalTransition X A 0 t x) = x
      rw [physicalTransition_to_zero hX h₀, physicalTransition_from_zero hX h₀, hP.1, hAi'.1]
    · intro x
      change physicalTransition X A 0 t (physicalTransition X A t 0 x) = x
      rw [physicalTransition_from_zero hX h₀, physicalTransition_to_zero hX h₀, hAi'.2, hP.2]
  have hfinal := child_flow_deformation_scale_le hD hfreq (show 0 ≤ 2 * B by positivity)
    (show 0 ≤ 2 * m by positivity) hellSize hh hk
    (show 2 * m ≤ (2 * B) * D ^ p * freq ^ (-5 / 4 : ℝ) from le_of_eq (by
      dsimp only [m]
      ring))
    hb (show 1 + 2 * (2 * B) ≤ Γ by linarith)
  obtain ⟨hYf, hYr⟩ := physicalTransition_fderiv_bounds hX h₀
    (fun x => ⟨hX.differentiableAt_transition hT hU hper h₀ ht x, (hParent t ht x).1⟩)
    (fun x => ⟨hX.differentiableAt_transition hT hU hper ht h₀ x, (hParent t ht x).2⟩)
    (hAnorm h₀ ht) (hAnorm ht h₀)
  exact ⟨hYinv, fun x => ⟨(hYf x).1, (hYf x).2.trans hfinal⟩,
    fun x => ⟨(hYr x).1, (hYr x).2.trans hfinal⟩⟩


/-- The physical child deformation from the oscillatory and mean bounds on the
pulled-back profile. The twisted Piola identity supplies the slope divergence
used to estimate the scalar phase speed. -/
theorem exists_childFlow_of_profile_jet_bounds
    {U v : Velocity} {X : ℝ → Velocity} {W : ℝ → Vec3 → ℝ → Vec3}
    {T D freq ell h B Γ : ℝ} {a p b : ℕ} {k : Vec3}
    (hT : 0 < T) (hT₁ : T ≤ 1)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t))
    (hUdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (U t) x = 0)
    (hX₂ : ∀ t ∈ Icc 0 T, ∀ x, ContDiffAt ℝ 2 (X 0 t) x)
    (hParent : ∀ t ∈ Icc 0 T, ∀ x : Vec3,
      ‖fderiv ℝ (X 0 t) x‖ ≤ D ∧ ‖fderiv ℝ (X t 0) x‖ ≤ D)
    (hD : 1 ≤ D) (hfreq : 1 ≤ freq) (hell : 0 < ell) (hB : 0 ≤ B)
    (hellSize : ell⁻¹ ≤ D ^ a) (hh : h = freq ^ (-1 / 2 : ℝ))
    (hk : ‖k‖ ≤ D * freq)
    (hb : max a 1 + (max a 1 + p) + 1 ≤ b) (hΓ : 1 + 40 * B ≤ Γ)
    (hsmall : Γ * D ^ b * freq ^ (-1 / 12 : ℝ) ≤ 1)
    (hc : ContDiffOn ℝ ∞ (Function.uncurry (pullbackField X W v))
      (Icc 0 T ×ˢ (univ : Set PhaseState)))
    (hW : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (Function.uncurry (W t)))
    (hWp : ∀ t ∈ Icc 0 T, ∀ x, Function.Periodic (W t x) 1)
    (hWskew : ∀ t ∈ Icc 0 T, ∀ (n : Fin 3 → ℤ) x s,
      W t (x + latticeVector n) (s + ⟪k, latticeVector n⟫_ℝ) = W t x s)
    (hWdiv : ∀ t ∈ Icc 0 T, ∀ x s,
      divergence (fun y => W t (X t 0 y) s) (X 0 t x) +
        ⟪(fderiv ℝ (X t 0) (X 0 t x)).adjoint k, deriv (W t x) s⟫_ℝ = 0)
    (hvper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (v t))
    (hvdiv : ∀ t ∈ Icc 0 T, ∀ x, DifferentiableAt ℝ (v t) x ∧ divergence (v t) x = 0)
    (hosc : ∀ t ∈ Icc 0 T,
      PhaseJetBound 2 (B * D ^ p * freq ^ (-5 / 4 : ℝ))
        (scaledPhaseProfile ell h (fun x => phaseOscillation (fun s => pullbackField X W v t (x, s)))))
    (hmean : ∀ t ∈ Icc 0 T,
      PhaseJetBound 1 (B * D ^ p * freq ^ (-5 / 2 : ℝ))
        (scaledPhaseProfile ell h (fun x _ => phaseMean (fun s => pullbackField X W v t (x, s))))) :
    ∃ Y : ℝ → Velocity,
      DeformationOn (childVelocity U X k W v) Y T (Γ * D ^ b * freq ^ (1 / 4 : ℝ)) := by
  let c (t : ℝ) := pullbackField X W v t
  let osc : ℝ := B * D ^ p * freq ^ (-5 / 4 : ℝ)
  let avg : ℝ := B * D ^ p * freq ^ (-5 / 2 : ℝ)
  let M : ℝ := 10 * B * D ^ (max a 1 + p) * freq ^ (-5 / 4 : ℝ)
  have hh₀ : 0 < h := hh ▸ Real.rpow_pos_of_pos (zero_lt_one.trans_le hfreq) _
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by norm_num)) hper
  obtain ⟨hRate, hPhaseRate⟩ := child_flow_pullback_profile_scales_le hD hfreq hell hB
    hellSize hh hk (p := p)
  have hc' (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (c t) := by
    apply contDiffOn_univ.mp
    exact hc.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ => mem_prod.mpr ⟨ht, mem_univ _⟩)
  have hdiv (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) (s : ℝ) :
      divergence (fun y => c t (y, s)) x + ⟪k, deriv (fun q => c t (x, q)) s⟫_ℝ = 0 := by
    have hs : DifferentiableAt ℝ (W t x) s :=
      ((hW t ht).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) s
    have hwLabel : DifferentiableAt ℝ (fun y => W t y s) (X t 0 (X 0 t x)) :=
      ((hW t ht).comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) _
    have hwPhysical := hwLabel.comp (X 0 t x)
      (hX.differentiableAt_transition hT hU hper ht h₀ _)
    have hsum : divergence (fun y => W t (X t 0 y) s + v t y) (X 0 t x) =
        divergence (fun y => W t (X t 0 y) s) (X 0 t x) := by
      have hdv := (hvdiv t ht (X 0 t x)).1.hasFDerivAt
      have hdW := hwPhysical.hasFDerivAt
      have hsumW : fderiv ℝ (fun y => W t (X t 0 y) s + v t y) (X 0 t x) =
          fderiv ℝ (fun y => W t (X t 0 y) s) (X 0 t x) + fderiv ℝ (v t) (X 0 t x) := by
        simpa only [Function.comp_def, Pi.add_def] using (hdW.add hdv).fderiv
      rw [divergence_eq_trace_fderiv, hsumW, ContinuousLinearMap.toLinearMap_add, map_add,
        ← divergence_eq_trace_fderiv, ← divergence_eq_trace_fderiv, (hvdiv t ht _).2, add_zero]
    refine slope_divergence_pullbackField hT ht hX hU hper hK hUdiv (hX₂ t ht x)
      ((hc' t ht).differentiable (by simp) (x, s)) hs ?_
    rw [hsum]
    exact hWdiv t ht x s
  have hphase (t : ℝ) (ht : t ∈ Icc 0 T) (z : PhaseState) :
      ‖fderiv ℝ ((fun q => ⟪k, c t q⟫_ℝ) ∘ labelPhaseScale ell h) z‖ ≤ M := by
    let c' (x : Vec3) (s : ℝ) := c t (x, s)
    have hper' (x : Vec3) : Function.Periodic (c' x) 1 := by
      intro s
      simp only [c', c, pullbackField, hWp t ht x s]
    have hd := phaseJetBound_scaled_longitudinal_of_slope_divergence hell hh₀
      (c := c') (hc' t ht) hper' k (hdiv t ht) (hosc t ht) (hmean t ht) 1 le_rfl z
    rw [norm_iteratedFDeriv_one] at hd
    exact hd.trans hPhaseRate
  have hcBound (t : ℝ) (ht : t ∈ Icc 0 T) (z : PhaseState) :
      ‖c t (labelPhaseScale ell h z)‖ ≤ M ∧
      ‖fderiv ℝ (c t ∘ labelPhaseScale ell h) z‖ ≤ M := by
    let c' (x : Vec3) (s : ℝ) := c t (x, s)
    let O := scaledPhaseProfile ell h (fun x => phaseOscillation (c' x))
    let A := scaledPhaseProfile ell h (fun x _ => phaseMean (c' x))
    have hSmoothA : ContDiff ℝ ∞ (Function.uncurry (fun x (_ : ℝ) => phaseMean (c' x))) :=
      (contDiff_and_iteratedFDeriv_phaseInterval (f := c') (hc' t ht) 0 1).1.comp contDiff_fst
    have hA : ContDiff ℝ ∞ A := hSmoothA.comp (labelPhaseScale ell h).contDiff
    have hO : ContDiff ℝ ∞ O := ((hc' t ht).sub hSmoothA).comp (labelPhaseScale ell h).contDiff
    have heq : c t ∘ labelPhaseScale ell h = O + A := by
      funext z
      change c t (labelPhaseScale ell h z) =
        (c t (labelPhaseScale ell h z) - phaseMean (c' (labelPhaseScale ell h z).1)) +
          phaseMean (c' (labelPhaseScale ell h z).1)
      rw [sub_add_cancel]
    have hOjet : PhaseJetBound 2 osc O := hosc t ht
    have hAjet : PhaseJetBound 1 avg A := hmean t ht
    constructor
    · change ‖(c t ∘ labelPhaseScale ell h) z‖ ≤ M
      rw [heq, Pi.add_apply]
      exact (norm_add_le _ _).trans ((add_le_add
        (by simpa only [norm_iteratedFDeriv_zero] using hOjet 0 (by decide) z)
        (by simpa only [norm_iteratedFDeriv_zero] using hAjet 0 (by decide) z)).trans hRate)
    · rw [heq, ((hO.differentiable (by simp) z).hasFDerivAt.add
        (hA.differentiable (by simp) z).hasFDerivAt).fderiv]
      exact (norm_add_le _ _).trans ((add_le_add
        (by simpa only [norm_iteratedFDeriv_one] using hOjet 1 (by decide) z)
        (by simpa only [norm_iteratedFDeriv_one] using hAjet 1 le_rfl z)).trans hRate)
  let C := Real.toNNReal (ell⁻¹ * M + h⁻¹ * (‖k‖ * M))
  have hvel (t : ℝ) (ht : t ∈ Icc 0 T) (z : PhaseState) :
      ‖scaledField ell h k c t z‖ ≤ C :=
    (norm_scaledField_le_of_label_value_bound hell hh₀ (hcBound t ht z).1).trans
      (Real.le_coe_toNNReal _)
  exact exists_childFlow_of_scaled_bounds hT hT₁ hX hU hper hParent hD hfreq hell
    (show 0 ≤ 10 * B by positivity) hellSize hh hk hb (by linarith) hsmall hc hvel
    (fun t ht => graphField_pullback_spatiallyPeriodic hX hK hper h₀ ht (hWskew t ht) (hvper t ht))
    (fun t ht z => (hcBound t ht z).2) hphase

end TorusEuler.ChildFlow
