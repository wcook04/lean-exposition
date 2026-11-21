import TorusEuler.TerminalHierarchyRelayAssembly

/-! Exact mixed-time completion and relay estimates. -/

open Set Finset
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

set_option maxHeartbeats 2300000

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)
local notation "VProw" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] ℝ)
local notation "SProw" => HierarchyTwistedProfile T k (ℝ →L[ℝ] Vec3)

namespace WaveRelayTimeCoefficients

variable {G M : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)}
  {κ : HierarchyTwistedProfile T k Vec3} {ell freq : ℝ}
  (R : WaveRelayTimeCoefficients G M κ ell freq)

private def profileEvaluation {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : HierarchyProfilePoint) : HierarchyTwistedProfile T k E →ₗ[ℝ] E where
  toFun f := f.val.val.val x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem completionProfile_eval (hT : 0 < T) (h : ℝ)
    (v : VP) (hv : PhaseMeanZero v) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3 × ℝ) :
    (R.completionProfile hT h v hv).val.val.val (t,x) = freq⁻¹ • ∑ i : Fin 3,
      hierarchyRelayCurlRow ell (G.val.val.val (t,x.1,0)) i
        (phaseDirectionalDerivative (hierarchyMixedDirection ell h i.castSucc)
          (relayPotentialProfile (fun a => freq⁻¹ • κ.val.val.val (t,a,0))
            (fun y => v.val.val.val (t,y))) x) := by
  change profileEvaluation (T := T) (k := k) (t,x) (R.completionProfile hT h v hv) = _
  rw [completionProfile, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change (relayPrimitiveTerm hT ell h i v hv R.potential R.potential_phaseIndependent
    (R.curl i)).val.val.val (t,x) = _
  rw [relayPrimitiveTerm_apply hT ell h i v hv _ _ _ ht, R.curl_eq i t ht]
  simp_rw [R.potential_eq t ht]
  congr 1

/-- The coordinate expression for completion is the actual selected
periodic curl completion. -/
theorem completionProfile_eq_complete (hT : 0 < T) (h : ℝ)
    (v : VP) (hv : profilePhaseAverage hT v = 0)
    (hGPhase : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t,a,0) ≠ 0)
    (hell : ell ≠ 0) (hfreq : 0 < freq) :
    let hv' : PhaseMeanZero v := fun t ht a => by
      have he := congrArg (fun u : VP => u.val.val.val (t,a,0)) hv
      exact (HierarchySmoothProfile.profilePhaseAverage_apply hT v.val.val
        (show (t,a,(0:ℝ)) ∈ hierarchyProfileSlab T from ⟨ht, mem_univ _⟩)).symm.trans he
    R.completionProfile hT h v hv' = complete hT G κ hκPhase hκ v := by
  intro hv'
  apply HierarchyTwistedProfile.ext
  rintro ⟨t,x⟩ hx
  rw [completionProfile_eval R hT h v hv' hx.1, complete_apply_relayPotential hT G κ v hGPhase
    hκPhase hκ hv hx.1]
  let κnorm (a : Vec3) := freq⁻¹ • κ.val.val.val (t,a,0)
  let V (y : Vec3 × ℝ) := v.val.val.val (t,y)
  let Q := relayPotentialProfile κnorm V
  have hQa : (relayPhasePrimitive hT v hv' R.potential R.potential_phaseIndependent).val.val.val
      ∘ (fun y : Vec3 × ℝ => (t,y)) = Q := by
    funext y
    rw [Function.comp_apply, relayPhasePrimitive_apply hT v hv' _ _ hx.1, R.potential_eq t hx.1]
    rfl
  have hDiff : DifferentiableAt ℝ Q x := by
    rw [← hQa]
    exact (contDiffOn_univ.mp ((HierarchySmoothProfile.smooth
      (relayPhasePrimitive hT v hv' R.potential R.potential_phaseIndependent).val.val).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨hx.1, mem_univ _⟩)))
      |>.differentiable (by simp) x
  have hNorm (a : Vec3) : freq • κnorm a = κ.val.val.val (t,a,0) := by
    dsimp only [κnorm]
    rw [smul_smul, mul_inv_cancel₀ hfreq.ne', one_smul]
  have hScale : relayPotentialProfile (fun a => κ.val.val.val (t,a,0)) V =
      fun y => freq⁻¹ • Q y := by
    funext y
    change wavePotential (κ.val.val.val (t,y.1,0)) (fun σ => V (y.1,σ)) y.2 = _
    rw [← hNorm y.1]
    exact wavePotential_frequency_scale hfreq (κnorm y.1) (fun σ => V (y.1,σ)) y.2
  rw [← pulledBackCurl_eq_weightedCoordinateSum hell h, hScale]
  unfold hierarchyRelayLabelJet
  rw [fderiv_fun_const_smul hDiff, ContinuousLinearMap.smul_comp, ContinuousLinearMap.smul_comp,
    curlOfDerivative_smul]

private def vectorRelayCost (n : ℕ) : ℝ :=
  2 * terminalHierarchyProductCost (ContinuousLinearMap.apply ℝ Vec3 (E := Vec3)).flip n *
    terminalHierarchyProductCost (ContinuousLinearMap.apply ℝ Vec3 (E := Vec3)).flip (n+1)

private def pressureRelayCost (n : ℕ) : ℝ :=
  2 * terminalHierarchyProductCost (ContinuousLinearMap.apply ℝ Vec3 (E := ℝ)).flip n *
    terminalHierarchyProductCost (ContinuousLinearMap.apply ℝ ℝ (E := Vec3)).flip (n+1)

/-- A common order constant for the velocity and pressure label terms. -/
def terminalWaveRelayTimeOrderCost (n : ℕ) : ℝ :=
  9 * (vectorRelayCost n + pressureRelayCost n)

theorem terminalWaveRelayTimeOrderCost_nonneg (n : ℕ) : 0 ≤ terminalWaveRelayTimeOrderCost n := by
  unfold terminalWaveRelayTimeOrderCost vectorRelayCost pressureRelayCost terminalHierarchyProductCost
  positivity

private theorem timeJetSeminorm_relayPrimitiveTerm_le_of_caps
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (hT : 0 < T) (q : ℕ) (ell h : ℝ) (n : ℕ)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ) {C : ℝ} (hτ : ∀ t ∈ A, ‖τ t‖ ≤ C)
    (i : Fin 3) (f : VP) (hf : PhaseMeanZero f)
    (c : HierarchyTwistedProfile T k (Vec3 →L[ℝ] F))
    (hc : HierarchyPeriodicProfile.PhaseIndependent c.val.val)
    (row : HierarchyTwistedProfile T k (F →L[ℝ] Vec3)) {K : ℝ} (hK : 0 ≤ K)
    (hInner : timeJetSeminorm hT q (unweightedSeminorm False ell h (n+1) hT) c ≤ K)
    (hOuter : timeJetSeminorm hT q (unweightedSeminorm False ell h n hT) row ≤ K) :
    timeJetSeminorm hT q (boundedWeightSeminorm False ell h n hT hA τ hτ)
        (relayPrimitiveTerm hT ell h i f hf c hc row) ≤
      (2 * terminalHierarchyProductCost (ContinuousLinearMap.apply ℝ Vec3 (E := F)).flip n *
        terminalHierarchyProductCost (ContinuousLinearMap.apply ℝ F (E := Vec3)).flip (n + 1)) * K ^ 2 *
        timeJetSeminorm hT q (boundedWeightSeminorm False ell h (n + 1) hT hA τ hτ) f := by
  refine (timeJetSeminorm_relayPrimitiveTerm_le hT q ell h n hA τ hτ i f hf c hc row).trans ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ ?_) (apply_nonneg _ _)
  · rw [pow_two]
    exact mul_le_mul hOuter hInner (apply_nonneg _ _) hK
  · unfold terminalHierarchyProductCost
    positivity

private theorem timeSeminorm_sum_fin3_le (N : Seminorm ℝ VP) (u : Fin 3 → VP) {C : ℝ}
    (h : ∀ i, N (u i) ≤ C) : N (∑ i, u i) ≤ 3 * C := by
  have hSum : N (∑ i, u i) ≤ ∑ i, N (u i) := by
    let := N.toAddGroupSeminorm.toSeminormedAddCommGroup
    exact norm_sum_le (Finset.univ : Finset (Fin 3)) u
  refine hSum.trans ((Finset.sum_le_sum fun i _ => h i).trans_eq ?_)
  simp

/-- Quantitative completion estimate with the original inverse carrier
factor after any fixed number of time differentiations. -/
theorem completionProfile_timeJet_le (hT : 0 < T) (q : ℕ) (h : ℝ) (n : ℕ)
    (hfreq : 0 < freq) {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ)
    {C K : ℝ} (hτ : ∀ t ∈ A, ‖τ t‖ ≤ C) (hK : 0 ≤ K)
    (hCoeff : WaveRelayTimeCoefficientBudget R hT h q n K) (v : VP) (hv : PhaseMeanZero v) :
    timeJetSeminorm hT q (boundedWeightSeminorm False ell h n hT hA τ hτ) (R.completionProfile hT h v hv) ≤
      terminalWaveRelayTimeOrderCost n * K ^ 2 * freq⁻¹ *
        timeJetSeminorm hT q (boundedWeightSeminorm False ell h (n + 1) hT hA τ hτ) v := by
  let N : Seminorm ℝ VP := timeJetSeminorm hT q (boundedWeightSeminorm False ell h n hT hA τ hτ)
  let Wv := timeJetSeminorm hT q (boundedWeightSeminorm False ell h (n + 1) hT hA τ hτ) v
  change N (R.completionProfile hT h v hv) ≤ _ * Wv
  rw [completionProfile, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hfreq)]
  have h := timeSeminorm_sum_fin3_le N _ fun i => timeJetSeminorm_relayPrimitiveTerm_le_of_caps
    hT q ell h n hA τ hτ i v hv R.potential R.potential_phaseIndependent (R.curl i) hK
    hCoeff.potential (hCoeff.curl i)
  refine (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hfreq.le)).trans ?_
  have hv₀ : 0 ≤ vectorRelayCost n := by unfold vectorRelayCost terminalHierarchyProductCost; positivity
  have hp₀ : 0 ≤ pressureRelayCost n := by unfold pressureRelayCost terminalHierarchyProductCost; positivity
  have hcmp : 3 * vectorRelayCost n ≤ terminalWaveRelayTimeOrderCost n := by
    unfold terminalWaveRelayTimeOrderCost
    linarith
  change freq⁻¹ * (3 * (vectorRelayCost n * K ^ 2 * Wv)) ≤ _
  rw [show freq⁻¹ * (3 * (vectorRelayCost n * K ^ 2 * Wv)) =
    3 * vectorRelayCost n * K ^ 2 * freq⁻¹ * Wv by ring]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcmp (sq_nonneg K))
      (inv_nonneg.mpr hfreq.le)) (apply_nonneg _ _)

/-- The five normalized primitive terms in the relay carry just one
spatial derivative and one inverse carrier factor, uniformly in time order. -/
theorem relayProfile_timeJet_le (hT : 0 < T) (q : ℕ) (h : ℝ) (n : ℕ)
    (hfreq : 0 < freq) {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ)
    {C K : ℝ} (hτ : ∀ t ∈ A, ‖τ t‖ ≤ C) (hK : 0 ≤ K)
    (hCoeff : WaveRelayTimeCoefficientBudget R hT h q n K)
    (v f : VP) (hv : PhaseMeanZero v) (hf : PhaseMeanZero f) :
    timeJetSeminorm hT q (boundedWeightSeminorm False ell h n hT hA τ hτ) (R.relayProfile hT h v f hv hf) ≤
      terminalWaveRelayTimeOrderCost n * K ^ 2 * freq⁻¹ *
        (timeJetSeminorm hT q (boundedWeightSeminorm False ell h (n + 1) hT hA τ hτ) v +
          timeJetSeminorm hT q (boundedWeightSeminorm False ell h (n + 1) hT hA τ hτ) f) := by
  let N : Seminorm ℝ VP := timeJetSeminorm hT q (boundedWeightSeminorm False ell h n hT hA τ hτ)
  let W : Seminorm ℝ VP := timeJetSeminorm hT q (boundedWeightSeminorm False ell h (n + 1) hT hA τ hτ)
  let H := (vectorRelayCost n + pressureRelayCost n) * K ^ 2
  have hv₀ : 0 ≤ vectorRelayCost n := by unfold vectorRelayCost terminalHierarchyProductCost; positivity
  have hp₀ : 0 ≤ pressureRelayCost n := by unfold pressureRelayCost terminalHierarchyProductCost; positivity
  have hV (g : VP) : vectorRelayCost n * K ^ 2 * W g ≤ H * W g :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hp₀) (sq_nonneg K))
      (apply_nonneg W g)
  have hP (g : VP) : pressureRelayCost n * K ^ 2 * W g ≤ H * W g :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hv₀) (sq_nonneg K))
      (apply_nonneg W g)
  change N (R.relayProfile hT h v f hv hf) ≤ _ * (W v + W f)
  rw [relayProfile, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hfreq)]
  apply le_trans (mul_le_mul_of_nonneg_left (timeSeminorm_sum_fin3_le N _ (C := 3 * H * (W v + W f)) ?_)
    (inv_nonneg.mpr hfreq.le))
  · unfold terminalWaveRelayTimeOrderCost H
    exact le_of_eq (by ring)
  · intro i
    have h₁ := (timeJetSeminorm_relayPrimitiveTerm_le_of_caps hT q ell h n hA τ hτ
      i v hv R.potentialTime R.potentialTime_phaseIndependent (R.curl i) hK
        hCoeff.potentialTime (hCoeff.curl i)).trans (hV v)
    have h₂ := (timeJetSeminorm_relayPrimitiveTerm_le_of_caps hT q ell h n hA τ hτ
      i f hf R.potential R.potential_phaseIndependent (R.curl i) hK
        hCoeff.potential (hCoeff.curl i)).trans (hV f)
    have h₃ := (timeJetSeminorm_relayPrimitiveTerm_le_of_caps hT q ell h n hA τ hτ
      i v hv R.potential R.potential_phaseIndependent (R.material i) hK
        hCoeff.potential (hCoeff.material i)).trans (hV v)
    have h₄ := (timeJetSeminorm_relayPrimitiveTerm_le_of_caps hT q ell h n hA τ hτ
      i v hv R.pressureAmplitude R.pressureAmplitude_phaseIndependent (R.gradient i) hK
        hCoeff.pressureAmplitude (hCoeff.gradient i)).trans (hP v)
    have h₅ := (timeJetSeminorm_relayPrimitiveTerm_le_of_caps hT q ell h n hA τ hτ
      i f hf R.pressureSource R.pressureSource_phaseIndependent (R.gradient i) hK
        hCoeff.pressureSource (hCoeff.gradient i)).trans (hP f)
    refine (map_add_le_add N _ _).trans (add_le_add
      ((map_add_le_add N _ _).trans (add_le_add ((map_add_le_add N _ _).trans (add_le_add h₁ h₂)) h₃))
      ((map_add_le_add N _ _).trans (add_le_add h₄ h₅))) |>.trans ?_
    have hf₀ : 0 ≤ H * W f := mul_nonneg (mul_nonneg (add_nonneg hv₀ hp₀) (sq_nonneg K))
      (apply_nonneg W f)
    linarith

private theorem phasePrimitive_add_local {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f g : ℝ → E} (hf : Continuous f)
    (hg : Continuous g) (s : ℝ) :
    phasePrimitive (fun σ => f σ + g σ) s = phasePrimitive f s + phasePrimitive g s := by
  have h := phasePrimitive_deriv
    (fun σ => (hasDerivAt_phasePrimitive hf σ).add (hasDerivAt_phasePrimitive hg σ)) (hf.add hg)
  rw [h]
  show phasePrimitive f s + phasePrimitive g s -
      phaseMean (fun σ => phasePrimitive f σ + phasePrimitive g σ) = _
  rw [phaseMean_add (continuous_iff_continuousAt.2 fun σ => (hasDerivAt_phasePrimitive hf σ).continuousAt)
    (continuous_iff_continuousAt.2 fun σ => (hasDerivAt_phasePrimitive hg σ).continuousAt),
    phaseMean_phasePrimitive hf, phaseMean_phasePrimitive hg, add_zero, sub_zero]

private theorem relaySlice_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : HierarchyTwistedProfile T k E) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContDiff ℝ ∞ (fun x : Vec3 × ℝ => f.val.val.val (t,x)) :=
  contDiffOn_univ.mp ((HierarchySmoothProfile.smooth f.val.val).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨ht, mem_univ _⟩))

/-- The expression measured by the factorial norm is precisely the
canonical physical relay at every time and independent phase. -/
theorem relayProfile_eq_waveRelayAt (hT : 0 < T) (h : ℝ) (v f : VP)
    (hv : PhaseMeanZero v) (hf : PhaseMeanZero f) (hell : ell ≠ 0) (hfreq : 0 < freq)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3 × ℝ) :
    (R.relayProfile hT h v f hv hf).val.val.val (t,x) = waveRelayAt G M κ v f t x := by
  let K (a : Vec3) := freq⁻¹ • κ.val.val.val (t,a,0)
  let Str (a : Vec3) := M.val.val.val (t,a,0)
  let V (y : Vec3 × ℝ) := v.val.val.val (t,y)
  let F (y : Vec3 × ℝ) := f.val.val.val (t,y)
  let q0 := relayPhasePrimitive hT v hv R.potential R.potential_phaseIndependent
  let qv := relayPhasePrimitive hT v hv R.potentialTime R.potentialTime_phaseIndependent
  let qf := relayPhasePrimitive hT f hf R.potential R.potential_phaseIndependent
  let pv := relayPhasePrimitive hT v hv R.pressureAmplitude R.pressureAmplitude_phaseIndependent
  let pf := relayPhasePrimitive hT f hf R.pressureSource R.pressureSource_phaseIndependent
  have hVcont (a : Vec3) : Continuous (fun σ => V (a,σ)) :=
    (relaySlice_smooth v ht).continuous.comp (continuous_const.prodMk continuous_id)
  have hFcont (a : Vec3) : Continuous (fun σ => F (a,σ)) :=
    (relaySlice_smooth f ht).continuous.comp (continuous_const.prodMk continuous_id)
  have hQ0 : relayPotentialProfile K V = fun y => q0.val.val.val (t,y) := by
    funext y
    rw [show q0.val.val.val (t,y) = _ from relayPhasePrimitive_apply hT v hv _ _ ht y.1 y.2,
      R.potential_eq t ht]
    rfl
  have hQt : relayPotentialTimeProfile Str K V F =
      fun y => qv.val.val.val (t,y) + qf.val.val.val (t,y) := by
    funext y
    rw [show qv.val.val.val (t,y) = _ from relayPhasePrimitive_apply hT v hv _ _ ht y.1 y.2,
      show qf.val.val.val (t,y) = _ from relayPhasePrimitive_apply hT f hf _ _ ht y.1 y.2,
      R.potentialTime_eq t ht, R.potential_eq t ht]
    unfold relayPotentialTimeProfile
    simp_rw [wavePotentialTimeSource_eq_coefficients]
    exact phasePrimitive_add_local
      ((hierarchyRelayTimeAmplitudeCoefficient (Str y.1) (K y.1)).continuous.comp (hVcont y.1))
      ((hierarchyRelayPotentialCoefficient (K y.1)).continuous.comp (hFcont y.1)) y.2
  have hP : relayPhasePressureProfile Str K V F =
      fun y => pv.val.val.val (t,y) + pf.val.val.val (t,y) := by
    funext y
    rw [show pv.val.val.val (t,y) = _ from relayPhasePrimitive_apply hT v hv _ _ ht y.1 y.2,
      show pf.val.val.val (t,y) = _ from relayPhasePrimitive_apply hT f hf _ _ ht y.1 y.2,
      R.pressureAmplitude_eq t ht, R.pressureSource_eq t ht]
    unfold relayPhasePressureProfile oscillatoryPhasePressure
    simp_rw [oscillatoryPressureSlope_eq_coefficients]
    exact phasePrimitive_add_local
      ((hierarchyRelayPressureAmplitudeCoefficient (Str y.1) (K y.1)).continuous.comp (hVcont y.1))
      ((hierarchyRelayPressureSourceCoefficient (K y.1)).continuous.comp (hFcont y.1)) y.2
  have hq0 := (relaySlice_smooth q0 ht).differentiable (by simp) x
  have hqv := (relaySlice_smooth qv ht).differentiable (by simp) x
  have hqf := (relaySlice_smooth qf ht).differentiable (by simp) x
  have hpv := (relaySlice_smooth pv ht).differentiable (by simp) x
  have hpf := (relaySlice_smooth pf ht).differentiable (by simp) x
  have hScale : (fun a => freq • K a) = fun a => κ.val.val.val (t,a,0) := by
    funext a
    dsimp only [K]
    rw [smul_smul, mul_inv_cancel₀ hfreq.ne', one_smul]
  have hRepr := hierarchyLinearRelayAt_frequency_scale hfreq
    (G.val.val.val (t,x.1,0)) Str K V F x (hQ0.symm ▸ hq0 : DifferentiableAt ℝ (relayPotentialProfile K V) x)
    (hQt.symm ▸ (hqv.add hqf) : DifferentiableAt ℝ (relayPotentialTimeProfile Str K V F) x)
    (hP.symm ▸ (hpv.add hpf) : DifferentiableAt ℝ (relayPhasePressureProfile Str K V F) x)
  rw [hScale] at hRepr
  change profileEvaluation (T := T) (k := k) (t,x) (R.relayProfile hT h v f hv hf) =
    hierarchyLinearRelayAt (G.val.val.val (t,x.1,0)) (Str x.1)
      (relayPotentialProfile (fun a => κ.val.val.val (t,a,0)) V)
      (relayPotentialTimeProfile Str (fun a => κ.val.val.val (t,a,0)) V F)
      (relayPhasePressureProfile Str (fun a => κ.val.val.val (t,a,0)) V F) x
  rw [hRepr, hierarchyLinearRelayAt_eq_coordinate_sum hell h, hQ0, hQt, hP,
    relayProfile, map_smul, map_sum]
  apply congrArg (fun w : Vec3 => freq⁻¹ • w)
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_add]
  change
    (((relayPrimitiveTerm hT ell h i v hv R.potentialTime R.potentialTime_phaseIndependent (R.curl i)).val.val.val (t,x) +
      (relayPrimitiveTerm hT ell h i f hf R.potential R.potential_phaseIndependent (R.curl i)).val.val.val (t,x)) +
      (relayPrimitiveTerm hT ell h i v hv R.potential R.potential_phaseIndependent (R.material i)).val.val.val (t,x)) +
    ((relayPrimitiveTerm hT ell h i v hv R.pressureAmplitude R.pressureAmplitude_phaseIndependent (R.gradient i)).val.val.val (t,x) +
      (relayPrimitiveTerm hT ell h i f hf R.pressureSource R.pressureSource_phaseIndependent (R.gradient i)).val.val.val (t,x)) = _
  simp only [relayPrimitiveTerm, applyField_eval _ _ (show (t,x) ∈ hierarchyProfileSlab T from ⟨ht, mem_univ _⟩),
    scaledProfileDerivative_apply hT ell h i.castSucc _ ht, R.curl_eq i t ht, R.material_eq i t ht, R.gradient_eq i t ht]
  have hdq : fderiv ℝ (fun y => qv.val.val.val (t,y) + qf.val.val.val (t,y)) x =
      fderiv ℝ (fun y => qv.val.val.val (t,y)) x + fderiv ℝ (fun y => qf.val.val.val (t,y)) x :=
    fderiv_add hqv hqf
  have hdp : fderiv ℝ (fun y => pv.val.val.val (t,y) + pf.val.val.val (t,y)) x =
      fderiv ℝ (fun y => pv.val.val.val (t,y)) x + fderiv ℝ (fun y => pf.val.val.val (t,y)) x :=
    fderiv_add hpv hpf
  simp only [phaseDirectionalDerivative, hdq, hdp, add_apply, map_add, Str]
  abel

end WaveRelayTimeCoefficients

end

end TorusEuler.HierarchyTwistedProfile
