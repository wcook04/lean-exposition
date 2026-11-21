import TorusEuler.PaperGenericWaveSwitch
import TorusEuler.LaterWavePrimaryPressureBound

/-! The signed leading Hessian and central gradient for every smooth paper cutoff. -/

open ContinuousLinearMap Filter InnerProductSpace Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

noncomputable section

local notation "I(" T ")" => Icc (0 : ℝ) T
local notation "J(" T ")" => Set.prod (Icc (0 : ℝ) T) (univ : Set Vec3)
local notation "Hess[" f "]" => fderiv ℝ (gradient f)

private theorem spatialSlice_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T t : ℝ} {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) J(T)) (ht : t ∈ I(T)) :
    ContDiff ℝ ∞ (f t) :=
  contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

private theorem spatialDerivative_smoothOn_slab
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} {f : ℝ → Vec3 → E} (hT : 0 < T)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) J(T)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 => fderiv ℝ (f p.1) p.2) J(T) := by
  have hJ : UniqueDiffOn ℝ J(T) := (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  refine ((hf.fderivWithin hJ (m := ∞) (by simp)).clm_comp
    (contDiffOn_const (c := inr ℝ ℝ Vec3))).congr ?_
  rintro ⟨t, x⟩ hx
  exact (((hf.differentiableOn (by simp)) (t, x) hx).hasFDerivWithinAt.comp_hasFDerivAt x
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x) (Eventually.of_forall fun y => ⟨hx.1, mem_univ y⟩)).fderiv

private theorem hessian_const_smul (c : ℝ) (f : Vec3 → ℝ) :
    Hess[c • f] = c • Hess[f] := by
  have heq : gradient (c • f) = c • gradient f := by
    funext x
    change (InnerProductSpace.toDual ℝ Vec3).symm (fderiv ℝ (c • f) x) =
      c • (InnerProductSpace.toDual ℝ Vec3).symm (fderiv ℝ f x)
    rw [fderiv_const_smul_field, Pi.smul_apply, map_smul]
  rw [heq, fderiv_const_smul_field]

namespace LocalizedAmplitude.SeedOn

open HierarchyTwistedProfile

variable {T t₀ ell D C r h : ℝ} {center : ℝ → Vec3}
  {U : Velocity} {X : ℝ → Velocity} {k : Vec3}
  {seed : SeedOn (fun t a => fderiv ℝ (U t) (X 0 t a))
    (fun t a => labelWaveVector X 0 a k t) center t₀ T ell D C}

/-- The derivative at the fixed origin includes the value of the chosen cutoff
and the transported central amplitude and covector. -/
theorem genericLeading_parentGraph_center (reg : seed.HierarchyRegularity r h)
    (χ : PaperWaveCutoff t₀ T)
    (hX : IsLabelFlowOn U X I(T)) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J(T))
    (hper : ∀ t ∈ I(T), SpatiallyPeriodic (U t)) (hodd : ∀ t ∈ I(T), Function.Odd (U t))
    {t : ℝ} (ht : t ∈ Icc t₀ T) :
    fderiv ℝ (graphRead (fun u => X u 0) (genericLeading (w := seed) reg k χ) t) 0 =
      χ.value t • rankOne ℝ (center t) (labelWaveVector X 0 0 k t) := by
  let A (u : ℝ) := X u 0
  let V (u : ℝ) (a : Vec3) (s : ℝ) :=
    (χ.value u * radialEnvelope ell a * waveProfile h s) • seed.amplitude u a
  have htI : t ∈ I(T) := ⟨reg.nonneg_start.trans ht.1, ht.2⟩
  have h0 : (0 : ℝ) ∈ I(T) := ⟨le_rfl, reg.end_pos.le⟩
  obtain ⟨K, hLip⟩ := exists_lipschitzWith_of_contDiffOn_periodic reg.end_pos (hU.of_le (by simp)) hper
  have hA := spatialSlice_smooth (f := A) (hX.contDiffOn_inverseLabelFlow reg.end_pos hU hper) htI
  have hneg : A t 0 = -A t 0 := by
    simpa only [A, neg_zero] using hX.odd hLip hodd htI h0 (0 : Vec3)
  have hA₀ : A t 0 = 0 := by
    have h2 : (2 : ℝ) • A t 0 = 0 := calc
      _ = A t 0 + A t 0 := two_smul ℝ _
      _ = A t 0 + -A t 0 := congrArg (A t 0 + ·) hneg
      _ = 0 := by simp
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  have hInv := (hX.inverse hLip h0 htI).2 (0 : Vec3)
  change X 0 t (A t 0) = 0 at hInv
  rw [hA₀] at hInv
  have hκ : (fderiv ℝ (A t) 0).adjoint k = labelWaveVector X 0 0 k t := by
    simp only [labelWaveVector, hInv, A]
  have hLead : graphRead A (genericLeading (w := seed) reg k χ) t =
      localizedTransportedProfile A k V t := by
    funext x
    change (genericLeading (w := seed) reg k χ).val.val.val
      (t, A t x, ⟪k, A t x⟫_ℝ) = _
    rw [genericLeading_eval (w := seed) reg k χ htI, ← phaseTwistedPeriodizeCentered_on_graph]
    simp only [phaseTwistedPeriodizeCentered, V, SeedOn.leading, smul_smul, mul_assoc]
  have ha : ContDiff ℝ ∞ (seed.amplitude t) :=
    contDiffOn_univ.mp (reg.amplitude_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  have hF := hasFDerivAt_inductionPrimaryWave_origin (A := A) (a := seed.amplitude) (k := k)
    (chi := χ.value) reg.phase_pos reg.phase_le_one
    reg.envelope_pos reg.envelope_fits ((hA.differentiable (by simp) 0).hasFDerivAt) hA₀
    (ha.differentiable (by simp) 0)
  have ha₀ : seed.amplitude t 0 = center t := seed.at_center ht
  change HasFDerivAt (localizedTransportedProfile A k V t)
    (χ.value t • rankOne ℝ (seed.amplitude t 0) ((fderiv ℝ (A t) 0).adjoint k)) 0 at hF
  rw [ha₀, hκ] at hF
  rw [show (fun u => X u 0) = A from rfl, hLead]
  exact hF.fderiv

set_option maxHeartbeats 4000000 in
/-- A time-only multiplier in `[0,1]` preserves the signed bound of the
saturated selected switches. The closed active endpoint follows by continuity. -/
theorem genericPressure_hessian_upper_of_switch_family (reg : seed.HierarchyRegularity r h)
    (χ : PaperWaveCutoff t₀ T)
    (hX : IsLabelFlowOn U X I(T)) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J(T))
    (hper : ∀ t ∈ I(T), SpatiallyPeriodic (U t))
    {Q : ℝ} (hQ : 0 ≤ Q)
    (hFamily : ∀ rate (reg' : seed.HierarchyRegularity rate h), ∀ t ∈ I(T), ∀ x v : Vec3,
      ⟪v, Hess[graphRead (fun u => X u 0) (seed.twistedPressure reg' k) t] x v⟫_ℝ ≤ Q * ‖v‖ ^ 2) :
    ∀ t ∈ I(T), ∀ x v : Vec3,
      ⟪v, Hess[graphRead (fun u => X u 0) (genericPressure (w := seed) reg k χ) t] x v⟫_ℝ ≤
        Q * ‖v‖ ^ 2 := by
  let A (t : ℝ) := X t 0
  let p := graphRead A (genericPressure (w := seed) reg k χ)
  intro t ht x v
  change ⟪v, Hess[p t] x v⟫_ℝ ≤ Q * ‖v‖ ^ 2
  by_cases hpre : t < t₀
  · have heq : p t = 0 := by
      funext y
      change (genericPressure (w := seed) reg k χ).val.val.val (t, A t y, ⟪k, A t y⟫_ℝ) = 0
      rw [genericPressure_eval (w := seed) reg k χ ht, χ.zero_before t ht hpre, zero_mul]
    rw [heq]
    have hz : (0 : Vec3 → ℝ) = fun _ => 0 := rfl
    rw [hz, gradient_fun_const', fderiv_fun_const]
    simp only [Pi.zero_apply, zero_apply, inner_zero_right]
    positivity
  have hInterior (u : ℝ) (hu : u ∈ Ioc t₀ T) : ⟪v, Hess[p u] x v⟫_ℝ ≤ Q * ‖v‖ ^ 2 := by
    have huI : u ∈ I(T) := ⟨reg.nonneg_start.trans hu.1.le, hu.2⟩
    let rate := (u - t₀)⁻¹
    have hr : 0 < rate := inv_pos.mpr (sub_pos.mpr hu.1)
    let reg' : seed.HierarchyRegularity rate h :=
      { reg with rate_nonneg := hr.le }
    have hOne : waveSwitch t₀ rate u = 1 := by
      apply Real.smoothTransition.one_of_one_le
      change 1 ≤ (u - t₀)⁻¹ * (u - t₀)
      rw [inv_mul_cancel₀ (sub_ne_zero.mpr hu.1.ne')]
    let q := graphRead A (seed.twistedPressure reg' k)
    have heq : p u = χ.value u • q u := by
      funext y
      change (genericPressure (w := seed) reg k χ).val.val.val (u, A u y, ⟪k, A u y⟫_ℝ) =
        χ.value u * (seed.twistedPressure reg' k).val.val.val (u, A u y, ⟪k, A u y⟫_ℝ)
      rw [genericPressure_eval (w := seed) reg k χ huI, twistedPressure_eval reg' k huI]
      simp only [phaseTwistedPeriodizeCentered, SeedOn.switchedPressure, hOne, one_mul]
    rw [heq, hessian_const_smul]
    change ⟪v, χ.value u • Hess[q u] x v⟫_ℝ ≤ Q * ‖v‖ ^ 2
    rw [real_inner_smul_right]
    exact (mul_le_mul_of_nonneg_left (hFamily rate reg' u huI x v) (χ.range u huI).1).trans
      (mul_le_of_le_one_left (by positivity) (χ.range u huI).2)
  have hP : ContDiffOn ℝ ∞ (Function.uncurry p) J(T) :=
    HierarchySmoothProfile.contDiffOn_graphRead k _
      (hX.contDiffOn_inverseLabelFlow reg.end_pos hU hper)
  have hG : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => gradient (p z.1) z.2) J(T) :=
    (InnerProductSpace.toDual ℝ Vec3).symm.contDiff.comp_contDiffOn
      (spatialDerivative_smoothOn_slab reg.end_pos hP)
  have hH := spatialDerivative_smoothOn_slab (f := fun t => gradient (p t)) reg.end_pos hG
  have hXcont : ContinuousOn (fun u => Hess[p u] x) I(T) :=
    hH.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hu => ⟨hu, mem_univ _⟩)
  have hTime : ContinuousOn (fun u => ⟪v, Hess[p u] x v⟫_ℝ) I(T) :=
    continuousOn_const.inner (hXcont.clm_apply continuousOn_const)
  have hClosure : closure (Ioc t₀ T) = Icc t₀ T := closure_Ioc reg.start_lt_end.ne
  have htClosure : t ∈ closure (Ioc t₀ T) := by
    rw [hClosure]
    exact ⟨le_of_not_gt hpre, ht.2⟩
  apply le_on_closure hInterior _ continuousOn_const htClosure
  rw [hClosure]
  exact hTime.mono (Icc_subset_Icc_left reg.nonneg_start)

end LocalizedAmplitude.SeedOn

open HierarchyTwistedProfile LocalizedAmplitude

set_option maxHeartbeats 2400000 in
/-- The uniform signed leading pressure cap for all paper cutoffs. -/
theorem exists_parent_genericLeading_pressure_hessian_bound
    (W : ℕ → ℝ) (hW : ∀ j, 0 ≤ W j) :
    ∃ (A : ℕ) (C : ℝ), 30 ≤ A ∧ 0 ≤ C ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T t₀ D ell Cseed freq rate : ℝ}
        {a : ℕ} {k : Vec3} {center : ℝ → Vec3},
        0 < T → T ≤ 1 → 2 ≤ D → 1 ≤ freq → A ≤ a → ell⁻¹ = D ^ a →
        ‖labelWaveVector X 0 0 k t₀‖ = freq → ‖k‖ ≤ D * freq →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (X 0 t) x‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (X t 0) (X 0 t x)‖ ≤ D) →
        (∀ n j : ℕ, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
          ‖iteratedFDeriv ℝ j (U t) x‖ ≤ W n * D ^ j) →
        (∀ t ∈ Icc t₀ T, ‖center t‖ ≤ freq ^ (-3 / 4 : ℝ)) →
        let M (t : ℝ) (x : Vec3) := fderiv ℝ (U t) (X 0 t x)
        let κ (t : ℝ) (x : Vec3) := labelWaveVector X 0 x k t
        CenterWaveOn (fun t => M t 0) (fun t => κ t 0) center t₀ T D →
        ∀ (seed : SeedOn M κ center t₀ T ell D Cseed)
          (reg : seed.HierarchyRegularity rate (freq ^ (-1 / 2 : ℝ))),
        ∀ χ : PaperWaveCutoff t₀ T, ∀ t ∈ Icc 0 T, ∀ x v : Vec3,
          ⟪v, fderiv ℝ (gradient (graphRead (fun u => X u 0) (SeedOn.genericPressure (w := seed) reg k χ) t)) x v⟫_ℝ ≤
            (C * D ^ (2 * a + 74) * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2 := by
  obtain ⟨A, C, hA, hC, hBound⟩ := exists_parent_leading_pressure_hessian_bound W hW
  refine ⟨A, C, hA, hC, ?_⟩
  intro U X T t₀ D ell Cinput freq rate a k center hT hTime hD hfreq ha hRadius
    hLaunch hCarrier hX hU hper hF hG hVel hCap M κ hCenter seed reg χ
  have hQ : 0 ≤ C * D ^ (2 * a + 74) * freq ^ (-1 / 4 : ℝ) :=
    mul_nonneg (mul_nonneg hC (pow_nonneg (zero_le_two.trans hD) _))
      (Real.rpow_nonneg (zero_le_one.trans hfreq) _)
  apply SeedOn.genericPressure_hessian_upper_of_switch_family reg χ hX hU hper hQ
  intro _ reg'
  exact hBound hT hTime hD hfreq ha hRadius hLaunch hCarrier hX hU hper hF hG hVel hCap
    hCenter seed reg'

end

end TorusEuler
