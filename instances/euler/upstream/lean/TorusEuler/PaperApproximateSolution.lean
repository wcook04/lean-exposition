import TorusEuler.PaperGraphReadout
import TorusEuler.HierarchyPhysicalPressureBounds
import TorusEuler.HierarchyPhysicalVelocityBounds
import TorusEuler.HierarchyCentralRemainder

/-! Approximate flow, pressure, and central gradient in Lemmas 5.8 and 5.9. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData

open HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3} {U : Velocity} {X : ℝ → Velocity} {p : Pressure}
  {hT : 0 < T} {d : ParentGeometry hT U X k} {P : ℕ}
  (b : PhysicalApproximationData d p P)

local notation "I" => Icc (0 : ℝ) T
local notation "J" => Set.prod (Icc (0 : ℝ) T) (univ : Set Vec3)

/-- The exact approximate equation and its two residual terms, in the
notation of (5.46). -/
theorem paperLemma58_approximateEquation (props : PhysicalApproximationProperties b) :
    ContDiffOn ℝ ∞ (Function.uncurry b.velocity) J ∧
    ContDiffOn ℝ ∞ (Function.uncurry b.pressure) J ∧
    (∀ t ∈ I, Function.Odd (b.velocity t) ∧ ∀ x, divergence (b.velocity t) x = 0) ∧
    ∀ t ∈ I, momentumResidual I b.velocity b.pressure t =
      graphRead (fun r => X r 0) (b.operators.remainder b.profiles P) t +
      graphRead (fun r => X r 0) (b.leading.leadingSwitch + b.leading.completionSwitch) t := by
  refine ⟨props.velocity_smooth, props.pressure_smooth,
    fun t ht => ⟨(props.reflection t ht).1, props.divergence_free t ht⟩, ?_⟩
  intro t ht
  rw [show momentumResidual I b.velocity b.pressure t = b.residual t from funext (props.residual_exact t ht)]
  exact b.residual_eq_graph_tail_add_switch t

/-- The oscillatory Hölder estimate in (5.47), through any prescribed
spatial order. Its parent exponent is linear in the spatial order and
its carrier exponent is exactly the one in the paper. -/
theorem paperLemma58_oscillationHolder (hP : 1 ≤ P)
    {ell h freq C D L : ℝ} {a r bExp m : ℕ}
    (hf : 1 ≤ freq) (hC : 0 ≤ C) (hell : 0 < ell) (hh : 0 < h)
    (hD : 1 ≤ D) (hL : 1 ≤ L) (hLabel : ell⁻¹ ≤ D ^ a)
    (hWidth : h = freq ^ (-1 / 2 : ℝ)) (hCarrier : ‖k‖ ≤ D * freq)
    (hExp : max a 1 + 1 ≤ bExp) (hr : 2 * r ≤ bExp)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγmax : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hinactive : ∀ t ∈ I, t < t₀ → b.oscillation t = 0)
    (hlevels : ∀ i ∈ Finset.Icc 1 P, HierarchyLevelBound
      (actualMeasuredLevels b.operators b.profiles P b.leading.completionSwitch b.parentResidual
        freq (zero_le_one.trans hf) ell h hT ht₀ htT γ hγ hpos) freq (D ^ r) C (m + 1) i)
    (B : ℝ → Vec3 → Vec3 →L[ℝ] Vec3)
    (hA : ∀ t ∈ I, ContDiff ℝ ∞ (X t 0))
    (hB : ∀ t ∈ I, ∀ x, B t (X t 0 x) = fderiv ℝ (X t 0) x)
    (hBreg : ∀ t ∈ I, ContDiff ℝ ∞ (B t))
    (hcoeff : ∀ t ∈ I, ∀ j ≤ m + 1, ∀ x, ell ^ j * ‖iteratedFDeriv ℝ j (B t) x‖ ≤ L * D) :
    let Cm := (3 * (m + 1) : ℝ) * oscillatoryGraphJetCost L (m + 1) *
      (2 * ((Finset.Icc 1 P).card : ℝ) * C)
    ∀ t ∈ I, SpatialHolderHalf m (b.oscillation t) ∧
      spatialHolderHalfNorm m (b.oscillation t) ≤
        Cm * D ^ (bExp * (m + 2)) * freq ^ ((3 : ℝ) * ((m : ℝ) + 1) / 2 - 5 / 4) := by
  intro Cm t ht
  let F := b.profiles.velocity P - b.operators.average (b.profiles.velocity P)
  let N := amplitudeSeminorm False ell h (m + 1) hT ht₀ htT γ hγ hpos F
  let prefactor := (3 * (m + 1) : ℝ) * oscillatoryGraphJetCost L (m + 1)
  let C₀ := 2 * ((Finset.Icc 1 P).card : ℝ) * C
  let dExp := (max a 1 + 1) * (m + 1)
  have hCm : Cm = prefactor * C₀ := rfl
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  have hPre : 0 ≤ prefactor := by
    have hL₀ := zero_le_one.trans hL
    dsimp only [prefactor, oscillatoryGraphJetCost]
    positivity
  have hPower : dExp + 2 * r ≤ bExp * (m + 2) := by
    dsimp only [dExp]
    calc
      _ ≤ bExp * (m + 1) + bExp := Nat.add_le_add (Nat.mul_le_mul_right _ hExp) hr
      _ = _ := by
        rw [show m + 2 = m + 1 + 1 by omega]
        simp only [Nat.mul_add, Nat.mul_one]
  by_cases hactive : t₀ ≤ t
  · have ht' : t ∈ Icc t₀ T := ⟨hactive, ht.2⟩
    have hMeasured := (b.velocityProfileSums_of_actualLevels hP (m + 1) hf
      (one_le_pow₀ hD) hC ht₀ htT γ hγ hpos hlevels).1
    have hNorm : N ≤ C₀ * D ^ (2 * r) * freq ^ (-5 / 4 : ℝ) := by
      refine hMeasured.trans_eq ?_
      rw [← pow_mul, Nat.mul_comm r 2]
    obtain ⟨_, hreg, hsize⟩ :=
      paperLemma57_graphWeighted hT F ht₀ htT γ hγ hpos
        (A := fun s => X s 0) (B := B t) (m := m) (a := a) (L := L)
        ht' hell hh hD hf hL hLabel hWidth hCarrier
        (hA t ht) (hB t ht) (hBreg t ht) (hcoeff t ht)
    change SpatialHolderHalf m (b.oscillation t) at hreg
    change spatialHolderHalfNorm m (b.oscillation t) ≤
      (3 * (m + 1) : ℝ) * (oscillatoryGraphJetCost L (m + 1) * D ^ dExp *
        freq ^ ((3 : ℝ) * ↑(m + 1) / 2)) * γ t * N at hsize
    refine ⟨hreg, hsize.trans ?_⟩
    have hDP : 0 ≤ D ^ dExp := pow_nonneg (zero_le_one.trans hD) _
    have hf₀ := zero_lt_one.trans_le hf
    have hF := Real.rpow_nonneg hf₀.le ((3 : ℝ) * ↑(m + 1) / 2)
    have hG := (hpos t ht').le
    calc
      _ = (prefactor * D ^ dExp * freq ^ ((3 : ℝ) * ↑(m + 1) / 2)) * γ t * N := by
        dsimp only [prefactor]
        ring_nf
      _ ≤ (prefactor * D ^ dExp * freq ^ ((3 : ℝ) * ↑(m + 1) / 2)) * 1 *
          (C₀ * D ^ (2 * r) * freq ^ (-5 / 4 : ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hγmax t ht') (mul_nonneg (mul_nonneg hPre hDP) hF))
          hNorm (apply_nonneg _ _) (by positivity)
      _ = Cm * D ^ (dExp + 2 * r) * freq ^ ((3 : ℝ) * ((m : ℝ) + 1) / 2 - 5 / 4) := by
        rw [hCm, pow_add, sub_eq_add_neg, Real.rpow_add hf₀]
        push_cast
        ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hPower) (hCm ▸ mul_nonneg hPre hC₀))
        (by positivity)
  · rw [hinactive t ht (lt_of_not_ge hactive)]
    have hZeroJets : PhaseJetBound (m + 1) 0 (0 : Vec3 → Vec3) := by
      intro j hj x
      simp
    have hs : ContDiff ℝ ∞ (0 : Vec3 → Vec3) := contDiff_const
    obtain ⟨hzero, hzeroNorm⟩ := spatialHolderHalfNorm_le_of_uniformJets (m := m) hs le_rfl hZeroJets
    have hCpos := hCm ▸ mul_nonneg hPre hC₀
    exact ⟨hzero, (by simpa only [mul_zero] using hzeroNorm : spatialHolderHalfNorm m (0 : Vec3 → Vec3) ≤ 0).trans
      (by positivity)⟩

/-- The same leading seed gives the signed pressure Hessian and the exact
central rank-one velocity derivative used in Lemma 5.9. -/
theorem paperLemma59_leadingSeedReadout
    {center : ℝ → Vec3} {t₀ ell D C rate h freq B K : ℝ}
    (seed : LocalizedAmplitude.SeedOn (fun t a => fderiv ℝ (U t) (X 0 t a))
      (fun t a => labelWaveVector X 0 a k t) center t₀ T ell D C)
    (reg : seed.HierarchyRegularity rate h)
    (hSeedVelocity : b.leading.output.V = seed.twistedLeading reg k)
    (hSeedPressure : b.leading.output.p = seed.twistedPressure reg k)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hPer : ∀ t ∈ I, SpatiallyPeriodic (U t)) (hOdd : ∀ t ∈ I, Function.Odd (U t))
    (hBudget : ∀ t ∈ I, seed.PrimaryPressureBudget (fun u => X u 0) k rate h t freq B K) :
    (∀ t ∈ I, ∀ x v, ⟪v, fderiv ℝ (gradient (b.leadingPressure t)) x v⟫_ℝ ≤
      ((2 * B ^ 3 + (3 * B ^ 4 + B ^ 2) * K) * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2) ∧
    ∀ t ∈ I, fderiv ℝ (b.leadingVelocity t) 0 = waveSwitch t₀ rate t •
      InnerProductSpace.rankOne ℝ (center t) (labelWaveVector X 0 0 k t) := by
  refine ⟨b.leadingPressure_hessian_upper_of_seed seed reg hSeedPressure hX hU hPer hBudget, ?_⟩
  intro t ht
  rw [leadingVelocity, hSeedVelocity]
  exact (LocalizedAmplitude.SeedOn.hasFDerivAt_twistedLeading_parentGraph_origin
    (seed := seed) reg hX hU hPer hOdd ht).fderiv

/-- The two nonleading pressure Hessians in Lemma 5.9 follow from the
same order-two measured hierarchy. The mean pressure uses its physical
Poisson equation and the selected mean velocity and force. -/
theorem paperLemma59_higherMeanHessians (hP : 1 ≤ P)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hPer : ∀ t ∈ I, SpatiallyPeriodic (U t))
    (hDiv : ∀ t ∈ I, ∀ x, divergence (U t) x = 0)
    {D freq ell h C Cjet Cparent Aell Kwave t₀ : ℝ} {r a : ℕ} {S : Set Vec3}
    (hS : IsClosed S) (hInactive : b.leading.Inactive t₀ S)
    (hD : 1 ≤ D) (hf : 1 ≤ freq) (hell : 0 < ell) (hWidth : h = freq ^ (-1 / 2 : ℝ))
    (hEllInv : ell⁻¹ ≤ Aell) (hCarrier : ‖k‖ ≤ Kwave * freq)
    (hC : 0 ≤ C) (hCjet : 0 ≤ Cjet) (hCparent : 0 ≤ Cparent)
    (hMeanCost : ell⁻¹ * Cjet ≤ D ^ a)
    (hParent : ∀ t ∈ I, SpatialHolderHalf 0 (fderiv ℝ (U t)) ∧
      spatialHolderHalfNorm 0 (fderiv ℝ (U t)) ≤ Cparent * D ^ 2)
    (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγle : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hCoframe : ∀ t ∈ I, ∀ j ≤ 2, ∀ x,
      ell ^ j * ‖iteratedFDeriv ℝ j (fun y => d.inverse.val.val.val (t, y, 0)) x‖ ≤ Cjet)
    (hAdjoint : ∀ t ∈ I, ∀ j ≤ 1, ∀ x,
      ell ^ j * ‖iteratedFDeriv ℝ j (fun y => (d.inverse.val.val.val (t, y, 0)).adjoint) x‖ ≤ Cjet)
    (hStrain : ∀ t ∈ I, ∀ j ≤ 1, ∀ x,
      ell ^ j * ‖iteratedFDeriv ℝ j (fun y => d.strain.val.val.val (t, y, 0)) x‖ ≤ Cjet)
    (hProjection : ∀ t ∈ I, ∀ j ≤ 1, ∀ x,
      ell ^ j * ‖iteratedFDeriv ℝ j
        (fun y => hierarchyLongitudinalProjection (d.covector.val.val.val (t, y, 0))) x‖ ≤ Cjet)
    (hLevels : ∀ n ≤ 2, ∀ i ∈ Finset.Icc 1 P, HierarchyLevelBound
      (actualMeasuredLevels b.operators b.profiles P b.leading.completionSwitch b.parentResidual
        freq (zero_le_one.trans hf) ell h hT ht₀ htT γ hγ hpos) freq (D ^ r) C n i) :
    let Cmean := ((Finset.Icc 2 P).card : ℝ) * C
    (∀ t ∈ I, ∀ x, ‖fderiv ℝ (gradient (b.higherOscillatoryPressure t)) x‖ ≤
      higherOscillatoryHessianPrefactor P C (D ^ r) Cjet Aell Kwave * freq ^ (-5 / 12 : ℝ)) ∧
    (∀ t ∈ I, ∀ x, ‖fderiv ℝ (gradient (b.meanPressure t)) x‖ ≤
      (48 * ‖pressureHessianMultiplier‖ * (13824 * Cmean) * (1 + Cparent)) *
        D ^ (6 * r + 2 * a + 2) * freq ^ (-5 / 2 : ℝ)) := by
  intro Cmean
  have includeLevel {i : ℕ} (hi : i ∈ Finset.Icc 2 P) : i ∈ Finset.Icc 1 P :=
    Finset.mem_Icc.mpr ⟨(by decide : 1 ≤ 2).trans (Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2⟩
  refine ⟨b.norm_higherOscillatoryPressure_hessian_le_of_actualLevels hP hX hU hPer hS hInactive hf
    hell hWidth hEllInv hCarrier hC (pow_nonneg (zero_le_one.trans hD) _) hCjet ht₀ htT γ hγ hpos hγle
    (fun t ht j hj => hCoframe t ht j (hj.trans (by decide))) hAdjoint hStrain hProjection
    (fun n hn i hi => hLevels n (Finset.mem_Icc.mp hn).2 i (includeLevel hi)), ?_⟩
  obtain ⟨hMeanVel, hMeanForce⟩ := b.meanProfileSums_le_of_actualLevels hf (one_le_pow₀ hD) hC
    ht₀ htT γ hγ hpos (fun i hi => hLevels 2 le_rfl i (includeLevel hi))
  have hCmean : 0 ≤ Cmean := mul_nonneg (Nat.cast_nonneg _) hC
  refine b.norm_meanPressure_hessian_le_of_orderTwo hP hX hU hPer hDiv hD (zero_lt_one.trans_le hf)
    (h := h) (e := 6 * r) hell hCjet hCparent hCmean hMeanCost hCoframe hParent ?_ ?_
  · simpa only [Cmean, pow_mul, Nat.mul_comm 6 r, mul_assoc] using hMeanVel
  · simpa only [Cmean, pow_mul, Nat.mul_comm 6 r, mul_assoc] using hMeanForce

/-- The leading, higher, and mean Hessian estimates assemble into (5.49).
The central error comes from the actual measured hierarchy at order one, and the
small step condition converts its bound into (5.50). -/
theorem paperLemma59_pressureCenter (props : PhysicalApproximationProperties b) (hP : 1 ≤ P)
    {freq Cstep leading higher mean t₀ : ℝ} {χ : ℝ → ℝ} {amp κ : ℝ → Vec3}
    (hf : 1 ≤ freq) (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T)
    (hsmall : Cstep * freq ^ (-1 / 12 : ℝ) ≤ 1)
    (hX : IsLabelFlowOn U X I)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hPer : ∀ t ∈ I, SpatiallyPeriodic (U t))
    (hLeading : ∀ t ∈ Icc t₀ T, fderiv ℝ (b.leadingVelocity t) 0 =
      χ t • InnerProductSpace.rankOne ℝ (amp t) (κ t))
    (hHigher₀ : 0 ≤ higher) (hMean₀ : 0 ≤ mean)
    (hPressureCost : leading + higher + mean ≤ Cstep)
    (hLead : ∀ t ∈ I, ∀ x v,
      ⟪v, fderiv ℝ (gradient (b.leadingPressure t)) x v⟫_ℝ ≤
        (leading * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2)
    (hHigher : ∀ t ∈ I, ∀ x,
      ‖fderiv ℝ (gradient (b.higherOscillatoryPressure t)) x‖ ≤ higher * freq ^ (-5 / 12 : ℝ))
    (hMean : ∀ t ∈ I, ∀ x,
      ‖fderiv ℝ (gradient (b.meanPressure t)) x‖ ≤ mean * freq ^ (-5 / 2 : ℝ))
    (γ : ℝ → ℝ) (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγle : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    {ell h D L C : ℝ} {a r : ℕ}
    (hell : 0 < ell) (hh : 0 < h) (hD : 1 ≤ D) (hL : 1 ≤ L)
    (hC : 0 ≤ C)
    (hLabel : ell⁻¹ ≤ D ^ a) (hWidth : h = freq ^ (-1 / 2 : ℝ)) (hCarrier : ‖k‖ ≤ D * freq)
    (hCoeff : ∀ t ∈ I, ∀ j ≤ 1, ∀ x,
      ell ^ j * ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ (X t 0) (X 0 t y)) x‖ ≤ L * D)
    (hLevels : ∀ i ∈ Finset.Icc 1 P, HierarchyLevelBound
      (actualMeasuredLevels b.operators b.profiles P b.leading.completionSwitch b.parentResidual
        freq (zero_le_one.trans hf) ell h hT ht₀ htT γ hγ hpos) freq (D ^ r) C 1 i)
    (hCentralCost : let count := ((Finset.Icc 1 P).card : ℝ)
      48 * L * (2 * count * C) * D ^ (max a 1 + 1 + 2 * r) +
        24 * L * (count * C) * D ^ (a + 1 + 6 * r) ≤ Cstep) :
    (∀ t ∈ I, ∀ x v, ⟪v, fderiv ℝ (gradient (b.pressure t - p t)) x v⟫_ℝ ≤
      (Cstep * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2) ∧
    ∃ E : ℝ → Vec3 →L[ℝ] Vec3, ∀ t ∈ Icc t₀ T,
      fderiv ℝ (b.velocity t) 0 = fderiv ℝ (U t) 0 +
        χ t • InnerProductSpace.rankOne ℝ (amp t) (κ t) + E t ∧
      ‖E t‖ ≤ freq ^ (-1 / 3 : ℝ) := by
  let E (t : ℝ) := fderiv ℝ (b.oscillationRemainder t) 0 + fderiv ℝ (b.meanCorrection t) 0
  refine ⟨?_, E, ?_⟩
  · intro t ht x v
    refine (b.pressureCorrection_hessian_upper_at_stepScale hP hX hU hPer hf hHigher₀ hMean₀
      hLead hHigher hMean t ht x v).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hPressureCost (Real.rpow_nonneg (zero_le_one.trans hf) _)) (sq_nonneg _)
  intro t ht
  have ht' : t ∈ I := ⟨ht₀.trans ht.1, ht.2⟩
  obtain ⟨hA, hB, hBreg⟩ := graphCoframe_geometry hT hX hU hPer ht'
  let count := ((Finset.Icc 1 P).card : ℝ)
  have hCount : 0 ≤ count := Nat.cast_nonneg _
  obtain ⟨_, hOsc, hMeanVelocity⟩ := b.velocityProfileSums_of_actualLevels hP 1 hf (one_le_pow₀ hD)
    hC ht₀ htT γ hγ hpos hLevels
  have hOscNorm : amplitudeSeminorm False ell h 1 hT ht₀ htT γ hγ hpos
      (b.profiles.velocity P - b.operators.average (b.profiles.velocity P) - b.profiles.V 1) ≤
      (2 * count * C) * D ^ (2 * r) * freq ^ (-23 / 12 : ℝ) := by
    simpa only [count, pow_mul, Nat.mul_comm 2 r] using hOsc
  have hMeanNorm : unweightedSeminorm False ell h 1 hT (b.operators.average (b.profiles.velocity P)) ≤
      (count * C) * D ^ (6 * r) * freq ^ (-5 / 2 : ℝ) := by
    simpa only [count, pow_mul, Nat.mul_comm 6 r] using hMeanVelocity
  have hError := (b.norm_centralRemainder_le hP ht₀ htT γ hγ hpos hγle ht hell hh hD hf hL
    (by positivity : 0 ≤ 2 * count * C) (mul_nonneg hCount hC)
    hLabel hWidth hCarrier hA hB hBreg (hCoeff t ht') hOscNorm hMeanNorm).trans
      (mul_le_mul_of_nonneg_right hCentralCost (Real.rpow_nonneg (zero_le_one.trans hf) _))
  have sliceReg {f : Velocity} (h : ContDiffOn ℝ ∞ (Function.uncurry f) J) :
      ContDiff ℝ ∞ (f t) :=
    contDiffOn_univ.mp (h.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht', mem_univ x⟩))
  have hLeadReg : ContDiffOn ℝ ∞ (Function.uncurry b.leadingVelocity) J :=
    HierarchySmoothProfile.contDiffOn_graphRead k _ (hX.contDiffOn_inverseLabelFlow hT hU hPer)
  have hU₁ : Differentiable ℝ (U t) := (sliceReg hU).differentiable (by simp)
  have hL₁ : Differentiable ℝ (b.leadingVelocity t) := (sliceReg hLeadReg).differentiable (by simp)
  have hO₁ : Differentiable ℝ (b.oscillationRemainder t) :=
    (sliceReg (b.oscillationRemainder_smooth hX hU hPer)).differentiable (by simp)
  have hM₁ : Differentiable ℝ (b.meanCorrection t) := (sliceReg props.mean_smooth).differentiable (by simp)
  have hSplit : b.velocity t = U t + b.leadingVelocity t + b.oscillationRemainder t + b.meanCorrection t :=
    congrFun (b.velocity_eq_parent_add_leading_add_remainder_add_mean hP) t
  refine ⟨?_, ?_⟩
  · rw [hSplit, fderiv_add (((hU₁.add hL₁).add hO₁) 0) (hM₁ 0),
      fderiv_add ((hU₁.add hL₁) 0) (hO₁ 0), fderiv_add (hU₁ 0) (hL₁ 0), hLeading t ht]
    dsimp only [E]
    abel
  · calc
      ‖E t‖ ≤ ‖fderiv ℝ (b.oscillationRemainder t) 0‖ + ‖fderiv ℝ (b.meanCorrection t) 0‖ := norm_add_le _ _
      _ ≤ Cstep * freq ^ (-5 / 12 : ℝ) := hError
      _ = (Cstep * freq ^ (-1 / 12 : ℝ)) * freq ^ (-1 / 3 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add (zero_lt_one.trans_le hf)]
        norm_num
      _ ≤ _ := mul_le_of_le_one_left (Real.rpow_nonneg (zero_le_one.trans hf) _) hsmall

end

end TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData
