import TorusEuler.HierarchyDepthTail
import TorusEuler.HierarchyGraphReadoutBounds
import TorusEuler.InductiveStageVelocityJetBounds
import TorusEuler.LaterPhysicalLeadingInput
import TorusEuler.PhysicalWaveStageClosure

/-! Physical velocity and residual bounds for the actual finite hierarchy. -/

open Filter Set UnitAddTorus
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.HierarchyTwistedProfile

open LocalizedAmplitude

noncomputable section

variable {T : ℝ} {k : Vec3} {U : Velocity} {X : ℝ → Velocity} {q : Pressure}
  {depth : ℕ} {hT : 0 < T} {g : ParentGeometry hT U X k}

local notation "I" => Icc (0 : ℝ) T
local notation "J" => Set.prod I (univ : Set Vec3)
local notation "InvLabel" => (fun t => X t 0)
local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "M" => (fun t a => fderiv ℝ (U t) (X 0 t a))
local notation "K" => (fun t a => labelWaveVector X 0 a k t)

namespace PhysicalApproximationData

private theorem physicalSlice_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → Vec3 → E} (hF : ContDiffOn ℝ ∞ (Function.uncurry F) J)
    {t : ℝ} (ht : t ∈ I) : ContDiff ℝ ∞ (F t) :=
  contDiffOn_univ.mp (hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

/-- The geometric fields in the graph readout are the physical inverse label
map and its derivative expressed in the forward labels of the same parent. -/
theorem graphCoframe_geometry (hT : 0 < T) (hX : IsLabelFlowOn U X I)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) {t : ℝ} (ht : t ∈ I) :
    let B := fun a => fderiv ℝ (X t 0) (X 0 t a)
    ContDiff ℝ ∞ (X t 0) ∧ (∀ x, B (X t 0 x) = fderiv ℝ (X t 0) x) ∧
      ContDiff ℝ ∞ B := by
  intro B
  obtain ⟨L, hLip⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by simp)) hper
  have h0 : (0 : ℝ) ∈ I := ⟨le_rfl, hT.le⟩
  have hA : ContDiffOn ℝ ∞ (Function.uncurry InvLabel) J :=
    hX.contDiffOn_inverseLabelFlow hT hU hper
  have hB : ContDiffOn ℝ ∞ (Function.uncurry (fun t a => fderiv ℝ (X t 0) (X 0 t a))) J :=
    hX.contDiffOn_inverseLabelDerivative hT hU hper
  exact ⟨physicalSlice_smooth hA ht, fun x =>
    congrArg (fderiv ℝ (X t 0)) ((hX.inverse hLip h0 ht).2 x), physicalSlice_smooth hB ht⟩

/-- The actual uncut profile multiplying the derivative of the activation
switch is the unswitched leading velocity plus its curl completion. -/
def activationPrimary {t₀ ell D C h : ℝ} {center : ℝ → Vec3}
    (w : SeedOn M K center t₀ T ell D C) (G : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)) :
    ℝ → Vec3 → ℝ → Vec3 :=
  fun t a s => phaseTwistedPeriodizeCentered k (w.leading h) t a s +
    w.wrappedUnswitchedCompletion (h := h) G t a s

theorem residual_eq_graph_tail_add_switch
    (b : PhysicalApproximationData g q depth) (t : ℝ) :
    b.residual t = graphRead InvLabel (b.operators.remainder b.profiles depth) t +
      graphRead InvLabel (b.leading.leadingSwitch + b.leading.completionSwitch) t := by
  funext x
  rfl

/-- Exact label-phase formula for the two activation sources of the chosen later wave. -/
theorem activationSwitch_slice_eq
    (b : PhysicalApproximationData g q depth)
    {t₀ ell D C r h : ℝ} {center : ℝ → Vec3}
    (w : SeedOn M K center t₀ T ell D C) (reg : w.HierarchyRegularity r h)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (hodd : ∀ t ∈ I, Function.Odd (U t))
    (hAmp : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t))
    (hLeading : b.leading = PhysicalLeadingInput.ofLaterWave g w reg hX hU hper hodd hAmp)
    {t : ℝ} (ht : t ∈ I) :
    ∀ a s, slice (b.leading.leadingSwitch + b.leading.completionSwitch) t a s =
      deriv (waveSwitch t₀ r) t • activationPrimary (h := h) w g.inverse t a s := by
  intro a s
  change b.leading.leadingSwitch.val.val.val (t, a, s) +
    b.leading.completionSwitch.val.val.val (t, a, s) =
      deriv (waveSwitch t₀ r) t • activationPrimary (h := h) w g.inverse t a s
  rw [hLeading]
  change (w.twistedLeadingSwitch reg k).val.val.val (t, a, s) +
    (w.twistedCompletionSwitch reg g.inverse g.covector
      g.oscillation.covector_independent g.oscillation.covector_ne_zero).val.val.val (t, a, s) = _
  rw [w.twistedLeadingSwitch_eval reg k ht,
    w.twistedCompletionSwitch_eval reg g.inverse g.covector g.oscillation.covector_independent
      g.oscillation.covector_ne_zero g.covector_value ht, activationPrimary, smul_add]
  rfl

/-- The activation term in the residual of the chosen later hierarchy is
exactly the time derivative of the switch multiplying its actual primary profile. -/
theorem residual_eq_graph_tail_add_laterPrimary
    (b : PhysicalApproximationData g q depth)
    {t₀ ell D C r h : ℝ} {center : ℝ → Vec3}
    (w : SeedOn M K center t₀ T ell D C) (reg : w.HierarchyRegularity r h)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (hodd : ∀ t ∈ I, Function.Odd (U t))
    (hAmp : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t))
    (hLeading : b.leading = PhysicalLeadingInput.ofLaterWave g w reg hX hU hper hodd hAmp)
    {t : ℝ} (ht : t ∈ I) :
    b.residual t = graphRead InvLabel (b.operators.remainder b.profiles depth) t +
      deriv (waveSwitch t₀ r) t •
        transportedProfile InvLabel k (activationPrimary (h := h) w g.inverse) t := by
  rw [b.residual_eq_graph_tail_add_switch]
  congr 1
  funext x
  exact b.activationSwitch_slice_eq w reg hX hU hper hodd hAmp hLeading ht _ _

/-- Only a slice on which the switch derivative is nonzero needs the raw
primary regularity. The smooth activation source supplies it by division. -/
theorem activationPrimary_smooth_of_switch_ne_zero
    (b : PhysicalApproximationData g q depth)
    {t₀ ell D C r h : ℝ} {center : ℝ → Vec3}
    (w : SeedOn M K center t₀ T ell D C) (reg : w.HierarchyRegularity r h)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (hodd : ∀ t ∈ I, Function.Odd (U t))
    (hAmp : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t))
    (hLeading : b.leading = PhysicalLeadingInput.ofLaterWave g w reg hX hU hper hodd hAmp)
    {t : ℝ} (ht : t ∈ I)
    (hσ : deriv (waveSwitch t₀ r) t ≠ 0) :
    ContDiff ℝ ∞ (Function.uncurry (activationPrimary (h := h) w g.inverse t)) := by
  let F := b.leading.leadingSwitch + b.leading.completionSwitch
  have hEq := b.activationSwitch_slice_eq w reg hX hU hper hodd hAmp hLeading ht
  have hF : Function.uncurry (activationPrimary (h := h) w g.inverse t) =
      fun z => (deriv (waveSwitch t₀ r) t)⁻¹ • slice F t z.1 z.2 := by
    funext z
    change activationPrimary (h := h) w g.inverse t z.1 z.2 =
      (deriv (waveSwitch t₀ r) t)⁻¹ • slice F t z.1 z.2
    rw [hEq, smul_smul, inv_mul_cancel₀ hσ, one_smul]
  rw [hF]
  exact (contDiff_slice F ht).const_smul (deriv (waveSwitch t₀ r) t)⁻¹

private theorem physical_transport_slice_smooth {f : ℝ → Vec3 → ℝ → Vec3} {t : ℝ}
    (hA : ContDiff ℝ ∞ (X t 0)) (hf : ContDiff ℝ ∞ (Function.uncurry (f t))) :
    ContDiff ℝ ∞ (transportedProfile InvLabel k f t) := by
  let L : Vec3 →L[ℝ] ℝ := innerSL ℝ k
  exact hf.comp (hA.prodMk (L.contDiff.comp hA))

/-- Read the actual depth remainder and the primary switch profile along the
parent graph, using their distinct unweighted and weighted bounds. -/
theorem residual_holder_of_measuredTail_and_primary
    (b : PhysicalApproximationData g q depth)
    {t₀ ℓ h D freq L Ctail Cprimary Cstep S : ℝ} {a p : ℕ}
    {primary : ℝ → Vec3 → ℝ → Vec3} {σ γ : ℝ → ℝ}
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t))
    (hℓ : 0 < ℓ) (hh : 0 < h) (hD : 1 ≤ D) (hf : 1 ≤ freq)
    (hL : 1 ≤ L) (hCt : 0 ≤ Ctail) (hCp : 0 ≤ Cprimary) (hS : 0 ≤ S)
    (hLabel : ℓ⁻¹ ≤ D ^ a) (hWidth : h = freq ^ (-1 / 2 : ℝ)) (hCarrier : ‖k‖ ≤ D * freq)
    (hCoframe : ∀ t ∈ I, ∀ j ≤ (2 : ℕ), ∀ a,
      ℓ ^ j * ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ (X t 0) (X 0 t x)) a‖ ≤ L * D)
    (hTail : unweightedSeminorm False ℓ h 2 hT (b.operators.remainder b.profiles depth) ≤
      Ctail * freq ^ hierarchyOscExponent (depth + 1))
    (hPrimaryReg : ∀ t ∈ Icc t₀ T, σ t ≠ 0 → ContDiff ℝ ∞ (Function.uncurry (primary t)))
    (hPrimary : ∀ t ∈ Icc t₀ T, PhaseJetBound 2
      (γ t * (Cprimary * D ^ p * freq ^ (-5 / 4 : ℝ))) (scaledPhaseProfile ℓ h (primary t)))
    (hγ : ∀ t ∈ Icc t₀ T, 0 ≤ γ t)
    (hSwitch : ∀ t ∈ Icc t₀ T, |σ t| * γ t ≤ S)
    (hInactive : ∀ t ∈ I, t < t₀ → σ t = 0)
    (hResidual : ∀ t ∈ I, b.residual t =
      graphRead InvLabel (b.operators.remainder b.profiles depth) t + σ t • transportedProfile InvLabel k primary t)
    (hTailCap : 6 * ((((3 : ℝ) * 2 ^ (2 : ℕ) * (2 * L)) ^ (2 : ℕ)) *
      ((4 : ℝ) ^ (2 : ℕ) * Ctail) * D ^ ((max a 1 + 1) * 2)) ≤ Cstep)
    (hPrimaryCap : 6 * ((((3 : ℝ) * 2 ^ (2 : ℕ) * (2 * L)) ^ (2 : ℕ)) *
      Cprimary * D ^ ((max a 1 + 1) * 2 + p)) ≤ Cstep) :
    ∀ t ∈ I, SpatialHolderHalf 1 (b.residual t) ∧ spatialHolderHalfNorm 1 (b.residual t) ≤
      Cstep * freq ^ (2 : ℝ) * (freq ^ (-2 * (depth : ℝ) / 3) + S) := by
  intro t ht
  let tail := b.operators.remainder b.profiles depth
  let E := (((3 : ℝ) * 2 ^ (2 : ℕ) * (2 * L)) ^ (2 : ℕ))
  let Ct := E * ((4 : ℝ) ^ (2 : ℕ) * Ctail) * D ^ ((max a 1 + 1) * 2)
  let Cp := E * Cprimary * D ^ ((max a 1 + 1) * 2 + p)
  have hCt₀ : 0 ≤ Ct := by dsimp [Ct, E]; positivity
  have hCp₀ : 0 ≤ Cp := by dsimp [Cp, E]; positivity
  have hCstep : 0 ≤ Cstep := (mul_nonneg (by norm_num) hCt₀).trans hTailCap
  obtain ⟨hA,hAB,hBreg⟩ := graphCoframe_geometry hT hX hU hper ht
  have hTailReg : ContDiff ℝ ∞ (graphRead InvLabel tail t) :=
    physical_transport_slice_smooth hA (contDiff_slice tail ht)
  have hTailNorm : unweightedSeminorm False ℓ h 2 hT tail ≤
      Ctail * D ^ (0 : ℕ) * freq ^ hierarchyOscExponent (depth + 1) := by simpa using hTail
  have hTailJet := graphRead_frequency_jetBound_unweighted (A := InvLabel) (p := 0) hT tail ht
    hℓ hh hD hf hL hCt hLabel hWidth hCarrier hA hAB hBreg (hCoframe t ht) hTailNorm
  have hTailExponent : (3 : ℝ) * (2 : ℕ) / 2 + hierarchyOscExponent (depth + 1) =
      7 / 4 + (-2 * (depth : ℝ) / 3) := by
    unfold hierarchyOscExponent
    push_cast
    ring
  have hTailJet' : PhaseJetBound 2 (Ct * (freq ^ (7 / 4 : ℝ) * freq ^ (-2 * (depth : ℝ) / 3)))
      (graphRead InvLabel tail t) := by
    rw [← Real.rpow_add (zero_lt_one.trans_le hf), ← hTailExponent]
    simpa only [Ct, E, add_zero] using hTailJet
  by_cases hσ : σ t ≠ 0
  · have ht' : t ∈ Icc t₀ T := ⟨le_of_not_gt (fun hpre => hσ (hInactive t ht hpre)), ht.2⟩
    have hPrimaryReg' : ContDiff ℝ ∞ (transportedProfile InvLabel k primary t) :=
      physical_transport_slice_smooth hA (hPrimaryReg t ht' hσ)
    have hPr := transportedHierarchyProfile_frequency_jetBound (A := InvLabel) (k := k) (f := primary)
      hℓ hh hD hf hL hCp (hγ t ht') hLabel hWidth hCarrier hA hAB hBreg
      (hPrimaryReg t ht' hσ) (hCoframe t ht) (hPrimary t ht')
    have hPr' : PhaseJetBound 2 (Cp * freq ^ (7 / 4 : ℝ) * γ t)
        (transportedProfile InvLabel k primary t) := by
      intro j hj x
      refine (hPr j hj x).trans_eq ?_
      rw [show (3 : ℝ) * (2 : ℕ) / 2 + (-5 / 4 : ℝ) = 7 / 4 by norm_num]
      dsimp only [Cp, E]
      ring
    exact physicalHierarchy_residual_holder_rate hf hCt₀ hCp₀ (hγ t ht') hTailCap hPrimaryCap
      (hSwitch t ht') (hResidual t ht) hTailReg hPrimaryReg' hTailJet' hPr'
  · have hEq : b.residual t = graphRead InvLabel tail t + (0 : ℝ) • (0 : Vec3 → Vec3) := by
      simp only [hResidual t ht, not_not.mp hσ, zero_smul, tail]
    have hPr' : PhaseJetBound 2 ((0 : ℝ) * freq ^ (7 / 4 : ℝ) * 0) (0 : Vec3 → Vec3) := by
      intro j hj x
      simp
    exact physicalHierarchy_residual_holder_rate (Cprimary := 0) (chiPrime := 0) (gamma := 0)
      hf hCt₀ le_rfl le_rfl hTailCap (by simpa only [mul_zero] using hCstep)
      (by simpa using hS) hEq hTailReg contDiff_const hTailJet' hPr'

/-- At depth six times the next frequency exponent, the actual physical
residual bound is small enough for the scheduled cutoff estimates. -/
theorem residual_size_of_scheduled_rate
    (b : PhysicalApproximationData g q depth) {freq μ Cstep : ℝ} {bExp qNext : ℕ}
    (hfreq : 2 ≤ freq) (hb : 1 ≤ bExp) (hμ : 1 ≤ μ) (hC : 0 ≤ Cstep)
    (hDepth : depth = 6 * frequencyExponent bExp qNext)
    (hCμ : Cstep * μ ≤ freq ^ (1 / 16 : ℝ))
    (hRate : ∀ t ∈ I, spatialHolderHalfNorm 1 (b.residual t) ≤
      Cstep * freq ^ (2 : ℝ) *
        (freq ^ (-2 * (depth : ℝ) / 3) + μ * (freq ^ frequencyExponent bExp qNext) ^ (-4 : ℝ))) :
    ∀ t ∈ I, spatialHolderHalfNorm 1 (b.residual t) ≤
      (freq ^ frequencyExponent bExp qNext) ^ (-7 / 2 : ℝ) := by
  intro t ht
  let next := freq ^ frequencyExponent bExp qNext
  have hf : 0 < freq := (by norm_num : (0 : ℝ) < 2).trans_le hfreq
  have hNext : 0 ≤ next := pow_nonneg hf.le _
  have hTail : freq ^ (-2 * (depth : ℝ) / 3) = next ^ (-4 : ℝ) := by
    rw [hDepth]
    exact frequencySchedule_residual_exponent hf.le bExp qNext
  refine (hRate t ht).trans ?_
  rw [hTail]
  calc
    _ = Cstep * (1 + μ) * freq ^ (2 : ℝ) * next ^ (-4 : ℝ) := by dsimp only [next]; ring
    _ ≤ 2 * (Cstep * μ) * freq ^ (2 : ℝ) * next ^ (-4 : ℝ) := by
      have hm : Cstep * (1 + μ) ≤ Cstep * (2 * μ) :=
        mul_le_mul_of_nonneg_left (by linarith) hC
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hm.trans_eq (by ring))
        (Real.rpow_nonneg hf.le _)) (Real.rpow_nonneg hNext _)
    _ ≤ 2 * freq ^ (1 / 16 : ℝ) * freq ^ (2 : ℝ) * next ^ (-4 : ℝ) := by gcongr
    _ = 2 * freq ^ (2 + 1 / 16 : ℝ) * next ^ (-4 : ℝ) := by
      rw [mul_assoc 2, mul_assoc 2, ← Real.rpow_add hf]
      ring
    _ ≤ _ := frequencySchedule_residual_budget hfreq hb

/-- The first stage has no activation residual. -/
theorem residual_eq_graph_tail_of_zeroSwitch
    (b : PhysicalApproximationData g q depth)
    (hLeading : b.leading.leadingSwitch = 0) (hCompletion : b.leading.completionSwitch = 0) (t : ℝ) :
    b.residual t = graphRead InvLabel (b.operators.remainder b.profiles depth) t := by
  rw [b.residual_eq_graph_tail_add_switch, hLeading, hCompletion, add_zero]
  funext x
  change _ + (0 : Vec3) = _
  exact add_zero _

/-- The actual parent's frequency costs at most a thirty-second power of the
new frequency. This absorbs the activation-source prefactor in §7. -/
theorem stepConstant_mul_parent_le {μ Cstep : ℝ} {bExp order : ℕ}
    (hμ : 1 ≤ μ) (hb : 1 ≤ bExp)
    (hStep : Cstep ≤ (μ ^ frequencyExponent bExp order) ^ (1 / 32 : ℝ)) :
    Cstep * μ ≤ (μ ^ frequencyExponent bExp order) ^ (1 / 16 : ℝ) := by
  let freq := μ ^ frequencyExponent bExp order
  have hExp : (32 : ℕ) ≤ frequencyExponent bExp order := by
    unfold frequencyExponent
    exact (show 32 ≤ (320 : ℕ) * 1 * 1 by decide).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left _ hb) (Nat.succ_pos _))
  have hM : μ ≤ freq ^ (1 / 32 : ℝ) := by
    have hExp' : (32 : ℝ) ≤ frequencyExponent bExp order := by exact_mod_cast hExp
    calc
      μ = μ ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ μ ^ ((frequencyExponent bExp order : ℝ) * (1 / 32 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hμ (by linarith)
      _ = freq ^ (1 / 32 : ℝ) := by
        dsimp only [freq]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  calc
    _ ≤ freq ^ (1 / 32 : ℝ) * freq ^ (1 / 32 : ℝ) :=
      mul_le_mul hStep hM (zero_le_one.trans hμ) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity : 0 < freq)]; norm_num [freq]

private theorem physicalWave_switch_deriv_zero_before {t₀ r t : ℝ}
    (hr : 0 ≤ r) (ht : t < t₀) :
    deriv (waveSwitch t₀ r) t = 0 := by
  have hEq : waveSwitch t₀ r =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with u hu
    exact waveSwitch_eq_zero_of_le hr (le_of_lt hu)
  exact ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hEq).deriv

/-- The residual estimate of Lemma 5.8 for the exact later-wave seed
and the measured remainder at the chosen depth. -/
theorem residual_holder_of_actualLaterGraph
    (b : PhysicalApproximationData g q depth)
    {t₀ ℓ D C r h freq L Ctail Cprimary Cstep S : ℝ} {a p : ℕ}
    {center : ℝ → Vec3}
    (w : SeedOn M K center t₀ T ℓ D C) (reg : w.HierarchyRegularity r h)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (hodd : ∀ t ∈ I, Function.Odd (U t))
    (hAmp : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t))
    (hLeading : b.leading = PhysicalLeadingInput.ofLaterWave g w reg hX hU hper hodd hAmp)
    (hD : 1 ≤ D) (hf : 1 ≤ freq) (hL : 1 ≤ L) (hCt : 0 ≤ Ctail) (hCp : 0 ≤ Cprimary)
    (hLabel : ℓ⁻¹ ≤ D ^ a) (hWidth : h = freq ^ (-1 / 2 : ℝ)) (hCarrier : ‖k‖ ≤ D * freq)
    (hCoframe : ∀ t ∈ I, ∀ j ≤ (2 : ℕ), ∀ a,
      ℓ ^ j * ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ (X t 0) (X 0 t x)) a‖ ≤ L * D)
    (hTail : unweightedSeminorm False ℓ h 2 hT (b.operators.remainder b.profiles depth) ≤
      Ctail * freq ^ hierarchyOscExponent (depth + 1))
    {γ : ℝ → ℝ}
    (hPrimary : ∀ t ∈ Icc t₀ T, PhaseJetBound 2
      (γ t * (Cprimary * D ^ p * freq ^ (-5 / 4 : ℝ)))
      (scaledPhaseProfile ℓ h (activationPrimary (h := h) w g.inverse t)))
    (hγ : ∀ t ∈ Icc t₀ T, 0 ≤ γ t)
    (hS : 0 ≤ S) (hSwitch : ∀ t ∈ Icc t₀ T, |deriv (waveSwitch t₀ r) t| * γ t ≤ S)
    (hTailCap : 6 * ((((3 : ℝ) * 2 ^ (2 : ℕ) * (2 * L)) ^ (2 : ℕ)) *
      ((4 : ℝ) ^ (2 : ℕ) * Ctail) * D ^ ((max a 1 + 1) * 2)) ≤ Cstep)
    (hPrimaryCap : 6 * ((((3 : ℝ) * 2 ^ (2 : ℕ) * (2 * L)) ^ (2 : ℕ)) *
      Cprimary * D ^ ((max a 1 + 1) * 2 + p)) ≤ Cstep) :
    ∀ t ∈ I, SpatialHolderHalf 1 (b.residual t) ∧ spatialHolderHalfNorm 1 (b.residual t) ≤
      Cstep * freq ^ (2 : ℝ) * (freq ^ (-2 * (depth : ℝ) / 3) + S) :=
  b.residual_holder_of_measuredTail_and_primary hX hU hper
    reg.envelope_pos reg.phase_pos hD hf hL hCt hCp hS hLabel hWidth hCarrier
    hCoframe hTail (fun _ ht hσ => b.activationPrimary_smooth_of_switch_ne_zero w reg
      hX hU hper hodd hAmp hLeading ⟨reg.nonneg_start.trans ht.1, ht.2⟩ hσ) hPrimary hγ hSwitch
    (fun _ _ ht => physicalWave_switch_deriv_zero_before reg.rate_nonneg ht)
    (fun _ ht => b.residual_eq_graph_tail_add_laterPrimary w reg hX hU hper hodd hAmp hLeading ht)
    hTailCap hPrimaryCap

/-- The scheduled residual bound for the exact chosen later leading input
and the exact measured depth remainder of the same hierarchy. -/
theorem residual_size_of_actualLaterGraph
    (b : PhysicalApproximationData g q depth)
    {t₀ ℓ D C r h freq L Ctail Cprimary Cstep μ : ℝ} {a p bExp qNext : ℕ}
    {center : ℝ → Vec3}
    (w : SeedOn M K center t₀ T ℓ D C) (reg : w.HierarchyRegularity r h)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (hodd : ∀ t ∈ I, Function.Odd (U t))
    (hAmp : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t))
    (hLeading : b.leading = PhysicalLeadingInput.ofLaterWave g w reg hX hU hper hodd hAmp)
    (hD : 1 ≤ D) (hf : 2 ≤ freq) (hL : 1 ≤ L) (hCt : 0 ≤ Ctail) (hCp : 0 ≤ Cprimary)
    (hLabel : ℓ⁻¹ ≤ D ^ a) (hWidth : h = freq ^ (-1 / 2 : ℝ)) (hCarrier : ‖k‖ ≤ D * freq)
    (hCoframe : ∀ t ∈ I, ∀ j ≤ (2 : ℕ), ∀ a,
      ℓ ^ j * ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ (X t 0) (X 0 t x)) a‖ ≤ L * D)
    (hTail : unweightedSeminorm False ℓ h 2 hT (b.operators.remainder b.profiles depth) ≤
      Ctail * freq ^ hierarchyOscExponent (depth + 1))
    {γ : ℝ → ℝ}
    (hPrimary : ∀ t ∈ Icc t₀ T, PhaseJetBound 2
      (γ t * (Cprimary * D ^ p * freq ^ (-5 / 4 : ℝ)))
      (scaledPhaseProfile ℓ h (activationPrimary (h := h) w g.inverse t)))
    (hγ : ∀ t ∈ Icc t₀ T, 0 ≤ γ t)
    (hSwitch : ∀ t ∈ Icc t₀ T, |deriv (waveSwitch t₀ r) t| * γ t ≤
      μ * (freq ^ frequencyExponent bExp qNext) ^ (-4 : ℝ))
    (hTailCap : 6 * ((((3 : ℝ) * 2 ^ (2 : ℕ) * (2 * L)) ^ (2 : ℕ)) *
      ((4 : ℝ) ^ (2 : ℕ) * Ctail) * D ^ ((max a 1 + 1) * 2)) ≤ Cstep)
    (hPrimaryCap : 6 * ((((3 : ℝ) * 2 ^ (2 : ℕ) * (2 * L)) ^ (2 : ℕ)) *
      Cprimary * D ^ ((max a 1 + 1) * 2 + p)) ≤ Cstep)
    (hb : 1 ≤ bExp) (hμ : 1 ≤ μ)
    (hDepth : depth = 6 * frequencyExponent bExp qNext)
    (hCμ : Cstep * μ ≤ freq ^ (1 / 16 : ℝ)) :
    ∀ t ∈ I, SpatialHolderHalf 1 (b.residual t) ∧ spatialHolderHalfNorm 1 (b.residual t) ≤
      (freq ^ frequencyExponent bExp qNext) ^ (-7 / 2 : ℝ) := by
  have hf1 : 1 ≤ freq := one_le_two.trans hf
  have hC : 0 ≤ Cstep := (by positivity : 0 ≤ 6 * ((((3 : ℝ) * 2 ^ (2 : ℕ) * (2 * L)) ^ (2 : ℕ)) *
    ((4 : ℝ) ^ (2 : ℕ) * Ctail) * D ^ ((max a 1 + 1) * 2))).trans hTailCap
  have hRate := b.residual_holder_of_actualLaterGraph w reg hX hU hper hodd hAmp hLeading hD hf1
    hL hCt hCp hLabel hWidth hCarrier hCoframe hTail hPrimary hγ (by positivity) hSwitch hTailCap hPrimaryCap
  exact fun t ht => ⟨(hRate t ht).1,
    b.residual_size_of_scheduled_rate hf hb hμ hC hDepth hCμ
      (fun t ht => (hRate t ht).2) t ht⟩

/-- The no-switch first-wave residual uses only the measured depth remainder. -/
theorem residual_size_of_zeroSwitchGraph
    (b : PhysicalApproximationData g q depth)
    {ℓ h D freq L Ctail Cstep μ : ℝ} {a bExp qNext : ℕ}
    (hLeading : b.leading.leadingSwitch = 0) (hCompletion : b.leading.completionSwitch = 0)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t))
    (hℓ : 0 < ℓ) (hh : 0 < h) (hD : 1 ≤ D) (hf : 2 ≤ freq) (hL : 1 ≤ L) (hCt : 0 ≤ Ctail)
    (hLabel : ℓ⁻¹ ≤ D ^ a) (hWidth : h = freq ^ (-1 / 2 : ℝ)) (hCarrier : ‖k‖ ≤ D * freq)
    (hCoframe : ∀ t ∈ I, ∀ j ≤ (2 : ℕ), ∀ a,
      ℓ ^ j * ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ (X t 0) (X 0 t x)) a‖ ≤ L * D)
    (hTail : unweightedSeminorm False ℓ h 2 hT (b.operators.remainder b.profiles depth) ≤
      Ctail * freq ^ hierarchyOscExponent (depth + 1))
    (hTailCap : 6 * ((((3 : ℝ) * 2 ^ (2 : ℕ) * (2 * L)) ^ (2 : ℕ)) *
      ((4 : ℝ) ^ (2 : ℕ) * Ctail) * D ^ ((max a 1 + 1) * 2)) ≤ Cstep)
    (hb : 1 ≤ bExp) (hμ : 1 ≤ μ)
    (hDepth : depth = 6 * frequencyExponent bExp qNext)
    (hCμ : Cstep * μ ≤ freq ^ (1 / 16 : ℝ)) :
    ∀ t ∈ I, SpatialHolderHalf 1 (b.residual t) ∧ spatialHolderHalfNorm 1 (b.residual t) ≤
      (freq ^ frequencyExponent bExp qNext) ^ (-7 / 2 : ℝ) := by
  have hC : 0 ≤ Cstep := (by positivity : 0 ≤ 6 * ((((3 : ℝ) * 2 ^ (2 : ℕ) * (2 * L)) ^ (2 : ℕ)) *
    ((4 : ℝ) ^ (2 : ℕ) * Ctail) * D ^ ((max a 1 + 1) * 2))).trans hTailCap
  have hSize : 0 ≤ μ * (freq ^ frequencyExponent bExp qNext) ^ (-4 : ℝ) :=
    mul_nonneg (zero_le_one.trans hμ) (Real.rpow_nonneg (pow_nonneg (by linarith) _) _)
  have hRate := b.residual_holder_of_measuredTail_and_primary
    (t₀ := 0) (primary := fun _ _ _ => 0) (σ := fun _ => 0) (γ := fun _ => 0)
    (p := 0) (Cprimary := 0) hX hU hper hℓ hh hD (one_le_two.trans hf) hL hCt le_rfl hSize
    hLabel hWidth hCarrier hCoframe hTail (fun _ _ _ => contDiff_const)
    (fun _ _ j _ x => by
      change ‖iteratedFDeriv ℝ j (fun _ : Vec3 × ℝ => (0 : Vec3)) x‖ ≤ _
      simp) (fun _ _ => le_rfl)
    (fun _ _ => by simpa using hSize) (fun _ _ _ => rfl)
    (fun t _ => by simpa only [zero_smul, add_zero] using b.residual_eq_graph_tail_of_zeroSwitch hLeading hCompletion t)
    hTailCap (by simpa only [mul_zero, zero_mul] using hC)
  exact fun t ht => ⟨(hRate t ht).1,
    b.residual_size_of_scheduled_rate hf hb hμ hC hDepth hCμ (fun t ht => (hRate t ht).2) t ht⟩

end PhysicalApproximationData

end

end TorusEuler.HierarchyTwistedProfile

namespace TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData

noncomputable section

variable {T : ℝ} {k : Vec3} {U : Velocity} {X : ℝ → Velocity} {p : Pressure}
  {hT : 0 < T} {d : ParentGeometry hT U X k} {P : ℕ}
  (b : PhysicalApproximationData d p P)

/-- Summing the measured levels gives the exact oscillatory, higher oscillatory,
and mean profiles used to define the physical approximation. -/
theorem velocityProfileSums_of_actualLevels (hP : 1 ≤ P) (n : ℕ)
    {ℓ h freq loss C : ℝ} (hf : 1 ≤ freq) (hLoss : 1 ≤ loss) (hC : 0 ≤ C)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hlevels : ∀ i ∈ Finset.Icc 1 P, HierarchyLevelBound
      (actualMeasuredLevels b.operators b.profiles P b.leading.completionSwitch b.parentResidual
        freq (zero_le_one.trans hf) ℓ h hT ht₀ htT γ hγ hpos) freq loss C n i) :
    let B := ((Finset.Icc 1 P).card : ℝ)
    let F := b.profiles.velocity P
    let avg := b.operators.average F
    let N := unweightedSeminorm False ℓ h n hT
    let W := amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos
    W (F - avg) ≤ 2 * B * C * loss ^ 2 * freq ^ (-5 / 4 : ℝ) ∧
    W (F - avg - b.profiles.V 1) ≤ 2 * B * C * loss ^ 2 * freq ^ (-23 / 12 : ℝ) ∧
    N avg ≤ B * C * loss ^ 6 * freq ^ (-5 / 2 : ℝ) := by
  let N : ℕ → Seminorm ℝ (HierarchyTwistedProfile T k Vec3) :=
    fun n => unweightedSeminorm False ℓ h n hT
  let W : ℕ → Seminorm ℝ (HierarchyTwistedProfile T k Vec3) :=
    fun n => amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos
  let Q : ℕ → Seminorm ℝ (HierarchyTwistedProfile T k ℝ) :=
    fun n => amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos
  have hs := hierarchySeminorm_velocity_sums b.operators b.profiles hP n N W (fun m q => Q m q)
    (fun m => apply_nonneg (Q m)) b.leading.completionSwitch b.parentResidual hf hLoss hC hlevels
  have hOsc := b.solvers.construct_velocity_sub_average P b.leading.completionSwitch b.parentResidual
    b.parentResidual_average b.leading.output
  change b.profiles.velocity P - b.operators.average (b.profiles.velocity P) =
    ∑ i ∈ Finset.Icc 1 P, (b.profiles.V i + b.profiles.C i) at hOsc
  have hSum : b.profiles.velocity P =
      (∑ i ∈ Finset.Icc 1 P, (b.profiles.V i + b.profiles.C i)) + ∑ i ∈ Finset.Icc 1 P, b.profiles.B i :=
    Finset.sum_add_distrib
  have hB₁ : b.profiles.B 1 = 0 :=
    (b.solvers.construct_leading P b.leading.completionSwitch b.parentResidual
      b.parentResidual_average b.leading.output).2.2.1
  have hMean : b.operators.average (b.profiles.velocity P) = ∑ i ∈ Finset.Icc 2 P, b.profiles.B i := by
    calc
      _ = b.profiles.velocity P - (b.profiles.velocity P - b.operators.average (b.profiles.velocity P)) := by abel
      _ = ∑ i ∈ Finset.Icc 1 P, b.profiles.B i := by rw [hOsc, hSum]; abel
      _ = _ := by
        rw [← Finset.insert_Icc_add_one_left_eq_Icc hP, Finset.sum_insert (by simp), hB₁, zero_add]
        rfl
  dsimp only
  rw [hOsc, hMean]
  exact hs

/-- The zeroth-order weighted level sum bounds the actual oscillation on the full slab. -/
theorem oscillation_sup_of_actualLevels (hP : 1 ≤ P)
    {ℓ h freq loss C Cstep : ℝ} (hf : 1 ≤ freq) (hLoss : 1 ≤ loss) (hC : 0 ≤ C)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγmax : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hinactive : ∀ t ∈ Icc 0 T, t < t₀ → b.oscillation t = 0)
    (hlevels : ∀ i ∈ Finset.Icc 1 P, HierarchyLevelBound
      (actualMeasuredLevels b.operators b.profiles P b.leading.completionSwitch b.parentResidual
        freq (zero_le_one.trans hf) ℓ h hT ht₀ htT γ hγ hpos) freq loss C 0 i)
    (hBudget : 2 * ((Finset.Icc 1 P).card : ℝ) * C * loss ^ 2 ≤ Cstep) :
    ∀ t ∈ Icc 0 T, ∀ x, ‖b.oscillation t x‖ ≤ Cstep * freq ^ (-5 / 4 : ℝ) := by
  let F := b.profiles.velocity P - b.operators.average (b.profiles.velocity P)
  let W : Seminorm ℝ (HierarchyTwistedProfile T k Vec3) :=
    amplitudeSeminorm False ℓ h 0 hT ht₀ htT γ hγ hpos
  have hsum := (b.velocityProfileSums_of_actualLevels hP 0 hf hLoss hC ht₀ htT γ hγ hpos hlevels).1
  change W F ≤ _ at hsum
  intro t ht x
  by_cases hactive : t₀ ≤ t
  · have ht' : t ∈ Icc t₀ T := ⟨hactive, ht.2⟩
    have hnil : ([] : List (Fin 4)) ∈ hierarchyAdmissibleWords (Fin 4) 0 := by
      simp [mem_hierarchyAdmissibleWords]
    have hpoint := norm_mixedWord_le_amplitudeSeminorm False ℓ h hT ht₀ htT γ hγ hpos F
      hnil ht' (X t 0 x, ⟪k, X t 0 x⟫_ℝ)
    change ‖b.oscillation t x‖ ≤ γ t * W F at hpoint
    exact hpoint.trans ((mul_le_of_le_one_left (apply_nonneg W F) (hγmax t ht')).trans
      (hsum.trans (mul_le_mul_of_nonneg_right hBudget (by positivity))))
  · rw [hinactive t ht (lt_of_not_ge hactive), Pi.zero_apply, norm_zero]
    exact mul_nonneg ((by positivity : 0 ≤ 2 * ((Finset.Icc 1 P).card : ℝ) * C * loss ^ 2).trans hBudget)
      (by positivity)

/-- The phase-independent actual mean incurs only label derivative costs on the physical graph. -/
theorem meanCorrection_holder_of_actualLevels (hP : 1 ≤ P)
    (hProperties : PhysicalApproximationProperties b)
    {ℓ h freq loss C D L K Cmean : ℝ} {a c bExp q : ℕ}
    (hf : 1 ≤ freq) (hLoss : 1 ≤ loss) (hC : 0 ≤ C)
    (hℓ : 0 < ℓ) (hD : 1 ≤ D) (hL : 1 ≤ L)
    (hLabel : ℓ⁻¹ ≤ D ^ a) (hLossScale : loss ≤ K * D ^ c)
    (hExp : a + 1 ≤ bExp) (hc : 6 * c ≤ bExp)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hlevels : ∀ m ≤ q, ∀ i ∈ Finset.Icc 1 P, HierarchyLevelBound
      (actualMeasuredLevels b.operators b.profiles P b.leading.completionSwitch b.parentResidual
        freq (zero_le_one.trans hf) ℓ h hT ht₀ htT γ hγ hpos) freq loss C (m + 1) i)
    (B : ℝ → Vec3 → Vec3 →L[ℝ] Vec3)
    (hA : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (X t 0))
    (hB : ∀ t ∈ Icc 0 T, ∀ x, B t (X t 0 x) = fderiv ℝ (X t 0) x)
    (hBreg : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (B t))
    (hCoeff : ∀ t ∈ Icc 0 T, ∀ j ≤ q + 1, ∀ x, ℓ ^ j * ‖iteratedFDeriv ℝ j (B t) x‖ ≤ L * D)
    (hBudget : (3 * (q + 1) : ℝ) * ((3 : ℝ) * (2 : ℝ) ^ (q + 1) * L) ^ (q + 1) *
      (4 : ℝ) ^ (q + 1) * (((Finset.Icc 1 P).card : ℝ) * C * K ^ 6) ≤ Cmean) :
    ∀ m ≤ q, ∀ t ∈ Icc 0 T, SpatialHolderHalf m (b.meanCorrection t) ∧
      spatialHolderHalfNorm m (b.meanCorrection t) ≤ Cmean * D ^ (bExp * (m + 2)) * freq ^ (-5 / 2 : ℝ) := by
  intro m hm t ht
  let F := b.operators.average (b.profiles.velocity P)
  let C₀ := ((Finset.Icc 1 P).card : ℝ) * C * K ^ 6
  have hMean : HierarchyPeriodicProfile.PhaseIndependent F.val.val :=
    (average_is_mean hT d.inverse d.strain d.covector (b.profiles.velocity P)).1
  have hsum := (b.velocityProfileSums_of_actualLevels hP (m + 1) hf hLoss hC ht₀ htT γ hγ hpos
    (hlevels m hm)).2.2
  have hN : unweightedSeminorm False ℓ h (m + 1) hT F ≤ C₀ * D ^ (6 * c) * freq ^ (-5 / 2 : ℝ) := by
    refine hsum.trans ?_
    calc
      _ ≤ ((Finset.Icc 1 P).card : ℝ) * C * (K * D ^ c) ^ 6 * freq ^ (-5 / 2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (zero_le_one.trans hLoss) hLossScale 6) (by positivity)) (by positivity)
      _ = _ := by dsimp only [C₀]; rw [mul_pow, ← pow_mul, Nat.mul_comm c 6]; ring
  have hjet := graphRead_frequency_jetBound_mean (A := fun r => X r 0) (a := a) (p := 6 * c)
    hT F hMean ht hℓ hD (zero_lt_one.trans_le hf) hL (by dsimp [C₀]; positivity)
    hLabel (hA t ht) (hB t ht) (hBreg t ht) (fun j hj => hCoeff t ht j (hj.trans (by omega))) hN
  have hReg : ContDiff ℝ ∞ (b.meanCorrection t) :=
    contDiffOn_univ.mp (hProperties.mean_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x (_ : x ∈ (univ : Set Vec3)) => mem_prod.mpr ⟨ht, mem_univ x⟩))
  have hHolder := spatialHolderHalfNorm_le_of_uniformJets (m := m) hReg (by dsimp [C₀]; positivity) hjet
  refine ⟨hHolder.1, hHolder.2.trans ?_⟩
  have hOrder : m + 1 ≤ q + 1 := Nat.succ_le_succ hm
  have hDexp : (a + 1) * (m + 1) + 6 * c ≤ bExp * (m + 2) := by
    calc
      _ ≤ bExp * (m + 1) + bExp :=
        Nat.add_le_add (Nat.mul_le_mul_right (m + 1) hExp) hc
      _ = _ := by simp only [Nat.mul_add, Nat.mul_one]; omega
  have hGeometric :
      ((3 : ℝ) * (2 : ℝ) ^ (m + 1) * L) ^ (m + 1) ≤
        ((3 : ℝ) * (2 : ℝ) ^ (q + 1) * L) ^ (q + 1) := by
    have hBase : (3 : ℝ) * (2 : ℝ) ^ (m + 1) * L ≤ (3 : ℝ) * (2 : ℝ) ^ (q + 1) * L := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hOrder) (by norm_num)) (zero_le_one.trans hL)
    have hOne : 1 ≤ (3 : ℝ) * (2 : ℝ) ^ (q + 1) * L :=
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ (by norm_num))) hL
    exact (pow_le_pow_left₀ (by positivity) hBase _).trans (pow_le_pow_right₀ hOne hOrder)
  have hFactor :
      (3 * (m + 1) : ℝ) * ((3 : ℝ) * (2 : ℝ) ^ (m + 1) * L) ^ (m + 1) *
        ((4 : ℝ) ^ (m + 1) * C₀) ≤ Cmean := by
    calc
      _ ≤ (3 * (q + 1) : ℝ) * ((3 : ℝ) * (2 : ℝ) ^ (q + 1) * L) ^ (q + 1) *
          ((4 : ℝ) ^ (q + 1) * C₀) := by
        have hmCast : (m : ℝ) + 1 ≤ (q : ℝ) + 1 :=
          add_le_add_left (Nat.cast_le.mpr hm) 1
        have hFirst := mul_le_mul (mul_le_mul_of_nonneg_left hmCast
          (by norm_num : (0 : ℝ) ≤ 3)) hGeometric (by positivity) (by positivity)
        have hSecond := mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hOrder)
          (show 0 ≤ C₀ by dsimp [C₀]; positivity)
        exact mul_le_mul hFirst hSecond (by dsimp [C₀]; positivity) (by positivity)
      _ ≤ _ := by rw [← mul_assoc]; exact hBudget
  calc
    _ = ((3 * (m + 1) : ℝ) * ((3 : ℝ) * (2 : ℝ) ^ (m + 1) * L) ^ (m + 1) *
        ((4 : ℝ) ^ (m + 1) * C₀)) * D ^ ((a + 1) * (m + 1) + 6 * c) * freq ^ (-5 / 2 : ℝ) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul hFactor (pow_le_pow_right₀ hD hDexp) (by positivity)
        ((by dsimp [C₀]; positivity : 0 ≤ (3 * (m + 1) : ℝ) * ((3 : ℝ) * (2 : ℝ) ^ (m + 1) * L) ^
          (m + 1) * ((4 : ℝ) ^ (m + 1) * C₀)).trans hFactor)

theorem oscillationRemainder_eq_graph_sub_leading (hP : 1 ≤ P) :
    b.oscillationRemainder = graphRead (fun t => X t 0)
      (b.profiles.velocity P - b.operators.average (b.profiles.velocity P) - b.profiles.V 1) := by
  funext t x
  have hLead : b.profiles.V 1 = b.leading.output.V :=
    (b.solvers.construct_leading P b.leading.completionSwitch b.parentResidual
      b.parentResidual_average b.leading.output).1
  rw [hLead]
  change b.oscillationRemainder t x = b.oscillation t x - b.leadingVelocity t x
  have h : b.oscillation t x = b.leadingVelocity t x + b.oscillationRemainder t x :=
    congrFun (congrFun (b.oscillation_eq_leading_add_remainder hP) t) x
  rw [h]
  abel

/-- One Eulerian derivative on the leading-subtracted level sum costs
one carrier derivative, leaving the central remainder with exponent `-5/12`. -/
theorem oscillationRemainder_fderiv_of_actualLevels (hP : 1 ≤ P)
    {ℓ h freq loss C D L K : ℝ} {a c : ℕ}
    (hf : 1 ≤ freq) (hLoss : 1 ≤ loss) (hC : 0 ≤ C)
    (hℓ : 0 < ℓ) (hh : 0 < h) (hD : 1 ≤ D) (hL : 1 ≤ L)
    (hLabel : ℓ⁻¹ ≤ D ^ a) (hWidth : h = freq ^ (-1 / 2 : ℝ))
    (hCarrier : ‖k‖ ≤ D * freq) (hLossScale : loss ≤ K * D ^ c)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hlevels : ∀ i ∈ Finset.Icc 1 P, HierarchyLevelBound
      (actualMeasuredLevels b.operators b.profiles P b.leading.completionSwitch b.parentResidual
        freq (zero_le_one.trans hf) ℓ h hT ht₀ htT γ hγ hpos) freq loss C 1 i)
    (B : ℝ → Vec3 → Vec3 →L[ℝ] Vec3)
    (hA : ∀ t ∈ Icc t₀ T, ContDiff ℝ ∞ (X t 0))
    (hB : ∀ t ∈ Icc t₀ T, ∀ x, B t (X t 0 x) = fderiv ℝ (X t 0) x)
    (hBreg : ∀ t ∈ Icc t₀ T, ContDiff ℝ ∞ (B t))
    (hCoeff : ∀ t ∈ Icc t₀ T, ∀ j ≤ 1, ∀ x, ℓ ^ j * ‖iteratedFDeriv ℝ j (B t) x‖ ≤ L * D) :
    ∀ t ∈ Icc t₀ T, ∀ x, ‖fderiv ℝ (b.oscillationRemainder t) x‖ ≤
      (96 * L * ((Finset.Icc 1 P).card : ℝ) * C * K ^ 2) *
        D ^ (max a 1 + 1 + 2 * c) * (γ t * freq ^ (-5 / 12 : ℝ)) := by
  intro t ht x
  rw [b.oscillationRemainder_eq_graph_sub_leading hP]
  let F := b.profiles.velocity P - b.operators.average (b.profiles.velocity P) - b.profiles.V 1
  let C₀ := 2 * ((Finset.Icc 1 P).card : ℝ) * C * K ^ 2
  have hsum := (b.velocityProfileSums_of_actualLevels hP 1 hf hLoss hC ht₀ htT γ hγ hpos hlevels).2.1
  have hN : amplitudeSeminorm False ℓ h 1 hT ht₀ htT γ hγ hpos F ≤
      C₀ * D ^ (2 * c) * freq ^ (-23 / 12 : ℝ) := by
    refine hsum.trans ?_
    calc
      _ ≤ 2 * ((Finset.Icc 1 P).card : ℝ) * C * (K * D ^ c) ^ 2 * freq ^ (-23 / 12 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (zero_le_one.trans hLoss) hLossScale 2) (by positivity)) (by positivity)
      _ = _ := by dsimp only [C₀]; rw [mul_pow, ← pow_mul, Nat.mul_comm c 2]; ring
  have hjet := graphRead_frequency_jetBound_weighted (A := fun r => X r 0) (a := a) (p := 2 * c)
    hT ht₀ htT γ hγ hpos F ht hℓ hh hD hf hL (by dsimp [C₀]; positivity)
    hLabel hWidth hCarrier (hA t ht) (hB t ht) (hBreg t ht) (hCoeff t ht) hN
  have hresult := hjet 1 le_rfl x
  rw [norm_iteratedFDeriv_one] at hresult
  refine hresult.trans_eq ?_
  dsimp only [C₀]
  simp only [pow_one, Nat.mul_one, Nat.cast_one]
  rw [show (3 : ℝ) * 1 / 2 + (-23 / 12 : ℝ) = -5 / 12 by norm_num]
  ring

end

end TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

private theorem velocityDepth_from_holder {U V O M : Vec3 → Vec3}
    {μ Cparent Cosc Cmean : ℝ} {P b q : ℕ}
    (hμ : 2 ≤ μ) (hb : 1 ≤ b)
    (hCp : Cparent ≤ μ) (hCo : Cosc ≤ μ) (hCm : Cmean ≤ μ)
    (hSplit : V = U + O + M)
    (hU : SpatialHolderHalf P U) (hO : SpatialHolderHalf P O) (hM : SpatialHolderHalf P M)
    (hParent : spatialHolderHalfNorm P U ≤ Cparent * μ ^ (5 * (P + 1) + 1))
    (hOsc : spatialHolderHalfNorm P O ≤
      Cosc * (μ ^ 9) ^ (b * (P + 2)) *
        (μ ^ frequencyExponent b q) ^ ((3 : ℝ) * (P + 1) / 2 - 5 / 4))
    (hMean : spatialHolderHalfNorm P M ≤
      Cmean * (μ ^ 9) ^ (b * (P + 2)) * (μ ^ frequencyExponent b q) ^ (-5 / 2 : ℝ)) :
    1 + spatialHolderHalfNorm P V ≤ 3 * (μ ^ frequencyExponent b q) ^ (2 * (P + 1)) := by
  let freq := μ ^ frequencyExponent b q
  let E : ℝ := (3 : ℝ) * (P + 1) / 2 - 5 / 4 + ((P : ℝ) + 2) / 32
  have hμ1 : 1 ≤ μ := one_le_two.trans hμ
  have hExp : frequencyExponent b q ≠ 0 := by
    unfold frequencyExponent
    exact Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos (by decide) hb) (Nat.succ_pos _))
  have hf₂ : 2 ≤ freq := hμ.trans (le_self_pow₀ hμ1 hExp)
  have hf : 1 ≤ freq := one_le_two.trans hf₂
  have hfpos : 0 < freq := zero_lt_one.trans_le hf
  have hPar' : spatialHolderHalfNorm P U ≤ freq ^ (2 * (P + 1)) :=
    hParent.trans ((frequencySchedule_fullOrder_parent_budget hμ1 hCp hb).trans
      (pow_le_pow_right₀ hf (by omega)))
  have hO' : spatialHolderHalfNorm P O ≤ freq ^ E := by
    refine hOsc.trans ((mul_le_mul_of_nonneg_right
      (frequencySchedule_fullOrder_wave_budget (q := q) hμ1 hCo hb) (by positivity)).trans_eq ?_)
    change freq ^ (((P : ℝ) + 2) / 32) * freq ^ ((3 : ℝ) * (P + 1) / 2 - 5 / 4) = _
    rw [← Real.rpow_add hfpos]
    congr 1
    dsimp only [E]
    ring
  have hM' : spatialHolderHalfNorm P M ≤ freq ^ E := by
    refine hMean.trans ((mul_le_mul_of_nonneg_right
      (frequencySchedule_fullOrder_wave_budget (q := q) hμ1 hCm hb) (by positivity)).trans ?_)
    change freq ^ (((P : ℝ) + 2) / 32) * freq ^ (-5 / 2 : ℝ) ≤ _
    rw [← Real.rpow_add hfpos]
    apply Real.rpow_le_rpow_of_exponent_le hf
    dsimp only [E]
    linarith [(show 0 ≤ (P : ℝ) from by positivity)]
  have hWave : spatialHolderHalfNorm P O + spatialHolderHalfNorm P M ≤ freq ^ (2 * (P + 1)) := by
    calc
      _ ≤ freq ^ E + freq ^ E := add_le_add hO' hM'
      _ = 2 * freq ^ E := by ring
      _ ≤ freq * freq ^ E := mul_le_mul_of_nonneg_right hf₂ (Real.rpow_nonneg hfpos.le _)
      _ = freq ^ (1 + E) := by
        simpa only [Real.rpow_one] using (Real.rpow_add hfpos 1 E).symm
      _ ≤ freq ^ (2 * (P + 1)) := by
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le hf
        push_cast
        dsimp only [E]
        linarith [(show 0 ≤ (P : ℝ) from by positivity)]
  obtain ⟨hUO, hUOnorm⟩ := spatialHolderHalf_add_exact hU hO
  obtain ⟨_, hVnorm⟩ := spatialHolderHalf_add_exact hUO hM
  rw [hSplit]
  have hOne : 1 ≤ freq ^ (2 * (P + 1)) := one_le_pow₀ hf
  linarith only [hOne, hVnorm, hUOnorm, hPar', hWave]

namespace PhysicalApproximationData

variable {T : ℝ} {k : Vec3} {U : Velocity} {X : ℝ → Velocity} {p : Pressure}
variable {hT : 0 < T} {d : ParentGeometry hT U X k} {P : ℕ}

/-- The full-order physical velocity size from bounds on the exact weighted
oscillatory and unweighted mean seminorms of the retained profiles. -/
theorem velocity_size_of_actualLevels
    (b : PhysicalApproximationData d p P) (properties : PhysicalApproximationProperties b)
    {μ ℓ h L loss C Cosc Cmean Cparent : ℝ} {schedule q a : ℕ}
    (hP : 1 ≤ P) (hμ : 2 ≤ μ) (hSchedule : 1 ≤ schedule)
    (hℓ : 0 < ℓ) (hh : 0 < h) (hL : 1 ≤ L) (hLoss : 1 ≤ loss) (hC : 0 ≤ C)
    (hLabel : ℓ⁻¹ ≤ (μ ^ 9) ^ a)
    (hWidth : h = (μ ^ frequencyExponent schedule q) ^ (-1 / 2 : ℝ))
    (hCarrier : ‖k‖ ≤ μ ^ 9 * (μ ^ frequencyExponent schedule q))
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T)
    (γ : ℝ → ℝ) (hγ : ContinuousOn γ (Icc t₀ T)) (hγpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγone : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hInactive : ∀ t ∈ Icc 0 T, t < t₀ → b.oscillation t = 0)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hA : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (X t 0))
    (B : ℝ → Vec3 → Vec3 →L[ℝ] Vec3)
    (hB : ∀ t ∈ Icc 0 T, ∀ x, B t (X t 0 x) = fderiv ℝ (X t 0) x)
    (hBreg : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (B t))
    (hcoeff : ∀ t ∈ Icc 0 T, ∀ j ≤ P + 1, ∀ x,
       ℓ ^ j * ‖iteratedFDeriv ℝ j (B t) x‖ ≤ L * (μ ^ 9))
    (hLevels : ∀ i ∈ Finset.Icc 1 P, HierarchyLevelBound
      (actualMeasuredLevels b.operators b.profiles P b.leading.completionSwitch b.parentResidual
        (μ ^ frequencyExponent schedule q) (by positivity) ℓ h hT ht₀ htT γ hγ hγpos)
      (μ ^ frequencyExponent schedule q) loss C (P + 1) i)
    (hOscGraphCost : (3 * ((P : ℝ) + 1)) *
      ((((3 : ℝ) * 2 ^ (P + 1) * (2 * L)) ^ (P + 1) * (4 ^ (P + 1) * (2 * ((Finset.Icc 1 P).card : ℝ) * C * loss ^ 2))) *
        (μ ^ 9) ^ ((max a 1 + 1) * (P + 1))) ≤ Cosc * (μ ^ 9) ^ (schedule * (P + 2)))
    (hMeanGraphCost : (3 * ((P : ℝ) + 1)) *
      ((((3 : ℝ) * 2 ^ (P + 1) * L) ^ (P + 1) * (4 ^ (P + 1) * (((Finset.Icc 1 P).card : ℝ) * C * loss ^ 6))) *
        (μ ^ 9) ^ ((a + 1) * (P + 1))) ≤ Cmean * (μ ^ 9) ^ (schedule * (P + 2)))
    (hCo : Cosc ≤ μ) (hCm : Cmean ≤ μ)
    (hParentJets : ∀ t ∈ Icc 0 T, PhaseJetBound (P + 1) (Cparent * μ ^ (5 * (P + 1) + 1)) (U t))
    (hCp : (3 * ((P : ℝ) + 1)) * Cparent ≤ μ) :
    ∀ t ∈ Icc 0 T, 1 + spatialHolderHalfNorm P (b.velocity t) ≤
      3 * (μ ^ frequencyExponent schedule q) ^ (2 * (P + 1)) := by
  intro t ht
  let freq := μ ^ frequencyExponent schedule q
  let D : ℝ := μ ^ 9
  let n := P + 1
  let osc := b.profiles.velocity P - b.operators.average (b.profiles.velocity P)
  let mean := b.operators.average (b.profiles.velocity P)
  let A : Velocity := fun r => X r 0
  have hμ1 : 1 ≤ μ := one_le_two.trans hμ
  have hD : 1 ≤ D := one_le_pow₀ hμ1
  have hf : 1 ≤ freq := one_le_pow₀ hμ1
  have hfpos : 0 < freq := zero_lt_one.trans_le hf
  let Nosc := 2 * ((Finset.Icc 1 P).card : ℝ) * C * loss ^ 2
  let Nmean := ((Finset.Icc 1 P).card : ℝ) * C * loss ^ 6
  have hNosc : 0 ≤ Nosc := by dsimp only [Nosc]; positivity
  have hNmean : 0 ≤ Nmean := by dsimp only [Nmean]; positivity
  have hNorms := b.velocityProfileSums_of_actualLevels hP (P + 1) hf hLoss hC ht₀ htT γ hγ hγpos hLevels
  have hOscNorm := hNorms.1
  have hMeanNorm := hNorms.2.2
  have hSlice {u : Velocity}
      (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3))) :
      ContDiff ℝ ∞ (u t) :=
    contDiffOn_univ.mp (hu.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  have hMeanIndependent : HierarchyPeriodicProfile.PhaseIndependent mean.val.val :=
    (average_is_mean hT d.inverse d.strain d.covector (b.profiles.velocity P)).1
  have hParentNonneg : 0 ≤ Cparent * μ ^ (5 * (P + 1) + 1) :=
    (norm_nonneg _).trans (hParentJets t ht 0 (Nat.zero_le _) 0)
  obtain ⟨hUreg, hParentNorm⟩ := spatialHolderHalfNorm_le_of_uniformJets (hSlice hU)
    hParentNonneg (hParentJets t ht)
  let mBudget := (((3 : ℝ) * 2 ^ n * L) ^ n * (4 ^ n * Nmean)) * D ^ ((a + 1) * n)
  have mNonneg : 0 ≤ mBudget := by dsimp only [mBudget]; positivity
  have hmj := graphRead_frequency_jetBound_mean (A := A) (B := B t) (a := a) (p := 0)
    hT mean hMeanIndependent ht hℓ hD hfpos hL hNmean hLabel (hA t ht)
    (hB t ht) (hBreg t ht) (hcoeff t ht)
    (by simpa only [pow_zero,mul_one] using hMeanNorm)
  have hMeanJets : PhaseJetBound (P + 1) (mBudget * freq ^ (-5 / 2 : ℝ)) (b.meanCorrection t) := by
    change PhaseJetBound (P + 1) (mBudget * freq ^ (-5 / 2 : ℝ)) (graphRead A mean t)
    dsimp only [mBudget, n]
    simpa only [add_zero] using hmj
  obtain ⟨hMreg, hMnorm⟩ := spatialHolderHalfNorm_le_of_uniformJets
    (hSlice properties.mean_smooth) (by positivity : 0 ≤ mBudget * freq ^ (-5 / 2 : ℝ)) hMeanJets
  have hMeanRate : spatialHolderHalfNorm P (b.meanCorrection t) ≤
      Cmean * D ^ (schedule * (P + 2)) * freq ^ (-5 / 2 : ℝ) := by
    calc
      _ ≤ (3 * ((P : ℝ) + 1)) * (mBudget * freq ^ (-5 / 2 : ℝ)) := hMnorm
      _ = ((3 * ((P : ℝ) + 1)) * mBudget) * freq ^ (-5 / 2 : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hMeanGraphCost (Real.rpow_nonneg hfpos.le _)
  have hOscRate : SpatialHolderHalf P (b.oscillation t) ∧
      spatialHolderHalfNorm P (b.oscillation t) ≤
        Cosc * D ^ (schedule * (P + 2)) * freq ^ ((3 : ℝ) * (P + 1) / 2 - 5 / 4) := by
    let oBudget := (((3 : ℝ) * 2 ^ n * (2 * L)) ^ n * (4 ^ n * Nosc)) * D ^ ((max a 1 + 1) * n)
    have oNonneg : 0 ≤ oBudget := by dsimp only [oBudget]; positivity
    by_cases ha : t₀ ≤ t
    · have ha' : t ∈ Icc t₀ T := ⟨ha,ht.2⟩
      have hoj := graphRead_frequency_jetBound_weighted (A := A) (B := B t) (a := a) (p := 0)
        hT ht₀ htT γ hγ hγpos osc ha' hℓ hh hD hf hL hNosc hLabel hWidth hCarrier
        (hA t ht) (hB t ht) (hBreg t ht) (hcoeff t ht)
        (by simpa only [pow_zero,mul_one] using hOscNorm)
      have hOscJets : PhaseJetBound (P + 1)
          (oBudget * freq ^ ((3 : ℝ) * (P + 1) / 2 - 5 / 4)) (b.oscillation t) := by
        intro j hj x
        refine (hoj j hj x).trans ?_
        simp only [add_zero]
        refine mul_le_mul_of_nonneg_left ?_ oNonneg
        have hExp :
            (3 : ℝ) * ((P + 1 : ℕ) : ℝ) / 2 + -5 / 4 =
              (3 : ℝ) * (P + 1) / 2 - 5 / 4 := by push_cast; ring
        rw [hExp]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hγone t ha') (Real.rpow_nonneg hfpos.le ((3 : ℝ) * (P + 1) / 2 - 5 / 4))
      obtain ⟨hOreg,hOnorm⟩ := spatialHolderHalfNorm_le_of_uniformJets
        (hSlice properties.oscillation_smooth)
        (by positivity : 0 ≤ oBudget * freq ^ ((3 : ℝ) * (P + 1) / 2 - 5 / 4)) hOscJets
      refine ⟨hOreg,hOnorm.trans ?_⟩
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hOscGraphCost (Real.rpow_nonneg hfpos.le _)
    · have hZero := hInactive t ht (lt_of_not_ge ha)
      have hOzeroJets : PhaseJetBound (P + 1) (0 : ℝ) (b.oscillation t) := by
        intro j hj x
        rw [hZero]
        simp
      obtain ⟨hOreg,hOnorm⟩ := spatialHolderHalfNorm_le_of_uniformJets
        (hSlice properties.oscillation_smooth) (show 0 ≤ (0 : ℝ) by norm_num) hOzeroJets
      have hCap : 0 ≤ Cosc * D ^ (schedule * (P + 2)) :=
        (mul_nonneg (by positivity) oNonneg).trans hOscGraphCost
      exact ⟨hOreg, hOnorm.trans (by rw [mul_zero]; exact mul_nonneg hCap (Real.rpow_nonneg hfpos.le _))⟩
  refine velocityDepth_from_holder hμ hSchedule hCp hCo hCm
    (congrFun b.velocity_eq_parent_add_oscillation_add_mean t) hUreg hOscRate.1 hMreg ?_
    hOscRate.2 hMeanRate
  exact hParentNorm.trans_eq (by ring)

end PhysicalApproximationData

end

end TorusEuler.HierarchyTwistedProfile

namespace TorusEuler.InductiveEulerStage

/-- A uniform parent Bernstein constant over all spatial orders needed for the
full-depth half-Hölder norm of the approximate velocity. -/
theorem exists_velocity_bernstein_bounds_through_depth :
    ∃ C : ℕ → ℝ, (∀ N, 0 ≤ C N) ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {activation : ℝ}
        (s : InductiveEulerStage P n activation), 1 ≤ P.frequency n →
        ∀ N : ℕ, ∀ t ∈ Icc 0 (P.slab n activation),
          PhaseJetBound (N + 1) (C N * P.frequency n ^ (5 * (N + 1) + 1)) (s.velocity t) := by
  obtain ⟨K, hK, hBernstein⟩ := exists_velocity_bernstein_bounds
  let C (N : ℕ) := ∑ i ∈ Finset.range (N + 2), K i
  have hC (N : ℕ) : 0 ≤ C N := Finset.sum_nonneg fun i _ => hK i
  refine ⟨C, hC, ?_⟩
  intro P n activation s hFreq N t ht j hj x
  have hj' : j ∈ Finset.range (N + 2) := Finset.mem_range.mpr (by omega)
  have hCap : K j ≤ C N := Finset.single_le_sum (fun i _ => hK i) hj'
  refine (hBernstein s hFreq j t ht x).trans (mul_le_mul hCap ?_ ?_ (hC N))
  · exact pow_le_pow_right₀ hFreq (by omega)
  · exact pow_nonneg (zero_le_one.trans hFreq) _

end TorusEuler.InductiveEulerStage

namespace TorusEuler.PhysicalWaveApproximationBounds

open HierarchyTwistedProfile

noncomputable section

variable {P : InductiveEulerParameters} {n : ℕ} {activationOld activation : ℝ}
local notation "Tchild" => P.slab (n + 1) activation
local notation "parentFreq" => P.frequency n
local notation "childFreq" => parentFreq ^ frequencyExponent P.exponentParameter (P.order (n + 1))
local notation "nextFreq" => childFreq ^ frequencyExponent P.exponentParameter (P.order (n + 2))
local notation "depth" => 6 * frequencyExponent P.exponentParameter (P.order (n + 2))

/-- The physical graph estimates on one actual approximation supply the
scheduled velocity and residual fields. The pressure estimate is supplied
separately for the same graph pressure. -/
theorem of_actual_readout (parent : InductiveEulerStage P n activationOld)
    {k : Vec3} {hT : 0 < Tchild} {g : ParentGeometry hT parent.velocity parent.flow k}
    (b : PhysicalApproximationData g parent.pressure depth) (properties : PhysicalApproximationProperties b)
    {Cstep Cmean : ℝ}
    (hVelocity : ∀ t ∈ Icc 0 Tchild,
      1 + spatialHolderHalfNorm depth (b.velocity t) ≤ 3 * childFreq ^ (2 * (depth + 1)))
    (hResidual : ∀ t ∈ Icc 0 Tchild, spatialHolderHalfNorm 1 (b.residual t) ≤ nextFreq ^ (-7 / 2 : ℝ))
    (hOscillation : ∀ t ∈ Icc 0 Tchild, ∀ x, ‖b.oscillation t x‖ ≤ Cstep * childFreq ^ (-5 / 4 : ℝ))
    (hMean : ∀ m ≤ P.order (n + 1), ∀ t ∈ Icc 0 Tchild,
      SpatialHolderHalf m (b.meanCorrection t) ∧
        spatialHolderHalfNorm m (b.meanCorrection t) ≤
          Cmean * (parentFreq ^ 9) ^ (P.exponentParameter * (m + 2)) * childFreq ^ (-5 / 2 : ℝ))
    (hPressure : ∀ t ∈ Icc 0 Tchild, ∀ x v : Vec3,
      ⟪v, fderiv ℝ (gradient (b.pressure t)) x v⟫_ℝ ≤
        ⟪v, fderiv ℝ (gradient (parent.pressure t)) x v⟫_ℝ +
          (Cstep * childFreq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2) :
    PhysicalWaveApproximationBounds parent activation b.velocity b.residual b.oscillation b.meanCorrection
      (b.potential properties) Cstep Cmean := by
  have hChild : P.frequency (n + 1) = childFreq := P.frequency_step n
  have hNext : P.frequency (n + 2) = nextFreq := by
    rw [P.frequency_step (n + 1), hChild]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hChild] using hVelocity
  · simpa only [hNext] using hResidual
  · simpa only [hChild] using hOscillation
  · simpa only [hChild] using hMean
  · intro t ht x v
    rw [b.potential_eq properties ht, hChild]
    exact hPressure t ht x v

end

end TorusEuler.PhysicalWaveApproximationBounds
