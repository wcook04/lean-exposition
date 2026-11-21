import TorusEuler.TerminalHierarchyRelayReadout
import TorusEuler.TerminalHierarchyTime
import TorusEuler.HierarchySelectedLinearEstimates

/-! Actual retained and final time-differentiated relays. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)
local notation "SP" => HierarchyTwistedProfile T k ℝ

/-- The exact force in the preceding transverse equation. At level two,
the separately subtracted activation completion removes this force. -/
def waveRelayPrecedingForce (A : HierarchyOperators VP SP)
    (u : HierarchyProfiles VP SP) (P : ℕ) (completionSwitch : VP) (p : ℕ) : VP :=
  let i := p - 1
  let H := A.sourceBeforeMean u P completionSwitch i
  if p = 2 then 0 else -(H - A.average H) - hierarchyAdvectionAtLevel P 1 i (A.meanPhaseProduct u)

set_option maxHeartbeats 2400000 in
/-- The selected relay identity holds also one level past the finite solve,
where it identifies the linear term of the exact depth remainder. -/
theorem construct_relayAtLevel_eq_waveRelayAt (hT : 0 < T)
    (G M : MP) (κ : VP)
    (hGPhase : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    (hMPhase : HierarchyPeriodicProfile.PhaseIndependent M.val.val)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0)
    (hGdot : ∀ t ∈ Icc 0 T, ∀ a,
      HasDerivWithinAt (fun r => G.val.val.val (r, a, 0))
        (-((G.val.val.val (t, a, 0)).comp (M.val.val.val (t, a, 0)))) (Icc 0 T) t)
    (hκdot : ∀ t ∈ Icc 0 T, ∀ a, HasDerivWithinAt
      (fun r => κ.val.val.val (r, a, 0))
      (-((M.val.val.val (t, a, 0)).adjoint (κ.val.val.val (t, a, 0)))) (Icc 0 T) t)
    (S : FiniteHierarchySolvers (twistedHierarchyOperators hT G M κ))
    (hcomplete : ∀ v, S.complete v = complete hT G κ hκPhase hκ v)
    {P p : ℕ} (hp : p ∈ Finset.Icc 2 (P + 1)) (completionSwitch residual activationForce : VP)
    (hR : (twistedHierarchyOperators hT G M κ).average residual = residual)
    (leading : HierarchyTransverseOutput (twistedHierarchyOperators hT G M κ))
    (hLeading : let ops := twistedHierarchyOperators hT G M κ
      ops.material leading.V + ops.phaseGrad leading.p = activationForce)
    (hSwitch : completionSwitch = complete hT G κ hκPhase hκ activationForce)
    (hActivationMean : (twistedHierarchyOperators hT G M κ).average activationForce = 0)
    (hActivationTransverse : ∀ t ∈ Icc 0 T, ∀ a s,
      ⟪κ.val.val.val (t, a, 0), activationForce.val.val.val (t, a, s)⟫_ℝ = 0)
    (hLeadingP : ∀ t ∈ Icc 0 T, ∀ a, phaseMean (fun r => leading.p.val.val.val (t, a, r)) = 0)
    (hSelectedP : ∀ f hf, ∀ t ∈ Icc 0 T, ∀ a,
      phaseMean (fun r => (S.solveTransverse f hf).val.p.val.val.val (t, a, r)) = 0)
    :
    let ops := twistedHierarchyOperators hT G M κ
    let u := S.construct P completionSwitch residual hR leading
    let F' := waveRelayPrecedingForce ops u P completionSwitch p
    ops.average (u.V (p-1)) = 0 ∧ ops.average F' = 0 ∧
      ∀ t ∈ Icc 0 T, ∀ x, (ops.relayAtLevel u completionSwitch p).val.val.val (t,x) =
        waveRelayAt G M κ (u.V (p-1)) F' t x := by
  intro ops u F'
  let i := p - 1
  let H := ops.sourceBeforeMean u P completionSwitch i
  let F := -(H - ops.average H) - hierarchyAdvectionAtLevel P 1 i (ops.meanPhaseProduct u)
  let R := ops.relayAtLevel u completionSwitch p
  obtain ⟨h₂, hP⟩ := Finset.mem_Icc.mp hp
  have hiRetained : i ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by dsimp [i]; omega, by dsimp [i]; omega⟩
  have hC : u.C i = complete hT G κ hκPhase hκ (u.V i) :=
    (S.construct_completion hiRetained completionSwitch residual hR leading).trans (hcomplete _)
  have transverseAt (o : HierarchyTransverseOutput ops) (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3 × ℝ) :
      ⟪κ.val.val.val (t, x.1, 0), o.V.val.val.val (t, x)⟫_ℝ = 0 := by
    have h := transverse_of_phaseAdv_eq_zero hT G M κ o.V o.phaseAdv_V
      (t, x) ⟨ht, mem_univ _⟩
    rwa [hκPhase (t, x.1, 0) ⟨ht, mem_univ _⟩ x.2] at h
  change ops.average (u.V i) = 0 ∧ ops.average F' = 0 ∧
      ∀ t ∈ Icc 0 T, ∀ x, R.val.val.val (t, x) = waveRelayAt G M κ (u.V i) F' t x
  by_cases hp₂ : p = 2
  · have hi : i = 1 := by dsimp [i]; omega
    obtain ⟨hv, hpr, _, _⟩ := S.construct_leading P completionSwitch residual hR leading
    have hV : u.V i = leading.V := by rw [hi]; exact hv
    have hpV : u.p i = leading.p := by rw [hi]; exact hpr
    have hf : F' = 0 := ite_eq_left hp₂
    refine ⟨hV.symm ▸ leading.average_V, hf.symm ▸ map_zero _, ?_⟩
    intro t ht x
    have hEval := material_complete_add_labelGrad_sub_switch_apply_relay hT G M κ
      leading.V activationForce leading.p hGPhase hMPhase hκPhase hκ
      leading.average_V hActivationMean hGdot hκdot
      (fun r hr a s => transverseAt leading r hr (a, s)) hActivationTransverse hLeadingP hLeading ht x
    change (ops.material (u.C i) + ops.labelGrad (u.p i) -
      (if p = 2 then completionSwitch else 0)).val.val.val (t, x) = _
    rw [hC, hV, hpV, ite_eq_left hp₂, hSwitch, hf]
    exact hEval
  · have hiCorrection : i ∈ Finset.Icc 2 P :=
      Finset.mem_Icc.mpr ⟨by dsimp [i]; omega, by dsimp [i]; omega⟩
    obtain ⟨hf, hV, hpV⟩ := S.construct_transverse_selected hiCorrection
      completionSwitch residual hR leading
    let o := (S.solveTransverse F hf).val
    change u.V i = o.V at hV
    change u.p i = o.p at hpV
    have hf' : F' = F := ite_eq_right hp₂
    refine ⟨hV.symm ▸ o.average_V, hf'.symm ▸ hf, ?_⟩
    intro t ht x
    have hEval := material_complete_add_labelGrad_apply_relay_of_momentum hT G M κ
      o.V F o.p hGPhase hMPhase hκPhase hκ o.average_V hGdot hκdot
      (fun r hr a s => transverseAt o r hr (a, s)) (hSelectedP F hf)
      (S.solveTransverse F hf).property ht x
    change (ops.material (u.C i) + ops.labelGrad (u.p i) -
      (if p = 2 then completionSwitch else 0)).val.val.val (t, x) = _
    rw [hC, hV, hpV, ite_eq_right hp₂, sub_zero, hf']
    exact hEval

/-- The bundled phase average has zero value exactly when every
instantaneous phase integral vanishes. -/
theorem phaseMeanZero_of_profilePhaseAverage_eq_zero (hT : 0 < T) (v : VP)
    (hv : profilePhaseAverage hT v = 0) : PhaseMeanZero v := by
  intro t ht a
  have he := congrArg (fun u : VP => u.val.val.val (t,a,0)) hv
  change (HierarchySmoothProfile.profilePhaseAverage hT v.val.val).val (t,a,0) = 0 at he
  rw [HierarchySmoothProfile.profilePhaseAverage_apply hT v.val.val
    (show (t,a,(0 : ℝ)) ∈ hierarchyProfileSlab T from ⟨ht, mem_univ _⟩)] at he
  exact he

/-- The selected relay's exact weighted time estimate follows from the
canonical phase-integral representation. -/
theorem timeJetSeminorm_waveRelay_le_of_eval (hT : 0 < T) (q : ℕ) (ell h : ℝ) (n : ℕ)
    (G M : MP) (κ v f r : VP) {freq : ℝ} (hfreq : 0 < freq) (hell : ell ≠ 0)
    (C : WaveRelayTimeCoefficients G M κ ell freq) {K : ℝ} (hK : 0 ≤ K)
    (hCoeff : WaveRelayTimeCoefficientBudget C hT h q n K)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ) {B : ℝ} (hτ : ∀ t ∈ A, ‖τ t‖ ≤ B)
    (hv : profilePhaseAverage hT v = 0) (hf : profilePhaseAverage hT f = 0)
    (hEval : ∀ t ∈ Icc 0 T, ∀ x, r.val.val.val (t,x) = waveRelayAt G M κ v f t x) :
    timeJetSeminorm hT q (boundedWeightSeminorm False ell h n hT hA τ hτ) r ≤
      WaveRelayTimeCoefficients.terminalWaveRelayTimeOrderCost n * K ^ 2 * freq⁻¹ *
        (timeJetSeminorm hT q (boundedWeightSeminorm False ell h (n+1) hT hA τ hτ) v +
          timeJetSeminorm hT q (boundedWeightSeminorm False ell h (n+1) hT hA τ hτ) f) := by
  let hv' := phaseMeanZero_of_profilePhaseAverage_eq_zero hT v hv
  let hf' := phaseMeanZero_of_profilePhaseAverage_eq_zero hT f hf
  have he : r = C.relayProfile hT h v f hv' hf' := by
    apply HierarchyTwistedProfile.ext
    rintro ⟨t,x⟩ hx
    exact (hEval t hx.1 x).trans (C.relayProfile_eq_waveRelayAt hT h v f hv' hf' hell hfreq hx.1 x).symm
  rw [he]
  exact C.relayProfile_timeJet_le hT q h n hfreq hA τ hτ hK hCoeff v f hv' hf'

namespace PhysicalApproximationData

variable {U : Velocity} {X : ℝ → Velocity} {p : Pressure}
  {hT : 0 < T} {d : ParentGeometry hT U X k} {P : ℕ}

local notation "I" => Icc (0 : ℝ) T
local notation "J" => Set.prod I (univ : Set Vec3)

set_option maxHeartbeats 2700000 in
/-- One coefficient budget estimates the actual completion and all relays,
including the last linear term of the depth remainder. -/
theorem selectedLinearTimeEstimates (b : PhysicalApproximationData d p P) (lead : LeadingRelayData b)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t))
    (ell h : ℝ) (hell : ell ≠ 0) (q n : ℕ) {freq K L : ℝ} (hfreq : 0 < freq)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (C : WaveRelayTimeCoefficients d.inverse d.strain d.covector ell freq)
    (hCoeff : WaveRelayTimeCoefficientBudget C hT h q n K) (hK : 0 ≤ K)
    (hCap : WaveRelayTimeCoefficients.terminalWaveRelayTimeOrderCost n * K ^ 2 ≤ L) :
    let U₀ : ℕ → Seminorm ℝ VP := fun n => timeJetSeminorm hT q (unweightedSeminorm False ell h n hT)
    let Ulower : ℕ → Seminorm ℝ VP := fun n => timeJetSeminorm hT (q-1) (unweightedSeminorm False ell h n hT)
    let W : ℕ → Seminorm ℝ VP := fun n => timeJetSeminorm hT q
      (amplitudeSeminorm False ell h n hT ht₀ htT γ hγ hpos)
    let Q : ℕ → Seminorm ℝ SP := fun n => timeJetSeminorm hT q
      (amplitudeSeminorm False ell h n hT ht₀ htT γ hγ hpos)
    let s := HierarchyMeasuredLevels.ofProfilesWithMeanForce b.operators b.profiles P
      b.leading.completionSwitch b.parentResidual freq hfreq.le U₀ Ulower W Q
    (∀ v, b.operators.average v = 0 → W n (b.solvers.complete v) ≤ L * freq⁻¹ * W (n+1) v) ∧
    (∀ i ∈ Finset.Icc 2 (P+1), W n (b.operators.relayAtLevel b.profiles b.leading.completionSwitch i) ≤
      L * (freq⁻¹ * (s.osc (n+1) (i-1) + s.oscSource (n+1) (i-1)))) := by
  intro U₀ Ulower W Q s
  let A := Icc t₀ T
  have hA : A ⊆ I := Icc_subset_Icc_left ht₀
  let τ (t : ℝ) := (γ t)⁻¹
  have hτ := (inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hpos).choose_spec
  have hGeom := transportedWaveRelay_coefficient_timeEquations hT hX (hU.of_le (by simp)) hper
    d.inverse d.strain d.covector (fun t ht a => d.inverse_value (t,a,0) ⟨ht,mem_univ _⟩)
    (fun t ht a => d.strain_value (t,a,0) ⟨ht,mem_univ _⟩)
    (fun t ht a => d.covector_value (t,a,0) ⟨ht,mem_univ _⟩)
  constructor
  · intro v hv
    have he := C.completionProfile_eq_complete hT h v hv d.mean.inverse_independent
      d.oscillation.covector_independent d.oscillation.covector_ne_zero hell hfreq
    have h := C.completionProfile_timeJet_le hT q h n hfreq hA τ hτ hK hCoeff v
      (phaseMeanZero_of_profilePhaseAverage_eq_zero hT v hv)
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCap (inv_nonneg.mpr hfreq.le)) (apply_nonneg _ _))
  · intro i hi
    let F := waveRelayPrecedingForce b.operators b.profiles P b.leading.completionSwitch i
    have hData := construct_relayAtLevel_eq_waveRelayAt hT d.inverse d.strain d.covector
      d.mean.inverse_independent (parentStrain_phaseIndependent (d := d)) d.oscillation.covector_independent
      d.oscillation.covector_ne_zero hGeom.1 hGeom.2 b.solvers (fun _ => rfl) hi
      b.leading.completionSwitch b.parentResidual b.leading.leadingSwitch b.parentResidual_average b.leading.output
      b.leading.momentum lead.completion_switch lead.activation_mean lead.activation_transverse lead.pressure_mean
      (fun f hf' => (solveTransverse hT d.inverse d.strain d.covector d.oscillation f hf').pressure_mean)
    have h := timeJetSeminorm_waveRelay_le_of_eval hT q ell h n d.inverse d.strain d.covector
      (b.profiles.V (i-1)) F (b.operators.relayAtLevel b.profiles b.leading.completionSwitch i)
      hfreq hell C hK hCoeff hA τ hτ hData.1 hData.2.1 hData.2.2
    have hV : W (n+1) (b.profiles.V (i-1)) ≤ s.osc (n+1) (i-1) :=
      le_add_of_nonneg_right (mul_nonneg hfreq.le (apply_nonneg _ _))
    have hF : W (n+1) F = s.oscSource (n+1) (i-1) := by
      have hi' := (Finset.mem_Icc.mp hi).1
      have hcase : i - 1 = 1 ↔ i = 2 := by omega
      let H := b.operators.sourceBeforeMean b.profiles P b.leading.completionSwitch (i-1)
      let src := -(H - b.operators.average H) -
        hierarchyAdvectionAtLevel P 1 (i-1) (b.operators.meanPhaseProduct b.profiles)
      change W (n+1) (if i = 2 then 0 else src) = if i - 1 = 1 then 0 else W (n+1) src
      by_cases htwo : i = 2
      · rw [ite_eq_left htwo, ite_eq_left (hcase.mpr htwo), map_zero]
      · rw [ite_eq_right htwo, ite_eq_right (fun e => htwo (hcase.mp e))]
    rw [mul_assoc (WaveRelayTimeCoefficients.terminalWaveRelayTimeOrderCost n * K ^ 2)] at h
    refine h.trans (mul_le_mul hCap (mul_le_mul_of_nonneg_left
      (add_le_add hV hF.le) (inv_nonneg.mpr hfreq.le)) (mul_nonneg (inv_nonneg.mpr hfreq.le) ?_) ?_)
    · exact add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
    · exact (mul_nonneg (WaveRelayTimeCoefficients.terminalWaveRelayTimeOrderCost_nonneg n)
        (sq_nonneg K)).trans hCap

end PhysicalApproximationData

end

end TorusEuler.HierarchyTwistedProfile
