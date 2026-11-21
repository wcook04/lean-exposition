import TorusEuler.HierarchyTwistedRelayBounds

/-! The selected recurrence reads the actual weighted linear relay at the previous level. -/

open ContinuousLinearMap Set
open scoped InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)

/-- The physical completion of the zero activation force is zero. -/
theorem complete_zero_of_phaseIndependent (hT : 0 < T) (G : MP) (κ : VP)
    (hGPhase : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    (hκPhase : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0) :
    complete hT G κ hκPhase hκ 0 = 0 := by
  apply ext
  intro x hx
  have h := complete_apply_relayPotential hT G κ (0 : VP) hGPhase hκPhase hκ (map_zero _) hx.1 x.2
  have hzero : relayPotentialProfile (fun a => κ.val.val.val (x.1, a, 0))
      (fun _ => (0 : Vec3)) = fun _ => 0 := by
    simpa only [zero_smul] using relayPotentialProfile_const_smul 0
      (fun a => κ.val.val.val (x.1, a, 0)) (fun _ => (0 : Vec3))
  change (complete hT G κ hκPhase hκ 0).val.val.val (x.1, x.2) = 0
  rw [h]
  change curlOfDerivative ((hierarchyRelayLabelJet
    (relayPotentialProfile (fun a => κ.val.val.val (x.1, a, 0))
      (fun _ => (0 : Vec3))) x.2).comp (G.val.val.val (x.1, x.2.1, 0))) = 0
  simp only [hzero, hierarchyRelayLabelJet, fderiv_fun_const, Pi.zero_apply, zero_comp]
  exact map_zero curlOfDerivativeCLM

set_option maxHeartbeats 2400000 in
/-- The actual level-`p` relay is controlled by the measured oscillation
and selected source at level `p - 1`. At level two the transverse activation
force is exactly removed by its curl completion. -/
theorem construct_amplitudeSeminorm_relayAtLevel_le (hT : 0 < T)
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
    {P p : ℕ} (hp : p ∈ Finset.Icc 2 P) (completionSwitch residual activationForce : VP)
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
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) {freq K : ℝ} (hfreq : 0 < freq)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hCoeff : WaveRelayCoefficientBudget ℓ h n K
      (fun (t : Icc t₀ T) a => G.val.val.val (t, a, 0))
      (fun (t : Icc t₀ T) a => M.val.val.val (t, a, 0))
      (fun (t : Icc t₀ T) a => freq⁻¹ • κ.val.val.val (t, a, 0))) :
    let ops := twistedHierarchyOperators hT G M κ
    let u := S.construct P completionSwitch residual hR leading
    let s := actualMeasuredLevels ops u P completionSwitch residual freq hfreq.le
      ℓ h hT ht₀ htT γ hγ hpos
    amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos (ops.relayAtLevel u completionSwitch p) ≤
      waveRelayOrderConstant n * K ^ 2 * freq⁻¹ *
        (s.osc (n + 1) (p - 1) + s.oscSource (n + 1) (p - 1)) := by
  intro ops u s
  let i := p - 1
  let W (m : ℕ) : Seminorm ℝ VP := amplitudeSeminorm False ℓ h m hT ht₀ htT γ hγ hpos
  let Wp (m : ℕ) : Seminorm ℝ SP := amplitudeSeminorm False ℓ h m hT ht₀ htT γ hγ hpos
  let H := ops.sourceBeforeMean u P completionSwitch i
  let F := -(H - ops.average H) - hierarchyAdvectionAtLevel P 1 i (ops.meanPhaseProduct u)
  let F' := if p = 2 then 0 else F
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
  have hData : ops.average (u.V i) = 0 ∧ ops.average F' = 0 ∧
      ∀ t ∈ Icc 0 T, ∀ x, R.val.val.val (t, x) = waveRelayAt G M κ (u.V i) F' t x := by
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
  have hbase := boundedWeightSeminorm_waveRelay_le_of_eval hT G M κ (u.V i) F' R
    ℓ h hℓ n hfreq (Icc_subset_Icc_left ht₀) (fun t => (γ t)⁻¹)
    (inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hpos).choose_spec
    hData.1 hData.2.1 (fun t ht x => hData.2.2 t (Icc_subset_Icc_left ht₀ ht) x) hCoeff
  have hv : W (n + 1) (u.V i) ≤ s.osc (n + 1) i := by
    change _ ≤ W (n + 1) (u.V i) + freq * Wp (n + 1) (u.p i)
    exact le_add_of_nonneg_right (mul_nonneg hfreq.le (apply_nonneg _ _))
  have hf : W (n + 1) F' ≤ s.oscSource (n + 1) i := by
    change W (n + 1) (if p = 2 then 0 else F) ≤ if i = 1 then 0 else W (n + 1) F
    have hi : i = 1 ↔ p = 2 := by dsimp [i]; omega
    by_cases hp₂ : p = 2
    · rw [ite_eq_left hp₂, ite_eq_left (hi.mpr hp₂), map_zero]
    · rw [ite_eq_right hp₂, ite_eq_right (fun h => hp₂ (hi.mp h))]
  exact hbase.trans (mul_le_mul_of_nonneg_left (add_le_add hv hf) (by
    unfold waveRelayOrderConstant
    positivity))

end

end TorusEuler.HierarchyTwistedProfile
