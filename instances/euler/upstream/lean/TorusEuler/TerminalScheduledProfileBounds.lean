import TorusEuler.TerminalSelectedHierarchyTime
import TorusEuler.TerminalScheduledSourceCoefficients
import TorusEuler.TerminalScheduledRelayCoefficients
import TorusEuler.TerminalScheduledTransverseTime
import TorusEuler.TerminalScheduledMeanBounds
import TorusEuler.TerminalSelectedRelayTime
import TorusEuler.InductiveTerminalLeadingTime
import TorusEuler.InductiveTerminalSwitchTime

/-! One loss and one finite-order budget for the mixed norms of the
actual selected hierarchy. -/

open Set
open scoped ContDiff

namespace TorusEuler.ScheduledEulerConstruction

open HierarchyTwistedProfile

local notation "Q²(" m ")" => hierarchyQuadraticConstant (Fin 4) m ^ (2 : ℕ)

noncomputable section

section

set_option quotPrecheck false

variable {P : InductiveEulerParameters} (c : ScheduledEulerConstruction P) (j : ℕ)

local notation "d" => (c.selectedStep j).selected
local notation "tip" => c.construction.tip j
local notation "cfg" => (c.selectedStep j).selected.approximation
local notation "geom" => (c.selectedStep j).selected.parent.geometry
local notation "freq" => P.frequency (j+2)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The full-slab mixed seminorm in the selected label and phase scales. -/
abbrev terminalProfileTimeNorm (q m : ℕ) :
    Seminorm ℝ (HierarchyTwistedProfile (c.construction.slab (j+2)) (d).carrier E) :=
  timeJetSeminorm (d).time_pos q (unweightedSeminorm False (d).radius (d).width m (d).time_pos)

/-- The active-slab mixed seminorm with the actual central amplitude weight. -/
abbrev terminalAmplitudeTimeNorm (q m : ℕ) :
    Seminorm ℝ (HierarchyTwistedProfile (c.construction.slab (j+2)) (d).carrier E) :=
  timeJetSeminorm (d).time_pos q
    (amplitudeSeminorm False (d).radius (d).width m (d).time_pos (tip).next_activation_nonnegative
      (d).regularity.start_lt_end.le (d).centerWeight (d).centerWeight_continuous (d).centerWeight_pos)

/-- The mean force uses a time derivative less than the retained profiles. -/
abbrev terminalMeasuredLevels (q : ℕ) : HierarchyMeasuredLevels :=
  HierarchyMeasuredLevels.ofProfilesWithMeanForce (cfg).operators (cfg).profiles (d).depth
    (cfg).leading.completionSwitch (cfg).parentResidual freq
    (zero_le_one.trans (d).child_frequency_ge_one) (terminalProfileTimeNorm c j q)
    (terminalProfileTimeNorm c j (q-1)) (terminalAmplitudeTimeNorm c j q)
    (terminalAmplitudeTimeNorm c j q)

/-- The final scalar is determined by the retained depth and the fixed
analytic cost at the derivative reserve. -/
def terminalProfileTailFactor (depth : ℕ) (K : ℝ) : ℝ :=
  let C := hierarchyLevelConstant depth K depth
  2 * K * (C+1)^2 * (1 + ((hierarchyTailPairs depth 0).card : ℝ) +
    2 * ((hierarchyTailPairs depth 1).card : ℝ))

/-- Quantitative bounds for all available spatial orders on the actual
selected finite expansion and its activation correction. -/
structure ScheduledMixedProfileBounds (q H : ℕ) (K L : ℝ) : Prop where
  one_le_cost : 1 ≤ K
  one_le_loss : 1 ≤ L
  oscillation : ∀ m, m + 3 * (d).depth ≤ H →
    terminalAmplitudeTimeNorm c j q m
      ((cfg).profiles.velocity (d).depth - (cfg).operators.average ((cfg).profiles.velocity (d).depth)) ≤
      2 * ((Finset.Icc 1 (d).depth).card : ℝ) * hierarchyLevelConstant (d).depth K (d).depth *
        L ^ 2 * freq ^ (-5 / 4 : ℝ)
  mean : ∀ m, m + 3 * (d).depth ≤ H →
    terminalProfileTimeNorm c j q m ((cfg).operators.average ((cfg).profiles.velocity (d).depth)) ≤
      ((Finset.Icc 1 (d).depth).card : ℝ) * hierarchyLevelConstant (d).depth K (d).depth *
        L ^ 6 * freq ^ (-5 / 2 : ℝ)
  remainder : ∀ m, m + 3 * (d).depth ≤ H →
    terminalProfileTimeNorm c j q m ((cfg).operators.remainder (cfg).profiles (d).depth) ≤
      terminalProfileTailFactor (d).depth K * freq ^ hierarchyOscExponent ((d).depth+1)
  activation : ∀ m, m + 1 ≤ H →
    terminalAmplitudeTimeNorm c j q m ((cfg).leading.leadingSwitch + (cfg).leading.completionSwitch) ≤
      2 * (K * L) ^ 2 * freq ^ (-5 / 4 : ℝ)

set_option maxHeartbeats 4500000 in
/-- Aggregate the fitted primitive rows on the same selected profiles. -/
theorem scheduledMixedProfileBounds_of_rows {q H : ℕ} {K L : ℝ}
    (hK : 1 ≤ K) (hL : 1 ≤ L) (hSmall : L^6 * freq ^ (-1 / 12 : ℝ) ≤ 1)
    (rowCap : ℕ → ℝ)
    (hrow : ∀ m, m + 1 ≤ H → ∀ i : Fin 3,
      terminalProfileTimeNorm c j q m (scaledCoframeRowProfile (d).radius (geom).inverse i) ≤ rowCap m)
    (hRowCap : ∀ m, m + 1 ≤ H → 2 * (3 * Q²(m) * rowCap m) ≤ K * L)
    (hFastCap : ∀ m, m + 1 ≤ H →
      (2 * Q²(m)) * terminalProfileTimeNorm c j q m
          (scaledPhaseCoefficientProfile (d).width (geom).covector) ≤ K * L * freq ^ (3 / 2 : ℝ))
    (hResidual : ∀ m, m + 1 ≤ H → terminalProfileTimeNorm c j (q - 1) m (cfg).parentResidual ≤
      K * L * freq ^ hierarchyMeanExponent 2)
    (hSeed : ∀ m ≤ H, terminalAmplitudeTimeNorm c j q m (cfg).leading.output.V +
      freq * terminalAmplitudeTimeNorm c j q m (cfg).leading.output.p ≤ K * L * freq ^ hierarchyOscExponent 1)
    (hSwitch : ∀ m ≤ H, terminalAmplitudeTimeNorm c j q m (cfg).leading.leadingSwitch ≤
      K * L * freq ^ (-5 / 4 : ℝ))
    (hMean : ∀ m, m + 1 ≤ H → ∀ f hf,
      terminalProfileTimeNorm c j q m ((cfg).solvers.solveMean f hf).val.B ≤
        K * L * terminalProfileTimeNorm c j (q - 1) (m+1) f)
    (hOsc : ∀ m ≤ H, ∀ i ∈ Finset.Icc 2 (d).depth,
      (terminalMeasuredLevels c j q).osc m i ≤ K * L * (terminalMeasuredLevels c j q).oscSource m i)
    (hComplete : ∀ m, m + 1 ≤ H → ∀ v, (cfg).operators.average v = 0 →
      terminalAmplitudeTimeNorm c j q m ((cfg).solvers.complete v) ≤
        K * L * freq ^ (-1 : ℝ) * terminalAmplitudeTimeNorm c j q (m+1) v)
    (hRelay : ∀ m, m + 1 ≤ H → ∀ i ∈ Finset.Icc 2 ((d).depth+1),
      terminalAmplitudeTimeNorm c j q m ((cfg).operators.relayAtLevel (cfg).profiles (cfg).leading.completionSwitch i) ≤
        K * L * (freq ^ (-1 : ℝ) * ((terminalMeasuredLevels c j q).osc (m+1) (i-1) +
          (terminalMeasuredLevels c j q).oscSource (m+1) (i-1)))) :
    c.ScheduledMixedProfileBounds j q H K L := by
  let data (m : ℕ) (hm : m + 3 * (d).depth ≤ H) :=
    (cfg).selectedTimeHierarchyBounds (d).leadingRelayData q (d).depth_ge_two hm
      (d).parent.deformationOn.flow (d).parent.smooth_velocity (fun t _ => (tip).parent.periodic_velocity t)
      (tip).next_activation_nonnegative (d).regularity.start_lt_end.le (isClosed_tsupport _) (d).leading_inactive
      (d).radius (d).width (d).regularity.envelope_pos.ne' (d).regularity.phase_pos.ne' (d).centerWeight
      (d).centerWeight_continuous (d).centerWeight_pos (d).centerWeight_le_one
      (d).child_frequency_ge_one hL hK hSmall rowCap hrow hRowCap hFastCap hResidual hSeed
      hMean hOsc hComplete hRelay
  refine ⟨hK,hL,fun m hm => (data m hm).2.2.1,fun m hm => (data m hm).2.2.2.1,
    fun m hm => (data m hm).2.2.2.2,?_⟩
  intro m hm
  let W := terminalAmplitudeTimeNorm (E := Vec3) c j q m
  let A := K * L
  let R := freq ^ (-5 / 4 : ℝ)
  have hA : 1 ≤ A := one_le_mul_of_one_le_of_one_le hK hL
  have hA₀ : 0 ≤ A := zero_le_one.trans hA
  have hR : 0 ≤ R := Real.rpow_nonneg (zero_le_one.trans (d).child_frequency_ge_one) _
  have hF : freq ^ (-1 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (d).child_frequency_ge_one (by norm_num)
  have hs : W (cfg).leading.completionSwitch ≤ A * (A * R) := by
    rw [(d).leadingRelayData.completion_switch]
    have h := hComplete m hm _ (d).leadingRelayData.activation_mean
    have hnext := hSwitch (m+1) hm
    refine h.trans ?_
    calc
      _ ≤ (A * 1) * (A * R) := mul_le_mul
        (mul_le_mul_of_nonneg_left hF hA₀) hnext (apply_nonneg _ _) (by positivity)
      _ = _ := by ring
  calc
    W ((cfg).leading.leadingSwitch + (cfg).leading.completionSwitch) ≤
        W (cfg).leading.leadingSwitch + W (cfg).leading.completionSwitch := map_add_le_add _ _ _
    _ ≤ A * R + A * (A * R) :=
      add_le_add (hSwitch m ((Nat.le_succ _).trans hm)) hs
    _ ≤ 2 * A ^ 2 * R := by
      calc
        _ ≤ A * (A * R) + A * (A * R) :=
          add_le_add (le_mul_of_one_le_left (mul_nonneg hA₀ hR) hA) le_rfl
        _ = _ := by ring

/-- A finite reserve gives a single majorant for all included order costs. -/
def terminalHierarchyOrderMajorant (rowCost : ℕ → ℝ) (H : ℕ) : ℝ :=
  1 + ∑ m ∈ Finset.range (H + 1), rowCost m

theorem terminalHierarchyOrderMajorant_ge_one {rowCost : ℕ → ℝ}
    (h : ∀ m, 0 ≤ rowCost m) (H : ℕ) : 1 ≤ terminalHierarchyOrderMajorant rowCost H :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun m _ => h m)

theorem terminalHierarchyOrderMajorant_mono {rowCost : ℕ → ℝ}
    (h : ∀ m, 0 ≤ rowCost m) : Monotone (terminalHierarchyOrderMajorant rowCost) := by
  intro H H' hh
  exact add_le_add le_rfl (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.2 (Nat.succ_le_succ hh)) (fun m _ _ => h m))

theorem le_terminalHierarchyOrderMajorant {rowCost : ℕ → ℝ}
    (h : ∀ m, 0 ≤ rowCost m) {m H : ℕ} (hm : m ≤ H) :
    rowCost m ≤ terminalHierarchyOrderMajorant rowCost H :=
  (Finset.single_le_sum (fun k _ => h k) (Finset.mem_range.2 (Nat.lt_succ_iff.2 hm))).trans
    (le_add_of_nonneg_left zero_le_one)

end

open InductiveEulerTip.SelectedLaterInput in
set_option maxHeartbeats 9000000 in
/-- At every actual later stage, the parent jet bound supplies a single
polynomial loss for the complete mixed hierarchy and activation profile.
Its degree is independent of the derivative reserve and the selected depth. -/
theorem exists_scheduledProfileBounds (strength : ℝ) (hStrength : 2 ≤ strength) :
    ∃ (a₀ : ℕ) (N : ℝ), 16 ≤ a₀ ∧ Real.exp 1 ≤ N ∧
      ∀ (a q A : ℕ), a₀ ≤ a → ∃ (e : ℕ) (K : ℕ → ℝ),
        (∀ H, 1 ≤ K H) ∧ Monotone K ∧
        ∀ {P : InductiveEulerParameters} (c : ScheduledEulerConstruction P) (j H : ℕ),
          c.radiusExponent = a → N ≤ P.frequency 0 → P.strengthConstant = strength →
          c.construction.stages.StageTimeBounds q A (j+1) →
          ((P.frequency (j+1) ^ (9 : ℕ)) ^ e)^6 * P.frequency (j+2)^(-1 / 12 : ℝ) ≤ 1 →
          c.ScheduledMixedProfileBounds j (q+1) H (K H) ((P.frequency (j+1) ^ (9 : ℕ)) ^ e) := by
  obtain ⟨aMean, haMean, mean⟩ := exists_scheduledMeanTimeBounds
  obtain ⟨aOsc, Krec, _, hKrec, osc⟩ := exists_scheduledTransverseTimeBudget
  obtain ⟨aSeed, haSeed, seed⟩ := exists_leadingTimeJetBudget 16
  obtain ⟨Cswitch, Nswitch, hCswitch, _, sw⟩ := exists_switchTimeJetBudget strength hStrength
  let a₀ := max aMean (max aOsc aSeed)
  let N := max (Real.exp 1) Nswitch
  refine ⟨a₀, N, haMean.trans (le_max_left _ _), le_max_left _ _, ?_⟩
  intro a q A ha
  obtain ⟨E, C, hC, parent⟩ := exists_scheduledParentCoefficientTimeBounds q A
  obtain ⟨eMean, Kmean, hKmean, mean⟩ := mean q E C hC
  obtain ⟨Kosc, hKosc, osc⟩ := osc q E C hC
  obtain ⟨Kcoeff, hKcoeff, coeff⟩ := exists_scheduledTransverseTimeCoefficientBounds q E C hC
  obtain ⟨Kseed, hKseed, seed⟩ := seed (q+1) (4*E) Kcoeff Cswitch hKcoeff hCswitch
  obtain ⟨Krelay, hKrelay, relay⟩ := exists_scheduledWaveRelayTimeCoefficients q E C hC
  let Kslow (m : ℕ) := 2 * (3 * Q²(m) * terminalLabelTimeSeminormCost C (q+1) m)
  let Kfast (m : ℕ) := 2 * Q²(m) * terminalLabelTimeSeminormCost C (q+1) m
  let Kres (m : ℕ) := terminalLabelTimeSeminormCost C q m
  let Ktrans (m : ℕ) := transverseTimeCost 1 m (q+1) (Krec m) (Kosc m)
  let Klin (m : ℕ) := WaveRelayTimeCoefficients.terminalWaveRelayTimeOrderCost m * (Krelay m)^2
  let rows : Fin 7 → ℕ → ℝ := ![Kslow, Kfast, Kres, Kmean, Ktrans, Kseed, Klin]
  have hKs (m : ℕ) : 0 ≤ Kslow m := by
    exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (terminalLabelTimeSeminormCost_nonneg hC _ _))
  have hKf (m : ℕ) : 0 ≤ Kfast m :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (terminalLabelTimeSeminormCost_nonneg hC _ _)
  have hKr (m : ℕ) : 0 ≤ Kres m := terminalLabelTimeSeminormCost_nonneg hC _ _
  have hKt (m : ℕ) : 0 ≤ Ktrans m := by
    have hv := terminalApplyFieldCost_nonneg Vec3 Vec3 m
    have hp := terminalApplyFieldCost_nonneg Vec3 ℝ m
    have hr := hKrec m
    have ho := hKosc m
    unfold Ktrans transverseTimeCost
    positivity
  have hKl (m : ℕ) : 0 ≤ Klin m := mul_nonneg
    (WaveRelayTimeCoefficients.terminalWaveRelayTimeOrderCost_nonneg m) (sq_nonneg _)
  have hRows (i : Fin 7) (m : ℕ) : 0 ≤ rows i m := by
    fin_cases i
    · exact hKs m
    · exact hKf m
    · exact hKr m
    · exact hKmean m
    · exact hKt m
    · exact hKseed m
    · exact hKl m
  let rowCost (m : ℕ) := ∑ i : Fin 7, rows i m
  have hCost (m : ℕ) : 0 ≤ rowCost m := Finset.sum_nonneg (fun i _ => hRows i m)
  let K := terminalHierarchyOrderMajorant rowCost
  have hK (H : ℕ) : 1 ≤ K H := terminalHierarchyOrderMajorant_ge_one hCost H
  let eOsc := 20 + 4 * E * (q + 2)
  let eSeed := leadingTimeParentPower (q+1) (4*E)
  let eRelay := max (6 * E) (a + 2 * E)
  let e := a + E + (eMean + a) + eOsc + eSeed + 2 * eRelay
  refine ⟨e, K, hK, terminalHierarchyOrderMajorant_mono hCost, ?_⟩
  intro P c j H haEq hBase hStrengthEq hParent hSmall
  let d := (c.selectedStep j).selected
  let tip := c.construction.tip j
  let cfg := d.approximation
  let geom := d.parent.geometry
  let freq := P.frequency (j+2)
  let D := P.frequency (j+1) ^ (9 : ℕ)
  have hrMean : aMean ≤ c.radiusExponent := (le_max_left aMean (max aOsc aSeed)).trans (ha.trans haEq.ge)
  have hrOsc : aOsc ≤ c.radiusExponent := (le_max_left aOsc aSeed).trans
    ((le_max_right aMean _).trans (ha.trans haEq.ge))
  have hrSeed : aSeed ≤ c.radiusExponent := (le_max_right aOsc aSeed).trans
    ((le_max_right aMean _).trans (ha.trans haEq.ge))
  have hr : 16 ≤ c.radiusExponent := haSeed.trans hrSeed
  have hμ : 2 ≤ P.frequency (j+1) := d.parent_frequency_ge_two
  have hRaw := parent c j hμ hParent
  have hD : 1 ≤ D := one_le_two.trans d.parent_scale_ge_two
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hf : 0 < freq := zero_lt_one.trans_le d.child_frequency_ge_one
  let L := D ^ e
  have hK₀ : 0 ≤ K H := zero_le_one.trans (hK H)
  have hFit (i : Fin 7) {m b : ℕ} (hm : m ≤ H) (hb : b ≤ e) :
      rows i m * D ^ b ≤ K H * L := by
    have hRow : rows i m ≤ rowCost m := Finset.single_le_sum
      (fun k _ => hRows k m) (Finset.mem_univ i)
    exact mul_le_mul (hRow.trans (le_terminalHierarchyOrderMajorant hCost hm))
      (pow_le_pow_right₀ hD hb) (pow_nonneg hD₀ _) hK₀
  have hSources := c.scheduledTimeSourceCoefficientBounds j q E hC hr hRaw
  have hMean := mean c j hrMean ((le_max_left _ _).trans hBase) hμ hRaw
  have hOsc := osc c j hrOsc hRaw
  have hCoeff := coeff c j hr hRaw
  have hSwitch := (sw d ((le_max_right _ _).trans hBase) hStrengthEq).2.2.1
  obtain ⟨R, hRelay⟩ := relay c j hr hRaw
  let osc := geom.oscillation
  let gen (t : ℝ) (x : Vec3) := affineWaveAmplitudeOperator
    (fderiv ℝ (tip.parent.velocity t) (tip.parent.flow 0 t x)) (labelWaveVector tip.parent.flow 0 x d.carrier t)
  let pre (t : ℝ) (x : Vec3) := hierarchyRelayPressureAmplitudeCoefficient
    (fderiv ℝ (tip.parent.velocity t) (tip.parent.flow 0 t x))
    (freq⁻¹ • labelWaveVector tip.parent.flow 0 x d.carrier t)
  have hGenEq (t : ℝ) (ht : t ∈ Icc 0 (c.construction.slab (j+2))) (x : Vec3) :
      affineWaveAmplitudeOperator (osc.strain t x) (osc.covector t x) = gen t x := by
    have hv := geom.transverse_values ht x
    exact congrArg₂ affineWaveAmplitudeOperator hv.2.1 hv.2.2
  have hPreEq (t : ℝ) (ht : t ∈ Icc 0 (c.construction.slab (j+2))) (x : Vec3) :
      hierarchyRelayPressureAmplitudeCoefficient (osc.strain t x) (freq⁻¹ • osc.covector t x) = pre t x := by
    have hv := geom.transverse_values ht x
    exact congrArg₂ hierarchyRelayPressureAmplitudeCoefficient hv.2.1
      (congrArg (fun z : Vec3 => freq⁻¹ • z) hv.2.2)
  have hSmooth := contDiffOn_transverseTimeCoefficients osc freq hf.ne'
  have hGenSmooth := hSmooth.1.congr (fun x hx => (hGenEq x.1 hx.1 x.2).symm)
  have hPreSmooth := hSmooth.2.2.1.congr (fun x hx => (hPreEq x.1 hx.1 x.2).symm)
  have hLead := seed d hrSeed hGenSmooth hPreSmooth (hCoeff.1.congr hGenEq)
    (hCoeff.2.1.congr hPreEq) (fun i _ t => hSwitch i t)
  have hLin (m : ℕ) (hm : m + 1 ≤ H) := by
    have hRelayPower : max (6 * E) (c.radiusExponent + 2 * E) = eRelay := by simp [eRelay, haEq]
    let B := Krelay m * D ^ max (6 * E) (c.radiusExponent + 2 * E)
    have hB : 0 ≤ B := mul_nonneg (hKrelay m) (pow_nonneg hD₀ _)
    have hCap : WaveRelayTimeCoefficients.terminalWaveRelayTimeOrderCost m * B ^ 2 ≤ K H * L := by
      have hb : 2 * eRelay ≤ e := by dsimp only [e]; omega
      calc
        _ = Klin m * D ^ (2 * eRelay) := by
          rw [show B = Krelay m * D ^ eRelay by simp [B, hRelayPower], mul_pow, ← pow_mul, Nat.mul_comm eRelay 2]
          unfold Klin
          ring
        _ ≤ _ := hFit 6 (by omega) hb
    exact cfg.selectedLinearTimeEstimates d.leadingRelayData d.parent.deformationOn.flow
      d.parent.smooth_velocity (fun t _ => tip.parent.periodic_velocity t) d.radius d.width
      d.regularity.envelope_pos.ne' (q+1) m hf tip.next_activation_nonnegative d.regularity.start_lt_end.le
      d.centerWeight d.centerWeight_continuous d.centerWeight_pos R (hRelay m) hB hCap
  let rowCap (m : ℕ) := terminalLabelTimeSeminormCost C (q+1) m * D ^ (c.radiusExponent + E)
  apply c.scheduledMixedProfileBounds_of_rows j (hK H) (one_le_pow₀ hD) hSmall rowCap
  · intro m _ i
    exact (hSources m).1 i
  · intro m hm
    have he : a+E ≤ e := by dsimp only [e]; omega
    calc
      _ = Kslow m * D ^ (a+E) := by unfold Kslow rowCap; rw [haEq]; ring
      _ ≤ _ := hFit 0 (by omega) he
  · intro m hm
    have he : E ≤ e := by dsimp only [e]; omega
    calc
      _ ≤ (2 * Q²(m)) * (terminalLabelTimeSeminormCost C (q+1) m * D ^ E * freq ^ (3/2:ℝ)) :=
        mul_le_mul_of_nonneg_left (hSources m).2.1 (by positivity)
      _ = (Kfast m * D ^ E) * freq ^ (3/2:ℝ) := by unfold Kfast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hFit 1 (by omega) he) (Real.rpow_nonneg hf.le _)
  · intro m hm
    have he : E ≤ e := by dsimp only [e]; omega
    rw [show hierarchyMeanExponent 2 = (-5/2:ℝ) by norm_num [hierarchyMeanExponent]]
    simpa only [Nat.add_sub_cancel] using (hSources m).2.2.trans
      (mul_le_mul_of_nonneg_right (hFit 2 (by omega) he) (Real.rpow_nonneg hf.le _))
  · intro m hm
    have he : eSeed ≤ e := by dsimp only [e]; omega
    rw [show hierarchyOscExponent 1 = (-5/4:ℝ) by norm_num [hierarchyOscExponent]]
    exact (hLead m).1.trans (mul_le_mul_of_nonneg_right (hFit 5 hm he) (Real.rpow_nonneg hf.le _))
  · intro m hm
    have he : eSeed ≤ e := by dsimp only [e]; omega
    exact (hLead m).2.trans (mul_le_mul_of_nonneg_right (hFit 5 hm he) (Real.rpow_nonneg hf.le _))
  · intro m hm f hf'
    have he : eMean+a ≤ e := by dsimp only [e]; omega
    have hcap : Kmean m * D ^ (eMean+c.radiusExponent) ≤ K H * L := by
      rw [haEq]
      exact hFit 3 (by omega) he
    rw [Nat.add_sub_cancel]
    exact (hMean m f hf').trans (mul_le_mul_of_nonneg_right hcap
      (apply_nonneg (terminalProfileTimeNorm (E := Vec3) c j q (m+1)) f))
  · intro m hm i hi
    have he : eOsc ≤ e := by dsimp only [e]; omega
    exact (hOsc m i hi).trans (mul_le_mul_of_nonneg_right (hFit 4 hm he)
      ((terminalMeasuredLevels c j (q+1)).nonneg m i).1)
  · intro m hm v hv
    rw [Real.rpow_neg_one]
    exact (hLin m hm).1 v hv
  · intro m hm i hi
    rw [Real.rpow_neg_one]
    exact (hLin m hm).2 i hi

end

end TorusEuler.ScheduledEulerConstruction
