import TorusEuler.TerminalTransverseTime
import TorusEuler.HierarchyPhysicalApproximation

/-! Mixed time estimates on the actual retained transverse profiles. -/

open Set
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T D : ℝ} {k : Vec3}

/-- Replacing the analytic bounds by old-parent powers leaves one power
depending only on the time order and the input powers. -/
theorem transverseTimeCost_le_parentPower {C₀ C A₀ A : ℝ} {a b n q : ℕ}
    (hT : 0 ≤ T) (hT₁ : T ≤ 1) (hD : 1 ≤ D) (hC₀ : 0 ≤ C₀) (hC : 0 ≤ C)
    (h₀ : C₀ ≤ A₀ * D ^ a) (h₁ : C ≤ A * D ^ b) :
    transverseTimeCost T n q C₀ C ≤ transverseTimeCost 1 n q A₀ A * D ^ (a + b * (q + 1)) := by
  let K := terminalApplyFieldCost Vec3 Vec3 n
  let L := terminalApplyFieldCost Vec3 ℝ n
  have hK : 0 ≤ K := terminalApplyFieldCost_nonneg Vec3 Vec3 n
  have hL : 0 ≤ L := terminalApplyFieldCost_nonneg Vec3 ℝ n
  have hA₀ : 0 ≤ A₀ := nonneg_of_mul_nonneg_left (hC₀.trans h₀) (by positivity)
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left (hC.trans h₁) (by positivity)
  have haD : 1 ≤ D ^ a := one_le_pow₀ hD
  have hbD : 1 ≤ D ^ b := one_le_pow₀ hD
  have hw₀ : C₀ + 1 ≤ (A₀ + 1) * D ^ a := by
    rw [add_mul, one_mul]
    exact add_le_add h₀ haD
  have hwL : 1 + 2 * L * C ≤ (1 + 2 * L * A) * D ^ b := by
    rw [add_mul, one_mul, mul_assoc (2 * L)]
    exact add_le_add hbD (mul_le_mul_of_nonneg_left h₁ (by positivity))
  have hwK : 1 + T * K * C ≤ (1 + K * A) * D ^ b := by
    rw [add_mul, one_mul, mul_assoc K]
    refine add_le_add hbD ((mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left hK hT₁) hC).trans ?_)
    exact mul_le_mul_of_nonneg_left h₁ hK
  have htail : 2 * L * C ≤ 2 * L * A * D ^ (a + b * (q + 1)) := by
    rw [mul_assoc (2 * L)]
    have hb : b ≤ a + b * (q + 1) := by rw [Nat.mul_succ]; omega
    exact mul_le_mul_of_nonneg_left
      (h₁.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hb) hA))
      (by positivity)
  unfold transverseTimeCost
  change (1 + 2 * L * C) * ((1 + T * K * C) ^ q * (C₀ + 1)) + 2 * L * C ≤ _
  calc
    _ ≤ ((1 + 2 * L * A) * D ^ b) * ((((1 + K * A) * D ^ b) ^ q) * ((A₀ + 1) * D ^ a)) +
        2 * L * A * D ^ (a + b * (q + 1)) := by
      refine add_le_add (mul_le_mul hwL (mul_le_mul (pow_le_pow_left₀ (by positivity) hwK q) hw₀
        (by positivity) (by positivity)) (by positivity) (by positivity)) htail
    _ = _ := by
      rw [mul_pow, ← pow_mul, Nat.mul_succ, pow_add D a, pow_add D (b*q)]
      change _ = ((1 + 2 * L * A) * ((1 + 1 * K * A) ^ q * (A₀ + 1)) + 2 * L * A) *
        (D ^ a * (D ^ (b * q) * D ^ b))
      ring

section Actual

variable {U : Velocity} {X : ℝ → Velocity} {hT : 0 < T}
  {d : ParentGeometry hT U X k} {p : Pressure} {P i : ℕ}

local notation "VQ" => HierarchyTwistedProfile T k Vec3

/-- The actual source selected by the finite recurrence at a transverse
correction level. -/
abbrev PhysicalApproximationData.selectedTransverseForce (cfg : PhysicalApproximationData d p P)
    (i : ℕ) : VQ :=
  let H := cfg.operators.sourceBeforeMean cfg.profiles P cfg.leading.completionSwitch i;
  -(H - cfg.operators.average H) -
    hierarchyAdvectionAtLevel P 1 i (cfg.operators.meanPhaseProduct cfg.profiles)

/-- The time inverse applies to the exact forcing and both exact retained
profiles of a selected hierarchy, with the same level-zero spatial estimate. -/
theorem PhysicalApproximationData.selectedTransverse_timeJet_le (cfg : PhysicalApproximationData d p P)
    (hi : i ∈ Finset.Icc 2 P)
    {t₀ freq : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (hf : 0 < freq)
    {γ : ℝ → ℝ} (hγ : ContinuousOn γ (Icc t₀ T)) (hγ₀ : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (ℓ h : ℝ) (n q : ℕ) {C₀ C : ℝ} (hC₀ : 0 ≤ C₀) (hC : 0 ≤ C) :
    let W := amplitudeSeminorm (E := Vec3) (k := k) False ℓ h n hT ht₀ htT γ hγ hγ₀
    let Q := amplitudeSeminorm (E := ℝ) (k := k) False ℓ h n hT ht₀ htT γ hγ hγ₀
    let N := unweightedSeminorm (E := Vec3 →L[ℝ] Vec3) (k := k) False ℓ h n hT
    let NP := unweightedSeminorm (E := Vec3 →L[ℝ] ℝ) (k := k) False ℓ h n hT
    let coeff := d.oscillation.timeCoefficients freq hf.ne'
    W (cfg.profiles.V i) ≤ C₀ * W (cfg.selectedTransverseForce i) →
    timeJetSeminorm hT q N coeff.velocity ≤ C →
    timeJetSeminorm hT q N coeff.source ≤ C →
    timeJetSeminorm hT q NP coeff.pressureVelocity ≤ C →
    timeJetSeminorm hT q NP coeff.pressureSource ≤ C →
    timeJetSeminorm hT q W (cfg.profiles.V i) + freq * timeJetSeminorm hT q Q (cfg.profiles.p i) ≤
      transverseTimeCost T n q C₀ C * timeJetSeminorm hT q W (cfg.selectedTransverseForce i) := by
  dsimp only
  intro hbase hA hB hP hQ
  obtain ⟨hF, hV, hp⟩ := cfg.solvers.construct_transverse_selected hi cfg.leading.completionSwitch
    cfg.parentResidual cfg.parentResidual_average cfg.leading.output
  let r := solveTransverse hT d.inverse d.strain d.covector d.oscillation (cfg.selectedTransverseForce i) hF
  have hVEq : cfg.profiles.V i = r.output.V := hV
  have hpEq : cfg.profiles.p i = r.output.p := hp
  rw [hVEq] at hbase
  rw [hVEq, hpEq]
  exact r.timeJet_bound hT ht₀ htT hγ hγ₀ ℓ h n q hf
    (d.oscillation.timeCoefficients freq hf.ne') hC₀ hC hbase hA hB hP hQ

/-- The undifferentiated bound can be supplied as the ordinary measured
oscillatory row, with its carrier-normalized pressure included. -/
theorem PhysicalApproximationData.selectedTransverse_timeJet_le_of_spatialRow
    (cfg : PhysicalApproximationData d p P) (hi : i ∈ Finset.Icc 2 P)
    {t₀ freq : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (hf : 0 < freq)
    {γ : ℝ → ℝ} (hγ : ContinuousOn γ (Icc t₀ T)) (hγ₀ : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (ℓ h : ℝ) (n q : ℕ) {C₀ C : ℝ} (hC₀ : 0 ≤ C₀) (hC : 0 ≤ C) :
    let W := amplitudeSeminorm (E := Vec3) (k := k) False ℓ h n hT ht₀ htT γ hγ hγ₀
    let Q := amplitudeSeminorm (E := ℝ) (k := k) False ℓ h n hT ht₀ htT γ hγ hγ₀
    let N := unweightedSeminorm (E := Vec3 →L[ℝ] Vec3) (k := k) False ℓ h n hT
    let NP := unweightedSeminorm (E := Vec3 →L[ℝ] ℝ) (k := k) False ℓ h n hT
    let coeff := d.oscillation.timeCoefficients freq hf.ne'
    let spatial := actualMeasuredLevels cfg.operators cfg.profiles P cfg.leading.completionSwitch
      cfg.parentResidual freq hf.le ℓ h hT ht₀ htT γ hγ hγ₀
    spatial.osc n i ≤ C₀ * spatial.oscSource n i →
    timeJetSeminorm hT q N coeff.velocity ≤ C →
    timeJetSeminorm hT q N coeff.source ≤ C →
    timeJetSeminorm hT q NP coeff.pressureVelocity ≤ C →
    timeJetSeminorm hT q NP coeff.pressureSource ≤ C →
    timeJetSeminorm hT q W (cfg.profiles.V i) + freq * timeJetSeminorm hT q Q (cfg.profiles.p i) ≤
      transverseTimeCost T n q C₀ C * timeJetSeminorm hT q W (cfg.selectedTransverseForce i) := by
  dsimp only
  intro hspatial
  let W := amplitudeSeminorm (E := Vec3) (k := k) False ℓ h n hT ht₀ htT γ hγ hγ₀
  let Q := amplitudeSeminorm (E := ℝ) (k := k) False ℓ h n hT ht₀ htT γ hγ hγ₀
  have hi₁ : i ≠ 1 := by have := (Finset.mem_Icc.mp hi).1; omega
  change W (cfg.profiles.V i) + freq * Q (cfg.profiles.p i) ≤
    C₀ * (if i = 1 then 0 else W (cfg.selectedTransverseForce i)) at hspatial
  rw [ite_eq_right hi₁] at hspatial
  exact cfg.selectedTransverse_timeJet_le hi ht₀ htT hf hγ hγ₀ ℓ h n q hC₀ hC
    ((le_add_of_nonneg_right (mul_nonneg hf.le (apply_nonneg Q _))).trans hspatial)

end Actual

end

end TorusEuler.HierarchyTwistedProfile
