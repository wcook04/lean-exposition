import TorusEuler.HierarchyPhysicalApproximation
import TorusEuler.HierarchyGraphReadoutBounds

/-! The exact central error after removing the leading rank-one wave. -/

open Set
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData

noncomputable section

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {p : Pressure}
  {hT : 0 < T} {d : ParentGeometry hT U X k} {P : ℕ}

local notation "VP" => HierarchyTwistedProfile T k Vec3

/-- The remainder in the central derivative estimate is the exact
oscillatory profile minus the prescribed leading level. -/
theorem oscillationRemainder_eq_centeredGraph (b : PhysicalApproximationData d p P) (hP : 1 ≤ P) :
    b.oscillationRemainder = graphRead (fun t => X t 0)
      (b.profiles.velocity P - b.operators.average (b.profiles.velocity P) - b.profiles.V 1) := by
  have hv : b.profiles.V 1 = b.leading.output.V :=
    (b.solvers.construct_leading P b.leading.completionSwitch b.parentResidual
      b.parentResidual_average b.leading.output).1
  funext t x
  rw [hv]
  change b.oscillationRemainder t x = b.oscillation t x - b.leadingVelocity t x
  have h : b.oscillation t x = b.leadingVelocity t x + b.oscillationRemainder t x :=
    congrFun (congrFun (b.oscillation_eq_leading_add_remainder hP) t) x
  rw [h]
  abel

set_option maxHeartbeats 2100000 in
/-- The actual central derivative of all terms beyond the leading wave
is bounded by the order-one hierarchy norms on the same parent graph. -/
theorem norm_centralRemainder_le (b : PhysicalApproximationData d p P) (hP : 1 ≤ P)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγle : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    {ℓ h D freq L C₁ C₂ : ℝ} {a e₁ e₂ : ℕ}
    {t : ℝ} (ht : t ∈ Icc t₀ T) (hℓ : 0 < ℓ) (hh : 0 < h) (hD : 1 ≤ D) (hf : 1 ≤ freq)
    (hL : 1 ≤ L) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hLabel : ℓ⁻¹ ≤ D ^ a) (hWidth : h = freq ^ (-1 / 2 : ℝ)) (hCarrier : ‖k‖ ≤ D * freq)
    (hA : ContDiff ℝ ∞ (X t 0)) {B : Vec3 → Vec3 →L[ℝ] Vec3}
    (hB : ∀ x, B (X t 0 x) = fderiv ℝ (X t 0) x) (hBreg : ContDiff ℝ ∞ B)
    (hcoeff : ∀ j ≤ 1, ∀ x, ℓ ^ j * ‖iteratedFDeriv ℝ j B x‖ ≤ L * D)
    (hOsc : amplitudeSeminorm False ℓ h 1 hT ht₀ htT γ hγ hpos
      (b.profiles.velocity P - b.operators.average (b.profiles.velocity P) - b.profiles.V 1) ≤
      C₁ * D ^ e₁ * freq ^ (-23 / 12 : ℝ))
    (hMean : unweightedSeminorm False ℓ h 1 hT (b.operators.average (b.profiles.velocity P)) ≤
      C₂ * D ^ e₂ * freq ^ (-5 / 2 : ℝ)) :
    ‖fderiv ℝ (b.oscillationRemainder t) 0‖ + ‖fderiv ℝ (b.meanCorrection t) 0‖ ≤
      (48 * L * C₁ * D ^ (max a 1 + 1 + e₁) + 24 * L * C₂ * D ^ (a + 1 + e₂)) *
        freq ^ (-5 / 12 : ℝ) := by
  let osc := b.profiles.velocity P - b.operators.average (b.profiles.velocity P) - b.profiles.V 1
  let mean := b.operators.average (b.profiles.velocity P)
  have hphase : HierarchyPeriodicProfile.PhaseIndependent mean.val.val :=
    (average_is_mean hT d.inverse d.strain d.covector (b.profiles.velocity P)).1
  have htime : t ∈ Icc 0 T := ⟨ht₀.trans ht.1,ht.2⟩
  have ho := graphRead_frequency_jetBound_weighted (A := fun r => X r 0) (n := 1) (a := a) (p := e₁)
    hT ht₀ htT γ hγ hpos osc
    ht hℓ hh hD hf hL hC₁ hLabel hWidth hCarrier hA hB hBreg hcoeff hOsc
  have hm := graphRead_frequency_jetBound_mean (A := fun r => X r 0) (n := 1) (a := a) (p := e₂) hT mean hphase
    htime hℓ hD (zero_lt_one.trans_le hf) hL hC₂ hLabel hA hB hBreg hcoeff hMean
  have hosc := ho 1 le_rfl (0 : Vec3)
  have hmean := hm 1 le_rfl (0 : Vec3)
  rw [norm_iteratedFDeriv_one] at hosc hmean
  have hOscGraph : b.oscillationRemainder t = graphRead (fun r => X r 0) osc t :=
    congrFun (b.oscillationRemainder_eq_centeredGraph hP) t
  have hMeanGraph : b.meanCorrection t = graphRead (fun r => X r 0) mean t := rfl
  rw [hOscGraph, hMeanGraph]
  have hosc' : ‖fderiv ℝ (graphRead (fun r => X r 0) osc t) 0‖ ≤
      48 * L * C₁ * D ^ (max a 1 + 1 + e₁) * freq ^ (-5 / 12 : ℝ) := by
    norm_num only [pow_one, Nat.cast_one, Nat.mul_one] at hosc
    refine hosc.trans ?_
    calc
      _ ≤ 6 * (2 * L) * (4 * C₁) * D ^ (max a 1 + 1 + e₁) *
          (1 * freq ^ (-(5 / 12) : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hγle t ht) (by positivity)) (by positivity)
      _ = _ := by ring
  have hmean' : ‖fderiv ℝ (graphRead (fun r => X r 0) mean t) 0‖ ≤
      24 * L * C₂ * D ^ (a + 1 + e₂) * freq ^ (-5 / 12 : ℝ) := by
    norm_num only [pow_one, Nat.mul_one] at hmean
    have hfreq : freq ^ (-(5 / 2) : ℝ) ≤ freq ^ (-5 / 12 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hf (by norm_num)
    refine hmean.trans ?_
    calc
      _ ≤ (6 * L) * (4 * C₂) * D ^ (a + 1 + e₂) * freq ^ (-5 / 12 : ℝ) :=
        mul_le_mul_of_nonneg_left hfreq (by positivity)
      _ = _ := by ring
  exact (add_le_add hosc' hmean').trans_eq (by ring)

end

end TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData
