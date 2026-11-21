import TorusEuler.TerminalHierarchyRelayTime

/-! The seven actual normalized coefficient rows of the mixed-time relay. -/

open Set Finset
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)
local notation "VProw" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] ℝ)
local notation "SProw" => HierarchyTwistedProfile T k (ℝ →L[ℝ] Vec3)

/-- Every row evaluates to its canonical value at the normalized covector.
The coefficient profiles are read at phase zero. -/
structure WaveRelayTimeCoefficients (G M : MP) (κ : VP) (ell freq : ℝ) where
  potential : MP
  potentialTime : MP
  pressureAmplitude : VProw
  pressureSource : VProw
  curl : Fin 3 → MP
  material : Fin 3 → MP
  gradient : Fin 3 → SProw
  potential_eq : ∀ t ∈ Icc 0 T, ∀ a s, potential.val.val.val (t,a,s) =
    hierarchyRelayPotentialCoefficient (freq⁻¹ • κ.val.val.val (t,a,0))
  potentialTime_eq : ∀ t ∈ Icc 0 T, ∀ a s, potentialTime.val.val.val (t,a,s) =
    hierarchyRelayTimeAmplitudeCoefficient (M.val.val.val (t,a,0)) (freq⁻¹ • κ.val.val.val (t,a,0))
  pressureAmplitude_eq : ∀ t ∈ Icc 0 T, ∀ a s, pressureAmplitude.val.val.val (t,a,s) =
    hierarchyRelayPressureAmplitudeCoefficient (M.val.val.val (t,a,0)) (freq⁻¹ • κ.val.val.val (t,a,0))
  pressureSource_eq : ∀ t ∈ Icc 0 T, ∀ a s, pressureSource.val.val.val (t,a,s) =
    hierarchyRelayPressureSourceCoefficient (freq⁻¹ • κ.val.val.val (t,a,0))
  curl_eq : ∀ i t, t ∈ Icc 0 T → ∀ a s, (curl i).val.val.val (t,a,s) =
    hierarchyRelayCurlRow ell (G.val.val.val (t,a,0)) i
  material_eq : ∀ i t, t ∈ Icc 0 T → ∀ a s, (material i).val.val.val (t,a,s) =
    hierarchyRelayMaterialRow ell (G.val.val.val (t,a,0)) (M.val.val.val (t,a,0)) i
  gradient_eq : ∀ i t, t ∈ Icc 0 T → ∀ a s, (gradient i).val.val.val (t,a,s) =
    hierarchyRelayPressureRow ell (G.val.val.val (t,a,0)) i

local notation "J[" hT "," q "," ell "," h "," n "]" =>
  timeJetSeminorm hT q (unweightedSeminorm False ell h n hT)

/-- A single finite-order constant bounds the normalized coefficients.
The inner primitive coefficients are used through one extra label order. -/
structure WaveRelayTimeCoefficientBudget {G M : MP} {κ : VP} {ell freq : ℝ}
    (R : WaveRelayTimeCoefficients G M κ ell freq) (hT : 0 < T)
    (h : ℝ) (q n : ℕ) (K : ℝ) : Prop where
  potential : J[hT,q,ell,h,n+1] R.potential ≤ K
  potentialTime : J[hT,q,ell,h,n+1] R.potentialTime ≤ K
  pressureAmplitude : J[hT,q,ell,h,n+1] R.pressureAmplitude ≤ K
  pressureSource : J[hT,q,ell,h,n+1] R.pressureSource ≤ K
  curl : ∀ i, J[hT,q,ell,h,n] (R.curl i) ≤ K
  material : ∀ i, J[hT,q,ell,h,n] (R.material i) ≤ K
  gradient : ∀ i, J[hT,q,ell,h,n] (R.gradient i) ≤ K

namespace WaveRelayTimeCoefficients

variable {G M : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)}
  {κ : HierarchyTwistedProfile T k Vec3} {ell freq : ℝ}
  (R : WaveRelayTimeCoefficients G M κ ell freq)

theorem potential_phaseIndependent : HierarchyPeriodicProfile.PhaseIndependent R.potential.val.val :=
  fun x hx s => (R.potential_eq x.1 hx.1 x.2.1 s).trans (R.potential_eq x.1 hx.1 x.2.1 x.2.2).symm

theorem potentialTime_phaseIndependent : HierarchyPeriodicProfile.PhaseIndependent R.potentialTime.val.val :=
  fun x hx s => (R.potentialTime_eq x.1 hx.1 x.2.1 s).trans (R.potentialTime_eq x.1 hx.1 x.2.1 x.2.2).symm

theorem pressureAmplitude_phaseIndependent :
    HierarchyPeriodicProfile.PhaseIndependent R.pressureAmplitude.val.val :=
  fun x hx s => (R.pressureAmplitude_eq x.1 hx.1 x.2.1 s).trans
    (R.pressureAmplitude_eq x.1 hx.1 x.2.1 x.2.2).symm

theorem pressureSource_phaseIndependent : HierarchyPeriodicProfile.PhaseIndependent R.pressureSource.val.val :=
  fun x hx s => (R.pressureSource_eq x.1 hx.1 x.2.1 s).trans
    (R.pressureSource_eq x.1 hx.1 x.2.1 x.2.2).symm

/-- The normalized completion written as its three scaled coordinate terms. -/
def completionProfile (hT : 0 < T) (h : ℝ) (v : VP) (hv : PhaseMeanZero v) : VP :=
  freq⁻¹ • ∑ i : Fin 3,
    relayPrimitiveTerm hT ell h i v hv R.potential R.potential_phaseIndependent (R.curl i)

/-- The normalized relay written in the same coordinate terms as (5.31)–(5.33). -/
def relayProfile (hT : 0 < T) (h : ℝ) (v f : VP) (hv : PhaseMeanZero v) (hf : PhaseMeanZero f) : VP :=
  freq⁻¹ • ∑ i : Fin 3,
    ((relayPrimitiveTerm hT ell h i v hv R.potentialTime R.potentialTime_phaseIndependent (R.curl i) +
      relayPrimitiveTerm hT ell h i f hf R.potential R.potential_phaseIndependent (R.curl i)) +
      relayPrimitiveTerm hT ell h i v hv R.potential R.potential_phaseIndependent (R.material i) +
    (relayPrimitiveTerm hT ell h i v hv R.pressureAmplitude R.pressureAmplitude_phaseIndependent (R.gradient i) +
      relayPrimitiveTerm hT ell h i f hf R.pressureSource R.pressureSource_phaseIndependent (R.gradient i)))

end WaveRelayTimeCoefficients

end

end TorusEuler.HierarchyTwistedProfile
