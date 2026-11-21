import TorusEuler.TerminalHierarchySourceTime
import TorusEuler.HierarchySelectedLinearEstimates

/-! The actual selected hierarchy estimates in the factorial time norms. -/

open Set
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData

noncomputable section

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {p : Pressure}
  {hT : 0 < T} {d : ParentGeometry hT U X k} {P : ℕ}

local notation "I" => Icc (0 : ℝ) T
local notation "J" => Set.prod I (univ : Set Vec3)
local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ
local notation "Q²(" n ")" => hierarchyQuadraticConstant (Fin 4) n ^ (2 : ℕ)

set_option maxHeartbeats 4300000 in
/-- The actual retained and omitted profiles satisfy the spatial hierarchy
induction in mixed-time norms. The parent residual is used only in the
lower-order mean force row. -/
theorem selectedTimeHierarchyBounds (b : PhysicalApproximationData d p P) (lead : LeadingRelayData b)
    {H n : ℕ} (q : ℕ) (hP : 2 ≤ P) (hReserve : n + 3 * P ≤ H)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t))
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) {S : Set Vec3} (hS : IsClosed S)
    (inactive : b.leading.Inactive t₀ S)
    (ell h : ℝ) (hell : ell ≠ 0) (hh : h ≠ 0) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγle : ∀ t ∈ Icc t₀ T, γ t ≤ 1) {freq L K : ℝ}
    (hf : 1 ≤ freq) (hL : 1 ≤ L) (hK : 1 ≤ K) (hsmall : L ^ 6 * freq ^ (-1 / 12 : ℝ) ≤ 1)
    (rowCap : ℕ → ℝ)
    (hrow : ∀ n, n + 1 ≤ H → ∀ i : Fin 3, timeJetSeminorm hT q
      (unweightedSeminorm False ell h n hT) (scaledCoframeRowProfile ell d.inverse i) ≤ rowCap n)
    (hRowCap : ∀ n, n + 1 ≤ H → 2 * (3 * Q²(n) * rowCap n) ≤ K * L)
    (hFastCap : ∀ n, n + 1 ≤ H →
      (2 * Q²(n)) * timeJetSeminorm hT q (unweightedSeminorm False ell h n hT)
        (scaledPhaseCoefficientProfile h d.covector) ≤ K * L * freq ^ (3 / 2 : ℝ)) :
    let U₀ : ℕ → Seminorm ℝ VP := fun n => timeJetSeminorm hT q (unweightedSeminorm False ell h n hT)
    let Uforce : ℕ → Seminorm ℝ VP := fun n => timeJetSeminorm hT (q-1) (unweightedSeminorm False ell h n hT)
    let W : ℕ → Seminorm ℝ VP := fun n =>
      timeJetSeminorm hT q (amplitudeSeminorm False ell h n hT ht₀ htT γ hγ hpos)
    let Q : ℕ → Seminorm ℝ SP := fun n =>
      timeJetSeminorm hT q (amplitudeSeminorm False ell h n hT ht₀ htT γ hγ hpos)
    let s := HierarchyMeasuredLevels.ofProfilesWithMeanForce b.operators b.profiles P b.leading.completionSwitch
      b.parentResidual freq (zero_le_one.trans hf) U₀ Uforce W Q
    (∀ n, n + 1 ≤ H → Uforce n b.parentResidual ≤ K * L * freq ^ hierarchyMeanExponent 2) →
    (∀ n ≤ H, W n b.leading.output.V + freq * Q n b.leading.output.p ≤ K * L * freq ^ hierarchyOscExponent 1) →
    (∀ n, n+1 ≤ H → ∀ f hf', U₀ n (b.solvers.solveMean f hf').val.B ≤ K * L * Uforce (n+1) f) →
    (∀ n ≤ H, ∀ i ∈ Finset.Icc 2 P, s.osc n i ≤ K * L * s.oscSource n i) →
    (∀ n, n+1 ≤ H → ∀ v, b.operators.average v = 0 →
      W n (b.solvers.complete v) ≤ K * L * freq ^ (-1 : ℝ) * W (n+1) v) →
    (∀ n, n+1 ≤ H → ∀ i ∈ Finset.Icc 2 (P+1), W n (b.operators.relayAtLevel b.profiles
      b.leading.completionSwitch i) ≤ K * L * (freq ^ (-1 : ℝ) *
        (s.osc (n+1) (i-1) + s.oscSource (n+1) (i-1)))) →
    let C := hierarchyLevelConstant P K P
    let count := ((Finset.Icc 1 P).card : ℝ)
    let V := b.profiles.velocity P
    let avg := b.operators.average V
    HierarchyNormRecurrence s freq L K P H (some L) ∧
    (∀ m ≤ n + 1, ∀ i ∈ Finset.Icc 1 P, HierarchyLevelBound s freq L C m i) ∧
    W n (V - avg) ≤ 2 * count * C * L ^ 2 * freq ^ (-5 / 4 : ℝ) ∧
    U₀ n avg ≤ count * C * L ^ 6 * freq ^ (-5 / 2 : ℝ) ∧
    U₀ n (b.operators.remainder b.profiles P) ≤ 2 * K * (C + 1) ^ 2 *
      (1 + ((hierarchyTailPairs P 0).card : ℝ) + 2 * ((hierarchyTailPairs P 1).card : ℝ)) *
        freq ^ hierarchyOscExponent (P+1) := by
  intro U₀ Uforce W Q s hResidual hSeed hMean hOsc hComplete hRelay C count V avg
  have hP₁ : 1 ≤ P := by omega
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hC₀ : 0 ≤ C := zero_le_one.trans (hierarchyLevelConstant_one_le hK₀ P)
  have hn : n + 1 ≤ H := by omega
  have hPnext : P + 1 ∈ Finset.Icc 2 (P + 1) := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  obtain ⟨hsupport, _, _⟩ := physicalConstruct_support_and_tail_on_inactive (τ := t₀)
    hT b.time_le_one hS d.inverse d.strain d.covector d.mean d.oscillation hP₁ b.leading.completionSwitch
    b.parentResidual b.parentResidual_average b.leading.output inactive.velocity inactive.pressure inactive.completionSwitch
  have hVzero (i : ℕ) (t : ℝ) (ht : t ∈ I) (hl : t < t₀) (x : Vec3 × ℝ) :
      (b.profiles.V i).val.val.val (t,x) = 0 :=
    (hsupport i).1 (x := (t,x)) ⟨⟨ht,mem_univ _⟩, Or.inl hl⟩
  have hCzero (i : ℕ) (t : ℝ) (ht : t ∈ I) (hl : t < t₀) (x : Vec3 × ℝ) :
      (b.profiles.C i).val.val.val (t,x) = 0 :=
    (hsupport i).2.1 (x := (t,x)) ⟨⟨ht,mem_univ _⟩, Or.inl hl⟩
  have hTerms := actualMixedMeasuredLevels_sourceTermBounds hT q d.inverse d.strain d.covector b.profiles P H
    b.leading.completionSwitch b.parentResidual (zero_le_one.trans hf) ell h hell hh ht₀ htT γ hγ hpos hγle
    d.mean.inverse_independent hVzero hCzero rowCap hrow hRowCap hFastCap
    (b.solvers.construct_average_B P b.leading.completionSwitch b.parentResidual b.parentResidual_average b.leading.output)
    (fun i hi => b.average_selectedSourceBeforeMean_eq hX hU hper lead.pressure_mean lead.completion_mean hP₁
      (Finset.mem_Icc.mp hi).2)
    (fun i hi => b.average_selectedRelay_eq_zero lead.pressure_mean lead.completion_mean hi)
    hResidual (fun j hj i hi => hRelay j hj i (Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans (Nat.le_succ P)⟩))
  have hRec : HierarchyNormRecurrence s freq L K P H (some L) :=
    b.solvers.construct_normRecurrence_withMeanForce hP₁ b.leading.completionSwitch b.parentResidual
      b.parentResidual_average b.leading.output (zero_le_one.trans hf) (zero_le_one.trans hL) hK₀ U₀ Uforce W Q
      (fun i j => slowLabelDivergenceProduct hT d.inverse (b.profiles.V i) (b.profiles.Y j))
      hSeed hMean hComplete hOsc hTerms
  have hLevels (m : ℕ) (hm : m ≤ n + 1) (i : ℕ) (hi : i ∈ Finset.Icc 1 P) :
      HierarchyLevelBound s freq L C m i := by
    obtain ⟨hmin,hmax⟩ := Finset.mem_Icc.mp hi
    have hResidualLoss : hierarchyParentResidualConstant K (some L) ≤ K * L ^ 5 := by
      change K * L ≤ K * L ^ 5
      exact mul_le_mul_of_nonneg_left (le_self_pow₀ hL (by decide)) hK₀
    exact (hierarchy_level_bounds_withResidualLoss hRec hf hL hK hResidualLoss hsmall i hmin hmax m
      (by omega)).mono hf hL (hierarchyLevelConstant_monotone hK₀ hmax)
  have hSums := b.solvers.velocity_sums_withMeanForce b.leading.completionSwitch b.parentResidual
    b.parentResidual_average b.leading.output hf hL hC₀ U₀ Uforce W Q n (hLevels n (Nat.le_succ n))
  let R := b.operators.material (b.profiles.C P) + b.operators.labelGrad (b.profiles.p P)
  have hRzero (t : ℝ) (ht : t ∈ I) (ht' : t < t₀) (x : Vec3 × ℝ) :
      R.val.val.val (t,x) = 0 := by
    let laws := inactiveLaws (τ := t₀) hT hS d.inverse d.strain d.covector d.mean.inverse_independent
    let E₀ := inactiveSubmodule T k Vec3 t₀ S
    have hRC : b.operators.material (b.profiles.C P) ∈ E₀ :=
      laws.material (mem_inactiveSubmodule.mpr (hsupport P).2.1)
    have hRp : b.operators.labelGrad (b.profiles.p P) ∈ E₀ :=
      laws.labelGrad (mem_inactiveSubmodule.mpr (hsupport P).2.2)
    exact (mem_inactiveSubmodule.mp (E₀.add_mem hRC hRp)) ⟨⟨ht, mem_univ _⟩, Or.inl ht'⟩
  have hFinal : W n R ≤ K * L * (freq ^ (-1 : ℝ) * (s.osc (n+1) P + s.oscSource (n+1) P)) := by
    have he : P + 1 ≠ 2 := by omega
    simpa only [HierarchyOperators.relayAtLevel, he, ite_false, Nat.add_sub_cancel, sub_zero, R]
      using hRelay n hn (P+1) hPnext
  have hNlin := actualMixedMeasuredLevels_tailNonlinearBounds hT q n d.inverse d.strain d.covector
    b.profiles P b.leading.completionSwitch b.parentResidual (zero_le_one.trans hf) ell h hell hh ht₀ htT
    γ hγ hpos hγle hVzero hCzero (hrow n hn) (hRowCap n hn) (hFastCap n hn)
  refine ⟨hRec, hLevels, hSums.1, hSums.2,
    b.solvers.remainder_withMeanForce hP₁ b.leading.completionSwitch b.parentResidual b.parentResidual_average
      b.leading.output hf hL hK₀ hC₀ hsmall U₀ Uforce W Q n ?_ ?_ (hLevels (n+1) le_rfl) ?_
      hNlin.1 hNlin.2.1 hNlin.2.2⟩
  · intro f
    exact timeJetSeminorm_mono_seminorm hT q
      (Seminorm.le_def.mpr (unweightedSeminorm_mono_order False ell h (Nat.le_succ n) hT)) f
  · intro f
    exact timeJetSeminorm_mono_seminorm hT q
      (Seminorm.le_def.mpr (amplitudeSeminorm_mono_order False ell h (Nat.le_succ n) hT ht₀ htT γ hγ hpos)) f
  · change U₀ n R ≤ K * L * freq ^ (-1 : ℝ) * (s.osc (n+1) P + s.oscSource (n+1) P)
    rw [mul_assoc (K * L)]
    exact (timeJetSeminorm_le_amplitude_of_inactive hT q False ell h n ht₀ htT γ hγ hpos hγle R hRzero).trans hFinal

end

end TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData
