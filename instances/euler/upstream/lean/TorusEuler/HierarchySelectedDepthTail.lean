import TorusEuler.HierarchyDepthTail
import TorusEuler.HierarchyPhysicalApproximation
import TorusEuler.HierarchySlowInteractionEstimates
import TorusEuler.HierarchyTwistedRelayCoefficientBudget

/-! The unweighted residual tail of the selected finite hierarchy in (5.45). -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)

set_option maxHeartbeats 1800000 in
/-- The omitted fast completion and mean interactions use their exact whole-slab
seminorms. Inactivity transfers the oscillatory factors to the active weighted
seminorm. The advecting mean stays in the whole-slab norm. -/
theorem actualMeasuredLevels_fastTail_terms (hT : 0 < T) (G M : MP) (κ : VP)
    (u : HierarchyProfiles VP SP) (P n : ℕ) (completionSwitch residual : VP)
    {freq L K : ℝ} (hf : 0 ≤ freq) (ℓ h : ℝ) (hh : h ≠ 0)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T))
    (hγpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγle : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hκN : hierarchyQuadraticConstant (Fin 4) n ^ 2 *
      unweightedSeminorm False ℓ h n hT (scaledPhaseCoefficientProfile h κ) ≤
        K * L * freq ^ (3 / 2 : ℝ))
    (i j : ℕ)
    (hCzero : ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ,
      (u.C (i-1)).val.val.val (t,x) = 0)
    (hYzero : ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, (u.Y j).val.val.val (t,x) = 0) :
    let A := twistedHierarchyOperators hT G M κ
    let U := unweightedSeminorm False ℓ h n hT
    let s := actualMeasuredLevels A u P completionSwitch residual freq hf ℓ h hT ht₀ htT
      γ hγ hγpos
    U (A.completionPhaseProduct u (i,j)) ≤ K * L * freq ^ (3 / 2 : ℝ) *
        (s.completion n (i - 1) * s.Y (n + 1) j) ∧
      U (A.meanPhaseProduct u (i,j)) ≤ K * L * freq ^ (3 / 2 : ℝ) *
        (s.mean n i * s.Y (n + 1) j) := by
  intro A U s
  let Q := hierarchyQuadraticConstant (Fin 4) n ^ 2 *
    unweightedSeminorm False ℓ h n hT (scaledPhaseCoefficientProfile h κ)
  let B := K * L * freq ^ (3 / 2 : ℝ)
  have hQ : 0 ≤ Q := mul_nonneg (sq_nonneg _) (apply_nonneg _ _)
  have hB : 0 ≤ B := hQ.trans hκN
  have hC : U (u.C (i - 1)) ≤ s.completion n (i - 1) :=
    unweightedSeminorm_le_amplitudeSeminorm_of_inactive False ℓ h n hT ht₀ htT _
      hγ hγpos hγle _ hCzero
  have hY : unweightedSeminorm False ℓ h (n + 1) hT (u.Y j) ≤ s.Y (n + 1) j :=
    unweightedSeminorm_le_amplitudeSeminorm_of_inactive False ℓ h (n + 1) hT ht₀ htT _
      hγ hγpos hγle _ hYzero
  have hYn : 0 ≤ unweightedSeminorm False ℓ h (n + 1) hT (u.Y j) := apply_nonneg _ _
  have hphase (Z : VP) (z : ℝ) (hz : U Z ≤ z) : U (A.phaseAdv Z (u.Y j)) ≤ B * (z * s.Y (n + 1) j) := by
    have hZn : 0 ≤ U Z := apply_nonneg _ _
    have hprod : U Z * unweightedSeminorm False ℓ h (n + 1) hT (u.Y j) ≤ z * s.Y (n + 1) j :=
      mul_le_mul hz hY hYn (hZn.trans hz)
    calc
      _ ≤ Q * U Z * unweightedSeminorm False ℓ h (n + 1) hT (u.Y j) :=
        unweightedSeminorm_phaseAdv_le ℓ h hh n hT G M κ Z (u.Y j)
      _ = Q * (U Z * unweightedSeminorm False ℓ h (n + 1) hT (u.Y j)) := mul_assoc _ _ _
      _ ≤ B * (z * s.Y (n + 1) j) :=
        (mul_le_mul_of_nonneg_right hκN (mul_nonneg hZn hYn)).trans
          (mul_le_mul_of_nonneg_left hprod hB)
  exact ⟨hphase (u.C (i - 1)) _ hC, hphase (u.B i) _ le_rfl⟩

/-- At the terminal quadratic index, the only possible velocity profile is the
completion from the last retained level. -/
theorem actualMeasuredLevels_tail_last (A : HierarchyOperators VP SP) (u : HierarchyProfiles VP SP)
    (P m : ℕ) (completionSwitch residual : VP) {freq : ℝ} (hf : 0 ≤ freq)
    (ℓ h : ℝ) (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hγpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hVlast : u.V (P + 1) = 0) (hBlast : u.B (P + 1) = 0) :
    let s := actualMeasuredLevels A u P completionSwitch residual freq hf ℓ h hT ht₀ htT γ hγ hγpos
    s.Y m (P + 1) = s.completion m P ∧ s.Z m (P + 1) = s.completion m P ∧ s.mean m (P + 1) = 0 := by
  intro s
  let U : Seminorm ℝ VP := unweightedSeminorm False ℓ h m hT
  let W : Seminorm ℝ VP := amplitudeSeminorm False ℓ h m hT ht₀ htT γ hγ hγpos
  have hY : u.Y (P + 1) = u.C P := by
    simp [HierarchyProfiles.Y, hVlast]
  change W (u.Y (P+1)) = W (u.C P) ∧ W (u.Y (P+1)) + U (u.B (P+1)) = W (u.C P) ∧
    U (u.B (P+1)) = 0
  rw [hY, hBlast, map_zero, add_zero]
  exact ⟨rfl, rfl, rfl⟩

/-- The selected hierarchy has no velocity or mean at index `P + 1`. -/
theorem construct_actualMeasuredLevels_tail_last
    (A : HierarchyOperators VP SP) (S : FiniteHierarchySolvers A) {P : ℕ} (hP : 1 ≤ P)
    (m : ℕ) (completionSwitch residual : VP) (hR : A.average residual = residual)
    (leading : HierarchyTransverseOutput A) {freq : ℝ} (hf : 0 ≤ freq) (ℓ h : ℝ) (hT : 0 < T)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hγpos : ∀ t ∈ Icc t₀ T, 0 < γ t) :
    let u := S.construct P completionSwitch residual hR leading
    let s := actualMeasuredLevels A u P completionSwitch residual freq hf ℓ h hT ht₀ htT γ hγ hγpos
    s.Y m (P + 1) = s.completion m P ∧ s.Z m (P + 1) = s.completion m P ∧ s.mean m (P + 1) = 0 := by
  intro u s
  have hz := S.construct_eq_zero_of_index hP (Or.inr (Nat.lt_succ_self P))
    completionSwitch residual hR leading
  exact actualMeasuredLevels_tail_last A u P m completionSwitch residual hf ℓ h hT ht₀ htT
    γ hγ hγpos hz.1 hz.2.2.1


/-- In the quadratic tail, the unweighted norm of the full velocity at a
given level is bounded by the measured weighted oscillation plus the
unweighted mean. -/
theorem actualMeasuredLevels_unweighted_Z_le (A : HierarchyOperators VP SP)
    (u : HierarchyProfiles VP SP) (P m i : ℕ)
    (completionSwitch residual : VP) {freq : ℝ} (hf : 0 ≤ freq)
    (ℓ h : ℝ) (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hγpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγle : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hYzero : ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, (u.Y i).val.val.val (t,x) = 0) :
    let s := actualMeasuredLevels A u P completionSwitch residual freq hf ℓ h hT ht₀ htT γ hγ hγpos
    unweightedSeminorm False ℓ h m hT (u.Z i) ≤ s.Z m i := by
  intro s
  let U : Seminorm ℝ VP := unweightedSeminorm False ℓ h m hT
  let W : Seminorm ℝ VP := amplitudeSeminorm False ℓ h m hT ht₀ htT γ hγ hγpos
  have hy : U (u.Y i) ≤ W (u.Y i) :=
    unweightedSeminorm_le_amplitudeSeminorm_of_inactive False ℓ h m hT ht₀ htT γ
      hγ hγpos hγle _ hYzero
  change U (u.Y i + u.B i) ≤ W (u.Y i) + U (u.B i)
  exact (map_add_le_add U _ _).trans (add_le_add hy le_rfl)

/-- Whole-slab slow tail advection costs one extra weighted coordinate order.
Both reconstructed profiles can be estimated at the higher order. -/
theorem actualMeasuredLevels_slowTail_term (hT : 0 < T) (G M : MP) (κ : VP)
    (u : HierarchyProfiles VP SP) (P n : ℕ) (completionSwitch residual : VP)
    {freq L K rowCap : ℝ} (hf : 0 ≤ freq) (ℓ h : ℝ) (hℓ : ℓ ≠ 0)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hγpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγle : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hrow : ∀ r : Fin 3,
      unweightedSeminorm False ℓ h n hT (scaledCoframeRowProfile ℓ G r) ≤ rowCap)
    (hRowCap : 3 * hierarchyQuadraticConstant (Fin 4) n ^ 2 * rowCap ≤ K * L)
    (i j : ℕ)
    (hYzero : ∀ p, ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, (u.Y p).val.val.val (t,x) = 0) :
    let A := twistedHierarchyOperators hT G M κ
    let s := actualMeasuredLevels A u P completionSwitch residual freq hf ℓ h hT ht₀ htT γ hγ hγpos
    unweightedSeminorm False ℓ h n hT (A.labelProduct u (i,j)) ≤
      K * L * (s.Z (n + 1) i * s.Z (n + 1) j) := by
  intro A s
  let U (m : ℕ) : Seminorm ℝ VP := unweightedSeminorm False ℓ h m hT
  let B := 3 * hierarchyQuadraticConstant (Fin 4) n ^ 2 * rowCap
  have hrowNonneg : 0 ≤ rowCap := (apply_nonneg _ _).trans (hrow 0)
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hKL : 0 ≤ K * L := hB.trans hRowCap
  have hZ (p : ℕ) : U (n + 1) (u.Z p) ≤ s.Z (n + 1) p :=
    actualMeasuredLevels_unweighted_Z_le A u P (n+1) p completionSwitch residual hf
      ℓ h hT ht₀ htT γ hγ hγpos hγle (hYzero p)
  have hZi : U n (u.Z i) ≤ s.Z (n + 1) i :=
    (unweightedSeminorm_mono_order False ℓ h (Nat.le_succ n) hT (u.Z i)).trans (hZ i)
  have hZi₀ : 0 ≤ U n (u.Z i) := apply_nonneg _ _
  have hZj₀ : 0 ≤ U (n + 1) (u.Z j) := apply_nonneg _ _
  calc
    _ ≤ B * U n (u.Z i) * U (n + 1) (u.Z j) :=
      unweightedSeminorm_labelAdv_le hT G M κ (u.Z i) (u.Z j) ℓ h hℓ n hrow
    _ = B * (U n (u.Z i) * U (n + 1) (u.Z j)) := mul_assoc _ _ _
    _ ≤ K * L * (s.Z (n + 1) i * s.Z (n + 1) j) :=
      (mul_le_mul_of_nonneg_right hRowCap (mul_nonneg hZi₀ hZj₀)).trans
        (mul_le_mul_of_nonneg_left (mul_le_mul hZi (hZ j) hZj₀ (hZi₀.trans hZi)) hKL)


end

end TorusEuler.HierarchyTwistedProfile


namespace TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData

noncomputable section

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {p : Pressure}
  {hT : 0 < T} {d : ParentGeometry hT U X k} {P : ℕ}

local notation "I" => Icc (0 : ℝ) T
local notation "J" => Set.prod I (univ : Set Vec3)
local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ

set_option maxHeartbeats 2200000 in
/-- The final retained oscillation supplies the next linear relay. At depth
at least two this relay has no activation switch and is the exact linear
part of the unweighted tail. -/
theorem amplitudeSeminorm_finalRelay_le (b : PhysicalApproximationData d p P)
    (hP : 2 ≤ P) (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ 2 (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t))
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) {freq KRelay : ℝ} (hfreq : 0 < freq)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hCoeff : WaveRelayCoefficientBudget ℓ h n KRelay
      (fun (t : Icc t₀ T) a => d.inverse.val.val.val (t, a, 0))
      (fun (t : Icc t₀ T) a => d.strain.val.val.val (t, a, 0))
      (fun (t : Icc t₀ T) a => freq⁻¹ • d.covector.val.val.val (t, a, 0))) :
    let s := actualMeasuredLevels b.operators b.profiles P b.leading.completionSwitch b.parentResidual
      freq hfreq.le ℓ h hT ht₀ htT γ hγ hpos
    amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos
      (b.operators.material (b.profiles.C P) + b.operators.labelGrad (b.profiles.p P)) ≤
      waveRelayOrderConstant n * KRelay ^ 2 * freq⁻¹ * (s.osc (n + 1) P + s.oscSource (n + 1) P) := by
  intro s
  let A := b.operators
  let u := b.profiles
  let R := A.material (u.C P) + A.labelGrad (u.p P)
  let H := A.sourceBeforeMean u P b.leading.completionSwitch P
  let F := -(H - A.average H) - hierarchyAdvectionAtLevel P 1 P (A.meanPhaseProduct u)
  let W (m : ℕ) : Seminorm ℝ VP := amplitudeSeminorm False ℓ h m hT ht₀ htT γ hγ hpos
  let Wp (m : ℕ) : Seminorm ℝ SP := amplitudeSeminorm False ℓ h m hT ht₀ htT γ hγ hpos
  have hPMem : P ∈ Finset.Icc 2 P := Finset.mem_Icc.mpr ⟨hP, le_rfl⟩
  have hP₁ : P ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  obtain ⟨hf, hv, hp⟩ := b.solvers.construct_transverse_selected hPMem b.leading.completionSwitch
    b.parentResidual b.parentResidual_average b.leading.output
  let o := (solveTransverse hT d.inverse d.strain d.covector d.oscillation F hf)
  change u.V P = o.output.V at hv
  change u.p P = o.output.p at hp
  have hC : u.C P = complete hT d.inverse d.covector d.oscillation.covector_independent
      d.oscillation.covector_ne_zero (u.V P) :=
    b.solvers.construct_completion hP₁ b.leading.completionSwitch b.parentResidual
      b.parentResidual_average b.leading.output
  obtain ⟨hGdot, hκdot⟩ := transportedWaveRelay_coefficient_timeEquations hT hX hU hper
    d.inverse d.strain d.covector
    (fun t ht a => d.inverse_value (t, a, 0) ⟨ht, mem_univ _⟩)
    (fun t ht a => d.strain_value (t, a, 0) ⟨ht, mem_univ _⟩)
    (fun t ht a => d.covector_value (t, a, 0) ⟨ht, mem_univ _⟩)
  have hMphase : HierarchyPeriodicProfile.PhaseIndependent d.strain.val.val := by
    intro x hx σ
    exact (d.strain_value (x.1, x.2.1, σ) ⟨hx.1, mem_univ _⟩).trans (d.strain_value x hx).symm
  have hEval (t : ℝ) (ht : t ∈ I) (x : Vec3 × ℝ) :
      R.val.val.val (t, x) = waveRelayAt d.inverse d.strain d.covector (u.V P) F t x := by
    change (A.material (u.C P) + A.labelGrad (u.p P)).val.val.val (t, x) = _
    rw [hC, hv, hp]
    exact material_complete_add_labelGrad_apply_relay hT d.inverse d.strain d.covector
      o.output.V F o.output.p d.mean.inverse_independent hMphase d.oscillation.covector_independent
      d.oscillation.covector_ne_zero o.output.average_V hGdot hκdot o.velocity_equation o.pressure_value ht x
  have hVmean : A.average (u.V P) = 0 := hv.symm ▸ o.output.average_V
  have hbase := boundedWeightSeminorm_waveRelay_le_of_eval hT d.inverse d.strain d.covector
    (u.V P) F R ℓ h hℓ n hfreq (Icc_subset_Icc_left ht₀) (fun t => (γ t)⁻¹)
    (inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hpos).choose_spec
    hVmean hf (fun t ht x => hEval t (Icc_subset_Icc_left ht₀ ht) x) hCoeff
  have hNormV : W (n + 1) (u.V P) ≤ s.osc (n + 1) P := by
    change _ ≤ W (n + 1) (u.V P) + freq * Wp (n + 1) (u.p P)
    exact le_add_of_nonneg_right (mul_nonneg hfreq.le (apply_nonneg _ _))
  have hNormF : W (n + 1) F = s.oscSource (n + 1) P := by
    change _ = if P = 1 then 0 else W (n + 1) F
    rw [ite_eq_right (by omega : P ≠ 1)]
  exact hbase.trans (mul_le_mul_of_nonneg_left (add_le_add hNormV hNormF.le)
    (by unfold waveRelayOrderConstant; positivity))

set_option maxHeartbeats 2600000 in
/-- The exact ignored interactions of the selected physical hierarchy satisfy
the whole-slab tail estimate. The final quadratic index is accounted for by
the last retained completion, and the transported switch is outside the tail. -/
theorem unweightedSeminorm_remainder_le (b : PhysicalApproximationData d p P)
    (hP : 2 ≤ P) (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ 2 (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t))
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (hh : h ≠ 0) (n : ℕ)
    {freq L K C KRelay rowCap : ℝ} (hfreq : 1 ≤ freq) (hL : 1 ≤ L) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hsmall : L ^ 6 * freq ^ (-1 / 12 : ℝ) ≤ 1)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγle : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    {envelope : Set Vec3} (hEnvelope : IsClosed envelope) (hInactive : b.leading.Inactive t₀ envelope)
    (hrow : ∀ i : Fin 3, unweightedSeminorm False ℓ h n hT
      (scaledCoframeRowProfile ℓ d.inverse i) ≤ rowCap)
    (hSlowCap : 3 * hierarchyQuadraticConstant (Fin 4) n ^ 2 * rowCap ≤ K * L)
    (hFastCap : hierarchyQuadraticConstant (Fin 4) n ^ 2 *
      unweightedSeminorm False ℓ h n hT (scaledPhaseCoefficientProfile h d.covector) ≤
        K * L * freq ^ (3 / 2 : ℝ))
    (hCoeff : WaveRelayCoefficientBudget ℓ h n KRelay
      (fun (t : Icc t₀ T) a => d.inverse.val.val.val (t, a, 0))
      (fun (t : Icc t₀ T) a => d.strain.val.val.val (t, a, 0))
      (fun (t : Icc t₀ T) a => freq⁻¹ • d.covector.val.val.val (t, a, 0)))
    (hRelayCap : waveRelayOrderConstant n * KRelay ^ 2 ≤ K * L) :
    let s := actualMeasuredLevels b.operators b.profiles P b.leading.completionSwitch b.parentResidual
      freq (zero_le_one.trans hfreq) ℓ h hT ht₀ htT γ hγ hpos
    (∀ i ∈ Finset.Icc 1 P, HierarchyLevelBound s freq L C (n + 1) i) →
    unweightedSeminorm False ℓ h n hT (b.operators.remainder b.profiles P) ≤
      2 * K * (C + 1) ^ 2 *
        (1 + ((hierarchyTailPairs P 0).card : ℝ) + 2 * ((hierarchyTailPairs P 1).card : ℝ)) *
        freq ^ hierarchyOscExponent (P + 1) := by
  intro s hlevel
  let A := b.operators
  let u := b.profiles
  let R := A.material (u.C P) + A.labelGrad (u.p P)
  let W (m : ℕ) : Seminorm ℝ VP := amplitudeSeminorm False ℓ h m hT ht₀ htT γ hγ hpos
  let N (m : ℕ) : Seminorm ℝ VP := unweightedSeminorm False ℓ h m hT
  have hf : 0 < freq := zero_lt_one.trans_le hfreq
  have hP₁ : 1 ≤ P := by omega
  obtain ⟨hsupport, _, _⟩ := physicalConstruct_support_and_tail_on_inactive
    (τ := t₀) hT b.time_le_one hEnvelope d.inverse d.strain d.covector d.mean d.oscillation hP₁
    b.leading.completionSwitch b.parentResidual b.parentResidual_average b.leading.output
    hInactive.velocity hInactive.pressure hInactive.completionSwitch
  have hCzero (i : ℕ) (t : ℝ) (ht : t ∈ I) (ht' : t < t₀) (x : Vec3 × ℝ) :
      (u.C i).val.val.val (t, x) = 0 :=
    (hsupport i).2.1 ⟨⟨ht, mem_univ _⟩, Or.inl ht'⟩
  have hYzero (i : ℕ) (t : ℝ) (ht : t ∈ I) (ht' : t < t₀) (x : Vec3 × ℝ) :
      (u.Y i).val.val.val (t, x) = 0 := by
    change (u.V i).val.val.val (t, x) + (u.C (i - 1)).val.val.val (t, x) = 0
    rw [show (u.V i).val.val.val (t, x) = 0 from
      (hsupport i).1 ⟨⟨ht, mem_univ _⟩, Or.inl ht'⟩, hCzero _ t ht ht' x, add_zero]
  have hRzero (t : ℝ) (ht : t ∈ I) (ht' : t < t₀) (x : Vec3 × ℝ) :
      R.val.val.val (t, x) = 0 := by
    let laws := inactiveLaws (τ := t₀) hT hEnvelope d.inverse d.strain d.covector d.mean.inverse_independent
    let E₀ := inactiveSubmodule T k Vec3 t₀ envelope
    have hRC : A.material (u.C P) ∈ E₀ :=
      laws.material (mem_inactiveSubmodule.mpr (hsupport P).2.1)
    have hRp : A.labelGrad (u.p P) ∈ E₀ :=
      laws.labelGrad (mem_inactiveSubmodule.mpr (hsupport P).2.2)
    exact (mem_inactiveSubmodule.mp (E₀.add_mem hRC hRp)) ⟨⟨ht, mem_univ _⟩, Or.inl ht'⟩
  have hLinear : N n R ≤ K * L * freq ^ (-1 : ℝ) *
      (s.osc (n + 1) P + s.oscSource (n + 1) P) := by
    have hNw : N n R ≤ W n R :=
      unweightedSeminorm_le_amplitudeSeminorm_of_inactive False ℓ h n hT ht₀ htT γ hγ hpos hγle R hRzero
    refine (hNw.trans (b.amplitudeSeminorm_finalRelay_le hP hX hU hper ℓ h hℓ n hf ht₀ htT γ hγ hpos
      hCoeff)).trans ?_
    rw [Real.rpow_neg_one]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hRelayCap (inv_nonneg.mpr hf.le))
      (add_nonneg (s.nonneg (n + 1) P).2.2.1 (s.nonneg (n + 1) P).1)
  have hLast (m : ℕ) :
      s.Y m (P + 1) = s.completion m P ∧ s.Z m (P + 1) = s.completion m P ∧ s.mean m (P + 1) = 0 :=
    construct_actualMeasuredLevels_tail_last A b.solvers hP₁ m b.leading.completionSwitch
      b.parentResidual b.parentResidual_average b.leading.output hf.le ℓ h hT ht₀ htT γ hγ hpos
  have hcompletion (i : ℕ) (hi : i ∈ Finset.Icc 1 P) : s.completion n i ≤
      C * L ^ 2 * freq ^ hierarchyCompletionExponent i :=
    (amplitudeSeminorm_mono_order False ℓ h (Nat.le_succ n) hT ht₀ htT γ hγ hpos (u.C i)).trans
      (hlevel i hi).completion
  have hmean (i : ℕ) (hi : i ∈ Finset.Icc 2 (P + 1)) : s.mean n i ≤
      C * freq ^ hierarchyInductiveMeanExponent i := by
    obtain ⟨hi₂, hiP⟩ := Finset.mem_Icc.mp hi
    by_cases hin : i ≤ P
    · exact (unweightedSeminorm_mono_order False ℓ h (Nat.le_succ n) hT (u.B i)).trans
        (hlevel i (Finset.mem_Icc.mpr ⟨by omega, hin⟩)).mean
    · have hlast : i = P + 1 := by omega
      rw [hlast, (hLast n).2.2]
      positivity
  have hFast (i j : ℕ) := actualMeasuredLevels_fastTail_terms hT d.inverse d.strain d.covector u P n
    b.leading.completionSwitch b.parentResidual hf.le ℓ h hh ht₀ htT γ hγ hpos hγle hFastCap i j
    (hCzero (i - 1)) (hYzero j)
  exact hierarchy_depth_tail_of_measuredProducts A u s P n (N n) hfreq hL hK hC hsmall hP₁
    hlevel hcompletion hmean (hLast (n + 1)).1.le (hLast (n + 1)).2.1.le hLinear
    (fun ij _ => actualMeasuredLevels_slowTail_term hT d.inverse d.strain d.covector u P n
      b.leading.completionSwitch b.parentResidual hf.le ℓ h hℓ ht₀ htT γ hγ hpos hγle hrow hSlowCap
      ij.1 ij.2 hYzero)
    (fun ij _ => (hFast ij.1 ij.2).1)
    (fun ij _ => (hFast ij.1 ij.2).2)


end

end TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData
