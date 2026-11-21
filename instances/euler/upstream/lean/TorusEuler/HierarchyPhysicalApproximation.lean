import TorusEuler.HierarchyPhysicalPiola
import TorusEuler.HierarchyParityPropagation
import TorusEuler.HierarchyPhysicalGraph
import TorusEuler.HierarchyPhysicalSupport
import TorusEuler.ParentPressureParity
import TorusEuler.TruncatedChildStage

/-! The qualitative Eulerian approximation from the actual finite profile solves. -/

open Filter MeasureTheory Set UnitAddTorus
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3} {U : Velocity} {X : ℝ → Velocity} {p : Pressure}

local notation "I" => Icc (0 : ℝ) T
local notation "J" => Set.prod I (univ : Set Vec3)
local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ

/-- The leading wave, its normalized phase pressure, and the two switch
sources, in the actual twisted profile spaces of the parent. -/
structure PhysicalLeadingInput {hT : 0 < T} (d : ParentGeometry hT U X k) where
  output : HierarchyTransverseOutput (twistedHierarchyOperators hT d.inverse d.strain d.covector)
  leadingSwitch : VP
  completionSwitch : VP
  momentum : let O := twistedHierarchyOperators hT d.inverse d.strain d.covector
    O.material output.V + O.phaseGrad output.p = leadingSwitch
  velocity_odd : HierarchyProfileReflectionParity (-1) output.V.val.val.val
  pressure_even : HierarchyProfileReflectionParity 1 output.p.val.val.val
  completionSwitch_odd : HierarchyProfileReflectionParity (-1) completionSwitch.val.val.val

/-- The supported leading profiles and switch forces share the same inactive region. -/
structure PhysicalLeadingInput.Inactive {hT : 0 < T} {d : ParentGeometry hT U X k}
    (L : PhysicalLeadingInput d) (τ : ℝ) (S : Set Vec3) : Prop where
  velocity : EqOn L.output.V.val.val.val 0 (hierarchyInactiveRegion T τ S)
  pressure : EqOn L.output.p.val.val.val 0 (hierarchyInactiveRegion T τ S)
  leadingSwitch : EqOn L.leadingSwitch.val.val.val 0 (hierarchyInactiveRegion T τ S)
  completionSwitch : EqOn L.completionSwitch.val.val.val 0 (hierarchyInactiveRegion T τ S)

/-- The inputs to the actual finite expansion. The parent residual is the
pullback of the physical momentum residual, including the within-time derivative. -/
structure PhysicalApproximationData {hT : 0 < T} (d : ParentGeometry hT U X k)
    (p : Pressure) (P : ℕ) where
  time_le_one : T ≤ 1
  leading : PhysicalLeadingInput d
  parentResidual : VP
  parentResidual_average : (twistedHierarchyOperators hT d.inverse d.strain d.covector).average
    parentResidual = parentResidual
  parentResidual_value : ∀ z ∈ hierarchyProfileSlab T,
    parentResidual.val.val.val z = momentumResidual I U p z.1 (X 0 z.1 z.2.1)
  parentResidual_odd : HierarchyProfileReflectionParity (-1) parentResidual.val.val.val

private theorem reflectionParity_of_onSlab {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : HierarchyTwistedProfile T k E} {sign : ℝ}
    (h : ∀ z ∈ hierarchyProfileSlab T,
      f.val.val.val (hierarchyProfileReflection z) = sign • f.val.val.val z) :
    HierarchyProfileReflectionParity sign f.val.val.val := by
  intro z
  by_cases hz : z ∈ hierarchyProfileSlab T
  · exact h z hz
  · rw [HierarchySmoothProfile.eq_zero_outside f.val.val
      (fun hz' => hz (hierarchyProfileReflection_mem_slab.mp hz')),
      HierarchySmoothProfile.eq_zero_outside f.val.val hz, smul_zero]

private theorem slice_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → Vec3 → E} (hu : ContDiffOn ℝ ∞ (Function.uncurry u) J) {t : ℝ} (ht : t ∈ I) :
    ContDiff ℝ ∞ (u t) := by
  have h : ContDiff ℝ ∞ (fun x : Vec3 => (t,x)) := contDiff_const.prodMk contDiff_id
  exact contDiffOn_univ.mp (hu.comp h.contDiffOn (fun x _ => ⟨ht, mem_univ x⟩))

/-- The actual parent residual supplies the admissible mean datum for the
construction. No independent choice of a forcing is required. -/
theorem exists_physicalApproximationData {hT : 0 < T} (d : ParentGeometry hT U X k)
    (hT₁ : T ≤ 1) (hX : IsLabelFlowOn U X I)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J) (hp : ContDiffOn ℝ ∞ (Function.uncurry p) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (hpper : ∀ t ∈ I, SpatiallyPeriodic (p t))
    (hodd : ∀ t ∈ I, Function.Odd (U t))
    (hRodd : ∀ t ∈ I, Function.Odd (momentumResidual I U p t))
    (L : PhysicalLeadingInput d) (P : ℕ) :
    ∃ b : PhysicalApproximationData d p P, b.leading = L := by
  have hRs := contDiffOn_closedSlab_momentumResidual hT hU hp
  have hRp : ∀ t ∈ I, SpatiallyPeriodic (momentumResidual I U p t) :=
    fun t ht => spatiallyPeriodic_closedSlab_momentumResidual ht (slice_smooth hU ht)
      (slice_smooth hp ht) hper (hpper t ht)
  obtain ⟨R, hR, hval, hReflection⟩ := exists_pulledBackParentResidual hT hX hU hper hRs hRp d
  exact ⟨⟨hT₁, L, R, hR, hval, hReflection hodd hRodd⟩, rfl⟩

namespace PhysicalApproximationData

variable {hT : 0 < T} {d : ParentGeometry hT U X k} {P : ℕ}
  (b : PhysicalApproximationData d p P)

/-- The concrete finite hierarchy operators of the same parent. -/
abbrev operators (_data : PhysicalApproximationData d p P) : HierarchyOperators VP SP :=
  twistedHierarchyOperators hT d.inverse d.strain d.covector

/-- The selected endpoint mean, affine transverse and curl completion solves. -/
abbrev solvers :
    FiniteHierarchySolvers (twistedHierarchyOperators hT d.inverse d.strain d.covector) :=
  physicalSolvers hT b.time_le_one d.inverse d.strain d.covector d.mean d.oscillation

/-- The actual retained profiles used for every Eulerian quantity below. -/
def profiles : HierarchyProfiles VP SP :=
  b.solvers.construct P b.leading.completionSwitch b.parentResidual b.parentResidual_average b.leading.output

/-- The complete retained velocity at arbitrary label and phase. -/
def profileVelocity (t : ℝ) (a : Vec3) (s : ℝ) : Vec3 :=
  (b.profiles.velocity P).val.val.val (t, a, s)

theorem profileVelocity_smooth (t : ℝ) (ht : t ∈ I) :
    ContDiff ℝ ∞ (Function.uncurry (b.profileVelocity t)) :=
  HierarchySmoothProfile.contDiff_labelPhase_slice (b.profiles.velocity P).val.val ht

theorem profileVelocity_periodic (t : ℝ) (a : Vec3) : Function.Periodic (b.profileVelocity t a) 1 :=
  HierarchyPeriodicProfile.phasePeriodic (b.profiles.velocity P).val t a

theorem profileVelocity_skew (t : ℝ) (n : Fin 3 → ℤ) (a : Vec3) (s : ℝ) :
    b.profileVelocity t (a + latticeVector n) (s + ⟪k, latticeVector n⟫_ℝ) = b.profileVelocity t a s :=
  twistedSlice (b.profiles.velocity P) t a s n

/-- Eulerian graph of the oscillatory correction. -/
def oscillation : Velocity :=
  graphRead (fun t => X t 0) (b.profiles.velocity P - b.operators.average (b.profiles.velocity P))

/-- The Eulerian leading wave prescribed as the input to level one. -/
def leadingVelocity : Velocity :=
  graphRead (fun t => X t 0) b.leading.output.V

/-- The leading completion and all subsequent oscillations, as used in the
central gradient estimate. -/
def oscillationRemainder : Velocity :=
  graphRead (fun t => X t 0) (b.profiles.C 1 +
    ∑ i ∈ Finset.Icc 2 P, (b.profiles.V i + b.profiles.C i))

/-- Eulerian graph of the mean correction. -/
def meanCorrection : Velocity :=
  graphRead (fun t => X t 0) (b.operators.average (b.profiles.velocity P))

/-- The approximate Eulerian velocity. -/
def velocity : Velocity :=
  U + graphRead (fun t => X t 0) (b.profiles.velocity P)

/-- The approximate Eulerian pressure. -/
def pressure : Pressure :=
  p + graphRead (fun t => X t 0) (b.profiles.pressure P)

/-- The exact retained tail and switch residual on the Eulerian graph. -/
def residual : Velocity :=
  graphRead (fun t => X t 0)
    (b.operators.remainder b.profiles P + (b.leading.leadingSwitch + b.leading.completionSwitch))

theorem velocity_eq_parent_add_oscillation_add_mean :
    b.velocity = U + b.oscillation + b.meanCorrection := by
  funext t x
  change U t x + (b.profiles.velocity P).val.val.val (hierarchyGraphPoint (fun t => X t 0) k t x) =
    U t x +
      ((b.profiles.velocity P).val.val.val (hierarchyGraphPoint (fun t => X t 0) k t x) -
        (b.operators.average (b.profiles.velocity P)).val.val.val (hierarchyGraphPoint (fun t => X t 0) k t x)) +
      (b.operators.average (b.profiles.velocity P)).val.val.val (hierarchyGraphPoint (fun t => X t 0) k t x)
  abel

/-- The physical oscillation is exactly the graph of the completed
oscillatory profiles, with no mean term. -/
theorem oscillation_eq_graph_sum :
    b.oscillation = graphRead (fun t => X t 0) (∑ i ∈ Finset.Icc 1 P, (b.profiles.V i + b.profiles.C i)) := by
  have h := b.solvers.construct_velocity_sub_average P b.leading.completionSwitch b.parentResidual
    b.parentResidual_average b.leading.output
  exact congrArg (graphRead (fun t => X t 0)) h

/-- The oscillatory correction consists of the leading wave and the
explicit sum of the remaining oscillations and completions. -/
theorem oscillation_eq_leading_add_remainder (hP : 1 ≤ P) :
    b.oscillation = b.leadingVelocity + b.oscillationRemainder := by
  classical
  rw [b.oscillation_eq_graph_sum]
  have hFirst : b.profiles.V 1 = b.leading.output.V :=
    (b.solvers.construct_leading P b.leading.completionSwitch b.parentResidual
      b.parentResidual_average b.leading.output).1
  rw [← Finset.insert_Icc_add_one_left_eq_Icc hP, Finset.sum_insert (by simp), hFirst, add_assoc]
  rfl

/-- The exact level-one decomposition used by the central wave estimates. -/
theorem velocity_eq_parent_add_leading_add_remainder_add_mean (hP : 1 ≤ P) :
    b.velocity = U + b.leadingVelocity + b.oscillationRemainder + b.meanCorrection := by
  rw [b.velocity_eq_parent_add_oscillation_add_mean, b.oscillation_eq_leading_add_remainder hP]
  abel

/-- The higher oscillatory remainder is smooth on the physical graph. -/
theorem oscillationRemainder_smooth (hX : IsLabelFlowOn U X I)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J) (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) :
    ContDiffOn ℝ ∞ (Function.uncurry b.oscillationRemainder) J :=
  HierarchySmoothProfile.contDiffOn_graphRead k _ (hX.contDiffOn_inverseLabelFlow hT hU hper)

/-- The phase average is exactly the sum of the selected mean profiles. -/
theorem meanCorrection_eq_graph_sum :
    b.meanCorrection = graphRead (fun t => X t 0) (∑ i ∈ Finset.Icc 1 P, b.profiles.B i) := by
  let O := b.operators
  apply congrArg (graphRead (fun t => X t 0))
  have hosc : b.profiles.velocity P - O.average (b.profiles.velocity P) =
        ∑ i ∈ Finset.Icc 1 P, (b.profiles.V i + b.profiles.C i) :=
    b.solvers.construct_velocity_sub_average P b.leading.completionSwitch b.parentResidual
      b.parentResidual_average b.leading.output
  have hsum : b.profiles.velocity P =
      (∑ i ∈ Finset.Icc 1 P, (b.profiles.V i + b.profiles.C i)) + ∑ i ∈ Finset.Icc 1 P, b.profiles.B i := by
    exact Finset.sum_add_distrib
  calc
    O.average (b.profiles.velocity P) = b.profiles.velocity P -
        (b.profiles.velocity P - O.average (b.profiles.velocity P)) := by abel
    _ = ∑ i ∈ Finset.Icc 1 P, b.profiles.B i := by rw [hosc, hsum]; abel

end PhysicalApproximationData

/-- The approximate smooth fields and their exact Eulerian equations,
with the parities of the odd construction. -/
structure PhysicalApproximationProperties {hT : 0 < T} {d : ParentGeometry hT U X k} {P : ℕ}
    (b : PhysicalApproximationData d p P) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ (Function.uncurry b.velocity) J
  pressure_smooth : ContDiffOn ℝ ∞ (Function.uncurry b.pressure) J
  residual_smooth : ContDiffOn ℝ ∞ (Function.uncurry b.residual) J
  oscillation_smooth : ContDiffOn ℝ ∞ (Function.uncurry b.oscillation) J
  mean_smooth : ContDiffOn ℝ ∞ (Function.uncurry b.meanCorrection) J
  periodic : ∀ t ∈ I, SpatiallyPeriodic (b.velocity t) ∧ SpatiallyPeriodic (b.pressure t) ∧
    SpatiallyPeriodic (b.residual t) ∧ SpatiallyPeriodic (b.oscillation t) ∧ SpatiallyPeriodic (b.meanCorrection t)
  reflection : ∀ t ∈ I, Function.Odd (b.velocity t) ∧ Function.Even (b.pressure t) ∧
    Function.Odd (b.residual t) ∧ Function.Odd (b.oscillation t) ∧ Function.Odd (b.meanCorrection t)
  divergence_free : ∀ t ∈ I, ∀ x, divergence (b.velocity t) x = 0
  profile_divergence : ∀ t ∈ I, ∀ x s,
    divergence (fun y => b.profileVelocity t (X t 0 y) s) (X 0 t x) +
      ⟪(fderiv ℝ (X t 0) (X 0 t x)).adjoint k, deriv (b.profileVelocity t x) s⟫_ℝ = 0
  residual_exact : ∀ t ∈ I, ∀ x, momentumResidual I b.velocity b.pressure t x = b.residual t x

namespace PhysicalApproximationData

variable {hT : 0 < T} {d : ParentGeometry hT U X k} {P : ℕ}
  (b : PhysicalApproximationData d p P)

private theorem divergence_add {f g : Vec3 → Vec3} {x : Vec3}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    divergence (f + g) x = divergence f x + divergence g x := by
  change divergence (fun y => f y + g y) x = _
  simp only [divergence, fderiv_fun_add hf hg, _root_.add_apply, PiLp.add_apply,
    Finset.sum_add_distrib]

set_option maxHeartbeats 1800000 in
/-- The actual selected profiles give a jointly smooth, periodic, odd and
solenoidal approximate Euler velocity and an even approximate pressure.
The remaining divergence premise is the Piola identity for the mean solve. -/
private theorem assemble_of_mean_divergence (hP : 2 ≤ P) (hX : IsLabelFlowOn U X I)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J) (hp : ContDiffOn ℝ ∞ (Function.uncurry p) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (hpper : ∀ t ∈ I, SpatiallyPeriodic (p t))
    (hodd : ∀ t ∈ I, Function.Odd (U t)) (hpEven : ∀ t ∈ I, Function.Even (p t))
    (hdiv : ∀ t ∈ I, ∀ x, divergence (U t) x = 0)
    (hB : ∀ f hf, HierarchySmoothProfile.profileTotalDivergence hT d.inverse.val.val d.covector.val.val
      (b.solvers.solveMean f hf).val.B.val.val = 0) : PhysicalApproximationProperties b := by
  let A : Velocity := fun t => X t 0
  let W := b.profiles.velocity P
  let Q := b.profiles.pressure P
  let B := b.operators.average W
  let R := b.operators.remainder b.profiles P + (b.leading.leadingSwitch + b.leading.completionSwitch)
  have hA : ContDiffOn ℝ ∞ (Function.uncurry A) J := hX.contDiffOn_inverseLabelFlow hT hU hper
  have hGraphSmooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : HierarchyTwistedProfile T k E) : ContDiffOn ℝ ∞ (Function.uncurry (graphRead A f)) J :=
    HierarchySmoothProfile.contDiffOn_graphRead k f.val.val hA
  have hGraphPeriodic {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : HierarchyTwistedProfile T k E) {t : ℝ} (ht : t ∈ I) : SpatiallyPeriodic (graphRead A f t) :=
    spatiallyPeriodic_inverseParentGraphRead hT hX hU hper f ht
  obtain ⟨hG, hM, hκ, _⟩ := d.reflection hX hU hper hodd
  have hMeanEven : d.mean.Even := d.meanEven hX hU hper hodd
  have hMean (f : VP) (hf : b.operators.average f = f)
      (h : HierarchyProfileReflectionParity (-1) f.val.val.val) :
      HierarchyProfileReflectionParity (-1) (b.solvers.solveMean f hf).val.B.val.val.val ∧
        HierarchyProfileReflectionParity 1 (b.solvers.solveMean f hf).val.q.val.val.val := by
    let out := solveMean hT b.time_le_one d.inverse d.strain d.covector d.mean f hf
    have hOdd (t : ℝ) (ht : t ∈ I) : Function.Odd (fun a => f.val.val.val (t,a,0)) := by
      intro a
      simpa only [hierarchyProfileReflection_apply, neg_zero, neg_one_smul] using h (t,a,0)
    refine ⟨reflectionParity_of_onSlab (f := out.output.B) ?_,
      reflectionParity_of_onSlab (f := out.output.q) ?_⟩
    · rintro ⟨t, a, s⟩ hz
      simpa only [hierarchyProfileReflection_apply, neg_one_smul] using (out.reflection hMeanEven hOdd t hz.1 a s).1
    · rintro ⟨t, a, s⟩ hz
      simpa only [hierarchyProfileReflection_apply, one_smul] using (out.reflection hMeanEven hOdd t hz.1 a s).2
  have hTransverse (f : VP) (hf : b.operators.average f = 0)
      (h : HierarchyProfileReflectionParity (-1) f.val.val.val) :
      HierarchyProfileReflectionParity (-1) (b.solvers.solveTransverse f hf).val.V.val.val.val ∧
        HierarchyProfileReflectionParity 1 (b.solvers.solveTransverse f hf).val.p.val.val.val := by
    let out := solveTransverse hT d.inverse d.strain d.covector d.oscillation f hf
    have hParity := out.reflection
      (fun t _ a => by simpa only [hierarchyProfileReflection_apply, neg_zero, one_smul] using hM (t,a,0))
      (fun t _ a => by simpa only [hierarchyProfileReflection_apply, neg_zero, one_smul] using hκ (t,a,0))
      (fun t _ a s => by simpa only [hierarchyProfileReflection_apply, neg_one_smul] using h (t,a,s))
    refine ⟨reflectionParity_of_onSlab (f := out.output.V) ?_,
      reflectionParity_of_onSlab (f := out.output.p) ?_⟩
    · rintro ⟨t, a, s⟩ hz
      simpa only [hierarchyProfileReflection_apply, neg_one_smul] using (hParity t hz.1 a s).1
    · rintro ⟨t, a, s⟩ hz
      simpa only [hierarchyProfileReflection_apply, one_smul] using (hParity t hz.1 a s).2
  have hCompletion (o : HierarchyTransverseOutput b.operators)
      (h : HierarchyProfileReflectionParity (-1) o.V.val.val.val) :
      HierarchyProfileReflectionParity (-1) (b.solvers.complete o.V).val.val.val :=
    complete_reflectionOdd_of_phaseMean_zero hT d.inverse d.covector d.oscillation.covector_independent
      d.oscillation.covector_ne_zero o.V hG hκ h o.average_V
  obtain ⟨_, hW, hQ, hTail⟩ := construct_reflectionParity hT d.inverse d.strain d.covector
    b.solvers (show 1 ≤ P by omega) b.leading.completionSwitch b.parentResidual b.parentResidual_average
    b.leading.output hG hM hκ b.leading.completionSwitch_odd b.parentResidual_odd b.leading.velocity_odd
    b.leading.pressure_even hMean hTransverse hCompletion
  have hR : HierarchyProfileReflectionParity (-1) R.val.val.val :=
    remainder_add_switch_reflectionParity hT d.inverse d.strain d.covector b.profiles P
      b.leading.output b.leading.leadingSwitch b.leading.completionSwitch hM hκ b.leading.velocity_odd
      b.leading.pressure_even b.leading.momentum b.leading.completionSwitch_odd hTail
  have hMeanOdd : HierarchyProfileReflectionParity (-1) B.val.val.val := average_reflectionParity hT W (-1) hW
  have hOsc : HierarchyProfileReflectionParity (-1) (W - B).val.val.val :=
    (reflectionSubmodule (T := T) (k := k) (-1) Vec3).sub_mem hW hMeanOdd
  have hGraphOdd (f : VP) (hf : HierarchyProfileReflectionParity (-1) f.val.val.val)
      {t : ℝ} (ht : t ∈ I) : Function.Odd (graphRead A f t) := by
    intro x
    simpa only [neg_one_smul] using inverseParentGraphRead_reflection hT hX hU hper hodd f hf ht x
  have hGraphEven (f : SP) (hf : HierarchyProfileReflectionParity 1 f.val.val.val)
      {t : ℝ} (ht : t ∈ I) : Function.Even (graphRead A f t) := by
    intro x
    simpa only [one_smul] using inverseParentGraphRead_reflection hT hX hU hper hodd f hf ht x
  obtain ⟨hSurj, hChart⟩ := d.inverseGraph_values hX hU hper
  have hGgraph (t : ℝ) (ht : t ∈ I) (x : Vec3) (s : ℝ) := (hChart t ht x s).1
  have hκgraph (t : ℝ) (ht : t ∈ I) (x : Vec3) (s : ℝ) := (hChart t ht x s).2
  have hCdiv (o : HierarchyTransverseOutput b.operators) :
      HierarchySmoothProfile.profileTotalDivergence hT d.inverse.val.val d.covector.val.val
        (o.V + b.solvers.complete o.V).val.val = 0 :=
    profileTotalDivergence_completedOutput_eq_zero hT d.inverse d.strain d.covector
      d.oscillation.covector_independent d.oscillation.covector_ne_zero o
      (fun _ ht => (slice_smooth hA ht).of_le (by simp)) hSurj hGgraph hκgraph
  let forget : VP →ₗ[ℝ] HierarchySmoothProfile T Vec3 :=
    (hierarchyPeriodicProfileSubmodule T Vec3).subtype.comp
      (hierarchyTwistedProfileSubmodule T k Vec3).subtype
  let D := (HierarchySmoothProfile.profileTotalDivergence hT d.inverse.val.val d.covector.val.val).comp forget
  have hWdiv : HierarchySmoothProfile.profileTotalDivergence hT d.inverse.val.val d.covector.val.val
      W.val.val = 0 :=
    b.solvers.construct_divergence_eq_zero P b.leading.completionSwitch b.parentResidual
      b.parentResidual_average b.leading.output D hCdiv hB
  refine ⟨hU.add (hGraphSmooth W), hp.add (hGraphSmooth Q), hGraphSmooth R,
    hGraphSmooth (W - B), hGraphSmooth B, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    refine ⟨?_, ?_, hGraphPeriodic R ht, hGraphPeriodic (W - B) ht, hGraphPeriodic B ht⟩
    · intro n x
      change U t (x + latticeVector n) + graphRead A W t (x + latticeVector n) = U t x + graphRead A W t x
      rw [hper t ht, hGraphPeriodic W ht]
    · intro n x
      change p t (x + latticeVector n) + graphRead A Q t (x + latticeVector n) = p t x + graphRead A Q t x
      rw [hpper t ht, hGraphPeriodic Q ht]
  · intro t ht
    refine ⟨?_, ?_, hGraphOdd R hR ht, hGraphOdd (W - B) hOsc ht, hGraphOdd B hMeanOdd ht⟩
    · intro x
      change U t (-x) + graphRead A W t (-x) = -(U t x + graphRead A W t x)
      rw [hodd t ht, hGraphOdd W hW ht, neg_add]
    · intro x
      change p t (-x) + graphRead A Q t (-x) = p t x + graphRead A Q t x
      rw [hpEven t ht, hGraphEven Q hQ ht]
  · intro t ht x
    have hDiffA : DifferentiableAt ℝ (A t) x := (slice_smooth hA ht).differentiable (by simp) x
    have hDiv : divergence (graphRead A W t) x = 0 :=
      HierarchySmoothProfile.divergence_transportedSmoothProfile_eq_zero hT
        d.inverse.val.val d.covector.val.val W.val.val ht hDiffA.hasFDerivAt
        (hGgraph t ht x ⟪k, A t x⟫_ℝ) (hκgraph t ht x ⟪k, A t x⟫_ℝ) hWdiv
    change divergence (U t + graphRead A W t) x = 0
    rw [divergence_add ((slice_smooth hU ht).differentiable (by simp) x)
      ((slice_smooth (hGraphSmooth W) ht).differentiable (by simp) x), hdiv t ht x, hDiv, add_zero]
  · intro t ht a s
    obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by simp)) hper
    have hInv : X t 0 (X 0 t a) = a := (hX.inverse hK (left_mem_Icc.mpr hT.le) ht).1 a
    have hA' := (slice_smooth hA ht).differentiable (by simp) (X 0 t a)
    have hLabel : DifferentiableAt ℝ (fun x => b.profileVelocity t x s) a :=
      ((b.profileVelocity_smooth t ht).comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) a
    have hLabel' : HasFDerivAt (fun x => b.profileVelocity t x s)
        (fderiv ℝ (fun x => b.profileVelocity t x s) a) (A t (X 0 t a)) := by
      rw [show A t (X 0 t a) = a from hInv]
      exact hLabel.hasFDerivAt
    have hD := hLabel'.comp (X 0 t a) hA'.hasFDerivAt
    change HasFDerivAt (fun y => b.profileVelocity t (X t 0 y) s)
      ((fderiv ℝ (fun x => b.profileVelocity t x s) a).comp (fderiv ℝ (X t 0) (X 0 t a)))
      (X 0 t a) at hD
    have hZero : (HierarchySmoothProfile.profileTotalDivergence hT d.inverse.val.val d.covector.val.val
        W.val.val).val (t, a, s) = 0 := by rw [hWdiv]; rfl
    rw [show divergence (fun y => b.profileVelocity t (X t 0 y) s) (X 0 t a) =
      LinearMap.trace ℝ Vec3 ((fderiv ℝ (fun x => b.profileVelocity t x s) a).comp
        (fderiv ℝ (X t 0) (X 0 t a))).toLinearMap by
      rw [divergence_eq_trace_fderiv, hD.fderiv]]
    change LinearMap.trace ℝ Vec3
      ((fderiv ℝ (fun x => W.val.val.val (t,x,s)) a).comp (fderiv ℝ (X t 0) (X 0 t a))).toLinearMap +
        ⟪(fderiv ℝ (X t 0) (X 0 t a)).adjoint k, deriv (fun r => W.val.val.val (t,a,r)) s⟫_ℝ = 0
    have hG' := hGgraph t ht (X 0 t a) s
    have hκ' := hκgraph t ht (X 0 t a) s
    rw [hInv] at hG' hκ'
    simpa only [HierarchySmoothProfile.profileTotalDivergence, LinearMap.add_apply, Submodule.coe_add,
      Pi.add_apply, HierarchySmoothProfile.profileLabelDivergence_apply hT d.inverse.val.val W.val.val ht,
      HierarchySmoothProfile.profilePhaseDivergence_apply hT d.covector.val.val W.val.val ht,
      hG', hκ'] using hZero
  · intro t ht x
    exact momentumResidual_construct_graphRead hT hX hU hper hA d.inverse d.strain d.covector
      b.solvers hP b.leading.leadingSwitch b.leading.completionSwitch b.parentResidual b.parentResidual_average
      b.leading.output b.leading.momentum ht x ((slice_smooth hp ht).differentiable (by simp) x)
      (fun a s => d.inverse_value (t,a,s) ⟨ht, mem_univ _⟩)
      (fun a s => d.strain_value (t,a,s) ⟨ht, mem_univ _⟩)
      (fun a s => d.covector_value (t,a,s) ⟨ht, mem_univ _⟩)
      (fun a s => b.parentResidual_value (t,a,s) ⟨ht, mem_univ _⟩)

/-- The actual selected hierarchy satisfies the qualitative physical
conclusions of the one-wave approximation, including its exact residual. -/
theorem assemble (hP : 2 ≤ P) (hX : IsLabelFlowOn U X I)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J) (hp : ContDiffOn ℝ ∞ (Function.uncurry p) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (hpper : ∀ t ∈ I, SpatiallyPeriodic (p t))
    (hodd : ∀ t ∈ I, Function.Odd (U t)) (hpEven : ∀ t ∈ I, Function.Even (p t))
    (hdiv : ∀ t ∈ I, ∀ x, divergence (U t) x = 0) : PhysicalApproximationProperties b :=
  b.assemble_of_mean_divergence hP hX hU hp hper hpper hodd hpEven hdiv
    (d.physicalSolvers_mean_divergence_eq_zero hX hU hper hdiv b.time_le_one)

/-- The actual parent residual parity also determines the parent pressure
parity, so no separate reflection assumption on the pressure is needed. -/
theorem assemble_of_parent (hP : 2 ≤ P) (hX : IsLabelFlowOn U X I)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J) (hp : ContDiffOn ℝ ∞ (Function.uncurry p) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (hpper : ∀ t ∈ I, SpatiallyPeriodic (p t))
    (hodd : ∀ t ∈ I, Function.Odd (U t))
    (hdiv : ∀ t ∈ I, ∀ x, divergence (U t) x = 0) : PhysicalApproximationProperties b := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by simp)) hper
  have hResidual (t : ℝ) (ht : t ∈ I) : Function.Odd (momentumResidual I U p t) := by
    have hEval (x : Vec3) : graphRead (fun r => X r 0) b.parentResidual t x =
        momentumResidual I U p t x := by
      change b.parentResidual.val.val.val (t, X t 0 x, ⟪k, X t 0 x⟫_ℝ) = _
      rw [b.parentResidual_value _ ⟨ht, mem_univ _⟩, (hX.inverse hK (left_mem_Icc.mpr hT.le) ht).2 x]
    intro x
    rw [← hEval (-x), ← hEval x]
    simpa only [neg_one_smul] using inverseParentGraphRead_reflection hT hX hU hper hodd
      b.parentResidual b.parentResidual_odd ht x
  exact b.assemble hP hX hU hp hper hpper hodd
    (even_pressure_on_closedSlab_of_odd_momentumResidual hp hodd hResidual) hdiv

/-- Off the common label envelope, and before activation, the actual
oscillation vanishes and the physical residual is precisely the slow mean tail. -/
theorem inactive {τ : ℝ} {S : Set Vec3} (hP : 1 ≤ P) (hS : IsClosed S)
    (hL : b.leading.Inactive τ S) {t : ℝ} (ht : t ∈ I) (x : Vec3)
    (hx : t < τ ∨ X t 0 x ∉ S) :
    b.oscillation t x = 0 ∧ b.residual t x = graphRead (fun r => X r 0)
      (∑ ij ∈ hierarchyTailPairs P 0, b.operators.labelAdv (b.profiles.B ij.1) (b.profiles.B ij.2)) t x := by
  obtain ⟨hLevels, _, hTail⟩ := physicalConstruct_support_and_tail_on_inactive (τ := τ)
    hT b.time_le_one hS d.inverse d.strain d.covector d.mean d.oscillation hP
    b.leading.completionSwitch b.parentResidual b.parentResidual_average b.leading.output
    hL.velocity hL.pressure hL.completionSwitch
  let z := hierarchyGraphPoint (fun r => X r 0) k t x
  have hz : z ∈ hierarchyInactiveRegion T τ S := ⟨⟨ht, mem_univ _⟩, hx⟩
  let N := inactiveSubmodule T k Vec3 τ S
  have hOsc : (∑ i ∈ Finset.Icc 1 P, (b.profiles.V i + b.profiles.C i)) ∈ N :=
    Submodule.sum_mem N fun i _ => N.add_mem (hLevels i).1 (hLevels i).2.1
  refine ⟨?_, ?_⟩
  · rw [b.oscillation_eq_graph_sum]
    exact (mem_inactiveSubmodule.mp hOsc) hz
  · change (b.operators.remainder b.profiles P).val.val.val z +
      (b.leading.leadingSwitch.val.val.val z + b.leading.completionSwitch.val.val.val z) = _
    rw [show b.leading.leadingSwitch.val.val.val z = 0 from hL.leadingSwitch hz,
      show b.leading.completionSwitch.val.val.val z = 0 from hL.completionSwitch hz, add_zero, add_zero]
    exact hTail hz

/-- A positive activation time also has zero oscillation on its activation slice. -/
theorem oscillation_eq_zero_through_activation {τ : ℝ} {S : Set Vec3} (hP : 1 ≤ P)
    (hS : IsClosed S) (hτ : 0 < τ) (hL : b.leading.Inactive τ S) {t : ℝ} (ht : t ∈ I)
    (x : Vec3) (hx : t ≤ τ ∨ X t 0 x ∉ S) : b.oscillation t x = 0 := by
  obtain ⟨hLevels, _, _⟩ := physicalConstruct_support_and_tail (τ := τ)
    hT b.time_le_one hτ hS d.inverse d.strain d.covector d.mean d.oscillation hP
    b.leading.completionSwitch b.parentResidual b.parentResidual_average b.leading.output
    hL.velocity hL.pressure hL.completionSwitch
  let f := ∑ i ∈ Finset.Icc 1 P, (b.profiles.V i + b.profiles.C i)
  let z := hierarchyGraphPoint (fun r => X r 0) k t x
  have hz : z ∈ hierarchyInactiveThroughActivation T τ S := ⟨⟨ht, mem_univ _⟩, hx⟩
  let E : VP →ₗ[ℝ] Vec3 := (LinearMap.proj z).comp (((hierarchySmoothProfileSubmodule T Vec3).subtype.comp
    (hierarchyPeriodicProfileSubmodule T Vec3).subtype).comp (hierarchyTwistedProfileSubmodule T k Vec3).subtype)
  rw [b.oscillation_eq_graph_sum]
  change E f = 0
  rw [show f = ∑ i ∈ Finset.Icc 1 P, (b.profiles.V i + b.profiles.C i) from rfl, map_sum]
  exact Finset.sum_eq_zero fun i _ => by
    change (b.profiles.V i).val.val.val z + (b.profiles.C i).val.val.val z = 0
    rw [show (b.profiles.V i).val.val.val z = 0 from (hLevels i).1 hz,
      show (b.profiles.C i).val.val.val z = 0 from (hLevels i).2.1 hz, add_zero]

/-- The flow theorem uses the same approximate field plus the cutoff correction. -/
theorem childVelocity_eq (v : Velocity) :
    ChildFlow.childVelocity U X k b.profileVelocity v = b.velocity + v := rfl

/-- The smooth periodic slice potentials used by the Fourier-cutoff stage. -/
def potential (h : PhysicalApproximationProperties b) (t : ℝ) : EndpointSmoothPotential :=
  if ht : t ∈ I then ⟨b.pressure t, slice_smooth h.pressure_smooth ht, (h.periodic t ht).2.1⟩
  else ⟨0, contDiff_const, fun _ _ => rfl⟩

theorem potential_eq (h : PhysicalApproximationProperties b) {t : ℝ} (ht : t ∈ I) :
    (b.potential h t).lift = b.pressure t := by
  simp only [potential, dite_eq_left ht]

end PhysicalApproximationData

namespace PhysicalApproximationProperties

variable {hT : 0 < T} {d : ParentGeometry hT U X k} {P : ℕ}
  {b : PhysicalApproximationData d p P}

/-- The exact residual in the slice-potential representation required by the cutoff. -/
theorem momentum_of_potential (h : PhysicalApproximationProperties b) (t : ℝ) (ht : t ∈ I) (x : Vec3) :
    derivWithin (fun r => b.velocity r x) I t + fderiv ℝ (b.velocity t) x (b.velocity t x) +
      gradient (b.potential h t).lift x = b.residual t x := by
  rw [b.potential_eq h ht]
  exact h.residual_exact t ht x

end PhysicalApproximationProperties

end

end TorusEuler.HierarchyTwistedProfile
