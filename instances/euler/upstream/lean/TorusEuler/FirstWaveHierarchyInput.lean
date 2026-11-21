import TorusEuler.FiniteHierarchyConstruction
import TorusEuler.HierarchyTwistedProfiles
import TorusEuler.InductionChildEstimates
import TorusEuler.LocalizedSeedRegularity
import TorusEuler.WavePressureCenter

/-! The first localized wave in the periodic hierarchy over the stationary shear. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

set_option maxHeartbeats 1100000

namespace HierarchyTwistedProfile

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {T : ℝ} {k : Vec3}

/-- A periodic field of the material labels gives a phase-independent
coefficient in the lattice-twisted hierarchy. -/
private def ofGlobalLabelField (f : ℝ → Vec3 → E)
    (hSmooth : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hPer : ∀ t, SpatiallyPeriodic (f t)) : HierarchyTwistedProfile T k E :=
  ofSmooth (fun p => f p.1 p.2.1)
    (hSmooth.comp (contDiff_fst.prodMk contDiff_snd.fst).contDiffOn
      (fun p hp => ⟨hp.1, mem_univ p.2.1⟩))
    (fun p => by
      rcases p with ⟨t, a, z⟩
      simp only [hierarchyPhasePeriod, Prod.mk_add_mk, add_zero])
    (fun n p => by
      rw [add_hierarchyLatticeShift]
      exact hPer p.1 n p.2.1)

private theorem ofGlobalLabelField_eval {f : ℝ → Vec3 → E}
    (hSmooth : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hPer : ∀ t, SpatiallyPeriodic (f t)) {p : HierarchyProfilePoint}
    (hp : p ∈ hierarchyProfileSlab T) :
    (ofGlobalLabelField (k := k) f hSmooth hPer).val.val.val p = f p.1 p.2.1 := by
  unfold ofGlobalLabelField
  exact ofSmooth_eval _ _ _ hp

private theorem ofGlobalLabelField_phaseIndependent {f : ℝ → Vec3 → E}
    (hSmooth : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hPer : ∀ t, SpatiallyPeriodic (f t)) :
    HierarchyPeriodicProfile.PhaseIndependent (ofGlobalLabelField (k := k) f hSmooth hPer).val.val := by
  intro p hp r
  rw [ofGlobalLabelField_eval hSmooth hPer (show (p.1, p.2.1, r) ∈ hierarchyProfileSlab T from
    ⟨hp.1, mem_univ _⟩), ofGlobalLabelField_eval hSmooth hPer hp]

/-- Insert a radial-envelope profile into the twisted space by the exact
phase shift associated with the launch covector. -/
def ofWrappedRadial (f : ℝ → Vec3 → ℝ → E) {r : ℝ}
    (hr : 0 < r) (hcell : 2 * r < 1 / 2)
    (hSmooth : ContDiffOn ℝ ∞ (fun p : HierarchyProfilePoint => f p.1 p.2.1 p.2.2)
      (hierarchyProfileSlab T))
    (hPhase : ∀ t a, Function.Periodic (f t a) 1) : HierarchyTwistedProfile T k E :=
  ofSmooth (fun p => phaseTwistedPeriodizeCentered k
      (fun t a z => radialEnvelope r a • f t a z) p.1 p.2.1 p.2.2)
    (contDiffOn_phaseTwistedPeriodizeCentered_radialEnvelope hr hcell hSmooth)
    (fun p => by
      rcases p with ⟨t, a, z⟩
      simp only [hierarchyPhasePeriod, Prod.mk_add_mk, add_zero]
      exact phaseTwistedPeriodizeCentered_phase_periodic (fun b q => by
        rw [hPhase t b q]) a z)
    (fun n p => by
      rw [add_hierarchyLatticeShift]
      exact phaseTwistedPeriodizeCentered_translate k _ p.1 p.2.1 p.2.2 n)

@[simp] theorem ofWrappedRadial_eval {f : ℝ → Vec3 → ℝ → E} {r : ℝ}
    (hr : 0 < r) (hcell : 2 * r < 1 / 2)
    (hSmooth : ContDiffOn ℝ ∞ (fun p : HierarchyProfilePoint => f p.1 p.2.1 p.2.2)
      (hierarchyProfileSlab T))
    (hPhase : ∀ t a, Function.Periodic (f t a) 1)
    {p : HierarchyProfilePoint} (hp : p ∈ hierarchyProfileSlab T) :
    (ofWrappedRadial (k := k) f hr hcell hSmooth hPhase).val.val.val p =
      phaseTwistedPeriodizeCentered k (fun t a z => radialEnvelope r a • f t a z)
        p.1 p.2.1 p.2.2 :=
  ofSmooth_eval _ _ _ hp

theorem eval_timeDerivative (hT : 0 < T) (f : HierarchyTwistedProfile T k E)
    {p : HierarchyProfilePoint} (hp : p ∈ hierarchyProfileSlab T) :
    fderivWithin ℝ f.val.val.val (hierarchyProfileSlab T) p (1, 0, 0) =
      derivWithin (fun t => f.val.val.val (t, p.2.1, p.2.2)) (Icc 0 T) p.1 := by
  have hF := (HierarchySmoothProfile.smooth f.val.val).differentiableOn (by simp) p hp
  have hline := (hasDerivWithinAt_id p.1 (Icc 0 T)).prodMk
    (hasDerivWithinAt_const p.1 (Icc 0 T) p.2)
  have h := hF.hasFDerivWithinAt.comp_hasDerivWithinAt p.1 hline
    (fun _ ht => show (_, p.2) ∈ hierarchyProfileSlab T from ⟨ht, mem_univ _⟩)
  exact (h.derivWithin (uniqueDiffOn_Icc hT p.1 hp.1)).symm

theorem eval_phaseDerivative (f : HierarchyTwistedProfile T k E)
    {p : HierarchyProfilePoint} (hp : p ∈ hierarchyProfileSlab T) :
    fderivWithin ℝ f.val.val.val (hierarchyProfileSlab T) p (0, 0, 1) =
      deriv (fun z => f.val.val.val (p.1, p.2.1, z)) p.2.2 := by
  have hF := (HierarchySmoothProfile.smooth f.val.val).differentiableOn (by simp) p hp
  have hline := (hasDerivAt_const p.2.2 p.1).prodMk
    ((hasDerivAt_const p.2.2 p.2.1).prodMk (hasDerivAt_id p.2.2))
  have h := hF.hasFDerivWithinAt.comp_hasDerivWithinAt p.2.2
    (hline.hasDerivWithinAt (s := univ))
    (fun _ _ => show (p.1, p.2.1, _) ∈ hierarchyProfileSlab T from ⟨hp.1, mem_univ _⟩)
  exact ((hasDerivWithinAt_univ.mp h).deriv).symm

end HierarchyTwistedProfile

local notation "Coefficient" => Vec3 →L[ℝ] Vec3

/-- The actual first material gradient is constant along each stationary-shear
trajectory, although it varies across the labels. -/
def firstWaveMaterialGradient (s : ℝ) (a : Vec3) : Coefficient :=
  Real.cos (2 * Real.pi * a 1) • stationaryShearGradient s

/-- The inverse deformation, evaluated at the particle of label `a`. -/
def firstWaveInverseDeformation (s t : ℝ) (a : Vec3) : Coefficient :=
  ContinuousLinearMap.id ℝ Vec3 - t • firstWaveMaterialGradient s a

theorem firstWaveMaterialGradient_eq (s t : ℝ) (a : Vec3) :
    firstWaveMaterialGradient s a =
      fderiv ℝ (stationaryShear s) (stationaryShearFlow s t a) :=
  (firstWave_shearGradient_onTrajectory s t a).symm

theorem firstWaveInverseDeformation_eq (s t : ℝ) (a : Vec3) :
    firstWaveInverseDeformation s t a =
      fderiv ℝ (stationaryShearFlow s (-t)) (stationaryShearFlow s t a) := by
  unfold firstWaveInverseDeformation firstWaveMaterialGradient
  rw [smul_smul]
  exact (stationaryShearFlow_jacobians_eq s t a).2.symm

theorem firstWaveTransportedCovector_eq_inverseDeformation (s freq t : ℝ) (a : Vec3) :
    firstWaveTransportedCovector s freq t a =
      (firstWaveInverseDeformation s t a).adjoint (freq • (EuclideanSpace.single (0 : Fin 3) 1 : Vec3)) := by
  rw [firstWaveTransportedCovector]
  unfold firstWaveInverseDeformation firstWaveMaterialGradient
  rw [smul_smul]

private theorem contDiff_firstWaveMaterialGradient (s : ℝ) :
    ContDiff ℝ ∞ (fun a => firstWaveMaterialGradient s a) := by
  have hc : ContDiff ℝ ∞ (fun a : Vec3 => Real.cos (2 * Real.pi * a 1)) :=
    Real.contDiff_cos.comp (contDiff_const.mul (EuclideanSpace.proj (1 : Fin 3) : Vec3 →L[ℝ] ℝ).contDiff)
  exact hc.smul contDiff_const

private theorem contDiff_firstWaveInverseDeformation (s : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × Vec3 => firstWaveInverseDeformation s p.1 p.2) :=
  contDiff_const.sub (contDiff_fst.smul ((contDiff_firstWaveMaterialGradient s).comp contDiff_snd))

private theorem spatiallyPeriodic_firstWaveMaterialGradient (s : ℝ) :
    SpatiallyPeriodic (firstWaveMaterialGradient s) := by
  intro n a
  unfold firstWaveMaterialGradient
  rw [show (a + latticeVector n) 1 = a 1 + (n 1 : ℝ) from rfl, mul_add]
  have hc := Real.cos_periodic.int_mul (n 1) (2 * Real.pi * a 1)
  rw [mul_comm (2 * Real.pi) (n 1 : ℝ)]
  exact congrArg (fun z : ℝ => z • stationaryShearGradient s) hc

private theorem spatiallyPeriodic_firstWaveInverseDeformation (s t : ℝ) :
    SpatiallyPeriodic (firstWaveInverseDeformation s t) := by
  intro n a
  rw [firstWaveInverseDeformation, firstWaveInverseDeformation,
    spatiallyPeriodic_firstWaveMaterialGradient s n a]

private theorem spatiallyPeriodic_firstWaveCovector (s freq t : ℝ) :
    SpatiallyPeriodic (firstWaveTransportedCovector s freq t) := by
  intro n a
  rw [firstWaveTransportedCovector_eq_inverseDeformation, firstWaveTransportedCovector_eq_inverseDeformation,
    spatiallyPeriodic_firstWaveInverseDeformation s t n a]

/-- The time-zero covector in cycles. -/
def firstWaveLaunchCovector (freq : ℝ) : Vec3 :=
  freq • (EuclideanSpace.single (0 : Fin 3) 1 : Vec3)

def firstWaveHierarchyInverseDeformation {T : ℝ} {k : Vec3} (s : ℝ) :
    HierarchyTwistedProfile T k Coefficient :=
  HierarchyTwistedProfile.ofGlobalLabelField (firstWaveInverseDeformation s)
    (contDiff_firstWaveInverseDeformation s).contDiffOn (spatiallyPeriodic_firstWaveInverseDeformation s)

def firstWaveHierarchyMaterialGradient {T : ℝ} {k : Vec3} (s : ℝ) :
    HierarchyTwistedProfile T k Coefficient :=
  HierarchyTwistedProfile.ofGlobalLabelField (fun _ => firstWaveMaterialGradient s)
    ((contDiff_firstWaveMaterialGradient s).comp contDiff_snd).contDiffOn
    (fun _ => spatiallyPeriodic_firstWaveMaterialGradient s)

def firstWaveHierarchyCovector {T : ℝ} (s freq : ℝ) :
    HierarchyTwistedProfile T (firstWaveLaunchCovector freq) Vec3 :=
  HierarchyTwistedProfile.ofGlobalLabelField (firstWaveTransportedCovector s freq)
    (contDiff_firstWaveTransportedCovector s freq).contDiffOn
    (spatiallyPeriodic_firstWaveCovector s freq)

theorem firstWaveHierarchyInverseDeformation_eval {T : ℝ} {k : Vec3} (s : ℝ)
    {p : HierarchyProfilePoint} (hp : p ∈ hierarchyProfileSlab T) :
    (firstWaveHierarchyInverseDeformation (T := T) (k := k) s).val.val.val p =
      firstWaveInverseDeformation s p.1 p.2.1 :=
  HierarchyTwistedProfile.ofGlobalLabelField_eval _ _ hp

theorem firstWaveHierarchyMaterialGradient_eval {T : ℝ} {k : Vec3} (s : ℝ)
    {p : HierarchyProfilePoint} (hp : p ∈ hierarchyProfileSlab T) :
    (firstWaveHierarchyMaterialGradient (T := T) (k := k) s).val.val.val p =
      firstWaveMaterialGradient s p.2.1 :=
  HierarchyTwistedProfile.ofGlobalLabelField_eval _ _ hp

theorem firstWaveHierarchyCovector_eval {T : ℝ} (s freq : ℝ)
    {p : HierarchyProfilePoint} (hp : p ∈ hierarchyProfileSlab T) :
    (firstWaveHierarchyCovector (T := T) s freq).val.val.val p =
      firstWaveTransportedCovector s freq p.1 p.2.1 :=
  HierarchyTwistedProfile.ofGlobalLabelField_eval _ _ hp

theorem firstWaveHierarchyInverseDeformation_phaseIndependent {T : ℝ} {k : Vec3} (s : ℝ) :
    HierarchyPeriodicProfile.PhaseIndependent
      (firstWaveHierarchyInverseDeformation (T := T) (k := k) s).val.val :=
  HierarchyTwistedProfile.ofGlobalLabelField_phaseIndependent _ _

theorem firstWaveHierarchyMaterialGradient_phaseIndependent {T : ℝ} {k : Vec3} (s : ℝ) :
    HierarchyPeriodicProfile.PhaseIndependent
      (firstWaveHierarchyMaterialGradient (T := T) (k := k) s).val.val :=
  HierarchyTwistedProfile.ofGlobalLabelField_phaseIndependent _ _

theorem firstWaveHierarchyCovector_phaseIndependent {T : ℝ} (s freq : ℝ) :
    HierarchyPeriodicProfile.PhaseIndependent (firstWaveHierarchyCovector (T := T) s freq).val.val :=
  HierarchyTwistedProfile.ofGlobalLabelField_phaseIndependent _ _

theorem firstWaveHierarchyCovector_ne_zero {T : ℝ} (s : ℝ) {freq : ℝ} (hf : freq ≠ 0)
    {p : HierarchyProfilePoint} (hp : p ∈ hierarchyProfileSlab T) :
    (firstWaveHierarchyCovector (T := T) s freq).val.val.val p ≠ 0 := by
  rw [firstWaveHierarchyCovector_eval s freq hp]
  exact firstWaveTransportedCovector_ne_zero s freq p.1 p.2.1 hf

/-- The actual first-wave material and spatial hierarchy operators. -/
def firstWaveHierarchyOperators {T : ℝ} (hT : 0 < T) (s freq : ℝ) :=
  HierarchyTwistedProfile.twistedHierarchyOperators hT
    (firstWaveHierarchyInverseDeformation s) (firstWaveHierarchyMaterialGradient s)
    (firstWaveHierarchyCovector s freq)

private def firstWaveVelocityWithoutEnvelope (s c h t : ℝ) (a : Vec3) (z : ℝ) : Vec3 :=
  waveProfile h z • firstWaveSmoothSeed s c t a

private def firstWavePressureWithoutEnvelope (s c freq h t : ℝ) (a : Vec3) (z : ℝ) : ℝ :=
  -wavePressureCoefficient 1 (firstWaveTransportedCovector s freq t a)
    (firstWaveSmoothSeed s c t a) (firstWaveMaterialGradient s a) * wavePressurePrimitive h z

/-- The pressure of the leading oscillation before the lattice extension. -/
def firstWaveLeadingPressureProfile (s c freq r h t : ℝ) (a : Vec3) (z : ℝ) : ℝ :=
  radialEnvelope r a * firstWavePressureWithoutEnvelope s c freq h t a z

theorem firstWaveLeadingPressureProfile_eq_phasePressure (s c freq r h t : ℝ) (a : Vec3) :
    firstWaveLeadingPressureProfile s c freq r h t a =
      oscillatoryPhasePressure (firstWaveMaterialGradient s a)
        (firstWaveTransportedCovector s freq t a) (fun _ => 0) (firstWaveLeadingProfile s c r h t a) := by
  rw [show firstWaveLeadingProfile s c r h t a =
    (fun z => (radialEnvelope r a * waveProfile h z) • firstWaveSmoothSeed s c t a) from rfl,
    oscillatoryPhasePressure_primary_eq]
  funext z
  simp only [firstWaveLeadingPressureProfile, firstWavePressureWithoutEnvelope, wavePressureCoefficient,
    mul_one, div_eq_mul_inv]
  ring

set_option maxSynthPendingDepth 4 in
private theorem contDiff_firstWaveVelocityWithoutEnvelope (s c : ℝ) {h : ℝ}
    (hh : 0 < h) (hh₁ : h ≤ 1) :
    ContDiff ℝ ∞ (fun p : HierarchyProfilePoint => firstWaveVelocityWithoutEnvelope s c h p.1 p.2.1 p.2.2) := by
  have hphase : ContDiff ℝ ∞ (fun p : HierarchyProfilePoint => waveProfile h p.2.2) :=
    (contDiff_waveProfile hh hh₁).comp contDiff_snd.snd
  have hlabel : ContDiff ℝ ∞ (fun p : HierarchyProfilePoint => (p.1, p.2.1)) :=
    contDiff_fst.prodMk contDiff_snd.fst
  have hseed : ContDiff ℝ ∞ (fun p : HierarchyProfilePoint => firstWaveSmoothSeed s c p.1 p.2.1) := by
    have h := (contDiff_firstWaveSmoothSeed s c).comp hlabel
    simpa only [Function.comp_def, Function.uncurry] using h
  change ContDiff ℝ ∞ (fun p : HierarchyProfilePoint =>
    waveProfile h p.2.2 • firstWaveSmoothSeed s c p.1 p.2.1)
  simpa only [Pi.smul_def'] using hphase.smul (𝕜' := ℝ) hseed

set_option maxSynthPendingDepth 4 in
private theorem contDiff_firstWavePressureWithoutEnvelope (s c : ℝ) {freq h : ℝ}
    (hf : freq ≠ 0) (hh : 0 < h) (hh₁ : h ≤ 1) :
    ContDiff ℝ ∞ (fun p : HierarchyProfilePoint =>
      firstWavePressureWithoutEnvelope s c freq h p.1 p.2.1 p.2.2) := by
  let k (p : HierarchyProfilePoint) := firstWaveTransportedCovector s freq p.1 p.2.1
  let A (p : HierarchyProfilePoint) := firstWaveSmoothSeed s c p.1 p.2.1
  have hp : ContDiff ℝ ∞ (fun p : HierarchyProfilePoint => (p.1, p.2.1)) :=
    contDiff_fst.prodMk contDiff_snd.fst
  have hκ : ContDiff ℝ ∞ k := by
    have h := (contDiff_firstWaveTransportedCovector s freq).comp hp
    simpa only [k, Function.comp_def, Function.uncurry] using h
  have hA : ContDiff ℝ ∞ A := by
    have h := (contDiff_firstWaveSmoothSeed s c).comp hp
    simpa only [A, Function.comp_def, Function.uncurry] using h
  have hM : ContDiff ℝ ∞ (fun p : HierarchyProfilePoint => firstWaveMaterialGradient s p.2.1) :=
    (contDiff_firstWaveMaterialGradient s).comp contDiff_snd.fst
  have hMA : ContDiff ℝ ∞ (fun p : HierarchyProfilePoint =>
    firstWaveMaterialGradient s p.2.1 (A p)) := hM.clm_apply hA
  have hDot : ContDiff ℝ ∞ (fun p : HierarchyProfilePoint =>
    ⟪k p, firstWaveMaterialGradient s p.2.1 (A p)⟫_ℝ) := hκ.inner ℝ hMA
  have hSq : ContDiff ℝ ∞ (fun p => ‖k p‖ ^ 2) := hκ.norm_sq ℝ
  have hn (p : HierarchyProfilePoint) : ‖k p‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (firstWaveTransportedCovector_ne_zero _ _ _ _ hf))
  change ContDiff ℝ ∞ (fun p : HierarchyProfilePoint => -(2 * 1 *
    ⟪k p, firstWaveMaterialGradient s p.2.1 (A p)⟫_ℝ / ‖k p‖ ^ 2) * wavePressurePrimitive h p.2.2)
  have hC : ContDiff ℝ ∞ (fun _ : HierarchyProfilePoint => (2 * 1 : ℝ)) := contDiff_const
  have hphase : ContDiff ℝ ∞ (fun p : HierarchyProfilePoint => wavePressurePrimitive h p.2.2) :=
    (contDiff_wavePressurePrimitive hh hh₁).comp contDiff_snd.snd
  have hd := (((hC.mul hDot).div hSq hn).neg).mul hphase
  simpa only [Pi.mul_def, Pi.div_def, Pi.neg_def] using hd

private theorem periodic_firstWaveVelocityWithoutEnvelope (s c t : ℝ) (a : Vec3) {h : ℝ}
    (hh : 0 < h) (hh₁ : h ≤ 1) : Function.Periodic (firstWaveVelocityWithoutEnvelope s c h t a) 1 :=
  fun z => congrArg (fun x : ℝ => x • firstWaveSmoothSeed s c t a) (periodic_waveProfile hh hh₁ z)

private theorem periodic_firstWavePressureWithoutEnvelope (s c freq t : ℝ) (a : Vec3) {h : ℝ}
    (hh : 0 < h) (hh₁ : h ≤ 1) : Function.Periodic (firstWavePressureWithoutEnvelope s c freq h t a) 1 :=
  fun z => congrArg (_ * ·) (periodic_wavePressurePrimitive hh hh₁ z)

/-- The first velocity has switch identically one and is wrapped with its launch covector. -/
def firstWaveHierarchyLeadingVelocity {T : ℝ} (s c freq : ℝ) {r h : ℝ}
    (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) :
    HierarchyTwistedProfile T (firstWaveLaunchCovector freq) Vec3 :=
  HierarchyTwistedProfile.ofWrappedRadial (firstWaveVelocityWithoutEnvelope s c h) hr hcell
    (contDiff_firstWaveVelocityWithoutEnvelope s c hh hh₁).contDiffOn
    (fun t a => periodic_firstWaveVelocityWithoutEnvelope s c t a hh hh₁)

/-- The pressure uses the same lattice and phase extension as the velocity. -/
def firstWaveHierarchyLeadingPressure {T : ℝ} (s c : ℝ) {freq r h : ℝ} (hf : freq ≠ 0)
    (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) :
    HierarchyTwistedProfile T (firstWaveLaunchCovector freq) ℝ :=
  HierarchyTwistedProfile.ofWrappedRadial (firstWavePressureWithoutEnvelope s c freq h) hr hcell
    (contDiff_firstWavePressureWithoutEnvelope s c hf hh hh₁).contDiffOn
    (fun t a => periodic_firstWavePressureWithoutEnvelope s c freq t a hh hh₁)

theorem firstWaveHierarchyLeadingVelocity_eval {T : ℝ} (s c freq : ℝ) {r h : ℝ}
    (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1)
    {p : HierarchyProfilePoint} (hp : p ∈ hierarchyProfileSlab T) :
    (firstWaveHierarchyLeadingVelocity (T := T) s c freq hr hcell hh hh₁).val.val.val p =
      phaseTwistedPeriodizeCentered (firstWaveLaunchCovector freq)
        (firstWaveLeadingProfile s c r h) p.1 p.2.1 p.2.2 := by
  unfold firstWaveHierarchyLeadingVelocity
  rw [HierarchyTwistedProfile.ofWrappedRadial_eval _ _ _ _ hp]
  simp only [phaseTwistedPeriodizeCentered, firstWaveVelocityWithoutEnvelope,
    firstWaveLeadingProfile, smul_smul]

theorem firstWaveHierarchyLeadingPressure_eval {T : ℝ} (s c : ℝ) {freq r h : ℝ}
    (hf : freq ≠ 0) (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1)
    {p : HierarchyProfilePoint} (hp : p ∈ hierarchyProfileSlab T) :
    (firstWaveHierarchyLeadingPressure (T := T) s c hf hr hcell hh hh₁).val.val.val p =
      phaseTwistedPeriodizeCentered (firstWaveLaunchCovector freq)
        (firstWaveLeadingPressureProfile s c freq r h) p.1 p.2.1 p.2.2 :=
  HierarchyTwistedProfile.ofWrappedRadial_eval _ _ _ _ hp

namespace HierarchyTwistedProfile

variable {T : ℝ} {k : Vec3}

theorem material_eval (hT : 0 < T) (G M : HierarchyTwistedProfile T k Coefficient)
    (κ V : HierarchyTwistedProfile T k Vec3) {p : HierarchyProfilePoint}
    (hp : p ∈ hierarchyProfileSlab T) :
    ((twistedHierarchyOperators hT G M κ).material V).val.val.val p =
      derivWithin (fun u => V.val.val.val (u, p.2.1, p.2.2)) (Icc 0 T) p.1 +
        M.val.val.val p (V.val.val.val p) := by
  rw [← eval_timeDerivative hT V hp]
  exact HierarchySmoothProfile.hierarchyConcreteOperators_material_apply
    hT G.val.val M.val.val κ.val.val V.val.val hp

theorem phaseGrad_eval (hT : 0 < T) (G M : HierarchyTwistedProfile T k Coefficient)
    (κ : HierarchyTwistedProfile T k Vec3) (q : HierarchyTwistedProfile T k ℝ)
    {p : HierarchyProfilePoint} (hp : p ∈ hierarchyProfileSlab T) :
    ((twistedHierarchyOperators hT G M κ).phaseGrad q).val.val.val p =
      deriv (fun z => q.val.val.val (p.1, p.2.1, z)) p.2.2 • κ.val.val.val p := by
  rw [← eval_phaseDerivative q hp]
  exact HierarchySmoothProfile.phaseGradient_apply hT κ.val.val q.val.val hp

theorem average_eval (hT : 0 < T) (G M : HierarchyTwistedProfile T k Coefficient)
    (κ V : HierarchyTwistedProfile T k Vec3) {p : HierarchyProfilePoint}
    (hp : p ∈ hierarchyProfileSlab T) :
    ((twistedHierarchyOperators hT G M κ).average V).val.val.val p =
      phaseMean (fun z => V.val.val.val (p.1, p.2.1, z)) :=
  HierarchySmoothProfile.profilePhaseAverage_apply hT V.val.val hp

end HierarchyTwistedProfile

private theorem periodicField_eval_centeredLabel {E : Type*} {f : Vec3 → E}
    (hf : SpatiallyPeriodic f) (a : Vec3) : f (centeredLabel a) = f a := by
  have heq : centeredLabel a = a + latticeVector (fun i => -⌊a i + 1 / 2⌋) := by
    apply PiLp.ext
    intro i
    change Int.fract (a i + 1 / 2) - 1 / 2 = a i + ((-⌊a i + 1 / 2⌋ : ℤ) : ℝ)
    rw [Int.fract, Int.cast_neg]
    ring
  rw [heq, hf]

private theorem firstWaveLeadingVelocity_hasDerivAt (s c freq r h t : ℝ) (a : Vec3) (z : ℝ)
    (hf : freq ≠ 0) :
    HasDerivAt (fun u => firstWaveLeadingProfile s c r h u a z)
      ((radialEnvelope r a * waveProfile h z) •
        affineWaveAmplitudeOperator (firstWaveMaterialGradient s a)
          (firstWaveTransportedCovector s freq t a) (firstWaveSmoothSeed s c t a)) t :=
  (hasDerivAt_firstWaveSmoothSeed s c freq t a hf).const_smul (radialEnvelope r a * waveProfile h z)

private theorem firstWaveLeadingPressure_hasDerivAt (s c freq r t : ℝ) (a : Vec3)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (z : ℝ) :
    HasDerivAt (firstWaveLeadingPressureProfile s c freq r h t a)
      ((radialEnvelope r a * (-wavePressureCoefficient 1 (firstWaveTransportedCovector s freq t a)
        (firstWaveSmoothSeed s c t a) (firstWaveMaterialGradient s a))) * waveProfile h z) z := by
  let C := -wavePressureCoefficient 1 (firstWaveTransportedCovector s freq t a)
    (firstWaveSmoothSeed s c t a) (firstWaveMaterialGradient s a)
  have H := (hasDerivAt_wavePressurePrimitive hh hh₁ z).const_mul (radialEnvelope r a * C)
  refine H.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
  change radialEnvelope r a * (C * wavePressurePrimitive h q) =
    (radialEnvelope r a * C) * wavePressurePrimitive h q
  exact (mul_assoc _ _ _).symm

private theorem firstWaveLeadingMomentum_at_label (s c freq r h t : ℝ) (a : Vec3) (z : ℝ) :
    let k := firstWaveTransportedCovector s freq t a
    let A := firstWaveSmoothSeed s c t a
    let M := firstWaveMaterialGradient s a
    let g := radialEnvelope r a
    (g * waveProfile h z) • affineWaveAmplitudeOperator M k A +
      M (firstWaveLeadingProfile s c r h t a z) +
      ((g * (-wavePressureCoefficient 1 k A M)) * waveProfile h z) • k = 0 := by
  dsimp only
  simp only [affineWaveAmplitudeOperator_apply, firstWaveLeadingProfile, map_smul, smul_add, smul_neg,
    smul_smul, wavePressureCoefficient, mul_one]
  rw [add_right_comm (-_) _, neg_add_cancel, zero_add, ← add_smul]
  convert zero_smul ℝ (firstWaveTransportedCovector s freq t a) using 2
  ring

/-- A constant first-wave switch gives no leading momentum source. The
identity holds through both endpoints of the closed time slab. -/
theorem firstWaveHierarchyLeading_momentum {T s c freq r h : ℝ} (hT : 0 < T) (hf : freq ≠ 0)
    (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) :
    let A := firstWaveHierarchyOperators hT s freq
    A.material (firstWaveHierarchyLeadingVelocity s c freq hr hcell hh hh₁) +
      A.phaseGrad (firstWaveHierarchyLeadingPressure s c hf hr hcell hh hh₁) = 0 := by
  dsimp only
  apply HierarchyTwistedProfile.ext
  rintro ⟨t, a, z⟩ hp
  let G := firstWaveHierarchyInverseDeformation (T := T) (k := firstWaveLaunchCovector freq) s
  let M := firstWaveHierarchyMaterialGradient (T := T) (k := firstWaveLaunchCovector freq) s
  let κ := firstWaveHierarchyCovector (T := T) s freq
  let V := firstWaveHierarchyLeadingVelocity (T := T) s c freq hr hcell hh hh₁
  let P := firstWaveHierarchyLeadingPressure (T := T) s c hf hr hcell hh hh₁
  let O := HierarchyTwistedProfile.twistedHierarchyOperators hT G M κ
  change (O.material V).val.val.val (t, a, z) + (O.phaseGrad P).val.val.val (t, a, z) = 0
  have ht : t ∈ Icc 0 T := hp.1
  rw [HierarchyTwistedProfile.material_eval hT G M κ V hp,
    HierarchyTwistedProfile.phaseGrad_eval hT G M κ P hp]
  let b := centeredLabel a
  let k₀ := firstWaveLaunchCovector freq
  let z₀ := z - ⟪k₀, a⟫_ℝ + ⟪k₀, b⟫_ℝ
  have hV (u : ℝ) (hu : u ∈ Icc 0 T) :
      V.val.val.val (u, a, z) = firstWaveLeadingProfile s c r h u b z₀ :=
    firstWaveHierarchyLeadingVelocity_eval s c freq hr hcell hh hh₁ ⟨hu, mem_univ _⟩
  have htime := (firstWaveLeadingVelocity_hasDerivAt s c freq r h t b z₀ hf).hasDerivWithinAt
    (s := Icc 0 T)
  have htime' := htime.congr_of_mem hV ht
  have hQ (q : ℝ) : P.val.val.val (t, a, q) =
      firstWaveLeadingPressureProfile s c freq r h t b (q - ⟪k₀, a⟫_ℝ + ⟪k₀, b⟫_ℝ) :=
    firstWaveHierarchyLeadingPressure_eval s c hf hr hcell hh hh₁ ⟨ht, mem_univ _⟩
  have haffine : HasDerivAt (fun q : ℝ => q - ⟪k₀, a⟫_ℝ + ⟪k₀, b⟫_ℝ) 1 z :=
    ((hasDerivAt_id z).sub_const _).add_const _
  have hphase := (firstWaveLeadingPressure_hasDerivAt s c freq r t b hh hh₁ z₀).scomp z haffine
  have hphase' := hphase.congr_of_eventuallyEq (Filter.Eventually.of_forall hQ)
  rw [htime'.derivWithin (uniqueDiffOn_Icc hT t ht), hphase'.deriv, hV t ht,
    firstWaveHierarchyCovector_eval s freq hp, firstWaveHierarchyMaterialGradient_eval s hp]
  have hMb : firstWaveMaterialGradient s b = firstWaveMaterialGradient s a :=
    periodicField_eval_centeredLabel (spatiallyPeriodic_firstWaveMaterialGradient s) a
  have hκb : firstWaveTransportedCovector s freq t b = firstWaveTransportedCovector s freq t a :=
    periodicField_eval_centeredLabel (spatiallyPeriodic_firstWaveCovector s freq t) a
  rw [← hMb, ← hκb, one_smul]
  exact firstWaveLeadingMomentum_at_label s c freq r h t b z₀

private theorem shift_phaseMean_waveProfile {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (u : ℝ) :
    phaseMean (fun z => waveProfile h (z + u)) = 0 := by
  have hp : phaseMean (fun z => waveProfile h (z + u)) = phaseMean (waveProfile h) := by
    unfold phaseMean
    rw [intervalIntegral.integral_comp_add_right]
    simpa only [zero_add, add_comm (1 : ℝ) u] using
      (periodic_waveProfile hh hh₁).intervalIntegral_add_eq u 0
  exact hp.trans (phaseMean_waveProfile hh hh₁)

theorem firstWaveHierarchyLeading_average {T s c freq r h : ℝ} (hT : 0 < T)
    (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) :
    (firstWaveHierarchyOperators hT s freq).average
      (firstWaveHierarchyLeadingVelocity s c freq hr hcell hh hh₁) = 0 := by
  apply HierarchyTwistedProfile.ext
  rintro ⟨t, a, z⟩ hp
  let V := firstWaveHierarchyLeadingVelocity (T := T) s c freq hr hcell hh hh₁
  let G := firstWaveHierarchyInverseDeformation (T := T) (k := firstWaveLaunchCovector freq) s
  let M := firstWaveHierarchyMaterialGradient (T := T) (k := firstWaveLaunchCovector freq) s
  let κ := firstWaveHierarchyCovector (T := T) s freq
  change (((HierarchyTwistedProfile.twistedHierarchyOperators hT G M κ).average V).val.val.val
    (t, a, z)) = 0
  rw [HierarchyTwistedProfile.average_eval hT G M κ V hp]
  let b := centeredLabel a
  let u := ⟪firstWaveLaunchCovector freq, b⟫_ℝ - ⟪firstWaveLaunchCovector freq, a⟫_ℝ
  have heq (q : ℝ) : V.val.val.val (t, a, q) =
      (radialEnvelope r b * waveProfile h (q + u)) • firstWaveSmoothSeed s c t b := by
    rw [firstWaveHierarchyLeadingVelocity_eval s c freq hr hcell hh hh₁
      (p := (t, a, q)) ⟨hp.1, mem_univ _⟩]
    dsimp only [phaseTwistedPeriodizeCentered, firstWaveLeadingProfile, u, b]
    congr 3
    ring
  rw [funext heq]
  unfold phaseMean
  rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_const_mul]
  rw [show (∫ q in (0 : ℝ)..1, waveProfile h (q + u)) = 0 from shift_phaseMean_waveProfile hh hh₁ u,
    mul_zero, zero_smul]

theorem firstWaveHierarchyLeading_transverse {T s c freq r h : ℝ}
    (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1)
    {p : HierarchyProfilePoint} (hp : p ∈ hierarchyProfileSlab T) :
    ⟪(firstWaveHierarchyCovector (T := T) s freq).val.val.val p,
      (firstWaveHierarchyLeadingVelocity (T := T) s c freq hr hcell hh hh₁).val.val.val p⟫_ℝ = 0 := by
  rw [firstWaveHierarchyCovector_eval s freq hp,
    firstWaveHierarchyLeadingVelocity_eval s c freq hr hcell hh hh₁ hp,
    ← periodicField_eval_centeredLabel (spatiallyPeriodic_firstWaveCovector s freq p.1) p.2.1]
  simp only [phaseTwistedPeriodizeCentered, firstWaveLeadingProfile, real_inner_smul_right,
    inner_firstWaveTransportedCovector_smoothSeed, mul_zero]

/-- The exact wrapped first-wave velocity and pressure form the transverse
leading output for the actual stationary-parent operators. -/
def firstWaveHierarchyLeadingOutput {T s c freq r h : ℝ} (hT : 0 < T) (hf : freq ≠ 0)
    (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) :
    HierarchyTransverseOutput (firstWaveHierarchyOperators hT s freq) where
  V := firstWaveHierarchyLeadingVelocity s c freq hr hcell hh hh₁
  p := firstWaveHierarchyLeadingPressure s c hf hr hcell hh hh₁
  average_V := firstWaveHierarchyLeading_average (s := s) (c := c) (freq := freq) hT hr hcell hh hh₁
  phaseAdv_V w := HierarchyTwistedProfile.phaseAdv_eq_zero_of_transverse hT _ _ _ _ w
    (fun _ hp => firstWaveHierarchyLeading_transverse (s := s) (c := c) (freq := freq) hr hcell hh hh₁ hp)

theorem firstWaveHierarchyLeadingOutput_momentum {T s c freq r h : ℝ} (hT : 0 < T)
    (hf : freq ≠ 0) (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) :
    let A := firstWaveHierarchyOperators hT s freq
    let L := firstWaveHierarchyLeadingOutput (s := s) (c := c) hT hf hr hcell hh hh₁
    A.material L.V + A.phaseGrad L.p = 0 :=
  firstWaveHierarchyLeading_momentum hT hf hr hcell hh hh₁

/-- Evaluating the wrapped first velocity on the stationary-shear phase
graph recovers exactly the centered-periodized physical leading velocity. -/
theorem firstWaveHierarchyLeadingVelocity_graph {T s c freq r h t : ℝ}
    (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1)
    (ht : t ∈ Icc 0 T) (x : Vec3) :
    let a := stationaryShearFlow s (-t) x
    (firstWaveHierarchyLeadingVelocity (T := T) s c freq hr hcell hh hh₁).val.val.val
      (t, a, ⟪firstWaveLaunchCovector freq, a⟫_ℝ) =
      localizedTransportedProfile (fun u => stationaryShearFlow s (-u))
        (firstWaveLaunchCovector freq) (firstWaveLeadingProfile s c r h) t x := by
  dsimp only
  rw [firstWaveHierarchyLeadingVelocity_eval s c freq hr hcell hh hh₁ ⟨ht, mem_univ _⟩]
  exact phaseTwistedPeriodizeCentered_on_graph (fun u => stationaryShearFlow s (-u)) _ _ t x


namespace HierarchyTwistedProfile

variable {T : ℝ} {k : Vec3}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem reflectionParity_of_onSlab {f : HierarchyTwistedProfile T k E} {sign : ℝ}
    (h : ∀ p ∈ hierarchyProfileSlab T,
      f.val.val.val (hierarchyProfileReflection p) = sign • f.val.val.val p) :
    HierarchyProfileReflectionParity sign f.val.val.val := by
  intro p
  by_cases hp : p ∈ hierarchyProfileSlab T
  · exact h p hp
  · rw [HierarchySmoothProfile.eq_zero_outside f.val.val
      (fun h' => hp (hierarchyProfileReflection_mem_slab.mp h')),
      HierarchySmoothProfile.eq_zero_outside f.val.val hp, smul_zero]

private theorem ofGlobalLabelField_reflectionParity {f : ℝ → Vec3 → E}
    (hSmooth : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hPer : ∀ t, SpatiallyPeriodic (f t)) (hEven : ∀ t ∈ Icc 0 T, Function.Even (f t)) :
    HierarchyProfileReflectionParity 1 (ofGlobalLabelField (k := k) f hSmooth hPer).val.val.val := by
  apply reflectionParity_of_onSlab
  intro p hp
  rw [ofGlobalLabelField_eval hSmooth hPer (hierarchyProfileReflection_mem_slab.mpr hp),
    ofGlobalLabelField_eval hSmooth hPer hp, hierarchyProfileReflection_apply, one_smul]
  exact hEven p.1 hp.1 p.2.1

theorem ofWrappedRadial_reflectionParity {f : ℝ → Vec3 → ℝ → E} {r sign : ℝ}
    (hr : 0 < r) (hcell : 2 * r < 1 / 2)
    (hSmooth : ContDiffOn ℝ ∞ (fun p : HierarchyProfilePoint => f p.1 p.2.1 p.2.2)
      (hierarchyProfileSlab T))
    (hPhase : ∀ t a, Function.Periodic (f t a) 1)
    (hReflect : ∀ t ∈ Icc 0 T, ∀ a z, f t (-a) (-z) = sign • f t a z) :
    HierarchyProfileReflectionParity sign
      (ofWrappedRadial (k := k) f hr hcell hSmooth hPhase).val.val.val := by
  apply reflectionParity_of_onSlab
  intro p hp
  rw [ofWrappedRadial_eval hr hcell hSmooth hPhase (hierarchyProfileReflection_mem_slab.mpr hp),
    ofWrappedRadial_eval hr hcell hSmooth hPhase hp, hierarchyProfileReflection_apply]
  exact phaseTwistedPeriodizeCentered_radialEnvelope_neg_equivariant
    (L := sign • ContinuousLinearMap.id ℝ E) hr hcell.le (hReflect p.1 hp.1) p.2.1 p.2.2

end HierarchyTwistedProfile

private theorem even_firstWaveMaterialGradient (s : ℝ) : Function.Even (firstWaveMaterialGradient s) := by
  intro a
  simp only [firstWaveMaterialGradient, PiLp.neg_apply, mul_neg, Real.cos_neg]

theorem firstWaveHierarchyInverseDeformation_reflection {T : ℝ} {k : Vec3} (s : ℝ) :
    HierarchyProfileReflectionParity 1
      (firstWaveHierarchyInverseDeformation (T := T) (k := k) s).val.val.val := by
  apply HierarchyTwistedProfile.ofGlobalLabelField_reflectionParity
  intro t _ a
  simp only [firstWaveInverseDeformation, even_firstWaveMaterialGradient s a]

theorem firstWaveHierarchyMaterialGradient_reflection {T : ℝ} {k : Vec3} (s : ℝ) :
    HierarchyProfileReflectionParity 1
      (firstWaveHierarchyMaterialGradient (T := T) (k := k) s).val.val.val :=
  HierarchyTwistedProfile.ofGlobalLabelField_reflectionParity _ _ (fun _ _ => even_firstWaveMaterialGradient s)

theorem firstWaveHierarchyCovector_reflection {T : ℝ} (s freq : ℝ) :
    HierarchyProfileReflectionParity 1 (firstWaveHierarchyCovector (T := T) s freq).val.val.val :=
  HierarchyTwistedProfile.ofGlobalLabelField_reflectionParity _ _ (fun t _ => even_firstWaveTransportedCovector s freq t)

theorem firstWaveHierarchyLeadingVelocity_reflection {T s c freq r h : ℝ}
    (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) :
    HierarchyProfileReflectionParity (-1)
      (firstWaveHierarchyLeadingVelocity (T := T) s c freq hr hcell hh hh₁).val.val.val := by
  apply HierarchyTwistedProfile.ofWrappedRadial_reflectionParity
  intro t _ a z
  simp only [firstWaveVelocityWithoutEnvelope, even_firstWaveSmoothSeed s c t a,
    odd_waveProfile hh hh₁ z, neg_smul, one_smul]

theorem firstWaveHierarchyLeadingPressure_reflection {T s c freq r h : ℝ} (hf : freq ≠ 0)
    (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) :
    HierarchyProfileReflectionParity 1
      (firstWaveHierarchyLeadingPressure (T := T) s c hf hr hcell hh hh₁).val.val.val := by
  apply HierarchyTwistedProfile.ofWrappedRadial_reflectionParity
  intro t _ a z
  simp only [firstWavePressureWithoutEnvelope, even_firstWaveSmoothSeed s c t a,
    even_firstWaveMaterialGradient s a, even_firstWaveTransportedCovector s freq t a,
    even_wavePressurePrimitive hh hh₁ z, one_smul]

section InitialCrossing

open InnerProductSpace MovingWaveVector

/-- The scheduled half-length bound implies the first-wave shear
smallness for a sufficiently large base frequency. -/
theorem firstWave_stationaryShear_window_small {s T τ μ : ℝ}
    (hs : |s| ≤ 1) (hT₀ : 0 ≤ T) (hT : T ≤ 2 * τ)
    (hτ : τ ≤ μ ^ (-1 / 16 : ℝ))
    (hμ : (64 * Real.pi) ^ (16 : ℕ) ≤ μ) :
    T * ‖stationaryShearGradient s‖ ≤ 1 / 8 := by
  have hπ : 0 < 64 * Real.pi := by positivity
  have h := Real.rpow_le_rpow_of_nonpos (pow_pos hπ 16) hμ (by norm_num : (-1 / 16 : ℝ) ≤ 0)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hπ.le] at h
  norm_num at h
  rw [show (-1 / 16 : ℝ) = -(1 / 16) by ring] at hτ
  rw [Real.rpow_neg hπ.le, Real.rpow_one] at h
  have hτ' : τ ≤ (64 * Real.pi)⁻¹ := hτ.trans h
  calc
    _ ≤ T * (4 * Real.pi) :=
      mul_le_mul_of_nonneg_left (norm_stationaryShearGradient_le hs) hT₀
    _ ≤ (2 * τ) * (4 * Real.pi) := mul_le_mul_of_nonneg_right hT (by positivity)
    _ ≤ (2 * (64 * Real.pi)⁻¹) * (4 * Real.pi) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ' (by norm_num)) (by positivity)
    _ = _ := by field_simp [Real.pi_ne_zero]; ring

/-- At the initial crossing (t_2=t_1=0), the first wave supplies the
coupling ratio and strength required by (T4). -/
theorem FirstWaveOrigin.initial_crossing_bounds {s T freq C L : ℝ}
    (w : FirstWaveOrigin s T freq) (hf : 0 < freq)
    (hsmall : T * ‖stationaryShearGradient s‖ ≤ 1 / 8) (hC : 2 ≤ C) (hL : 1 ≤ L) :
    let ν := entry (frame w.covector w.amplitude 0) (stationaryShearGradient s) 0 1
    let η := entry (frame w.covector w.amplitude 0) (stationaryShearGradient s) 2 1
    let σ := ‖w.covector 0‖ * ‖w.amplitude 0‖
    η / ν = s ∧ Real.pi ≤ ν ∧ ν ≤ 4 * Real.pi ∧
      C⁻¹ * freq ^ (1 / 4 : ℝ) ≤ σ ∧ σ ≤ C * freq ^ (1 / 4 : ℝ) * L ^ 2 := by
  dsimp only
  obtain ⟨hν, hη⟩ := w.initial_couplings hf
  obtain ⟨hlow, hhigh⟩ := w.initial_strength hf hsmall
  have hpower : 0 ≤ freq ^ (1 / 4 : ℝ) := Real.rpow_nonneg hf.le _
  have hC₁ : 1 ≤ C := by linarith
  have hL₂ : 1 ≤ L ^ 2 := one_le_pow₀ hL
  rw [hν, hη]
  refine ⟨?_, by linarith [Real.pi_pos], by linarith [Real.pi_pos], ?_, ?_⟩
  · field_simp [Real.pi_ne_zero]
  · calc
      _ ≤ (2 : ℝ)⁻¹ * freq ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right (inv_anti₀ (by norm_num) hC) hpower
      _ = freq ^ (1 / 4 : ℝ) / 2 := by ring
      _ ≤ _ := hlow
  · exact hhigh.trans ((le_mul_of_one_le_left hpower hC₁).trans
      (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hC₁) hpower) hL₂))

/-- The actual periodized primary wave has the normalized affine pair's
central rank-one gradient at every time of the initial slab. -/
theorem FirstWaveOrigin.hasFDerivAt_localizedLeading_origin {s T freq r h t : ℝ}
    (w : FirstWaveOrigin s T freq) (hf : 0 < freq) (ht : t ∈ Icc 0 T)
    (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) :
    HasFDerivAt
      (localizedTransportedProfile (fun τ => stationaryShearFlow s (-τ))
        (freq • EuclideanSpace.single 0 1) (firstWaveLeadingProfile s w.scale r h) t)
      (rankOne ℝ (w.amplitude t) (w.covector t)) 0 := by
  let G := ContinuousLinearMap.id ℝ Vec3 -
    (t * Real.cos (2 * Real.pi * (0 : Vec3) 1)) • stationaryShearGradient s
  have hA : HasFDerivAt (stationaryShearFlow s (-t)) G (0 : Vec3) := by
    convert hasFDerivAt_stationaryShearFlow s (-t) (0 : Vec3) using 1
    apply ContinuousLinearMap.ext
    intro v
    change v - (t * Real.cos (2 * Real.pi * (0 : Vec3) 1)) • stationaryShearGradient s v =
      v + ((-t) * Real.cos (2 * Real.pi * (0 : Vec3) 1)) • stationaryShearGradient s v
    rw [neg_mul, _root_.neg_smul, sub_eq_add_neg]
  have hSeed : ContDiff ℝ ∞ (firstWaveSmoothSeed s w.scale t) := by
    change ContDiff ℝ ∞ ((Function.uncurry (firstWaveSmoothSeed s w.scale)) ∘
      (fun a => (t, a)))
    exact (contDiff_firstWaveSmoothSeed s w.scale).comp (contDiff_const.prodMk contDiff_id)
  have hd := hasFDerivAt_inductionPrimaryWave_origin
    (chi := fun _ => (1 : ℝ)) (k := freq • EuclideanSpace.single 0 1)
    (a := firstWaveSmoothSeed s w.scale) (A := fun τ => stationaryShearFlow s (-τ))
    hh hh₁ hr hcell hA (stationaryShearFlow_origin s (-t)) (hSeed.differentiable (by simp) 0)
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hk : G.adjoint (freq • EuclideanSpace.single 0 1) = w.covector t :=
    (w.covector_eq_transported hT ht).symm
  have ha : firstWaveSmoothSeed s w.scale t 0 = w.amplitude t :=
    (w.amplitude_eq_smoothSeed hT hf.ne' ht).symm
  unfold firstWaveLeadingProfile
  simpa only [one_mul, one_smul, hk, ha] using hd

/-- The actual completed first wave at time zero has the same exact
rank-one gradient as the normalized affine seed. -/
theorem FirstWaveOrigin.hasFDerivAt_completedVelocity_initial {s T freq r h : ℝ}
    (w : FirstWaveOrigin s T freq) (hf : freq ≠ 0)
    (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) :
    HasFDerivAt (firstWaveLocalizedVelocity s w.scale freq r h 0)
      (rankOne ℝ (w.amplitude 0) (w.covector 0)) 0 := by
  rw [w.amplitude_initial, w.covector_initial]
  exact hasFDerivAt_firstWaveLocalizedVelocity_initial hf hr hcell hh hh₁

set_option maxHeartbeats 650000 in
/-- Specialize the central gradient and the crossing part of (T4) to the
actual first wave over the stationary shear. The approximation remainder
and the Fourier tail use the same derivative budgets as the later stages. -/
theorem FirstWaveOrigin.child_T4_center {s T freq next r h C Cstep L τ : ℝ}
    (w : FirstWaveOrigin s T freq)
    (hfreq : (2 : ℝ) ^ (12 : ℕ) ≤ freq) (hnext : freq ≤ next)
    (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hsmall : T * ‖stationaryShearGradient s‖ ≤ 1 / 8) (hC : 2 ≤ C) (hL : 1 ≤ L)
    (hτ : 0 ≤ τ) (hCstep : Cstep ≤ freq ^ (1 / 32 : ℝ))
    {V child oscRemainder mean tail : Velocity}
    (hV : ∀ t ∈ Icc 0 T, V t = stationaryShear s +
      localizedTransportedProfile (fun u => stationaryShearFlow s (-u))
        (freq • EuclideanSpace.single 0 1) (firstWaveLeadingProfile s w.scale r h) t +
      oscRemainder t + mean t)
    (hChild : ∀ t ∈ Icc 0 T, child t = V t + tail t)
    (hOsc : ∀ t ∈ Icc 0 T, DifferentiableAt ℝ (oscRemainder t) 0)
    (hMean : ∀ t ∈ Icc 0 T, DifferentiableAt ℝ (mean t) 0)
    (hRem : ∀ t ∈ Icc 0 T, ‖fderiv ℝ (oscRemainder t) 0‖ + ‖fderiv ℝ (mean t) 0‖ ≤
      Cstep * freq ^ (-5 / 12 : ℝ))
    (hTail : ∀ t ∈ Icc 0 T, SpatialHolderHalf 2 (tail t) ∧
      spatialHolderHalfNorm 2 (tail t) ≤ next ^ (-5 : ℝ)) :
    let ν := entry (frame w.covector w.amplitude (0 : ℝ)) (stationaryShearGradient s) 0 1
    let η := entry (frame w.covector w.amplitude (0 : ℝ)) (stationaryShearGradient s) 2 1
    let σ := ‖w.covector 0‖ * ‖w.amplitude 0‖
    let Ec (t : ℝ) := fderiv ℝ (oscRemainder t) 0 + fderiv ℝ (mean t) 0 + fderiv ℝ (tail t) 0
    (∀ t ∈ Icc 0 T, fderiv ℝ (child t) 0 = stationaryShearGradient s +
      rankOne ℝ (w.amplitude t) (w.covector t) + Ec t ∧ ‖Ec t‖ ≤ freq ^ (-1 / 4 : ℝ)) ∧
    0 ≤ (0 : ℝ) - 0 ∧ (0 : ℝ) - 0 ≤ τ ∧
    η / ν = s ∧ Real.pi ≤ ν ∧ ν ≤ 4 * Real.pi ∧
      C⁻¹ * freq ^ (1 / 4 : ℝ) ≤ σ ∧ σ ≤ C * freq ^ (1 / 4 : ℝ) * L ^ 2 := by
  have hf₁ : 1 ≤ freq := (by norm_num : (1 : ℝ) ≤ 2 ^ (12 : ℕ)).trans hfreq
  have hf : 0 < freq := zero_lt_one.trans_le hf₁
  let E (t : ℝ) := fderiv ℝ (oscRemainder t) 0 + fderiv ℝ (mean t) 0
  have hParent := (hasFDerivAt_stationaryShear s (0 : Vec3)).differentiableAt
  have hPrimary (t : ℝ) (ht : t ∈ Icc 0 T) :=
    w.hasFDerivAt_localizedLeading_origin hf ht hr hcell hh hh₁
  have hPre (t : ℝ) (ht : t ∈ Icc 0 T) :
      fderiv ℝ (V t) 0 = fderiv ℝ (stationaryShear s) 0 +
        (1 : ℝ) • rankOne ℝ (w.amplitude t) (w.covector t) + E t ∧
      ‖E t‖ ≤ freq ^ (-1 / 3 : ℝ) :=
    induction_approximate_child_center_split hf₁ hCstep (hV t ht) hParent
      (by simpa only [one_smul] using hPrimary t ht) (hOsc t ht) (hMean t ht) (hRem t ht)
  dsimp only
  refine ⟨?_, by simp, by simpa only [sub_self] using hτ, w.initial_crossing_bounds hf hsmall hC hL⟩
  intro t ht
  obtain ⟨hTailReg, hTailSize⟩ := hTail t ht
  have hTailDiff : DifferentiableAt ℝ (tail t) 0 := (hTailReg.1.differentiable (by norm_num)) 0
  have hTailJet := norm_iteratedFDeriv_le_spatialHolderHalfNorm hTailReg (by decide : 1 ≤ 2) 0
  rw [norm_iteratedFDeriv_one] at hTailJet
  have hVDiff : DifferentiableAt ℝ (V t) 0 := by
    rw [hV t ht]
    exact ((hParent.add (hPrimary t ht).differentiableAt).add (hOsc t ht)).add (hMean t ht)
  have hc := induction_child_center_split
    (parent := fun _ => stationaryShear s) (chi := fun _ => (1 : ℝ))
    (a := w.amplitude) (k := w.covector) (E := E)
    ht hfreq hnext (hChild t ht) hVDiff hTailDiff
    (fun u hu => (hPre u hu).1) (hPre t ht).2 (hTailJet.trans hTailSize)
  simpa only [one_smul, E, stationaryShearGradient_origin] using hc


/-- The graph readout used in the hierarchy has the same exact origin
gradient as the normalized first-wave pair. -/
theorem FirstWaveOrigin.hasFDerivAt_hierarchyLeading_origin {s T freq r h t : ℝ}
    (w : FirstWaveOrigin s T freq) (hf : 0 < freq) (ht : t ∈ Icc 0 T)
    (hr : 0 < r) (hcell : 2 * r < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) :
    HasFDerivAt
      (fun x =>
        let a := stationaryShearFlow s (-t) x
        (firstWaveHierarchyLeadingVelocity (T := T) s w.scale freq hr hcell hh hh₁).val.val.val
          (t, a, ⟪firstWaveLaunchCovector freq, a⟫_ℝ))
      (rankOne ℝ (w.amplitude t) (w.covector t)) 0 := by
  have heq : (fun x =>
      let a := stationaryShearFlow s (-t) x
      (firstWaveHierarchyLeadingVelocity (T := T) s w.scale freq hr hcell hh hh₁).val.val.val
        (t, a, ⟪firstWaveLaunchCovector freq, a⟫_ℝ)) =
      localizedTransportedProfile (fun u => stationaryShearFlow s (-u))
        (firstWaveLaunchCovector freq) (firstWaveLeadingProfile s w.scale r h) t :=
    funext (firstWaveHierarchyLeadingVelocity_graph hr hcell hh hh₁ ht)
  rw [heq]
  exact w.hasFDerivAt_localizedLeading_origin hf ht hr hcell hh hh₁

end InitialCrossing

end

end TorusEuler
