import TorusEuler.InductivePhysicalApproximation
import TorusEuler.HierarchyPhysicalInitialSlice
import TorusEuler.InductiveStageVelocityJetBounds
import TorusEuler.LaterPhysicalLeadingInput
import TorusEuler.HierarchyTwistedLeadingSwitch
import TorusEuler.HierarchyPrimaryPressureCenter

/-! Selection of the later wave and its qualitative approximation from a certified prefix. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

open MovingWaveVector LocalizedAmplitude HierarchyTwistedProfile

noncomputable section

variable {P : InductiveEulerParameters} {n : ℕ}

/-- The parent's slab of every exact finite prefix still lies in the initial unit slab. -/
theorem InductiveEulerPrefix.tip_parent_slab_le_one {h : P.LifetimeBounds}
    {p : InductiveEulerTip P n} (prior : InductiveEulerPrefix P h n p) :
    P.slab (n + 1) p.activation ≤ 1 := by
  induction prior with
  | initial b =>
    change 0 + 2 * inductionHalfLength P.frequency 0 ≤ 1
    linarith only [h.first]
  | @append i tip prior step ih =>
    exact (tip.next_slab_lt h).le.trans ih

namespace InductiveEulerTip

variable (p : InductiveEulerTip P n)

local notation "T₊" => P.slab (n + 2) p.nextActivation
local notation "D₊" => P.frequency (n + 1) ^ 9
local notation "λ₊" => P.frequency (n + 2)
local notation "I₊" => Icc (0 : ℝ) T₊
local notation "A₊" => Icc p.nextActivation T₊

/-- The physical comparison uses the actual previous wave and two actual stages. -/
abbrev LaterWindow := LaterPhysicalWindow p.older.velocity p.parent.velocity p.wave.waveVector
  p.wave.amplitude p.wave.error p.nextActivation T₊

/-- The selected crossing uses the next scheduled frequency and gain. -/
abbrev LaterSelection (w : p.LaterWindow) := LaterWaveSelection p.parent.velocity w.physical
  P.comparisonConstant (inductionHalfLength P.frequency (n + 1)) λ₊ (4 * Real.log (P.frequency (n + 4))) D₊

/-- Pull back the selected wave's activation covector to the initial label coordinates. -/
abbrev laterCarrier {w : p.LaterWindow} (s : p.LaterSelection w) : Vec3 :=
  (fderiv ℝ (p.parent.flow 0 p.nextActivation) (0 : Vec3)).adjoint (s.crossing.waveVector p.nextActivation)

local notation "Radius(" a ")" => (D₊ ^ a)⁻¹
local notation "Width" => λ₊ ^ (-1 / 2 : ℝ)
local notation "Slope(" C ")" => amplitudeLabelSlope D₊ (C * D₊ ^ 24) (C * D₊ ^ 24)
  (C * D₊ ^ 24) (C * D₊ ^ 24)

/-- All qualitative inputs for the later wave, with its selected crossing,
label seed and restricted parent tied to the same certified prefix tip. -/
structure SelectedLaterInput (Cenv : ℝ) (a : ℕ) where
  time_pos : 0 < T₊
  time_le_one : T₊ ≤ 1
  radiusExponent_ge_six : 6 ≤ a
  parent_frequency_ge_four : 4 ≤ P.frequency (n + 1)
  window : p.LaterWindow
  selection : p.LaterSelection window
  carrier_nonzero : p.laterCarrier selection ≠ 0
  carrier_transport : EqOn (labelWaveVector p.parent.flow 0 0 (p.laterCarrier selection))
    selection.crossing.waveVector A₊
  carrier_bound : ‖p.laterCarrier selection‖ ≤ D₊ * λ₊
  parent : p.parent.OnSlab time_pos (p.laterCarrier selection)
  seed : SeedOn (fun t x => fderiv ℝ (p.parent.velocity t) (p.parent.flow 0 t x))
    (fun t x => labelWaveVector p.parent.flow 0 x (p.laterCarrier selection) t)
    selection.crossing.amplitude p.nextActivation T₊ (Radius(a)) D₊ (Slope(Cenv))
  regularity : seed.HierarchyRegularity window.physical.rate Width
  seed_even : ∀ t ∈ A₊, Function.Even (seed.amplitude t)

namespace SelectedLaterInput

variable {p} {Cenv : ℝ} {a : ℕ} (d : p.SelectedLaterInput Cenv a)

abbrev carrier : Vec3 := p.laterCarrier d.selection

abbrev radius (_input : p.SelectedLaterInput Cenv a) : ℝ := Radius(a)

abbrev width (_input : p.SelectedLaterInput Cenv a) : ℝ := Width

abbrev leading : PhysicalLeadingInput d.parent.geometry :=
  PhysicalLeadingInput.ofLaterWave d.parent.geometry d.seed d.regularity d.parent.deformationOn.flow
    d.parent.smooth_velocity (fun t _ => p.parent.periodic_velocity t)
    (fun t ht => p.parent.odd_velocity t (d.parent.subset ht)) d.seed_even

abbrev depth (_input : p.SelectedLaterInput Cenv a) : ℕ :=
  6 * frequencyExponent P.exponentParameter (P.order (n + 3))

/-- The actual approximation at the scheduled retained depth. -/
def approximation : PhysicalApproximationData d.parent.geometry p.parent.pressure d.depth :=
  d.parent.physicalApproximationData d.time_le_one d.leading d.depth

theorem depth_ge_two : 2 ≤ d.depth := by
  have hb : 0 < P.exponentParameter := P.exponentParameter_ge
  have hPositive : 0 < frequencyExponent P.exponentParameter (P.order (n + 3)) := by
    unfold frequencyExponent
    positivity
  change 2 ≤ 6 * frequencyExponent P.exponentParameter (P.order (n + 3))
  omega

/-- The selected input already supplies all exact qualitative cutoff premises. -/
theorem properties : PhysicalApproximationProperties d.approximation :=
  d.parent.physicalApproximationProperties d.time_le_one d.leading d.depth_ge_two

/-- The wrapped wave and both switch sources have the same closed support envelope. -/
theorem leading_inactive : d.leading.Inactive p.nextActivation
    (tsupport (periodizeCentered (radialEnvelope d.radius))) :=
  PhysicalLeadingInput.ofLaterWave_inactive d.parent.geometry d.seed d.regularity
    d.parent.deformationOn.flow d.parent.smooth_velocity (fun t _ => p.parent.periodic_velocity t)
    (fun t ht => p.parent.odd_velocity t (d.parent.subset ht)) d.seed_even
    (isClosed_tsupport _) (subset_tsupport _)

/-- The normalized phase pressure belongs to the same selected leading wave. -/
theorem leading_pressure_phaseMean (t : ℝ) (ht : t ∈ I₊) (x : Vec3) :
    phaseMean (fun s => d.leading.output.p.val.val.val (t, x, s)) = 0 :=
  d.seed.twistedPressure_phaseMean_zero d.regularity d.carrier ht x

/-- The selected activation force has zero phase average. -/
theorem leadingSwitch_average : d.approximation.operators.average d.leading.leadingSwitch = 0 :=
  d.seed.twistedLeadingSwitch_average_zero d.regularity d.carrier

/-- The selected activation force is transverse on the full profile slab. -/
theorem leadingSwitch_transverse (z : HierarchyProfilePoint) (hz : z ∈ hierarchyProfileSlab T₊) :
    ⟪d.parent.geometry.covector.val.val.val z, d.leading.leadingSwitch.val.val.val z⟫_ℝ = 0 :=
  d.seed.twistedLeadingSwitch_transverse d.regularity d.parent.geometry.covector
    d.parent.geometry.covector_value z hz

/-- The activation completion is the same curl operator as in the finite hierarchy. -/
theorem completionSwitch_eq_complete :
    d.leading.completionSwitch = d.approximation.solvers.complete d.leading.leadingSwitch := rfl

/-- At the activation time, the selected leading velocity is zero at every label and phase. -/
theorem leading_eq_zero_through_activation (t : ℝ) (ht : t ∈ I₊) (ht₀ : t ≤ p.nextActivation)
    (x : Vec3) (s : ℝ) : d.leading.output.V.val.val.val (t, x, s) = 0 :=
  d.seed.twistedLeading_before_activation d.regularity d.carrier ht ht₀ x s

/-- The correction vanishes through the activation time, including stage two. -/
theorem oscillation_vanishes (t : ℝ) (ht : t ∈ Icc 0 p.nextActivation) : d.approximation.oscillation t = 0 := by
  have ht₀ : p.nextActivation ≤ T₊ := d.regularity.start_lt_end.le
  funext x
  exact d.approximation.oscillation_eq_zero_through_nonnegative_activation
    ((by decide : 1 ≤ 2).trans d.depth_ge_two) (isClosed_tsupport _) p.next_activation_nonnegative
    d.leading_inactive (fun _ a s => d.leading_eq_zero_through_activation 0
      (left_mem_Icc.mpr d.time_pos.le) p.next_activation_nonnegative a s)
    ⟨ht.1, ht.2.trans ht₀⟩ x (Or.inl ht.2)

include d in
theorem parent_frequency_ge_two : 2 ≤ P.frequency (n + 1) :=
  (by norm_num : (2 : ℝ) ≤ 4).trans d.parent_frequency_ge_four

include d in
theorem parent_frequency_le_scale : P.frequency (n + 1) ≤ D₊ := by
  have hμ₁ := (by norm_num : (1 : ℝ) ≤ 2).trans d.parent_frequency_ge_two
  simpa only [pow_one] using pow_le_pow_right₀ hμ₁ (by decide : (1 : ℕ) ≤ 9)

include d in
theorem parent_scale_ge_two : 2 ≤ D₊ :=
  d.parent_frequency_ge_two.trans d.parent_frequency_le_scale

/-- The actual flat envelope is the negative power used in the stage budget. -/
theorem radius_eq_rpow : d.radius = D₊ ^ (-(a : ℝ)) := by
  change (D₊ ^ a)⁻¹ = D₊ ^ (-(a : ℝ))
  rw [Real.rpow_neg ((by norm_num : (0 : ℝ) ≤ 2).trans d.parent_scale_ge_two), Real.rpow_natCast]

theorem radius_inv : d.radius⁻¹ = D₊ ^ a := inv_inv _

/-- Every power of the coframe scale through the chosen envelope exponent is absorbed. -/
theorem radius_mul_parent_power {j : ℕ} (hj : j ≤ a) : d.radius * D₊ ^ j ≤ 1 := by
  have hD := (by norm_num : (1 : ℝ) ≤ 2).trans d.parent_scale_ge_two
  have hPow : 0 < D₊ ^ j := pow_pos (zero_lt_one.trans_le hD) j
  have hRadius : d.radius ≤ (D₊ ^ j)⁻¹ := inv_anti₀ hPow (pow_le_pow_right₀ hD hj)
  exact (mul_le_mul_of_nonneg_right hRadius hPow.le).trans_eq (inv_mul_cancel₀ hPow.ne')

/-- The chosen envelope gives the exact lattice-distance bound in T4. -/
theorem oscillation_support (t : ℝ) (ht : t ∈ I₊) (x : Vec3)
    (hx : d.approximation.oscillation t x ≠ 0) :
    ∃ z : Fin 3 → ℤ, dist (latticeVector z) x ≤ (P.frequency (n + 1))⁻¹ := by
  have hD := (by norm_num : (1 : ℝ) ≤ 2).trans d.parent_scale_ge_two
  have hRadius : d.radius ≤ (D₊ ^ (3 : ℕ))⁻¹ :=
    inv_anti₀ (pow_pos (zero_lt_one.trans_le hD) _) (pow_le_pow_right₀ hD
      ((by decide : 3 ≤ 6).trans d.radiusExponent_ge_six))
  exact d.parent.physicalApproximation_oscillation_support d.time_le_one d.leading
    ((by decide : 1 ≤ 2).trans d.depth_ge_two) d.regularity.envelope_pos
    d.parent_frequency_ge_two d.parent_frequency_le_scale hRadius d.leading_inactive t ht x hx

/-- The physical contribution of the higher oscillations and mean to the
central gradient of the actual approximate field. -/
def centralError (t : ℝ) : Vec3 →L[ℝ] Vec3 :=
  fderiv ℝ (d.approximation.oscillationRemainder t) 0 + fderiv ℝ (d.approximation.meanCorrection t) 0

/-- Differentiating the actual Eulerian hierarchy at the center gives the
selected wave term and the exact two-profile error. -/
theorem gradient_split (t : ℝ) (ht : t ∈ A₊) :
    fderiv ℝ (d.approximation.velocity t) 0 = fderiv ℝ (p.parent.velocity t) 0 +
      waveSwitch p.nextActivation d.window.physical.rate t •
        InnerProductSpace.rankOne ℝ (d.selection.crossing.amplitude t) (d.selection.crossing.waveVector t) +
      d.centralError t := by
  let b := d.approximation
  have htSlab : t ∈ I₊ := ⟨p.next_activation_nonnegative.trans ht.1, ht.2⟩
  have hper (r : ℝ) (_ : r ∈ I₊) : SpatiallyPeriodic (p.parent.velocity r) := p.parent.periodic_velocity r
  have hodd (r : ℝ) (hr : r ∈ I₊) : Function.Odd (p.parent.velocity r) := p.parent.odd_velocity r (d.parent.subset hr)
  have hSlice {U : Velocity}
      (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (I₊ ×ˢ (univ : Set Vec3))) :
      DifferentiableAt ℝ (U t) 0 := by
    have hSmooth : ContDiff ℝ ∞ (U t) := contDiffOn_univ.mp
      (hU.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun x _ => ⟨htSlab, mem_univ x⟩)
    exact hSmooth.differentiable (by simp) 0
  have hL : HasFDerivAt (b.leadingVelocity t)
      (waveSwitch p.nextActivation d.window.physical.rate t • InnerProductSpace.rankOne ℝ
        (d.selection.crossing.amplitude t) (labelWaveVector p.parent.flow 0 0 d.carrier t)) 0 :=
    SeedOn.hasFDerivAt_twistedLeading_parentGraph_origin d.regularity d.parent.deformationOn.flow
      d.parent.smooth_velocity hper hodd htSlab
  rw [d.carrier_transport ht] at hL
  have hOsc := hSlice (b.oscillationRemainder_smooth d.parent.deformationOn.flow d.parent.smooth_velocity hper)
  have hMean := hSlice d.properties.mean_smooth
  have hSplit := congrFun (b.velocity_eq_parent_add_leading_add_remainder_add_mean
    ((by decide : 1 ≤ 2).trans d.depth_ge_two)) t
  have hD := ((((hSlice d.parent.smooth_velocity).hasFDerivAt.add hL).add hOsc.hasFDerivAt).add
    hMean.hasFDerivAt).fderiv
  rw [show d.approximation.velocity t = p.parent.velocity t + b.leadingVelocity t + b.oscillationRemainder t +
    b.meanCorrection t from hSplit]
  change fderiv ℝ (p.parent.velocity t + b.leadingVelocity t + b.oscillationRemainder t + b.meanCorrection t) 0 = _
  rw [hD]
  unfold centralError
  abel

/-- The actual selected pair has the coupling ratio and bounds supplied by the prefix. -/
theorem crossing_coupling {h : P.LifetimeBounds}
    (prior : InductiveEulerPrefix P h n p) (hLarge : Real.exp 4 ≤ P.frequency 0) :
    let t := d.selection.crossing.crossing
    let E := frame d.selection.crossing.waveVector d.selection.crossing.amplitude t
    let M := fderiv ℝ (p.parent.velocity t) 0
    Real.pi ≤ entry E M 0 1 ∧ entry E M 0 1 ≤ 4 * Real.pi ∧
      entry E M 2 1 / entry E M 0 1 = couplingRatioOfGain (4 * Real.log (P.frequency (n + 4))) :=
  prior.later_wave_exit_coupling hLarge d.window d.selection

/-- The common strength constant applies to the actual selected pair at its crossing. -/
theorem strength_at_crossing (hBase : Real.exp 1 ≤ P.frequency 0)
    (hC : 18 * Real.exp 3 ≤ P.strengthConstant) :
    let t := d.selection.crossing.crossing
    let σ := ‖d.selection.crossing.waveVector t‖ * ‖d.selection.crossing.amplitude t‖
    P.strengthConstant⁻¹ * λ₊ ^ (1 / 4 : ℝ) ≤ σ ∧
      σ ≤ P.strengthConstant * λ₊ ^ (1 / 4 : ℝ) * (4 * Real.log (P.frequency (n + 4))) ^ 2 := by
  let w := d.window
  let s := d.selection
  have hbase : 1 < P.frequency 0 := (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hBase
  have hmono := frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency
    P.exponentParameter_ge hbase.le P.frequency_step
  obtain ⟨_,hLogL,hStep,_⟩ := frequencySchedule_laterWindow_gains
    P.exponentParameter P.order P.threshold P.frequency P.exponentParameter_ge P.initial_order
    P.initial_threshold hbase P.frequency_step P.order_maximum P.threshold_pos P.threshold_floor n
  have hL : 1 ≤ 4 * Real.log (P.frequency (n + 3)) := by
    have hlog := Real.log_le_log (Real.exp_pos 1) (hBase.trans (hmono (Nat.zero_le (n + 1))))
    rw [Real.log_exp] at hlog
    exact hlog.trans hLogL
  have hScale : 0 < λ₊ := (zero_lt_one.trans hbase).trans_le (hmono (Nat.zero_le (n + 2)))
  have hRatio : w.physical.ratio = couplingRatioOfGain (4 * Real.log (P.frequency (n + 3))) := by
    unfold PhysicalAmplification.ratio PhysicalAmplification.thirdCoupling
      PhysicalAmplification.firstCoupling PhysicalAmplification.basis
    rw [w.preceding_vector_eq, w.preceding_amplitude_eq, w.older_gradient_eq]
    exact p.wave.ratio_at_crossing
  have hBounds (peak : ℝ) (hpeak : peak = λ₊ ^ (-(3 / 4 : ℝ)))
      (crossing : w.physical.GrowingCrossing s.window λ₊ peak
        (couplingRatioOfGain (4 * Real.log (P.frequency (n + 4))))) :
      (Real.exp (-1) / 4) * λ₊ ^ (1 / 4 : ℝ) ≤
        ‖crossing.waveVector crossing.crossing‖ * ‖crossing.amplitude crossing.crossing‖ ∧
      ‖crossing.waveVector crossing.crossing‖ * ‖crossing.amplitude crossing.crossing‖ ≤
        (18 * Real.exp 3) * λ₊ ^ (1 / 4 : ℝ) * (4 * Real.log (P.frequency (n + 4))) ^ 2 := by
    subst peak
    exact PhysicalAmplification.GrowingCrossing.strength_bounds_for_next hScale hL hStep hRatio crossing
  obtain ⟨hl,hu⟩ := hBounds _ (by rw [neg_div]) s.crossing
  have hInv : P.strengthConstant⁻¹ ≤ Real.exp (-1) / 4 :=
    (inv_anti₀ (by positivity : 0 < (18 : ℝ) * Real.exp 3) hC).trans inductionCrossingStrengthConstants.2
  exact ⟨(mul_le_mul_of_nonneg_right hInv (by positivity)).trans hl,
    hu.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) (sq_nonneg _))⟩

end SelectedLaterInput

set_option maxHeartbeats 1600000 in
/-- A common initial threshold selects the actual later wave, its launch
coframe, its local seed and the same parent residual for every prefix. -/
theorem exists_selectedLaterInput_threshold (C : ℝ) (hC : 2 ≤ C) :
    ∃ (C₀ : ℕ) (N Cenv : ℝ) (A : ℕ), 240 ≤ C₀ ∧ 4 ≤ N ∧ 0 ≤ Cenv ∧ 6 ≤ A ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} (p : InductiveEulerTip P n) {h : P.LifetimeBounds},
        InductiveEulerPrefix P h n p → N ≤ P.frequency 0 → P.strengthConstant = C →
        P.comparisonConstant = C₀ → ∀ a : ℕ, A ≤ a → Nonempty (p.SelectedLaterInput Cenv a) := by
  obtain ⟨C₀,Nwave,hC₀,_,hWave⟩ := exists_inductiveEulerTip_laterWave_threshold C hC
  obtain ⟨Nparent,hNparent,hParent⟩ := InductiveEulerStage.exists_onSlab_threshold
  obtain ⟨R,hR,hJet⟩ := InductiveEulerStage.exists_velocity_jet_bounds
  obtain ⟨Ngrad,_,hGrad⟩ := InductiveEulerStage.exists_velocity_gradient_bound
  obtain ⟨Cenv,A,hCenv,_,hSeed⟩ := exists_seedOn_of_parent_bounds R hR
  let N := max Nparent (max Nwave Ngrad)
  refine ⟨C₀, N, Cenv, max 6 A, hC₀, hNparent.trans (le_max_left _ _), hCenv, le_max_left _ _, ?_⟩
  intro P n p h prior hBase hStrength hComparison a ha
  let T := P.slab (n + 2) p.nextActivation
  let D := P.frequency (n + 1) ^ 9
  let freq := P.frequency (n + 2)
  let radius (j : ℕ) := (D ^ j)⁻¹
  have hBase4 : 4 ≤ P.frequency 0 := hNparent.trans ((le_max_left _ _).trans hBase)
  have hmono := frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency
    P.exponentParameter_ge ((by norm_num : (1 : ℝ) ≤ 4).trans hBase4) P.frequency_step
  have hμ : 4 ≤ P.frequency (n + 1) := hBase4.trans (hmono (Nat.zero_le _))
  have hμ₁ : 1 ≤ P.frequency (n + 1) := (by norm_num : (1 : ℝ) ≤ 4).trans hμ
  have hf : 1 ≤ freq := hμ₁.trans (hmono (by omega : n + 1 ≤ n + 2))
  have hfp : 0 < freq := zero_lt_one.trans_le hf
  have hT : 0 < T := p.next_slab_pos h
  have hTold : T ≤ P.slab (n + 1) p.activation := (p.next_slab_lt h).le
  have hT₁ : T ≤ 1 := hTold.trans prior.tip_parent_slab_le_one
  have ht₀T : p.nextActivation < T := by
    change p.nextActivation < p.nextActivation + 2 * inductionHalfLength P.frequency (n + 1)
    linarith only [(h.step (n + 1)).1]
  have ht₀ : p.nextActivation ∈ (Icc 0 T) := ⟨p.next_activation_nonnegative, ht₀T.le⟩
  have hsub : (Icc 0 T) ⊆ Icc 0 (P.slab (n + 1) p.activation) := Icc_subset_Icc_right hTold
  have hX : IsLabelFlowOn p.parent.velocity p.parent.flow (Icc 0 T) := p.parent.deformation.flow.mono hsub
  have hU : ContDiffOn ℝ ∞ (Function.uncurry p.parent.velocity) ((Icc 0 T) ×ˢ (univ : Set Vec3)) :=
    p.parent.smooth_velocity.mono (prod_mono_left hsub)
  have hper (t : ℝ) (_ : t ∈ (Icc 0 T)) : SpatiallyPeriodic (p.parent.velocity t) := p.parent.periodic_velocity t
  have hodd (t : ℝ) (ht : t ∈ (Icc 0 T)) : Function.Odd (p.parent.velocity t) := p.parent.odd_velocity t (hsub ht)
  obtain ⟨w,⟨s⟩⟩ := hWave p h (((le_max_left Nwave Ngrad).trans (le_max_right _ _)).trans hBase)
    hStrength hComparison
  have hμD : P.frequency (n + 1) ≤ D := by
    simpa only [pow_one] using pow_le_pow_right₀ hμ₁ (by decide : (1 : ℕ) ≤ 9)
  have hD : 2 ≤ D := ((by norm_num : (2 : ℝ) ≤ 4).trans hμ).trans hμD
  have hF (t : ℝ) (ht : t ∈ (Icc 0 T)) (x : Vec3) : ‖fderiv ℝ (p.parent.flow 0 t) x‖ ≤ D :=
    ((p.parent.deformation.bounds t (hsub ht)).2.1 x).2.trans hμD
  have hG (t : ℝ) (ht : t ∈ (Icc 0 T)) (x : Vec3) : ‖fderiv ℝ (p.parent.flow t 0) (p.parent.flow 0 t x)‖ ≤ D :=
    ((p.parent.deformation.bounds t (hsub ht)).2.2 (p.parent.flow 0 t x)).2.trans hμD
  have hNg : Ngrad ≤ P.frequency (n + 1) :=
    (((le_max_right Nwave Ngrad).trans (le_max_right _ _)).trans hBase).trans (hmono (Nat.zero_le _))
  have hM (t : ℝ) (ht : t ∈ (Icc 0 T)) (x : Vec3) : ‖fderiv ℝ (p.parent.velocity t) x‖ ≤ D :=
    hGrad p.parent hNg t (hsub ht) x
  have hLaunch := s.crossing.launch_geometry hfp
  have hKexpr : p.laterCarrier s = freq • (fderiv ℝ (p.parent.flow 0 p.nextActivation) (0 : Vec3)).adjoint
      (w.physical.basis p.nextActivation 2) := by
    simp only [laterCarrier, hLaunch.1, map_smul, freq]
  have hTransport := s.crossing.transport_launch_covector hX hT (hU.of_le (by simp)) hper hodd ht₀
    s.clock_eq w.parent_gradient_eq
  dsimp only at hTransport
  rw [← hKexpr] at hTransport
  have hKnorm : ‖p.laterCarrier s‖ ≤ D * freq := by
    unfold laterCarrier
    calc
      _ ≤ ‖(fderiv ℝ (p.parent.flow 0 p.nextActivation) (0 : Vec3)).adjoint‖ *
          ‖s.crossing.waveVector p.nextActivation‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ D * freq := by
        rw [hLaunch.2.1, ContinuousLinearMap.adjoint.norm_map]
        exact mul_le_mul_of_nonneg_right (hF _ ht₀ _) hfp.le
  obtain ⟨parent⟩ := hParent P ((le_max_left _ _).trans hBase) p.parent hT hTold hTransport.1
  have hD₁ : 1 ≤ D := (by norm_num : (1 : ℝ) ≤ 2).trans hD
  have hEll : 0 < radius a := inv_pos.mpr (pow_pos (zero_lt_one.trans_le hD₁) _)
  have hRadius (j : ℕ) (hj : j ≤ a) : radius a ≤ radius j :=
    inv_anti₀ (pow_pos (zero_lt_one.trans_le hD₁) _) (pow_le_pow_right₀ hD₁ hj)
  have ha₆ : 6 ≤ a := (le_max_left _ _).trans ha
  have haA : A ≤ a := (le_max_right _ _).trans ha
  have hEllFit : 2 * radius a < 1 / 2 := by
    have hCube : (2 : ℝ) ^ 3 ≤ D ^ 3 := pow_le_pow_left₀ zero_le_two hD _
    have hEighth : radius a ≤ (1 / 8 : ℝ) := (hRadius 3 (by omega)).trans (by
      simpa only [show ((2 : ℝ) ^ 3)⁻¹ = 1 / 8 by norm_num] using
        inv_anti₀ (by norm_num : (0 : ℝ) < (2 : ℝ) ^ 3) hCube)
    linarith only [hEighth]
  obtain ⟨seed⟩ := hSeed hT hT₁ ht₀ hD hX hU hper hodd hF hG hM
    (fun j k h₁ hj t ht x => hJet p.parent hμ₁ j k h₁ hj t (hsub ht) x) s.center hEll (hRadius A haA)
  obtain ⟨reg,hEven,_,_⟩ := SeedOn.hierarchyRegularity_of_parent p.next_activation_nonnegative ht₀T
    hX hU hper hodd hTransport.1 seed w.physical.rate_pos.le hEll hEllFit
    (Real.rpow_pos_of_pos hfp _) (Real.rpow_le_one_of_one_le_of_nonpos hf (by norm_num : (-1 / 2 : ℝ) ≤ 0))
  exact ⟨{
    time_pos := hT
    time_le_one := hT₁
    radiusExponent_ge_six := ha₆
    parent_frequency_ge_four := hμ
    window := w
    selection := s
    carrier_nonzero := hTransport.1
    carrier_transport := hTransport.2
    carrier_bound := hKnorm
    parent := parent
    seed := seed
    regularity := reg
    seed_even := hEven }⟩

end InductiveEulerTip

end

end TorusEuler
