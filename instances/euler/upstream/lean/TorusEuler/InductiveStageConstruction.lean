import TorusEuler.BaseParentData
import TorusEuler.ChildFlowDeformation
import TorusEuler.InductionCumulativeCouplings
import TorusEuler.LaterPhysicalAmplification
import TorusEuler.LocalizedAmplitudeComparison
import TorusEuler.Theorem11FromInductiveStages

/-! Dependent prefixes for the frozen Euler stage construction. -/

open Filter MeasureTheory Set UnitAddTorus
open scoped BigOperators ContDiff InnerProductSpace Topology

namespace TorusEuler

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)

open MovingWaveVector (PhysicalAmplification LaterPhysicalWindow LaterWaveSelection frame entry)
open ChildFlow (DeformationOn)
open LocalizedAmplitude (CenterWaveOn)

/-- The prescribed spatial schedule and constants stay fixed along every prefix. -/
structure InductiveEulerParameters where
  exponentParameter : ℕ
  threshold : ℕ → ℝ
  order : ℕ → ℕ
  frequency : ℕ → ℝ
  exponentParameter_ge : 1 ≤ exponentParameter
  initial_order : order 1 = 1
  initial_threshold : threshold 1 ≤ frequency 0
  frequency_step : ∀ i, frequency (i + 1) = frequency i ^ frequencyExponent exponentParameter (order (i + 1))
  order_maximum : ∀ i, IsGreatest {s | 1 ≤ s ∧ s ≤ order (i + 1) + 1 ∧ threshold s ≤ frequency i}
    (order (i + 2))
  threshold_pos : ∀ s, 1 ≤ s → 0 < threshold s
  threshold_floor : ∀ s, 1 ≤ s →
    4 * (frequencyExponent exponentParameter (s + 1) : ℝ) ^ 3 ≤ Real.log (threshold s)
  strengthConstant : ℝ
  strengthConstant_ge : 2 ≤ strengthConstant
  comparisonConstant : ℕ
  comparisonConstant_ge : 240 ≤ comparisonConstant

namespace InductiveEulerParameters

/-- The endpoint time of stage `n` is fixed once its activation time is known. -/
def slab (P : InductiveEulerParameters) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, t => t + 2 * inductionHalfLength P.frequency n

@[simp] theorem slab_zero (P : InductiveEulerParameters) (t : ℝ) : P.slab 0 t = 1 := rfl

@[simp] theorem slab_succ (P : InductiveEulerParameters) (n : ℕ) (t : ℝ) :
    P.slab (n + 1) t = t + 2 * inductionHalfLength P.frequency n := rfl

/-- The arithmetic estimates on the half lengths in (7.7). -/
structure LifetimeBounds (P : InductiveEulerParameters) : Prop where
  first : inductionHalfLength P.frequency 0 ≤ 1 / 4
  step : ∀ j, 0 < inductionHalfLength P.frequency j ∧
    inductionHalfLength P.frequency j ≤ P.frequency j ^ (-1 / 16 : ℝ) ∧
    4 * inductionHalfLength P.frequency (j + 1) ≤ inductionHalfLength P.frequency j

/-- A sufficiently large initial frequency ensures the required endpoint nesting. -/
theorem exists_lifetime_threshold : ∃ N : ℝ, ∀ P : InductiveEulerParameters,
    N ≤ P.frequency 0 → P.LifetimeBounds := by
  obtain ⟨N, hN⟩ := frequencySchedule_halfLength_bounds
  refine ⟨max N ((4 : ℝ) ^ (16 : ℕ)), fun P hP => ?_⟩
  have h := hN P.exponentParameter P.order P.threshold P.frequency P.exponentParameter_ge P.initial_order
    P.initial_threshold ((le_max_left _ _).trans hP) P.frequency_step P.order_maximum
    P.threshold_pos P.threshold_floor
  exact ⟨inductionHalfLength_zero_le_quarter ((le_max_right _ _).trans hP) (h 0).2.1, h⟩

end InductiveEulerParameters

open InductiveEulerParameters

/-- The physical velocity, normalized pressure, and actual two-time flow of one stage.
The residual is the physical momentum residual for that pressure. -/
structure InductiveEulerStage (P : InductiveEulerParameters) (n : ℕ) (activation : ℝ) where
  torusVelocity : ℝ → C(Labels, Vec3)
  pressure : Pressure
  flow : ℝ → Velocity
  smooth_velocity : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => torusVelocity z.1 (toUnitTorus z.2))
    (Icc 0 (P.slab n activation) ×ˢ (univ : Set Vec3))
  odd_velocity : ∀ t ∈ Icc 0 (P.slab n activation), Function.Odd (fun x => torusVelocity t (toUnitTorus x))
  divergence_free : ∀ t ∈ Icc 0 (P.slab n activation), ∀ x,
    divergence (fun y => torusVelocity t (toUnitTorus y)) x = 0
  velocity_band : ∀ t ∈ Icc 0 (P.slab n activation), RealTorusFourierBand (2 * P.frequency n ^ 5) (torusVelocity t)
  velocity_bound : ∀ t ∈ Icc 0 (P.slab n activation), ‖torusVelocity t‖ ≤ P.frequency n
  smooth_pressure : ContDiffOn ℝ ∞ (Function.uncurry pressure) (Icc 0 (P.slab n activation) ×ˢ (univ : Set Vec3))
  periodic_pressure : ∀ t ∈ Icc 0 (P.slab n activation), SpatiallyPeriodic (pressure t)
  mean_zero_pressure : ∀ t ∈ Icc 0 (P.slab n activation), (∫ x in centeredCell, pressure t x) = 0
  poisson : ∀ t ∈ Icc 0 (P.slab n activation), ∀ x, divergence (gradient (pressure t)) x =
    -LinearMap.trace ℝ Vec3 ((fderiv ℝ (fun y => torusVelocity t (toUnitTorus y)) x).comp
      (fderiv ℝ (fun y => torusVelocity t (toUnitTorus y)) x)).toLinearMap
  projected_eq : ∀ t ∈ Icc 0 (P.slab n activation),
    momentumResidual (Icc 0 (P.slab n activation)) (fun r x => torusVelocity r (toUnitTorus x)) pressure t =
      closedSlabLerayMomentum 0 (P.slab n activation) (fun r x => torusVelocity r (toUnitTorus x)) t
  residual_bound : ∀ t ∈ Icc 0 (P.slab n activation), ∀ x,
    ‖momentumResidual (Icc 0 (P.slab n activation)) (fun r y => torusVelocity r (toUnitTorus y)) pressure t x‖ ≤
      ((P.frequency (n + 1))⁻¹)^3
  deformation : DeformationOn (fun t x => torusVelocity t (toUnitTorus x)) flow (P.slab n activation) (P.frequency n)
  pressure_hessian : ∀ t ∈ Icc 0 (P.slab n activation), ∀ x v : Vec3,
    ⟪v, fderiv ℝ (gradient (pressure t)) x v⟫_ℝ ≤ (∑ i ∈ Finset.range n, (P.frequency i)⁻¹) * ‖v‖ ^ 2

namespace InductiveEulerStage

variable {P : InductiveEulerParameters} {n : ℕ} {activation : ℝ}

/-- The velocity on the Euclidean lift of the torus. -/
def velocity (s : InductiveEulerStage P n activation) : Velocity :=
  fun t x => s.torusVelocity t (toUnitTorus x)

/-- The residual of the physical momentum equation. -/
def residual (s : InductiveEulerStage P n activation) : Velocity :=
  momentumResidual (Icc 0 (P.slab n activation)) s.velocity s.pressure

theorem periodic_velocity (s : InductiveEulerStage P n activation) (t : ℝ) :
    SpatiallyPeriodic (s.velocity t) := by
  intro k x
  exact congrArg (s.torusVelocity t) ((toUnitTorus_eq_iff _ _).mpr ⟨k, rfl⟩)

end InductiveEulerStage

/-- The certified increment from one physical stage to its child, with the
child wave's exit data evaluated at the activation it selects. -/
structure InductiveEulerWave (P : InductiveEulerParameters) (n : ℕ)
    {tOld t : ℝ} (parent : InductiveEulerStage P n tOld)
    (child : InductiveEulerStage P (n + 1) t) (next : ℝ) where
  oscillation : Velocity
  waveVector : ℝ → Vec3
  amplitude : ℝ → Vec3
  cutoff : ℝ → ℝ
  error : ℝ → Vec3 →L[ℝ] Vec3
  center : CenterWaveOn (fun r => fderiv ℝ (parent.velocity r) 0) waveVector amplitude t
    (P.slab (n + 1) t) (P.frequency n ^ 9)
  activation_step : 0 ≤ next - t ∧ next - t ≤ inductionHalfLength P.frequency n
  oscillation_bound : ∀ r ∈ Icc 0 (P.slab (n + 1) t), ∀ x, ‖oscillation r x‖ ≤ (P.frequency (n + 1))⁻¹
  correction_bound : ∀ m ≤ P.order (n + 1), ∀ r ∈ Icc 0 (P.slab (n + 1) t),
    let v := child.velocity r - parent.velocity r - oscillation r
    SpatialHolderHalf m v ∧ spatialHolderHalfNorm m v ≤ (P.frequency (n + 1))⁻¹
  oscillation_vanishes : 2 ≤ n + 1 → ∀ r ∈ Icc 0 t, oscillation r = 0
  oscillation_support : ∀ r ∈ Icc 0 (P.slab (n + 1) t), ∀ x, oscillation r x ≠ 0 →
    ∃ z : Fin 3 → ℤ, dist (latticeVector z) x ≤ (P.frequency n)⁻¹
  gradient_split : ∀ r ∈ Icc t (P.slab (n + 1) t),
    fderiv ℝ (child.velocity r) 0 = fderiv ℝ (parent.velocity r) 0 +
      cutoff r • (innerSL ℝ (waveVector r)).smulRight (amplitude r) + error r
  error_bound : ∀ r ∈ Icc t (P.slab (n + 1) t), ‖error r‖ ≤ P.frequency (n + 1) ^ (-1 / 4 : ℝ)
  cutoff_complete : ∀ r ∈ Icc next (P.slab (n + 1) t), cutoff r = 1
  strength_at_crossing :
    P.strengthConstant⁻¹ * P.frequency (n + 1) ^ (1 / 4 : ℝ) ≤ ‖waveVector next‖ * ‖amplitude next‖ ∧
    ‖waveVector next‖ * ‖amplitude next‖ ≤
      P.strengthConstant * P.frequency (n + 1) ^ (1 / 4 : ℝ) * (4 * Real.log (P.frequency (n + 3))) ^ 2
  coupling_at_crossing :
    let ν := entry (frame waveVector amplitude next) (fderiv ℝ (parent.velocity next) 0) 0 1
    Real.pi ≤ ν ∧ ν ≤ 4 * Real.pi
  ratio_at_crossing :
    let B := fderiv ℝ (parent.velocity next) 0
    let E := frame waveVector amplitude next
    entry E B 2 1 / entry E B 0 1 = couplingRatioOfGain (4 * Real.log (P.frequency (n + 3)))

/-- The two available physical stages at a prefix tip, together with
the latest completed wave and the next activation it selected. -/
structure InductiveEulerTip (P : InductiveEulerParameters) (n : ℕ) where
  olderActivation : ℝ
  activation : ℝ
  nextActivation : ℝ
  older : InductiveEulerStage P n olderActivation
  parent : InductiveEulerStage P (n + 1) activation
  wave : InductiveEulerWave P n older parent nextActivation
  activation_nonnegative : 0 ≤ activation
  slab_le_parent : P.slab (n + 1) activation ≤ P.slab n olderActivation

namespace InductiveEulerTip

variable {P : InductiveEulerParameters} {n : ℕ}

/-- The next endpoint fits inside the latest stage's closed time slab. -/
theorem next_slab_lt (p : InductiveEulerTip P n) (h : P.LifetimeBounds) :
    P.slab (n + 2) p.nextActivation < P.slab (n + 1) p.activation := by
  change p.nextActivation + 2 * inductionHalfLength P.frequency (n + 1) <
    p.activation + 2 * inductionHalfLength P.frequency n
  linarith only [p.wave.activation_step.2, (h.step n).1, (h.step n).2.2]

/-- The exact current comparison domain lies inside the interval on which
the preceding pair solves the wave equations. -/
theorem next_activeSlab_subset (p : InductiveEulerTip P n) (h : P.LifetimeBounds) :
    Icc p.nextActivation (P.slab (n + 2) p.nextActivation) ⊆
      Icc p.activation (P.slab (n + 1) p.activation) :=
  Icc_subset_Icc (sub_nonneg.mp p.wave.activation_step.1) (p.next_slab_lt h).le

theorem next_activation_nonnegative (p : InductiveEulerTip P n) : 0 ≤ p.nextActivation :=
  p.activation_nonnegative.trans (sub_nonneg.mp p.wave.activation_step.1)

theorem next_slab_pos (p : InductiveEulerTip P n) (h : P.LifetimeBounds) :
    0 < P.slab (n + 2) p.nextActivation := by
  change 0 < p.nextActivation + 2 * inductionHalfLength P.frequency (n + 1)
  exact add_pos_of_nonneg_of_pos p.next_activation_nonnegative (mul_pos (by norm_num) (h.step (n + 1)).1)

end InductiveEulerTip

/-- The two initial velocities and the first wave. The initial endpoint
times are zero and the same first wave activates the second stage at zero. -/
structure InductiveEulerBase (P : InductiveEulerParameters) where
  stationary : InductiveEulerStage P 0 0
  first : InductiveEulerStage P 1 0
  wave : InductiveEulerWave P 0 stationary first 0
  initial_coupling :
    entry (frame wave.waveVector wave.amplitude 0) (fderiv ℝ (stationary.velocity 0) 0) 0 1 = 2 * Real.pi

namespace InductiveEulerBase

def tip {P : InductiveEulerParameters} (b : InductiveEulerBase P) (h : P.LifetimeBounds) :
    InductiveEulerTip P 0 :=
  ⟨0, 0, 0, b.stationary, b.first, b.wave, le_rfl, by
    change 0 + 2 * inductionHalfLength P.frequency 0 ≤ 1
    linarith only [h.first]⟩

end InductiveEulerBase

/-- A stage step extends the actual tip. It uses one physical comparison on
the next active slab, and binds its selected pair to the new stage and wave. -/
structure InductiveEulerStep {P : InductiveEulerParameters} {n : ℕ}
    (p : InductiveEulerTip P n) where
  physical : PhysicalAmplification (Icc p.nextActivation (P.slab (n + 2) p.nextActivation)) p.nextActivation
  window : ℝ
  crossing : physical.GrowingCrossing window (P.frequency (n + 2)) (P.frequency (n + 2) ^ (-3 / 4 : ℝ))
    (couplingRatioOfGain (4 * Real.log (P.frequency (n + 4))))
  child : InductiveEulerStage P (n + 2) p.nextActivation
  wave : InductiveEulerWave P (n + 1) p.parent child crossing.crossing
  physical_window : physical.clock window = P.slab (n + 2) p.nextActivation
  window_ge : 2 ≤ window
  preceding_vector : physical.kp = p.wave.waveVector
  preceding_amplitude : physical.ap = p.wave.amplitude
  older_gradient : ∀ t ∈ Icc p.nextActivation (P.slab (n + 2) p.nextActivation), physical.B t = fderiv ℝ (p.older.velocity t) 0
  preceding_error : ∀ t ∈ Icc p.nextActivation (P.slab (n + 2) p.nextActivation), physical.E t = p.wave.error t
  current_vector : crossing.waveVector = wave.waveVector
  current_amplitude : crossing.amplitude = wave.amplitude
  prescribed_ratio : physical.ratio = couplingRatioOfGain (4 * Real.log (P.frequency (n + 3)))
  comparison_ratio : (P.comparisonConstant : ℝ) * physical.ratio ≤ 1
  comparison_error : (P.comparisonConstant : ℝ) * window ^ P.comparisonConstant * physical.errorSize ≤ physical.ratio

namespace InductiveEulerStep

def tip {P : InductiveEulerParameters} {n : ℕ} {p : InductiveEulerTip P n}
    (d : InductiveEulerStep p) (h : P.LifetimeBounds) : InductiveEulerTip P (n + 1) :=
  ⟨p.activation, p.nextActivation, d.crossing.crossing, p.parent, d.child, d.wave,
    p.next_activation_nonnegative, (p.next_slab_lt h).le⟩

end InductiveEulerStep

/-- A prefix is indexed by its exact tip. Each constructor appends a step
to the previous tip without a choice of replacement stages or wave data. -/
inductive InductiveEulerPrefix (P : InductiveEulerParameters) (h : P.LifetimeBounds) :
    (n : ℕ) → InductiveEulerTip P n → Type where
  | initial (base : InductiveEulerBase P) : InductiveEulerPrefix P h 0 (base.tip h)
  | append {n : ℕ} {p : InductiveEulerTip P n} (prior : InductiveEulerPrefix P h n p)
      (step : InductiveEulerStep p) : InductiveEulerPrefix P h (n + 1) (step.tip h)

namespace InductiveEulerPrefix

variable {P : InductiveEulerParameters} {h : P.LifetimeBounds}

/-- Recover the exact stage tip and compatible prefix at an earlier index. -/
noncomputable def lookup {n : ℕ} {tip : InductiveEulerTip P n} (p : InductiveEulerPrefix P h n tip) :
    (k : ℕ) → k ≤ n → Σ q : InductiveEulerTip P k, InductiveEulerPrefix P h k q :=
  match p with
  | .initial b => by
    intro k hk
    obtain rfl := Nat.eq_zero_of_le_zero hk
    exact ⟨b.tip h, .initial b⟩
  | @InductiveEulerPrefix.append _ _ n tip p step => fun k hk =>
    if hEq : k = n + 1 then by
      subst k
      exact ⟨step.tip h, .append p step⟩
    else p.lookup k (by omega)

@[simp] theorem lookup_self {n : ℕ} {tip : InductiveEulerTip P n} (p : InductiveEulerPrefix P h n tip)
    (hn : n ≤ n) : p.lookup n hn = ⟨tip, p⟩ := by
  cases p with
  | initial _ => rfl
  | append _ _ => simp [lookup]

/-- Appending a stage preserves the exact prefix at every earlier index. -/
theorem lookup_append_le {n : ℕ} {tip : InductiveEulerTip P n}
    (p : InductiveEulerPrefix P h n tip) (d : InductiveEulerStep tip)
    {k : ℕ} (hk : k ≤ n) (hk' : k ≤ n + 1) :
    (p.append d).lookup k hk' = p.lookup k hk := by
  simp [lookup, show k ≠ n + 1 by omega]

/-- Looking up an earlier stage in a looked-up prefix yields the same exact prefix. -/
theorem lookup_lookup {n : ℕ} {tip : InductiveEulerTip P n}
    (p : InductiveEulerPrefix P h n tip) {k l : ℕ} (hkl : k ≤ l) (hln : l ≤ n) :
    (p.lookup l hln).2.lookup k hkl = p.lookup k (hkl.trans hln) := by
  induction p generalizing l with
  | initial _ =>
    obtain rfl := Nat.eq_zero_of_le_zero hln
    rw [lookup_self]
  | @append n tip prior step ih =>
    by_cases hl : l = n + 1
    · subst l
      rw [lookup_self]
    · have hln' : l ≤ n := by omega
      rw [lookup_append_le prior step hln', lookup_append_le prior step (hkl.trans hln')]
      exact ih hkl hln'

/-- Activation times are nondecreasing along the exact prefix. -/
theorem lookup_activation_le {n : ℕ} {tip : InductiveEulerTip P n}
    (p : InductiveEulerPrefix P h n tip) {k : ℕ} (hk : k ≤ n) :
    (p.lookup k hk).1.activation ≤ tip.activation := by
  induction p with
  | initial _ =>
    obtain rfl := Nat.eq_zero_of_le_zero hk
    rw [lookup_self]
  | @append n tip prior step ih =>
    by_cases hkn : k = n + 1
    · subst k
      rw [lookup_self]
    · have hk' : k ≤ n := by omega
      rw [lookup_append_le prior step hk']
      exact (ih hk').trans (sub_nonneg.mp tip.wave.activation_step.1)

/-- Later closed slabs end no later than the exact earlier stage's slab. -/
theorem slab_le_lookup_slab {n : ℕ} {tip : InductiveEulerTip P n}
    (p : InductiveEulerPrefix P h n tip) {k : ℕ} (hk : k ≤ n) :
    P.slab (n + 1) tip.activation ≤ P.slab (k + 1) (p.lookup k hk).1.activation := by
  induction p with
  | initial _ =>
    obtain rfl := Nat.eq_zero_of_le_zero hk
    rw [lookup_self]
  | @append n tip prior step ih =>
    by_cases hkn : k = n + 1
    · subst k
      rw [lookup_self]
    · have hk' : k ≤ n := by omega
      rw [lookup_append_le prior step hk']
      exact (step.tip h).slab_le_parent.trans (ih hk')

/-- The current active interval is contained in the active interval of every earlier wave. -/
theorem activeSlab_subset_lookup {n : ℕ} {tip : InductiveEulerTip P n}
    (p : InductiveEulerPrefix P h n tip) {k : ℕ} (hk : k ≤ n) :
    Icc tip.activation (P.slab (n + 1) tip.activation) ⊆
      Icc (p.lookup k hk).1.activation (P.slab (k + 1) (p.lookup k hk).1.activation) :=
  Icc_subset_Icc (p.lookup_activation_le hk) (p.slab_le_lookup_slab hk)


/-- The new comparison interval lies in every previously recorded active interval. -/
theorem next_activeSlab_subset_lookup {n : ℕ} {tip : InductiveEulerTip P n}
    (p : InductiveEulerPrefix P h n tip) {k : ℕ} (hk : k ≤ n) :
    Icc tip.nextActivation (P.slab (n + 2) tip.nextActivation) ⊆
      Icc (p.lookup k hk).1.activation (P.slab (k + 1) (p.lookup k hk).1.activation) :=
  (tip.next_activeSlab_subset h).trans (p.activeSlab_subset_lookup hk)

/-- Consecutive lookup results are joined by the actual recorded step, including its crossing. -/
theorem exists_lookup_step {n : ℕ} {tip : InductiveEulerTip P n}
    (p : InductiveEulerPrefix P h n tip) {k : ℕ} (hk : k + 1 ≤ n) :
    let old := p.lookup k ((Nat.le_succ k).trans hk)
    ∃ d : InductiveEulerStep old.1, p.lookup (k + 1) hk = ⟨d.tip h, old.2.append d⟩ := by
  dsimp only
  have hL := p.lookup_lookup (Nat.le_succ k) hk
  rw [← hL]
  rcases p.lookup (k + 1) hk with ⟨_, q⟩
  cases q with
  | append prior step =>
    rw [lookup_append_le prior step (le_refl k), lookup_self]
    exact ⟨step, rfl⟩


end InductiveEulerPrefix


namespace InductiveEulerTip

/-- The latest wave's first coupling at the activation it selected. -/
def exitCoupling {P : InductiveEulerParameters} {n : ℕ} (p : InductiveEulerTip P n) : ℝ :=
  entry (frame p.wave.waveVector p.wave.amplitude p.nextActivation)
    (fderiv ℝ (p.older.velocity p.nextActivation) 0) 0 1

end InductiveEulerTip

namespace InductiveEulerStep

variable {P : InductiveEulerParameters} {n : ℕ} {p : InductiveEulerTip P n}

/-- The strain of the stored physical window is the actual parent gradient. -/
theorem parent_gradient (d : InductiveEulerStep p) (h : P.LifetimeBounds) :
    EqOn d.physical.gradient (fun t => fderiv ℝ (p.parent.velocity t) 0)
      (Icc p.nextActivation (P.slab (n + 2) p.nextActivation)) := by
  intro t ht
  have hprev := p.next_activeSlab_subset h ht
  have hs := p.wave.gradient_split t hprev
  rw [p.wave.cutoff_complete t ⟨ht.1, hprev.2⟩, one_smul] at hs
  rw [PhysicalAmplification.gradient, d.preceding_vector, d.preceding_amplitude,
    d.older_gradient t ht, d.preceding_error t ht]
  exact hs.symm

/-- A stored successor records the physical crossing between the two exact
couplings in the prefix. -/
theorem scheduledPhysicalCrossing (d : InductiveEulerStep p) (h : P.LifetimeBounds) :
    IsScheduledPhysicalCrossing p.exitCoupling (d.tip h).exitCoupling
      (scheduledCrossingRatio P.frequency n) (scheduledCrossingRatio P.frequency (n + 1)) := by
  refine ⟨_, _, d.window, P.frequency (n + 2), P.frequency (n + 2) ^ (-3 / 4 : ℝ),
    d.physical, d.crossing, ?_, d.prescribed_ratio, ?_⟩
  · unfold PhysicalAmplification.firstCoupling PhysicalAmplification.basis InductiveEulerTip.exitCoupling
    rw [d.preceding_vector, d.preceding_amplitude,
      d.older_gradient _ d.physical.activation]
  · have ht := d.crossing.crossing_in_slab
    have ht' : d.crossing.crossing ∈ Icc p.nextActivation (P.slab (n + 2) p.nextActivation) :=
      ⟨ht.1, ht.2.trans_eq d.physical_window⟩
    have hGrad := d.parent_gradient h ht'
    change d.physical.gradient d.crossing.crossing = fderiv ℝ (p.parent.velocity d.crossing.crossing) 0 at hGrad
    unfold PhysicalAmplification.physicalNu
    rw [hGrad, d.current_vector, d.current_amplitude]
    rfl

end InductiveEulerStep

namespace InductiveEulerPrefix

variable {P : InductiveEulerParameters} {h : P.LifetimeBounds}
  {n : ℕ} {p : InductiveEulerTip P n} (a : InductiveEulerPrefix P h n p)

theorem initial_coupling : (a.lookup 0 (Nat.zero_le n)).1.exitCoupling = 2 * Real.pi := by
  induction a with
  | initial b => exact b.initial_coupling
  | @append n p prior d ih =>
    rw [lookup_append_le _ _ (Nat.zero_le n)]
    exact ih

/-- Each adjacent pair of looked-up tips inherits the actual crossing of its
stored successor, including its prescribed geometric ratio. -/
theorem scheduledPhysicalCrossing {i : ℕ} (hi : i + 1 ≤ n) :
    IsScheduledPhysicalCrossing
      (a.lookup i ((Nat.le_succ i).trans hi)).1.exitCoupling
      (a.lookup (i + 1) hi).1.exitCoupling
      (scheduledCrossingRatio P.frequency i) (scheduledCrossingRatio P.frequency (i + 1)) := by
  obtain ⟨d, hd⟩ := a.exists_lookup_step hi
  rw [hd]
  exact d.scheduledPhysicalCrossing h

include a in
/-- The new coupling bound follows from the finite prefix and the newly
selected crossing. The physical construction of the new stage can use it
before the new stage or its wave has been added to the prefix. -/
theorem next_coupling_bounds (hLarge : Real.exp 4 ≤ P.frequency 0)
    {I : Set ℝ} {start window scale peak : ℝ} {w : PhysicalAmplification I start}
    (d : w.GrowingCrossing window scale peak (scheduledCrossingRatio P.frequency (n + 1)))
    (hfirst : w.firstCoupling = p.exitCoupling) (hratio : w.ratio = scheduledCrossingRatio P.frequency n) :
    Real.pi ≤ w.physicalNu d.waveVector d.amplitude d.crossing ∧
      w.physicalNu d.waveVector d.amplitude d.crossing ≤ 4 * Real.pi := by
  let νnext := w.physicalNu d.waveVector d.amplitude d.crossing
  let ν (i : ℕ) := if hi : i ≤ n then (a.lookup i hi).1.exitCoupling else νnext
  have h0 : ν 0 = 2 * Real.pi := by
    simpa only [ν, dite_eq_left (Nat.zero_le n)] using a.initial_coupling
  have hCross (i : ℕ) (hi : i < n + 1) :
      IsScheduledPhysicalCrossing (ν i) (ν (i + 1))
        (scheduledCrossingRatio P.frequency i) (scheduledCrossingRatio P.frequency (i + 1)) := by
    by_cases hl : i + 1 ≤ n
    · simpa only [ν, dite_eq_left ((Nat.le_succ i).trans hl), dite_eq_left hl] using a.scheduledPhysicalCrossing hl
    · have heq : i = n := by omega
      subst i
      simp only [ν, dite_eq_left le_rfl, lookup_self, dite_eq_right hl]
      exact ⟨I, start, window, scale, peak, w, d, hfirst, hratio, rfl⟩
  have hbound := frequencySchedule_physical_coupling_prefix_bounds (ν := ν) (n + 1)
    P.exponentParameter_ge hLarge P.frequency_step P.order_maximum h0 hCross (n + 1) le_rfl
  change Real.pi ≤ νnext ∧ νnext ≤ 4 * Real.pi
  simpa only [ν, dite_eq_right (show ¬ n + 1 ≤ n by omega)] using hbound.2.2

end InductiveEulerPrefix


/-- The local induction statement. The constructor may inspect the
certified finite prefix, and its output is tied to its exact tip. -/
abbrev InductiveEulerSuccessor (P : InductiveEulerParameters) (h : P.LifetimeBounds) :=
  ∀ (n : ℕ) (p : InductiveEulerTip P n), InductiveEulerPrefix P h n p → Nonempty (InductiveEulerStep p)


/-- The inputs to the infinite induction are an initial pair and a local
successor construction on certified finite prefixes. -/
structure InductiveEulerConstruction (P : InductiveEulerParameters) where
  lifetime : P.LifetimeBounds
  base : InductiveEulerBase P
  successor : ∀ (n : ℕ) (p : InductiveEulerTip P n),
    InductiveEulerPrefix P lifetime n p → InductiveEulerStep p

namespace InductiveEulerConstruction

variable {P : InductiveEulerParameters} (c : InductiveEulerConstruction P)

/-- The exact finite prefixes generated by repeated local extension. -/
def trace (n : ℕ) : Σ p : InductiveEulerTip P n, InductiveEulerPrefix P c.lifetime n p :=
  match n with
  | 0 => ⟨c.base.tip c.lifetime, .initial c.base⟩
  | j + 1 =>
    let a := trace j
    let d := c.successor j a.1 a.2
    ⟨d.tip c.lifetime, .append a.2 d⟩

abbrev tip (n : ℕ) : InductiveEulerTip P n := (c.trace n).1

/-- A local step is chosen once at its generated prefix. -/
def selectedStep (n : ℕ) : InductiveEulerStep (c.tip n) :=
  c.successor n (c.trace n).1 (c.trace n).2

/-- The prefix at the next index extends the prefix at the current index. -/
theorem trace_succ (n : ℕ) : c.trace (n + 1) =
    ⟨(c.selectedStep n).tip c.lifetime, .append (c.trace n).2 (c.selectedStep n)⟩ := rfl

/-- Restriction of a generated prefix gives exactly the earlier generated prefix. -/
theorem trace_lookup {k n : ℕ} (hk : k ≤ n) :
    (c.trace n).2.lookup k hk = c.trace k := by
  induction n with
  | zero =>
    obtain rfl := Nat.eq_zero_of_le_zero hk
    exact InductiveEulerPrefix.lookup_self (c.trace 0).2 hk
  | succ n ih =>
    by_cases heq : k = n + 1
    · subst k
      exact InductiveEulerPrefix.lookup_self (c.trace (n + 1)).2 hk
    · have hkn : k ≤ n := by omega
      change ((c.trace n).2.append (c.selectedStep n)).lookup k hk = c.trace k
      rw [InductiveEulerPrefix.lookup_append_le _ _ hkn]
      exact ih hkn

/-- The activation sequence is read from the successively appended stages. -/
def activation : ℕ → ℝ
  | 0 => 0
  | n + 1 => (c.tip n).activation

/-- The physical stage retained at each index, with its actual activation. -/
def stage : ∀ n, InductiveEulerStage P n (c.activation n)
  | 0 => c.base.stationary
  | n + 1 => (c.tip n).parent

@[simp] theorem activation_zero : c.activation 0 = 0 := rfl
@[simp] theorem activation_one : c.activation 1 = 0 := rfl
@[simp] theorem activation_two : c.activation 2 = 0 := rfl

theorem activation_next (n : ℕ) : c.activation (n + 2) = (c.tip n).nextActivation := rfl

theorem activation_crossing (n : ℕ) :
    c.activation (n + 3) = (c.selectedStep n).crossing.crossing := rfl

private theorem older_activation (n : ℕ) : (c.tip n).olderActivation = c.activation n := by
  cases n <;> rfl

/-- The older member of each tip is exactly the already retained stage. -/
theorem older_stage (n : ℕ) :
    c.older_activation n ▸ (c.tip n).older = c.stage n := by
  cases n <;> rfl

private theorem older_velocity (n : ℕ) : (c.tip n).older.velocity = (c.stage n).velocity := by
  cases n <;> rfl

/-- The closed time slab of each retained stage. -/
def slab (n : ℕ) : ℝ := P.slab n (c.activation n)

theorem slab_succ_lt (n : ℕ) : c.slab (n + 1) < c.slab n := by
  cases n with
  | zero =>
    change 0 + 2 * inductionHalfLength P.frequency 0 < 1
    linarith only [c.lifetime.first]
  | succ n => exact (c.tip n).next_slab_lt c.lifetime

theorem stage_activation_nonnegative (n : ℕ) : 0 ≤ c.activation n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact (c.tip n).activation_nonnegative

private def oscillation : ℕ → Velocity
  | 0 => 0
  | n + 1 => (c.tip n).wave.oscillation

private def waveVector : ℕ → ℝ → Vec3
  | 0 => 0
  | n + 1 => (c.tip n).wave.waveVector

private def amplitude : ℕ → ℝ → Vec3
  | 0 => 0
  | n + 1 => (c.tip n).wave.amplitude

private def cutoff : ℕ → ℝ → ℝ
  | 0 => 0
  | n + 1 => (c.tip n).wave.cutoff

private def error : ℕ → ℝ → Vec3 →L[ℝ] Vec3
  | 0 => 0
  | n + 1 => (c.tip n).wave.error

/-- Serialize the retained physical fields and certified increments into the
common stage family used by the limit argument. -/
def stages : InductiveEulerStages where
  exponentParameter := P.exponentParameter
  threshold := P.threshold
  order := P.order
  frequency := P.frequency
  exponentParameter_ge := P.exponentParameter_ge
  initial_order := P.initial_order
  initial_threshold := P.initial_threshold
  frequency_step := P.frequency_step
  order_maximum := P.order_maximum
  threshold_pos := P.threshold_pos
  threshold_floor := P.threshold_floor
  activation := c.activation
  slab := c.slab
  activation_zero := c.activation_zero
  first_activation := c.activation_one
  second_activation := c.activation_two
  slab_base := rfl
  slab_step _ := rfl
  activation_step n := (c.tip n).wave.activation_step
  torusVelocity n := (c.stage n).torusVelocity
  residual n := (c.stage n).residual
  oscillation := c.oscillation
  smooth n := (c.stage n).smooth_velocity
  odd n := (c.stage n).odd_velocity
  divergence_free n := (c.stage n).divergence_free
  velocity_bound n := (c.stage n).velocity_bound
  velocity_band n := (c.stage n).velocity_band
  projected_residual n t ht := ((c.stage n).projected_eq t ht).symm
  residual_bound n := (c.stage n).residual_bound
  oscillation_bound n := (c.tip n).wave.oscillation_bound
  correction_bound n m hm t ht := by
    change SpatialHolderHalf m ((c.tip n).parent.velocity t - (c.stage n).velocity t -
      (c.tip n).wave.oscillation t) ∧ spatialHolderHalfNorm m
      ((c.tip n).parent.velocity t - (c.stage n).velocity t - (c.tip n).wave.oscillation t) ≤
        (P.frequency (n + 1))⁻¹
    rw [← c.older_velocity n]
    exact (c.tip n).wave.correction_bound m hm t ht
  oscillation_vanishes n hn := by
    cases n with
    | zero => omega
    | succ j => exact (c.tip j).wave.oscillation_vanishes hn
  oscillation_support n := (c.tip n).wave.oscillation_support

/-- The same prefix choices supply the entire family of central waves
and physical crossings used in the terminal estimates. -/
def centralWaves : InductiveEulerCentralWaves c.stages where
  waveVector := c.waveVector
  amplitude := c.amplitude
  cutoff := c.cutoff
  error := c.error
  strengthConstant := P.strengthConstant
  strengthConstant_ge := P.strengthConstant_ge
  gradient_split n t ht := by
    change fderiv ℝ ((c.tip n).parent.velocity t) 0 = fderiv ℝ ((c.stage n).velocity t) 0 +
      (c.tip n).wave.cutoff t • (innerSL ℝ ((c.tip n).wave.waveVector t)).smulRight ((c.tip n).wave.amplitude t) +
      (c.tip n).wave.error t
    rw [← c.older_velocity n]
    exact (c.tip n).wave.gradient_split t ht
  error_bound n := (c.tip n).wave.error_bound
  cutoff_complete n := (c.tip n).wave.cutoff_complete
  strength_at_crossing n := (c.tip n).wave.strength_at_crossing
  coupling_at_crossing n := by
    change Real.pi ≤ entry (frame (c.tip n).wave.waveVector (c.tip n).wave.amplitude (c.tip n).nextActivation)
      (fderiv ℝ ((c.stage n).velocity (c.tip n).nextActivation) 0) 0 1 ∧
      entry (frame (c.tip n).wave.waveVector (c.tip n).wave.amplitude (c.tip n).nextActivation)
        (fderiv ℝ ((c.stage n).velocity (c.tip n).nextActivation) 0) 0 1 ≤ 4 * Real.pi
    rw [← c.older_velocity n]
    exact (c.tip n).wave.coupling_at_crossing
  comparisonConstant := P.comparisonConstant
  comparisonConstant_ge := P.comparisonConstant_ge
  window n := (c.selectedStep n).window
  physical n := (c.selectedStep n).physical
  crossing n := (c.selectedStep n).crossing
  physical_window n := (c.selectedStep n).physical_window
  window_ge n := (c.selectedStep n).window_ge
  preceding_vector n := (c.selectedStep n).preceding_vector
  preceding_amplitude n := (c.selectedStep n).preceding_amplitude
  older_gradient n t ht := by
    change (c.selectedStep n).physical.B t = fderiv ℝ ((c.stage n).velocity t) 0
    rw [← c.older_velocity n]
    exact (c.selectedStep n).older_gradient t ht
  preceding_error n := (c.selectedStep n).preceding_error
  current_vector n := (c.selectedStep n).current_vector
  current_amplitude n := (c.selectedStep n).current_amplitude
  crossing_time n := (c.activation_crossing n).symm
  prescribed_ratio n := (c.selectedStep n).prescribed_ratio
  comparison_ratio n := (c.selectedStep n).comparison_ratio
  comparison_error n := (c.selectedStep n).comparison_error

end InductiveEulerConstruction

/-- A base pair and a true local successor on finite prefixes give one
compatible infinite family with the frozen schedule. -/
theorem exists_inductiveEulerStages_of_localSuccessor {P : InductiveEulerParameters}
    (h : P.LifetimeBounds) (hbase : Nonempty (InductiveEulerBase P)) (hstep : InductiveEulerSuccessor P h) :
    ∃ s : InductiveEulerStages, s.frequency = P.frequency ∧ s.order = P.order ∧
      Nonempty (InductiveEulerCentralWaves s) := by
  let c : InductiveEulerConstruction P := ⟨h, Classical.choice hbase,
    fun n tip prior => Classical.choice (hstep n tip prior)⟩
  exact ⟨c.stages, rfl, rfl, ⟨c.centralWaves⟩⟩

/-- For sufficiently large base frequency, construction of the initial pair
and the local successor implies the frozen Theorem 1.1. -/
theorem theorem11_of_inductiveEulerLocalSuccessor :
    ∃ N : ℝ, ∀ P : InductiveEulerParameters, N ≤ P.frequency 0 →
      ∀ h : P.LifetimeBounds, Nonempty (InductiveEulerBase P) → InductiveEulerSuccessor P h → Theorem11 := by
  obtain ⟨N, hN⟩ := theorem11_of_inductiveEulerStages
  refine ⟨N, fun P hP h hbase hstep => ?_⟩
  obtain ⟨s, hs, _, ⟨w⟩⟩ := exists_inductiveEulerStages_of_localSuccessor h hbase hstep
  exact hN s w (by rwa [hs])

/-- The real torus field obtained from the two signed Fourier modes of the stationary shear. -/
def stationaryShearTorus (s : ℝ) : C(Labels, Vec3) := by
  classical
  refine ⟨fun z => periodicRealPartVector (stationaryShearComplexTorus s z),
    periodicRealPartVector.continuous.comp ?_⟩
  unfold stationaryShearComplexTorus finiteFourierSum
  exact continuous_finsetSum _ fun k _ => (mFourier k).continuous.smul continuous_const

@[simp] theorem stationaryShearTorus_lift (s : ℝ) (x : Vec3) :
    stationaryShearTorus s (toUnitTorus x) = stationaryShear s x := by
  change periodicRealPartVector (stationaryShearComplexTorus s (toUnitTorus x)) = _
  rw [stationaryShearComplexTorus_lift, periodicRealPartVector_complexifyVector]

private theorem stationaryShear_stage_deformation {s C : ℝ} (hs : |s| ≤ 1)
    (hC : 1 + 4 * Real.pi ≤ C) :
    DeformationOn (fun _ => stationaryShear s) (fun r t => stationaryShearFlow s (t - r)) 1 C := by
  refine ⟨stationaryShear_isLabelFlowOn s _, fun r _ t _ n x =>
    stationaryShearFlow_lattice_equiv s (t - r) n x, fun t ht => ?_⟩
  simp only [sub_zero, zero_sub]
  refine ⟨⟨stationaryShearFlow_inverse s t, fun x => ?_⟩, fun x => ?_, fun x => ?_⟩
  · simpa only [neg_neg] using stationaryShearFlow_inverse s (-t) x
  · exact ⟨(hasFDerivAt_stationaryShearFlow s t x).differentiableAt,
      (stationaryShearFlow_jacobian_norms hs ht x).1.trans hC⟩
  · have hinv : stationaryShearFlow s t (stationaryShearFlow s (-t) x) = x := by
      simpa only [neg_neg] using stationaryShearFlow_inverse s (-t) x
    have h := (stationaryShearFlow_jacobian_norms hs ht (stationaryShearFlow s (-t) x)).2
    rw [hinv] at h
    exact ⟨(hasFDerivAt_stationaryShearFlow s (-t) x).differentiableAt, h.trans hC⟩

private theorem stationaryShear_closedSlabLerayMomentum_zero (s t : ℝ) :
    closedSlabLerayMomentum 0 1 (fun _ => stationaryShear s) t = 0 := by
  have hzero : periodicLerayHolderLift (0 : Vec3 → Vec3) = 0 := by
    change periodicLerayHolderLift (fun _ => (0 : Vec3)) = (fun _ => 0)
    simpa only [map_zero] using periodicLerayHolderLift_pullback (0 : HalfHolder Labels Vec3)
  unfold closedSlabLerayMomentum
  have h : (fun x => derivWithin (fun _ : ℝ => stationaryShear s x) (Icc 0 1) t +
      fderiv ℝ (stationaryShear s) x (stationaryShear s x)) = 0 := by
    funext x
    simp [stationaryShear_advection]
  rw [h, hzero]

/-- The actual stationary shear, tilted by the scheduled first-wave gain
`4 * log (P.frequency 3)`, supplies the base stage. -/
def stationaryInductiveEulerStage (P : InductiveEulerParameters)
    (hs : |couplingRatioOfGain (4 * Real.log (P.frequency 3))| ≤ 1)
    (hfreq : 1 + 4 * Real.pi ≤ P.frequency 0) : InductiveEulerStage P 0 0 := by
  let s := couplingRatioOfGain (4 * Real.log (P.frequency 3))
  have htwo : 2 ≤ P.frequency 0 := by linarith only [hfreq, Real.pi_gt_three]
  have hfreq₁ : 0 ≤ P.frequency 1 := by
    rw [P.frequency_step 0]
    positivity
  have hT1 := stationaryShear_base_T1 (s := s) (show 1 ≤ P.frequency 0 by linarith only [htwo])
  have hvelocity : (fun (_ : ℝ) x => stationaryShearTorus s (toUnitTorus x)) =
      (fun _ => stationaryShear s) := by
    funext t x
    exact stationaryShearTorus_lift s x
  have hres (t : ℝ) : momentumResidual (Icc 0 1) (fun _ => stationaryShear s) (fun _ _ => 0) t = 0 :=
    funext (stationaryShear_closed_residual s t)
  refine {
    torusVelocity := fun _ => stationaryShearTorus s
    pressure := fun _ _ => 0
    flow := fun r t => stationaryShearFlow s (t - r)
    smooth_velocity := ?_
    odd_velocity := ?_
    divergence_free := ?_
    velocity_band := ?_
    velocity_bound := ?_
    smooth_pressure := contDiffOn_const
    periodic_pressure := fun _ _ _ _ => rfl
    mean_zero_pressure := fun _ _ => integral_zero _ _
    poisson := ?_
    projected_eq := ?_
    residual_bound := ?_
    deformation := ?_
    pressure_hessian := ?_ }
  · change ContDiffOn ℝ ∞ (Function.uncurry (fun (_ : ℝ) x =>
      stationaryShearTorus s (toUnitTorus x))) (Icc 0 1 ×ˢ (univ : Set Vec3))
    rw [hvelocity]
    exact hT1.1
  · intro t _
    simp only [stationaryShearTorus_lift]
    exact odd_stationaryShear s
  · intro t _ x
    simp only [stationaryShearTorus_lift]
    exact divergence_stationaryShear s x
  · intro t _ k hk
    have hcomplex : (fun z => periodicComplexifyVector (stationaryShearTorus s z)) =
        stationaryShearComplexTorus s := by
      funext z
      obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
      rw [stationaryShearTorus_lift, stationaryShearComplexTorus_lift]
    rw [hcomplex]
    exact hT1.2.2.2.2 k (fun hmem => (not_lt_of_ge ((mem_frequencyBand _ _).mp hmem)) hk)
  · intro t _
    apply (ContinuousMap.norm_le (stationaryShearTorus s) (by linarith only [htwo])).mpr
    intro z
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
    rw [stationaryShearTorus_lift]
    exact (norm_stationaryShear_le hs x).trans htwo
  · intro t _ x
    simp only [stationaryShearTorus_lift]
    exact (stationaryShear_normalized_pressure s).2 x
  · intro t _
    rw [hvelocity, InductiveEulerParameters.slab_zero, hres, stationaryShear_closedSlabLerayMomentum_zero]
  · intro t _ x
    rw [hvelocity, InductiveEulerParameters.slab_zero, hres, Pi.zero_apply, norm_zero]
    exact pow_nonneg (inv_nonneg.mpr hfreq₁) _
  · rw [hvelocity, InductiveEulerParameters.slab_zero]
    exact stationaryShear_stage_deformation hs hfreq
  · intro t _ x v
    simp

@[simp] theorem stationaryInductiveEulerStage_velocity (P : InductiveEulerParameters)
    (hs : |couplingRatioOfGain (4 * Real.log (P.frequency 3))| ≤ 1)
    (hfreq : 1 + 4 * Real.pi ≤ P.frequency 0) (t : ℝ) (x : Vec3) :
    (stationaryInductiveEulerStage P hs hfreq).velocity t x =
      stationaryShear (couplingRatioOfGain (4 * Real.log (P.frequency 3))) x :=
  stationaryShearTorus_lift _ _


/-- Attach the selected comparison to the actual next stage and its wave. -/
noncomputable def InductiveEulerStep.ofLaterWaveSelection
    {P : InductiveEulerParameters} {n : ℕ} (p : InductiveEulerTip P n)
    (w : LaterPhysicalWindow p.older.velocity p.parent.velocity p.wave.waveVector
      p.wave.amplitude p.wave.error p.nextActivation (P.slab (n + 2) p.nextActivation))
    (d : LaterWaveSelection p.parent.velocity w.physical P.comparisonConstant
      (inductionHalfLength P.frequency (n + 1)) (P.frequency (n + 2))
      (4 * Real.log (P.frequency (n + 4))) (P.frequency (n + 1) ^ 9))
    (child : InductiveEulerStage P (n + 2) p.nextActivation)
    (wave : InductiveEulerWave P (n + 1) p.parent child d.crossing.crossing)
    (hk : d.crossing.waveVector = wave.waveVector)
    (ha : d.crossing.amplitude = wave.amplitude) : InductiveEulerStep p where
  physical := w.physical
  window := d.window
  crossing := d.crossing
  child := child
  wave := wave
  physical_window := d.clock_eq
  window_ge := d.window_ge
  preceding_vector := w.preceding_vector_eq
  preceding_amplitude := w.preceding_amplitude_eq
  older_gradient := fun t _ => congrFun w.older_gradient_eq t
  preceding_error := fun t _ => congrFun w.error_eq t
  current_vector := hk
  current_amplitude := ha
  prescribed_ratio := by
    unfold PhysicalAmplification.ratio PhysicalAmplification.firstCoupling
      PhysicalAmplification.thirdCoupling PhysicalAmplification.basis
    rw [w.preceding_vector_eq, w.preceding_amplitude_eq, w.older_gradient_eq]
    exact p.wave.ratio_at_crossing
  comparison_ratio := d.comparison_ratio
  comparison_error := d.comparison_error


/-- Recover the actual comparison window directly from a certified prefix tip. -/
theorem InductiveEulerTip.exists_laterPhysicalWindow
    {P : InductiveEulerParameters} {n : ℕ} (p : InductiveEulerTip P n)
    (h : P.LifetimeBounds) (hbase : 1 < P.frequency 0) :
    Nonempty (LaterPhysicalWindow p.older.velocity p.parent.velocity p.wave.waveVector
      p.wave.amplitude p.wave.error p.nextActivation (P.slab (n + 2) p.nextActivation)) := by
  let finish := P.slab (n + 2) p.nextActivation
  let start := p.nextActivation
  let parentFinish := P.slab (n + 1) p.activation
  let olderFinish := P.slab n p.olderActivation
  have hsub : Icc start finish ⊆ Icc p.activation parentFinish := p.next_activeSlab_subset h
  have htime : start ≤ finish := by
    change p.nextActivation ≤ p.nextActivation + 2 * inductionHalfLength P.frequency (n + 1)
    linarith only [(h.step (n + 1)).1]
  have hfit : finish < parentFinish := p.next_slab_lt h
  have htimeParent : 0 < parentFinish := (p.next_slab_pos h).trans hfit
  have htimeOlder : 0 < olderFinish := htimeParent.trans_le p.slab_le_parent
  have hfOlder : finish ≤ olderFinish := hfit.le.trans p.slab_le_parent
  have hprePos : 0 ≤ start := p.next_activation_nonnegative
  have hOldCont := MovingWaveVector.continuousOn_central_gradient_of_smooth
    (u := p.older.velocity) htimeOlder hprePos hfOlder p.older.smooth_velocity
  have hNewCont := MovingWaveVector.continuousOn_central_gradient_of_smooth
    (u := p.parent.velocity) htimeParent hprePos hfit.le p.parent.smooth_velocity
  let frameAt := frame p.wave.waveVector p.wave.amplitude start
  let B := fderiv ℝ (p.older.velocity start) 0
  have hν : 0 < entry frameAt B 0 1 := Real.pi_pos.trans_le p.wave.coupling_at_crossing.1
  have hm := frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency
    P.exponentParameter_ge hbase.le P.frequency_step
  have hL : 0 < 4 * Real.log (P.frequency (n + 3)) :=
    mul_pos (by norm_num) (Real.log_pos (hbase.trans_le (hm (Nat.zero_le _))))
  have hη : 0 < entry frameAt B 2 1 := by
    have heps : 0 < couplingRatioOfGain (4 * Real.log (P.frequency (n + 3))) :=
      inv_pos.mpr (sq_pos_of_pos hL)
    have heq : entry frameAt B 2 1 / entry frameAt B 0 1 =
        couplingRatioOfGain (4 * Real.log (P.frequency (n + 3))) := p.wave.ratio_at_crossing
    have hquot : 0 < entry frameAt B 2 1 / entry frameAt B 0 1 := heq.symm ▸ heps
    exact (div_pos_iff_of_pos_right hν).mp hquot
  refine MovingWaveVector.exists_laterPhysicalWindow_of_stage htime hsub
    hOldCont hNewCont ?_ p.wave.center.nonzero p.wave.center.covector p.wave.center.amplitude
    p.wave.gradient_split ?_ hν hη
  · intro t ht
    exact p.older.divergence_free t ⟨hprePos.trans ht.1, ht.2.trans hfOlder⟩ 0
  · intro t ht
    exact p.wave.cutoff_complete t ⟨ht.1, ht.2.trans hfit.le⟩

/-- The older truncated stage supplies its raw central gradient bounds on
the actual later comparison interval. -/
theorem exists_inductiveEulerTip_olderGradient_threshold :
    ∃ N : ℝ, 1 ≤ N ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} (p : InductiveEulerTip P n),
        P.LifetimeBounds → N ≤ P.frequency 0 →
        let B := fun t => fderiv ℝ (p.older.velocity t) (0 : Vec3)
        let Bt := fun t => derivWithin B (Icc 0 (P.slab n p.olderActivation)) t
        ∀ t ∈ Icc p.nextActivation (P.slab (n + 2) p.nextActivation),
          HasDerivWithinAt B (Bt t) (Icc p.nextActivation (P.slab (n + 2) p.nextActivation)) t ∧
            ‖B t‖ ≤ P.frequency n ^ 9 ∧ ‖Bt t‖ ≤ P.frequency n ^ 18 := by
  obtain ⟨N, hN, hOld⟩ := exists_older_central_gradient_raw_bounds_of_projectedMomentum
  refine ⟨N, hN, ?_⟩
  intro P n p h hBase
  have hmono := frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency
    P.exponentParameter_ge (hN.trans hBase) P.frequency_step
  have hParent := p.next_slab_lt h
  have hfit := hParent.le.trans p.slab_le_parent
  have hOlderPos := (p.next_slab_pos h).trans_le hfit
  exact hOld hOlderPos p.next_activation_nonnegative hfit
    (hBase.trans (hmono (Nat.zero_le n))) (hN.trans (hBase.trans (hmono (Nat.zero_le (n + 1)))))
    p.older.torusVelocity p.older.residual p.older.smooth_velocity
    (fun t ht => ⟨p.older.velocity_bound t ht, p.older.velocity_band t ht⟩)
    p.older.divergence_free (fun t ht => (p.older.projected_eq t ht).symm)
    p.older.residual_bound


set_option maxHeartbeats 550000 in
/-- A certified prefix tip supplies every input of the next physical
comparison, including the actual older gradient's time derivative. -/
theorem exists_inductiveEulerTip_laterWave_threshold (C : ℝ) (hC : 2 ≤ C) :
    ∃ (C₀ : ℕ) (N : ℝ), 240 ≤ C₀ ∧ 1 < N ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} (p : InductiveEulerTip P n),
        P.LifetimeBounds → N ≤ P.frequency 0 →
        P.strengthConstant = C → P.comparisonConstant = C₀ →
        ∃ w : LaterPhysicalWindow p.older.velocity p.parent.velocity p.wave.waveVector
          p.wave.amplitude p.wave.error p.nextActivation (P.slab (n + 2) p.nextActivation),
          Nonempty (LaterWaveSelection p.parent.velocity w.physical P.comparisonConstant
            (inductionHalfLength P.frequency (n + 1)) (P.frequency (n + 2))
            (4 * Real.log (P.frequency (n + 4))) (P.frequency (n + 1) ^ 9)) := by
  have hCp : 0 < C := (by norm_num : (0 : ℝ) < 2).trans_le hC
  obtain ⟨C₀, Nsel, hC₀, hNsel, hSel⟩ :=
    MovingWaveVector.exists_frequencySchedule_selectLaterWave C⁻¹ C (inv_pos.mpr hCp) hCp
  obtain ⟨Nold, _, hOld⟩ := exists_inductiveEulerTip_olderGradient_threshold
  refine ⟨C₀, max Nsel Nold, hC₀, hNsel.trans_le (le_max_left _ _), ?_⟩
  intro P n p h hBase hStrengthConstant hComparisonConstant
  have hBaseSel : Nsel ≤ P.frequency 0 := (le_max_left _ _).trans hBase
  have hBaseOld : Nold ≤ P.frequency 0 := (le_max_right _ _).trans hBase
  obtain ⟨w⟩ := p.exists_laterPhysicalWindow h (hNsel.trans_le hBaseSel)
  let Bt (t : ℝ) := derivWithin (fun u => fderiv ℝ (p.older.velocity u) (0 : Vec3))
    (Icc 0 (P.slab n p.olderActivation)) t
  have hBt := hOld p h hBaseOld
  have hB : w.physical.initialStrength =
      ‖p.wave.waveVector p.nextActivation‖ * ‖p.wave.amplitude p.nextActivation‖ := by
    unfold PhysicalAmplification.initialStrength
    rw [w.preceding_vector_eq, w.preceding_amplitude_eq]
  have hν : w.physical.firstCoupling =
      entry (frame p.wave.waveVector p.wave.amplitude p.nextActivation)
        (fderiv ℝ (p.older.velocity p.nextActivation) 0) 0 1 := by
    unfold PhysicalAmplification.firstCoupling PhysicalAmplification.basis
    rw [w.preceding_vector_eq, w.preceding_amplitude_eq, w.older_gradient_eq]
  have hRatio : w.physical.ratio = couplingRatioOfGain (4 * Real.log (P.frequency (n + 3))) := by
    unfold PhysicalAmplification.ratio PhysicalAmplification.thirdCoupling
      PhysicalAmplification.firstCoupling PhysicalAmplification.basis
    rw [w.preceding_vector_eq, w.preceding_amplitude_eq, w.older_gradient_eq]
    exact p.wave.ratio_at_crossing
  have hσlo : C⁻¹ * P.frequency (n + 1) ^ (1 / 4 : ℝ) ≤ w.physical.initialStrength := by
    rw [hB, ← hStrengthConstant]
    exact p.wave.strength_at_crossing.1
  have hσhi : w.physical.initialStrength ≤
      C * P.frequency (n + 1) ^ (1 / 4 : ℝ) * (4 * Real.log (P.frequency (n + 3))) ^ 2 := by
    rw [hB, ← hStrengthConstant]
    exact p.wave.strength_at_crossing.2
  obtain ⟨hνlo, hνhi⟩ : Real.pi ≤ w.physical.firstCoupling ∧ w.physical.firstCoupling ≤ 4 * Real.pi := by
    rw [hν]
    exact p.wave.coupling_at_crossing
  have hSlab := p.next_activeSlab_subset h
  have hSelect := hSel P.exponentParameter P.order P.threshold P.frequency
    P.exponentParameter_ge P.initial_order P.initial_threshold hBaseSel P.frequency_step
    P.order_maximum P.threshold_pos P.threshold_floor n w Bt rfl
    hRatio hσlo hσhi hνlo hνhi
    (fun t ht => (hBt t ht).1) (fun t ht => (hBt t ht).2.1) (fun t ht => (hBt t ht).2.2)
    (fun t ht => p.wave.error_bound t (hSlab ht))
  exact ⟨w, by simpa only [hComparisonConstant] using hSelect⟩


/-- The selected exit's first-coupling bounds and ratio use the actual parent
gradient. They are available before constructing the cutoff child. -/
theorem InductiveEulerPrefix.later_wave_exit_coupling
    {P : InductiveEulerParameters} {h : P.LifetimeBounds} {n : ℕ} {p : InductiveEulerTip P n}
    (a : InductiveEulerPrefix P h n p) (hLarge : Real.exp 4 ≤ P.frequency 0)
    (w : LaterPhysicalWindow p.older.velocity p.parent.velocity p.wave.waveVector
      p.wave.amplitude p.wave.error p.nextActivation (P.slab (n + 2) p.nextActivation))
    (d : LaterWaveSelection p.parent.velocity w.physical P.comparisonConstant
      (inductionHalfLength P.frequency (n + 1)) (P.frequency (n + 2))
      (4 * Real.log (P.frequency (n + 4))) (P.frequency (n + 1) ^ 9)) :
    let t := d.crossing.crossing
    let E := frame d.crossing.waveVector d.crossing.amplitude t
    let B := fderiv ℝ (p.parent.velocity t) 0
    Real.pi ≤ entry E B 0 1 ∧ entry E B 0 1 ≤ 4 * Real.pi ∧
      entry E B 2 1 / entry E B 0 1 = couplingRatioOfGain (4 * Real.log (P.frequency (n + 4))) := by
  have hFirst : w.physical.firstCoupling = p.exitCoupling := by
    unfold PhysicalAmplification.firstCoupling PhysicalAmplification.basis InductiveEulerTip.exitCoupling
    rw [w.preceding_vector_eq, w.preceding_amplitude_eq, w.older_gradient_eq]
  have hRatio : w.physical.ratio = scheduledCrossingRatio P.frequency n := by
    unfold PhysicalAmplification.ratio PhysicalAmplification.firstCoupling
      PhysicalAmplification.thirdCoupling PhysicalAmplification.basis scheduledCrossingRatio
    rw [w.preceding_vector_eq, w.preceding_amplitude_eq, w.older_gradient_eq]
    exact p.wave.ratio_at_crossing
  have hν := a.next_coupling_bounds hLarge d.crossing hFirst hRatio
  let t := d.crossing.crossing
  have ht : t ∈ Icc p.nextActivation (P.slab (n + 2) p.nextActivation) :=
    ⟨d.crossing.crossing_in_slab.1, d.crossing.crossing_in_slab.2.trans_eq d.clock_eq⟩
  have hB : w.physical.gradient t = fderiv ℝ (p.parent.velocity t) 0 := w.parent_gradient_eq ht
  have hη := d.crossing.crossing_ratio
  change w.physical.physicalEta d.crossing.waveVector d.crossing.amplitude t /
      w.physical.physicalNu d.crossing.waveVector d.crossing.amplitude t = _ at hη
  change Real.pi ≤ w.physical.physicalNu d.crossing.waveVector d.crossing.amplitude t ∧
    w.physical.physicalNu d.crossing.waveVector d.crossing.amplitude t ≤ 4 * Real.pi at hν
  simp only [PhysicalAmplification.physicalNu, PhysicalAmplification.physicalEta, hB] at hν hη
  exact ⟨hν.1, hν.2, hη⟩


end

end TorusEuler
