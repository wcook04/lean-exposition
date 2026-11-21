import TorusEuler.Paper.Proofs.S678a.Library.StepApprox
import TorusEuler.Paper.Proofs.S678a.Library.ChildBounds
import TorusEuler.Paper.Proofs.S678a.Library.StepInput
import TorusEuler.Paper.Proofs.S678a.Library.LaterWindow
import TorusEuler.Paper.Proofs.S678a.Library.WaveSelection
import TorusEuler.PhysicalWaveStageClosure

/-! # Step objects from the cutoff child (package S678a)

Own glue of row 7.1 (item 4 of the proof, sections/08b_induction.tex:376-460).

Copies of the library constructors of PhysicalWaveStageClosure.lean on `TruncatedChildStage`, for the
structure `CutoffChild` (whose residual fields, the identity (5.58) of Proposition 5.11, the proof
of 7.1 does not use):
`growingCutoffCenter` (:376, private), `InductiveEulerWave.ofGrowingCrossingCutoff` (:402),
`InductiveEulerStep.ofPhysicalHierarchyCutoff` (:655),
`exists_inductiveEulerChild_of_physicalCutoff` (:766). The hypothesis
`hCut : s.CutoffBounds …` is replaced by its tail clauses (`hTails`, `hTailTwo`, which come from
(B.2) of Lemma B.1) and, in the last one, by the final residual bound `hRes`, the C^2 bound `hTwo` of (5.56) and the pressure-increment
bound `hPress57` of (5.57) (Proposition 5.11 at the scheduled size; the child stage is built from
`StepApproxBounds`, the fields of Lemma 5.8 without a pressure bound). -/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

local notation "Labels" => UnitAddTorus (Fin 3)

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler
open HierarchyTwistedProfile

noncomputable section

namespace InductiveEulerWave

/-- The gradient of the child at the center is the parent gradient plus the cutoff-weighted rank-one term of the growing crossing plus an error (glue for the later wave). -/
theorem growingCutoffCenter
    {I : Set ℝ} {t₀ μ T scale Ustar ratio half : ℝ}
    {w : MovingWaveVector.PhysicalAmplification I t₀} {b q qNext : ℕ}
    {parent V child tail : Velocity} {E : ℝ → Vec3 →L[ℝ] Vec3}
    (d : w.GrowingCrossing T scale Ustar ratio)
    (hScale : scale = μ ^ frequencyExponent b q)
    (hμ : 2 ≤ μ) (hb : 1 ≤ b) (hhalf : d.crossing - t₀ ≤ half)
    (hChild : ∀ r ∈ w.activeSlab T, child r = V r + tail r)
    (hV : ∀ r ∈ w.activeSlab T, DifferentiableAt ℝ (V r) 0)
    (hTail : ∀ r ∈ w.activeSlab T, SpatialHolderHalf 2 (tail r) ∧
      spatialHolderHalfNorm 2 (tail r) ≤ (scale ^ frequencyExponent b qNext) ^ (-5 : ℝ))
    (hPre : ∀ r ∈ w.activeSlab T,
      fderiv ℝ (V r) 0 = fderiv ℝ (parent r) 0 +
        waveSwitch t₀ w.rate r • InnerProductSpace.rankOne ℝ (d.amplitude r) (d.waveVector r) + E r ∧
      ‖E r‖ ≤ scale ^ (-1 / 3 : ℝ)) :
    ∀ r ∈ w.activeSlab T,
      fderiv ℝ (child r) 0 = fderiv ℝ (parent r) 0 +
        waveSwitch t₀ w.rate r • InnerProductSpace.rankOne ℝ (d.amplitude r) (d.waveVector r) +
        (E r + fderiv ℝ (tail r) 0) ∧
      ‖E r + fderiv ℝ (tail r) 0‖ ≤ scale ^ (-1 / 4 : ℝ) := by
  subst scale
  exact (frequencySchedule_child_T4_center d hμ hb hhalf hChild hV hTail hPre).1


/-- The actual cutoff correction adds its spatial first jet to the central error
of the approximate velocity. The normalized crossing fixes the cutoff and ratio
of this same wave. -/
def ofGrowingCrossingCutoff'
    {P : InductiveEulerParameters} {n depth : ℕ} {tOld t window Λ K : ℝ}
    {ψ : Vec3 → ℝ} {V osc : Velocity} {rawError : ℝ → Vec3 →L[ℝ] Vec3}
    {w : MovingWaveVector.PhysicalAmplification (Icc t (P.slab (n + 1) t)) t}
    (parent : InductiveEulerStage P n tOld) (child : InductiveEulerStage P (n + 1) t)
    (s : CutoffChild (P.slab (n + 1) t) Λ ψ V)
    (hChild : child.velocity = s.velocity)
    (d : w.GrowingCrossing window (P.frequency (n + 1))
      (P.frequency (n + 1) ^ (-3 / 4 : ℝ))
      (couplingRatioOfGain (4 * Real.log (P.frequency (n + 3)))))
    (hμ : 2 ≤ P.frequency n) (ht : 0 ≤ t)
    (hSlab : w.clock window = P.slab (n + 1) t)
    (hHalf : d.crossing - t ≤ inductionHalfLength P.frequency n)
    (hGradient : EqOn w.gradient (fun r => fderiv ℝ (parent.velocity r) 0)
      (Icc t (P.slab (n + 1) t)))
    (hCenter : LocalizedAmplitude.CenterWaveOn (fun r => fderiv ℝ (parent.velocity r) 0) d.waveVector d.amplitude t
      (P.slab (n + 1) t) (P.frequency n ^ 9))
    (hOsc : ∀ r ∈ Icc 0 (P.slab (n + 1) t), ∀ x, ‖osc r x‖ ≤ (P.frequency (n + 1))⁻¹)
    (hCorrection : ∀ m ≤ P.order (n + 1), ∀ r ∈ Icc 0 (P.slab (n + 1) t),
      let v := s.velocity r - parent.velocity r - osc r
      SpatialHolderHalf m v ∧ spatialHolderHalfNorm m v ≤ (P.frequency (n + 1))⁻¹)
    (hVanish : 2 ≤ n + 1 → ∀ r ∈ Icc 0 t, osc r = 0)
    (hSupport : ∀ r ∈ Icc 0 (P.slab (n + 1) t), ∀ x, osc r x ≠ 0 →
      ∃ z : Fin 3 → ℤ, dist (latticeVector z) x ≤ (P.frequency n)⁻¹)
    (hTails : ∀ m ≤ depth, ∀ r ∈ Icc 0 (P.slab (n + 1) t), SpatialHolderHalf m (s.velocity r - V r) ∧
      spatialHolderHalfNorm m (s.velocity r - V r) ≤ K * Λ ^ ((m : ℤ) - depth) * spatialHolderHalfNorm depth (V r))
    (hTailTwo : ∀ r ∈ Icc 0 (P.slab (n + 1) t),
      spatialHolderHalfNorm 2 (s.velocity r - V r) ≤ K * truncErr Λ V depth r)
    (hDepth : 2 ≤ depth)
    (hTail : ∀ r ∈ Icc 0 (P.slab (n + 1) t),
      K * truncErr Λ V depth r ≤ P.frequency (n + 2) ^ (-5 : ℝ))
    (hVSmooth : ContDiffOn ℝ ∞ (Function.uncurry V)
      (Icc 0 (P.slab (n + 1) t) ×ˢ (univ : Set Vec3)))
    (hApprox : ∀ r ∈ Icc t (P.slab (n + 1) t),
      fderiv ℝ (V r) 0 = fderiv ℝ (parent.velocity r) 0 +
        waveSwitch t w.rate r • InnerProductSpace.rankOne ℝ (d.amplitude r) (d.waveVector r) +
        rawError r ∧ ‖rawError r‖ ≤ P.frequency (n + 1) ^ (-1 / 3 : ℝ))
    (hStrength :
      P.strengthConstant⁻¹ * P.frequency (n + 1) ^ (1 / 4 : ℝ) ≤
        ‖d.waveVector d.crossing‖ * ‖d.amplitude d.crossing‖ ∧
      ‖d.waveVector d.crossing‖ * ‖d.amplitude d.crossing‖ ≤
        P.strengthConstant * P.frequency (n + 1) ^ (1 / 4 : ℝ) *
          (4 * Real.log (P.frequency (n + 3))) ^ 2)
    (hCoupling : Real.pi ≤ w.physicalNu d.waveVector d.amplitude d.crossing ∧
      w.physicalNu d.waveVector d.amplitude d.crossing ≤ 4 * Real.pi) :
    InductiveEulerWave P n parent child d.crossing := by
  let tail : Velocity := fun r => s.velocity r - V r
  have hActive : w.activeSlab window = Icc t (P.slab (n + 1) t) := by
    unfold MovingWaveVector.PhysicalAmplification.activeSlab
    rw [hSlab]
  have hFull {r : ℝ} (hr : r ∈ w.activeSlab window) : r ∈ Icc 0 (P.slab (n + 1) t) := by
    rw [hActive] at hr
    exact ⟨ht.trans hr.1, hr.2⟩
  have hVSlice (r : ℝ) (hr : r ∈ w.activeSlab window) : DifferentiableAt ℝ (V r) 0 := by
    have hs := hVSmooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x (_ : x ∈ (univ : Set Vec3)) => mem_prod.mpr ⟨hFull hr, mem_univ x⟩)
    exact ((contDiffOn_univ.mp hs).differentiable (by simp)) 0
  have hChildSplit (r : ℝ) (_ : r ∈ w.activeSlab window) : child.velocity r = V r + tail r := by
    rw [hChild]
    dsimp only [tail]
    abel
  have hc := growingCutoffCenter
    (b := P.exponentParameter) (q := P.order (n + 1)) (qNext := P.order (n + 2))
    (E := rawError) (parent := parent.velocity)
    d (P.frequency_step n) hμ P.exponentParameter_ge hHalf hChildSplit hVSlice
    (fun r hr => ⟨(hTails 2 hDepth r (hFull hr)).1,
      (hTailTwo r (hFull hr)).trans (by
        rw [← P.frequency_step (n + 1)]
        exact hTail r (hFull hr))⟩)
    (fun r hr => hApprox r (hActive ▸ hr))
  let E := fun r => rawError r + fderiv ℝ (tail r) 0
  refine
    { oscillation := osc
      waveVector := d.waveVector
      amplitude := d.amplitude
      cutoff := waveSwitch t w.rate
      error := E
      center := hCenter
      activation_step := ?_
      oscillation_bound := hOsc
      correction_bound := by simpa only [hChild] using hCorrection
      oscillation_vanishes := hVanish
      oscillation_support := hSupport
      gradient_split := ?_
      error_bound := ?_
      cutoff_complete := ?_
      strength_at_crossing := hStrength
      coupling_at_crossing := ?_
      ratio_at_crossing := ?_ }
  · exact ⟨sub_nonneg.mpr d.crossing_in_slab.1, hHalf⟩
  · intro r hr
    have h := (hc r (hActive.symm ▸ hr)).1
    simpa only [InnerProductSpace.rankOne_def] using h
  · intro r hr
    exact (hc r (hActive.symm ▸ hr)).2
  · exact fun r hr => d.waveSwitch_eq_one_after hr.1
  · have hAt := hGradient (hActive ▸ d.crossing_in_slab)
    simp only [MovingWaveVector.PhysicalAmplification.physicalNu, hAt] at hCoupling
    exact hCoupling
  · have hAt := hGradient (hActive ▸ d.crossing_in_slab)
    have hRatio := d.crossing_ratio
    simp only [MovingWaveVector.PhysicalAmplification.physicalNu, MovingWaveVector.PhysicalAmplification.physicalEta, hAt] at hRatio
    exact hRatio

end InductiveEulerWave

/-- Attach the central proof and selected crossing to the same child produced
by the quantitative hierarchy cutoff. The exit coupling is taken from the
certified prefix. -/
def InductiveEulerStep.ofPhysicalHierarchyCutoff'
    {P : InductiveEulerParameters} {n depth : ℕ} {hLife : P.LifetimeBounds} {tip : InductiveEulerTip P n}
    (pre : InductiveEulerPrefix P hLife n tip)
    (w : MovingWaveVector.LaterPhysicalWindow tip.older.velocity tip.parent.velocity tip.wave.waveVector
      tip.wave.amplitude tip.wave.error tip.nextActivation (P.slab (n + 2) tip.nextActivation))
    (d : MovingWaveVector.LaterWaveSelection tip.parent.velocity w.physical P.comparisonConstant
      (inductionHalfLength P.frequency (n + 1)) (P.frequency (n + 2))
      (4 * Real.log (P.frequency (n + 4))) (P.frequency (n + 1) ^ 9))
    {Λ K : ℝ} {ψ : Vec3 → ℝ} {V osc : Velocity} {rawError : ℝ → Vec3 →L[ℝ] Vec3}
    (s : CutoffChild (P.slab (n + 2) tip.nextActivation) Λ ψ V)
    (child : InductiveEulerStage P (n + 2) tip.nextActivation) (hChild : child.velocity = s.velocity)
    (hLarge : Real.exp 4 ≤ P.frequency 0) (hConst : 18 * Real.exp 3 ≤ P.strengthConstant)
    (hOsc : ∀ t ∈ Icc 0 (P.slab (n + 2) tip.nextActivation), ∀ x, ‖osc t x‖ ≤ (P.frequency (n + 2))⁻¹)
    (hCorrection : ∀ m ≤ P.order (n + 2), ∀ t ∈ Icc 0 (P.slab (n + 2) tip.nextActivation),
      let v := child.velocity t - tip.parent.velocity t - osc t
      SpatialHolderHalf m v ∧ spatialHolderHalfNorm m v ≤ (P.frequency (n + 2))⁻¹)
    (hVanish : ∀ t ∈ Icc 0 tip.nextActivation, osc t = 0)
    (hSupport : ∀ t ∈ Icc 0 (P.slab (n + 2) tip.nextActivation), ∀ x, osc t x ≠ 0 →
      ∃ z : Fin 3 → ℤ, dist (latticeVector z) x ≤ (P.frequency (n + 1))⁻¹)
    (hTails : ∀ m ≤ depth, ∀ r ∈ Icc 0 (P.slab (n + 2) tip.nextActivation),
      SpatialHolderHalf m (s.velocity r - V r) ∧
      spatialHolderHalfNorm m (s.velocity r - V r) ≤ K * Λ ^ ((m : ℤ) - depth) * spatialHolderHalfNorm depth (V r))
    (hTailTwo : ∀ r ∈ Icc 0 (P.slab (n + 2) tip.nextActivation),
      spatialHolderHalfNorm 2 (s.velocity r - V r) ≤ K * truncErr Λ V depth r)
    (hDepth : 2 ≤ depth)
    (hTail : ∀ t ∈ Icc 0 (P.slab (n + 2) tip.nextActivation),
      K * truncErr Λ V depth t ≤ P.frequency (n + 3) ^ (-5 : ℝ))
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 (P.slab (n + 2) tip.nextActivation) ×ˢ
      (univ : Set Vec3)))
    (hApprox : ∀ t ∈ Icc tip.nextActivation (P.slab (n + 2) tip.nextActivation),
      fderiv ℝ (V t) 0 = fderiv ℝ (tip.parent.velocity t) 0 +
        waveSwitch tip.nextActivation w.physical.rate t •
          InnerProductSpace.rankOne ℝ (d.crossing.amplitude t) (d.crossing.waveVector t) + rawError t ∧
      ‖rawError t‖ ≤ P.frequency (n + 2) ^ (-1 / 3 : ℝ)) :
    InductiveEulerStep tip := by
  have hInitial : 2 ≤ P.frequency 0 := by
    have h : (2 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    exact h.trans hLarge
  have hMono := frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency
    P.exponentParameter_ge (one_le_two.trans hInitial) P.frequency_step
  have hμ : 2 ≤ P.frequency (n + 1) := hInitial.trans (hMono (Nat.zero_le _))
  have hRatio : w.physical.ratio = couplingRatioOfGain (4 * Real.log (P.frequency (n + 3))) := by
    unfold MovingWaveVector.PhysicalAmplification.ratio MovingWaveVector.PhysicalAmplification.firstCoupling
      MovingWaveVector.PhysicalAmplification.thirdCoupling MovingWaveVector.PhysicalAmplification.basis
    rw [w.preceding_vector_eq, w.preceding_amplitude_eq, w.older_gradient_eq]
    exact tip.wave.ratio_at_crossing
  have hStrength := InductiveEulerWave.growingCrossingStrength d.crossing rfl hLarge hConst hRatio
  have hAt : d.crossing.crossing ∈ Icc tip.nextActivation (P.slab (n + 2) tip.nextActivation) :=
    ⟨d.crossing.crossing_in_slab.1, d.crossing.crossing_in_slab.2.trans_eq d.clock_eq⟩
  have hCoupling := pre.later_wave_exit_coupling hLarge w d
  have hCoupling' : Real.pi ≤ w.physical.physicalNu d.crossing.waveVector d.crossing.amplitude d.crossing.crossing ∧
      w.physical.physicalNu d.crossing.waveVector d.crossing.amplitude d.crossing.crossing ≤ 4 * Real.pi := by
    simp only [MovingWaveVector.PhysicalAmplification.physicalNu, w.parent_gradient_eq hAt]
    exact ⟨hCoupling.1,hCoupling.2.1⟩
  let wave := InductiveEulerWave.ofGrowingCrossingCutoff' tip.parent child s hChild d.crossing
    hμ tip.next_activation_nonnegative d.clock_eq d.crossing_in_first_half w.parent_gradient_eq d.center
    hOsc (by simpa only [hChild] using hCorrection) (fun _ => hVanish) hSupport
    hTails hTailTwo hDepth hTail hV hApprox hStrength hCoupling'
  exact InductiveEulerStep.ofLaterWaveSelection tip w d child wave rfl rfl

/-- The divergence of a difference of fields differentiable at `x`. -/
theorem divergence_sub' {f g : Vec3 → Vec3} {x : Vec3} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) : divergence (f - g) x = divergence f x - divergence g x := by
  unfold divergence
  rw [fderiv_sub hf hg]
  simp [Finset.sum_sub_distrib]

/-- **The deformation of the cutoff child from Lemma 5.10** (item 4 of the proof of Theorem 7.1,
sections/08b_induction.tex:419-426; Lemma 5.10 applied to the cutoff tail `v = S_Λ V - V`): the
child `S_Λ V = V + v` has a label flow with deformation bound `C` as soon as `v` is smooth,
periodic, divergence free with two derivatives at most `lam` (`h510`, the content of 5.10 at `V`). -/
theorem deformation_of_5_10 {T C lam Λ : ℝ} {ψ : Vec3 → ℝ} {V : Velocity}
    (s : CutoffChild T Λ ψ V)
    (hVsm : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hVper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (V t))
    (hVdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (V t) x = 0)
    (hv2 : ∀ t ∈ Icc 0 T, ∀ j ≤ 2, ∀ x, ‖iteratedFDeriv ℝ j (s.velocity t - V t) x‖ ≤ lam)
    (h510 : ∀ v : Velocity, ContDiffOn ℝ ∞ (Function.uncurry v) (Icc 0 T ×ˢ (univ : Set Vec3)) →
      (∀ t ∈ Icc 0 T, SpatiallyPeriodic (v t)) → (∀ t ∈ Icc 0 T, ∀ x, divergence (v t) x = 0) →
      (∀ t ∈ Icc 0 T, ∀ j ≤ 2, ∀ x, ‖iteratedFDeriv ℝ j (v t) x‖ ≤ lam) →
      ∃ Yf : ℝ → Velocity, ChildFlow.DeformationOn (V + v) Yf T C) :
    ∃ Y : ℝ → Velocity, ChildFlow.DeformationOn s.velocity Y T C := by
  obtain ⟨Yf, hY⟩ := h510 (s.velocity - V) (s.smooth_velocity.sub hVsm)
    (fun t ht n x => by
      show s.velocity t (x + latticeVector n) - V t (x + latticeVector n) =
        s.velocity t x - V t x
      rw [s.periodic_velocity t n x, hVper t ht n x])
    (fun t ht x => by
      have hs : ContDiff ℝ ∞ (s.velocity t) := contDiff_slice' (f := s.velocity) s.smooth_velocity ht
      have hv := contDiff_slice' hVsm ht
      show divergence (s.velocity t - V t) x = 0
      rw [divergence_sub' (hs.differentiable (by simp)).differentiableAt
        (hv.differentiable (by simp)).differentiableAt]
      have h0 : divergence (s.velocity t) x = 0 := s.divergence_free t ht x
      rw [h0, hVdiv t ht x, sub_zero])
    hv2
  exact ⟨Yf, by rwa [add_sub_cancel] at hY⟩

section Scheduled

variable {P : InductiveEulerParameters} {n : ℕ} {activationOld activation : ℝ}

local notation "Tchild" => P.slab (n + 1) activation
local notation "Tparent" => P.slab n activationOld
local notation "parentFrequency" => P.frequency n
local notation "childFrequency" => P.frequency (n + 1)
local notation "nextFrequency" => P.frequency (n + 2)
local notation "order" => P.order (n + 1)
local notation "nextOrder" => P.order (n + 2)
local notation "depth" => 6 * frequencyExponent P.exponentParameter nextOrder


/-- Schedule facts of a step: the parent frequency is at least `2`, the order is nondecreasing, and the depth dominates `max 2 order`. -/
theorem physicalWave_schedule (hInitial : 2 ≤ P.frequency 0) :
    2 ≤ parentFrequency ∧ order ≤ nextOrder ∧ max 2 order ≤ depth := by
  have hMono := frequencySchedule_frequency_mono P.exponentParameter P.order P.frequency
    P.exponentParameter_ge (one_le_two.trans hInitial) P.frequency_step
  have hOrder := (frequencySchedule_order_steps P.threshold P.frequency P.order P.initial_order
    P.initial_threshold hMono P.order_maximum n).1
  have hExponent : nextOrder + 1 ≤ frequencyExponent P.exponentParameter nextOrder := by
    unfold frequencyExponent
    exact Nat.le_mul_of_pos_left _ (by have := P.exponentParameter_ge; positivity)
  have hDepth : 2 * (nextOrder + 1) ≤ depth := by omega
  exact ⟨hInitial.trans (hMono (Nat.zero_le n)), hOrder, max_le (by omega) (by omega)⟩

local notation "scheduledFrequency" => parentFrequency ^ frequencyExponent P.exponentParameter order
local notation "scheduledNext" => scheduledFrequency ^ frequencyExponent P.exponentParameter nextOrder

/-- The next frequency of a step equals the scheduled next frequency (rewriting with `frequency_step`). -/
theorem physicalWave_next_frequency :
    nextFrequency = scheduledNext := by
  rw [P.frequency_step (n + 1), P.frequency_step n]


/-- Apply the scheduled cutoff estimates to the same physical field on which
the deformation estimate is established. -/
theorem exists_inductiveEulerChild_of_physicalCutoff'
    (parent : InductiveEulerStage P n activationOld)
    {V RV oscillation mean : Velocity} {ψ : Vec3 → ℝ}
    (s : CutoffChild Tchild (scheduledFrequency ^ 5) ψ V)
    {C K Cstep Cmean : ℝ}
    (hTails : ∀ m ≤ depth, ∀ t ∈ Icc 0 Tchild, SpatialHolderHalf m (s.velocity t - V t) ∧
      spatialHolderHalfNorm m (s.velocity t - V t) ≤
        K * (scheduledFrequency ^ 5) ^ ((m : ℤ) - depth) * spatialHolderHalfNorm depth (V t))
    (hRes : ∀ t ∈ Icc 0 Tchild, SpatialHolderHalf 1 (s.residual t) ∧
      spatialHolderHalfNorm 1 (s.residual t) ≤ C * scheduledNext ^ (-7 / 2 : ℝ) + scheduledNext ^ (-5 : ℝ))
    (hTwo : ∀ t ∈ Icc 0 Tchild, SpatialHolderHalf 2 (s.velocity t - V t) ∧
      spatialHolderHalfNorm 2 (s.velocity t - V t) ≤ scheduledNext ^ (-5 : ℝ))
    (hPress57 : ∀ t ∈ Icc 0 Tchild, ∀ x v : Vec3,
      ⟪v, fderiv ℝ (gradient (s.pressure t - parent.pressure t)) x v⟫_ℝ ≤
        (Cstep * scheduledFrequency ^ (-1 / 4 : ℝ) +
          (C * scheduledNext ^ (-7 / 2 : ℝ) + scheduledNext ^ (-5 : ℝ))) * ‖v‖ ^ 2)
    (hApprox : Lib.S678a.StepApproxBounds P n activation V RV oscillation mean Cstep Cmean)
    (hInitial : 2 ≤ P.frequency 0) (hSlab : Tchild ≤ Tparent)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hKμ : K ≤ parentFrequency) (hMeanμ : Cmean ≤ parentFrequency)
    (hCstep : Cstep ≤ childFrequency ^ (1 / 32 : ℝ))
    (hLarge : max 2 ((2 * C) ^ (2 : ℕ)) ≤ nextFrequency)
    (hV : ∀ t ∈ Icc 0 Tchild, SpatialHolderHalf depth (V t))
    (hSplit : ∀ t ∈ Icc 0 Tchild, V t = parent.velocity t + oscillation t + mean t)
    (hVsm : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 Tchild ×ˢ (univ : Set Vec3)))
    (hVper : ∀ t ∈ Icc 0 Tchild, SpatiallyPeriodic (V t))
    (hVdiv : ∀ t ∈ Icc 0 Tchild, ∀ x, divergence (V t) x = 0)
    (h510 : ∀ v : Velocity, ContDiffOn ℝ ∞ (Function.uncurry v) (Icc 0 Tchild ×ˢ (univ : Set Vec3)) →
      (∀ t ∈ Icc 0 Tchild, SpatiallyPeriodic (v t)) →
      (∀ t ∈ Icc 0 Tchild, ∀ x, divergence (v t) x = 0) →
      (∀ t ∈ Icc 0 Tchild, ∀ j ≤ 2, ∀ x, ‖iteratedFDeriv ℝ j (v t) x‖ ≤ childFrequency ^ (-5 / 2 : ℝ)) →
      ∃ Yf : ℝ → Velocity, ChildFlow.DeformationOn (V + v) Yf Tchild
        (Cstep * childFrequency ^ (1 / 4 : ℝ))) :
    ∃ child : InductiveEulerStage P (n + 1) activation,
      child.velocity = s.velocity ∧ child.pressure = s.pressure ∧
      (∀ t ∈ Icc 0 Tchild, ∀ x, ‖oscillation t x‖ ≤ childFrequency⁻¹) ∧
      ∀ m ≤ order, ∀ t ∈ Icc 0 Tchild, SpatialHolderHalf m (child.velocity t - parent.velocity t - oscillation t) ∧
        spatialHolderHalfNorm m (child.velocity t - parent.velocity t - oscillation t) ≤ childFrequency⁻¹ := by
  obtain ⟨hμ, hOrder, hDepth⟩ := physicalWave_schedule (P := P) (n := n) hInitial
  have hChildEq : childFrequency = scheduledFrequency := P.frequency_step n
  have hNextEq : nextFrequency = scheduledNext := physicalWave_next_frequency
  have hFreq : 1 ≤ scheduledFrequency := one_le_pow₀ (by linarith)
  have hErr (t : ℝ) (ht : t ∈ Icc 0 Tchild) :
      K * truncErr (scheduledFrequency ^ 5) V depth t ≤ scheduledNext ^ (-5 : ℝ) :=
    truncErr_le_next (V := V) hμ P.exponentParameter_ge hKμ t (hV t ht)
      (by simpa only [hChildEq] using hApprox.velocity_size t ht)
  have hInc := scheduled_increment' s hTails hμ P.exponentParameter_ge hOrder
    ((le_max_right 2 order).trans hDepth) hMeanμ hK hV hSplit
    (by simpa only [hChildEq] using hApprox.mean_size) hErr
  have hΛ : 0 < scheduledFrequency ^ 5 := pow_pos (by linarith) _
  obtain ⟨Y, hFlow⟩ := deformation_of_5_10 s hVsm hVper hVdiv
    (fun t ht j hj x => by
      refine (norm_iteratedFDeriv_le_spatialHolderHalfNorm (hTwo t ht).1 hj x).trans ?_
      refine (hTwo t ht).2.trans ?_
      rw [hChildEq]
      calc _ ≤ scheduledFrequency ^ (-5 : ℝ) :=
            Real.rpow_le_rpow_of_nonpos (by linarith) (le_self_pow₀ hFreq
              (Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos (by decide) P.exponentParameter_ge)
                (Nat.succ_pos _)))) (by norm_num)
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hFreq (by norm_num))
    h510
  have hParent (t : ℝ) (ht : t ∈ Icc 0 Tchild) (x : Vec3) : ‖parent.velocity t x‖ ≤ parentFrequency :=
    ((parent.torusVelocity t).norm_coe_le_norm _).trans (parent.velocity_bound t ⟨ht.1, ht.2.trans hSlab⟩)
  have hT := scheduled_T2_T3' s hμ P.exponentParameter_ge hC hSlab
    (by simpa only [hChildEq] using hCstep) (by simpa only [hNextEq] using hLarge)
    (by simpa only [hChildEq] using hFlow) hParent
    (by simpa only [hChildEq] using hApprox.oscillation_size) (hInc 0 (Nat.zero_le _))
    (by simpa only [hNextEq] using hRes)
    (fun t ht => contDiff_slice' parent.smooth_pressure ⟨ht.1, ht.2.trans hSlab⟩)
    parent.pressure_hessian
    (by simpa only [hChildEq, hNextEq] using hPress57)
  obtain ⟨hU, hY, hR, hPress⟩ := hT
  have hRadius : scheduledFrequency ^ (5 : ℕ) = childFrequency ^ (5 : ℕ) := by rw [hChildEq]
  have hInU (t : ℝ) (ht : t ∈ Icc 0 Tchild) : ‖s.torusVelocity t‖ ≤ childFrequency :=
    (hU t ht).trans_eq hChildEq.symm
  have hInFlow : ChildFlow.DeformationOn s.velocity Y Tchild childFrequency := by rwa [hChildEq]
  have hInR (t : ℝ) (ht : t ∈ Icc 0 Tchild) (x : Vec3) :
      ‖s.residual t x‖ ≤ nextFrequency ^ (-3 : ℝ) := by rw [hNextEq]; exact hR t ht x
  let child := InductiveEulerStage.ofCutoffChild s rfl hRadius hInU hInFlow hInR hPress
  have hVel : child.velocity = s.velocity := InductiveEulerStage.ofCutoffChild_velocity _ _ _ _ _ _ _
  have hPressEq : child.pressure = s.pressure :=
    InductiveEulerStage.ofCutoffChild_pressure _ _ _ _ _ _ _
  have hOsc := (induction_child_oscillation_and_deformation_budget hFreq
    (by simpa only [hChildEq] using hCstep)).1
  refine ⟨child, hVel, hPressEq, fun t ht x => ?_, ?_⟩
  · rw [hChildEq]
    exact (hApprox.oscillation_size t ht x).trans (by simpa only [hChildEq] using hOsc)
  · simpa only [hChildEq,hVel] using hInc

end Scheduled

end

end TorusEuler.Paper.Lib.S678a
