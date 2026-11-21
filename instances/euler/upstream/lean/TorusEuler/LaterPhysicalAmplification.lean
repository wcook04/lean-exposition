import Mathlib.Analysis.Real.Pi.Bounds
import TorusEuler.EulerLimitClosure
import TorusEuler.FrameCouplingVariation
import TorusEuler.FirstWaveInitialization
import TorusEuler.InductionChildEstimates
import TorusEuler.LocalizedAmplitudeComparison
import TorusEuler.ParentVelocityEstimates
import TorusEuler.PeriodicEulerLimit
import TorusEuler.InductionAmplificationSmallness
import TorusEuler.InductiveActivationClock
import TorusEuler.PhysicalGrowthPropagator
import TorusEuler.Piola

/-! The physical amplification window for a later stage of Theorem 7.1. -/

open ContinuousLinearMap Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.MovingWaveVector

open AmplificationCrossing (crossingHorizon)

/-- The next physical comparison slab fits inside the preceding active slab. -/
theorem later_comparisonSlab_subset_parent
    {p t oldHalf half : ℝ}
    (hAdvance : p ≤ t) (hDelay : t - p ≤ oldHalf)
    (hHalf : 4 * half ≤ oldHalf) (hNonnegative : 0 ≤ half) :
    Icc t (t + 2 * half) ⊆ Icc p (p + 2 * oldHalf) := by
  intro u hu
  refine ⟨hAdvance.trans hu.1, hu.2.trans ?_⟩
  linarith only [hDelay, hHalf, hNonnegative]

/-- A parent stored on its smooth closed slab has a continuous actual
central gradient on every comparison subslab. -/
theorem continuousOn_central_gradient_of_smooth
    {u : Velocity} {T start finish : ℝ}
    (hT : 0 < T) (hStart : 0 ≤ start) (hFinish : finish ≤ T)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3))) :
    ContinuousOn (fun t => fderiv ℝ (u t) 0) (Icc start finish) := by
  have hGrad : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => fderiv ℝ (u z.1) z.2)
      (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    contDiffOn_spatialDerivative_of_joint_contDiff (uniqueDiffOn_Icc hT) (by simpa using hU)
  let e : ℝ → ℝ × Vec3 := fun t => (t, 0)
  have he : Continuous e := continuous_id.prodMk continuous_const
  have hm : MapsTo e (Icc start finish) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    fun _ ht => mem_prod.mpr ⟨⟨hStart.trans ht.1, ht.2.trans hFinish⟩, mem_univ _⟩
  exact hGrad.continuousOn.comp he.continuousOn hm

/-- The exact older pair, older gradient and correction underlying a
physical comparison. Its strain is the gradient of the actual parent. -/
structure LaterPhysicalWindow (older parent : Velocity) (kp ap : ℝ → Space)
    (E : ℝ → Space →L[ℝ] Space) (t₀ finish : ℝ) where
  physical : PhysicalAmplification (Icc t₀ finish) t₀
  preceding_vector_eq : physical.kp = kp
  preceding_amplitude_eq : physical.ap = ap
  older_gradient_eq : physical.B = fun t => fderiv ℝ (older t) 0
  error_eq : physical.E = E
  parent_gradient_eq : EqOn physical.gradient (fun t => fderiv ℝ (parent t) 0) (Icc t₀ finish)

/-- The completed cutoff in (T4) constructs a physical amplification window
over the actual new parent. The physical error field is the given stage
error, whose continuity follows from the gradient splitting. -/
theorem exists_laterPhysicalWindow_of_stage
    {older parent : Velocity} {kp ap : ℝ → Space}
    {E : ℝ → Space →L[ℝ] Space} {cutoff : ℝ → ℝ}
    {startPrev endPrev t₀ finish : ℝ}
    (hTime : t₀ ≤ finish) (hSlab : Icc t₀ finish ⊆ Icc startPrev endPrev)
    (hOlder : ContinuousOn (fun t => fderiv ℝ (older t) 0) (Icc t₀ finish))
    (hParent : ContinuousOn (fun t => fderiv ℝ (parent t) 0) (Icc t₀ finish))
    (hDiv : ∀ t ∈ Icc t₀ finish, divergence (older t) 0 = 0)
    (hPair : ∀ t ∈ Icc startPrev endPrev,
      kp t ≠ 0 ∧ ap t ≠ 0 ∧ ⟪kp t, ap t⟫_ℝ = 0)
    (hk : ∀ t ∈ Icc startPrev endPrev, HasDerivWithinAt kp
      (-((fderiv ℝ (older t) 0).adjoint (kp t))) (Icc startPrev endPrev) t)
    (ha : ∀ t ∈ Icc startPrev endPrev, HasDerivWithinAt ap
      (affineWaveAmplitudeOperator (fderiv ℝ (older t) 0) (kp t) (ap t))
      (Icc startPrev endPrev) t)
    (hT4 : ∀ t ∈ Icc startPrev endPrev,
      fderiv ℝ (parent t) 0 = fderiv ℝ (older t) 0 +
        cutoff t • (innerSL ℝ (kp t)).smulRight (ap t) + E t)
    (hComplete : ∀ t ∈ Icc t₀ finish, cutoff t = 1)
    (hν : 0 < entry (frame kp ap t₀) (fderiv ℝ (older t₀) 0) 0 1)
    (hη : 0 < entry (frame kp ap t₀) (fderiv ℝ (older t₀) 0) 2 1) :
    Nonempty (LaterPhysicalWindow older parent kp ap E t₀ finish) := by
  let I := Icc t₀ finish
  let B (t : ℝ) := fderiv ℝ (older t) 0
  let M (t : ℝ) := fderiv ℝ (parent t) 0
  let R (t : ℝ) := InnerProductSpace.rankOne ℝ (ap t) (kp t)
  have hSplit (t : ℝ) (ht : t ∈ I) : M t = B t + R t + E t := by
    simpa only [M, B, R, InnerProductSpace.rankOne_def, hComplete t ht, one_smul] using
      hT4 t (hSlab ht)
  have hkc : ContinuousOn kp I := (HasDerivWithinAt.continuousOn hk).mono hSlab
  have hac : ContinuousOn ap I := (HasDerivWithinAt.continuousOn ha).mono hSlab
  have hR : ContinuousOn R I := by
    let L : Space →L[ℝ] Space →L[ℝ] (Space →L[ℝ] Space) := InnerProductSpace.rankOne ℝ
    exact (L.continuous.comp_continuousOn hac).clm_apply hkc
  have hE : ContinuousOn E I :=
    ((hParent.sub hOlder).sub hR).congr fun t ht => by
      change E t = M t - B t - R t
      rw [hSplit t ht]
      abel
  let w : PhysicalAmplification I t₀ :=
    { kp := kp
      ap := ap
      B := B
      E := E
      compact := isCompact_Icc
      activation := left_mem_Icc.mpr hTime
      older_continuous := hOlder
      error_continuous := hE
      trace_zero := fun t ht => (divergence_eq_trace_fderiv (older t) 0).symm.trans (hDiv t ht)
      preceding_data := fun t ht => hPair t (hSlab ht)
      preceding_vector := fun t ht => (hk t (hSlab ht)).mono hSlab
      preceding_amplitude := fun t ht => (ha t (hSlab ht)).mono hSlab
      first_coupling_positive := hν
      third_coupling_positive := hη }
  exact ⟨⟨w, rfl, rfl, rfl, rfl, fun t ht => (hSplit t ht).symm⟩⟩

namespace PhysicalAmplification

/-- The explicit physical-frame estimate (6.6) for the actual older
gradient on a closed comparison slab. -/
theorem errorSize_le_of_older_gradient {t₀ finish Bmax Btmax Emax : ℝ}
    (w : PhysicalAmplification (Icc t₀ finish) t₀)
    (hRatio : w.ratio ≤ 1)
    (Bt : ℝ → Space →L[ℝ] Space)
    (hBd : ∀ t ∈ Icc t₀ finish, HasDerivWithinAt w.B (Bt t) (Icc t₀ finish) t)
    (hB : ∀ t ∈ Icc t₀ finish, ‖w.B t‖ ≤ Bmax)
    (hBt : ∀ t ∈ Icc t₀ finish, ‖Bt t‖ ≤ Btmax)
    (hE : ∀ t ∈ Icc t₀ finish, ‖w.E t‖ ≤ Emax) :
    0 ≤ w.errorSize ∧ w.errorSize ≤
      8 * ((finish - t₀) * (Bmax ^ 2 + Btmax) / w.thirdCoupling +
        Bmax / w.rate + Emax / w.firstCoupling) := by
  have hsome := w.preceding_data t₀ w.activation
  have hrate := normalized_rates_of_physical_error
    (e := w.basis) (B := w.B) (E := w.E) w.compact w.activation
    (orthonormal_movingFrame hsome.1 hsome.2.1 hsome.2.2) w.continuousOn_basis
    w.older_continuous w.error_continuous w.initialStrength_pos w.first_coupling_positive
    w.third_coupling_positive hRatio
  refine ⟨hrate.1, ?_⟩
  have hη : w.thirdCoupling ≤ w.firstCoupling := by
    have h := (div_le_iff₀ w.first_coupling_positive).mp hRatio
    rwa [one_mul] at h
  exact amplificationPhysicalError_le_movingFrame (k := w.kp) (a := w.ap) (B := w.B)
    (E := w.E) w.activation.2 w.rate_pos w.trace_zero w.preceding_data w.preceding_vector
    (fun t ht => by simpa only [affineWaveAmplitudeOperator_apply] using w.preceding_amplitude t ht)
    hBd hB hBt hE w.third_coupling_positive hη

/-- With the physical endpoint chosen at twice the half-length the affine
clock reaches that same endpoint and maps the entire normalized slab back. -/
theorem clock_comparison_window {t₀ half : ℝ}
    (w : PhysicalAmplification (Icc t₀ (t₀ + 2 * half)) t₀) :
    let T := 2 * w.rate * half
    w.clock T = t₀ + 2 * half ∧ MapsTo w.clock (Icc 0 T) (Icc t₀ (t₀ + 2 * half)) := by
  dsimp only
  have hr := w.rate_pos.ne'
  have hclock : w.clock (2 * w.rate * half) = t₀ + 2 * half := by
    unfold clock
    field_simp
  refine ⟨hclock, fun τ hτ => ?_⟩
  refine ⟨?_, ?_⟩
  · simpa only [clock_zero] using w.strictMono_clock.monotone hτ.1
  · simpa only [hclock] using w.strictMono_clock.monotone hτ.2

/-- The frozen shear is the physical rate divided by twice the first
coupling. -/
theorem shear_eq_rate_div_firstCoupling {I : Set ℝ} {t₀ : ℝ}
    (w : PhysicalAmplification I t₀) :
    w.shear = w.rate / (2 * w.firstCoupling) := by
  have hν : 0 < 2 * w.firstCoupling := mul_pos (by norm_num) w.first_coupling_positive
  have hsq : w.rate ^ 2 = 2 * w.initialStrength * w.firstCoupling :=
    amplificationGrowthRate_sq w.initialStrength_pos w.first_coupling_positive
  unfold shear
  apply (div_eq_div_iff w.rate_pos.ne' hν.ne').mpr
  rw [← pow_two]
  rw [hsq]
  ring


/-- Both center bounds in (5.21) fit the same parameter (D=mu^9)
as the actual parent gradient. -/
theorem exists_later_center_bounds (CStrength : ℝ) (hCStrength : 0 < CStrength) :
    ∃ N : ℝ, 1 < N ∧
      ∀ {I : Set ℝ} {t₀ μ L : ℝ} (w : PhysicalAmplification I t₀),
        N ≤ μ → 0 < L → L ≤ (Real.log μ) ^ 2 →
        Real.pi ≤ w.firstCoupling →
        w.ratio = couplingRatioOfGain L →
        w.rate ≤ Real.sqrt (8 * CStrength * Real.pi) * μ ^ (1 / 8 : ℝ) * L →
        252 * Real.exp 1 * w.shear ≤ μ ^ 9 ∧
          2 / (w.firstCoupling * w.ratio) ≤ μ ^ 9 := by
  let Cr := Real.sqrt (8 * CStrength * Real.pi)
  let coefficients (i : Bool) := if i then 126 * Real.exp 1 * Cr else (2 : ℝ)
  let exponent (i : Bool) := if i then (1 : ℕ) else 2
  let decay (i : Bool) := if i then (7 / 8 : ℝ) else 1
  have hCoef : ∀ i, 0 ≤ coefficients i := by intro i; cases i <;> dsimp [coefficients, Cr] <;> positivity
  have hDecay : ∀ i, 0 < decay i := by intro i; cases i <;> norm_num [decay]
  obtain ⟨N, hN, hBudget⟩ := exists_uniform_log_gain_budget coefficients exponent decay hCoef hDecay
  refine ⟨N, hN, ?_⟩
  intro I t₀ μ L w hμ hL hLog hν hRatio hRate
  have hμ₁ : 1 ≤ μ := hN.le.trans hμ
  have hμ₀ : 0 < μ := zero_lt_one.trans_le hμ₁
  have hBig : μ ≤ μ ^ 9 := le_self_pow₀ hμ₁ (by decide)
  have hOne : 1 ≤ w.firstCoupling := by linarith [Real.pi_gt_three, hν]
  have hOneTwo : 2 ≤ 2 * w.firstCoupling := by linarith
  have h1 : 126 * Real.exp 1 * Cr * L ≤ μ ^ (7 / 8 : ℝ) := by
    simpa [coefficients, exponent, decay] using
      hBudget μ hμ L hL.le hLog true
  have h2' : 2 * L ^ 2 ≤ μ := by
    simpa [coefficients, exponent, decay] using hBudget μ hμ L hL.le hLog false
  have hPowers : μ ^ (7 / 8 : ℝ) * μ ^ (1 / 8 : ℝ) = μ := by
    rw [← Real.rpow_add hμ₀, show (7 / 8 + 1 / 8 : ℝ) = 1 by norm_num, Real.rpow_one]
  constructor
  · calc
      252 * Real.exp 1 * w.shear = (252 * Real.exp 1) * (w.rate / (2 * w.firstCoupling)) := by
        rw [w.shear_eq_rate_div_firstCoupling]
      _ ≤ (252 * Real.exp 1) * (w.rate / 2) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left w.rate_pos.le (by norm_num) hOneTwo)
          (by positivity)
      _ = (126 * Real.exp 1) * w.rate := by ring
      _ ≤ (126 * Real.exp 1) * (Cr * μ ^ (1 / 8 : ℝ) * L) :=
        mul_le_mul_of_nonneg_left hRate (by positivity)
      _ = (126 * Real.exp 1 * Cr * L) * μ ^ (1 / 8 : ℝ) := by ring
      _ ≤ μ ^ (7 / 8 : ℝ) * μ ^ (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = μ := hPowers
      _ ≤ _ := hBig
  · calc
      2 / (w.firstCoupling * w.ratio) ≤ 2 / w.ratio :=
        div_le_div_of_nonneg_left (by norm_num) w.ratio_pos
          (le_mul_of_one_le_left w.ratio_pos.le hOne)
      _ = 2 * L ^ 2 := by rw [hRatio, couplingRatioOfGain, div_inv_eq_mul]
      _ ≤ μ := h2'
      _ ≤ _ := hBig

end PhysicalAmplification

end TorusEuler.MovingWaveVector


namespace TorusEuler

/-- The next half-length bound puts the whole new endpoint slab inside the
previous one when the activation is in the first half. -/
theorem nextSlab_le_of_halfLength {start activation half nextHalf : ℝ}
    (hcross : activation - start ≤ half) (hhalf : 4 * nextHalf ≤ half) (hpos : 0 < half) :
    activation + 2 * nextHalf < start + 2 * half := by
  linarith only [hcross, hhalf, hpos]

/-- The common upper strength constant also gives the reciprocal lower
constant used in the central-wave induction invariant. -/
theorem inductionCrossingStrengthConstants :
    2 ≤ 18 * Real.exp 3 ∧ (18 * Real.exp 3)⁻¹ ≤ Real.exp (-1) / 4 := by
  have hehi : 1 ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
  have hprod : Real.exp (-1) * Real.exp 3 = Real.exp 2 := by
    rw [← Real.exp_add]
    congr 1
    norm_num
  have he₂ : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  refine ⟨by linarith, ?_⟩
  rw [← one_div]
  exact (div_le_iff₀ (by positivity)).mpr (by linarith only [he₂, hprod])

/-- On a slab where the rank-one return formula holds, the actual gradient
split determines a continuous central error from continuous data. -/
theorem centralSplit_error_continuous {J : Set ℝ}
    {B child E : ℝ → Vec3 →L[ℝ] Vec3} {χ : ℝ → ℝ} {k a : ℝ → Vec3}
    (hB : ContinuousOn B J) (hchild : ContinuousOn child J) (hχ : ContinuousOn χ J)
    (hk : ContinuousOn k J) (ha : ContinuousOn a J)
    (hsplit : ∀ t ∈ J, child t = B t +
      χ t • (innerSL ℝ (k t)).smulRight (a t) + E t) :
    ContinuousOn E J := by
  have hrank : ContinuousOn (fun t => InnerProductSpace.rankOne ℝ (a t) (k t)) J :=
    ((InnerProductSpace.rankOne ℝ).continuous.comp_continuousOn ha).clm_apply hk
  refine ((hchild.sub hB).sub (hχ.smul hrank)).congr ?_
  intro t ht
  change E t = child t - B t - χ t • InnerProductSpace.rankOne ℝ (a t) (k t)
  rw [hsplit t ht, InnerProductSpace.rankOne_def]
  abel

namespace MovingWaveVector.PhysicalAmplification

variable {I : Set ℝ} {t₀ T scale peak next : ℝ}
  {w : PhysicalAmplification I t₀}

/-- The two scalar entries of the physical gradient are the actual frozen
couplings used when the growing wave becomes the preceding wave. -/
theorem GrowingCrossing.frozenCouplings
    (d : w.GrowingCrossing T scale peak next) :
    let t := d.crossing
    let ν := entry (frame d.waveVector d.amplitude t) (w.gradient t) 0 1
    let η := entry (frame d.waveVector d.amplitude t) (w.gradient t) 2 1
    0 < ν ∧ η / ν = next ∧
      |Real.log (ν / w.firstCoupling)| ≤ 2 * w.ratio := by
  have hν : 0 < w.physicalNu d.waveVector d.amplitude d.crossing :=
    (div_pos (mul_pos w.first_coupling_positive w.ratio_pos) (by norm_num)).trans_le
      (d.first_coupling_lower _ d.crossing_in_slab)
  have hνEq (t : ℝ) :
      entry (frame d.waveVector d.amplitude t) (w.gradient t) 0 1 =
        w.physicalNu d.waveVector d.amplitude t := by
    rfl
  have hηEq (t : ℝ) :
      entry (frame d.waveVector d.amplitude t) (w.gradient t) 2 1 =
        w.physicalEta d.waveVector d.amplitude t := by
    rfl
  dsimp only
  rw [hνEq, hηEq]
  exact ⟨hν, d.crossing_ratio, d.crossing_coupling_log⟩

/-- Restrict the previous wave to the next active slab and retain its exact
affine equations and the cutoff value after its crossing. -/
theorem GrowingCrossing.nextSlabData (d : w.GrowingCrossing T scale peak next)
    {finish : ℝ} (hfinish : finish ≤ w.clock T) :
    (∀ t ∈ Icc d.crossing finish, d.waveVector t ≠ 0 ∧ d.amplitude t ≠ 0 ∧
      ⟪d.waveVector t, d.amplitude t⟫_ℝ = 0) ∧
    (∀ t ∈ Icc d.crossing finish, HasDerivWithinAt d.waveVector
      (-((w.gradient t).adjoint (d.waveVector t))) (Icc d.crossing finish) t) ∧
    (∀ t ∈ Icc d.crossing finish, HasDerivWithinAt d.amplitude
      (affineWaveAmplitudeOperator (w.gradient t) (d.waveVector t) (d.amplitude t))
      (Icc d.crossing finish) t) ∧
    (∀ t ∈ Icc d.crossing finish, waveSwitch t₀ w.rate t = 1) := by
  have hsub : Icc d.crossing finish ⊆ w.activeSlab T := by
    intro t ht
    exact ⟨d.crossing_in_slab.1.trans ht.1, ht.2.trans hfinish⟩
  exact ⟨fun t ht => d.transverse t (hsub ht),
    fun t ht => (d.waveVector_derivative t (hsub ht)).mono hsub,
    fun t ht => (d.amplitude_derivative t (hsub ht)).mono hsub,
    fun _ ht => d.waveSwitch_eq_one_after ht.1⟩

/-- The same next-slab wave equations hold over the actual older gradient
whenever the earlier window identifies its physical gradient there. -/
theorem GrowingCrossing.nextSlabEquations_of_gradientEq
    (d : w.GrowingCrossing T scale peak next)
    {finish : ℝ} {B : ℝ → Space →L[ℝ] Space}
    (hfinish : finish ≤ w.clock T)
    (hB : EqOn w.gradient B (Icc d.crossing finish)) :
    (∀ t ∈ Icc d.crossing finish, HasDerivWithinAt d.waveVector
      (-((B t).adjoint (d.waveVector t))) (Icc d.crossing finish) t) ∧
    (∀ t ∈ Icc d.crossing finish, HasDerivWithinAt d.amplitude
      (affineWaveAmplitudeOperator (B t) (d.waveVector t) (d.amplitude t))
      (Icc d.crossing finish) t) := by
  obtain ⟨_, hk, ha, _⟩ := d.nextSlabData hfinish
  exact ⟨fun t ht => by simpa only [hB ht] using hk t ht,
    fun t ht => by simpa only [hB ht] using ha t ht⟩

/-- When the frozen gradient is written as the actual preceding stage
gradient, the previous crossing still fixes both couplings and their ratio. -/
theorem GrowingCrossing.frozenCouplings_of_gradientEq
    (d : w.GrowingCrossing T scale peak next) {B : ℝ → Space →L[ℝ] Space}
    (hB : w.gradient d.crossing = B d.crossing) (hnext : 0 < next) :
    let t := d.crossing
    let ν := entry (frame d.waveVector d.amplitude t) (B t) 0 1
    let η := entry (frame d.waveVector d.amplitude t) (B t) 2 1
    0 < ν ∧ 0 < η ∧ η / ν = next ∧
      |Real.log (ν / w.firstCoupling)| ≤ 2 * w.ratio := by
  dsimp only
  rw [← hB]
  obtain ⟨hν, hratio, hlog⟩ := d.frozenCouplings
  have hη := (div_eq_iff hν.ne').mp hratio
  exact ⟨hν, hη ▸ mul_pos hnext hν, hratio, hlog⟩

/-- The switched rank-one return in (T4) becomes the actual unswitched
splitting on the next interval. -/
theorem GrowingCrossing.nextGradientSplit
    (d : w.GrowingCrossing T scale peak next)
    {B child E : ℝ → Space →L[ℝ] Space} {finish : ℝ}
    (hfinish : finish ≤ w.clock T)
    (hsplit : ∀ t ∈ w.activeSlab T, child t = B t +
      waveSwitch t₀ w.rate t • (innerSL ℝ (d.waveVector t)).smulRight (d.amplitude t) + E t)
    {t : ℝ} (ht : t ∈ Icc d.crossing finish) :
    child t = B t + InnerProductSpace.rankOne ℝ (d.amplitude t) (d.waveVector t) + E t := by
  have ht' : t ∈ w.activeSlab T :=
    ⟨d.crossing_in_slab.1.trans ht.1, ht.2.trans hfinish⟩
  simpa only [d.waveSwitch_eq_one_after ht.1, one_smul, InnerProductSpace.rankOne_def]
    using hsplit t ht'

/-- At the prescribed peak the previous crossing supplies the two strength
bounds for the next activation, with the same constants for all gains. -/
theorem GrowingCrossing.strength_bounds_for_next
    {Lprev L : ℝ} (hscale : 0 < scale) (hLprev : 1 ≤ Lprev) (hstep : 640 * Lprev ≤ L)
    (hratio : w.ratio = couplingRatioOfGain Lprev)
    (d : w.GrowingCrossing T scale (scale ^ (-(3 / 4 : ℝ))) (couplingRatioOfGain L)) :
    (Real.exp (-1) / 4) * scale ^ (1 / 4 : ℝ) ≤
      ‖d.waveVector d.crossing‖ * ‖d.amplitude d.crossing‖ ∧
    ‖d.waveVector d.crossing‖ * ‖d.amplitude d.crossing‖ ≤
      (18 * Real.exp 3) * scale ^ (1 / 4 : ℝ) * L ^ 2 := by
  have hLprev₀ : 0 < Lprev := zero_lt_one.trans_le hLprev
  have hL : 1 ≤ L := by linarith
  have hgain : (Real.sqrt (w.ratio * couplingRatioOfGain L))⁻¹ = Lprev * L := by
    rw [hratio, Real.sqrt_eq_rpow, ← Real.rpow_neg (by unfold couplingRatioOfGain; positivity)]
    simpa only [neg_div] using (couplingRatioOfGain_step hLprev₀ hstep).2.2.1
  have hb := GrowingCrossing.strength_at_induction_peak w hscale d
  rw [hgain] at hb
  have hpos : 0 < scale ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hscale _
  have hlprod : 1 ≤ Lprev * L := one_le_mul_of_one_le_of_one_le hLprev hL
  constructor
  · calc
      _ ≤ (Real.exp (-1) / 4 * (Lprev * L)) * scale ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right (by positivity) hlprod) hpos.le
      _ ≤ _ := by simpa only [mul_comm ‖d.waveVector d.crossing‖ ‖d.amplitude d.crossing‖]
        using (le_div_iff₀ hpos).mp hb.1
  · calc
      ‖d.waveVector d.crossing‖ * ‖d.amplitude d.crossing‖ ≤
          (18 * Real.exp 3 * (Lprev * L)) * scale ^ (1 / 4 : ℝ) := by
        simpa only [mul_comm ‖d.waveVector d.crossing‖ ‖d.amplitude d.crossing‖]
          using (div_le_iff₀ hpos).mp hb.2
      _ ≤ (18 * Real.exp 3 * L ^ 2) * scale ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (couplingRatioOfGain_step hLprev₀ hstep).2.2.2
            (by positivity)) hpos.le
      _ = _ := by ring

end MovingWaveVector.PhysicalAmplification

open MovingWaveVector (frame entry)

/-- Wave one supplies the same affine equations on its successor's slab.
Its constant cutoff is already one at the common activation time zero. -/
theorem FirstWaveOrigin.nextSlabData {s T freq finish : ℝ} (d : FirstWaveOrigin s T freq)
    (hfinish : finish ≤ T) (hfreq : 0 < freq)
    (hsmall : T * ‖stationaryShearGradient s‖ ≤ 1 / 8) :
    let ν := entry (frame d.covector d.amplitude 0) (stationaryShearGradient s) 0 1
    let η := entry (frame d.covector d.amplitude 0) (stationaryShearGradient s) 2 1
    (∀ t ∈ Icc 0 finish, d.covector t ≠ 0 ∧ d.amplitude t ≠ 0 ∧
      ⟪d.covector t, d.amplitude t⟫_ℝ = 0) ∧
    (∀ t ∈ Icc 0 finish, HasDerivWithinAt d.covector
      (-((stationaryShearGradient s).adjoint (d.covector t))) (Icc 0 finish) t) ∧
    (∀ t ∈ Icc 0 finish, HasDerivWithinAt d.amplitude
      (affineWaveAmplitudeOperator (stationaryShearGradient s) (d.covector t) (d.amplitude t))
      (Icc 0 finish) t) ∧
    (ν = 2 * Real.pi ∧ Real.pi ≤ ν ∧ ν ≤ 4 * Real.pi ∧ η / ν = s) ∧
    (freq ^ (1 / 4 : ℝ) / 2 ≤ ‖d.covector 0‖ * ‖d.amplitude 0‖ ∧
      ‖d.covector 0‖ * ‖d.amplitude 0‖ ≤ freq ^ (1 / 4 : ℝ)) := by
  dsimp only
  have hsub : Icc (0 : ℝ) finish ⊆ Icc 0 T := Icc_subset_Icc_right hfinish
  obtain ⟨hν, hη⟩ := d.initial_couplings hfreq
  refine ⟨fun t ht => d.transverse t (hsub ht),
    fun t ht => (d.covector_equation t (hsub ht)).mono hsub,
    fun t ht => (d.amplitude_equation t (hsub ht)).mono hsub, ?_,
    d.initial_strength hfreq hsmall⟩
  rw [hν, hη]
  exact ⟨rfl, by linarith [Real.pi_pos], by linarith [Real.pi_pos],
    mul_div_cancel_left₀ s (by positivity [Real.pi_pos] : 2 * Real.pi ≠ 0)⟩

/-- The first wave obeys the same loose strength constants as all later
crossings once the next scheduled gain is at least one. -/
theorem FirstWaveOrigin.strength_bounds_for_next {s T freq L : ℝ} (d : FirstWaveOrigin s T freq)
    (hfreq : 0 < freq) (hL : 1 ≤ L) (hsmall : T * ‖stationaryShearGradient s‖ ≤ 1 / 8) :
    (Real.exp (-1) / 4) * freq ^ (1 / 4 : ℝ) ≤ ‖d.covector 0‖ * ‖d.amplitude 0‖ ∧
    ‖d.covector 0‖ * ‖d.amplitude 0‖ ≤ (18 * Real.exp 3) * freq ^ (1 / 4 : ℝ) * L ^ 2 := by
  obtain ⟨hlo, hhi⟩ := d.initial_strength hfreq hsmall
  have hpow : 0 ≤ freq ^ (1 / 4 : ℝ) := Real.rpow_nonneg hfreq.le _
  have helo : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hehi : 1 ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
  constructor
  · exact (show (Real.exp (-1) / 4) * freq ^ (1 / 4 : ℝ) ≤ freq ^ (1 / 4 : ℝ) / 2 by
      linarith only [mul_le_mul_of_nonneg_right helo hpow, hpow]).trans hlo
  · calc
      _ ≤ freq ^ (1 / 4 : ℝ) := hhi
      _ ≤ (18 * Real.exp 3) * freq ^ (1 / 4 : ℝ) :=
        le_mul_of_one_le_left hpow (by linarith)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL)

/-- The actual central velocity gradient inherits the old-frequency bounds
on any later closed time interval in the parent slab. Its time derivative
is taken on the original parent slab and restricted to that interval. -/
theorem older_central_gradient_raw_bounds_of_derivedLowBounds
    {u : Velocity} {T l r old : ℝ}
    (hT : 0 < T) (hl : 0 ≤ l) (hr : r ≤ T)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hLow : ∀ t ∈ Icc 0 T, ‖fderiv ℝ (u t) (0 : Vec3)‖ ≤ old ^ 9 ∧
      ‖derivWithin (fun s => fderiv ℝ (u s) (0 : Vec3)) (Icc 0 T) t‖ ≤ old ^ 18) :
    let B := fun t => fderiv ℝ (u t) (0 : Vec3)
    let Bt := fun t => derivWithin B (Icc 0 T) t
    ∀ t ∈ Icc l r, HasDerivWithinAt B (Bt t) (Icc l r) t ∧
      ‖B t‖ ≤ old ^ 9 ∧ ‖Bt t‖ ≤ old ^ 18 := by
  let B (t : ℝ) := fderiv ℝ (u t) (0 : Vec3)
  have hF : ContDiffOn ℝ 1 (fun z : ℝ × Vec3 => fderiv ℝ (u z.1) z.2)
      (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    contDiffOn_spatialDerivative_of_joint_contDiff (uniqueDiffOn_Icc hT) (by
      convert hu using 1
      norm_num)
  have hSlice : ContDiffOn ℝ 1 (fun t : ℝ => (t, (0 : Vec3))) (Icc 0 T) :=
    (contDiff_id.prodMk contDiff_const).contDiffOn
  have hMaps : MapsTo (fun t : ℝ => (t, (0 : Vec3))) (Icc 0 T)
      (Icc 0 T ×ˢ (univ : Set Vec3)) := fun _ ht => ⟨ht, mem_univ _⟩
  have hB : ContDiffOn ℝ 1 B (Icc 0 T) := hF.comp hSlice hMaps
  have hsub : Icc l r ⊆ Icc 0 T := Icc_subset_Icc hl hr
  dsimp only
  intro t ht
  have ht' := hsub ht
  exact ⟨((hB.differentiableOn (by simp) t ht').hasDerivWithinAt).mono hsub,
    hLow t ht'⟩

/-- The actual central velocity gradient inherits the old-frequency bounds
on any later closed time interval in the parent slab. Its time derivative
is taken on the original parent slab and restricted to that interval. -/
theorem older_central_gradient_bounds_of_derivedLowBounds
    {u : Velocity} {T l r old μ : ℝ} {b q : ℕ}
    (hT : 0 < T) (hl : 0 ≤ l) (hr : r ≤ T)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hb : 1 ≤ b) (hold : 1 ≤ old) (hμ : μ = old ^ frequencyExponent b q)
    (hLow : ∀ t ∈ Icc 0 T, ‖fderiv ℝ (u t) (0 : Vec3)‖ ≤ old ^ 9 ∧
      ‖derivWithin (fun s => fderiv ℝ (u s) (0 : Vec3)) (Icc 0 T) t‖ ≤ old ^ 18) :
    let B := fun t => fderiv ℝ (u t) (0 : Vec3)
    let Bt := fun t => derivWithin B (Icc 0 T) t
    ∀ t ∈ Icc l r, HasDerivWithinAt B (Bt t) (Icc l r) t ∧
      ‖B t‖ ≤ μ ^ (1 / 32 : ℝ) ∧ ‖Bt t‖ ≤ μ ^ (1 / 16 : ℝ) := by
  dsimp only
  intro t ht
  obtain ⟨hDiff, hB, hBt⟩ :=
    older_central_gradient_raw_bounds_of_derivedLowBounds hT hl hr hu hLow t ht
  exact ⟨hDiff, induction_older_gradient_scales hb hold hμ hB hBt⟩

/-- The parent Fourier cutoff and projected momentum equation supply the
actual older-gradient bounds of item 2 of the proof of Theorem 7.1. -/
theorem exists_older_central_gradient_bounds :
    ∃ N : ℝ, 1 ≤ N ∧
      ∀ {T l r old μ : ℝ} {b q : ℕ}, 0 < T → 0 ≤ l → r ≤ T →
        N ≤ old → 1 ≤ μ → 1 ≤ b → μ = old ^ frequencyExponent b q →
        ∀ (U R : ℝ → C(UnitAddTorus (Fin 3), Vec3))
          (A : ℝ → HalfHolder (UnitAddTorus (Fin 3)) Vec3),
          let u : Velocity := fun t x => U t (toUnitTorus x)
          ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)) →
          (∀ t ∈ Icc 0 T, ‖U t‖ ≤ old ∧ RealTorusFourierBand (2 * old ^ 5) (U t)) →
          (∀ t ∈ Icc 0 T, ‖R t‖ ≤ μ ^ (-3 : ℝ)) →
          (∀ t ∈ Icc 0 T, ∀ x, HalfHolder.eval (toUnitTorus x) (A t) = fderiv ℝ (u t) x (u t x)) →
          (∀ t ∈ Icc 0 T, ∀ x, HasDerivWithinAt (fun s => u s x)
            (-HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray (A t)) +
              R t (toUnitTorus x)) (Icc 0 T) t) →
          let B := fun t => fderiv ℝ (u t) (0 : Vec3)
          let Bt := fun t => derivWithin B (Icc 0 T) t
          ∀ t ∈ Icc l r, HasDerivWithinAt B (Bt t) (Icc l r) t ∧
            ‖B t‖ ≤ μ ^ (1 / 32 : ℝ) ∧ ‖Bt t‖ ≤ μ ^ (1 / 16 : ℝ) := by
  obtain ⟨N, hN, hLow⟩ := exists_parentDerivedLowBounds
  refine ⟨N, hN, ?_⟩
  intro T l r old μ b q hT hl hr hold hμ₁ hb hμ U R A u hSmooth hU hR hA hEq
  exact older_central_gradient_bounds_of_derivedLowBounds hT hl hr (hSmooth.of_le (by simp))
    hb (hN.trans hold) hμ (fun t ht => hLow hT hold hμ₁ U R A hSmooth hU hR hA hEq t ht 0)

/-- The closed-slab projected momentum of the actual parent determines
the torus lifts of its advection and residual. The Fourier cutoff bounds
the older velocity gradient, its time derivative, and the gradient of
the same residual at every physical point. -/
theorem exists_parent_projectedMomentum_bounds :
    ∃ (N K : ℝ), 1 ≤ N ∧ 0 ≤ K ∧
      ∀ {T old μ : ℝ}, 0 < T → N ≤ old → 1 ≤ μ →
        ∀ (U : ℝ → C(UnitAddTorus (Fin 3), Vec3)) (R : Velocity),
          let u : Velocity := fun t x => U t (toUnitTorus x)
          ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)) →
          (∀ t ∈ Icc 0 T, ‖U t‖ ≤ old ∧ RealTorusFourierBand (2 * old ^ 5) (U t)) →
          (∀ t ∈ Icc 0 T, ∀ x, divergence (u t) x = 0) →
          (∀ t ∈ Icc 0 T, closedSlabLerayMomentum 0 T u t = R t) →
          (∀ t ∈ Icc 0 T, ∀ x, ‖R t x‖ ≤ (μ⁻¹) ^ (3 : ℕ)) →
          ∃ (A : ℝ → HalfHolder (UnitAddTorus (Fin 3)) Vec3)
            (Rtor : ℝ → C(UnitAddTorus (Fin 3), Vec3)),
            (∀ t ∈ Icc 0 T, ∀ x,
              HalfHolder.eval (toUnitTorus x) (A t) = fderiv ℝ (u t) x (u t x)) ∧
            (∀ t ∈ Icc 0 T, ∀ x, Rtor t (toUnitTorus x) = R t x) ∧
            (∀ t ∈ Icc 0 T, ‖Rtor t‖ ≤ μ ^ (-3 : ℝ)) ∧
            (∀ t ∈ Icc 0 T, ∀ x,
              HasDerivWithinAt (fun s => u s x)
                (-HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray (A t)) +
                  Rtor t (toUnitTorus x)) (Icc 0 T) t) ∧
            (∀ t ∈ Icc 0 T, RealTorusFourierBand (4 * old ^ 5) (Rtor t) ∧
              ContDiff ℝ ∞ (R t)) ∧
            (∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (u t) x‖ ≤ old ^ 9 ∧
              ‖derivWithin (fun s => fderiv ℝ (u s) x) (Icc 0 T) t‖ ≤ old ^ 18 ∧
              ‖fderiv ℝ (R t) x‖ ≤ K * old ^ 5 * μ ^ (-3 : ℝ)) := by
  classical
  obtain ⟨N, hN, hLow⟩ := exists_parentDerivedLowBounds
  obtain ⟨K, hK, hBernstein⟩ := exists_bandBernsteinJetBounds
  refine ⟨N, K 1, hN, hK 1, ?_⟩
  intro T old μ hT hOld hμ₁ U R u hSmooth hU hDiv hMom hR
  let I := Icc (0 : ℝ) T
  let Labels := UnitAddTorus (Fin 3)
  let W : Velocity := fun t x => derivWithin (fun s => u s x) I t
  have hPer (t : ℝ) (_ht : t ∈ I) : SpatiallyPeriodic (u t) := fun n x =>
    congrArg (U t) ((toUnitTorus_eq_iff _ _).2 ⟨n, rfl⟩)
  have hSlice {f : Velocity} (h : ContDiffOn ℝ ∞ (Function.uncurry f) (I ×ˢ (univ : Set Vec3)))
      (t : ℝ) (ht : t ∈ I) : ContDiff ℝ ∞ (f t) := by
    let e : Vec3 → ℝ × Vec3 := fun x => (t, x)
    exact h.comp_contDiff (f := e) (contDiff_const.prodMk contDiff_id)
      (fun x => ⟨ht, mem_univ x⟩)
  have hWt : ContDiffOn ℝ ∞ (Function.uncurry W) (I ×ˢ (univ : Set Vec3)) :=
    contDiffOn_sliceTimeDerivWithin_Icc hT hSmooth
  let adv : Velocity := fun t x => fderiv ℝ (u t) x (u t x)
  have hExistsA (t : ℝ) : ∃ a : HalfHolder Labels Vec3,
      t ∈ I → ∀ x, HalfHolder.eval (toUnitTorus x) a = adv t x := by
    by_cases ht : t ∈ I
    · have hUs := hSlice hSmooth t ht
      have hA : ContDiff ℝ ∞ (adv t) := (hUs.fderiv_right (m := ∞) (by simp)).clm_apply hUs
      have hAPer : SpatiallyPeriodic (adv t) := by
        intro n x
        change fderiv ℝ (u t) (x + latticeVector n) (u t (x + latticeVector n)) =
          fderiv ℝ (u t) x (u t x)
        rw [(hPer t ht).fderiv (hUs.differentiable (by simp)) n x, hPer t ht n x]
      obtain ⟨a, ha, _⟩ := exists_halfHolder_of_spatialHolderHalf_zero hAPer
        (spatialHolderHalf_zero_of_contDiff_spatiallyPeriodic (hA.of_le (by simp)) hAPer)
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => (ht h).elim⟩
  choose A hA using hExistsA
  let S : Velocity := fun t x =>
    HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray (A t))
  have hEq (t : ℝ) (ht : t ∈ I) (x : Vec3) :
      HasDerivWithinAt (fun s => u s x) (R t x - S t x) I t := by
    have hU_s := hSlice hSmooth t ht
    have hX := hasDerivWithinAt_of_closedSlabLerayMomentum hT hSmooth hPer hDiv hMom ht x
    have hAdv : momentumTensorDivergence ∘ fderiv ℝ (fun y => momentumTensor (u t y) (u t y)) =
        adv t := momentumTensorDivergence_self_eq_advection (hU_s.differentiable (by simp)) (hDiv t ht)
    have hTor : periodicLerayHolderLift (adv t) = S t := by
      rw [← funext (hA t ht), periodicLerayHolderLift_pullback]
    rwa [hAdv, hTor] at hX
  have hExistsR (t : ℝ) : ∃ z : C(Labels, Vec3), t ∈ I →
      (∀ x, z (toUnitTorus x) = R t x) ∧ ‖z‖ ≤ μ ^ (-3 : ℝ) := by
    by_cases ht : t ∈ I
    · have hWc : Continuous (W t) := (hSlice hWt t ht).continuous
      have hWper : SpatiallyPeriodic (W t) := fun n x =>
        derivWithin_congr (fun s hs => hPer s hs n x) (hPer t ht n x)
      have hSc : Continuous (S t) :=
        (endpointStrongSpatialLeray (A t)).val.1.continuous.comp
          isOpenQuotientMap_toUnitTorus.continuous
      have hSper : SpatiallyPeriodic (S t) := fun n x =>
        congrArg (fun y => HalfHolder.eval y (endpointStrongSpatialLeray (A t)))
          ((toUnitTorus_eq_iff _ _).2 ⟨n, rfl⟩)
      have hRep : R t = W t + S t := by
        funext x
        exact (sub_eq_iff_eq_add.mp ((hEq t ht x).derivWithin
          (uniqueDiffOn_Icc hT t ht)).symm)
      have hSumPer : SpatiallyPeriodic (W t + S t) := by
        intro n x
        change W t (x + latticeVector n) + S t (x + latticeVector n) = W t x + S t x
        rw [hWper n x, hSper n x]
      obtain ⟨z, hz⟩ := hSumPer.exists_continuousTorusFunction (hWc.add hSc)
      have hzR : ∀ x, z (toUnitTorus x) = R t x := fun x =>
        (hz x).trans (congrFun hRep x).symm
      have hPow : (μ⁻¹) ^ (3 : ℕ) = μ ^ (-3 : ℝ) := by
        rw [inv_pow, Real.rpow_neg (zero_le_one.trans hμ₁), Real.rpow_ofNat]
      have hzBound : ‖z‖ ≤ μ ^ (-3 : ℝ) := by
        apply (ContinuousMap.norm_le z (Real.rpow_nonneg (zero_le_one.trans hμ₁) _)).2
        intro a
        obtain ⟨x, rfl⟩ := isOpenQuotientMap_toUnitTorus.surjective a
        rw [hzR, ← hPow]
        exact hR t ht x
      exact ⟨z, fun _ => ⟨hzR, hzBound⟩⟩
    · exact ⟨0, fun h => (ht h).elim⟩
  choose Rtor hRtor using hExistsR
  have hMomentum (t : ℝ) (ht : t ∈ I) (x : Vec3) :
      HasDerivWithinAt (fun s => u s x)
        (-HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray (A t)) +
          Rtor t (toUnitTorus x)) I t := by
    rw [(hRtor t ht).1 x]
    exact (hEq t ht x).congr_deriv (sub_eq_neg_add _ _)
  have hD : 0 < old ^ 5 := pow_pos (zero_lt_one.trans_le (hN.trans hOld)) _
  have hRband (t : ℝ) (ht : t ∈ I) : RealTorusFourierBand (4 * old ^ 5) (Rtor t) :=
    parentResidualFourierBand_of_projectedMomentum hT hD.le ht U (Rtor t) (A t)
      hSmooth (fun s hs => (hU s hs).2) (hA t ht) (hMomentum t ht)
  have hRjet (t : ℝ) (ht : t ∈ I) :
      ContDiff ℝ ∞ (R t) ∧
        ∀ x, ‖fderiv ℝ (R t) x‖ ≤ K 1 * old ^ 5 * μ ^ (-3 : ℝ) := by
    have hRep : (fun x => Rtor t (toUnitTorus x)) = R t := funext (hRtor t ht).1
    obtain ⟨hRsmooth, hJet⟩ := hBernstein (Rtor t) hD
      (Real.rpow_nonneg (zero_le_one.trans hμ₁) _) (hRtor t ht).2 (hRband t ht)
    rw [hRep] at hRsmooth hJet
    refine ⟨hRsmooth, fun x => ?_⟩
    simpa only [norm_iteratedFDeriv_one, pow_one, mul_right_comm] using hJet 1 x
  refine ⟨A, Rtor, hA, fun t ht => (hRtor t ht).1, fun t ht => (hRtor t ht).2, hMomentum,
    fun t ht => ⟨hRband t ht, (hRjet t ht).1⟩, ?_⟩
  intro t ht x
  obtain ⟨hGrad, hTimeGrad⟩ := hLow hT hOld hμ₁ U Rtor A hSmooth hU
    (fun s hs => (hRtor s hs).2) hA hMomentum t ht x
  exact ⟨hGrad, hTimeGrad, (hRjet t ht).2 x⟩

/-- Recover the older-gradient bounds directly from the closed-slab projected
momentum identity and pointwise residual bound of an actual parent. -/
theorem exists_older_central_gradient_raw_bounds_of_projectedMomentum :
    ∃ N : ℝ, 1 ≤ N ∧
      ∀ {T l r old μ : ℝ}, 0 < T → 0 ≤ l → r ≤ T →
        N ≤ old → 1 ≤ μ →
        ∀ (U : ℝ → C(UnitAddTorus (Fin 3), Vec3)) (R : Velocity),
          let u : Velocity := fun t x => U t (toUnitTorus x)
          ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)) →
          (∀ t ∈ Icc 0 T, ‖U t‖ ≤ old ∧ RealTorusFourierBand (2 * old ^ 5) (U t)) →
          (∀ t ∈ Icc 0 T, ∀ x, divergence (u t) x = 0) →
          (∀ t ∈ Icc 0 T, closedSlabLerayMomentum 0 T u t = R t) →
          (∀ t ∈ Icc 0 T, ∀ x, ‖R t x‖ ≤ (μ⁻¹) ^ (3 : ℕ)) →
          let B := fun t => fderiv ℝ (u t) (0 : Vec3)
          let Bt := fun t => derivWithin B (Icc 0 T) t
          ∀ t ∈ Icc l r, HasDerivWithinAt B (Bt t) (Icc l r) t ∧
            ‖B t‖ ≤ old ^ 9 ∧ ‖Bt t‖ ≤ old ^ 18 := by
  obtain ⟨N, _, hN, _, hBounds⟩ := exists_parent_projectedMomentum_bounds
  refine ⟨N, hN, ?_⟩
  intro T l r old μ hT hl hr hOld hμ₁ U R u hSmooth hU hDiv hMom hR
  obtain ⟨_, _, _, _, _, _, _, hSpatial⟩ := hBounds hT hOld hμ₁ U R hSmooth hU hDiv hMom hR
  exact older_central_gradient_raw_bounds_of_derivedLowBounds hT hl hr (hSmooth.of_le (by simp))
    (fun t ht => ⟨(hSpatial t ht 0).1, (hSpatial t ht 0).2.1⟩)

/-- Recover the older-gradient bounds directly from the closed-slab projected
momentum identity and pointwise residual bound of an actual parent. -/
theorem exists_older_central_gradient_bounds_of_projectedMomentum :
    ∃ N : ℝ, 1 ≤ N ∧
      ∀ {T l r old μ : ℝ} {b q : ℕ}, 0 < T → 0 ≤ l → r ≤ T →
        N ≤ old → 1 ≤ μ → 1 ≤ b → μ = old ^ frequencyExponent b q →
        ∀ (U : ℝ → C(UnitAddTorus (Fin 3), Vec3)) (R : Velocity),
          let u : Velocity := fun t x => U t (toUnitTorus x)
          ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)) →
          (∀ t ∈ Icc 0 T, ‖U t‖ ≤ old ∧ RealTorusFourierBand (2 * old ^ 5) (U t)) →
          (∀ t ∈ Icc 0 T, ∀ x, divergence (u t) x = 0) →
          (∀ t ∈ Icc 0 T, closedSlabLerayMomentum 0 T u t = R t) →
          (∀ t ∈ Icc 0 T, ∀ x, ‖R t x‖ ≤ (μ⁻¹) ^ (3 : ℕ)) →
          let B := fun t => fderiv ℝ (u t) (0 : Vec3)
          let Bt := fun t => derivWithin B (Icc 0 T) t
          ∀ t ∈ Icc l r, HasDerivWithinAt B (Bt t) (Icc l r) t ∧
            ‖B t‖ ≤ μ ^ (1 / 32 : ℝ) ∧ ‖Bt t‖ ≤ μ ^ (1 / 16 : ℝ) := by
  obtain ⟨N, hN, hRaw⟩ := exists_older_central_gradient_raw_bounds_of_projectedMomentum
  refine ⟨N, hN, ?_⟩
  intro T l r old μ b q hT hl hr hOld hμ₁ hb hμ U R u hSmooth hU hDiv hMom hR
  dsimp only
  intro t ht
  obtain ⟨hDiff, hB, hBt⟩ := hRaw hT hl hr hOld hμ₁ U R hSmooth hU hDiv hMom hR t ht
  exact ⟨hDiff, induction_older_gradient_scales hb (hN.trans hOld) hμ hB hBt⟩

open MovingWaveVector (PhysicalAmplification)
open AmplificationCrossing (crossingHorizon)

/-- The two gains for wave (j+2) are three and four frequency indices
ahead of the older velocity (U_j). -/
theorem frequencySchedule_laterWindow_gains
    (b : ℕ) (q : ℕ → ℕ) (B freq : ℕ → ℝ)
    (hb : 1 ≤ b) (hq : q 1 = 1) (hInit : B 1 ≤ freq 0)
    (hbase : 1 < freq 0)
    (hFreq : ∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1)))
    (hMax : ∀ i, IsGreatest {s | 1 ≤ s ∧ s ≤ q (i + 1) + 1 ∧ B s ≤ freq i} (q (i + 2)))
    (hBPos : ∀ s, 1 ≤ s → 0 < B s)
    (hFloor : ∀ s, 1 ≤ s → 4 * (frequencyExponent b (s + 1) : ℝ) ^ 3 ≤ Real.log (B s))
    (j : ℕ) :
    let μ := freq (j + 1)
    let L := 4 * Real.log (freq (j + 3))
    let LNext := 4 * Real.log (freq (j + 4))
    1 < μ ∧ Real.log μ ≤ L ∧ 640 * L ≤ LNext ∧ LNext ≤ (Real.log μ) ^ 2 := by
  dsimp only
  let gains := fun i => 4 * Real.log (freq (i + 1))
  have hmono := frequencySchedule_frequency_mono b q freq hb hbase.le hFreq
  have hpositive (i : ℕ) : 1 < freq i := hbase.trans_le (hmono (Nat.zero_le i))
  have hgain := frequencySchedule_gain_ratio b q freq gains (j + 2) hb
    (by simpa [Nat.add_assoc] using (hMax (j + 2)).1.1)
    (by simpa [Nat.add_assoc] using hpositive (j + 3))
    (by simpa [Nat.add_assoc] using hFreq (j + 3)) (fun _ => rfl)
  have hlogs := frequencySchedule_log_bound_of_maxima b q B freq gains hb hq hInit hFreq
    (fun _ => rfl) hMax hBPos hFloor (j + 1)
  have hlogmono : Real.log (freq (j + 1)) ≤ Real.log (freq (j + 3)) :=
    Real.log_le_log (zero_lt_one.trans (hpositive (j + 1))) (hmono (by omega))
  have hlogpos : 0 ≤ Real.log (freq (j + 3)) := (Real.log_pos (hpositive _)).le
  exact ⟨hpositive _, by linarith only [hlogmono, hlogpos],
    by simpa [gains, Nat.add_assoc] using hgain.2,
    by simpa [gains, Nat.add_assoc] using hlogs⟩

/-- The new physical endpoint is strictly inside the preceding parent slab
when the preceding crossing is in its first half. -/
theorem laterPhysicalWindow_fits_parentSlab {freq : ℕ → ℝ} {j : ℕ}
    {previousStart start : ℝ}
    (hordered : previousStart ≤ start)
    (hcross : start - previousStart ≤ inductionHalfLength freq j)
    (hτ : 0 < inductionHalfLength freq j)
    (hshrink : 4 * inductionHalfLength freq (j + 1) ≤ inductionHalfLength freq j) :
    start + 2 * inductionHalfLength freq (j + 1) <
        previousStart + 2 * inductionHalfLength freq j ∧
      Icc start (start + 2 * inductionHalfLength freq (j + 1)) ⊆
        Icc previousStart (previousStart + 2 * inductionHalfLength freq j) := by
  have hfinish : start + 2 * inductionHalfLength freq (j + 1) <
      previousStart + 2 * inductionHalfLength freq j := by linarith
  exact ⟨hfinish, Icc_subset_Icc hordered hfinish.le⟩

/-- The bounds needed by the physical comparison and its crossing. -/
structure ScheduledLaterPhysicalWindowBounds {start finish : ℝ}
    (w : PhysicalAmplification (Icc start finish) start)
    (window halfTime next : ℝ) (C₀ : ℕ) : Prop where
  window_ge : 2 ≤ window
  clock_end : w.clock window = finish
  clock_maps : MapsTo w.clock (Icc 0 window) (Icc start finish)
  comparison_ratio : (C₀ : ℝ) * w.ratio ≤ 1
  comparison_error : (C₀ : ℝ) * window ^ C₀ * w.errorSize ≤ w.ratio
  next_pos : 0 < next
  next_le : next ≤ w.ratio / 32
  horizon_half : crossingHorizon w.ratio next ≤ w.rate * halfTime
  horizon_full : crossingHorizon w.ratio next ≤ window

private theorem laterPhysicalWindow_error_nonneg {start finish : ℝ}
    (w : PhysicalAmplification (Icc start finish) start) : 0 ≤ w.errorSize := by
  have hSup {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t) :
      0 ≤ sSup (f '' Icc start finish) := by
    apply Real.sSup_nonneg
    rintro _ ⟨t, _, rfl⟩
    exact hf t
  unfold PhysicalAmplification.errorSize MovingWaveVector.amplificationPhysicalError
  exact add_nonneg (add_nonneg (add_nonneg (hSup (fun _ => abs_nonneg _))
    (hSup (fun _ => abs_nonneg _))) (div_nonneg (hSup (fun _ => norm_nonneg _)) w.rate_pos.le))
    (div_nonneg (hSup (fun _ => norm_nonneg _)) w.first_coupling_positive.le)

private theorem laterPhysicalWindow_clock {start finish halfTime : ℝ}
    (w : PhysicalAmplification (Icc start finish) start)
    (hFinish : finish = start + 2 * halfTime) :
    let window := 2 * w.rate * halfTime
    w.clock window = finish ∧ MapsTo w.clock (Icc 0 window) (Icc start finish) := by
  intro window
  have hclock : w.clock window = finish := by
    change start + (2 * w.rate * halfTime) / w.rate = finish
    rw [show 2 * w.rate * halfTime = (2 * halfTime) * w.rate by ring,
      mul_div_cancel_right₀ _ w.rate_pos.ne']
    exact hFinish.symm
  refine ⟨hclock, ?_⟩
  intro t ht
  have hlow := w.strictMono_clock.monotone ht.1
  have hhigh := w.strictMono_clock.monotone ht.2
  rw [w.clock_zero] at hlow
  rw [hclock] at hhigh
  exact ⟨hlow, hhigh⟩

set_option maxHeartbeats 650000 in
/-- The physical derivative and residual estimate (6.6), with the scheduled
preceding-wave strengths, gives (2.5) uniformly and puts the entire search for
the next crossing in the first half of the actual wave-(j+2) interval. -/
theorem exists_frequencySchedule_laterPhysicalWindow (C₀ : ℕ) (c C : ℝ)
    (hc : 0 < c) (hC : 0 < C) :
    ∃ N₀ : ℝ, 1 < N₀ ∧
      ∀ (b : ℕ) (q : ℕ → ℕ) (B freq : ℕ → ℝ),
        1 ≤ b → q 1 = 1 → B 1 ≤ freq 0 → N₀ ≤ freq 0 →
        (∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1))) →
        (∀ i, IsGreatest {s | 1 ≤ s ∧ s ≤ q (i + 1) + 1 ∧ B s ≤ freq i} (q (i + 2))) →
        (∀ s, 1 ≤ s → 0 < B s) →
        (∀ s, 1 ≤ s → 4 * (frequencyExponent b (s + 1) : ℝ) ^ 3 ≤ Real.log (B s)) →
        ∀ (j : ℕ) {start finish Bmax Btmax Emax : ℝ}
          (w : PhysicalAmplification (Icc start finish) start),
        let μ := freq (j + 1)
        let L := 4 * Real.log (freq (j + 3))
        let LNext := 4 * Real.log (freq (j + 4))
        let halfTime := inductionHalfLength freq (j + 1)
        let window := 2 * w.rate * halfTime
        let next := couplingRatioOfGain LNext
        finish = start + 2 * halfTime →
        w.ratio = couplingRatioOfGain L →
        c * μ ^ (1 / 4 : ℝ) ≤ w.initialStrength →
        w.initialStrength ≤ C * μ ^ (1 / 4 : ℝ) * L ^ 2 →
        Real.pi ≤ w.firstCoupling → w.firstCoupling ≤ 4 * Real.pi →
        0 ≤ Bmax → Bmax ≤ freq j ^ 9 → Btmax ≤ freq j ^ 18 → Emax ≤ μ ^ (-1 / 4 : ℝ) →
        w.errorSize ≤ 8 * (2 * halfTime * (Bmax ^ 2 + Btmax) /
          (w.firstCoupling * w.ratio) + Bmax / w.rate + Emax / w.firstCoupling) →
        ScheduledLaterPhysicalWindowBounds w window halfTime next C₀ := by
  let cRate := Real.sqrt (2 * c * Real.pi)
  let CRate := Real.sqrt (8 * C * Real.pi)
  have hcRate : 0 < cRate := by dsimp [cRate]; positivity [Real.pi_pos]
  have hCRate : 0 < CRate := by dsimp [CRate]; positivity [Real.pi_pos]
  obtain ⟨N, hN, hSmall⟩ :=
    exists_induction_amplification_step_comparison C₀ 8 cRate CRate (by norm_num) hcRate hCRate.le
  let top := max N (Real.exp (1 + 2 / cRate))
  refine ⟨top, hN.trans_le (le_max_left _ _), ?_⟩
  intro b q B freq hb hq hInit hbase hFreq hMax hBPos hFloor j start finish Bmax Btmax Emax w
    μ L LNext halfTime window next hFinish hRatio hσLo hσHi hνLo hνHi hB₀ hB hBt hE hError
  have hbase' : 1 < freq 0 := hN.trans_le ((le_max_left _ _).trans hbase)
  have hmono := frequencySchedule_frequency_mono b q freq hb hbase'.le hFreq
  obtain ⟨hμ, hlogL, hstep, hUpper⟩ :=
    frequencySchedule_laterWindow_gains b q B freq hb hq hInit hbase' hFreq hMax hBPos hFloor j
  have hμpos : 0 < μ := zero_lt_one.trans hμ
  have hL : 0 < L := (Real.log_pos hμ).trans_le hlogL
  have hLNext : 0 < LNext := (mul_pos (by norm_num : 0 < (640 : ℝ)) hL).trans_le hstep
  have hLmono : L ≤ LNext := by linarith only [hstep, hL]
  have hμlarge : top ≤ μ := hbase.trans (hmono (Nat.zero_le _))
  have hloglarge : 1 + 2 / cRate ≤ Real.log μ := by
    have hlog := Real.log_le_log (Real.exp_pos (1 + 2 / cRate))
      ((le_max_right N (Real.exp (1 + 2 / cRate))).trans hμlarge)
    rwa [Real.log_exp] at hlog
  have hLNextLarge : 2 / cRate ≤ LNext := by linarith only [hloglarge, hlogL, hLmono]
  have hδ₀ : 0 ≤ w.errorSize := laterPhysicalWindow_error_nonneg w
  have hν : 1 ≤ w.firstCoupling := (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi).trans hνLo
  obtain ⟨hrLo, hrHi⟩ := activationGrowthRate_bounds hμpos hL.le hc hC hσLo hσHi hνLo hνHi
  have hhalf : halfTime = μ ^ (-1 / 8 : ℝ) * LNext ^ 3 := rfl
  have hhalf₀ : 0 ≤ halfTime := by rw [hhalf]; positivity
  have hRec : μ = freq j ^ frequencyExponent b (q (j + 1)) := hFreq j
  have hold : 1 ≤ freq j := hbase'.le.trans (hmono (Nat.zero_le _))
  have hErrActual : w.errorSize ≤ 8 * (2 * (μ ^ (-1 / 8 : ℝ) * LNext ^ 3) * (Bmax ^ 2 + Btmax) /
      (w.firstCoupling * couplingRatioOfGain L) + Bmax / w.rate + Emax / w.firstCoupling) := by
    rwa [← hhalf, ← hRatio]
  obtain ⟨hT, hsmallε, hsmallδ⟩ := hSmall (r := w.rate) (μ := μ) (L := L) (LNext := LNext)
    (b := b) (q := q (j + 1)) ((le_max_left _ _).trans hμlarge) hb hold hRec hν
    hrLo hrHi hlogL hLmono hUpper hB₀ hB hBt hE hδ₀ hErrActual
  rw [← hhalf, ← hRatio] at hsmallδ
  rw [← hRatio] at hsmallε
  obtain ⟨hclock, hmap⟩ := laterPhysicalWindow_clock w hFinish
  have hNextPos : 0 < next := inv_pos.mpr (sq_pos_of_pos hLNext)
  have hNextSmall : next ≤ w.ratio / 32 := by
    rw [hRatio]
    exact (couplingRatioOfGain_step hL hstep).2.1
  have hHhalf : crossingHorizon w.ratio next ≤ w.rate * halfTime := by
    have hh := crossingClock_le_endpointHalfLength hμpos hcRate hL hstep hrLo hLNextLarge
    rw [(couplingRatioOfGain_step hL hstep).2.2.1] at hh
    change crossingHorizon w.ratio (couplingRatioOfGain LNext) ≤ w.rate * halfTime
    rw [hRatio, crossingHorizon_eq_of_gains hL hstep, mul_comm w.rate halfTime, hhalf]
    exact (div_le_iff₀ w.rate_pos).mp hh
  have hHalfWin : w.rate * halfTime ≤ window := by
    change w.rate * halfTime ≤ 2 * w.rate * halfTime
    nlinarith only [mul_nonneg w.rate_pos.le hhalf₀]
  have hT' : 2 ≤ window := by
    change 2 ≤ 2 * w.rate * halfTime
    rw [hhalf]
    exact hT
  exact ⟨hT', hclock, hmap, hsmallε, hsmallδ, hNextPos, hNextSmall, hHhalf, hHhalf.trans hHalfWin⟩

end TorusEuler

namespace TorusEuler.MovingWaveVector.PhysicalAmplification

/-- The positively normalized growing seed at activation has frequency `scale`
and the two initial directions prescribed in §6.2. -/
theorem GrowingCrossing.launch_geometry
    {I : Set ℝ} {t₀ T scale Ustar next : ℝ} {w : PhysicalAmplification I t₀}
    (d : w.GrowingCrossing T scale Ustar next) (hscale : 0 < scale) :
    d.waveVector t₀ = scale • w.basis t₀ 2 ∧
    ‖d.waveVector t₀‖ = scale ∧
    ∃ (c : ℝ), 0 < c ∧ d.amplitude t₀ = c • ((-w.shear⁻¹) • w.basis t₀ 0 + w.basis t₀ 1) := by
  have h := w.preceding_data t₀ w.activation
  have hw : Orthonormal ℝ (w.basis t₀) :=
    orthonormal_movingFrame h.1 h.2.1 h.2.2
  refine ⟨d.initial_waveVector, ?_, d.seedFactor, d.seedFactor_pos, d.initial_amplitude⟩
  rw [d.initial_waveVector, norm_smul, Real.norm_of_nonneg hscale.le, hw.norm_eq_one 2, mul_one]

/-- For the same selected crossing, the label covector in §6.2 is nonzero and
its actual transport by the parent matches the Eulerian wave-vector solution
on the closed activation slab, including its left endpoint. -/
theorem GrowingCrossing.transport_launch_covector
    {I : Set ℝ} {t₀ T scale Ustar next finish : ℝ} {w : PhysicalAmplification I t₀}
    (d : w.GrowingCrossing T scale Ustar next)
    {U : Velocity} {X : ℝ → Velocity}
    (hX : IsLabelFlowOn U X (Icc 0 finish)) (hfinish : 0 < finish)
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 finish ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 finish, SpatiallyPeriodic (U t))
    (hodd : ∀ t ∈ Icc 0 finish, Function.Odd (U t))
    (h₀ : t₀ ∈ Icc 0 finish) (hclock : w.clock T = finish)
    (hGrad : EqOn w.gradient (fun t => fderiv ℝ (U t) (0 : Vec3)) (Icc t₀ finish)) :
    let k := scale • (fderiv ℝ (X 0 t₀) (0 : Vec3)).adjoint (w.basis t₀ 2)
    k ≠ 0 ∧ EqOn (labelWaveVector X 0 0 k) d.waveVector (Icc t₀ finish) := by
  let k := scale • (fderiv ℝ (X 0 t₀) (0 : Vec3)).adjoint (w.basis t₀ 2)
  have hslab : w.activeSlab T = Icc t₀ finish := by
    rw [PhysicalAmplification.activeSlab, hclock]
  have hv (t : ℝ) (ht : t ∈ Icc t₀ finish) :
      HasDerivWithinAt d.waveVector
        (-((fderiv ℝ (U t) (0 : Vec3)).adjoint (d.waveVector t))) (Icc t₀ finish) t := by
    have hd := d.waveVector_derivative t (hslab.symm ▸ ht)
    rw [hslab, hGrad ht] at hd
    exact hd
  have hlaunch : (fderiv ℝ (X 0 t₀) (0 : Vec3)).adjoint (d.waveVector t₀) = k := by
    rw [d.initial_waveVector, map_smul]
  have htransport := hX.center_coframe_covector_eq hfinish hU hper hodd h₀ hv
  dsimp only at htransport
  rw [hlaunch] at htransport
  have ht₀ : t₀ ∈ w.activeSlab T := hslab.symm ▸ left_mem_Icc.mpr h₀.2
  have h0T : (0 : ℝ) ∈ Icc 0 finish := left_mem_Icc.mpr hfinish.le
  obtain ⟨L, hL⟩ := exists_lipschitzWith_of_contDiffOn_periodic hfinish (hU.of_le (by norm_num)) hper
  refine ⟨htransport.1 (d.transverse t₀ ht₀).1, ?_⟩
  intro t ht
  have hp : t ∈ Icc 0 finish := ⟨h₀.1.trans ht.1, ht.2⟩
  have hfix : X 0 t (0 : Vec3) = 0 := by
    have heq := hX.odd hL hodd h0T hp (0 : Vec3)
    rw [neg_zero] at heq
    have hDouble : (2 : ℝ) • X 0 t (0 : Vec3) = 0 := by
      rw [two_smul]
      nth_rw 1 [heq]
      exact neg_add_cancel _
    exact (smul_eq_zero.mp hDouble).resolve_left (by norm_num)
  rw [labelWaveVector, hfix]
  exact htransport.2 t ht


end TorusEuler.MovingWaveVector.PhysicalAmplification

namespace TorusEuler.MovingWaveVector

open AmplificationCrossing (crossingHorizon)
open LocalizedAmplitude (CenterWaveOn)

/-- The later wave, its actual scale and the comparison estimates for that
same physical trajectory. -/
structure LaterWaveSelection {t₀ finish : ℝ}
    (parent : Velocity) (w : PhysicalAmplification (Icc t₀ finish) t₀)
    (C₀ : ℕ) (half scale LNext D : ℝ) where
  window : ℝ
  window_eq : window = 2 * w.rate * half
  window_ge : 2 ≤ window
  clock_eq : w.clock window = finish
  comparison_ratio : (C₀ : ℝ) * w.ratio ≤ 1
  comparison_error : (C₀ : ℝ) * window ^ C₀ * w.errorSize ≤ w.ratio
  crossing : w.GrowingCrossing window scale (scale ^ (-3 / 4 : ℝ)) (couplingRatioOfGain LNext)
  crossing_after_start : t₀ < crossing.crossing
  crossing_in_first_half : crossing.crossing - t₀ ≤ half
  center : CenterWaveOn (fun t => fderiv ℝ (parent t) 0)
    crossing.waveVector crossing.amplitude t₀ finish D

set_option maxHeartbeats 600000 in
/-- The scheduled comparison hypotheses construct the later wave over the
actual parent gradient. The window, first crossing, prescribed peak and
center bounds all refer to the same physical path. -/
theorem exists_frequencySchedule_selectLaterWave (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ (C₀ : ℕ) (N₀ : ℝ), 240 ≤ C₀ ∧ 1 < N₀ ∧
      ∀ (b : ℕ) (q : ℕ → ℕ) (B freq : ℕ → ℝ),
        1 ≤ b → q 1 = 1 → B 1 ≤ freq 0 → N₀ ≤ freq 0 →
        (∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1))) →
        (∀ i, IsGreatest {s | 1 ≤ s ∧ s ≤ q (i + 1) + 1 ∧ B s ≤ freq i} (q (i + 2))) →
        (∀ s, 1 ≤ s → 0 < B s) →
        (∀ s, 1 ≤ s → 4 * (frequencyExponent b (s + 1) : ℝ) ^ 3 ≤ Real.log (B s)) →
        ∀ (j : ℕ) {older parent : Velocity} {kp ap : ℝ → Space}
          {E : ℝ → Space →L[ℝ] Space} {start finish : ℝ}
          (p : LaterPhysicalWindow older parent kp ap E start finish)
          (Bt : ℝ → Space →L[ℝ] Space),
        let w := p.physical
        let μ := freq (j + 1)
        let L := 4 * Real.log (freq (j + 3))
        let LNext := 4 * Real.log (freq (j + 4))
        let half := inductionHalfLength freq (j + 1)
        finish = start + 2 * half →
        w.ratio = couplingRatioOfGain L →
        c * μ ^ (1 / 4 : ℝ) ≤ w.initialStrength →
        w.initialStrength ≤ C * μ ^ (1 / 4 : ℝ) * L ^ 2 →
        Real.pi ≤ w.firstCoupling → w.firstCoupling ≤ 4 * Real.pi →
        (∀ t ∈ Icc start finish,
          HasDerivWithinAt (fun u => fderiv ℝ (older u) 0) (Bt t) (Icc start finish) t) →
        (∀ t ∈ Icc start finish, ‖fderiv ℝ (older t) 0‖ ≤ freq j ^ 9) →
        (∀ t ∈ Icc start finish, ‖Bt t‖ ≤ freq j ^ 18) →
        (∀ t ∈ Icc start finish, ‖E t‖ ≤ μ ^ (-1 / 4 : ℝ)) →
        Nonempty (LaterWaveSelection parent w C₀ half (freq (j + 2)) LNext (μ ^ 9)) := by
  obtain ⟨Ncross, hNcross, hExists⟩ := PhysicalAmplification.exists_growingCrossing
  obtain ⟨Ncenter, _, hCenter⟩ := LocalizedAmplitude.exists_laterWave_centerWaveOn_threshold
  let C₀ := max Ncross Ncenter
  obtain ⟨Nsmall, hNsmall, hSchedule⟩ := exists_frequencySchedule_laterPhysicalWindow C₀ c C hc hC
  obtain ⟨Nparams, hNparams, hParams⟩ := PhysicalAmplification.exists_later_center_bounds C hC
  let N := max (max Nsmall Nparams) (Real.exp 1)
  have hSmallN : Nsmall ≤ N := (le_max_left Nsmall Nparams).trans (le_max_left _ _)
  have hParamsN : Nparams ≤ N := (le_max_right Nsmall Nparams).trans (le_max_left _ _)
  refine ⟨C₀, N, hNcross.trans (le_max_left _ _), hNsmall.trans_le hSmallN, ?_⟩
  intro b q B freq hb hq hInit hbase hFreq hMax hBpos hFloor j older parent kp ap E start finish p Bt
    w μ L LNext half hFinish hRatio hσlo hσhi hνlo hνhi hBd hB hBt hE
  have hbase₁ : 1 < freq 0 := hNsmall.trans_le (hSmallN.trans hbase)
  have hMono := frequencySchedule_frequency_mono b q freq hb hbase₁.le hFreq
  have hμlarge : N ≤ μ := hbase.trans (hMono (Nat.zero_le _))
  obtain ⟨hμ, hLogL, hStep, hUpper⟩ :=
    frequencySchedule_laterWindow_gains b q B freq hb hq hInit hbase₁ hFreq hMax hBpos hFloor j
  have hL : 0 < L := (Real.log_pos hμ).trans_le hLogL
  have hLNext : L ≤ LNext := by linarith only [hStep, hL]
  have hLone : 1 ≤ L := by
    have hs := Real.log_le_log (Real.exp_pos 1)
      ((le_max_right (max Nsmall Nparams) (Real.exp 1)).trans hμlarge)
    rw [Real.log_exp] at hs
    exact hs.trans hLogL
  have hEps : w.ratio ≤ 1 := by
    rw [hRatio, couplingRatioOfGain, ← one_div, div_le_iff₀ (sq_pos_of_pos hL)]
    simpa only [one_mul] using (one_le_pow₀ hLone : 1 ≤ L ^ (2 : ℕ))
  have hG : ∀ t ∈ Icc start finish, HasDerivWithinAt w.B (Bt t) (Icc start finish) t := by
    change ∀ t ∈ Icc start finish, HasDerivWithinAt p.physical.B (Bt t) (Icc start finish) t
    rwa [p.older_gradient_eq]
  have hGnorm : ∀ t ∈ Icc start finish, ‖w.B t‖ ≤ freq j ^ 9 := by
    change ∀ t ∈ Icc start finish, ‖p.physical.B t‖ ≤ freq j ^ 9
    rwa [p.older_gradient_eq]
  have hEnorm : ∀ t ∈ Icc start finish, ‖w.E t‖ ≤ μ ^ (-1 / 4 : ℝ) := by
    change ∀ t ∈ Icc start finish, ‖p.physical.E t‖ ≤ μ ^ (-1 / 4 : ℝ)
    rwa [p.error_eq]
  have hη : w.thirdCoupling = w.firstCoupling * w.ratio := by
    calc
      _ = (w.thirdCoupling / w.firstCoupling) * w.firstCoupling :=
        (div_mul_cancel₀ _ w.first_coupling_positive.ne').symm
      _ = _ := mul_comm _ _
  have hTime : finish - start = 2 * half := by linarith only [hFinish]
  have hError := (w.errorSize_le_of_older_gradient hEps Bt hG hGnorm hBt hEnorm).2
  rw [hTime, hη] at hError
  have hB₀ : 0 ≤ freq j ^ 9 :=
    pow_nonneg (zero_le_one.trans (hbase₁.le.trans (hMono (Nat.zero_le _)))) _
  obtain ⟨hT, hClock, hMap, hSmallε, hSmallδ, hNext, hNextSmall, hHorizonHalf, hHorizon⟩ :=
    hSchedule b q B freq hb hq hInit (hSmallN.trans hbase) hFreq hMax hBpos hFloor j w
      hFinish hRatio hσlo hσhi hνlo hνhi hB₀ le_rfl le_rfl le_rfl hError
  let T := 2 * w.rate * half
  let scale := freq (j + 2)
  let next := couplingRatioOfGain LNext
  have hscale : 0 < scale := zero_lt_one.trans_le (hbase₁.le.trans (hMono (Nat.zero_le _)))
  have hPeak : 0 < scale ^ (-3 / 4 : ℝ) := Real.rpow_pos_of_pos hscale _
  obtain ⟨d⟩ := hExists (le_max_left Ncross Ncenter) w hT hscale hPeak hMap
    hSmallε hSmallδ hNext hNextSmall hHorizon
  have hRate := (activationGrowthRate_bounds (zero_lt_one.trans hμ) hL.le hc hC
    hσlo hσhi hνlo hνhi).2
  obtain ⟨hGrowth, hInvCoupling⟩ := hParams w (hParamsN.trans hμlarge) hL
    (hLNext.trans hUpper) hνlo hRatio hRate
  have hCenterActual := hCenter (le_max_right Ncross Ncenter) w d hT hscale.ne'
    hSmallε hSmallδ (μ ^ 9) hGrowth hInvCoupling
  have hCenterOn : CenterWaveOn w.gradient d.waveVector d.amplitude start finish (μ ^ 9) := by
    change CenterWaveOn w.gradient d.waveVector d.amplitude start (w.clock T) (μ ^ 9)
      at hCenterActual
    rw [hClock] at hCenterActual
    exact hCenterActual
  have hFirstHalf : d.crossing - start ≤ half :=
    d.delay_bounds.2.trans ((div_le_iff₀ w.rate_pos).mpr (by
      simpa only [mul_comm half] using hHorizonHalf))
  have hStartCross : start < d.crossing := by
    have h := d.crossing_after_switch
    unfold PhysicalAmplification.clock at h
    linarith only [h, one_div_pos.mpr w.rate_pos]
  exact ⟨⟨T, rfl, hT, hClock, hSmallε, hSmallδ, d, hStartCross, hFirstHalf,
    hCenterOn.congr_gradient p.parent_gradient_eq⟩⟩

end TorusEuler.MovingWaveVector
