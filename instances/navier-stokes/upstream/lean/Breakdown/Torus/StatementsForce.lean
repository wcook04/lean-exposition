import Breakdown.Torus.StatementsSmooth
import Breakdown.Torus.Basic
import Breakdown.Torus.FreqTrSeries

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

def forceSeq (τ : ℝ) (F : Space → Space) (k : Lattice) : Coef :=
  if 0 < τ then (Real.sqrt (weight k) * heatFactor τ k) • divFree k (freqTrCoef F k) else 0

namespace Force.Internal

theorem character_neg_mul (k : Lattice) (x : Space) : character (-k) x * character k x = 1 := by
  rw [FreqTrSeries.Internal.character_neg, Complex.conj_mul', FreqTrSeries.Internal.norm_character]
  simp

theorem integrableOn_character_smul (k : Lattice) {G : Space → Coef} (hG : IntegrableOn G cell) :
    IntegrableOn (fun x => character k x • G x) cell := by
  refine Integrable.mono hG
    ((FreqTrSeries.Internal.continuous_character k).aestronglyMeasurable.smul hG.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_smul, FreqTrSeries.Internal.norm_character, one_mul]

theorem integral_apply {G : Space → Coef} (hG : IntegrableOn G cell) (i : Fin 3) :
    (∫ x in cell, G x).ofLp i = ∫ x in cell, (G x).ofLp i := by
  have h := (EuclideanSpace.proj (𝕜 := ℂ) i).integral_comp_comm hG
  change EuclideanSpace.proj (𝕜 := ℂ) i _ = _
  rw [← h]
  rfl

theorem freqTrCoef_neg_apply (F : Space → Space) (k : Lattice) (i : Fin 3) :
    (freqTrCoef F (-k)).ofLp i = starRingEnd ℂ ((freqTrCoef F k).ofLp i) := by
  by_cases hI : IntegrableOn (fun x => complexify (F x)) cell
  · unfold freqTrCoef
    rw [integral_apply (integrableOn_character_smul _ hI), integral_apply (integrableOn_character_smul _ hI),
      ← integral_conj]
    congr 1
    funext x
    simp only [PiLp.smul_apply, smul_eq_mul, map_mul, FreqTrSeries.Internal.character_neg]
    congr 1
    simp [complexify]
  · have h0 : ∀ m : Lattice, freqTrCoef F m = 0 := by
      intro m
      unfold freqTrCoef
      refine integral_undef fun h => hI ?_
      refine (integrableOn_character_smul (-m) h).congr_fun (fun x _ => ?_) measurableSet_cell
      dsimp only
      rw [smul_smul, character_neg_mul, one_smul]
    rw [h0, h0]
    simp
where
  measurableSet_cell : MeasurableSet cell := FreqTrSeries.Internal.isCompact_cell.isClosed.measurableSet

theorem latVec_ne_zero {k : Lattice} (hk : k ≠ 0) : latVec k ≠ 0 := by
  intro h
  apply hk
  funext i
  have := congrArg (fun c : Coef => c.ofLp i) h
  simpa [latVec] using this

theorem divPairing_divFree (k : Lattice) (c : Coef) : divPairing k (divFree k c) = 0 := by
  unfold divFree
  split_ifs with hk
  · simp [hk, divPairing]
  · rw [Internal.divPairing_eq_inner, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
      Internal.norm_latVec, ← Internal.divPairing_eq_inner]
    have hne : ‖freq k‖ ≠ 0 := by
      rw [← Internal.norm_latVec]
      exact norm_ne_zero_iff.mpr (latVec_ne_zero hk)
    rw [Complex.ofReal_pow]
    refine sub_eq_zero.mpr (div_mul_cancel₀ _ ?_).symm
    simpa using hne

theorem divPairing_real_smul (k : Lattice) (r : ℝ) (c : Coef) : divPairing k (r • c) = r * divPairing k c := by
  simp only [divPairing, PiLp.smul_apply, Complex.real_smul, Finset.mul_sum]
  congr 1
  funext i
  ring

theorem heatFactor_neg (t : ℝ) (k : Lattice) : heatFactor t (-k) = heatFactor t k := by
  simp [heatFactor, FreqTrSeries.Internal.freq_neg, norm_neg]

theorem divFree_neg_apply (k : Lattice) {c d : Coef} (hd : ∀ i, d.ofLp i = starRingEnd ℂ (c.ofLp i)) (i : Fin 3) :
    (divFree (-k) d).ofLp i = starRingEnd ℂ ((divFree k c).ofLp i) := by
  unfold divFree
  by_cases hk : k = 0
  · rw [if_pos (neg_eq_zero.mpr hk), if_pos hk, hd]
  · rw [if_neg (fun h => hk (neg_eq_zero.mp h)), if_neg hk]
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, map_sub, map_mul, map_div₀, hd, divPairing,
      latVec, FreqTrSeries.Internal.freq_neg, norm_neg, Complex.conj_ofReal, map_sum, Pi.neg_apply,
      Int.cast_neg, map_intCast]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring

theorem norm_forceSeq_le {τ : ℝ} (hτ : 0 < τ) (F : Space → Space) (k : Lattice) :
    ‖forceSeq τ F k‖ ≤ Real.sqrt (weight k) * heatFactor τ k * (2 * ‖freqTrCoef F k‖) := by
  unfold forceSeq
  rw [if_pos hτ, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _)
    (Internal.heatFactor_nonneg _ _))]
  exact mul_le_mul_of_nonneg_left (Internal.norm_divFree_le _ _)
    (mul_nonneg (Real.sqrt_nonneg _) (Internal.heatFactor_nonneg _ _))

theorem sq_norm_forceSeq_le {τ : ℝ} (hτ : 0 < τ) (F : Space → Space) (k : Lattice) :
    ‖forceSeq τ F k‖ ^ 2 ≤ 4 * ‖freqTrCoef F k‖ ^ 2 * (weight k * heatFactor τ k ^ 2) := by
  have h := norm_forceSeq_le hτ F k
  have h0 : 0 ≤ ‖forceSeq τ F k‖ := norm_nonneg _
  calc ‖forceSeq τ F k‖ ^ 2 ≤ (Real.sqrt (weight k) * heatFactor τ k * (2 * ‖freqTrCoef F k‖)) ^ 2 :=
        pow_le_pow_left₀ h0 h 2
    _ = 4 * ‖freqTrCoef F k‖ ^ 2 * (weight k * heatFactor τ k ^ 2) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (Internal.weight_pos k).le]
        ring

end Force.Internal

theorem memℓp_forceSeq (τ : ℝ) (F : Space → Space) : Memℓp (forceSeq τ F) 2 := by
  by_cases hτ : 0 < τ
  · rw [memℓp_gen_iff (by norm_num)]
    set A := ∫ x in cell, ‖complexify (F x)‖
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((Internal.summable_weight_heat hτ).mul_left (4 * A ^ 2))
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    refine (Force.Internal.sq_norm_forceSeq_le hτ F k).trans ?_
    have hA : ‖freqTrCoef F k‖ ≤ A := FreqTrSeries.Internal.norm_freqTrCoef_le k
    have hw : 0 ≤ weight k * heatFactor τ k ^ 2 :=
      mul_nonneg (Internal.weight_pos k).le (sq_nonneg _)
    gcongr
  · have h : forceSeq τ F = 0 := funext fun k => if_neg hτ
    rw [h]
    exact zero_memℓp

theorem forceSeq_mem (τ : ℝ) (F : Space → Space) :
    (⟨forceSeq τ F, memℓp_forceSeq τ F⟩ : Seq) ∈ fieldSpace := by
  change (∀ k i, (forceSeq τ F (-k)).ofLp i = starRingEnd ℂ ((forceSeq τ F k).ofLp i)) ∧
    ∀ k, divPairing k (forceSeq τ F k) = 0
  refine ⟨fun k i => ?_, fun k => ?_⟩
  · unfold forceSeq
    split_ifs with hτ
    · rw [FreqTrSeries.Internal.weight_neg, Force.Internal.heatFactor_neg, PiLp.smul_apply, PiLp.smul_apply,
        Force.Internal.divFree_neg_apply k (Force.Internal.freqTrCoef_neg_apply F k)]
      simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]
    · simp
  · unfold forceSeq
    split_ifs with hτ
    · rw [Force.Internal.divPairing_real_smul, Force.Internal.divPairing_divFree, mul_zero]
    · simp [divPairing]

def forceV (τ : ℝ) (F : Space → Space) : V := ⟨⟨forceSeq τ F, memℓp_forceSeq τ F⟩, forceSeq_mem τ F⟩

def IsForcedMildOnIcc (u : ℝ → V) (F : ℝ → Space → Space) (a b : ℝ) : Prop :=
  ContinuousOn u (Icc a b) ∧
    ∀ t ∈ Icc a b, IntervalIntegrable (fun s => kernel (t - s) (u s) (u s)) volume a t ∧
      IntervalIntegrable (fun s => forceV (t - s) (F s)) volume a t ∧
      u t = heat (t - a) (u a) + (∫ s in a..t, kernel (t - s) (u s) (u s)) +
        ∫ s in a..t, forceV (t - s) (F s)

def IsForcedPeriodicSolution (u : ℝ → Space → Space) (p : ℝ → Space → ℝ) (F : ℝ → Space → Space)
    (a b : ℝ) : Prop :=
  ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2) (Icc a b ×ˢ univ) ∧
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => p z.1 z.2) (Icc a b ×ˢ univ) ∧
    ContinuousOn (fun z : ℝ × Space => F z.1 z.2) (Icc a b ×ˢ univ) ∧
    (∀ t ∈ Icc a b, IsPeriodic (u t) ∧ IsPeriodic (p t) ∧ IsPeriodic (F t)) ∧
    (∀ t ∈ Icc a b, ∀ x, divergenceAt (u t) x = 0) ∧
    ∀ t ∈ Ioo a b, ∀ x, deriv (fun τ => u τ x) t + advectionAt (u t) x - sumSecondPartialsAt (u t) x
      + gradientAt (p t) x = F t x

def ForcedPeriodicIsMild : Prop :=
  ∀ (u : ℝ → Space → Space) (p : ℝ → Space → ℝ) (F : ℝ → Space → Space) (a b : ℝ), a < b →
    IsForcedPeriodicSolution u p F a b → IsForcedMildOnIcc (fun t => toV (u t)) F a b

def ForceSmoothing : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ F : Space → Space, Continuous F → IsPeriodic F →
    ‖forceV τ F‖ ≤ C * τ ^ (-(1 / 2 : ℝ)) * Real.sqrt (∫ x in cell, ‖F x‖ ^ 2)

end Breakdown.Periodic
