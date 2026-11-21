import Breakdown.Torus.HeatComparisonStatements

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace Breakdown.Periodic

namespace StepSum.Internal

theorem freq_coord (k : Lattice) (i : Fin 3) : (freq k) i = (k i : ℝ) := by
  simp [freq, unitVector, Pi.single_apply]

theorem measurable_latticeIndex (h : ℝ) : Measurable (latticeIndex h) := by
  apply measurable_pi_lambda
  intro i
  have : Measurable (fun ξ : Space => ξ i / h) := by fun_prop
  exact this.floor

theorem fibre_eq (h : ℝ) (hh : 0 < h) (k : Lattice) :
    latticeIndex h ⁻¹' {k} =
      (WithLp.ofLp : Space → (Fin 3 → ℝ)) ⁻¹' (pi univ fun i => Ico (h * k i) (h * k i + h)) := by
  ext ξ
  simp only [mem_preimage, mem_singleton_iff, mem_pi, mem_univ, true_implies, mem_Ico]
  constructor
  · intro hk i
    have e := congrFun hk i
    simp only [latticeIndex] at e
    rw [Int.floor_eq_iff, le_div_iff₀ hh, div_lt_iff₀ hh] at e
    change h * (k i : ℝ) ≤ ξ i ∧ ξ i < h * k i + h
    constructor <;> nlinarith [e.1, e.2]
  · intro hk
    funext i
    simp only [latticeIndex]
    rw [Int.floor_eq_iff, le_div_iff₀ hh, div_lt_iff₀ hh]
    have := hk i
    change h * (k i : ℝ) ≤ ξ i ∧ ξ i < h * k i + h at this
    constructor <;> nlinarith [this.1, this.2]

theorem volume_fibre (h : ℝ) (hh : 0 < h) (k : Lattice) :
    volume (latticeIndex h ⁻¹' {k}) = ENNReal.ofReal (h ^ 3) := by
  rw [fibre_eq h hh k, (PiLp.volume_preserving_ofLp (ι := Fin 3)).measure_preimage
    (MeasurableSet.univ_pi fun i => measurableSet_Ico).nullMeasurableSet,
    Real.volume_pi_Ico]
  simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hh.le]

theorem map_singleton (h : ℝ) (hh : 0 < h) (k : Lattice) :
    (Measure.map (latticeIndex h) volume) {k} = ENNReal.ofReal (h ^ 3) := by
  rw [Measure.map_apply (measurable_latticeIndex h) (measurableSet_singleton k)]
  exact volume_fibre h hh k

theorem lintegral_step (h : ℝ) (hh : 0 < h) (c : Lattice → ℝ≥0∞) :
    ∫⁻ ξ, c (latticeIndex h ξ) = ENNReal.ofReal (h ^ 3) * ∑' k, c k := by
  rw [← lintegral_map (measurable_of_countable c) (measurable_latticeIndex h), lintegral_countable']
  simp_rw [map_singleton h hh]
  rw [ENNReal.tsum_mul_right, mul_comm]

theorem integrable_step (h : ℝ) (hh : 0 < h) (c : Lattice → Coef) (hs : Summable fun k => ‖c k‖) :
    Integrable (fun ξ => c (latticeIndex h ξ)) := by
  refine ⟨((measurable_of_countable c).comp (measurable_latticeIndex h)).aestronglyMeasurable, ?_⟩
  have e := lintegral_step h hh (fun k => ‖c k‖ₑ)
  rw [HasFiniteIntegral, e]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have hs' : Summable fun k => ‖c k‖₊ := NNReal.summable_coe.1 (by simpa using hs)
  have : ∑' k, ‖c k‖ₑ = ((∑' k, ‖c k‖₊ : NNReal) : ℝ≥0∞) := by
    rw [ENNReal.coe_tsum hs']
    rfl
  rw [this]
  exact ENNReal.coe_lt_top

theorem integral_step (h : ℝ) (hh : 0 < h) (c : Lattice → Coef) (hs : Summable fun k => ‖c k‖) :
    ∫ ξ, c (latticeIndex h ξ) = (h ^ 3) • ∑' k, c k := by
  have hi := integrable_step h hh c hs
  have hm : AEStronglyMeasurable c (Measure.map (latticeIndex h) volume) :=
    (measurable_of_countable c).aestronglyMeasurable
  rw [← integral_map (measurable_latticeIndex h).aemeasurable hm,
    integral_countable ((integrable_map_measure hm (measurable_latticeIndex h).aemeasurable).2 hi)]
  simp_rw [Measure.real, map_singleton h hh, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ h ^ 3)]
  exact hs.of_norm.tsum_const_smul _

theorem near_lattice (h : ℝ) (hh : 0 < h) (ξ : Space) :
    ‖ξ - h • freq (latticeIndex h ξ)‖ ≤ 2 * h := by
  have hc : ∀ j, ‖(ξ - h • freq (latticeIndex h ξ)) j‖ ≤ h := by
    intro j
    have e : (ξ - h • freq (latticeIndex h ξ)) j = ξ j - h * (⌊ξ j / h⌋ : ℝ) := by
      simp [freq_coord, latticeIndex]
    rw [e, Real.norm_eq_abs, abs_le]
    have h1 := Int.floor_le (ξ j / h)
    have h2 := Int.lt_floor_add_one (ξ j / h)
    have h3 : h * (ξ j / h) = ξ j := by field_simp
    constructor
    · nlinarith
    · nlinarith
  have hsq : ‖ξ - h • freq (latticeIndex h ξ)‖ ^ 2 ≤ (2 * h) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    have a0 := pow_le_pow_left₀ (norm_nonneg _) (hc 0) 2
    have a1 := pow_le_pow_left₀ (norm_nonneg _) (hc 1) 2
    have a2 := pow_le_pow_left₀ (norm_nonneg _) (hc 2) 2
    nlinarith [sq_nonneg h]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

theorem decay_lattice (h : ℝ) (hh : 0 < h) (ξ : Space) :
    (1 + ‖h • freq (latticeIndex h ξ)‖) ^ (-4 : ℝ) ≤ (1 + 2 * h) ^ 4 * (1 + ‖ξ‖) ^ (-4 : ℝ) := by
  set b := 1 + ‖h • freq (latticeIndex h ξ)‖ with hb
  have hx : 0 < 1 + ‖ξ‖ := by positivity
  have hy : 0 < b := by positivity
  have hb1 : 1 ≤ b := by have := norm_nonneg (h • freq (latticeIndex h ξ)); linarith
  have htri : ‖ξ‖ ≤ ‖h • freq (latticeIndex h ξ)‖ + 2 * h := by
    have := norm_sub_norm_le ξ (h • freq (latticeIndex h ξ))
    linarith [near_lattice h hh ξ]
  have hle : 1 + ‖ξ‖ ≤ (1 + 2 * h) * b := by nlinarith
  have e : ∀ t : ℝ, 0 < t → t ^ (-4 : ℝ) = (t ^ 4)⁻¹ := by
    intro t ht
    rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht.le, Real.rpow_natCast]
  rw [e _ hx, e _ hy]
  have hp : (1 + ‖ξ‖) ^ 4 ≤ (1 + 2 * h) ^ 4 * b ^ 4 := by
    calc (1 + ‖ξ‖) ^ 4 ≤ ((1 + 2 * h) * b) ^ 4 := by gcongr
      _ = (1 + 2 * h) ^ 4 * b ^ 4 := by ring
  have hc : 0 < (1 + 2 * h) ^ 4 := by positivity
  calc (b ^ 4)⁻¹ = (1 + 2 * h) ^ 4 * ((1 + 2 * h) ^ 4 * b ^ 4)⁻¹ := by
        rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    _ ≤ (1 + 2 * h) ^ 4 * ((1 + ‖ξ‖) ^ 4)⁻¹ := by gcongr

theorem summable_decay (h : ℝ) (hh : 0 < h) :
    Summable (fun k : Lattice => (1 + ‖h • freq k‖) ^ (-4 : ℝ)) := by
  set f : Lattice → ℝ≥0∞ := fun k => ENNReal.ofReal ((1 + ‖h • freq k‖) ^ (-4 : ℝ)) with hf
  have hint : Integrable (fun ξ : Space => (1 + ‖ξ‖) ^ (-(4 : ℝ))) volume :=
    integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; norm_num)
  have hfin : ∫⁻ ξ, f (latticeIndex h ξ) < ∞ := by
    calc ∫⁻ ξ, f (latticeIndex h ξ)
        ≤ ∫⁻ ξ, ENNReal.ofReal ((1 + 2 * h) ^ 4 * (1 + ‖ξ‖) ^ (-(4 : ℝ))) :=
          lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (decay_lattice h hh ξ)
      _ < ∞ := (hint.const_mul _).lintegral_lt_top
  rw [lintegral_step h hh f] at hfin
  have hne : ∑' k, f k ≠ ∞ := by
    intro htop
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne'] at hfin
    exact lt_irrefl _ hfin
  refine (ENNReal.summable_toReal hne).congr fun k => ?_
  simp only [hf]
  exact ENNReal.toReal_ofReal (by positivity)

end StepSum.Internal

theorem stepIntegral : StepIntegral := by
  intro h hh
  exact ⟨fun c => StepSum.Internal.lintegral_step h hh c,
    fun c hs => ⟨StepSum.Internal.integrable_step h hh c hs, StepSum.Internal.integral_step h hh c hs⟩,
    StepSum.Internal.summable_decay h hh⟩

end Breakdown.Periodic
