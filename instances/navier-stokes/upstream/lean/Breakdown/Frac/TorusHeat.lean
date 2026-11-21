import Breakdown.Frac.StTorusBasic
import Breakdown.Torus.Basic

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown.Periodic

namespace FracTorusHeatInternal

theorem factor_pos (α t : ℝ) (k : Lattice) : 0 < fracLatticeFactor α t k := Real.exp_pos _

theorem factor_le_one (α t : ℝ) (k : Lattice) : fracLatticeFactor α t k ≤ 1 := by
  rw [fracLatticeFactor, Real.exp_le_one_iff, neg_nonpos]
  have h1 : 0 ≤ (2 * π * ‖freq k‖) ^ (2 * α) := Real.rpow_nonneg (by positivity) _
  exact mul_nonneg h1 (le_max_right t 0)

theorem abs_factor_le (α t : ℝ) (k : Lattice) : |fracLatticeFactor α t k| ≤ 1 := by
  rw [abs_of_pos (factor_pos α t k)]
  exact factor_le_one α t k

theorem freq_neg (k : Lattice) : freq (-k) = -freq k := by
  simp [freq, Finset.sum_neg_distrib]

theorem factor_neg (α t : ℝ) (k : Lattice) :
    fracLatticeFactor α t (-k) = fracLatticeFactor α t k := by
  rw [fracLatticeFactor, fracLatticeFactor, freq_neg, norm_neg]

theorem factor_add (α : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (k : Lattice) :
    fracLatticeFactor α (s + t) k = fracLatticeFactor α s k * fracLatticeFactor α t k := by
  unfold fracLatticeFactor
  rw [max_eq_left (add_nonneg hs ht), max_eq_left hs, max_eq_left ht, ← Real.exp_add]
  ring_nf

theorem factor_zero (α : ℝ) (k : Lattice) : fracLatticeFactor α 0 k = 1 := by
  simp [fracLatticeFactor]

theorem factor_max (α t : ℝ) (k : Lattice) :
    fracLatticeFactor α (max t 0) k = fracLatticeFactor α t k := by
  simp only [fracLatticeFactor, max_eq_left (le_max_right t 0)]

theorem continuous_factor (α : ℝ) (k : Lattice) : Continuous fun t => fracLatticeFactor α t k := by
  unfold fracLatticeFactor
  exact Real.continuous_exp.comp ((continuous_const.mul (continuous_id.max continuous_const)).neg)

theorem divPairing_real_smul (k : Lattice) (r : ℝ) (c : Coef) :
    divPairing k (r • c) = (r : ℂ) * divPairing k c := by
  simp only [divPairing, PiLp.smul_apply, Complex.real_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem mem (α t : ℝ) (a : V) :
    mulSeq (fracLatticeFactor α t) zero_le_one (abs_factor_le α t) (a : Seq) ∈ fieldSpace := by
  have ha2 : (∀ k i, ((a : Seq) (-k)) i = starRingEnd ℂ (((a : Seq) k) i)) ∧
      ∀ k, divPairing k ((a : Seq) k) = 0 := a.2
  obtain ⟨ha, ha'⟩ := ha2
  refine ⟨fun k i => ?_, fun k => ?_⟩
  · show (fracLatticeFactor α t (-k) • (a : Seq) (-k)) i =
      starRingEnd ℂ ((fracLatticeFactor α t k • (a : Seq) k) i)
    rw [factor_neg, PiLp.smul_apply, PiLp.smul_apply, ha k i]
    simp [Complex.real_smul]
  · show divPairing k (fracLatticeFactor α t k • (a : Seq) k) = 0
    rw [divPairing_real_smul, ha' k, mul_zero]

def op (α t : ℝ) : V →L[ℝ] V :=
  ((mulSeq (fracLatticeFactor α t) zero_le_one (abs_factor_le α t)).comp
    fieldSpace.subtypeL).codRestrict fieldSpace (mem α t)

theorem op_apply (α t : ℝ) (x : V) (k : Lattice) :
    ((op α t x : V) : Seq) k = fracLatticeFactor α t k • (x : Seq) k := rfl

theorem op_spec (α t : ℝ) : FracTorusHeatSpec α t (op α t) := by
  intro u k
  rw [coeff, coeff, op_apply]
  exact smul_comm _ _ _

theorem heat_eq (α t : ℝ) : fracTorusHeat α t = op α t := by
  have h : ∃ H, FracTorusHeatSpec α t H := ⟨op α t, op_spec α t⟩
  unfold fracTorusHeat
  rw [dif_pos h]
  refine ContinuousLinearMap.ext fun x => coeff_injective fun k => ?_
  rw [h.choose_spec x k, op_spec α t x k]

theorem op_continuous (α : ℝ) (x : V) : Continuous fun t => op α t x := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, tendsto_subtype_rng]
  apply Internal.tendsto_seq (b := fun k => ‖(x : Seq) k‖) (Internal.summable_sq _)
  · intro k
    simp only [op_apply]
    exact ((continuous_factor α k).tendsto t₀).smul_const _
  · refine Eventually.of_forall fun t k => ?_
    rw [op_apply, norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by simpa using abs_factor_le α t k)

end FracTorusHeatInternal

open FracTorusHeatInternal

theorem fracTorusHeatExists (α : ℝ) : FracTorusHeatExists α := fun t => ⟨op α t, op_spec α t⟩

theorem fracTorusHeatAlgebra (α : ℝ) : FracTorusHeatAlgebra α := by
  refine ⟨fun t u k => ?_, ?_, fun s t hs ht => ?_, fun t => ?_, fun t => ?_, fun x => ?_⟩
  · rw [heat_eq]
    exact op_spec α t u k
  · rw [heat_eq]
    ext1 x
    apply Subtype.ext
    apply lp.ext
    funext k
    rw [op_apply, factor_zero, one_smul]
    rfl
  · rw [heat_eq, heat_eq, heat_eq]
    ext1 x
    apply Subtype.ext
    apply lp.ext
    funext k
    rw [ContinuousLinearMap.comp_apply, op_apply, op_apply, op_apply, smul_smul, factor_add α hs ht]
  · rw [heat_eq]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    show ‖((op α t x : V) : Seq)‖ ≤ ‖(x : Seq)‖
    apply Internal.norm_le_of_le
    intro k
    rw [op_apply, norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by simpa using abs_factor_le α t k)
  · rw [heat_eq, heat_eq]
    ext1 x
    apply Subtype.ext
    apply lp.ext
    funext k
    rw [op_apply, op_apply, factor_max]
  · have e : (fun t => fracTorusHeat α t x) = fun t => op α t x := funext fun t => by rw [heat_eq]
    rw [e]
    exact op_continuous α x

end Breakdown.Periodic
