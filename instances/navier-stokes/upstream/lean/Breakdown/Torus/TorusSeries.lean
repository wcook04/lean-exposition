import Breakdown.Torus.StatementsSmooth
import Breakdown.Torus.StatementsCoeff
import Breakdown.Torus.TrigHs
import Breakdown.Torus.Trilinear

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace Breakdown.Periodic

instance factOneLeSixLattice : Fact ((1 : ℝ≥0∞) ≤ 6) := ⟨by norm_num⟩

open Classical in
def lpOrZero (p : ℝ≥0∞) (m : Measure Space) (f : Space → Coef) : Lp Coef p m :=
  if h : MemLp f p m then h.toLp f else 0

def torusSeries (p : ℝ≥0∞) [Fact (1 ≤ p)] (c : Lattice → Coef) : Lp Coef p (volume.restrict cell) :=
  ∑' k, lpOrZero p (volume.restrict cell) (fun x => character (-k) x • c k)

def gradCoef (j : Fin 3) (z : V) (k : Lattice) : Coef := (2 * π * Complex.I * (k j : ℂ)) • coeff z k

namespace TorusSeries.Internal

theorem finite_cell : IsFiniteMeasure (volume.restrict cell) :=
  isFiniteMeasure_restrict.2 Trilinear.Internal.isCompact_cell.measure_lt_top.ne

theorem memLp_of_continuous (p : ℝ≥0∞) {g : Space → Coef} (hg : Continuous g) :
    MemLp g p (volume.restrict cell) := by
  have := finite_cell
  obtain ⟨C, hC⟩ := Trilinear.Internal.isCompact_cell.exists_bound_of_continuousOn hg.continuousOn
  exact MemLp.of_bound hg.aestronglyMeasurable C
    ((ae_restrict_iff' Trilinear.Internal.isCompact_cell.isClosed.measurableSet).2 (ae_of_all _ hC))

def term (c : Lattice → Coef) (k : Lattice) (x : Space) : Coef := character (-k) x • c k

theorem continuous_term (c : Lattice → Coef) (k : Lattice) : Continuous (term c k) :=
  (TrigHs.Internal.continuous_character_neg k).smul continuous_const

theorem lpOrZero_term (p : ℝ≥0∞) (c : Lattice → Coef) (k : Lattice) :
    lpOrZero p (volume.restrict cell) (fun x => character (-k) x • c k) =
      (memLp_of_continuous p (continuous_term c k)).toLp (term c k) := by
  have h : MemLp (fun x => character (-k) x • c k) p (volume.restrict cell) :=
    memLp_of_continuous p (continuous_term c k)
  unfold lpOrZero
  rw [dif_pos h]
  rfl

def partialSum (c : Lattice → Coef) (s : Finset Lattice) (x : Space) : Coef :=
  ∑ k ∈ s, character (-k) x • c k

theorem continuous_partialSum (c : Lattice → Coef) (s : Finset Lattice) :
    Continuous (partialSum c s) := by
  unfold partialSum
  exact continuous_finsetSum _ (fun k _ => continuous_term c k)

theorem sum_lpOrZero (p : ℝ≥0∞) (c : Lattice → Coef) (s : Finset Lattice) :
    ∑ k ∈ s, lpOrZero p (volume.restrict cell) (fun x => character (-k) x • c k) =
      (memLp_of_continuous p (continuous_partialSum c s)).toLp (partialSum c s) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · have h0 : MemLp (0 : Space → Coef) p (volume.restrict cell) := memLp_of_continuous p continuous_zero
    rw [Finset.sum_empty, eq_comm, ← MemLp.toLp_zero h0, MemLp.toLp_eq_toLp_iff]
    exact ae_of_all _ fun x => by simp [partialSum]
  · intro a s ha ih
    rw [Finset.sum_insert ha, ih, lpOrZero_term, ← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
    exact ae_of_all _ fun x => by simp [partialSum, term, Finset.sum_insert ha]

theorem norm_sum_lpOrZero (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (c : Lattice → Coef) (s : Finset Lattice) :
    ‖∑ k ∈ s, lpOrZero p (volume.restrict cell) (fun x => character (-k) x • c k)‖ =
      (∫ x in cell, ‖∑ k ∈ s, character (-k) x • c k‖ ^ p.toReal) ^ p.toReal⁻¹ := by
  rw [sum_lpOrZero, Lp.norm_toLp,
    MemLp.eLpNorm_eq_integral_rpow_norm hp0 hpt (memLp_of_continuous p (continuous_partialSum c s)),
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _)]
  rfl

theorem norm_sum_two (c : Lattice → Coef) (s : Finset Lattice) :
    ‖∑ k ∈ s, lpOrZero 2 (volume.restrict cell) (fun x => character (-k) x • c k)‖ =
      √(∑ k ∈ s, ‖c k‖ ^ 2) := by
  rw [norm_sum_lpOrZero 2 (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
  simp_rw [Real.rpow_two]
  rw [Trilinear.Internal.integral_norm_sq_sum, Real.sqrt_eq_rpow, one_div]

theorem norm_sum_six_le {C : ℝ} (hC : ∀ (s : Finset Lattice) (c : Lattice → Coef),
    (∫ x in cell, ‖∑ k ∈ s, character (-k) x • c k‖ ^ (6 : ℝ)) ^ (1 / 6 : ℝ) ≤
      C * (∑ k ∈ s, weight k * ‖c k‖ ^ 2) ^ (1 / 2 : ℝ)) (c : Lattice → Coef) (s : Finset Lattice) :
    ‖∑ k ∈ s, lpOrZero 6 (volume.restrict cell) (fun x => character (-k) x • c k)‖ ≤
      C * √(∑ k ∈ s, weight k * ‖c k‖ ^ 2) := by
  rw [norm_sum_lpOrZero 6 (by norm_num) (by norm_num), ENNReal.toReal_ofNat, Real.sqrt_eq_rpow,
    ← one_div]
  exact hC s c

theorem summable_of_bound {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (L : Lattice → E)
    (g : Lattice → ℝ) (hg0 : ∀ k, 0 ≤ g k) (hg : Summable g) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ t : Finset Lattice, ‖∑ k ∈ t, L k‖ ≤ C * √(∑ k ∈ t, g k)) : Summable L := by
  rw [summable_iff_vanishing_norm]
  intro ε hε
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < (ε / (C + 1)) ^ 2 := by positivity
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.1 hg _ hδ
  refine ⟨s, fun t ht => ?_⟩
  have h1 := hs t ht
  have h2 : 0 ≤ ∑ k ∈ t, g k := Finset.sum_nonneg fun k _ => hg0 k
  rw [Real.norm_of_nonneg h2] at h1
  have h3 : √(∑ k ∈ t, g k) < ε / (C + 1) := by
    rw [Real.sqrt_lt' (by positivity)]
    exact h1
  have h4 : C * (ε / (C + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ hC1]
    nlinarith
  calc ‖∑ k ∈ t, L k‖ ≤ C * √(∑ k ∈ t, g k) := h t
    _ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left h3.le hC
    _ < ε := h4

theorem norm_tsum_le_of_bound {E : Type*} [NormedAddCommGroup E] (L : Lattice → E) (hL : Summable L)
    (g : Lattice → ℝ) (hg0 : ∀ k, 0 ≤ g k) (hg : Summable g) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ t : Finset Lattice, ‖∑ k ∈ t, L k‖ ≤ C * √(∑ k ∈ t, g k)) :
    ‖∑' k, L k‖ ≤ C * √(∑' k, g k) := by
  refine le_of_tendsto' hL.hasSum.norm fun t => (h t).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hg.sum_le_tsum t fun k _ => hg0 k)) hC

theorem summable_two (c : Lattice → Coef) (hc : Summable fun k => ‖c k‖ ^ 2) :
    Summable (fun k => lpOrZero 2 (volume.restrict cell) (fun x => character (-k) x • c k)) :=
  summable_of_bound _ _ (fun _ => sq_nonneg _) hc 1 zero_le_one fun t => by
    rw [norm_sum_two, one_mul]

theorem summable_six (c : Lattice → Coef) (hc : Summable fun k => weight k * ‖c k‖ ^ 2) :
    Summable (fun k => lpOrZero 6 (volume.restrict cell) (fun x => character (-k) x • c k)) := by
  obtain ⟨C, hC0, hC⟩ := trigHs
  exact summable_of_bound _ _ (fun k => mul_nonneg (Trilinear.Internal.weight_pos k).le (sq_nonneg _))
    hc C hC0.le (norm_sum_six_le hC c)

theorem summable_coeff_sq (z : V) : Summable fun k => ‖coeff z k‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun k => le_mul_of_one_le_left (sq_nonneg _) (Trilinear.Internal.one_le_weight k))
    (Trilinear.Internal.hasSum_weight_coeff z).summable

theorem norm_gradCoef_sq_le (j : Fin 3) (z : V) (k : Lattice) :
    ‖gradCoef j z k‖ ^ 2 ≤ weight k * ‖coeff z k‖ ^ 2 := by
  have e : ‖(2 * π * Complex.I * (k j : ℂ))‖ = 2 * π * |(k j : ℝ)| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_intCast, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos pi_pos]
    simp
  have h1 : ((k j : ℝ)) ^ 2 ≤ ‖freq k‖ ^ 2 := by
    rw [TrigHs.Internal.norm_freq_sq]
    exact Finset.single_le_sum (f := fun i => ((k i : ℝ)) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : (2 * π * |(k j : ℝ)|) ^ 2 ≤ weight k := by
    have := Trilinear.Internal.freq_le_weight k
    rw [mul_pow, sq_abs]
    nlinarith [pi_pos]
  rw [gradCoef, norm_smul, mul_pow, e]
  exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

end TorusSeries.Internal

open TorusSeries.Internal

theorem summable_torusSeries (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p = 2 ∨ p = 6) (z : V) :
    Summable (fun k => lpOrZero p (volume.restrict cell) (fun x => character (-k) x • coeff z k)) := by
  rcases hp with rfl | rfl
  · exact summable_two (coeff z) (summable_coeff_sq z)
  · exact summable_six (coeff z) (Trilinear.Internal.hasSum_weight_coeff z).summable

theorem summable_torusSeries_grad (j : Fin 3) (z : V) :
    Summable (fun k => lpOrZero 2 (volume.restrict cell) (fun x => character (-k) x • gradCoef j z k)) :=
  summable_two (gradCoef j z) (Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (norm_gradCoef_sq_le j z) (Trilinear.Internal.hasSum_weight_coeff z).summable)

theorem torusSeries_norm_sq (c : Lattice → Coef) (hc : Summable (fun k => ‖c k‖ ^ 2)) :
    ‖torusSeries 2 c‖ ^ 2 = ∑' k, ‖c k‖ ^ 2 := by
  have hL := summable_two c hc
  have h1 := hL.hasSum.norm.pow 2
  have e : (fun t : Finset Lattice =>
      ‖∑ k ∈ t, lpOrZero 2 (volume.restrict cell) (fun x => character (-k) x • c k)‖ ^ 2) =
      fun t => ∑ k ∈ t, ‖c k‖ ^ 2 := funext fun t => by
    rw [norm_sum_two, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rw [e] at h1
  have h2 : HasSum (fun k => ‖c k‖ ^ 2) (‖torusSeries 2 c‖ ^ 2) := h1
  exact h2.tsum_eq.symm

theorem torusSeries_add (p : ℝ≥0∞) [Fact (1 ≤ p)] (c d : Lattice → Coef)
    (hc : Summable (fun k => lpOrZero p (volume.restrict cell) (fun x => character (-k) x • c k)))
    (hd : Summable (fun k => lpOrZero p (volume.restrict cell) (fun x => character (-k) x • d k))) :
    torusSeries p (c + d) = torusSeries p c + torusSeries p d := by
  unfold torusSeries
  rw [← hc.tsum_add hd]
  congr 1
  funext k
  rw [lpOrZero_term, lpOrZero_term, lpOrZero_term, ← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
  exact ae_of_all _ fun x => by simp [term, smul_add]

theorem torusSeries_smul (p : ℝ≥0∞) [Fact (1 ≤ p)] (r : ℝ) (c : Lattice → Coef) :
    torusSeries p (r • c) = r • torusSeries p c := by
  unfold torusSeries
  rw [← tsum_const_smul'' r]
  congr 1
  funext k
  rw [lpOrZero_term, lpOrZero_term, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
  exact ae_of_all _ fun x => by
    simp only [term, Pi.smul_apply]
    exact smul_comm _ _ _

theorem torusSeries_six_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : V, ‖torusSeries 6 (coeff z)‖ ≤ C * ‖z‖ := by
  obtain ⟨C, hC0, hC⟩ := trigHs
  refine ⟨C, hC0.le, fun z => ?_⟩
  have hw := Trilinear.Internal.hasSum_weight_coeff z
  have h := norm_tsum_le_of_bound _ (summable_six (coeff z) hw.summable) _
    (fun k => mul_nonneg (Trilinear.Internal.weight_pos k).le (sq_nonneg _)) hw.summable C hC0.le
    (norm_sum_six_le hC (coeff z))
  rw [hw.tsum_eq, Real.sqrt_sq (norm_nonneg z)] at h
  exact h

end Breakdown.Periodic
