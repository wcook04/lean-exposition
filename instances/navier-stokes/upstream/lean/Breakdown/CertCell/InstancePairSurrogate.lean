import Breakdown.CertCell.InstancePairShares
import Breakdown.CertCell.InstancePairHalfPlane

open scoped ENNReal ComplexOrder
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace InstancePair

open Instance

namespace Internal

open Coercive Bridge Breakdown.CertCell.InstancePair.Internal.PairHalf

def SqWeighted (μ : Measure (ℝ × ℝ)) (f : ℝ × ℝ → ℂ) : Prop :=
  AEStronglyMeasurable f μ ∧ Integrable (fun p => p.1 * ‖f p‖ ^ 2) μ

theorem surr_entry_young {k : ℕ} {w : ℝ} (hw : 0 < w) (z : ℂ) (d : Fin k → ℂ) (κ : Fin k → ℝ) :
    ∑ i, κ i * (z * starRingEnd ℂ (d i)).re
      ≤ w * ‖z‖ ^ 2 + (4 * w)⁻¹ * (∑ i, κ i ^ 2) * ∑ i, ‖d i‖ ^ 2 := by
  set S := ∑ i, |κ i| * ‖d i‖ with hS
  have h1 : ∑ i, κ i * (z * starRingEnd ℂ (d i)).re ≤ ‖z‖ * S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc κ i * (z * starRingEnd ℂ (d i)).re ≤ |κ i * (z * starRingEnd ℂ (d i)).re| := le_abs_self _
      _ = |κ i| * |(z * starRingEnd ℂ (d i)).re| := abs_mul _ _
      _ ≤ |κ i| * ‖z * starRingEnd ℂ (d i)‖ :=
          mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg _)
      _ = ‖z‖ * (|κ i| * ‖d i‖) := by rw [norm_mul, Complex.norm_conj]; ring
  have h2 : S ^ 2 ≤ (∑ i, κ i ^ 2) * ∑ i, ‖d i‖ ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |κ i|) (fun i => ‖d i‖)
    simpa only [sq_abs] using h
  have hw0 : w ≠ 0 := hw.ne'
  have h3 : ‖z‖ * S ≤ w * ‖z‖ ^ 2 + (4 * w)⁻¹ * S ^ 2 := by
    have e : w * ‖z‖ ^ 2 + (4 * w)⁻¹ * S ^ 2 - ‖z‖ * S = (4 * w)⁻¹ * (2 * w * ‖z‖ - S) ^ 2 := by
      field_simp
      ring
    have : 0 ≤ (4 * w)⁻¹ * (2 * w * ‖z‖ - S) ^ 2 := by positivity
    linarith
  have h4 : (4 * w)⁻¹ * S ^ 2 ≤ (4 * w)⁻¹ * ((∑ i, κ i ^ 2) * ∑ i, ‖d i‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  rw [mul_assoc ((4 * w)⁻¹)]
  linarith

theorem surr_point_young {k : ℕ} {w : ℝ} (hw : 0 < w) (g : Fin 3 → Fin 3 → ℂ)
    (d : Fin k → Fin 3 → Fin 3 → ℂ) (κ : Fin k → ℝ) :
    ∑ i, κ i * (∑ a : Fin 3, ∑ b : Fin 3, g a b * starRingEnd ℂ (d i a b)).re
      ≤ w * ∑ a : Fin 3, ∑ b : Fin 3, ‖g a b‖ ^ 2
        + (4 * w)⁻¹ * (∑ i, κ i ^ 2) * ∑ i, ∑ a : Fin 3, ∑ b : Fin 3, ‖d i a b‖ ^ 2 := by
  have hL : ∑ i, κ i * (∑ a : Fin 3, ∑ b : Fin 3, g a b * starRingEnd ℂ (d i a b)).re
      = ∑ a : Fin 3, ∑ b : Fin 3, ∑ i, κ i * (g a b * starRingEnd ℂ (d i a b)).re := by
    simp only [Complex.re_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  have hR : (4 * w)⁻¹ * (∑ i, κ i ^ 2) * ∑ i, ∑ a : Fin 3, ∑ b : Fin 3, ‖d i a b‖ ^ 2
      = ∑ a : Fin 3, ∑ b : Fin 3, (4 * w)⁻¹ * (∑ i, κ i ^ 2) * ∑ i, ‖d i a b‖ ^ 2 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  rw [hL, hR, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun b _ => surr_entry_young hw (g a b) (fun i => d i a b) κ

theorem surr_integrable_pair {μ : Measure (ℝ × ℝ)} (hρ : ∀ᵐ p ∂μ, 0 ≤ p.1) {f h : ℝ × ℝ → ℂ}
    (hf : SqWeighted μ f) (hh : SqWeighted μ h) :
    Integrable (fun p => (p.1 : ℂ) * (f p * starRingEnd ℂ (h p))) μ := by
  refine Integrable.mono' (hf.2.add hh.2) ?_ ?_
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable measurable_fst.aestronglyMeasurable).mul
      (hf.1.mul (Complex.continuous_conj.comp_aestronglyMeasurable hh.1))
  · filter_upwards [hρ] with p hp
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hp]
    have h0 : 0 ≤ p.1 * (‖f p‖ * ‖h p‖) := mul_nonneg hp (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    show p.1 * (‖f p‖ * ‖h p‖) ≤ p.1 * ‖f p‖ ^ 2 + p.1 * ‖h p‖ ^ 2
    nlinarith [mul_nonneg hp (sq_nonneg (‖f p‖ - ‖h p‖))]

theorem surr_integrable_sum {μ : Measure (ℝ × ℝ)} (hρ : ∀ᵐ p ∂μ, 0 ≤ p.1) {g X : Fin 3 → Fin 3 → ℝ × ℝ → ℂ}
    (hg : ∀ a b, SqWeighted μ (g a b)) (hX : ∀ a b, SqWeighted μ (X a b)) :
    Integrable (fun p => (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (X a b p)) μ := by
  have e : (fun p : ℝ × ℝ => (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (X a b p))
      = fun p => ∑ a : Fin 3, ∑ b : Fin 3, (p.1 : ℂ) * (g a b p * starRingEnd ℂ (X a b p)) := by
    funext p
    simp only [Finset.mul_sum]
  rw [e]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    surr_integrable_pair hρ (hg a b) (hX a b)

theorem surr_integrable_re {μ : Measure (ℝ × ℝ)} (hρ : ∀ᵐ p ∂μ, 0 ≤ p.1) {g X : Fin 3 → Fin 3 → ℝ × ℝ → ℂ}
    (hg : ∀ a b, SqWeighted μ (g a b)) (hX : ∀ a b, SqWeighted μ (X a b)) :
    Integrable (fun p => p.1 * (∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (X a b p)).re) μ := by
  refine (surr_integrable_sum hρ hg hX).re.congr (ae_of_all _ fun p => ?_)
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul]

theorem surr_re_integral {μ : Measure (ℝ × ℝ)} (hρ : ∀ᵐ p ∂μ, 0 ≤ p.1) {g X : Fin 3 → Fin 3 → ℝ × ℝ → ℂ}
    (hg : ∀ a b, SqWeighted μ (g a b)) (hX : ∀ a b, SqWeighted μ (X a b)) :
    (∫ p, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (X a b p) ∂μ).re
      = ∫ p, p.1 * (∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (X a b p)).re ∂μ := by
  have h := integral_re (𝕜 := ℂ) (surr_integrable_sum hρ hg hX)
  simp only [RCLike.re_to_complex] at h
  rw [← h]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [Complex.re_ofReal_mul]

theorem surr_integrable_sq {μ : Measure (ℝ × ℝ)} {g : Fin 3 → Fin 3 → ℝ × ℝ → ℂ}
    (hg : ∀ a b, SqWeighted μ (g a b)) :
    Integrable (fun p => p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖g a b p‖ ^ 2) μ := by
  have e : (fun p : ℝ × ℝ => p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖g a b p‖ ^ 2)
      = fun p => ∑ a : Fin 3, ∑ b : Fin 3, p.1 * ‖g a b p‖ ^ 2 := by
    funext p
    simp only [Finset.mul_sum]
  rw [e]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hg a b).2

theorem surr_sqw_sub {μ : Measure (ℝ × ℝ)} (hρ : ∀ᵐ p ∂μ, 0 ≤ p.1) {f h : ℝ × ℝ → ℂ}
    (hf : SqWeighted μ f) (hh : SqWeighted μ h) : SqWeighted μ (fun p => f p - h p) := by
  refine ⟨hf.1.sub hh.1, Integrable.mono' ((hf.2.add hh.2).const_mul 2) ?_ ?_⟩
  · exact measurable_fst.aestronglyMeasurable.mul ((hf.1.sub hh.1).norm.pow 2)
  · filter_upwards [hρ] with p hp
    rw [Real.norm_of_nonneg (mul_nonneg hp (sq_nonneg _))]
    have h1 : ‖f p - h p‖ ^ 2 ≤ 2 * ‖f p‖ ^ 2 + 2 * ‖h p‖ ^ 2 := by
      have h3 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (f p) (h p)) 2
      nlinarith [sq_nonneg (‖f p‖ - ‖h p‖)]
    have h2 := mul_le_mul_of_nonneg_left h1 hp
    show p.1 * ‖f p - h p‖ ^ 2 ≤ 2 * (p.1 * ‖f p‖ ^ 2 + p.1 * ‖h p‖ ^ 2)
    nlinarith [h2]

theorem surr_label_bound {k : ℕ} {μ : Measure (ℝ × ℝ)} (hρ : ∀ᵐ p ∂μ, 0 ≤ p.1) {w : ℝ} (hw : 0 < w)
    (g : Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (X Y : Fin k → Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (hg : ∀ a b, SqWeighted μ (g a b)) (hX : ∀ i a b, SqWeighted μ (X i a b))
    (hY : ∀ i a b, SqWeighted μ (Y i a b)) (κ : Fin k → ℝ) :
    ∑ i, κ i * (∫ p, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (X i a b p) ∂μ).re
      ≤ ∑ i, κ i * (∫ p, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (Y i a b p) ∂μ).re
        + w * ∫ p, p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖g a b p‖ ^ 2 ∂μ
        + (4 * w)⁻¹ * (∑ i, κ i ^ 2) *
          ∑ i, ∫ p, p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖X i a b p - Y i a b p‖ ^ 2 ∂μ := by
  have eX : ∀ i, (∫ p, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (X i a b p) ∂μ).re
      = ∫ p, p.1 * (∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (X i a b p)).re ∂μ :=
    fun i => surr_re_integral hρ hg (hX i)
  have eY : ∀ i, (∫ p, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (Y i a b p) ∂μ).re
      = ∫ p, p.1 * (∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (Y i a b p)).re ∂μ :=
    fun i => surr_re_integral hρ hg (hY i)
  simp only [eX, eY]
  have hu : ∀ i, Integrable (fun p => p.1 * (∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (X i a b p)).re) μ :=
    fun i => surr_integrable_re hρ hg (hX i)
  have hv : ∀ i, Integrable (fun p => p.1 * (∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (Y i a b p)).re) μ :=
    fun i => surr_integrable_re hρ hg (hY i)
  have hG : Integrable (fun p => p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖g a b p‖ ^ 2) μ := surr_integrable_sq hg
  have hE : ∀ i, Integrable (fun p => p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖X i a b p - Y i a b p‖ ^ 2) μ :=
    fun i => surr_integrable_sq fun a b => surr_sqw_sub hρ (hX i a b) (hY i a b)
  set c := (4 * w)⁻¹ * (∑ i, κ i ^ 2) with hc
  have Lu : ∑ i, κ i * ∫ p, p.1 * (∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (X i a b p)).re ∂μ
      = ∫ p, ∑ i, κ i * (p.1 * (∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (X i a b p)).re) ∂μ := by
    rw [integral_finsetSum _ fun i _ => (hu i).const_mul (κ i)]
    exact Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm
  have Lv : ∑ i, κ i * ∫ p, p.1 * (∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (Y i a b p)).re ∂μ
      = ∫ p, ∑ i, κ i * (p.1 * (∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (Y i a b p)).re) ∂μ := by
    rw [integral_finsetSum _ fun i _ => (hv i).const_mul (κ i)]
    exact Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm
  have LE : c * ∑ i, ∫ p, p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖X i a b p - Y i a b p‖ ^ 2 ∂μ
      = ∫ p, c * ∑ i, p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖X i a b p - Y i a b p‖ ^ 2 ∂μ := by
    rw [integral_const_mul, integral_finsetSum _ fun i _ => hE i]
  have LG : w * ∫ p, p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖g a b p‖ ^ 2 ∂μ
      = ∫ p, w * (p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖g a b p‖ ^ 2) ∂μ := (integral_const_mul _ _).symm
  have iu := integrable_finsetSum Finset.univ fun i _ => (hu i).const_mul (κ i)
  have iv := integrable_finsetSum Finset.univ fun i _ => (hv i).const_mul (κ i)
  have iE := (integrable_finsetSum Finset.univ fun i _ => hE i).const_mul c
  rw [Lu, Lv, LE, LG, ← integral_add iv (hG.const_mul w)]
  have hadd := integral_add (iv.add (hG.const_mul w)) iE
  simp only [Pi.add_apply] at hadd
  rw [← hadd]
  refine integral_mono_ae iu ((iv.add (hG.const_mul w)).add iE) ?_
  filter_upwards [hρ] with p hp
  have hy := surr_point_young hw (fun a b => g a b p) (fun i a b => X i a b p - Y i a b p) κ
  have e1 : ∀ i, (∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (X i a b p)).re
      = (∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (Y i a b p)).re
        + (∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (X i a b p - Y i a b p)).re := by
    intro i
    rw [← Complex.add_re, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_sub]
    ring
  simp only [e1, mul_add, Finset.sum_add_distrib]
  have e2 : ∑ i, κ i * (p.1 * (∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (X i a b p - Y i a b p)).re)
      = p.1 * ∑ i, κ i * (∑ a : Fin 3, ∑ b : Fin 3, g a b p * starRingEnd ℂ (X i a b p - Y i a b p)).re := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i, p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖X i a b p - Y i a b p‖ ^ 2
      = p.1 * ∑ i, ∑ a : Fin 3, ∑ b : Fin 3, ‖X i a b p - Y i a b p‖ ^ 2 := (Finset.mul_sum _ _ _).symm
  rw [e2, e3]
  have h2 := mul_le_mul_of_nonneg_left hy hp
  nlinarith [h2]

theorem surr_ae_eq_halfPlane {T : Set (ℝ × ℝ)} (hT : T ⊆ Set.Ici 0 ×ˢ Set.Ici 0) :
    volume.restrict T = volume.restrict (T ∩ halfPlane) := by
  refine Measure.restrict_congr_set ?_
  have h0 : volume (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) ∪ (Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ)) = 0 := by
    refine measure_union_null ?_ ?_
    · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
    · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
  refine ae_eq_set.2 ⟨measure_mono_null (fun p hp => ?_) h0, ?_⟩
  · obtain ⟨hpT, hpH⟩ := hp
    have h1 := (hT hpT).1
    have h2 := (hT hpT).2
    simp only [Set.mem_Ici] at h1 h2
    by_cases ha : p.1 = 0
    · exact Or.inl ⟨ha, Set.mem_univ _⟩
    · refine Or.inr ⟨Set.mem_univ _, ?_⟩
      by_contra hb
      exact hpH ⟨hpT, lt_of_le_of_ne h1 (Ne.symm ha), lt_of_le_of_ne h2 (Ne.symm hb)⟩
  · rw [Set.sdiff_eq_empty.2 Set.inter_subset_left, measure_empty]

theorem surr_sqw_gradAt (hH : HalfPlaneReductionHolds) {B : ℝ → Space → (Space →L[ℝ] Space)}
    (hBm : AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2) volume) (hBp : IsTimePeriodic B)
    (hBf : periodLIntegral (fun σ y => matSq (B σ y)) < ⊤) (hBF : FlipModes B) (m : ℕ) (ι : ℤ × ℤ)
    {T : Set (ℝ × ℝ)} (hT : T ⊆ Set.Ici 0 ×ˢ Set.Ici 0) (hTm : MeasurableSet T) (a b : Fin 3) :
    SqWeighted (volume.restrict T) (fun p => CellCalculus.gradAt m ι B a b p) := by
  have hHm : MeasurableSet halfPlane := measurableSet_Ioi.prod measurableSet_Ioi
  rw [surr_ae_eq_halfPlane hT]
  have hsub : volume.restrict (T ∩ halfPlane) ≤ volume.restrict halfPlane :=
    Measure.restrict_mono Set.inter_subset_right le_rfl
  have hA := aesm_labelGrad hBm m ι
  have hAe : AEStronglyMeasurable (fun p => CellCalculus.gradAt m ι B a b p) (volume.restrict (T ∩ halfPlane)) :=
    ((continuous_apply (a, b)).comp_aestronglyMeasurable hA).mono_measure hsub
  refine ⟨hAe, ?_⟩
  have hlin := halfPlane_modeNorm_lt_top hH hBm hBp hBf hBF (labelHarmonic m ι)
  have hN : AEStronglyMeasurable (fun p => cnormSq (labelGrad m ι B p) * p.1) (volume.restrict halfPlane) :=
    (aesm_cnormSq hA).mul measurable_fst.aestronglyMeasurable
  have hint : Integrable (fun p => cnormSq (labelGrad m ι B p) * p.1) (volume.restrict halfPlane) := by
    refine ⟨hN, ?_⟩
    have hpos : 0 ≤ᵐ[volume.restrict halfPlane] fun p => cnormSq (labelGrad m ι B p) * p.1 := by
      filter_upwards [ae_restrict_mem hHm] with p hp
      exact mul_nonneg (cnormSq_nonneg' _) (le_of_lt hp.1)
    rw [hasFiniteIntegral_iff_ofReal hpos]
    refine lt_of_le_of_lt (le_of_eq ?_) hlin
    refine lintegral_congr fun p => ?_
    rw [ENNReal.ofReal_mul (cnormSq_nonneg' _)]
    rfl
  refine (hint.mono_measure hsub).mono' ?_ ?_
  · exact measurable_fst.aestronglyMeasurable.mul (hAe.norm.pow 2)
  · filter_upwards [ae_restrict_mem (hTm.inter hHm)] with p hp
    have hp1 : 0 ≤ p.1 := le_of_lt hp.2.1
    rw [Real.norm_of_nonneg (mul_nonneg hp1 (sq_nonneg _)), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ hp1
    have hle := Finset.single_le_sum (f := fun j : Fin 3 × Fin 3 => ‖labelGrad m ι B p j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ (a, b))
    exact hle

theorem surr_sqw_bounded {T : Set (ℝ × ℝ)} (hTc : IsCompact T) (hTm : MeasurableSet T) {f : ℝ × ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict T)) {c : ℝ} (hc : ∀ p ∈ T, ‖f p‖ ≤ c) :
    SqWeighted (volume.restrict T) f := by
  obtain ⟨M, hM⟩ := hTc.exists_bound_of_continuousOn continuous_fst.continuousOn
  have : IsFiniteMeasure (volume.restrict T) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hTc.measure_lt_top⟩
  refine ⟨hf, Integrable.mono' (integrable_const (M * c ^ 2))
    (measurable_fst.aestronglyMeasurable.mul (hf.norm.pow 2)) ?_⟩
  filter_upwards [ae_restrict_mem hTm] with p hp
  rw [norm_mul, norm_pow, norm_norm]
  have h1 : ‖p.1‖ ≤ M := hM p hp
  have h2 : ‖f p‖ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hc p hp) 2
  exact mul_le_mul h1 h2 (by positivity) (le_trans (norm_nonneg _) h1)

def cellPairTerm {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (K : Fin D.mesh.count)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (X : Fin k ⊕ Fin k → ℤ × ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ)
    (gg : Fin k ⊕ Fin k) (ι : ℤ × ℤ) : ℝ :=
  (∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
    CellCalculus.gradAt D.azimuthOrder ι G a b p * (starRingEnd ℂ) (X gg ι p a b)).re

theorem surr_share_eq {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (K : Fin D.mesh.count)
    (L : Finset (ℤ × ℤ)) (X : Fin k ⊕ Fin k → ℤ × ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ) (κ ζ : Fin k → ℝ)
    (G : ℝ → Space → (Space →L[ℝ] Space)) :
    CellCalculus.pairShare D K L X κ ζ G
      = ∑ i, κ i * ∑ ι ∈ L, cellPairTerm D K G X (.inl i) ι
        + ∑ i, 2 * ζ i * ∑ ι ∈ L, cellPairTerm D K G X (.inr i) ι := by
  unfold CellCalculus.pairShare cellPairTerm
  rw [Fintype.sum_sum_type]
  rfl

theorem surr_cell {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (K : Fin D.mesh.count)
    (hT : (D.mesh.box K).rect ⊆ Set.Ici 0 ×ˢ Set.Ici 0) (hTm : MeasurableSet (D.mesh.box K).rect)
    (L Sl : Finset (ℤ × ℤ)) (hSl : Sl ⊆ L) (w : ℤ × ℤ → ℝ) (hw : ∀ ι ∈ Sl, 0 < w ι)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (Xs Xe : Fin k ⊕ Fin k → ℤ × ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ)
    (hpin : ∀ i ι, ∀ p ∈ (D.mesh.box K).rect, ∀ a b, Xs (.inr i) ι p a b = Xe (.inr i) ι p a b)
    (hoff : ∀ i, ∀ ι ∈ L, ι ∉ Sl → ∀ p ∈ (D.mesh.box K).rect, ∀ a b,
      Xs (.inl i) ι p a b = Xe (.inl i) ι p a b)
    (hg : ∀ ι ∈ Sl, ∀ a b, SqWeighted (volume.restrict (D.mesh.box K).rect)
      (fun p => CellCalculus.gradAt D.azimuthOrder ι G a b p))
    (hXs : ∀ i, ∀ ι ∈ Sl, ∀ a b, SqWeighted (volume.restrict (D.mesh.box K).rect) (fun p => Xs (.inl i) ι p a b))
    (hXe : ∀ i, ∀ ι ∈ Sl, ∀ a b, SqWeighted (volume.restrict (D.mesh.box K).rect) (fun p => Xe (.inl i) ι p a b))
    (κ ζ : Fin k → ℝ) :
    CellCalculus.pairShare D K L Xs κ ζ G
      ≤ CellCalculus.pairShare D K L Xe κ ζ G + CellCalculus.pairStrainSlack D K Sl w G
        + (∑ i, κ i ^ 2) * ∑ ι ∈ Sl, (4 * w ι)⁻¹ * ∑ i, ∫ p in (D.mesh.box K).rect,
            p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖Xs (.inl i) ι p a b - Xe (.inl i) ι p a b‖ ^ 2 := by
  have hρ : ∀ᵐ p ∂(volume.restrict (D.mesh.box K).rect), 0 ≤ p.1 := by
    filter_upwards [ae_restrict_mem hTm] with p hp
    exact (hT hp).1
  rw [surr_share_eq, surr_share_eq]
  have hP : ∀ i ι, cellPairTerm D K G Xs (.inr i) ι = cellPairTerm D K G Xe (.inr i) ι := by
    intro i ι
    unfold cellPairTerm
    congr 1
    refine setIntegral_congr_fun hTm fun p hp => ?_
    simp only [hpin i ι p hp]
  have hO : ∀ i, ∀ ι ∈ L, ι ∉ Sl → cellPairTerm D K G Xs (.inl i) ι = cellPairTerm D K G Xe (.inl i) ι := by
    intro i ι hι hn
    unfold cellPairTerm
    congr 1
    refine setIntegral_congr_fun hTm fun p hp => ?_
    simp only [hoff i ι hι hn p hp]
  have hsplit : ∀ i, ∑ ι ∈ L, cellPairTerm D K G Xs (.inl i) ι
      = ∑ ι ∈ L, cellPairTerm D K G Xe (.inl i) ι
        + ∑ ι ∈ Sl, (cellPairTerm D K G Xs (.inl i) ι - cellPairTerm D K G Xe (.inl i) ι) := by
    intro i
    have h := Finset.sum_subset hSl (f := fun ι => cellPairTerm D K G Xs (.inl i) ι - cellPairTerm D K G Xe (.inl i) ι)
      (fun ι hι hn => by simp only [hO i ι hι hn, sub_self])
    rw [h, Finset.sum_sub_distrib]
    ring
  simp only [hP, hsplit, mul_add, Finset.sum_add_distrib]
  have hmain : ∑ i, κ i * ∑ ι ∈ Sl, (cellPairTerm D K G Xs (.inl i) ι - cellPairTerm D K G Xe (.inl i) ι)
      ≤ CellCalculus.pairStrainSlack D K Sl w G
        + (∑ i, κ i ^ 2) * ∑ ι ∈ Sl, (4 * w ι)⁻¹ * ∑ i, ∫ p in (D.mesh.box K).rect,
            p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖Xs (.inl i) ι p a b - Xe (.inl i) ι p a b‖ ^ 2 := by
    have e : ∑ i, κ i * ∑ ι ∈ Sl, (cellPairTerm D K G Xs (.inl i) ι - cellPairTerm D K G Xe (.inl i) ι)
        = ∑ ι ∈ Sl, (∑ i, κ i * cellPairTerm D K G Xs (.inl i) ι
          - ∑ i, κ i * cellPairTerm D K G Xe (.inl i) ι) := by
      calc _ = ∑ i, ∑ ι ∈ Sl, κ i * (cellPairTerm D K G Xs (.inl i) ι - cellPairTerm D K G Xe (.inl i) ι) := by
            simp only [Finset.mul_sum]
        _ = ∑ ι ∈ Sl, ∑ i, κ i * (cellPairTerm D K G Xs (.inl i) ι - cellPairTerm D K G Xe (.inl i) ι) :=
            Finset.sum_comm
        _ = _ := by simp only [mul_sub, Finset.sum_sub_distrib]
    rw [e]
    unfold CellCalculus.pairStrainSlack
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ι hι => ?_
    have hb := surr_label_bound hρ (hw ι hι) (fun a b p => CellCalculus.gradAt D.azimuthOrder ι G a b p)
      (fun i a b p => Xs (.inl i) ι p a b) (fun i a b p => Xe (.inl i) ι p a b) (hg ι hι)
      (fun i => hXs i ι hι) (fun i => hXe i ι hι) κ
    beta_reduce at hb
    unfold cellPairTerm
    have e2 : (∑ i, κ i ^ 2) * ((4 * w ι)⁻¹ * ∑ i, ∫ p in (D.mesh.box K).rect,
            p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖Xs (.inl i) ι p a b - Xe (.inl i) ι p a b‖ ^ 2)
        = (4 * w ι)⁻¹ * (∑ i, κ i ^ 2) * ∑ i, ∫ p in (D.mesh.box K).rect,
            p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖Xs (.inl i) ι p a b - Xe (.inl i) ι p a b‖ ^ 2 := by ring
    rw [e2]
    linarith
  linarith

def exactPairProfiles {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) :
    Fin k ⊕ Fin k → ℤ × ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ :=
  fun gg ι p a b => CellCalculus.gradAt D.azimuthOrder ι
    (Sum.elim (fun i => gradField (D.cert.actuator i)) (fun i => D.cert.pin i) gg) a b p

end Internal

open _root_.Breakdown.CertCell.InstancePair.Internal Coercive Bridge
  Breakdown.CertCell.InstancePair.Internal.PairHalf in
theorem pairSharesFromSurrogateProfiles_of (hex : PairSharesFromExactProfiles) (hgm : ActuatorGradientModes)
    (hH : HalfPlaneReductionHolds) (hX : ModeFlipHolds) : PairSharesFromSurrogateProfiles := by
  intro k C nE nM D R S jmax ePair e hclass hact hfmt hsupp hpin hsur he q hq v G H g hp κ ζ
  have hbox := hpin.mesh_valid.box_valid
  have hq0 : ∀ K, (D.mesh.box K).rect ⊆ Set.Ici 0 ×ˢ Set.Ici 0 := fun K p hp' =>
    ⟨le_trans (hbox K).r_order.1 hp'.1.1, le_trans (hbox K).z_order.1 hp'.2.1⟩
  have hcm : ∀ K, MeasurableSet (D.mesh.box K).rect := fun K => measurableSet_Icc.prod measurableSet_Icc
  have hcc : ∀ K, IsCompact (D.mesh.box K).rect := fun K => isCompact_Icc.prod isCompact_Icc
  let R' : CellCalculus.CellCalculusEntry D := { R with pairProfile := fun _ => exactPairProfiles D }
  have hrec : IsPairEntry D R' S :=
    ⟨hsur.actuator_labels, hsur.pin_labels, fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩
  have hexact : ∑ K, CellCalculus.pairShare D K R.pairLabels (exactPairProfiles D) κ ζ G
      ≤ (∑ i, κ i * multiplierRight (D.pieces q) v G H (D.cert.actuator i)
          + 2 * ∑ i, ζ i * pinValue (D.cert.pin i) G) / (4 * Real.pi) + 0 * ∑ i, κ i ^ 2 :=
    hex D R' S jmax 0 hclass hact hfmt hsupp hpin hrec le_rfl q hq v G H g hp κ ζ
  have hGF : FlipModes G := flipModes_of_perturbation hX hp hclass.flip
  have hAct : ∀ i, FlipModes (gradField (D.cert.actuator i)) ∧
      PairInput D.azimuthOrder R.pairLabels (fun K => (D.mesh.box K).rect) (gradField (D.cert.actuator i)) :=
    fun i => by
      have hin := actuator_input hgm D R' S hclass hfmt hsupp hrec i
      exact ⟨flipModes_of_ae hin.flip, hin⟩
  have hk : 0 ≤ ∑ i, κ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcell : ∀ K, CellCalculus.pairShare D K R.pairLabels (R.pairProfile K) κ ζ G
      ≤ CellCalculus.pairShare D K R.pairLabels (exactPairProfiles D) κ ζ G
        + CellCalculus.pairStrainSlack D K (R.pairSlackLabels K) (R.pairSlackWeight K) G
        + (∑ i, κ i ^ 2) * ePair K := by
    intro K
    have h := surr_cell D K (hq0 K) (hcm K) R.pairLabels (R.pairSlackLabels K) (hsur.slack_in_labels K)
      (R.pairSlackWeight K) (hsur.slack_weight_pos K) G (R.pairProfile K) (exactPairProfiles D)
      (fun i ι p hp' a b => hsur.pin_profile K i ι p hp' a b)
      (fun i ι hι hn p hp' a b => hsur.exact_off_slack K i ι hι hn p hp' a b)
      (fun ι _ a b => surr_sqw_gradAt hH hp.measurable_gradient hp.periodic_gradient hp.gradient_finite hGF
        D.azimuthOrder ι (hq0 K) (hcm K) a b)
      (fun i ι _ a b => by
        obtain ⟨hm, c, hc⟩ := hsur.profile_regular K (.inl i) ι a b
        exact surr_sqw_bounded (hcc K) (hcm K) hm hc)
      (fun i ι _ a b => surr_sqw_gradAt hH (hAct i).2.meas (hAct i).2.periodic (hAct i).2.finite (hAct i).1
        D.azimuthOrder ι (hq0 K) (hcm K) a b)
      κ ζ
    have herr : ∑ ι ∈ R.pairSlackLabels K, (4 * R.pairSlackWeight K ι)⁻¹ * ∑ i,
        ∫ p in (D.mesh.box K).rect, p.1 * ∑ a : Fin 3, ∑ b : Fin 3,
          ‖R.pairProfile K (.inl i) ι p a b - exactPairProfiles D (.inl i) ι p a b‖ ^ 2 ≤ ePair K :=
      hsur.surrogate_error K
    have := mul_le_mul_of_nonneg_left herr hk
    linarith
  have hsum := Finset.sum_le_sum fun K (_ : K ∈ Finset.univ) => hcell K
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hE : (∑ i, κ i ^ 2) * ∑ K, ePair K ≤ (∑ i, κ i ^ 2) * e := mul_le_mul_of_nonneg_left he hk
  nlinarith [hsum, hexact, hE]

theorem pairSharesFromSurrogateProfiles (hreg : CellMatFieldRegular) (hgm : ActuatorGradientModes)
    (hhalf : HalfPlanePairing) (hibp : ActuatorPairingByParts) : PairSharesFromSurrogateProfiles :=
  pairSharesFromSurrogateProfiles_of (pairSharesFromExactProfiles hreg hgm hhalf hibp) hgm
    Bridge.halfPlaneReduction Bridge.modeFlip

end InstancePair

end CertCell

end Breakdown
