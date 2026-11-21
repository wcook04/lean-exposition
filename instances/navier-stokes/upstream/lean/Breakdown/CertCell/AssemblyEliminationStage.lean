import Breakdown.CertCell.AssemblyStatements

open MeasureTheory Matrix
open scoped ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

namespace TurnedBand

theorem sum_twelve_split {M : Type*} [AddCommMonoid M] (f : Fin 12 → M) :
    ∑ j, f j = ∑ j : Fin 9, f (gradSlot j) + ∑ b : Fin 3, f ⟨9 + b.val, by omega⟩ :=
  Fin.sum_univ_add (a := 9) (b := 3) f

theorem sum_nine_split {M : Type*} [AddCommMonoid M] (f : Fin 9 → M) :
    ∑ j, f j = ∑ a : Fin 3, (f ⟨3 * a.val, by omega⟩ + f ⟨3 * a.val + 1, by omega⟩ + f ⟨3 * a.val + 2, by omega⟩) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Fin.val_zero, Fin.val_succ, Fin.succ_zero_eq_one, Fin.val_one]
  abel_nf
  rfl

theorem turnMatrix_det (n : ℤ) : (turnMatrix n).det = (n : ℂ) * Complex.I * (1 - (n : ℂ) ^ 2) := by
  rw [Matrix.det_fin_three]
  simp [turnMatrix]
  ring_nf
  rw [show Complex.I ^ 3 = -Complex.I by rw [pow_succ, Complex.I_sq]; ring]
  ring

theorem turnMatrix_det_isUnit {n : ℤ} (h0 : n ≠ 0) (h1 : n ^ 2 ≠ 1) : IsUnit (turnMatrix n).det := by
  rw [turnMatrix_det, isUnit_iff_ne_zero]
  have hn : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr h0
  have hq : (1 - (n : ℂ) ^ 2) ≠ 0 := by
    have e : (1 - (n : ℂ) ^ 2) = ((1 - n ^ 2 : ℤ) : ℂ) := by push_cast; ring
    rw [e, Int.cast_ne_zero]
    exact sub_ne_zero.mpr (Ne.symm h1)
  exact mul_ne_zero (mul_ne_zero hn Complex.I_ne_zero) hq

theorem turned_velocity {n : ℤ} (h0 : n ≠ 0) (h1 : n ^ 2 ≠ 1) (r : ℝ) (σ : Fin 12 → ℂ)
    (hσ : ∀ a : Fin 3, (r : ℂ) * σ ⟨3 * a.val + 1, by omega⟩
      = ∑ b : Fin 3, turnMatrix n a b * σ ⟨9 + b.val, by omega⟩) (b : Fin 3) :
    σ ⟨9 + b.val, by omega⟩ = ∑ a : Fin 3, (turnMatrix n)⁻¹ b a * ((r : ℂ) * σ ⟨3 * a.val + 1, by omega⟩) := by
  have hN : turnMatrix n *ᵥ (fun b : Fin 3 => σ ⟨9 + b.val, by omega⟩)
      = fun a : Fin 3 => (r : ℂ) * σ ⟨3 * a.val + 1, by omega⟩ := by
    funext a
    rw [hσ a]
    rfl
  have hM : (turnMatrix n)⁻¹ *ᵥ (fun a : Fin 3 => (r : ℂ) * σ ⟨3 * a.val + 1, by omega⟩)
      = fun b : Fin 3 => σ ⟨9 + b.val, by omega⟩ := by
    rw [← hN, mulVec_mulVec, nonsing_inv_mul _ (turnMatrix_det_isUnit h0 h1), one_mulVec]
  exact (congrFun hM b).symm

theorem turned_extra (n : ℤ) (p : ℝ × ℝ) (U σ : Fin 12 → ℂ) :
    ∑ j : Fin 9, (starRingEnd ℂ) (turnedVec n p U j) * σ (gradSlot j)
      = ∑ j : Fin 9, (starRingEnd ℂ) (U (gradSlot j)) * σ (gradSlot j)
        + ∑ a : Fin 3, (starRingEnd ℂ) ((p.1 : ℂ) * ∑ b : Fin 3,
            (starRingEnd ℂ) ((turnMatrix n)⁻¹ b a) * U ⟨9 + b.val, by omega⟩) * σ ⟨3 * a.val + 1, by omega⟩ := by
  unfold turnedVec
  simp only [map_add, add_mul, Finset.sum_add_distrib]
  congr 1
  rw [sum_nine_split]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e0 : ¬ ((⟨3 * a.val, by omega⟩ : Fin 9).val % 3 = 1) := by simp only []; omega
  have e1 : (⟨3 * a.val + 1, by omega⟩ : Fin 9).val % 3 = 1 := by simp only []; omega
  have e2 : ¬ ((⟨3 * a.val + 2, by omega⟩ : Fin 9).val % 3 = 1) := by simp only []; omega
  rw [if_neg e0, if_pos e1, if_neg e2]
  have ea : (⟨(3 * a.val + 1) / 3, by omega⟩ : Fin 3) = a := Fin.ext (by simp only []; omega)
  simp only [ea, map_zero, zero_mul, zero_add, add_zero]
  rfl

theorem turned_dot {n : ℤ} (h0 : n ≠ 0) (h1 : n ^ 2 ≠ 1) (p : ℝ × ℝ) (σ U : Fin 12 → ℂ)
    (hσ : ∀ a : Fin 3, (p.1 : ℂ) * σ ⟨3 * a.val + 1, by omega⟩
      = ∑ b : Fin 3, turnMatrix n a b * σ ⟨9 + b.val, by omega⟩) :
    ∑ j, (starRingEnd ℂ) (U j) * σ j
      = ∑ j : Fin 9, (starRingEnd ℂ) (turnedVec n p U j) * σ (gradSlot j) := by
  rw [turned_extra, sum_twelve_split]
  congr 1
  simp only [turned_velocity h0 h1 p.1 σ hσ, map_mul, map_sum, Complex.conj_conj, Complex.conj_ofReal,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem turned_dot_right {n : ℤ} (h0 : n ≠ 0) (h1 : n ^ 2 ≠ 1) (p : ℝ × ℝ) (σ U : Fin 12 → ℂ)
    (hσ : ∀ a : Fin 3, (p.1 : ℂ) * σ ⟨3 * a.val + 1, by omega⟩
      = ∑ b : Fin 3, turnMatrix n a b * σ ⟨9 + b.val, by omega⟩) :
    ∑ j, σ j * (starRingEnd ℂ) (U j)
      = ∑ j : Fin 9, σ (gradSlot j) * (starRingEnd ℂ) (turnedVec n p U j) := by
  have h := turned_dot h0 h1 p σ U hσ
  simp only [mul_comm (σ _)] at h ⊢
  exact h

theorem weight_split_le {w : Fin 12 → ℝ} (hw : ∀ b : Fin 3, 0 ≤ w ⟨9 + b.val, by omega⟩) (σ : Fin 12 → ℂ) :
    ∑ j : Fin 9, w (gradSlot j) * ‖σ (gradSlot j)‖ ^ 2 ≤ ∑ j, w j * ‖σ j‖ ^ 2 := by
  rw [sum_twelve_split (fun j => w j * ‖σ j‖ ^ 2)]
  have : 0 ≤ ∑ b : Fin 3, w ⟨9 + b.val, by omega⟩ * ‖σ ⟨9 + b.val, by omega⟩‖ ^ 2 :=
    Finset.sum_nonneg fun b _ => mul_nonneg (hw b) (sq_nonneg _)
  linarith

end TurnedBand

namespace TurnedBand

namespace Internal

theorem cross_le {n : Type*} [Fintype n] [DecidableEq n] {W : Matrix n n ℂ}
    (hW : W.PosDef) (b y : n → ℂ) :
    2 * (star y ⬝ᵥ b).re - (star y ⬝ᵥ (W *ᵥ y)).re ≤ Coupling.inverseWeightedSq W b := by
  have hu : IsUnit W.det := (isUnit_iff_isUnit_det W).mp hW.isUnit
  set u := W⁻¹ *ᵥ b with hudef
  have hWu : W *ᵥ u = b := by rw [hudef, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have h0 : 0 ≤ (star (y - u) ⬝ᵥ (W *ᵥ (y - u))).re :=
    (Complex.le_def.mp (hW.posSemidef.dotProduct_mulVec_nonneg (y - u))).1
  have hsw : (star u ⬝ᵥ (W *ᵥ y)).re = (star y ⬝ᵥ b).re := by
    rw [star_dotProduct u (W *ᵥ y), star_mulVec, hW.isHermitian.eq, ← dotProduct_mulVec, hWu]
    exact Complex.conj_re _
  have hq : Coupling.inverseWeightedSq W b = (star u ⬝ᵥ b).re := by
    unfold Coupling.inverseWeightedSq Coupling.quadForm
    rw [← hudef, star_dotProduct b u]
    exact Complex.conj_re _
  rw [star_sub, mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hWu] at h0
  simp only [Complex.sub_re] at h0
  rw [hq]
  linarith

theorem le_exists {n : Type*} [Fintype n] [DecidableEq n] (F : Matrix n n ℂ) (a : n → ℂ) :
    ∃ y : n → ℂ, Coupling.inverseWeightedSq F a ≤ 2 * (star y ⬝ᵥ a).re - (star y ⬝ᵥ (F *ᵥ y)).re := by
  by_cases hu : IsUnit F.det
  · refine ⟨F⁻¹ *ᵥ a, le_of_eq ?_⟩
    have hFy : F *ᵥ (F⁻¹ *ᵥ a) = a := by rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
    rw [hFy]
    have hs : (star a ⬝ᵥ (F⁻¹ *ᵥ a)).re = (star (F⁻¹ *ᵥ a) ⬝ᵥ a).re := by
      rw [star_dotProduct a (F⁻¹ *ᵥ a)]
      exact Complex.conj_re _
    unfold Coupling.inverseWeightedSq Coupling.quadForm
    rw [hs]
    ring
  · refine ⟨0, ?_⟩
    unfold Coupling.inverseWeightedSq Coupling.quadForm
    rw [nonsing_inv_apply_not_isUnit F hu]
    simp

structure IsHalfBox (S : Set (ℝ × ℝ)) : Prop where
  meas : MeasurableSet S
  finite : volume S < ⊤
  nonneg : ∀ p ∈ S, 0 ≤ p.1
  bounded : ∃ c : ℝ, ∀ p ∈ S, p.1 ≤ c

def Wsq (S : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℂ) : Prop :=
  AEStronglyMeasurable f (volume.restrict S) ∧ IntegrableOn (fun p => p.1 * ‖f p‖ ^ 2) S

variable {S : Set (ℝ × ℝ)}

theorem wsq_of_bounded (hS : IsHalfBox S) {f : ℝ × ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict S)) (hb : ∃ c : ℝ, ∀ p ∈ S, ‖f p‖ ≤ c) : Wsq S f := by
  refine ⟨hf, ?_⟩
  obtain ⟨c, hc⟩ := hb
  obtain ⟨R, hR⟩ := hS.bounded
  have : IsFiniteMeasure (volume.restrict S) := ⟨by rw [Measure.restrict_apply_univ]; exact hS.finite⟩
  refine Integrable.of_bound (continuous_fst.aestronglyMeasurable.mul (hf.norm.pow 2)) (R * c ^ 2) ?_
  refine (ae_restrict_iff' hS.meas).2 (Filter.Eventually.of_forall fun p hp => ?_)
  have h0 := hS.nonneg p hp
  have h1 : ‖f p‖ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hc p hp) 2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (sq_nonneg _))]
  exact mul_le_mul (hR p hp) h1 (sq_nonneg _) (h0.trans (hR p hp))

theorem integrable_mul (hS : IsHalfBox S) {f g : ℝ × ℝ → ℂ} (hf : Wsq S f) (hg : Wsq S g) :
    IntegrableOn (fun p => (p.1 : ℂ) * (f p * g p)) S := by
  refine Integrable.mono' (hf.2.add hg.2)
    ((Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable.mul (hf.1.mul hg.1)) ?_
  refine (ae_restrict_iff' hS.meas).2 (Filter.Eventually.of_forall fun p hp => ?_)
  have h0 := hS.nonneg p hp
  simp only [Pi.add_apply]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  nlinarith [mul_nonneg h0 (sq_nonneg (‖f p‖ - ‖g p‖)), mul_nonneg h0 (mul_nonneg (norm_nonneg (f p)) (norm_nonneg (g p)))]

theorem wsq_add (hS : IsHalfBox S) {f g : ℝ × ℝ → ℂ} (hf : Wsq S f) (hg : Wsq S g) :
    Wsq S (fun p => f p + g p) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  refine Integrable.mono' ((hf.2.add hg.2).const_mul 2)
    (continuous_fst.aestronglyMeasurable.mul ((hf.1.add hg.1).norm.pow 2)) ?_
  refine (ae_restrict_iff' hS.meas).2 (Filter.Eventually.of_forall fun p hp => ?_)
  have h0 := hS.nonneg p hp
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (sq_nonneg _))]
  have h2 : ‖f p + g p‖ ^ 2 ≤ 2 * ‖f p‖ ^ 2 + 2 * ‖g p‖ ^ 2 := by
    nlinarith [sq_nonneg (‖f p‖ - ‖g p‖), norm_nonneg (f p + g p), norm_nonneg (f p), norm_nonneg (g p),
      norm_add_le (f p) (g p)]
  nlinarith [mul_le_mul_of_nonneg_left h2 h0]

theorem wsq_const_mul {f : ℝ × ℝ → ℂ} (hf : Wsq S f) (c : ℂ) : Wsq S (fun p => c * f p) := by
  refine ⟨aestronglyMeasurable_const.mul hf.1, ?_⟩
  refine (hf.2.const_mul (‖c‖ ^ 2)).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [norm_mul]
  ring

theorem wsq_fst_mul (hS : IsHalfBox S) {f : ℝ × ℝ → ℂ} (hf : Wsq S f) : Wsq S (fun p => (p.1 : ℂ) * f p) := by
  obtain ⟨R, hR⟩ := hS.bounded
  refine ⟨(Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable.mul hf.1, ?_⟩
  refine Integrable.mono' (hf.2.const_mul (R ^ 2))
    (continuous_fst.aestronglyMeasurable.mul
      (((Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable.mul hf.1).norm.pow 2)) ?_
  refine (ae_restrict_iff' hS.meas).2 (Filter.Eventually.of_forall fun p hp => ?_)
  have h0 := hS.nonneg p hp
  have h1 : p.1 ≤ R := hR p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (sq_nonneg _)), norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg h0]
  have h2 : p.1 ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : 0 ≤ p.1 * ‖f p‖ ^ 2 := mul_nonneg h0 (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right h2 h3]

theorem wsq_conj {f : ℝ × ℝ → ℂ} (hf : Wsq S f) : Wsq S (fun p => (starRingEnd ℂ) (f p)) := by
  refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable hf.1, ?_⟩
  refine hf.2.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Complex.norm_conj]

theorem wsq_zero : Wsq S (fun _ => 0) := ⟨aestronglyMeasurable_const, by simp⟩

theorem wsq_sum (hS : IsHalfBox S) {α : Type*} (s : Finset α) {f : α → ℝ × ℝ → ℂ}
    (hf : ∀ i ∈ s, Wsq S (f i)) : Wsq S (fun p => ∑ i ∈ s, f i p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (wsq_zero (S := S))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact wsq_add hS (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem wsq_congr {f g : ℝ × ℝ → ℂ} (hf : Wsq S f) (h : ∀ p, f p = g p) : Wsq S g := by
  have e : f = g := funext h
  rw [← e]
  exact hf

theorem dot_sum_integral {n α : Type*} [Fintype n] (T : Finset α) (y : n → ℂ) (h : n → α → ℝ × ℝ → ℂ)
    (hh : ∀ i, ∀ ι ∈ T, IntegrableOn (h i ι) S) :
    star y ⬝ᵥ (fun i => ∑ ι ∈ T, ∫ p in S, h i ι p) = ∑ ι ∈ T, ∫ p in S, ∑ i, star (y i) * h i ι p := by
  simp only [dotProduct, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ι hι => ?_
  rw [integral_finsetSum _ (fun i _ => (hh i ι hι).const_mul _)]
  simp only [integral_const_mul]

theorem sum_integral_mul {n α : Type*} [Fintype n] (T : Finset α) (c : n → ℂ) (g : n → α → ℝ × ℝ → ℂ)
    (hg : ∀ i, ∀ ι ∈ T, IntegrableOn (g i ι) S) :
    ∑ i, (∑ ι ∈ T, ∫ p in S, g i ι p) * c i = ∑ ι ∈ T, ∫ p in S, ∑ i, g i ι p * c i := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ι hι => ?_
  rw [integral_finsetSum _ (fun i _ => (hg i ι hι).mul_const _)]
  simp only [integral_mul_const]

theorem re_sum_integral {α : Type*} (T : Finset α) (H : α → ℝ × ℝ → ℂ) (hH : ∀ ι ∈ T, IntegrableOn (H ι) S) :
    (∑ ι ∈ T, ∫ p in S, H ι p).re = ∑ ι ∈ T, ∫ p in S, (H ι p).re := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun ι hι => ?_
  exact (integral_re (hH ι hι)).symm

theorem integral_combine {f₁ f₂ f₃ f₄ f₅ f₆ f₇ : ℝ × ℝ → ℝ} (h₁ : IntegrableOn f₁ S) (h₂ : IntegrableOn f₂ S)
    (h₃ : IntegrableOn f₃ S) (h₄ : IntegrableOn f₄ S) (h₅ : IntegrableOn f₅ S) (h₆ : IntegrableOn f₆ S)
    (h₇ : IntegrableOn f₇ S) (s t u : ℝ) :
    ∫ p in S, (f₁ p + f₂ p + f₃ p + s * f₄ p + t * f₅ p + u * f₆ p - f₇ p)
      = (∫ p in S, f₁ p) + (∫ p in S, f₂ p) + (∫ p in S, f₃ p) + s * (∫ p in S, f₄ p)
        + t * (∫ p in S, f₅ p) + u * (∫ p in S, f₆ p) - ∫ p in S, f₇ p := by
  rw [integral_sub, integral_add, integral_add, integral_add, integral_add, integral_add,
    integral_const_mul, integral_const_mul, integral_const_mul]
  · exact h₁
  · exact h₂
  · exact h₁.add h₂
  · exact h₃
  · exact (h₁.add h₂).add h₃
  · exact h₄.const_mul s
  · exact ((h₁.add h₂).add h₃).add (h₄.const_mul s)
  · exact h₅.const_mul t
  · exact (((h₁.add h₂).add h₃).add (h₄.const_mul s)).add (h₅.const_mul t)
  · exact h₆.const_mul u
  · exact ((((h₁.add h₂).add h₃).add (h₄.const_mul s)).add (h₅.const_mul t)).add (h₆.const_mul u)
  · exact h₇

theorem square_completion {t : ℝ} (ht : 0 < t) (u₁ u₂ v₁ v₂ : ℝ) :
    0 ≤ t * (u₁ ^ 2 + u₂ ^ 2) + 2 * (v₁ * u₁ + v₂ * u₂) + (v₁ ^ 2 + v₂ ^ 2) / t := by
  have e : t * (u₁ ^ 2 + u₂ ^ 2) + 2 * (v₁ * u₁ + v₂ * u₂) + (v₁ ^ 2 + v₂ ^ 2) / t
      = ((t * u₁ + v₁) ^ 2 + (t * u₂ + v₂) ^ 2) / t := by
    field_simp
    ring
  rw [e]
  positivity

theorem point_nonneg {w θ : ℝ} (hw : 0 < w) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (σ μ s z : ℂ)
    (hE : θ = 0 → s = (w : ℂ) * μ) :
    0 ≤ w * ‖σ‖ ^ 2 + 2 * ((starRingEnd ℂ) s * σ).re + 2 * (σ * (starRingEnd ℂ) z).re
      + 2 * (μ * (starRingEnd ℂ) z).re + (1 - θ)⁻¹ * (‖z‖ ^ 2 / w)
      - (w * ‖μ‖ ^ 2 - 2 * ((starRingEnd ℂ) μ * s).re - ‖s - (w : ℂ) * μ‖ ^ 2 / (w * θ)) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hB := square_completion (mul_pos h1θ hw) (σ.re + μ.re) (σ.im + μ.im) z.re z.im
  rcases hθ.lt_or_eq with hθp | hθ0
  · have hA := square_completion (mul_pos hθp hw) (σ.re + μ.re) (σ.im + μ.im)
      (s.re - w * μ.re) (s.im - w * μ.im)
    refine (add_nonneg hA hB).trans_eq ?_
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring
  · subst hθ0
    have hs := hE rfl
    subst hs
    refine hB.trans_eq ?_
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring

theorem integrable_sum (hS : IsHalfBox S) {J : Type*} [Fintype J] {f g : J → ℝ × ℝ → ℂ}
    (hf : ∀ j, Wsq S (f j)) (hg : ∀ j, Wsq S (g j)) :
    IntegrableOn (fun p => (p.1 : ℂ) * ∑ j, f j p * g j p) S := by
  have h := integrable_finsetSum Finset.univ (fun j _ => integrable_mul hS (hf j) (hg j))
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Finset.mul_sum]

theorem integrable_sum_div (hS : IsHalfBox S) {J : Type*} [Fintype J] {f g : J → ℝ × ℝ → ℂ} (c : J → ℂ)
    (hf : ∀ j, Wsq S (f j)) (hg : ∀ j, Wsq S (g j)) :
    IntegrableOn (fun p => (p.1 : ℂ) * ∑ j, f j p * g j p / c j) S := by
  have h := integrable_sum hS hf (fun j => wsq_const_mul (hg j) (c j)⁻¹)
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [div_eq_mul_inv]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem integrableOn_scaled_re {f : ℝ × ℝ → ℝ} {F : ℝ × ℝ → ℂ} (hF : IntegrableOn F S) (c : ℝ)
    (h : ∀ p, f p = c * (F p).re) : IntegrableOn f S := by
  have e : f = fun p => c * RCLike.re (F p) := funext fun p => by rw [h p]; rfl
  rw [e]
  exact hF.re.const_mul c

theorem rect_halfBox {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (hm : IsCellMesh D.mesh)
    (K : Fin D.mesh.count) : IsHalfBox (D.mesh.box K).rect where
  meas := measurableSet_Icc.prod measurableSet_Icc
  finite := (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  nonneg := fun _ hp => (hm.box_valid K).r_order.1.trans hp.1.1
  bounded := ⟨(D.mesh.box K).r₂, fun _ hp => hp.1.2⟩

theorem wsq_turned (hS : IsHalfBox S) (n : ℤ) {U : ℝ × ℝ → Fin 12 → ℂ} (hU : ∀ j, Wsq S (fun p => U p j))
    (j : Fin 9) : Wsq S (fun p => turnedVec n p (U p) j) := by
  unfold turnedVec
  by_cases h : j.val % 3 = 1
  · simp only [h, if_true]
    exact wsq_add hS (hU _) (wsq_fst_mul hS (wsq_sum hS Finset.univ fun b _ => wsq_const_mul (hU _) _))
  · simp only [h, if_false, add_zero]
    exact hU _

end Internal

end TurnedBand

namespace TurnedBand

open Breakdown.CertCell.Assembly.TurnedBand.Internal

theorem band_bound {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)
    (A : AssemblyEntry D R) (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop)
    (hc : EliminationConditions D R A S) (K : Fin D.mesh.count) (x : CellVars D R K → ℂ) (hx : S K x)
    (σ : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) (hσ : BandSquareIntegrable D K σ) (ht : IsBandTurned D K σ)
    (y : Fin (A.blocks K).rowCount → ℂ) :
    bandEliminated D K (A.blocks K) x
      ≤ bandQuad D K (A.blocks K).bandWeight σ + bandLinear D K (A.blocks K).potentialSource x σ
        + bandLinear D K (A.blocks K).pairingSource x σ
        + 2 * (star y ⬝ᵥ fun i => ∑ ι ∈ D.mesh.band K, ∫ p in (D.mesh.box K).rect,
            (p.1 : ℂ) * ∑ j, σ ι p j * (starRingEnd ℂ) ((A.blocks K).rowBand i ι p j)).re
        + 2 * (star y ⬝ᵥ fun i => ∑ ι ∈ D.mesh.band K, ∫ p in (D.mesh.box K).rect,
            (p.1 : ℂ) * ∑ j : Fin 9, linearField ((A.blocks K).bandMap ι) x p (gradSlot j)
              * (starRingEnd ℂ) (turnedRowBand D (A.blocks K) i ι p j)).re
        + (1 - (A.blocks K).bandSlack)⁻¹ * (star y ⬝ᵥ (bandGram D K (A.blocks K) *ᵥ y)).re := by
  classical
  set T := D.mesh.band K with hTdef
  set Sx := (D.mesh.box K).rect with hSdef
  have hS : IsHalfBox Sx := rect_halfBox D hc.mesh_valid K
  have hfb := hc.fields_bounded K
  have hσg : ∀ ι ∈ T, ∀ j, Wsq Sx (fun p => σ ι p j) := by
    intro ι hι j
    refine ⟨(hσ ι hι).1 j, ?_⟩
    refine Integrable.mono' (hσ ι hι).2
      (continuous_fst.aestronglyMeasurable.mul (((hσ ι hι).1 j).norm.pow 2)) ?_
    refine (ae_restrict_iff' hS.meas).2 (Filter.Eventually.of_forall fun p hp => ?_)
    have h0 := hS.nonneg p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun j => ‖σ ι p j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ j)) h0
  have hlin : ∀ (F : CellVars D R K → ℝ × ℝ → Fin 12 → ℂ) (j : Fin 12),
      (∀ d, IsBoundedOnCell D K (fun p => F d p j)) → Wsq Sx (fun p => linearField F x p j) :=
    fun F j hF => wsq_sum hS Finset.univ
      (fun d _ => wsq_const_mul (wsq_of_bounded hS (hF d).1 (hF d).2) (x d))
  have hBg : ∀ ι ∈ T, ∀ i j, Wsq Sx (fun p => (A.blocks K).rowBand i ι p j) := fun ι hι i j =>
    wsq_of_bounded hS ((hfb ι hι j).2.2.2 i).1 ((hfb ι hι j).2.2.2 i).2
  have hμg : ∀ ι ∈ T, ∀ j, Wsq Sx (fun p => linearField ((A.blocks K).bandMap ι) x p j) :=
    fun ι hι j => hlin _ j (hfb ι hι j).2.2.1
  have hPg : ∀ ι ∈ T, ∀ j, Wsq Sx (fun p => linearField ((A.blocks K).potentialSource ι) x p j) :=
    fun ι hι j => hlin _ j (hfb ι hι j).1
  have hQg : ∀ ι ∈ T, ∀ j, Wsq Sx (fun p => linearField ((A.blocks K).pairingSource ι) x p j) :=
    fun ι hι j => hlin _ j (hfb ι hι j).2.1
  have hsg : ∀ ι ∈ T, ∀ j, Wsq Sx (fun p => sourceSum (A.blocks K) ι x p j) :=
    fun ι hι j => wsq_add hS (hPg ι hι j) (hQg ι hι j)
  have hsg' : ∀ ι ∈ T, ∀ j : Fin 9, Wsq Sx (fun p => turnedSource D (A.blocks K) ι x p j) :=
    fun ι hι j => wsq_turned hS _ (U := fun p => sourceSum (A.blocks K) ι x p) (hsg ι hι) j
  have hBg' : ∀ ι ∈ T, ∀ i (j : Fin 9), Wsq Sx (fun p => turnedRowBand D (A.blocks K) i ι p j) :=
    fun ι hι i j => wsq_turned hS _ (U := fun p => (A.blocks K).rowBand i ι p) (hBg ι hι i) j
  have hμ9 : ∀ ι ∈ T, ∀ j : Fin 9, Wsq Sx (fun p => linearField ((A.blocks K).bandMap ι) x p (gradSlot j)) :=
    fun ι hι j => hμg ι hι _
  have hE9 : ∀ ι ∈ T, ∀ j : Fin 9, Wsq Sx (fun p => turnedSource D (A.blocks K) ι x p j
      - ((A.blocks K).bandWeight ι (gradSlot j) : ℂ) * linearField ((A.blocks K).bandMap ι) x p (gradSlot j)) :=
    fun ι hι j => wsq_congr
      (wsq_add hS (hsg' ι hι j) (wsq_const_mul (hμ9 ι hι j) (-((A.blocks K).bandWeight ι (gradSlot j) : ℂ))))
      (fun p => by ring)
  have hI1 : ∀ i, ∀ ι ∈ T, IntegrableOn
      (fun p => (p.1 : ℂ) * ∑ j, σ ι p j * (starRingEnd ℂ) ((A.blocks K).rowBand i ι p j)) Sx :=
    fun i ι hι => integrable_sum hS (f := fun j p => σ ι p j) (hσg ι hι)
      (fun j => wsq_conj (hBg ι hι i j))
  have hI2 : ∀ i, ∀ ι ∈ T, IntegrableOn (fun p => (p.1 : ℂ) * ∑ j : Fin 9,
      linearField ((A.blocks K).bandMap ι) x p (gradSlot j) * (starRingEnd ℂ) (turnedRowBand D (A.blocks K) i ι p j)) Sx :=
    fun i ι hι => integrable_sum hS (f := fun j p => linearField ((A.blocks K).bandMap ι) x p (gradSlot j)) (hμ9 ι hι)
      (fun j => wsq_conj (hBg' ι hι i j))
  have hIG : ∀ i i', ∀ ι ∈ T, IntegrableOn (fun p => (p.1 : ℂ) * ∑ j : Fin 9,
      (starRingEnd ℂ) (turnedRowBand D (A.blocks K) i ι p j) * turnedRowBand D (A.blocks K) i' ι p j
        / ((A.blocks K).bandWeight ι (gradSlot j) : ℂ)) Sx :=
    fun i i' ι hι => integrable_sum_div hS (fun j => ((A.blocks K).bandWeight ι (gradSlot j) : ℂ))
      (f := fun j p => (starRingEnd ℂ) (turnedRowBand D (A.blocks K) i ι p j)) (g := fun j p => turnedRowBand D (A.blocks K) i' ι p j)
      (fun j => wsq_conj (hBg' ι hι i j)) (hBg' ι hι i')
  have hX1 := dot_sum_integral T y _ hI1
  have hX2 := dot_sum_integral T y _ hI2
  have hGy : bandGram D K (A.blocks K) *ᵥ y = fun i => ∑ ι ∈ T, ∫ p in Sx, ∑ i', ((p.1 : ℂ) * ∑ j : Fin 9,
      (starRingEnd ℂ) (turnedRowBand D (A.blocks K) i ι p j) * turnedRowBand D (A.blocks K) i' ι p j
        / ((A.blocks K).bandWeight ι (gradSlot j) : ℂ)) * y i' := by
    funext i
    exact sum_integral_mul T y _ (fun i' ι hι => hIG i i' ι hι)
  have hIG' : ∀ i, ∀ ι ∈ T, IntegrableOn (fun p => ∑ i', ((p.1 : ℂ) * ∑ j : Fin 9,
      (starRingEnd ℂ) (turnedRowBand D (A.blocks K) i ι p j) * turnedRowBand D (A.blocks K) i' ι p j
        / ((A.blocks K).bandWeight ι (gradSlot j) : ℂ)) * y i') Sx :=
    fun i ι hι => integrable_finsetSum _ (fun i' _ => (hIG i i' ι hι).mul_const _)
  have hX3 : star y ⬝ᵥ (bandGram D K (A.blocks K) *ᵥ y) = ∑ ι ∈ T, ∫ p in Sx, ∑ i, star (y i) * ∑ i', ((p.1 : ℂ) * ∑ j : Fin 9,
      (starRingEnd ℂ) (turnedRowBand D (A.blocks K) i ι p j) * turnedRowBand D (A.blocks K) i' ι p j
        / ((A.blocks K).bandWeight ι (gradSlot j) : ℂ)) * y i' := by
    rw [hGy]
    exact dot_sum_integral T y _ hIG'
  have hH1 : ∀ ι ∈ T, IntegrableOn (fun p => ∑ i, star (y i)
      * ((p.1 : ℂ) * ∑ j, σ ι p j * (starRingEnd ℂ) ((A.blocks K).rowBand i ι p j))) Sx :=
    fun ι hι => integrable_finsetSum _ (fun i _ => (hI1 i ι hι).const_mul _)
  have hH2 : ∀ ι ∈ T, IntegrableOn (fun p => ∑ i, star (y i)
      * ((p.1 : ℂ) * ∑ j : Fin 9, linearField ((A.blocks K).bandMap ι) x p (gradSlot j)
        * (starRingEnd ℂ) (turnedRowBand D (A.blocks K) i ι p j))) Sx :=
    fun ι hι => integrable_finsetSum _ (fun i _ => (hI2 i ι hι).const_mul _)
  have hH3 : ∀ ι ∈ T, IntegrableOn (fun p => ∑ i, star (y i) * ∑ i', ((p.1 : ℂ) * ∑ j : Fin 9,
      (starRingEnd ℂ) (turnedRowBand D (A.blocks K) i ι p j) * turnedRowBand D (A.blocks K) i' ι p j
        / ((A.blocks K).bandWeight ι (gradSlot j) : ℂ)) * y i') Sx :=
    fun ι hι => integrable_finsetSum _ (fun i _ => (hIG' i ι hι).const_mul _)
  rw [hX1, hX2, hX3, re_sum_integral T _ hH1, re_sum_integral T _ hH2, re_sum_integral T _ hH3]
  have hper : ∀ ι ∈ T, (∫ p in Sx, p.1 * (∑ j : Fin 9, (A.blocks K).bandWeight ι (gradSlot j)
            * ‖linearField ((A.blocks K).bandMap ι) x p (gradSlot j)‖ ^ 2
          - 2 * (∑ j : Fin 9, (starRingEnd ℂ) (linearField ((A.blocks K).bandMap ι) x p (gradSlot j))
              * turnedSource D (A.blocks K) ι x p j).re
          - ∑ j : Fin 9, ‖turnedSource D (A.blocks K) ι x p j
              - ((A.blocks K).bandWeight ι (gradSlot j) : ℂ) * linearField ((A.blocks K).bandMap ι) x p (gradSlot j)‖ ^ 2
              / ((A.blocks K).bandWeight ι (gradSlot j) * (A.blocks K).bandSlack)))
      ≤ (∫ p in Sx, p.1 * ∑ j, (A.blocks K).bandWeight ι j * ‖σ ι p j‖ ^ 2)
        + (∫ p in Sx, p.1 * (2 * (∑ j, (starRingEnd ℂ) (linearField ((A.blocks K).potentialSource ι) x p j) * σ ι p j).re))
        + (∫ p in Sx, p.1 * (2 * (∑ j, (starRingEnd ℂ) (linearField ((A.blocks K).pairingSource ι) x p j) * σ ι p j).re))
        + 2 * (∫ p in Sx, (∑ i, star (y i) * ((p.1 : ℂ) * ∑ j, σ ι p j
            * (starRingEnd ℂ) ((A.blocks K).rowBand i ι p j))).re)
        + 2 * (∫ p in Sx, (∑ i, star (y i) * ((p.1 : ℂ) * ∑ j : Fin 9, linearField ((A.blocks K).bandMap ι) x p (gradSlot j)
            * (starRingEnd ℂ) (turnedRowBand D (A.blocks K) i ι p j))).re)
        + (1 - (A.blocks K).bandSlack)⁻¹ * (∫ p in Sx, (∑ i, star (y i) * ∑ i', ((p.1 : ℂ) * ∑ j : Fin 9,
            (starRingEnd ℂ) (turnedRowBand D (A.blocks K) i ι p j) * turnedRowBand D (A.blocks K) i' ι p j
              / ((A.blocks K).bandWeight ι (gradSlot j) : ℂ)) * y i').re) := by
    intro ι hι
    have hn := hc.band_turn K ι hι
    have hw := hc.band_weight_pos K ι hι
    have i4 : IntegrableOn (fun p => p.1 * ∑ j, (A.blocks K).bandWeight ι j * ‖σ ι p j‖ ^ 2) Sx :=
      integrableOn_scaled_re (integrable_sum hS
        (f := fun j p => ((A.blocks K).bandWeight ι j : ℂ) * σ ι p j) (g := fun j p => (starRingEnd ℂ) (σ ι p j))
        (fun j => wsq_const_mul (hσg ι hι j) _) (fun j => wsq_conj (hσg ι hι j))) 1 (fun p => by
          rw [one_mul, Complex.re_ofReal_mul, Complex.re_sum]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.sq_norm, Complex.normSq_apply]
          ring)
    have i5 : IntegrableOn (fun p => p.1 * (2 * (∑ j, (starRingEnd ℂ) (linearField ((A.blocks K).potentialSource ι) x p j)
      * σ ι p j).re)) Sx :=
      integrableOn_scaled_re (integrable_sum hS
        (f := fun j p => (starRingEnd ℂ) (linearField ((A.blocks K).potentialSource ι) x p j)) (g := fun j p => σ ι p j)
        (fun j => wsq_conj (hPg ι hι j)) (hσg ι hι)) 2 (fun p => by rw [Complex.re_ofReal_mul]; ring)
    have i6 : IntegrableOn (fun p => p.1 * (2 * (∑ j, (starRingEnd ℂ) (linearField ((A.blocks K).pairingSource ι) x p j)
      * σ ι p j).re)) Sx :=
      integrableOn_scaled_re (integrable_sum hS
        (f := fun j p => (starRingEnd ℂ) (linearField ((A.blocks K).pairingSource ι) x p j)) (g := fun j p => σ ι p j)
        (fun j => wsq_conj (hQg ι hι j)) (hσg ι hι)) 2 (fun p => by rw [Complex.re_ofReal_mul]; ring)
    have ia : IntegrableOn (fun p => p.1 * ∑ j : Fin 9, (A.blocks K).bandWeight ι (gradSlot j)
        * ‖linearField ((A.blocks K).bandMap ι) x p (gradSlot j)‖ ^ 2) Sx :=
      integrableOn_scaled_re (integrable_sum hS
        (f := fun j p => ((A.blocks K).bandWeight ι (gradSlot j) : ℂ) * linearField ((A.blocks K).bandMap ι) x p (gradSlot j))
        (g := fun j p => (starRingEnd ℂ) (linearField ((A.blocks K).bandMap ι) x p (gradSlot j)))
        (fun j => wsq_const_mul (hμ9 ι hι j) _) (fun j => wsq_conj (hμ9 ι hι j))) 1 (fun p => by
          rw [one_mul, Complex.re_ofReal_mul, Complex.re_sum]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.sq_norm, Complex.normSq_apply]
          ring)
    have ib : IntegrableOn (fun p => p.1 * (2 * (∑ j : Fin 9, (starRingEnd ℂ) (linearField ((A.blocks K).bandMap ι) x p (gradSlot j))
        * turnedSource D (A.blocks K) ι x p j).re)) Sx :=
      integrableOn_scaled_re (integrable_sum hS
        (f := fun j p => (starRingEnd ℂ) (linearField ((A.blocks K).bandMap ι) x p (gradSlot j)))
        (g := fun j p => turnedSource D (A.blocks K) ι x p j)
        (fun j => wsq_conj (hμ9 ι hι j)) (hsg' ι hι)) 2 (fun p => by rw [Complex.re_ofReal_mul]; ring)
    have ic : IntegrableOn (fun p => p.1 * ∑ j : Fin 9, ‖turnedSource D (A.blocks K) ι x p j
        - ((A.blocks K).bandWeight ι (gradSlot j) : ℂ) * linearField ((A.blocks K).bandMap ι) x p (gradSlot j)‖ ^ 2
          / ((A.blocks K).bandWeight ι (gradSlot j) * (A.blocks K).bandSlack)) Sx :=
      integrableOn_scaled_re (integrable_sum_div hS
        (fun j => (((A.blocks K).bandWeight ι (gradSlot j) * (A.blocks K).bandSlack : ℝ) : ℂ))
        (f := fun j p => turnedSource D (A.blocks K) ι x p j
          - ((A.blocks K).bandWeight ι (gradSlot j) : ℂ) * linearField ((A.blocks K).bandMap ι) x p (gradSlot j))
        (g := fun j p => (starRingEnd ℂ) (turnedSource D (A.blocks K) ι x p j
          - ((A.blocks K).bandWeight ι (gradSlot j) : ℂ) * linearField ((A.blocks K).bandMap ι) x p (gradSlot j)))
        (hE9 ι hι) (fun j => wsq_conj (hE9 ι hι j))) 1 (fun p => by
          rw [one_mul, Complex.re_ofReal_mul, Complex.re_sum]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Complex.div_ofReal_re]
          simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
          ring)
    set F1 : ℝ × ℝ → ℝ := fun p => p.1 * ∑ j, (A.blocks K).bandWeight ι j * ‖σ ι p j‖ ^ 2 with hF1
    set F2 : ℝ × ℝ → ℝ := fun p => p.1 * (2 * (∑ j, (starRingEnd ℂ) (linearField ((A.blocks K).potentialSource ι) x p j)
      * σ ι p j).re) with hF2
    set F3 : ℝ × ℝ → ℝ := fun p => p.1 * (2 * (∑ j, (starRingEnd ℂ) (linearField ((A.blocks K).pairingSource ι) x p j)
      * σ ι p j).re) with hF3
    set F4 : ℝ × ℝ → ℝ := fun p => (∑ i, star (y i) * ((p.1 : ℂ) * ∑ j, σ ι p j
      * (starRingEnd ℂ) ((A.blocks K).rowBand i ι p j))).re with hF4
    set F5 : ℝ × ℝ → ℝ := fun p => (∑ i, star (y i) * ((p.1 : ℂ) * ∑ j : Fin 9,
      linearField ((A.blocks K).bandMap ι) x p (gradSlot j) * (starRingEnd ℂ) (turnedRowBand D (A.blocks K) i ι p j))).re with hF5
    set F6 : ℝ × ℝ → ℝ := fun p => (∑ i, star (y i) * ∑ i', ((p.1 : ℂ) * ∑ j : Fin 9,
      (starRingEnd ℂ) (turnedRowBand D (A.blocks K) i ι p j) * turnedRowBand D (A.blocks K) i' ι p j
        / ((A.blocks K).bandWeight ι (gradSlot j) : ℂ)) * y i').re with hF6
    set F7 : ℝ × ℝ → ℝ := fun p => p.1 * (∑ j : Fin 9, (A.blocks K).bandWeight ι (gradSlot j)
            * ‖linearField ((A.blocks K).bandMap ι) x p (gradSlot j)‖ ^ 2
          - 2 * (∑ j : Fin 9, (starRingEnd ℂ) (linearField ((A.blocks K).bandMap ι) x p (gradSlot j))
              * turnedSource D (A.blocks K) ι x p j).re
          - ∑ j : Fin 9, ‖turnedSource D (A.blocks K) ι x p j
              - ((A.blocks K).bandWeight ι (gradSlot j) : ℂ) * linearField ((A.blocks K).bandMap ι) x p (gradSlot j)‖ ^ 2
              / ((A.blocks K).bandWeight ι (gradSlot j) * (A.blocks K).bandSlack)) with hF7
    have i7 : IntegrableOn F7 Sx :=
      ((ia.sub ib).sub ic).congr (Filter.Eventually.of_forall fun p => by
        simp only [hF7, Pi.sub_apply]
        ring)
    have j1 : IntegrableOn F4 Sx := integrableOn_scaled_re (hH1 ι hι) 1 (fun p => (one_mul _).symm)
    have j2 : IntegrableOn F5 Sx := integrableOn_scaled_re (hH2 ι hι) 1 (fun p => (one_mul _).symm)
    have j3 : IntegrableOn F6 Sx := integrableOn_scaled_re (hH3 ι hι) 1 (fun p => (one_mul _).symm)
    have hcomb := integral_combine i4 i5 i6 j1 j2 j3 i7 2 2 (1 - (A.blocks K).bandSlack)⁻¹
    have hnn : 0 ≤ ∫ p in Sx, (F1 p + F2 p + F3 p + 2 * F4 p + 2 * F5 p + (1 - (A.blocks K).bandSlack)⁻¹ * F6 p - F7 p) := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [ht ι hι, ae_restrict_mem hS.meas] with p hpt hp
      show (0 : ℝ) ≤ F1 p + F2 p + F3 p + 2 * F4 p + 2 * F5 p + (1 - (A.blocks K).bandSlack)⁻¹ * F6 p - F7 p
      have h0 := hS.nonneg p hp
      obtain ⟨z, hz⟩ : ∃ z : Fin 9 → ℂ, ∀ j, z j = ∑ i, y i * turnedRowBand D (A.blocks K) i ι p j := ⟨_, fun _ => rfl⟩
      have hzc : ∀ j, (starRingEnd ℂ) (z j)
          = ∑ i, (starRingEnd ℂ) (y i) * (starRingEnd ℂ) (turnedRowBand D (A.blocks K) i ι p j) := by
        intro j
        rw [hz, map_sum]
        simp only [map_mul]
      have L1 : p.1 * ∑ j : Fin 9, (A.blocks K).bandWeight ι (gradSlot j) * ‖σ ι p (gradSlot j)‖ ^ 2 ≤ F1 p :=
        mul_le_mul_of_nonneg_left (weight_split_le hw.2 (σ ι p)) h0
      have L2 : F2 p + F3 p = p.1 * (2 * (∑ j : Fin 9, (starRingEnd ℂ) (turnedSource D (A.blocks K) ι x p j)
          * σ ι p (gradSlot j)).re) := by
        have hd : ∑ j, (starRingEnd ℂ) (sourceSum (A.blocks K) ι x p j) * σ ι p j
            = ∑ j : Fin 9, (starRingEnd ℂ) (turnedSource D (A.blocks K) ι x p j) * σ ι p (gradSlot j) :=
          turned_dot hn.1 hn.2 p (σ ι p) (sourceSum (A.blocks K) ι x p) hpt
        rw [← hd]
        simp only [hF2, hF3, sourceSum, map_add, add_mul, Finset.sum_add_distrib, Complex.add_re]
        ring
      have L4 : F4 p = ((p.1 : ℂ) * ∑ j : Fin 9, σ ι p (gradSlot j) * (starRingEnd ℂ) (z j)).re := by
        have hd : ∀ i, ∑ j, σ ι p j * (starRingEnd ℂ) ((A.blocks K).rowBand i ι p j)
            = ∑ j : Fin 9, σ ι p (gradSlot j) * (starRingEnd ℂ) (turnedRowBand D (A.blocks K) i ι p j) :=
          fun i => turned_dot_right hn.1 hn.2 p (σ ι p) ((A.blocks K).rowBand i ι p) hpt
        simp only [hF4, hd]
        congr 1
        simp only [hzc, Finset.mul_sum, Complex.star_def]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        ring
      have L5 : F5 p = ((p.1 : ℂ) * ∑ j : Fin 9, linearField ((A.blocks K).bandMap ι) x p (gradSlot j)
          * (starRingEnd ℂ) (z j)).re := by
        simp only [hF5]
        congr 1
        simp only [hzc, Finset.mul_sum, Complex.star_def]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        ring
      have L6 : F6 p = ((p.1 : ℂ) * ∑ j : Fin 9, (starRingEnd ℂ) (z j) * z j
          / ((A.blocks K).bandWeight ι (gradSlot j) : ℂ)).re := by
        have e3a : ∀ i, ∑ i', ((p.1 : ℂ) * ∑ j : Fin 9, (starRingEnd ℂ) (turnedRowBand D (A.blocks K) i ι p j)
              * turnedRowBand D (A.blocks K) i' ι p j / ((A.blocks K).bandWeight ι (gradSlot j) : ℂ)) * y i'
            = (p.1 : ℂ) * ∑ j : Fin 9, (starRingEnd ℂ) (turnedRowBand D (A.blocks K) i ι p j) * z j
              / ((A.blocks K).bandWeight ι (gradSlot j) : ℂ) := by
          intro i
          simp only [hz, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i' _ => ?_
          ring
        simp only [hF6, e3a]
        congr 1
        simp only [hzc, Finset.mul_sum, Finset.sum_mul, Finset.sum_div, Complex.star_def]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        ring
      have key : 0 ≤ p.1 * ∑ j : Fin 9, ((A.blocks K).bandWeight ι (gradSlot j) * ‖σ ι p (gradSlot j)‖ ^ 2
          + 2 * ((starRingEnd ℂ) (turnedSource D (A.blocks K) ι x p j) * σ ι p (gradSlot j)).re
          + 2 * (σ ι p (gradSlot j) * (starRingEnd ℂ) (z j)).re
          + 2 * (linearField ((A.blocks K).bandMap ι) x p (gradSlot j) * (starRingEnd ℂ) (z j)).re
          + (1 - (A.blocks K).bandSlack)⁻¹ * (‖z j‖ ^ 2 / (A.blocks K).bandWeight ι (gradSlot j))
          - ((A.blocks K).bandWeight ι (gradSlot j) * ‖linearField ((A.blocks K).bandMap ι) x p (gradSlot j)‖ ^ 2
            - 2 * ((starRingEnd ℂ) (linearField ((A.blocks K).bandMap ι) x p (gradSlot j)) * turnedSource D (A.blocks K) ι x p j).re
            - ‖turnedSource D (A.blocks K) ι x p j - ((A.blocks K).bandWeight ι (gradSlot j) : ℂ)
                * linearField ((A.blocks K).bandMap ι) x p (gradSlot j)‖ ^ 2
              / ((A.blocks K).bandWeight ι (gradSlot j) * (A.blocks K).bandSlack))) :=
        mul_nonneg h0 (Finset.sum_nonneg fun j _ => point_nonneg (hw.1 j) (hc.band_slack K).1 (hc.band_slack K).2
          (σ ι p (gradSlot j)) (linearField ((A.blocks K).bandMap ι) x p (gradSlot j)) (turnedSource D (A.blocks K) ι x p j) (z j)
          (fun h => hc.slack_zero K h ι hι x hx p j))
      have hid : p.1 * ∑ j : Fin 9, ((A.blocks K).bandWeight ι (gradSlot j) * ‖σ ι p (gradSlot j)‖ ^ 2
          + 2 * ((starRingEnd ℂ) (turnedSource D (A.blocks K) ι x p j) * σ ι p (gradSlot j)).re
          + 2 * (σ ι p (gradSlot j) * (starRingEnd ℂ) (z j)).re
          + 2 * (linearField ((A.blocks K).bandMap ι) x p (gradSlot j) * (starRingEnd ℂ) (z j)).re
          + (1 - (A.blocks K).bandSlack)⁻¹ * (‖z j‖ ^ 2 / (A.blocks K).bandWeight ι (gradSlot j))
          - ((A.blocks K).bandWeight ι (gradSlot j) * ‖linearField ((A.blocks K).bandMap ι) x p (gradSlot j)‖ ^ 2
            - 2 * ((starRingEnd ℂ) (linearField ((A.blocks K).bandMap ι) x p (gradSlot j)) * turnedSource D (A.blocks K) ι x p j).re
            - ‖turnedSource D (A.blocks K) ι x p j - ((A.blocks K).bandWeight ι (gradSlot j) : ℂ)
                * linearField ((A.blocks K).bandMap ι) x p (gradSlot j)‖ ^ 2
              / ((A.blocks K).bandWeight ι (gradSlot j) * (A.blocks K).bandSlack)))
          = p.1 * ∑ j : Fin 9, (A.blocks K).bandWeight ι (gradSlot j) * ‖σ ι p (gradSlot j)‖ ^ 2
            + p.1 * (2 * (∑ j : Fin 9, (starRingEnd ℂ) (turnedSource D (A.blocks K) ι x p j) * σ ι p (gradSlot j)).re)
            + 2 * ((p.1 : ℂ) * ∑ j : Fin 9, σ ι p (gradSlot j) * (starRingEnd ℂ) (z j)).re
            + 2 * ((p.1 : ℂ) * ∑ j : Fin 9, linearField ((A.blocks K).bandMap ι) x p (gradSlot j) * (starRingEnd ℂ) (z j)).re
            + (1 - (A.blocks K).bandSlack)⁻¹ * ((p.1 : ℂ) * ∑ j : Fin 9, (starRingEnd ℂ) (z j) * z j
                / ((A.blocks K).bandWeight ι (gradSlot j) : ℂ)).re
            - F7 p := by
        have hzz : ∀ j : Fin 9, ((starRingEnd ℂ) (z j) * z j / ((A.blocks K).bandWeight ι (gradSlot j) : ℂ)).re
            = ‖z j‖ ^ 2 / (A.blocks K).bandWeight ι (gradSlot j) := by
          intro j
          rw [Complex.div_ofReal_re]
          simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
          ring
        simp only [hF7, Complex.re_ofReal_mul, Complex.re_sum, hzz]
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, mul_sub]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [L4, L5, L6]
      linarith [L1, L2, key, hid]
    linarith [hcomb, hnn]
  have hsum := Finset.sum_le_sum hper
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  exact hsum

end TurnedBand

theorem eliminationStage_holds : EliminationStageHolds := by
  intro k C nE nM D R A S _ _ hc K x σ hx hσ ht
  have hres := hc.residual_value_le K x hx
  obtain ⟨y, hy⟩ := TurnedBand.Internal.le_exists (A.blocks K).rowFull
    ((A.blocks K).rowMap *ᵥ x - fun i => ∑ ι ∈ D.mesh.band K, ∫ p in (D.mesh.box K).rect,
      (p.1 : ℂ) * ∑ j : Fin 9, linearField ((A.blocks K).bandMap ι) x p (gradSlot j)
        * (starRingEnd ℂ) (turnedRowBand D (A.blocks K) i ι p j))
  have hW := TurnedBand.Internal.cross_le (hc.row_weight_pos K) (rowVector D K (A.blocks K) x σ) y
  have hband := TurnedBand.band_bound D R A S hc K x hx σ hσ ht y
  have hP : 0 ≤ (star y ⬝ᵥ (((A.blocks K).rowFull - (A.blocks K).rowWeight
      - ((1 - (A.blocks K).bandSlack)⁻¹ : ℂ) • bandGram D K (A.blocks K)) *ᵥ y)).re :=
    (Complex.le_def.mp ((hc.row_full_dominates K).dotProduct_mulVec_nonneg y)).1
  have hcc : ((1 - (A.blocks K).bandSlack)⁻¹ : ℂ) = (((1 - (A.blocks K).bandSlack)⁻¹ : ℝ) : ℂ) := by
    push_cast
    ring
  rw [sub_mulVec, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_sub, dotProduct_smul, hcc,
    smul_eq_mul, Complex.sub_re, Complex.sub_re, Complex.re_ofReal_mul] at hP
  have hre : rowsEliminated D K (A.blocks K) x = Coupling.inverseWeightedSq (A.blocks K).rowFull
      ((A.blocks K).rowMap *ᵥ x - fun i => ∑ ι ∈ D.mesh.band K, ∫ p in (D.mesh.box K).rect,
        (p.1 : ℂ) * ∑ j : Fin 9, linearField ((A.blocks K).bandMap ι) x p (gradSlot j)
          * (starRingEnd ℂ) (turnedRowBand D (A.blocks K) i ι p j)) := rfl
  have hrv : rowVector D K (A.blocks K) x σ = (A.blocks K).rowMap *ᵥ x + fun i => ∑ ι ∈ D.mesh.band K,
      ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ j, σ ι p j * (starRingEnd ℂ) ((A.blocks K).rowBand i ι p j) := rfl
  rw [dotProduct_sub, Complex.sub_re] at hy
  rw [hrv, dotProduct_add, Complex.add_re] at hW
  rw [← hrv] at hW
  linarith

end Assembly

end CertCell

end Breakdown
