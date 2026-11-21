import Breakdown.FracCell.CellFormBoundSharpSt
import Breakdown.FracCell.CellFormBound

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace CellFormBoundInternal

lemma cpx_complete {h : ℝ} (hh : 0 < h) (a b : ℂ) :
    -(‖b‖ ^ 2 / h) ≤ h * ‖a‖ ^ 2 + 2 * (a * (starRingEnd ℂ) b).re := by
  rw [← sub_nonneg]
  have key : h * ‖a‖ ^ 2 + 2 * (a * (starRingEnd ℂ) b).re - -(‖b‖ ^ 2 / h) =
      ((h * a.re + b.re) ^ 2 + (h * a.im + b.im) ^ 2) / h := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    field_simp
    ring
  rw [key]; positivity

lemma cpx_expand (y w : ℂ) : ‖y + w‖ ^ 2 = ‖y‖ ^ 2 + 2 * (y * (starRingEnd ℂ) w).re + ‖w‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]; ring

lemma cpx_self (z : ℂ) : (z * (starRingEnd ℂ) z).re = ‖z‖ ^ 2 := by
  rw [Complex.mul_conj, Complex.sq_norm]; simp

lemma cpx_far {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (y w : ℂ) :
    ‖y + w‖ ^ 2 ≤ ‖y‖ ^ 2 / t + ‖w‖ ^ 2 / (1 - t) := by
  have h1 : 0 < 1 - t := by linarith
  have htri : ‖y + w‖ ≤ ‖y‖ + ‖w‖ := norm_add_le y w
  have hsq : ‖y + w‖ ^ 2 ≤ (‖y‖ + ‖w‖) ^ 2 := by
    have := norm_nonneg (y + w); nlinarith
  have key : ‖y‖ ^ 2 / t + ‖w‖ ^ 2 / (1 - t) - (‖y‖ + ‖w‖) ^ 2 =
      ((1 - t) * ‖y‖ - t * ‖w‖) ^ 2 / (t * (1 - t)) := by
    field_simp; ring
  have : 0 ≤ ((1 - t) * ‖y‖ - t * ‖w‖) ^ 2 / (t * (1 - t)) := by positivity
  linarith

end CellFormBoundInternal

namespace CellFormBoundInternal

lemma pen_ge {hs ha : ℝ} (hs0 : 0 < hs) (ha0 : 0 < ha) (σ Z : Fin 3 → Fin 3 → ℂ) :
    -(symSq Z / hs + antiSq Z / ha) ≤ strainPen hs ha σ Z := by
  have e1 := Finset.sum_nonneg fun (a : Fin 3) (_ : a ∈ Finset.univ) => Finset.sum_nonneg
    fun (b : Fin 3) (_ : b ∈ Finset.univ) =>
      sub_nonneg.2 (cpx_complete hs0 ((σ a b + σ b a) / 2) ((Z a b + Z b a) / 2))
  have e2 := Finset.sum_nonneg fun (a : Fin 3) (_ : a ∈ Finset.univ) => Finset.sum_nonneg
    fun (b : Fin 3) (_ : b ∈ Finset.univ) =>
      sub_nonneg.2 (cpx_complete ha0 ((σ a b - σ b a) / 2) ((Z a b - Z b a) / 2))
  unfold strainPen symSq antiSq entryPairing
  simp only [Complex.add_re, Complex.re_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.sum_div] at e1 e2 ⊢
  linarith

lemma vel_ge {hv : ℝ} (hv0 : 0 < hv) (σ Z : Fin 3 → ℂ) : -(vecSq Z / hv) ≤ velPen hv σ Z := by
  have e1 := Finset.sum_nonneg fun (a : Fin 3) (_ : a ∈ Finset.univ) =>
      sub_nonneg.2 (cpx_complete hv0 (σ a) (Z a))
  unfold velPen vecSq CellScalars.vecPair
  simp only [Complex.re_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.sum_div] at e1 ⊢
  linarith

lemma symSq_add (Y W : Fin 3 → Fin 3 → ℂ) :
    symSq (fun a b => Y a b + W a b) = symSq Y
      + 2 * (entryPairing (fun a b => (Y a b + Y b a) / 2) (fun a b => (W a b + W b a) / 2)).re
      + (entryPairing (fun a b => (W a b + W b a) / 2) (fun a b => (W a b + W b a) / 2)).re := by
  simp only [symSq, entryPairing, Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [cpx_self, show (Y a b + W a b + (Y b a + W b a)) / 2 = (Y a b + Y b a) / 2 + (W a b + W b a) / 2 by ring,
    cpx_expand]

lemma antiSq_add (Y W : Fin 3 → Fin 3 → ℂ) :
    antiSq (fun a b => Y a b + W a b) = antiSq Y
      + 2 * (entryPairing (fun a b => (Y a b - Y b a) / 2) (fun a b => (W a b - W b a) / 2)).re
      + (entryPairing (fun a b => (W a b - W b a) / 2) (fun a b => (W a b - W b a) / 2)).re := by
  simp only [antiSq, entryPairing, Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [cpx_self, show (Y a b + W a b - (Y b a + W b a)) / 2 = (Y a b - Y b a) / 2 + (W a b - W b a) / 2 by ring,
    cpx_expand]

lemma vecSq_add (Y W : Fin 3 → ℂ) :
    vecSq (fun a => Y a + W a) = vecSq Y + 2 * (CellScalars.vecPair Y W).re + (CellScalars.vecPair W W).re := by
  simp only [vecSq, CellScalars.vecPair, Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [cpx_self, cpx_expand]

lemma swp_re (X Y : Fin 3 → Fin 3 → ℂ) (hs ha : ℝ) :
    (CellScalars.sigmaWeightedPair X Y hs ha).re =
      (entryPairing (fun a b => (Y a b + Y b a) / 2) (fun a b => (X a b + X b a) / 2)).re / hs
        + (entryPairing (fun a b => (Y a b - Y b a) / 2) (fun a b => (X a b - X b a) / 2)).re / ha := by
  simp only [CellScalars.sigmaWeightedPair, Complex.add_re, Complex.div_ofReal_re]

lemma swp_self (W : Fin 3 → Fin 3 → ℂ) (hs ha : ℝ) :
    (CellScalars.sigmaWeightedPair W W hs ha).re = symSq W / hs + antiSq W / ha := by
  rw [swp_re]
  simp only [symSq, antiSq, entryPairing, Complex.re_sum, cpx_self]

lemma vecPair_self (W : Fin 3 → ℂ) : (CellScalars.vecPair W W).re = vecSq W := by
  simp only [vecSq, CellScalars.vecPair, Complex.re_sum, cpx_self]

end CellFormBoundInternal

namespace CellFormBoundInternal

lemma strain_near {hs ha : ℝ} (hs0 : 0 < hs) (ha0 : 0 < ha) (σ Y W : Fin 3 → Fin 3 → ℂ) (q : Prop) [Decidable q] :
    -(symSq Y / hs + antiSq Y / ha)
        - (if q then 2 * (CellScalars.sigmaWeightedPair W Y hs ha).re + (CellScalars.sigmaWeightedPair W W hs ha).re
          else 0)
      ≤ strainPen hs ha σ (fun i j => Y i j + if q then W i j else 0) := by
  by_cases hq : q
  · simp only [hq, if_true]
    have hp := pen_ge hs0 ha0 σ (fun i j => Y i j + W i j)
    rw [symSq_add, antiSq_add] at hp
    rw [swp_re, swp_re]
    have e1 : (symSq Y + 2 * (entryPairing (fun a b => (Y a b + Y b a) / 2) (fun a b => (W a b + W b a) / 2)).re
        + (entryPairing (fun a b => (W a b + W b a) / 2) (fun a b => (W a b + W b a) / 2)).re) / hs
        = symSq Y / hs + 2 * ((entryPairing (fun a b => (Y a b + Y b a) / 2) (fun a b => (W a b + W b a) / 2)).re / hs)
          + (entryPairing (fun a b => (W a b + W b a) / 2) (fun a b => (W a b + W b a) / 2)).re / hs := by ring
    have e2 : (antiSq Y + 2 * (entryPairing (fun a b => (Y a b - Y b a) / 2) (fun a b => (W a b - W b a) / 2)).re
        + (entryPairing (fun a b => (W a b - W b a) / 2) (fun a b => (W a b - W b a) / 2)).re) / ha
        = antiSq Y / ha + 2 * ((entryPairing (fun a b => (Y a b - Y b a) / 2) (fun a b => (W a b - W b a) / 2)).re / ha)
          + (entryPairing (fun a b => (W a b - W b a) / 2) (fun a b => (W a b - W b a) / 2)).re / ha := by ring
    rw [e1, e2] at hp
    linarith
  · simp only [hq, if_false, add_zero, sub_zero]
    exact pen_ge hs0 ha0 σ Y

lemma vel_near {hv : ℝ} (hv0 : 0 < hv) (τ Y W : Fin 3 → ℂ) :
    -(vecSq Y / hv) - (2 * ((CellScalars.vecPair Y W).re / hv) + vecSq W / hv)
      ≤ velPen hv τ (fun i => Y i + W i) := by
  have hp := vel_ge hv0 τ (fun i => Y i + W i)
  rw [vecSq_add, vecPair_self] at hp
  have e : (vecSq Y + 2 * (CellScalars.vecPair Y W).re + vecSq W) / hv
      = vecSq Y / hv + 2 * ((CellScalars.vecPair Y W).re / hv) + vecSq W / hv := by ring
  rw [e] at hp
  linarith

lemma symSq_nonneg' (Y : Fin 3 → Fin 3 → ℂ) : 0 ≤ symSq Y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma antiSq_nonneg' (Y : Fin 3 → Fin 3 → ℂ) : 0 ≤ antiSq Y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma vecSq_nonneg' (Y : Fin 3 → ℂ) : 0 ≤ vecSq Y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma symSq_far {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (Y W : Fin 3 → Fin 3 → ℂ) :
    symSq (fun a b => Y a b + W a b) ≤ symSq Y / t + symSq W / (1 - t) := by
  simp only [symSq, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  rw [show (Y a b + W a b + (Y b a + W b a)) / 2 = (Y a b + Y b a) / 2 + (W a b + W b a) / 2 by ring]
  exact cpx_far ht0 ht1 _ _

lemma antiSq_far {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (Y W : Fin 3 → Fin 3 → ℂ) :
    antiSq (fun a b => Y a b + W a b) ≤ antiSq Y / t + antiSq W / (1 - t) := by
  simp only [antiSq, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  rw [show (Y a b + W a b - (Y b a + W b a)) / 2 = (Y a b - Y b a) / 2 + (W a b - W b a) / 2 by ring]
  exact cpx_far ht0 ht1 _ _

lemma vecSq_far {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (Y W : Fin 3 → ℂ) :
    vecSq (fun a => Y a + W a) ≤ vecSq Y / t + vecSq W / (1 - t) := by
  simp only [vecSq, Finset.sum_div, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun a _ => cpx_far ht0 ht1 _ _

lemma strain_far {hs ha t : ℝ} (hs0 : 0 < hs) (ha0 : 0 < ha) (ht0 : 0 < t) (ht1 : t < 1)
    (σ Y W : Fin 3 → Fin 3 → ℂ) (q : Prop) [Decidable q] :
    -((symSq Y / hs + antiSq Y / ha) / t)
        - (if q then (CellScalars.sigmaWeightedPair W W hs ha).re / (1 - t) else 0)
      ≤ strainPen hs ha σ (fun i j => Y i j + if q then W i j else 0) := by
  have h1t : 0 < 1 - t := by linarith
  by_cases hq : q
  · simp only [hq, if_true]
    have hp := pen_ge hs0 ha0 σ (fun i j => Y i j + W i j)
    rw [swp_self]
    have f1 := div_le_div_of_nonneg_right (symSq_far ht0 ht1 Y W) hs0.le
    have f2 := div_le_div_of_nonneg_right (antiSq_far ht0 ht1 Y W) ha0.le
    have e : (symSq Y / t + symSq W / (1 - t)) / hs + (antiSq Y / t + antiSq W / (1 - t)) / ha
        = (symSq Y / hs + antiSq Y / ha) / t + (symSq W / hs + antiSq W / ha) / (1 - t) := by ring
    linarith
  · simp only [hq, if_false, add_zero, sub_zero]
    have hp := pen_ge hs0 ha0 σ Y
    have hY : 0 ≤ symSq Y / hs + antiSq Y / ha :=
      add_nonneg (div_nonneg (symSq_nonneg' Y) hs0.le) (div_nonneg (antiSq_nonneg' Y) ha0.le)
    have : symSq Y / hs + antiSq Y / ha ≤ (symSq Y / hs + antiSq Y / ha) / t := by
      rw [le_div_iff₀ ht0]; nlinarith
    linarith

lemma vel_far {hv t : ℝ} (hv0 : 0 < hv) (ht0 : 0 < t) (ht1 : t < 1) (τ Y W : Fin 3 → ℂ) :
    -(vecSq Y / hv / t) - vecSq W / hv / (1 - t) ≤ velPen hv τ (fun i => Y i + W i) := by
  have hp := vel_ge hv0 τ (fun i => Y i + W i)
  have f := div_le_div_of_nonneg_right (vecSq_far ht0 ht1 Y W) hv0.le
  have e : (vecSq Y / t + vecSq W / (1 - t)) / hv = vecSq Y / hv / t + vecSq W / hv / (1 - t) := by ring
  linarith

lemma ep_lin (P Q R : Fin 3 → Fin 3 → ℂ) (r : ℝ) :
    (entryPairing P (fun a b => (r : ℂ) * Q a b + R a b)).re = r * (entryPairing P Q).re + (entryPairing P R).re := by
  simp only [entryPairing, map_add, map_mul, Complex.conj_ofReal, mul_add, Finset.sum_add_distrib,
    Complex.add_re, Complex.re_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_left_comm, Complex.re_ofReal_mul]

lemma ep_sum {ι : Type*} (T : Finset ι) (μ : ι → ℝ) (P : Fin 3 → Fin 3 → ℂ) (Q : ι → Fin 3 → Fin 3 → ℂ) :
    (entryPairing P (fun i q => ∑ a ∈ T, ((μ a : ℝ) : ℂ) * Q a i q)).re
      = ∑ a ∈ T, μ a * (entryPairing P (Q a)).re := by
  simp only [entryPairing, map_sum, map_mul, Complex.conj_ofReal, Finset.mul_sum, Complex.re_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => ?_
  rw [mul_left_comm, Complex.re_ofReal_mul]

lemma swp_lin {ι : Type*} (T : Finset ι) (μ : ι → ℝ) (X : ι → Fin 3 → Fin 3 → ℂ) (Y : Fin 3 → Fin 3 → ℂ)
    (hs ha : ℝ) :
    (CellScalars.sigmaWeightedPair (fun i q => ∑ a ∈ T, ((μ a : ℝ) : ℂ) * X a i q) Y hs ha).re
      = ∑ a ∈ T, μ a * (CellScalars.sigmaWeightedPair (X a) Y hs ha).re := by
  simp only [swp_re]
  have e1 : (fun i q => (∑ a ∈ T, ((μ a : ℝ) : ℂ) * X a i q + ∑ a ∈ T, ((μ a : ℝ) : ℂ) * X a q i) / 2)
      = fun i q => ∑ a ∈ T, ((μ a : ℝ) : ℂ) * ((X a i q + X a q i) / 2) := by
    funext i q; rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun a _ => by ring
  have e2 : (fun i q => (∑ a ∈ T, ((μ a : ℝ) : ℂ) * X a i q - ∑ a ∈ T, ((μ a : ℝ) : ℂ) * X a q i) / 2)
      = fun i q => ∑ a ∈ T, ((μ a : ℝ) : ℂ) * ((X a i q - X a q i) / 2) := by
    funext i q; rw [← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [e1, e2, ep_sum, ep_sum]
  simp only [mul_add, Finset.sum_add_distrib, Finset.sum_div, mul_div_assoc]

lemma vp_lin {ι : Type*} (T : Finset ι) (μ : ι → ℝ) (X : ι → Fin 3 → ℂ) (Y : Fin 3 → ℂ) :
    (CellScalars.vecPair Y (fun i => ∑ a ∈ T, ((μ a : ℝ) : ℂ) * X a i)).re
      = ∑ a ∈ T, μ a * (CellScalars.vecPair Y (X a)).re := by
  simp only [CellScalars.vecPair, map_sum, map_mul, Complex.conj_ofReal, Finset.mul_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, Complex.re_ofReal_mul]

end CellFormBoundInternal

namespace CellFormBoundInternal

variable {α : ℝ} {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
  {Cl : CellClasses} {slots : ℕ} {R : CellRows N slots k}

lemma sum_mem_ite (s t : Finset ℤ) (hts : t ⊆ s) (F : ℤ → ℕ → ℕ → ℝ) (m : ℕ) :
    (∑ n ∈ s, ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m, if n ∈ t then F n j l else 0)
      = ∑ n ∈ t, ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m, F n j l := by
  have e : ∀ n, (∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m, if n ∈ t then F n j l else 0)
      = if n ∈ t then ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m, F n j l else 0 := by
    intro n; split_ifs <;> simp
  simp only [e]
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hts]

lemma sym_pos (hd : IsCellData α c K S B Cl R) {n : ℤ} {j l : ℕ} (h : n ∉ S.resolved ∨ S.degHigh < max j l) :
    0 < S.symWeight n j l :=
  lt_of_lt_of_le hd.scalars.weightFloor_pos (hd.scalars.sym_weight n j l h).1

lemma anti_pos (hd : IsCellData α c K S B Cl R) {n : ℤ} {j l : ℕ} (h : n ∉ S.resolved ∨ S.degHigh < max j l) :
    0 < S.antiWeight n j l :=
  lt_of_lt_of_le hd.scalars.weightFloor_pos (hd.scalars.anti_weight n j l h).1

lemma vel_pos (hd : IsCellData α c K S B Cl R) {n : ℤ} (hn : n ∈ S.resolved) {j l : ℕ} (h : S.degHigh ≤ max j l) :
    0 < S.velWeight n j l :=
  lt_of_lt_of_le hd.scalars.weightFloor_pos (hd.scalars.vel_weight n hn j l h).1

end CellFormBoundInternal

namespace CellFormBoundInternal

lemma comm4 {ι : Type*} (T : Finset ι) (s : Finset ℤ) (m : ℕ) (μ : ι → ℝ) (cnd : ℤ → ℕ → ℕ → Prop)
    [∀ n j l, Decidable (cnd n j l)] (f : ι → ℤ → ℕ → ℕ → ℝ) :
    (∑ a ∈ T, μ a * ∑ n ∈ s, ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m, if cnd n j l then f a n j l else 0)
      = ∑ n ∈ s, ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m,
          if cnd n j l then ∑ a ∈ T, μ a * f a n j l else 0 := by
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

variable {k N : ℕ} {slots : ℕ}

lemma rowY_sum (c : FracCellData k N) (K : CellBox) (S : CellScalars) (R : CellRows N slots k) (B : CellBases)
    (κ ζ : Fin k → ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (μ : Fin N → ℝ) :
    (∑ a ∈ R.rowSet, μ a * CellScalars.rowYPair c K S R B κ ζ v G a)
      = (∑ n ∈ S.resolved ∪ S.band, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
          if (n ∉ S.resolved ∨ S.degHigh < max j l) then
            (CellScalars.sigmaWeightedPair
              (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n p i q) j l)
              (fun i q => B.coef K (fun p => CellScalars.yFolded c K S κ ζ v G n p i q) j l)
              (S.symWeight n j l) (S.antiWeight n j l)).re
          else 0)
        + ∑ n ∈ S.resolved, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
          if S.degHigh ≤ max j l then
            (CellScalars.vecPair (fun i => B.coef K (fun p => CellScalars.yVelocity c K S v G n p i) j l)
              (fun i => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingVelocity c K R a n p i) j l)).re
              / S.velWeight n j l
          else 0 := by
  unfold CellScalars.rowYPair
  simp only [Complex.add_re, Complex.re_sum, apply_ite Complex.re, Complex.zero_re, Complex.div_ofReal_re,
    mul_add, Finset.sum_add_distrib]
  rw [comm4, comm4]
  congr 1
  · refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · exact (swp_lin _ _ _ _ _ _).symm
    · rfl
  · refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rw [vp_lin, Finset.sum_div]
      exact Finset.sum_congr rfl fun a _ => by ring
    · rfl

end CellFormBoundInternal

namespace CellFormBoundInternal

lemma near_bound {α : ℝ} {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {Cl : CellClasses} {slots : ℕ} {R : CellRows N slots k} (hd : IsCellData α c K S B Cl R)
    (κ ζ : Fin k → ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (μ : Fin N → ℝ)
    (σ : ℤ → ℕ → ℕ → Fin 3 → Fin 3 → ℂ) (τ : ℤ → ℕ → ℕ → Fin 3 → ℂ) :
    -CellScalars.nearWeighted c K S B κ ζ v G R - 2 * (∑ a ∈ R.rowSet, μ a * CellScalars.rowYPair c K S R B κ ζ v G a)
        - CellScalars.rowSquare c K S R B μ (fun _ _ => True)
      ≤ (∑ n ∈ R.yModes, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
            CellScalars.sharpStrainTerm c K S R B μ κ ζ v G σ n j l)
        + ∑ n ∈ S.resolved, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
            CellScalars.sharpVelocityTerm c K S R B μ v G τ n j l := by
  have hS : ∀ n ∈ R.yModes, ∀ j ∈ Finset.range (S.degNear + 1), ∀ l ∈ Finset.range (S.degNear + 1),
      -(if True ∧ (n ∉ S.resolved ∨ S.degHigh < max j l) then
          symSq (fun a b => B.coef K (fun p => CellScalars.yFolded c K S κ ζ v G n p a b) j l) / S.symWeight n j l
            + antiSq (fun a b => B.coef K (fun p => CellScalars.yFolded c K S κ ζ v G n p a b) j l) / S.antiWeight n j l
        else 0)
      - (if n ∈ S.resolved ∪ S.band then
          2 * (if (n ∉ S.resolved ∨ S.degHigh < max j l) then
            (CellScalars.sigmaWeightedPair
              (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n p i q) j l)
              (fun i q => B.coef K (fun p => CellScalars.yFolded c K S κ ζ v G n p i q) j l)
              (S.symWeight n j l) (S.antiWeight n j l)).re else 0)
          + (if True ∧ (n ∉ S.resolved ∨ S.degHigh < max j l) then
            (CellScalars.sigmaWeightedPair
              (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n p i q) j l)
              (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n p i q) j l)
              (S.symWeight n j l) (S.antiWeight n j l)).re else 0)
        else 0)
      ≤ CellScalars.sharpStrainTerm c K S R B μ κ ζ v G σ n j l := by
    intro n _ j _ l _
    unfold CellScalars.sharpStrainTerm
    by_cases hc : n ∉ S.resolved ∨ S.degHigh < max j l
    · simp only [hc, true_and, if_true]
      have h := strain_near (sym_pos hd hc) (anti_pos hd hc) (σ n j l)
        (fun i q => B.coef K (fun p => CellScalars.yFolded c K S κ ζ v G n p i q) j l)
        (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n p i q) j l)
        (n ∈ S.resolved ∪ S.band)
      exact h
    · simp only [hc, and_false, if_false, mul_zero, add_zero, ite_self, neg_zero, sub_zero, le_refl]
  have hV : ∀ n ∈ S.resolved, ∀ j ∈ Finset.range (S.degNear + 1), ∀ l ∈ Finset.range (S.degNear + 1),
      -(if True ∧ S.degHigh ≤ max j l then
          vecSq (fun a => B.coef K (fun p => CellScalars.yVelocity c K S v G n p a) j l) / S.velWeight n j l else 0)
      - (2 * (if S.degHigh ≤ max j l then
            (CellScalars.vecPair (fun i => B.coef K (fun p => CellScalars.yVelocity c K S v G n p i) j l)
              (fun i => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingVelocity c K R a n p i) j l)).re
              / S.velWeight n j l else 0)
        + (if True ∧ S.degHigh ≤ max j l then
            vecSq (fun i => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingVelocity c K R a n p i) j l)
              / S.velWeight n j l else 0))
      ≤ CellScalars.sharpVelocityTerm c K S R B μ v G τ n j l := by
    intro n hn j _ l _
    unfold CellScalars.sharpVelocityTerm
    by_cases hc : S.degHigh ≤ max j l
    · simp only [hc, true_and, if_true]
      exact vel_near (vel_pos hd hn hc) (τ n j l) _ _
    · simp only [hc, and_false, if_false, mul_zero, add_zero, neg_zero, sub_zero, le_refl]
  have sS := Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun l hl => hS n hn j hj l hl
  have sV := Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun l hl => hV n hn j hj l hl
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at sS
  rw [sum_mem_ite _ _ hd.yModes_contain] at sS
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at sS sV
  have eN : CellScalars.nearWeighted c K S B κ ζ v G R =
      (∑ n ∈ R.yModes, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
        if True ∧ (n ∉ S.resolved ∨ S.degHigh < max j l) then
          symSq (fun a b => B.coef K (fun p => CellScalars.yFolded c K S κ ζ v G n p a b) j l) / S.symWeight n j l
            + antiSq (fun a b => B.coef K (fun p => CellScalars.yFolded c K S κ ζ v G n p a b) j l) / S.antiWeight n j l
        else 0)
      + ∑ n ∈ S.resolved, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
        if True ∧ S.degHigh ≤ max j l then
          vecSq (fun a => B.coef K (fun p => CellScalars.yVelocity c K S v G n p a) j l) / S.velWeight n j l else 0 := rfl
  have eR : CellScalars.rowSquare c K S R B μ (fun _ _ => True) =
      (∑ n ∈ S.resolved ∪ S.band, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
        if True ∧ (n ∉ S.resolved ∨ S.degHigh < max j l) then
            (CellScalars.sigmaWeightedPair
              (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n p i q) j l)
              (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n p i q) j l)
              (S.symWeight n j l) (S.antiWeight n j l)).re else 0)
      + ∑ n ∈ S.resolved, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
        if True ∧ S.degHigh ≤ max j l then
            vecSq (fun i => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingVelocity c K R a n p i) j l)
              / S.velWeight n j l else 0 := rfl
  rw [eN, eR, rowY_sum]
  linarith

end CellFormBoundInternal

namespace CellFormBoundInternal

lemma far_bound' {α : ℝ} {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {Cl : CellClasses} {slots : ℕ} {R : CellRows N slots k} (hd : IsCellData α c K S B Cl R)
    (κ ζ : Fin k → ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (μ : Fin N → ℝ)
    (σ : ℤ → ℕ → ℕ → Fin 3 → Fin 3 → ℂ) (τ : ℤ → ℕ → ℕ → Fin 3 → ℂ)
    (hsF : Summable (CellScalars.sharpFarTerm c K S R B μ κ ζ v G σ τ))
    (hsY : Summable (fun jl : ℕ × ℕ =>
          if S.degNear < max jl.1 jl.2 then
            (∑ n ∈ R.yModes, if (n ∉ S.resolved ∨ S.degHigh < max jl.1 jl.2) then
              symSq (fun a b => B.coef K (fun p => CellScalars.yFolded c K S κ ζ v G n p a b) jl.1 jl.2)
                  / S.symWeight n jl.1 jl.2
                + antiSq (fun a b => B.coef K (fun p => CellScalars.yFolded c K S κ ζ v G n p a b) jl.1 jl.2)
                  / S.antiWeight n jl.1 jl.2
              else 0)
            + ∑ n ∈ S.resolved,
                vecSq (fun a => B.coef K (fun p => CellScalars.yVelocity c K S v G n p a) jl.1 jl.2)
                  / S.velWeight n jl.1 jl.2
          else 0))
    (hsW : Summable (fun jl : ℕ × ℕ => if S.degNear < max jl.1 jl.2 then
          (∑ n' ∈ S.resolved ∪ S.band,
            (CellScalars.sigmaWeightedPair
              (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n' p i q) jl.1 jl.2)
              (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n' p i q) jl.1 jl.2)
              (S.symWeight n' jl.1 jl.2) (S.antiWeight n' jl.1 jl.2)).re)
          + ∑ n' ∈ S.resolved,
            vecSq (fun i => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingVelocity c K R a n' p i) jl.1 jl.2)
              / S.velWeight n' jl.1 jl.2
          else 0)) :
    -(CellScalars.farWeighted c K S B κ ζ v G R / R.farShare)
        - CellScalars.rowSquareFar c K S R B μ / (1 - R.farShare)
      ≤ ∑' jl : ℕ × ℕ, CellScalars.sharpFarTerm c K S R B μ κ ζ v G σ τ jl := by
  obtain ⟨ht0, ht1⟩ := hd.farShare_mem
  obtain ⟨_, _, hdeg⟩ := hd.scalars.degrees
  have hper : ∀ jl : ℕ × ℕ,
      -((if S.degNear < max jl.1 jl.2 then
            (∑ n ∈ R.yModes, if (n ∉ S.resolved ∨ S.degHigh < max jl.1 jl.2) then
              symSq (fun a b => B.coef K (fun p => CellScalars.yFolded c K S κ ζ v G n p a b) jl.1 jl.2)
                  / S.symWeight n jl.1 jl.2
                + antiSq (fun a b => B.coef K (fun p => CellScalars.yFolded c K S κ ζ v G n p a b) jl.1 jl.2)
                  / S.antiWeight n jl.1 jl.2
              else 0)
            + ∑ n ∈ S.resolved,
                vecSq (fun a => B.coef K (fun p => CellScalars.yVelocity c K S v G n p a) jl.1 jl.2)
                  / S.velWeight n jl.1 jl.2
          else 0) / R.farShare)
        - (if S.degNear < max jl.1 jl.2 then
          (∑ n' ∈ S.resolved ∪ S.band,
            (CellScalars.sigmaWeightedPair
              (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n' p i q) jl.1 jl.2)
              (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n' p i q) jl.1 jl.2)
              (S.symWeight n' jl.1 jl.2) (S.antiWeight n' jl.1 jl.2)).re)
          + ∑ n' ∈ S.resolved,
            vecSq (fun i => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingVelocity c K R a n' p i) jl.1 jl.2)
              / S.velWeight n' jl.1 jl.2
          else 0) / (1 - R.farShare)
      ≤ CellScalars.sharpFarTerm c K S R B μ κ ζ v G σ τ jl := by
    intro jl
    unfold CellScalars.sharpFarTerm
    by_cases hf : S.degNear < max jl.1 jl.2
    · have hlt : S.degHigh < max jl.1 jl.2 := lt_of_le_of_lt (by omega) hf
      have hc : ∀ n : ℤ, n ∉ S.resolved ∨ S.degHigh < max jl.1 jl.2 := fun _ => Or.inr hlt
      simp only [hf, if_true]
      have sS := Finset.sum_le_sum fun (n : ℤ) (_ : n ∈ R.yModes) => (show
          -((symSq (fun a b => B.coef K (fun p => CellScalars.yFolded c K S κ ζ v G n p a b) jl.1 jl.2)
                  / S.symWeight n jl.1 jl.2
                + antiSq (fun a b => B.coef K (fun p => CellScalars.yFolded c K S κ ζ v G n p a b) jl.1 jl.2)
                  / S.antiWeight n jl.1 jl.2) / R.farShare)
            - (if n ∈ S.resolved ∪ S.band then
              (CellScalars.sigmaWeightedPair
                (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n p i q) jl.1 jl.2)
                (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n p i q) jl.1 jl.2)
                (S.symWeight n jl.1 jl.2) (S.antiWeight n jl.1 jl.2)).re / (1 - R.farShare) else 0)
          ≤ CellScalars.sharpStrainTerm c K S R B μ κ ζ v G σ n jl.1 jl.2 by
        unfold CellScalars.sharpStrainTerm
        rw [if_pos (hc n)]
        exact strain_far (sym_pos hd (hc n)) (anti_pos hd (hc n)) ht0 ht1 (σ n jl.1 jl.2) _ _ _)
      have sV := Finset.sum_le_sum fun (n : ℤ) (hn : n ∈ S.resolved) => (show
          -(vecSq (fun a => B.coef K (fun p => CellScalars.yVelocity c K S v G n p a) jl.1 jl.2)
                  / S.velWeight n jl.1 jl.2 / R.farShare)
            - vecSq (fun i => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingVelocity c K R a n p i) jl.1 jl.2)
              / S.velWeight n jl.1 jl.2 / (1 - R.farShare)
          ≤ CellScalars.sharpVelocityTerm c K S R B μ v G τ n jl.1 jl.2 by
        unfold CellScalars.sharpVelocityTerm
        rw [if_pos hlt.le]
        exact vel_far (vel_pos hd hn hlt.le) ht0 ht1 (τ n jl.1 jl.2) _ _)
      simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at sS sV
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hd.yModes_contain] at sS
      simp only [← Finset.sum_div] at sS sV
      simp only [hc, ↓reduceIte]
      rw [add_div, add_div]
      linarith
    · simp only [hf, if_false, zero_div, neg_zero, sub_zero, le_refl]
  have hsN := ((hsY.div_const R.farShare).neg).sub (hsW.div_const (1 - R.farShare))
  have hle := hsN.tsum_le_tsum hper hsF
  have e1 := Summable.tsum_sub ((hsY.div_const R.farShare).neg) (hsW.div_const (1 - R.farShare))
  rw [tsum_neg, tsum_div_const, tsum_div_const] at e1
  unfold CellScalars.farWeighted CellScalars.rowSquareFar
  linarith

end CellFormBoundInternal

theorem cellModeBound_of_sharp (h : CellSharpBoundStatement) : CellModeBoundStatement := by
  intro α hα1 hα2 k N c hc K S B Cl slots R hd hax x hx ζ μ hμ0
  obtain ⟨σ, τ, hsF, hsY, hsW, hmain⟩ := h α hα1 hα2 c hc K S B Cl R hd hax x hx ζ μ hμ0
  have hN := CellFormBoundInternal.near_bound hd x.2.2.2.1 ζ x.1 x.2.1 μ σ τ
  have hF := CellFormBoundInternal.far_bound' hd x.2.2.2.1 ζ x.1 x.2.1 μ σ τ hsF hsY hsW
  unfold CellScalars.sharpForm at hmain
  linarith

theorem cellFormBound_of_sharp (h1 : CellDensityModesStatement) (h5 : CellSharpBoundStatement) :
    CellFormBoundStatement :=
  cellFormBound_of_modes h1 (cellModeBound_of_sharp h5)

end CellAnalysis

end CellCert

end Breakdown
