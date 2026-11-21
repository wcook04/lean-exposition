import Breakdown.FracCell.SharpYChargeSt
import Breakdown.FracCell.ModeSquareIntegrable
import Breakdown.FracCell.ModeVelSquare

open MeasureTheory Set

noncomputable section


namespace Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal

open SteadyCert Assembly SharpParts Real
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal
open Breakdown.CellCert.CellAnalysis.ModeGradSquare.Internal

theorem sumSq_nonneg (s : Fin 3 → Fin 3 → ℂ) : 0 ≤ sumSq s := by unfold sumSq; positivity

theorem vecSq_nonneg (v : Fin 3 → ℂ) : 0 ≤ vecSq v := by unfold vecSq; positivity

theorem curlSq_nonneg (s : Fin 3 → Fin 3 → ℂ) : 0 ≤ curlSq s := by unfold curlSq; positivity

theorem curlSq_le (s : Fin 3 → Fin 3 → ℂ) : curlSq s ≤ 27 * sumSq s := by
  have h : ∀ i, ‖curlComp s i‖ ^ 2 ≤ 9 * sumSq s := by
    intro i
    have hc := ModeSquareIntegrable.Internal.combo_pt (fun j l => (CellCert.permSign i j l : ℂ)) (fun j l => s l j)
    have h0 : ∀ j l, ‖(CellCert.permSign i j l : ℂ)‖ ^ 2 ≤ 1 := by
      intro j l
      unfold CellCert.permSign
      split_ifs <;> simp
    have h1 : ∑ j : Fin 3, ∑ l : Fin 3, ‖(CellCert.permSign i j l : ℂ)‖ ^ 2 ≤ 9 := by
      calc ∑ j : Fin 3, ∑ l : Fin 3, ‖(CellCert.permSign i j l : ℂ)‖ ^ 2
          ≤ ∑ j : Fin 3, ∑ l : Fin 3, (1 : ℝ) :=
            Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => h0 j l
        _ = 9 := by simp; norm_num
    have h2 : ∑ j : Fin 3, ∑ l : Fin 3, ‖s l j‖ ^ 2 = sumSq s := by
      unfold sumSq; exact Finset.sum_comm
    unfold curlComp
    calc _ ≤ _ := hc
      _ ≤ 9 * sumSq s := by rw [h2]; exact mul_le_mul_of_nonneg_right h1 (sumSq_nonneg s)
  unfold curlSq
  calc ∑ i, ‖curlComp s i‖ ^ 2 ≤ ∑ _i : Fin 3, 9 * sumSq s := Finset.sum_le_sum fun i _ => h i
    _ = 27 * sumSq s := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

theorem nsq_sub (x y : ℂ) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_sub_le x y
  have h0 := norm_nonneg (x - y)
  nlinarith [mul_le_mul h h h0 (by positivity : (0 : ℝ) ≤ ‖x‖ + ‖y‖), sq_nonneg (‖x‖ - ‖y‖)]

theorem sumSq_sub (x y : Fin 3 → Fin 3 → ℂ) :
    sumSq (fun a b => x a b - y a b) ≤ 2 * sumSq x + 2 * sumSq y := by
  unfold sumSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun b _ => nsq_sub _ _

theorem vecSq_sub (x y : Fin 3 → ℂ) : vecSq (fun a => x a - y a) ≤ 2 * vecSq x + 2 * vecSq y := by
  unfold vecSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun a _ => nsq_sub _ _

theorem sqrt_mul_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.sqrt a * Real.sqrt b ≤ a + b := by
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb,
    Real.sqrt_nonneg a, Real.sqrt_nonneg b]

theorem supLoss_bd (lam g₀ g' ℓ : ℝ) (hℓ : 0 < ℓ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) :
    |supremumLoss lam g₀ g' ℓ s v| ≤
      (27 * |lam| + |Exterior.traceFreeConst| * |g₀| + |Exterior.traceFreeConst| * |g'| * (ℓ + 1 / ℓ)) *
        (sumSq s + vecSq v) := by
  have h1 := sumSq_nonneg s
  have h2 := vecSq_nonneg v
  have h3 := curlSq_nonneg s
  have h4 := curlSq_le s
  have h5 := sqrt_mul_le _ _ h1 h2
  have h6 : 0 ≤ Real.sqrt (sumSq s) * Real.sqrt (vecSq v) := by positivity
  unfold supremumLoss
  have e1 : |lam * curlSq s| ≤ 27 * |lam| * (sumSq s + vecSq v) := by
    rw [abs_mul, abs_of_nonneg h3]
    nlinarith [abs_nonneg lam]
  have e2 : |Exterior.traceFreeConst * g₀ * Real.sqrt (sumSq s) * Real.sqrt (vecSq v)| ≤
      |Exterior.traceFreeConst| * |g₀| * (sumSq s + vecSq v) := by
    rw [mul_assoc, abs_mul, abs_mul, abs_of_nonneg h6]
    exact mul_le_mul_of_nonneg_left h5 (by positivity)
  have e3 : |(1 / 2) * Exterior.traceFreeConst * g' * (ℓ * sumSq s + vecSq v / ℓ)| ≤
      |Exterior.traceFreeConst| * |g'| * (ℓ + 1 / ℓ) * (sumSq s + vecSq v) := by
    have hq : 0 ≤ ℓ * sumSq s + vecSq v / ℓ := by positivity
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hq, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    have hl : ℓ * sumSq s + vecSq v / ℓ ≤ (ℓ + 1 / ℓ) * (sumSq s + vecSq v) := by
      have : 0 ≤ 1 / ℓ := by positivity
      rw [div_eq_mul_one_div (vecSq v) ℓ]
      nlinarith
    have hA : 0 ≤ |Exterior.traceFreeConst| * |g'| := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hl hA]
  calc _ ≤ |lam * curlSq s + Exterior.traceFreeConst * g₀ * Real.sqrt (sumSq s) * Real.sqrt (vecSq v)|
        + |(1 / 2) * Exterior.traceFreeConst * g' * (ℓ * sumSq s + vecSq v / ℓ)| := abs_add_le _ _
    _ ≤ |lam * curlSq s| + |Exterior.traceFreeConst * g₀ * Real.sqrt (sumSq s) * Real.sqrt (vecSq v)|
        + |(1 / 2) * Exterior.traceFreeConst * g' * (ℓ * sumSq s + vecSq v / ℓ)| := by
          gcongr; exact abs_add_le _ _
    _ ≤ _ := by nlinarith

theorem cyl0_meas : Measurable (fun p : ℝ × ℝ => cylPoint p.1 0 p.2) := by
  have h : (fun p : ℝ × ℝ => cylPoint p.1 0 p.2) = cylArg ∘ (fun p : ℝ × ℝ => ((p.1, p.2), (0 : ℝ))) := rfl
  rw [h]
  exact cylArg_meas.comp ((measurable_fst.prodMk measurable_snd).prodMk measurable_const)

theorem proj_cont (K : CellBox) (d d' : ℕ) (F : ℝ × ℝ → ℂ) : Continuous (K.proj d d' F) := by
  unfold CellBox.proj
  split_ifs with h
  · exact poly_cont h.choose_spec.1
  · exact continuous_const

theorem continuous_curlSq : Continuous curlSq := by
  unfold curlSq curlComp; fun_prop

theorem continuous_sumSq : Continuous sumSq := by
  unfold sumSq; fun_prop

theorem continuous_vecSq : Continuous vecSq := by
  unfold vecSq; fun_prop

end Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal



namespace Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal

open SteadyCert Assembly SharpParts Real
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal
open Breakdown.CellCert.CellAnalysis.ModeGradSquare.Internal

theorem r_nonneg {K : CellBox} (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) : 0 ≤ p.1 :=
  le_trans hK.r_order.1 hp.1.1

theorem lw_nonneg {K : CellBox} (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) : 0 ≤ K.lineWeight p.1 := by
  unfold CellBox.lineWeight
  split_ifs
  · exact r_nonneg hK hp
  · exact zero_le_one

theorem r_le_lw {K : CellBox} (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) :
    p.1 ≤ max 1 K.r₂ * K.lineWeight p.1 := by
  have h0 := r_nonneg hK hp
  unfold CellBox.lineWeight
  split_ifs
  · nlinarith [le_max_left 1 K.r₂]
  · rw [mul_one]; exact le_trans hp.1.2 (le_max_right _ _)

theorem lw_aem (K : CellBox) : AEMeasurable (fun p : ℝ × ℝ => K.lineWeight p.1) (volume.restrict K.rect) :=
  ((lineWeight_cont K).comp continuous_fst).measurable.aemeasurable

theorem r_aem (K : CellBox) : AEMeasurable (fun p : ℝ × ℝ => p.1) (volume.restrict K.rect) :=
  measurable_fst.aemeasurable

theorem int_mono {K : CellBox} {f g : ℝ × ℝ → ℝ} (hg : IntegrableOn g K.rect)
    (hf : AEStronglyMeasurable f (volume.restrict K.rect)) (h : ∀ p ∈ K.rect, |f p| ≤ g p) :
    IntegrableOn f K.rect :=
  Integrable.mono' hg hf ((ae_restrict_iff' (rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => by
    rw [Real.norm_eq_abs]; exact h p hp))

theorem abs_int_le {K : CellBox} {f g : ℝ × ℝ → ℝ} (hg : IntegrableOn g K.rect)
    (h : ∀ p ∈ K.rect, |f p| ≤ g p) : |∫ p in K.rect, f p| ≤ ∫ p in K.rect, g p := by
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le hg ((ae_restrict_iff' (rect_meas K)).2
    (Filter.Eventually.of_forall fun p hp => by rw [Real.norm_eq_abs]; exact h p hp))

theorem wt_bound {w lw d Gq Lq E B R M : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ R * lw) (hB : 0 ≤ B)
    (hd : |d| ≤ B * E) (hE : E ≤ M * (Gq + Lq)) : |w * d| ≤ (R * B * M) * (lw * Gq + lw * Lq) := by
  rw [abs_mul, abs_of_nonneg hw0]
  have hE0 : 0 ≤ B * E := le_trans (abs_nonneg _) hd
  calc w * |d| ≤ w * (B * E) := mul_le_mul_of_nonneg_left hd hw0
    _ ≤ (R * lw) * (B * (M * (Gq + Lq))) :=
        mul_le_mul hw (mul_le_mul_of_nonneg_left hE hB) hE0 (le_trans hw0 hw)
    _ = _ := by ring

theorem summ_of {F g l : ℤ → ℝ} (A : ℝ) (T : Finset ℤ) (hg : Summable g) (hl : ∀ n ∉ T, l n = 0)
    (h : ∀ n, |F n| ≤ A * (g n + l n)) : Summable F := by
  have hl' : Summable (fun n => |A| * |l n|) :=
    summable_of_ne_finset_zero (s := T) fun n hn => by simp [hl n hn]
  refine Summable.of_norm_bounded ((hg.abs.mul_left |A|).add hl') fun n => ?_
  rw [Real.norm_eq_abs]
  refine (h n).trans ?_
  calc A * (g n + l n) ≤ |A * (g n + l n)| := le_abs_self _
    _ = |A| * |g n + l n| := abs_mul _ _
    _ ≤ |A| * (|g n| + |l n|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
    _ = |A| * |g n| + |A| * |l n| := by ring

theorem pairVec_cont (i : Fin 12) :
    Continuous (fun q : (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ) => pairVec q.1 q.2 i) := by
  unfold pairVec
  split_ifs
  · exact (continuous_apply _).comp ((continuous_apply _).comp continuous_fst)
  · exact (continuous_apply _).comp continuous_snd

theorem pairVec_sq_le (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (i : Fin 12) :
    ‖pairVec s v i‖ ^ 2 ≤ sumSq s + vecSq v := by
  have h1 := sumSq_nonneg s
  have h2 := vecSq_nonneg v
  unfold pairVec
  split_ifs
  · have e1 : ‖s ⟨i.val / 3, by omega⟩ ⟨i.val % 3, Nat.mod_lt _ (by norm_num)⟩‖ ^ 2 ≤
        ∑ b : Fin 3, ‖s ⟨i.val / 3, by omega⟩ b‖ ^ 2 :=
      Finset.single_le_sum (f := fun b => ‖s ⟨i.val / 3, by omega⟩ b‖ ^ 2) (fun b _ => by positivity)
        (Finset.mem_univ _)
    have e2 : ∑ b : Fin 3, ‖s ⟨i.val / 3, by omega⟩ b‖ ^ 2 ≤ sumSq s :=
      Finset.single_le_sum (f := fun a => ∑ b : Fin 3, ‖s a b‖ ^ 2) (fun a _ => by positivity)
        (Finset.mem_univ _)
    linarith
  · have e1 : ‖v ⟨i.val - 9, by omega⟩‖ ^ 2 ≤ vecSq v :=
      Finset.single_le_sum (f := fun a => ‖v a‖ ^ 2) (fun a _ => by positivity) (Finset.mem_univ _)
    linarith

theorem term_le (u w : ℂ) (A : ℂ) (CA : ℝ) (hA : ‖A‖ ≤ CA) (EU EW : ℝ) (hu : ‖u‖ ^ 2 ≤ EU) (hw : ‖w‖ ^ 2 ≤ EW) :
    ‖(starRingEnd ℂ) u * A * w‖ ≤ CA * (EU + EW) := by
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have h0 : 0 ≤ CA := le_trans (norm_nonneg _) hA
  have h1 : ‖u‖ * ‖w‖ ≤ EU + EW := by nlinarith [sq_nonneg (‖u‖ - ‖w‖), norm_nonneg u, norm_nonneg w]
  calc ‖u‖ * ‖A‖ * ‖w‖ = ‖A‖ * (‖u‖ * ‖w‖) := by ring
    _ ≤ CA * (EU + EW) := mul_le_mul hA h1 (by positivity) h0

theorem sesq_bd (A : Matrix (Fin 12) (Fin 12) ℂ) (CA : ℝ) (hA : ∀ i j, ‖A i j‖ ≤ CA) (U W : Fin 12 → ℂ)
    (EU EW : ℝ) (hU : ∀ i, ‖U i‖ ^ 2 ≤ EU) (hW : ∀ i, ‖W i‖ ^ 2 ≤ EW) :
    |(∑ i, ∑ j, ((starRingEnd ℂ) (U i) * A i j * W j + (starRingEnd ℂ) (W i) * A i j * U j)).re|
      ≤ 288 * CA * (EU + EW) := by
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ i j, ‖(starRingEnd ℂ) (U i) * A i j * W j + (starRingEnd ℂ) (W i) * A i j * U j‖
      ≤ 2 * CA * (EU + EW) := by
    intro i j
    refine (norm_add_le _ _).trans ?_
    have a1 := term_le (U i) (W j) (A i j) CA (hA i j) EU EW (hU i) (hW j)
    have a2 := term_le (W i) (U j) (A i j) CA (hA i j) EW EU (hW i) (hU j)
    linarith
  calc ∑ i, ‖∑ j, ((starRingEnd ℂ) (U i) * A i j * W j + (starRingEnd ℂ) (W i) * A i j * U j)‖
      ≤ ∑ i : Fin 12, ∑ j : Fin 12, 2 * CA * (EU + EW) :=
        Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => h i j)
    _ = 288 * CA * (EU + EW) := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

end Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly

def ModeSeriesStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ), 1 ≤ m →
    ∀ (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
      IsSecondOrderField m v G H →
      (∀ a : Fin 3, Summable (fun n : ℤ => ∫ p in K.rect, K.lineWeight p.1 * ‖modeVec m n v p.1 p.2 a‖ ^ 2)) ∧
      ∀ a b : Fin 3, Summable (fun n : ℤ =>
        (1 + modeNumber m n ^ 2) * ∫ p in K.rect, K.lineWeight p.1 * ‖gradMode m n G a b p‖ ^ 2)

def AbsorbGrowthStatement : Prop :=
  ∀ (α : ℝ) {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars), IsCellBox K →
    IsCellScalars α c K S →
    ∃ C : ℝ, ∀ n ∉ S.resolved, |S.curlAbsorb n| + |S.strainAbsorb n| ≤ C * (1 + modeNumber c.order n ^ 2)

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal

open SteadyCert Assembly SharpParts Real
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal
open Breakdown.CellCert.CellAnalysis.ModeGradSquare.Internal

section Data

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

theorem lowGrad_cont (n : ℤ) : Continuous (fun p => lowGrad c K S x n p) := by
  by_cases hn : n ∈ S.resolved
  · simp only [lowGrad, hn, if_true]
    exact continuous_pi fun a => continuous_pi fun b => by
      simpa only [CellBox.lowStrainAt, CellBox.lowStrain] using
        proj_cont K S.degHigh S.degHigh (gradMode c.order n x.2.1 a b)
  · simp only [lowGrad, hn, if_false]
    exact continuous_const

theorem lowVel_cont (n : ℤ) : Continuous (fun p => lowVel c K S x n p) := by
  by_cases hn : n ∈ S.resolved
  · simp only [lowVel, hn, if_true]
    exact continuous_pi fun a => by
      simpa only [CellBox.lowVelocityAt, CellBox.lowVelocity] using
        proj_cont K (S.degHigh - 1) (S.degHigh - 1) (fun p => modeVec c.order n x.1 p.1 p.2 a)
  · simp only [lowVel, hn, if_false]
    exact continuous_const

theorem low_zero (n : ℤ) (hn : n ∉ S.resolved) (p : ℝ × ℝ) :
    sumSq (lowGrad c K S x n p) + vecSq (lowVel c K S x n p) = 0 := by
  simp [lowGrad, lowVel, hn, sumSq, vecSq]

theorem gmv_aem (hK : IsCellBox K) (hG : AEStronglyMeasurable x.2.1 volume) (n : ℤ) :
    AEMeasurable (fun p => fun a b => gradMode c.order n x.2.1 a b p) (volume.restrict K.rect) :=
  aemeasurable_pi_lambda _ fun a => aemeasurable_pi_lambda _ fun b => (gm_meas K hK _ n hG a b).aemeasurable

theorem mv_aem (hK : IsCellBox K) (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1) (n : ℤ) :
    AEMeasurable (fun p : ℝ × ℝ => modeVec c.order n x.1 p.1 p.2) (volume.restrict K.rect) :=
  aemeasurable_pi_lambda _ fun a => (modeVelSquare K hK _ _ _ _ hs n a).1.aemeasurable

theorem sG_aem (hK : IsCellBox K) (hG : AEStronglyMeasurable x.2.1 volume) (n : ℤ) :
    AEMeasurable (fun p => sharpGrad c K S x n p) (volume.restrict K.rect) :=
  aemeasurable_pi_lambda _ fun a => aemeasurable_pi_lambda _ fun b =>
    (gm_meas K hK _ n hG a b).aemeasurable.sub
      ((continuous_apply b).comp ((continuous_apply a).comp (lowGrad_cont c K S x n))).measurable.aemeasurable

theorem sV_aem (hK : IsCellBox K) (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1) (n : ℤ) :
    AEMeasurable (fun p => sharpVel c K S x n p) (volume.restrict K.rect) :=
  aemeasurable_pi_lambda _ fun a =>
    (modeVelSquare K hK _ _ _ _ hs n a).1.aemeasurable.sub
      ((continuous_apply a).comp (lowVel_cont c K S x n)).measurable.aemeasurable

theorem sharp_le (n : ℤ) (p : ℝ × ℝ) :
    sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p) ≤
      2 * ((sumSq (fun a b => gradMode c.order n x.2.1 a b p) + vecSq (modeVec c.order n x.1 p.1 p.2))
        + (sumSq (lowGrad c K S x n p) + vecSq (lowVel c K S x n p))) := by
  have h1 := sumSq_sub (fun a b => gradMode c.order n x.2.1 a b p) (lowGrad c K S x n p)
  have h2 := vecSq_sub (modeVec c.order n x.1 p.1 p.2) (lowVel c K S x n p)
  have e1 : sharpGrad c K S x n p = fun a b => gradMode c.order n x.2.1 a b p - lowGrad c K S x n p a b := rfl
  have e2 : sharpVel c K S x n p = fun a => modeVec c.order n x.1 p.1 p.2 a - lowVel c K S x n p a := rfl
  rw [e1, e2]
  linarith

theorem gq_int (hK : IsCellBox K) (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1) (n : ℤ) :
    IntegrableOn (fun p => K.lineWeight p.1 *
      (sumSq (fun a b => gradMode c.order n x.2.1 a b p) + vecSq (modeVec c.order n x.1 p.1 p.2))) K.rect := by
  have e : (fun p : ℝ × ℝ => K.lineWeight p.1 *
      (sumSq (fun a b => gradMode c.order n x.2.1 a b p) + vecSq (modeVec c.order n x.1 p.1 p.2))) =
      fun p => (∑ a : Fin 3, ∑ b : Fin 3, K.lineWeight p.1 * ‖gradMode c.order n x.2.1 a b p‖ ^ 2)
        + ∑ a : Fin 3, K.lineWeight p.1 * ‖modeVec c.order n x.1 p.1 p.2 a‖ ^ 2 := by
    funext p
    simp only [sumSq, vecSq, mul_add, Finset.mul_sum]
  rw [e]
  exact (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (modeGradSquare K hK _ _ _ _ hs n a b).2).add
      (integrable_finsetSum _ fun a _ => (modeVelSquare K hK _ _ _ _ hs n a).2)

theorem lq_cont (n : ℤ) : Continuous (fun p : ℝ × ℝ => K.lineWeight p.1 *
    (sumSq (lowGrad c K S x n p) + vecSq (lowVel c K S x n p))) :=
  ((lineWeight_cont K).comp continuous_fst).mul
    ((continuous_sumSq.comp (lowGrad_cont c K S x n)).add (continuous_vecSq.comp (lowVel_cont c K S x n)))

theorem lq_int (n : ℤ) : IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 *
    (sumSq (lowGrad c K S x n p) + vecSq (lowVel c K S x n p))) K.rect :=
  (lq_cont c K S x n).continuousOn.integrableOn_compact (rect_compact K)

theorem gq_summable (hK : IsCellBox K) (hm : 1 ≤ c.order) (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1)
    (hM : ModeSeriesStatement) :
    Summable (fun n : ℤ => ∫ p in K.rect, K.lineWeight p.1 *
      (sumSq (fun a b => gradMode c.order n x.2.1 a b p) + vecSq (modeVec c.order n x.1 p.1 p.2))) := by
  obtain ⟨hv, hg⟩ := hM K hK c.order hm _ _ _ hs
  have hg' : ∀ a b : Fin 3, Summable (fun n : ℤ =>
      ∫ p in K.rect, K.lineWeight p.1 * ‖gradMode c.order n x.2.1 a b p‖ ^ 2) := by
    intro a b
    refine Summable.of_nonneg_of_le (fun n => setIntegral_nonneg (rect_meas K) fun p hp =>
      mul_nonneg (lw_nonneg hK hp) (sq_nonneg _)) (fun n => ?_) (hg a b)
    have h0 : 0 ≤ ∫ p in K.rect, K.lineWeight p.1 * ‖gradMode c.order n x.2.1 a b p‖ ^ 2 :=
      setIntegral_nonneg (rect_meas K) fun p hp => mul_nonneg (lw_nonneg hK hp) (sq_nonneg _)
    have h1 : 0 ≤ modeNumber c.order n ^ 2 := sq_nonneg _
    nlinarith
  have e : ∀ n : ℤ, ∫ p in K.rect, K.lineWeight p.1 *
      (sumSq (fun a b => gradMode c.order n x.2.1 a b p) + vecSq (modeVec c.order n x.1 p.1 p.2)) =
      (∑ a : Fin 3, ∑ b : Fin 3, ∫ p in K.rect, K.lineWeight p.1 * ‖gradMode c.order n x.2.1 a b p‖ ^ 2)
        + ∑ a : Fin 3, ∫ p in K.rect, K.lineWeight p.1 * ‖modeVec c.order n x.1 p.1 p.2 a‖ ^ 2 := by
    intro n
    simp only [sumSq, vecSq, mul_add, Finset.mul_sum]
    rw [integral_add (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      (modeGradSquare K hK _ _ _ _ hs n a b).2)
      (integrable_finsetSum _ fun a _ => (modeVelSquare K hK _ _ _ _ hs n a).2)]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      (modeGradSquare K hK _ _ _ _ hs n a b).2]
    rw [integral_finsetSum _ fun a _ => (modeVelSquare K hK _ _ _ _ hs n a).2]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => (modeGradSquare K hK _ _ _ _ hs n a b).2]
  refine Summable.congr ?_ fun n => (e n).symm
  exact (summable_sum fun a _ => summable_sum fun b _ => hg' a b).add (summable_sum fun a _ => hv a)

end Data

end Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal



namespace Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal

open SteadyCert Assembly SharpParts Real
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal
open Breakdown.CellCert.CellAnalysis.ModeGradSquare.Internal

section Dens

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

theorem dens_int (hK : IsCellBox K) (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1)
    (w : ℝ × ℝ → ℝ) (hwm : AEMeasurable w (volume.restrict K.rect)) (hw0 : ∀ p ∈ K.rect, 0 ≤ w p)
    (hwR : ∀ p ∈ K.rect, w p ≤ max 1 K.r₂ * K.lineWeight p.1)
    (n : ℤ) (d : ℝ × ℝ → ℝ) (hdm : AEMeasurable d (volume.restrict K.rect)) (B : ℝ) (hB : 0 ≤ B)
    (hd : ∀ p ∈ K.rect, |d p| ≤ B * ((sumSq (fun a b => gradMode c.order n x.2.1 a b p) + vecSq (modeVec c.order n x.1 p.1 p.2))
      + (sumSq (lowGrad c K S x n p) + vecSq (lowVel c K S x n p)))) :
    IntegrableOn (fun p => w p * d p) K.rect ∧
      |∫ p in K.rect, w p * d p| ≤ (max 1 K.r₂ * B * 1) *
        ((∫ p in K.rect, K.lineWeight p.1 *
          (sumSq (fun a b => gradMode c.order n x.2.1 a b p) + vecSq (modeVec c.order n x.1 p.1 p.2)))
        + ∫ p in K.rect, K.lineWeight p.1 * (sumSq (lowGrad c K S x n p) + vecSq (lowVel c K S x n p))) := by
  have hb : ∀ p ∈ K.rect, |w p * d p| ≤ (max 1 K.r₂ * B * 1) *
      (K.lineWeight p.1 * (sumSq (fun a b => gradMode c.order n x.2.1 a b p) + vecSq (modeVec c.order n x.1 p.1 p.2))
        + K.lineWeight p.1 * (sumSq (lowGrad c K S x n p) + vecSq (lowVel c K S x n p))) := by
    intro p hp
    exact wt_bound (hw0 p hp) (hwR p hp) hB (hd p hp) (by rw [one_mul])
  have hI := ((gq_int c K x hK hs n).add (lq_int c K S x n)).const_mul (max 1 K.r₂ * B * 1)
  refine ⟨int_mono hI (hwm.mul hdm).aestronglyMeasurable hb, ?_⟩
  refine (abs_int_le hI hb).trans (le_of_eq ?_)
  rw [integral_const_mul]
  congr 1
  exact integral_add (gq_int c K x hK hs n) (lq_int c K S x n)

theorem dens_sum (hK : IsCellBox K) (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1) (hm : 1 ≤ c.order)
    (hM : ModeSeriesStatement)
    (w : ℝ × ℝ → ℝ) (hwm : AEMeasurable w (volume.restrict K.rect)) (hw0 : ∀ p ∈ K.rect, 0 ≤ w p)
    (hwR : ∀ p ∈ K.rect, w p ≤ max 1 K.r₂ * K.lineWeight p.1)
    (d : ℤ → ℝ × ℝ → ℝ) (hdm : ∀ n, AEMeasurable (d n) (volume.restrict K.rect)) (B : ℝ) (hB : 0 ≤ B)
    (hd : ∀ n, ∀ p ∈ K.rect, |d n p| ≤ B * ((sumSq (fun a b => gradMode c.order n x.2.1 a b p)
      + vecSq (modeVec c.order n x.1 p.1 p.2)) + (sumSq (lowGrad c K S x n p) + vecSq (lowVel c K S x n p)))) :
    (∀ n, IntegrableOn (fun p => w p * d n p) K.rect) ∧ Summable (fun n => ∫ p in K.rect, w p * d n p) := by
  refine ⟨fun n => (dens_int c K S x hK hs w hwm hw0 hwR n (d n) (hdm n) B hB (hd n)).1, ?_⟩
  refine summ_of (max 1 K.r₂ * B * 1) S.resolved (gq_summable c K x hK hm hs hM) (fun n hn => ?_)
    fun n => (dens_int c K S x hK hs w hwm hw0 hwR n (d n) (hdm n) B hB (hd n)).2
  have e : (fun p : ℝ × ℝ => K.lineWeight p.1 * (sumSq (lowGrad c K S x n p) + vecSq (lowVel c K S x n p))) =
      fun _ => 0 := by
    funext p; rw [low_zero c K S x n hn p, mul_zero]
  simp only [e, integral_zero]

end Dens

end Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal



namespace Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal

open SteadyCert Assembly SharpParts Real
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal
open Breakdown.CellCert.CellAnalysis.ModeGradSquare.Internal

theorem form_bd {k N : ℕ} (c : FracCellData k N) (α : ℝ) (p : ℝ × ℝ) (s : Fin 3 → Fin 3 → ℂ) (W : ℝ)
    (hW : |CellScalars.sampleWeight c p| ≤ W) :
    |CellScalars.densityForm c α p s| ≤
      (27 * |1 - 3 / (4 * α) - c.curlWeight| + (|c.curlWeight| + |c.coercivity| * W)) * sumSq s := by
  have h1 := sumSq_nonneg s
  have h2 := curlSq_nonneg s
  have h3 := curlSq_le s
  unfold CellScalars.densityForm
  have e1 : |(1 - 3 / (4 * α) - c.curlWeight) * curlSq s| ≤ 27 * |1 - 3 / (4 * α) - c.curlWeight| * sumSq s := by
    rw [abs_mul, abs_of_nonneg h2]; nlinarith [abs_nonneg (1 - 3 / (4 * α) - c.curlWeight)]
  have e2 : |c.curlWeight - c.coercivity * CellScalars.sampleWeight c p| ≤ |c.curlWeight| + |c.coercivity| * W := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    gcongr
  have e3 : |(c.curlWeight - c.coercivity * CellScalars.sampleWeight c p) * sumSq s| ≤
      (|c.curlWeight| + |c.coercivity| * W) * sumSq s := by
    rw [abs_mul, abs_of_nonneg h1]; exact mul_le_mul_of_nonneg_right e2 h1
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add e1 e3
    _ = _ := by ring

theorem pen_bd (S : CellScalars) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) :
    |S.penalty s v| ≤ (|S.penaltyStrain| + 27 * |S.penaltyCurl| + |S.penaltyVelocity|) * (sumSq s + vecSq v) := by
  have h1 := sumSq_nonneg s
  have h2 := curlSq_nonneg s
  have h3 := curlSq_le s
  have h4 := vecSq_nonneg v
  unfold CellScalars.penalty
  have e1 : |S.penaltyStrain * sumSq s| ≤ |S.penaltyStrain| * sumSq s := by rw [abs_mul, abs_of_nonneg h1]
  have e2 : |S.penaltyCurl * curlSq s| ≤ 27 * |S.penaltyCurl| * sumSq s := by
    rw [abs_mul, abs_of_nonneg h2]; nlinarith [abs_nonneg S.penaltyCurl]
  have e3 : |S.penaltyVelocity * vecSq v| ≤ |S.penaltyVelocity| * vecSq v := by rw [abs_mul, abs_of_nonneg h4]
  have t1 := abs_add_le (S.penaltyStrain * sumSq s + S.penaltyCurl * curlSq s) (S.penaltyVelocity * vecSq v)
  have t2 := abs_add_le (S.penaltyStrain * sumSq s) (S.penaltyCurl * curlSq s)
  have a1 := abs_nonneg S.penaltyStrain
  have a2 := abs_nonneg S.penaltyCurl
  have a3 := abs_nonneg S.penaltyVelocity
  nlinarith

theorem absorb_bd (ca sa va : ℝ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (P : Prop) [Decidable P] :
    |ca * curlSq s + sa * sumSq s + (if P then va * vecSq v else 0)| ≤
      (27 * |ca| + |sa| + |va|) * (sumSq s + vecSq v) := by
  have h1 := sumSq_nonneg s
  have h2 := curlSq_nonneg s
  have h3 := curlSq_le s
  have h4 := vecSq_nonneg v
  have e1 : |ca * curlSq s| ≤ 27 * |ca| * sumSq s := by
    rw [abs_mul, abs_of_nonneg h2]; nlinarith [abs_nonneg ca]
  have e2 : |sa * sumSq s| ≤ |sa| * sumSq s := by rw [abs_mul, abs_of_nonneg h1]
  have e3 : |(if P then va * vecSq v else 0)| ≤ |va| * vecSq v := by
    split_ifs
    · rw [abs_mul, abs_of_nonneg h4]
    · simp only [abs_zero]; positivity
  have t1 := abs_add_le (ca * curlSq s + sa * sumSq s) (if P then va * vecSq v else 0)
  have t2 := abs_add_le (ca * curlSq s) (sa * sumSq s)
  have a1 := abs_nonneg ca
  have a2 := abs_nonneg sa
  have a3 := abs_nonneg va
  nlinarith

theorem sesqV_bd (A : Matrix (Fin 12) (Fin 12) ℂ) (CA : ℝ) (hA : ∀ i j, ‖A i j‖ ≤ CA) (U : Fin 12 → ℂ)
    (EU : ℝ) (hU : ∀ i, ‖U i‖ ^ 2 ≤ EU) : |sesqValue A U| ≤ 144 * CA * (EU + EU) := by
  unfold sesqValue
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖∑ j, (starRingEnd ℂ) (U i) * A i j * U j‖
      ≤ ∑ i : Fin 12, ∑ j : Fin 12, CA * (EU + EU) :=
        Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
          term_le (U i) (U j) (A i j) CA (hA i j) EU EU (hU i) (hU j))
    _ = 144 * CA * (EU + EU) := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

end Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal



namespace Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal

open SteadyCert Assembly SharpParts Real
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal
open Breakdown.CellCert.CellAnalysis.ModeGradSquare.Internal

section Main

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

theorem sharp_bd (n : ℤ) (p : ℝ × ℝ) (B : ℝ) (hB : 0 ≤ B) (d : ℝ)
    (hd : |d| ≤ B * (sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p))) :
    |d| ≤ (2 * B) * ((sumSq (fun a b => gradMode c.order n x.2.1 a b p) + vecSq (modeVec c.order n x.1 p.1 p.2))
      + (sumSq (lowGrad c K S x n p) + vecSq (lowVel c K S x n p))) := by
  have h := sharp_le c K S x n p
  calc |d| ≤ B * (sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p)) := hd
    _ ≤ B * (2 * ((sumSq (fun a b => gradMode c.order n x.2.1 a b p) + vecSq (modeVec c.order n x.1 p.1 p.2))
      + (sumSq (lowGrad c K S x n p) + vecSq (lowVel c K S x n p)))) := mul_le_mul_of_nonneg_left h hB
    _ = _ := by ring

include S in
theorem dAt_facts (α : ℝ) (hc : IsFormData α c) (hK : IsCellBox K)
    (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1) (hm : 1 ≤ c.order) (hM : ModeSeriesStatement) :
    (∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * densityAt c x α n p) K.rect) ∧
      Summable (fun n : ℤ => ∫ p in K.rect, p.1 * densityAt c x α n p) := by
  have hwt : ∀ p, |CellScalars.sampleWeight c p| ≤ |c.weightMax| := fun p => by
    have h1 := hc.base.weight_lower (cylPoint p.1 0 p.2)
    have h2 := hc.base.weight_upper (cylPoint p.1 0 p.2)
    have h3 := hc.base.weightMin_pos
    unfold CellScalars.sampleWeight
    exact abs_le.2 ⟨by linarith [abs_nonneg c.weightMax], by linarith [le_abs_self c.weightMax]⟩
  have hB0 : 0 ≤ 27 * |1 - 3 / (4 * α) - c.curlWeight| + (|c.curlWeight| + |c.coercivity| * |c.weightMax|) := by
    positivity
  refine dens_sum c K S x hK hs hm hM (fun p => p.1) (r_aem K) (fun p hp => r_nonneg hK hp)
    (fun p hp => r_le_lw hK hp) (fun n p => densityAt c x α n p) (fun n => ?_) _ hB0 (fun n p hp => ?_)
  · unfold densityAt CellScalars.densityForm CellScalars.sampleWeight
    have hg := gmv_aem c K x hK hs.measurable_gradient n
    exact ((continuous_curlSq.measurable.comp_aemeasurable hg).const_mul _).add
      ((((hc.base.weight_measurable.comp cyl0_meas).const_mul c.coercivity).const_sub c.curlWeight).aemeasurable.mul
        (continuous_sumSq.measurable.comp_aemeasurable hg))
  · have h := form_bd c α p (fun a b => gradMode c.order n x.2.1 a b p) _ (hwt p)
    have l1 := vecSq_nonneg (modeVec c.order n x.1 p.1 p.2)
    have l2 := sumSq_nonneg (lowGrad c K S x n p)
    have l3 := vecSq_nonneg (lowVel c K S x n p)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hB0)
    linarith

theorem sup_facts (α : ℝ) (hK : IsCellBox K) (hS : IsCellScalars α c K S)
    (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1) (hm : 1 ≤ c.order) (hM : ModeSeriesStatement) :
    (∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * supDensity c K S x n p) K.rect) ∧
      Summable (fun n : ℤ => ∫ p in K.rect, p.1 * supDensity c K S x n p) := by
  obtain ⟨_, ⟨hsbm, C1, hC1⟩, ⟨hmgm, C2, hC2⟩, ⟨hwgm, C3, hC3⟩⟩ := hS.data_regular
  have hℓ := hS.splitLength_pos
  have hB0 : 0 ≤ 27 * max C1 0 + |Exterior.traceFreeConst| * max C2 0 +
      |Exterior.traceFreeConst| * max C3 0 * (S.splitLength + 1 / S.splitLength) := by positivity
  refine dens_sum c K S x hK hs hm hM (fun p => p.1) (r_aem K) (fun p hp => r_nonneg hK hp)
    (fun p hp => r_le_lw hK hp) (fun n p => supDensity c K S x n p) (fun n => ?_) _ (by positivity)
    (fun n p hp => sharp_bd c K S x n p _ hB0 _ ?_)
  · unfold supDensity supremumLoss
    have hG := sG_aem c K S x hK hs.measurable_gradient n
    have hV := sV_aem c K S x hK hs n
    have h1 := continuous_curlSq.measurable.comp_aemeasurable hG
    have h2 := continuous_sumSq.measurable.comp_aemeasurable hG
    have h3 := continuous_vecSq.measurable.comp_aemeasurable hV
    have h4 := Real.continuous_sqrt.measurable.comp_aemeasurable h2
    have h5 := Real.continuous_sqrt.measurable.comp_aemeasurable h3
    exact ((hsbm.aemeasurable.mul h1).add (((hmgm.aemeasurable.const_mul _).mul h4).mul h5)).add
      ((hwgm.aemeasurable.const_mul _).mul ((h2.const_mul _).add (h3.div_const _)))
  · have h := supLoss_bd (S.strainBound p) (S.meanGradBound p) (S.waveGradBound p) S.splitLength hℓ
      (sharpGrad c K S x n p) (sharpVel c K S x n p)
    have q1 := (hC1 p hp).trans (le_max_left C1 0)
    have q2 := (hC2 p hp).trans (le_max_left C2 0)
    have q3 := (hC3 p hp).trans (le_max_left C3 0)
    have hq : 0 ≤ S.splitLength + 1 / S.splitLength := by positivity
    have hle : 27 * |S.strainBound p| + |Exterior.traceFreeConst| * |S.meanGradBound p|
        + |Exterior.traceFreeConst| * |S.waveGradBound p| * (S.splitLength + 1 / S.splitLength) ≤
        27 * max C1 0 + |Exterior.traceFreeConst| * max C2 0 +
          |Exterior.traceFreeConst| * max C3 0 * (S.splitLength + 1 / S.splitLength) := by
      gcongr
    have hE := add_nonneg (sumSq_nonneg (sharpGrad c K S x n p)) (vecSq_nonneg (sharpVel c K S x n p))
    exact h.trans (mul_le_mul_of_nonneg_right hle hE)

theorem pen_facts (hK : IsCellBox K)
    (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1) (hm : 1 ≤ c.order) (hM : ModeSeriesStatement) :
    (∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * penaltyDensity c K S x n p) K.rect) ∧
      Summable (fun n : ℤ => ∫ p in K.rect, p.1 * penaltyDensity c K S x n p) := by
  have hB0 : 0 ≤ |S.penaltyStrain| + 27 * |S.penaltyCurl| + |S.penaltyVelocity| := by positivity
  refine dens_sum c K S x hK hs hm hM (fun p => p.1) (r_aem K) (fun p hp => r_nonneg hK hp)
    (fun p hp => r_le_lw hK hp) (fun n p => penaltyDensity c K S x n p) (fun n => ?_) _ (by positivity)
    (fun n p hp => sharp_bd c K S x n p _ hB0 _ ?_)
  · by_cases hn : n ∈ S.resolved ∪ S.band
    · simp only [penaltyDensity, hn, if_true]
      exact aemeasurable_const
    · simp only [penaltyDensity, hn, if_false]
      unfold CellScalars.penalty
      have hG := sG_aem c K S x hK hs.measurable_gradient n
      have hV := sV_aem c K S x hK hs n
      exact (((continuous_sumSq.measurable.comp_aemeasurable hG).const_mul _).add
        ((continuous_curlSq.measurable.comp_aemeasurable hG).const_mul _)).add
          ((continuous_vecSq.measurable.comp_aemeasurable hV).const_mul _)
  · by_cases hn : n ∈ S.resolved ∪ S.band
    · simp only [penaltyDensity, hn, if_true, abs_zero]
      exact mul_nonneg hB0 (add_nonneg (sumSq_nonneg _) (vecSq_nonneg _))
    · simp only [penaltyDensity, hn, if_false]
      exact pen_bd S _ _

end Main

end Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal



namespace Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal

open SteadyCert Assembly SharpParts Real
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal
open Breakdown.CellCert.CellAnalysis.ModeGradSquare.Internal

section Rest

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

theorem absorb_facts (α : ℝ) (hK : IsCellBox K) (hS : IsCellScalars α c K S)
    (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1) (hm : 1 ≤ c.order) (hM : ModeSeriesStatement)
    (hA : AbsorbGrowthStatement) :
    (∀ n, IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * absorbDensity c K S x n p) K.rect) ∧
      Summable (fun n : ℤ => ∫ p in K.rect, K.lineWeight p.1 * absorbDensity c K S x n p) := by
  have hwR : ∀ p ∈ K.rect, K.lineWeight p.1 ≤ max 1 K.r₂ * K.lineWeight p.1 := fun p hp => by
    have := lw_nonneg hK hp
    nlinarith [le_max_left 1 K.r₂]
  have hdm : ∀ n, AEMeasurable (fun p => absorbDensity c K S x n p) (volume.restrict K.rect) := by
    intro n
    have hG := sG_aem c K S x hK hs.measurable_gradient n
    have hV := sV_aem c K S x hK hs n
    by_cases hn : n ∈ S.resolved
    · simp only [absorbDensity, hn, if_true]
      exact (((continuous_curlSq.measurable.comp_aemeasurable hG).const_mul _).add
        ((continuous_sumSq.measurable.comp_aemeasurable hG).const_mul _)).add
          ((continuous_vecSq.measurable.comp_aemeasurable hV).const_mul _)
    · simp only [absorbDensity, hn, if_false, add_zero]
      exact ((continuous_curlSq.measurable.comp_aemeasurable hG).const_mul _).add
        ((continuous_sumSq.measurable.comp_aemeasurable hG).const_mul _)
  refine ⟨fun n => (dens_int c K S x hK hs (fun p => K.lineWeight p.1) (lw_aem K) (fun p hp => lw_nonneg hK hp) hwR n
    _ (hdm n) (2 * (27 * |S.curlAbsorb n| + |S.strainAbsorb n| + |S.velocityAbsorb n|)) (by positivity)
    (fun p hp => sharp_bd c K S x n p _ (by positivity) _ (by unfold absorbDensity; exact absorb_bd _ _ _ _ _ _))).1, ?_⟩
  obtain ⟨C, hC⟩ := hA α c K S hK hS
  obtain ⟨_, hg⟩ := hM K hK c.order hm _ _ _ hs
  have hgs := summable_sum (s := (Finset.univ : Finset (Fin 3))) fun a _ =>
    summable_sum (s := (Finset.univ : Finset (Fin 3))) fun b _ => hg a b
  have hint : ∀ n a b, IntegrableOn (fun p => K.lineWeight p.1 * ‖gradMode c.order n x.2.1 a b p‖ ^ 2) K.rect :=
    fun n a b => (modeGradSquare K hK _ _ _ _ hs n a b).2
  have hg0 : ∀ n : ℤ, 0 ≤ ∑ a : Fin 3, ∑ b : Fin 3, (1 + modeNumber c.order n ^ 2) *
      ∫ p in K.rect, K.lineWeight p.1 * ‖gradMode c.order n x.2.1 a b p‖ ^ 2 := fun n =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => mul_nonneg (by positivity)
      (setIntegral_nonneg (rect_meas K) fun p hp => mul_nonneg (lw_nonneg hK hp) (sq_nonneg _))
  refine summ_of (54 * |C| + 1) S.resolved hgs
    (l := fun n => if n ∈ S.resolved then |∫ p in K.rect, K.lineWeight p.1 * absorbDensity c K S x n p| else 0)
    (fun n hn => by simp only [hn, if_false]) (fun n => ?_)
  have hC0 := abs_nonneg C
  by_cases hn : n ∈ S.resolved
  · simp only [hn, if_true]
    have h1 := hg0 n
    have h2 := abs_nonneg (∫ p in K.rect, K.lineWeight p.1 * absorbDensity c K S x n p)
    nlinarith
  · simp only [hn, if_false, add_zero]
    have hsg : ∀ p, sharpGrad c K S x n p = fun a b => gradMode c.order n x.2.1 a b p := fun p => by
      funext a b; simp [sharpGrad, lowGrad, hn]
    set K0 : ℝ := 54 * |C| * (1 + modeNumber c.order n ^ 2) with hK0
    have hK00 : 0 ≤ K0 := by positivity
    have hcs : 27 * |S.curlAbsorb n| + |S.strainAbsorb n| ≤ K0 / 2 := by
      have h1 := hC n hn
      have h2 : C * (1 + modeNumber c.order n ^ 2) ≤ |C| * (1 + modeNumber c.order n ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      have h3 := abs_nonneg (S.curlAbsorb n)
      have h4 := abs_nonneg (S.strainAbsorb n)
      rw [hK0]
      nlinarith
    have e : (fun p : ℝ × ℝ => K0 * (K.lineWeight p.1 * sumSq (fun a b => gradMode c.order n x.2.1 a b p))) =
        fun p => ∑ a : Fin 3, ∑ b : Fin 3, K0 * (K.lineWeight p.1 * ‖gradMode c.order n x.2.1 a b p‖ ^ 2) := by
      funext p; simp only [sumSq, Finset.mul_sum]
    have hI2 : IntegrableOn (fun p : ℝ × ℝ =>
        K0 * (K.lineWeight p.1 * sumSq (fun a b => gradMode c.order n x.2.1 a b p))) K.rect := by
      rw [e]
      exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hint n a b).const_mul _
    have hb : ∀ p ∈ K.rect, |K.lineWeight p.1 * absorbDensity c K S x n p| ≤
        K0 * (K.lineWeight p.1 * sumSq (fun a b => gradMode c.order n x.2.1 a b p)) := by
      intro p hp
      have hl := lw_nonneg hK hp
      have hq := sumSq_nonneg (fun a b => gradMode c.order n x.2.1 a b p)
      have hc2 := curlSq_nonneg (fun a b => gradMode c.order n x.2.1 a b p)
      have hc3 := curlSq_le (fun a b => gradMode c.order n x.2.1 a b p)
      have had : |absorbDensity c K S x n p| ≤ (27 * |S.curlAbsorb n| + |S.strainAbsorb n|) *
          sumSq (fun a b => gradMode c.order n x.2.1 a b p) := by
        simp only [absorbDensity, hn, if_false, add_zero, hsg]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hc2, abs_of_nonneg hq]
        nlinarith [abs_nonneg (S.curlAbsorb n)]
      rw [abs_mul, abs_of_nonneg hl]
      have h5 : (27 * |S.curlAbsorb n| + |S.strainAbsorb n|) * sumSq (fun a b => gradMode c.order n x.2.1 a b p)
          ≤ K0 * sumSq (fun a b => gradMode c.order n x.2.1 a b p) := by
        refine mul_le_mul_of_nonneg_right ?_ hq
        linarith
      calc K.lineWeight p.1 * |absorbDensity c K S x n p|
          ≤ K.lineWeight p.1 * (K0 * sumSq (fun a b => gradMode c.order n x.2.1 a b p)) :=
            mul_le_mul_of_nonneg_left (had.trans h5) hl
        _ = _ := by ring
    refine (abs_int_le hI2 hb).trans ?_
    have h0 := hg0 n
    suffices heq : ∫ p in K.rect, K0 * (K.lineWeight p.1 * sumSq (fun a b => gradMode c.order n x.2.1 a b p)) =
        54 * |C| * ∑ a : Fin 3, ∑ b : Fin 3, (1 + modeNumber c.order n ^ 2) *
          ∫ p in K.rect, K.lineWeight p.1 * ‖gradMode c.order n x.2.1 a b p‖ ^ 2 by
      rw [heq]; nlinarith
    rw [e, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hint n a b).const_mul _,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => (hint n a b).const_mul _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, hK0]
    ring

theorem lowM_facts (α : ℝ) (hK : IsCellBox K) (hS : IsCellScalars α c K S)
    (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1) :
    ∀ n ∈ S.resolved, IntegrableOn (fun p : ℝ × ℝ => p.1 * lowMatrixDensity c K S x n p) K.rect := by
  intro n hn
  obtain ⟨hAm, CA, hCA⟩ := hS.data_regular.1 n hn
  have hU : ∀ i, AEMeasurable (fun p => pairVec (lowGrad c K S x n p) (lowVel c K S x n p) i)
      (volume.restrict K.rect) := fun i =>
    ((pairVec_cont i).comp ((lowGrad_cont c K S x n).prodMk (lowVel_cont c K S x n))).measurable.aemeasurable
  have hM0 : 0 ≤ max CA 0 := le_max_right _ _
  refine (dens_int c K S x hK hs (fun p => p.1) (r_aem K) (fun p hp => r_nonneg hK hp) (fun p hp => r_le_lw hK hp)
    n _ ?_ (288 * max CA 0) (by positivity) (fun p hp => ?_)).1
  · unfold lowMatrixDensity sesqValue
    refine Complex.measurable_re.comp_aemeasurable (Finset.aemeasurable_fun_sum _ fun i _ =>
      Finset.aemeasurable_fun_sum _ fun j _ => ?_)
    exact ((Complex.continuous_conj.measurable.comp_aemeasurable (hU i)).mul (hAm i j).aemeasurable).mul (hU j)
  · have h := sesqV_bd (S.localMatrix n p) (max CA 0) (fun i j => (hCA p hp i j).trans (le_max_left _ _))
      (pairVec (lowGrad c K S x n p) (lowVel c K S x n p)) _ (fun i => pairVec_sq_le _ _ i)
    have l1 := sumSq_nonneg (fun a b => gradMode c.order n x.2.1 a b p)
    have l2 := vecSq_nonneg (modeVec c.order n x.1 p.1 p.2)
    have l3 := sumSq_nonneg (lowGrad c K S x n p)
    have l4 := vecSq_nonneg (lowVel c K S x n p)
    refine h.trans ?_
    nlinarith

theorem cross_facts (α : ℝ) (hK : IsCellBox K) (hS : IsCellScalars α c K S)
    (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1) :
    ∀ n ∈ S.resolved, IntegrableOn (fun p : ℝ × ℝ => p.1 * matrixCrossDensity c K S x n p) K.rect := by
  intro n hn
  obtain ⟨hAm, CA, hCA⟩ := hS.data_regular.1 n hn
  have hU : ∀ i, AEMeasurable (fun p => pairVec (lowGrad c K S x n p) (lowVel c K S x n p) i)
      (volume.restrict K.rect) := fun i =>
    ((pairVec_cont i).comp ((lowGrad_cont c K S x n).prodMk (lowVel_cont c K S x n))).measurable.aemeasurable
  have hW : ∀ i, AEMeasurable (fun p => pairVec (sharpGrad c K S x n p) (sharpVel c K S x n p) i)
      (volume.restrict K.rect) := fun i =>
    (pairVec_cont i).measurable.comp_aemeasurable
      ((sG_aem c K S x hK hs.measurable_gradient n).prodMk (sV_aem c K S x hK hs n))
  have hM0 : 0 ≤ max CA 0 := le_max_right _ _
  refine (dens_int c K S x hK hs (fun p => p.1) (r_aem K) (fun p hp => r_nonneg hK hp) (fun p hp => r_le_lw hK hp)
    n _ ?_ (864 * max CA 0) (by positivity) (fun p hp => ?_)).1
  · unfold matrixCrossDensity
    refine Complex.measurable_re.comp_aemeasurable (Finset.aemeasurable_fun_sum _ fun i _ =>
      Finset.aemeasurable_fun_sum _ fun j _ => ?_)
    exact (((Complex.continuous_conj.measurable.comp_aemeasurable (hU i)).mul (hAm i j).aemeasurable).mul (hW j)).add
      (((Complex.continuous_conj.measurable.comp_aemeasurable (hW i)).mul (hAm i j).aemeasurable).mul (hU j))
  · have h := sesq_bd (S.localMatrix n p) (max CA 0) (fun i j => (hCA p hp i j).trans (le_max_left _ _))
      (pairVec (lowGrad c K S x n p) (lowVel c K S x n p)) (pairVec (sharpGrad c K S x n p) (sharpVel c K S x n p))
      _ _ (fun i => pairVec_sq_le _ _ i) (fun i => pairVec_sq_le _ _ i)
    have hE := sharp_le c K S x n p
    have l1 := sumSq_nonneg (fun a b => gradMode c.order n x.2.1 a b p)
    have l2 := vecSq_nonneg (modeVec c.order n x.1 p.1 p.2)
    have l3 := sumSq_nonneg (lowGrad c K S x n p)
    have l4 := vecSq_nonneg (lowVel c K S x n p)
    have l5 := sumSq_nonneg (sharpGrad c K S x n p)
    have l6 := vecSq_nonneg (sharpVel c K S x n p)
    unfold matrixCrossDensity
    refine h.trans ?_
    nlinarith

end Rest

end Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal

namespace Breakdown.CellCert.CellAnalysis

open SharpYDensityRegular.Internal

theorem densityRegular_of (hM : ModeSeriesStatement) (hA : AbsorbGrowthStatement) : DensityRegularStatement := by
  intro α _ _ k N c hc K S B Cl slots R hD _ x hx
  have hK := hD.box
  have hS := hD.scalars
  have hs : SteadyCert.IsSecondOrderField c.order x.1 x.2.1 x.2.2.1 := hx.1
  have hm : 1 ≤ c.order := le_trans (by norm_num) hc.base.order_ge
  obtain ⟨d1, d2⟩ := dAt_facts c K S x α hc hK hs hm hM
  obtain ⟨s1, s2⟩ := sup_facts c K S x α hK hS hs hm hM
  obtain ⟨p1, p2⟩ := pen_facts c K S x hK hs hm hM
  obtain ⟨a1, a2⟩ := absorb_facts c K S x α hK hS hs hm hM hA
  exact ⟨d1, s1, p1, a1, lowM_facts c K S x α hK hS hs, cross_facts c K S x α hK hS hs, d2, s2, p2, a2⟩

end Breakdown.CellCert.CellAnalysis



namespace Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal

open SteadyCert Assembly SharpParts Real

def symTest : Fin 3 → Fin 3 → ℂ := ![![1, 0, 0], ![0, -1, 0], ![0, 0, 0]]

def antiTest : Fin 3 → Fin 3 → ℂ := ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]

theorem symTest_sumSq : sumSq symTest = 2 := by
  simp [sumSq, symTest, Fin.sum_univ_three]; norm_num

theorem antiTest_sumSq : sumSq antiTest = 2 := by
  simp [sumSq, antiTest, Fin.sum_univ_three]; norm_num

theorem symTest_curlSq : curlSq symTest = 0 := by
  simp [curlSq, curlComp, symTest, Fin.sum_univ_three, CellCert.permSign]

theorem antiTest_curlSq : curlSq antiTest = 4 := by
  simp [curlSq, curlComp, antiTest, Fin.sum_univ_three, CellCert.permSign]; norm_num

theorem symTest_tf : IsTraceFree symTest := by
  simp [IsTraceFree, symTest, Fin.sum_univ_three]

theorem antiTest_tf : IsTraceFree antiTest := by
  simp [IsTraceFree, antiTest, Fin.sum_univ_three]

theorem symTest_turn (k r t : ℝ) (ht : t * (k ^ 2 - 1) = r) :
    turnVec k ![(t : ℂ), Complex.I * k * t, 0] = fun a => (r : ℂ) * symTest a 1 := by
  have htC : (t : ℂ) * ((k : ℂ) ^ 2 - 1) = (r : ℂ) := by exact_mod_cast ht
  funext a
  fin_cases a
  · simp [turnVec, symTest]; ring
  · simp [turnVec, symTest]
    linear_combination (k ^ 2 * t : ℂ) * Complex.I_sq - htC
  · simp [turnVec, symTest]

theorem antiTest_turn (k r t : ℝ) (ht : t * (k ^ 2 - 1) = r) :
    turnVec k ![-(Complex.I * k * t), (t : ℂ), 0] = fun a => (r : ℂ) * antiTest a 1 := by
  have htC : (t : ℂ) * ((k : ℂ) ^ 2 - 1) = (r : ℂ) := by exact_mod_cast ht
  funext a
  fin_cases a
  · simp [turnVec, antiTest]
    linear_combination (-(k ^ 2 * t) : ℂ) * Complex.I_sq + htC
  · simp [turnVec, antiTest]; ring
  · simp [turnVec, antiTest]

theorem test_vecSq (k r t : ℝ) (hk : 9 ≤ k ^ 2) (ht : t * (k ^ 2 - 1) = r) :
    vecSq ![(t : ℂ), Complex.I * k * t, 0] ≤ r ^ 2 ∧ vecSq ![-(Complex.I * k * t), (t : ℂ), 0] ≤ r ^ 2 := by
  have e1 : vecSq ![(t : ℂ), Complex.I * k * t, 0] = t ^ 2 * (1 + k ^ 2) := by
    simp [vecSq, Fin.sum_univ_three, Complex.norm_real, mul_pow, sq_abs]; ring
  have e2 : vecSq ![-(Complex.I * k * t), (t : ℂ), 0] = t ^ 2 * (1 + k ^ 2) := by
    simp [vecSq, Fin.sum_univ_three, Complex.norm_real, mul_pow, sq_abs]; ring
  have h : 0 ≤ (k ^ 2 - 1) ^ 2 - (1 + k ^ 2) := by nlinarith
  have hr : r ^ 2 = t ^ 2 * (k ^ 2 - 1) ^ 2 := by rw [← ht]; ring
  have hb : t ^ 2 * (1 + k ^ 2) ≤ r ^ 2 := by rw [hr]; nlinarith [mul_nonneg (sq_nonneg t) h]
  exact ⟨e1 ▸ hb, e2 ▸ hb⟩

end Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal

namespace Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal

open SteadyCert Assembly SharpParts Real

theorem pt_bound (α : ℝ) {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (hℓ : 0 < S.splitLength)
    (n : ℤ) (p : ℝ × ℝ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (hs : sumSq s = 2) (hv : vecSq v ≤ K.r₂ ^ 2) :
    |CellScalars.densityForm c α p s
        - supremumLoss (S.strainBound p) (S.meanGradBound p) (S.waveGradBound p) S.splitLength s v
        - (if n ∈ S.band then 0 else S.penalty s v)| ≤
      ((27 * |1 - 3 / (4 * α) - c.curlWeight| + (|c.curlWeight| + |c.coercivity| * |CellScalars.sampleWeight c p|))
        + (27 * |S.strainBound p| + |Exterior.traceFreeConst| * |S.meanGradBound p|
          + |Exterior.traceFreeConst| * |S.waveGradBound p| * (S.splitLength + 1 / S.splitLength))
        + (|S.penaltyStrain| + 27 * |S.penaltyCurl| + |S.penaltyVelocity|)) * (2 + K.r₂ ^ 2) := by
  have h1 := form_bd c α p s _ le_rfl
  have h2 := supLoss_bd (S.strainBound p) (S.meanGradBound p) (S.waveGradBound p) S.splitLength hℓ s v
  have h3 : |(if n ∈ S.band then 0 else S.penalty s v)| ≤
      (|S.penaltyStrain| + 27 * |S.penaltyCurl| + |S.penaltyVelocity|) * (sumSq s + vecSq v) := by
    split_ifs
    · rw [abs_zero]; exact mul_nonneg (by positivity) (add_nonneg (sumSq_nonneg s) (vecSq_nonneg v))
    · exact pen_bd S s v
  have hv0 := vecSq_nonneg v
  have hE : sumSq s + vecSq v ≤ 2 + K.r₂ ^ 2 := by rw [hs]; linarith
  have hs2 : sumSq s ≤ 2 + K.r₂ ^ 2 := by rw [hs]; nlinarith [sq_nonneg K.r₂]
  have b1 : 0 ≤ 27 * |1 - 3 / (4 * α) - c.curlWeight| + (|c.curlWeight| + |c.coercivity| * |CellScalars.sampleWeight c p|) := by
    positivity
  have hq : 0 ≤ S.splitLength + 1 / S.splitLength := by positivity
  have b2 : 0 ≤ 27 * |S.strainBound p| + |Exterior.traceFreeConst| * |S.meanGradBound p|
          + |Exterior.traceFreeConst| * |S.waveGradBound p| * (S.splitLength + 1 / S.splitLength) := by positivity
  have b3 : 0 ≤ |S.penaltyStrain| + 27 * |S.penaltyCurl| + |S.penaltyVelocity| := by positivity
  have t1 := abs_sub (CellScalars.densityForm c α p s
        - supremumLoss (S.strainBound p) (S.meanGradBound p) (S.waveGradBound p) S.splitLength s v)
    (if n ∈ S.band then 0 else S.penalty s v)
  have t2 := abs_sub (CellScalars.densityForm c α p s)
    (supremumLoss (S.strainBound p) (S.meanGradBound p) (S.waveGradBound p) S.splitLength s v)
  have u1 := mul_le_mul_of_nonneg_left hs2 b1
  have u2 := mul_le_mul_of_nonneg_left hE b2
  have u3 := mul_le_mul_of_nonneg_left hE b3
  nlinarith

theorem max_sq_le (y c : ℝ) (hc : 0 ≤ c) : max (|y| - c) 0 ^ 2 ≤ y ^ 2 := by
  have h0 := le_max_right (|y| - c) 0
  have h1 : max (|y| - c) 0 ≤ |y| := max_le (by linarith) (abs_nonneg _)
  calc max (|y| - c) 0 ^ 2 ≤ |y| ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = y ^ 2 := sq_abs y

theorem tailLam_zero (K : CellBox) : CellScalars.tailLam K 0 0 = 0 := by
  simp [CellScalars.tailLam, radialEigen, heightEigen]

theorem angular_bd (K : CellBox) (hK : IsCellBox K) (n : ℤ) :
    0 ≤ K.angularWeight n ∧ K.angularWeight n ≤ K.r₂⁻¹ + K.r₂⁻¹ ^ 2 := by
  have hr : 0 < K.r₂ := lt_of_le_of_lt hK.r_order.1 hK.r_order.2
  have h1 : 0 ≤ K.r₂⁻¹ := inv_nonneg.2 hr.le
  have h2 : 0 ≤ K.r₂⁻¹ ^ 2 := sq_nonneg _
  unfold CellBox.angularWeight
  split_ifs <;> constructor <;> linarith

end Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal

namespace Breakdown.CellCert.CellAnalysis

open SharpYDensityRegular.Internal

theorem absorbGrowth : AbsorbGrowthStatement := by
  intro α k N c K S hK hS
  have hr : 0 < K.r₂ := lt_of_le_of_lt hK.r_order.1 hK.r_order.2
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ × ℝ, p = (K.r₂, K.z₁) := ⟨_, rfl⟩
  have hp : p ∈ K.rect := by rw [hpdef]; exact ⟨⟨hK.r_order.2.le, le_rfl⟩, ⟨le_rfl, hK.z_order.2.le⟩⟩
  have hp0 : p.1 ≠ 0 := by rw [hpdef]; exact hr.ne'
  obtain ⟨B0, hB0⟩ : ∃ B0 : ℝ, B0 = (27 * |1 - 3 / (4 * α) - c.curlWeight| + (|c.curlWeight| + |c.coercivity| * |CellScalars.sampleWeight c p|))
        + (27 * |S.strainBound p| + |Exterior.traceFreeConst| * |S.meanGradBound p|
          + |Exterior.traceFreeConst| * |S.waveGradBound p| * (S.splitLength + 1 / S.splitLength))
        + (|S.penaltyStrain| + 27 * |S.penaltyCurl| + |S.penaltyVelocity|) := ⟨_, rfl⟩
  set Cst : ℝ := |CellScalars.rHat K p| * (B0 * (2 + K.r₂ ^ 2)) with hCst
  set U : ℝ := (|c.innerWeight - c.coercivity| + 2 * |c.splitVisc - c.innerWeight|) * (K.r₂⁻¹ + K.r₂⁻¹ ^ 2) with hU
  have hU0 : 0 ≤ U := by positivity
  have hℓ := hS.splitLength_pos
  have hq : 0 ≤ S.splitLength + 1 / S.splitLength := by positivity
  have hB00 : 0 ≤ B0 := by rw [hB0]; positivity
  have hC0 : 0 ≤ Cst := by positivity
  refine ⟨2 * Cst + 2 * U, fun n hn => ?_⟩
  set kk : ℝ := azimuth c.order n with hkk
  have hmn : modeNumber c.order n = |kk| := rfl
  have h3 := hS.unresolved_large n hn
  rw [hmn] at h3 ⊢
  have hk9 : 9 ≤ kk ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) h3 2
    rw [sq_abs] at this
    linarith
  set t : ℝ := K.r₂ / (kk ^ 2 - 1) with htdef
  have hne : kk ^ 2 - 1 ≠ 0 := ne_of_gt (by linarith)
  have ht : t * (kk ^ 2 - 1) = K.r₂ := by rw [htdef, div_mul_cancel₀ _ hne]
  obtain ⟨hv1, hv2⟩ := test_vecSq kk K.r₂ t hk9 ht
  have key : ∀ (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ), sumSq s = 2 → vecSq v ≤ K.r₂ ^ 2 → IsTraceFree s →
      turnVec kk v = (fun a => (K.r₂ : ℂ) * s a 1) →
      -Cst ≤ S.curlAbsorb n * curlSq s + S.strainAbsorb n * sumSq s := by
    intro s v hs hv htf htv
    have htv' : turnVec (azimuth c.order n) v = fun a => (p.1 : ℂ) * s a 1 := by rw [hpdef]; exact htv
    have h0 := hS.unresolved_pointwise n hn p hp hp0 s v htf htv'
    have hb := pt_bound α c K S hℓ n p s v hs hv
    rw [← hB0] at hb
    have hX : |CellScalars.rHat K p * (CellScalars.densityForm c α p s
        - supremumLoss (S.strainBound p) (S.meanGradBound p) (S.waveGradBound p) S.splitLength s v
        - (if n ∈ S.band then 0 else S.penalty s v))| ≤ Cst := by
      rw [abs_mul, hCst]
      exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    have := le_abs_self (CellScalars.rHat K p * (CellScalars.densityForm c α p s
        - supremumLoss (S.strainBound p) (S.meanGradBound p) (S.waveGradBound p) S.splitLength s v
        - (if n ∈ S.band then 0 else S.penalty s v)))
    linarith
  have k1 := key symTest _ symTest_sumSq hv1 symTest_tf (symTest_turn kk K.r₂ t ht)
  have k2 := key antiTest _ antiTest_sumSq hv2 antiTest_tf (antiTest_turn kk K.r₂ t ht)
  rw [symTest_curlSq, symTest_sumSq] at k1
  rw [antiTest_curlSq, antiTest_sumSq] at k2
  obtain ⟨a1, a2⟩ := angular_bd K hK n
  have hew := hS.energyWeight_pos n
  have hew2 := hS.energyWeight_le n
  have hvw := hS.vorticityWeight_nonneg n
  have hvw2 := hS.vorticityWeight_le n
  have hts := hS.tailShift_zero n hn
  have hwf := hS.weightFloor_pos
  obtain ⟨s1, s2⟩ := hS.sym_weight n 0 0 (Or.inl hn)
  obtain ⟨w1, w2⟩ := hS.anti_weight n 0 0 (Or.inl hn)
  rw [tailLam_zero, zero_add, hmn, hts] at s2
  rw [tailLam_zero, zero_add, hmn, hts] at w2
  have hT0 : 0 ≤ kk ^ 2 := sq_nonneg kk
  have m1 := max_sq_le kk 2 (by norm_num)
  have m2 := max_sq_le kk 1 (by norm_num)
  have hA0 : 0 ≤ K.r₂⁻¹ + K.r₂⁻¹ ^ 2 := by positivity
  have g1 : K.angularWeight n * max (|kk| - 2) 0 ^ 2 ≤ (K.r₂⁻¹ + K.r₂⁻¹ ^ 2) * kk ^ 2 :=
    mul_le_mul a2 m1 (sq_nonneg _) hA0
  have g2 : K.angularWeight n * max (|kk| - 1) 0 ^ 2 ≤ (K.r₂⁻¹ + K.r₂⁻¹ ^ 2) * kk ^ 2 :=
    mul_le_mul a2 m2 (sq_nonneg _) hA0
  have e1 : S.energyWeight n ≤ |c.innerWeight - c.coercivity| + 2 * |c.splitVisc - c.innerWeight| := by
    have := le_abs_self (c.innerWeight - c.coercivity)
    have := abs_nonneg (c.splitVisc - c.innerWeight)
    linarith
  have e2 : S.energyWeight n + 2 * S.vorticityWeight n ≤
      |c.innerWeight - c.coercivity| + 2 * |c.splitVisc - c.innerWeight| := by
    have := le_abs_self (c.innerWeight - c.coercivity)
    have := le_abs_self (c.splitVisc - c.innerWeight)
    linarith
  have q1 : S.energyWeight n * (K.angularWeight n * max (|kk| - 2) 0 ^ 2) ≤ U * kk ^ 2 := by
    rw [hU, mul_assoc]
    exact mul_le_mul e1 g1 (mul_nonneg a1 (sq_nonneg _)) (by positivity)
  have q2 : (S.energyWeight n + 2 * S.vorticityWeight n) * (K.angularWeight n * max (|kk| - 1) 0 ^ 2) ≤
      U * kk ^ 2 := by
    rw [hU, mul_assoc]
    exact mul_le_mul e2 g2 (mul_nonneg a1 (sq_nonneg _)) (by positivity)
  have hUT : 0 ≤ U * kk ^ 2 := mul_nonneg hU0 hT0
  have hsa : |S.strainAbsorb n| ≤ Cst + U * kk ^ 2 := abs_le.2 ⟨by linarith, by linarith⟩
  have hca : |S.curlAbsorb n| ≤ Cst + U * kk ^ 2 := abs_le.2 ⟨by linarith, by linarith⟩
  rw [sq_abs]
  have hCT := mul_nonneg hC0 hT0
  calc |S.curlAbsorb n| + |S.strainAbsorb n| ≤ 2 * Cst + 2 * (U * kk ^ 2) := by linarith
    _ ≤ (2 * Cst + 2 * U) * (1 + kk ^ 2) := by
        have e : (2 * Cst + 2 * U) * (1 + kk ^ 2) = 2 * Cst + 2 * (U * kk ^ 2) + (2 * (Cst * kk ^ 2) + 2 * U) := by
          ring
        linarith

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellAnalysis

theorem densityRegular_of_series (hM : ModeSeriesStatement) : DensityRegularStatement :=
  densityRegular_of hM absorbGrowth

end Breakdown.CellCert.CellAnalysis
