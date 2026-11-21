import Breakdown.FracCell.CellSharpBoundSt
import Breakdown.FracCell.LowEntry

open MeasureTheory Set

noncomputable section

namespace Breakdown.CellCert.CellAnalysis.SharpTargetSquare.Internal

open SteadyCert Assembly Real
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal

def Bd (K : CellBox) (F : ℝ × ℝ → ℂ) : Prop :=
  AEStronglyMeasurable F (volume.restrict K.rect) ∧ ∃ C : ℝ, ∀ p ∈ K.rect, ‖F p‖ ≤ C

variable {K : CellBox}

theorem wt_nonneg (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) : 0 ≤ K.lineWeight p.1 := by
  unfold CellBox.lineWeight
  split_ifs
  · exact le_trans hK.r_order.1 hp.1.1
  · exact zero_le_one

theorem wt_le (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) : K.lineWeight p.1 ≤ 1 + K.r₂ := by
  have h1 := hK.r_order.1
  have h2 := hK.r_order.2
  have h3 : p.1 ≤ K.r₂ := hp.1.2
  unfold CellBox.lineWeight
  split_ifs <;> linarith

theorem wt_meas : Continuous (fun p : ℝ × ℝ => K.lineWeight p.1) :=
  (lineWeight_cont K).comp continuous_fst

theorem W_le (hK : IsCellBox K) {F : ℝ × ℝ → ℂ} (g : ℝ × ℝ → ℝ)
    (hF : AEStronglyMeasurable F (volume.restrict K.rect)) (hg : Integrable g (volume.restrict K.rect))
    (h : ∀ p ∈ K.rect, K.lineWeight p.1 * ‖F p‖ ^ 2 ≤ g p) : IsWeightedSquareOn K F := by
  refine ⟨hF, Integrable.mono' hg (wt_meas.aestronglyMeasurable.mul (hF.norm.pow 2)) ?_⟩
  filter_upwards [ae_restrict_mem (rect_meas K)] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (wt_nonneg hK hp) (sq_nonneg _))]
  exact h p hp

theorem W_add (hK : IsCellBox K) {F G : ℝ × ℝ → ℂ} (hF : IsWeightedSquareOn K F) (hG : IsWeightedSquareOn K G) :
    IsWeightedSquareOn K (fun p => F p + G p) := by
  refine W_le hK _ (hF.1.add hG.1) ((Integrable.const_mul hF.2 2).add (Integrable.const_mul hG.2 2)) ?_
  intro p hp
  have hw := wt_nonneg hK hp
  have hn := norm_add_le (F p) (G p)
  have h2 : ‖F p + G p‖ ^ 2 ≤ 2 * ‖F p‖ ^ 2 + 2 * ‖G p‖ ^ 2 := by
    nlinarith [norm_nonneg (F p + G p), sq_nonneg (‖F p‖ - ‖G p‖), norm_nonneg (F p), norm_nonneg (G p)]
  simp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left h2 hw]

theorem W_sub (hK : IsCellBox K) {F G : ℝ × ℝ → ℂ} (hF : IsWeightedSquareOn K F) (hG : IsWeightedSquareOn K G) :
    IsWeightedSquareOn K (fun p => F p - G p) := by
  refine W_le hK _ (hF.1.sub hG.1) ((Integrable.const_mul hF.2 2).add (Integrable.const_mul hG.2 2)) ?_
  intro p hp
  have hw := wt_nonneg hK hp
  have hn := norm_sub_le (F p) (G p)
  have h2 : ‖F p - G p‖ ^ 2 ≤ 2 * ‖F p‖ ^ 2 + 2 * ‖G p‖ ^ 2 := by
    nlinarith [norm_nonneg (F p - G p), sq_nonneg (‖F p‖ - ‖G p‖), norm_nonneg (F p), norm_nonneg (G p)]
  simp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left h2 hw]

theorem W_neg (hK : IsCellBox K) {F : ℝ × ℝ → ℂ} (hF : IsWeightedSquareOn K F) :
    IsWeightedSquareOn K (fun p => -F p) := by
  refine W_le hK _ hF.1.neg hF.2 ?_
  intro p _
  rw [norm_neg]

theorem W_mul_left (hK : IsCellBox K) {g F : ℝ × ℝ → ℂ} (hg : Bd K g) (hF : IsWeightedSquareOn K F) :
    IsWeightedSquareOn K (fun p => g p * F p) := by
  obtain ⟨C, hC⟩ := hg.2
  refine W_le hK _ (hg.1.mul hF.1) (Integrable.const_mul hF.2 (C ^ 2)) ?_
  intro p hp
  have hw := wt_nonneg hK hp
  have h1 : ‖g p‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hC p hp) 2
  rw [norm_mul, mul_pow]
  have h3 : 0 ≤ K.lineWeight p.1 * ‖F p‖ ^ 2 := mul_nonneg hw (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right h1 h3]

theorem W_mul_right (hK : IsCellBox K) {g F : ℝ × ℝ → ℂ} (hF : IsWeightedSquareOn K F) (hg : Bd K g) :
    IsWeightedSquareOn K (fun p => F p * g p) := by
  have h := W_mul_left hK hg hF
  simpa only [mul_comm] using h

theorem W_of_Bd (hK : IsCellBox K) {g : ℝ × ℝ → ℂ} (hg : Bd K g) : IsWeightedSquareOn K g := by
  obtain ⟨C, hC⟩ := hg.2
  refine W_le hK (fun _ => (1 + K.r₂) * C ^ 2) hg.1
    ((continuous_const.continuousOn).integrableOn_compact (rect_compact K)) ?_
  intro p hp
  have hw := wt_nonneg hK hp
  have hw2 := wt_le hK hp
  have h1 : ‖g p‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hC p hp) 2
  exact mul_le_mul hw2 h1 (sq_nonneg _) (by linarith)

theorem Bd_const (c : ℂ) : Bd K (fun _ => c) := ⟨aestronglyMeasurable_const, ‖c‖, fun _ _ => le_rfl⟩

theorem Bd_add {f g : ℝ × ℝ → ℂ} (hf : Bd K f) (hg : Bd K g) : Bd K (fun p => f p + g p) := by
  obtain ⟨C1, h1⟩ := hf.2
  obtain ⟨C2, h2⟩ := hg.2
  exact ⟨hf.1.add hg.1, C1 + C2, fun p hp => (norm_add_le _ _).trans (add_le_add (h1 p hp) (h2 p hp))⟩

theorem Bd_sub {f g : ℝ × ℝ → ℂ} (hf : Bd K f) (hg : Bd K g) : Bd K (fun p => f p - g p) := by
  obtain ⟨C1, h1⟩ := hf.2
  obtain ⟨C2, h2⟩ := hg.2
  exact ⟨hf.1.sub hg.1, C1 + C2, fun p hp => (norm_sub_le _ _).trans (add_le_add (h1 p hp) (h2 p hp))⟩

theorem Bd_neg {f : ℝ × ℝ → ℂ} (hf : Bd K f) : Bd K (fun p => -f p) := by
  obtain ⟨C1, h1⟩ := hf.2
  exact ⟨hf.1.neg, C1, fun p hp => by rw [norm_neg]; exact h1 p hp⟩

theorem Bd_mul {f g : ℝ × ℝ → ℂ} (hf : Bd K f) (hg : Bd K g) : Bd K (fun p => f p * g p) := by
  obtain ⟨C1, h1⟩ := hf.2
  obtain ⟨C2, h2⟩ := hg.2
  refine ⟨hf.1.mul hg.1, C1 * C2, fun p hp => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (h1 p hp) (h2 p hp) (norm_nonneg _) ((norm_nonneg _).trans (h1 p hp))

theorem Bd_conj {f : ℝ × ℝ → ℂ} (hf : Bd K f) : Bd K (fun p => (starRingEnd ℂ) (f p)) := by
  obtain ⟨C1, h1⟩ := hf.2
  exact ⟨Complex.continuous_conj.comp_aestronglyMeasurable hf.1, C1, fun p hp => by
    rw [Complex.norm_conj]; exact h1 p hp⟩

theorem Bd_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ × ℝ → ℂ} (hf : ∀ i ∈ s, Bd K (f i)) :
    Bd K (fun p => ∑ i ∈ s, f i p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Bd_const (K := K) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact Bd_add (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem W_sum (hK : IsCellBox K) {ι : Type*} (s : Finset ι) {f : ι → ℝ × ℝ → ℂ}
    (hf : ∀ i ∈ s, IsWeightedSquareOn K (f i)) : IsWeightedSquareOn K (fun p => ∑ i ∈ s, f i p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using W_of_Bd hK (Bd_const (K := K) 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact W_add hK (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem Bd_ite (P : Prop) [Decidable P] {f : ℝ × ℝ → ℂ} (hf : P → Bd K f) :
    Bd K (fun p => if P then f p else 0) := by
  by_cases h : P
  · simpa only [if_pos h] using hf h
  · simpa only [if_neg h] using Bd_const (K := K) 0

theorem W_ite (hK : IsCellBox K) (P : Prop) [Decidable P] {f : ℝ × ℝ → ℂ} (hf : P → IsWeightedSquareOn K f) :
    IsWeightedSquareOn K (fun p => if P then f p else 0) := by
  by_cases h : P
  · simpa only [if_pos h] using hf h
  · simpa only [if_neg h] using W_of_Bd hK (Bd_const (K := K) 0)

theorem Bd_cont {f : ℝ × ℝ → ℂ} (hf : Continuous f) : Bd K f :=
  ⟨hf.aestronglyMeasurable, (rect_compact K).exists_bound_of_continuousOn hf.continuousOn⟩

theorem Bd_fst : Bd K (fun p => ((p.1 : ℝ) : ℂ)) := Bd_cont (Complex.continuous_ofReal.comp continuous_fst)

theorem Bd_rHat (hK : IsCellBox K) : Bd K (fun p => ((CellScalars.rHat K p : ℝ) : ℂ)) := by
  refine ⟨(Complex.measurable_ofReal.comp (measurable_fst.div
    ((lineWeight_cont K).measurable.comp measurable_fst))).aestronglyMeasurable, 1 + K.r₂, fun p hp => ?_⟩
  have h1 := hK.r_order.1
  have h2 := hK.r_order.2
  have h3 : p.1 ≤ K.r₂ := hp.1.2
  have h4 : K.r₁ ≤ p.1 := hp.1.1
  rw [Complex.norm_real, Real.norm_eq_abs, CellScalars.rHat]
  unfold CellBox.lineWeight
  split_ifs
  · rcases eq_or_ne p.1 0 with h | h
    · rw [h]; simp; linarith
    · rw [div_self h]; simp; linarith
  · rw [div_one, abs_of_nonneg (by linarith)]; linarith

theorem proj_mem' (d d' : ℕ) (F : ℝ × ℝ → ℂ) : K.proj d d' F ∈ polyFn d d' := by
  unfold CellBox.proj
  split_ifs with h
  · exact h.choose_spec.1
  · exact ⟨0, fun p => by simp⟩

theorem Bd_proj (d d' : ℕ) (F : ℝ × ℝ → ℂ) : Bd K (K.proj d d' F) := Bd_cont (poly_cont (proj_mem' d d' F))

theorem rect_le (hK : IsCellBox K) :
    volume.restrict K.rect ≤ volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
  refine Measure.restrict_mono_ae ?_
  have hsub : K.rect ⊆ Ici (0 : ℝ) ×ˢ (univ : Set ℝ) := fun p hp => ⟨le_trans hK.r_order.1 hp.1.1, trivial⟩
  refine hsub.eventuallyLE.trans ?_
  have : (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ)) =ᵐ[volume] Ici (0 : ℝ) ×ˢ (univ : Set ℝ) :=
    Measure.set_prod_ae_eq Ioi_ae_eq_Ici (ae_eq_refl _)
  exact this.symm.le

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fiber_meas (hK : IsCellBox K) {X : Space → E} (hX : AEStronglyMeasurable X volume) (φ : ℝ → E → ℂ)
    (hφc : Continuous (fun q : ℝ × E => φ q.1 q.2)) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => ∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2)))
      (volume.restrict K.rect) := by
  have hf : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => φ q.2 (X (cylArg q))) muU :=
    hφc.comp_aestronglyMeasurable (measurable_snd.aestronglyMeasurable.prodMk
      (hX.comp_quasiMeasurePreserving qmp))
  rw [muU_def] at hf
  exact hf.integral_prod_right'.mono_measure (rect_le hK)

theorem fiber_bd (hK : IsCellBox K) {X : Space → E} (hX : AEStronglyMeasurable X volume) (φ : ℝ → E → ℂ)
    (hφc : Continuous (fun q : ℝ × E => φ q.1 q.2)) (hφb : ∀ θ e, ‖φ θ e‖ ≤ ‖e‖) {C : ℝ}
    (hC : ∀ p ∈ K.rect, ∀ θ, ‖X (cylPoint p.1 θ p.2)‖ ≤ C) :
    Bd K (fun p => (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2))) := by
  refine Bd_mul (Bd_const _) ⟨fiber_meas hK hX φ hφc, C * volume.real (Ioo (-π) π), fun p hp => ?_⟩
  exact norm_setIntegral_le_of_norm_le_const measure_Ioo_lt_top (fun θ _ => (hφb _ _).trans (hC p hp θ))

theorem sq_lintegral_le_aux {α : Type*} [MeasurableSpace α] (μ : Measure α) {h : α → ENNReal} (hh : AEMeasurable h μ) :
    (∫⁻ x, h x ∂μ) ^ 2 ≤ μ univ * ∫⁻ x, h x ^ 2 ∂μ := by
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two aemeasurable_const hh
    (f := fun _ => (1 : ENNReal))
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const, one_mul] at H
  have H2 := pow_le_pow_left₀ zero_le H 2
  refine H2.trans (le_of_eq ?_)
  rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (((∫⁻ a, h a ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ)))),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  norm_num

theorem sq_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (h : α → ENNReal) :
    (∫⁻ x, h x ∂μ) ^ 2 ≤ μ univ * ∫⁻ x, h x ^ 2 ∂μ := by
  obtain ⟨g, hg, hgh, he⟩ := exists_measurable_le_lintegral_eq μ h
  rw [he]
  exact (sq_lintegral_le_aux μ hg.aemeasurable).trans
    (mul_le_mul' le_rfl (lintegral_mono fun x => pow_le_pow_left₀ zero_le (hgh x) 2))

theorem fiber_W (hK : IsCellBox K) {X : Space → E} (hX : MemLp X 2 volume) (φ : ℝ → E → ℂ)
    (hφc : Continuous (fun q : ℝ × E => φ q.1 q.2)) (hφb : ∀ θ e, ‖φ θ e‖ ≤ ‖e‖) :
    IsWeightedSquareOn K (fun p => (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2))) := by
  have hFm := fiber_meas hK hX.1 φ hφc
  refine W_mul_left hK (Bd_const _) ⟨hFm, wt_meas.aestronglyMeasurable.mul (hFm.norm.pow 2), ?_⟩
  set F : ℝ × ℝ → ℂ := fun p => ∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2)) with hF_def
  set g : Space → ENNReal := fun y => ‖X y‖ₑ ^ 2 with hg_def
  set V : ENNReal := volume (Ioo (-π) π) with hV
  set C : ℝ := if K.r₁ = 0 then 1 else K.r₁⁻¹ with hC
  have hC0 : 0 ≤ C := by
    rw [hC]; split_ifs
    · norm_num
    · exact inv_nonneg.2 hK.r_order.1
  have hw : ∀ p ∈ K.rect, 0 ≤ K.lineWeight p.1 ∧ K.lineWeight p.1 ≤ C * p.1 := by
    intro p hp
    have h1 : K.r₁ ≤ p.1 := hp.1.1
    by_cases h : K.r₁ = 0
    · simp only [CellBox.lineWeight, hC, h, if_true]
      constructor <;> linarith
    · have hr : 0 < K.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h)
      simp only [CellBox.lineWeight, hC, h, if_false]
      refine ⟨zero_le_one, ?_⟩
      rw [inv_mul_eq_div, le_div_iff₀ hr]
      linarith
  have hpt : ∀ p ∈ K.rect, ‖K.lineWeight p.1 * ‖F p‖ ^ 2‖ₑ ≤
      ENNReal.ofReal C * V * (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) := by
    intro p hp
    obtain ⟨hw0, hw1⟩ := hw p hp
    have hp1 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
    have hF1 : ‖F p‖ₑ ≤ ∫⁻ θ in Ioo (-π) π, ‖X (cylPoint p.1 θ p.2)‖ₑ := by
      refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun θ => ?_)
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hφb θ _)
    have hF2 : ‖F p‖ₑ ^ 2 ≤ V * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := by
      refine (pow_le_pow_left₀ zero_le hF1 2).trans ?_
      have := sq_lintegral_le (volume.restrict (Ioo (-π) π)) (fun θ => ‖X (cylPoint p.1 θ p.2)‖ₑ)
      rwa [Measure.restrict_apply_univ] at this
    rw [Real.enorm_eq_ofReal (mul_nonneg hw0 (sq_nonneg _))]
    calc ENNReal.ofReal (K.lineWeight p.1 * ‖F p‖ ^ 2)
        ≤ ENNReal.ofReal (C * p.1 * ‖F p‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hw1 (sq_nonneg _))
      _ = ENNReal.ofReal C * ENNReal.ofReal p.1 * ‖F p‖ₑ ^ 2 := by
          rw [ENNReal.ofReal_mul (mul_nonneg hC0 hp1), ENNReal.ofReal_mul hC0,
            ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal p.1 * (V * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) :=
          mul_le_mul' le_rfl hF2
      _ = _ := by ring
  have hgm : AEMeasurable g volume := hX.1.enorm.pow_const 2
  have hfin : ∫⁻ y, g y < ⊤ := by
    have hi := (memLp_two_iff_integrable_sq_norm hX.1).1 hX
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) hi.lintegral_lt_top
    rw [hg_def]
    dsimp only
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hint : ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal p.1 *
      ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) = ∫⁻ y, g y := by
    rw [← key g, muU_def, lintegral_prod]
    · congr 1; funext p
      dsimp only
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    · exact (ENNReal.measurable_ofReal.comp measurable_fst.fst).aemeasurable.mul
        (hgm.comp_quasiMeasurePreserving (muU_def ▸ qmp))
  have hCV : ENNReal.ofReal C * V ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_Ioo_lt_top.ne
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (b := ENNReal.ofReal C * V * ∫⁻ y, g y) ?_ (ENNReal.mul_lt_top hCV.lt_top hfin)
  calc ∫⁻ p in K.rect, ‖K.lineWeight p.1 * ‖F p‖ ^ 2‖ₑ
      ≤ ∫⁻ p in K.rect, ENNReal.ofReal C * V * (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) :=
        setLIntegral_mono' (rect_meas K) hpt
    _ ≤ ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal C * V *
          (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) := lintegral_mono' (rect_le hK) le_rfl
    _ = ENNReal.ofReal C * V * ∫⁻ y, g y := by rw [lintegral_const_mul' _ _ hCV, hint]

theorem cyl_solid (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) (θ : ℝ) : cylPoint p.1 θ p.2 ∈ K.solid := by
  have h1 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
  have h2 : 0 ≤ p.2 := le_trans hK.z_order.1 hp.2.1
  have c0 : cylPoint p.1 θ p.2 0 = p.1 * Real.cos θ := by simp [cylPoint]
  have c1 : cylPoint p.1 θ p.2 1 = p.1 * Real.sin θ := by simp [cylPoint]
  have c2 : cylPoint p.1 θ p.2 2 = p.2 := by simp [cylPoint]
  have er : cylRadius (cylPoint p.1 θ p.2) = p.1 := by
    unfold cylRadius
    rw [c0, c1, show (p.1 * Real.cos θ) ^ 2 + (p.1 * Real.sin θ) ^ 2 = p.1 ^ 2 by
      linear_combination p.1 ^ 2 * Real.sin_sq_add_cos_sq θ, Real.sqrt_sq h1]
  have ez : |cylHeight (cylPoint p.1 θ p.2)| = p.2 := by
    unfold cylHeight; rw [c2, abs_of_nonneg h2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [er]; exact hp.1.1
  · rw [er]; exact hp.1.2
  · rw [ez]; exact hp.2.1
  · rw [ez]; exact hp.2.2

theorem modeMat_bd (hK : IsCellBox K) {G : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume)
    (m : ℕ) (n : ℤ) (a b : Fin 3) {C : ℝ} (hC : ∀ y ∈ K.solid, ‖G y‖ ≤ C) :
    Bd K (fun p => modeMat m n G p.1 p.2 a b) := by
  have e : (fun p : ℝ × ℝ => modeMat m n G p.1 p.2 a b) = fun p => (1 / (2 * π) : ℂ) *
      ∫ θ in Ioo (-π) π, gradKernel m n a b θ (G (cylPoint p.1 θ p.2)) := funext fun p => gradMode_eq m n G a b p
  rw [e]
  exact fiber_bd hK hG _ (gradKernel_cont m n a b) (gradKernel_bound m n a b)
    (fun p hp θ => hC _ (cyl_solid hK hp θ))

theorem modeVec_bd (hK : IsCellBox K) {v : Space → Space} (hv : AEStronglyMeasurable v volume)
    (m : ℕ) (n : ℤ) (a : Fin 3) {C : ℝ} (hC : ∀ y ∈ K.solid, ‖v y‖ ≤ C) :
    Bd K (fun p => modeVec m n v p.1 p.2 a) := by
  have e : (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) = fun p => (1 / (2 * π) : ℂ) *
      ∫ θ in Ioo (-π) π, velKernel m n a θ (v (cylPoint p.1 θ p.2)) := funext fun p => modeVec_eq m n v a p
  rw [e]
  exact fiber_bd hK hv _ (velKernel_cont m n a) (velKernel_bound m n a)
    (fun p hp θ => hC _ (cyl_solid hK hp θ))

theorem modeMat_W (hK : IsCellBox K) {G : Space → (Space →L[ℝ] Space)} (hG : MemLp G 2 volume)
    (m : ℕ) (n : ℤ) (a b : Fin 3) : IsWeightedSquareOn K (fun p => modeMat m n G p.1 p.2 a b) := by
  have e : (fun p : ℝ × ℝ => modeMat m n G p.1 p.2 a b) = fun p => (1 / (2 * π) : ℂ) *
      ∫ θ in Ioo (-π) π, gradKernel m n a b θ (G (cylPoint p.1 θ p.2)) := funext fun p => gradMode_eq m n G a b p
  rw [e]
  exact fiber_W hK hG _ (gradKernel_cont m n a b) (gradKernel_bound m n a b)

theorem modeVec_W (hK : IsCellBox K) {v : Space → Space} (hv : MemLp v 2 volume)
    (m : ℕ) (n : ℤ) (a : Fin 3) : IsWeightedSquareOn K (fun p => modeVec m n v p.1 p.2 a) := by
  have e : (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) = fun p => (1 / (2 * π) : ℂ) *
      ∫ θ in Ioo (-π) π, velKernel m n a θ (v (cylPoint p.1 θ p.2)) := funext fun p => modeVec_eq m n v a p
  rw [e]
  exact fiber_W hK hv _ (velKernel_cont m n a) (velKernel_bound m n a)

theorem memLp_of_entry {G : Space → (Space →L[ℝ] Space)} (hG1 : AEStronglyMeasurable G volume)
    (hG2 : Integrable (fun y => entrySq (G y))) : MemLp G 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm hG1).2 ((hG2.const_mul 3).mono'
    ((hG1.norm.aemeasurable.pow_const 2).aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact EmbedWeak.Internal.norm_sq_le (G y)

end Breakdown.CellCert.CellAnalysis.SharpTargetSquare.Internal


namespace Breakdown.CellCert.CellAnalysis.SharpTargetSquare.Internal

open SteadyCert Assembly Real

variable {K : CellBox}

theorem pair_bd {s : ℝ × ℝ → Fin 3 → Fin 3 → ℂ} {v : ℝ × ℝ → Fin 3 → ℂ}
    (hs : ∀ a b, Bd K (fun p => s p a b)) (hv : ∀ a, Bd K (fun p => v p a)) (j : Fin 12) :
    Bd K (fun p => pairVec (s p) (v p) j) := by
  by_cases h : j.val < 9
  · simp only [pairVec, dif_pos h]; exact hs _ _
  · simp only [pairVec, dif_neg h]; exact hv _

theorem split_bd {L : ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ} {s : ℝ × ℝ → Fin 3 → Fin 3 → ℂ}
    {v : ℝ × ℝ → Fin 3 → ℂ} (hL : ∀ i j, Bd K (fun p => L p i j))
    (hs : ∀ a b, Bd K (fun p => s p a b)) (hv : ∀ a, Bd K (fun p => v p a)) :
    (∀ a b, Bd K (fun p => splitStrain (matAct (L p) (pairVec (s p) (v p))) a b)) ∧
    (∀ a, Bd K (fun p => splitVelocity (matAct (L p) (pairVec (s p) (v p))) a)) := by
  refine ⟨fun a b => ?_, fun a => ?_⟩
  · simp only [splitStrain, matAct]; exact Bd_sum _ fun j _ => Bd_mul (hL _ _) (pair_bd hs hv j)
  · simp only [splitVelocity, matAct]; exact Bd_sum _ fun j _ => Bd_mul (hL _ _) (pair_bd hs hv j)

theorem wave_bd {Sβ Gβ s : ℝ × ℝ → Fin 3 → Fin 3 → ℂ} {v : ℝ × ℝ → Fin 3 → ℂ}
    (hS : ∀ a b, Bd K (fun p => Sβ p a b)) (hG : ∀ a b, Bd K (fun p => Gβ p a b))
    (hs : ∀ a b, Bd K (fun p => s p a b)) (hv : ∀ a, Bd K (fun p => v p a)) (a b : Fin 3) :
    Bd K (fun p => waveActionStrain (Sβ p) (Gβ p) (s p) (v p) a b) := by
  simp only [waveActionStrain, curlAdj, matVec, curlComp, couplingMap, bracketMat]
  repeat' with_reducible first
    | exact Bd_const _
    | exact hS _ _ | exact hG _ _ | exact hs _ _ | exact hv _
    | apply Bd_add | apply Bd_sub | apply Bd_neg | apply Bd_mul | apply Bd_conj
    | (apply Bd_sum; intro _ _)

theorem waveV_bd {Gm s : ℝ × ℝ → Fin 3 → Fin 3 → ℂ}
    (hG : ∀ a b, Bd K (fun p => Gm p a b)) (hs : ∀ a b, Bd K (fun p => s p a b)) (b : Fin 3) :
    Bd K (fun p => waveActionVelocity (Gm p) (s p) b) := by
  simp only [waveActionVelocity, couplingAdj]
  repeat' with_reducible first
    | exact Bd_const _
    | exact hG _ _ | exact hs _ _
    | apply Bd_add | apply Bd_sub | apply Bd_neg | apply Bd_mul | apply Bd_conj
    | (apply Bd_sum; intro _ _)

theorem fold_W (hK : IsCellBox K) (k : ℝ) {Ys : ℝ × ℝ → Fin 3 → Fin 3 → ℂ} {Yv : ℝ × ℝ → Fin 3 → ℂ}
    (hs : ∀ a b, IsWeightedSquareOn K (fun p => Ys p a b)) (hv : ∀ a, IsWeightedSquareOn K (fun p => Yv p a))
    (a b : Fin 3) : IsWeightedSquareOn K (fun p => foldVelocity k p.1 (Ys p) (Yv p) a b) := by
  unfold foldVelocity
  refine W_add hK (hs a b) (W_ite hK _ fun _ => W_mul_left hK Bd_fst ?_)
  fin_cases a <;> simp [turnAdjInv, div_eq_mul_inv] <;>
  repeat' first
    | exact hv _
    | apply W_add hK | apply W_sub hK | apply W_neg hK
    | refine W_mul_left hK (Bd_const _) ?_
    | refine W_mul_right hK ?_ (Bd_const _)

theorem cross_W1 (hK : IsCellBox K) {A : ℝ × ℝ → Fin 3 → ℂ} {B : ℝ × ℝ → Fin 3 → ℂ}
    (hA : ∀ j, Bd K (fun p => A p j)) (hB : ∀ j, IsWeightedSquareOn K (fun p => B p j)) (i : Fin 3) :
    IsWeightedSquareOn K (fun p => crossC (conjVec3 (A p)) (B p) i) := by
  fin_cases i <;> simp [crossC, conjVec3] <;>
  exact W_sub hK (W_mul_left hK (Bd_conj (hA _)) (hB _)) (W_mul_left hK (Bd_conj (hA _)) (hB _))

theorem cross_W2 (hK : IsCellBox K) {A : ℝ × ℝ → Fin 3 → ℂ} {B : ℝ × ℝ → Fin 3 → ℂ}
    (hB : ∀ j, IsWeightedSquareOn K (fun p => B p j)) (hA : ∀ j, Bd K (fun p => A p j)) (i : Fin 3) :
    IsWeightedSquareOn K (fun p => crossC (B p) (conjVec3 (A p)) i) := by
  fin_cases i <;> simp [crossC, conjVec3] <;>
  exact W_sub hK (W_mul_right hK (hB _) (Bd_conj (hA _))) (W_mul_right hK (hB _) (Bd_conj (hA _)))

variable {k N : ℕ}

theorem yStrain_W (hK : IsCellBox K) (c : FracCellData k N) (S : CellScalars) (κ ζ : Fin k → ℝ)
    (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (n : ℤ)
    (hR : Bd K (fun p => ((CellScalars.rHat K p : ℝ) : ℂ)))
    (hwave : ∀ n' a b, Bd K (fun p => waveActionStrain (CellScalars.strainMode c (n - n') p)
      (CellScalars.curlGradMode c (n - n') p) (K.lowStrainAt c.order n' S.degHigh G p)
      (K.lowVelocityAt c.order n' S.degHigh v p) a b))
    (hsplit : n ∈ S.resolved → ∀ a b, Bd K (fun p => splitStrain (matAct (S.localMatrix n p)
      (pairVec (K.lowStrainAt c.order n S.degHigh G p) (K.lowVelocityAt c.order n S.degHigh v p))) a b))
    (hA : ∀ i a b, IsWeightedSquareOn K (fun p => modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b))
    (hP : ∀ i a b, IsWeightedSquareOn K (fun p => modeMat c.order n (c.modelPinField i) p.1 p.2 a b))
    (a b : Fin 3) : IsWeightedSquareOn K (fun p => CellScalars.yStrain c K S κ ζ v G n p a b) := by
  unfold CellScalars.yStrain
  refine W_mul_left hK hR (W_add hK (W_add hK ?_ ?_) ?_)
  · exact W_of_Bd hK (Bd_ite _ fun _ => Bd_sum _ fun n' _ => hwave n' a b)
  · exact W_of_Bd hK (Bd_ite _ fun hn => hsplit hn a b)
  · exact W_sum hK _ fun i _ => W_add hK (W_mul_left hK (Bd_const _) (hA i a b))
      (W_mul_left hK (Bd_const _) (hP i a b))

theorem yVel_bd (c : FracCellData k N) (S : CellScalars)
    (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (n : ℤ)
    (hR : Bd K (fun p => ((CellScalars.rHat K p : ℝ) : ℂ)))
    (hwv : ∀ n' b, Bd K (fun p => waveActionVelocity (CellScalars.curlGradMode c (n' - n) p)
      (K.lowStrainAt c.order n' S.degHigh G p) b))
    (hsplit : n ∈ S.resolved → ∀ b, Bd K (fun p => splitVelocity (matAct (S.localMatrix n p)
      (pairVec (K.lowStrainAt c.order n S.degHigh G p) (K.lowVelocityAt c.order n S.degHigh v p))) b))
    (b : Fin 3) : Bd K (fun p => CellScalars.yVelocity c K S v G n p b) := by
  unfold CellScalars.yVelocity
  exact Bd_mul hR (Bd_add (Bd_ite _ fun _ => Bd_sum _ fun n' _ => hwv n' b) (Bd_ite _ fun hn => hsplit hn b))

theorem rowS_W (hK : IsCellBox K) (c : FracCellData k N) {slots : ℕ} (R : CellRows N slots k) (r : Fin N) (n' : ℤ)
    (hR : Bd K (fun p => ((CellScalars.rHat K p : ℝ) : ℂ)))
    (hV : ∀ β j, Bd K (fun p => modeVec c.order β c.modelVelocity p.1 p.2 j))
    (hRow : ∀ n j, IsWeightedSquareOn K (fun p => CellScalars.rowMode c r n p j)) (i l : Fin 3) :
    IsWeightedSquareOn K (fun p => CellScalars.rowCouplingStrain c K R r n' p i l) := by
  unfold CellScalars.rowCouplingStrain
  refine W_mul_left hK hR (W_sum hK _ fun n _ => ?_)
  simp only [curlAdj]
  exact W_sum hK _ fun j _ => W_mul_left hK (Bd_const _) (cross_W1 hK (hV (n - n')) (hRow n) j)

theorem rowV_W (hK : IsCellBox K) (c : FracCellData k N) {slots : ℕ} (R : CellRows N slots k) (r : Fin N) (n' : ℤ)
    (hR : Bd K (fun p => ((CellScalars.rHat K p : ℝ) : ℂ)))
    (hC : ∀ β j, Bd K (fun p => modeVec c.order β c.modelCurl p.1 p.2 j))
    (hRow : ∀ n j, IsWeightedSquareOn K (fun p => CellScalars.rowMode c r n p j)) (i : Fin 3) :
    IsWeightedSquareOn K (fun p => CellScalars.rowCouplingVelocity c K R r n' p i) := by
  unfold CellScalars.rowCouplingVelocity
  exact W_mul_left hK hR (W_sum hK _ fun n _ => cross_W2 hK (hRow n) (hC (n - n')) i)

end Breakdown.CellCert.CellAnalysis.SharpTargetSquare.Internal

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly SharpTargetSquare.Internal

theorem sharpTargetSquare : SharpTargetSquareStatement := by
  intro α _ _ k N c hform K S B Cl slots R hcell _ x _ ζ
  have hK := hcell.box
  obtain ⟨C0, hC0⟩ := hform.model_bounded
  have hsol : ∀ y ∈ K.solid, ‖c.modelVelocity y‖ ≤ C0 ∧ ‖c.modelCurl y‖ ≤ C0 ∧
      ‖c.modelStrain y‖ ≤ C0 ∧ ‖c.modelCurlGrad y‖ ≤ C0 := fun y hy => hC0 y (hcell.solid_in_region hy)
  obtain ⟨mV, mC, mS, mG⟩ := hform.model_measurable
  have hR : Bd K (fun p => ((CellScalars.rHat K p : ℝ) : ℂ)) := Bd_rHat hK
  have bS : ∀ β a b, Bd K (fun p => CellScalars.strainMode c β p a b) :=
    fun β a b => modeMat_bd hK mS _ _ a b (fun y hy => (hsol y hy).2.2.1)
  have bG : ∀ β a b, Bd K (fun p => CellScalars.curlGradMode c β p a b) :=
    fun β a b => modeMat_bd hK mG _ _ a b (fun y hy => (hsol y hy).2.2.2)
  have bV : ∀ β a, Bd K (fun p => modeVec c.order β c.modelVelocity p.1 p.2 a) :=
    fun β a => modeVec_bd hK mV _ _ a (fun y hy => (hsol y hy).1)
  have bC : ∀ β a, Bd K (fun p => modeVec c.order β c.modelCurl p.1 p.2 a) :=
    fun β a => modeVec_bd hK mC _ _ a (fun y hy => (hsol y hy).2.1)
  have bLS : ∀ n' a b, Bd K (fun p => K.lowStrainAt c.order n' S.degHigh x.2.1 p a b) :=
    fun n' a b => Bd_proj _ _ _
  have bLV : ∀ n' a, Bd K (fun p => K.lowVelocityAt c.order n' S.degHigh x.1 p a) :=
    fun n' a => Bd_proj _ _ _
  have bL : ∀ n ∈ S.resolved, ∀ i j, Bd K (fun p => S.localMatrix n p i j) := by
    intro n hn i j
    obtain ⟨hm, C, hC⟩ := hcell.scalars.data_regular.1 n hn
    exact ⟨(hm i j).aestronglyMeasurable, C, fun p hp => hC p hp i j⟩
  have wA : ∀ i n a b, IsWeightedSquareOn K (fun p => modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b) :=
    fun i n a b => modeMat_W hK (memLp_of_entry (hform.modelActuatorGrad_data i).1
      (hform.modelActuatorGrad_data i).2.1) _ _ a b
  have wP : ∀ i n a b, IsWeightedSquareOn K (fun p => modeMat c.order n (c.modelPinField i) p.1 p.2 a b) :=
    fun i n a b => modeMat_W hK (memLp_of_entry (hform.modelPin_data i).1 (hform.modelPin_data i).2.1) _ _ a b
  have wRow : ∀ r n j, IsWeightedSquareOn K (fun p => CellScalars.rowMode c r n p j) :=
    fun r n j => modeVec_W hK (hform.base.row_two r) _ _ j
  have yS : ∀ n a b, IsWeightedSquareOn K
      (fun p => CellScalars.yStrain c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b) := fun n a b =>
    yStrain_W hK c S _ _ _ _ n hR (fun n' a b => wave_bd (bS _) (bG _) (bLS n') (bLV n') a b)
      (fun hn => (split_bd (bL n hn) (bLS n) (bLV n)).1) (wA · n) (wP · n) a b
  have yV : ∀ n b, Bd K (fun p => CellScalars.yVelocity c K S x.1 x.2.1 n p b) := fun n b =>
    yVel_bd c S _ _ n hR (fun n' b => waveV_bd (bG _) (bLS n') b)
      (fun hn => (split_bd (bL n hn) (bLS n) (bLV n)).2) b
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n _ a b
    unfold CellScalars.yFolded
    by_cases hn : n ∈ S.resolved
    · simp only [if_pos hn]; exact yS n a b
    · simp only [if_neg hn]; exact fold_W hK _ (yS n) (fun b => W_of_Bd hK (yV n b)) a b
  · intro n _ a
    exact W_of_Bd hK (yV n a)
  · intro r _ n _ a b
    unfold CellScalars.rowCouplingFolded
    by_cases hn : n ∈ S.resolved
    · simp only [if_pos hn]; exact rowS_W hK c R r n hR bV (wRow r) a b
    · simp only [if_neg hn]
      exact fold_W hK _ (rowS_W hK c R r n hR bV (wRow r)) (rowV_W hK c R r n hR bC (wRow r)) a b
  · intro r _ n _ a
    exact rowV_W hK c R r n hR bC (wRow r) a

end Breakdown.CellCert.CellAnalysis
