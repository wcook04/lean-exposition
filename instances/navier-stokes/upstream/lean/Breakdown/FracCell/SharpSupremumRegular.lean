import Breakdown.FracCell.SharpYSharpSupremum
import Breakdown.FracCell.SharpYDensityRegular
import Breakdown.FracCell.SharpYChargeRegular

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly SharpParts SharpSupremumParts

def WaveSumBoundStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      ∃ C : ℝ, ∀ p ∈ K.rect, Summable (fun n : ℤ => sumSq (sharpGrad c K S x n p)) →
        Summable (fun n : ℤ => vecSq (sharpVel c K S x n p)) →
        |(waveSum c K S x p).re| ≤ C * ∑' n : ℤ, (sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p))

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellAnalysis.SharpSupremumRegular.Internal

open SteadyCert Assembly SharpParts SharpSupremumParts
open Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal

theorem rectM (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

theorem ae_fst_ne (K : CellBox) : ∀ᵐ p ∂(volume.restrict K.rect), p.1 ≠ 0 := by
  refine ae_restrict_of_ae ?_
  rw [ae_iff]
  have e : {a : ℝ × ℝ | ¬a.1 ≠ 0} = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
    ext a; simp
  rw [e, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

theorem rectC (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

theorem tsum_eq_toReal {f : ℤ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    ∑' n, f n = (∑' n, ENNReal.ofReal (f n)).toReal := by
  by_cases hs : Summable f
  · rw [← ENNReal.ofReal_tsum_of_nonneg hf hs, ENNReal.toReal_ofReal (tsum_nonneg hf)]
  · rw [tsum_eq_zero_of_not_summable hs]
    have h : ∑' n, ENNReal.ofReal (f n) = ⊤ := by
      by_contra h
      exact hs ((ENNReal.summable_toReal h).congr fun n => ENNReal.toReal_ofReal (hf n))
    rw [h, ENNReal.toReal_top]

theorem lint_tsum_eq {μ : Measure (ℝ × ℝ)} {F : ℤ → ℝ × ℝ → ℝ} (h0 : ∀ n a, 0 ≤ F n a)
    (hF : ∀ n, Integrable (F n) μ) (hs : Summable fun n => ∫ a, F n a ∂μ) :
    ∫⁻ a, ∑' n, ENNReal.ofReal (F n a) ∂μ = ENNReal.ofReal (∑' n, ∫ a, F n a ∂μ) := by
  rw [lintegral_tsum fun n => (hF n).1.aemeasurable.ennreal_ofReal,
    ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg (h0 n)) hs]
  congr 1
  funext n
  exact (ofReal_integral_eq_lintegral_ofReal (hF n) (ae_of_all _ (h0 n))).symm

theorem ae_summable_of {μ : Measure (ℝ × ℝ)} {F : ℤ → ℝ × ℝ → ℝ} (h0 : ∀ n a, 0 ≤ F n a)
    (hF : ∀ n, Integrable (F n) μ) (hs : Summable fun n => ∫ a, F n a ∂μ) :
    ∀ᵐ a ∂μ, Summable fun n => F n a := by
  have hm : AEMeasurable (fun a => ∑' n, ENNReal.ofReal (F n a)) μ :=
    AEMeasurable.tsum fun n => (hF n).1.aemeasurable.ennreal_ofReal
  have hfin : ∫⁻ a, ∑' n, ENNReal.ofReal (F n a) ∂μ ≠ ⊤ := by
    rw [lint_tsum_eq h0 hF hs]; exact ENNReal.ofReal_ne_top
  filter_upwards [ae_lt_top' hm hfin] with a ha
  exact (ENNReal.summable_toReal ha.ne).congr fun n => ENNReal.toReal_ofReal (h0 n a)

theorem integrable_tsum_nonneg {μ : Measure (ℝ × ℝ)} {F : ℤ → ℝ × ℝ → ℝ} (h0 : ∀ n a, 0 ≤ F n a)
    (hF : ∀ n, Integrable (F n) μ) (hs : Summable fun n => ∫ a, F n a ∂μ) :
    Integrable (fun a => ∑' n, F n a) μ := by
  have e : (fun a => ∑' n, F n a) = fun a => (∑' n, ENNReal.ofReal (F n a)).toReal :=
    funext fun a => tsum_eq_toReal fun n => h0 n a
  have hm : AEMeasurable (fun a => ∑' n, ENNReal.ofReal (F n a)) μ :=
    AEMeasurable.tsum fun n => (hF n).1.aemeasurable.ennreal_ofReal
  have hl := lint_tsum_eq h0 hF hs
  rw [e]
  refine ⟨hm.ennreal_toReal.aestronglyMeasurable, ?_⟩
  show ∫⁻ a, ‖(∑' n, ENNReal.ofReal (F n a)).toReal‖ₑ ∂μ < ⊤
  calc ∫⁻ a, ‖(∑' n, ENNReal.ofReal (F n a)).toReal‖ₑ ∂μ ≤ ∫⁻ a, ∑' n, ENNReal.ofReal (F n a) ∂μ :=
        lintegral_mono fun a => by
          rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg]; exact ENNReal.ofReal_toReal_le
    _ < ⊤ := by rw [hl]; exact ENNReal.ofReal_lt_top

theorem waveForm_aem {μ : Measure (ℝ × ℝ)} (A B C s s' : ℝ × ℝ → Fin 3 → Fin 3 → ℂ) (v v' : ℝ × ℝ → Fin 3 → ℂ)
    (hA : AEMeasurable A μ) (hB : AEMeasurable B μ) (hC : AEMeasurable C μ) (hs : AEMeasurable s μ)
    (hs' : AEMeasurable s' μ) (hv : AEMeasurable v μ) (hv' : AEMeasurable v' μ) :
    AEMeasurable (fun p => waveForm (A p) (B p) (C p) (s p) (v p) (s' p) (v' p)) μ := by
  unfold waveForm couplingMap entryPairing bracketMat curlComp
  fun_prop

section Q

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

theorem sharpQ_facts (hK : IsCellBox K) (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1) (hm : 0 < c.order) :
    (∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * (sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p))) K.rect) ∧
    Summable (fun n : ℤ => ∫ p in K.rect, p.1 * (sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p))) := by
  have hT := SharpYChargeRegular.Internal.tot_sum K hK c.order hm hs
  have hL : ∀ n : ℤ, IntegrableOn (fun p : ℝ × ℝ => p.1 * (sumSq (lowGrad c K S x n p) + vecSq (lowVel c K S x n p)))
      K.rect := fun n =>
    (continuous_fst.mul ((continuous_sumSq.comp (lowGrad_cont c K S x n)).add
      (continuous_vecSq.comp (lowVel_cont c K S x n)))).continuousOn.integrableOn_compact (rectC K)
  have hI : ∀ n : ℤ, IntegrableOn (fun p : ℝ × ℝ => 2 * (p.1 * (sumSq (fun a b => gradMode c.order n x.2.1 a b p)
      + vecSq (modeVec c.order n x.1 p.1 p.2)) + p.1 * (sumSq (lowGrad c K S x n p) + vecSq (lowVel c K S x n p))))
      K.rect := fun n => ((hT.1 n).add (hL n)).const_mul 2
  have hb : ∀ n : ℤ, ∀ p ∈ K.rect, |p.1 * (sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p))| ≤
      2 * (p.1 * (sumSq (fun a b => gradMode c.order n x.2.1 a b p) + vecSq (modeVec c.order n x.1 p.1 p.2))
        + p.1 * (sumSq (lowGrad c K S x n p) + vecSq (lowVel c K S x n p))) := by
    intro n p hp
    have h0 := r_nonneg hK hp
    have h1 := sharp_le c K S x n p
    have h2 := add_nonneg (sumSq_nonneg (sharpGrad c K S x n p)) (vecSq_nonneg (sharpVel c K S x n p))
    rw [abs_of_nonneg (mul_nonneg h0 h2)]
    have h3 := mul_le_mul_of_nonneg_left h1 h0
    linarith
  have hint : ∀ n : ℤ, IntegrableOn (fun p : ℝ × ℝ => p.1 * (sumSq (sharpGrad c K S x n p)
      + vecSq (sharpVel c K S x n p))) K.rect := by
    intro n
    have hG := sG_aem c K S x hK hs.measurable_gradient n
    have hV := sV_aem c K S x hK hs n
    exact int_mono (hI n) ((measurable_fst.aemeasurable.mul ((continuous_sumSq.measurable.comp_aemeasurable hG).add
      (continuous_vecSq.measurable.comp_aemeasurable hV))).aestronglyMeasurable) (hb n)
  refine ⟨hint, ?_⟩
  refine summ_of 2 S.resolved hT.2 (l := fun n => ∫ p in K.rect, p.1 * (sumSq (lowGrad c K S x n p)
    + vecSq (lowVel c K S x n p))) (fun n hn => ?_) fun n => ?_
  · have e : (fun p : ℝ × ℝ => p.1 * (sumSq (lowGrad c K S x n p) + vecSq (lowVel c K S x n p))) = fun _ => 0 := by
      funext p; rw [low_zero c K S x n hn p, mul_zero]
    simp only [e, integral_zero]
  · refine (abs_int_le (hI n) (hb n)).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_add (hT.1 n) (hL n)]

theorem sharpQ_ae (hK : IsCellBox K) (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1) (hm : 0 < c.order) :
    ∀ᵐ p ∂(volume.restrict K.rect), Summable (fun n : ℤ => sumSq (sharpGrad c K S x n p)) ∧
      Summable (fun n : ℤ => vecSq (sharpVel c K S x n p)) := by
  obtain ⟨hQi, hQs⟩ := sharpQ_facts c K S x hK hs hm
  have hF0 : ∀ n (p : ℝ × ℝ), 0 ≤ |p.1| * (sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p)) :=
    fun n p => mul_nonneg (abs_nonneg _) (add_nonneg (sumSq_nonneg _) (vecSq_nonneg _))
  have hFi : ∀ n : ℤ, IntegrableOn (fun p : ℝ × ℝ => |p.1| * (sumSq (sharpGrad c K S x n p)
      + vecSq (sharpVel c K S x n p))) K.rect := fun n =>
    (hQi n).congr_fun (fun p hp => by rw [abs_of_nonneg (r_nonneg hK hp)]) (rectM K)
  have hFs : Summable (fun n : ℤ => ∫ p in K.rect, |p.1| * (sumSq (sharpGrad c K S x n p)
      + vecSq (sharpVel c K S x n p))) :=
    hQs.congr fun n => setIntegral_congr_fun (rectM K) fun p hp => by rw [abs_of_nonneg (r_nonneg hK hp)]
  filter_upwards [ae_summable_of hF0 hFi hFs, ae_fst_ne K] with p hp hp0
  have ha : 0 < |p.1| := abs_pos.2 hp0
  have hQ : Summable (fun n : ℤ => sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p)) :=
    (hp.mul_left |p.1|⁻¹).congr fun n => by rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
  exact ⟨Summable.of_nonneg_of_le (fun n => sumSq_nonneg _) (fun n => le_add_of_nonneg_right (vecSq_nonneg _)) hQ,
    Summable.of_nonneg_of_le (fun n => vecSq_nonneg _) (fun n => le_add_of_nonneg_left (sumSq_nonneg _)) hQ⟩

theorem waveSum_aem (α : ℝ) (hc : IsFormData α c) (hK : IsCellBox K)
    (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => (waveSum c K S x p).re) (volume.restrict K.rect) := by
  have hSm : ∀ β : ℤ, AEMeasurable (fun p => CellScalars.strainMode c β p) (volume.restrict K.rect) := fun β =>
    aemeasurable_pi_lambda _ fun a => aemeasurable_pi_lambda _ fun b =>
      (ModeGradSquare.Internal.gm_meas K hK c.order β hc.model_measurable.2.2.1 a b).aemeasurable
  have hCm : ∀ β : ℤ, AEMeasurable (fun p => CellScalars.curlGradMode c β p) (volume.restrict K.rect) := fun β =>
    aemeasurable_pi_lambda _ fun a => aemeasurable_pi_lambda _ fun b =>
      (ModeGradSquare.Internal.gm_meas K hK c.order β hc.model_measurable.2.2.2 a b).aemeasurable
  have hG := sG_aem c K S x hK hs.measurable_gradient
  have hV := sV_aem c K S x hK hs
  have hpw : ∀ n n' : ℤ, AEMeasurable (fun p => pairWave c n n' p (sharpGrad c K S x n p) (sharpVel c K S x n p)
      (sharpGrad c K S x n' p) (sharpVel c K S x n' p)) (volume.restrict K.rect) := fun n n' =>
    waveForm_aem _ _ _ _ _ _ _ (hSm (n - n')) (hCm (n - n')) (hCm (n' - n)) (hG n) (hG n') (hV n) (hV n')
  have hw : AEMeasurable (fun p => waveSum c K S x p) (volume.restrict K.rect) :=
    AEMeasurable.tsum fun n => AEMeasurable.tsum fun n' => hpw n n'
  exact (Complex.measurable_re.comp_aemeasurable hw).aestronglyMeasurable

end Q

end Breakdown.CellCert.CellAnalysis.SharpSupremumRegular.Internal

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly SharpParts SharpSupremumParts
open SharpSupremumRegular.Internal SharpYDensityRegular.Internal

theorem sharpSupremumRegular_of (hW : WaveSumBoundStatement) : SharpSupremumRegularStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx
  have hK : IsCellBox K := hd.box
  have hS := hd.scalars
  have hm : 0 < c.order := by have := hc.base.order_ge; omega
  have hs := hx.1
  obtain ⟨hQi, hQs⟩ := sharpQ_facts c K S x hK hs hm
  obtain ⟨_, ⟨hsbm, C1, hC1⟩, ⟨hmgm, C2, hC2⟩, ⟨hwgm, C3, hC3⟩⟩ := hS.data_regular
  have hℓ := hS.splitLength_pos
  set B0 := 27 * max C1 0 + |Exterior.traceFreeConst| * max C2 0 +
      |Exterior.traceFreeConst| * max C3 0 * (S.splitLength + 1 / S.splitLength) with hB0def
  have hB0 : 0 ≤ B0 := by positivity
  have hpt : ∀ n, ∀ p ∈ K.rect, ‖p.1 * supDensity c K S x n p‖ ≤
      B0 * (p.1 * (sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p))) := by
    intro n p hp
    have h0 := r_nonneg hK hp
    have h := supLoss_bd (S.strainBound p) (S.meanGradBound p) (S.waveGradBound p) S.splitLength hℓ
      (sharpGrad c K S x n p) (sharpVel c K S x n p)
    have q1 := (hC1 p hp).trans (le_max_left C1 0)
    have q2 := (hC2 p hp).trans (le_max_left C2 0)
    have q3 := (hC3 p hp).trans (le_max_left C3 0)
    have hq : 0 ≤ S.splitLength + 1 / S.splitLength := by positivity
    have hle : 27 * |S.strainBound p| + |Exterior.traceFreeConst| * |S.meanGradBound p|
        + |Exterior.traceFreeConst| * |S.waveGradBound p| * (S.splitLength + 1 / S.splitLength) ≤ B0 := by
      rw [hB0def]; gcongr
    have hE := add_nonneg (sumSq_nonneg (sharpGrad c K S x n p)) (vecSq_nonneg (sharpVel c K S x n p))
    have h' := h.trans (mul_le_mul_of_nonneg_right hle hE)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    calc p.1 * |supDensity c K S x n p| ≤ p.1 * (B0 * (sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p))) :=
          mul_le_mul_of_nonneg_left h' h0
      _ = _ := by ring
  have hmeas : ∀ n, AEStronglyMeasurable (fun p : ℝ × ℝ => p.1 * supDensity c K S x n p) (volume.restrict K.rect) := by
    intro n
    unfold supDensity supremumLoss
    have hG := sG_aem c K S x hK hs.measurable_gradient n
    have hV := sV_aem c K S x hK hs n
    have g1 := continuous_curlSq.measurable.comp_aemeasurable hG
    have g2 := continuous_sumSq.measurable.comp_aemeasurable hG
    have g3 := continuous_vecSq.measurable.comp_aemeasurable hV
    have g4 := Real.continuous_sqrt.measurable.comp_aemeasurable g2
    have g5 := Real.continuous_sqrt.measurable.comp_aemeasurable g3
    exact (measurable_fst.aemeasurable.mul (((hsbm.aemeasurable.mul g1).add
      (((hmgm.aemeasurable.const_mul _).mul g4).mul g5)).add
      ((hwgm.aemeasurable.const_mul _).mul ((g2.const_mul _).add (g3.div_const _))))).aestronglyMeasurable
  have hint : ∀ n : ℤ, IntegrableOn (fun p : ℝ × ℝ => p.1 * supDensity c K S x n p) K.rect := by
    intro n
    refine ((hQi n).const_mul B0).mono' (hmeas n) ?_
    filter_upwards [ae_restrict_mem (rectM K)] with p hp
    exact hpt n p hp
  have hnb : ∀ n : ℤ, ∫ p in K.rect, ‖p.1 * supDensity c K S x n p‖ ≤
      B0 * ∫ p in K.rect, p.1 * (sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p)) := by
    intro n
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun p => norm_nonneg _) ((hQi n).const_mul _) ?_
    filter_upwards [ae_restrict_mem (rectM K)] with p hp
    exact hpt n p hp
  refine ⟨hint, Summable.of_nonneg_of_le (fun n => integral_nonneg fun p => norm_nonneg _) hnb (hQs.mul_left _), ?_⟩
  obtain ⟨C, hC⟩ := hW α h1 h2 c hc K S B Cl R hd hw x hx
  have hWm := waveSum_aem c K S x α hc hK hs
  have hF0 : ∀ n (p : ℝ × ℝ), 0 ≤ |p.1| * (sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p)) :=
    fun n p => mul_nonneg (abs_nonneg _) (add_nonneg (sumSq_nonneg _) (vecSq_nonneg _))
  have hFi : ∀ n : ℤ, IntegrableOn (fun p : ℝ × ℝ => |p.1| * (sumSq (sharpGrad c K S x n p)
      + vecSq (sharpVel c K S x n p))) K.rect := fun n =>
    (hQi n).congr_fun (fun p hp => by rw [abs_of_nonneg (r_nonneg hK hp)]) (rectM K)
  have hFs : Summable (fun n : ℤ => ∫ p in K.rect, |p.1| * (sumSq (sharpGrad c K S x n p)
      + vecSq (sharpVel c K S x n p))) :=
    hQs.congr fun n => setIntegral_congr_fun (rectM K) fun p hp => by rw [abs_of_nonneg (r_nonneg hK hp)]
  have hD := (integrable_tsum_nonneg hF0 hFi hFs).const_mul (max C 0)
  refine hD.mono' (continuous_fst.aestronglyMeasurable.mul hWm) ?_
  filter_upwards [ae_restrict_mem (rectM K), sharpQ_ae c K S x hK hs hm] with p hp hsp
  have hCp := hC p hp hsp.1 hsp.2
  have h0 := r_nonneg hK hp
  have hT0 : 0 ≤ ∑' n : ℤ, (sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p)) :=
    tsum_nonneg fun n => add_nonneg (sumSq_nonneg _) (vecSq_nonneg _)
  have e : ∑' n : ℤ, |p.1| * (sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p)) =
      p.1 * ∑' n : ℤ, (sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p)) := by
    rw [tsum_mul_left, abs_of_nonneg h0]
  rw [e, Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
  have hCm : C * ∑' n : ℤ, (sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p)) ≤
      max C 0 * ∑' n : ℤ, (sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hT0
  calc p.1 * |(waveSum c K S x p).re| ≤ p.1 * (max C 0 * ∑' n : ℤ, (sumSq (sharpGrad c K S x n p)
        + vecSq (sharpVel c K S x n p))) := mul_le_mul_of_nonneg_left (hCp.trans hCm) h0
    _ = _ := by ring

theorem sharpCircleSquare_holds : SharpCircleSquareStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx
  exact sharpQ_ae c K S x hd.box hx.1 (by have := hc.base.order_ge; omega)

end Breakdown.CellCert.CellAnalysis
