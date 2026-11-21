import Breakdown.FracCell.SharpYModeExpansion
import Breakdown.FracCell.SharpYDensityRegular
import Breakdown.FracCell.EnergyPairIntegrable

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly SharpParts ModeExpansionParts

def ThirdSeriesStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ), 1 ≤ m →
    ∀ (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
      IsSecondOrderField m v G H →
      Summable (fun n : ℤ => ∫ p in K.rect, p.1 * secondModeSq m n H p)

def GradSeriesStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ), 1 ≤ m → ∀ (E : Space → (Space →L[ℝ] Space)),
    AEStronglyMeasurable E volume → Integrable (fun y => entrySq (E y)) →
      ∀ a b : Fin 3, Summable (fun n : ℤ => ∫ p in K.rect, K.lineWeight p.1 * ‖gradMode m n E a b p‖ ^ 2)

def ModeWaveRegularStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      (∀ᵐ p ∂(volume.restrict K.rect),
        (∀ n, Summable (fun n' => sharpPair c K S x n n' p)) ∧
        Summable (fun n => ∑' n', sharpPair c K S x n n' p) ∧
        (∀ n ∈ S.resolved, Summable (fun n' => lowSharpPair c K S x n n' p) ∧
          Summable (fun n' => sharpLowPair c K S x n' n p)) ∧
        (∀ i, Summable (fun n => fieldSharp c K S x (c.modelActuatorGrad i) n p) ∧
          Summable (fun n => fieldSharp c K S x (c.modelPinField i) n p))) ∧
      (∀ n ∈ S.resolved, Summable (fun n' : ℤ => ∫ p in K.rect, ‖p.1 * (crossPair c K S x n n' p).re‖)) ∧
      IntegrableOn (fun p : ℝ × ℝ => p.1 * (∑' n, ∑' n', sharpPair c K S x n n' p).re) K.rect

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellAnalysis.SharpModeExpansionRegular.Internal

open SteadyCert Assembly SharpParts ModeExpansionParts Real
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal
open Breakdown.CellCert.CellAnalysis.ModeGradSquare.Internal
open Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal

theorem int_tsum {β : Type*} [MeasurableSpace β] {μ : Measure β} {F : ℤ → β → ℝ}
    (hF : ∀ n, Integrable (F n) μ) (hs : Summable (fun n => ∫ a, ‖F n a‖ ∂μ)) :
    Integrable (fun a => ∑' n, F n a) μ := by
  set f : ℤ → Lp ℝ 1 μ := fun n => (hF n).toL1 (F n) with hf
  have hsum : ∑' n, ‖f n‖ₑ ≠ ⊤ := by
    simp only [hf, Integrable.enorm_toL1]
    have e : ∀ i, ∫⁻ a, ‖F i a‖ₑ ∂μ = ‖∫ a, ‖F i a‖ ∂μ‖ₑ := by
      intro i
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (hF i).norm, ENNReal.coe_nnreal_eq]
      simp only [coe_nnnorm, Real.norm_eq_abs]
      rw [abs_of_nonneg (integral_nonneg fun a => abs_nonneg _)]
    rw [funext e]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hs.abs)
  have h1 := Lp.coeFn_tsum hsum
  have h2 : ∀ᵐ a ∂μ, ∀ n, f n a = F n a := ae_all_iff.2 (fun n => Integrable.coeFn_toL1 (hF n))
  refine (L1.integrable_coeFn (∑' n, f n)).congr ?_
  filter_upwards [h1, h2] with a ha hb
  rw [ha]
  exact tsum_congr hb

theorem re_tsum_int {K : CellBox} {z : ℤ → ℝ × ℝ → ℂ}
    (hF : ∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * (z n p).re) K.rect)
    (hN : Summable (fun n : ℤ => ∫ p in K.rect, ‖p.1 * (z n p).re‖))
    (hz : ∀ᵐ p ∂(volume.restrict K.rect), Summable (fun n => z n p)) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * (∑' n, z n p).re) K.rect := by
  refine (int_tsum hF hN).congr ?_
  filter_upwards [hz] with p hp
  rw [Complex.re_tsum hp, tsum_mul_left]

theorem unit_combo (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b d : Fin 3) (p : ℝ × ℝ) :
    comboThird (fun a' b' => if a' = a then (if b' = b then (1 : ℂ) else 0) else 0) m n H d p =
      modeThird m n H a b d p := by
  simp [comboThird, ite_mul, Finset.sum_ite_eq']

theorem curl_combo (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (i d : Fin 3) (p : ℝ × ℝ) :
    comboThird (fun a b => (CellCert.permSign i b a : ℂ)) m n H d p =
      curlComp (fun a b => modeThird m n H a b d p) i := by
  simp only [comboThird, curlComp]
  exact Finset.sum_comm

theorem second_nonneg (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    0 ≤ secondModeSq m n H p := by
  unfold secondModeSq; positivity

theorem curlGrad_nonneg (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    0 ≤ curlGradModeSq m n H p := by
  unfold curlGradModeSq; positivity

theorem curlGrad_le (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    curlGradModeSq m n H p ≤ 27 * secondModeSq m n H p := by
  have e1 : curlGradModeSq m n H p = ∑ d : Fin 3, curlSq (fun a b => modeThird m n H a b d p) := by
    simp only [curlGradModeSq, curlSq]
    exact Finset.sum_comm
  have e2 : secondModeSq m n H p = ∑ d : Fin 3, sumSq (fun a b => modeThird m n H a b d p) := by
    simp only [secondModeSq, sumSq, Fin.sum_univ_three]
    ring
  rw [e1, e2, Finset.mul_sum]
  exact Finset.sum_le_sum fun d _ => curlSq_le _

theorem second_int {K : CellBox} (hK : IsCellBox K) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * secondModeSq m n H p) K.rect := by
  have h : ∀ a b d : Fin 3, IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖modeThird m n H a b d p‖ ^ 2) K.rect := by
    intro a b d
    have := ((modeSquareIntegrable K hK m v G H hs n
      (fun a' b' => if a' = a then (if b' = b then (1 : ℂ) else 0) else 0)).2.2 d).2
    simpa only [unit_combo] using this
  have e : (fun p : ℝ × ℝ => p.1 * secondModeSq m n H p) =
      fun p => ∑ a : Fin 3, ∑ b : Fin 3, ∑ d : Fin 3, p.1 * ‖modeThird m n H a b d p‖ ^ 2 := by
    funext p
    simp only [secondModeSq, Finset.mul_sum]
  rw [e]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => integrable_finsetSum _ fun d _ => h a b d

theorem curlGrad_int {K : CellBox} (hK : IsCellBox K) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * curlGradModeSq m n H p) K.rect := by
  have h : ∀ i d : Fin 3, IntegrableOn
      (fun p : ℝ × ℝ => p.1 * ‖curlComp (fun a b => modeThird m n H a b d p) i‖ ^ 2) K.rect := by
    intro i d
    have := ((modeSquareIntegrable K hK m v G H hs n (fun a b => (CellCert.permSign i b a : ℂ))).2.2 d).2
    simpa only [curl_combo] using this
  have e : (fun p : ℝ × ℝ => p.1 * curlGradModeSq m n H p) =
      fun p => ∑ i : Fin 3, ∑ d : Fin 3, p.1 * ‖curlComp (fun a b => modeThird m n H a b d p) i‖ ^ 2 := by
    funext p
    simp only [curlGradModeSq, Finset.mul_sum]
  rw [e]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun d _ => h i d

section Energy

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

theorem energy_abs (n : ℤ) (p : ℝ × ℝ) :
    |energyAt c x n p| ≤ (|c.innerWeight - c.coercivity| + 27 * |c.splitVisc - c.innerWeight|) *
      secondModeSq c.order n x.2.2.1 p := by
  have h0 := second_nonneg c.order n x.2.2.1 p
  have h1 := curlGrad_nonneg c.order n x.2.2.1 p
  have h2 := mul_le_mul_of_nonneg_left (curlGrad_le c.order n x.2.2.1 p) (abs_nonneg (c.splitVisc - c.innerWeight))
  unfold energyAt
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg h1]
  linarith

theorem energy_int (hK : IsCellBox K) (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1) (n : ℤ) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * energyAt c x n p) K.rect := by
  have e : (fun p : ℝ × ℝ => p.1 * energyAt c x n p) = fun p =>
      (c.innerWeight - c.coercivity) * (p.1 * secondModeSq c.order n x.2.2.1 p)
        + (c.splitVisc - c.innerWeight) * (p.1 * curlGradModeSq c.order n x.2.2.1 p) := by
    funext p
    unfold energyAt
    ring
  rw [e]
  exact ((second_int hK hs n).const_mul _).add ((curlGrad_int hK hs n).const_mul _)

include S in
theorem dens_abs (α : ℝ) (hc : IsFormData α c) (hK : IsCellBox K)
    (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1) (hm : 1 ≤ c.order) (hM : ModeSeriesStatement) :
    (∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * |densityAt c x α n p|) K.rect) ∧
      Summable (fun n : ℤ => ∫ p in K.rect, p.1 * |densityAt c x α n p|) := by
  have hwt : ∀ p, |CellScalars.sampleWeight c p| ≤ |c.weightMax| := fun p => by
    have h1 := hc.base.weight_lower (cylPoint p.1 0 p.2)
    have h2 := hc.base.weight_upper (cylPoint p.1 0 p.2)
    have h3 := hc.base.weightMin_pos
    unfold CellScalars.sampleWeight
    exact abs_le.2 ⟨by linarith [abs_nonneg c.weightMax], by linarith [le_abs_self c.weightMax]⟩
  have hB0 : 0 ≤ 27 * |1 - 3 / (4 * α) - c.curlWeight| + (|c.curlWeight| + |c.coercivity| * |c.weightMax|) := by
    positivity
  refine dens_sum c K S x hK hs hm hM (fun p => p.1) (r_aem K) (fun p hp => r_nonneg hK hp)
    (fun p hp => r_le_lw hK hp) (fun n p => |densityAt c x α n p|) (fun n => ?_) _ hB0 (fun n p hp => ?_)
  · refine continuous_abs.measurable.comp_aemeasurable ?_
    unfold densityAt CellScalars.densityForm CellScalars.sampleWeight
    have hg := gmv_aem c K x hK hs.measurable_gradient n
    exact ((continuous_curlSq.measurable.comp_aemeasurable hg).const_mul _).add
      ((((hc.base.weight_measurable.comp cyl0_meas).const_mul c.coercivity).const_sub c.curlWeight).aemeasurable.mul
        (continuous_sumSq.measurable.comp_aemeasurable hg))
  · rw [abs_abs]
    have h := form_bd c α p (fun a b => gradMode c.order n x.2.1 a b p) _ (hwt p)
    have l1 := vecSq_nonneg (modeVec c.order n x.1 p.1 p.2)
    have l2 := sumSq_nonneg (lowGrad c K S x n p)
    have l3 := vecSq_nonneg (lowVel c K S x n p)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hB0)
    linarith

include S in
theorem energy_facts (α : ℝ) (hc : IsFormData α c) (hK : IsCellBox K)
    (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1) (hm : 1 ≤ c.order) (hM : ModeSeriesStatement)
    (hT : ThirdSeriesStatement) :
    (∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * energyAt c x n p) K.rect) ∧
      Summable (fun n : ℤ => ∫ p in K.rect, ‖p.1 * modeLocalDensity c α x n p‖) ∧
      Summable (fun n : ℤ => ∫ p in K.rect, p.1 * energyAt c x n p) ∧
      IntegrableOn (fun p : ℝ × ℝ => p.1 * ∑' n : ℤ, modeLocalDensity c α x n p) K.rect := by
  set A := |c.innerWeight - c.coercivity| + 27 * |c.splitVisc - c.innerWeight| with hA
  have hA0 : 0 ≤ A := by positivity
  have hS2 := hT K hK c.order hm x.1 x.2.1 x.2.2.1 hs
  obtain ⟨hDi, hDs⟩ := dens_abs c K S x α hc hK hs hm hM
  have hDR := dAt_facts c K S x α hc hK hs hm hM
  have hE := energy_int c K x hK hs
  have hL : ∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * modeLocalDensity c α x n p) K.rect := by
    intro n
    have e : (fun p : ℝ × ℝ => p.1 * modeLocalDensity c α x n p) =
        fun p => p.1 * energyAt c x n p + p.1 * densityAt c x α n p := by
      funext p
      simp only [modeLocalDensity, energyAt, densityAt]
      ring
    rw [e]
    exact (hE n).add (hDR.1 n)
  have hbound : ∀ n, ∫ p in K.rect, ‖p.1 * modeLocalDensity c α x n p‖ ≤
      A * (∫ p in K.rect, p.1 * secondModeSq c.order n x.2.2.1 p) + ∫ p in K.rect, p.1 * |densityAt c x α n p| := by
    intro n
    rw [← integral_const_mul, ← integral_add ((second_int hK hs n).const_mul A) (hDi n)]
    refine setIntegral_mono_on (hL n).norm (((second_int hK hs n).const_mul A).add (hDi n)) (rect_meas K)
      (fun p hp => ?_)
    have h0 := r_nonneg hK hp
    have e : modeLocalDensity c α x n p = energyAt c x n p + densityAt c x α n p := by
      simp only [modeLocalDensity, energyAt, densityAt]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, e]
    have h1 := energy_abs c x n p
    have h2 := abs_add_le (energyAt c x n p) (densityAt c x α n p)
    have h3 := mul_le_mul_of_nonneg_left (h2.trans (add_le_add h1 le_rfl)) h0
    linarith
  have hN : Summable (fun n : ℤ => ∫ p in K.rect, ‖p.1 * modeLocalDensity c α x n p‖) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun p => norm_nonneg _) hbound
      ((hS2.mul_left A).add hDs)
  refine ⟨hE, hN, ?_, ?_⟩
  · refine (hS2.mul_left A).of_norm_bounded (fun n => ?_)
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hE n).norm ((second_int hK hs n).const_mul A) (rect_meas K) (fun p hp => ?_)
    have h0 := r_nonneg hK hp
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    have h1 := mul_le_mul_of_nonneg_left (energy_abs c x n p) h0
    linarith
  · have e : (fun p : ℝ × ℝ => p.1 * ∑' n : ℤ, modeLocalDensity c α x n p) =
        fun p => ∑' n : ℤ, p.1 * modeLocalDensity c α x n p := by
      funext p
      rw [tsum_mul_left]
    rw [e]
    exact int_tsum hL hN

end Energy

section Low

open Breakdown.FracInternal.EnergyPairIntegrable CellCert.ModelFormInternal

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

theorem lowLow_int (α : ℝ) (hc : IsFormData α c) (hK : IsCellBox K) (n n' : ℤ) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * lowLowPair c K S x n n' p) K.rect := by
  obtain ⟨C, hC⟩ := hc.model_bounded
  obtain ⟨Cc, hCc⟩ := hc.centre_bounds
  have hCc0 := centre_nonneg hCc
  have hSb : ∀ y, ‖c.modelStrain y‖ ≤ max C Cc := by
    intro y
    by_cases hy : y ∈ c.cellRegion
    · exact (hC y hy).2.2.1.trans (le_max_left _ _)
    · rw [(hc.model_outside y hy).1]
      exact ((norm_symPart_le _).trans ((hCc y).2.1.trans
        (mul_le_of_le_one_right hCc0 (rpow_neg_le_one y 2 (by norm_num))))).trans (le_max_right _ _)
  have hGb : ∀ y, ‖c.modelCurlGrad y‖ ≤ max C (81 * Cc) := by
    intro y
    by_cases hy : y ∈ c.cellRegion
    · exact (hC y hy).2.2.2.trans (le_max_left _ _)
    · rw [(hc.model_outside y hy).2]
      refine ((norm_curlGradMatrix_le _).trans ?_).trans (le_max_right _ _)
      have := (hCc y).2.2.trans (mul_le_of_le_one_right hCc0 (rpow_neg_le_one y 3 (by norm_num)))
      linarith
  have hSm : ∀ (β : ℤ) (a b : Fin 3), Bdd K (fun p => CellScalars.strainMode c β p a b) :=
    fun β a b => bdd_mode hK c.order β hc.model_measurable.2.2.1 _ hSb a b
  have hGm : ∀ (β : ℤ) (a b : Fin 3), Bdd K (fun p => CellScalars.curlGradMode c β p a b) :=
    fun β a b => bdd_mode hK c.order β hc.model_measurable.2.2.2 _ hGb a b
  have hlg : ∀ (j : ℤ) (a b : Fin 3), Bdd K (fun p => lowGrad c K S x j p a b) := fun j a b =>
    bdd_cont K ((continuous_apply b).comp ((continuous_apply a).comp (lowGrad_cont c K S x j)))
  have hlv : ∀ (j : ℤ) (a : Fin 3), Bdd K (fun p => lowVel c K S x j p a) := fun j a =>
    bdd_cont K ((continuous_apply a).comp (lowVel_cont c K S x j))
  have hr : Bdd K (fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ)) := bdd_cont K (by fun_prop)
  exact Bdd.integrableOn (bdd_mul hr (bdd_wave (hSm (n - n')) (hGm (n - n')) (hGm (n' - n))
    (hlg n) (hlg n') (hlv n) (hlv n')))

theorem fieldLow_int (hK : IsCellBox K) (E : Space → (Space →L[ℝ] Space)) (hE1 : AEStronglyMeasurable E volume)
    (hE2 : Integrable (fun y => entrySq (E y))) (n : ℤ) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * fieldLow c K S x E n p) K.rect := by
  have hlw : IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1) K.rect :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      ((Breakdown.CellCert.CellAnalysis.LowEntry.Internal.lineWeight_cont K).comp continuous_fst).continuousOn
  have h : ∀ a b : Fin 3, IntegrableOn (fun p : ℝ × ℝ =>
      (p.1 : ℂ) * (lowGrad c K S x n p a b * (starRingEnd ℂ) (modeMat c.order n E p.1 p.2 a b))) K.rect := by
    intro a b
    obtain ⟨-, L, hL⟩ := bdd_cont K ((continuous_apply b).comp ((continuous_apply a).comp (lowGrad_cont c K S x n)))
    have hg := gm_sq K hK c.order n hE1 hE2 a b
    have hm := gm_meas K hK c.order n hE1 a b
    have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (p.1 : ℂ) * (lowGrad c K S x n p a b * (starRingEnd ℂ) (modeMat c.order n E p.1 p.2 a b)))
        (volume.restrict K.rect) := by
      refine (Continuous.aestronglyMeasurable (by fun_prop)).mul
        ((Continuous.aestronglyMeasurable ((continuous_apply b).comp ((continuous_apply a).comp
          (lowGrad_cont c K S x n)))).mul (Complex.continuous_conj.comp_aestronglyMeasurable hm))
    refine Integrable.mono' ((hlw.add hg).const_mul (max 1 K.r₂ * max L 0)) hmeas
      ((ae_restrict_iff' (rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_))
    have h0 := r_nonneg hK hp
    have hw := r_le_lw hK hp
    have hw0 := lw_nonneg hK hp
    have hl : ‖lowGrad c K S x n p a b‖ ≤ max L 0 := (hL p hp).trans (le_max_left _ _)
    have hL0 : 0 ≤ max L 0 := le_max_right _ _
    set g := ‖modeMat c.order n E p.1 p.2 a b‖ with hgdef
    have hg0 : 0 ≤ g := norm_nonneg _
    have hgg : g ≤ 1 + g ^ 2 := by nlinarith [sq_nonneg (g - 1)]
    have e : ‖(p.1 : ℂ) * (lowGrad c K S x n p a b * (starRingEnd ℂ) (modeMat c.order n E p.1 p.2 a b))‖ =
        p.1 * (‖lowGrad c K S x n p a b‖ * g) := by
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg h0]
    have e2 : gradMode c.order n E a b p = modeMat c.order n E p.1 p.2 a b := rfl
    rw [e]
    show p.1 * (‖lowGrad c K S x n p a b‖ * g) ≤ max 1 K.r₂ * max L 0 *
      (K.lineWeight p.1 + K.lineWeight p.1 * ‖gradMode c.order n E a b p‖ ^ 2)
    rw [e2, ← hgdef]
    have h1 : ‖lowGrad c K S x n p a b‖ * g ≤ max L 0 * (1 + g ^ 2) :=
      mul_le_mul hl hgg hg0 hL0
    have h2 := mul_le_mul hw h1 (by positivity) (by positivity)
    nlinarith
  have e : (fun p : ℝ × ℝ => (p.1 : ℂ) * fieldLow c K S x E n p) = fun p => ∑ a : Fin 3, ∑ b : Fin 3,
      (p.1 : ℂ) * (lowGrad c K S x n p a b * (starRingEnd ℂ) (modeMat c.order n E p.1 p.2 a b)) := by
    funext p
    simp only [fieldLow, entryPairing, Finset.mul_sum]
  rw [e]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => h a b

def Wt (K : CellBox) (f : ℝ × ℝ → ℂ) : Prop :=
  AEStronglyMeasurable f (volume.restrict K.rect) ∧ IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * f p) K.rect

theorem wt_add {f g : ℝ × ℝ → ℂ} (hf : Wt K f) (hg : Wt K g) : Wt K (fun p => f p + g p) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  have e : (fun p : ℝ × ℝ => (p.1 : ℂ) * (f p + g p)) = fun p => (p.1 : ℂ) * f p + (p.1 : ℂ) * g p :=
    funext fun p => by ring
  rw [e]
  exact hf.2.add hg.2

theorem wt_neg {f : ℝ × ℝ → ℂ} (hf : Wt K f) : Wt K (fun p => -f p) := by
  refine ⟨hf.1.neg, ?_⟩
  have e : (fun p : ℝ × ℝ => (p.1 : ℂ) * -f p) = fun p => -((p.1 : ℂ) * f p) := funext fun p => by ring
  rw [e]
  exact hf.2.neg

theorem wt_sub {f g : ℝ × ℝ → ℂ} (hf : Wt K f) (hg : Wt K g) : Wt K (fun p => f p - g p) := by
  have h := wt_add K hf (wt_neg K hg)
  simpa only [sub_eq_add_neg] using h

theorem wt_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ × ℝ → ℂ} (hf : ∀ i ∈ s, Wt K (f i)) :
    Wt K (fun p => ∑ i ∈ s, f i p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨aestronglyMeasurable_const, by simp⟩
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact wt_add K (hf j (Finset.mem_insert_self j s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem wt_bdd_mul {b f : ℝ × ℝ → ℂ} (hb : Bdd K b) (hf : Wt K f) : Wt K (fun p => b p * f p) := by
  obtain ⟨hbm, C, hC⟩ := hb
  refine ⟨hbm.mul hf.1, ?_⟩
  have e : (fun p : ℝ × ℝ => (p.1 : ℂ) * (b p * f p)) = fun p => b p * ((p.1 : ℂ) * f p) :=
    funext fun p => by ring
  rw [e]
  exact hf.2.bdd_mul hbm ((ae_restrict_iff' (rect_meas K)).2 (Filter.Eventually.of_forall hC))

theorem wt_mul_bdd {b f : ℝ × ℝ → ℂ} (hf : Wt K f) (hb : Bdd K b) : Wt K (fun p => f p * b p) := by
  have h := wt_bdd_mul K hb hf
  simpa only [mul_comm] using h

theorem wt_conj {f : ℝ × ℝ → ℂ} (hf : Wt K f) : Wt K (fun p => (starRingEnd ℂ) (f p)) := by
  refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable hf.1, ?_⟩
  refine Integrable.mono' hf.2.norm
    ((Continuous.aestronglyMeasurable (by fun_prop)).mul (Complex.continuous_conj.comp_aestronglyMeasurable hf.1))
    (Filter.Eventually.of_forall fun p => ?_)
  rw [norm_mul, norm_mul, Complex.norm_conj]

theorem wt_of_bdd {b : ℝ × ℝ → ℂ} (hb : Bdd K b) : Wt K b :=
  ⟨hb.1, Bdd.integrableOn (bdd_mul (bdd_cont K (by fun_prop : Continuous fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ))) hb)⟩

theorem wt_sq (hK : IsCellBox K) {g : ℝ × ℝ → ℂ} (hgm : AEStronglyMeasurable g (volume.restrict K.rect))
    (hg : IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * ‖g p‖ ^ 2) K.rect) : Wt K g := by
  have hlw : IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1) K.rect :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      ((Breakdown.CellCert.CellAnalysis.LowEntry.Internal.lineWeight_cont K).comp continuous_fst).continuousOn
  refine ⟨hgm, Integrable.mono' ((hlw.add hg).const_mul (max 1 K.r₂))
    ((Continuous.aestronglyMeasurable (by fun_prop)).mul hgm)
    ((ae_restrict_iff' (rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_))⟩
  have h0 := r_nonneg hK hp
  have hw := r_le_lw hK hp
  have hw0 := lw_nonneg hK hp
  have hg0 : 0 ≤ ‖g p‖ := norm_nonneg _
  have hgg : ‖g p‖ ≤ 1 + ‖g p‖ ^ 2 := by nlinarith [sq_nonneg (‖g p‖ - 1)]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
  have h2 := mul_le_mul hw hgg hg0 (by positivity)
  simp only [Pi.add_apply]
  nlinarith

theorem wt_bil (hK : IsCellBox K) {g h : ℝ × ℝ → ℂ} (hgm : AEStronglyMeasurable g (volume.restrict K.rect))
    (hg : IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * ‖g p‖ ^ 2) K.rect)
    (hhm : AEStronglyMeasurable h (volume.restrict K.rect))
    (hh : IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * ‖h p‖ ^ 2) K.rect) :
    Wt K (fun p => g p * (starRingEnd ℂ) (h p)) := by
  have hm : AEStronglyMeasurable (fun p => g p * (starRingEnd ℂ) (h p)) (volume.restrict K.rect) :=
    hgm.mul (Complex.continuous_conj.comp_aestronglyMeasurable hhm)
  refine ⟨hm, Integrable.mono' ((hg.add hh).const_mul (max 1 K.r₂))
    ((Continuous.aestronglyMeasurable (by fun_prop)).mul hm)
    ((ae_restrict_iff' (rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_))⟩
  have h0 := r_nonneg hK hp
  have hw := r_le_lw hK hp
  have hw0 := lw_nonneg hK hp
  have ha : 0 ≤ ‖g p‖ := norm_nonneg _
  have hb : 0 ≤ ‖h p‖ := norm_nonneg _
  have hab : ‖g p‖ * ‖h p‖ ≤ ‖g p‖ ^ 2 + ‖h p‖ ^ 2 := by nlinarith [sq_nonneg (‖g p‖ - ‖h p‖)]
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg h0]
  have h2 := mul_le_mul hw hab (by positivity) (by positivity)
  simp only [Pi.add_apply]
  nlinarith

theorem wt_curl {s : ℝ × ℝ → Fin 3 → Fin 3 → ℂ} (hs : ∀ a b, Wt K (fun p => s p a b)) (i : Fin 3) :
    Wt K (fun p => curlComp (s p) i) := by
  simp only [curlComp]
  exact wt_sum K _ fun j _ => wt_sum K _ fun l _ => wt_bdd_mul K (bdd_const K _) (hs l j)

theorem wt_coupling {M : ℝ × ℝ → Fin 3 → Fin 3 → ℂ} {v : ℝ × ℝ → Fin 3 → ℂ}
    (hM : ∀ a b, Bdd K (fun p => M p a b)) (hv : ∀ a, Wt K (fun p => v p a)) (i l : Fin 3) :
    Wt K (fun p => couplingMap (M p) (v p) i l) := by
  simp only [couplingMap, bracketMat]
  exact wt_add K (wt_neg K (wt_sum K _ fun j _ => wt_bdd_mul K (bdd_const K _)
      (wt_sum K _ fun b _ => wt_bdd_mul K (hM _ _) (hv b))))
    (wt_bdd_mul K (bdd_const K _) (wt_sum K _ fun q _ =>
      wt_mul_bdd K (wt_sum K _ fun j _ => wt_bdd_mul K (bdd_const K _) (hv j)) (hM _ _)))

theorem wt_wave_right {Sm Gm Gm' s s' : ℝ × ℝ → Fin 3 → Fin 3 → ℂ} {v v' : ℝ × ℝ → Fin 3 → ℂ}
    (hSm : ∀ a b, Bdd K (fun p => Sm p a b)) (hGm : ∀ a b, Bdd K (fun p => Gm p a b))
    (hGm' : ∀ a b, Bdd K (fun p => Gm' p a b)) (hs : ∀ a b, Bdd K (fun p => s p a b))
    (hs' : ∀ a b, Wt K (fun p => s' p a b)) (hv : ∀ a, Bdd K (fun p => v p a))
    (hv' : ∀ a, Wt K (fun p => v' p a)) :
    Wt K (fun p => waveForm (Sm p) (Gm p) (Gm' p) (s p) (v p) (s' p) (v' p)) := by
  have hc := bdd_curl hs
  have hc' := wt_curl K hs'
  have hk := wt_coupling K hGm hv'
  have hk' := bdd_coupling hGm' hv
  simp only [waveForm, entryPairing]
  exact wt_add K (wt_add K (wt_neg K (wt_sum K _ fun a _ => wt_bdd_mul K (bdd_conj (hc a))
      (wt_sum K _ fun b _ => wt_bdd_mul K (hSm a b) (hc' b))))
    (wt_bdd_mul K (bdd_const _ _) (wt_sum K _ fun a _ => wt_sum K _ fun b _ => wt_mul_bdd K (hk a b) (bdd_conj (hs a b)))))
    (wt_bdd_mul K (bdd_const _ _) (wt_sum K _ fun a _ => wt_sum K _ fun b _ => wt_mul_bdd K (hs' a b) (bdd_conj (hk' a b))))

theorem wt_wave_left {Sm Gm Gm' s s' : ℝ × ℝ → Fin 3 → Fin 3 → ℂ} {v v' : ℝ × ℝ → Fin 3 → ℂ}
    (hSm : ∀ a b, Bdd K (fun p => Sm p a b)) (hGm : ∀ a b, Bdd K (fun p => Gm p a b))
    (hGm' : ∀ a b, Bdd K (fun p => Gm' p a b)) (hs : ∀ a b, Wt K (fun p => s p a b))
    (hs' : ∀ a b, Bdd K (fun p => s' p a b)) (hv : ∀ a, Wt K (fun p => v p a))
    (hv' : ∀ a, Bdd K (fun p => v' p a)) :
    Wt K (fun p => waveForm (Sm p) (Gm p) (Gm' p) (s p) (v p) (s' p) (v' p)) := by
  have hc := wt_curl K hs
  have hc' := bdd_curl hs'
  have hk := bdd_coupling hGm hv'
  have hk' := wt_coupling K hGm' hv
  simp only [waveForm, entryPairing]
  exact wt_add K (wt_add K (wt_neg K (wt_sum K _ fun a _ => wt_mul_bdd K (wt_conj K (hc a))
      (bdd_sum _ fun b _ => bdd_mul (hSm a b) (hc' b))))
    (wt_bdd_mul K (bdd_const _ _) (wt_sum K _ fun a _ => wt_sum K _ fun b _ => wt_bdd_mul K (hk a b) (wt_conj K (hs a b)))))
    (wt_bdd_mul K (bdd_const _ _) (wt_sum K _ fun a _ => wt_sum K _ fun b _ => wt_bdd_mul K (hs' a b) (wt_conj K (hk' a b))))

theorem model_bdd (α : ℝ) (hc : IsFormData α c) (hK : IsCellBox K) :
    (∀ (β : ℤ) (a b : Fin 3), Bdd K (fun p => CellScalars.strainMode c β p a b)) ∧
      ∀ (β : ℤ) (a b : Fin 3), Bdd K (fun p => CellScalars.curlGradMode c β p a b) := by
  obtain ⟨C, hC⟩ := hc.model_bounded
  obtain ⟨Cc, hCc⟩ := hc.centre_bounds
  have hCc0 := centre_nonneg hCc
  have hSb : ∀ y, ‖c.modelStrain y‖ ≤ max C Cc := by
    intro y
    by_cases hy : y ∈ c.cellRegion
    · exact (hC y hy).2.2.1.trans (le_max_left _ _)
    · rw [(hc.model_outside y hy).1]
      exact ((norm_symPart_le _).trans ((hCc y).2.1.trans
        (mul_le_of_le_one_right hCc0 (rpow_neg_le_one y 2 (by norm_num))))).trans (le_max_right _ _)
  have hGb : ∀ y, ‖c.modelCurlGrad y‖ ≤ max C (81 * Cc) := by
    intro y
    by_cases hy : y ∈ c.cellRegion
    · exact (hC y hy).2.2.2.trans (le_max_left _ _)
    · rw [(hc.model_outside y hy).2]
      refine ((norm_curlGradMatrix_le _).trans ?_).trans (le_max_right _ _)
      have := (hCc y).2.2.trans (mul_le_of_le_one_right hCc0 (rpow_neg_le_one y 3 (by norm_num)))
      linarith
  exact ⟨fun β a b => bdd_mode hK c.order β hc.model_measurable.2.2.1 _ hSb a b,
    fun β a b => bdd_mode hK c.order β hc.model_measurable.2.2.2 _ hGb a b⟩

theorem wt_re {z : ℝ × ℝ → ℂ} (h : Wt K z) : IntegrableOn (fun p : ℝ × ℝ => p.1 * (z p).re) K.rect := by
  refine (h.2.re).congr (Filter.Eventually.of_forall fun p => ?_)
  show ((p.1 : ℂ) * z p).re = p.1 * (z p).re
  exact Complex.re_ofReal_mul _ _

theorem cross_wt (α : ℝ) (hc : IsFormData α c) (hK : IsCellBox K)
    (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1) (n n' : ℤ) :
    Wt K (fun p => crossPair c K S x n n' p) := by
  obtain ⟨hSm, hGm⟩ := model_bdd c K α hc hK
  have hlg : ∀ (j : ℤ) (a b : Fin 3), Bdd K (fun p => lowGrad c K S x j p a b) := fun j a b =>
    bdd_cont K ((continuous_apply b).comp ((continuous_apply a).comp (lowGrad_cont c K S x j)))
  have hlv : ∀ (j : ℤ) (a : Fin 3), Bdd K (fun p => lowVel c K S x j p a) := fun j a =>
    bdd_cont K ((continuous_apply a).comp (lowVel_cont c K S x j))
  have hsg : ∀ (j : ℤ) (a b : Fin 3), Wt K (fun p => sharpGrad c K S x j p a b) := fun j a b =>
    wt_sub K (wt_sq K hK (gm_meas K hK _ j hs.measurable_gradient a b) (modeGradSquare K hK _ _ _ _ hs j a b).2)
      (wt_of_bdd K (hlg j a b))
  have hsv : ∀ (j : ℤ) (a : Fin 3), Wt K (fun p => sharpVel c K S x j p a) := fun j a =>
    wt_sub K (wt_sq K hK (modeVelSquare K hK _ _ _ _ hs j a).1 (modeVelSquare K hK _ _ _ _ hs j a).2)
      (wt_of_bdd K (hlv j a))
  exact wt_add K (wt_wave_right K (hSm (n - n')) (hGm (n - n')) (hGm (n' - n)) (hlg n) (hsg n') (hlv n) (hsv n'))
    (wt_wave_left K (hSm (n' - n)) (hGm (n' - n)) (hGm (n - n')) (hsg n') (hlg n) (hsv n') (hlv n))

theorem field_wt (hK : IsCellBox K) (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1)
    (E : Space → (Space →L[ℝ] Space)) (hE1 : AEStronglyMeasurable E volume)
    (hE2 : Integrable (fun y => entrySq (E y))) (n : ℤ) :
    Wt K (fun p => fieldSharp c K S x E n p) := by
  have hlg : ∀ (a b : Fin 3), Bdd K (fun p => lowGrad c K S x n p a b) := fun a b =>
    bdd_cont K ((continuous_apply b).comp ((continuous_apply a).comp (lowGrad_cont c K S x n)))
  have e : (fun p => fieldSharp c K S x E n p) = fun p => ∑ a : Fin 3, ∑ b : Fin 3,
      (gradMode c.order n x.2.1 a b p * (starRingEnd ℂ) (gradMode c.order n E a b p)
        - lowGrad c K S x n p a b * (starRingEnd ℂ) (gradMode c.order n E a b p)) := by
    funext p
    simp only [fieldSharp, entryPairing, sharpGrad, sub_mul]
    rfl
  rw [e]
  exact wt_sum K _ fun a _ => wt_sum K _ fun b _ => wt_sub K
    (wt_bil K hK (gm_meas K hK _ n hs.measurable_gradient a b) (modeGradSquare K hK _ _ _ _ hs n a b).2
      (gm_meas K hK _ n hE1 a b) (gm_sq K hK c.order n hE1 hE2 a b))
    (wt_bdd_mul K (hlg a b) (wt_conj K (wt_sq K hK (gm_meas K hK _ n hE1 a b) (gm_sq K hK c.order n hE1 hE2 a b))))

theorem field_summ (hK : IsCellBox K) (hm : 1 ≤ c.order) (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1)
    (hGS : GradSeriesStatement)
    (E : Space → (Space →L[ℝ] Space)) (hE1 : AEStronglyMeasurable E volume)
    (hE2 : Integrable (fun y => entrySq (E y))) :
    Summable (fun n : ℤ => ∫ p in K.rect, ‖p.1 * (fieldSharp c K S x E n p).re‖) := by
  set T : ℤ → Fin 3 → Fin 3 → ℝ × ℝ → ℝ := fun n a b p =>
    2 * (K.lineWeight p.1 * ‖gradMode c.order n x.2.1 a b p‖ ^ 2)
      + 2 * (K.lineWeight p.1 * ‖lowGrad c K S x n p a b‖ ^ 2)
      + K.lineWeight p.1 * ‖gradMode c.order n E a b p‖ ^ 2 with hT
  have hlow : ∀ n a b, IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * ‖lowGrad c K S x n p a b‖ ^ 2) K.rect :=
    fun n a b => ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      ((((Breakdown.CellCert.CellAnalysis.LowEntry.Internal.lineWeight_cont K).comp continuous_fst).mul
        ((continuous_norm.comp ((continuous_apply b).comp ((continuous_apply a).comp
          (lowGrad_cont c K S x n)))).pow 2))).continuousOn
  have hTi : ∀ n a b, IntegrableOn (T n a b) K.rect := fun n a b =>
    ((((modeGradSquare K hK _ _ _ _ hs n a b).2).const_mul 2).add ((hlow n a b).const_mul 2)).add
      (gm_sq K hK c.order n hE1 hE2 a b)
  have hG := hGS K hK c.order hm x.2.1 hs.measurable_gradient hs.gradient_two
  have hEs := hGS K hK c.order hm E hE1 hE2
  have hLs : ∀ a b, Summable (fun n : ℤ => ∫ p in K.rect, K.lineWeight p.1 * ‖lowGrad c K S x n p a b‖ ^ 2) :=
    fun a b => summable_of_ne_finset_zero (s := S.resolved) fun n hn => by simp [lowGrad, hn]
  have hTs : ∀ a b, Summable (fun n => ∫ p in K.rect, T n a b p) := by
    intro a b
    have e : (fun n => ∫ p in K.rect, T n a b p) = fun n =>
        2 * (∫ p in K.rect, K.lineWeight p.1 * ‖gradMode c.order n x.2.1 a b p‖ ^ 2)
          + 2 * (∫ p in K.rect, K.lineWeight p.1 * ‖lowGrad c K S x n p a b‖ ^ 2)
          + ∫ p in K.rect, K.lineWeight p.1 * ‖gradMode c.order n E a b p‖ ^ 2 := by
      funext n
      simp only [hT]
      have i1 : IntegrableOn (fun p : ℝ × ℝ => 2 * (K.lineWeight p.1 * ‖gradMode c.order n x.2.1 a b p‖ ^ 2)) K.rect :=
        ((modeGradSquare K hK _ _ _ _ hs n a b).2).const_mul 2
      have i2 : IntegrableOn (fun p : ℝ × ℝ => 2 * (K.lineWeight p.1 * ‖lowGrad c K S x n p a b‖ ^ 2)) K.rect :=
        (hlow n a b).const_mul 2
      have i12 : IntegrableOn (fun p : ℝ × ℝ => 2 * (K.lineWeight p.1 * ‖gradMode c.order n x.2.1 a b p‖ ^ 2)
          + 2 * (K.lineWeight p.1 * ‖lowGrad c K S x n p a b‖ ^ 2)) K.rect := i1.add i2
      rw [integral_add i12 (gm_sq K hK c.order n hE1 hE2 a b), integral_add i1 i2,
        integral_const_mul, integral_const_mul]
    rw [e]
    exact (((hG a b).mul_left 2).add ((hLs a b).mul_left 2)).add (hEs a b)
  have hB : ∀ n, ∫ p in K.rect, ‖p.1 * (fieldSharp c K S x E n p).re‖ ≤
      max 1 K.r₂ * ∑ a : Fin 3, ∑ b : Fin 3, ∫ p in K.rect, T n a b p := by
    intro n
    have hsum : IntegrableOn (fun p => max 1 K.r₂ * ∑ a : Fin 3, ∑ b : Fin 3, T n a b p) K.rect :=
      (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hTi n a b).const_mul _
    have e2 : max 1 K.r₂ * ∑ a : Fin 3, ∑ b : Fin 3, ∫ p in K.rect, T n a b p =
        ∫ p in K.rect, max 1 K.r₂ * ∑ a : Fin 3, ∑ b : Fin 3, T n a b p := by
      rw [integral_const_mul, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hTi n a b]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum _ fun b _ => hTi n a b]
    rw [e2]
    refine setIntegral_mono_on (wt_re K (field_wt c K S x hK hs E hE1 hE2 n)).norm hsum (rect_meas K)
      (fun p hp => ?_)
    have h0 := r_nonneg hK hp
    have hw := r_le_lw hK hp
    have hw0 := lw_nonneg hK hp
    have hpt : ‖fieldSharp c K S x E n p‖ ≤ ∑ a : Fin 3, ∑ b : Fin 3,
        (2 * ‖gradMode c.order n x.2.1 a b p‖ ^ 2 + 2 * ‖lowGrad c K S x n p a b‖ ^ 2
          + ‖gradMode c.order n E a b p‖ ^ 2) := by
      simp only [fieldSharp, entryPairing]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun b _ => ?_))
      rw [norm_mul, Complex.norm_conj]
      have h1 := nsq_sub (gradMode c.order n x.2.1 a b p) (lowGrad c K S x n p a b)
      have h2 : ‖sharpGrad c K S x n p a b‖ * ‖modeMat c.order n E p.1 p.2 a b‖ ≤
          ‖sharpGrad c K S x n p a b‖ ^ 2 + ‖modeMat c.order n E p.1 p.2 a b‖ ^ 2 := by
        nlinarith [sq_nonneg (‖sharpGrad c K S x n p a b‖ - ‖modeMat c.order n E p.1 p.2 a b‖),
          norm_nonneg (sharpGrad c K S x n p a b), norm_nonneg (modeMat c.order n E p.1 p.2 a b)]
      have e3 : sharpGrad c K S x n p a b = gradMode c.order n x.2.1 a b p - lowGrad c K S x n p a b := rfl
      have e4 : gradMode c.order n E a b p = modeMat c.order n E p.1 p.2 a b := rfl
      rw [e4, e3]
      rw [e3] at h2
      linarith
    have hre : |(fieldSharp c K S x E n p).re| ≤ ‖fieldSharp c K S x E n p‖ := Complex.abs_re_le_norm _
    have e5 : ∑ a : Fin 3, ∑ b : Fin 3, T n a b p = K.lineWeight p.1 * ∑ a : Fin 3, ∑ b : Fin 3,
        (2 * ‖gradMode c.order n x.2.1 a b p‖ ^ 2 + 2 * ‖lowGrad c K S x n p a b‖ ^ 2
          + ‖gradMode c.order n E a b p‖ ^ 2) := by
      simp only [hT, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [e5, Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    have hQ : 0 ≤ ∑ a : Fin 3, ∑ b : Fin 3,
        (2 * ‖gradMode c.order n x.2.1 a b p‖ ^ 2 + 2 * ‖lowGrad c K S x n p a b‖ ^ 2
          + ‖gradMode c.order n E a b p‖ ^ 2) := by positivity
    have h6 := mul_le_mul_of_nonneg_left (hre.trans hpt) h0
    have h7 := mul_le_mul_of_nonneg_right hw hQ
    nlinarith
  refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun p => norm_nonneg _) hB ?_
  exact (summable_sum fun a _ => summable_sum fun b _ => hTs a b).mul_left _

end Low

end Breakdown.CellCert.CellAnalysis.SharpModeExpansionRegular.Internal

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert SharpParts ModeExpansionParts SharpModeExpansionRegular.Internal SharpYDensityRegular.Internal

theorem modeExpansionRegular_of (hM : ModeSeriesStatement) (hT : ThirdSeriesStatement)
    (hGS : GradSeriesStatement) (hW : ModeWaveRegularStatement) : ModeExpansionRegularStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hD hAx x hx
  have hK := hD.box
  have hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1 := hx.1
  have hm : 1 ≤ c.order := le_trans (by norm_num) hc.base.order_ge
  obtain ⟨w1, w4, w6⟩ := hW α h1 h2 c hc K S B Cl R hD hAx x hx
  have w3 : ∀ n ∈ S.resolved, ∀ n', IntegrableOn (fun p : ℝ × ℝ => p.1 * (crossPair c K S x n n' p).re) K.rect :=
    fun n _ n' => wt_re K (cross_wt c K S x α hc hK hs n n')
  have w5 : ∀ n ∈ S.resolved, IntegrableOn (fun p : ℝ × ℝ => p.1 * (∑' n', crossPair c K S x n n' p).re) K.rect := by
    intro n hn
    refine re_tsum_int (w3 n hn) (w4 n hn) ?_
    filter_upwards [w1] with p hp
    exact ((hp.2.2.1 n hn).1.add (hp.2.2.1 n hn).2)
  have w2 : ∀ n ∈ S.resolved, ∀ n' ∈ S.resolved,
      IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * lowLowPair c K S x n n' p) K.rect :=
    fun n _ n' _ => lowLow_int c K S x α hc hK n n'
  obtain ⟨e1, e2, e3, e4⟩ := energy_facts c K S x α hc hK hs hm hM hT
  have hR := densityRegular_of_series hM α h1 h2 c hc K S B Cl R hD hAx x hx
  refine ⟨w1, e1, hR.1, e2, e3, hR.2.2.2.2.2.2.1, e4, w2, hR.2.2.2.2.1, w3, w4, w5, w6, fun i E hE => ?_⟩
  have hE12 : AEStronglyMeasurable E volume ∧ Integrable (fun y => entrySq (E y)) := by
    rcases hE with rfl | rfl
    · exact ⟨(hc.modelActuatorGrad_data i).1, (hc.modelActuatorGrad_data i).2.1⟩
    · exact ⟨(hc.modelPin_data i).1, (hc.modelPin_data i).2.1⟩
  have f2 := field_summ c K S x hK hm hs hGS E hE12.1 hE12.2
  have f1 : ∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * (fieldSharp c K S x E n p).re) K.rect :=
    fun n => wt_re K (field_wt c K S x hK hs E hE12.1 hE12.2 n)
  have f3 : IntegrableOn (fun p : ℝ × ℝ => p.1 * (∑' n, fieldSharp c K S x E n p).re) K.rect := by
    refine re_tsum_int f1 f2 ?_
    filter_upwards [w1] with p hp
    rcases hE with rfl | rfl
    · exact (hp.2.2.2 i).1
    · exact (hp.2.2.2 i).2
  exact ⟨f1, f2, f3, fun n _ => fieldLow_int c K S x hK E hE12.1 hE12.2 n⟩

end Breakdown.CellCert.CellAnalysis
