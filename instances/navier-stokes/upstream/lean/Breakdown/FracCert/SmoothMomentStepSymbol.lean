import Breakdown.FracCert.StatementsSmooth
import Breakdown.Uniqueness.RegAprioriAuxMildPart1
import Breakdown.Uniqueness.RegToolkit
import Breakdown.Uniqueness.RegLocalAuxEstPart3
import Breakdown.Frac.RegPowerBilinPhys
import Breakdown.Frac.RegPowerHeatSolenoidal
import Breakdown.Frac.RExports
import Breakdown.FreqTr.H1Consistency
import Breakdown.Cert.ProjectionSpec
import Breakdown.Uniqueness.RegPhysAuxPressurePart1
import Breakdown.Uniqueness.RegEmbed
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

private theorem norm_sum_le_components (z : CSpace) : ‖z‖ ≤ ∑ i, ‖z i‖ := by
  rw [EuclideanSpace.norm_eq]
  have hs : 0 ≤ ∑ i, ‖z i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  calc Real.sqrt (∑ i, ‖z i‖ ^ 2) ≤ Real.sqrt ((∑ i, ‖z i‖) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => norm_nonneg _)
    _ = ∑ i, ‖z i‖ := Real.sqrt_sq hs

private theorem enorm_advection_le {f : Space → CSpace} (hf : IsSolenoidalSymbol f)
    (hm : AEStronglyMeasurable f volume) (h1 : freqL1Norm f < ⊤) (h2 : gradFreqL1Norm f < ⊤)
    (h3 : hsNormSq 1 f < ⊤) (ξ : Space) :
    ‖advectionSymbol f ξ‖ₑ ≤ ENNReal.ofReal (2 * π * ‖ξ‖) * convEnormSum f ξ := by
  rw [advectionSymbol_eq_div hf hm h1 h2 h3 ξ, ← ofReal_norm]
  have hreal : ‖(WithLp.toLp 2 (fun i => 2 * (π : ℂ) * Complex.I *
      ∑ j, ((ξ j : ℝ) : ℂ) * convC (fun η => f η j) (fun η => f η i) ξ) : CSpace)‖ ≤
      2 * π * ‖ξ‖ * ∑ i, ∑ j, ‖convC (fun η => f η j) (fun η => f η i) ξ‖ := by
    refine (norm_sum_le_components _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc ‖2 * (π : ℂ) * Complex.I * ∑ j, ((ξ j : ℝ) : ℂ) *
            convC (fun η => f η j) (fun η => f η i) ξ‖ =
          2 * π * ‖∑ j, ((ξ j : ℝ) : ℂ) * convC (fun η => f η j) (fun η => f η i) ξ‖ := by
          rw [norm_mul]
          simp [abs_of_pos pi_pos]
      _ ≤ 2 * π * ∑ j, ‖ξ‖ * ‖convC (fun η => f η j) (fun η => f η i) ξ‖ := by
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [norm_mul, Complex.norm_real]
          gcongr
          exact PiLp.norm_apply_le ξ j
      _ = 2 * π * ‖ξ‖ * ∑ j, ‖convC (fun η => f η j) (fun η => f η i) ξ‖ := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  refine (ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
  simp only [ofReal_norm]

theorem smoothBilinNiceBound (α : ℝ) (hα : 1 < α) (τ : ℝ) (hτ : 0 < τ) (f : Space → CSpace)
    (hm : AEStronglyMeasurable f volume) (hs : IsSolenoidalSymbol f) (hf : ∀ m, hsNormSq m f < ⊤)
    (h1 : freqL1Norm f < ⊤) (h2 : gradFreqL1Norm f < ⊤) :
    ∀ᵐ ξ ∂volume, ‖((fracBilinX α τ (embedX (physField f)) (embedX (physField f)) : X) : L2C) ξ‖ₑ ≤
      ENNReal.ofReal (fracPhiFactor α τ ξ * (2 * π * ‖ξ‖)) * convEnormSum f ξ := by
  have hK := powerBilinPhys_of α hα (fracBilinH1_holds α hα) (powerSolenoidal α hα) f hm hs hf τ hτ
  filter_upwards [hK] with ξ hξ
  have hφ : 0 ≤ fracPhiFactor α τ ξ := by unfold fracPhiFactor; positivity
  rw [hξ, Complex.coe_smul, enorm_smul, Real.enorm_eq_ofReal hφ, ENNReal.ofReal_mul hφ, mul_assoc]
  gcongr
  unfold nonlinSymbol
  rw [enorm_neg]
  refine le_trans ?_ (enorm_advection_le hs hm h1 h2 (hf 1) ξ)
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (norm_divFreeC_le_self ξ _)

namespace SmoothMomentStepSymbol.Internal

def IsBase (h : Space → CSpace) (ξ : Space) : Prop :=
  (∑ i, ((ξ i : ℝ) : ℂ) * h ξ i = 0) ∧ h (-ξ) = conjVec (h ξ)

def ann (n : ℕ) : Set Space := {ξ | ((n : ℝ) + 1)⁻¹ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ (n : ℝ) + 1}

open Classical in
def cutSym (h : Space → CSpace) (n : ℕ) (ξ : Space) : CSpace :=
  if IsBase h ξ ∧ ξ ∈ ann n then h ξ else 0

theorem conjVec_apply (z : CSpace) (i : Fin 3) : (conjVec z) i = star (z i) := rfl

theorem conjVec_conjVec (z : CSpace) : conjVec (conjVec z) = z := by
  ext i
  simp [conjVec_apply]

theorem measurableSet_ann (n : ℕ) : MeasurableSet (ann n) :=
  ((isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const)).measurableSet

theorem mem_ann_neg {n : ℕ} {ξ : Space} (h : ξ ∈ ann n) : -ξ ∈ ann n := by
  simpa [ann, norm_neg] using h

theorem isBase_neg {h : Space → CSpace} {ξ : Space} (hb : IsBase h ξ) : IsBase h (-ξ) := by
  obtain ⟨h1, h2⟩ := hb
  refine ⟨?_, by rw [neg_neg, h2, conjVec_conjVec]⟩
  rw [h2]
  have e : ∑ i, ((((-ξ) i : ℝ)) : ℂ) * (conjVec (h ξ)) i = -star (∑ i, ((ξ i : ℝ) : ℂ) * h ξ i) := by
    simp only [conjVec_apply, star_sum, star_mul', Complex.star_def, Complex.conj_ofReal,
      PiLp.neg_apply, Complex.ofReal_neg, neg_mul, Finset.sum_neg_distrib]
  rw [e, h1, star_zero, neg_zero]

theorem cutSym_sol (h : Space → CSpace) (n : ℕ) : IsSolenoidalSymbol (cutSym h n) := by
  intro ξ
  by_cases hg : IsBase h ξ ∧ ξ ∈ ann n
  · have hg' : IsBase h (-ξ) ∧ -ξ ∈ ann n := ⟨isBase_neg hg.1, mem_ann_neg hg.2⟩
    unfold cutSym
    rw [if_pos hg, if_pos hg']
    exact ⟨hg.1.1, hg.1.2⟩
  · have hg' : ¬ (IsBase h (-ξ) ∧ -ξ ∈ ann n) := fun h' =>
      hg ⟨by simpa using isBase_neg h'.1, by simpa using mem_ann_neg h'.2⟩
    unfold cutSym
    rw [if_neg hg, if_neg hg']
    simp

theorem cutSym_of {h : Space → CSpace} {n : ℕ} {ξ : Space} (hb : IsBase h ξ) :
    cutSym h n ξ = (ann n).indicator h ξ := by
  by_cases hm : ξ ∈ ann n
  · simp [cutSym, hb, hm]
  · simp [cutSym, hm]

theorem norm_cutSym_le (h : Space → CSpace) (n : ℕ) (ξ : Space) : ‖cutSym h n ξ‖ ≤ ‖h ξ‖ := by
  unfold cutSym
  split_ifs <;> simp

theorem norm_cutSym_apply_le (h : Space → CSpace) (n : ℕ) (ξ : Space) (j : Fin 3) :
    ‖cutSym h n ξ j‖ ≤ ‖h ξ‖ :=
  (PiLp.norm_apply_le _ j).trans (norm_cutSym_le h n ξ)

theorem eventually_ann {ξ : Space} (hξ : ξ ≠ 0) : ∀ᶠ n : ℕ in atTop, ξ ∈ ann n := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max ‖ξ‖ ‖ξ‖⁻¹)
  have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := le_max_left ‖ξ‖ ‖ξ‖⁻¹
  have h2 := le_max_right ‖ξ‖ ‖ξ‖⁻¹
  refine ⟨?_, by linarith⟩
  rw [inv_le_comm₀ (by positivity) hpos]
  linarith

theorem isBase_ae (x : X) : ∀ᵐ ξ ∂volume, IsBase (symbolX x) ξ := by
  have hR := Freq.Internal.H1Consistency.reflConj_ae fieldOpRealized_holds (x : L2C)
  rw [Cert.Internal.ProjectionSpec.reflConj_of_mem x.2] at hR
  have hR' := Freq.Internal.H1Consistency.ae_comp_neg hR
  have hL := Cert.Internal.ProjectionSpec.fieldOp_longitudinal_ae (x : L2C)
  rw [Cert.Internal.ProjectionSpec.fieldOp_longitudinal_of_mem x.2] at hL
  filter_upwards [hR', hL, Lp.coeFn_zero CSpace 2 (volume : Measure Space)] with ξ e1 e2 e3
  simp only [neg_neg] at e1
  rw [e3] at e2
  refine ⟨?_, ?_⟩
  · unfold symbolX
    by_cases hξ : ξ = 0
    · subst hξ
      simp
    have hfv : freqVec ξ ≠ 0 := by
      rw [← norm_ne_zero_iff, Freq.Internal.H1Consistency.norm_freqVec]
      exact norm_ne_zero_iff.2 hξ
    have hc : ((‖ξ‖ ^ 2)⁻¹ : ℝ) ≠ 0 := inv_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 hξ))
    rw [Freq.Internal.H1Consistency.longitudinal_apply] at e2
    have hin : inner ℂ (freqVec ξ) ((x : L2C) ξ) = 0 := by
      rcases smul_eq_zero.1 e2.symm with h | h
      · exact absurd h hc
      rcases smul_eq_zero.1 h with h | h
      · exact h
      · exact absurd h hfv
    have hsum : inner ℂ (freqVec ξ) ((x : L2C) ξ) = ∑ i, ((ξ i : ℝ) : ℂ) * (x : L2C) ξ i := by
      simp [freqVec, complexifyVec, PiLp.inner_apply, Complex.conj_ofReal]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [PiLp.smul_apply, Complex.real_smul]
    have e4 : ∀ i, ((ξ i : ℝ) : ℂ) * (((2 * π * ‖ξ‖)⁻¹ : ℝ) * (x : L2C) ξ i) =
        (((2 * π * ‖ξ‖)⁻¹ : ℝ) : ℂ) * (((ξ i : ℝ) : ℂ) * (x : L2C) ξ i) := fun i => by ring
    simp_rw [e4]
    rw [← Finset.mul_sum, ← hsum, hin, mul_zero]
  · unfold symbolX
    rw [norm_neg, e1, map_smul]

theorem aesm_symbolX (x : X) : AEStronglyMeasurable (symbolX x) volume :=
  ((by fun_prop : Measurable fun ξ : Space => ((2 * π * ‖ξ‖)⁻¹ : ℝ)).aestronglyMeasurable).smul
    (Lp.aestronglyMeasurable _)

theorem aesm_cutSym {h : Space → CSpace} (hm : AEStronglyMeasurable h volume)
    (hb : ∀ᵐ ξ ∂volume, IsBase h ξ) (n : ℕ) : AEStronglyMeasurable (cutSym h n) volume :=
  (hm.indicator (measurableSet_ann n)).congr (by
    filter_upwards [hb] with ξ hξ
    exact (cutSym_of hξ).symm)

theorem norm_symbolX_le (x : X) {n : ℕ} {ξ : Space} (hξ : ξ ∈ ann n) :
    ‖symbolX x ξ‖ ≤ ((n : ℝ) + 1) * ‖(x : L2C) ξ‖ := by
  have hpos : 0 < ‖ξ‖ := lt_of_lt_of_le (by positivity) hξ.1
  unfold symbolX
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  gcongr
  rw [inv_le_comm₀ (by positivity) (by positivity)]
  calc ((n : ℝ) + 1)⁻¹ ≤ ‖ξ‖ := hξ.1
    _ ≤ 2 * π * ‖ξ‖ := le_mul_of_one_le_left hpos.le (by linarith [pi_gt_three])

theorem lintegral_sq_ne_top (x : L2C) : ∫⁻ ξ, ‖(x : Space → CSpace) ξ‖ₑ ^ 2 ≠ ⊤ := by
  have hE : eLpNorm (x : Space → CSpace) 2 volume ≠ ⊤ := Lp.eLpNorm_ne_top x
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top] at hE
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at hE
  intro h
  rw [h, ENNReal.top_rpow_of_pos (by norm_num)] at hE
  exact hE rfl

theorem ofReal_mul_enorm_sq {a : ℝ} (ha : 0 ≤ a) (v : CSpace) :
    ENNReal.ofReal a * ‖v‖ₑ ^ 2 = ENNReal.ofReal (a * ‖v‖ ^ 2) := by
  rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem hsNormSq_cutSym_lt_top (x : X) (n m : ℕ) : hsNormSq m (cutSym (symbolX x) n) < ⊤ := by
  set K : ℝ := (1 + ((n : ℝ) + 1) ^ 2) ^ m * ((n : ℝ) + 1) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ ξ, ENNReal.ofReal (hsWeight m ξ) * ‖cutSym (symbolX x) n ξ‖ₑ ^ 2 ≤
      ENNReal.ofReal K * ‖(x : L2C) ξ‖ₑ ^ 2 := by
    intro ξ
    have hw : 0 ≤ hsWeight m ξ := by unfold hsWeight; positivity
    rw [ofReal_mul_enorm_sq hw, ofReal_mul_enorm_sq hK0]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold cutSym
    split_ifs with hg
    · have h1 : hsWeight m ξ ≤ (1 + ((n : ℝ) + 1) ^ 2) ^ m := by
        unfold hsWeight
        gcongr
        exact hg.2.2
      have h2 : ‖symbolX x ξ‖ ^ 2 ≤ ((n : ℝ) + 1) ^ 2 * ‖(x : L2C) ξ‖ ^ 2 := by
        rw [← mul_pow]
        gcongr
        exact norm_symbolX_le x hg.2
      calc hsWeight m ξ * ‖symbolX x ξ‖ ^ 2 ≤
            (1 + ((n : ℝ) + 1) ^ 2) ^ m * (((n : ℝ) + 1) ^ 2 * ‖(x : L2C) ξ‖ ^ 2) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = K * ‖(x : L2C) ξ‖ ^ 2 := by rw [hK]; ring
    · rw [norm_zero, zero_pow two_ne_zero, mul_zero]
      positivity
  calc hsNormSq m (cutSym (symbolX x) n) ≤ ∫⁻ ξ, ENNReal.ofReal K * ‖(x : L2C) ξ‖ₑ ^ 2 :=
        lintegral_mono hpt
    _ = ENNReal.ofReal K * ∫⁻ ξ, ‖(x : L2C) ξ‖ₑ ^ 2 :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_sq_ne_top _).lt_top

theorem symbolL1_cutSym_lt_top {h : Space → CSpace} (hw : freqL1Norm h < ⊤) (n : ℕ) :
    freqL1Norm (cutSym h n) < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono fun ξ => ?_) hw
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (norm_cutSym_le h n ξ)

theorem gradSymbolL1_cutSym_lt_top {h : Space → CSpace} (hw : freqL1Norm h < ⊤) (n : ℕ) :
    gradFreqL1Norm (cutSym h n) < ⊤ := by
  have hpt : ∀ ξ, ENNReal.ofReal ‖ξ‖ * ‖cutSym h n ξ‖ₑ ≤ ENNReal.ofReal ((n : ℝ) + 1) * ‖h ξ‖ₑ := by
    intro ξ
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold cutSym
    split_ifs with hg
    · exact mul_le_mul_of_nonneg_right hg.2.2 (norm_nonneg _)
    · simp only [norm_zero, mul_zero]
      positivity
  calc gradFreqL1Norm (cutSym h n) ≤ ∫⁻ ξ, ENNReal.ofReal ((n : ℝ) + 1) * ‖h ξ‖ₑ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal ((n : ℝ) + 1) * freqL1Norm h :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hw

theorem ae_ne (a : Space) : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ a := by
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton a)] with ξ hξ using hξ

theorem tendsto_lintegral_cut (x : L2C) :
    Tendsto (fun n : ℕ => ∫⁻ ξ, (ann n)ᶜ.indicator (fun ξ => ‖(x : Space → CSpace) ξ‖ₑ ^ 2) ξ)
      atTop (𝓝 0) := by
  have hmeas : Measurable fun ξ => ‖(x : Space → CSpace) ξ‖ₑ ^ 2 :=
    (Lp.stronglyMeasurable x).measurable.enorm.pow_const 2
  have := tendsto_lintegral_of_dominated_convergence (fun ξ => ‖(x : Space → CSpace) ξ‖ₑ ^ 2)
    (fun n => hmeas.indicator (measurableSet_ann n).compl)
    (fun n => ae_of_all _ fun ξ => Set.indicator_le_self _ _ ξ) (lintegral_sq_ne_top x)
    (f := fun _ => 0) (by
      filter_upwards [ae_ne 0] with ξ hξ
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ann hξ] with n hn
      simp [hn])
  simpa using this

theorem smul_symbolX (x : X) {ξ : Space} (hξ : ξ ≠ 0) :
    (((2 * π * ‖ξ‖ : ℝ)) : ℂ) • symbolX x ξ = (x : L2C) ξ := by
  have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  unfold symbolX
  rw [Complex.coe_smul, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

theorem approx_tendsto (x : X) :
    Tendsto (fun n : ℕ => embedX (physField (cutSym (symbolX x) n))) atTop (𝓝 x) := by
  have hb := isBase_ae x
  have hmn := aesm_cutSym (aesm_symbolX x) hb
  rw [tendsto_subtype_rng, Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have e : ∀ n : ℕ, eLpNorm (⇑(embedX (physField (cutSym (symbolX x) n)) : L2C) - ⇑(x : L2C)) 2 volume =
      (∫⁻ ξ, (ann n)ᶜ.indicator (fun ξ => ‖(x : L2C) ξ‖ₑ ^ 2) ξ) ^ (1 / 2 : ℝ) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [coe_embedX_physField fieldOpRealized_holds (hmn n) (cutSym_sol _ n)
      (hsNormSq_cutSym_lt_top x n), hb, ae_ne 0] with ξ e1 hξb hξ0
    rw [Pi.sub_apply, e1, cutSym_of hξb]
    by_cases hm : ξ ∈ ann n
    · rw [Set.indicator_of_mem hm, smul_symbolX x hξ0, sub_self]
      simp [hm]
    · rw [Set.indicator_of_notMem hm]
      simp [hm]
  simp_rw [e]
  have h := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp
    (tendsto_lintegral_cut (x : L2C))
  rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h

theorem conv_tendsto_ae {h : Space → CSpace} (hm : AEStronglyMeasurable h volume)
    (hb : ∀ᵐ ξ ∂volume, IsBase h ξ) (hw : freqL1Norm h < ⊤) :
    ∀ᵐ ξ ∂volume, Tendsto (fun n => convEnormSum (cutSym h n) ξ) atTop (𝓝 (convEnormSum h ξ)) := by
  have ha := hm.enorm
  have hfin : ∀ᵐ ξ ∂(volume : Measure Space), ∫⁻ η, ‖h η‖ₑ * ‖h (ξ - η)‖ₑ < ⊤ := by
    refine ae_lt_top' (PressureSingle.Internal.aemeasurable_conv ha ha).aemeasurable ?_
    rw [PressureSingle.Internal.lintegral_conv ha ha]
    exact ENNReal.mul_ne_top hw.ne hw.ne
  have hmn := aesm_cutSym hm hb
  filter_upwards [hfin] with ξ hξ
  have hq := quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure Space) ξ
  have hmp := Measure.measurePreserving_sub_left (volume : Measure Space) ξ
  have key : ∀ i j, Tendsto (fun n => convC (fun η => cutSym h n η j) (fun η => cutSym h n η i) ξ)
      atTop (𝓝 (convC (fun η => h η j) (fun η => h η i) ξ)) := by
    intro i j
    unfold convC
    refine tendsto_integral_of_dominated_convergence (fun η => ‖h η‖ * ‖h (ξ - η)‖)
      (fun n => ?_) ?_ (fun n => ae_of_all _ fun η => ?_) ?_
    · exact ((PiLp.continuous_apply 2 _ j).comp_aestronglyMeasurable (hmn n)).mul
        ((PiLp.continuous_apply 2 _ i).comp_aestronglyMeasurable ((hmn n).comp_measurePreserving hmp))
    · refine ⟨hm.norm.mul (hm.comp_measurePreserving hmp).norm, ?_⟩
      show ∫⁻ η, ‖‖h η‖ * ‖h (ξ - η)‖‖ₑ < ⊤
      refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun η => ?_)) hξ
      rw [enorm_mul, enorm_norm, enorm_norm]
    · rw [norm_mul]
      exact mul_le_mul (norm_cutSym_apply_le h n η j) (norm_cutSym_apply_le h n (ξ - η) i)
        (norm_nonneg _) (norm_nonneg _)
    · filter_upwards [hb, hq.ae hb, ae_ne 0, ae_ne ξ] with η h1 h2 h3 h4
      have h4' : ξ - η ≠ 0 := sub_ne_zero.2 (Ne.symm h4)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ann h3, eventually_ann h4'] with n n1 n2
      rw [cutSym_of h1, cutSym_of h2, Set.indicator_of_mem n1, Set.indicator_of_mem n2]
  unfold convEnormSum
  exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
    (continuous_enorm.tendsto _).comp (key i j)

theorem bilin_tendsto (B : X →L[ℝ] X →L[ℝ] X) {y : ℕ → X} {x : X} (hy : Tendsto y atTop (𝓝 x)) :
    Tendsto (fun n => ((B (y n) (y n) : X) : L2C)) atTop (𝓝 ((B x x : X) : L2C)) :=
  (continuous_subtype_val.tendsto _).comp ((B.continuous₂.tendsto (x, x)).comp (hy.prodMk_nhds hy))

end SmoothMomentStepSymbol.Internal

open SmoothMomentStepSymbol.Internal in
theorem smoothBilinSymbolBound (α : ℝ) (hα : 1 < α) (τ : ℝ) (hτ : 0 < τ) (x : X)
    (hx : freqL1Norm (symbolX x) < ⊤) :
    ∀ᵐ ξ ∂volume, ‖((fracBilinX α τ x x : X) : L2C) ξ‖ₑ ≤
      ENNReal.ofReal (fracPhiFactor α τ ξ * (2 * π * ‖ξ‖)) * convEnormSum (symbolX x) ξ := by
  have hb := isBase_ae x
  have hm := aesm_symbolX x
  have hmn := aesm_cutSym hm hb
  have hy := approx_tendsto x
  have hK : Tendsto (fun n : ℕ => ((fracBilinX α τ (embedX (physField (cutSym (symbolX x) n)))
      (embedX (physField (cutSym (symbolX x) n))) : X) : L2C)) atTop
      (𝓝 ((fracBilinX α τ x x : X) : L2C)) :=
    bilin_tendsto (fracBilinX α τ) hy
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hK).exists_seq_tendsto_ae
  have hbd : ∀ n : ℕ, ∀ᵐ ξ ∂volume,
      ‖((fracBilinX α τ (embedX (physField (cutSym (symbolX x) n)))
        (embedX (physField (cutSym (symbolX x) n))) : X) : L2C) ξ‖ₑ ≤
      ENNReal.ofReal (fracPhiFactor α τ ξ * (2 * π * ‖ξ‖)) * convEnormSum (cutSym (symbolX x) n) ξ :=
    fun n => smoothBilinNiceBound α hα τ hτ _ (hmn n) (cutSym_sol _ n)
      (hsNormSq_cutSym_lt_top x n) (symbolL1_cutSym_lt_top hx n) (gradSymbolL1_cutSym_lt_top hx n)
  filter_upwards [hae, ae_all_iff.2 hbd, conv_tendsto_ae hm hb hx] with ξ h1 h2 h3
  exact le_of_tendsto_of_tendsto' ((continuous_enorm.tendsto _).comp h1)
    (ENNReal.Tendsto.const_mul (h3.comp hns.tendsto_atTop) (Or.inr ENNReal.ofReal_ne_top))
    fun k => h2 (ns k)

end Breakdown.FracCert
