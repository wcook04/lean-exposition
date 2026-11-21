import Breakdown.Torus.HeatComparisonStatements
import Breakdown.FreqTr.BilinTestFormula
import Breakdown.FreqTr.H1Consistency

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace DivFreeProjection.Internal

open Freq Freq.Internal.H1Consistency

theorem longitudinal_coord (ξ : Space) (z : Coef) (j : Fin 3) :
    (longitudinal ξ z) j =
      (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * (∑ i, ((ξ i : ℝ) : ℂ) * z i) * ((ξ j : ℝ) : ℂ) := by
  rw [longitudinal_apply]
  simp [PiLp.inner_apply, freqVec, complexifyVec, Complex.real_smul, mul_comm, mul_assoc]

theorem divFreeVec_eq (ξ : Space) (c : Coef) : divFreeVec ξ c = c - longitudinal ξ c := by
  unfold divFreeVec
  split_ifs with h
  · subst h
    simp [longitudinal]
  · congr 1
    ext j
    rw [longitudinal_coord]
    simp only [PiLp.smul_apply, smul_eq_mul, complexifyVec]
    simp [div_eq_mul_inv, mul_comm]

theorem conj_longitudinal_neg (ξ : Space) (z : Coef) :
    conjVec (longitudinal (-ξ) z) = longitudinal ξ (conjVec z) := by
  ext j
  have e1 : (conjVec (longitudinal (-ξ) z)) j = star ((longitudinal (-ξ) z) j) := rfl
  have e2 : ∀ i, (conjVec z) i = star (z i) := fun i => rfl
  rw [e1, longitudinal_coord, longitudinal_coord]
  simp only [e2, norm_neg, star_mul', PiLp.neg_apply, Complex.star_def, Complex.conj_ofReal,
    map_neg, Complex.ofReal_neg, neg_mul, Finset.sum_neg_distrib]
  simp only [map_sum, map_mul, Complex.conj_ofReal]
  ring

theorem longitudinal_proj (ξ : Space) (z : Coef) : longitudinal ξ (z - longitudinal ξ z) = 0 := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [longitudinal]
  have hn : ‖ξ‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hξ)
  set S : ℂ := ∑ i, ((ξ i : ℝ) : ℂ) * z i with hS
  have hr : (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ((∑ i, (ξ i) ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← norm_sq_eq, ← Complex.ofReal_mul, inv_mul_cancel₀ hn, Complex.ofReal_one]
  have hs : ∑ i, ((ξ i : ℝ) : ℂ) * (z - longitudinal ξ z) i = 0 := by
    simp only [PiLp.sub_apply, longitudinal_coord, mul_sub, Finset.sum_sub_distrib, ← hS]
    rw [Finset.sum_congr rfl (fun i _ => show ((ξ i : ℝ) : ℂ) * ((((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * S * ((ξ i : ℝ) : ℂ)) =
        ((((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * S) * (((ξ i) ^ 2 : ℝ) : ℂ) by push_cast; ring), ← Finset.mul_sum]
    rw [← Complex.ofReal_sum]
    linear_combination (-S) * hr
  ext j
  rw [longitudinal_coord, hs]
  simp

theorem real_inner_coef (x y : Coef) : inner ℝ x y = RCLike.re (inner ℂ x y) := rfl

theorem inner_longitudinal (ξ : Space) (a b : Coef) :
    inner ℝ (longitudinal ξ a) b = inner ℝ a (longitudinal ξ b) := by
  rw [real_inner_coef, real_inner_coef]
  congr 1
  rw [longitudinal_apply, longitudinal_apply, ← Complex.coe_smul, ← Complex.coe_smul, inner_smul_left,
    inner_smul_left, inner_smul_right, inner_smul_right, ← inner_conj_symm a (freqVec ξ)]
  simp only [Complex.conj_ofReal]
  ring

theorem freqTr_ae (h2 : FreqTrL1L2) {b' : ℝ} {A : L2R}
    (hA : ∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) :
    (freqTrR (Freq.complexify A) : Space → CSpace) =ᵐ[volume] freqTrVec (⇑A) := by
  set f : Space → CSpace := fun x => complexifyVec (A x) with hf
  have hf2 : MemLp f 2 volume := complexifyVec.comp_memLp' (Lp.memLp A)
  have hind : (Metric.closedBall (0 : Space) b').indicator f =ᵐ[volume] f := by
    filter_upwards [hA] with y hy
    by_cases hyB : y ∈ Metric.closedBall (0 : Space) b'
    · exact indicator_of_mem hyB f
    · rw [indicator_of_notMem hyB, hf]
      simp [hy hyB]
  have hf1 : MemLp f 1 volume := by
    have h := (hf2.ae_eq hind.symm).mono_exponent_of_measure_support_ne_top
      (p := 1) (s := Metric.closedBall (0 : Space) b') (fun x hx => indicator_of_notMem hx f)
      measure_closedBall_lt_top.ne (by norm_num)
    exact h.ae_eq hind
  have hc : Freq.complexify A = toLpOrZero 2 f := by
    apply Lp.ext
    filter_upwards [coe_complexify_ae A, Freq.Internal.BilinTestFormula.toLpOrZero_ae hf2] with x e1 e2
    rw [e1, e2]
  rw [hc]
  exact h2 f hf1 hf2

theorem heatFactor_neg (τ : ℝ) (ξ : Space) : Freq.heatFactor τ (-ξ) = Freq.heatFactor τ ξ := by
  simp [Freq.heatFactor, norm_neg]

theorem phiFactor_neg (τ : ℝ) (ξ : Space) : phiFactor τ (-ξ) = phiFactor τ ξ := by
  simp [phiFactor, norm_neg]

theorem norm_heat_smul_le (τ : ℝ) (ξ : Space) :
    ‖Freq.heatFactor τ ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ 1 := by
  refine (norm_smul_le _ _).trans ?_
  refine (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)).trans ?_
  unfold Freq.heatFactor
  rw [mul_one, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
  have : 0 ≤ 4 * π ^ 2 * max τ 0 * ‖ξ‖ ^ 2 := by positivity
  linarith

theorem norm_phi_smul_le {τ : ℝ} (hτ : 0 < τ) (ξ : Space) :
    ‖phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ 1 + 1 / τ := by
  refine (norm_smul_le _ _).trans ?_
  refine (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)).trans ?_
  have hp : 0 ≤ phiFactor τ ξ := by unfold phiFactor; positivity
  rw [mul_one, Real.norm_eq_abs, abs_of_nonneg hp]
  unfold phiFactor
  have he := Real.add_one_le_exp (4 * π ^ 2 * τ * ‖ξ‖ ^ 2)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  have h1 : (1 + 1 / τ) * (4 * π ^ 2 * τ * ‖ξ‖ ^ 2 + 1) =
      4 * π ^ 2 * τ * ‖ξ‖ ^ 2 + 1 + (2 * π * ‖ξ‖) ^ 2 + 1 / τ := by
    field_simp
    ring
  have h2 : 2 * π * ‖ξ‖ ≤ (1 + 1 / τ) * (4 * π ^ 2 * τ * ‖ξ‖ ^ 2 + 1) := by
    rw [h1]
    have : 0 ≤ 1 / τ := by positivity
    nlinarith [sq_nonneg (2 * π * ‖ξ‖ - 1)]
  calc 2 * π * ‖ξ‖ ≤ (1 + 1 / τ) * (4 * π ^ 2 * τ * ‖ξ‖ ^ 2 + 1) := h2
    _ ≤ (1 + 1 / τ) * Real.exp (4 * π ^ 2 * τ * ‖ξ‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left he; positivity

theorem heat_ae (h1 : FieldOpRealized) (τ : ℝ) (f : L2C) :
    (fieldOp id (fun ξ => Freq.heatFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) f : Space → CSpace)
      =ᵐ[volume] fun ξ => Freq.heatFactor τ ξ • f ξ := by
  have hc : Continuous (fun ξ : Space => Freq.heatFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) := by
    unfold Freq.heatFactor; fun_prop
  have := Freq.Internal.BilinTestFormula.fieldOp_id_ae h1 _ 1 hc.aestronglyMeasurable
    (norm_heat_smul_le τ) f
  simpa using this

theorem phi_ae (h1 : FieldOpRealized) {τ : ℝ} (hτ : 0 < τ) (f : L2C) :
    (fieldOp id (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) f : Space → CSpace)
      =ᵐ[volume] fun ξ => phiFactor τ ξ • f ξ := by
  have hc : Continuous (fun ξ : Space => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) := by
    unfold phiFactor; fun_prop
  have := Freq.Internal.BilinTestFormula.fieldOp_id_ae h1 _ (1 + 1 / τ) hc.aestronglyMeasurable
    (norm_phi_smul_le hτ) f
  simpa using this

theorem divFree_mem_sig (h1 : FieldOpRealized) (W : L2C) (hW : reflConj W = W) :
    W - fieldOp id longitudinal W ∈ Sig := by
  have hs : ((W - fieldOp id longitudinal W : L2C) : Space → CSpace) =ᵐ[volume]
      fun ξ => W ξ - longitudinal ξ (W ξ) := by
    filter_upwards [Lp.coeFn_sub W (fieldOp id longitudinal W), longitudinal_ae h1 W] with ξ e1 e2
    rw [e1, Pi.sub_apply, e2]
  have hWh : ∀ᵐ ξ ∂volume, conjVec (W (-ξ)) = W ξ := by
    have h := reflConj_ae h1 W
    rw [hW] at h
    filter_upwards [h] with ξ e using e.symm
  rw [mem_sig_iff]
  constructor
  · apply Lp.ext
    filter_upwards [reflConj_ae h1 (W - fieldOp id longitudinal W), ae_comp_neg hs, hs, hWh]
      with ξ e1 e2 e3 e4
    rw [e1, e2, e3, map_sub, conj_longitudinal_neg, e4]
  · apply Lp.ext
    filter_upwards [longitudinal_ae h1 (W - fieldOp id longitudinal W), hs,
      Lp.coeFn_zero CSpace 2 (volume : Measure Space)] with ξ e1 e2 e3
    rw [e1, e2, e3, longitudinal_proj]
    rfl

theorem ae_longitudinal_of_mem (h1 : FieldOpRealized) {t : L2C} (ht : t ∈ Sig) :
    ∀ᵐ ξ ∂volume, longitudinal ξ (t ξ) = 0 := by
  have h := longitudinal_ae h1 t
  rw [((mem_sig_iff t).1 ht).2] at h
  filter_upwards [h, Lp.coeFn_zero CSpace 2 (volume : Measure Space)] with ξ e1 e2
  rw [← e1, e2]
  rfl

end DivFreeProjection.Internal

open DivFreeProjection.Internal Freq.Internal.H1Consistency in
theorem heatDivFreeFactor (h1 : Freq.FieldOpRealized) (h2 : Freq.FreqTrL1L2)
    (h3 : Freq.FreqTrConjSym) : HeatDivFreeFactor := by
  intro b' τ hτ A hA
  set W : Freq.L2C := Freq.freqTrR (Freq.complexify A) with hWdef
  set s : Freq.L2C := W - Freq.fieldOp id Freq.longitudinal W with hsdef
  set H := Freq.fieldOp id (fun ξ => Freq.heatFactor τ ξ • ContinuousLinearMap.id ℝ Freq.CSpace) with hHdef
  set M := Freq.fieldOp id (fun ξ => Freq.phiFactor τ ξ • ContinuousLinearMap.id ℝ Freq.CSpace) with hMdef
  have hWfreqTr := freqTr_ae h2 hA
  have hs : (s : Space → Freq.CSpace) =ᵐ[volume] fun ξ => W ξ - Freq.longitudinal ξ (W ξ) := by
    filter_upwards [Lp.coeFn_sub W (Freq.fieldOp id Freq.longitudinal W), longitudinal_ae h1 W]
      with ξ e1 e2
    rw [e1, Pi.sub_apply, e2]
  have hsig : s ∈ Freq.Sig := divFree_mem_sig h1 W (h3 A)
  have hg : H s ∈ Freq.Sig := mem_sig_of_ae h1 hsig (Freq.heatFactor τ) (heatFactor_neg τ) (heat_ae h1 τ s)
  have hv : M s ∈ Freq.Sig := mem_sig_of_ae h1 hsig (Freq.phiFactor τ) (phiFactor_neg τ) (phi_ae h1 hτ s)
  have hp : (Freq.projX (M W) : Freq.L2C) = M s := by
    rw [Freq.projX, Submodule.coe_orthogonalProjectionOnto_apply]
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hv
    intro t ht
    rw [MeasureTheory.L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_sub (M W) (M s), phi_ae h1 hτ W, phi_ae h1 hτ s, hs,
      ae_longitudinal_of_mem h1 ht] with ξ e1 e2 e3 e4 e5
    rw [e1, Pi.sub_apply, e2, e3, e4, ← smul_sub, sub_sub_cancel, real_inner_smul_left,
      inner_longitudinal, e5, inner_zero_right, mul_zero]
    rfl
  have hhl : (Freq.heatDivFree τ A : Freq.L2C) = M s := hp
  refine ⟨⟨H s, hg⟩, ?_, ?_⟩
  · filter_upwards [heat_ae h1 τ s, hs, hWfreqTr] with ξ e1 e2 e3
    show (H s : Space → Freq.CSpace) ξ = _
    rw [e1, e2, e3, divFreeVec_eq]
  · unfold Freq.IsHalfSspOf
    rw [hhl]
    filter_upwards [phi_ae h1 hτ s, heat_ae h1 τ s] with ξ e1 e2
    show (M s : Space → Freq.CSpace) ξ = _ • (H s : Space → Freq.CSpace) ξ
    rw [e1, e2, smul_smul]
    congr 1
    unfold Freq.phiFactor Freq.heatFactor
    rw [max_eq_left hτ.le]

end Breakdown.Periodic
