import Breakdown.Torus.HeatComparisonStatements
import Breakdown.Torus.FreqTrSeries

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace TorusShellSeries.Internal

theorem center_apply (i : Fin 3) : center i = 1 / 2 := by
  simp [center, unitVector, Pi.single_apply]

theorem mem_cell {h b : ℝ} (hh : 0 < h) (hhb : h * b ≤ 1 / 8) {y : Space}
    (hy : y ∈ Metric.closedBall (0 : Space) b) : center + h • y ∈ cell := by
  show ∀ i, (center + h • y) i ∈ Icc (0 : ℝ) 1
  intro i
  have h1 : |y i| ≤ b := by
    have := PiLp.norm_apply_le y i
    rw [Real.norm_eq_abs] at this
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    linarith
  have h2 : |h * y i| ≤ 1 / 8 :=
    calc |h * y i| = h * |y i| := by rw [abs_mul, abs_of_pos hh]
      _ ≤ h * b := mul_le_mul_of_nonneg_left h1 hh.le
      _ ≤ 1 / 8 := hhb
  rw [abs_le] at h2
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, center_apply, mem_Icc]
  constructor <;> linarith [h2.1, h2.2]

theorem qmp_affine {h : ℝ} (hh : h ≠ 0) :
    Measure.QuasiMeasurePreserving (fun y : Space => center + h • y) volume volume :=
  (measurePreserving_add_left volume center).quasiMeasurePreserving.comp
    (Measure.quasiMeasurePreserving_smul volume hh)

theorem freq_eq_zero {k : Lattice} : freq k = 0 ↔ k = 0 := by
  constructor
  · intro hk
    funext i
    have := congrArg (fun v : Space => v i) hk
    simpa [FreqTrSeries.Internal.freq_apply] using this
  · rintro rfl
    simp [freq]

theorem heatFactor_eq {μ : ℝ} (hμ : 0 < μ) (t : ℝ) (k : Lattice) :
    heatFactor (μ * t) k = Freq.heatFactor t (Real.sqrt μ • freq k) := by
  have e : max (μ * t) 0 = μ * max t 0 := by rw [mul_max_of_nonneg _ _ hμ.le, mul_zero]
  rw [heatFactor, Freq.heatFactor, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt hμ.le, e]
  congr 1
  ring

theorem divFree_eq {h : ℝ} (hh : 0 < h) (k : Lattice) (c : Coef) :
    divFree k c = divFreeVec (h • freq k) c := by
  unfold divFree divFreeVec
  by_cases hk : k = 0
  · subst hk
    simp [freq]
  · have hf : freq k ≠ 0 := fun h0 => hk (freq_eq_zero.1 h0)
    have hn : ‖freq k‖ ≠ 0 := norm_ne_zero_iff.2 hf
    rw [if_neg hk, if_neg (smul_ne_zero hh.ne' hf)]
    have e1 : (∑ i, (((h • freq k) i : ℝ) : ℂ) * c i) = (h : ℂ) * divPairing k c := by
      simp [divPairing, FreqTrSeries.Internal.freq_apply, Finset.mul_sum, mul_assoc]
    have e2 : ((‖h • freq k‖ ^ 2 : ℝ) : ℂ) = (h : ℂ) ^ 2 * ((‖freq k‖ ^ 2 : ℝ) : ℂ) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
      push_cast
      ring
    have e3 : Freq.complexifyVec (h • freq k) = (h : ℂ) • latVec k := by
      ext i
      simp [Freq.complexifyVec, latVec, FreqTrSeries.Internal.freq_apply]
    have hn' : ((‖freq k‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 hn
    have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    rw [e1, e2, e3, smul_smul]
    congr 2
    field_simp

theorem divFreeVec_csmul (ξ : Space) (w : ℂ) (c : Coef) : divFreeVec ξ (w • c) = w • divFreeVec ξ c := by
  unfold divFreeVec
  split_ifs
  · rfl
  · have : (∑ i, ((ξ i : ℝ) : ℂ) * (w • c) i) = w * ∑ i, ((ξ i : ℝ) : ℂ) * c i := by
      simp [Finset.mul_sum, mul_left_comm]
    rw [this, smul_sub, smul_smul, mul_div_assoc]

theorem character_shift (k : Lattice) (h : ℝ) (y : Space) :
    character (-k) (center + h • y) * character k center = expChar y (h • freq k) := by
  unfold character expChar
  rw [← Complex.exp_add, FreqTrSeries.Internal.freq_neg]
  congr 1
  simp only [inner_neg_left, inner_add_right, real_inner_smul_right, real_inner_smul_left]
  push_cast
  ring

theorem coeff_smul (r : ℝ) (u : V) (k : Lattice) : coeff (r • u) k = r • coeff u k := by
  show (Real.sqrt (weight k))⁻¹ • (r • (u : Seq) k) = r • ((Real.sqrt (weight k))⁻¹ • (u : Seq) k)
  exact smul_comm _ _ _

theorem coeff_sourceOp {μ τ : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (A : Freq.L2R) (k : Lattice) :
    coeff (sourceOp μ τ A) k =
      heatFactor (μ * τ) k • divFree k (freqTrCoef (fun x => (A : Space → Space) (simCoord μ x)) k) := by
  have e : sourceOp μ τ A = forceV (μ * τ) (fun x => (A : Space → Space) (simCoord μ x)) := by
    show sourceFun μ τ A = _
    rw [sourceFun, if_pos hμ]
  rw [e]
  show (Real.sqrt (weight k))⁻¹ • forceSeq (μ * τ) _ k = _
  rw [forceSeq, if_pos (mul_pos hμ hτ), smul_smul, ← mul_assoc,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (FreqTrSeries.Internal.weight_pos k)).ne', one_mul]

theorem rpow_three_halves {μ : ℝ} (hμ : 0 < μ) : μ ^ (3 / 2 : ℝ) = Real.sqrt μ ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hμ.le]
  norm_num

theorem rpow_quarter_mul {μ : ℝ} (hμ : 0 < μ) : μ ^ (1 / 4 : ℝ) * μ ^ (-(1 / 4 : ℝ)) = 1 := by
  rw [← Real.rpow_add hμ]
  norm_num

theorem source_value (hC : SourceCoefFormula) {b' μ τ : ℝ} (hμ : 0 < μ) (hτ : 0 < τ)
    (hb' : Real.sqrt μ * b' ≤ 1 / 4) (A : Freq.L2R)
    (hA : ∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) (y : Space) (k : Lattice) :
    character (-k) (center + Real.sqrt μ • y) •
        ((μ ^ (1 / 4 : ℝ)) • coeff ((μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ A) k) =
      (Real.sqrt μ ^ 3) • valueDensity τ (⇑A) y (Real.sqrt μ • freq k) := by
  rw [coeff_smul, coeff_sourceOp hμ hτ, hC b' μ hμ hb' A hA k, heatFactor_eq hμ,
    divFree_eq (Real.sqrt_pos.2 hμ), valueDensity, ← Complex.coe_smul (μ ^ (3 / 2 : ℝ)),
    divFreeVec_csmul, divFreeVec_csmul]
  have e1 := character_shift k (Real.sqrt μ) y
  have e2 : ((μ ^ (1 / 4 : ℝ) : ℝ) : ℂ) * ((μ ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) = 1 := by
    exact_mod_cast rpow_quarter_mul hμ
  have e3 : ((μ ^ (3 / 2 : ℝ) : ℝ) : ℂ) = ((Real.sqrt μ ^ 3 : ℝ) : ℂ) := by
    rw [rpow_three_halves hμ]
  simp only [← Complex.coe_smul, smul_smul]
  congr 1
  linear_combination
    (((Freq.heatFactor τ (Real.sqrt μ • freq k) : ℝ) : ℂ) * ((μ ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
      ((μ ^ (1 / 4 : ℝ) : ℝ) : ℂ) * ((μ ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) * e1 +
    (((Freq.heatFactor τ (Real.sqrt μ • freq k) : ℝ) : ℂ) * ((μ ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
      expChar y (Real.sqrt μ • freq k)) * e2 +
    (((Freq.heatFactor τ (Real.sqrt μ • freq k) : ℝ) : ℂ) * expChar y (Real.sqrt μ • freq k)) * e3

theorem series_pullback (p : ℝ≥0∞) [Fact (1 ≤ p)] (c : Lattice → Coef)
    (hser : (torusSeries p c : Space → Coef) =ᵐ[volume.restrict cell]
      (fun x => ∑' k, character (-k) x • c k))
    {h b s : ℝ} (hh : 0 < h) (hhb : h * b ≤ 1 / 8) (G : Space → Space → Coef)
    (hG : ∀ y k, character (-k) (center + h • y) • (s • c k) = (h ^ 3) • G y (h • freq k)) :
    ∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : Space) b)),
      s • (torusSeries p c : Space → Coef) (center + h • y) = latticeSum h (G y) := by
  have hcell : MeasurableSet cell := FreqTrSeries.Internal.isCompact_cell.isClosed.measurableSet
  have h1 := (ae_restrict_iff' hcell).1 hser
  have h2 := (qmp_affine hh.ne').ae h1
  filter_upwards [ae_restrict_of_ae h2, ae_restrict_mem Metric.isClosed_closedBall.measurableSet]
    with y hy hyb
  rw [hy (mem_cell hh hhb hyb), latticeSum, ← tsum_const_smul'', ← tsum_const_smul'']
  congr 1
  funext k
  rw [smul_comm s, hG y k]

theorem grad_identity {c : Lattice → Coef} {G : Space → Space → Coef} {h s : ℝ} (j : Fin 3)
    (hG : ∀ y k, character (-k) (center + h • y) • (s • c k) = (h ^ 3) • G y (h • freq k))
    (y : Space) (k : Lattice) :
    character (-k) (center + h • y) • ((s * h) • ((2 * π * Complex.I * (k j : ℂ)) • c k)) =
      (h ^ 3) • ((2 * π * Complex.I * (((h • freq k) j : ℝ) : ℂ)) • G y (h • freq k)) := by
  rw [smul_comm (h ^ 3), ← hG y k]
  have e : ((h • freq k) j : ℝ) = h * (k j : ℝ) := by
    simp [FreqTrSeries.Internal.freq_apply]
  rw [e]
  simp only [← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  ring

theorem rpow_free {μ : ℝ} (hμ : 0 < μ) :
    μ ^ (1 / 4 : ℝ) * μ ^ (1 / 4 : ℝ) * μ = Real.sqrt μ ^ 3 := by
  rw [← rpow_three_halves hμ, ← Real.rpow_add hμ, ← Real.rpow_add_one hμ.ne']
  norm_num

theorem rpow_grad {μ : ℝ} (hμ : 0 < μ) : μ ^ (3 / 4 : ℝ) = μ ^ (1 / 4 : ℝ) * Real.sqrt μ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hμ]
  norm_num

theorem free_value (hT : TransplantCoefFormula) (hD : CoefDeriv) (hTS : TransplantSmooth)
    {φ : Space → Space} (hφ : IsTestField φ) {b' μ τ : ℝ} (hsh : IsShellScale μ b')
    (hsupp : tsupport φ ⊆ Metric.closedBall 0 b') (y : Space) (k : Lattice) :
    character (-k) (center + Real.sqrt μ • y) •
        ((μ ^ (1 / 4 : ℝ)) • coeff ((μ ^ (1 / 4 : ℝ)) • heat (μ * τ) (toV (transplantField μ φ))) k) =
      (Real.sqrt μ ^ 3) • freeDensity τ φ y (Real.sqrt μ • freq k) := by
  obtain ⟨hs1, hs2, hs3, -⟩ := hTS φ μ b' hφ.1 hφ.2.2 hsh hsupp
  have hμ := hsh.1
  have hb4 : Real.sqrt μ * b' ≤ 1 / 4 := by linarith [hsh.2.2.2]
  rw [coeff_smul, coeff_heat, FreqTrSeries.Internal.coeff_toV hD hs1 hs2 hs3,
    hT φ hφ b' μ hμ hb4 hsupp k, heatFactor_eq hμ, freeDensity]
  have e1 := character_shift k (Real.sqrt μ) y
  have e2 : ((μ ^ (1 / 4 : ℝ) : ℝ) : ℂ) * ((μ ^ (1 / 4 : ℝ) : ℝ) : ℂ) * ((μ : ℝ) : ℂ) =
      ((Real.sqrt μ ^ 3 : ℝ) : ℂ) := by
    rw [← rpow_free hμ]
    push_cast
    ring
  simp only [← Complex.coe_smul, smul_smul]
  congr 1
  linear_combination
    (((Freq.heatFactor τ (Real.sqrt μ • freq k) : ℝ) : ℂ) * ((μ ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
      ((μ ^ (1 / 4 : ℝ) : ℝ) : ℂ) * ((μ : ℝ) : ℂ)) * e1 +
    (((Freq.heatFactor τ (Real.sqrt μ • freq k) : ℝ) : ℂ) * expChar y (Real.sqrt μ • freq k)) * e2

theorem summable_heat {t : ℝ} (ht : 0 < t) : Summable (heatFactor t) := by
  refine (Internal.summable_exp_freq (c := 4 * π ^ 2 * t) (by positivity)).congr fun k => ?_
  rw [heatFactor, max_eq_left ht.le]
  congr 1
  ring

theorem norm_coeff_source_le {μ τ : ℝ} (hμ : 0 < μ) (hτ : 0 < τ) (A : Freq.L2R) (k : Lattice) :
    ‖coeff ((μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ A) k‖ ≤
      (μ ^ (-(1 / 4 : ℝ)) * (2 * ∫ x in cell, ‖complexify ((A : Space → Space) (simCoord μ x))‖)) *
        heatFactor (μ * τ) k := by
  rw [coeff_smul, coeff_sourceOp hμ hτ, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hμ _), abs_of_nonneg (Internal.heatFactor_nonneg _ _)]
  have h1 := (Internal.norm_divFree_le k (freqTrCoef (fun x => (A : Space → Space) (simCoord μ x)) k)).trans
    (mul_le_mul_of_nonneg_left (FreqTrSeries.Internal.norm_freqTrCoef_le k) zero_le_two)
  have h2 := Internal.heatFactor_nonneg (μ * τ) k
  have h3 := Real.rpow_pos_of_pos hμ (-(1 / 4 : ℝ))
  calc μ ^ (-(1 / 4 : ℝ)) * (heatFactor (μ * τ) k *
        ‖divFree k (freqTrCoef (fun x => (A : Space → Space) (simCoord μ x)) k)‖) ≤
      μ ^ (-(1 / 4 : ℝ)) * (heatFactor (μ * τ) k *
        (2 * ∫ x in cell, ‖complexify ((A : Space → Space) (simCoord μ x))‖)) := by gcongr
    _ = _ := by ring

theorem summable_grad_of_bound {z : V} {C t : ℝ} (hC : 0 ≤ C) (ht : 0 < t)
    (hz : ∀ k, ‖coeff z k‖ ≤ C * heatFactor t k) (j : Fin 3) :
    Summable fun k => ‖gradCoef j z k‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    ((Internal.summable_weight_heat (half_pos ht)).mul_left C)
  have hw := Trilinear.Internal.one_le_weight k
  have h1 : ‖gradCoef j z k‖ ≤ Real.sqrt (weight k) * ‖coeff z k‖ := by
    have := Real.sqrt_le_sqrt (TorusSeries.Internal.norm_gradCoef_sq_le j z k)
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (by linarith), Real.sqrt_sq (norm_nonneg _)] at this
  have h2 : Real.sqrt (weight k) ≤ weight k := by
    have := Real.sqrt_le_sqrt (show weight k ≤ weight k ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at this
  have h3 : heatFactor t k = heatFactor (t / 2) k ^ 2 := by
    rw [sq, ← Internal.heatFactor_add (by linarith) (by linarith), add_halves]
  have h4 := Internal.heatFactor_nonneg t k
  calc ‖gradCoef j z k‖ ≤ Real.sqrt (weight k) * (C * heatFactor t k) :=
        h1.trans (mul_le_mul_of_nonneg_left (hz k) (Real.sqrt_nonneg _))
    _ ≤ weight k * (C * heatFactor t k) := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = C * (weight k * heatFactor (t / 2) k ^ 2) := by rw [← h3]; ring

theorem summable_of_density {c : Lattice → Coef} {G : Space → Space → Coef} {h s K : ℝ}
    (hh : 0 < h) (hs : 0 < s)
    (hG : ∀ y k, character (-k) (center + h • y) • (s • c k) = (h ^ 3) • G y (h • freq k))
    (hK : ∀ ξ, ‖G 0 ξ‖ ≤ K * (1 + ‖ξ‖) ^ (-4 : ℝ))
    (hsum : Summable fun k : Lattice => (1 + ‖h • freq k‖) ^ (-4 : ℝ)) :
    Summable fun k => ‖c k‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    (hsum.mul_left (h ^ 3 / s * K))
  have e := congrArg norm (hG 0 k)
  rw [norm_smul, norm_smul, norm_smul, FreqTrSeries.Internal.norm_character, one_mul,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hs, abs_of_pos (pow_pos hh 3)] at e
  have e' : ‖c k‖ = h ^ 3 / s * ‖G 0 (h • freq k)‖ := by
    field_simp
    linarith
  rw [e', mul_assoc]
  exact mul_le_mul_of_nonneg_left (hK _) (by positivity)

end TorusShellSeries.Internal

open TorusShellSeries.Internal

theorem torusSourceSeries_of (hP : TorusSeriesPointwise) (hC : SourceCoefFormula) :
    TorusSourceSeries := by
  intro b b' μ τ hsh hb' hτ A hA
  obtain ⟨hμ, -, -, hhb⟩ := hsh
  have hh : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have hval := source_value hC hμ hτ hb' A hA
  have hM : 0 ≤ μ ^ (-(1 / 4 : ℝ)) *
      (2 * ∫ x in cell, ‖complexify ((A : Space → Space) (simCoord μ x))‖) :=
    mul_nonneg (Real.rpow_nonneg hμ.le _) (mul_nonneg zero_le_two (integral_nonneg fun _ => norm_nonneg _))
  have hb := norm_coeff_source_le hμ hτ A
  have hsum : Summable fun k => ‖coeff ((μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ A) k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb ((summable_heat (mul_pos hμ hτ)).mul_left _)
  refine ⟨series_pullback 6 _ (hP _ hsum).2 hh hhb _ hval, fun j => ?_⟩
  refine series_pullback 2 _ (hP _ (summable_grad_of_bound hM (mul_pos hμ hτ) hb j)).1 hh hhb
    (gradDensity j τ A) fun y k => ?_
  rw [rpow_grad hμ]
  exact grad_identity j hval y k

theorem torusFreeSeries_of (hP : TorusSeriesPointwise) (hT : TransplantCoefFormula) (hD : CoefDeriv)
    (hTS : TransplantSmooth) (hS : StepIntegral) (hF : FreeDensityBounds) : TorusFreeSeries := by
  intro φ hφ b b' μ τ hsh hsh' hτ hsupp
  have hμ := hsh.1
  have hh : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have hs : 0 < μ ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hμ _
  have hs' : 0 < μ ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hμ _
  have hval := free_value hT hD hTS hφ (τ := τ) hsh' hsupp
  obtain ⟨K, hK⟩ := hF φ hφ 0 (1 / (τ + 1)) (by positivity)
  have hτI : τ ∈ Icc 0 (1 / (τ + 1))⁻¹ := ⟨hτ, by rw [one_div, inv_inv]; linarith⟩
  have hy0 : ‖(0 : Space)‖ ≤ 0 := by simp
  have hsq := (hS _ hh).2.2
  have hsum := summable_of_density hh hs hval (fun ξ => (hK 0 hy0 τ hτI ξ).1) hsq
  refine ⟨series_pullback 6 _ (hP _ hsum).2 hh hsh.2.2.2 _ hval, fun j => ?_⟩
  have hgrad : ∀ y k, character (-k) (center + Real.sqrt μ • y) •
      ((μ ^ (3 / 4 : ℝ)) • gradCoef j ((μ ^ (1 / 4 : ℝ)) • heat (μ * τ) (toV (transplantField μ φ))) k) =
      (Real.sqrt μ ^ 3) • freeGradDensity j τ φ y (Real.sqrt μ • freq k) := fun y k => by
    rw [rpow_grad hμ]
    exact grad_identity j hval y k
  have hgsum := summable_of_density hh hs' hgrad (fun ξ => (hK 0 hy0 τ hτI ξ).2 j) hsq
  exact series_pullback 2 _ (hP _ hgsum).1 hh hsh.2.2.2 (freeGradDensity j τ φ) hgrad

end Breakdown.Periodic
