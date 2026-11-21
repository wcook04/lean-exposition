import Breakdown.Frac.StTorusShell
import Breakdown.Torus.ShellTorus
import Breakdown.Torus.ShellTorusPhi
import Breakdown.Torus.TrigHs
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace TorusShellLambda.Internal

open ShellTorus.Internal TorusSeries.Internal

def gCoef (g : Lattice → ℝ) (ψ : V) (k : Lattice) : Coef := (weight k * g k : ℝ) • coeff ψ k

def gPhi (g : Lattice → ℝ) (ψ : V) (x : Space) : Space :=
  Freq.realVec (∑' k, character (-k) x • ((weight k * g k : ℝ) • coeff ψ k))

theorem norm_gCoef {g : Lattice → ℝ} (hg0 : ∀ k, 0 ≤ g k) (ψ : V) (k : Lattice) :
    ‖gCoef g ψ k‖ = weight k * g k * ‖coeff ψ k‖ := by
  rw [gCoef, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Internal.weight_pos k).le (hg0 k))]

theorem summable_norm_gCoef {g : Lattice → ℝ} (hg0 : ∀ k, 0 ≤ g k)
    (hgs : Summable fun k => weight k * g k ^ 2) (ψ : V) :
    Summable fun k => ‖gCoef g ψ k‖ := by
  have hw := Trilinear.Internal.hasSum_weight_coeff ψ
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    ((hgs.add hw.summable).mul_left (1 / 2))
  rw [norm_gCoef hg0]
  have hw0 := (Internal.weight_pos k).le
  have := mul_nonneg hw0 (sq_nonneg (g k - ‖coeff ψ k‖))
  nlinarith

theorem sq_norm_gCoef_le {g : Lattice → ℝ} {B : ℝ} (hg0 : ∀ k, 0 ≤ g k) (hg1 : ∀ k, g k ≤ 1)
    (hgB : ∀ k, weight k * g k ≤ B) (ψ : V) (k : Lattice) :
    ‖gCoef g ψ k‖ ^ 2 ≤ B * (weight k * ‖coeff ψ k‖ ^ 2) := by
  rw [norm_gCoef hg0]
  have hw0 := (Internal.weight_pos k).le
  have h0 : 0 ≤ weight k * g k := mul_nonneg hw0 (hg0 k)
  have e : (weight k * g k * ‖coeff ψ k‖) ^ 2 =
      (weight k * g k) * g k * (weight k * ‖coeff ψ k‖ ^ 2) := by ring
  rw [e]
  have ha := mul_nonneg hw0 (sq_nonneg ‖coeff ψ k‖)
  have h2 : weight k * g k * g k ≤ B := (mul_le_of_le_one_right h0 (hg1 k)).trans (hgB k)
  exact mul_le_mul_of_nonneg_right h2 ha

theorem weight_sq_norm_gCoef_le {g : Lattice → ℝ} {B : ℝ} (hg0 : ∀ k, 0 ≤ g k)
    (hgB : ∀ k, weight k * g k ≤ B) (ψ : V) (k : Lattice) :
    weight k * ‖gCoef g ψ k‖ ^ 2 ≤ B ^ 2 * (weight k * ‖coeff ψ k‖ ^ 2) := by
  rw [norm_gCoef hg0]
  have hw0 := (Internal.weight_pos k).le
  have h0 : 0 ≤ weight k * g k := mul_nonneg hw0 (hg0 k)
  have e : weight k * (weight k * g k * ‖coeff ψ k‖) ^ 2 =
      (weight k * g k) ^ 2 * (weight k * ‖coeff ψ k‖ ^ 2) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 (hgB k) 2) (mul_nonneg hw0 (sq_nonneg _))

theorem eLpNorm_gPhi_le (p : ℝ≥0∞) [Fact (1 ≤ p)] {g : Lattice → ℝ} (hg0 : ∀ k, 0 ≤ g k)
    (hgs : Summable fun k => weight k * g k ^ 2) (ψ : V) :
    eLpNorm (gPhi g ψ) p (volume.restrict cell) ≤ ENNReal.ofReal ‖torusSeries p (gCoef g ψ)‖ := by
  have hae : gPhi g ψ =ᵐ[volume.restrict cell]
      fun x => Freq.realVec (torusSeries p (gCoef g ψ) x) :=
    (torusSeries_ae_eq p _ (summable_norm_gCoef hg0 hgs ψ)).mono fun x hx => by
      exact congrArg Freq.realVec hx.symm
  rw [eLpNorm_congr_ae hae, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  exact eLpNorm_mono fun x => ShellDefs.Internal.norm_realVec_le _

theorem torusSeries_two_gCoef_le {g : Lattice → ℝ} {B : ℝ} (hg0 : ∀ k, 0 ≤ g k)
    (hg1 : ∀ k, g k ≤ 1) (hgB : ∀ k, weight k * g k ≤ B) (ψ : V) :
    ‖torusSeries 2 (gCoef g ψ)‖ ^ 2 ≤ B * ‖ψ‖ ^ 2 := by
  have hw := Trilinear.Internal.hasSum_weight_coeff ψ
  have hsum : Summable fun k => ‖gCoef g ψ k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (sq_norm_gCoef_le hg0 hg1 hgB ψ)
      (hw.summable.mul_left _)
  rw [torusSeries_norm_sq _ hsum, ← hw.tsum_eq, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (sq_norm_gCoef_le hg0 hg1 hgB ψ) hsum (hw.summable.mul_left _)

theorem torusSeries_six_gCoef_le (C : ℝ) (hC0 : 0 < C) (hC : ∀ (t : Finset Lattice) (c : Lattice → Coef),
    (∫ x in cell, ‖∑ k ∈ t, character (-k) x • c k‖ ^ (6 : ℝ)) ^ (1 / 6 : ℝ) ≤
      C * (∑ k ∈ t, weight k * ‖c k‖ ^ 2) ^ (1 / 2 : ℝ)) {g : Lattice → ℝ} {B : ℝ}
    (hg0 : ∀ k, 0 ≤ g k) (hgB : ∀ k, weight k * g k ≤ B) (hB : 0 ≤ B) (ψ : V) :
    ‖torusSeries 6 (gCoef g ψ)‖ ≤ C * (B * ‖ψ‖) := by
  have hw := Trilinear.Internal.hasSum_weight_coeff ψ
  have hsum : Summable fun k => weight k * ‖gCoef g ψ k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (Internal.weight_pos k).le (sq_nonneg _))
      (weight_sq_norm_gCoef_le hg0 hgB ψ) (hw.summable.mul_left _)
  have h := norm_tsum_le_of_bound _ (summable_six _ hsum) _
    (fun k => mul_nonneg (Internal.weight_pos k).le (sq_nonneg _)) hsum C hC0.le (norm_sum_six_le hC _)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hC0.le)
  have h2 : ∑' k, weight k * ‖gCoef g ψ k‖ ^ 2 ≤ (B * ‖ψ‖) ^ 2 := by
    rw [mul_pow, ← hw.tsum_eq, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (weight_sq_norm_gCoef_le hg0 hgB ψ) hsum (hw.summable.mul_left _)
  have h3 := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (mul_nonneg hB (norm_nonneg _))] at h3

theorem gPhi_bound (C6 : ℝ) (hC60 : 0 < C6) (hC6 : ∀ (t : Finset Lattice) (c : Lattice → Coef),
    (∫ x in cell, ‖∑ k ∈ t, character (-k) x • c k‖ ^ (6 : ℝ)) ^ (1 / 6 : ℝ) ≤
      C6 * (∑ k ∈ t, weight k * ‖c k‖ ^ 2) ^ (1 / 2 : ℝ)) {g : Lattice → ℝ} {u : ℝ} (hu : 0 < u)
    (hg0 : ∀ k, 0 ≤ g k) (hg1 : ∀ k, g k ≤ 1) (hgB : ∀ k, weight k * g k ≤ 2 * u ^ 4)
    (hgs : Summable fun k => weight k * g k ^ 2) (ψ : V) :
    MemLp (gPhi g ψ) 3 (volume.restrict cell) ∧
      (eLpNorm (gPhi g ψ) 3 (volume.restrict cell)).toReal ≤ 2 * Real.sqrt C6 * u ^ 3 * ‖ψ‖ := by
  set a := ‖torusSeries 2 (gCoef g ψ)‖ with ha_def
  set b := ‖torusSeries 6 (gCoef g ψ)‖ with hb_def
  have hmeas : AEStronglyMeasurable (gPhi g ψ) (volume.restrict cell) := by
    have hae : gPhi g ψ =ᵐ[volume.restrict cell]
        fun x => Freq.realVec (torusSeries 2 (gCoef g ψ) x) :=
      (torusSeries_ae_eq 2 _ (summable_norm_gCoef hg0 hgs ψ)).mono fun x hx => by
        exact congrArg Freq.realVec hx.symm
    exact (Freq.realVec.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)).congr hae.symm
  have key : eLpNorm (gPhi g ψ) 3 (volume.restrict cell) ≤
      ENNReal.ofReal (Real.sqrt a * Real.sqrt b) := by
    calc _ ≤ _ := eLpNorm_three_le _ _ hmeas
      _ ≤ ENNReal.ofReal a ^ (1 / 2 : ℝ) * ENNReal.ofReal b ^ (1 / 2 : ℝ) :=
          mul_le_mul' (ENNReal.rpow_le_rpow (eLpNorm_gPhi_le 2 hg0 hgs ψ) (by norm_num))
            (ENNReal.rpow_le_rpow (eLpNorm_gPhi_le 6 hg0 hgs ψ) (by norm_num))
      _ = _ := by
          rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
            ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
            ← ENNReal.ofReal_mul (by positivity), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  refine ⟨⟨hmeas, key.trans_lt ENNReal.ofReal_lt_top⟩, ?_⟩
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) key).trans ?_
  have hψ := norm_nonneg ψ
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have ha : a ≤ 2 * u ^ 2 * ‖ψ‖ := by
    have h1 : a ^ 2 ≤ (2 * u ^ 2 * ‖ψ‖) ^ 2 := by
      refine (torusSeries_two_gCoef_le hg0 hg1 hgB ψ).trans ?_
      nlinarith [sq_nonneg (u ^ 2 * ‖ψ‖)]
    have h3 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq ha0, Real.sqrt_sq (by positivity)] at h3
  have hb : b ≤ C6 * (2 * u ^ 4 * ‖ψ‖) :=
    torusSeries_six_gCoef_le C6 hC60 hC6 hg0 hgB (by positivity) ψ
  have hab : a * b ≤ (2 * Real.sqrt C6 * u ^ 3 * ‖ψ‖) ^ 2 := by
    have e : (2 * Real.sqrt C6 * u ^ 3 * ‖ψ‖) ^ 2 = 2 * u ^ 2 * ‖ψ‖ * (C6 * (2 * u ^ 4 * ‖ψ‖)) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hC60.le]
      ring
    rw [e]
    exact mul_le_mul ha hb hb0 (by positivity)
  rw [← Real.sqrt_mul ha0]
  calc Real.sqrt (a * b) ≤ Real.sqrt ((2 * Real.sqrt C6 * u ^ 3 * ‖ψ‖) ^ 2) := Real.sqrt_le_sqrt hab
    _ = 2 * Real.sqrt C6 * u ^ 3 * ‖ψ‖ := Real.sqrt_sq (by positivity)

theorem norm_sq_eq_pairing {g : Lattice → ℝ} (hg0 : ∀ k, 0 ≤ g k)
    (hgs : Summable fun k => weight k * g k ^ 2) (F : Space → Space) (hF : IntegrableOn F cell)
    (u : V) (hcu : ∀ k, coeff u k = g k • divFree k (freqTrCoef F k)) :
    ‖u‖ ^ 2 = ∫ x in cell, inner ℝ (F x) (gPhi g u x) := by
  obtain ⟨d, hd⟩ : ∃ d : Lattice → Coef, d = fun k => (weight k * g k : ℝ) • coeff u k :=
    ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = ∫ x in cell, ‖F x‖ := ⟨_, rfl⟩
  have hG : IntegrableOn (fun x => complexify (F x)) cell := Freq.complexifyVec.integrable_comp hF
  have hFk : ∀ k, ‖freqTrCoef F k‖ ≤ M := fun k => by
    rw [hM]
    unfold freqTrCoef
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext x
    rw [norm_smul, FreqTrSeries.Internal.norm_character, one_mul, norm_complexify]
  have hw : ∀ k, 0 ≤ weight k := fun k => (Internal.weight_pos k).le
  have hdk : ∀ k, ‖d k‖ ≤ 2 * M * (weight k * g k ^ 2) := by
    intro k
    rw [hd]
    simp only
    rw [norm_smul, hcu, norm_smul, Real.norm_of_nonneg (mul_nonneg (hw k) (hg0 k)),
      Real.norm_of_nonneg (hg0 k)]
    have hl := (Internal.norm_divFree_le k (freqTrCoef F k)).trans
      (mul_le_mul_of_nonneg_left (hFk k) (by norm_num : (0 : ℝ) ≤ 2))
    calc weight k * g k * (g k * ‖divFree k (freqTrCoef F k)‖)
        ≤ weight k * g k * (g k * (2 * M)) := by
          gcongr
          · exact mul_nonneg (hw k) (hg0 k)
          · exact hg0 k
      _ = 2 * M * (weight k * g k ^ 2) := by ring
  have hsd : Summable fun k => ‖d k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdk (hgs.mul_left _)
  have hpt : ∀ x, inner ℝ (F x) (gPhi g u x) =
      ∑' k, RCLike.re (inner ℂ (d k) (character k x • complexify (F x))) := by
    intro x
    have hsx : Summable fun k => character (-k) x • d k := by
      refine Summable.of_norm (hsd.congr fun k => ?_)
      rw [norm_smul, FreqTrSeries.Internal.norm_character, one_mul]
    have e1 : gPhi g u x = Freq.realVec (∑' k, character (-k) x • d k) := by
      rw [gPhi, hd]
    rw [e1, inner_realVec]
    have e2 : inner ℂ (complexify (F x)) (∑' k, character (-k) x • d k) =
        ∑' k, inner ℂ (complexify (F x)) (character (-k) x • d k) :=
      (innerSL ℂ (complexify (F x))).map_tsum hsx
    have hsi : Summable fun k => inner ℂ (complexify (F x)) (character (-k) x • d k) :=
      hsx.mapL (innerSL ℂ (complexify (F x)))
    rw [e2, show RCLike.re (∑' k, inner ℂ (complexify (F x)) (character (-k) x • d k)) =
      ∑' k, RCLike.re (inner ℂ (complexify (F x)) (character (-k) x • d k)) from
      RCLike.reCLM.map_tsum hsi]
    refine tsum_congr fun k => ?_
    rw [inner_smul_right, inner_smul_right, FreqTrSeries.Internal.character_neg,
      ← inner_conj_symm (complexify (F x)) (d k), ← map_mul]
    exact RCLike.conj_re _
  rw [show (fun x => inner ℝ (F x) (gPhi g u x)) =
    fun x => ∑' k, RCLike.re (inner ℂ (d k) (character k x • complexify (F x))) from funext hpt]
  have hint : ∀ k, Integrable (fun x => RCLike.re (inner ℂ (d k) (character k x • complexify (F x))))
      (volume.restrict cell) := fun k =>
    ((Force.Internal.integrableOn_character_smul k hG).const_inner (d k)).re
  have hnorm : ∀ k, ∫ x in cell, ‖RCLike.re (inner ℂ (d k) (character k x • complexify (F x)))‖ ≤
      ‖d k‖ * M := by
    intro k
    rw [hM, ← integral_const_mul]
    refine integral_mono (hint k).norm (hF.norm.const_mul ‖d k‖) fun x => ?_
    refine (RCLike.norm_re_le_norm _).trans ((norm_inner_le_norm _ _).trans (le_of_eq ?_))
    rw [norm_smul, FreqTrSeries.Internal.norm_character, one_mul, norm_complexify]
  have hsum : Summable fun k =>
      ∫ x in cell, ‖RCLike.re (inner ℂ (d k) (character k x • complexify (F x)))‖ :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun x => norm_nonneg _) hnorm (hsd.mul_right M)
  rw [← integral_tsum_of_summable_integral_norm hint hsum, norm_sq_eq_tsum]
  refine tsum_congr fun k => ?_
  symm
  rw [integral_re ((Force.Internal.integrableOn_character_smul k hG).const_inner (d k)),
    integral_inner (Force.Internal.integrableOn_character_smul k hG)]
  change RCLike.re (inner ℂ (d k) (freqTrCoef F k)) = _
  rw [hd]
  simp only
  rw [hcu, smul_smul, ← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal, ← Complex.coe_smul,
    norm_smul, Complex.norm_real, Real.norm_of_nonneg (hg0 k)]
  rw [show RCLike.re (((weight k * g k * g k : ℝ) : ℂ) *
      inner ℂ (divFree k (freqTrCoef F k)) (freqTrCoef F k)) =
      weight k * g k * g k *
        RCLike.re (inner ℂ (divFree k (freqTrCoef F k)) (freqTrCoef F k)) from Complex.re_ofReal_mul _ _,
    re_inner_divFree]
  ring

theorem fracFactor_nonneg (α s : ℝ) (k : Lattice) : 0 ≤ fracLatticeFactor α s k := (Real.exp_pos _).le

theorem fracFactor_le_one (α s : ℝ) (k : Lattice) : fracLatticeFactor α s k ≤ 1 := by
  unfold fracLatticeFactor
  rw [Real.exp_le_one_iff, neg_nonpos]
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (le_max_right _ _)

theorem sq_le_rpow_add_one {α r : ℝ} (hα : 1 ≤ α) (hr : 0 ≤ r) : r ^ 2 ≤ r ^ (2 * α) + 1 := by
  rcases le_total r 1 with h | h
  · have h1 : r ^ 2 ≤ 1 := pow_le_one₀ hr h
    have h2 : 0 ≤ r ^ (2 * α) := Real.rpow_nonneg hr _
    linarith
  · have h1 : r ^ (2 : ℝ) ≤ r ^ (2 * α) := Real.rpow_le_rpow_of_exponent_le h (by linarith)
    rw [Real.rpow_two] at h1
    linarith

theorem fracFactor_le_heat {α s : ℝ} (hα : 1 ≤ α) (hs : 0 < s) (k : Lattice) :
    fracLatticeFactor α s k ≤ Real.exp s * heatFactor s k := by
  have hr : 0 ≤ 2 * π * ‖freq k‖ := by positivity
  have h := sq_le_rpow_add_one hα hr
  unfold fracLatticeFactor heatFactor
  rw [max_eq_left hs.le, ← Real.exp_add, Real.exp_le_exp]
  have e : (2 * π * ‖freq k‖) ^ 2 = 4 * π ^ 2 * ‖freq k‖ ^ 2 := by ring
  rw [e] at h
  nlinarith [mul_le_mul_of_nonneg_right h hs.le]

theorem summable_weight_fracFactor {α s : ℝ} (hα : 1 ≤ α) (hs : 0 < s) :
    Summable fun k => weight k * fracLatticeFactor α s k ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (Internal.weight_pos k).le (sq_nonneg _))
    (fun k => ?_) ((Internal.summable_weight_heat hs).mul_left (Real.exp s ^ 2))
  have h0 := fracFactor_nonneg α s k
  have h1 := fracFactor_le_heat hα hs k
  have hw := (Internal.weight_pos k).le
  calc weight k * fracLatticeFactor α s k ^ 2 ≤ weight k * (Real.exp s * heatFactor s k) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 2) hw
    _ = Real.exp s ^ 2 * (weight k * heatFactor s k ^ 2) := by ring

theorem rpow_mul_exp_le {y s g : ℝ} (hy : 0 ≤ y) (hs : 0 < s) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    y ^ g * Real.exp (-(y * s)) ≤ s ^ (-g) := by
  have hys : 0 ≤ y * s := mul_nonneg hy hs.le
  have h1 : (y * s) ^ g ≤ 1 + y * s := by
    rcases le_total (y * s) 1 with h | h
    · have := Real.rpow_le_one hys h hg0
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le h hg1
      rw [Real.rpow_one] at this
      linarith
  have h2 := Real.add_one_le_exp (y * s)
  have h3 : (y * s) ^ g * Real.exp (-(y * s)) ≤ 1 := by
    calc (y * s) ^ g * Real.exp (-(y * s)) ≤ Real.exp (y * s) * Real.exp (-(y * s)) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hp : 0 < s ^ g := Real.rpow_pos_of_pos hs g
  have e : y ^ g * Real.exp (-(y * s)) = (s ^ g)⁻¹ * ((y * s) ^ g * Real.exp (-(y * s))) := by
    rw [Real.mul_rpow hy hs.le]
    field_simp
  rw [e, Real.rpow_neg hs.le]
  calc (s ^ g)⁻¹ * ((y * s) ^ g * Real.exp (-(y * s))) ≤ (s ^ g)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr hp.le)
    _ = (s ^ g)⁻¹ := mul_one _

theorem weight_fracFactor_le {α s : ℝ} (hα : 1 ≤ α) (hs : 0 < s) (hs1 : s ≤ 1) (k : Lattice) :
    weight k * fracLatticeFactor α s k ≤ 2 * s ^ (-(1 / α)) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨r, hr_def⟩ : ∃ r, r = 2 * π * ‖freq k‖ := ⟨_, rfl⟩
  have hr : 0 ≤ r := by rw [hr_def]; positivity
  have hw : weight k = 1 + r ^ 2 := by rw [hr_def]; unfold weight; ring
  have hf : fracLatticeFactor α s k = Real.exp (-(r ^ (2 * α) * s)) := by
    unfold fracLatticeFactor
    rw [max_eq_left hs.le, hr_def]
  have hy : 0 ≤ r ^ (2 * α) := Real.rpow_nonneg hr _
  have hg0 : 0 ≤ 1 / α := by positivity
  have hg1 : 1 / α ≤ 1 := by rw [div_le_one hα0]; exact hα
  have key := rpow_mul_exp_le hy hs hg0 hg1
  have hyp : (r ^ (2 * α)) ^ (1 / α) = r ^ 2 := by
    rw [← Real.rpow_mul hr, show 2 * α * (1 / α) = ((2 : ℕ) : ℝ) by field_simp; norm_num,
      Real.rpow_natCast]
  rw [hyp] at key
  have hE1 : Real.exp (-(r ^ (2 * α) * s)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg hy hs.le
  have h1 : 1 ≤ s ^ (-(1 / α)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs hs1 (by linarith)
  rw [hw, hf, add_mul, one_mul]
  linarith

theorem fracSourceOp_apply {α : ℝ} (hE : FracSourceOpExists α) {μ : ℝ} (hμ : 0 < μ) (τ : ℝ)
    (A : Freq.L2R) :
    fracSourceOp α μ τ A =
      fracTorusForce α (μ * τ) (fun x => (A : Space → Space) (simCoord (simScale α μ) x)) := by
  have h := hE μ τ
  unfold fracSourceOp
  rw [dif_pos h, h.choose_spec A, fracSourceFun, if_pos hμ]

theorem coeff_fracForce {α : ℝ} (hF : FracTorusForceAlgebra α) {s : ℝ} (hs : 0 < s)
    (F : Space → Space) (k : Lattice) :
    coeff (fracTorusForce α s F) k = fracLatticeFactor α s k • divFree k (freqTrCoef F k) := by
  rw [hF.1, fracTorusForceCoef, if_pos hs]

theorem fracSourceOp_threeHalves {α : ℝ} (hα : 1 < α) (hF : FracTorusForceAlgebra α)
    (hE : FracSourceOpExists α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ μ b τ : ℝ, 0 < μ → IsShellScale (simScale α μ) b → 0 < τ → μ * τ ≤ 1 →
      ∀ A : Freq.L2R,
      (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b → (A : Space → Space) y = 0) →
        ‖fracSourceOp α μ τ A‖ ≤
          C * μ ^ (1 / (4 * α)) * τ ^ (-(3 / (4 * α))) *
            (eLpNorm (A : Space → Space) (3 / 2) volume).toReal := by
  obtain ⟨C6, hC60, hC6⟩ := trigHs
  have hα0 : 0 < α := by linarith
  refine ⟨2 * Real.sqrt C6, by positivity, fun μ b τ hμ0 hμ hτ hμτ A hA => ?_⟩
  have hs : 0 < μ * τ := mul_pos hμ0 hτ
  have hν0 : 0 < simScale α μ := hμ.1
  rw [fracSourceOp_apply hE hμ0]
  obtain ⟨w, hw_def⟩ : ∃ w, w = (μ * τ) ^ (-(1 / (4 * α))) := ⟨_, rfl⟩
  have hw : 0 < w := hw_def ▸ Real.rpow_pos_of_pos hs _
  have hw4 : w ^ 4 = (μ * τ) ^ (-(1 / α)) := by
    rw [hw_def, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    congr 1
    push_cast
    field_simp
  have hw3 : w ^ 3 = (μ * τ) ^ (-(3 / (4 * α))) := by
    rw [hw_def, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    congr 1
    push_cast
    field_simp
  have hgB : ∀ k, weight k * fracLatticeFactor α (μ * τ) k ≤ 2 * w ^ 4 := fun k => by
    rw [hw4]
    exact weight_fracFactor_le hα.le hs hμτ k
  have hgs := summable_weight_fracFactor hα.le hs
  obtain ⟨hmem, hbd⟩ := gPhi_bound C6 hC60 hC6 hw (fracFactor_nonneg α (μ * τ))
    (fracFactor_le_one α (μ * τ)) hgB hgs
    (fracTorusForce α (μ * τ) (fun x => (A : Space → Space) (simCoord (simScale α μ) x)))
  obtain ⟨hint, hpair⟩ := pairing_transplant (simScale α μ) b hμ A hA _ hmem
  have hsq := norm_sq_eq_pairing (fracFactor_nonneg α (μ * τ)) hgs _ hint _ (coeff_fracForce hF hs _)
  set u := fracTorusForce α (μ * τ) (fun x => (A : Space → Space) (simCoord (simScale α μ) x)) with hu
  set a := (eLpNorm (A : Space → Space) (3 / 2) volume).toReal with ha
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have key : ‖u‖ * ‖u‖ ≤ (simScale α μ * a * (2 * Real.sqrt C6 * w ^ 3)) * ‖u‖ := by
    rw [← sq, hsq]
    refine (le_abs_self _).trans (hpair.trans ?_)
    calc simScale α μ * a * (eLpNorm (gPhi (fracLatticeFactor α (μ * τ)) u) 3 (volume.restrict cell)).toReal
        ≤ simScale α μ * a * (2 * Real.sqrt C6 * w ^ 3 * ‖u‖) :=
          mul_le_mul_of_nonneg_left hbd (mul_nonneg hν0.le ha0)
      _ = (simScale α μ * a * (2 * Real.sqrt C6 * w ^ 3)) * ‖u‖ := by ring
  have hK : ‖u‖ ≤ simScale α μ * a * (2 * Real.sqrt C6 * w ^ 3) := by
    rcases (norm_nonneg u).eq_or_lt with h | h
    · rw [← h]
      positivity
    · exact le_of_mul_le_mul_right key h
  have e1 : w ^ 3 = μ ^ (-(3 / (4 * α))) * τ ^ (-(3 / (4 * α))) := by
    rw [hw3, Real.mul_rpow hμ0.le hτ.le]
  have e2 : simScale α μ * μ ^ (-(3 / (4 * α))) = μ ^ (1 / (4 * α)) := by
    rw [simScale, ← Real.rpow_add hμ0]
    congr 1
    field_simp
    ring
  calc ‖u‖ ≤ simScale α μ * a * (2 * Real.sqrt C6 * w ^ 3) := hK
    _ = 2 * Real.sqrt C6 * (simScale α μ * μ ^ (-(3 / (4 * α)))) * τ ^ (-(3 / (4 * α))) * a := by
        rw [e1]
        ring
    _ = 2 * Real.sqrt C6 * μ ^ (1 / (4 * α)) * τ ^ (-(3 / (4 * α))) * a := by rw [e2]

end TorusShellLambda.Internal

open ShellTorus.Internal TorusShellLambda.Internal

theorem fracTorusLambdaBound (α : ℝ) (hα : 1 < α) (hF : FracTorusForceAlgebra α)
    (hE : FracSourceOpExists α) : FracTorusLambdaBound α := by
  obtain ⟨C1, hC1, h1⟩ := advectShell_threeHalves Freq.gradSixDecay Freq.embedNormLinear_holds.1
  obtain ⟨C2, hC2, h2⟩ := fracSourceOp_threeHalves hα hF hE
  refine ⟨C2 * C1, mul_nonneg hC2 hC1, ?_⟩
  intro φ hφ b μ τ hμ0 _hμ1 hμ hτ hμτ ζ
  have hA := h2 μ b τ hμ0 hμ hτ hμτ _ (advectShell_ae_zero φ hφ b ζ)
  have hB := h1 φ hφ b ζ
  have ht : 0 ≤ τ ^ (-(3 / (4 * α))) := Real.rpow_nonneg hτ.le _
  have hfl : fracLambdaTorus α φ hφ b μ τ ζ =
      -((μ ^ (-(1 / (4 * α)))) • fracSourceOp α μ τ (advectShell φ hφ b ζ)) := rfl
  rw [hfl, norm_neg, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hμ0.le _)]
  have e : μ ^ (-(1 / (4 * α))) * μ ^ (1 / (4 * α)) = 1 := by
    rw [← Real.rpow_add hμ0, neg_add_cancel, Real.rpow_zero]
  set E := (eLpNorm (advectShell φ hφ b ζ : Space → Space) (3 / 2) volume).toReal with hE_def
  calc μ ^ (-(1 / (4 * α))) * ‖fracSourceOp α μ τ (advectShell φ hφ b ζ)‖
      ≤ μ ^ (-(1 / (4 * α))) * (C2 * μ ^ (1 / (4 * α)) * τ ^ (-(3 / (4 * α))) * E) :=
        mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg hμ0.le _)
    _ = C2 * τ ^ (-(3 / (4 * α))) * E := by
        linear_combination (C2 * τ ^ (-(3 / (4 * α))) * E) * e
    _ ≤ C2 * τ ^ (-(3 / (4 * α))) * (C1 * ‖Freq.embedX φ‖ * ‖ζ‖) :=
        mul_le_mul_of_nonneg_left hB (mul_nonneg hC2 ht)
    _ = C2 * C1 * τ ^ (-(3 / (4 * α))) * ‖Freq.embedX φ‖ * ‖ζ‖ := by ring

end Breakdown.Periodic
