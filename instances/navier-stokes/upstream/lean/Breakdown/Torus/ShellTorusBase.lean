import Breakdown.Torus.StatementsShell

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace ShellTorus.Internal

theorem coeff_smul_real (r : ℝ) (u : V) (k : Lattice) : coeff (r • u) k = r • coeff u k := by
  unfold coeff
  rw [Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, smul_comm]

theorem coeff_neg_vec (u : V) (k : Lattice) : coeff (-u) k = -coeff u k := by
  unfold coeff
  rw [Submodule.coe_neg, lp.coeFn_neg, Pi.neg_apply, smul_neg]

theorem divFree_smul_real (k : Lattice) (r : ℝ) (c : Coef) : divFree k (r • c) = r • divFree k c := by
  unfold divFree
  split_ifs
  · rfl
  · have h : divPairing k (r • c) = (r : ℂ) * divPairing k c := by
      simp only [divPairing, PiLp.smul_apply, Complex.real_smul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h, smul_sub, mul_div_assoc, mul_smul, Complex.coe_smul]

theorem coeff_forceV {s : ℝ} (hs : 0 < s) (F : Space → Space) (k : Lattice) :
    coeff (forceV s F) k = heatFactor s k • divFree k (freqTrCoef F k) := by
  show (Real.sqrt (weight k))⁻¹ • forceSeq s F k = _
  rw [forceSeq, if_pos hs, smul_smul, ← mul_assoc, inv_mul_cancel₀ (Internal.sqrt_weight_pos k).ne', one_mul]

theorem sourceOp_apply {μ : ℝ} (hμ : 0 < μ) (τ : ℝ) (A : Freq.L2R) :
    sourceOp μ τ A = forceV (μ * τ) (fun x => (A : Space → Space) (simCoord μ x)) := by
  show sourceFun μ τ A = _
  rw [sourceFun, if_pos hμ]

theorem lambdaTorus_apply (φ : Space → Space) (hφ : IsTestField φ) (b μ τ : ℝ) (ζ : ShellData) :
    lambdaTorus φ hφ b μ τ ζ = -((μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ (advectShell φ hφ b ζ)) := rfl

def zField (z : V) (x : Space) : Space := Freq.realVec (torusSeries 6 (coeff z) x)

def gField (j : Fin 3) (z : V) (x : Space) : Space := Freq.realVec (torusSeries 2 (gradCoef j z) x)

def productField (f : Space → Space) (z : V) (x : Space) : Space :=
  ∑ j : Fin 3, (f x j • gField j z x + zField z x j • fderiv ℝ f x (unitVector j))

theorem volume_coord_eq (i : Fin 3) (a : ℝ) : volume {x : Space | x i = a} = 0 := by
  have h := (PiLp.volume_preserving_ofLp (ι := Fin 3)).measure_preimage
    (s := {f : Fin 3 → ℝ | f i = a})
    (measurableSet_eq_fun (measurable_pi_apply i) measurable_const).nullMeasurableSet
  rw [show {x : Space | x i = a} = WithLp.ofLp ⁻¹' {f : Fin 3 → ℝ | f i = a} from rfl, h, volume_pi]
  exact Measure.pi_hyperplane (fun _ : Fin 3 => (volume : Measure ℝ)) i a

theorem center_coord (i : Fin 3) : center i = 1 / 2 := by
  simp [center, unitVector, Finset.sum_apply, Pi.single_apply]

theorem wrap_eq_self {x : Space} (hx : ∀ i, x i ∈ Ico (0 : ℝ) 1) : wrap x = x := by
  have hr : ∀ i, round (x i - center i) = 0 := fun i => by
    rw [round_eq_zero_iff, center_coord]
    constructor <;> linarith [(hx i).1, (hx i).2]
  simp [wrap, hr]

theorem ae_wrap_eq : ∀ᵐ x ∂(volume.restrict cell), wrap x = x := by
  have hnull : volume (⋃ i : Fin 3, {x : Space | x i = 1}) = 0 :=
    measure_iUnion_null fun i => volume_coord_eq i 1
  refine (ae_restrict_iff' FreqTrSeries.Internal.isCompact_cell.isClosed.measurableSet).mpr ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hxc
  exact wrap_eq_self fun i => ⟨(hxc i).1, lt_of_le_of_ne (hxc i).2 fun h => hx (mem_iUnion.mpr ⟨i, h⟩)⟩

theorem ae_simCoord_eq (μ : ℝ) :
    ∀ᵐ x ∂(volume.restrict cell), simCoord μ x = (Real.sqrt μ)⁻¹ • (x - center) := by
  filter_upwards [ae_wrap_eq] with x hx
  rw [simCoord, hx]

theorem divergenceAt_scale (c : ℝ) (f : Space → Space) (x : Space) :
    divergenceAt (fun y => c • f y) x = c * divergenceAt f x := by
  have e : (fun y => c • f y) = c • f := rfl
  rw [e]
  simp [divergenceAt, fderiv_const_smul_field, Finset.mul_sum]

theorem freqTrCoef_scale (r : ℝ) (F : Space → Space) (k : Lattice) :
    freqTrCoef (fun x => r • F x) k = r • freqTrCoef F k := by
  unfold freqTrCoef
  rw [← integral_smul]
  congr 1
  funext x
  rw [smul_comm]
  congr 1
  ext i
  simp [complexify, Complex.real_smul]

theorem freqTrCoef_congr {F G : Space → Space} (h : F =ᵐ[volume.restrict cell] G) (k : Lattice) :
    freqTrCoef F k = freqTrCoef G k := by
  unfold freqTrCoef
  exact integral_congr_ae (h.mono fun x hx => by simp only [hx])

theorem advectShell_ae_zero (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ) (ζ : ShellData) :
    ∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b → (advectShell φ hφ b ζ : Space → Space) y = 0 := by
  show ∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b → (advectShellFun φ b ζ : Space → Space) y = 0
  unfold advectShellFun Freq.toLpOrZero
  split_ifs with h
  · filter_upwards [h.coeFn_toLp] with y hy hyb
    rw [hy, indicator_of_notMem hyb]
  · filter_upwards [Lp.coeFn_zero Space 2 volume] with y hy _
    rw [hy]
    rfl

theorem isDecay_of_test {φ : Space → Space} (h : IsTestField φ) : IsDecayField φ := by
  refine ⟨h.1, h.2.2, ?_⟩
  have h0 : Continuous φ := h.1.continuous
  have h1 : Continuous (fderiv ℝ φ) := h.1.continuous_fderiv (by simp)
  have hc : Continuous fun y => (1 + ‖y‖) ^ 2 * (‖φ y‖ + ‖fderiv ℝ φ y‖) := by fun_prop
  have hk : HasCompactSupport fun y => (1 + ‖y‖) ^ 2 * (‖φ y‖ + ‖fderiv ℝ φ y‖) :=
    (h.2.1.norm.add (h.2.1.fderiv ℝ).norm).mul_left
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hk
  refine ⟨C, fun y => ?_⟩
  have hp : 0 < 1 + ‖y‖ := by positivity
  have hy := (Real.le_norm_self _).trans (hC y)
  have a := norm_nonneg (φ y)
  have b := norm_nonneg (fderiv ℝ φ y)
  have r := norm_nonneg y
  constructor
  · rw [le_div_iff₀ hp]
    nlinarith [mul_nonneg a r, mul_nonneg (mul_nonneg a r) r, mul_nonneg b (sq_nonneg (1 + ‖y‖))]
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg a (sq_nonneg (1 + ‖y‖))]

instance lpProdSixTwo : ENNReal.HolderTriple 6 2 (3 / 2) := by
  constructor
  rw [ENNReal.inv_div (by simp) (by simp)]
  rw [← ENNReal.toReal_eq_toReal_iff']
  · rw [ENNReal.toReal_add (by simp) (by simp)]
    simp
    norm_num
  · simp
  · exact ENNReal.div_ne_top (by simp) (by simp)

theorem one_le_threeHalves : (1 : ℝ≥0∞) ≤ 3 / 2 := by
  rw [ENNReal.le_div_iff_mul_le (by simp) (by simp)]
  norm_num

theorem eLpNorm_advectShell_le (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ) (ζ : ShellData) :
    eLpNorm (advectShell φ hφ b ζ : Space → Space) (3 / 2) volume ≤
      eLpNorm (fun y => ∑ j : Fin 3, (φ y j • (ζ.1 j : Space → Space) y +
        (ζ.2 : Space → Space) y j • Freq.partialField φ j y)) (3 / 2) volume := by
  show eLpNorm (advectShellFun φ b ζ : Space → Space) (3 / 2) volume ≤ _
  unfold advectShellFun Freq.toLpOrZero
  split_ifs with h
  · rw [eLpNorm_congr_ae h.coeFn_toLp]
    exact eLpNorm_indicator_le _
  · rw [eLpNorm_congr_ae (Lp.coeFn_zero _ _ _)]
    simp

theorem eLpNorm_Lp_eq {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Lp (α := Space) Space p) :
    eLpNorm (f : Space → Space) p volume = ENNReal.ofReal ‖f‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]

theorem advectShell_threeHalves (hG : Freq.GradSixDecay) (hE : Freq.EmbedNorm) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ) (ζ : ShellData),
      (eLpNorm (advectShell φ hφ b ζ : Space → Space) (3 / 2) volume).toReal ≤
        C * ‖Freq.embedX φ‖ * ‖ζ‖ := by
  obtain ⟨S, hS⟩ := hG
  refine ⟨6 * (|S| + 1), by positivity, fun φ hφ b ζ => ?_⟩
  have hD := isDecay_of_test hφ
  obtain ⟨hm6, hS6⟩ := hS φ hD
  obtain ⟨E, hEdef⟩ : ∃ E, E = ‖Freq.embedX φ‖ := ⟨_, rfl⟩
  rw [← hEdef]
  have hE0 : 0 ≤ E := hEdef ▸ norm_nonneg _
  have hE2 : E ^ 2 = ∫ y, ∑ i : Fin 3, ‖fderiv ℝ φ y (unitVector i)‖ ^ 2 := by
    rw [hEdef]
    exact hE φ hD
  have hsq : Real.sqrt (∫ y, ∑ i : Fin 3, ‖fderiv ℝ φ y (unitVector i)‖ ^ 2) = E := by
    rw [← hE2, Real.sqrt_sq hE0]
  have hζ0 : 0 ≤ ‖ζ‖ := norm_nonneg _
  have hS0 : 0 ≤ |S| := abs_nonneg S
  have hφ6 : eLpNorm φ 6 volume ≤ ENNReal.ofReal (|S| * E) := by
    rw [← ENNReal.ofReal_toReal hm6.eLpNorm_ne_top]
    apply ENNReal.ofReal_le_ofReal
    rw [hsq] at hS6
    exact hS6.trans (mul_le_mul_of_nonneg_right (le_abs_self S) hE0)
  have hcont : Continuous φ := hφ.1.continuous
  have hdc : ∀ j : Fin 3, Continuous (Freq.partialField φ j) := fun j =>
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hm : ∀ i : Fin 3, MemLp (Freq.partialField φ i) 2 volume := fun i =>
    (hdc i).memLp_of_hasCompactSupport (hφ.2.1.fderiv_apply (𝕜 := ℝ) (unitVector i))
  have hd2 : ∀ j : Fin 3, eLpNorm (Freq.partialField φ j) 2 volume ≤ ENNReal.ofReal E := by
    intro j
    rw [(hm j).eLpNorm_eq_integral_rpow_norm (by simp) (by simp)]
    apply ENNReal.ofReal_le_ofReal
    have hint : ∀ i : Fin 3, Integrable (fun y => ‖Freq.partialField φ i y‖ ^ 2) volume := fun i =>
      (hm i).integrable_norm_pow (by simp)
    have hle : ∫ y, ‖Freq.partialField φ j y‖ ^ 2 ≤ E ^ 2 := by
      rw [hE2]
      refine integral_mono (hint j) (integrable_finsetSum _ fun i _ => hint i) fun y => ?_
      exact Finset.single_le_sum (f := fun i => ‖Freq.partialField φ i y‖ ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    have e : ((2 : ℝ≥0∞).toReal)⁻¹ = (1 / 2 : ℝ) := by norm_num
    rw [e, ← Real.sqrt_eq_rpow]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    calc Real.sqrt (∫ y, ‖Freq.partialField φ j y‖ ^ 2) ≤ Real.sqrt (E ^ 2) := Real.sqrt_le_sqrt hle
      _ = E := Real.sqrt_sq hE0
  have hζ1 : ∀ j : Fin 3, eLpNorm (ζ.1 j : Space → Space) 2 volume ≤ ENNReal.ofReal ‖ζ‖ := fun j => by
    rw [eLpNorm_Lp_eq]
    exact ENNReal.ofReal_le_ofReal ((norm_le_pi_norm ζ.1 j).trans (norm_fst_le ζ))
  have hζ2 : eLpNorm (ζ.2 : Space → Space) 6 volume ≤ ENNReal.ofReal ‖ζ‖ := by
    rw [eLpNorm_Lp_eq]
    exact ENNReal.ofReal_le_ofReal (norm_snd_le ζ)
  set X := ENNReal.ofReal ((|S| + 1) * E * ‖ζ‖) with hX
  have hT1 : ∀ j : Fin 3, eLpNorm (fun y => φ y j • (ζ.1 j : Space → Space) y) (3 / 2) volume ≤ X := by
    intro j
    have hc : Continuous fun y => φ y j := (EuclideanSpace.proj j).continuous.comp hcont
    calc eLpNorm (fun y => φ y j • (ζ.1 j : Space → Space) y) (3 / 2) volume
        = eLpNorm ((fun y => φ y j) • (ζ.1 j : Space → Space)) (3 / 2) volume := rfl
      _ ≤ eLpNorm (fun y => φ y j) 6 volume * eLpNorm (ζ.1 j : Space → Space) 2 volume :=
          eLpNorm_smul_le_mul_eLpNorm (Lp.aestronglyMeasurable _) hc.aestronglyMeasurable
      _ ≤ ENNReal.ofReal (|S| * E) * ENNReal.ofReal ‖ζ‖ := by
          gcongr
          · exact (eLpNorm_mono fun y => PiLp.norm_apply_le (φ y) j).trans hφ6
          · exact hζ1 j
      _ ≤ X := by
          rw [← ENNReal.ofReal_mul (by positivity), hX]
          apply ENNReal.ofReal_le_ofReal
          nlinarith [mul_nonneg hE0 hζ0]
  have hT2 : ∀ j : Fin 3, eLpNorm (fun y => (ζ.2 : Space → Space) y j • Freq.partialField φ j y)
      (3 / 2) volume ≤ X := by
    intro j
    have hc : AEStronglyMeasurable (fun y => (ζ.2 : Space → Space) y j) volume :=
      (EuclideanSpace.proj j).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)
    calc eLpNorm (fun y => (ζ.2 : Space → Space) y j • Freq.partialField φ j y) (3 / 2) volume
        = eLpNorm ((fun y => (ζ.2 : Space → Space) y j) • Freq.partialField φ j) (3 / 2) volume := rfl
      _ ≤ eLpNorm (fun y => (ζ.2 : Space → Space) y j) 6 volume *
            eLpNorm (Freq.partialField φ j) 2 volume :=
          eLpNorm_smul_le_mul_eLpNorm (hdc j).aestronglyMeasurable hc
      _ ≤ ENNReal.ofReal ‖ζ‖ * ENNReal.ofReal E := by
          gcongr
          · exact (eLpNorm_mono fun y => PiLp.norm_apply_le _ j).trans hζ2
          · exact hd2 j
      _ ≤ X := by
          rw [← ENNReal.ofReal_mul hζ0, hX]
          apply ENNReal.ofReal_le_ofReal
          nlinarith [mul_nonneg hE0 hζ0]
  have hmeas1 : ∀ j : Fin 3, AEStronglyMeasurable (fun y => φ y j • (ζ.1 j : Space → Space) y) volume :=
    fun j => (((EuclideanSpace.proj j).continuous.comp hcont).aestronglyMeasurable).smul
      (Lp.aestronglyMeasurable _)
  have hmeas2 : ∀ j : Fin 3, AEStronglyMeasurable
      (fun y => (ζ.2 : Space → Space) y j • Freq.partialField φ j y) volume :=
    fun j => by
      have hc : AEStronglyMeasurable (fun y => (ζ.2 : Space → Space) y j) volume :=
        (EuclideanSpace.proj j).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)
      exact hc.smul (hdc j).aestronglyMeasurable
  have hsum : eLpNorm (fun y => ∑ j : Fin 3, (φ y j • (ζ.1 j : Space → Space) y +
      (ζ.2 : Space → Space) y j • Freq.partialField φ j y)) (3 / 2) volume ≤ ∑ _j : Fin 3, (X + X) := by
    have e : (fun y => ∑ j : Fin 3, (φ y j • (ζ.1 j : Space → Space) y +
        (ζ.2 : Space → Space) y j • Freq.partialField φ j y)) =
        ∑ j : Fin 3, (fun y => φ y j • (ζ.1 j : Space → Space) y +
          (ζ.2 : Space → Space) y j • Freq.partialField φ j y) := by
      funext y
      rw [Finset.sum_apply]
    rw [e]
    refine (eLpNorm_sum_le (fun j _ => (hmeas1 j).add (hmeas2 j)) one_le_threeHalves).trans ?_
    refine Finset.sum_le_sum fun j _ => ?_
    exact (eLpNorm_add_le (hmeas1 j) (hmeas2 j) one_le_threeHalves).trans (add_le_add (hT1 j) (hT2 j))
  have htot : ∑ _j : Fin 3, (X + X) = ENNReal.ofReal (6 * (|S| + 1) * E * ‖ζ‖) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hX, ← ENNReal.ofReal_add (by positivity)
      (by positivity), nsmul_eq_mul, Nat.cast_ofNat, ← ENNReal.ofReal_ofNat 3,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  rw [← htot]
  exact (eLpNorm_advectShell_le φ hφ b ζ).trans hsum

def phiField (s : ℝ) (ψ : V) (x : Space) : Space :=
  Freq.realVec (∑' k, character (-k) x • ((weight k * heatFactor s k : ℝ) • coeff ψ k))

theorem norm_complexify (a : Space) : ‖complexify a‖ = ‖a‖ := by
  simp [EuclideanSpace.norm_eq, complexify, Complex.norm_real]

theorem inner_realVec (a : Space) (v : Coef) :
    inner ℝ a (Freq.realVec v) = RCLike.re (inner ℂ (complexify a) v) := by
  simp [PiLp.inner_apply, Freq.realVec, complexify, mul_comm]

theorem re_inner_divFree (k : Lattice) (c : Coef) :
    RCLike.re (inner ℂ (divFree k c) c) = ‖divFree k c‖ ^ 2 := by
  by_cases hk : k = 0
  · rw [divFree, if_pos hk]
    exact inner_self_eq_norm_sq c
  · have h0 : inner ℂ (divFree k c) (latVec k) = 0 := by
      rw [← inner_conj_symm, ← Internal.divPairing_eq_inner, Force.Internal.divPairing_divFree, map_zero]
    have e : c = divFree k c + (divPairing k c / ((‖freq k‖ ^ 2 : ℝ) : ℂ)) • latVec k := by
      rw [divFree, if_neg hk, sub_add_cancel]
    have h1 : inner ℂ (divFree k c) c = inner ℂ (divFree k c) (divFree k c) := by
      calc inner ℂ (divFree k c) c
          = inner ℂ (divFree k c) (divFree k c + (divPairing k c / ((‖freq k‖ ^ 2 : ℝ) : ℂ)) • latVec k) := by
            rw [← e]
        _ = inner ℂ (divFree k c) (divFree k c) := by rw [inner_add_right, inner_smul_right, h0, mul_zero, add_zero]
    rw [h1]
    exact inner_self_eq_norm_sq _

theorem norm_sq_forceV {s : ℝ} (hs : 0 < s) (F : Space → Space) (hF : IntegrableOn F cell) :
    ‖forceV s F‖ ^ 2 = ∫ x in cell, inner ℝ (F x) (phiField s (forceV s F) x) := by
  obtain ⟨u, hu⟩ : ∃ u, u = forceV s F := ⟨_, rfl⟩
  rw [← hu]
  have hcu : ∀ k, coeff u k = heatFactor s k • divFree k (freqTrCoef F k) := fun k => by
    rw [hu]
    exact coeff_forceV hs F k
  obtain ⟨d, hd⟩ : ∃ d : Lattice → Coef, d = fun k => (weight k * heatFactor s k : ℝ) • coeff u k :=
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
  have hh : ∀ k, 0 ≤ heatFactor s k := fun k => Internal.heatFactor_nonneg s k
  have hdk : ∀ k, ‖d k‖ ≤ 2 * M * (weight k * heatFactor s k ^ 2) := by
    intro k
    rw [hd]
    simp only
    rw [norm_smul, hcu, norm_smul, Real.norm_of_nonneg (mul_nonneg (hw k) (hh k)),
      Real.norm_of_nonneg (hh k)]
    have hl := (Internal.norm_divFree_le k (freqTrCoef F k)).trans
      (mul_le_mul_of_nonneg_left (hFk k) (by norm_num : (0 : ℝ) ≤ 2))
    calc weight k * heatFactor s k * (heatFactor s k * ‖divFree k (freqTrCoef F k)‖)
        ≤ weight k * heatFactor s k * (heatFactor s k * (2 * M)) := by
          gcongr
          · exact mul_nonneg (hw k) (hh k)
          · exact hh k
      _ = 2 * M * (weight k * heatFactor s k ^ 2) := by ring
  have hsd : Summable fun k => ‖d k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdk ((Internal.summable_weight_heat hs).mul_left _)
  have hpt : ∀ x, inner ℝ (F x) (phiField s u x) =
      ∑' k, RCLike.re (inner ℂ (d k) (character k x • complexify (F x))) := by
    intro x
    have hsx : Summable fun k => character (-k) x • d k := by
      refine Summable.of_norm (hsd.congr fun k => ?_)
      rw [norm_smul, FreqTrSeries.Internal.norm_character, one_mul]
    have e1 : phiField s u x = Freq.realVec (∑' k, character (-k) x • d k) := by
      rw [phiField, hd]
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
  rw [show (fun x => inner ℝ (F x) (phiField s u x)) =
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
    norm_smul, Complex.norm_real, Real.norm_of_nonneg (hh k)]
  rw [show RCLike.re (((weight k * heatFactor s k * heatFactor s k : ℝ) : ℂ) *
      inner ℂ (divFree k (freqTrCoef F k)) (freqTrCoef F k)) =
      weight k * heatFactor s k * heatFactor s k *
        RCLike.re (inner ℂ (divFree k (freqTrCoef F k)) (freqTrCoef F k)) from Complex.re_ofReal_mul _ _,
    re_inner_divFree]
  ring


instance lpProdThreeHalvesThree : ENNReal.HolderTriple (3 / 2) 3 1 := by
  constructor
  rw [ENNReal.inv_div (by simp) (by simp), inv_one]
  rw [← ENNReal.toReal_eq_toReal_iff']
  · rw [ENNReal.toReal_add (ENNReal.div_ne_top (by simp) (by simp)) (by simp)]
    simp
    norm_num
  · exact ENNReal.add_ne_top.mpr ⟨ENNReal.div_ne_top (by simp) (by simp), by simp⟩
  · simp

theorem threeHalves_le_two : (3 / 2 : ℝ≥0∞) ≤ 2 := by
  rw [ENNReal.div_le_iff (by simp) (by simp)]
  norm_num

theorem eLpNorm_threeHalves_ne_top (b : ℝ) (A : Freq.L2R)
    (hA : ∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b → (A : Space → Space) y = 0) :
    eLpNorm (A : Space → Space) (3 / 2) volume ≠ ⊤ := by
  have hball : MeasurableSet (Metric.closedBall (0 : Space) b) := measurableSet_closedBall
  have hind : (A : Space → Space) =ᵐ[volume] (Metric.closedBall (0 : Space) b).indicator A :=
    hA.mono fun y hy => by
      by_cases hyb : y ∈ Metric.closedBall (0 : Space) b
      · rw [indicator_of_mem hyb]
      · rw [indicator_of_notMem hyb, hy hyb]
  rw [eLpNorm_congr_ae hind, eLpNorm_indicator_eq_eLpNorm_restrict hball]
  refine ne_top_of_le_ne_top ?_ (eLpNorm_le_eLpNorm_mul_rpow_measure_univ threeHalves_le_two
    (Lp.aestronglyMeasurable A).restrict)
  have hfin : (volume.restrict (Metric.closedBall (0 : Space) b)) univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_closedBall (0 : Space) b).measure_lt_top.ne
  have hexp : (0 : ℝ) ≤ 1 / (3 / 2 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal := by
    simp [ENNReal.toReal_div]
    norm_num
  exact ENNReal.mul_ne_top
    (ne_top_of_le_ne_top (Lp.eLpNorm_ne_top A) (eLpNorm_mono_measure _ Measure.restrict_le_self))
    (ENNReal.rpow_ne_top_of_nonneg hexp hfin)

theorem pairing_transplant (μ b : ℝ) (hμ : IsShellScale μ b) (A : Freq.L2R)
    (hA : ∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b → (A : Space → Space) y = 0)
    (G : Space → Space) (hG : MemLp G 3 (volume.restrict cell)) :
    IntegrableOn (fun x => (A : Space → Space) (simCoord μ x)) cell ∧
      |∫ x in cell, inner ℝ ((A : Space → Space) (simCoord μ x)) (G x)| ≤
        μ * (eLpNorm (A : Space → Space) (3 / 2) volume).toReal *
          (eLpNorm G 3 (volume.restrict cell)).toReal := by
  have hμ0 : 0 < μ := hμ.1
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (Real.sqrt μ)⁻¹ := ⟨_, rfl⟩
  have hr0 : r ≠ 0 := hr ▸ inv_ne_zero (Real.sqrt_pos.mpr hμ0).ne'
  have hLm : Measurable fun x : Space => r • (x - center) :=
    (measurable_const_smul r).comp (measurable_id.sub_const center)
  have hmap : Measure.map (fun x : Space => r • (x - center)) volume =
      ENNReal.ofReal |(r ^ 3)⁻¹| • volume := by
    have e : (fun x : Space => r • (x - center)) = (fun y => r • y) ∘ (fun x => x - center) := rfl
    rw [e, ← Measure.map_map (measurable_const_smul r) (continuous_sub_right center).measurable,
      map_sub_right_eq_self, Measure.map_addHaar_smul volume hr0, finrank_euclideanSpace_fin]
  obtain ⟨c, hc⟩ : ∃ c, c = ENNReal.ofReal |(r ^ 3)⁻¹| := ⟨_, rfl⟩
  rw [← hc] at hmap
  have hqmp : Measure.QuasiMeasurePreserving (fun x : Space => r • (x - center)) volume volume :=
    ⟨hLm, by rw [hmap]; exact Measure.smul_absolutelyContinuous⟩
  have hAm : AEStronglyMeasurable (A : Space → Space)
      (Measure.map (fun x : Space => r • (x - center)) volume) := by
    rw [hmap]
    exact (Lp.aestronglyMeasurable A).smul_measure c
  have hALm : AEStronglyMeasurable (fun x => (A : Space → Space) (r • (x - center))) volume :=
    (Lp.aestronglyMeasurable A).comp_quasiMeasurePreserving hqmp
  have hAL : eLpNorm (fun x => (A : Space → Space) (r • (x - center))) (3 / 2) volume =
      c ^ (1 / (3 / 2 : ℝ≥0∞)).toReal • eLpNorm (A : Space → Space) (3 / 2) volume := by
    rw [show (fun x => (A : Space → Space) (r • (x - center))) =
      (A : Space → Space) ∘ (fun x : Space => r • (x - center)) from rfl,
      ← eLpNorm_map_measure hAm hLm.aemeasurable, hmap,
      eLpNorm_smul_measure_of_ne_top (ENNReal.div_ne_top (by simp) (by simp))]
  have hcμ : c ^ (1 / (3 / 2 : ℝ≥0∞)).toReal = ENNReal.ofReal μ := by
    have e1 : |(r ^ 3)⁻¹| = μ ^ (3 / 2 : ℝ) := by
      rw [hr, inv_pow, inv_inv, abs_of_nonneg (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_natCast,
        ← Real.rpow_mul hμ0.le]
      norm_num
    have e2 : (1 / (3 / 2 : ℝ≥0∞)).toReal = 2 / 3 := by
      rw [one_div, ENNReal.inv_div (by simp) (by simp)]
      simp [ENNReal.toReal_div]
    rw [hc, e1, e2, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.rpow_mul hμ0.le]
    norm_num
  rw [hcμ] at hAL
  have hAfin := eLpNorm_threeHalves_ne_top b A hA
  have hsimae := ae_simCoord_eq μ
  rw [← hr] at hsimae
  have hae : (fun x => (A : Space → Space) (r • (x - center))) =ᵐ[volume.restrict cell]
      fun x => (A : Space → Space) (simCoord μ x) := hsimae.mono fun x hx => by simp only [hx]
  have hcell : volume cell ≠ ⊤ := FreqTrSeries.Internal.isCompact_cell.measure_lt_top.ne
  have : IsFiniteMeasure (volume.restrict cell) := ⟨by rw [Measure.restrict_apply_univ]; exact hcell.lt_top⟩
  have hle : eLpNorm (fun x => (A : Space → Space) (simCoord μ x)) (3 / 2) (volume.restrict cell) ≤
      ENNReal.ofReal μ * eLpNorm (A : Space → Space) (3 / 2) volume := by
    rw [← eLpNorm_congr_ae hae, ← smul_eq_mul, ← hAL]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have hmem : MemLp (fun x => (A : Space → Space) (simCoord μ x)) (3 / 2) (volume.restrict cell) :=
    ⟨(hALm.restrict).congr hae, hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hAfin.lt_top)⟩
  refine ⟨memLp_one_iff_integrable.mp (hmem.mono_exponent one_le_threeHalves), ?_⟩
  have hb := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 3 / 2) (q := 3) (r := 1) hmem.1 hG.1
    (fun u v : Space => inner ℝ u v) 1 (Filter.Eventually.of_forall fun x => by
      rw [one_mul]
      exact nnnorm_inner_le_nnnorm _ _)
  have hint : AEStronglyMeasurable (fun x => inner ℝ ((A : Space → Space) (simCoord μ x)) (G x))
      (volume.restrict cell) := hmem.1.inner hG.1
  have hGfin := hG.eLpNorm_ne_top
  rw [ENNReal.coe_one, one_mul] at hb
  calc |∫ x in cell, inner ℝ ((A : Space → Space) (simCoord μ x)) (G x)|
      ≤ ∫ x in cell, ‖inner ℝ ((A : Space → Space) (simCoord μ x)) (G x)‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
    _ = (eLpNorm (fun x => inner ℝ ((A : Space → Space) (simCoord μ x)) (G x)) 1
          (volume.restrict cell)).toReal := by
        rw [integral_norm_eq_lintegral_enorm hint, eLpNorm_one_eq_lintegral_enorm]
    _ ≤ ((ENNReal.ofReal μ * eLpNorm (A : Space → Space) (3 / 2) volume) *
          eLpNorm G 3 (volume.restrict cell)).toReal := by
        refine ENNReal.toReal_mono ?_ (hb.trans ?_)
        · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin) hGfin
        · gcongr
    _ = μ * (eLpNorm (A : Space → Space) (3 / 2) volume).toReal *
          (eLpNorm G 3 (volume.restrict cell)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hμ0.le]


end ShellTorus.Internal

end Breakdown.Periodic
