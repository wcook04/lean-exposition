import Breakdown.CertCell.TailStatements
import Breakdown.CertCell.TailSquareSmoothing

open scoped ENNReal ContDiff Convolution
open MeasureTheory Filter Topology ContinuousLinearMap

noncomputable section

namespace Breakdown

namespace CertCell

namespace TailBand

open SquareInternal

def spaceSquareExterior (R : ℝ) : Set Space :=
  {y | (Real.sqrt (y 0 ^ 2 + y 1 ^ 2), y 2) ∈ planeSquareExterior R}

def IsAxialFlipField (w : Space → Space) : Prop :=
  (∀ (ψ : ℝ) (y : Space), w (axialRot ψ y) = axialRot ψ (w y)) ∧
    ∀ y, w (flipPoint y) = flipPoint (w y)

def SquareExteriorSpaceSmoothStatement : Prop :=
  ∀ R : ℝ, 0 < R → ∀ w : Space → Space, ContDiff ℝ 1 w → HasCompactSupport w →
    IsAxialFlipField w →
      ENNReal.ofReal 2 * ∫⁻ y in spaceSquareExterior R, ENNReal.ofReal (‖w y‖ ^ 2 / ‖y‖ ^ 2)
        ≤ ∫⁻ y in spaceSquareExterior R, ENNReal.ofReal (matSq (fderiv ℝ w y))

def SquareExteriorSpaceWeakStatement : Prop :=
  ∀ R : ℝ, 0 < R → ∀ (w : Space → Space) (g : Space → (Space →L[ℝ] Space)),
    IsWeakGradient w g → ∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 6) < ⊤ →
      ∫⁻ y, ENNReal.ofReal (matSq (g y)) < ⊤ →
      (∀ ψ : ℝ, ∀ᵐ y, w (axialRot ψ y) = axialRot ψ (w y)) →
      (∀ᵐ y, w (flipPoint y) = flipPoint (w y)) →
      ENNReal.ofReal 2 * ∫⁻ y in spaceSquareExterior R, ENNReal.ofReal (‖w y‖ ^ 2 / ‖y‖ ^ 2)
        ≤ ∫⁻ y in spaceSquareExterior R, ENNReal.ofReal (matSq (g y))

private lemma cutoff_smul_isAxialFlipField {s : ℝ} {w : Space → Space} (hw : IsAxialFlipField w) :
    IsAxialFlipField (fun y => scaledBump s y • w y) := by
  refine ⟨fun ψ y => ?_, fun y => ?_⟩
  · obtain ⟨A, hA⟩ := exists_rotationIsometry ψ
    show scaledBump s (axialRot ψ y) • w (axialRot ψ y) = axialRot ψ (scaledBump s y • w y)
    rw [scaledBump_axialRot, hw.1, ← hA (w y), ← hA (scaledBump s y • w y), map_smul]
  · show scaledBump s (flipPoint y) • w (flipPoint y) = flipPoint (scaledBump s y • w y)
    rw [scaledBump_flip, hw.2, ← flipIsometry_apply, ← flipIsometry_apply, map_smul]


private lemma tail_sixth_tendsto {w : Space → Space} (h6 : Integrable (fun y => ‖w y‖ ^ 6)) :
    Tendsto (fun n : ℕ => ∫ y in (Metric.ball (0 : Space) ((n : ℝ) + 1))ᶜ, ‖w y‖ ^ 6) atTop (𝓝 0) := by
  have hm : ∀ n : ℕ, MeasurableSet (Metric.ball (0 : Space) ((n : ℝ) + 1))ᶜ :=
    fun n => Metric.isOpen_ball.measurableSet.compl
  have ha : Antitone (fun n : ℕ => (Metric.ball (0 : Space) ((n : ℝ) + 1))ᶜ) := by
    intro m n hmn
    have : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
    exact Set.compl_subset_compl.2 (Metric.ball_subset_ball (by linarith))
  have h := tendsto_setIntegral_of_antitone hm ha ⟨0, h6.integrableOn⟩
  have he : (⋂ n : ℕ, (Metric.ball (0 : Space) ((n : ℝ) + 1))ᶜ) = ∅ := by
    ext y
    simp only [Set.mem_iInter, Set.mem_compl_iff, Metric.mem_ball, dist_zero_right,
      Set.mem_empty_iff_false, iff_false, not_forall, not_not]
    obtain ⟨n, hn⟩ := exists_nat_gt ‖y‖
    exact ⟨n, by linarith⟩
  rwa [he, Measure.restrict_empty, integral_zero_measure] at h

private lemma cutoff_stage (h : SquareExteriorSpaceSmoothStatement) {R : ℝ} (hR : 0 < R)
    {w : Space → Space} (hw : ContDiff ℝ 1 w) (h6 : Integrable (fun y => ‖w y‖ ^ 6))
    (hs : IsAxialFlipField w) :
    ENNReal.ofReal 2 * ∫⁻ y in spaceSquareExterior R, ENNReal.ofReal (‖w y‖ ^ 2 / ‖y‖ ^ 2)
      ≤ ∫⁻ y in spaceSquareExterior R, ENNReal.ofReal (matSq (fderiv ℝ w y)) := by
  set S := spaceSquareExterior R
  set A := ∫⁻ y in S, ENNReal.ofReal (matSq (fderiv ℝ w y)) with hA_def
  set V := volume.real (Metric.ball (0 : Space) 1)
  have hV0 : 0 ≤ V := measureReal_nonneg
  obtain ⟨M, hM⟩ := exists_fderiv_roundBump_bound
  set T : ℕ → ℝ := fun n => ∫ y in (Metric.ball (0 : Space) ((n : ℝ) + 1))ᶜ, ‖w y‖ ^ 6
  have hT : Tendsto T atTop (𝓝 0) := tail_sixth_tendsto h6
  have hDw : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
  have step : ∀ (n : ℕ) {δ s : ℝ}, 0 < δ → 0 < s →
      ENNReal.ofReal 2 * ∫⁻ y in S,
          ENNReal.ofReal (‖scaledBump ((n : ℝ) + 1) y • w y‖ ^ 2 / ‖y‖ ^ 2)
        ≤ ENNReal.ofReal (1 + δ) * A +
          ENNReal.ofReal ((1 + δ⁻¹) * 3) * ENNReal.ofReal (M ^ 2 * (8 * V * s + T n / s ^ 2)) := by
    intro n δ s hδ hs0
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hc : ContDiff ℝ 1 (scaledBump ((n : ℝ) + 1)) := (scaledBump_contDiff _).of_le (by norm_num)
    have hv : ContDiff ℝ 1 (fun y => scaledBump ((n : ℝ) + 1) y • w y) := hc.smul hw
    have hvc : HasCompactSupport (fun y => scaledBump ((n : ℝ) + 1) y • w y) :=
      (scaledBump_hasCompactSupport hn).smul_right
    refine (h R hR _ hv hvc (cutoff_smul_isAxialFlipField hs)).trans ?_
    obtain ⟨hg, hgle⟩ := integral_fderiv_scaledBump_sq_mul_le hn hs0 hM hw h6
    have hmeas : Measurable (fun y => ENNReal.ofReal (1 + δ) * ENNReal.ofReal (matSq (fderiv ℝ w y))) :=
      (ENNReal.measurable_ofReal.comp (continuous_matSq'.comp hDw).measurable).const_mul _
    calc ∫⁻ y in S, ENNReal.ofReal (matSq (fderiv ℝ (fun z => scaledBump ((n : ℝ) + 1) z • w z) y))
        ≤ ∫⁻ y in S, (ENNReal.ofReal (1 + δ) * ENNReal.ofReal (matSq (fderiv ℝ w y)) +
            ENNReal.ofReal ((1 + δ⁻¹) * 3) *
              ENNReal.ofReal (‖fderiv ℝ (scaledBump ((n : ℝ) + 1)) y‖ ^ 2 * ‖w y‖ ^ 2)) := by
          refine lintegral_mono fun y => ?_
          rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (mul_nonneg (by linarith) (matSq_nonneg' _)) (by positivity)]
          exact ENNReal.ofReal_le_ofReal ((matSq_fderiv_cutoff_le hδ hw y).trans (le_of_eq (by ring)))
      _ = ENNReal.ofReal (1 + δ) * A + ENNReal.ofReal ((1 + δ⁻¹) * 3) *
            ∫⁻ y in S, ENNReal.ofReal (‖fderiv ℝ (scaledBump ((n : ℝ) + 1)) y‖ ^ 2 * ‖w y‖ ^ 2) := by
          rw [lintegral_add_left hmeas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (1 + δ) * A + ENNReal.ofReal ((1 + δ⁻¹) * 3) *
            ENNReal.ofReal (M ^ 2 * (8 * V * s + T n / s ^ 2)) := by
          gcongr
          calc _ ≤ ∫⁻ y, ENNReal.ofReal (‖fderiv ℝ (scaledBump ((n : ℝ) + 1)) y‖ ^ 2 * ‖w y‖ ^ 2) :=
                setLIntegral_le_lintegral _ _
            _ = ENNReal.ofReal (∫ y, ‖fderiv ℝ (scaledBump ((n : ℝ) + 1)) y‖ ^ 2 * ‖w y‖ ^ 2) :=
                (ofReal_integral_eq_lintegral_ofReal hg (ae_of_all _ fun y => by positivity)).symm
            _ ≤ _ := ENNReal.ofReal_le_ofReal (hgle.trans (le_of_eq (by ring)))
  have limitBound : ∀ {δ s : ℝ}, 0 < δ → 0 < s →
      ENNReal.ofReal 2 * ∫⁻ y in S, ENNReal.ofReal (‖w y‖ ^ 2 / ‖y‖ ^ 2)
        ≤ ENNReal.ofReal (1 + δ) * A +
          ENNReal.ofReal ((1 + δ⁻¹) * 3) * ENNReal.ofReal (M ^ 2 * (8 * V * s)) := by
    intro δ s hδ hs0
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 + δ) * A +
        ENNReal.ofReal ((1 + δ⁻¹) * 3) * ENNReal.ofReal (M ^ 2 * (8 * V * s + T n / s ^ 2))) atTop
        (𝓝 (ENNReal.ofReal (1 + δ) * A +
          ENNReal.ofReal ((1 + δ⁻¹) * 3) * ENNReal.ofReal (M ^ 2 * (8 * V * s)))) := by
      refine tendsto_const_nhds.add
        (ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal ?_) (Or.inr ENNReal.ofReal_ne_top))
      have := ((hT.div_const (s ^ 2)).const_add (8 * V * s)).const_mul (M ^ 2)
      simpa using this
    have hpt : ∀ y, Tendsto (fun n : ℕ => ENNReal.ofReal 2 *
        ENNReal.ofReal (‖scaledBump ((n : ℝ) + 1) y • w y‖ ^ 2 / ‖y‖ ^ 2)) atTop
        (𝓝 (ENNReal.ofReal 2 * ENNReal.ofReal (‖w y‖ ^ 2 / ‖y‖ ^ 2))) := by
      intro y
      apply tendsto_const_nhds.congr'
      obtain ⟨N, hN⟩ := exists_nat_gt ‖y‖
      filter_upwards [eventually_ge_atTop N] with n hn
      have : (N : ℝ) ≤ n := Nat.cast_le.2 hn
      rw [scaledBump_eq_one (by positivity) (by linarith), one_smul]
    have hmeas : ∀ n : ℕ, AEMeasurable (fun y => ENNReal.ofReal 2 *
        ENNReal.ofReal (‖scaledBump ((n : ℝ) + 1) y • w y‖ ^ 2 / ‖y‖ ^ 2)) (volume.restrict S) := by
      intro n
      exact ((ENNReal.measurable_ofReal.comp
        (((((scaledBump_contDiff _).continuous.smul hw.continuous).norm.pow 2).measurable).div
          ((continuous_norm.pow 2).measurable))).const_mul _).aemeasurable
    calc ENNReal.ofReal 2 * ∫⁻ y in S, ENNReal.ofReal (‖w y‖ ^ 2 / ‖y‖ ^ 2)
        = ∫⁻ y in S, liminf (fun n : ℕ => ENNReal.ofReal 2 *
            ENNReal.ofReal (‖scaledBump ((n : ℝ) + 1) y • w y‖ ^ 2 / ‖y‖ ^ 2)) atTop := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact lintegral_congr fun y => ((hpt y).liminf_eq).symm
      _ ≤ liminf (fun n : ℕ => ∫⁻ y in S, ENNReal.ofReal 2 *
            ENNReal.ofReal (‖scaledBump ((n : ℝ) + 1) y • w y‖ ^ 2 / ‖y‖ ^ 2)) atTop :=
          lintegral_liminf_le' hmeas
      _ ≤ liminf (fun n : ℕ => ENNReal.ofReal (1 + δ) * A +
            ENNReal.ofReal ((1 + δ⁻¹) * 3) * ENNReal.ofReal (M ^ 2 * (8 * V * s + T n / s ^ 2))) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact step n hδ hs0
      _ = _ := hlim.liminf_eq
  by_cases hA : A = ⊤
  · rw [hA]
    exact le_top
  have hA' : A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hA).symm
  set a := A.toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ) < ε := hε
  set δ : ℝ := (ε : ℝ) / (2 * (a + 1)) with hδ_def
  have hδ : 0 < δ := by positivity
  set c : ℝ := (1 + δ⁻¹) * 3 * (M ^ 2 * (8 * V)) with hc_def
  have hc : 0 ≤ c := by positivity
  set s : ℝ := (ε : ℝ) / (2 * (c + 1)) with hs_def
  have hs0 : 0 < s := by positivity
  refine (limitBound hδ hs0).trans ?_
  rw [hA', ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_add ha (NNReal.coe_nonneg ε)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e1 : δ * a ≤ ε / 2 := by
    rw [hδ_def, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have e3 : c * s ≤ ε / 2 := by
    rw [hs_def, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have e2 : (1 + δ) * a + (1 + δ⁻¹) * 3 * (M ^ 2 * (8 * V * s)) = a + δ * a + c * s := by
    rw [hc_def]
    ring
  rw [e2]
  linarith
private lemma mem_spaceSquareExterior {R : ℝ} {y : Space} :
    y ∈ spaceSquareExterior R ↔ 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ∧ 0 < y 2 ∧
      (R < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ∨ R < y 2) := by
  simp [spaceSquareExterior, planeSquareExterior, halfPlane, Set.mem_prod, and_assoc]

private lemma isOpen_spaceSquareExterior (R : ℝ) : IsOpen (spaceSquareExterior R) := by
  have : spaceSquareExterior R = {y : Space | 0 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2)} ∩
      ({y : Space | 0 < y 2} ∩ ({y : Space | R < Real.sqrt (y 0 ^ 2 + y 1 ^ 2)} ∪ {y : Space | R < y 2})) := by
    ext y
    simp only [mem_spaceSquareExterior, Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq]
  rw [this]
  exact (isOpen_lt continuous_const continuous_axialRadius).inter
    ((isOpen_lt continuous_const (continuous_coord 2)).inter
      ((isOpen_lt continuous_const continuous_axialRadius).union
        (isOpen_lt continuous_const (continuous_coord 2))))

private def collar (R η : ℝ) : Set Space :=
  {y | (R < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ∨ R < y 2) ∧ -η < y 2}

private lemma isOpen_collar (R η : ℝ) : IsOpen (collar R η) :=
  ((isOpen_lt continuous_const continuous_axialRadius).union
    (isOpen_lt continuous_const (continuous_coord 2))).inter
    (isOpen_lt continuous_const (continuous_coord 2))

private lemma mem_collar_of_near {R η : ℝ} {x t : Space} (hx : x ∈ spaceSquareExterior (R + η))
    (hxt : ‖x - t‖ < η) : t ∈ collar R η := by
  rw [mem_spaceSquareExterior] at hx
  obtain ⟨-, hx2, hx3⟩ := hx
  have hr := axialRadius_le x t
  have hz := coord_sub_le x t 2
  refine ⟨?_, by linarith⟩
  rcases hx3 with h | h
  · left
    linarith
  · right
    linarith

private lemma weakGradient_smoothing {w : Space → Space} {g : Space → (Space →L[ℝ] Space)}
    (hwg : IsWeakGradient w g) (h6 : Integrable (fun y => ‖w y‖ ^ 6))
    (hrot : ∀ ψ : ℝ, ∀ᵐ y, w (axialRot ψ y) = axialRot ψ (w y))
    (hflip : ∀ᵐ y, w (flipPoint y) = flipPoint (w y)) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ 1 (roundKernel s ⋆[lsmul ℝ ℝ, volume] w) ∧
      Integrable (fun y => ‖(roundKernel s ⋆[lsmul ℝ ℝ, volume] w) y‖ ^ 6) ∧
      IsAxialFlipField (roundKernel s ⋆[lsmul ℝ ℝ, volume] w) := by
  have hk := roundKernel_contDiff s
  have hks := roundKernel_hasCompactSupport hs
  have hk0 := roundKernel_nonneg hs
  have hk1 := roundKernel_integral hs
  have hki : Integrable (roundKernel s) := hk.continuous.integrable_of_hasCompactSupport hks
  have hc : ContDiff ℝ 1 (roundKernel s ⋆[lsmul ℝ ℝ, volume] w) :=
    hks.contDiff_convolution_left _ (hk.of_le (by norm_num)) hwg.1
  refine ⟨hc, ?_, ?_, ?_⟩
  · refine (hki.integrable_convolution (lsmul ℝ ℝ) h6).mono' (hc.continuous.norm.pow 6).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact norm_smoothing_sixth_le hk hks hk0 hk1 hwg.1 h6.locallyIntegrable x
  · intro ψ x
    obtain ⟨A, hA⟩ := exists_rotationIsometry ψ
    have hwA : ∀ᵐ y, w (A y) = A (w y) := (hrot ψ).mono fun y hy => by rw [hA, hA]; exact hy
    rw [← hA, ← hA]
    exact smoothing_isometry A (roundKernel_isometry s A) hwA x
  · intro x
    have hwA : ∀ᵐ y, w (flipIsometry y) = flipIsometry (w y) := hflip
    rw [← flipIsometry_apply, ← flipIsometry_apply]
    exact smoothing_isometry flipIsometry (roundKernel_isometry s flipIsometry) hwA x

private lemma smoothing_energy_le {w : Space → Space} {g : Space → (Space →L[ℝ] Space)}
    (hwg : IsWeakGradient w g) (h2 : Integrable (fun y => matSq (g y))) {R η s : ℝ} (hs : 0 < s)
    (hsη : 2 * s ≤ η) :
    ∫⁻ x in spaceSquareExterior (R + η),
        ENNReal.ofReal (matSq (fderiv ℝ (roundKernel s ⋆[lsmul ℝ ℝ, volume] w) x))
      ≤ ∫⁻ t in collar R η, ENNReal.ofReal (matSq (g t)) := by
  have hk := roundKernel_contDiff s
  have hks := roundKernel_hasCompactSupport hs
  have hk0 := roundKernel_nonneg hs
  have hkc : Continuous (roundKernel s) := hk.continuous
  have hki : Integrable (roundKernel s) := hkc.integrable_of_hasCompactSupport hks
  have hf0 : ∀ t, 0 ≤ matSq (g t) := fun t => matSq_nonneg' _
  have hfm : AEMeasurable (fun t => ENNReal.ofReal (matSq (g t))) volume :=
    h2.aemeasurable.ennreal_ofReal
  have hS : MeasurableSet (spaceSquareExterior (R + η)) :=
    (isOpen_spaceSquareExterior _).measurableSet
  have hU : MeasurableSet (collar R η) := (isOpen_collar R η).measurableSet
  have hpt : ∀ x, ENNReal.ofReal (matSq (fderiv ℝ (roundKernel s ⋆[lsmul ℝ ℝ, volume] w) x))
      ≤ ∫⁻ t, ENNReal.ofReal (roundKernel s (x - t)) * ENNReal.ofReal (matSq (g t)) := by
    intro x
    refine (ENNReal.ofReal_le_ofReal (matSq_fderiv_smoothing_le hk hks hk0 (roundKernel_integral hs)
      hwg h2.locallyIntegrable x)).trans (le_of_eq ?_)
    have hex : ConvolutionExistsAt (roundKernel s) (fun y => matSq (g y)) x (lsmul ℝ ℝ) volume :=
      hks.convolutionExists_left _ hkc h2.locallyIntegrable x
    have hint : Integrable (fun t => roundKernel s (x - t) * matSq (g t)) := by
      have h1 := Integrable.comp_sub_left (μ := volume) hex x
      simpa [lsmul_apply, smul_eq_mul, sub_sub_cancel] using h1
    rw [convolution_eq_swap]
    simp only [lsmul_apply, smul_eq_mul]
    rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun t => mul_nonneg (hk0 _) (hf0 _))]
    exact lintegral_congr fun t => ENNReal.ofReal_mul (hk0 _)
  have hmeas : AEMeasurable (Function.uncurry fun x t =>
      ENNReal.ofReal (roundKernel s (x - t)) * ENNReal.ofReal (matSq (g t)))
      ((volume.restrict (spaceSquareExterior (R + η))).prod volume) :=
    ((hkc.comp (continuous_fst.sub continuous_snd)).measurable.ennreal_ofReal.aemeasurable).mul
      hfm.comp_snd
  have hone : ∀ t, ∫⁻ x, ENNReal.ofReal (roundKernel s (x - t)) = 1 := by
    intro t
    rw [lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (roundKernel s x)) t,
      ← ofReal_integral_eq_lintegral_ofReal hki (ae_of_all _ hk0), roundKernel_integral hs,
      ENNReal.ofReal_one]
  calc ∫⁻ x in spaceSquareExterior (R + η),
        ENNReal.ofReal (matSq (fderiv ℝ (roundKernel s ⋆[lsmul ℝ ℝ, volume] w) x))
      ≤ ∫⁻ x in spaceSquareExterior (R + η), ∫⁻ t,
          ENNReal.ofReal (roundKernel s (x - t)) * ENNReal.ofReal (matSq (g t)) :=
        lintegral_mono hpt
    _ = ∫⁻ t, ∫⁻ x in spaceSquareExterior (R + η),
          ENNReal.ofReal (roundKernel s (x - t)) * ENNReal.ofReal (matSq (g t)) :=
        lintegral_lintegral_swap hmeas
    _ = ∫⁻ t, (∫⁻ x in spaceSquareExterior (R + η), ENNReal.ofReal (roundKernel s (x - t))) *
          ENNReal.ofReal (matSq (g t)) :=
        lintegral_congr fun t => lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∫⁻ t, (collar R η).indicator (fun t => ENNReal.ofReal (matSq (g t))) t := by
        refine lintegral_mono fun t => ?_
        by_cases ht : t ∈ collar R η
        · rw [Set.indicator_of_mem ht]
          calc (∫⁻ x in spaceSquareExterior (R + η), ENNReal.ofReal (roundKernel s (x - t))) *
                ENNReal.ofReal (matSq (g t))
              ≤ 1 * ENNReal.ofReal (matSq (g t)) := by
                gcongr
                exact (setLIntegral_le_lintegral _ _).trans (le_of_eq (hone t))
            _ = _ := one_mul _
        · rw [Set.indicator_of_notMem ht]
          have hz : ∫⁻ x in spaceSquareExterior (R + η), ENNReal.ofReal (roundKernel s (x - t)) = 0 := by
            rw [← lintegral_zero (μ := volume.restrict (spaceSquareExterior (R + η)))]
            refine lintegral_congr_ae ((ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx => ?_))
            by_contra hne
            have hne' : roundKernel s (x - t) ≠ 0 := fun h0 => hne (by simp [h0])
            exact ht (mem_collar_of_near hx ((norm_lt_of_roundKernel_ne hs hne').trans_le hsη))
          rw [hz, zero_mul]
    _ = ∫⁻ t in collar R η, ENNReal.ofReal (matSq (g t)) := lintegral_indicator hU _

theorem squareExteriorSpaceWeak_of (h : SquareExteriorSpaceSmoothStatement) :
    SquareExteriorSpaceWeakStatement := by
  intro R hR w g hwg h6 h2 hrot hflip
  have hwm : AEStronglyMeasurable w volume := hwg.1.aestronglyMeasurable
  have h6i : Integrable (fun y => ‖w y‖ ^ 6) :=
    ⟨hwm.norm.pow 6, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => by positivity)).2 h6⟩
  have h2i : Integrable (fun y => matSq (g y)) :=
    ⟨continuous_matSq'.comp_aestronglyMeasurable hwg.2.1.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => matSq_nonneg' _)).2 h2⟩
  have hεpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hεanti : ∀ {m n : ℕ}, m ≤ n → 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
    intro m n hmn
    have : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hconv := ae_tendsto_roundKernel hwg.1
  have stepN : ∀ N : ℕ, ENNReal.ofReal 2 *
      ∫⁻ y in spaceSquareExterior (R + 2 * (1 / ((N : ℝ) + 1))), ENNReal.ofReal (‖w y‖ ^ 2 / ‖y‖ ^ 2)
        ≤ ∫⁻ t in collar R (2 * (1 / ((N : ℝ) + 1))), ENNReal.ofReal (matSq (g t)) := by
    intro N
    have hbound : ∀ n : ℕ, N ≤ n → ENNReal.ofReal 2 *
        ∫⁻ y in spaceSquareExterior (R + 2 * (1 / ((N : ℝ) + 1))),
          ENNReal.ofReal (‖(roundKernel (1 / ((n : ℝ) + 1)) ⋆[lsmul ℝ ℝ, volume] w) y‖ ^ 2 / ‖y‖ ^ 2)
        ≤ ∫⁻ t in collar R (2 * (1 / ((N : ℝ) + 1))), ENNReal.ofReal (matSq (g t)) := by
      intro n hn
      obtain ⟨hc, h6n, hsym⟩ := weakGradient_smoothing hwg h6i hrot hflip (hεpos n)
      refine (cutoff_stage h (by have := hεpos N; linarith) hc h6n hsym).trans ?_
      exact smoothing_energy_le hwg h2i (hεpos n) (by have := hεanti hn; linarith)
    have hmeas : ∀ n : ℕ, AEMeasurable (fun y => ENNReal.ofReal 2 *
        ENNReal.ofReal (‖(roundKernel (1 / ((n : ℝ) + 1)) ⋆[lsmul ℝ ℝ, volume] w) y‖ ^ 2 / ‖y‖ ^ 2))
        (volume.restrict (spaceSquareExterior (R + 2 * (1 / ((N : ℝ) + 1))))) := by
      intro n
      obtain ⟨hc, -, -⟩ := weakGradient_smoothing hwg h6i hrot hflip (hεpos n)
      exact ((ENNReal.measurable_ofReal.comp (((hc.continuous.norm.pow 2).measurable).div
        ((continuous_norm.pow 2).measurable))).const_mul _).aemeasurable
    have hlim : ∀ᵐ y ∂(volume.restrict (spaceSquareExterior (R + 2 * (1 / ((N : ℝ) + 1))))),
        Tendsto (fun n : ℕ => ENNReal.ofReal 2 * ENNReal.ofReal
          (‖(roundKernel (1 / ((n : ℝ) + 1)) ⋆[lsmul ℝ ℝ, volume] w) y‖ ^ 2 / ‖y‖ ^ 2)) atTop
          (𝓝 (ENNReal.ofReal 2 * ENNReal.ofReal (‖w y‖ ^ 2 / ‖y‖ ^ 2))) := by
      refine ae_restrict_of_ae (hconv.mono fun y hy => ?_)
      exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal ((hy.norm.pow 2).div_const _))
        (Or.inr ENNReal.ofReal_ne_top)
    calc ENNReal.ofReal 2 * ∫⁻ y in spaceSquareExterior (R + 2 * (1 / ((N : ℝ) + 1))),
          ENNReal.ofReal (‖w y‖ ^ 2 / ‖y‖ ^ 2)
        = ∫⁻ y in spaceSquareExterior (R + 2 * (1 / ((N : ℝ) + 1))),
            liminf (fun n : ℕ => ENNReal.ofReal 2 * ENNReal.ofReal
              (‖(roundKernel (1 / ((n : ℝ) + 1)) ⋆[lsmul ℝ ℝ, volume] w) y‖ ^ 2 / ‖y‖ ^ 2)) atTop := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact lintegral_congr_ae (hlim.mono fun y hy => hy.liminf_eq.symm)
      _ ≤ liminf (fun n : ℕ => ∫⁻ y in spaceSquareExterior (R + 2 * (1 / ((N : ℝ) + 1))),
            ENNReal.ofReal 2 * ENNReal.ofReal
              (‖(roundKernel (1 / ((n : ℝ) + 1)) ⋆[lsmul ℝ ℝ, volume] w) y‖ ^ 2 / ‖y‖ ^ 2)) atTop :=
          lintegral_liminf_le' hmeas
      _ ≤ liminf (fun _ : ℕ => ∫⁻ t in collar R (2 * (1 / ((N : ℝ) + 1))),
            ENNReal.ofReal (matSq (g t))) atTop := by
          refine liminf_le_liminf ((eventually_ge_atTop N).mono fun n hn => ?_)
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact hbound n hn
      _ = _ := liminf_const _
  have hSm : ∀ r : ℝ, MeasurableSet (spaceSquareExterior r) :=
    fun r => (isOpen_spaceSquareExterior r).measurableSet
  have hUm : ∀ N : ℕ, MeasurableSet (collar R (2 * (1 / ((N : ℝ) + 1)))) :=
    fun N => (isOpen_collar _ _).measurableSet
  have hmono : Monotone (fun N : ℕ => spaceSquareExterior (R + 2 * (1 / ((N : ℝ) + 1)))) := by
    intro m n hmn y hy
    have := hεanti hmn
    rw [mem_spaceSquareExterior] at hy ⊢
    obtain ⟨h1, h2', h3⟩ := hy
    refine ⟨h1, h2', ?_⟩
    rcases h3 with h3 | h3
    · left; linarith
    · right; linarith
  have hunion : (⋃ N : ℕ, spaceSquareExterior (R + 2 * (1 / ((N : ℝ) + 1)))) = spaceSquareExterior R := by
    ext y
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨N, hN⟩
      have := hεpos N
      rw [mem_spaceSquareExterior] at hN ⊢
      obtain ⟨h1, h2', h3⟩ := hN
      refine ⟨h1, h2', ?_⟩
      rcases h3 with h3 | h3
      · left; linarith
      · right; linarith
    · intro hy
      rw [mem_spaceSquareExterior] at hy
      obtain ⟨h1, h2', h3⟩ := hy
      have hpos : 0 < max (Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) (y 2) - R := by
        rcases h3 with h3 | h3
        · linarith [le_max_left (Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) (y 2)]
        · linarith [le_max_right (Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) (y 2)]
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos hpos)
      refine ⟨N, ?_⟩
      rw [mem_spaceSquareExterior]
      refine ⟨h1, h2', ?_⟩
      rcases le_total (y 2) (Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) with hm | hm
      · left
        rw [max_eq_left hm] at hN
        linarith
      · right
        rw [max_eq_right hm] at hN
        linarith
  have hanti : Antitone (fun N : ℕ => collar R (2 * (1 / ((N : ℝ) + 1)))) := by
    intro m n hmn y hy
    have := hεanti hmn
    exact ⟨hy.1, by linarith [hy.2]⟩
  have hinter : (⋂ N : ℕ, collar R (2 * (1 / ((N : ℝ) + 1)))) ⊆
      spaceSquareExterior R ∪ ({y : Space | y 2 = 0} ∪ {y : Space | y 0 = 0}) := by
    intro y hy
    simp only [Set.mem_iInter] at hy
    have hz : 0 ≤ y 2 := by
      by_contra hneg
      replace hneg := not_le.1 hneg
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos (neg_pos.2 hneg))
      linarith [(hy N).2]
    rcases hz.lt_or_eq with hz | hz
    · rcases (Real.sqrt_nonneg (y 0 ^ 2 + y 1 ^ 2)).lt_or_eq with hr | hr
      · left
        exact mem_spaceSquareExterior.2 ⟨hr, hz, (hy 0).1⟩
      · right; right
        have h0 : y 0 ^ 2 + y 1 ^ 2 ≤ 0 := Real.sqrt_eq_zero'.1 hr.symm
        show y 0 = 0
        nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    · right; left
      exact hz.symm
  set νL := volume.withDensity (fun y : Space => ENNReal.ofReal (‖w y‖ ^ 2 / ‖y‖ ^ 2))
  set νR := volume.withDensity (fun y : Space => ENNReal.ofReal (matSq (g y)))
  have hL : Tendsto (fun N : ℕ => ENNReal.ofReal 2 * νL (spaceSquareExterior (R + 2 * (1 / ((N : ℝ) + 1)))))
      atTop (𝓝 (ENNReal.ofReal 2 * νL (spaceSquareExterior R))) := by
    rw [← hunion]
    exact ENNReal.Tendsto.const_mul (tendsto_measure_iUnion_atTop hmono) (Or.inr ENNReal.ofReal_ne_top)
  have hfin : νR (collar R (2 * (1 / (((0 : ℕ) : ℝ) + 1)))) ≠ ⊤ := by
    refine ((measure_mono (Set.subset_univ _)).trans_lt ?_).ne
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact h2
  have hRt : Tendsto (fun N : ℕ => νR (collar R (2 * (1 / ((N : ℝ) + 1))))) atTop
      (𝓝 (νR (⋂ N : ℕ, collar R (2 * (1 / ((N : ℝ) + 1)))))) :=
    tendsto_measure_iInter_atTop (fun N => (hUm N).nullMeasurableSet) hanti ⟨0, hfin⟩
  have key := le_of_tendsto_of_tendsto' hL hRt fun N => by
    rw [withDensity_apply _ (hSm _), withDensity_apply _ (hUm N)]
    exact stepN N
  have hnull : νR ({y : Space | y 2 = 0} ∪ {y : Space | y 0 = 0}) = 0 :=
    withDensity_absolutelyContinuous _ _ (measure_union_null (volume_coord_zero 2) (volume_coord_zero 0))
  rw [withDensity_apply _ (hSm R)] at key
  refine key.trans ?_
  calc νR (⋂ N : ℕ, collar R (2 * (1 / ((N : ℝ) + 1))))
      ≤ νR (spaceSquareExterior R ∪ ({y : Space | y 2 = 0} ∪ {y : Space | y 0 = 0})) := measure_mono hinter
    _ ≤ νR (spaceSquareExterior R) + νR ({y : Space | y 2 = 0} ∪ {y : Space | y 0 = 0}) :=
        measure_union_le _ _
    _ = ∫⁻ y in spaceSquareExterior R, ENNReal.ofReal (matSq (g y)) := by
        rw [hnull, add_zero, withDensity_apply _ (hSm R)]

end TailBand

end CertCell

end Breakdown
