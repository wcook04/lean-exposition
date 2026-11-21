import Breakdown.CertCell.InstanceStatements
import Breakdown.CertCell.InstanceGeneratorForm

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Instance

open CellCert.CellAnalysis (CellBox cylRadius cylHeight radialUnit angularUnit axialUnit)

private theorem coord_continuous (i : Fin 3) : Continuous fun y : Space => y i := by
  fun_prop

private theorem solid_isClosed (K : CellBox) : IsClosed K.solid := by
  have hρ : Continuous cylRadius := by
    change Continuous fun y : Space => Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
    fun_prop
  have hh : Continuous fun y : Space => |cylHeight y| := by
    change Continuous fun y : Space => |y 2|
    fun_prop
  exact (isClosed_le continuous_const hρ).inter ((isClosed_le hρ continuous_const).inter
    ((isClosed_le continuous_const hh).inter (isClosed_le hh continuous_const)))

private theorem solid_isBounded (K : CellBox) : Bornology.IsBounded K.solid := by
  refine (Metric.isBounded_closedBall (x := (0 : Space)) (r := Real.sqrt (K.r₂ ^ 2 + K.z₂ ^ 2))).subset
    fun y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  obtain ⟨-, h2, -, h4⟩ := hy
  have hs : 0 ≤ y 0 ^ 2 + y 1 ^ 2 := by positivity
  have hsq := Real.sq_sqrt hs
  have hnn := Real.sqrt_nonneg (y 0 ^ 2 + y 1 ^ 2)
  have hr : y 0 ^ 2 + y 1 ^ 2 ≤ K.r₂ ^ 2 := by
    change Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ K.r₂ at h2
    nlinarith
  have hz : y 2 ^ 2 ≤ K.z₂ ^ 2 := by
    unfold cylHeight at h4
    have ha := abs_nonneg (y 2)
    have hb : |y 2| ^ 2 = y 2 ^ 2 := sq_abs _
    nlinarith
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  linarith

private theorem testValue_continuous {count rowCount : ℕ} (R : RowValues count rowCount)
    (box : Fin count → CellBox) (a : Fin rowCount) (c : Fin 3) :
    Continuous (R.testValue box a c) := by
  unfold RowValues.testValue CellPoly.eval CellBox.refR CellBox.refZ
  fun_prop

private theorem labelPhase_continuous (m : ℕ) (ι : ℤ × ℤ) :
    Continuous fun q : ℝ × ℝ => labelPhase m ι q.1 q.2 := by
  unfold labelPhase
  fun_prop

private theorem labelPhase_norm (m : ℕ) (ι : ℤ × ℤ) (σ θ : ℝ) : ‖labelPhase m ι σ θ‖ = 1 := by
  unfold labelPhase
  exact Complex.norm_exp_ofReal_mul_I _

private theorem rowPartFactor_norm (b : Bool) : ‖rowPartFactor b‖ = 1 := by
  unfold rowPartFactor
  split_ifs <;> simp

private theorem frameSign_norm (c : Fin 3) : ‖(frameSign c : ℂ)‖ = 1 := by
  unfold frameSign
  split_ifs <;> simp

private theorem frameUnit_norm_le (θ : ℝ) (c : Fin 3) : ‖frameUnit θ c‖ ≤ 2 := by
  fin_cases c
  · show ‖radialUnit θ‖ ≤ 2
    unfold radialUnit
    refine (norm_add_le _ _).trans ?_
    rw [PiLp.norm_single, PiLp.norm_single, Real.norm_eq_abs, Real.norm_eq_abs]
    linarith [Real.abs_cos_le_one θ, Real.abs_sin_le_one θ]
  · show ‖angularUnit θ‖ ≤ 2
    unfold angularUnit
    refine (norm_add_le _ _).trans ?_
    rw [PiLp.norm_single, PiLp.norm_single, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
    linarith [Real.abs_cos_le_one θ, Real.abs_sin_le_one θ]
  · show ‖axialUnit‖ ≤ 2
    unfold axialUnit
    rw [PiLp.norm_single]
    norm_num

private theorem single_eq_smul (i : Fin 3) (t : ℝ) :
    (EuclideanSpace.single i t : Space) = t • (EuclideanSpace.single i (1 : ℝ) : Space) := by
  ext j
  simp only [PiLp.single_apply, PiLp.smul_apply, smul_eq_mul]
  split_ifs <;> simp

private theorem single_continuous (i : Fin 3) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous fun θ : ℝ => (EuclideanSpace.single i (f θ) : Space) := by
  have h : (fun θ : ℝ => (EuclideanSpace.single i (f θ) : Space)) =
      fun θ => f θ • (EuclideanSpace.single i (1 : ℝ) : Space) := funext fun θ => single_eq_smul i (f θ)
  rw [h]
  exact hf.smul continuous_const

private theorem frameUnit_continuous (c : Fin 3) : Continuous fun θ : ℝ => frameUnit θ c := by
  fin_cases c
  · show Continuous fun θ : ℝ => radialUnit θ
    unfold radialUnit
    exact (single_continuous 0 Real.continuous_cos).add (single_continuous 1 Real.continuous_sin)
  · show Continuous fun θ : ℝ => angularUnit θ
    unfold angularUnit
    exact (single_continuous 0 Real.continuous_sin.neg).add (single_continuous 1 Real.continuous_cos)
  · exact continuous_const

private theorem pointAngle_measurable : Measurable pointAngle := by
  unfold pointAngle
  exact Complex.measurable_arg.comp
    (by fun_prop : Continuous fun y : Space => (y 0 : ℂ) + (y 1 : ℂ) * Complex.I).measurable

private theorem term_norm_le (φ v : ℂ) (hφ : ‖φ‖ = 1) (u : Space) (hu : ‖u‖ ≤ 2) :
    ‖(φ * v).re • u‖ ≤ 2 * ‖v‖ := by
  rw [norm_smul, Real.norm_eq_abs]
  calc |(φ * v).re| * ‖u‖ ≤ ‖φ * v‖ * 2 :=
        mul_le_mul (Complex.abs_re_le_norm _) hu (norm_nonneg _) (norm_nonneg _)
    _ = 2 * ‖v‖ := by rw [norm_mul, hφ]; ring

private theorem generatorField_norm_le {rowCount : ℕ} (M : CellMesh) (R : RowValues M.count rowCount)
    (m : ℕ) (a : Fin rowCount) : ∃ B : ℝ, ∀ σ y, ‖R.generatorField M.box m a σ y‖ ≤
      (M.box (R.cellOf a)).solid.indicator (fun _ => B) y := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (f := fun p : ℝ × ℝ => ∑ c : Fin 3, ‖R.testValue M.box a c p‖)
    (continuous_finsetSum _ fun c _ => (testValue_continuous R M.box a c).norm).continuousOn
  refine ⟨2 * C, fun σ y => ?_⟩
  rw [generatorField_eq]
  by_cases hy : y ∈ (M.box (R.cellOf a)).solid
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    obtain ⟨h1, h2, h3, h4⟩ := hy
    have hsum : ∀ q : ℝ × ℝ, q ∈ (M.box (R.cellOf a)).rect → ∑ c : Fin 3, ‖R.testValue M.box a c q‖ ≤ C := by
      intro q hq
      have := hC q hq
      rwa [Real.norm_of_nonneg (Finset.sum_nonneg fun c _ => norm_nonneg _)] at this
    refine (norm_sum_le _ _).trans ?_
    by_cases h0 : 0 ≤ y 2
    · have hq : pointPlane y ∈ (M.box (R.cellOf a)).rect := by
        unfold cylHeight at h3 h4
        rw [abs_of_nonneg h0] at h3 h4
        exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      calc ∑ c : Fin 3, ‖(labelPhase m (if 0 ≤ y 2 then R.labelOf a else labelFlip (R.labelOf a)) σ (pointAngle y) *
              (if 0 ≤ y 2 then rowPartFactor (R.realPart a) * R.testValue M.box a c (pointPlane y)
                else (frameSign c : ℂ) * rowPartFactor (R.realPart a) *
                  R.testValue M.box a c ((pointPlane y).1, -(pointPlane y).2))).re • frameUnit (pointAngle y) c‖
          ≤ ∑ c : Fin 3, 2 * ‖R.testValue M.box a c (pointPlane y)‖ := by
            refine Finset.sum_le_sum fun c _ => ?_
            simp only [if_pos h0]
            refine (term_norm_le _ _ (labelPhase_norm _ _ _ _) _ (frameUnit_norm_le _ _)).trans ?_
            rw [norm_mul, rowPartFactor_norm, one_mul]
        _ = 2 * ∑ c : Fin 3, ‖R.testValue M.box a c (pointPlane y)‖ := by rw [Finset.mul_sum]
        _ ≤ 2 * C := by linarith [hsum _ hq]
    · have hq : ((pointPlane y).1, -(pointPlane y).2) ∈ (M.box (R.cellOf a)).rect := by
        unfold cylHeight at h3 h4
        rw [abs_of_neg (lt_of_not_ge h0)] at h3 h4
        exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      calc ∑ c : Fin 3, ‖(labelPhase m (if 0 ≤ y 2 then R.labelOf a else labelFlip (R.labelOf a)) σ (pointAngle y) *
              (if 0 ≤ y 2 then rowPartFactor (R.realPart a) * R.testValue M.box a c (pointPlane y)
                else (frameSign c : ℂ) * rowPartFactor (R.realPart a) *
                  R.testValue M.box a c ((pointPlane y).1, -(pointPlane y).2))).re • frameUnit (pointAngle y) c‖
          ≤ ∑ c : Fin 3, 2 * ‖R.testValue M.box a c ((pointPlane y).1, -(pointPlane y).2)‖ := by
            refine Finset.sum_le_sum fun c _ => ?_
            simp only [if_neg h0]
            refine (term_norm_le _ _ (labelPhase_norm _ _ _ _) _ (frameUnit_norm_le _ _)).trans ?_
            rw [norm_mul, norm_mul, rowPartFactor_norm, frameSign_norm, one_mul, one_mul]
        _ = 2 * ∑ c : Fin 3, ‖R.testValue M.box a c ((pointPlane y).1, -(pointPlane y).2)‖ := by
            rw [Finset.mul_sum]
        _ ≤ 2 * C := by linarith [hsum _ hq]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, norm_zero]

private theorem generatorField_measurable {rowCount : ℕ} (M : CellMesh) (R : RowValues M.count rowCount)
    (m : ℕ) (a : Fin rowCount) :
    Measurable fun z : ℝ × Space => R.generatorField M.box m a z.1 z.2 := by
  have hA : Measurable fun z : ℝ × Space => pointAngle z.2 := pointAngle_measurable.comp measurable_snd
  have hH : MeasurableSet {z : ℝ × Space | 0 ≤ z.2 2} :=
    measurableSet_le measurable_const ((coord_continuous 2).measurable.comp measurable_snd)
  have hS : MeasurableSet (Prod.snd ⁻¹' (M.box (R.cellOf a)).solid : Set (ℝ × Space)) :=
    (solid_isClosed _).measurableSet.preimage measurable_snd
  have hP : Continuous pointPlane := by
    unfold pointPlane
    fun_prop
  have hphase : ∀ ι, Measurable fun z : ℝ × Space => labelPhase m ι z.1 (pointAngle z.2) :=
    fun ι => (labelPhase_continuous m ι).measurable.comp (measurable_fst.prodMk hA)
  have hU : ∀ c, Measurable fun z : ℝ × Space => R.testValue M.box a c (pointPlane z.2) :=
    fun c => ((testValue_continuous R M.box a c).comp hP).measurable.comp measurable_snd
  have hL : ∀ c, Measurable fun z : ℝ × Space =>
      R.testValue M.box a c ((pointPlane z.2).1, -(pointPlane z.2).2) := fun c =>
    ((testValue_continuous R M.box a c).comp (hP.fst.prodMk hP.snd.neg)).measurable.comp measurable_snd
  have heq : (fun z : ℝ × Space => R.generatorField M.box m a z.1 z.2) =
      (Prod.snd ⁻¹' (M.box (R.cellOf a)).solid).indicator (fun z => ∑ c : Fin 3,
        (if 0 ≤ z.2 2 then
          (labelPhase m (R.labelOf a) z.1 (pointAngle z.2) *
            (rowPartFactor (R.realPart a) * R.testValue M.box a c (pointPlane z.2))).re
        else
          (labelPhase m (labelFlip (R.labelOf a)) z.1 (pointAngle z.2) *
            ((frameSign c : ℂ) * rowPartFactor (R.realPart a) *
              R.testValue M.box a c ((pointPlane z.2).1, -(pointPlane z.2).2))).re) •
          frameUnit (pointAngle z.2) c) := by
    funext z
    rw [generatorField_eq]
    by_cases hz : z.2 ∈ (M.box (R.cellOf a)).solid
    · rw [Set.indicator_of_mem hz,
        Set.indicator_of_mem (show z ∈ Prod.snd ⁻¹' (M.box (R.cellOf a)).solid from hz)]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases h0 : 0 ≤ z.2 2
      · simp only [if_pos h0]
      · simp only [if_neg h0]
    · rw [Set.indicator_of_notMem hz,
        Set.indicator_of_notMem (show z ∉ Prod.snd ⁻¹' (M.box (R.cellOf a)).solid from hz)]
  rw [heq]
  refine Measurable.indicator ?_ hS
  refine Finset.measurable_sum _ fun c _ => ?_
  refine Measurable.smul (M := ℝ) (Measurable.ite hH ?_ ?_) ((frameUnit_continuous c).measurable.comp hA)
  · exact Complex.measurable_re.comp ((hphase _).mul (measurable_const.mul (hU c)))
  · exact Complex.measurable_re.comp ((hphase _).mul (measurable_const.mul (hL c)))

private theorem pairing_integrable (F H : ℝ → Space → Space)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤)
    (hHm : Measurable fun z : ℝ × Space => H z.1 z.2) (S : Set Space) (hS : MeasurableSet S)
    (hSb : volume S < ⊤) (B : ℝ) (hB : ∀ σ y, ‖H σ y‖ ≤ S.indicator (fun _ => B) y) :
    Integrable (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (H z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  have hac : (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space) ≪
      (volume : Measure ℝ).prod (volume : Measure Space) :=
    Measure.AbsolutelyContinuous.prod (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
      Measure.AbsolutelyContinuous.rfl
  have hFm' : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := hFm.mono_ac hac
  have hF2i : Integrable (fun z : ℝ × Space => ‖F z.1 z.2‖ ^ 2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    refine ⟨hFm'.norm.pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => by positivity),
      lintegral_prod (fun z : ℝ × Space => ENNReal.ofReal (‖F z.1 z.2‖ ^ 2))
        (hFm'.norm.pow 2).aemeasurable.ennreal_ofReal]
    exact hF2
  have hind : Integrable (fun z : ℝ × Space => S.indicator (fun _ => B ^ 2) z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    have h : (fun z : ℝ × Space => S.indicator (fun _ => B ^ 2) z.2) =
        (Set.univ ×ˢ S).indicator (fun _ => B ^ 2) := by
      funext z
      by_cases hz : z.2 ∈ S
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (show z ∈ Set.univ ×ˢ S from ⟨Set.mem_univ _, hz⟩)]
      · rw [Set.indicator_of_notMem hz,
          Set.indicator_of_notMem (show z ∉ Set.univ ×ˢ S from fun h => hz h.2)]
    rw [h, integrable_indicator_iff (MeasurableSet.univ.prod hS)]
    refine integrableOn_const ?_
    rw [Measure.prod_prod, Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSb.ne
  refine Integrable.mono' (hF2i.add hind) (hFm'.inner hHm.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => ?_)
  have h1 := norm_inner_le_norm (𝕜 := ℝ) (F z.1 z.2) (H z.1 z.2)
  have h2 := hB z.1 z.2
  have h3 : S.indicator (fun _ => B) z.2 ^ 2 = S.indicator (fun _ => B ^ 2) z.2 := by
    by_cases hz : z.2 ∈ S
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
      ring
  have h4 := norm_nonneg (H z.1 z.2)
  have h5 := norm_nonneg (F z.1 z.2)
  have h6 := mul_le_mul_of_nonneg_left h2 h5
  have h7 := sq_nonneg (‖F z.1 z.2‖ - S.indicator (fun _ => B) z.2)
  have h8 : 0 ≤ ‖F z.1 z.2‖ * S.indicator (fun _ => B) z.2 := mul_nonneg h5 (h4.trans h2)
  simp only [Pi.add_apply]
  nlinarith

private theorem periodPairing_eq_integral (F H : ℝ → Space → Space)
    (hint : Integrable (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (H z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume)) :
    periodPairing F H = ∫ z, inner ℝ (F z.1 z.2) (H z.1 z.2)
      ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  unfold periodPairing
  rw [integral_prod _ hint]

theorem periodPairing_generator_halves {rowCount : ℕ} (M : CellMesh) (R : RowValues M.count rowCount)
    (m : ℕ) (F : ℝ → Space → Space) (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (a : Fin rowCount) :
    periodPairing F (R.generatorField M.box m a) =
      periodPairing F (fun σ y => Set.indicator {y : Space | 0 ≤ y 2} (R.generatorField M.box m a σ) y) +
      periodPairing F (fun σ y => Set.indicator {y : Space | y 2 < 0} (R.generatorField M.box m a σ) y) := by
  obtain ⟨B, hB⟩ := generatorField_norm_le M R m a
  have hG := generatorField_measurable M R m a
  have hU : MeasurableSet {y : Space | 0 ≤ y 2} :=
    measurableSet_le measurable_const (coord_continuous 2).measurable
  have hL : MeasurableSet {y : Space | y 2 < 0} :=
    measurableSet_lt (coord_continuous 2).measurable measurable_const
  have hS := (solid_isClosed (M.box (R.cellOf a))).measurableSet
  have hSb : volume (M.box (R.cellOf a)).solid < ⊤ := (solid_isBounded _).measure_lt_top
  have half : ∀ T : Set Space, MeasurableSet T →
      Integrable (fun z : ℝ × Space =>
        inner ℝ (F z.1 z.2) (Set.indicator T (R.generatorField M.box m a z.1) z.2))
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    intro T hT
    refine pairing_integrable F (fun σ y => Set.indicator T (R.generatorField M.box m a σ) y) hFm hF2 ?_ _ hS
      hSb B fun σ y => ?_
    · have h : (fun z : ℝ × Space => Set.indicator T (R.generatorField M.box m a z.1) z.2) =
          (Prod.snd ⁻¹' T).indicator (fun z => R.generatorField M.box m a z.1 z.2) := by
        funext z
        by_cases hz : z.2 ∈ T
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (show z ∈ Prod.snd ⁻¹' T from hz)]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (show z ∉ Prod.snd ⁻¹' T from hz)]
      exact h ▸ hG.indicator (hT.preimage measurable_snd)
    · exact le_trans (norm_indicator_le_norm_self _ _) (hB σ y)
  rw [periodPairing_eq_integral F _ (pairing_integrable F _ hFm hF2 hG _ hS hSb B hB),
    periodPairing_eq_integral F (fun σ y => Set.indicator {y : Space | 0 ≤ y 2} (R.generatorField M.box m a σ) y)
      (half _ hU),
    periodPairing_eq_integral F (fun σ y => Set.indicator {y : Space | y 2 < 0} (R.generatorField M.box m a σ) y)
      (half _ hL)]
  refine Eq.trans ?_ (integral_add (half _ hU) (half _ hL))
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  rw [← inner_add_right]
  congr 1
  by_cases h0 : 0 ≤ z.2 2
  · rw [Set.indicator_of_mem (show z.2 ∈ {y : Space | 0 ≤ y 2} from h0),
      Set.indicator_of_notMem (show z.2 ∉ {y : Space | y 2 < 0} from not_lt.2 h0), add_zero]
  · rw [Set.indicator_of_notMem (show z.2 ∉ {y : Space | 0 ≤ y 2} from h0),
      Set.indicator_of_mem (show z.2 ∈ {y : Space | y 2 < 0} from lt_of_not_ge h0), zero_add]

theorem generatorPairingMoments_of_halves
    (hup : ∀ {rowCount : ℕ} (M : CellMesh) (R : RowValues M.count rowCount) (m : ℕ) (tauMax : ℝ),
      IsRowValues M R m tauMax → ∀ F : ℝ → Space → Space,
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ → ∀ a,
      periodPairing F (fun σ y => Set.indicator {y : Space | 0 ≤ y 2} (R.generatorField M.box m a σ) y) =
        R.upperMoment M.box m a F)
    (hlow : ∀ {rowCount : ℕ} (M : CellMesh) (R : RowValues M.count rowCount) (m : ℕ) (tauMax : ℝ),
      IsRowValues M R m tauMax → ∀ F : ℝ → Space → Space,
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ → ∀ a,
      periodPairing F (fun σ y => Set.indicator {y : Space | y 2 < 0} (R.generatorField M.box m a σ) y) =
        R.lowerMoment M.box m a F) :
    GeneratorPairingMoments := by
  intro rowCount M R m tauMax hR F hFm hFp hF2 a
  rw [periodPairing_generator_halves M R m F hFm hF2 a, hup M R m tauMax hR F hFm hFp hF2 a,
    hlow M R m tauMax hR F hFm hFp hF2 a]

end Instance

end CertCell

end Breakdown
