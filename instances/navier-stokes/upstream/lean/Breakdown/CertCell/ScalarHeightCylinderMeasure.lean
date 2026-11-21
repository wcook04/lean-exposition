import Breakdown.CertCell.BridgeStatements
import Breakdown.FracCell.CylIntegral

open scoped ContDiff ENNReal
open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal.ScalarHeight

lemma axialRot_planePoint (φ r z : ℝ) :
    axialRot φ (planePoint (r, z)) = CellCert.CellAnalysis.cylPoint r φ z := by
  ext i
  fin_cases i <;> simp [axialRot, planePoint, CellCert.CellAnalysis.cylPoint, unitVector] <;> ring

lemma cylPoint_eq_toSpace (r θ z : ℝ) :
    CellCert.CellAnalysis.cylPoint r θ z =
      CellCert.Spectral.Internal.CylIntegral.toSpace (polarCoord.symm (r, θ), z) := by
  rw [polarCoord_symm_apply, CellCert.Spectral.Internal.CylIntegral.toSpace_apply]
  rfl

lemma continuous_cylPoint :
    Continuous (fun x : ℝ × ℝ × ℝ => CellCert.CellAnalysis.cylPoint x.1 x.2.1 x.2.2) := by
  have hs : ∀ (i : Fin 3) (a : ℝ), EuclideanSpace.single i a = a • unitVector i := by
    intro i a
    ext j
    by_cases h : j = i <;> simp [unitVector, h]
  unfold CellCert.CellAnalysis.cylPoint
  simp_rw [hs]
  fun_prop

lemma measurable_cylPoint_comp {α : Type*} [MeasurableSpace α] {a b c : α → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    Measurable fun x => CellCert.CellAnalysis.cylPoint (a x) (b x) (c x) := by
  show Measurable ((fun y : ℝ × ℝ × ℝ => CellCert.CellAnalysis.cylPoint y.1 y.2.1 y.2.2) ∘
    fun x => (a x, b x, c x))
  exact continuous_cylPoint.measurable.comp (ha.prodMk (hb.prodMk hc))

abbrev slabMeasure : Measure (ℝ × Space) := (volume.restrict (Icc (0 : ℝ) 1)).prod volume

abbrev boxMeasure : Measure ((ℝ × ℝ) × ℝ) :=
  ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Ioo (-Real.pi) Real.pi))).prod volume

abbrev cellMeasure : Measure (ℝ × ((ℝ × ℝ) × ℝ)) := (volume.restrict (Ioi (0 : ℝ))).prod boxMeasure

def cellMap (x : ℝ × ((ℝ × ℝ) × ℝ)) : ℝ × Space :=
  (x.2.1.1, CellCert.CellAnalysis.cylPoint x.1 x.2.1.2 x.2.2)

lemma measurable_cellMap : Measurable cellMap := by
  have h : Continuous cellMap := by
    refine continuous_fst.comp (continuous_fst.comp continuous_snd) |>.prodMk ?_
    exact continuous_cylPoint.comp ((continuous_fst).prodMk
      ((continuous_snd.comp (continuous_fst.comp continuous_snd)).prodMk (continuous_snd.comp continuous_snd)))
  exact h.measurable

lemma lintegral_cellMap (f : ℝ × Space → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, ENNReal.ofReal x.1 * f (cellMap x) ∂cellMeasure = ∫⁻ p, f p ∂slabMeasure := by
  have hc := continuous_cylPoint
  have hH : Measurable fun x : ℝ × ((ℝ × ℝ) × ℝ) => ENNReal.ofReal x.1 * f (cellMap x) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul (hf.comp measurable_cellMap)
  have hK : Measurable fun w : ((ℝ × ℝ) × ℝ) × ℝ =>
      ENNReal.ofReal w.1.1.1 * f (w.1.1.2, CellCert.CellAnalysis.cylPoint w.1.1.1 w.1.2 w.2) := by
    have h1 : Measurable fun w : ((ℝ × ℝ) × ℝ) × ℝ => w.1.1.1 := by fun_prop
    have h2 : Measurable fun w : ((ℝ × ℝ) × ℝ) × ℝ => w.1.1.2 := by fun_prop
    have h3 : Measurable fun w : ((ℝ × ℝ) × ℝ) × ℝ => w.1.2 := by fun_prop
    have h4 : Measurable fun w : ((ℝ × ℝ) × ℝ) × ℝ => w.2 := by fun_prop
    exact (ENNReal.measurable_ofReal.comp h1).mul (hf.comp (h2.prodMk (measurable_cylPoint_comp h1 h3 h4)))
  have step1 : ∫⁻ x, ENNReal.ofReal x.1 * f (cellMap x) ∂cellMeasure =
      ∫⁻ r in Ioi (0 : ℝ), ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ z,
        ENNReal.ofReal r * f (τ, CellCert.CellAnalysis.cylPoint r θ z) := by
    rw [cellMeasure, lintegral_prod _ hH.aemeasurable]
    refine lintegral_congr fun r => ?_
    have hr : Measurable fun u : (ℝ × ℝ) × ℝ => ENNReal.ofReal r * f (cellMap (r, u)) :=
      hH.comp measurable_prodMk_left
    rw [boxMeasure, lintegral_prod _ hr.aemeasurable, lintegral_prod _ hr.lintegral_prod_right'.aemeasurable]
    rfl
  have hG : Measurable fun p : ℝ × ℝ => ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ z,
      ENNReal.ofReal p.1 * f (p.2, CellCert.CellAnalysis.cylPoint p.1 θ z) :=
    hK.lintegral_prod_right'.lintegral_prod_right'
  rw [step1, lintegral_lintegral_swap hG.aemeasurable, slabMeasure, lintegral_prod _ hf.aemeasurable]
  refine lintegral_congr fun τ => ?_
  have hτ : Measurable fun y : Space => f (τ, y) := hf.comp measurable_prodMk_left
  have hw : Measurable fun w : (ℝ × ℝ) × ℝ =>
      f (τ, CellCert.Spectral.Internal.CylIntegral.toSpace w) :=
    hτ.comp CellCert.Spectral.Internal.CylIntegral.toSpace.measurable
  have hp : Measurable fun w : (ℝ × ℝ) × ℝ => f (τ, CellCert.CellAnalysis.cylPoint w.1.1 w.1.2 w.2) :=
    hτ.comp (measurable_cylPoint_comp (by fun_prop) (by fun_prop) (by fun_prop))
  symm
  calc ∫⁻ y, f (τ, y)
      = ∫⁻ w, f (τ, CellCert.Spectral.Internal.CylIntegral.toSpace w) :=
        (CellCert.Spectral.Internal.CylIntegral.toSpace_mp.lintegral_comp_emb
          CellCert.Spectral.Internal.CylIntegral.toSpace.measurableEmbedding _).symm
    _ = ∫⁻ a : ℝ × ℝ, ∫⁻ z, f (τ, CellCert.Spectral.Internal.CylIntegral.toSpace (a, z)) := by
        rw [Measure.volume_eq_prod, lintegral_prod _ hw.aemeasurable]
    _ = ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
          ∫⁻ z, f (τ, CellCert.Spectral.Internal.CylIntegral.toSpace (polarCoord.symm p, z)) :=
        (lintegral_comp_polarCoord_symm _).symm
    _ = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal p.1 * (∫⁻ z, f (τ, CellCert.CellAnalysis.cylPoint p.1 p.2 z))
          ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
        rw [Measure.prod_restrict, ← Measure.volume_eq_prod, polarCoord_target]
        simp_rw [cylPoint_eq_toSpace]
        rfl
    _ = _ := by
        have hm : Measurable fun p : ℝ × ℝ =>
            ENNReal.ofReal p.1 * ∫⁻ z, f (τ, CellCert.CellAnalysis.cylPoint p.1 p.2 z) :=
          (ENNReal.measurable_ofReal.comp measurable_fst).mul hp.lintegral_prod_right'
        rw [lintegral_prod _ hm.aemeasurable]
        refine lintegral_congr fun r => lintegral_congr fun θ => ?_
        exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm

lemma cellMap_measurePreserving :
    MeasurePreserving cellMap (cellMeasure.withDensity fun x => ENNReal.ofReal x.1) slabMeasure := by
  refine ⟨measurable_cellMap, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply measurable_cellMap hs, withDensity_apply _ (measurable_cellMap hs),
    ← lintegral_indicator_one₀ hs.nullMeasurableSet, ← lintegral_cellMap _ (measurable_one.indicator hs),
    ← lintegral_indicator (measurable_cellMap hs)]
  refine lintegral_congr fun x => ?_
  by_cases h : cellMap x ∈ s <;> simp [indicator, h]

lemma cell_ae_pos : ∀ᵐ x ∂cellMeasure, 0 < x.1 := by
  rw [cellMeasure, Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_fst)]
  exact (ae_restrict_mem measurableSet_Ioi).mono fun r hr => Eventually.of_forall fun _ => hr

lemma integral_slab_eq {F : ℝ × Space → ℂ} (hF : AEStronglyMeasurable F slabMeasure) :
    ∫ p, F p ∂slabMeasure = ∫ x, x.1 • F (cellMap x) ∂cellMeasure := by
  have hmp := cellMap_measurePreserving
  rw [← hmp.map_eq] at hF
  rw [← hmp.map_eq, integral_map measurable_cellMap.aemeasurable hF,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (cell_ae_pos.mono fun x hx => ?_)
  simp only [ENNReal.toReal_ofReal hx.le]

lemma integrable_cell {F : ℝ × Space → ℂ} (hF : Integrable F slabMeasure) :
    Integrable (fun x => x.1 • F (cellMap x)) cellMeasure := by
  have hmp := cellMap_measurePreserving
  rw [← hmp.map_eq] at hF
  have h1 : Integrable (F ∘ cellMap) (cellMeasure.withDensity fun x => ENNReal.ofReal x.1) :=
    (integrable_map_measure hF.1 measurable_cellMap.aemeasurable).1 hF
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h1
  refine h1.congr (cell_ae_pos.mono fun x hx => ?_)
  simp only [Function.comp_apply, ENNReal.toReal_ofReal hx.le]

lemma ae_integrable_slice {F : ℝ × Space → ℂ} (hF : Integrable F slabMeasure) :
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), Integrable (fun u => F (cellMap (r, u))) boxMeasure := by
  have h := (integrable_cell hF).prod_right_ae
  filter_upwards [h, ae_restrict_mem measurableSet_Ioi] with r hr hr0
  refine (hr.smul r⁻¹).congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.smul_apply, smul_smul, inv_mul_cancel₀ (ne_of_gt (show (0 : ℝ) < r from hr0)), one_smul]

lemma integral_slab_iter {F : ℝ × Space → ℂ} (hF : Integrable F slabMeasure) :
    ∫ p, F p ∂slabMeasure = ∫ r in Ioi (0 : ℝ), r • ∫ u, F (cellMap (r, u)) ∂boxMeasure := by
  rw [integral_slab_eq hF.1, cellMeasure, integral_prod _ (integrable_cell hF)]
  exact integral_congr_ae (Eventually.of_forall fun r => integral_smul _ _)

lemma integrable_slab_iter {F : ℝ × Space → ℂ} (hF : Integrable F slabMeasure) :
    Integrable (fun r => r • ∫ u, F (cellMap (r, u)) ∂boxMeasure) (volume.restrict (Ioi (0 : ℝ))) := by
  refine (integrable_cell hF).integral_prod_left.congr (Eventually.of_forall fun r => ?_)
  exact integral_smul _ _

lemma slab_eq_restrict : slabMeasure = (volume : Measure (ℝ × Space)).restrict (Icc 0 1 ×ˢ univ) := by
  rw [slabMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

lemma aestronglyMeasurable_slab {β : Type*} [TopologicalSpace β] {f : ℝ × Space → β}
    (hf : AEStronglyMeasurable f volume) : AEStronglyMeasurable f slabMeasure := by
  rw [slab_eq_restrict]
  exact hf.restrict

lemma integrable_slab_mul {q : ℝ → Space → ℝ} {dq : ℝ → Space → Space}
    (hq : AEStronglyMeasurable (fun z : ℝ × Space => q z.1 z.2) volume)
    (hdq : AEStronglyMeasurable (fun z : ℝ × Space => dq z.1 z.2) volume)
    (hL : ∀ R : ℝ, periodLIntegral (fun σ y => if ‖y‖ ≤ R then q σ y ^ 2 + ‖dq σ y‖ ^ 2 else 0) < ⊤)
    {c d : ℝ × Space → ℂ} (hc : AEStronglyMeasurable c slabMeasure) (hd : AEStronglyMeasurable d slabMeasure)
    {C R : ℝ} (hcC : ∀ p, ‖c p‖ ≤ C) (hdC : ∀ p, ‖d p‖ ≤ C)
    (hcR : ∀ p : ℝ × Space, R < ‖p.2‖ → c p = 0) (hdR : ∀ p : ℝ × Space, R < ‖p.2‖ → d p = 0) :
    Integrable (fun p => c p * (q p.1 p.2 : ℂ) + d p * (dq p.1 p.2 2 : ℂ)) slabMeasure := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hcC (0, 0))
  have hS : MeasurableSet {p : ℝ × Space | ‖p.2‖ ≤ R} := measurableSet_le (by fun_prop) measurable_const
  have h1 := aestronglyMeasurable_slab hq
  have h2 := aestronglyMeasurable_slab hdq
  have h3 : AEStronglyMeasurable (fun p : ℝ × Space => dq p.1 p.2 2) slabMeasure :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable h2
  set G : ℝ × Space → ℝ := {p : ℝ × Space | ‖p.2‖ ≤ R}.indicator
    (fun p => 1 + (q p.1 p.2 ^ 2 + ‖dq p.1 p.2‖ ^ 2)) with hG
  have hGm : AEStronglyMeasurable G slabMeasure :=
    (aestronglyMeasurable_const.add ((h1.pow 2).add (h2.norm.pow 2))).indicator hS
  have hG0 : ∀ p, 0 ≤ G p := fun p => by
    rw [hG]
    exact indicator_nonneg (fun p _ => by positivity) p
  have hGi : Integrable G slabMeasure := by
    refine ⟨hGm, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hG0)).2 ?_⟩
    have hle : ∀ p, ENNReal.ofReal (G p) ≤ {p : ℝ × Space | ‖p.2‖ ≤ R}.indicator 1 p +
        ENNReal.ofReal (if ‖p.2‖ ≤ R then q p.1 p.2 ^ 2 + ‖dq p.1 p.2‖ ^ 2 else 0) := by
      intro p
      by_cases hp : ‖p.2‖ ≤ R
      · simp only [hG, indicator_of_mem (show p ∈ {p : ℝ × Space | ‖p.2‖ ≤ R} from hp), if_pos hp,
          Pi.one_apply]
        rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]
      · simp [hG, hp]
    refine (lintegral_mono hle).trans_lt ?_
    rw [lintegral_add_left (measurable_one.indicator hS), lintegral_indicator_one₀ hS.nullMeasurableSet]
    refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
    · refine (measure_mono (show {p : ℝ × Space | ‖p.2‖ ≤ R} ⊆ univ ×ˢ Metric.closedBall 0 R from
        fun p hp => ⟨trivial, by simpa using hp⟩)).trans_lt ?_
      rw [slabMeasure, Measure.prod_prod, Measure.restrict_apply MeasurableSet.univ, univ_inter,
        Real.volume_Icc]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
    · have hm : AEMeasurable (fun p : ℝ × Space =>
          ENNReal.ofReal (if ‖p.2‖ ≤ R then q p.1 p.2 ^ 2 + ‖dq p.1 p.2‖ ^ 2 else 0)) slabMeasure := by
        have : (fun p : ℝ × Space => if ‖p.2‖ ≤ R then q p.1 p.2 ^ 2 + ‖dq p.1 p.2‖ ^ 2 else 0) =
            {p : ℝ × Space | ‖p.2‖ ≤ R}.indicator (fun p => q p.1 p.2 ^ 2 + ‖dq p.1 p.2‖ ^ 2) := by
          funext p
          by_cases hp : ‖p.2‖ ≤ R <;> simp [hp]
        show AEMeasurable (ENNReal.ofReal ∘ fun p : ℝ × Space =>
          if ‖p.2‖ ≤ R then q p.1 p.2 ^ 2 + ‖dq p.1 p.2‖ ^ 2 else 0) slabMeasure
        rw [this]
        exact ENNReal.measurable_ofReal.comp_aemeasurable
          (((h1.pow 2).add (h2.norm.pow 2)).indicator hS).aemeasurable
      rw [slabMeasure, lintegral_prod _ hm]
      exact hL R
  refine (hGi.const_mul (2 * C)).mono' ?_ (Eventually.of_forall fun p => ?_)
  · exact (hc.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable h1)).add
      (hd.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable h3))
  · by_cases hp : ‖p.2‖ ≤ R
    · have hGp : G p = 1 + (q p.1 p.2 ^ 2 + ‖dq p.1 p.2‖ ^ 2) := by
        rw [hG]
        exact indicator_of_mem (show p ∈ {p : ℝ × Space | ‖p.2‖ ≤ R} from hp) _
      have e1 : |q p.1 p.2| ≤ G p := by
        rw [hGp]
        nlinarith [abs_nonneg (q p.1 p.2), sq_abs (q p.1 p.2), norm_nonneg (dq p.1 p.2)]
      have e2 : |dq p.1 p.2 2| ≤ G p := by
        have := PiLp.norm_apply_le (dq p.1 p.2) 2
        rw [Real.norm_eq_abs] at this
        rw [hGp]
        nlinarith [norm_nonneg (dq p.1 p.2), sq_nonneg (q p.1 p.2)]
      calc ‖c p * (q p.1 p.2 : ℂ) + d p * (dq p.1 p.2 2 : ℂ)‖
          ≤ ‖c p‖ * |q p.1 p.2| + ‖d p‖ * |dq p.1 p.2 2| := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ C * G p + C * G p := by
            gcongr
            · exact hcC p
            · exact hdC p
        _ = 2 * C * G p := by ring
    · rw [hcR p (not_le.mp hp), hdR p (not_le.mp hp)]
      simp only [zero_mul, add_zero, norm_zero]
      exact mul_nonneg (by positivity) (hG0 p)

def planeRadius (y : Space) : ℝ := Real.sqrt (y 0 ^ 2 + y 1 ^ 2)

def turnSign (k : ℤ) : ℂ := if 0 ≤ k then -Complex.I else Complex.I

def turnPoly (k : ℤ) (y : Space) : ℂ := ((y 0 : ℂ) + turnSign k * (y 1 : ℂ)) ^ k.natAbs

lemma contDiff_coord (i : Fin 3) : ContDiff ℝ ∞ (fun y : Space => y i) :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff

lemma continuous_planeRadius : Continuous planeRadius := by
  unfold planeRadius
  exact ((((contDiff_coord 0).continuous.pow 2).add ((contDiff_coord 1).continuous.pow 2))).sqrt

lemma contDiff_turnPoly (k : ℤ) : ContDiff ℝ ∞ (turnPoly k) := by
  unfold turnPoly
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_coord 0)).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_coord 1)))).pow _

lemma cylPoint_apply_zero (r θ z : ℝ) : CellCert.CellAnalysis.cylPoint r θ z 0 = r * Real.cos θ := by
  simp [CellCert.CellAnalysis.cylPoint]

lemma cylPoint_apply_one (r θ z : ℝ) : CellCert.CellAnalysis.cylPoint r θ z 1 = r * Real.sin θ := by
  simp [CellCert.CellAnalysis.cylPoint]

lemma cylPoint_apply_two (r θ z : ℝ) : CellCert.CellAnalysis.cylPoint r θ z 2 = z := by
  simp [CellCert.CellAnalysis.cylPoint]

lemma planeRadius_cylPoint {r : ℝ} (hr : 0 ≤ r) (θ z : ℝ) :
    planeRadius (CellCert.CellAnalysis.cylPoint r θ z) = r := by
  rw [planeRadius, cylPoint_apply_zero, cylPoint_apply_one]
  have : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    have := Real.cos_sq_add_sin_sq θ
    calc (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      _ = r ^ 2 := by rw [this, mul_one]
  rw [this, Real.sqrt_sq hr]

lemma turnPoly_cylPoint (k : ℤ) (r θ z : ℝ) :
    turnPoly k (CellCert.CellAnalysis.cylPoint r θ z) =
      (r : ℂ) ^ k.natAbs * Complex.exp (-(((k * θ : ℝ) : ℂ) * Complex.I)) := by
  rw [turnPoly, cylPoint_apply_zero, cylPoint_apply_one, turnSign]
  by_cases hk : 0 ≤ k
  · rw [if_pos hk]
    have e : ((r * Real.cos θ : ℝ) : ℂ) + -Complex.I * ((r * Real.sin θ : ℝ) : ℂ) =
        (r : ℂ) * Complex.exp (-((θ : ℂ) * Complex.I)) := by
      rw [show -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    rw [e, mul_pow, ← Complex.exp_nat_mul]
    congr 2
    have : ((k.natAbs : ℕ) : ℂ) = (k : ℂ) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg hk]
    rw [this]
    push_cast
    ring
  · rw [if_neg hk]
    have e : ((r * Real.cos θ : ℝ) : ℂ) + Complex.I * ((r * Real.sin θ : ℝ) : ℂ) =
        (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast
      ring
    rw [e, mul_pow, ← Complex.exp_nat_mul]
    congr 2
    have : ((k.natAbs : ℕ) : ℂ) = -(k : ℂ) := by
      rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos (le_of_lt (not_le.mp hk))]
      push_cast
      ring
    rw [this]
    push_cast
    ring

lemma abs_coord_le (y : Space) (i : Fin 3) : |y i| ≤ ‖y‖ := by
  have := PiLp.norm_apply_le y i
  rwa [Real.norm_eq_abs] at this

lemma norm_turnPoly_le (k : ℤ) (y : Space) : ‖turnPoly k y‖ ≤ (2 * ‖y‖) ^ k.natAbs := by
  rw [turnPoly, norm_pow]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
  have hs : ‖turnSign k‖ = 1 := by
    unfold turnSign
    split_ifs <;> simp
  calc ‖(y 0 : ℂ) + turnSign k * (y 1 : ℂ)‖ ≤ ‖(y 0 : ℂ)‖ + ‖turnSign k‖ * ‖(y 1 : ℂ)‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul]
    _ ≤ ‖y‖ + 1 * ‖y‖ := by
        rw [hs, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        gcongr
        · exact abs_coord_le y 0
        · exact abs_coord_le y 1
    _ = 2 * ‖y‖ := by ring

lemma norm_le_planeRadius_add (y : Space) : ‖y‖ ≤ planeRadius y + |y 2| := by
  rw [EuclideanSpace.norm_eq, planeRadius, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  have ha : 0 ≤ y 0 ^ 2 + y 1 ^ 2 := by positivity
  calc Real.sqrt (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2)
      ≤ Real.sqrt ((Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + |y 2|) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg (y 0 ^ 2 + y 1 ^ 2), abs_nonneg (y 2), sq_abs (y 2)]
    _ = Real.sqrt (y 0 ^ 2 + y 1 ^ 2) + |y 2| := Real.sqrt_sq (by positivity)

lemma shift_apply (y : Space) (t : ℝ) (i : Fin 3) :
    (y + t • unitVector 2) i = y i + if i = 2 then t else 0 := by
  fin_cases i <;> simp [unitVector]

lemma planeRadius_shift (y : Space) (t : ℝ) : planeRadius (y + t • unitVector 2) = planeRadius y := by
  simp only [planeRadius, shift_apply]
  simp

lemma turnPoly_shift (k : ℤ) (y : Space) (t : ℝ) : turnPoly k (y + t • unitVector 2) = turnPoly k y := by
  simp only [turnPoly, shift_apply]
  simp

end Internal.ScalarHeight

end Bridge

end CertCell

end Breakdown
