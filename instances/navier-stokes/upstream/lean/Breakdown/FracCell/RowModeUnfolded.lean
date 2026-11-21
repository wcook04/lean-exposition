import Breakdown.FracCell.SharpRowIdentity
import Breakdown.FracCell.LayoutRowValueModes
import Breakdown.FracCell.LayoutRowValueVolume
import Breakdown.FracCell.SharpYChargeRegular
import Breakdown.FracCell.EnergyHeightProj

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace CellScalars

def rowModeDensity {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) {slots : ℕ}
    (R : CellRows N slots k) (x : FieldTuple k) (a : Fin N) (n : ℤ) (p : ℝ × ℝ) : ℂ :=
  ((K.lineWeight p.1 : ℝ) : ℂ) *
    (entryPairing (fun i q => gradMode c.order n x.2.1 i q p
        - (if n ∈ S.resolved then K.lowStrain c.order n S.degHigh x.2.1 i q p else 0))
        (rowCouplingStrain c K R a n p)
      + vecPair (fun i => modeVec c.order n x.1 p.1 p.2 i
        - (if n ∈ S.resolved then K.lowVelocity c.order n S.degHigh x.1 i p else 0))
        (rowCouplingVelocity c K R a n p))

def circleRowPair {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)
    (a : Fin N) (p : ℝ × ℝ) : ℝ :=
  1 / (2 * Real.pi) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
    inner ℝ (highCouplingField c K S x.1 x.2.1 (cylPoint p.1 θ p.2)) (c.row a (cylPoint p.1 θ p.2))

end CellScalars

def RowCircleSeriesStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ a ∈ R.rowSet,
      ∀ᵐ p ∂(volume.restrict K.rect),
        HasSum (fun n : ℤ => (CellScalars.rowModeDensity c K S R x a n p).re)
          (p.1 * CellScalars.circleRowPair c K S x a p)

def RowSeriesDominationStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ a ∈ R.rowSet,
      Summable (fun n : ℤ => ∫ p in K.rect, ‖CellScalars.rowModeDensity c K S R x a n p‖)

def RowCouplingTailStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ a ∈ R.rowSet,
      Summable (fun n : ℤ => ∫ p in K.rect, K.lineWeight p.1 *
        (sumSq (CellScalars.rowCouplingStrain c K R a n p) + vecSq (CellScalars.rowCouplingVelocity c K R a n p)))

namespace RowModeUnfolded.Internal

open SharpRowIdentity.Internal

theorem low_sq (K : CellBox) (B : CellBases) (hK : IsCellBox K) (hB : IsCellBases K B)
    (h3 : ProjCoefStatement) (F : ℝ × ℝ → ℂ) (hF : IsWeightedSquare K F) (d : ℕ) (b : Prop) [Decidable b] :
    IsWeightedSquare K (fun p => F p - (if b then K.proj d d F p else 0)) := by
  by_cases hb : b
  · simp only [if_pos hb]
    exact (h3 K B hK hB F hF d).1
  · simp only [if_neg hb, sub_zero]
    exact hF


theorem coupling_mirror_pt {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)
    {y : Space} (hy : cylHeight y ≠ 0) (hv : x.1 (mirror y) = mirror (x.1 y))
    (hG : ∀ u, x.2.1 (mirror y) u = mirror (x.2.1 y (mirror u)))
    (hV : c.modelVelocity (mirror y) = mirror (c.modelVelocity y))
    (hW : c.modelCurl (mirror y) = -mirror (c.modelCurl y)) :
    CellScalars.highCouplingField c K S x.1 x.2.1 (mirror y)
      = mirror (CellScalars.highCouplingField c K S x.1 x.2.1 y) := by
  have hM : ∀ u, (x.2.1 (mirror y) - CellScalars.lowGradField c K S x.2.1 (mirror y)) u
      = mirror ((x.2.1 y - CellScalars.lowGradField c K S x.2.1 y) (mirror u)) := by
    intro u
    rw [sub_apply, sub_apply, hG,
      FracInternal.LayoutRowVolume.lowG_mirror c K S x.2.1 hy, FracInternal.LayoutRowVolume.mirror_sub]
  unfold CellScalars.highCouplingField
  rw [FracInternal.LayoutRowVolume.curl_conj hM, hV, hW, hv, FracInternal.LayoutRowVolume.lowV_mirror c K S x.1 hy,
    ← FracInternal.LayoutRowVolume.mirror_sub, FracInternal.LayoutRowVolume.cross_mirror_neg,
    FracInternal.LayoutRowVolume.cross_mirror_neg, FracInternal.LayoutRowVolume.mirror_add]

theorem coupling_pair_mirror {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {x : FieldTuple k} (a : Fin N)
    (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R) (hx : IsAdmissible c x) :
    ∀ᵐ y ∂volume, y ∈ K.solid →
      inner ℝ (CellScalars.highCouplingField c K S x.1 x.2.1 (mirror y)) (c.row a (mirror y))
        = inner ℝ (CellScalars.highCouplingField c K S x.1 x.2.1 y) (c.row a y) := by
  have hz : ∀ᵐ y ∂(volume : Measure Space), y ∉ {y : Space | y 2 = 0} :=
    measure_eq_zero_iff_ae_notMem.1 FracInternal.CellDensityModesSolid.plane_null
  filter_upwards [gradientMirror c.order x.1 x.2.1 x.2.2.1 hx.1,
    hx.1.symmetric.2, (hc.base.row_class a).2, hz] with y hGH hv hr hy0 hy
  have hy' : cylHeight y ≠ 0 := hy0
  obtain ⟨hV, hW, -⟩ := hD.model_mirror y hy hy'
  rw [coupling_mirror_pt c K S x hy' hv hGH.1 hV hW, hr, FracInternal.LayoutRowModes.mirror_inner]

theorem op_cont (a b : Fin 3) :
    Continuous (fun θ => (innerSL ℝ (frameUnit θ b)).smulRight (frameUnit θ a)) := by
  have hb : Continuous (fun θ => frameUnit θ b) := LowEntry.Internal.unit_cont b
  have ha : Continuous (fun θ => frameUnit θ a) := LowEntry.Internal.unit_cont a
  exact isBoundedBilinearMap_smulRight.continuous.comp (((innerSL ℝ).continuous.comp hb).prodMk ha)

theorem unit_nm (θ : ℝ) (a : Fin 3) : ‖frameUnit θ a‖ ≤ 1 := LowEntry.Internal.unit_norm θ a

theorem angle_m : Measurable cylAngle := by
  unfold cylAngle
  exact Complex.measurable_arg.comp (by fun_prop)

theorem sign_m (a : Fin 3) : Measurable (fun y => CellScalars.mirrorSign y a) := by
  unfold CellScalars.mirrorSign
  refine Measurable.ite ?_ measurable_const measurable_const
  have hc : Continuous cylHeight := by unfold cylHeight; fun_prop
  exact (measurableSet_lt hc.measurable measurable_const).inter (MeasurableSet.const _)

theorem sign_bd (y : Space) (a : Fin 3) : |CellScalars.mirrorSign y a| = 1 := by
  unfold CellScalars.mirrorSign
  split_ifs <;> simp

theorem rho_c : Continuous (fun y : Space => ((cylRadius y, |cylHeight y|) : ℝ × ℝ)) := by
  unfold cylRadius cylHeight
  fun_prop

theorem wsum_m (m : ℕ) (s : Finset ℤ) (F : ℤ → ℝ × ℝ → ℂ) (hF : ∀ n, Continuous (F n)) :
    Measurable (fun y => (∑ n ∈ s, F n (cylRadius y, |cylHeight y|) *
      Complex.exp ((azimuth m n * cylAngle y : ℝ) * Complex.I)).re) := by
  refine Complex.measurable_re.comp (Finset.measurable_sum _ fun n _ => ?_)
  exact ((hF n).comp rho_c).measurable.mul
    (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp (measurable_const.mul angle_m)).mul
      measurable_const))

theorem wsum_bd (K : CellBox) (m : ℕ) (s : Finset ℤ) (F : ℤ → ℝ × ℝ → ℂ) (hF : ∀ n, Continuous (F n)) :
    ∃ C, ∀ y ∈ K.solid, |(∑ n ∈ s, F n (cylRadius y, |cylHeight y|) *
      Complex.exp ((azimuth m n * cylAngle y : ℝ) * Complex.I)).re| ≤ C := by
  have hc : Continuous (fun p => ∑ n ∈ s, ‖F n p‖) := continuous_finsetSum _ fun n _ => (hF n).norm
  obtain ⟨C, hC⟩ := (LowEntry.Internal.rect_compact K).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun y hy => ?_⟩
  have hm : ((cylRadius y, |cylHeight y|) : ℝ × ℝ) ∈ K.rect := ⟨⟨hy.1, hy.2.1⟩, ⟨hy.2.2.1, hy.2.2.2⟩⟩
  have h1 := hC _ hm
  rw [Real.norm_eq_abs] at h1
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans (le_trans (le_of_eq ?_) ((le_abs_self _).trans h1)))
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem op_bd (θ : ℝ) (M : Fin 3 → Fin 3 → ℝ) : ‖cartOpOfFrame θ M‖ ≤ ∑ a : Fin 3, ∑ b : Fin 3, |M a b| := by
  unfold cartOpOfFrame
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun b _ => ?_))
  rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
  have h1 := unit_nm θ a
  have h2 := unit_nm θ b
  have h3 : ‖frameUnit θ b‖ * ‖frameUnit θ a‖ ≤ 1 := by
    nlinarith [norm_nonneg (frameUnit θ a), norm_nonneg (frameUnit θ b)]
  exact mul_le_of_le_one_right (abs_nonneg _) h3

theorem vec_bd (θ : ℝ) (w : Fin 3 → ℝ) : ‖cartOfFrame θ w‖ ≤ ∑ a : Fin 3, |w a| := by
  unfold cartOfFrame
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (unit_nm θ a)

theorem proj_c (K : CellBox) (d d' : ℕ) (F : ℝ × ℝ → ℂ) : Continuous (K.proj d d' F) := by
  unfold CellBox.proj
  split_ifs with h
  · exact LowEntry.Internal.poly_cont h.choose_spec.1
  · exact continuous_const

theorem lowG_props {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)
    (G : Space → (Space →L[ℝ] Space)) :
    AEStronglyMeasurable (CellScalars.lowGradField c K S G) volume ∧
      ∃ C, ∀ y ∈ K.solid, ‖CellScalars.lowGradField c K S G y‖ ≤ C := by
  have hF : ∀ (a b : Fin 3) (n : ℤ), Continuous (K.lowStrain c.order n S.degHigh G a b) := fun a b n =>
    proj_c K _ _ _
  constructor
  · refine Measurable.aestronglyMeasurable ?_
    unfold CellScalars.lowGradField cartOpOfFrame
    exact Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ =>
      (((sign_m a).mul (sign_m b)).mul (wsum_m c.order S.resolved _ (fun n => hF a b n))).smul
        ((op_cont a b).measurable.comp angle_m)
  · choose C hC using fun ab : Fin 3 × Fin 3 =>
      wsum_bd K c.order S.resolved (fun n => K.lowStrain c.order n S.degHigh G ab.1 ab.2) (fun n => hF ab.1 ab.2 n)
    refine ⟨∑ a : Fin 3, ∑ b : Fin 3, C (a, b), fun y hy => ?_⟩
    unfold CellScalars.lowGradField
    refine (op_bd _ _).trans (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_)
    rw [abs_mul, abs_mul, sign_bd, sign_bd, one_mul, one_mul]
    exact hC (a, b) y hy

theorem lowV_props {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (v : Space → Space) :
    AEStronglyMeasurable (CellScalars.lowVelocityField c K S v) volume ∧
      ∃ C, ∀ y ∈ K.solid, ‖CellScalars.lowVelocityField c K S v y‖ ≤ C := by
  have hF : ∀ (a : Fin 3) (n : ℤ), Continuous (K.lowVelocity c.order n S.degHigh v a) := fun a n =>
    proj_c K _ _ _
  constructor
  · refine Measurable.aestronglyMeasurable ?_
    unfold CellScalars.lowVelocityField cartOfFrame
    exact Finset.measurable_sum _ fun a _ =>
      ((sign_m a).mul (wsum_m c.order S.resolved _ (fun n => hF a n))).smul
        ((LowEntry.Internal.unit_cont a).measurable.comp angle_m)
  · choose C hC using fun a : Fin 3 =>
      wsum_bd K c.order S.resolved (fun n => K.lowVelocity c.order n S.degHigh v a) (fun n => hF a n)
    refine ⟨∑ a : Fin 3, C a, fun y hy => ?_⟩
    unfold CellScalars.lowVelocityField
    refine (vec_bd _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [abs_mul, sign_bd, one_mul]
    exact hC a y hy

theorem pair_integrable {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {x : FieldTuple k} {a : Fin N}
    (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet) :
    Integrable (fun y => inner ℝ (CellScalars.highCouplingField c K S x.1 x.2.1 y) (c.row a y)) := by
  have hTm : MeasurableSet K.solid := FracInternal.CellDensityModesSolid.solid_closed K
  have hTf : volume K.solid < ⊤ := (hc.cellRegion_bounded.subset hD.solid_in_region).measure_lt_top
  have : IsFiniteMeasure (volume.restrict K.solid) := isFiniteMeasure_restrict.mpr hTf.ne
  obtain ⟨mLG, BG, hBG⟩ := lowG_props c K S x.2.1
  obtain ⟨mLV, BV, hBV⟩ := lowV_props c K S x.1
  obtain ⟨CM, hCM⟩ := hc.model_bounded
  have hS := hx.1
  have hrow : MemLp (c.row a) 2 volume := hc.base.row_two a
  have hGL : MemLp x.2.1 2 volume := ModelFieldInternal.memLp_grad hS.measurable_gradient hS.gradient_two
  have hv2 : MemLp x.1 2 (volume.restrict K.solid) :=
    (hS.velocity_six.restrict K.solid).mono_exponent (by norm_num)
  have hHm : AEStronglyMeasurable (fun y => CellScalars.highCouplingField c K S x.1 x.2.1 y) volume :=
    (ModelFieldInternal.aesm_cross (ModelFieldInternal.aesm_curl (hS.measurable_gradient.sub mLG))
      hc.model_measurable.1).add
      (ModelFieldInternal.aesm_cross hc.model_measurable.2.1 (hS.measurable_velocity.sub mLV))
  have i1 : Integrable (fun y => ‖x.2.1 y‖ * ‖c.row a y‖) (volume.restrict K.solid) :=
    (hGL.norm.restrict K.solid).integrable_mul (hrow.norm.restrict K.solid)
  have i2 : Integrable (fun y => ‖x.1 y‖ * ‖c.row a y‖) (volume.restrict K.solid) :=
    hv2.norm.integrable_mul (hrow.norm.restrict K.solid)
  have i3 : Integrable (fun y => ‖c.row a y‖) (volume.restrict K.solid) :=
    (hrow.norm.restrict K.solid).integrable (by norm_num)
  have hbd : IntegrableOn (fun y => 27 * |CM| * (‖x.2.1 y‖ * ‖c.row a y‖) + |CM| * (‖x.1 y‖ * ‖c.row a y‖)
      + (27 * |CM| * |BG| + |CM| * |BV|) * ‖c.row a y‖) K.solid :=
    ((i1.const_mul _).add (i2.const_mul _)).add (i3.const_mul _)
  have hon : IntegrableOn (fun y => inner ℝ (CellScalars.highCouplingField c K S x.1 x.2.1 y) (c.row a y))
      K.solid := by
    refine hbd.mono' (hHm.inner hrow.aestronglyMeasurable).restrict ?_
    refine (ae_restrict_iff' hTm).2 (ae_of_all _ fun y hy => ?_)
    obtain ⟨hV, hW, -⟩ := hCM y (hD.solid_in_region hy)
    have e2 : ‖x.1 y - CellScalars.lowVelocityField c K S x.1 y‖ ≤ ‖x.1 y‖ + |BV| := by
      linarith [norm_sub_le (x.1 y) (CellScalars.lowVelocityField c K S x.1 y), hBV y hy, le_abs_self BV]
    have e1 : ‖x.2.1 y - CellScalars.lowGradField c K S x.2.1 y‖ ≤ ‖x.2.1 y‖ + |BG| := by
      linarith [norm_sub_le (x.2.1 y) (CellScalars.lowGradField c K S x.2.1 y), hBG y hy, le_abs_self BG]
    have hV' : ‖c.modelVelocity y‖ ≤ |CM| := hV.trans (le_abs_self _)
    have hW' : ‖c.modelCurl y‖ ≤ |CM| := hW.trans (le_abs_self _)
    have e3 : ‖crossVec (curlOf (x.2.1 y - CellScalars.lowGradField c K S x.2.1 y)) (c.modelVelocity y)‖
        ≤ 27 * (‖x.2.1 y‖ + |BG|) * |CM| :=
      (ModelFieldInternal.cross_le _ _).trans (mul_le_mul ((ModelFieldInternal.curl_le _).trans (by linarith))
        hV' (norm_nonneg _) (by positivity))
    have e4 : ‖crossVec (c.modelCurl y) (x.1 y - CellScalars.lowVelocityField c K S x.1 y)‖
        ≤ |CM| * (‖x.1 y‖ + |BV|) :=
      (ModelFieldInternal.cross_le _ _).trans (mul_le_mul hW' e2 (norm_nonneg _) (abs_nonneg _))
    have eH : ‖CellScalars.highCouplingField c K S x.1 x.2.1 y‖
        ≤ 27 * (‖x.2.1 y‖ + |BG|) * |CM| + |CM| * (‖x.1 y‖ + |BV|) := by
      unfold CellScalars.highCouplingField
      exact (norm_add_le _ _).trans (add_le_add e3 e4)
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    have hr := norm_nonneg (c.row a y)
    calc ‖CellScalars.highCouplingField c K S x.1 x.2.1 y‖ * ‖c.row a y‖
        ≤ (27 * (‖x.2.1 y‖ + |BG|) * |CM| + |CM| * (‖x.1 y‖ + |BV|)) * ‖c.row a y‖ :=
          mul_le_mul_of_nonneg_right eH hr
      _ = _ := by ring
  refine hon.integrable_of_forall_notMem_eq_zero fun y hy => ?_
  rw [hD.rows_in_cell a ha y hy, inner_zero_right]

theorem amgm (w x y : ℝ) (hw : 0 ≤ w) : w * (x * y) ≤ (1 / 2) * (w * x ^ 2) + (1 / 2) * (w * y ^ 2) := by
  nlinarith [mul_nonneg hw (sq_nonneg (x - y))]

theorem entry_bd (s t : Fin 3 → Fin 3 → ℂ) : ‖entryPairing s t‖ ≤ (1 / 2) * sumSq s + (1 / 2) * sumSq t := by
  unfold entryPairing sumSq
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [norm_mul, Complex.norm_conj]
  nlinarith [sq_nonneg (‖s i q‖ - ‖t i q‖)]

theorem vec_bd2 (s t : Fin 3 → ℂ) : ‖CellScalars.vecPair s t‖ ≤ (1 / 2) * vecSq s + (1 / 2) * vecSq t := by
  unfold CellScalars.vecPair vecSq
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, Complex.norm_conj]
  nlinarith [sq_nonneg (‖s i‖ - ‖t i‖)]

theorem density_bd {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) {slots : ℕ}
    (R : CellRows N slots k) (x : FieldTuple k) (a : Fin N) (n : ℤ) (p : ℝ × ℝ) (hw : 0 ≤ K.lineWeight p.1) :
    ‖CellScalars.rowModeDensity c K S R x a n p‖ ≤
      (1 / 2) * (K.lineWeight p.1 * (sumSq (fun i q => gradMode c.order n x.2.1 i q p
          - (if n ∈ S.resolved then K.lowStrain c.order n S.degHigh x.2.1 i q p else 0))
        + vecSq (fun i => modeVec c.order n x.1 p.1 p.2 i
          - (if n ∈ S.resolved then K.lowVelocity c.order n S.degHigh x.1 i p else 0))))
      + (1 / 2) * (K.lineWeight p.1 *
        (sumSq (CellScalars.rowCouplingStrain c K R a n p) + vecSq (CellScalars.rowCouplingVelocity c K R a n p))) := by
  unfold CellScalars.rowModeDensity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
  have h1 := entry_bd (fun i q => gradMode c.order n x.2.1 i q p
          - (if n ∈ S.resolved then K.lowStrain c.order n S.degHigh x.2.1 i q p else 0))
    (CellScalars.rowCouplingStrain c K R a n p)
  have h2 := vec_bd2 (fun i => modeVec c.order n x.1 p.1 p.2 i
          - (if n ∈ S.resolved then K.lowVelocity c.order n S.degHigh x.1 i p else 0))
    (CellScalars.rowCouplingVelocity c K R a n p)
  have h3 := norm_add_le (entryPairing (fun i q => gradMode c.order n x.2.1 i q p
          - (if n ∈ S.resolved then K.lowStrain c.order n S.degHigh x.2.1 i q p else 0))
    (CellScalars.rowCouplingStrain c K R a n p)) (CellScalars.vecPair (fun i => modeVec c.order n x.1 p.1 p.2 i
          - (if n ∈ S.resolved then K.lowVelocity c.order n S.degHigh x.1 i p else 0))
    (CellScalars.rowCouplingVelocity c K R a n p))
  have h4 := mul_le_mul_of_nonneg_left (h3.trans (add_le_add h1 h2)) hw
  nlinarith [h4]

theorem sq_int {K : CellBox} {F : Fin 3 → Fin 3 → ℝ × ℝ → ℂ} (hF : ∀ i q, IsWeightedSquare K (F i q)) :
    IntegrableOn (fun p => K.lineWeight p.1 * sumSq (fun i q => F i q p)) K.rect := by
  have h := integrable_finsetSum (Finset.univ : Finset (Fin 3)) fun i _ =>
    integrable_finsetSum (Finset.univ : Finset (Fin 3)) fun q _ => (hF i q).2
  refine h.congr (ae_of_all _ fun p => ?_)
  simp only [sumSq, Finset.mul_sum]

theorem vsq_int {K : CellBox} {F : Fin 3 → ℝ × ℝ → ℂ} (hF : ∀ i, IsWeightedSquare K (F i)) :
    IntegrableOn (fun p => K.lineWeight p.1 * vecSq (fun i => F i p)) K.rect := by
  have h := integrable_finsetSum (Finset.univ : Finset (Fin 3)) fun i _ => (hF i).2
  refine h.congr (ae_of_all _ fun p => ?_)
  simp only [vecSq, Finset.mul_sum]

theorem lw_le (K : CellBox) (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) :
    K.lineWeight p.1 ≤ (if K.r₁ = 0 then 1 else 1 / K.r₁) * p.1 := by
  unfold CellBox.lineWeight
  split_ifs with h
  · linarith
  · have h1 : 0 < K.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h)
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ h1, one_mul]
    exact hp.1.1

theorem field_tail {k : ℕ} (K : CellBox) (hK : IsCellBox K) (m : ℕ) (hm : 0 < m) {x : FieldTuple k}
    (hs : IsSecondOrderField m x.1 x.2.1 x.2.2.1) :
    Summable (fun n : ℤ => ∫ p in K.rect, K.lineWeight p.1 *
      (sumSq (fun i q => gradMode m n x.2.1 i q p) + vecSq (modeVec m n x.1 p.1 p.2))) := by
  obtain ⟨hi, hsum⟩ := SharpYChargeRegular.Internal.tot_sum K hK m hm hs
  have hκ : 0 ≤ (if K.r₁ = 0 then (1 : ℝ) else 1 / K.r₁) := by
    split_ifs
    · norm_num
    · exact div_nonneg zero_le_one hK.r_order.1
  refine (hsum.mul_left (if K.r₁ = 0 then (1 : ℝ) else 1 / K.r₁)).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · refine setIntegral_nonneg (LowEntry.Internal.rect_meas K) fun p hp => ?_
    have := SharpRowIdentity.Internal.lw_nonneg_rect K hK hp
    have h1 : 0 ≤ sumSq (fun i q => gradMode m n x.2.1 i q p) := by unfold sumSq; positivity
    have h2 : 0 ≤ vecSq (modeVec m n x.1 p.1 p.2) := by unfold vecSq; positivity
    positivity
  · rw [← integral_const_mul]
    refine integral_mono_of_nonneg ?_ ((hi n).const_mul _) ?_
    · refine (ae_restrict_iff' (LowEntry.Internal.rect_meas K)).2 (ae_of_all _ fun p hp => ?_)
      have := SharpRowIdentity.Internal.lw_nonneg_rect K hK hp
      have h1 : 0 ≤ sumSq (fun i q => gradMode m n x.2.1 i q p) := by unfold sumSq; positivity
      have h2 : 0 ≤ vecSq (modeVec m n x.1 p.1 p.2) := by unfold vecSq; positivity
      simp only [Pi.zero_apply]
      positivity
    · refine (ae_restrict_iff' (LowEntry.Internal.rect_meas K)).2 (ae_of_all _ fun p hp => ?_)
      have h1 : 0 ≤ sumSq (fun i q => gradMode m n x.2.1 i q p) := by unfold sumSq; positivity
      have h2 : 0 ≤ vecSq (modeVec m n x.1 p.1 p.2) := by unfold vecSq; positivity
      have h3 := lw_le K hK hp
      calc K.lineWeight p.1 * (sumSq (fun i q => gradMode m n x.2.1 i q p) + vecSq (modeVec m n x.1 p.1 p.2))
          ≤ ((if K.r₁ = 0 then 1 else 1 / K.r₁) * p.1) *
              (sumSq (fun i q => gradMode m n x.2.1 i q p) + vecSq (modeVec m n x.1 p.1 p.2)) :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = _ := by ring

theorem curlAdj_bd (u : Fin 3 → ℂ) : sumSq (curlAdj u) ≤ 2 * vecSq u := by
  simp [curlAdj, sumSq, vecSq, Fin.sum_univ_three, permSign]
  nlinarith [norm_nonneg (u 0), norm_nonneg (u 1), norm_nonneg (u 2)]

theorem sub_bd (x y z w : ℂ) : ‖x * y - z * w‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 * ‖y‖ ^ 2 + ‖z‖ ^ 2 * ‖w‖ ^ 2) := by
  have h := norm_sub_le (x * y) (z * w)
  rw [norm_mul, norm_mul] at h
  have h0 := norm_nonneg (x * y - z * w)
  nlinarith [sq_nonneg (‖x‖ * ‖y‖ - ‖z‖ * ‖w‖), mul_nonneg (norm_nonneg x) (norm_nonneg y),
    mul_nonneg (norm_nonneg z) (norm_nonneg w)]

theorem cross_bd (a b : Fin 3 → ℂ) : vecSq (crossC a b) ≤ 2 * (vecSq a * vecSq b) := by
  simp only [vecSq, crossC, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  have h1 := sub_bd (a 1) (b 2) (a 2) (b 1)
  have h2 := sub_bd (a 2) (b 0) (a 0) (b 2)
  have h3 := sub_bd (a 0) (b 1) (a 1) (b 0)
  nlinarith [mul_nonneg (sq_nonneg ‖a 0‖) (sq_nonneg ‖b 0‖), mul_nonneg (sq_nonneg ‖a 1‖) (sq_nonneg ‖b 1‖),
    mul_nonneg (sq_nonneg ‖a 2‖) (sq_nonneg ‖b 2‖)]

theorem conj_sq (u : Fin 3 → ℂ) : vecSq (conjVec3 u) = vecSq u := by
  simp [vecSq, conjVec3]

theorem fsum_bd {ι : Type} (s : Finset ι) (X : ι → ℂ) :
    ‖∑ n ∈ s, X n‖ ^ 2 ≤ (s.card : ℝ) * ∑ n ∈ s, ‖X n‖ ^ 2 := by
  refine le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2) ?_
  exact sq_sum_le_card_mul_sum_sq

theorem mat_sum_bd {ι : Type} (s : Finset ι) (r : ℝ) (X : ι → Fin 3 → Fin 3 → ℂ) :
    sumSq (fun i l => ((r : ℝ) : ℂ) * ∑ n ∈ s, X n i l) ≤ r ^ 2 * ((s.card : ℝ) * ∑ n ∈ s, sumSq (X n)) := by
  unfold sumSq
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg r)
  calc (∑ i : Fin 3, ∑ l : Fin 3, ‖∑ n ∈ s, X n i l‖ ^ 2)
      ≤ ∑ i : Fin 3, ∑ l : Fin 3, (s.card : ℝ) * ∑ n ∈ s, ‖X n i l‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => fsum_bd s _
    _ = _ := by
      have e : ∀ i : Fin 3, ∑ l : Fin 3, ∑ n ∈ s, (s.card : ℝ) * ‖X n i l‖ ^ 2
          = ∑ n ∈ s, ∑ l : Fin 3, (s.card : ℝ) * ‖X n i l‖ ^ 2 := fun i => Finset.sum_comm
      simp only [Finset.mul_sum]
      simp only [e]
      exact Finset.sum_comm

theorem vec_sum_bd {ι : Type} (s : Finset ι) (r : ℝ) (X : ι → Fin 3 → ℂ) :
    vecSq (fun i => ((r : ℝ) : ℂ) * ∑ n ∈ s, X n i) ≤ r ^ 2 * ((s.card : ℝ) * ∑ n ∈ s, vecSq (X n)) := by
  unfold vecSq
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg r)
  calc (∑ i : Fin 3, ‖∑ n ∈ s, X n i‖ ^ 2)
      ≤ ∑ i : Fin 3, (s.card : ℝ) * ∑ n ∈ s, ‖X n i‖ ^ 2 := Finset.sum_le_sum fun i _ => fsum_bd s _
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_comm]

theorem rcs_bd {k N : ℕ} (c : FracCellData k N) (K : CellBox) {slots : ℕ} (R : CellRows N slots k)
    (a : Fin N) (n' : ℤ) (p : ℝ × ℝ) :
    sumSq (CellScalars.rowCouplingStrain c K R a n' p) ≤ CellScalars.rHat K p ^ 2 * ((R.rowModes.card : ℝ) *
      ∑ n ∈ R.rowModes, 4 * (vecSq (modeVec c.order (n - n') c.modelVelocity p.1 p.2) *
        vecSq (CellScalars.rowMode c a n p))) := by
  refine (mat_sum_bd R.rowModes (CellScalars.rHat K p) _).trans ?_
  gcongr with n
  refine (curlAdj_bd _).trans ?_
  have := cross_bd (conjVec3 (modeVec c.order (n - n') c.modelVelocity p.1 p.2)) (CellScalars.rowMode c a n p)
  rw [conj_sq] at this
  linarith

theorem rcv_bd {k N : ℕ} (c : FracCellData k N) (K : CellBox) {slots : ℕ} (R : CellRows N slots k)
    (a : Fin N) (n' : ℤ) (p : ℝ × ℝ) :
    vecSq (CellScalars.rowCouplingVelocity c K R a n' p) ≤ CellScalars.rHat K p ^ 2 * ((R.rowModes.card : ℝ) *
      ∑ n ∈ R.rowModes, 2 * (vecSq (modeVec c.order (n - n') c.modelCurl p.1 p.2) *
        vecSq (CellScalars.rowMode c a n p))) := by
  refine (vec_sum_bd R.rowModes (CellScalars.rHat K p) _).trans ?_
  gcongr with n
  have := cross_bd (CellScalars.rowMode c a n p) (conjVec3 (modeVec c.order (n - n') c.modelCurl p.1 p.2))
  rw [conj_sq] at this
  linarith

theorem cyl_mem (K : CellBox) (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) (θ : ℝ) :
    cylPoint p.1 θ p.2 ∈ K.solid := by
  have hr : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
  have hz : 0 ≤ p.2 := le_trans hK.z_order.1 hp.2.1
  have e1 := FracInternal.CellDensityModesSolid.cyl_radius hr θ p.2
  have e2 : |cylHeight (cylPoint p.1 θ p.2)| = p.2 := by
    simp [cylHeight, cylPoint, abs_of_nonneg hz]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1]; exact hp.1.1
  · rw [e1]; exact hp.1.2
  · rw [e2]; exact hp.2.1
  · rw [e2]; exact hp.2.2

theorem lwr_le (K : CellBox) (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) :
    K.lineWeight p.1 * CellScalars.rHat K p ^ 2 ≤ max K.r₂ 1 * p.1 := by
  have hr : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
  unfold CellScalars.rHat CellBox.lineWeight
  split_ifs with h
  · rcases eq_or_lt_of_le hr with h0 | h0
    · rw [← h0]; simp
    · rw [div_self h0.ne', one_pow, mul_one]
      nlinarith [le_max_right K.r₂ 1]
  · rw [div_one, one_mul, sq]
    exact mul_le_mul_of_nonneg_right (hp.1.2.trans (le_max_left _ _)) hr

open SharpYChargeRegular.Internal in
theorem slice_coef_sq (K : CellBox) (hK : IsCellBox K) (m : ℕ) (hm : 0 < m) {X : Space → Space}
    (hX : AEStronglyMeasurable X volume) {C : ℝ} (hC : ∀ y ∈ K.solid, ‖X y‖ ≤ C) :
    ∀ᵐ p ∂(volume.restrict K.rect), ∀ (j0 : ℤ) (F : Finset ℤ),
      ∑ n ∈ F, vecSq (modeVec m (j0 - n) X p.1 p.2) ≤ 3 * C ^ 2 := by
  have hs : ∀ i : Fin 3, ∀ᵐ p ∂(volume.restrict K.rect),
      AEStronglyMeasurable (fun θ => frameVec θ (X (cylPoint p.1 θ p.2)) i) (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) :=
    fun i => ae_mono (ModeGradSquare.Internal.hle K hK)
      (slice_meas hX (fun θ u => frameVec θ u i) (ModeVelSquareInternal.frameVec_cont i))
  filter_upwards [hs 0, hs 1, hs 2, ae_restrict_mem (LowEntry.Internal.rect_meas K)] with p h0 h1 h2 hp
  intro j0 F
  have hb : ∀ i : Fin 3, AEStronglyMeasurable (fun θ => frameVec θ (X (cylPoint p.1 θ p.2)) i)
      (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) →
      ∑ n ∈ F, ‖modeVec m (j0 - n) X p.1 p.2 i‖ ^ 2 ≤ C ^ 2 := by
    intro i hi
    set f : ℝ → ℝ := fun θ => frameVec θ (X (cylPoint p.1 θ p.2)) i with hfdef
    have hfb : ∀ θ, |f θ| ≤ C := fun θ =>
      (ModeVelSquareInternal.frameVec_abs θ _ i).trans (hC _ (cyl_mem K hK hp θ))
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hfb 0)
    have hiC : AEStronglyMeasurable f (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
      exact hi
    have hfm : MemLp f 2 (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) :=
      MemLp.of_bound hiC C (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact hfb θ)
    obtain ⟨hsum, hle⟩ := coef_sq_sum m hm f hfm
    have e : ∀ j : ℤ, modeVec m j X p.1 p.2 i = coefAt m j f := fun j => mv_coef m j X i p
    have hinj : Set.InjOn (fun n : ℤ => j0 - n) F := fun x _ y _ h => by simpa using h
    calc ∑ n ∈ F, ‖modeVec m (j0 - n) X p.1 p.2 i‖ ^ 2
        = ∑ j ∈ F.image (fun n => j0 - n), ‖coefAt m j f‖ ^ 2 := by
          rw [Finset.sum_image hinj]
          exact Finset.sum_congr rfl fun n _ => by rw [e]
      _ ≤ ∑' j : ℤ, ‖coefAt m j f‖ ^ 2 := hsum.sum_le_tsum _ fun j _ => sq_nonneg _
      _ ≤ (2 * Real.pi)⁻¹ * ∫ θ in Set.Ioc (-Real.pi) Real.pi, f θ ^ 2 := hle
      _ ≤ (2 * Real.pi)⁻¹ * ∫ θ in Set.Ioc (-Real.pi) Real.pi, C ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine integral_mono_of_nonneg (μ := volume.restrict (Set.Ioc (-Real.pi) Real.pi)) (f := fun θ => f θ ^ 2) (g := fun _ => C ^ 2)
            (ae_of_all _ fun θ => sq_nonneg (f θ)) (integrable_const _)
            (ae_of_all _ fun θ => ?_)
          have := hfb θ
          nlinarith [abs_nonneg (f θ), sq_abs (f θ)]
      _ = C ^ 2 := by
          have hpi : 0 < Real.pi := Real.pi_pos
          rw [setIntegral_const, measureReal_def, Real.volume_Ioc, smul_eq_mul, ENNReal.toReal_ofReal (by linarith)]
          field_simp
          ring
  have H0 := hb 0 h0
  have H1 := hb 1 h1
  have H2 := hb 2 h2
  unfold vecSq
  rw [Finset.sum_comm]
  simp only [Fin.sum_univ_three]
  linarith

open SharpYChargeRegular.Internal in
theorem row_mode_int (K : CellBox) (hK : IsCellBox K) (m : ℕ) (hm : 0 < m) {X : Space → Space}
    (h2 : MemLp X 2 volume) (n : ℤ) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * vecSq (modeVec m n X p.1 p.2)) K.rect := by
  have hX := h2.aestronglyMeasurable
  have hfin : ∫⁻ y, ‖X y‖ₑ ^ 2 ≠ ⊤ := by
    have hi := ((memLp_two_iff_integrable_sq_norm hX).1 h2).2
    unfold HasFiniteIntegral at hi
    simpa only [enorm_pow, enorm_norm] using hi.ne
  have hc : ∀ i : Fin 3, IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖modeVec m n X p.1 p.2 i‖ ^ 2) K.rect := by
    intro i
    have H := (mode_sum K hK m hm hX (fun θ u => frameVec θ u i) (ModeVelSquareInternal.frameVec_cont i)
      (fun y => ‖X y‖ₑ ^ 2) (hX.enorm.pow_const 2) hfin (fun p _ θ => by
        refine pow_le_pow_left₀ (by positivity) ?_ 2
        rw [Real.enorm_eq_ofReal_abs, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (ModeVelSquareInternal.frameVec_abs θ _ i))).1 n
    simp only [← mv_coef] at H
    exact H
  have h := integrable_finsetSum (Finset.univ : Finset (Fin 3)) fun i _ => hc i
  refine h.congr (ae_of_all _ fun p => ?_)
  simp only [vecSq, Finset.mul_sum]

theorem modeMat_neg (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (r z : ℝ) (a b : Fin 3) :
    modeMat m (-n) G r z a b = (starRingEnd ℂ) (modeMat m n G r z a b) := by
  unfold modeMat
  have h : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [map_mul, intervalIntegral.integral_of_le h, intervalIntegral.integral_of_le h, ← integral_conj]
  congr 1
  · rw [map_div₀, map_one, map_mul, map_ofNat, Complex.conj_ofReal]
  · refine integral_congr_ae (ae_of_all _ fun θ => ?_)
    simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, Complex.conj_I, azimuth]
    push_cast
    ring_nf

theorem modeVec_neg (m : ℕ) (n : ℤ) (v : Space → Space) (r z : ℝ) (a : Fin 3) :
    modeVec m (-n) v r z a = (starRingEnd ℂ) (modeVec m n v r z a) := by
  unfold modeVec
  have h : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [map_mul, intervalIntegral.integral_of_le h, intervalIntegral.integral_of_le h, ← integral_conj]
  congr 1
  · rw [map_div₀, map_one, map_mul, map_ofNat, Complex.conj_ofReal]
  · refine integral_congr_ae (ae_of_all _ fun θ => ?_)
    simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, Complex.conj_I, azimuth]
    push_cast
    ring_nf

theorem coef_conj (K : CellBox) (B : CellBases) (F : ℝ × ℝ → ℂ) (j l : ℕ) :
    B.coef K (fun p => (starRingEnd ℂ) (F p)) j l = (starRingEnd ℂ) (B.coef K F j l) := by
  unfold CellBases.coef
  rw [← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [map_mul, Complex.conj_ofReal]

theorem proj_conj (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (Q : ℕ) (F : ℝ × ℝ → ℂ)
    (hF : ∀ t s : ℝ → ℝ, Continuous t → Continuous s →
      IntegrableOn (fun p => ((K.lineWeight p.1 * t p.1 * s p.2 : ℝ) : ℂ) * F p) K.rect) :
    K.proj Q Q (fun p => (starRingEnd ℂ) (F p)) = fun p => (starRingEnd ℂ) (K.proj Q Q F p) := by
  have hF' : ∀ t s : ℝ → ℝ, Continuous t → Continuous s →
      IntegrableOn (fun p => ((K.lineWeight p.1 * t p.1 * s p.2 : ℝ) : ℂ) * (starRingEnd ℂ) (F p)) K.rect := by
    intro t s ht hs
    have e : (fun p => ((K.lineWeight p.1 * t p.1 * s p.2 : ℝ) : ℂ) * (starRingEnd ℂ) (F p))
        = fun p => (starRingEnd ℂ) (((K.lineWeight p.1 * t p.1 * s p.2 : ℝ) : ℂ) * F p) := by
      funext p
      simp only [map_mul, Complex.conj_ofReal]
    rw [e]
    exact Integrable.mono' (hF t s ht hs).norm
      (Complex.continuous_conj.comp_aestronglyMeasurable (hF t s ht hs).aestronglyMeasurable)
      (ae_of_all _ fun p => (Complex.norm_conj _).le)
  rw [CellEnergy.HeightProj.proj_eq_basis K B hB Q _ hF', CellEnergy.HeightProj.proj_eq_basis K B hB Q F hF]
  funext p
  simp only [map_sum, map_mul, Complex.conj_ofReal, coef_conj]

theorem ws_int (K : CellBox) (hK : IsCellBox K) {F : ℝ × ℝ → ℂ} (hF : IsWeightedSquare K F) :
    ∀ t s : ℝ → ℝ, Continuous t → Continuous s →
      IntegrableOn (fun p => ((K.lineWeight p.1 * t p.1 * s p.2 : ℝ) : ℂ) * F p) K.rect := by
  intro t s ht hs
  have hw : Continuous (fun p : ℝ × ℝ => K.lineWeight p.1) := (LowEntry.Internal.lineWeight_cont K).comp continuous_fst
  have hts : Continuous (fun p : ℝ × ℝ => t p.1 * s p.2) := (ht.comp continuous_fst).mul (hs.comp continuous_snd)
  have hc : Continuous (fun p : ℝ × ℝ => K.lineWeight p.1 * t p.1 * s p.2) :=
    (hw.mul (ht.comp continuous_fst)).mul (hs.comp continuous_snd)
  obtain ⟨C, hC⟩ := (LowEntry.Internal.rect_compact K).exists_bound_of_continuousOn hts.continuousOn
  have hlw : IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1) K.rect :=
    hw.continuousOn.integrableOn_compact (LowEntry.Internal.rect_compact K)
  refine Integrable.mono' ((hlw.add hF.2).const_mul C)
    ((Complex.continuous_ofReal.comp hc).aestronglyMeasurable.mul hF.1) ?_
  refine (ae_restrict_iff' (LowEntry.Internal.rect_meas K)).2 (ae_of_all _ fun p hp => ?_)
  have h0 := SharpRowIdentity.Internal.lw_nonneg_rect K hK hp
  have h1 := hC p hp
  rw [Real.norm_eq_abs] at h1
  have hC0 : 0 ≤ C := (abs_nonneg _).trans h1
  have hx := norm_nonneg (F p)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg h0]
  simp only [Pi.add_apply]
  have h2 : ‖F p‖ ≤ 1 + ‖F p‖ ^ 2 := by nlinarith [sq_nonneg (‖F p‖ - 1)]
  calc K.lineWeight p.1 * |t p.1 * s p.2| * ‖F p‖ ≤ K.lineWeight p.1 * C * (1 + ‖F p‖ ^ 2) := by
        gcongr
    _ = C * (K.lineWeight p.1 + K.lineWeight p.1 * ‖F p‖ ^ 2) := by ring

theorem lowStrain_neg (K : CellBox) (B : CellBases) (hK : IsCellBox K) (hB : IsCellBases K B) (m : ℕ) (n : ℤ)
    (Q : ℕ) (G : Space → (Space →L[ℝ] Space)) (a b : Fin 3) (hF : IsWeightedSquare K (gradMode m n G a b)) (p : ℝ × ℝ) :
    K.lowStrain m (-n) Q G a b p = (starRingEnd ℂ) (K.lowStrain m n Q G a b p) := by
  unfold CellBox.lowStrain
  have e : gradMode m (-n) G a b = fun p => (starRingEnd ℂ) (gradMode m n G a b p) := by
    funext q
    exact modeMat_neg m n G q.1 q.2 a b
  rw [e, proj_conj K B hB Q _ (ws_int K hK hF)]

theorem lowVelocity_neg (K : CellBox) (B : CellBases) (hK : IsCellBox K) (hB : IsCellBases K B) (m : ℕ) (n : ℤ)
    (Q : ℕ) (v : Space → Space) (a : Fin 3) (hF : IsWeightedSquare K (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a))
    (p : ℝ × ℝ) :
    K.lowVelocity m (-n) Q v a p = (starRingEnd ℂ) (K.lowVelocity m n Q v a p) := by
  unfold CellBox.lowVelocity
  have e : (fun q : ℝ × ℝ => modeVec m (-n) v q.1 q.2 a) = fun q => (starRingEnd ℂ) (modeVec m n v q.1 q.2 a) := by
    funext q
    exact modeVec_neg m n v q.1 q.2 a
  rw [e, proj_conj K B hB (Q - 1) _ (ws_int K hK hF)]

end RowModeUnfolded.Internal

open SharpRowIdentity.Internal RowModeUnfolded.Internal in
theorem rowModeUnfolded_of (h0 : ModeSquareStatement) (h3 : ProjCoefStatement)
    (hC : RowCircleSeriesStatement) (hD : RowSeriesDominationStatement) : RowModeUnfoldedStatement := by
  intro α ha1 ha2 k N c hc K S B Cl slots R hd hw x hx a ha
  have hK := hd.box
  obtain ⟨hg, hv, hrow⟩ := h0 α ha1 ha2 c hc K S B Cl R hd hw x hx
  have hE : ∀ n : ℤ, IntegrableOn (fun p => ((K.lineWeight p.1 : ℝ) : ℂ) *
      entryPairing (fun i q => gradMode c.order n x.2.1 i q p
        - (if n ∈ S.resolved then K.lowStrain c.order n S.degHigh x.2.1 i q p else 0))
        (CellScalars.rowCouplingStrain c K R a n p)) K.rect := fun n =>
    entry_int K hK (F := fun i q p => gradMode c.order n x.2.1 i q p
        - (if n ∈ S.resolved then K.lowStrain c.order n S.degHigh x.2.1 i q p else 0))
      (W := fun i q p => CellScalars.rowCouplingStrain c K R a n p i q)
      (fun i q => low_sq K B hK hd.bases h3 _ (hg n i q) S.degHigh (n ∈ S.resolved))
      (fun i q => (hrow a ha n).1 i q)
  have hV : ∀ n : ℤ, IntegrableOn (fun p => ((K.lineWeight p.1 : ℝ) : ℂ) *
      CellScalars.vecPair (fun i => modeVec c.order n x.1 p.1 p.2 i
        - (if n ∈ S.resolved then K.lowVelocity c.order n S.degHigh x.1 i p else 0))
        (CellScalars.rowCouplingVelocity c K R a n p)) K.rect := fun n =>
    vec_int K hK (F := fun i p => modeVec c.order n x.1 p.1 p.2 i
        - (if n ∈ S.resolved then K.lowVelocity c.order n S.degHigh x.1 i p else 0))
      (W := fun i p => CellScalars.rowCouplingVelocity c K R a n p i)
      (fun i => low_sq K B hK hd.bases h3 _ (hv n i) (S.degHigh - 1) (n ∈ S.resolved))
      (fun i => (hrow a ha n).2.1 i)
  have hDe : ∀ n : ℤ, CellScalars.rowModeDensity c K S R x a n = fun p =>
      ((K.lineWeight p.1 : ℝ) : ℂ) *
        entryPairing (fun i q => gradMode c.order n x.2.1 i q p
          - (if n ∈ S.resolved then K.lowStrain c.order n S.degHigh x.2.1 i q p else 0))
          (CellScalars.rowCouplingStrain c K R a n p)
      + ((K.lineWeight p.1 : ℝ) : ℂ) *
        CellScalars.vecPair (fun i => modeVec c.order n x.1 p.1 p.2 i
          - (if n ∈ S.resolved then K.lowVelocity c.order n S.degHigh x.1 i p else 0))
          (CellScalars.rowCouplingVelocity c K R a n p) := fun n => by
    funext p
    unfold CellScalars.rowModeDensity
    ring
  have hDi : ∀ n : ℤ, IntegrableOn (CellScalars.rowModeDensity c K S R x a n) K.rect := fun n => by
    rw [hDe n]
    exact (hE n).add (hV n)
  have hDr : ∀ n : ℤ, IntegrableOn (fun p => (CellScalars.rowModeDensity c K S R x a n p).re) K.rect :=
    fun n => (hDi n).re
  set T : ℤ → ℝ := fun n => ∫ p in K.rect, (CellScalars.rowModeDensity c K S R x a n p).re with hT
  have hTe : ∀ n, T n = (∫ p in K.rect, CellScalars.rowModeDensity c K S R x a n p).re := fun n =>
    integral_re (hDi n)
  have hsumN : Summable (fun n : ℤ => ∫ p in K.rect, ‖(CellScalars.rowModeDensity c K S R x a n p).re‖) := by
    refine (hD α ha1 ha2 c hc K S B Cl R hd hw x hx a ha).of_nonneg_of_le
      (fun n => integral_nonneg fun p => norm_nonneg _) (fun n => ?_)
    refine integral_mono (hDr n).norm (hDi n).norm fun p => ?_
    simp only [Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _
  have hTs : Summable T := by
    refine hsumN.of_norm_bounded (fun n => ?_)
    exact norm_integral_le_integral_norm _
  have h1 : l2Pair (CellScalars.highCouplingField c K S x.1 x.2.1) (c.row a)
      = 4 * Real.pi * ∫ p in K.rect, p.1 * CellScalars.circleRowPair c K S x a p := by
    refine FracInternal.LayoutRowModes.pairing_mode_reduction hK (hd.rows_in_cell a ha)
      (pair_integrable hc hd hx ha) (coupling_pair_mirror a hc hd hx) _
      (ae_of_all _ fun p => ?_)
    unfold CellScalars.circleRowPair
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    rw [← mul_assoc, mul_one_div_cancel hpi, one_mul]
  have h2 : (∫ p in K.rect, p.1 * CellScalars.circleRowPair c K S x a p)
      = ∫ p in K.rect, ∑' n : ℤ, (CellScalars.rowModeDensity c K S R x a n p).re := by
    refine integral_congr_ae ?_
    filter_upwards [hC α ha1 ha2 c hc K S B Cl R hd hw x hx a ha] with p hp
    exact hp.tsum_eq.symm
  have h4 : (∫ p in K.rect, ∑' n : ℤ, (CellScalars.rowModeDensity c K S R x a n p).re) = ∑' n, T n :=
    (integral_tsum_of_summable_integral_norm hDr hsumN).symm
  have hU : ∀ n ∈ S.resolved ∪ S.band, T n = CellScalars.unfoldedRowPair c K S R x a n := by
    intro n _
    rw [hTe n, hDe n, integral_add (hE n) (hV n), Complex.add_re]
    rfl
  have hR : ∀ n, CellScalars.unresolvedRowPair c K S R x a n
      = if n ∈ S.resolved ∪ S.band then 0 else T n := by
    intro n
    unfold CellScalars.unresolvedRowPair
    split_ifs with hn
    · rfl
    · have hr : n ∉ S.resolved := fun h => hn (Finset.mem_union_left _ h)
      rw [hTe n]
      unfold CellScalars.rowModeDensity
      simp only [if_neg hr, sub_zero]
  have hI : Summable (fun n => if n ∈ S.resolved ∪ S.band then T n else 0) :=
    summable_of_ne_finset_zero (s := S.resolved ∪ S.band) fun n hn => if_neg hn
  have hsplit : T = fun n => (if n ∈ S.resolved ∪ S.band then T n else 0)
      + CellScalars.unresolvedRowPair c K S R x a n := by
    funext n
    rw [hR n]
    split_ifs <;> simp
  have hUs : Summable (fun n => CellScalars.unresolvedRowPair c K S R x a n) := by
    have : (fun n => CellScalars.unresolvedRowPair c K S R x a n)
        = fun n => T n - (if n ∈ S.resolved ∪ S.band then T n else 0) := by
      funext n
      rw [hR n]
      split_ifs <;> simp
    rw [this]
    exact hTs.sub hI
  have hfin : (∑' n, T n) = ∑' n, ((if n ∈ S.resolved ∪ S.band then T n else 0)
      + CellScalars.unresolvedRowPair c K S R x a n) := tsum_congr fun n => congrFun hsplit n
  rw [h1, h2, h4, hfin, hI.tsum_add hUs, tsum_eq_sum (s := S.resolved ∪ S.band) (fun n hn => if_neg hn)]
  congr 2
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [if_pos hn]
  exact hU n hn

open RowModeUnfolded.Internal in
theorem rowSeriesDomination_of (h0 : ModeSquareStatement) (h3 : ProjCoefStatement) (hT : RowCouplingTailStatement) :
    RowSeriesDominationStatement := by
  intro α ha1 ha2 k N c hc K S B Cl slots R hd hw x hx a ha
  have hK := hd.box
  obtain ⟨hg, hv, hrow⟩ := h0 α ha1 ha2 c hc K S B Cl R hd hw x hx
  have hm : 0 < c.order := by have := hc.base.order_ge; omega
  have hrm := LowEntry.Internal.rect_meas K
  have hfi : ∀ n : ℤ, IntegrableOn (fun p => K.lineWeight p.1 *
      (sumSq (fun i q => gradMode c.order n x.2.1 i q p
          - (if n ∈ S.resolved then K.lowStrain c.order n S.degHigh x.2.1 i q p else 0))
        + vecSq (fun i => modeVec c.order n x.1 p.1 p.2 i
          - (if n ∈ S.resolved then K.lowVelocity c.order n S.degHigh x.1 i p else 0)))) K.rect := by
    intro n
    have h1 := sq_int (K := K) (F := fun i q p => gradMode c.order n x.2.1 i q p
          - (if n ∈ S.resolved then K.lowStrain c.order n S.degHigh x.2.1 i q p else 0))
      (fun i q => low_sq K B hK hd.bases h3 _ (hg n i q) S.degHigh (n ∈ S.resolved))
    have h2 := vsq_int (K := K) (F := fun i p => modeVec c.order n x.1 p.1 p.2 i
          - (if n ∈ S.resolved then K.lowVelocity c.order n S.degHigh x.1 i p else 0))
      (fun i => low_sq K B hK hd.bases h3 _ (hv n i) (S.degHigh - 1) (n ∈ S.resolved))
    refine (h1.add h2).congr (ae_of_all _ fun p => ?_)
    simp only [Pi.add_apply]
    ring
  have hti : ∀ n : ℤ, IntegrableOn (fun p => K.lineWeight p.1 *
      (sumSq (CellScalars.rowCouplingStrain c K R a n p) + vecSq (CellScalars.rowCouplingVelocity c K R a n p)))
      K.rect := by
    intro n
    have h1 := sq_int (K := K) (F := fun i q p => CellScalars.rowCouplingStrain c K R a n p i q) (hrow a ha n).1
    have h2 := vsq_int (K := K) (F := fun i p => CellScalars.rowCouplingVelocity c K R a n p i) (hrow a ha n).2.1
    refine (h1.add h2).congr (ae_of_all _ fun p => ?_)
    simp only [Pi.add_apply]
    ring
  have hnn : ∀ (X : ℝ × ℝ → ℝ), (∀ p ∈ K.rect, 0 ≤ X p) → 0 ≤ ∫ p in K.rect, X p := fun X hX =>
    setIntegral_nonneg hrm hX
  have sq0 : ∀ s : Fin 3 → Fin 3 → ℂ, 0 ≤ sumSq s := fun s => by unfold sumSq; positivity
  have vq0 : ∀ s : Fin 3 → ℂ, 0 ≤ vecSq s := fun s => by unfold vecSq; positivity
  have hfield := field_tail K hK c.order hm hx.1
  have hf : Summable (fun n : ℤ => ∫ p in K.rect, K.lineWeight p.1 *
      (sumSq (fun i q => gradMode c.order n x.2.1 i q p
          - (if n ∈ S.resolved then K.lowStrain c.order n S.degHigh x.2.1 i q p else 0))
        + vecSq (fun i => modeVec c.order n x.1 p.1 p.2 i
          - (if n ∈ S.resolved then K.lowVelocity c.order n S.degHigh x.1 i p else 0)))) := by
    set f := fun n : ℤ => ∫ p in K.rect, K.lineWeight p.1 *
      (sumSq (fun i q => gradMode c.order n x.2.1 i q p
          - (if n ∈ S.resolved then K.lowStrain c.order n S.degHigh x.2.1 i q p else 0))
        + vecSq (fun i => modeVec c.order n x.1 p.1 p.2 i
          - (if n ∈ S.resolved then K.lowVelocity c.order n S.degHigh x.1 i p else 0))) with hfdef
    have hI : Summable (fun n => if n ∈ S.resolved then f n else 0) :=
      summable_of_ne_finset_zero (s := S.resolved) fun n hn => if_neg hn
    refine (hfield.add hI).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · exact hnn _ fun p hp => mul_nonneg (SharpRowIdentity.Internal.lw_nonneg_rect K hK hp)
        (add_nonneg (sq0 _) (vq0 _))
    · have hF0 : 0 ≤ ∫ p in K.rect, K.lineWeight p.1 *
          (sumSq (fun i q => gradMode c.order n x.2.1 i q p) + vecSq (modeVec c.order n x.1 p.1 p.2)) :=
        hnn _ fun p hp => mul_nonneg (SharpRowIdentity.Internal.lw_nonneg_rect K hK hp)
          (add_nonneg (sq0 _) (vq0 _))
      by_cases hn : n ∈ S.resolved
      · simp only [if_pos hn]
        linarith
      · simp only [if_neg hn, add_zero, hfdef, sub_zero]
        exact le_rfl
  have hts := hT α ha1 ha2 c hc K S B Cl R hd hw a ha
  refine ((hf.add hts).mul_left (1 / 2)).of_nonneg_of_le (fun n => hnn _ fun p _ => norm_nonneg _) (fun n => ?_)
  rw [mul_add, ← integral_const_mul, ← integral_const_mul, ← integral_add ((hfi n).const_mul _) ((hti n).const_mul _)]
  refine integral_mono_of_nonneg (ae_of_all _ fun p => norm_nonneg _) (((hfi n).const_mul _).add ((hti n).const_mul _)) ?_
  refine (ae_restrict_iff' hrm).2 (ae_of_all _ fun p hp => ?_)
  exact density_bd c K S R x a n p (SharpRowIdentity.Internal.lw_nonneg_rect K hK hp)

theorem rowModeUnfolded_of_leaves (h0 : ModeSquareStatement) (h3 : ProjCoefStatement)
    (hC : RowCircleSeriesStatement) (hT : RowCouplingTailStatement) : RowModeUnfoldedStatement :=
  rowModeUnfolded_of h0 h3 hC (rowSeriesDomination_of h0 h3 hT)

open RowModeUnfolded.Internal in
theorem rowCouplingTail_of (hR : RowCouplingSquareStatement) : RowCouplingTailStatement := by
  intro α ha1 ha2 k N c hc K S B Cl slots R hd hw a ha
  have hK := hd.box
  have hm : 0 < c.order := by have := hc.base.order_ge; omega
  have hrm := LowEntry.Internal.rect_meas K
  obtain ⟨CM, hCM⟩ := hc.model_bounded
  have hV : ∀ y ∈ K.solid, ‖c.modelVelocity y‖ ≤ |CM| := fun y hy =>
    (hCM y (hd.solid_in_region hy)).1.trans (le_abs_self _)
  have hW : ∀ y ∈ K.solid, ‖c.modelCurl y‖ ≤ |CM| := fun y hy =>
    (hCM y (hd.solid_in_region hy)).2.1.trans (le_abs_self _)
  have bV := slice_coef_sq K hK c.order hm hc.model_measurable.1 hV
  have bW := slice_coef_sq K hK c.order hm hc.model_measurable.2.1 hW
  have hsq := hR α ha1 ha2 c hc K S B Cl R hd hw a ha
  have hTi : ∀ n : ℤ, IntegrableOn (fun p => K.lineWeight p.1 *
      (sumSq (CellScalars.rowCouplingStrain c K R a n p) + vecSq (CellScalars.rowCouplingVelocity c K R a n p)))
      K.rect := by
    intro n
    have h1 := sq_int (K := K) (F := fun i q p => CellScalars.rowCouplingStrain c K R a n p i q) (hsq n).1
    have h2 := vsq_int (K := K) (F := fun i p => CellScalars.rowCouplingVelocity c K R a n p i) (hsq n).2.1
    refine (h1.add h2).congr (ae_of_all _ fun p => ?_)
    simp only [Pi.add_apply]
    ring
  have sq0 : ∀ s : Fin 3 → Fin 3 → ℂ, 0 ≤ sumSq s := fun s => by unfold sumSq; positivity
  have vq0 : ∀ s : Fin 3 → ℂ, 0 ≤ vecSq s := fun s => by unfold vecSq; positivity
  set L : ℝ := max K.r₂ 1 * ((R.rowModes.card : ℝ) * (18 * |CM| ^ 2)) with hL
  have hL0 : 0 ≤ L := by positivity
  have hBi : IntegrableOn (fun p : ℝ × ℝ => L * ∑ n ∈ R.rowModes, p.1 * vecSq (CellScalars.rowMode c a n p)) K.rect := by
    refine Integrable.const_mul ?_ L
    have h := integrable_finsetSum R.rowModes fun n _ =>
      row_mode_int K hK c.order hm (hc.base.row_two a) n
    refine h.congr (ae_of_all _ fun p => ?_)
    rfl
  refine summable_of_sum_le (c := ∫ p in K.rect, L * ∑ n ∈ R.rowModes, p.1 * vecSq (CellScalars.rowMode c a n p))
    (fun n => setIntegral_nonneg hrm fun p hp => mul_nonneg (SharpRowIdentity.Internal.lw_nonneg_rect K hK hp)
      (add_nonneg (sq0 _) (vq0 _))) (fun F => ?_)
  rw [← integral_finsetSum F fun n _ => hTi n]
  refine integral_mono_ae (integrable_finsetSum F fun n _ => hTi n) hBi ?_
  filter_upwards [bV, bW, ae_restrict_mem hrm] with p hbV hbW hp
  have hw0 := SharpRowIdentity.Internal.lw_nonneg_rect K hK hp
  have hr0 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
  set ψ : ℤ → ℝ := fun n => vecSq (CellScalars.rowMode c a n p) with hψ
  set Q : ℝ := K.lineWeight p.1 * (CellScalars.rHat K p ^ 2 * (R.rowModes.card : ℝ))
  have hQ0 : 0 ≤ Q := by positivity
  have step1 : ∀ n' : ℤ, K.lineWeight p.1 * (sumSq (CellScalars.rowCouplingStrain c K R a n' p)
      + vecSq (CellScalars.rowCouplingVelocity c K R a n' p)) ≤
      Q * ∑ n ∈ R.rowModes, (4 * vecSq (modeVec c.order (n - n') c.modelVelocity p.1 p.2)
        + 2 * vecSq (modeVec c.order (n - n') c.modelCurl p.1 p.2)) * ψ n := by
    intro n'
    have e1 := rcs_bd c K R a n' p
    have e2 := rcv_bd c K R a n' p
    have e3 : Q * ∑ n ∈ R.rowModes, (4 * vecSq (modeVec c.order (n - n') c.modelVelocity p.1 p.2)
        + 2 * vecSq (modeVec c.order (n - n') c.modelCurl p.1 p.2)) * ψ n
        = K.lineWeight p.1 * (CellScalars.rHat K p ^ 2 * ((R.rowModes.card : ℝ) *
          ∑ n ∈ R.rowModes, 4 * (vecSq (modeVec c.order (n - n') c.modelVelocity p.1 p.2) *
            vecSq (CellScalars.rowMode c a n p)))
          + CellScalars.rHat K p ^ 2 * ((R.rowModes.card : ℝ) *
          ∑ n ∈ R.rowModes, 2 * (vecSq (modeVec c.order (n - n') c.modelCurl p.1 p.2) *
            vecSq (CellScalars.rowMode c a n p)))) := by
      simp only [Q, hψ, mul_add, Finset.mul_sum, add_mul, Finset.sum_add_distrib]
      congr 1 <;> refine Finset.sum_congr rfl fun n _ => ?_ <;> ring
    rw [e3]
    exact mul_le_mul_of_nonneg_left (add_le_add e1 e2) hw0
  have step2 : ∑ n' ∈ F, ∑ n ∈ R.rowModes, (4 * vecSq (modeVec c.order (n - n') c.modelVelocity p.1 p.2)
        + 2 * vecSq (modeVec c.order (n - n') c.modelCurl p.1 p.2)) * ψ n
      ≤ ∑ n ∈ R.rowModes, 18 * |CM| ^ 2 * ψ n := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := hbV n F
    have h2 := hbW n F
    have hp0 : 0 ≤ ψ n := vq0 _
    nlinarith
  have hQL : Q * 18 * |CM| ^ 2 ≤ L * p.1 := by
    have := lwr_le K hK hp
    simp only [Q, hL]
    have hc0 : (0 : ℝ) ≤ R.rowModes.card := by positivity
    nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg hc0 (by positivity : (0 : ℝ) ≤ 18 * |CM| ^ 2))]
  calc ∑ n' ∈ F, K.lineWeight p.1 * (sumSq (CellScalars.rowCouplingStrain c K R a n' p)
        + vecSq (CellScalars.rowCouplingVelocity c K R a n' p))
      ≤ ∑ n' ∈ F, Q * ∑ n ∈ R.rowModes, (4 * vecSq (modeVec c.order (n - n') c.modelVelocity p.1 p.2)
        + 2 * vecSq (modeVec c.order (n - n') c.modelCurl p.1 p.2)) * ψ n := Finset.sum_le_sum fun n' _ => step1 n'
    _ = Q * ∑ n' ∈ F, ∑ n ∈ R.rowModes, (4 * vecSq (modeVec c.order (n - n') c.modelVelocity p.1 p.2)
        + 2 * vecSq (modeVec c.order (n - n') c.modelCurl p.1 p.2)) * ψ n := by rw [Finset.mul_sum]
    _ ≤ Q * ∑ n ∈ R.rowModes, 18 * |CM| ^ 2 * ψ n := mul_le_mul_of_nonneg_left step2 hQ0
    _ = ∑ n ∈ R.rowModes, (Q * 18 * |CM| ^ 2) * ψ n := by rw [Finset.mul_sum]; simp only [mul_assoc]
    _ ≤ ∑ n ∈ R.rowModes, (L * p.1) * ψ n :=
        Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_right hQL (vq0 _)
    _ = L * ∑ n ∈ R.rowModes, p.1 * vecSq (CellScalars.rowMode c a n p) := by
        rw [Finset.mul_sum]; simp only [hψ, mul_assoc]

theorem rowModeUnfolded_of_circle (hF : FieldModeSquareStatement) (hR : RowCouplingSquareStatement)
    (h3 : ProjCoefStatement) (hC : RowCircleSeriesStatement) : RowModeUnfoldedStatement :=
  rowModeUnfolded_of (modeSquare_of hF hR) h3 hC
    (rowSeriesDomination_of (modeSquare_of hF hR) h3 (rowCouplingTail_of hR))

end CellAnalysis

end CellCert

end Breakdown
