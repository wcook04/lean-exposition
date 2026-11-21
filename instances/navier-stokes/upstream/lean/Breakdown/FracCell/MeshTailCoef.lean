import Breakdown.FracCell.MeshTailSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace MeshTailCoef

variable {I O : Type} [Fintype I] [Fintype O]

theorem angleField_bound (K : CellBox) (m : ℕ) (B : CellBases) (T : TailFamily I O)
    (hreg : IsTailRegular K T) (w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ) (o : O) :
    ∃ C : ℝ, ∀ p ∈ K.rect, ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖T.angleField m B w o p θ‖ ≤ C := by
  have hrectc : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  choose Cm hCm using hreg.mult_bounded
  have hCi : ∀ i c, ∃ C, ∀ q ∈ K.rect ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi),
      ‖(fun q : (ℝ × ℝ) × ℝ => T.inputFn m B w i c q.1 q.2) q‖ ≤ C := by
    intro i c
    refine (hrectc.prod isCompact_Icc).exists_bound_of_continuousOn (Continuous.continuousOn ?_)
    unfold TailFamily.inputFn CellBases.radialPoly CellBases.heightPoly
    fun_prop
  choose Ci hCi using hCi
  refine ⟨∑ i, ∑ c, |Cm i o c| * |Ci i c|, fun p hp θ hθ => ?_⟩
  unfold TailFamily.angleField
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun c _ => ?_))
  rw [norm_mul]
  exact mul_le_mul ((hCm i o c p hp θ).trans (le_abs_self _)) ((hCi i c (p, θ) ⟨hp, hθ⟩).trans (le_abs_self _))
    (norm_nonneg _) (abs_nonneg _)

theorem lineWeight_continuous (K : CellBox) : Continuous (fun r : ℝ => K.lineWeight r) := by
  by_cases h : K.r₁ = 0
  · simp only [CellBox.lineWeight, h, if_true]; exact continuous_id
  · simp only [CellBox.lineWeight, h, if_false]; exact continuous_const

end MeshTailCoef

open MeshTailCoef in
theorem coefMode_holds : CoefModeStatement := by
  intro K B hK m I O _ _ T hreg w o n j l
  have hrect : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hrectc : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have : IsFiniteMeasure (volume.restrict K.rect) := isFiniteMeasure_restrict.2 hrectc.measure_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hprod : (volume.restrict K.rect).prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))
      = ((volume.restrict K.rect).prod volume).restrict (Set.univ ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hprod' : (volume.restrict K.rect).prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))
      = ((volume : Measure (ℝ × ℝ)).prod volume).restrict (K.rect ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi)) := by
    rw [Measure.prod_restrict]
  have hmult : ∀ i c, AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => T.mult i o c q.1 q.2)
      ((volume.restrict K.rect).prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))) := by
    intro i c; rw [hprod]; exact (hreg.mult_measurable i o c).restrict
  have hinC : ∀ i c, Continuous (fun q : (ℝ × ℝ) × ℝ => T.inputFn m B w i c q.1 q.2) := by
    intro i c
    unfold TailFamily.inputFn CellBases.radialPoly CellBases.heightPoly
    fun_prop
  have hlw := lineWeight_continuous K
  have hrp : Continuous (fun r : ℝ => B.radialPoly j r) := by
    unfold CellBases.radialPoly
    exact continuous_finsetSum _ fun i _ => by fun_prop
  have hhp : Continuous (fun z : ℝ => B.heightPoly l z) := by
    unfold CellBases.heightPoly
    exact continuous_finsetSum _ fun i _ => by fun_prop
  have hW : Continuous (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp (hlw.comp continuous_fst)).mul
      (Complex.continuous_ofReal.comp ((hrp.comp continuous_fst).mul (hhp.comp continuous_snd)))
  have hE : Continuous (fun θ : ℝ => Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I)) := by fun_prop
  have hE1 : ∀ θ : ℝ, ‖Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I)‖ = 1 := by
    intro θ; rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  obtain ⟨CΦ, hCΦ⟩ := angleField_bound K m B T hreg w o
  obtain ⟨CW, hCW⟩ := hrectc.exists_bound_of_continuousOn hW.continuousOn
  set f : (ℝ × ℝ) × ℝ → ℂ := fun q => ((K.lineWeight q.1.1 : ℂ) *
      ((B.radialPoly j q.1.1 * B.heightPoly l q.1.2 : ℝ) : ℂ)) *
      (Complex.exp (-(azimuth m n * q.2 : ℝ) * Complex.I) * T.angleField m B w o q.1 q.2) with hf
  set g : (ℝ × ℝ) × ℝ → ℂ := fun q => ((K.lineWeight q.1.1 : ℂ) *
      ((B.radialPoly j q.1.1 * B.heightPoly l q.1.2 : ℝ) : ℂ)) * T.angleField m B w o q.1 q.2 with hg
  have hΦm : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => T.angleField m B w o q.1 q.2)
      ((volume.restrict K.rect).prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))) := by
    unfold TailFamily.angleField
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => Finset.aestronglyMeasurable_fun_sum _ fun c _ => ?_
    exact (hmult i c).mul (hinC i c).aestronglyMeasurable
  have hfm : AEStronglyMeasurable f
      ((volume.restrict K.rect).prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))) :=
    (hW.comp continuous_fst).aestronglyMeasurable.mul ((hE.comp continuous_snd).aestronglyMeasurable.mul hΦm)
  have hgm : AEStronglyMeasurable g
      ((volume.restrict K.rect).prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))) :=
    (hW.comp continuous_fst).aestronglyMeasurable.mul hΦm
  have hmem : ∀ᵐ q ∂((volume.restrict K.rect).prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))),
      q ∈ K.rect ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi) := by
    rw [hprod']; exact ae_restrict_mem (hrect.prod measurableSet_Ioc)
  have hfb : ∀ q ∈ K.rect ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi), ‖f q‖ ≤ CW * CΦ := by
    intro q hq
    simp only [hf]
    rw [norm_mul ((K.lineWeight q.1.1 : ℂ) * _), norm_mul (Complex.exp _), hE1, one_mul]
    exact mul_le_mul (hCW q.1 hq.1) (hCΦ q.1 hq.1 q.2 (Set.Ioc_subset_Icc_self hq.2)) (norm_nonneg _)
      ((norm_nonneg _).trans (hCW q.1 hq.1))
  have hfi : Integrable f ((volume.restrict K.rect).prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))) :=
    Integrable.of_bound hfm (CW * CΦ) (hmem.mono fun q hq => hfb q hq)
  constructor
  · have hswap := integral_integral_swap (f := fun p θ => f (p, θ)) hfi
    have e2 : B.coef K (T.outputMode m B w o n) j l
        = (1 / (2 * Real.pi) : ℂ) * ∫ p in K.rect, ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), f (p, θ) := by
      unfold CellBases.coef
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp only [hf]
      rw [integral_const_mul]
      unfold TailFamily.outputMode TailFamily.angleField
      rw [intervalIntegral.integral_of_le hpi.le]
      ring
    have e3 : (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
              Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * B.coef K (fun p => T.angleField m B w o p θ) j l
        = (1 / (2 * Real.pi) : ℂ) * ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), ∫ p in K.rect, f (p, θ) := by
      rw [intervalIntegral.integral_of_le hpi.le]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      unfold CellBases.coef
      simp only [hf]
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      ring
    rw [e2, e3, hswap]
  · refine MemLp.of_bound ?_ (CW * CΦ * (volume.real K.rect)) ?_
    · have h1 := (hgm.prod_swap).integral_prod_right'
      refine h1.congr (Filter.Eventually.of_forall fun θ => ?_)
      unfold CellBases.coef
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp only [hg, Prod.swap_prod_mk]
      ring
    · refine (ae_restrict_mem measurableSet_Ioc).mono fun θ hθ => ?_
      unfold CellBases.coef
      refine norm_setIntegral_le_of_norm_le_const hrectc.measure_lt_top fun p hp => ?_
      have e4 : (K.lineWeight p.1 : ℂ) * T.angleField m B w o p θ * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)
          = ((K.lineWeight p.1 : ℂ) * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) *
              T.angleField m B w o p θ := by ring
      rw [e4, norm_mul]
      exact mul_le_mul (hCW p hp) (hCΦ p hp θ (Set.Ioc_subset_Icc_self hθ)) (norm_nonneg _)
        ((norm_nonneg _).trans (hCW p hp))

end CellAnalysis

end CellCert

end Breakdown
