import Breakdown.FracCell.MeshFarPoly

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly MeshFarPolyInternal

def CylinderCompStatement : Prop :=
  ∀ (f : Space → (Space →L[ℝ] Space)), AEStronglyMeasurable f volume →
    AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => f (cylPoint q.1.1 q.2 q.1.2)) volume

namespace MeshFarRegularInternal

theorem single_continuous (i : Fin 3) :
    Continuous (fun x : ℝ => (EuclideanSpace.single i x : EuclideanSpace ℝ (Fin 3))) := by
  have e : (fun x : ℝ => (EuclideanSpace.single i x : EuclideanSpace ℝ (Fin 3))) =
      fun x => x • (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 3)) := by
    funext x
    ext j
    simp
  rw [e]
  exact continuous_id.smul continuous_const

theorem frameMat_continuous (a b : Fin 3) :
    Continuous (fun x : (Space →L[ℝ] Space) × ℝ => frameMat x.2 x.1 a b) := by
  have hr : Continuous radialUnit := by
    unfold radialUnit
    exact ((single_continuous 0).comp Real.continuous_cos).add ((single_continuous 1).comp Real.continuous_sin)
  have ha : Continuous angularUnit := by
    unfold angularUnit
    exact ((single_continuous 0).comp Real.continuous_sin.neg).add ((single_continuous 1).comp Real.continuous_cos)
  unfold frameMat
  fin_cases a <;> fin_cases b <;> simp <;> fun_prop

theorem frame_vec_norm (θ : ℝ) (b : Fin 3) : ‖(![radialUnit θ, angularUnit θ, axialUnit] b : Space)‖ ≤ 2 := by
  have h1 : ∀ (i j : Fin 3) (x y : ℝ), |x| ≤ 1 → |y| ≤ 1 →
      ‖(EuclideanSpace.single i x + EuclideanSpace.single j y : EuclideanSpace ℝ (Fin 3))‖ ≤ 2 := by
    intro i j x y hx hy
    refine (norm_add_le _ _).trans ?_
    rw [PiLp.norm_single, PiLp.norm_single, Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  fin_cases b
  · exact h1 0 1 _ _ (Real.abs_cos_le_one θ) (Real.abs_sin_le_one θ)
  · exact h1 0 1 _ _ (by rw [abs_neg]; exact Real.abs_sin_le_one θ) (Real.abs_cos_le_one θ)
  · show ‖axialUnit‖ ≤ 2
    unfold axialUnit
    rw [PiLp.norm_single]
    norm_num

theorem frameMat_bound (θ : ℝ) (M : Space →L[ℝ] Space) (a b : Fin 3) : ‖frameMat θ M a b‖ ≤ 4 * ‖M‖ := by
  unfold frameMat
  rw [Real.norm_eq_abs]
  have h1 := abs_real_inner_le_norm (M (![radialUnit θ, angularUnit θ, axialUnit] b)) (![radialUnit θ, angularUnit θ, axialUnit] a)
  have h2 := M.le_opNorm (![radialUnit θ, angularUnit θ, axialUnit] b)
  have h3 := frame_vec_norm θ a
  have h4 := frame_vec_norm θ b
  have h5 := norm_nonneg M
  have h6 := norm_nonneg (M (![radialUnit θ, angularUnit θ, axialUnit] b))
  nlinarith


theorem regular_of (K : CellBox) {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O) {E : Type}
    [NormedAddCommGroup E] [ProperSpace E] (X : (ℝ × ℝ) × ℝ → E)
    (hX : AEStronglyMeasurable X ((volume.restrict K.rect).prod volume)) (R : ℝ)
    (hR : ∀ p ∈ K.rect, ∀ θ : ℝ, ‖X (p, θ)‖ ≤ R) (Φ : (i : I) → O → Fin (T.dim i) → E → ℂ)
    (hΦ : ∀ i o c, Continuous (Φ i o c)) (hm : ∀ i o c p θ, T.mult i o c p θ = Φ i o c (X (p, θ))) :
    IsTailRegular K T where
  mult_measurable i o c := by
    have e : (fun q : (ℝ × ℝ) × ℝ => T.mult i o c q.1 q.2) = fun q => Φ i o c (X q) :=
      funext (fun q => hm i o c q.1 q.2)
    rw [e]
    exact (hΦ i o c).comp_aestronglyMeasurable hX
  mult_bounded i o c := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn (hΦ i o c).continuousOn
    exact ⟨C, fun p hp θ => by
      rw [hm]
      exact hC _ (mem_closedBall_zero_iff.mpr (hR p hp θ))⟩

theorem entry_meas (hcyl : CylinderCompStatement) (K : CellBox) (f : Space → (Space →L[ℝ] Space))
    (hf : AEStronglyMeasurable f volume) (a b : Fin 3) :
    AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => ((frameMat q.2 (f (cylPoint q.1.1 q.2 q.1.2)) a b : ℝ) : ℂ))
      ((volume.restrict K.rect).prod volume) := by
  have hac : (volume.restrict K.rect).prod (volume : Measure ℝ) ≪ (volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ) :=
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).prod (Measure.AbsolutelyContinuous.refl _)
  have h0 : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => f (cylPoint q.1.1 q.2 q.1.2))
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]
    exact hcyl f hf
  have h1 := h0.mono_ac hac
  have h2 : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => (f (cylPoint q.1.1 q.2 q.1.2), q.2))
      ((volume.restrict K.rect).prod volume) := h1.prodMk continuous_snd.aestronglyMeasurable
  have hcont : Continuous (fun x : (Space →L[ℝ] Space) × ℝ => ((frameMat x.2 x.1 a b : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (frameMat_continuous a b)
  have h3 := hcont.comp_aestronglyMeasurable h2
  exact h3

theorem mat_meas {μ : Measure ((ℝ × ℝ) × ℝ)} (g : (ℝ × ℝ) × ℝ → Fin 3 → Fin 3 → ℂ)
    (h : ∀ a b, AEStronglyMeasurable (fun q => g q a b) μ) : AEStronglyMeasurable g μ := by
  rw [aestronglyMeasurable_iff_aemeasurable]
  exact aemeasurable_pi_lambda _ (fun a => aemeasurable_pi_lambda _ (fun b => (h a b).aemeasurable))

theorem rHat_measurable (K : CellBox) : Measurable (fun p : ℝ × ℝ => CellScalars.rHat K p) := by
  unfold CellScalars.rHat
  exact measurable_fst.div ((lineWeight_continuous K).measurable.comp measurable_fst)

theorem rHat_bound (K : CellBox) (hK : IsCellBox K) (p : ℝ × ℝ) (hp : p ∈ K.rect) :
    |CellScalars.rHat K p| ≤ max 1 K.r₂ := by
  have h0 : 0 ≤ p.1 := hK.r_order.1.trans hp.1.1
  unfold CellScalars.rHat CellBox.lineWeight
  split_ifs
  · rw [abs_div]
    exact (div_self_le_one _).trans (le_max_left _ _)
  · rw [div_one, abs_of_nonneg h0]
    exact hp.1.2.trans (le_max_right _ _)

theorem cyl_mem (K : CellBox) (hK : IsCellBox K) (p : ℝ × ℝ) (hp : p ∈ K.rect) (θ : ℝ) :
    cylPoint p.1 θ p.2 ∈ K.solid := by
  have h0 : 0 ≤ p.1 := hK.r_order.1.trans hp.1.1
  have hz : 0 ≤ p.2 := hK.z_order.1.trans hp.2.1
  have e0 : (cylPoint p.1 θ p.2) 0 = p.1 * Real.cos θ := by simp [cylPoint]
  have e1 : (cylPoint p.1 θ p.2) 1 = p.1 * Real.sin θ := by simp [cylPoint]
  have e2 : (cylPoint p.1 θ p.2) 2 = p.2 := by simp [cylPoint]
  have hr : cylRadius (cylPoint p.1 θ p.2) = p.1 := by
    unfold cylRadius
    rw [e0, e1]
    have : (p.1 * Real.cos θ) ^ 2 + (p.1 * Real.sin θ) ^ 2 = p.1 ^ 2 := by
      have := Real.sin_sq_add_cos_sq θ
      nlinarith
    rw [this, Real.sqrt_sq h0]
  have hh : |cylHeight (cylPoint p.1 θ p.2)| = p.2 := by
    unfold cylHeight
    rw [e2, abs_of_nonneg hz]
  simp only [CellBox.solid, Set.mem_setOf_eq]
  rw [hr, hh]
  exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩

theorem mat_bound (M : Space →L[ℝ] Space) (C : ℝ) (hM : ‖M‖ ≤ C) (θ : ℝ) :
    ‖(fun a b => ((frameMat θ M a b : ℝ) : ℂ) : Fin 3 → Fin 3 → ℂ)‖ ≤ 4 * C := by
  have hC : 0 ≤ 4 * C := by linarith [norm_nonneg M]
  refine (pi_norm_le_iff_of_nonneg hC).mpr (fun a => (pi_norm_le_iff_of_nonneg hC).mpr (fun b => ?_))
  rw [Complex.norm_real]
  linarith [frameMat_bound θ M a b]

end MeshFarRegularInternal

open MeshFarRegularInternal in
theorem farRegular_of (hcyl : CylinderCompStatement) : FarRegularStatement := by
  intro α hα1 hα2 k N c hc K S F hK hsol hS
  obtain ⟨Cm, hCm⟩ := hc.model_bounded
  have hmS := hc.model_measurable.2.2.1
  have hmG := hc.model_measurable.2.2.2
  have hin : ∀ p ∈ K.rect, ∀ θ : ℝ, cylPoint p.1 θ p.2 ∈ c.cellRegion := fun p hp θ => hsol (cyl_mem K hK p hp θ)
  have hSm : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => CellScalars.strainAt c q.1 q.2)
      ((volume.restrict K.rect).prod volume) :=
    mat_meas _ (fun a b => entry_meas hcyl K c.modelStrain hmS a b)
  have hGm : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => CellScalars.curlGradAt c q.1 q.2)
      ((volume.restrict K.rect).prod volume) :=
    mat_meas _ (fun a b => entry_meas hcyl K c.modelCurlGrad hmG a b)
  have hSb : ∀ p ∈ K.rect, ∀ θ : ℝ, ‖CellScalars.strainAt c p θ‖ ≤ 4 * Cm :=
    fun p hp θ => mat_bound _ Cm (hCm _ (hin p hp θ)).2.2.1 θ
  have hGb : ∀ p ∈ K.rect, ∀ θ : ℝ, ‖CellScalars.curlGradAt c p θ‖ ≤ 4 * Cm :=
    fun p hp θ => mat_bound _ Cm (hCm _ (hin p hp θ)).2.2.2 θ
  have hρ1 : Measurable (fun q : (ℝ × ℝ) × ℝ => ((CellScalars.rHat K q.1 : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp ((rHat_measurable K).comp measurable_fst)
  have hρ2 : Measurable (fun q : (ℝ × ℝ) × ℝ => ((q.1.1 * CellScalars.rHat K q.1 : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp ((measurable_fst.comp measurable_fst).mul ((rHat_measurable K).comp measurable_fst))
  refine ⟨?_, ?_, ?_⟩
  · refine regular_of K _ (fun q => (((CellScalars.rHat K q.1 : ℝ) : ℂ), CellScalars.strainAt c q.1 q.2,
      CellScalars.curlGradAt c q.1 q.2))
      (hρ1.aestronglyMeasurable.prodMk (hSm.prodMk hGm)) (max (max 1 K.r₂) (4 * Cm)) ?_
      (fun i o c' x => x.1 * (if i = 0 then -curlAdj (matVec x.2.1 (CellScalars.unitVec3 c')) o.1 o.2
        else (1 / 2 : ℂ) * couplingMap x.2.2 (CellScalars.unitVec3 c') o.1 o.2)) ?_ (fun i o c' p θ => rfl)
    · intro p hp θ
      refine norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_, ?_⟩⟩
      · rw [Complex.norm_real, Real.norm_eq_abs]
        exact (rHat_bound K hK p hp).trans (le_max_left _ _)
      · exact (hSb p hp θ).trans (le_max_right _ _)
      · exact (hGb p hp θ).trans (le_max_right _ _)
    · intro i o c'
      by_cases hi : i = 0
      · simp only [hi, if_true]
        unfold curlAdj matVec
        fun_prop
      · simp only [hi, if_false]
        unfold couplingMap bracketMat
        fun_prop
  · refine regular_of K _ (fun q => (((CellScalars.rHat K q.1 : ℝ) : ℂ), CellScalars.strainAt c q.1 q.2,
      CellScalars.curlGradAt c q.1 q.2))
      (hρ1.aestronglyMeasurable.prodMk (hSm.prodMk hGm)) (max (max 1 K.r₂) (4 * Cm)) ?_
      (fun _ o e x => x.1 * waveActionVelocity x.2.2 (CellScalars.unitMat e) o) ?_ (fun i o e p θ => rfl)
    · intro p hp θ
      refine norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_, ?_⟩⟩
      · rw [Complex.norm_real, Real.norm_eq_abs]
        exact (rHat_bound K hK p hp).trans (le_max_left _ _)
      · exact (hSb p hp θ).trans (le_max_right _ _)
      · exact (hGb p hp θ).trans (le_max_right _ _)
    · intro i o e
      unfold waveActionVelocity couplingAdj
      fun_prop
  · refine regular_of K _ (fun q => (((q.1.1 * CellScalars.rHat K q.1 : ℝ) : ℂ), CellScalars.strainAt c q.1 q.2,
      CellScalars.curlGradAt c q.1 q.2))
      (hρ2.aestronglyMeasurable.prodMk (hSm.prodMk hGm)) (max (K.r₂ * max 1 K.r₂) (4 * Cm)) ?_
      (fun _ o e x => x.1 * waveActionVelocity x.2.2 (CellScalars.unitMat e) o) ?_ (fun i o e p θ => rfl)
    · intro p hp θ
      refine norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_, ?_⟩⟩
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
        have h0 : 0 ≤ p.1 := hK.r_order.1.trans hp.1.1
        rw [abs_of_nonneg h0]
        exact (mul_le_mul hp.1.2 (rHat_bound K hK p hp) (abs_nonneg _) (h0.trans hp.1.2)).trans (le_max_left _ _)
      · exact (hSb p hp θ).trans (le_max_right _ _)
      · exact (hGb p hp θ).trans (le_max_right _ _)
    · intro i o e
      unfold waveActionVelocity couplingAdj
      fun_prop

end CellAnalysis

end CellCert

end Breakdown
