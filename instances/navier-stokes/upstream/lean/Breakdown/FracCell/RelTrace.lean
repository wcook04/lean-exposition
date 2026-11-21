import Breakdown.FracCell.StCoordsProof
import Breakdown.FracCell.CylIntegral

open MeasureTheory Real Set

noncomputable section

namespace Breakdown.CellCert.CellFormula

namespace Internal.RelTrace

open SteadyCert Assembly CellAnalysis Spectral.Internal.CylIntegral

def cylF (x : (ℝ × ℝ) × ℝ) : Space := cylPoint x.1.1 x.2 x.1.2

theorem cylF_eq (x : (ℝ × ℝ) × ℝ) :
    cylF x = toSpace ((x.1.1 * Real.cos x.2, x.1.1 * Real.sin x.2), x.1.2) :=
  (toSpace_apply _ _ _).symm

theorem measurable_cylF : Measurable cylF := by
  have : cylF = fun x => toSpace ((x.1.1 * Real.cos x.2, x.1.1 * Real.sin x.2), x.1.2) := funext cylF_eq
  rw [this]
  exact toSpace.measurable.comp (by fun_prop)

def region : Set ((ℝ × ℝ) × ℝ) := (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioo (-π) π

theorem measurableSet_region : MeasurableSet region :=
  (measurableSet_Ioi.prod MeasurableSet.univ).prod measurableSet_Ioo

theorem lintegral_cyl (h : Space → ENNReal) :
    ∫⁻ x in region, ENNReal.ofReal x.1.1 * h (cylF x) = ∫⁻ y, h y := by
  calc ∫⁻ x in region, ENNReal.ofReal x.1.1 * h (cylF x)
      = ∫⁻ x in swapEquiv ⁻¹' cylMap.target,
          ENNReal.ofReal |(cylDeriv (swapEquiv x)).det| * h (toSpace (cylMap.symm (swapEquiv x))) := by
        rw [swapEquiv_preimage]
        refine setLIntegral_congr_fun measurableSet_region (fun x hx => ?_)
        have hx' : swapEquiv x ∈ cylMap.target := by
          rw [← Set.mem_preimage, swapEquiv_preimage]; exact hx
        rw [abs_det_eq hx']
        obtain ⟨⟨r, z⟩, θ⟩ := x
        simp only [swapEquiv_apply, cylF]
        rw [show cylMap.symm ((r, θ), z) = ((r * Real.cos θ, r * Real.sin θ), z) from rfl, toSpace_apply]
        rfl
    _ = ∫⁻ x in cylMap.target, ENNReal.ofReal |(cylDeriv x).det| * h (toSpace (cylMap.symm x)) :=
        swapEquiv_mp.setLIntegral_comp_preimage_emb swapEquiv.measurableEmbedding
          (fun x => ENNReal.ofReal |(cylDeriv x).det| * h (toSpace (cylMap.symm x))) cylMap.target
    _ = ∫⁻ w in cylMap.symm '' cylMap.target, h (toSpace w) :=
        (lintegral_image_eq_lintegral_abs_det_fderiv_mul volume cylMap.open_target.measurableSet
          (fun x _ => (hasDeriv x).hasFDerivWithinAt) cylMap.symm.injOn (fun w => h (toSpace w))).symm
    _ = ∫⁻ w, h (toSpace w) := by rw [setLIntegral_congr image_ae, setLIntegral_univ]
    _ = ∫⁻ y, h y := toSpace_mp.lintegral_comp_emb toSpace.measurableEmbedding h

theorem region_null {N : Set Space} (hN : MeasurableSet N) (h0 : volume N = 0) :
    volume.restrict region (cylF ⁻¹' N) = 0 := by
  have hl : ∫⁻ x in region, ENNReal.ofReal x.1.1 * N.indicator 1 (cylF x) = 0 := by
    rw [lintegral_cyl, lintegral_indicator_one hN, h0]
  have hm : Measurable (fun x : (ℝ × ℝ) × ℝ => ENNReal.ofReal x.1.1 * N.indicator 1 (cylF x)) :=
    (ENNReal.measurable_ofReal.comp measurable_fst.fst).mul
      ((measurable_one.indicator hN).comp measurable_cylF)
  rw [lintegral_eq_zero_iff hm] at hl
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hl, ae_restrict_mem measurableSet_region] with x hx hxR
  intro hxN
  have hr : 0 < x.1.1 := hxR.1.1
  simp only [Pi.zero_apply, mem_preimage] at hx hxN
  rw [Set.indicator_of_mem hxN] at hx
  simp at hx
  linarith

theorem qmp_region : Measure.QuasiMeasurePreserving cylF (volume.restrict region) volume :=
  ⟨measurable_cylF, Measure.AbsolutelyContinuous.mk fun s hs h0 => by
    rw [Measure.map_apply measurable_cylF hs]; exact region_null hs h0⟩

theorem axis_null : volume {x : (ℝ × ℝ) × ℝ | x.1.1 = 0} = 0 := by
  have : {x : (ℝ × ℝ) × ℝ | x.1.1 = 0} = ({0} ×ˢ univ) ×ˢ univ := by ext x; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]
  simp

theorem restrict_le (K : CellBox) (hK : IsCellBox K) :
    volume.restrict (K.rect ×ˢ Ioo (-π) π) ≤ volume.restrict region := by
  refine Measure.restrict_mono_ae ?_
  have := measure_eq_zero_iff_ae_notMem.mp axis_null
  filter_upwards [this] with x hx
  intro hxD
  have hx' : x.1.1 ≠ 0 := hx
  have hxD' : x ∈ K.rect ×ˢ Ioo (-π) π := hxD
  change x ∈ region
  simp only [CellBox.rect, mem_prod, mem_Icc] at hxD'
  exact ⟨⟨lt_of_le_of_ne (le_trans hK.r_order.1 hxD'.1.1.1) (Ne.symm hx'), mem_univ _⟩, hxD'.2⟩

theorem mode_window (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (a b : Fin 3) (p : ℝ × ℝ) :
    gradMode m n G a b p = (1 / (2 * Real.pi) : ℂ) * ∫ θ in Ioo (-π) π,
      Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * (frameMat θ (G (cylPoint p.1 θ p.2)) a b : ℂ) := by
  set g : ℝ → ℂ := fun θ => Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
    (frameMat θ (G (cylPoint p.1 θ p.2)) a b : ℂ) with hg
  have hper : Function.Periodic g (2 * π) := by
    intro θ
    simp only [hg]
    have h1 : cylPoint p.1 (θ + 2 * π) p.2 = cylPoint p.1 θ p.2 := by
      simp [cylPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]
    have h2 : ∀ M, frameMat (θ + 2 * π) M = frameMat θ M := by
      intro M; funext a b
      simp [frameMat, radialUnit, angularUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]
    have h3 : Complex.exp (-(azimuth m n * (θ + 2 * π) : ℝ) * Complex.I) =
        Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) := by
      have : (-(azimuth m n * (θ + 2 * π) : ℝ) * Complex.I) =
          (-(azimuth m n * θ : ℝ) * Complex.I) + ((-((n * m : ℤ))) : ℤ) * (2 * π * Complex.I) := by
        simp only [azimuth]; push_cast; ring
      rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [h1, h2, h3]
  have h := hper.intervalIntegral_add_eq 0 (-π)
  rw [zero_add, show -π + 2 * π = π by ring] at h
  have e : gradMode m n G a b p = (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), g θ := rfl
  rw [e, h, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]

end Internal.RelTrace

end Breakdown.CellCert.CellFormula

namespace Breakdown.CellCert.CellFormula

namespace Internal.RelTrace

open SteadyCert Assembly CellAnalysis

def ent (M : Space →L[ℝ] Space) (i j : Fin 3) : ℝ := inner ℝ (M (unitVector j)) (unitVector i)

def diagExp (θ : ℝ) (M : Space →L[ℝ] Space) : Fin 3 → ℝ :=
  ![Real.cos θ ^ 2 * ent M 0 0 + Real.cos θ * Real.sin θ * (ent M 0 1 + ent M 1 0) + Real.sin θ ^ 2 * ent M 1 1,
    Real.sin θ ^ 2 * ent M 0 0 + (-(Real.cos θ * Real.sin θ)) * (ent M 0 1 + ent M 1 0) + Real.cos θ ^ 2 * ent M 1 1,
    ent M 2 2]

theorem radialUnit_eq (θ : ℝ) : radialUnit θ = Real.cos θ • unitVector 0 + Real.sin θ • unitVector 1 := by
  ext i; fin_cases i <;> simp [radialUnit, unitVector]

theorem angularUnit_eq (θ : ℝ) : angularUnit θ = (-Real.sin θ) • unitVector 0 + Real.cos θ • unitVector 1 := by
  ext i; fin_cases i <;> simp [angularUnit, unitVector]

theorem axialUnit_eq : axialUnit = unitVector 2 := by
  ext i; fin_cases i <;> simp [axialUnit, unitVector]

theorem frameMat_diag (θ : ℝ) (M : Space →L[ℝ] Space) (a : Fin 3) : frameMat θ M a a = diagExp θ M a := by
  fin_cases a <;>
  simp [frameMat, diagExp, ent, radialUnit_eq, angularUnit_eq, axialUnit_eq, map_add, map_smul,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right] <;> ring

theorem diag_sum (θ : ℝ) (M : Space →L[ℝ] Space) : ∑ a, diagExp θ M a = ∑ i, ent M i i := by
  simp only [Fin.sum_univ_three, diagExp]
  simp
  linear_combination (ent M 0 0 + ent M 1 1) * Real.sin_sq_add_cos_sq θ

theorem abs_ent_le (M : Space →L[ℝ] Space) (i j : Fin 3) : |ent M i j| ≤ ‖M (unitVector j)‖ := by
  have h := abs_real_inner_le_norm (M (unitVector j)) (unitVector i)
  have hu : ‖unitVector i‖ = 1 := by simp [unitVector]
  rw [hu, mul_one] at h
  exact h

theorem abs_mul_le_of (t u : ℝ) (h : |t| ≤ 1) : |t * u| ≤ |u| := by
  rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) h

theorem abs_diag_le (θ : ℝ) (M : Space →L[ℝ] Space) (a : Fin 3) :
    |diagExp θ M a| ≤ 5 + 2 * entrySq M := by
  have hc : |Real.cos θ ^ 2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg _)]; exact Real.cos_sq_le_one θ
  have hs : |Real.sin θ ^ 2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg _)]; exact Real.sin_sq_le_one θ
  have hcs : |Real.cos θ * Real.sin θ| ≤ 1 := by
    rw [abs_mul]; exact mul_le_one₀ (Real.abs_cos_le_one θ) (abs_nonneg _) (Real.abs_sin_le_one θ)
  have hcs' : |(-(Real.cos θ * Real.sin θ))| ≤ 1 := by rw [abs_neg]; exact hcs
  have e00 := abs_ent_le M 0 0
  have e01 := abs_ent_le M 0 1
  have e10 := abs_ent_le M 1 0
  have e11 := abs_ent_le M 1 1
  have e22 := abs_ent_le M 2 2
  have q : ∀ j, ‖M (unitVector j)‖ ≤ 1 + ‖M (unitVector j)‖ ^ 2 := fun j => by
    nlinarith [sq_nonneg (‖M (unitVector j)‖ - 1)]
  have hE : entrySq M = ‖M (unitVector 0)‖ ^ 2 + ‖M (unitVector 1)‖ ^ 2 + ‖M (unitVector 2)‖ ^ 2 := by
    simp [entrySq, Fin.sum_univ_three]
  have h01 := abs_add_le (ent M 0 1) (ent M 1 0)
  have q0 := q 0
  have q1 := q 1
  have q2 := q 2
  have s0 := sq_nonneg ‖M (unitVector 0)‖
  have s1 := sq_nonneg ‖M (unitVector 1)‖
  have s2 := sq_nonneg ‖M (unitVector 2)‖
  fin_cases a
  · have h3 := abs_add_three (Real.cos θ ^ 2 * ent M 0 0) (Real.cos θ * Real.sin θ * (ent M 0 1 + ent M 1 0))
      (Real.sin θ ^ 2 * ent M 1 1)
    have hA := abs_mul_le_of _ (ent M 0 0) hc
    have hB := abs_mul_le_of _ (ent M 0 1 + ent M 1 0) hcs
    have hC := abs_mul_le_of _ (ent M 1 1) hs
    simp only [diagExp, Fin.zero_eta, Matrix.cons_val_zero]
    linarith
  · have h3 := abs_add_three (Real.sin θ ^ 2 * ent M 0 0) ((-(Real.cos θ * Real.sin θ)) * (ent M 0 1 + ent M 1 0))
      (Real.cos θ ^ 2 * ent M 1 1)
    have hA := abs_mul_le_of _ (ent M 0 0) hs
    have hB := abs_mul_le_of _ (ent M 0 1 + ent M 1 0) hcs'
    have hC := abs_mul_le_of _ (ent M 1 1) hc
    simp only [diagExp, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith
  · simp only [diagExp]
    simp
    linarith

end Internal.RelTrace

end Breakdown.CellCert.CellFormula

namespace Breakdown.CellCert.CellFormula

namespace Internal.RelTrace

open SteadyCert Assembly CellAnalysis

theorem norm_cyl_le (r θ z : ℝ) : ‖cylPoint r θ z‖ ≤ 2 * |r| + |z| := by
  unfold cylPoint
  refine (norm_add₃_le).trans ?_
  simp only [PiLp.norm_single, Real.norm_eq_abs, abs_mul]
  have h1 := mul_le_of_le_one_right (abs_nonneg r) (Real.abs_cos_le_one θ)
  have h2 := mul_le_of_le_one_right (abs_nonneg r) (Real.abs_sin_le_one θ)
  linarith

theorem norm_coef_le : ‖(1 / (2 * Real.pi) : ℂ)‖ ≤ 1 := by
  rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity), div_le_one (by positivity)]
  linarith [Real.pi_gt_three]

def wPoly (K : CellBox) (B : CellBases) (j l : ℕ) (p : ℝ × ℝ) : ℝ :=
  K.lineWeight p.1 * (B.radialPoly j p.1 * B.heightPoly l p.2)

def phase (m : ℕ) (n : ℤ) (θ : ℝ) : ℂ := Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I)

def phi (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (K : CellBox) (B : CellBases) (j l : ℕ)
    (a : Fin 3) (x : (ℝ × ℝ) × ℝ) : ℂ :=
  (wPoly K B j l x.1 : ℂ) * ((1 / (2 * Real.pi) : ℂ) * (phase m n x.2 * (diagExp x.2 (G (cylF x)) a : ℂ)))

theorem continuous_poly (B : CellBases) (j l : ℕ) :
    Continuous (fun p : ℝ × ℝ => B.radialPoly j p.1 * B.heightPoly l p.2) := by
  simp only [CellBases.radialPoly, CellBases.heightPoly]
  fun_prop

theorem continuous_wPoly (K : CellBox) (B : CellBases) (j l : ℕ) : Continuous (wPoly K B j l) := by
  have h := continuous_poly B j l
  unfold wPoly CellBox.lineWeight
  split_ifs
  · exact continuous_fst.mul h
  · exact continuous_const.mul h

theorem continuous_phase (m : ℕ) (n : ℤ) : Continuous (phase m n) := by
  unfold phase; fun_prop

theorem continuous_ent (i j : Fin 3) : Continuous (fun M : Space →L[ℝ] Space => ent M i j) := by
  unfold ent
  exact ((ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous).inner continuous_const

theorem continuous_diag {X : Type*} [TopologicalSpace X] {f : X → ℝ} {g : X → (Space →L[ℝ] Space)}
    (hf : Continuous f) (hg : Continuous g) (a : Fin 3) :
    Continuous (fun x => diagExp (f x) (g x) a) := by
  have e : ∀ i j : Fin 3, Continuous (fun x => ent (g x) i j) :=
    fun i j => (continuous_ent i j).comp hg
  have c : Continuous (fun x => Real.cos (f x)) := Real.continuous_cos.comp hf
  have s : Continuous (fun x => Real.sin (f x)) := Real.continuous_sin.comp hf
  fin_cases a
  · exact ((c.pow 2).mul (e 0 0)).add ((c.mul s).mul ((e 0 1).add (e 1 0))) |>.add ((s.pow 2).mul (e 1 1))
  · exact ((s.pow 2).mul (e 0 0)).add ((c.mul s).neg.mul ((e 0 1).add (e 1 0))) |>.add ((c.pow 2).mul (e 1 1))
  · exact e 2 2

theorem aesm_phi (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (K : CellBox) (B : CellBases) (j l : ℕ)
    (a : Fin 3) (μ : Measure ((ℝ × ℝ) × ℝ))
    (hGc : AEStronglyMeasurable (fun x => G (cylF x)) μ) :
    AEStronglyMeasurable (phi m n G K B j l a) μ := by
  have hd : Continuous (fun q : ((ℝ × ℝ) × ℝ) × (Space →L[ℝ] Space) => diagExp q.1.2 q.2 a) :=
    continuous_diag (f := fun q : ((ℝ × ℝ) × ℝ) × (Space →L[ℝ] Space) => q.1.2)
      (g := fun q : ((ℝ × ℝ) × ℝ) × (Space →L[ℝ] Space) => q.2) (continuous_snd.comp continuous_fst) continuous_snd a
  have hF : Continuous (fun q : ((ℝ × ℝ) × ℝ) × (Space →L[ℝ] Space) =>
      (wPoly K B j l q.1.1 : ℂ) * ((1 / (2 * Real.pi) : ℂ) * (phase m n q.1.2 * (diagExp q.1.2 q.2 a : ℂ)))) :=
    (Complex.continuous_ofReal.comp ((continuous_wPoly K B j l).comp (continuous_fst.comp continuous_fst))).mul
      (continuous_const.mul (((continuous_phase m n).comp (continuous_snd.comp continuous_fst)).mul
        (Complex.continuous_ofReal.comp hd)))
  have hp : AEStronglyMeasurable (fun x : (ℝ × ℝ) × ℝ => (x, G (cylF x))) μ :=
    aestronglyMeasurable_id.prodMk hGc
  exact hF.comp_aestronglyMeasurable hp

theorem wPoly_bound (K : CellBox) (hK : IsCellBox K) (B : CellBases) (j l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K.rect, |wPoly K B j l p| ≤ C * p.1 := by
  have hrc : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  obtain ⟨Mb, hMb⟩ := hrc.exists_bound_of_continuousOn (continuous_poly B j l).continuousOn
  refine ⟨max Mb 0 * max 1 (1 / K.r₁), mul_nonneg (le_max_right _ _) (le_trans zero_le_one (le_max_left _ _)),
    fun p hp => ?_⟩
  have hb0 : |B.radialPoly j p.1 * B.heightPoly l p.2| ≤ Mb := by
    simpa [Real.norm_eq_abs] using hMb p hp
  have hb : |B.radialPoly j p.1 * B.heightPoly l p.2| ≤ max Mb 0 := hb0.trans (le_max_left _ _)
  have hr1 : K.r₁ ≤ p.1 := hp.1.1
  have hp1 : 0 ≤ p.1 := le_trans hK.r_order.1 hr1
  unfold wPoly CellBox.lineWeight
  split_ifs with h0
  · rw [abs_mul, abs_of_nonneg hp1]
    have hMC : max Mb 0 ≤ max Mb 0 * max 1 (1 / K.r₁) :=
      le_mul_of_one_le_right (le_max_right _ _) (le_max_left _ _)
    calc p.1 * _ ≤ p.1 * max Mb 0 := mul_le_mul_of_nonneg_left hb hp1
      _ ≤ p.1 * (max Mb 0 * max 1 (1 / K.r₁)) := mul_le_mul_of_nonneg_left hMC hp1
      _ = _ := mul_comm _ _
  · have hr0 : 0 < K.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h0)
    rw [one_mul]
    have h1 : 1 ≤ (1 / K.r₁) * p.1 := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hr0]; linarith
    have h2 : (1 / K.r₁) ≤ max 1 (1 / K.r₁) := le_max_right _ _
    calc |_| ≤ max Mb 0 := hb
      _ ≤ max Mb 0 * ((1 / K.r₁) * p.1) := le_mul_of_one_le_right (le_max_right _ _) h1
      _ ≤ max Mb 0 * (max 1 (1 / K.r₁) * p.1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hp1) (le_max_right _ _)
      _ = _ := by ring

theorem integrableOn_phi (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (hG : AEStronglyMeasurable G volume)
    (hG2 : Integrable (fun y => entrySq (G y))) (K : CellBox) (hK : IsCellBox K) (B : CellBases) (j l : ℕ)
    (a : Fin 3) : IntegrableOn (phi m n G K B j l a) (K.rect ×ˢ Ioo (-π) π) := by
  have hDm : MeasurableSet (K.rect ×ˢ Ioo (-π) π) :=
    (measurableSet_Icc.prod measurableSet_Icc).prod measurableSet_Ioo
  have hQ : Measure.QuasiMeasurePreserving cylF (volume.restrict (K.rect ×ˢ Ioo (-π) π)) volume :=
    qmp_region.mono_left (Measure.absolutelyContinuous_of_le (restrict_le K hK))
  obtain ⟨C, hC0, hPb⟩ := wPoly_bound K hK B j l
  have hfinh : ∫⁻ y, (Metric.closedBall (0 : Space) (2 * K.r₂ + K.z₂)).indicator
      (fun y => ENNReal.ofReal (5 + 2 * entrySq (G y))) y < ⊤ := by
    rw [lintegral_indicator Metric.isClosed_closedBall.measurableSet]
    have hi : Integrable (fun y => 5 + 2 * entrySq (G y))
        (volume.restrict (Metric.closedBall (0 : Space) (2 * K.r₂ + K.z₂))) :=
      (integrableOn_const measure_closedBall_lt_top.ne).add
        (hG2.integrableOn.const_mul 2)
    exact hi.lintegral_lt_top
  refine ⟨aesm_phi m n G K B j l a _ (hG.comp_quasiMeasurePreserving hQ), ?_⟩
  have hpt : ∀ᵐ x ∂(volume.restrict (K.rect ×ˢ Ioo (-π) π)),
      ‖phi m n G K B j l a x‖ₑ ≤ ENNReal.ofReal C * (ENNReal.ofReal x.1.1 *
        (Metric.closedBall (0 : Space) (2 * K.r₂ + K.z₂)).indicator
          (fun y => ENNReal.ofReal (5 + 2 * entrySq (G y))) (cylF x)) := by
    filter_upwards [ae_restrict_mem hDm] with x hx
    have hx1 : x.1 ∈ K.rect := hx.1
    have hr : 0 ≤ x.1.1 := le_trans hK.r_order.1 hx1.1.1
    have hz : 0 ≤ x.1.2 := le_trans hK.z_order.1 hx1.2.1
    have hball : cylF x ∈ Metric.closedBall (0 : Space) (2 * K.r₂ + K.z₂) := by
      rw [mem_closedBall_zero_iff]
      refine (norm_cyl_le _ _ _).trans ?_
      rw [abs_of_nonneg hr, abs_of_nonneg hz]
      linarith [hx1.1.2, hx1.2.2]
    rw [Set.indicator_of_mem hball, ← ENNReal.ofReal_mul hr, ← ENNReal.ofReal_mul hC0,
      ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    have hnE : ‖phase m n x.2‖ = 1 := by simp [phase, Complex.norm_exp]
    calc ‖phi m n G K B j l a x‖ = |wPoly K B j l x.1| * (‖(1 / (2 * Real.pi) : ℂ)‖ *
          (‖phase m n x.2‖ * |diagExp x.2 (G (cylF x)) a|)) := by
          simp only [phi, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (C * x.1.1) * (1 * (1 * (5 + 2 * entrySq (G (cylF x))))) := by
          rw [hnE]
          refine mul_le_mul (hPb _ hx1) (mul_le_mul norm_coef_le ?_ (by positivity) zero_le_one)
            (by positivity) (by positivity)
          rw [one_mul, one_mul]; exact abs_diag_le _ _ _
      _ = C * (x.1.1 * (5 + 2 * entrySq (G (cylF x)))) := by ring
  show ∫⁻ x in K.rect ×ˢ Ioo (-π) π, ‖phi m n G K B j l a x‖ₑ < ⊤
  calc ∫⁻ x in K.rect ×ˢ Ioo (-π) π, ‖phi m n G K B j l a x‖ₑ
      ≤ ∫⁻ x in K.rect ×ˢ Ioo (-π) π, ENNReal.ofReal C * (ENNReal.ofReal x.1.1 *
        (Metric.closedBall (0 : Space) (2 * K.r₂ + K.z₂)).indicator
          (fun y => ENNReal.ofReal (5 + 2 * entrySq (G y))) (cylF x)) := lintegral_mono_ae hpt
    _ = ENNReal.ofReal C * ∫⁻ x in K.rect ×ˢ Ioo (-π) π, ENNReal.ofReal x.1.1 *
        (Metric.closedBall (0 : Space) (2 * K.r₂ + K.z₂)).indicator
          (fun y => ENNReal.ofReal (5 + 2 * entrySq (G y))) (cylF x) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * ∫⁻ x in region, ENNReal.ofReal x.1.1 *
        (Metric.closedBall (0 : Space) (2 * K.r₂ + K.z₂)).indicator
          (fun y => ENNReal.ofReal (5 + 2 * entrySq (G y))) (cylF x) := by
        exact mul_le_mul' le_rfl (lintegral_mono' (restrict_le K hK) le_rfl)
    _ = ENNReal.ofReal C * ∫⁻ y, (Metric.closedBall (0 : Space) (2 * K.r₂ + K.z₂)).indicator
          (fun y => ENNReal.ofReal (5 + 2 * entrySq (G y))) y := by rw [lintegral_cyl]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinh

theorem coef_eq (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (K : CellBox) (B : CellBases) (j l : ℕ)
    (a : Fin 3) (hint : IntegrableOn (phi m n G K B j l a) (K.rect ×ˢ Ioo (-π) π)) :
    B.coef K (gradMode m n G a a) j l = ∫ x in K.rect ×ˢ Ioo (-π) π, phi m n G K B j l a x := by
  have h := setIntegral_prod (phi m n G K B j l a) hint
  rw [show (∫ x in K.rect ×ˢ Ioo (-π) π, phi m n G K B j l a x) =
    ∫ p in K.rect, ∫ θ in Ioo (-π) π, phi m n G K B j l a (p, θ) from h]
  unfold CellBases.coef
  refine setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) (fun p _ => ?_)
  rw [mode_window]
  simp only [phi, phase, wPoly, frameMat_diag, cylF]
  rw [integral_const_mul, integral_const_mul]
  push_cast
  ring

theorem trace_coef (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (hG : AEStronglyMeasurable G volume)
    (hG2 : Integrable (fun y => entrySq (G y)))
    (hdiv : ∀ᵐ y ∂volume, ∑ i : Fin 3, inner ℝ (G y (unitVector i)) (unitVector i) = 0)
    (K : CellBox) (hK : IsCellBox K) (B : CellBases) (j l : ℕ) :
    ∑ a : Fin 3, B.coef K (gradMode m n G a a) j l = 0 := by
  have hint := integrableOn_phi m n G hG hG2 K hK B j l
  have hQ : Measure.QuasiMeasurePreserving cylF (volume.restrict (K.rect ×ˢ Ioo (-π) π)) volume :=
    qmp_region.mono_left (Measure.absolutelyContinuous_of_le (restrict_le K hK))
  simp_rw [fun a => coef_eq m n G K B j l a (hint a)]
  rw [← integral_finsetSum Finset.univ (fun a _ => hint a)]
  apply integral_eq_zero_of_ae
  filter_upwards [hQ.ae hdiv] with x hx
  have hs : ∑ a : Fin 3, phi m n G K B j l a x = (wPoly K B j l x.1 : ℂ) * ((1 / (2 * Real.pi) : ℂ) *
      (phase m n x.2 * ((∑ a, diagExp x.2 (G (cylF x)) a : ℝ) : ℂ))) := by
    simp only [phi, Fin.sum_univ_three]; push_cast; ring
  rw [hs, diag_sum]
  simp only [ent]
  rw [hx]
  simp

end Internal.RelTrace

end Breakdown.CellCert.CellFormula

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

theorem relTrace_holds : RelTraceStatement := by
  intro k N c K S B L hL x hx ρ
  obtain ⟨n, j, l⟩ := ρ
  have hrow : ∀ d, L.relationRow (Sum.inr (Sum.inr (Sum.inr (Sum.inl (n, j, l))))) d =
      ∑ a : Fin 3, L.unitAt (CellDatum.lowStrain n a a j l) d := by
    intro d
    simp only [CellLayout.relationRow, CellLayout.strainAt, Sum.elim_inr, Sum.elim_inl, j.isLt, l.isLt, and_self,
      dif_pos, Fin.eta, Finset.sum_apply]
  simp only [hrow, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [CellLayout.unitAt, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [CellLayout.trueData, CellDatum.lowStrain, Sum.elim_inl, CellLayout.gradModeOf]
  have hK : IsCellBox L.box := by rw [hL.box_eq]; exact hL.box_valid
  exact Internal.RelTrace.trace_coef L.order n x.2.1 hx.1.measurable_gradient hx.1.gradient_two
    hx.1.divergence L.box hK L.bases j l

end Breakdown.CellCert.CellFormula
