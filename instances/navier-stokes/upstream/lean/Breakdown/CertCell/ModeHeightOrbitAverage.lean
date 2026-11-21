import Breakdown.CertCell.ModeHeightLineSlice
import Breakdown.FracCell.CylModeWeak
import Breakdown.FracCell.RelTrace
import Breakdown.Cert.CoercivePerturbationFactsProof

open scoped ContDiff Topology ENNReal
open MeasureTheory Set Filter

noncomputable section

namespace Breakdown.CertCell.Bridge

namespace Internal.HeightOrbit

open CellCert.CellAnalysis (cylPoint radialUnit axialUnit azimuth)
open CellCert.CellFormula.Internal.RelTrace (region cylF lintegral_cyl measurable_cylF)

def unitAt (q : ℝ × ℝ) : Space := EuclideanSpace.single 0 q.1 + EuclideanSpace.single 1 q.2

theorem unitAt_eq : unitAt = fun q : ℝ × ℝ => q.1 • unitVector 0 + q.2 • unitVector 1 := by
  funext q
  ext i
  fin_cases i <;> simp [unitAt, unitVector]

theorem unitAt_cont : Continuous unitAt := by
  rw [unitAt_eq]
  fun_prop

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialL (L : ℝ × ℝ → (E →L[ℝ] ℝ)) (q : ℝ × ℝ) : (Space →L[ℝ] E) →L[ℝ] ℝ :=
  (L q).comp (ContinuousLinearMap.apply ℝ E (unitAt q))

def axialL (L : ℝ × ℝ → (E →L[ℝ] ℝ)) (q : ℝ × ℝ) : (Space →L[ℝ] E) →L[ℝ] ℝ :=
  (L q).comp (ContinuousLinearMap.apply ℝ E axialUnit)

theorem radialL_cont {L : ℝ × ℝ → (E →L[ℝ] ℝ)} (hL : Continuous L) : Continuous (radialL L) :=
  hL.clm_comp ((ContinuousLinearMap.apply ℝ E).continuous.comp unitAt_cont)

theorem axialL_cont {L : ℝ × ℝ → (E →L[ℝ] ℝ)} (hL : Continuous L) : Continuous (axialL L) :=
  hL.clm_comp continuous_const

def wave (h : ℝ → Space → E) (Λ : ℝ × ℝ → (E →L[ℝ] ℝ)) (n : ℤ) (x : ℝ × (ℝ × ℝ)) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth 1 n * θ : ℝ) * Complex.I) *
    (Λ (Real.cos θ, Real.sin θ) (h x.1 (cylPoint x.2.1 θ x.2.2)) : ℂ)

def timeFactor (k : ℤ) (τ : ℝ) : ℂ := Complex.exp (-(((2 * Real.pi * k * τ : ℝ) : ℂ) * Complex.I))

def waveAvg (h : ℝ → Space → E) (Λ : ℝ × ℝ → (E →L[ℝ] ℝ)) (k n : ℤ) (p : ℝ × ℝ) : ℂ :=
  ∫ τ in (0 : ℝ)..1, timeFactor k τ * wave h Λ n (τ, p)

abbrev boxM (a b c d : ℝ) : Measure ((ℝ × (ℝ × ℝ)) × ℝ) :=
  ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Icc a b ×ˢ Icc c d))).prod
    (volume.restrict (Ioo (-Real.pi) Real.pi))

def orbitPt (w : (ℝ × (ℝ × ℝ)) × ℝ) : ℝ × Space := (w.1.1, cylPoint w.1.2.1 w.2 w.1.2.2)

theorem orbitPt_meas : Measurable orbitPt := by
  have e : orbitPt = fun w : (ℝ × (ℝ × ℝ)) × ℝ => (w.1.1, cylF (w.1.2, w.2)) := rfl
  rw [e]
  exact (measurable_fst.comp measurable_fst).prodMk
    (measurable_cylF.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

theorem boxM_eq (a b c d : ℝ) :
    boxM a b c d = volume.restrict ((Ioc (0 : ℝ) 1 ×ˢ (Icc a b ×ˢ Icc c d)) ×ˢ Ioo (-Real.pi) Real.pi) := by
  unfold boxM
  rw [Measure.prod_restrict, Measure.prod_restrict]
  rfl

theorem cyl_lint_le (Φ : ℝ × Space → ℝ≥0∞) (hΦ : Measurable Φ) {a b c d : ℝ} (ha : 0 < a) :
    ∫⁻ w, Φ (orbitPt w) ∂boxM a b c d ≤ ENNReal.ofReal (1 / a) * ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ y, Φ (τ, y) := by
  have hm : Measurable (fun w => Φ (orbitPt w)) := hΦ.comp orbitPt_meas
  unfold boxM
  rw [lintegral_prod _ hm.aemeasurable, lintegral_prod _ hm.lintegral_prod_right'.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun τ => ?_
  have hmτ : Measurable (fun x : (ℝ × ℝ) × ℝ => ENNReal.ofReal x.1.1 * Φ (τ, cylF x)) :=
    (ENNReal.measurable_ofReal.comp measurable_fst.fst).mul (hΦ.comp (measurable_const.prodMk measurable_cylF))
  have hreg : (volume : Measure ((ℝ × ℝ) × ℝ)).restrict region =
      (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
    rw [Measure.prod_restrict]
    rfl
  rw [← lintegral_cyl, hreg, lintegral_prod _ hmτ.aemeasurable, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans ?_ (lintegral_mono_set (μ := volume)
    (show Icc a b ×ˢ Icc c d ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) from fun p hp => ⟨lt_of_lt_of_le ha hp.1.1, mem_univ _⟩))
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun θ => ?_
  have h1 : 1 ≤ ENNReal.ofReal (1 / a) * ENNReal.ofReal p.1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.one_le_ofReal.2 ?_
    rw [one_div, inv_mul_eq_div, le_div_iff₀ ha, one_mul]
    exact hp.1.1
  calc Φ (orbitPt ((τ, p), θ)) = 1 * Φ (τ, cylF (p, θ)) := (one_mul _).symm
    _ ≤ ENNReal.ofReal (1 / a) * ENNReal.ofReal p.1 * Φ (τ, cylF (p, θ)) := mul_le_mul_of_nonneg_right h1 (by simp)
    _ = ENNReal.ofReal (1 / a) * (ENNReal.ofReal (p, θ).1.1 * Φ (τ, cylF (p, θ))) := mul_assoc _ _ _

theorem orbit_qmp {a b c d : ℝ} (ha : 0 < a) : Measure.QuasiMeasurePreserving orbitPt (boxM a b c d) volume := by
  refine ⟨orbitPt_meas, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply orbitPt_meas hs]
  have h2 : ∫⁻ τ, ∫⁻ y, s.indicator 1 (τ, y) = 0 := by
    rw [← lintegral_prod _ (measurable_one.indicator hs).aemeasurable, lintegral_indicator_one hs]
    exact h0
  refine le_antisymm ?_ (by simp)
  calc boxM a b c d (orbitPt ⁻¹' s) = ∫⁻ w, s.indicator 1 (orbitPt w) ∂boxM a b c d := by
        rw [← lintegral_indicator_one (orbitPt_meas hs)]
        rfl
    _ ≤ ENNReal.ofReal (1 / a) * ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ y, s.indicator 1 (τ, y) :=
        cyl_lint_le _ (measurable_one.indicator hs) ha
    _ ≤ ENNReal.ofReal (1 / a) * ∫⁻ τ, ∫⁻ y, s.indicator 1 (τ, y) := by
        gcongr
        exact Measure.restrict_le_self
    _ = 0 := by rw [h2, mul_zero]


theorem cylPoint_add_two_pi (r θ z : ℝ) : cylPoint r (θ + 2 * Real.pi) z = cylPoint r θ z := by
  simp [cylPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem phase_periodic (n : ℤ) (θ : ℝ) :
    Complex.exp (-(azimuth 1 n * (θ + 2 * Real.pi) : ℝ) * Complex.I) =
      Complex.exp (-(azimuth 1 n * θ : ℝ) * Complex.I) :=
  Complex.exp_eq_exp_iff_exists_int.2 ⟨-n, by unfold azimuth; push_cast; ring⟩

def waveKer (h : ℝ → Space → E) (Λ : ℝ × ℝ → (E →L[ℝ] ℝ)) (n : ℤ) (w : (ℝ × (ℝ × ℝ)) × ℝ) : ℂ :=
  Complex.exp (-(azimuth 1 n * w.2 : ℝ) * Complex.I) *
    (Λ (Real.cos w.2, Real.sin w.2) (h (orbitPt w).1 (orbitPt w).2) : ℂ)

theorem wave_eq (h : ℝ → Space → E) (Λ : ℝ × ℝ → (E →L[ℝ] ℝ)) (n : ℤ) (x : ℝ × (ℝ × ℝ)) :
    wave h Λ n x = ∫ θ in Ioo (-Real.pi) Real.pi, waveKer h Λ n (x, θ) := by
  have hper : Function.Periodic (fun θ => waveKer h Λ n (x, θ)) (2 * Real.pi) := fun θ => by
    simp only [waveKer, orbitPt, Real.cos_add_two_pi, Real.sin_add_two_pi, cylPoint_add_two_pi, phase_periodic]
  have e := hper.intervalIntegral_add_eq 0 (-Real.pi)
  rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at e
  show (∫ θ in (0 : ℝ)..(2 * Real.pi), waveKer h Λ n (x, θ)) = _
  rw [e, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]

theorem ker_bound (Λ : ℝ × ℝ → (E →L[ℝ] ℝ)) (hΛ : Continuous Λ) :
    ∃ C, 0 ≤ C ∧ ∀ θ : ℝ, ‖Λ (Real.cos θ, Real.sin θ)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝ × ℝ) 1).exists_bound_of_continuousOn hΛ.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun θ => (hC _ ?_).trans (le_max_left _ _)⟩
  rw [mem_closedBall_zero_iff, Prod.norm_def]
  exact max_le (by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one θ)
    (by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one θ)

theorem norm_cyl_le {r θ z a b c d : ℝ} (hr : r ∈ Icc a b) (ha : 0 < a) (hz : z ∈ Icc c d) :
    ‖cylPoint r θ z‖ ≤ 2 * b + |c| + |d| := by
  have hr0 : 0 ≤ r := ha.le.trans hr.1
  have hz' : |z| ≤ |c| + |d| := (abs_le_max_abs_abs hz.1 hz.2).trans
    (max_le (by linarith [abs_nonneg d]) (by linarith [abs_nonneg c]))
  unfold cylPoint
  refine norm_add₃_le.trans ?_
  rw [PiLp.norm_single, PiLp.norm_single, PiLp.norm_single, Real.norm_eq_abs,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hr0]
  have h1 := Real.abs_cos_le_one θ
  have h2 := Real.abs_sin_le_one θ
  nlinarith [hr.2, abs_nonneg (Real.cos θ), abs_nonneg (Real.sin θ)]

theorem orbit_integrable (h : ℝ → Space → E) (hh : LocallyIntegrable (fun z : ℝ × Space => h z.1 z.2) volume)
    {a b c d : ℝ} (ha : 0 < a) : Integrable (fun w => h (orbitPt w).1 (orbitPt w).2) (boxM a b c d) := by
  have hq := orbit_qmp (b := b) (c := c) (d := d) ha
  have hsm := hh.aestronglyMeasurable
  refine ⟨hsm.comp_quasiMeasurePreserving hq, ?_⟩
  set T : Set (ℝ × Space) := Icc 0 1 ×ˢ Metric.closedBall 0 (2 * b + |c| + |d|) with hTdef
  have hT : MeasurableSet T := measurableSet_Icc.prod Metric.isClosed_closedBall.measurableSet
  set Φ : ℝ × Space → ℝ≥0∞ := T.indicator (fun z => ‖hsm.mk _ z‖ₑ) with hΦdef
  have hΦ : Measurable Φ := hsm.stronglyMeasurable_mk.enorm.indicator hT
  have hae : ∀ᵐ w ∂boxM a b c d, ‖h (orbitPt w).1 (orbitPt w).2‖ₑ ≤ Φ (orbitPt w) := by
    have h1 := hq.ae_eq hsm.ae_eq_mk
    have h2 : ∀ᵐ w ∂boxM a b c d, w ∈ (Ioc (0 : ℝ) 1 ×ˢ (Icc a b ×ˢ Icc c d)) ×ˢ Ioo (-Real.pi) Real.pi := by
      rw [boxM_eq]
      exact ae_restrict_mem ((measurableSet_Ioc.prod (measurableSet_Icc.prod measurableSet_Icc)).prod measurableSet_Ioo)
    filter_upwards [h1, h2] with w hw hmem
    have hin : orbitPt w ∈ T :=
      ⟨⟨hmem.1.1.1.le, hmem.1.1.2⟩, mem_closedBall_zero_iff.2 (norm_cyl_le hmem.1.2.1 ha hmem.1.2.2)⟩
    rw [hΦdef, indicator_of_mem hin]
    exact le_of_eq (congrArg (fun u => ‖u‖ₑ) hw)
  have hfin : ∫⁻ z in T, ‖h z.1 z.2‖ₑ < ⊤ :=
    (hh.integrableOn_isCompact (isCompact_Icc.prod (isCompact_closedBall _ _))).2
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ w, ‖h (orbitPt w).1 (orbitPt w).2‖ₑ ∂boxM a b c d ≤ ∫⁻ w, Φ (orbitPt w) ∂boxM a b c d :=
        lintegral_mono_ae hae
    _ ≤ ENNReal.ofReal (1 / a) * ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ y, Φ (τ, y) := cyl_lint_le Φ hΦ ha
    _ ≤ ENNReal.ofReal (1 / a) * ∫⁻ z, Φ z ∂((volume : Measure ℝ).prod (volume : Measure Space)) := by
        gcongr
        rw [lintegral_prod _ hΦ.aemeasurable]
        exact setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (1 / a) * ∫⁻ z in T, ‖h z.1 z.2‖ₑ := by
        rw [← Measure.volume_eq_prod, hΦdef, lintegral_indicator hT]
        congr 1
        exact setLIntegral_congr_fun_ae hT (hsm.ae_eq_mk.mono fun z hz _ => congrArg (fun u => ‖u‖ₑ) hz.symm)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

theorem norm_phase (t : ℝ) : ‖Complex.exp (-(t : ℂ) * Complex.I)‖ = 1 := by
  rw [← Complex.ofReal_neg]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_timeFactor (k : ℤ) (τ : ℝ) : ‖timeFactor k τ‖ = 1 := by
  unfold timeFactor
  rw [← neg_mul]
  exact norm_phase _

theorem timeFactor_cont (k : ℤ) : Continuous (timeFactor k) := by
  unfold timeFactor
  fun_prop

theorem wave_integrable (h : ℝ → Space → E) (hh : LocallyIntegrable (fun z : ℝ × Space => h z.1 z.2) volume)
    (Λ : ℝ × ℝ → (E →L[ℝ] ℝ)) (hΛ : Continuous Λ) (n : ℤ) {a b c d : ℝ} (ha : 0 < a) :
    Integrable (wave h Λ n) ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Icc a b ×ˢ Icc c d))) := by
  obtain ⟨C, _, hC⟩ := ker_bound Λ hΛ
  have hi := orbit_integrable h hh (b := b) (c := c) (d := d) ha
  have hcont : Continuous (fun q : ℝ × E => Complex.exp (-(azimuth 1 n * q.1 : ℝ) * Complex.I) *
      ((Λ (Real.cos q.1, Real.sin q.1) q.2 : ℝ) : ℂ)) := by
    have h1 : Continuous (fun q : ℝ × E => Λ (Real.cos q.1, Real.sin q.1)) :=
      hΛ.comp ((Real.continuous_cos.comp continuous_fst).prodMk (Real.continuous_sin.comp continuous_fst))
    exact (Complex.continuous_exp.comp (by fun_prop)).mul (Complex.continuous_ofReal.comp (h1.clm_apply continuous_snd))
  have hpair : AEStronglyMeasurable (fun w : (ℝ × (ℝ × ℝ)) × ℝ => (w.2, h (orbitPt w).1 (orbitPt w).2))
      (boxM a b c d) := measurable_snd.aestronglyMeasurable.prodMk hi.1
  have hmeas : AEStronglyMeasurable (waveKer h Λ n) (boxM a b c d) :=
    (hcont.comp_aestronglyMeasurable hpair).congr (Eventually.of_forall fun w => rfl)
  have hK : Integrable (waveKer h Λ n) (boxM a b c d) := by
    refine (hi.norm.const_mul C).mono' hmeas (Eventually.of_forall fun w => ?_)
    simp only [waveKer]
    rw [norm_mul, norm_phase, one_mul, Complex.norm_real]
    exact ((Λ _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
  rw [show wave h Λ n = fun x => ∫ θ, waveKer h Λ n (x, θ) ∂(volume.restrict (Ioo (-Real.pi) Real.pi)) from
    funext (wave_eq h Λ n)]
  exact hK.integral_prod_left

theorem waveAvg_eq (h : ℝ → Space → E) (Λ : ℝ × ℝ → (E →L[ℝ] ℝ)) (k n : ℤ) :
    waveAvg h Λ k n = fun p => ∫ τ in Ioc (0 : ℝ) 1, timeFactor k τ * wave h Λ n (τ, p) :=
  funext fun _ => intervalIntegral.integral_of_le zero_le_one

theorem waveAvg_integrableOn (h : ℝ → Space → E) (hh : LocallyIntegrable (fun z : ℝ × Space => h z.1 z.2) volume)
    (Λ : ℝ × ℝ → (E →L[ℝ] ℝ)) (hΛ : Continuous Λ) (k n : ℤ) {a b c d : ℝ} (ha : 0 < a) :
    IntegrableOn (waveAvg h Λ k n) (Icc a b ×ˢ Icc c d) := by
  have hw := (wave_integrable h hh Λ hΛ n (b := b) (c := c) (d := d) ha).swap
  have hm := hw.bdd_mul (c := 1) (f := fun x : (ℝ × ℝ) × ℝ => timeFactor k x.2)
    ((timeFactor_cont k).comp continuous_snd).aestronglyMeasurable
    (Eventually.of_forall fun x => (norm_timeFactor k x.2).le)
  rw [waveAvg_eq]
  exact hm.integral_prod_left

theorem avg_pair (h : ℝ → Space → E) (hh : LocallyIntegrable (fun z : ℝ × Space => h z.1 z.2) volume)
    (Λ : ℝ × ℝ → (E →L[ℝ] ℝ)) (hΛ : Continuous Λ) (k n : ℤ) (χ : ℝ × ℝ → ℝ) (hχ : Continuous χ)
    {a b c d : ℝ} (ha : 0 < a) (hχs : ∀ p, p ∉ Icc a b ×ˢ Icc c d → χ p = 0) :
    ∫ p, ((χ p : ℝ) : ℂ) * waveAvg h Λ k n p =
      ∫ τ in Ioc (0 : ℝ) 1, timeFactor k τ * ∫ p, ((χ p : ℝ) : ℂ) * wave h Λ n (τ, p) := by
  have hSc : IsCompact (Icc a b ×ˢ Icc c d) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨Cχ, hCχ⟩ : ∃ C, ∀ p, ‖χ p‖ ≤ C := by
    obtain ⟨C, hC⟩ := hSc.exists_bound_of_continuousOn hχ.continuousOn
    refine ⟨max C 0, fun p => ?_⟩
    by_cases hp : p ∈ Icc a b ×ˢ Icc c d
    · exact (hC p hp).trans (le_max_left _ _)
    · rw [hχs p hp, norm_zero]
      exact le_max_right _ _
  have hw := (wave_integrable h hh Λ hΛ n (b := b) (c := c) (d := d) ha).swap
  have hF : Integrable (fun x : (ℝ × ℝ) × ℝ => timeFactor k x.2 * (((χ x.1 : ℝ) : ℂ) * wave h Λ n (x.2, x.1)))
      ((volume.restrict (Icc a b ×ˢ Icc c d)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    have := hw.bdd_mul (c := Cχ) (f := fun x : (ℝ × ℝ) × ℝ => timeFactor k x.2 * ((χ x.1 : ℝ) : ℂ))
      (((timeFactor_cont k).comp continuous_snd).mul
        (Complex.continuous_ofReal.comp (hχ.comp continuous_fst))).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [norm_mul, norm_timeFactor, one_mul, Complex.norm_real]
        exact hCχ _)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Function.comp_apply, mul_assoc]
    rfl
  calc ∫ p, ((χ p : ℝ) : ℂ) * waveAvg h Λ k n p
      = ∫ p in Icc a b ×ˢ Icc c d, ((χ p : ℝ) : ℂ) * waveAvg h Λ k n p :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => by rw [hχs p hp]; simp).symm
    _ = ∫ p in Icc a b ×ˢ Icc c d, ∫ τ in Ioc (0 : ℝ) 1,
          timeFactor k τ * (((χ p : ℝ) : ℂ) * wave h Λ n (τ, p)) := by
        refine setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) fun p _ => ?_
        rw [waveAvg_eq, ← integral_const_mul]
        congr 1
        funext τ
        ring
    _ = ∫ τ in Ioc (0 : ℝ) 1, ∫ p in Icc a b ×ˢ Icc c d,
          timeFactor k τ * (((χ p : ℝ) : ℂ) * wave h Λ n (τ, p)) :=
        integral_integral_swap (f := fun p τ => timeFactor k τ * (((χ p : ℝ) : ℂ) * wave h Λ n (τ, p))) hF
    _ = _ := by
        refine setIntegral_congr_fun measurableSet_Ioc fun τ _ => ?_
        rw [integral_const_mul,
          setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => by rw [hχs p hp]; simp]

theorem rect_of_tsupport {ψ : ℝ × ℝ → ℝ} (hc : HasCompactSupport ψ) (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) :
    ∃ a b c d : ℝ, 0 < a ∧ tsupport ψ ⊆ Icc a b ×ˢ Icc c d := by
  obtain ⟨a, b, ha, hab⟩ := HeightLine.compact_in_Ioi (hc.isCompact.image continuous_fst)
    (by rintro _ ⟨p, hp, rfl⟩; exact hpos p hp)
  obtain ⟨c, hc'⟩ := (hc.isCompact.image continuous_snd).bddBelow
  obtain ⟨d, hd⟩ := (hc.isCompact.image continuous_snd).bddAbove
  exact ⟨a, b, c, d, ha, fun p hp => ⟨hab ⟨p, hp, rfl⟩, hc' ⟨p, hp, rfl⟩, hd ⟨p, hp, rfl⟩⟩⟩

theorem plane_weak {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    (f : ℝ → Space → F) (g : ℝ → Space → (Space →L[ℝ] F))
    (hf : LocallyIntegrable (fun z : ℝ × Space => f z.1 z.2) volume)
    (hg : LocallyIntegrable (fun z : ℝ × Space => g z.1 z.2) volume)
    (hw : ∀ᵐ τ, LocallyIntegrable (f τ) volume ∧
      (∀ j : Fin 3, LocallyIntegrable (fun y => g τ y (unitVector j)) volume) ∧
      ∀ φ : Space → ℝ, SteadyCert.IsTestScalar φ → ∀ j : Fin 3,
        ∫ y, fderiv ℝ φ y (unitVector j) • f τ y = -∫ y, φ y • g τ y (unitVector j))
    (L : ℝ × ℝ → (F →L[ℝ] ℝ)) (hL : ContDiff ℝ ∞ L) (k n : ℤ) (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) :
    ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * waveAvg f L k n p =
        -∫ p, ((ψ p : ℝ) : ℂ) * waveAvg g (radialL L) k n p ∧
      ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * waveAvg f L k n p =
        -∫ p, ((ψ p : ℝ) : ℂ) * waveAvg g (axialL L) k n p := by
  obtain ⟨a, b, c, d, ha, hS⟩ := rect_of_tsupport hc hpos
  have off : ∀ p, p ∉ Icc a b ×ˢ Icc c d → p ∉ tsupport ψ := fun p hp h' => hp (hS h')
  have z0 : ∀ p, p ∉ Icc a b ×ˢ Icc c d → ψ p = 0 := fun p hp => by
    by_contra h'
    exact off p hp (subset_tsupport _ h')
  have zd : ∀ u : ℝ × ℝ, ∀ p, p ∉ Icc a b ×ˢ Icc c d → fderiv ℝ ψ p u = 0 := fun u p hp => by
    simp [fderiv_of_notMem_tsupport ℝ (off p hp)]
  have cd : ∀ u : ℝ × ℝ, Continuous (fun p => fderiv ℝ ψ p u) := fun u =>
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hτ : ∀ᵐ τ, (∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * wave f L n (τ, p) =
        -∫ p, ((ψ p : ℝ) : ℂ) * wave g (radialL L) n (τ, p)) ∧
      (∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * wave f L n (τ, p) =
        -∫ p, ((ψ p : ℝ) : ℂ) * wave g (axialL L) n (τ, p)) := by
    filter_upwards [hw] with τ hτ
    exact CellCert.CellFormula.cylModeWeak F (f τ) (g τ) hτ.1 hτ.2.1 hτ.2.2 L hL 1 n ψ hψ hc hpos
  have hLc := hL.continuous
  have eψ := avg_pair g hg (radialL L) (radialL_cont hLc) k n ψ hψ.continuous ha z0
  have eψ' := avg_pair g hg (axialL L) (axialL_cont hLc) k n ψ hψ.continuous ha z0
  have er := avg_pair f hf L hLc k n (fun p => fderiv ℝ ψ p (1, 0)) (cd (1, 0)) ha (zd (1, 0))
  have ez := avg_pair f hf L hLc k n (fun p => fderiv ℝ ψ p (0, 1)) (cd (0, 1)) ha (zd (0, 1))
  constructor
  · rw [er, eψ, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hτ] with τ h'
    rw [h'.1, mul_neg]
  · rw [ez, eψ', ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hτ] with τ h'
    rw [h'.2, mul_neg]

end Internal.HeightOrbit

end Breakdown.CertCell.Bridge
