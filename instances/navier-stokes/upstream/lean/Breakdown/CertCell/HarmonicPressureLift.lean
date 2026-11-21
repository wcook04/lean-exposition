import Breakdown.CertCell.RowProfileDefs
import Breakdown.CertCell.TailAngularPlane
import Breakdown.Cert.CoerciveModeL2

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

namespace Internal.PressureLift

theorem rot_neg_coord (φ : ℝ) (u : Space) (a : Fin 3) :
    axialRot (-φ) u a = frameVec φ u a := by
  fin_cases a <;> simp [axialRot, frameVec, radialUnit, angularUnit, axialUnit, unitVector,
    PiLp.inner_apply, Fin.sum_univ_three]

theorem rot_planePoint (θ : ℝ) (p : ℝ × ℝ) :
    axialRot θ (planePoint p) = CellCert.CellAnalysis.cylPoint p.1 θ p.2 := by
  ext i
  fin_cases i <;> simp [axialRot, planePoint, CellCert.CellAnalysis.cylPoint, unitVector] <;> ring

theorem frameVec_eq_inner (θ : ℝ) (u : Space) (a : Fin 3) :
    frameVec θ u a = innerSL ℝ (![radialUnit θ, angularUnit θ, axialUnit] a) u := by
  fin_cases a <;> simp [frameVec, real_inner_comm]

theorem frameVec_integral {μ : Measure ℝ} (θ : ℝ) (a : Fin 3) {f : ℝ → Space} (hf : Integrable f μ) :
    frameVec θ (∫ τ, f τ ∂μ) a = ∫ τ, frameVec θ (f τ) a ∂μ := by
  simp only [frameVec_eq_inner]
  exact ((innerSL ℝ _).integral_comp_comm hf).symm

theorem frameVec_smul (θ c : ℝ) (u : Space) (a : Fin 3) :
    frameVec θ (c • u) a = c * frameVec θ u a := by
  simp only [frameVec_eq_inner, map_smul, smul_eq_mul]

theorem frameVec_neg (θ : ℝ) (u : Space) (a : Fin 3) :
    frameVec θ (-u) a = -frameVec θ u a := by
  simp only [frameVec_eq_inner, map_neg]

theorem abs_frameVec_le (θ : ℝ) (u : Space) (a : Fin 3) : |frameVec θ u a| ≤ ‖u‖ := by
  rw [← rot_neg_coord, ← Real.norm_eq_abs, ← Coercive.RotationInternal.axialRot_norm (-θ) u]
  exact PiLp.norm_apply_le _ a

theorem continuous_frameVec (a : Fin 3) : Continuous (fun q : ℝ × Space => frameVec q.1 q.2 a) := by
  have e2 : (fun q : ℝ × Space => frameVec q.1 q.2 a) = fun q => axialRot (-q.1) q.2 a := by
    funext q
    exact (rot_neg_coord _ _ _).symm
  rw [e2]
  exact Coercive.ModeL2Internal.continuous_rotCoord a

theorem continuous_cylPoint (r z : ℝ) : Continuous (fun θ : ℝ => CellCert.CellAnalysis.cylPoint r θ z) := by
  have e : (fun θ : ℝ => CellCert.CellAnalysis.cylPoint r θ z) = fun θ => axialRot θ (planePoint (r, z)) := by
    funext θ
    exact (rot_planePoint θ (r, z)).symm
  rw [e]
  unfold axialRot
  fun_prop

theorem cylPoint_add_two_pi (r θ z : ℝ) :
    CellCert.CellAnalysis.cylPoint r (θ + 2 * Real.pi) z = CellCert.CellAnalysis.cylPoint r θ z := by
  simp [CellCert.CellAnalysis.cylPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem setLIntegral_periodic {h : ℝ → ℝ≥0∞} (hh : Function.Periodic h (2 * Real.pi)) :
    ∫⁻ θ in Ioc (-Real.pi) Real.pi, h θ = ∫⁻ θ in Ioc 0 (2 * Real.pi), h θ := by
  have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have h1 := AddCircle.lintegral_preimage (2 * Real.pi) (-Real.pi) hh.lift
  have h2 := AddCircle.lintegral_preimage (2 * Real.pi) 0 hh.lift
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h1
  rw [zero_add] at h2
  exact h1.trans h2.symm

theorem continuous_cylPoint_joint :
    Continuous (fun w : (ℝ × ℝ) × ℝ => CellCert.CellAnalysis.cylPoint w.1.1 w.2 w.1.2) := by
  have e : (fun w : (ℝ × ℝ) × ℝ => CellCert.CellAnalysis.cylPoint w.1.1 w.2 w.1.2) =
      fun w => axialRot w.2 (planePoint w.1) := by
    funext w
    exact (rot_planePoint w.2 w.1).symm
  rw [e]
  exact TailBand.Internal.AngularPlane.continuous_orbitPlane

theorem norm_cylPoint (p : ℝ × ℝ) (θ : ℝ) :
    ‖CellCert.CellAnalysis.cylPoint p.1 θ p.2‖ = ‖planePoint p‖ := by
  rw [← rot_planePoint]
  exact Coercive.RotationInternal.axialRot_norm θ _

theorem measurable_orbitLIntegral (E : ℝ × Space → ℝ≥0∞) (hE : Measurable E) :
    Measurable (fun p : ℝ × ℝ => ∫⁻ x, E (x.1, CellCert.CellAnalysis.cylPoint p.1 x.2 p.2)
      ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi))))) := by
  have h1 : Continuous (fun w : (ℝ × ℝ) × (ℝ × ℝ) => CellCert.CellAnalysis.cylPoint w.1.1 w.2.2 w.1.2) :=
    continuous_cylPoint_joint.comp (continuous_fst.prodMk continuous_snd.snd)
  have h2 : Measurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => (w.2.1, CellCert.CellAnalysis.cylPoint w.1.1 w.2.2 w.1.2)) :=
    measurable_snd.fst.prodMk h1.measurable
  have hm : Measurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
      E (w.2.1, CellCert.CellAnalysis.cylPoint w.1.1 w.2.2 w.1.2)) := hE.comp h2
  exact hm.lintegral_prod_right' (ν := (volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi))))

theorem lintegral_orbit (E : ℝ × Space → ℝ≥0∞) (hE : Measurable E) :
    ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y, E (σ, y) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ univ, ENNReal.ofReal p.1 *
        ∫⁻ x, E (x.1, CellCert.CellAnalysis.cylPoint p.1 x.2 p.2)
          ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi)))) := by
  have hF : Measurable (fun y => ∫⁻ σ in Icc (0 : ℝ) 1, E (σ, y)) := hE.lintegral_prod_left'
  rw [lintegral_lintegral_swap (f := fun σ y => E (σ, y)) (by exact hE.aemeasurable), TailBand.lintegral_eq_cylindrical _ hF]
  refine lintegral_congr fun p => ?_
  congr 1
  have hG : Measurable (fun x : ℝ × ℝ => E (x.1, CellCert.CellAnalysis.cylPoint p.1 x.2 p.2)) :=
    hE.comp (measurable_fst.prodMk ((continuous_cylPoint p.1 p.2).measurable.comp measurable_snd))
  have hper : Function.Periodic
      (fun θ => ∫⁻ σ in Icc (0 : ℝ) 1, E (σ, CellCert.CellAnalysis.cylPoint p.1 θ p.2)) (2 * Real.pi) := by
    intro θ
    simp only [cylPoint_add_two_pi]
  simp_rw [rot_planePoint]
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, setLIntegral_periodic hper, lintegral_prod _ hG.aemeasurable,
    ← Measure.restrict_congr_set (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := 1))]
  exact lintegral_lintegral_swap (hG.comp measurable_swap).aemeasurable

theorem ae_integrable_orbit {Pg : ℝ → Space → Space} (hP : IsPeriodicPressure Pg) :
    ∀ᵐ p : ℝ × ℝ, 0 < p.1 →
      Integrable (fun x : ℝ × ℝ => Pg x.1 (CellCert.CellAnalysis.cylPoint p.1 x.2 p.2))
        ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi)))) := by
  set μ := (volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi))) with hμ
  set S : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ univ with hS
  have hSm : MeasurableSet S := measurableSet_Ioi.prod MeasurableSet.univ
  obtain ⟨Q, hQm, hQ⟩ : ∃ Q : ℝ × Space → Space, StronglyMeasurable Q ∧
      (fun z : ℝ × Space => Pg z.1 z.2) =ᵐ[volume] Q :=
    ⟨_, hP.measurable.stronglyMeasurable_mk, hP.measurable.ae_eq_mk⟩
  set N := toMeasurable volume {z : ℝ × Space | Pg z.1 z.2 ≠ Q z} with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume N = 0 := by
    rw [hN, measure_toMeasurable]
    exact hQ
  have hE0 : Measurable (N.indicator (1 : ℝ × Space → ℝ≥0∞)) := measurable_one.indicator hNm
  have hL0 : ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y, N.indicator (1 : ℝ × Space → ℝ≥0∞) (σ, y) = 0 := by
    refine le_antisymm ?_ zero_le
    calc ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y, N.indicator (1 : ℝ × Space → ℝ≥0∞) (σ, y)
        ≤ ∫⁻ σ, ∫⁻ y, N.indicator (1 : ℝ × Space → ℝ≥0∞) (σ, y) := setLIntegral_le_lintegral _ _
      _ = ∫⁻ z, N.indicator (1 : ℝ × Space → ℝ≥0∞) z := by
        rw [Measure.volume_eq_prod, lintegral_prod _ hE0.aemeasurable]
      _ = 0 := by rw [lintegral_indicator_one hNm, hN0]
  have hz := lintegral_orbit _ hE0
  rw [hL0] at hz
  have hzae := (lintegral_eq_zero_iff ((ENNReal.measurable_ofReal.comp measurable_fst).mul
    (measurable_orbitLIntegral _ hE0))).1 hz.symm
  have hfin : ∀ R : ℕ, ∀ᵐ p ∂(volume.restrict S), ENNReal.ofReal p.1 *
      ∫⁻ x, ({z : ℝ × Space | z.2 ∈ Metric.closedBall (0 : Space) R}).indicator
        (fun z => ENNReal.ofReal (‖Q z‖ ^ 2)) (x.1, CellCert.CellAnalysis.cylPoint p.1 x.2 p.2) ∂μ < ⊤ := by
    intro R
    have hBm : MeasurableSet {z : ℝ × Space | z.2 ∈ Metric.closedBall (0 : Space) R} :=
      measurable_snd Metric.isClosed_closedBall.measurableSet
    have hER : Measurable (({z : ℝ × Space | z.2 ∈ Metric.closedBall (0 : Space) R}).indicator
        (fun z => ENNReal.ofReal (‖Q z‖ ^ 2))) :=
      ((hQm.measurable.norm.pow_const 2).ennreal_ofReal).indicator hBm
    have hlt : ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y, ({z : ℝ × Space | z.2 ∈ Metric.closedBall (0 : Space) R}).indicator
        (fun z => ENNReal.ofReal (‖Q z‖ ^ 2)) (σ, y) < ⊤ := by
      have hae : ∀ᵐ σ : ℝ, ∀ᵐ y : Space, Pg σ y = Q (σ, y) := by
        have h := hQ
        rw [Measure.volume_eq_prod] at h
        exact Measure.ae_ae_of_ae_prod h
      calc ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y, ({z : ℝ × Space | z.2 ∈ Metric.closedBall (0 : Space) R}).indicator
            (fun z => ENNReal.ofReal (‖Q z‖ ^ 2)) (σ, y)
          = ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖Pg σ y‖ ^ 2) := by
            refine lintegral_congr_ae (ae_restrict_of_ae ?_)
            filter_upwards [hae] with σ hσ
            rw [← lintegral_indicator Metric.isClosed_closedBall.measurableSet]
            refine lintegral_congr_ae ?_
            filter_upwards [hσ] with y hy
            by_cases hy' : y ∈ Metric.closedBall (0 : Space) R
            · rw [Set.indicator_of_mem (show (σ, y) ∈ {z : ℝ × Space | z.2 ∈ Metric.closedBall (0 : Space) R} from hy'),
                Set.indicator_of_mem hy', hy]
            · rw [Set.indicator_of_notMem (show (σ, y) ∉ {z : ℝ × Space | z.2 ∈ Metric.closedBall (0 : Space) R} from hy'),
                Set.indicator_of_notMem hy']
        _ < ⊤ := hP.local_square R
    have h := lintegral_orbit _ hER
    rw [h] at hlt
    exact ae_lt_top ((ENNReal.measurable_ofReal.comp measurable_fst).mul (measurable_orbitLIntegral _ hER)) hlt.ne
  rw [← ae_all_iff] at hfin
  have hall := (ae_restrict_iff' hSm).1 (hzae.and hfin)
  filter_upwards [hall] with p hp hp1
  obtain ⟨h0, hR⟩ := hp ⟨hp1, mem_univ _⟩
  have hr : ENNReal.ofReal p.1 ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hp1
  have hc : Measurable (fun x : ℝ × ℝ => (x.1, CellCert.CellAnalysis.cylPoint p.1 x.2 p.2)) :=
    measurable_fst.prodMk ((continuous_cylPoint p.1 p.2).measurable.comp measurable_snd)
  have hI0 : ∫⁻ x, N.indicator (1 : ℝ × Space → ℝ≥0∞) (x.1, CellCert.CellAnalysis.cylPoint p.1 x.2 p.2) ∂μ = 0 := by
    have h0' : ENNReal.ofReal p.1 * ∫⁻ x, N.indicator (1 : ℝ × Space → ℝ≥0∞)
        (x.1, CellCert.CellAnalysis.cylPoint p.1 x.2 p.2) ∂μ = 0 := h0
    exact (mul_eq_zero.1 h0').resolve_left hr
  have hgood := (lintegral_eq_zero_iff (hE0.comp hc)).1 hI0
  have heq : (fun x : ℝ × ℝ => Q (x.1, CellCert.CellAnalysis.cylPoint p.1 x.2 p.2)) =ᵐ[μ]
      fun x => Pg x.1 (CellCert.CellAnalysis.cylPoint p.1 x.2 p.2) := by
    filter_upwards [hgood] with x hx
    have hxN : (x.1, CellCert.CellAnalysis.cylPoint p.1 x.2 p.2) ∉ N := by
      intro hmem
      simp [Function.comp, Set.indicator_of_mem hmem] at hx
    by_contra hne
    exact hxN (subset_toMeasurable _ _ (Ne.symm hne))
  set R : ℕ := ⌈‖planePoint p‖⌉₊ with hRdef
  have hRlt := hR R
  have hIR : ∫⁻ x, ENNReal.ofReal (‖Q (x.1, CellCert.CellAnalysis.cylPoint p.1 x.2 p.2)‖ ^ 2) ∂μ < ⊤ := by
    have hball : ∀ x : ℝ × ℝ, (x.1, CellCert.CellAnalysis.cylPoint p.1 x.2 p.2) ∈
        {z : ℝ × Space | z.2 ∈ Metric.closedBall (0 : Space) R} := by
      intro x
      simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right, norm_cylPoint]
      exact Nat.le_ceil _
    have hcong : ∫⁻ x, ({z : ℝ × Space | z.2 ∈ Metric.closedBall (0 : Space) R}).indicator
        (fun z => ENNReal.ofReal (‖Q z‖ ^ 2)) (x.1, CellCert.CellAnalysis.cylPoint p.1 x.2 p.2) ∂μ =
        ∫⁻ x, ENNReal.ofReal (‖Q (x.1, CellCert.CellAnalysis.cylPoint p.1 x.2 p.2)‖ ^ 2) ∂μ :=
      lintegral_congr fun x => Set.indicator_of_mem (hball x) _
    rw [← hcong]
    exact ENNReal.lt_top_of_mul_ne_top_right hRlt.ne hr
  have hQint : Integrable (fun x : ℝ × ℝ => Q (x.1, CellCert.CellAnalysis.cylPoint p.1 x.2 p.2)) μ := by
    refine ⟨(hQm.comp_measurable hc).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ x, ‖Q (x.1, CellCert.CellAnalysis.cylPoint p.1 x.2 p.2)‖ₑ ∂μ
        ≤ ∫⁻ x, (1 + ENNReal.ofReal (‖Q (x.1, CellCert.CellAnalysis.cylPoint p.1 x.2 p.2)‖ ^ 2)) ∂μ := by
          refine lintegral_mono fun x => ?_
          rw [← ofReal_norm, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (sq_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith [sq_nonneg (‖Q (x.1, CellCert.CellAnalysis.cylPoint p.1 x.2 p.2)‖ - 1)]
      _ = μ univ + ∫⁻ x, ENNReal.ofReal (‖Q (x.1, CellCert.CellAnalysis.cylPoint p.1 x.2 p.2)‖ ^ 2) ∂μ := by
          rw [lintegral_add_left measurable_const, lintegral_const, one_mul]
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨measure_lt_top _ _, hIR⟩
  exact hQint.congr heq

theorem exp_neg_mul_I (x : ℝ) :
    Complex.exp (-((x : ℂ) * Complex.I)) = (Real.cos x : ℂ) - Complex.I * (Real.sin x : ℂ) := by
  rw [← neg_mul, ← Complex.ofReal_neg, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

theorem norm_exp_neg_mul_I (x : ℝ) : ‖Complex.exp (-((x : ℂ) * Complex.I))‖ = 1 := by
  rw [← neg_mul, ← Complex.ofReal_neg]
  exact Complex.norm_exp_ofReal_mul_I _

theorem frameVec_harmonicCos_ae {Pg : ℝ → Space → Space} (ν : ℤ) (θ : ℝ) (y : Space) (a : Fin 3)
    (hs : Integrable (fun τ => Pg τ y) (volume.restrict (Ioc (0 : ℝ) 1))) :
    frameVec θ (harmonicCos ν Pg y) a =
      ∫ τ in Ioc (0 : ℝ) 1, Real.cos (2 * Real.pi * ν * τ) * frameVec θ (Pg τ y) a := by
  have hi : Integrable (fun τ => Real.cos (2 * Real.pi * ν * τ) • Pg τ y) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hs.bdd_smul 1 (by fun_prop : Continuous fun τ : ℝ => Real.cos (2 * Real.pi * ν * τ)).aestronglyMeasurable
      (ae_of_all _ fun τ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  rw [harmonicCos, integral_Icc_eq_integral_Ioc, frameVec_integral θ a hi]
  simp only [frameVec_smul]

theorem frameVec_harmonicSin_ae {Pg : ℝ → Space → Space} (ν : ℤ) (θ : ℝ) (y : Space) (a : Fin 3)
    (hs : Integrable (fun τ => Pg τ y) (volume.restrict (Ioc (0 : ℝ) 1))) :
    frameVec θ (harmonicSin ν Pg y) a =
      -∫ τ in Ioc (0 : ℝ) 1, Real.sin (2 * Real.pi * ν * τ) * frameVec θ (Pg τ y) a := by
  have hi : Integrable (fun τ => Real.sin (2 * Real.pi * ν * τ) • Pg τ y) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hs.bdd_smul 1 (by fun_prop : Continuous fun τ : ℝ => Real.sin (2 * Real.pi * ν * τ)).aestronglyMeasurable
      (ae_of_all _ fun τ => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  rw [harmonicSin, integral_Icc_eq_integral_Ioc, frameVec_neg, frameVec_integral θ a hi]
  simp only [frameVec_smul]

theorem harmonic_orbit {Pg : ℝ → Space → Space} (ν : ℤ) (k r z : ℝ) (a : Fin 3)
    (hF : Integrable (fun x : ℝ × ℝ => Pg x.1 (CellCert.CellAnalysis.cylPoint r x.2 z))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi))))) :
    ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(((2 * Real.pi * ν * τ + k * φ : ℝ) : ℂ) * Complex.I)) *
          ((frameVec φ (Pg τ (CellCert.CellAnalysis.cylPoint r φ z)) a : ℝ) : ℂ)
      = (∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-((k * θ : ℝ) : ℂ) * Complex.I) *
            ((frameVec θ (harmonicCos ν Pg (CellCert.CellAnalysis.cylPoint r θ z)) a : ℝ) : ℂ))
        + Complex.I * ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-((k * θ : ℝ) : ℂ) * Complex.I) *
            ((frameVec θ (harmonicSin ν Pg (CellCert.CellAnalysis.cylPoint r θ z)) a : ℝ) : ℂ) := by
  set μτ := volume.restrict (Ioc (0 : ℝ) 1) with hμτ
  set μθ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)) with hμθ
  have hπ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  set g : ℝ × ℝ → ℝ := fun x => frameVec x.2 (Pg x.1 (CellCert.CellAnalysis.cylPoint r x.2 z)) a with hgdef
  have hg : Integrable g (μτ.prod μθ) := by
    refine Integrable.mono' hF.norm ?_ (ae_of_all _ fun x => ?_)
    · exact (continuous_frameVec a).comp_aestronglyMeasurable
        (f := fun x : ℝ × ℝ => (x.2, Pg x.1 (CellCert.CellAnalysis.cylPoint r x.2 z)))
        (measurable_snd.aestronglyMeasurable.prodMk hF.aestronglyMeasurable)
    · rw [Real.norm_eq_abs]
      exact abs_frameVec_le _ _ _
  set K : ℝ × ℝ → ℂ := fun x => Complex.exp (-(((2 * Real.pi * ν * x.1 + k * x.2 : ℝ) : ℂ) * Complex.I)) *
    ((g x : ℝ) : ℂ) with hKdef
  have hK : Integrable K (μτ.prod μθ) :=
    hg.ofReal.bdd_mul (c := 1) (by fun_prop : Continuous fun x : ℝ × ℝ =>
        Complex.exp (-(((2 * Real.pi * ν * x.1 + k * x.2 : ℝ) : ℂ) * Complex.I))).aestronglyMeasurable
      (ae_of_all _ fun x => (norm_exp_neg_mul_I _).le)
  have hcosc : Continuous fun τ : ℝ => Real.cos (2 * Real.pi * ν * τ) := by fun_prop
  have hsinc : Continuous fun τ : ℝ => Real.sin (2 * Real.pi * ν * τ) := by fun_prop
  have hcg : Integrable (fun x : ℝ × ℝ => Real.cos (2 * Real.pi * ν * x.1) * g x) (μτ.prod μθ) :=
    hg.bdd_mul (c := 1) (hcosc.comp continuous_fst).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hsg : Integrable (fun x : ℝ × ℝ => Real.sin (2 * Real.pi * ν * x.1) * g x) (μτ.prod μθ) :=
    hg.bdd_mul (c := 1) (hsinc.comp continuous_fst).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hexpc : Continuous fun θ : ℝ => Complex.exp (-((k * θ : ℝ) : ℂ) * Complex.I) := by fun_prop
  have hexpn : ∀ θ : ℝ, ‖Complex.exp (-((k * θ : ℝ) : ℂ) * Complex.I)‖ ≤ 1 := fun θ => by
    rw [neg_mul]
    exact (norm_exp_neg_mul_I _).le
  have hC : ∀ᵐ θ ∂μθ, frameVec θ (harmonicCos ν Pg (CellCert.CellAnalysis.cylPoint r θ z)) a =
      ∫ τ, Real.cos (2 * Real.pi * ν * τ) * g (τ, θ) ∂μτ := by
    filter_upwards [hF.prod_left_ae] with θ hθ
    exact frameVec_harmonicCos_ae ν θ _ a hθ
  have hS : ∀ᵐ θ ∂μθ, frameVec θ (harmonicSin ν Pg (CellCert.CellAnalysis.cylPoint r θ z)) a =
      -∫ τ, Real.sin (2 * Real.pi * ν * τ) * g (τ, θ) ∂μτ := by
    filter_upwards [hF.prod_left_ae] with θ hθ
    exact frameVec_harmonicSin_ae ν θ _ a hθ
  have hCi : Integrable (fun θ => Complex.exp (-((k * θ : ℝ) : ℂ) * Complex.I) *
      ((frameVec θ (harmonicCos ν Pg (CellCert.CellAnalysis.cylPoint r θ z)) a : ℝ) : ℂ)) μθ := by
    refine (hcg.integral_prod_right.ofReal.bdd_mul (c := 1) hexpc.aestronglyMeasurable
      (ae_of_all _ hexpn)).congr ?_
    filter_upwards [hC] with θ hθ
    exact congrArg (fun t : ℝ => Complex.exp (-((k * θ : ℝ) : ℂ) * Complex.I) * (t : ℂ)) hθ.symm
  have hSi : Integrable (fun θ => Complex.exp (-((k * θ : ℝ) : ℂ) * Complex.I) *
      ((frameVec θ (harmonicSin ν Pg (CellCert.CellAnalysis.cylPoint r θ z)) a : ℝ) : ℂ)) μθ := by
    refine (hsg.integral_prod_right.neg.ofReal.bdd_mul (c := 1) hexpc.aestronglyMeasurable
      (ae_of_all _ hexpn)).congr ?_
    filter_upwards [hS] with θ hθ
    exact congrArg (fun t : ℝ => Complex.exp (-((k * θ : ℝ) : ℂ) * Complex.I) * (t : ℂ)) hθ.symm
  have hpt : ∀ᵐ θ ∂μθ, ∫ τ, K (τ, θ) ∂μτ =
      Complex.exp (-((k * θ : ℝ) : ℂ) * Complex.I) *
          ((frameVec θ (harmonicCos ν Pg (CellCert.CellAnalysis.cylPoint r θ z)) a : ℝ) : ℂ)
        + Complex.I * (Complex.exp (-((k * θ : ℝ) : ℂ) * Complex.I) *
          ((frameVec θ (harmonicSin ν Pg (CellCert.CellAnalysis.cylPoint r θ z)) a : ℝ) : ℂ)) := by
    filter_upwards [hC, hS, hg.prod_left_ae] with θ hCθ hSθ hgθ
    have hc1 : Integrable (fun τ => Real.cos (2 * Real.pi * ν * τ) * g (τ, θ)) μτ :=
      hgθ.bdd_mul (c := 1) hcosc.aestronglyMeasurable
        (ae_of_all _ fun τ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
    have hs1 : Integrable (fun τ => Real.sin (2 * Real.pi * ν * τ) * g (τ, θ)) μτ :=
      hgθ.bdd_mul (c := 1) hsinc.aestronglyMeasurable
        (ae_of_all _ fun τ => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
    have hK1 : ∀ τ, K (τ, θ) = Complex.exp (-((k * θ : ℝ) : ℂ) * Complex.I) *
        ((((Real.cos (2 * Real.pi * ν * τ) * g (τ, θ)) : ℝ) : ℂ)
          - Complex.I * (((Real.sin (2 * Real.pi * ν * τ) * g (τ, θ)) : ℝ) : ℂ)) := by
      intro τ
      have e1 : -(((2 * Real.pi * ν * τ + k * θ : ℝ) : ℂ) * Complex.I) =
          -((k * θ : ℝ) : ℂ) * Complex.I + -(((2 * Real.pi * ν * τ : ℝ) : ℂ) * Complex.I) := by
        push_cast
        ring
      simp only [hKdef]
      rw [e1, Complex.exp_add, exp_neg_mul_I]
      push_cast
      ring
    simp only [hK1]
    rw [integral_const_mul, integral_sub hc1.ofReal (hs1.ofReal.const_mul _), integral_const_mul,
      integral_complex_ofReal, integral_complex_ofReal, hCθ, hSθ]
    push_cast
    ring
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le hπ,
    intervalIntegral.integral_of_le hπ]
  simp_rw [intervalIntegral.integral_of_le hπ]
  calc ∫ τ in Ioc (0 : ℝ) 1, ∫ φ in Ioc (0 : ℝ) (2 * Real.pi),
        Complex.exp (-(((2 * Real.pi * ν * τ + k * φ : ℝ) : ℂ) * Complex.I)) *
          ((frameVec φ (Pg τ (CellCert.CellAnalysis.cylPoint r φ z)) a : ℝ) : ℂ)
      = ∫ τ, ∫ φ, K (τ, φ) ∂μθ ∂μτ := rfl
    _ = ∫ φ, ∫ τ, K (τ, φ) ∂μτ ∂μθ := integral_integral_swap (f := fun τ φ => K (τ, φ)) (by exact hK)
    _ = _ := by
      rw [integral_congr_ae hpt, integral_add hCi (hSi.const_mul _), integral_const_mul]

end Internal.PressureLift

theorem harmonicPressureLift_holds : HarmonicPressureLiftStatement := by
  intro m Pg hP ν n hn
  filter_upwards [Internal.PressureLift.ae_integrable_orbit hP] with p hp hp1 a
  have hι : labelHarmonic m (harmonicMode ν n) = (ν, n * (m : ℤ)) := by
    simp only [labelHarmonic, labelTime, labelAzimuth, harmonicMode]
    rw [Int.two_mul_ediv_two_of_even hn]
    ring_nf
  have hk : (((n * (m : ℤ) : ℤ)) : ℝ) = azimuth m n := by
    simp only [azimuth]
    push_cast
    ring
  have key := Internal.PressureLift.harmonic_orbit (Pg := Pg) ν (((n * (m : ℤ) : ℤ)) : ℝ) p.1 p.2 a (hp hp1)
  rw [hk] at key
  rw [velAt, labelVel, hι, modeVel, modeAverage]
  simp only [zero_add, Internal.PressureLift.rot_planePoint, Internal.PressureLift.rot_neg_coord]
  rw [hk, key, modeVec, modeVec]
  ring

end CellCalculus

end CertCell

end Breakdown
