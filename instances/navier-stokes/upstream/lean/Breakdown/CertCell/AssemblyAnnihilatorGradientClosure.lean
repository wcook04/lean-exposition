import Breakdown.FracCert.Defs
import Breakdown.CertCell.AssemblyAnnihilatorGradientPotential
import Breakdown.CertCell.AssemblyAnnihilatorGradientMollify
import Breakdown.CertCell.AssemblyAnnihilatorGradientBound

open MeasureTheory Set Metric
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.CertCell.AnnihilatorGradient.Internal

open SteadyCert

theorem lintegral_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) : (∫⁻ a, f a ∂μ) ^ 2 ≤ μ univ * ∫⁻ a, f a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, lintegral_const, ENNReal.rpow_two, one_pow, one_mul] at h
  calc (∫⁻ a, f a ∂μ) ^ 2 ≤ ((∫⁻ a, f a ^ 2 ∂μ) ^ (1 / (2 : ℝ)) * μ univ ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h 2
    _ = μ univ * ∫⁻ a, f a ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (μ univ ^ _), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num
        ring

theorem region_bound (G : Space → ℝ≥0∞) (hG : Measurable G) (R : ℝ) (hR : 1 ≤ R) :
    ∫⁻ x in closedBall (0 : Space) R, ∫⁻ z in closedBall (0 : Space) 1 ×ˢ Ioc (0 : ℝ) 1,
        G (z.1 + z.2 • (x - z.1))
      ≤ 8 * volume (closedBall (0 : Space) R) * ∫⁻ y in closedBall (0 : Space) R, G y := by
  set H := (closedBall (0 : Space) R).indicator G
  have hH : Measurable H := hG.indicator measurableSet_closedBall
  have hpt : ∀ x ∈ closedBall (0 : Space) R, EqOn (fun z : Space × ℝ => G (z.1 + z.2 • (x - z.1)))
      (fun z : Space × ℝ => H (z.1 + z.2 • (x - z.1))) (closedBall (0 : Space) 1 ×ˢ Ioc (0 : ℝ) 1) := by
    intro x hx z hz
    simp only [H]
    rw [indicator_of_mem]
    exact (convex_closedBall (0 : Space) R).add_smul_sub_mem (closedBall_subset_closedBall hR hz.1) hx
      ⟨hz.2.1.le, hz.2.2⟩
  calc _ = ∫⁻ x in closedBall (0 : Space) R, ∫⁻ a in closedBall (0 : Space) 1, ∫⁻ s in Ioc (0 : ℝ) 1,
          H (a + s • (x - a)) := by
        refine setLIntegral_congr_fun measurableSet_closedBall (fun x hx => ?_)
        rw [setLIntegral_congr_fun (measurableSet_closedBall.prod measurableSet_Ioc) (hpt x hx),
          Measure.volume_eq_prod, setLIntegral_prod (fun z : Space × ℝ => H (z.1 + z.2 • (x - z.1)))
            ((hH.comp (by fun_prop)).aemeasurable)]
    _ ≤ 8 * volume (closedBall (0 : Space) R) * ∫⁻ y, H y := key_bound H hH R hR
    _ = _ := by rw [lintegral_indicator measurableSet_closedBall]

theorem measurable_integrand {F : Space → Space} (hF : StronglyMeasurable F) :
    StronglyMeasurable (fun p : Space × (Space × ℝ) => inner ℝ (F (p.2.1 + p.2.2 • (p.1 - p.2.1))) (p.1 - p.2.1)) :=
  (hF.comp_measurable (by fun_prop)).inner (by fun_prop : Continuous fun p : Space × (Space × ℝ) => p.1 - p.2.1).stronglyMeasurable

theorem stronglyMeasurable_avgPotential {F : Space → Space} (hF : StronglyMeasurable F) :
    StronglyMeasurable (avgPotential F) := by
  unfold avgPotential
  exact (measurable_integrand hF).integral_prod_right'

theorem norm_sub_le_of_mem {R : ℝ} {x : Space} (hx : x ∈ closedBall (0 : Space) R) {z : Space × ℝ}
    (hz : z ∈ closedBall (0 : Space) 1 ×ˢ Ioc (0 : ℝ) 1) : ‖x - z.1‖ ≤ R + 1 := by
  have h1 := mem_closedBall_zero_iff.mp hx
  have h2 := mem_closedBall_zero_iff.mp hz.1
  linarith [norm_sub_le x z.1]

theorem enorm_avgPotential_sub_le {F1 F2 : Space → Space} (hF1 : StronglyMeasurable F1)
    (hF2 : StronglyMeasurable F2) {R : ℝ} (hR : 1 ≤ R) {x : Space} (hx : x ∈ closedBall (0 : Space) R)
    (h2 : Integrable (fun z : Space × ℝ => inner ℝ (F2 (z.1 + z.2 • (x - z.1))) (x - z.1))
      (volume.restrict (closedBall (0 : Space) 1 ×ˢ Ioc (0 : ℝ) 1))) :
    ‖avgPotential F1 x - avgPotential F2 x‖ₑ ≤ ENNReal.ofReal (R + 1) *
      ∫⁻ z in closedBall (0 : Space) 1 ×ˢ Ioc (0 : ℝ) 1, ‖F1 (z.1 + z.2 • (x - z.1)) - F2 (z.1 + z.2 • (x - z.1))‖ₑ := by
  set S := closedBall (0 : Space) 1 ×ˢ Ioc (0 : ℝ) 1
  have hS : MeasurableSet S := measurableSet_closedBall.prod measurableSet_Ioc
  have hm : ∀ F : Space → Space, StronglyMeasurable F →
      AEStronglyMeasurable (fun z : Space × ℝ => inner ℝ (F (z.1 + z.2 • (x - z.1))) (x - z.1))
        (volume.restrict S) := fun F hF =>
    ((hF.comp_measurable (by fun_prop)).inner (by fun_prop : Continuous fun z : Space × ℝ => x - z.1).stronglyMeasurable).aestronglyMeasurable
  have hbd : ∀ᵐ z ∂(volume.restrict S), ‖inner ℝ (F1 (z.1 + z.2 • (x - z.1)) - F2 (z.1 + z.2 • (x - z.1))) (x - z.1)‖ₑ
      ≤ ENNReal.ofReal (R + 1) * ‖F1 (z.1 + z.2 • (x - z.1)) - F2 (z.1 + z.2 • (x - z.1))‖ₑ := by
    refine (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun z hz => ?_)
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by linarith)]
    apply ENNReal.ofReal_le_ofReal
    calc ‖inner ℝ (F1 (z.1 + z.2 • (x - z.1)) - F2 (z.1 + z.2 • (x - z.1))) (x - z.1)‖
        ≤ ‖F1 (z.1 + z.2 • (x - z.1)) - F2 (z.1 + z.2 • (x - z.1))‖ * ‖x - z.1‖ := norm_inner_le_norm _ _
      _ ≤ ‖F1 (z.1 + z.2 • (x - z.1)) - F2 (z.1 + z.2 • (x - z.1))‖ * (R + 1) := by
          gcongr
          exact norm_sub_le_of_mem hx hz
      _ = (R + 1) * ‖F1 (z.1 + z.2 • (x - z.1)) - F2 (z.1 + z.2 • (x - z.1))‖ := mul_comm _ _
  have hlin : ∫⁻ z in S, ‖inner ℝ (F1 (z.1 + z.2 • (x - z.1)) - F2 (z.1 + z.2 • (x - z.1))) (x - z.1)‖ₑ
      ≤ ENNReal.ofReal (R + 1) * ∫⁻ z in S, ‖F1 (z.1 + z.2 • (x - z.1)) - F2 (z.1 + z.2 • (x - z.1))‖ₑ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono_ae hbd
  by_cases h1 : Integrable (fun z : Space × ℝ => inner ℝ (F1 (z.1 + z.2 • (x - z.1))) (x - z.1))
      (volume.restrict S)
  · have he : avgPotential F1 x - avgPotential F2 x
        = ∫ z in S, inner ℝ (F1 (z.1 + z.2 • (x - z.1)) - F2 (z.1 + z.2 • (x - z.1))) (x - z.1) := by
      rw [avgPotential, avgPotential, ← integral_sub h1 h2]
      simp_rw [inner_sub_left]
    rw [he]
    exact (enorm_integral_le_lintegral_enorm _).trans hlin
  · have htop : ∫⁻ z in S, ‖F1 (z.1 + z.2 • (x - z.1)) - F2 (z.1 + z.2 • (x - z.1))‖ₑ = ⊤ := by
      by_contra hne
      apply h1
      have hd : Integrable (fun z : Space × ℝ => inner ℝ (F1 (z.1 + z.2 • (x - z.1)) - F2 (z.1 + z.2 • (x - z.1))) (x - z.1))
          (volume.restrict S) := by
        refine ⟨?_, ?_⟩
        · exact hm (F1 - F2) (hF1.sub hF2)
        · exact lt_of_le_of_lt hlin (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hne))
      refine (hd.add h2).congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Pi.add_apply, inner_sub_left]
      ring
    rw [htop, ENNReal.mul_top (by simp; linarith)]
    exact le_top

theorem avgPotential_zero (x : Space) : avgPotential (fun _ => 0) x = 0 := by
  simp [avgPotential]

theorem enorm_avgPotential_le {F : Space → Space} (hF : StronglyMeasurable F) {R : ℝ} (hR : 1 ≤ R) {x : Space}
    (hx : x ∈ closedBall (0 : Space) R) :
    ‖avgPotential F x‖ₑ ≤ ENNReal.ofReal (R + 1) *
      ∫⁻ z in closedBall (0 : Space) 1 ×ˢ Ioc (0 : ℝ) 1, ‖F (z.1 + z.2 • (x - z.1))‖ₑ := by
  have h := enorm_avgPotential_sub_le (F2 := fun _ => 0) hF stronglyMeasurable_const hR hx (by simp)
  simpa [avgPotential_zero] using h

theorem measurable_region_lintegral {G : Space → ℝ≥0∞} (hG : Measurable G) :
    Measurable (fun x : Space => ∫⁻ z in closedBall (0 : Space) 1 ×ˢ Ioc (0 : ℝ) 1, G (z.1 + z.2 • (x - z.1))) :=
  (hG.comp (by fun_prop : Measurable fun p : Space × (Space × ℝ) => p.2.1 + p.2.2 • (p.1 - p.2.1))).lintegral_prod_right'

theorem lintegral_avgPotential_sub_le {F1 F2 : Space → Space} (hF1 : StronglyMeasurable F1)
    (hF2 : StronglyMeasurable F2) {R : ℝ} (hR : 1 ≤ R)
    (h2 : ∀ x, Integrable (fun z : Space × ℝ => inner ℝ (F2 (z.1 + z.2 • (x - z.1))) (x - z.1))
      (volume.restrict (closedBall (0 : Space) 1 ×ˢ Ioc (0 : ℝ) 1))) :
    ∫⁻ x in closedBall (0 : Space) R, ‖avgPotential F1 x - avgPotential F2 x‖ₑ ≤
      ENNReal.ofReal (R + 1) * (8 * volume (closedBall (0 : Space) R) *
        ∫⁻ y in closedBall (0 : Space) R, ‖F1 y - F2 y‖ₑ) := by
  have hG : Measurable (fun y => ‖F1 y - F2 y‖ₑ) := (hF1.sub hF2).measurable.enorm
  calc ∫⁻ x in closedBall (0 : Space) R, ‖avgPotential F1 x - avgPotential F2 x‖ₑ
      ≤ ∫⁻ x in closedBall (0 : Space) R, ENNReal.ofReal (R + 1) *
          ∫⁻ z in closedBall (0 : Space) 1 ×ˢ Ioc (0 : ℝ) 1, ‖F1 (z.1 + z.2 • (x - z.1)) - F2 (z.1 + z.2 • (x - z.1))‖ₑ :=
        setLIntegral_mono' measurableSet_closedBall fun x hx => enorm_avgPotential_sub_le hF1 hF2 hR hx (h2 x)
    _ = ENNReal.ofReal (R + 1) * ∫⁻ x in closedBall (0 : Space) R,
          ∫⁻ z in closedBall (0 : Space) 1 ×ˢ Ioc (0 : ℝ) 1, ‖F1 (z.1 + z.2 • (x - z.1)) - F2 (z.1 + z.2 • (x - z.1))‖ₑ :=
        lintegral_const_mul _ (measurable_region_lintegral hG)
    _ ≤ _ := by
        gcongr
        exact region_bound _ hG R hR

theorem lintegral_avgPotential_sq_le {F : Space → Space} (hF : StronglyMeasurable F) {R : ℝ} (hR : 1 ≤ R) :
    ∫⁻ x in closedBall (0 : Space) R, ‖avgPotential F x‖ₑ ^ 2 ≤
      ENNReal.ofReal (R + 1) ^ 2 * volume (closedBall (0 : Space) 1 ×ˢ Ioc (0 : ℝ) 1) *
        (8 * volume (closedBall (0 : Space) R) * ∫⁻ y in closedBall (0 : Space) R, ‖F y‖ₑ ^ 2) := by
  set S := closedBall (0 : Space) 1 ×ˢ Ioc (0 : ℝ) 1
  have hG : Measurable (fun y => ‖F y‖ₑ ^ 2) := hF.measurable.enorm.pow_const 2
  have hpt : ∀ x ∈ closedBall (0 : Space) R, ‖avgPotential F x‖ₑ ^ 2 ≤
      ENNReal.ofReal (R + 1) ^ 2 * volume S * ∫⁻ z in S, ‖F (z.1 + z.2 • (x - z.1))‖ₑ ^ 2 := by
    intro x hx
    calc ‖avgPotential F x‖ₑ ^ 2 ≤ (ENNReal.ofReal (R + 1) * ∫⁻ z in S, ‖F (z.1 + z.2 • (x - z.1))‖ₑ) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (enorm_avgPotential_le hF hR hx) 2
      _ = ENNReal.ofReal (R + 1) ^ 2 * (∫⁻ z in S, ‖F (z.1 + z.2 • (x - z.1))‖ₑ) ^ 2 := mul_pow _ _ _
      _ ≤ ENNReal.ofReal (R + 1) ^ 2 * ((volume.restrict S) univ * ∫⁻ z in S, ‖F (z.1 + z.2 • (x - z.1))‖ₑ ^ 2) := by
          gcongr
          exact lintegral_sq_le _ ((hF.measurable.comp (by fun_prop)).enorm.aemeasurable)
      _ = _ := by rw [Measure.restrict_apply_univ, mul_assoc]
  calc ∫⁻ x in closedBall (0 : Space) R, ‖avgPotential F x‖ₑ ^ 2
      ≤ ∫⁻ x in closedBall (0 : Space) R, ENNReal.ofReal (R + 1) ^ 2 * volume S *
          ∫⁻ z in S, ‖F (z.1 + z.2 • (x - z.1))‖ₑ ^ 2 := setLIntegral_mono' measurableSet_closedBall hpt
    _ = ENNReal.ofReal (R + 1) ^ 2 * volume S * ∫⁻ x in closedBall (0 : Space) R,
          ∫⁻ z in S, ‖F (z.1 + z.2 • (x - z.1))‖ₑ ^ 2 := lintegral_const_mul _ (measurable_region_lintegral hG)
    _ ≤ _ := by
        gcongr
        exact region_bound _ hG R hR

theorem integrable_mul_of_supp {ψ h : Space → ℝ} {R M : ℝ} (hψ : Continuous ψ) (hM : ∀ x, ‖ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ closedBall (0 : Space) R) (hh : IntegrableOn h (closedBall (0 : Space) R)) :
    Integrable (fun x => ψ x * h x) := by
  have h1 : IntegrableOn (fun x => ψ x * h x) (closedBall (0 : Space) R) :=
    Integrable.bdd_mul (f := ψ) hh hψ.aestronglyMeasurable (ae_of_all _ hM)
  exact h1.integrable_of_forall_notMem_eq_zero fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun h' => hx (hs h')), zero_mul]

theorem enorm_integral_mul_le {ψ h : Space → ℝ} {R M : ℝ} (hM : ∀ x, ‖ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ closedBall (0 : Space) R) :
    ‖∫ x, ψ x * h x‖ₑ ≤ ENNReal.ofReal M * ∫⁻ x in closedBall (0 : Space) R, ‖h x‖ₑ := by
  have he : (fun x => ‖ψ x * h x‖ₑ) = (closedBall (0 : Space) R).indicator (fun x => ‖ψ x * h x‖ₑ) := by
    funext x
    by_cases hx : x ∈ closedBall (0 : Space) R
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun h' => hx (hs h')), zero_mul, enorm_zero]
  calc ‖∫ x, ψ x * h x‖ₑ ≤ ∫⁻ x, ‖ψ x * h x‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ x in closedBall (0 : Space) R, ‖ψ x * h x‖ₑ := by
        conv_lhs => rw [he]
        rw [lintegral_indicator measurableSet_closedBall]
    _ ≤ ∫⁻ x in closedBall (0 : Space) R, ENNReal.ofReal M * ‖h x‖ₑ := by
        refine lintegral_mono fun x => ?_
        rw [enorm_mul, ← ofReal_norm (ψ x)]
        gcongr
        exact hM x
    _ = ENNReal.ofReal M * ∫⁻ x in closedBall (0 : Space) R, ‖h x‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem continuous_avgPotential {F : Space → Space} (hF : ContDiff ℝ 1 F)
    (hs : ∀ z v w, inner ℝ (fderiv ℝ F z v) w = inner ℝ (fderiv ℝ F z w) v) : Continuous (avgPotential F) := by
  have he : avgPotential F = fun x => volume.real (closedBall (0 : Space) 1) * radialPotential F x
      - ∫ a in closedBall (0 : Space) 1, radialPotential F a := funext (avgPotential_eq hF hs)
  rw [he]
  exact (continuous_const.mul (continuous_radialPotential hF hs)).sub continuous_const

theorem integrand_integrable_of_continuous {F : Space → Space} (hF : Continuous F) (x : Space) :
    Integrable (fun z : Space × ℝ => inner ℝ (F (z.1 + z.2 • (x - z.1))) (x - z.1))
      (volume.restrict (closedBall (0 : Space) 1 ×ˢ Ioc (0 : ℝ) 1)) := by
  have hcont : Continuous (fun z : Space × ℝ => inner ℝ (F (z.1 + z.2 • (x - z.1))) (x - z.1)) := by
    fun_prop
  exact (hcont.continuousOn.integrableOn_compact ((isCompact_closedBall _ _).prod isCompact_Icc)).mono_set
    (prod_mono le_rfl Ioc_subset_Icc_self)

theorem weak_identity {P : Space → Space} (hP : StronglyMeasurable P) (hPloc : LocallyIntegrable P volume)
    (hann : ∀ φ : Space → Space, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ y, divergenceAt φ y = 0) →
      ∫ y, inner ℝ (P y) (φ y) = 0)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) {v : Space} (hv : ‖v‖ ≤ 1) :
    ∫ x, fderiv ℝ φ x v * avgPotential P x
      = -(volume.real (closedBall (0 : Space) 1) * ∫ x, φ x * inner ℝ (P x) v) := by
  set m := volume.real (closedBall (0 : Space) 1)
  obtain ⟨r, hr⟩ := hφc.isCompact.isBounded.subset_closedBall (0 : Space)
  set R := max r 1
  have hR : 1 ≤ R := le_max_right _ _
  have hsupp : tsupport φ ⊆ closedBall (0 : Space) R :=
    hr.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hsupp' : tsupport (fun x => fderiv ℝ φ x v) ⊆ closedBall (0 : Space) R :=
    (tsupport_fderiv_apply_subset ℝ v).trans hsupp
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_cast)
  have hφ'c : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨M1, hStrain⟩ := hφ'c.bounded_above_of_compact_support (hφc.fderiv_apply ℝ v)
  obtain ⟨M0, hM0⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hPR : IntegrableOn P (closedBall (0 : Space) R) := hPloc.integrableOn_isCompact (isCompact_closedBall _ _)
  have hPv : IntegrableOn (fun x => inner ℝ (P x) v) (closedBall (0 : Space) R) := by
    have := (innerSL ℝ v).integrable_comp hPR
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [real_inner_comm]
  have hV : volume (closedBall (0 : Space) R) ≠ ⊤ := measure_closedBall_lt_top.ne
  have haP : IntegrableOn (avgPotential P) (closedBall (0 : Space) R) := by
    refine ⟨(stronglyMeasurable_avgPotential hP).aestronglyMeasurable, ?_⟩
    have h := lintegral_avgPotential_sub_le hP stronglyMeasurable_const hR (F2 := fun _ => 0) (fun x => by simp)
    simp only [avgPotential_zero, sub_zero] at h
    refine lt_of_le_of_lt h ?_
    have hfin : ∫⁻ y in closedBall (0 : Space) R, ‖P y‖ₑ < ⊤ := hPR.2
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) measure_closedBall_lt_top) hfin)
  set D := (∫ x, fderiv ℝ φ x v * avgPotential P x) + m * ∫ x, φ x * inner ℝ (P x) v with hDdef
  suffices hD : D = 0 by linarith
  set K : ℝ≥0∞ := ENNReal.ofReal M1 * (ENNReal.ofReal (R + 1) * (8 * volume (closedBall (0 : Space) R)))
    + ‖m‖ₑ * ENNReal.ofReal M0 with hKdef
  have hK : K ≠ ⊤ := by
    simp [K, ENNReal.mul_eq_top]
  have hmain : ∀ ε : ℝ≥0∞, ε ≠ 0 → ‖D‖ₑ ≤ K * ε := by
    intro ε hε
    obtain ⟨ρ, hρ, hρc, hρε⟩ := approx_mollify hP hPloc R hε
    set F := mollify P ρ
    have hF : ContDiff ℝ ∞ F := mollify_contDiff hPloc hρ hρc
    have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_cast)
    have hFs := mollify_symm hPloc hann hρ hρc
    have hFw := avgPotential_weak hF1 hFs hφ1 hφc v
    have hFc : Continuous F := hF.continuous
    have haF : Continuous (avgPotential F) := continuous_avgPotential hF1 hFs
    have i1 : Integrable (fun x => fderiv ℝ φ x v * avgPotential P x) :=
      integrable_mul_of_supp hφ'c hStrain hsupp' haP
    have i2 : Integrable (fun x => fderiv ℝ φ x v * avgPotential F x) :=
      integrable_mul_of_supp hφ'c hStrain hsupp' (haF.continuousOn.integrableOn_compact (isCompact_closedBall _ _))
    have hFv : Continuous (fun x => inner ℝ (F x) v) := hFc.inner continuous_const
    have i3 : Integrable (fun x => φ x * inner ℝ (P x) v) := integrable_mul_of_supp hφ.continuous hM0 hsupp hPv
    have i4 : Integrable (fun x => φ x * inner ℝ (F x) v) :=
      integrable_mul_of_supp hφ.continuous hM0 hsupp (hFv.continuousOn.integrableOn_compact (isCompact_closedBall _ _))
    have hDeq : D = (∫ x, fderiv ℝ φ x v * (avgPotential P x - avgPotential F x))
        + m * ∫ x, φ x * inner ℝ (P x - F x) v := by
      simp_rw [mul_sub, inner_sub_left, mul_sub]
      rw [integral_sub i1 i2, integral_sub i3 i4, hFw]
      ring
    have hPF : ∫⁻ y in closedBall (0 : Space) R, ‖P y - F y‖ₑ ≤ ε := by
      simp_rw [enorm_sub_rev (P _)]
      exact hρε
    have hA : ‖∫ x, fderiv ℝ φ x v * (avgPotential P x - avgPotential F x)‖ₑ ≤
        ENNReal.ofReal M1 * (ENNReal.ofReal (R + 1) * (8 * volume (closedBall (0 : Space) R))) * ε := by
      calc ‖∫ x, fderiv ℝ φ x v * (avgPotential P x - avgPotential F x)‖ₑ
          ≤ ENNReal.ofReal M1 * ∫⁻ x in closedBall (0 : Space) R, ‖avgPotential P x - avgPotential F x‖ₑ :=
            enorm_integral_mul_le hStrain hsupp'
        _ ≤ ENNReal.ofReal M1 * (ENNReal.ofReal (R + 1) * (8 * volume (closedBall (0 : Space) R) *
              ∫⁻ y in closedBall (0 : Space) R, ‖P y - F y‖ₑ)) := by
            gcongr
            exact lintegral_avgPotential_sub_le hP hFc.stronglyMeasurable hR
              (integrand_integrable_of_continuous hFc)
        _ = ENNReal.ofReal M1 * (ENNReal.ofReal (R + 1) * (8 * volume (closedBall (0 : Space) R))) *
              ∫⁻ y in closedBall (0 : Space) R, ‖P y - F y‖ₑ := by ring
        _ ≤ _ := by gcongr
    have hB : ‖∫ x, φ x * inner ℝ (P x - F x) v‖ₑ ≤ ENNReal.ofReal M0 * ε := by
      calc ‖∫ x, φ x * inner ℝ (P x - F x) v‖ₑ
          ≤ ENNReal.ofReal M0 * ∫⁻ x in closedBall (0 : Space) R, ‖inner ℝ (P x - F x) v‖ₑ :=
            enorm_integral_mul_le hM0 hsupp
        _ ≤ ENNReal.ofReal M0 * ∫⁻ x in closedBall (0 : Space) R, ‖P x - F x‖ₑ := by
            gcongr with x
            rw [← ofReal_norm, ← ofReal_norm]
            apply ENNReal.ofReal_le_ofReal
            calc ‖inner ℝ (P x - F x) v‖ ≤ ‖P x - F x‖ * ‖v‖ := norm_inner_le_norm _ _
              _ ≤ ‖P x - F x‖ := by nlinarith [norm_nonneg (P x - F x), norm_nonneg v]
        _ ≤ _ := by gcongr
    calc ‖D‖ₑ = ‖(∫ x, fderiv ℝ φ x v * (avgPotential P x - avgPotential F x))
          + m * ∫ x, φ x * inner ℝ (P x - F x) v‖ₑ := by rw [hDeq]
      _ ≤ ‖∫ x, fderiv ℝ φ x v * (avgPotential P x - avgPotential F x)‖ₑ
          + ‖m‖ₑ * ‖∫ x, φ x * inner ℝ (P x - F x) v‖ₑ := by
          refine (enorm_add_le _ _).trans ?_
          rw [enorm_mul]
      _ ≤ ENNReal.ofReal M1 * (ENNReal.ofReal (R + 1) * (8 * volume (closedBall (0 : Space) R))) * ε
          + ‖m‖ₑ * (ENNReal.ofReal M0 * ε) := by gcongr
      _ = K * ε := by rw [hKdef]; ring
  have hz : ‖D‖ₑ = 0 := by
    refine le_antisymm ?_ (by positivity)
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    have hK1 : K + 1 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hK, ENNReal.one_ne_top⟩
    have hδ' : (δ : ℝ≥0∞) / (K + 1) ≠ 0 := (ENNReal.div_pos (by simpa using hδ.ne') hK1).ne'
    calc ‖D‖ₑ ≤ K * ((δ : ℝ≥0∞) / (K + 1)) := hmain _ hδ'
      _ ≤ (K + 1) * ((δ : ℝ≥0∞) / (K + 1)) := by gcongr; exact le_self_add
      _ = δ := ENNReal.mul_div_cancel (by simp) hK1
      _ = 0 + δ := (zero_add _).symm
  exact enorm_eq_zero.mp hz

theorem gradient_of_annihilator (Q : Space → Space) (hQm : AEStronglyMeasurable Q volume)
    (hQ2 : IsLocalSquareIntegrable (fun y => ‖Q y‖ ^ 2))
    (hann : ∀ φ : Space → Space, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ y, divergenceAt φ y = 0) →
      ∫ y, inner ℝ (Q y) (φ y) = 0) : IsGradientField Q := by
  set P := hQm.mk Q
  have hP : StronglyMeasurable P := hQm.stronglyMeasurable_mk
  have hQP : Q =ᵐ[volume] P := hQm.ae_eq_mk
  have hP2 : ∀ K : Set Space, IsCompact K → IntegrableOn (fun y => ‖P y‖ ^ 2) K := by
    intro K hK
    refine (hQ2 K hK).congr_fun_ae ?_
    filter_upwards [ae_restrict_of_ae hQP] with y hy
    rw [hy]
  have hPloc : LocallyIntegrable P volume := by
    refine locallyIntegrable_iff.2 fun K hK => ?_
    refine Integrable.mono'
      (((continuous_const : Continuous fun _ : Space => (1 : ℝ)).continuousOn.integrableOn_compact hK).add (hP2 K hK))
      hP.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    simp only [Pi.add_apply]
    nlinarith [norm_nonneg (P y)]
  have hPann : ∀ φ : Space → Space, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ y, divergenceAt φ y = 0) →
      ∫ y, inner ℝ (P y) (φ y) = 0 := by
    intro φ h1 h2 h3
    rw [← hann φ h1 h2 h3]
    exact integral_congr_ae (hQP.mono fun y hy => by simp only [hy])
  set m := volume.real (closedBall (0 : Space) 1)
  have hm : 0 < m := ENNReal.toReal_pos (measure_closedBall_pos _ _ one_pos).ne' measure_closedBall_lt_top.ne
  refine ⟨fun y => m⁻¹ * avgPotential P y, ?_, hQ2, hQm, ?_⟩
  · intro K hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : Space)
    have hR : (1 : ℝ) ≤ max r 1 := le_max_right _ _
    have hKR : K ⊆ closedBall (0 : Space) (max r 1) := hr.trans (closedBall_subset_closedBall (le_max_left _ _))
    refine IntegrableOn.mono_set ⟨((stronglyMeasurable_const.mul (stronglyMeasurable_avgPotential hP)).pow
      2).aestronglyMeasurable, ?_⟩ hKR
    show ∫⁻ y in closedBall (0 : Space) (max r 1), ‖(m⁻¹ * avgPotential P y) ^ 2‖ₑ < ⊤
    simp_rw [enorm_pow, enorm_mul, mul_pow]
    rw [lintegral_const_mul' _ _ (by simp)]
    refine ENNReal.mul_lt_top (by simp) (lt_of_le_of_lt (lintegral_avgPotential_sq_le hP hR) ?_)
    have hfin : ∫⁻ y in closedBall (0 : Space) (max r 1), ‖P y‖ₑ ^ 2 < ⊤ := by
      have := (hP2 _ (isCompact_closedBall (0 : Space) (max r 1))).2
      simpa [HasFiniteIntegral, enorm_pow] using this
    have hS : volume (closedBall (0 : Space) 1 ×ˢ Ioc (0 : ℝ) 1) < ⊤ :=
      lt_of_le_of_lt (measure_mono (prod_mono le_rfl Ioc_subset_Icc_self))
        ((isCompact_closedBall _ _).prod isCompact_Icc).measure_lt_top
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) hS)
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) measure_closedBall_lt_top) hfin)
  · intro φ hφ j
    have hv : ‖unitVector j‖ ≤ 1 := by simp [unitVector]
    have h := weak_identity hP hPloc hPann hφ.1 hφ.2 hv
    have hQe : ∫ y, φ y * inner ℝ (Q y) (unitVector j) = ∫ y, φ y * inner ℝ (P y) (unitVector j) :=
      integral_congr_ae (hQP.mono fun y hy => by simp only [hy])
    have hfun : (fun y => fderiv ℝ φ y (unitVector j) * (m⁻¹ * avgPotential P y))
        = fun y => m⁻¹ * (fderiv ℝ φ y (unitVector j) * avgPotential P y) := funext fun y => by ring
    simp only [hQe, hfun]
    rw [integral_const_mul, h, mul_neg, ← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]

end Breakdown.CertCell.AnnihilatorGradient.Internal
