import Breakdown.FracCell.EnergyRadialParts
import Breakdown.FracCell.ModeRadialLine
import Breakdown.FracCell.ModeRectIntegrable
import Breakdown.FracCell.CylModeWeak

open scoped ContDiff
open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown.CellCert.CellEnergy.RadialTraceInternal

open CellAnalysis CellFormula SteadyCert Assembly
open Breakdown.CellCert.CellAnalysis.ModeRadialLineInternal

theorem deriv_bound {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (a b : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ r ∈ Icc a b, |deriv χ r| ≤ M := by
  have hc : Continuous (deriv χ) := hχ.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun r hr => (hM r hr).trans (le_max_left _ _)⟩

theorem lin_bound {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) {a b : ℝ} (ha : χ a = 0) :
    ∃ M, 0 ≤ M ∧ ∀ r ∈ Icc a b, |χ r| ≤ M * (r - a) := by
  obtain ⟨M, hM0, hM⟩ := deriv_bound hχ a b
  refine ⟨M, hM0, fun r hr => ?_⟩
  have hd : ∀ x, DifferentiableAt ℝ χ x := fun x => (hχ.differentiable one_ne_zero).differentiableAt
  have hc : Continuous (deriv χ) := hχ.continuous_deriv le_rfl
  have e : ∫ x in a..r, deriv χ x = χ r - χ a :=
    intervalIntegral.integral_deriv_eq_sub' χ rfl (fun x _ => hd x) hc.continuousOn
  rw [ha, sub_zero] at e
  rw [← e]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := r) (C := M)
    (f := deriv χ) (fun x hx => by
      rw [Real.norm_eq_abs]
      refine hM x ⟨?_, ?_⟩
      · rw [uIoc_of_le hr.1] at hx; exact hx.1.le
      · rw [uIoc_of_le hr.1] at hx; exact hx.2.trans hr.2)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hr.1)] at h
  exact h

theorem tail_ibp {a b : ℝ} (_hab : a ≤ b) {A : ℝ → ℂ}
    (hAm : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hA : IntegrableOn (fun u => ((u - a : ℝ) : ℂ) * A u) (Icc a b))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (hχa : χ a = 0) :
    ∫ z in Icc a b, (∫ u in z..b, A u) * ((deriv χ z : ℝ) : ℂ) = ∫ u in Icc a b, A u * ((χ u : ℝ) : ℂ) := by
  set μ := volume.restrict (Icc a b)
  set k : ℝ → ℂ := fun z => ((deriv χ z : ℝ) : ℂ) with hk
  have hkc : Continuous k := Complex.continuous_ofReal.comp (hχ.continuous_deriv le_rfl)
  obtain ⟨M, hM0, hM⟩ := deriv_bound hχ a b
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} := measurableSet_le measurable_fst measurable_snd
  set f : ℝ × ℝ → ℂ := {p : ℝ × ℝ | p.1 ≤ p.2}.indicator (fun p => A p.2 * k p.1) with hf
  have hfm : AEStronglyMeasurable f (μ.prod μ) :=
    (hAm.comp_snd.mul (hkc.comp continuous_fst).aestronglyMeasurable).indicator hmeas
  have hd : ∀ x, DifferentiableAt ℝ χ x := fun x => (hχ.differentiable one_ne_zero).differentiableAt
  have hprim : ∀ u, ∫ z in a..u, k z = ((χ u : ℝ) : ℂ) := by
    intro u
    rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_deriv_eq_sub' χ rfl (fun x _ => hd x)
      (hχ.continuous_deriv le_rfl).continuousOn, hχa, sub_zero]
  have hslice : ∀ u ∈ Icc a b, ∫ z in Icc a b, f (z, u) = A u * ((χ u : ℝ) : ℂ) := by
    intro u hu
    have e : (fun z => f (z, u)) = (Iic u).indicator (fun z => A u * k z) := by
      funext z
      simp [hf, Set.indicator]
    rw [e, setIntegral_indicator measurableSet_Iic, integral_const_mul]
    congr 1
    have hs : Icc a b ∩ Iic u = Icc a u := by
      ext z
      simp only [mem_inter_iff, mem_Icc, mem_Iic]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, le_trans h3 hu.2⟩, h3⟩
    rw [hs, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu.1, hprim]
  have hslice2 : ∀ z ∈ Icc a b, ∫ u in Icc a b, f (z, u) = (∫ u in z..b, A u) * k z := by
    intro z hz
    have e : (fun u => f (z, u)) = (Ici z).indicator (fun u => A u * k z) := by
      funext u
      simp [hf, Set.indicator]
    rw [e, setIntegral_indicator measurableSet_Ici, integral_mul_const]
    congr 1
    have hs : Icc a b ∩ Ici z = Icc z b := by
      ext u
      simp only [mem_inter_iff, mem_Icc, mem_Ici]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨le_trans hz.1 h1, h3⟩, h1⟩
    rw [hs, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hz.2]
  have hint : Integrable f (μ.prod μ) := by
    rw [integrable_prod_iff' hfm]
    constructor
    · refine Eventually.of_forall fun u => ?_
      have e : (fun z => f (z, u)) = (Iic u).indicator (fun z => A u * k z) := by
        funext z
        simp [hf, Set.indicator]
      rw [e]
      exact ((hkc.continuousOn.integrableOn_compact isCompact_Icc).const_mul (A u)).indicator measurableSet_Iic
    · have hval : ∀ u ∈ Icc a b, ∫ z, ‖f (z, u)‖ ∂μ = ‖A u‖ * ∫ z in a..u, ‖k z‖ := by
        intro u hu
        have e : (fun z => ‖f (z, u)‖) = (Iic u).indicator (fun z => ‖A u‖ * ‖k z‖) := by
          funext z
          by_cases h : z ≤ u
          · simp [hf, Set.indicator, h]
          · simp [hf, Set.indicator, h]
        rw [e, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic, integral_const_mul]
        congr 1
        have hs : Iic u ∩ Icc a b = Icc a u := by
          ext z
          simp only [mem_inter_iff, mem_Icc, mem_Iic]
          constructor
          · rintro ⟨h3, h1, _⟩; exact ⟨h1, h3⟩
          · rintro ⟨h1, h3⟩; exact ⟨h3, h1, le_trans h3 hu.2⟩
        rw [hs, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu.1]
      have hpc : Continuous (fun u => ∫ z in a..u, ‖k z‖) :=
        intervalIntegral.continuous_primitive (fun _ _ => (continuous_norm.comp hkc).intervalIntegrable _ _) a
      have hI : Integrable (fun u => ‖A u‖ * ∫ z in a..u, ‖k z‖) μ := by
        refine Integrable.mono' (hA.norm.const_mul M) (hAm.norm.mul hpc.aestronglyMeasurable) ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := u) (C := M)
          (f := fun z => ‖k z‖) (fun x hx => by
            rw [norm_norm, hk, Complex.norm_real, Real.norm_eq_abs]
            rw [uIoc_of_le hu.1] at hx
            exact hM x ⟨hx.1.le, hx.2.trans hu.2⟩)
        rw [abs_of_nonneg (sub_nonneg.2 hu.1)] at hb
        rw [Real.norm_eq_abs] at hb
        rw [norm_mul, norm_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.2 hu.1)]
        calc ‖A u‖ * |∫ z in a..u, ‖k z‖| ≤ ‖A u‖ * (M * (u - a)) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
          _ = M * ((u - a) * ‖A u‖) := by ring
      refine hI.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      exact (hval u hu).symm
  have hswap := integral_integral_swap (μ := μ) (ν := μ) (f := fun z u => f (z, u)) hint
  rw [← setIntegral_congr_fun measurableSet_Icc hslice2, ← setIntegral_congr_fun measurableSet_Icc hslice]
  exact hswap

theorem line_ibp {a b : ℝ} (hab : a < b) {u g : ℝ → ℂ} (hu : IntegrableOn u (Icc a b))
    (hgm : AEStronglyMeasurable g (volume.restrict (Icc a b)))
    (hg : IntegrableOn (fun r => ((r - a : ℝ) : ℂ) * g r) (Icc a b))
    {L : ℂ} (hL : ∀ᵐ x ∂(volume.restrict (Icc a b)), u x = L - ∫ t in x..b, g t)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (ha : χ a = 0) (hb : χ b = 0) :
    ∫ r in Icc a b, (g r * ((χ r : ℝ) : ℂ) + u r * ((deriv χ r : ℝ) : ℂ)) = 0 := by
  obtain ⟨M, hM0, hM⟩ := lin_bound hχ (b := b) ha
  have hkc : Continuous (fun r => ((deriv χ r : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hχ.continuous_deriv le_rfl)
  have hχc : Continuous (fun r => ((χ r : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hχ.continuous
  have h1 : IntegrableOn (fun r => g r * ((χ r : ℝ) : ℂ)) (Icc a b) := by
    refine Integrable.mono' (hg.norm.const_mul M) (hgm.mul hχc.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.2 hr.1)]
    calc ‖g r‖ * |χ r| ≤ ‖g r‖ * (M * (r - a)) := mul_le_mul_of_nonneg_left (hM r hr) (norm_nonneg _)
      _ = M * ((r - a) * ‖g r‖) := by ring
  have h2 : IntegrableOn (fun r => u r * ((deriv χ r : ℝ) : ℂ)) (Icc a b) :=
    hu.mul_continuousOn hkc.continuousOn isCompact_Icc
  have hkI : IntegrableOn (fun r => ((deriv χ r : ℝ) : ℂ)) (Icc a b) :=
    hkc.continuousOn.integrableOn_compact isCompact_Icc
  have hLk : IntegrableOn (fun r => L * ((deriv χ r : ℝ) : ℂ)) (Icc a b) := hkI.const_mul L
  have hT : IntegrableOn (fun r => (∫ t in r..b, g t) * ((deriv χ r : ℝ) : ℂ)) (Icc a b) := by
    refine (hLk.sub h2).congr ?_
    filter_upwards [hL] with r hr
    simp only [Pi.sub_apply, hr]
    ring
  have hk0 : ∫ r in Icc a b, ((deriv χ r : ℝ) : ℂ) = 0 := by
    have hd : ∀ x, DifferentiableAt ℝ χ x := fun x => (hχ.differentiable one_ne_zero).differentiableAt
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_deriv_eq_sub' χ rfl (fun x _ => hd x) (hχ.continuous_deriv le_rfl).continuousOn,
      ha, hb, sub_zero, Complex.ofReal_zero]
  have hu' : ∫ r in Icc a b, u r * ((deriv χ r : ℝ) : ℂ) =
      ∫ r in Icc a b, (L * ((deriv χ r : ℝ) : ℂ) - (∫ t in r..b, g t) * ((deriv χ r : ℝ) : ℂ)) := by
    refine integral_congr_ae ?_
    filter_upwards [hL] with r hr
    rw [hr]
    ring
  rw [integral_add h1 h2, hu', integral_sub hLk hT, integral_const_mul, hk0,
    tail_ibp hab.le hgm hg hχ ha]
  ring

def IsRadialWeak (F D : ℝ × ℝ → ℂ) : Prop :=
  ∀ Ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ Ψ → HasCompactSupport Ψ → (∀ p ∈ tsupport Ψ, 0 < p.1) →
    ∫ p, ((fderiv ℝ Ψ p (1, 0) : ℝ) : ℂ) * F p = -∫ p, ((Ψ p : ℝ) : ℂ) * D p

theorem step_smooth (k : ℕ) : ContDiff ℝ ∞ (step k) := by
  have hd : deriv (step k) = kern k := funext fun s => (step_hasDeriv k s).deriv
  refine contDiff_infty_iff_deriv.2 ⟨fun s => (step_hasDeriv k s).differentiableAt, ?_⟩
  rw [hd]
  exact (bumpAt k).contDiff_normed (n := ⊤)

theorem test_smooth (k : ℕ) (x y : ℝ) : ContDiff ℝ ∞ (test k x y) := by
  unfold test
  exact ((step_smooth k).comp (contDiff_id.sub contDiff_const)).sub
    ((step_smooth k).comp (contDiff_id.sub contDiff_const))

theorem test_out (k : ℕ) {x y r : ℝ} (h : r ≤ min x y - width k ∨ max x y + width k ≤ r) :
    test k x y r = 0 ∧ deriv (test k x y) r = 0 := by
  rcases h with h | h
  · have hx : r ≤ x - width k := h.trans (by linarith [min_le_left x y])
    have hy : r ≤ y - width k := h.trans (by linarith [min_le_right x y])
    refine ⟨test_left k hx hy, ?_⟩
    have hw := width_pos k
    rw [test_deriv, kern_zero k (t := r - x), kern_zero k (t := r - y), sub_zero]
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith)]; linarith
  · have hx : x + width k ≤ r := le_trans (by linarith [le_max_left x y]) h
    have hy : y + width k ≤ r := le_trans (by linarith [le_max_right x y]) h
    refine ⟨test_right k hx hy, ?_⟩
    have hw := width_pos k
    rw [test_deriv, kern_zero k (t := r - x), kern_zero k (t := r - y), sub_zero]
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith

theorem prod_fderiv (k : ℕ) (x y : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => test k x y q.1 * g q.2) p (1, 0) = deriv (test k x y) p.1 * g p.2 := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => test k x y q.1)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv (test k x y) p.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
    ((test_smooth k x y).differentiable (by simp) p.1).hasDerivAt.hasFDerivAt.comp p hasFDerivAt_fst
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => g q.2)
      ((fderiv ℝ g p.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    ((hg.differentiable (by simp) p.2).hasFDerivAt).comp p hasFDerivAt_snd
  have h3 : HasFDerivAt (fun q : ℝ × ℝ => test k x y q.1 * g q.2)
      (test k x y p.1 • ((fderiv ℝ g p.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) +
        g p.2 • ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv (test k x y) p.1)).comp
          (ContinuousLinearMap.fst ℝ ℝ ℝ))) p := h1.mul h2
  rw [h3.fderiv]
  simp [mul_comm]

theorem slice_vanish (K : CellBox) (hK : IsCellBox K) {F D : ℝ × ℝ → ℂ} (hW : IsRadialWeak F D)
    (hF : IntegrableOn F K.rect) (hDw : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * D p) K.rect)
    (k : ℕ) {x y : ℝ} (hx1 : K.r₁ < x - width k) (hx2 : x + width k < K.r₂)
    (hy1 : K.r₁ < y - width k) (hy2 : y + width k < K.r₂) :
    ∀ᵐ z ∂(volume.restrict (Icc K.z₁ K.z₂)), ∫ r in Icc K.r₁ K.r₂,
      (((deriv (test k x y) r : ℝ) : ℂ) * F (r, z) + ((test k x y r : ℝ) : ℂ) * D (r, z)) = 0 := by
  set Φ : ℝ × ℝ → ℂ := fun p => ((deriv (test k x y) p.1 : ℝ) : ℂ) * F p + ((test k x y p.1 : ℝ) : ℂ) * D p
    with hΦdef
  have hΦ : IntegrableOn Φ K.rect := integrable_weak_integrand K hK hF hDw k hx1 hy1
  have hrect : volume.restrict K.rect =
      (volume.restrict (Icc K.r₁ K.r₂)).prod (volume.restrict (Icc K.z₁ K.z₂)) := rect_measure _ _ _ _
  have hΦp : Integrable Φ ((volume.restrict (Icc K.r₁ K.r₂)).prod (volume.restrict (Icc K.z₁ K.z₂))) := by
    rw [← hrect]; exact hΦ
  set h : ℝ → ℂ := fun z => ∫ r in Icc K.r₁ K.r₂, Φ (r, z) with hhdef
  have hh : IntegrableOn h (Icc K.z₁ K.z₂) := hΦp.integral_prod_right
  have hlo : 0 < min x y - width k := by
    have := hK.r_order.1
    rcases min_choice x y with e | e <;> rw [e] <;> linarith
  have hout : ∀ r, r ∉ Icc (min x y - width k) (max x y + width k) →
      test k x y r = 0 ∧ deriv (test k x y) r = 0 := by
    intro r hr
    simp only [mem_Icc, not_and_or, not_le] at hr
    rcases hr with hr | hr
    · exact test_out k (Or.inl hr.le)
    · exact test_out k (Or.inr hr.le)
  have hsubr : Icc (min x y - width k) (max x y + width k) ⊆ Icc K.r₁ K.r₂ := by
    intro r hr
    constructor
    · have : K.r₁ < min x y - width k := by
        rcases min_choice x y with e | e <;> rw [e] <;> linarith
      linarith [hr.1]
    · have : max x y + width k < K.r₂ := by
        rcases max_choice x y with e | e <;> rw [e] <;> linarith
      linarith [hr.2]
  have key : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ioo K.z₁ K.z₂ →
      ∫ z, g z • h z = 0 := by
    intro g hg hgc hgU
    have hg0 : ∀ z, z ∉ Icc K.z₁ K.z₂ → g z = 0 := fun z hz =>
      image_eq_zero_of_notMem_tsupport (fun hz' => hz (Ioo_subset_Icc_self (hgU hz')))
    obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
    set Ψ : ℝ × ℝ → ℝ := fun q => test k x y q.1 * g q.2 with hΨ
    have hΨs : ContDiff ℝ ∞ Ψ := ((test_smooth k x y).comp contDiff_fst).mul (hg.comp contDiff_snd)
    have hΨ0 : ∀ q, q ∉ Icc (min x y - width k) (max x y + width k) ×ˢ tsupport g → Ψ q = 0 := by
      intro q hq
      simp only [mem_prod, not_and_or] at hq
      rcases hq with hq | hq
      · simp [hΨ, (hout q.1 hq).1]
      · simp [hΨ, image_eq_zero_of_notMem_tsupport hq]
    have hKc : IsCompact (Icc (min x y - width k) (max x y + width k) ×ˢ tsupport g) :=
      isCompact_Icc.prod hgc
    have hΨc : HasCompactSupport Ψ := HasCompactSupport.intro hKc hΨ0
    have hΨpos : ∀ q ∈ tsupport Ψ, 0 < q.1 := by
      intro q hq
      have hsub : tsupport Ψ ⊆ Icc (min x y - width k) (max x y + width k) ×ˢ tsupport g :=
        closure_minimal (fun q hq' => by_contra fun hn => hq' (hΨ0 q hn))
          (isClosed_Icc.prod (isClosed_tsupport g))
      exact lt_of_lt_of_le hlo (hsub hq).1.1
    have hW' := hW Ψ hΨs hΨc hΨpos
    simp only [hΨ, prod_fderiv k x y hg] at hW'
    have hA : IntegrableOn (fun p : ℝ × ℝ => (((deriv (test k x y) p.1 * g p.2 : ℝ) : ℂ)) * F p) K.rect := by
      obtain ⟨C', hC'⟩ := test_deriv_bound k x y
      refine Integrable.bdd_mul (c := C' * C) hF ?_ (Eventually.of_forall fun p => ?_)
      · exact (Complex.continuous_ofReal.comp ((((test_smooth k x y).continuous_deriv (by simp)).comp
          continuous_fst).mul (hg.continuous.comp continuous_snd))).aestronglyMeasurable
      · rw [Complex.norm_real, norm_mul]
        exact mul_le_mul (by rw [Real.norm_eq_abs]; exact hC' _) (hC _) (norm_nonneg _)
          ((abs_nonneg _).trans (hC' 0))
    have hB0 : IntegrableOn (fun p : ℝ × ℝ => ((g p.2 : ℝ) : ℂ) * Φ p) K.rect := by
      refine Integrable.bdd_mul (c := C) hΦ ?_ (Eventually.of_forall fun p => ?_)
      · exact (Complex.continuous_ofReal.comp (hg.continuous.comp continuous_snd)).aestronglyMeasurable
      · rw [Complex.norm_real]; exact hC _
    have hB : IntegrableOn (fun p : ℝ × ℝ => (((test k x y p.1 * g p.2 : ℝ) : ℂ)) * D p) K.rect := by
      refine (hB0.sub hA).congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
      simp only [hΦdef, Pi.sub_apply]
      push_cast
      ring
    have hzero : ∀ p : ℝ × ℝ, p ∉ K.rect → Φ p * ((g p.2 : ℝ) : ℂ) = 0 ∧
        (((deriv (test k x y) p.1 * g p.2 : ℝ) : ℂ)) * F p = 0 ∧ (((test k x y p.1 * g p.2 : ℝ) : ℂ)) * D p = 0 := by
      intro p hp
      simp only [CellBox.rect, mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · have ho := hout p.1 (fun h' => hp (hsubr h'))
        simp [hΦdef, ho.1, ho.2]
      · simp [hΦdef, hg0 p.2 hp]
    have eA := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := K.rect)
      (fun p hp => (hzero p hp).2.1)
    have eB := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := K.rect)
      (fun p hp => (hzero p hp).2.2)
    have eS : ∫ z, g z • h z = ∫ p in K.rect, Φ p * ((g p.2 : ℝ) : ℂ) := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := Icc K.z₁ K.z₂)
        (fun z hz => by simp [hg0 z hz])]
      have hi : Integrable (fun p : ℝ × ℝ => Φ p * ((g p.2 : ℝ) : ℂ))
          ((volume.restrict (Icc K.r₁ K.r₂)).prod (volume.restrict (Icc K.z₁ K.z₂))) := by
        rw [← hrect]
        exact hB0.congr_fun (fun p _ => mul_comm _ _) (measurableSet_Icc.prod measurableSet_Icc)
      rw [hrect, integral_prod_symm _ hi]
      congr 1
      funext z
      rw [hhdef, ← integral_smul]
      congr 1
      funext r
      rw [Complex.real_smul]
      ring
    have eSplit : ∫ p in K.rect, Φ p * ((g p.2 : ℝ) : ℂ) =
        (∫ p in K.rect, (((deriv (test k x y) p.1 * g p.2 : ℝ) : ℂ)) * F p) +
          ∫ p in K.rect, (((test k x y p.1 * g p.2 : ℝ) : ℂ)) * D p := by
      rw [← integral_add hA hB]
      congr 1
      funext p
      simp only [hΦdef]
      push_cast
      ring
    rw [eS, eSplit, eA, eB, hW']
    ring
  have hloc : LocallyIntegrableOn h (Ioo K.z₁ K.z₂) volume :=
    (hh.mono_set Ioo_subset_Icc_self).locallyIntegrableOn
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc key
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hae, ae_ne_pt K.z₁, ae_ne_pt K.z₂] with z hz h1 h2 hzI
  exact hz ⟨lt_of_le_of_ne hzI.1 (Ne.symm h1), lt_of_le_of_ne hzI.2 h2⟩

theorem ae_fst_ne (c : ℝ) : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ c := by
  rw [Measure.volume_eq_prod]
  exact (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).ae (ae_ne_pt c)

theorem shifted_int (K : CellBox) (_hK : IsCellBox K) {D : ℝ × ℝ → ℂ}
    (hDw : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * D p) K.rect) :
    IntegrableOn (fun p => ((p.1 - K.r₁ : ℝ) : ℂ) * D p) K.rect := by
  by_cases h0 : K.r₁ = 0
  · refine hDw.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
    simp [CellBox.lineWeight, h0]
  · have hD : IntegrableOn D K.rect :=
      hDw.congr_fun (fun p _ => by simp [CellBox.lineWeight, h0]) (measurableSet_Icc.prod measurableSet_Icc)
    refine Integrable.bdd_mul (c := K.r₂ - K.r₁) hD ?_ ?_
    · exact (Complex.continuous_ofReal.comp (continuous_fst.sub continuous_const)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
      obtain ⟨⟨h1, h2⟩, _⟩ := hp
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith

theorem meas_of_shifted (K : CellBox) {D : ℝ × ℝ → ℂ}
    (hDs : IntegrableOn (fun p => ((p.1 - K.r₁ : ℝ) : ℂ) * D p) K.rect) :
    AEStronglyMeasurable D (volume.restrict K.rect) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => (((p.1 - K.r₁)⁻¹ : ℝ) : ℂ) * (((p.1 - K.r₁ : ℝ) : ℂ) * D p))
      (volume.restrict K.rect) :=
    (Complex.continuous_ofReal.measurable.comp ((measurable_fst.sub measurable_const).inv)).aestronglyMeasurable.mul
      hDs.aestronglyMeasurable
  refine hm.congr ?_
  filter_upwards [ae_restrict_of_ae (ae_fst_ne K.r₁)] with p hp
  have : p.1 - K.r₁ ≠ 0 := sub_ne_zero.2 hp
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ this, Complex.ofReal_one, one_mul]

theorem rect_core (K : CellBox) (hK : IsCellBox K) {F D : ℝ × ℝ → ℂ} (hW : IsRadialWeak F D)
    (hF : IntegrableOn F K.rect) (hDw : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * D p) K.rect)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (h1 : χ K.r₁ = 0) (h2 : χ K.r₂ = 0) {t : ℝ → ℝ} (ht : Continuous t) :
    IntegrableOn (fun p => D p * ((χ p.1 * t p.2 : ℝ) : ℂ) + F p * ((deriv χ p.1 * t p.2 : ℝ) : ℂ)) K.rect ∧
    ∫ p in K.rect, (D p * ((χ p.1 * t p.2 : ℝ) : ℂ) + F p * ((deriv χ p.1 * t p.2 : ℝ) : ℂ)) = 0 := by
  have hab : K.r₁ < K.r₂ := hK.r_order.2
  have hKm : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hDs := shifted_int K hK hDw
  have hDm := meas_of_shifted K hDs
  obtain ⟨M, hM0, hM⟩ := lin_bound hχ (b := K.r₂) h1
  obtain ⟨M', hM'0, hM'⟩ := deriv_bound hχ K.r₁ K.r₂
  obtain ⟨T, hT⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc K.z₁ K.z₂) ht.continuousOn
  have hT0 : 0 ≤ T := (norm_nonneg _).trans (hT K.z₁ ⟨le_rfl, hK.z_order.2.le⟩)
  have hA : IntegrableOn (fun p => D p * ((χ p.1 * t p.2 : ℝ) : ℂ)) K.rect := by
    refine Integrable.mono' (hDs.norm.const_mul (M * T)) (hDm.mul (Complex.continuous_ofReal.comp
      ((hχ.continuous.comp continuous_fst).mul (ht.comp continuous_snd))).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem hKm] with p hp
    obtain ⟨hr, hz⟩ := hp
    have e1 := hM p.1 hr
    have e2 := hT p.2 hz
    rw [Real.norm_eq_abs] at e2
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg (sub_nonneg.2 hr.1)]
    calc ‖D p‖ * (|χ p.1| * |t p.2|) ≤ ‖D p‖ * ((M * (p.1 - K.r₁)) * T) :=
          mul_le_mul_of_nonneg_left (mul_le_mul e1 e2 (abs_nonneg _) (by nlinarith [hr.1])) (norm_nonneg _)
      _ = M * T * ((p.1 - K.r₁) * ‖D p‖) := by ring
  have hB : IntegrableOn (fun p => F p * ((deriv χ p.1 * t p.2 : ℝ) : ℂ)) K.rect := by
    have := Integrable.bdd_mul (c := M' * T) hF ((Complex.continuous_ofReal.comp
      (((hχ.continuous_deriv le_rfl).comp continuous_fst).mul (ht.comp continuous_snd))).aestronglyMeasurable)
      (f := fun p : ℝ × ℝ => ((deriv χ p.1 * t p.2 : ℝ) : ℂ)) (by
        filter_upwards [ae_restrict_mem hKm] with p hp
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
        have e2 := hT p.2 hp.2
        rw [Real.norm_eq_abs] at e2
        exact mul_le_mul (hM' p.1 hp.1) e2 (abs_nonneg _) hM'0)
    exact IntegrableOn.congr_fun this (fun p _ => mul_comm _ _) hKm
  refine ⟨hA.add hB, ?_⟩
  have hall : ∀ᵐ z ∂(volume.restrict (Icc K.z₁ K.z₂)), ∀ k : ℕ, ∀ x y : ℚ,
      K.r₁ < (x : ℝ) - width k → (x : ℝ) + width k < K.r₂ →
      K.r₁ < (y : ℝ) - width k → (y : ℝ) + width k < K.r₂ →
      ∫ r in Icc K.r₁ K.r₂, (((deriv (test k x y) r : ℝ) : ℂ) * F (r, z) + ((test k x y r : ℝ) : ℂ) * D (r, z)) = 0 := by
    refine ae_all_iff.2 fun k => ae_all_iff.2 fun x => ae_all_iff.2 fun y => ?_
    by_cases hg : K.r₁ < (x : ℝ) - width k ∧ (x : ℝ) + width k < K.r₂ ∧
        K.r₁ < (y : ℝ) - width k ∧ (y : ℝ) + width k < K.r₂
    · obtain ⟨hx1, hx2, hy1, hy2⟩ := hg
      filter_upwards [slice_vanish K hK hW hF hDw k hx1 hx2 hy1 hy2] with z hz
      intro _ _ _ _
      exact hz
    · exact Eventually.of_forall fun z hx1 hx2 hy1 hy2 => absurd ⟨hx1, hx2, hy1, hy2⟩ hg
  have hzero : ∀ᵐ z ∂(volume.restrict (Icc K.z₁ K.z₂)),
      ∫ r in Icc K.r₁ K.r₂, (D (r, z) * ((χ r : ℝ) : ℂ) + F (r, z) * ((deriv χ r : ℝ) : ℂ)) = 0 := by
    filter_upwards [hall, slice_integrable (a := K.r₁) (b := K.r₂) hF, slice_integrable (a := K.r₁) (b := K.r₂) hDs]
      with z hz hFz hDz
    have hgm : AEStronglyMeasurable (fun r => D (r, z)) (volume.restrict (Icc K.r₁ K.r₂)) := by
      have hm : AEStronglyMeasurable (fun r => (((r - K.r₁)⁻¹ : ℝ) : ℂ) * (((r - K.r₁ : ℝ) : ℂ) * D (r, z)))
          (volume.restrict (Icc K.r₁ K.r₂)) :=
        (Complex.continuous_ofReal.measurable.comp ((measurable_id.sub measurable_const).inv)).aestronglyMeasurable.mul
          hDz.aestronglyMeasurable
      refine hm.congr ?_
      filter_upwards [ae_restrict_of_ae (ae_ne_pt K.r₁)] with r hr
      have : r - K.r₁ ≠ 0 := sub_ne_zero.2 hr
      show (((r - K.r₁)⁻¹ : ℝ) : ℂ) * (((r - K.r₁ : ℝ) : ℂ) * D (r, z)) = D (r, z)
      rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ this, Complex.ofReal_one, one_mul]
    have hgI : ∀ x', K.r₁ < x' → IntegrableOn (fun r => D (r, z)) (Icc x' K.r₂) := by
      intro x' hx'
      have hpos : 0 < x' - K.r₁ := by linarith
      refine Integrable.mono' ((hDz.mono_set (Icc_subset_Icc_left (by linarith))).norm.const_mul (x' - K.r₁)⁻¹)
        (hgm.mono_measure (Measure.restrict_mono (Icc_subset_Icc_left (by linarith)) le_rfl)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      have hr1 : x' - K.r₁ ≤ r - K.r₁ := by linarith [hr.1]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      rw [← mul_assoc, ← div_eq_inv_mul]
      have : 1 ≤ (r - K.r₁) / (x' - K.r₁) := (one_le_div hpos).2 hr1
      nlinarith [norm_nonneg (D (r, z))]
    obtain ⟨L, hL⟩ := line_core K.r₁ K.r₂ hab (fun r => F (r, z)) (fun r => D (r, z)) hFz hgI hz
    exact line_ibp hab hFz hgm hDz hL hχ h1 h2
  have hrect : volume.restrict K.rect =
      (volume.restrict (Icc K.r₁ K.r₂)).prod (volume.restrict (Icc K.z₁ K.z₂)) := rect_measure _ _ _ _
  have hI : Integrable (fun p => D p * ((χ p.1 * t p.2 : ℝ) : ℂ) + F p * ((deriv χ p.1 * t p.2 : ℝ) : ℂ))
      ((volume.restrict (Icc K.r₁ K.r₂)).prod (volume.restrict (Icc K.z₁ K.z₂))) := by
    rw [← hrect]; exact hA.add hB
  rw [hrect, integral_prod_symm _ hI]
  refine (integral_congr_ae ?_).trans (integral_zero _ _)
  filter_upwards [hzero] with z hz
  have e : (fun r => D (r, z) * ((χ r * t z : ℝ) : ℂ) + F (r, z) * ((deriv χ r * t z : ℝ) : ℂ)) =
      fun r => (D (r, z) * ((χ r : ℝ) : ℂ) + F (r, z) * ((deriv χ r : ℝ) : ℂ)) * ((t z : ℝ) : ℂ) := by
    funext r
    push_cast
    ring
  show ∫ r in Icc K.r₁ K.r₂, (D (r, z) * ((χ r * t z : ℝ) : ℂ) + F (r, z) * ((deriv χ r * t z : ℝ) : ℂ)) = 0
  rw [e, integral_mul_const, hz, zero_mul]

section Instance

open Breakdown.CellCert.CellAnalysis.LowEntry.Internal

def unitAt (q : ℝ × ℝ) : Fin 3 → Space :=
  ![EuclideanSpace.single 0 q.1 + EuclideanSpace.single 1 q.2,
    EuclideanSpace.single 0 (-q.2) + EuclideanSpace.single 1 q.1, axialUnit]

theorem unitAt_circle (θ : ℝ) : unitAt (Real.cos θ, Real.sin θ) = frameUnit θ := rfl

def coordForm (a : Fin 3) (q : ℝ × ℝ) : Space →L[ℝ] ℝ :=
  ∑ k : Fin 3, unitAt q a k • EuclideanSpace.proj k

theorem coordForm_circle (a : Fin 3) (θ : ℝ) (u : Space) :
    coordForm a (Real.cos θ, Real.sin θ) u = inner ℝ u (frameUnit θ a) := by
  simp [coordForm, unitAt_circle, PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

theorem unitAt_coord_smooth (a k : Fin 3) : ContDiff ℝ ∞ (fun q : ℝ × ℝ => unitAt q a k) := by
  fin_cases a <;> fin_cases k <;>
    simp [unitAt, axialUnit] <;>
    first | exact contDiff_const | exact contDiff_fst | exact contDiff_snd | exact contDiff_snd.neg

theorem unitAt_smooth (a : Fin 3) : ContDiff ℝ ∞ (fun q : ℝ × ℝ => unitAt q a) :=
  (contDiff_piLp 2).2 fun k => unitAt_coord_smooth a k

theorem coordForm_smooth (a : Fin 3) : ContDiff ℝ ∞ (coordForm a) := by
  unfold coordForm
  exact ContDiff.sum fun k _ => (unitAt_coord_smooth a k).smul contDiff_const

def entryForm (a b : Fin 3) (q : ℝ × ℝ) : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  (coordForm a q).comp (ContinuousLinearMap.apply ℝ Space (unitAt q b))

theorem entryForm_smooth (a b : Fin 3) : ContDiff ℝ ∞ (entryForm a b) :=
  (coordForm_smooth a).clm_comp ((ContinuousLinearMap.apply ℝ Space).contDiff.comp (unitAt_smooth b))

theorem entryForm_circle (a b : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space) :
    entryForm a b (Real.cos θ, Real.sin θ) M = inner ℝ (M (frameUnit θ b)) (frameUnit θ a) := by
  simp only [entryForm, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  rw [coordForm_circle, unitAt_circle]

theorem vec_sum (u : Space) : u = ∑ j : Fin 3, u j • unitVector j := by
  ext i; fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

theorem opNorm_cols {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : Space →L[ℝ] E) :
    ‖A‖ ≤ ∑ i : Fin 3, ‖A (unitVector i)‖ := by
  refine A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun u => ?_
  conv_lhs => rw [vec_sum u]
  rw [map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_smul, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u i) (norm_nonneg _)

theorem locInt_cols {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Space → (Space →L[ℝ] E)} (hm : AEStronglyMeasurable A volume)
    (hc : ∀ i, LocallyIntegrable (fun y => A y (unitVector i)) volume) : LocallyIntegrable A volume := by
  have hn : ∀ i, LocallyIntegrable (fun y => ‖A y (unitVector i)‖) volume := fun i =>
    (hc i).mono (hc i).aestronglyMeasurable.norm (Eventually.of_forall fun y => by simp)
  have hs : LocallyIntegrable (fun y => ∑ i : Fin 3, ‖A y (unitVector i)‖) volume := by
    simp only [Fin.sum_univ_three]
    exact ((hn 0).add (hn 1)).add (hn 2)
  refine hs.mono hm (Eventually.of_forall fun y => ?_)
  refine (opNorm_cols (A y)).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]

theorem field_weak {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (a b : Fin 3) (n : ℤ) :
    IsRadialWeak (gradMode m n G a b) (radialGradMode m n H a b) := by
  have hGc : ∀ j, LocallyIntegrable (fun y => G y (unitVector j)) volume := fun j =>
    (Breakdown.FracInternal.ModeHeightAxis.col_memLp hs.measurable_gradient hs.gradient_two j).locallyIntegrable
      (by norm_num)
  have hG : LocallyIntegrable G volume := locInt_cols hs.measurable_gradient hGc
  have hHc : ∀ j, LocallyIntegrable (fun y => H y (unitVector j)) volume := fun j =>
    locInt_cols ((continuous_id.clm_apply continuous_const).comp_aestronglyMeasurable hs.measurable_second)
      fun i => (Breakdown.FracInternal.ModeHeightAxis.second_memLp hs.measurable_second hs.second_two j i).locallyIntegrable
        (by norm_num)
  have hweakG : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) • G y = -∫ y, φ y • H y (unitVector j) := by
    intro φ hφ j
    have hd : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have i1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • G y) volume :=
      hG.integrable_smul_left_of_hasCompactSupport hd (hφ.2.fderiv_apply (𝕜 := ℝ) _)
    have i2 : Integrable (fun y => φ y • H y (unitVector j)) volume :=
      (hHc j).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    have key : ∀ i, (∫ y, fderiv ℝ φ y (unitVector j) • G y) (unitVector i) =
        (-∫ y, φ y • H y (unitVector j)) (unitVector i) := by
      intro i
      rw [neg_apply, ContinuousLinearMap.integral_apply i1, ContinuousLinearMap.integral_apply i2]
      simpa using hs.weak_second φ hφ i j
    refine ContinuousLinearMap.ext fun u => ?_
    rw [vec_sum u]
    simp only [map_sum, map_smul, key]
  intro Ψ hΨ hc hpos
  have h := (cylModeWeak (Space →L[ℝ] Space) G H hG hHc hweakG (entryForm a b) (entryForm_smooth a b) m n Ψ
    hΨ hc hpos).1
  have e1 : ∀ p : ℝ × ℝ, gradMode m n G a b p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (entryForm a b (Real.cos θ, Real.sin θ) (G (cylPoint p.1 θ p.2)) : ℂ) := by
    intro p
    simp only [gradMode, modeMat, entryForm_circle]
    rfl
  have e2 : ∀ p : ℝ × ℝ, radialGradMode m n H a b p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (entryForm a b (Real.cos θ, Real.sin θ) (H (cylPoint p.1 θ p.2) (radialUnit θ)) : ℂ) := by
    intro p
    simp only [radialGradMode, modeThird, entryForm_circle]
    rfl
  simp only [e1, e2]
  have f1 : (fun p : ℝ × ℝ => ((fderiv ℝ Ψ p (1, 0) : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (entryForm a b (Real.cos θ, Real.sin θ) (G (cylPoint p.1 θ p.2)) : ℂ))) =
      fun p => (1 / (2 * Real.pi) : ℂ) * (((fderiv ℝ Ψ p (1, 0) : ℝ) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (entryForm a b (Real.cos θ, Real.sin θ) (G (cylPoint p.1 θ p.2)) : ℂ)) := funext fun p => by ring
  have f2 : (fun p : ℝ × ℝ => ((Ψ p : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (entryForm a b (Real.cos θ, Real.sin θ) (H (cylPoint p.1 θ p.2) (radialUnit θ)) : ℂ))) =
      fun p => (1 / (2 * Real.pi) : ℂ) * (((Ψ p : ℝ) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (entryForm a b (Real.cos θ, Real.sin θ) (H (cylPoint p.1 θ p.2) (radialUnit θ)) : ℂ)) :=
    funext fun p => by ring
  rw [f1, f2, integral_const_mul, integral_const_mul, h, mul_neg]

end Instance

section Final

open Breakdown.CellCert.CellAnalysis.LowEntry.Internal
open Breakdown.FracInternal.ModeRectIntegrable Breakdown.FracInternal.ModeHeightAxis
open Real

theorem second_loc {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) :
    LocallyIntegrable H volume :=
  locInt_cols hs.measurable_second fun j =>
    locInt_cols ((continuous_id.clm_apply continuous_const).comp_aestronglyMeasurable hs.measurable_second)
      fun i => (second_memLp hs.measurable_second hs.second_two j i).locallyIntegrable (by norm_num)

def thirdKernel (m : ℕ) (n : ℤ) (a b : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space →L[ℝ] Space) : ℂ :=
  Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * (frameThird θ M a b 0 : ℂ)

theorem thirdKernel_cont (m : ℕ) (n : ℤ) (a b : Fin 3) :
    Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) => thirdKernel m n a b q.1 q.2) := by
  refine (phase_cont m n).mul (Complex.continuous_ofReal.comp ?_)
  unfold frameThird frameUnit
  exact ((continuous_snd.clm_apply ((unit_cont 0).comp continuous_fst)).clm_apply
    ((unit_cont b).comp continuous_fst)).inner ((unit_cont a).comp continuous_fst)

theorem thirdKernel_bound (m : ℕ) (n : ℤ) (a b : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖thirdKernel m n a b θ M‖ ≤ ‖M‖ := by
  rw [thirdKernel, norm_mul, phase_norm, one_mul, Complex.norm_real, Real.norm_eq_abs]
  unfold frameThird frameUnit
  have h0 := unit_norm θ 0
  have hb := unit_norm θ b
  have ha := unit_norm θ a
  refine (abs_real_inner_le_norm _ _).trans ?_
  calc ‖M (![radialUnit θ, angularUnit θ, axialUnit] 0) (![radialUnit θ, angularUnit θ, axialUnit] b)‖ *
        ‖![radialUnit θ, angularUnit θ, axialUnit] a‖
      ≤ (‖M‖ * ‖![radialUnit θ, angularUnit θ, axialUnit] 0‖ * ‖![radialUnit θ, angularUnit θ, axialUnit] b‖) * 1 :=
        mul_le_mul (M.le_opNorm₂ _ _) ha (norm_nonneg _) (by positivity)
    _ ≤ ‖M‖ * 1 * 1 * 1 := by
        gcongr
    _ = ‖M‖ := by ring

theorem frameThird_per (θ : ℝ) (M : Space →L[ℝ] Space →L[ℝ] Space) (a b c : Fin 3) :
    frameThird (θ + 2 * π) M a b c = frameThird θ M a b c := by
  simp only [frameThird, frameUnit, radialUnit, angularUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem radialGradMode_eq (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b : Fin 3)
    (p : ℝ × ℝ) :
    radialGradMode m n H a b p =
      (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, thirdKernel m n a b θ (H (cylPoint p.1 θ p.2)) := by
  unfold radialGradMode modeThird
  rw [per_interval]
  · rfl
  · intro θ
    simp only [phase_per, cylPoint_per, frameThird_per]

theorem third_lw_int {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (K : CellBox)
    (hK : IsCellBox K) (a b : Fin 3) (n : ℤ) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * radialGradMode m n H a b p) K.rect := by
  have h := (mode_int K hK (second_loc hs) (thirdKernel m n a b) (thirdKernel_cont m n a b)
    (thirdKernel_bound m n a b)).const_mul (1 / (2 * π) : ℂ)
  refine IntegrableOn.congr_fun h (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
  rw [radialGradMode_eq]
  ring

theorem grad_int {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (K : CellBox)
    (hK : IsCellBox K) (a b : Fin 3) (n : ℤ) :
    IntegrableOn (gradMode m n G a b) K.rect := by
  have hsub := rect_sub K hK
  have hKm : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  set ρ : ℝ := 2 * |K.r₂| + |K.z₂| + 1 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hχ : IsTestScalar (radialCutoff ρ) := ⟨contDiff_radialCutoff hρ0, hasCompactSupport_radialCutoff hρ0⟩
  have hχ1 : ∀ y, |radialCutoff ρ y| ≤ 1 := fun y => by
    rw [abs_of_nonneg (radialCutoff_nonneg ρ y)]
    exact radialCutoff_le_one ρ y
  have h6 := op_six hs hχ hχ1
  have hint0 : IntegrableOn _ (Icc 0 K.r₂ ×ˢ Icc (-K.z₂) K.z₂) :=
    (six_int K.r₂ K.z₂ h6 (gradKernel m n a b) (gradKernel_cont m n a b)
      (gradKernel_bound m n a b)).const_mul (1 / (2 * π) : ℂ)
  have hint := hint0.mono_set hsub
  refine IntegrableOn.congr_fun hint (fun p hp => ?_) hKm
  rw [gradMode_eq]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
  have hp' := hsub hp
  have hn : ‖cylPoint p.1 θ p.2‖ ≤ ρ := by
    refine (cylPoint_norm _ _ _).trans ?_
    have h1 : |p.1| ≤ |K.r₂| := by rw [abs_of_nonneg hp'.1.1]; exact hp'.1.2.trans (le_abs_self _)
    have h2 : |p.2| ≤ |K.z₂| :=
      abs_le.2 ⟨by linarith [hp'.2.1, le_abs_self K.z₂, neg_abs_le K.z₂], hp'.2.2.trans (le_abs_self _)⟩
    rw [hρ]
    linarith
  simp only [radialCutoff_eq_one hρ0 hn, one_smul]

end Final

end Breakdown.CellCert.CellEnergy.RadialTraceInternal

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis CellFormula SteadyCert Assembly
open RadialTraceInternal

theorem radialTrace : RadialTraceStatement := by
  intro K hK m v G H hs n a b
  have hF := grad_int hs K hK a b n
  have hDw := third_lw_int hs K hK a b n
  have hab : K.r₁ < K.r₂ := hK.r_order.2
  have hKm : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  refine ⟨hF, ?_, ?_, ?_⟩
  · have hK' : IsCellBox ⟨0, K.r₂, K.z₁, K.z₂⟩ := ⟨⟨le_rfl, lt_of_le_of_lt hK.r_order.1 hab⟩, hK.z_order⟩
    have h := (third_lw_int hs ⟨0, K.r₂, K.z₁, K.z₂⟩ hK' a b n).mono_set
      (Set.prod_mono (Set.Icc_subset_Icc_left hK.r_order.1) subset_rfl)
    refine IntegrableOn.congr_fun h (fun p _ => ?_) hKm
    simp [CellBox.lineWeight]
  · intro h0
    refine IntegrableOn.congr_fun hDw (fun p _ => ?_) hKm
    simp [CellBox.lineWeight, h0]
  · intro ψ t hψ ht hcase
    set F := gradMode m n G a b with hFdef
    set D := radialGradMode m n H a b with hDdef
    have hc : 0 < K.r₂ - K.r₁ := sub_pos.2 hab
    set α := ψ K.r₂ with hα
    set β := ψ K.r₁ with hβ
    set χ : ℝ → ℝ := fun r => ψ r - α / (K.r₂ - K.r₁) * (r - K.r₁) - β / (K.r₂ - K.r₁) * (K.r₂ - r) with hχdef
    have hχ : ContDiff ℝ 1 χ :=
      (hψ.sub (contDiff_const.mul (contDiff_id.sub contDiff_const))).sub
        (contDiff_const.mul (contDiff_const.sub contDiff_id))
    have hχd : ∀ r, deriv χ r = deriv ψ r - α / (K.r₂ - K.r₁) + β / (K.r₂ - K.r₁) := by
      intro r
      have hd : HasDerivAt χ (deriv ψ r - α / (K.r₂ - K.r₁) * 1 - β / (K.r₂ - K.r₁) * (-1)) r :=
        (((hψ.differentiable one_ne_zero) r).hasDerivAt.sub (((hasDerivAt_id' r).sub_const K.r₁).const_mul _)).sub
          (((hasDerivAt_id' r).const_sub K.r₂).const_mul _)
      rw [hd.deriv]
      ring
    have hχ1 : χ K.r₁ = 0 := by
      simp only [hχdef]
      rw [sub_self, mul_zero, sub_zero, div_mul_cancel₀ _ hc.ne', hβ, sub_self]
    have hχ2 : χ K.r₂ = 0 := by
      simp only [hχdef]
      rw [sub_self, mul_zero, sub_zero, div_mul_cancel₀ _ hc.ne', hα, sub_self]
    obtain ⟨hI, hbase⟩ := rect_core K hK (field_weak hs a b n) hF hDw hχ hχ1 hχ2 ht
    obtain ⟨T, hT⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc K.z₁ K.z₂) ht.continuousOn
    have hT0 : 0 ≤ T := (norm_nonneg _).trans (hT K.z₁ ⟨le_rfl, hK.z_order.2.le⟩)
    have hDs := shifted_int K hK hDw
    set X₁ : ℝ × ℝ → ℂ := fun p => ((((1 / (K.r₂ - K.r₁) : ℝ)) : ℂ) * F p +
      (((p.1 - K.r₁) / (K.r₂ - K.r₁) : ℝ) : ℂ) * D p) * ((t p.2 : ℝ) : ℂ) with hX₁
    set Y₀ : ℝ × ℝ → ℂ := fun p => ((((1 / (K.r₁ - K.r₂) : ℝ)) : ℂ) * F p +
      (((p.1 - K.r₂) / (K.r₁ - K.r₂) : ℝ) : ℂ) * D p) * ((t p.2 : ℝ) : ℂ) with hY₀
    have htc : Continuous (fun p : ℝ × ℝ => ((t p.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (ht.comp continuous_snd)
    have hbd : ∀ (f : ℝ × ℝ → ℂ) (C : ℂ), IntegrableOn f K.rect →
        IntegrableOn (fun p => C * ((t p.2 : ℝ) : ℂ) * f p) K.rect := by
      intro f C hf
      refine Integrable.bdd_mul (c := ‖C‖ * T) hf ((continuous_const.mul htc).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem hKm] with p hp
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (hT p.2 hp.2) (norm_nonneg _)
    have hX₁i : IntegrableOn X₁ K.rect := by
      refine IntegrableOn.congr_fun ((hbd F (((1 / (K.r₂ - K.r₁) : ℝ)) : ℂ) hF).add
        (hbd _ (((1 / (K.r₂ - K.r₁) : ℝ)) : ℂ) hDs)) (fun p _ => ?_) hKm
      simp only [hX₁, Pi.add_apply]
      push_cast
      ring
    have hY₀i : IntegrableOn (fun p => (β : ℂ) * Y₀ p) K.rect := by
      by_cases hb0 : β = 0
      · simp only [hb0, Complex.ofReal_zero, zero_mul]
        exact integrableOn_zero
      · have hr : K.r₁ ≠ 0 := by
          rcases hcase with h | h
          · exact h
          · intro h0
            exact hb0 (by rw [hβ, h0, h])
        have hD : IntegrableOn D K.rect :=
          IntegrableOn.congr_fun hDw (fun p _ => by simp [CellBox.lineWeight, hr]) hKm
        have hD2 : IntegrableOn (fun p => ((p.1 - K.r₂ : ℝ) : ℂ) * D p) K.rect := by
          refine Integrable.bdd_mul (c := K.r₂ - K.r₁) hD ?_ ?_
          · exact (Complex.continuous_ofReal.comp (continuous_fst.sub continuous_const)).aestronglyMeasurable
          · filter_upwards [ae_restrict_mem hKm] with p hp
            obtain ⟨⟨h1, h2⟩, _⟩ := hp
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
            linarith
        refine IntegrableOn.congr_fun (((hbd F (((1 / (K.r₁ - K.r₂) : ℝ)) : ℂ) hF).add
          (hbd _ (((1 / (K.r₁ - K.r₂) : ℝ)) : ℂ) hD2)).const_mul (β : ℂ)) (fun p _ => ?_) hKm
        simp only [hY₀, Pi.add_apply]
        push_cast
        ring
    have hne1 : ((K.r₂ : ℂ) - K.r₁) ≠ 0 := by
      rw [← Complex.ofReal_sub]; exact Complex.ofReal_ne_zero.2 hc.ne'
    have hne2 : ((K.r₁ : ℂ) - K.r₂) ≠ 0 := by
      rw [← Complex.ofReal_sub]; exact Complex.ofReal_ne_zero.2 (by linarith)
    have hpt : ∀ p : ℝ × ℝ, D p * ((ψ p.1 * t p.2 : ℝ) : ℂ) + F p * ((deriv ψ p.1 * t p.2 : ℝ) : ℂ) =
        (D p * ((χ p.1 * t p.2 : ℝ) : ℂ) + F p * ((deriv χ p.1 * t p.2 : ℝ) : ℂ)) + (α : ℂ) * X₁ p +
          (β : ℂ) * Y₀ p := by
      intro p
      rw [hχd]
      simp only [hχdef, hX₁, hY₀]
      push_cast
      field_simp
      ring
    have hR1 : radialFaceMoment K F D 1 t = ∫ p in K.rect, X₁ p := by
      unfold radialFaceMoment radialStripMoment edgeSign
      rw [if_pos rfl, if_pos hab, min_eq_right hab.le, max_eq_left hab.le, one_mul]
      rfl
    have hR0 : radialFaceMoment K F D 0 t = -∫ p in K.rect, Y₀ p := by
      unfold radialFaceMoment radialStripMoment edgeSign
      rw [if_neg (by decide), if_neg (not_lt.2 hab.le), min_eq_left hab.le, max_eq_right hab.le, neg_one_mul]
      rfl
    have hI' : IntegrableOn (fun p => D p * ((χ p.1 * t p.2 : ℝ) : ℂ) + F p * ((deriv χ p.1 * t p.2 : ℝ) : ℂ))
        K.rect := hI
    have hcore' : ∫ p in K.rect, (D p * ((χ p.1 * t p.2 : ℝ) : ℂ) + F p * ((deriv χ p.1 * t p.2 : ℝ) : ℂ)) = 0 :=
      hbase
    have hX' : IntegrableOn (fun p => (α : ℂ) * X₁ p) K.rect := hX₁i.const_mul _
    have hI2 : IntegrableOn (fun p => D p * ((χ p.1 * t p.2 : ℝ) : ℂ) + F p * ((deriv χ p.1 * t p.2 : ℝ) : ℂ) +
        (α : ℂ) * X₁ p) K.rect := hI'.add hX'
    rw [hR1, hR0, setIntegral_congr_fun hKm (fun p _ => hpt p), integral_add hI2 hY₀i, integral_add hI' hX',
      hcore', integral_const_mul, integral_const_mul]
    ring

end Breakdown.CellCert.CellEnergy
