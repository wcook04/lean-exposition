import Breakdown.FracCell.ModeRadialWeak
import Breakdown.FracCell.ModeWeakIdentity
import Breakdown.FracCell.ModeHeightAxis

open scoped ContDiff Convolution
open MeasureTheory Filter Topology Set

noncomputable section

namespace Breakdown.CellCert.CellAnalysis.ModeRadialWeakInternal

open SteadyCert Real
open Breakdown.FracInternal.ModeHeightAxis Breakdown.CellCert.CellAnalysis.LowEntry.Internal

theorem vel_on {m : ℕ} {v : Space → Space} (hv : MemLp v 6 volume) (n : ℤ) (a : Fin 3) (R Z : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) (Icc 0 R ×ˢ Icc (-Z) Z) := by
  have h := (vel_int R Z hv (velKernel m n a) (velKernel_cont m n a) (velKernel_bound m n a)).const_mul
    (1 / (2 * π) : ℂ)
  exact IntegrableOn.congr_fun h (fun p _ => (modeVec_eq m n v a p).symm) (measurableSet_Icc.prod measurableSet_Icc)

theorem grad_memLp {G : Space → (Space →L[ℝ] Space)} (hG1 : AEStronglyMeasurable G volume)
    (hG2 : Integrable (fun y => entrySq (G y))) : MemLp G 2 volume :=
  (memLp_two_iff_integrable_sq_norm hG1).2 ((hG2.const_mul 3).mono'
      ((hG1.norm.aemeasurable.pow_const 2).aestronglyMeasurable) (Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact EmbedWeak.Internal.norm_sq_le (G y)))

theorem grad_on {m : ℕ} {G : Space → (Space →L[ℝ] Space)} (hG : LocallyIntegrable G volume) (n : ℤ) (a : Fin 3)
    (R Z : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * gradMode m n G a 0 p) (Icc 0 R ×ˢ Icc (-Z) Z) := by
  have h := (weighted_int R Z hG (gradKernel m n a 0) (gradKernel_cont m n a 0)
    (gradKernel_bound m n a 0)).const_mul (1 / (2 * π) : ℂ)
  refine IntegrableOn.congr_fun h (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
  simp only [gradMode_eq]
  ring

theorem grad_meas {m : ℕ} {G : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume) (n : ℤ)
    (a : Fin 3) (R Z : ℝ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => gradMode m n G a 0 p) (volume.restrict (Icc 0 R ×ˢ Icc (-Z) Z)) := by
  have h := ((kmeas hG (gradKernel m n a 0) (gradKernel_cont m n a 0)).mono_measure (half_le R Z)).const_mul
    (1 / (2 * π) : ℂ)
  refine h.congr (Eventually.of_forall fun p => ?_)
  simp only [gradMode_eq]

theorem bound_sub {k : Set ℝ} (hk : IsCompact k) : ∃ Z, k ⊆ Icc (-Z) Z := by
  obtain ⟨C, hC⟩ := hk.exists_bound_of_continuousOn continuousOn_id
  exact ⟨C, fun x hx => abs_le.1 (by simpa using hC x hx)⟩

theorem zero_off {α : ℝ → ℝ} {x : ℝ} (h : x ∉ tsupport α) : α x = 0 := image_eq_zero_of_notMem_tsupport h

theorem deriv_zero_off {α : ℝ → ℝ} {x : ℝ} (h : x ∉ tsupport α) : deriv α x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h' => h (tsupport_deriv_subset h'))

theorem ratio_cont {α : ℝ → ℝ} (hα : Continuous α) (hs : ∀ x ∈ tsupport α, 0 < x) :
    Continuous (fun r => α r / r) := by
  rw [continuous_iff_continuousAt]
  intro r
  by_cases hr : r = 0
  · subst hr
    have h0 : (0 : ℝ) ∉ tsupport α := fun h => lt_irrefl (0 : ℝ) (hs 0 h)
    have e : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 0] fun r => α r / r := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 h0] with x hx
      simp only [Pi.zero_apply] at hx
      simp [hx]
    exact continuousAt_const.congr e
  · exact hα.continuousAt.div continuousAt_id hr

theorem ratio_mul {α : ℝ → ℝ} (hs : ∀ x ∈ tsupport α, 0 < x) (r : ℝ) : α r = α r / r * r := by
  by_cases hr : r = 0
  · subst hr
    have h0 : (0 : ℝ) ∉ tsupport α := fun h => lt_irrefl (0 : ℝ) (hs 0 h)
    simp [zero_off h0]
  · field_simp

section Generic

variable {F g : ℝ × ℝ → ℂ}

theorem part_int (hF : ∀ R Z, IntegrableOn F (Icc 0 R ×ˢ Icc (-Z) Z))
    (hg : ∀ R Z, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * g p) (Icc 0 R ×ˢ Icc (-Z) Z))
    {α : ℝ → ℝ} (hα : ContDiff ℝ 1 α) {R : ℝ} (hs : tsupport α ⊆ Ioo 0 R) (Z : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => ((deriv α p.1 : ℝ) : ℂ) * F p) (univ ×ˢ Icc (-Z) Z) ∧
      IntegrableOn (fun p : ℝ × ℝ => (α p.1 : ℂ) * g p) (univ ×ˢ Icc (-Z) Z) := by
  have hpos : ∀ x ∈ tsupport α, 0 < x := fun x hx => (hs hx).1
  have hK : IsCompact (Icc (0 : ℝ) R ×ˢ Icc (-Z) Z) := isCompact_Icc.prod isCompact_Icc
  have hmeas : MeasurableSet (univ ×ˢ Icc (-Z) Z : Set (ℝ × ℝ)) := MeasurableSet.univ.prod measurableSet_Icc
  have hout : ∀ p ∈ (univ ×ˢ Icc (-Z) Z : Set (ℝ × ℝ)) \ (Icc 0 R ×ˢ Icc (-Z) Z), p.1 ∉ tsupport α := by
    intro p hp h
    exact hp.2 ⟨⟨(hs h).1.le, (hs h).2.le⟩, hp.1.2⟩
  constructor
  · have h1 := (hF R Z).continuousOn_mul
      (g := fun p : ℝ × ℝ => ((deriv α p.1 : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp ((hα.continuous_deriv le_rfl).comp continuous_fst)).continuousOn hK
    refine h1.of_forall_sdiff_eq_zero hmeas (fun p hp => ?_)
    simp [deriv_zero_off (hout p hp)]
  · have h1 := (hg R Z).continuousOn_mul
      (g := fun p : ℝ × ℝ => ((α p.1 / p.1 : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp ((ratio_cont hα.continuous hpos).comp continuous_fst)).continuousOn hK
    have h2 : IntegrableOn (fun p : ℝ × ℝ => (α p.1 : ℂ) * g p) (Icc 0 R ×ˢ Icc (-Z) Z) := by
      refine IntegrableOn.congr_fun h1 (fun p _ => ?_) hK.measurableSet
      conv_rhs => rw [ratio_mul hpos p.1]
      push_cast
      ring
    refine h2.of_forall_sdiff_eq_zero hmeas (fun p hp => ?_)
    simp [zero_off (hout p hp)]

theorem weight_int {X : ℝ × ℝ → ℂ} (hX : ∀ Z, IntegrableOn X (univ ×ˢ Icc (-Z) Z)) {β : ℝ → ℝ}
    (hβ : Continuous β) (hc : HasCompactSupport β) :
    Integrable (fun p : ℝ × ℝ => (β p.2 : ℂ) * X p) := by
  obtain ⟨Z, hZ⟩ := bound_sub hc.isCompact
  obtain ⟨C, hC⟩ := hβ.bounded_above_of_compact_support hc
  have h1 : IntegrableOn (fun p : ℝ × ℝ => (β p.2 : ℂ) * X p) (univ ×ˢ Icc (-Z) Z) :=
    (hX Z).bdd_mul (c := C) (Complex.continuous_ofReal.comp (hβ.comp continuous_snd)).aestronglyMeasurable
      (Eventually.of_forall fun p => by simpa using hC p.2)
  refine h1.integrable_of_forall_notMem_eq_zero (fun p hp => ?_)
  have : p.2 ∉ tsupport β := fun h => hp ⟨trivial, hZ h⟩
  simp [zero_off this]

theorem fderiv_dir {α β : ℝ → ℝ} (hα : Differentiable ℝ α) (hβ : Differentiable ℝ β) (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => α q.1 * β q.2) p (1, 0) = deriv α p.1 * β p.2 := by
  have hΦ : DifferentiableAt ℝ (fun q : ℝ × ℝ => α q.1 * β q.2) (p.1, p.2) :=
    ((hα _).comp _ differentiableAt_fst).mul ((hβ _).comp _ differentiableAt_snd)
  have h1 : HasDerivAt (fun r : ℝ => (r, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have h2 := hΦ.hasFDerivAt.comp_hasDerivAt p.1 h1
  have h3 : HasDerivAt (fun r => α r * β p.2) (deriv α p.1 * β p.2) p.1 :=
    (hα p.1).hasDerivAt.mul_const _
  exact h2.unique h3

theorem slice_ae (hF : ∀ R Z, IntegrableOn F (Icc 0 R ×ˢ Icc (-Z) Z))
    (hg : ∀ R Z, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * g p) (Icc 0 R ×ˢ Icc (-Z) Z))
    (hW : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * F p = -∫ p, (ψ p : ℂ) * g p)
    {α : ℝ → ℝ} (hα : ContDiff ℝ ∞ α) (hc : HasCompactSupport α) {R : ℝ} (hs : tsupport α ⊆ Ioo 0 R) :
    ∀ᵐ z ∂(volume : Measure ℝ), ∫ r, (((deriv α r : ℝ) : ℂ) * F (r, z) + (α r : ℂ) * g (r, z)) = 0 := by
  have hα1 : ContDiff ℝ 1 α := hα.of_le (by exact_mod_cast le_top)
  have hP := part_int hF hg hα1 hs
  have hPZ : ∀ Z, IntegrableOn (fun p : ℝ × ℝ => ((deriv α p.1 : ℝ) : ℂ) * F p + (α p.1 : ℂ) * g p)
      (univ ×ˢ Icc (-Z) Z) := fun Z => (hP Z).1.add (hP Z).2
  have hprod : ∀ Z, Integrable (fun p : ℝ × ℝ => ((deriv α p.1 : ℝ) : ℂ) * F p + (α p.1 : ℂ) * g p)
      ((volume : Measure ℝ).prod (volume.restrict (Icc (-Z) Z))) := by
    intro Z
    have := hPZ Z
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at this
    exact this
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero ?_ ?_
  · rw [locallyIntegrable_iff]
    intro k hk
    obtain ⟨Z, hZ⟩ := bound_sub hk
    exact IntegrableOn.mono_set ((hprod Z).integral_prod_right) hZ
  · intro β hβ hβc
    have hβ1 : Differentiable ℝ β := hβ.differentiable (by simp)
    have hα1' : Differentiable ℝ α := hα.differentiable (by simp)
    have hΦ := hW (fun q : ℝ × ℝ => α q.1 * β q.2) ((hα.comp contDiff_fst).mul (hβ.comp contDiff_snd))
      (by
        refine HasCompactSupport.intro (hc.isCompact.prod hβc.isCompact) (fun p hp => ?_)
        by_cases h1 : p.1 ∈ tsupport α
        · have h2 : p.2 ∉ tsupport β := fun h2 => hp ⟨h1, h2⟩
          simp [zero_off h2]
        · simp [zero_off h1])
      (by
        intro p hp
        have : p.1 ∈ tsupport α := by
          by_contra h1
          have hz : (fun q : ℝ × ℝ => α q.1 * β q.2) =ᶠ[𝓝 p] 0 := by
            have hev : ∀ᶠ q in 𝓝 p, α q.1 = 0 :=
              (continuous_fst.tendsto p).eventually (notMem_tsupport_iff_eventuallyEq.1 h1)
            filter_upwards [hev] with q hq
            simp [hq]
          exact notMem_tsupport_iff_eventuallyEq.2 hz hp
        exact (hs this).1)
    simp only [fderiv_dir hα1' hβ1] at hΦ
    have i1 := weight_int (fun Z => (hP Z).1) hβ.continuous hβc
    have i2 := weight_int (fun Z => (hP Z).2) hβ.continuous hβc
    have hsum : ∫ p : ℝ × ℝ, (β p.2 : ℂ) * (((deriv α p.1 : ℝ) : ℂ) * F p + (α p.1 : ℂ) * g p) = 0 := by
      have e : (fun p : ℝ × ℝ => (β p.2 : ℂ) * (((deriv α p.1 : ℝ) : ℂ) * F p + (α p.1 : ℂ) * g p)) =
          fun p => (β p.2 : ℂ) * (((deriv α p.1 : ℝ) : ℂ) * F p) + (β p.2 : ℂ) * ((α p.1 : ℂ) * g p) := by
        funext p; ring
      rw [e, integral_add i1 i2]
      have e1 : (fun p : ℝ × ℝ => (β p.2 : ℂ) * (((deriv α p.1 : ℝ) : ℂ) * F p)) =
          fun p => ((deriv α p.1 * β p.2 : ℝ) : ℂ) * F p := by
        funext p; push_cast; ring
      have e2 : (fun p : ℝ × ℝ => (β p.2 : ℂ) * ((α p.1 : ℂ) * g p)) =
          fun p => ((α p.1 * β p.2 : ℝ) : ℂ) * g p := by
        funext p; push_cast; ring
      rw [e1, e2, hΦ]
      ring
    have hint : Integrable (fun p : ℝ × ℝ => (β p.2 : ℂ) * (((deriv α p.1 : ℝ) : ℂ) * F p + (α p.1 : ℂ) * g p)) := by
      have := i1.add i2
      refine this.congr (Eventually.of_forall fun p => ?_)
      simp only [Pi.add_apply]
      ring
    rw [Measure.volume_eq_prod] at hint hsum
    rw [integral_prod_symm _ hint] at hsum
    rw [← hsum]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    rw [← integral_smul]
    rfl


theorem rect_smooth (hF : ∀ R Z, IntegrableOn F (Icc 0 R ×ˢ Icc (-Z) Z))
    (hg : ∀ R Z, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * g p) (Icc 0 R ×ˢ Icc (-Z) Z))
    (hW : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * F p = -∫ p, (ψ p : ℂ) * g p)
    {α : ℝ → ℝ} (hα : ContDiff ℝ ∞ α) (hc : HasCompactSupport α) {r₁ r₂ : ℝ} (h0 : 0 ≤ r₁)
    (hs : tsupport α ⊆ Ioo r₁ r₂) (z₁ z₂ : ℝ) {t : ℝ → ℝ} (ht : Continuous t) :
    ∫ p in Icc r₁ r₂ ×ˢ Icc z₁ z₂, (((deriv α p.1 : ℝ) : ℂ) * F p + ((α p.1 : ℝ) : ℂ) * g p) * ((t p.2 : ℝ) : ℂ)
      = 0 := by
  have hs' : tsupport α ⊆ Ioo 0 r₂ := fun x hx => ⟨h0.trans_lt (hs hx).1, (hs hx).2⟩
  have hz := slice_ae hF hg hW hα hc hs'
  have hα1 : ContDiff ℝ 1 α := hα.of_le (by exact_mod_cast le_top)
  have hP := part_int hF hg hα1 hs'
  set Z := |z₁| + |z₂| with hZdef
  have hZ : Icc z₁ z₂ ⊆ Icc (-Z) Z := fun x hx =>
    ⟨by linarith [hx.1, neg_abs_le z₁, abs_nonneg z₂], by linarith [hx.2, le_abs_self z₂, abs_nonneg z₁]⟩
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (ht.continuousOn (s := Icc z₁ z₂))
  have hmS : MeasurableSet (univ ×ˢ Icc z₁ z₂ : Set (ℝ × ℝ)) := MeasurableSet.univ.prod measurableSet_Icc
  have hI : IntegrableOn (fun p : ℝ × ℝ =>
      (((deriv α p.1 : ℝ) : ℂ) * F p + ((α p.1 : ℝ) : ℂ) * g p) * ((t p.2 : ℝ) : ℂ)) (univ ×ˢ Icc z₁ z₂) := by
    have h1 : IntegrableOn (fun p : ℝ × ℝ => (((deriv α p.1 : ℝ) : ℂ) * F p + ((α p.1 : ℝ) : ℂ) * g p))
        (univ ×ˢ Icc z₁ z₂) :=
      IntegrableOn.mono_set ((hP Z).1.add (hP Z).2) (prod_mono subset_rfl hZ)
    exact Integrable.mul_bdd (c := B) h1
      (Complex.continuous_ofReal.comp (ht.comp continuous_snd)).aestronglyMeasurable
      ((ae_restrict_iff' hmS).2 (Eventually.of_forall fun p hp => by simpa using hB p.2 hp.2))
  rw [← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmS (prod_mono (subset_univ _) subset_rfl)]
  · rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at hI
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ, integral_prod_symm _ hI]
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [ae_restrict_of_ae hz] with z hz'
    rw [integral_mul_const, hz', zero_mul]
  · intro p hp
    have : p.1 ∉ tsupport α := fun h => hp.2 ⟨⟨(hs h).1.le, (hs h).2.le⟩, hp.1.2⟩
    simp [zero_off this, deriv_zero_off this]

theorem limit_zero {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) {w t : ℝ → ℝ} {B C : ℝ} (hC : 0 ≤ C)
    (hF : IntegrableOn F S) (hg : IntegrableOn (fun p : ℝ × ℝ => (w p.1 : ℂ) * g p) S)
    (hgm : AEStronglyMeasurable g (volume.restrict S)) (hw : ∀ p ∈ S, 0 ≤ w p.1)
    (ht : Continuous t) (htB : ∀ p ∈ S, |t p.2| ≤ B)
    (a d : ℕ → ℝ → ℝ) (a0 d0 : ℝ → ℝ) (ha : ∀ k, Continuous (a k)) (hd : ∀ k, Continuous (d k))
    (hab : ∀ k, ∀ p ∈ S, |a k p.1| ≤ C * w p.1) (hdb : ∀ k, ∀ p ∈ S, |d k p.1| ≤ C)
    (hlim : ∀ᵐ p ∂(volume.restrict S), Tendsto (fun k => a k p.1) atTop (𝓝 (a0 p.1)) ∧
      Tendsto (fun k => d k p.1) atTop (𝓝 (d0 p.1)))
    (hzero : ∀ k, ∫ p in S, (((d k p.1 : ℝ) : ℂ) * F p + ((a k p.1 : ℝ) : ℂ) * g p) * ((t p.2 : ℝ) : ℂ) = 0) :
    ∫ p in S, (((d0 p.1 : ℝ) : ℂ) * F p + ((a0 p.1 : ℝ) : ℂ) * g p) * ((t p.2 : ℝ) : ℂ) = 0 := by
  have hbd : ∀ k, ∀ p ∈ S, ‖(((d k p.1 : ℝ) : ℂ) * F p + ((a k p.1 : ℝ) : ℂ) * g p) * ((t p.2 : ℝ) : ℂ)‖ ≤
      (C * ‖F p‖ + C * ‖(w p.1 : ℂ) * g p‖) * B := by
    intro k p hp
    have h1 : ‖((d k p.1 : ℝ) : ℂ) * F p‖ ≤ C * ‖F p‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hdb k p hp) (norm_nonneg _)
    have h2 : ‖((a k p.1 : ℝ) : ℂ) * g p‖ ≤ C * ‖(w p.1 : ℂ) * g p‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (hw p hp), ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hab k p hp) (norm_nonneg _)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul ((norm_add_le _ _).trans (add_le_add h1 h2)) (htB p hp) (abs_nonneg _) (by positivity)
  have hT := tendsto_integral_of_dominated_convergence
    (fun p : ℝ × ℝ => (C * ‖F p‖ + C * ‖(w p.1 : ℂ) * g p‖) * B)
    (F := fun k p => (((d k p.1 : ℝ) : ℂ) * F p + ((a k p.1 : ℝ) : ℂ) * g p) * ((t p.2 : ℝ) : ℂ))
    (f := fun p => (((d0 p.1 : ℝ) : ℂ) * F p + ((a0 p.1 : ℝ) : ℂ) * g p) * ((t p.2 : ℝ) : ℂ))
    (μ := volume.restrict S)
    (fun k => ((((Complex.continuous_ofReal.comp ((hd k).comp continuous_fst)).aestronglyMeasurable.mul hF.1).add
      ((Complex.continuous_ofReal.comp ((ha k).comp continuous_fst)).aestronglyMeasurable.mul hgm)).mul
      (Complex.continuous_ofReal.comp (ht.comp continuous_snd)).aestronglyMeasurable))
    (((hF.norm.const_mul C).add (hg.norm.const_mul C)).mul_const B)
    (fun k => (ae_restrict_iff' hS).2 (Eventually.of_forall fun p hp => hbd k p hp))
    (hlim.mono fun p hp => ((((Complex.continuous_ofReal.tendsto _).comp hp.2).mul_const (F p)).add
      (((Complex.continuous_ofReal.tendsto _).comp hp.1).mul_const (g p))).mul_const _)
  have e : (fun k => ∫ p in S, (((d k p.1 : ℝ) : ℂ) * F p + ((a k p.1 : ℝ) : ℂ) * g p) * ((t p.2 : ℝ) : ℂ)) =
      fun _ => 0 := funext hzero
  rw [e] at hT
  exact tendsto_nhds_unique hT tendsto_const_nhds

def bumpSeq (δ : ℝ) (hδ : 0 < δ) (k : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := δ * (1 / ((k : ℝ) + 1)) / 2
  rOut := δ * (1 / ((k : ℝ) + 1))
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : 0 < δ * (1 / ((k : ℝ) + 1)) := by positivity
    linarith

theorem rect_c1 (hF : ∀ R Z, IntegrableOn F (Icc 0 R ×ˢ Icc (-Z) Z))
    (hg : ∀ R Z, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * g p) (Icc 0 R ×ˢ Icc (-Z) Z))
    (hW : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * F p = -∫ p, (ψ p : ℂ) * g p)
    {r₁ r₂ z₁ z₂ : ℝ} (h0 : 0 ≤ r₁) {w : ℝ → ℝ} (hwc : Continuous w) (hwpos : ∀ r, 0 < r → 0 < w r)
    (hwn : ∀ r ∈ Icc r₁ r₂, 0 ≤ w r)
    (hFr : IntegrableOn F (Icc r₁ r₂ ×ˢ Icc z₁ z₂))
    (hgr : IntegrableOn (fun p : ℝ × ℝ => (w p.1 : ℂ) * g p) (Icc r₁ r₂ ×ˢ Icc z₁ z₂))
    (hgm : AEStronglyMeasurable g (volume.restrict (Icc r₁ r₂ ×ˢ Icc z₁ z₂)))
    {α : ℝ → ℝ} (hα : ContDiff ℝ 1 α) (hc : HasCompactSupport α) (hs : tsupport α ⊆ Ioo r₁ r₂)
    {t : ℝ → ℝ} (ht : Continuous t) :
    ∫ p in Icc r₁ r₂ ×ˢ Icc z₁ z₂, (((deriv α p.1 : ℝ) : ℂ) * F p + ((α p.1 : ℝ) : ℂ) * g p) * ((t p.2 : ℝ) : ℂ)
      = 0 := by
  obtain ⟨δ, hδ, hδs⟩ := hc.isCompact.exists_cthickening_subset_open isOpen_Ioo hs
  set Kδ := Metric.cthickening δ (tsupport α) with hKδ
  have hKc : IsCompact Kδ := hc.isCompact.cthickening
  set ρ := bumpSeq δ hδ with hρ
  set a : ℕ → ℝ → ℝ := fun k => (ρ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] α with ha
  have hαc := hα.continuous
  have hdc : Continuous (deriv α) := hα.continuous_deriv le_rfl
  have hloc : ∀ k, LocallyIntegrable ((ρ k).normed volume) volume := fun k =>
    ((ρ k).integrable_normed).locallyIntegrable
  have hsmooth : ∀ k, ContDiff ℝ ∞ (a k) := fun k =>
    (ρ k).hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (ρ k).contDiff_normed hαc.locallyIntegrable
  have hcs : ∀ k, HasCompactSupport (a k) := fun k =>
    (ρ k).hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hc
  have hrO : ∀ k, (ρ k).rOut ≤ δ := by
    intro k
    show δ * (1 / ((k : ℝ) + 1)) ≤ δ
    have : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith
  have hsupp : ∀ k, Function.support (a k) ⊆ Kδ := by
    intro k x hx
    have h1 := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) hx
    rw [(ρ k).support_normed_eq] at h1
    obtain ⟨u, hu, s, hs', rfl⟩ := h1
    refine Metric.mem_cthickening_of_dist_le _ s δ _ (subset_tsupport _ hs') ?_
    rw [Metric.mem_ball, dist_zero_right] at hu
    rw [Real.dist_eq, add_sub_cancel_right, ← Real.norm_eq_abs]
    exact hu.le.trans (hrO k)
  have hts : ∀ k, tsupport (a k) ⊆ Ioo r₁ r₂ := fun k =>
    (closure_minimal (hsupp k) Metric.isClosed_cthickening).trans hδs
  have hzero : ∀ k, ∫ p in Icc r₁ r₂ ×ˢ Icc z₁ z₂,
      (((deriv (a k) p.1 : ℝ) : ℂ) * F p + ((a k p.1 : ℝ) : ℂ) * g p) * ((t p.2 : ℝ) : ℂ) = 0 := fun k =>
    rect_smooth hF hg hW (hsmooth k) (hcs k) h0 (hts k) z₁ z₂ ht
  have hder : ∀ k x, deriv (a k) x = ((ρ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] deriv α) x :=
    fun k x => (HasCompactSupport.hasDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (hloc k) hc hα x).deriv
  have hrT : Tendsto (fun k => (ρ k).rOut) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul δ
    rw [mul_zero] at this
    exact this
  obtain ⟨Mα, hMα⟩ := hαc.bounded_above_of_compact_support hc
  obtain ⟨Dα, hDα⟩ := hdc.bounded_above_of_compact_support hc.deriv
  have hMα0 : 0 ≤ Mα := (norm_nonneg _).trans (hMα 0)
  have hDα0 : 0 ≤ Dα := (norm_nonneg _).trans (hDα 0)
  have hconvb : ∀ k (f : ℝ → ℝ) (M : ℝ), 0 ≤ M → Continuous f → (∀ x, ‖f x‖ ≤ M) → ∀ x,
      |((ρ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x| ≤ M := by
    intro k f M hM hf hfM x
    have := dist_convolution_le (μ := volume) (z₀ := (0 : ℝ)) (x₀ := x) hM (ρ k).support_normed_eq.subset
      (fun y => (ρ k).nonneg_normed y) (ρ k).integral_normed hf.aestronglyMeasurable
      (fun y _ => by rw [dist_zero_right]; exact hfM y)
    rwa [dist_zero_right, Real.norm_eq_abs] at this
  have hwK : ContinuousOn (fun x => 1 / w x) Kδ := by
    refine ContinuousOn.div continuousOn_const hwc.continuousOn (fun x hx => ?_)
    have := hδs hx
    exact (hwpos x (h0.trans_lt this.1)).ne'
  obtain ⟨Cw, hCw⟩ := hKc.exists_bound_of_continuousOn hwK
  set C := Mα * max Cw 0 + Dα with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hab : ∀ k, ∀ p ∈ Icc r₁ r₂ ×ˢ Icc z₁ z₂, |a k p.1| ≤ C * w p.1 := by
    intro k p hp
    have hwp := hwn p.1 hp.1
    by_cases hK : p.1 ∈ Kδ
    · have hw0 : 0 < w p.1 := hwpos p.1 (h0.trans_lt (hδs hK).1)
      have h1 : 1 ≤ max Cw 0 * w p.1 := by
        have h2 : 1 / w p.1 ≤ max Cw 0 := by
          have := hCw p.1 hK
          rw [Real.norm_eq_abs] at this
          exact (le_abs_self _).trans (this.trans (le_max_left _ _))
        rw [div_le_iff₀ hw0] at h2
        linarith
      calc |a k p.1| ≤ Mα := hconvb k α Mα hMα0 hαc hMα p.1
        _ ≤ Mα * (max Cw 0 * w p.1) := le_mul_of_one_le_right hMα0 h1
        _ ≤ C * w p.1 := by rw [hCdef]; nlinarith
    · have : a k p.1 = 0 := by
        by_contra hne
        exact hK (hsupp k hne)
      rw [this, abs_zero]
      exact mul_nonneg hC0 hwp
  have hdb : ∀ k, ∀ p ∈ Icc r₁ r₂ ×ˢ Icc z₁ z₂, |deriv (a k) p.1| ≤ C := by
    intro k p _
    rw [hder]
    refine (hconvb k (deriv α) Dα hDα0 hdc hDα p.1).trans ?_
    rw [hCdef]
    have : 0 ≤ Mα * max Cw 0 := mul_nonneg hMα0 (le_max_right _ _)
    linarith
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (ht.continuousOn (s := Icc z₁ z₂))
  refine limit_zero (measurableSet_Icc.prod measurableSet_Icc) hC0 hFr hgr hgm (fun p hp => hwn p.1 hp.1) ht
    (B := B) (fun p hp => by simpa using hB p.2 hp.2) a (fun k => deriv (a k)) α (deriv α)
    (fun k => (hsmooth k).continuous) (fun k => (hsmooth k).continuous_deriv (by simp)) hab hdb
    (Eventually.of_forall fun p => ⟨ContDiffBump.convolution_tendsto_right_of_continuous hrT hαc p.1, ?_⟩) hzero
  simp only [hder]
  exact ContDiffBump.convolution_tendsto_right_of_continuous hrT hdc p.1

theorem edge_bound {p s q δ M D : ℝ} (hδ : 0 < δ) (hq : |q| ≤ 1) (hs : |s| ≤ D)
    (hp : s ≠ 0 → |p| ≤ M * (2 * δ)) (hM : 0 ≤ M) (hD : 0 ≤ D) :
    |p * (s * (1 / δ) * q)| ≤ 2 * M * D := by
  by_cases hs0 : s = 0
  · simp [hs0]; positivity
  have h1 : |p| * |s| * |q| ≤ M * (2 * δ) * D * 1 :=
    mul_le_mul (mul_le_mul (hp hs0) hs (abs_nonneg _) (by positivity)) hq (abs_nonneg _) (by positivity)
  have e : |p * (s * (1 / δ) * q)| = |p| * |s| * |q| / δ := by
    rw [abs_mul, abs_mul, abs_mul, abs_div, abs_one, abs_of_pos hδ]
    ring
  rw [e, div_le_iff₀ hδ]
  nlinarith

theorem trans_deriv_zero {x : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) : deriv Real.smoothTransition x = 0 := by
  rcases lt_or_gt_of_ne (show x ≠ 0 from fun h => hx (by rw [h]; exact ⟨le_rfl, zero_le_one⟩)) with h | h
  · have e : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [e.deriv_eq, deriv_const]
  · have h1 : 1 < x := by
      by_contra h2
      exact hx ⟨h.le, not_lt.1 h2⟩
    have e : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds h1] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [e.deriv_eq, deriv_const]

theorem rect_psi (hF : ∀ R Z, IntegrableOn F (Icc 0 R ×ˢ Icc (-Z) Z))
    (hg : ∀ R Z, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * g p) (Icc 0 R ×ˢ Icc (-Z) Z))
    (hW : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * F p = -∫ p, (ψ p : ℂ) * g p)
    {r₁ r₂ z₁ z₂ : ℝ} (h0 : 0 ≤ r₁) (h12 : r₁ < r₂) {w : ℝ → ℝ} (hwc : Continuous w)
    (hwpos : ∀ r, 0 < r → 0 < w r) (hwn : ∀ r ∈ Icc r₁ r₂, 0 ≤ w r)
    (hwl : ∀ r ∈ Icc r₁ r₂, r - r₁ ≤ (1 + (r₂ - r₁)) * w r)
    (hFr : IntegrableOn F (Icc r₁ r₂ ×ˢ Icc z₁ z₂))
    (hgr : IntegrableOn (fun p : ℝ × ℝ => (w p.1 : ℂ) * g p) (Icc r₁ r₂ ×ˢ Icc z₁ z₂))
    (hgm : AEStronglyMeasurable g (volume.restrict (Icc r₁ r₂ ×ˢ Icc z₁ z₂)))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψ1 : ψ r₁ = 0) (hψ2 : ψ r₂ = 0) {t : ℝ → ℝ} (ht : Continuous t) :
    ∫ p in Icc r₁ r₂ ×ˢ Icc z₁ z₂, (((deriv ψ p.1 : ℝ) : ℂ) * F p + ((ψ p.1 : ℝ) : ℂ) * g p) * ((t p.2 : ℝ) : ℂ)
      = 0 := by
  set L := r₂ - r₁ with hL
  have hL0 : 0 < L := by rw [hL]; linarith
  set S := Real.smoothTransition with hSdef
  have hS : ContDiff ℝ ∞ S := Real.smoothTransition.contDiff
  have hSd : Differentiable ℝ S := hS.differentiable (by simp)
  have hS'c : Continuous (deriv S) := hS.continuous_deriv (by simp)
  have hS01 : ∀ x, |S x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg x)]
    exact Real.smoothTransition.le_one x
  obtain ⟨D, hD⟩ := hS'c.bounded_above_of_compact_support
    (HasCompactSupport.intro isCompact_Icc (fun x hx => trans_deriv_zero hx))
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  have hψd : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  obtain ⟨Mψ, hMψ⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hψ.continuous_deriv le_rfl).continuousOn (s := Icc r₁ r₂))
  set M := max Mψ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hmvt : ∀ x y, r₁ ≤ x → x ≤ y → y ≤ r₂ → |ψ y - ψ x| ≤ M * (y - x) := by
    intro x y hx hxy hy
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := ψ) (f' := deriv ψ) (C := M)
      (fun u _ => (hψd u).hasDerivAt.hasDerivWithinAt)
      (fun u hu => (hMψ u ⟨hx.trans hu.1, hu.2.le.trans hy⟩).trans (le_max_left _ _)) y ⟨hxy, le_rfl⟩
    rwa [Real.norm_eq_abs] at this
  have hleft : ∀ r ∈ Icc r₁ r₂, |ψ r| ≤ M * (r - r₁) := fun r hr => by
    have := hmvt r₁ r le_rfl hr.1 hr.2
    rwa [hψ1, sub_zero] at this
  have hright : ∀ r ∈ Icc r₁ r₂, |ψ r| ≤ M * (r₂ - r) := fun r hr => by
    have := hmvt r r₂ hr.1 hr.2 le_rfl
    rwa [hψ2, zero_sub, abs_neg] at this
  set δ : ℕ → ℝ := fun k => L / ((k : ℝ) + 4) with hδdef
  have hδ : ∀ k, 0 < δ k := fun k => by positivity
  set η : ℕ → ℝ → ℝ := fun k r => S ((r - r₁) / δ k - 1) * S ((r₂ - r) / δ k - 1) with hηdef
  set a : ℕ → ℝ → ℝ := fun k r => ψ r * η k r with hadef
  have hη : ∀ k, ContDiff ℝ ∞ (η k) := fun k =>
    (hS.comp (((contDiff_id.sub contDiff_const).div_const _).sub contDiff_const)).mul
      (hS.comp (((contDiff_const.sub contDiff_id).div_const _).sub contDiff_const))
  have ha1 : ∀ k, ContDiff ℝ 1 (a k) := fun k => hψ.mul ((hη k).of_le (by exact_mod_cast le_top))
  have hηz : ∀ k r, r ∉ Icc (r₁ + δ k) (r₂ - δ k) → η k r = 0 := by
    intro k r hr
    have hd := hδ k
    rcases not_and_or.1 hr with h | h
    · have : (r - r₁) / δ k - 1 ≤ 0 := by
        rw [sub_nonpos, div_le_one hd]
        linarith [not_le.1 h]
      simp only [hηdef, hSdef, Real.smoothTransition.zero_of_nonpos this, zero_mul]
    · have : (r₂ - r) / δ k - 1 ≤ 0 := by
        rw [sub_nonpos, div_le_one hd]
        linarith [not_le.1 h]
      simp only [hηdef, hSdef, Real.smoothTransition.zero_of_nonpos this, mul_zero]
  have hac : ∀ k, HasCompactSupport (a k) := fun k =>
    HasCompactSupport.intro (K := Icc (r₁ + δ k) (r₂ - δ k)) isCompact_Icc
      (fun r hr => by simp only [hadef, hηz k r hr, mul_zero])
  have hats : ∀ k, tsupport (a k) ⊆ Ioo r₁ r₂ := by
    intro k
    refine (closure_minimal (fun r hr => ?_) (isClosed_Icc (a := r₁ + δ k) (b := r₂ - δ k))).trans
      (fun r hr => ⟨by linarith [hr.1, hδ k], by linarith [hr.2, hδ k]⟩)
    by_contra hn
    exact hr (by simp only [hadef, hηz k r hn, mul_zero])
  have hzero : ∀ k, ∫ p in Icc r₁ r₂ ×ˢ Icc z₁ z₂,
      (((deriv (a k) p.1 : ℝ) : ℂ) * F p + ((a k p.1 : ℝ) : ℂ) * g p) * ((t p.2 : ℝ) : ℂ) = 0 := fun k =>
    rect_c1 hF hg hW h0 hwc hwpos hwn hFr hgr hgm (ha1 k) (hac k) (hats k) ht
  have hderiv : ∀ k r, deriv (a k) r = deriv ψ r * η k r +
      (ψ r * (deriv S ((r - r₁) / δ k - 1) * (1 / δ k) * S ((r₂ - r) / δ k - 1)) -
        ψ r * (deriv S ((r₂ - r) / δ k - 1) * (1 / δ k) * S ((r - r₁) / δ k - 1))) := by
    intro k r
    have h1 : HasDerivAt (fun r => (r - r₁) / δ k - 1) (1 / δ k) r :=
      (((hasDerivAt_id r).sub_const r₁).div_const (δ k)).sub_const 1
    have h2 : HasDerivAt (fun r => (r₂ - r) / δ k - 1) (-1 / δ k) r :=
      (((hasDerivAt_id r).const_sub r₂).div_const (δ k)).sub_const 1
    have h3 := ((hSd _).hasDerivAt.comp r h1).mul ((hSd _).hasDerivAt.comp r h2)
    have h4 := (hψd r).hasDerivAt.mul h3
    rw [(show HasDerivAt (a k) _ r from h4).deriv]
    simp only [hηdef, Function.comp_def, Pi.mul_apply]
    ring
  have hab : ∀ k, ∀ p ∈ Icc r₁ r₂ ×ˢ Icc z₁ z₂, |a k p.1| ≤ (M * (1 + L) + (M + 4 * M * D)) * w p.1 := by
    intro k p hp
    have hr := hp.1
    have hη1 : |η k p.1| ≤ 1 := by
      simp only [hηdef, abs_mul]
      exact mul_le_one₀ (hS01 _) (abs_nonneg _) (hS01 _)
    have h1 : |a k p.1| ≤ |ψ p.1| := by
      simp only [hadef, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) hη1
    have h2 : M * (p.1 - r₁) ≤ M * ((1 + L) * w p.1) := mul_le_mul_of_nonneg_left (hwl p.1 hr) hM0
    have h3 : 0 ≤ (M + 4 * M * D) * w p.1 := mul_nonneg (by positivity) (hwn p.1 hr)
    nlinarith [hleft p.1 hr]
  have hdb : ∀ k, ∀ p ∈ Icc r₁ r₂ ×ˢ Icc z₁ z₂, |deriv (a k) p.1| ≤ M * (1 + L) + (M + 4 * M * D) := by
    intro k p hp
    have hr := hp.1
    rw [hderiv]
    have hη1 : |η k p.1| ≤ 1 := by
      simp only [hηdef, abs_mul]
      exact mul_le_one₀ (hS01 _) (abs_nonneg _) (hS01 _)
    have e1 : |deriv ψ p.1 * η k p.1| ≤ M := by
      rw [abs_mul]
      have := (hMψ p.1 hr).trans (le_max_left Mψ 0)
      rw [Real.norm_eq_abs] at this
      exact (mul_le_mul this hη1 (abs_nonneg _) hM0).trans (by rw [mul_one])
    have e2 := edge_bound (p := ψ p.1) (s := deriv S ((p.1 - r₁) / δ k - 1)) (q := S ((r₂ - p.1) / δ k - 1))
      (hδ k) (hS01 _) (by simpa using hD _) (fun hs0 => by
        have hin : (p.1 - r₁) / δ k - 1 ∈ Icc (0 : ℝ) 1 := by
          by_contra hn; exact hs0 (trans_deriv_zero hn)
        have : p.1 - r₁ ≤ 2 * δ k := by
          have := hin.2
          rw [sub_le_iff_le_add, div_le_iff₀ (hδ k)] at this
          linarith
        exact (hleft p.1 hr).trans (mul_le_mul_of_nonneg_left this hM0)) hM0 hD0
    have e3 := edge_bound (p := ψ p.1) (s := deriv S ((r₂ - p.1) / δ k - 1)) (q := S ((p.1 - r₁) / δ k - 1))
      (hδ k) (hS01 _) (by simpa using hD _) (fun hs0 => by
        have hin : (r₂ - p.1) / δ k - 1 ∈ Icc (0 : ℝ) 1 := by
          by_contra hn; exact hs0 (trans_deriv_zero hn)
        have : r₂ - p.1 ≤ 2 * δ k := by
          have := hin.2
          rw [sub_le_iff_le_add, div_le_iff₀ (hδ k)] at this
          linarith
        exact (hright p.1 hr).trans (mul_le_mul_of_nonneg_left this hM0)) hM0 hD0
    have hML : 0 ≤ M * (1 + L) := mul_nonneg hM0 (by linarith)
    calc _ ≤ |deriv ψ p.1 * η k p.1| + (|ψ p.1 * (deriv S ((p.1 - r₁) / δ k - 1) * (1 / δ k) *
            S ((r₂ - p.1) / δ k - 1))| + |ψ p.1 * (deriv S ((r₂ - p.1) / δ k - 1) * (1 / δ k) *
            S ((p.1 - r₁) / δ k - 1))|) := (abs_add_le _ _).trans (add_le_add le_rfl (abs_sub _ _))
      _ ≤ M + (2 * M * D + 2 * M * D) := add_le_add e1 (add_le_add e2 e3)
      _ ≤ _ := by linarith
  have hnull : ∀ c : ℝ, ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p.1 ≠ c := by
    intro c
    have h : (volume : Measure (ℝ × ℝ)) ({c} ×ˢ univ) = 0 := by
      rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with p hp
    exact fun hc => hp ⟨hc, trivial⟩
  have hev : ∀ r ∈ Ioo r₁ r₂, ∀ᶠ k in atTop, a k =ᶠ[𝓝 r] ψ := by
    intro r hr
    have hε : 0 < min (r - r₁) (r₂ - r) := lt_min (by linarith [hr.1]) (by linarith [hr.2])
    obtain ⟨N, hN⟩ := exists_nat_gt (3 * L / min (r - r₁) (r₂ - r))
    refine eventually_atTop.2 ⟨N, fun k hk => ?_⟩
    have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
    have h3 : 3 * δ k < min (r - r₁) (r₂ - r) := by
      simp only [hδdef]
      rw [div_lt_iff₀ hε] at hN
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    have hm1 := min_le_left (r - r₁) (r₂ - r)
    have hm2 := min_le_right (r - r₁) (r₂ - r)
    have hd := hδ k
    filter_upwards [Metric.ball_mem_nhds r hd] with y hy
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
    have u1 : 1 ≤ (y - r₁) / δ k - 1 := by
      rw [le_sub_iff_add_le, le_div_iff₀ hd]; linarith
    have u2 : 1 ≤ (r₂ - y) / δ k - 1 := by
      rw [le_sub_iff_add_le, le_div_iff₀ hd]; linarith
    simp only [hadef, hηdef, hSdef, Real.smoothTransition.one_of_one_le u1,
      Real.smoothTransition.one_of_one_le u2, mul_one]
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (ht.continuousOn (s := Icc z₁ z₂))
  have hC0 : 0 ≤ M * (1 + L) + (M + 4 * M * D) := by
    have : 0 ≤ 1 + L := by linarith
    positivity
  refine limit_zero (measurableSet_Icc.prod measurableSet_Icc) hC0 hFr hgr hgm (fun p hp => hwn p.1 hp.1) ht
    (B := B) (fun p hp => by simpa using hB p.2 hp.2) a (fun k => deriv (a k)) ψ (deriv ψ)
    (fun k => (ha1 k).continuous) (fun k => (ha1 k).continuous_deriv le_rfl) hab hdb ?_ hzero
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc), ae_restrict_of_ae (hnull r₁),
    ae_restrict_of_ae (hnull r₂)] with p hp h1 h2
  have hr : p.1 ∈ Ioo r₁ r₂ := ⟨lt_of_le_of_ne hp.1.1 (Ne.symm h1), lt_of_le_of_ne hp.1.2 h2⟩
  have hk := hev p.1 hr
  exact ⟨tendsto_const_nhds.congr' (hk.mono fun k hk' => hk'.eq_of_nhds.symm),
    tendsto_const_nhds.congr' (hk.mono fun k hk' => hk'.deriv_eq.symm)⟩

end Generic

end Breakdown.CellCert.CellAnalysis.ModeRadialWeakInternal

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert
open Breakdown.CellCert.CellAnalysis.ModeRadialWeakInternal

theorem modeRadialWeak : ModeRadialWeakStatement := by
  intro K hK m v G H hs n a
  have hG2 : MemLp G 2 volume := grad_memLp hs.measurable_gradient hs.gradient_two
  have hGl : LocallyIntegrable G volume := hG2.locallyIntegrable (by norm_num)
  have hF := vel_on (m := m) hs.velocity_six n a
  have hg := grad_on (m := m) hGl n a
  have hW : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a =
        -∫ p, (ψ p : ℂ) * gradMode m n G a 0 p :=
    fun ψ h1 h2 h3 => (CellFormula.modeWeakIdentity m v G H hs n a ψ h1 h2 h3).1
  have h0 : 0 ≤ K.r₁ := hK.r_order.1
  have h12 : K.r₁ < K.r₂ := hK.r_order.2
  have hz0 : 0 ≤ K.z₁ := hK.z_order.1
  have hsub : K.rect ⊆ Icc 0 K.r₂ ×ˢ Icc (-K.z₂) K.z₂ := fun p hp =>
    ⟨⟨h0.trans hp.1.1, hp.1.2⟩, ⟨by linarith [hp.2.1, hp.2.2], hp.2.2⟩⟩
  have hFr : IntegrableOn (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) K.rect :=
    IntegrableOn.mono_set (hF K.r₂ K.z₂) hsub
  have hgr := LowEntry.Internal.gradMode_int K hK m n hs.measurable_gradient hs.gradient_two a 0
  refine ⟨hFr, hgr, ?_⟩
  intro ψ hψ hψ1 hψ2 t ht
  have hgm : AEStronglyMeasurable (fun p : ℝ × ℝ => gradMode m n G a 0 p) (volume.restrict K.rect) :=
    (grad_meas hs.measurable_gradient n a K.r₂ K.z₂).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hwpos : ∀ r, 0 < r → 0 < K.lineWeight r := by
    intro r hr
    simp only [CellBox.lineWeight]
    split_ifs <;> linarith
  have hwn : ∀ r ∈ Icc K.r₁ K.r₂, 0 ≤ K.lineWeight r := by
    intro r hr
    simp only [CellBox.lineWeight]
    split_ifs <;> linarith [hr.1]
  have hwl : ∀ r ∈ Icc K.r₁ K.r₂, r - K.r₁ ≤ (1 + (K.r₂ - K.r₁)) * K.lineWeight r := by
    intro r hr
    simp only [CellBox.lineWeight]
    split_ifs with h
    · rw [h, sub_zero]
      have : 0 ≤ r := h0.trans hr.1
      nlinarith
    · linarith [hr.2]
  exact rect_psi hF hg hW h0 h12 (LowEntry.Internal.lineWeight_cont K) hwpos hwn hwl hFr hgr hgm hψ hψ1 hψ2 ht

end Breakdown.CellCert.CellAnalysis
