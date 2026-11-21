import Breakdown.Cert.Nodes
import Breakdown.Cert.ProjectionSpec
import Breakdown.Cert.SupBoundHalfSsp
import Breakdown.Cert.PeriodIntegral

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.TestDense

theorem isH1Field_of_test {ψ : Space → Space} (hψ : IsTestField ψ) : IsH1Field ψ :=
  ⟨hψ.1, hψ.2.2, Freq.Internal.BilinTestFormula.test_memLp hψ 2,
    fun k => Freq.Internal.BilinTestFormula.partialField_memLp hψ k 2⟩

theorem coe_solField_test {ψ : Space → Space} (hψ : IsTestField ψ) :
    ((solField ψ : HBar) : L2C) = freqTrR (complexify (toLpOrZero 2 ψ)) := by
  have hs := Freq.Internal.H1Consistency.hat_mem_sig fieldOpRealized_holds
    (freqTrConjSym fieldOpRealized_holds) (isH1Field_of_test hψ)
  rw [solField, solProj_coe, Internal.ProjectionSpec.fieldOp_longitudinal_of_mem hs, sub_zero]

theorem halfSsp_solField_embed {ψ : Space → Space} (hψ : IsTestField ψ) :
    IsHalfSspOf (solField ψ) (embedX ψ) := by
  have hH := isH1Field_of_test hψ
  have hmem : ofGrad ψ ∈ Sig := (h1Consistency_holds ψ hH).1
  have hemb : ((embedX ψ : X) : L2C) = ofGrad ψ := by rw [embedX, dif_pos hmem]
  unfold IsHalfSspOf
  rw [hemb, coe_solField_test hψ]
  exact Freq.Internal.H1Consistency.ofGrad_ae fieldOpRealized_holds hH

theorem halfSsp_embed_solField_negSsp {φ : Space → Space} (hφ : IsTestField φ) :
    IsHalfSspOf (embedX φ) (solField (negSsp φ)) := by
  have h1 := halfSsp_solField_embed (isTestField_negSsp hφ)
  have h2 := embedNegSsp_holds φ hφ
  unfold IsHalfSspOf at h1 ⊢
  unfold IsSspOf at h2
  filter_upwards [h1, h2, Freq.Internal.H1Consistency.ae_ne_zero] with ξ e1 e2 hξ
  have ha : (2 * π * ‖ξ‖) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) (norm_ne_zero_iff.2 hξ)
  rw [e2] at e1
  apply (smul_right_inj ha).1
  rw [← e1, smul_smul]
  congr 1
  unfold sspFactor
  ring

theorem isHalfSspOf_sub {x k x' k' : X} (h : IsHalfSspOf x k) (h' : IsHalfSspOf x' k') :
    IsHalfSspOf (x - x') (k - k') := by
  unfold IsHalfSspOf at *
  simp only [Submodule.coe_sub]
  filter_upwards [h, h', Lp.coeFn_sub (k : L2C) (k' : L2C), Lp.coeFn_sub (x : L2C) (x' : L2C)]
    with ξ e1 e2 e3 e4
  rw [e3, e4, Pi.sub_apply, Pi.sub_apply, e1, e2, smul_sub]

theorem isSspOf_sub {x k x' k' : X} (h : IsSspOf x k) (h' : IsSspOf x' k') :
    IsSspOf (x - x') (k - k') := by
  unfold IsSspOf at *
  simp only [Submodule.coe_sub]
  filter_upwards [h, h', Lp.coeFn_sub (k : L2C) (k' : L2C), Lp.coeFn_sub (x : L2C) (x' : L2C)]
    with ξ e1 e2 e3 e4
  rw [e3, e4, Pi.sub_apply, Pi.sub_apply, e1, e2, smul_sub]

theorem inner_eq_zero_of_ssp {x y k l : X}
    (hx : ∀ ψ, IsTestField ψ → inner ℝ (solField ψ) x = 0)
    (hk : IsHalfSspOf y k) (hl : IsSspOf y l) : inner ℝ k x = 0 := by
  have key : ∀ ε > 0, |inner ℝ k x| ≤ ε * ‖x‖ := by
    intro ε hε
    obtain ⟨φ, hφ, h1, h2⟩ := testDense_holds.1 y l hl ε hε
    have hL : IsSspOf (embedX φ - y) (embedX (negSsp φ) - l) :=
      isSspOf_sub (embedNegSsp_holds φ hφ) hl
    have hH : IsHalfSspOf (embedX φ - y) (solField (negSsp φ) - k) :=
      isHalfSspOf_sub (halfSsp_embed_solField_negSsp hφ) hk
    have hsq := Breakdown.Cert.Internal.SupBoundHalfSsp.inner_eq_norm_sq hL hH
    have hle : ‖solField (negSsp φ) - k‖ ^ 2 ≤ ε ^ 2 := by
      rw [← hsq]
      calc inner ℝ (embedX φ - y) (embedX (negSsp φ) - l)
          ≤ ‖embedX φ - y‖ * ‖embedX (negSsp φ) - l‖ := real_inner_le_norm _ _
        _ ≤ ε * ε := mul_le_mul h1.le h2.le (norm_nonneg _) hε.le
        _ = ε ^ 2 := by ring
    have hn : ‖solField (negSsp φ) - k‖ ≤ ε := by
      nlinarith [norm_nonneg (solField (negSsp φ) - k)]
    have he : inner ℝ k x = -inner ℝ (solField (negSsp φ) - k) x := by
      rw [inner_sub_left, hx _ (isTestField_negSsp hφ)]
      ring
    rw [he, abs_neg]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  by_contra hne
  have hpos : 0 < |inner ℝ k x| := abs_pos.2 hne
  have hxpos : 0 < ‖x‖ + 1 := by positivity
  have h1 := key (|inner ℝ k x| / (‖x‖ + 1)) (div_pos hpos hxpos)
  have h2 : |inner ℝ k x| / (‖x‖ + 1) * ‖x‖ < |inner ℝ k x| := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hxpos]
    nlinarith [norm_nonneg x]
  linarith

theorem exists_mul (x : X) (g : Space → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ ξ, |g ξ| ≤ C)
    (he : ∀ ξ, g (-ξ) = g ξ) :
    ∃ z : X, ((z : L2C) : Space → CSpace) =ᵐ[volume] fun ξ => g ξ • (x : L2C) ξ := by
  have hm := Freq.Internal.TestDense.memLp_smul_of_bounded (x : L2C) g hg C hC
  exact ⟨⟨hm.toLp _, Freq.Internal.H1Consistency.mem_sig_of_ae fieldOpRealized_holds x.2 g he
    hm.coeFn_toLp⟩, hm.coeFn_toLp⟩

theorem zero_on_annulus (x : X) (hx : ∀ ψ, IsTestField ψ → inner ℝ (solField ψ) x = 0)
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    ∀ᵐ ξ ∂volume, r ≤ ‖ξ‖ → ‖ξ‖ ≤ R → (x : L2C) ξ = 0 := by
  set A : Set Space := {ξ | r ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ R} with hA
  have hAm : MeasurableSet A :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hpos : ∀ ξ ∈ A, 0 < ‖ξ‖ := fun ξ h => hr.trans_le h.1
  have hneg : ∀ ξ : Space, (-ξ ∈ A ↔ ξ ∈ A) := fun ξ => by simp [hA, norm_neg]
  obtain ⟨y, hy⟩ := exists_mul x (A.indicator fun ξ => (2 * π * ‖ξ‖)⁻¹)
    (((measurable_const.mul measurable_norm).inv).indicator hAm) (2 * π * r)⁻¹
    (fun ξ => by
      by_cases h : ξ ∈ A
      · rw [Set.indicator_of_mem h, abs_of_pos (by have := hpos ξ h; positivity)]
        exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left h.1 (by positivity))
      · rw [Set.indicator_of_notMem h, abs_zero]
        positivity)
    (fun ξ => by
      by_cases h : ξ ∈ A
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hneg ξ).2 h), norm_neg]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hneg ξ).1 h'))])
  obtain ⟨k, hk⟩ := exists_mul x (A.indicator fun _ => (1 : ℝ))
    (measurable_const.indicator hAm) 1
    (fun ξ => by
      by_cases h : ξ ∈ A
      · rw [Set.indicator_of_mem h, abs_one]
      · rw [Set.indicator_of_notMem h, abs_zero]
        exact zero_le_one)
    (fun ξ => by
      by_cases h : ξ ∈ A
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hneg ξ).2 h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hneg ξ).1 h'))])
  obtain ⟨l, hl⟩ := exists_mul x (A.indicator fun ξ => 2 * π * ‖ξ‖)
    ((measurable_const.mul measurable_norm).indicator hAm) (2 * π * R)
    (fun ξ => by
      by_cases h : ξ ∈ A
      · rw [Set.indicator_of_mem h, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left h.2 (by positivity)
      · rw [Set.indicator_of_notMem h, abs_zero]
        positivity)
    (fun ξ => by
      by_cases h : ξ ∈ A
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hneg ξ).2 h), norm_neg]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hneg ξ).1 h'))])
  have hyk : IsHalfSspOf y k := by
    unfold IsHalfSspOf
    filter_upwards [hy, hk] with ξ e1 e2
    rw [e1, e2, smul_smul]
    congr 1
    by_cases h : ξ ∈ A
    · have := (hpos ξ h).ne'
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      field_simp
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  have hyl : IsSspOf y l := by
    unfold IsSspOf
    filter_upwards [hy, hl] with ξ e1 e2
    rw [e1, e2, smul_smul]
    congr 1
    unfold sspFactor
    by_cases h : ξ ∈ A
    · have := (hpos ξ h).ne'
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      field_simp
      ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  have h0 := inner_eq_zero_of_ssp hx hyk hyl
  rw [Breakdown.Cert.Internal.SupBoundHalfSsp.inner_eq_integral] at h0
  have hexp : (fun ξ => inner ℝ ((k : L2C) ξ) ((x : L2C) ξ)) =ᵐ[volume]
      fun ξ => A.indicator (fun _ => (1 : ℝ)) ξ * ‖(x : L2C) ξ‖ ^ 2 := by
    filter_upwards [hk] with ξ e
    rw [e, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hnn : 0 ≤ᵐ[volume] fun ξ => inner ℝ ((k : L2C) ξ) ((x : L2C) ξ) := by
    filter_upwards [hexp] with ξ e
    rw [e]
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) ξ) (sq_nonneg _)
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn (L2.integrable_inner (𝕜 := ℝ) (k : L2C) (x : L2C))).1 h0
  filter_upwards [hz, hexp] with ξ e1 e2 h1 h2
  have e3 := e2.symm.trans e1
  rw [Pi.zero_apply, Set.indicator_of_mem (show ξ ∈ A from ⟨h1, h2⟩), one_mul] at e3
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 e3)

theorem eq_zero_of_forall_inner (x : X) (hx : ∀ ψ, IsTestField ψ → inner ℝ (solField ψ) x = 0) :
    x = 0 := by
  have h := fun n : ℕ => zero_on_annulus x hx (r := 1 / ((n : ℝ) + 1)) (R := (n : ℝ) + 1)
    (by positivity) (by positivity)
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero, Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [ae_all_iff.2 h, Freq.Internal.H1Consistency.ae_ne_zero] with ξ hall hξ
  obtain ⟨n, hn⟩ := exists_nat_ge (max ‖ξ‖ ‖ξ‖⁻¹)
  have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hinv : ‖ξ‖⁻¹ ≤ n := (le_max_right _ _).trans hn
  have h1 : 1 / ((n : ℝ) + 1) ≤ ‖ξ‖ := by
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hinv hpos.le
    rw [mul_inv_cancel₀ hpos.ne'] at this
    nlinarith
  have h2 : ‖ξ‖ ≤ (n : ℝ) + 1 := by linarith [le_max_left ‖ξ‖ ‖ξ‖⁻¹]
  exact hall n h1 h2

end Internal.TestDense


namespace Internal.TestDense

theorem circleRep_mem (t : TimeCircle) : circleRep t ∈ Ico (0 : ℝ) 1 := by
  unfold circleRep
  have := (AddCircle.equivIco (1 : ℝ) 0 t).2
  simpa using this

theorem circleRep_coe {σ : ℝ} (h : σ ∈ Ico (0 : ℝ) 1) : circleRep (σ : TimeCircle) = σ := by
  unfold circleRep
  exact AddCircle.equivIco_coe_of_mem (by simpa using h)

theorem measurable_circleRep : Measurable circleRep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable

theorem isSpaceTimeTestField_prod {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (has : HasCompactSupport a)
    {ψ : Space → Space} (hψ : IsTestField ψ) : IsSpaceTimeTestField (fun σ y => a σ • ψ y) := by
  refine ⟨(ha.comp contDiff_fst).smul (hψ.1.comp contDiff_snd), ?_, fun s y => ?_⟩
  · refine HasCompactSupport.intro (has.isCompact.prod hψ.2.1.isCompact) fun z hz => ?_
    rw [Set.mem_prod, not_and_or] at hz
    rcases hz with h | h
    · simp [image_eq_zero_of_notMem_tsupport h]
    · simp [image_eq_zero_of_notMem_tsupport h]
  · have hd := hψ.2.2 y
    unfold divergenceAt at hd ⊢
    beta_reduce
    rw [show (fun y => a s • ψ y) = a s • ψ from rfl, fderiv_const_smul ((hψ.1.differentiable (by simp)).differentiableAt)]
    simp only [FunLike.coe_smul, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, hd,
      mul_zero]

theorem periodize_prod {a : ℝ → ℝ} (hsupp : tsupport a ⊆ Ioo 0 1) (ψ : Space → Space) {σ : ℝ}
    (hσ : σ ∈ Ico (0 : ℝ) 1) (y : Space) :
    periodize (fun σ y => a σ • ψ y) σ y = a σ • ψ y := by
  unfold periodize
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    have : a (σ + n) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have h := hsupp hmem
      rcases lt_or_gt_of_ne hn with h' | h'
      · have h'' : n ≤ -1 := by omega
        have : (n : ℝ) ≤ -1 := by exact_mod_cast h''
        linarith [h.1, hσ.2]
      · have h'' : 1 ≤ n := by omega
        have : (1 : ℝ) ≤ n := by exact_mod_cast h''
        linarith [h.2, hσ.1]
    show a (σ + n) • ψ y = 0
    rw [this, zero_smul]

theorem solField_smul (c : ℝ) {ψ : Space → Space} (hψ : MemLp ψ 2 volume) :
    solField (fun y => c • ψ y) = c • solField ψ := by
  have h1 : MemLp (fun y => c • ψ y) 2 volume := hψ.const_smul c
  unfold solField toLpOrZero
  rw [dif_pos h1, dif_pos hψ, ← map_smul]
  refine congrArg solProj ?_
  apply Lp.ext
  filter_upwards [h1.coeFn_toLp, hψ.coeFn_toLp, Lp.coeFn_smul c (hψ.toLp ψ)] with y e1 e2 e3
  rw [e1, e3, Pi.smul_apply, e2]

theorem testInHH_prod_ae {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (has : HasCompactSupport a)
    (hsupp : tsupport a ⊆ Ioo 0 1) {ψ : Space → Space} (hψ : IsTestField ψ) :
    ((testInHH (fun σ y => a σ • ψ y) : HH) : TimeCircle → HBar) =ᵐ[volume]
      fun t => a (circleRep t) • solField ψ := by
  have hfun : onCircle (fun σ => solField (periodize (fun σ y => a σ • ψ y) σ)) =
      fun t => a (circleRep t) • solField ψ := by
    funext t
    unfold onCircle
    have : periodize (fun σ y => a σ • ψ y) (circleRep t) = fun y => a (circleRep t) • ψ y :=
      funext fun y => periodize_prod hsupp ψ (circleRep_mem t) y
    show solField (periodize (fun σ y => a σ • ψ y) (circleRep t)) = _
    rw [this, solField_smul _ (Freq.Internal.BilinTestFormula.test_memLp hψ 2)]
  obtain ⟨C, hC⟩ := ha.continuous.bounded_above_of_compact_support has
  have hm : MemLp (fun t => a (circleRep t) • solField ψ) 2 volume := by
    refine MemLp.of_bound ((ha.continuous.measurable.comp measurable_circleRep).aestronglyMeasurable.smul
      aestronglyMeasurable_const) (C * ‖solField ψ‖) (Filter.Eventually.of_forall fun t => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  have e : testInHH (fun σ y => a σ • ψ y) = hm.toLp _ := by
    have hc : ∀ {F : TimeCircle → HBar} (h : MemLp F 2 volume), circleLpOrZero F = h.toLp F :=
      fun h => dif_pos h
    exact (congrArg circleLpOrZero hfun).trans (hc hm)
  rw [e]
  exact hm.coeFn_toLp

theorem inner_testInHH_prod (f : HH) {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (has : HasCompactSupport a)
    (hsupp : tsupport a ⊆ Ioo 0 1) {ψ : Space → Space} (hψ : IsTestField ψ) :
    inner ℝ f (testInHH (fun σ y => a σ • ψ y)) =
      ∫ t, a (circleRep t) * inner ℝ ((f : TimeCircle → HBar) t) (solField ψ) := by
  have hae := testInHH_prod_ae ha has hsupp hψ
  refine (L2.inner_def f _).trans (integral_congr_ae ?_)
  filter_upwards [hae] with t ht
  rw [ht, real_inner_smul_right]

theorem ae_zero_of_integral {G : TimeCircle → ℝ} (hG : Integrable G)
    (h : ∀ a : ℝ → ℝ, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ Ioo 0 1 →
      ∫ t, a (circleRep t) * G t = 0) : ∀ᵐ t, G t = 0 := by
  have hmp := AddCircle.measurePreserving_mk (1 : ℝ) 0
  rw [zero_add] at hmp
  have hI : IntegrableOn (fun σ : ℝ => G σ) (Ioc 0 1) :=
    (hmp.integrable_comp hG.aestronglyMeasurable).2 hG
  have hloc : LocallyIntegrableOn (fun σ : ℝ => G σ) (Ioo 0 1) :=
    (hI.mono_set Ioo_subset_Ioc_self).locallyIntegrableOn
  have h1 := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun a ha has hsub => by
    have hz : ∀ σ, σ ∉ Ioo (0 : ℝ) 1 → a σ = 0 := fun σ hσ =>
      image_eq_zero_of_notMem_tsupport (fun hm => hσ (hsub hm))
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc (0 : ℝ) 1) (fun σ hσ =>
      by rw [hz σ (fun h' => hσ (Ioo_subset_Ioc_self h')), zero_smul])]
    have heq : EqOn (fun σ : ℝ => a σ • G σ) (fun σ : ℝ => a (circleRep σ) * G σ) (Ioc 0 1) := by
      intro σ hσ
      simp only [smul_eq_mul]
      rcases eq_or_lt_of_le hσ.2 with h1 | h1
      · have hc : ((σ : ℝ) : TimeCircle) = ((0 : ℝ) : TimeCircle) := by
          rw [h1, AddCircle.coe_period, AddCircle.coe_zero]
        rw [hc, circleRep_coe ⟨le_rfl, one_pos⟩, hz 0 (fun h' => lt_irrefl _ h'.1),
          hz σ (fun h' => by rw [h1] at h'; exact lt_irrefl _ h'.2)]
      · rw [circleRep_coe ⟨hσ.1.le, h1⟩]
    rw [setIntegral_congr_fun measurableSet_Ioc heq]
    have hp := AddCircle.integral_preimage (1 : ℝ) 0 (fun t => a (circleRep t) * G t)
    rw [zero_add] at hp
    rw [hp]
    exact h a ha has hsub)
  have h2 : ∀ᵐ σ : ℝ ∂((volume : Measure ℝ).restrict (Ioc (0 : ℝ) (0 + 1))), G σ = 0 := by
    rw [zero_add, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc, ae_restrict_iff' measurableSet_Ioo]
    exact h1
  have h3 := Breakdown.Cert.PeriodIntegralInternal.measurePreserving_equivIoc_val.quasiMeasurePreserving.ae h2
  filter_upwards [h3] with t ht
  rwa [Breakdown.Cert.PeriodIntegralInternal.coe_equivIoc_val] at ht

theorem ae_inner_zero (f : HH) (hf : ∀ φ, IsSpaceTimeTestField φ → inner ℝ f (testInHH φ) = 0)
    {ψ : Space → Space} (hψ : IsTestField ψ) :
    ∀ᵐ t, inner ℝ ((f : TimeCircle → HBar) t) (solField ψ) = 0 := by
  have hint : Integrable fun t => inner ℝ ((f : TimeCircle → HBar) t) (solField ψ) := by
    refine Integrable.mono' (((Lp.memLp f).integrable one_le_two).norm.mul_const ‖solField ψ‖)
      ((Lp.aestronglyMeasurable f).inner aestronglyMeasurable_const)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs]
    exact abs_real_inner_le_norm _ _
  apply ae_zero_of_integral hint
  intro a ha has hsub
  rw [← inner_testInHH_prod f ha has hsub hψ]
  exact hf _ (isSpaceTimeTestField_prod ha has hψ)

end Internal.TestDense

open Internal.TestDense in
theorem testDenseHolds_proof : TestDenseHolds := by
  intro f hf
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  have : SecondCountableTopology L2C := Lp.SecondCountableTopology
  set S : Set HBar := {v | ∃ ψ, IsTestField ψ ∧ solField ψ = v} with hS
  obtain ⟨D, hDS, hDc, hSD⟩ := (TopologicalSpace.IsSeparable.of_separableSpace S).exists_countable_dense_subset
  have hslice : ∀ v ∈ S, ∀ᵐ t, inner ℝ ((f : TimeCircle → HBar) t) v = 0 := by
    rintro v ⟨ψ, hψ, rfl⟩
    exact ae_inner_zero f hf hψ
  have hall : ∀ᵐ t, ∀ v ∈ D, inner ℝ ((f : TimeCircle → HBar) t) v = 0 :=
    (ae_ball_iff hDc).2 fun v hv => hslice v (hDS hv)
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hall] with t ht
  apply eq_zero_of_forall_inner
  intro ψ hψ
  have hcl : closure D ⊆ {v | inner ℝ ((f : TimeCircle → HBar) t) v = 0} :=
    closure_minimal (fun v hv => ht v hv)
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
  rw [real_inner_comm]
  exact hcl (hSD ⟨ψ, hψ, rfl⟩)

end Breakdown.Cert
