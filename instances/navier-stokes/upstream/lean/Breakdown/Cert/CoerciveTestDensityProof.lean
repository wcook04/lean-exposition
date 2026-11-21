import Breakdown.Cert.CoerciveTestDensity
import Breakdown.Cert.TestDense
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

open scoped ContDiff ENNReal Manifold
open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown.Coercive

namespace Internal.TestDensityProof

abbrev periodMeasure : Measure (ℝ × Space) :=
  (volume.restrict (Icc (0 : ℝ) 1)).prod (volume : Measure Space)

open Classical in
def toL2 (X : ℝ → Space → Space) : Lp Space 2 periodMeasure :=
  if h : MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure then h.toLp _ else 0

theorem coeFn_toL2 {X : ℝ → Space → Space}
    (h : MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure) :
    (toL2 X : ℝ × Space → Space) =ᵐ[periodMeasure] fun z => X z.1 z.2 := by
  rw [toL2, dif_pos h]
  exact h.coeFn_toLp

theorem periodMeasure_eq :
    periodMeasure = (volume : Measure (ℝ × Space)).restrict (Icc (0 : ℝ) 1 ×ˢ univ) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem aestronglyMeasurable_period {X : ℝ → Space → Space}
    (hX : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume) :
    AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) periodMeasure := by
  rw [periodMeasure_eq]
  exact hX.restrict

theorem memLp_of {X : ℝ → Space → Space}
    (hX : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume)
    (h2 : periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) < ⊤) :
    MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure := by
  have hm := aestronglyMeasurable_period hX
  rw [memLp_two_iff_integrable_sq_norm hm]
  have hmeas : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖X z.1 z.2‖ ^ 2)) periodMeasure :=
    (hm.norm.aemeasurable.pow_const 2).ennreal_ofReal
  refine ⟨(hm.norm.aemeasurable.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg _), lintegral_prod _ hmeas]
  exact h2

theorem periodic_int {X : ℝ → Space → Space} (hX : IsTimePeriodic X) (σ : ℝ) (n : ℤ) :
    X (σ + n) = X σ := by
  have hp : Function.Periodic X 1 := fun s => funext (hX s)
  simpa using (hp.int_mul n) σ

theorem ae_of_period {X : ℝ → Space → Space} (hX : IsTimePeriodic X)
    (h : ∀ᵐ z ∂periodMeasure, X z.1 z.2 = 0) : ∀ᵐ z : ℝ × Space, X z.1 z.2 = 0 := by
  rw [periodMeasure_eq, ae_restrict_iff' (measurableSet_Icc.prod MeasurableSet.univ)] at h
  have hn : ∀ n : ℤ, ∀ᵐ z : ℝ × Space, (z.1 + n, z.2) ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set Space) →
      X (z.1 + n) z.2 = 0 := by
    intro n
    have hmp : MeasurePreserving (Prod.map (fun s : ℝ => s + n) (id : Space → Space))
        (volume : Measure (ℝ × Space)) volume := by
      rw [Measure.volume_eq_prod]
      exact (measurePreserving_add_right volume (n : ℝ)).prod (MeasurePreserving.id volume)
    filter_upwards [hmp.quasiMeasurePreserving.ae h] with z hz
    simpa using hz
  filter_upwards [ae_all_iff.2 hn] with z hz
  have hmem : (z.1 + ((-⌊z.1⌋ : ℤ) : ℝ), z.2) ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set Space) := by
    refine ⟨⟨?_, ?_⟩, trivial⟩
    · push_cast
      linarith [Int.floor_le z.1]
    · push_cast
      linarith [Int.lt_floor_add_one z.1]
  have e := hz (-⌊z.1⌋) hmem
  rwa [periodic_int hX] at e

end Internal.TestDensityProof

namespace Internal.TestDensityProof


def periodicExt (a : ℝ → ℝ) (σ : ℝ) : ℝ := ∑ᶠ n : ℤ, a (σ + n)

theorem periodicExt_add_one (a : ℝ → ℝ) (σ : ℝ) : periodicExt a (σ + 1) = periodicExt a σ := by
  unfold periodicExt
  have e := finsum_comp_equiv (Equiv.addRight (1 : ℤ)) (f := fun n : ℤ => a (σ + n))
  rw [← e]
  congr 1
  funext n
  simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one]
  ring_nf

theorem exists_norm_bound {E : Type*} [Zero E] {w : Space → E} (hw : HasCompactSupport w) :
    ∃ R, ∀ y, R < ‖y‖ → w y = 0 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Space)).1 hw.isCompact.isBounded
  refine ⟨R, fun y hy => image_eq_zero_of_notMem_tsupport fun hm => ?_⟩
  have h := hR hm
  rw [Metric.mem_closedBall, dist_zero_right] at h
  linarith

theorem locallyFinite_translates {a : ℝ → ℝ} (hs : HasCompactSupport a) :
    LocallyFinite fun n : ℤ => Function.support fun σ => a (σ + n) := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hs.isCompact.isBounded
  intro x
  refine ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  refine (Set.finite_Icc (-⌈R + |x| + 1⌉) ⌈R + |x| + 1⌉).subset ?_
  rintro n ⟨σ, hσ1, hσ2⟩
  have hm : σ + n ∈ Metric.closedBall (0 : ℝ) R := hR (subset_tsupport _ hσ1)
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hm
  have hb : |(n : ℝ)| ≤ R + |x| + 1 := by
    have h1 : |σ - x| < 1 := by rw [abs_lt]; constructor <;> linarith [hσ2.1, hσ2.2]
    calc |(n : ℝ)| = |(σ + n) - (σ - x) - x| := by ring_nf
      _ ≤ |σ + n| + |σ - x| + |x| := by
          have := abs_sub (σ + n - (σ - x)) x
          have := abs_sub (σ + n) (σ - x)
          linarith
      _ ≤ R + |x| + 1 := by linarith
  have hc := Int.le_ceil (R + |x| + 1)
  rw [abs_le] at hb
  constructor
  · have : (-(⌈R + |x| + 1⌉ : ℝ)) ≤ n := by linarith
    exact_mod_cast this
  · have : (n : ℝ) ≤ ⌈R + |x| + 1⌉ := by linarith
    exact_mod_cast this

theorem periodicExt_contDiff {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hs : HasCompactSupport a) :
    ContDiff ℝ ∞ (periodicExt a) := by
  have h := contMDiff_finsum (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (n := ∞)
    (f := fun (n : ℤ) (σ : ℝ) => a (σ + n))
    (fun n => contMDiff_iff_contDiff.2 (ha.comp (contDiff_id.add contDiff_const)))
    (locallyFinite_translates hs)
  exact contMDiff_iff_contDiff.1 h

theorem periodicExt_eq {a : ℝ → ℝ} (hsupp : tsupport a ⊆ Ioo 0 1) {σ : ℝ}
    (hσ : σ ∈ Icc (0 : ℝ) 1) : periodicExt a σ = a σ := by
  unfold periodicExt
  rw [finsum_eq_single (fun n : ℤ => a (σ + n)) 0 (fun n hn => ?_)]
  · simp
  · apply image_eq_zero_of_notMem_tsupport
    intro hm
    have h := hsupp hm
    rcases lt_or_gt_of_ne hn with h' | h'
    · have : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      linarith [h.1, hσ.2]
    · have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      linarith [h.2, hσ.1]

theorem divergenceAt_smul (r : ℝ) {w : Space → Space} (hw : Differentiable ℝ w) (y : Space) :
    divergenceAt (fun y => r • w y) y = r * divergenceAt w y := by
  unfold divergenceAt
  rw [show (fun y => r • w y) = r • w from rfl, fderiv_const_smul (hw y)]
  simp only [FunLike.coe_smul, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul,
    ← Finset.mul_sum]

theorem isPeriodicTestField_prod {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hs : HasCompactSupport a)
    {w : Space → Space} (hw : IsTestField w) :
    IsPeriodicTestField (fun σ y => periodicExt a σ • w y) := by
  obtain ⟨R, hR⟩ := exists_norm_bound hw.2.1
  refine ⟨((periodicExt_contDiff ha hs).comp contDiff_fst).smul (hw.1.comp contDiff_snd),
    fun σ y => by simp only [periodicExt_add_one], ⟨R, fun σ y hy => by simp only [hR y hy, smul_zero]⟩,
    fun σ y => ?_⟩
  rw [divergenceAt_smul _ (hw.1.differentiable (by simp)), hw.2.2 y, mul_zero]

theorem gradientAt_const_mul (r : ℝ) {c : Space → ℝ} (hc : Differentiable ℝ c) (y : Space) :
    gradientAt (fun y => r * c y) y = r • gradientAt c y := by
  unfold gradientAt
  rw [fderiv_const_mul (hc y), Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  rfl

theorem isPeriodicTestPotential_prod {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hs : HasCompactSupport a)
    {c : Space → ℝ} (hc : ContDiff ℝ ∞ c) (hcs : HasCompactSupport c) :
    IsPeriodicTestPotential (fun σ y => periodicExt a σ * c y) := by
  obtain ⟨R, hR⟩ := exists_norm_bound hcs
  exact ⟨((periodicExt_contDiff ha hs).comp contDiff_fst).mul (hc.comp contDiff_snd),
    fun σ y => by simp only [periodicExt_add_one], ⟨R, fun σ y hy => by simp only [hR y hy, mul_zero]⟩⟩

theorem ae_zero_of_periodic_tests {G : ℝ → ℝ} (hG : IntegrableOn G (Icc 0 1))
    (h : ∀ a : ℝ → ℝ, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ Ioo 0 1 →
      ∫ σ in Icc (0 : ℝ) 1, periodicExt a σ * G σ = 0) :
    ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) 1)), G σ = 0 := by
  have hloc : LocallyIntegrableOn G (Ioo 0 1) :=
    (hG.mono_set (Ioo_subset_Icc_self : Ioo (0 : ℝ) 1 ⊆ Icc 0 1)).locallyIntegrableOn
  have h1 := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun a ha has hsub => by
    have hz : ∀ σ, σ ∉ Icc (0 : ℝ) 1 → a σ • G σ = 0 := fun σ hσ => by
      rw [image_eq_zero_of_notMem_tsupport (fun hm => hσ ((Ioo_subset_Icc_self : Ioo (0 : ℝ) 1 ⊆ Icc 0 1) (hsub hm))),
        zero_smul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    refine Eq.trans ?_ (h a ha has hsub)
    refine setIntegral_congr_fun measurableSet_Icc (fun σ hσ => ?_)
    simp only [smul_eq_mul, periodicExt_eq hsub hσ])
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := 1)),
    ae_restrict_iff' measurableSet_Ioo]
  exact h1

theorem memLp_const_time {w : Space → Space} (hw : MemLp w 2 volume) :
    MemLp (fun z : ℝ × Space => w z.2) 2 periodMeasure := by
  have hm : AEStronglyMeasurable (fun z : ℝ × Space => w z.2) (volume : Measure (ℝ × Space)) := by
    rw [Measure.volume_eq_prod]
    exact hw.1.comp_snd
  refine memLp_of (X := fun _ y => w y) hm ?_
  have hi := (memLp_two_iff_integrable_sq_norm hw.1).1 hw
  have hf : ∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 2) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => sq_nonneg _)).1 hi.2
  unfold periodLIntegral
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
  exact ENNReal.mul_lt_top hf ENNReal.ofReal_lt_top

theorem integrableOn_slicePairing {X : ℝ → Space → Space}
    (hm : MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure)
    {w : Space → Space} (hw : MemLp w 2 volume) :
    IntegrableOn (fun σ => ∫ y, inner ℝ (X σ y) (w y)) (Icc (0 : ℝ) 1) := by
  have hi : Integrable (fun z : ℝ × Space => inner ℝ (X z.1 z.2) (w z.2)) periodMeasure := by
    refine (L2.integrable_inner (𝕜 := ℝ) (toL2 X) (toL2 (fun _ y => w y))).congr ?_
    filter_upwards [coeFn_toL2 hm, coeFn_toL2 (X := fun _ y => w y) (memLp_const_time hw)] with z h1 h2
    rw [h1, h2]
  exact hi.integral_prod_left

theorem ae_forall_inner_zero {μ : Measure ℝ} (g : ℝ → Freq.L2R) (S : Set Freq.L2R)
    (h : ∀ v ∈ S, ∀ᵐ σ ∂μ, inner ℝ (g σ) v = 0) : ∀ᵐ σ ∂μ, ∀ v ∈ S, inner ℝ (g σ) v = 0 := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  have : SecondCountableTopology Freq.L2R := Lp.SecondCountableTopology
  obtain ⟨D, hDS, hDc, hSD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace S).exists_countable_dense_subset
  have hall : ∀ᵐ σ ∂μ, ∀ v ∈ D, inner ℝ (g σ) v = 0 := (ae_ball_iff hDc).2 fun v hv => h v (hDS hv)
  filter_upwards [hall] with σ hσ v hv
  have hcl : closure D ⊆ {v | inner ℝ (g σ) v = 0} :=
    closure_minimal (fun v hv => hσ v hv)
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
  exact hcl (hSD hv)

theorem inner_toLp_eq {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    inner ℝ (Freq.toLpOrZero 2 f) (Freq.toLpOrZero 2 g) = ∫ y, inner ℝ (f y) (g y) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Freq.Internal.H1Consistency.toLpOrZero_ae hf,
    Freq.Internal.H1Consistency.toLpOrZero_ae hg] with y h1 h2
  rw [h1, h2]

theorem ae_period_of_slices {X : ℝ → Space → Space}
    (hX : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) periodMeasure)
    (h : ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ᵐ y, X σ y = 0) :
    ∀ᵐ z ∂periodMeasure, X z.1 z.2 = 0 := by
  have hmk := hX.ae_eq_mk
  have hsl := Measure.ae_ae_of_ae_prod hmk
  have hset : MeasurableSet {z : ℝ × Space | hX.mk _ z = 0} :=
    hX.stronglyMeasurable_mk.measurable (measurableSet_singleton 0)
  have h2 : ∀ᵐ z ∂periodMeasure, hX.mk _ z = 0 := by
    rw [Measure.ae_prod_iff_ae_ae hset]
    filter_upwards [h, hsl] with σ h1 h3
    filter_upwards [h1, h3] with y e1 e3
    rw [← e3, e1]
  filter_upwards [hmk, h2] with z e1 e2
  rw [e1, e2]

end Internal.TestDensityProof

namespace Internal.TestDensityProof

open Breakdown.Freq Breakdown.Cert.Internal.TestDense Real

theorem inner_zero_of_ssp_negSsp {x y k l : Freq.X}
    (hx : ∀ ψ, IsTestField ψ → inner ℝ (Cert.solField (negSsp ψ)) x = 0)
    (hk : IsHalfSspOf y k) (hl : IsSspOf y l) : inner ℝ k x = 0 := by
  have key : ∀ ε > 0, |inner ℝ k x| ≤ ε * ‖x‖ := by
    intro ε hε
    obtain ⟨φ, hφ, h1, h2⟩ := testDense_holds.1 y l hl ε hε
    have hL : IsSspOf (embedX φ - y) (embedX (negSsp φ) - l) :=
      isSspOf_sub (embedNegSsp_holds φ hφ) hl
    have hH : IsHalfSspOf (embedX φ - y) (Cert.solField (negSsp φ) - k) :=
      isHalfSspOf_sub (halfSsp_embed_solField_negSsp hφ) hk
    have hsq := Breakdown.Cert.Internal.SupBoundHalfSsp.inner_eq_norm_sq hL hH
    have hle : ‖Cert.solField (negSsp φ) - k‖ ^ 2 ≤ ε ^ 2 := by
      rw [← hsq]
      calc inner ℝ (embedX φ - y) (embedX (negSsp φ) - l)
          ≤ ‖embedX φ - y‖ * ‖embedX (negSsp φ) - l‖ := real_inner_le_norm _ _
        _ ≤ ε * ε := mul_le_mul h1.le h2.le (norm_nonneg _) hε.le
        _ = ε ^ 2 := by ring
    have hn : ‖Cert.solField (negSsp φ) - k‖ ≤ ε := by
      nlinarith [norm_nonneg (Cert.solField (negSsp φ) - k)]
    have he : inner ℝ k x = -inner ℝ (Cert.solField (negSsp φ) - k) x := by
      rw [inner_sub_left, hx φ hφ]
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

theorem annulus_zero_of_negSsp (x : Freq.X)
    (hx : ∀ ψ, IsTestField ψ → inner ℝ (Cert.solField (negSsp ψ)) x = 0)
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    ∀ᵐ ξ ∂volume, r ≤ ‖ξ‖ → ‖ξ‖ ≤ R → (x : L2C) ξ = 0 := by
  set A : Set Space := {ξ | r ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ R} with hA
  have hAm : MeasurableSet A :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hpos : ∀ ξ ∈ A, 0 < ‖ξ‖ := fun ξ h => hr.trans_le h.1
  have hneg : ∀ ξ : Space, (-ξ ∈ A ↔ ξ ∈ A) := fun ξ => by simp [hA, norm_neg]
  have hev : ∀ f : Space → ℝ, (∀ ξ, f (-ξ) = f ξ) → ∀ ξ, A.indicator f (-ξ) = A.indicator f ξ := by
    intro f hf ξ
    by_cases h : ξ ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hneg ξ).2 h), hf]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hneg ξ).1 h'))]
  obtain ⟨y, hy⟩ := exists_mul x (A.indicator fun ξ => (2 * π * ‖ξ‖)⁻¹)
    (((measurable_const.mul measurable_norm).inv).indicator hAm) (2 * π * r)⁻¹
    (fun ξ => by
      by_cases h : ξ ∈ A
      · rw [Set.indicator_of_mem h, abs_of_pos (by have := hpos ξ h; positivity)]
        exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left h.1 (by positivity))
      · rw [Set.indicator_of_notMem h, abs_zero]
        positivity)
    (hev _ fun ξ => by rw [norm_neg])
  obtain ⟨k, hk⟩ := exists_mul x (A.indicator fun _ => (1 : ℝ))
    (measurable_const.indicator hAm) 1
    (fun ξ => by
      by_cases h : ξ ∈ A
      · rw [Set.indicator_of_mem h, abs_one]
      · rw [Set.indicator_of_notMem h, abs_zero]
        exact zero_le_one)
    (hev _ fun ξ => rfl)
  obtain ⟨l, hl⟩ := exists_mul x (A.indicator fun ξ => 2 * π * ‖ξ‖)
    ((measurable_const.mul measurable_norm).indicator hAm) (2 * π * R)
    (fun ξ => by
      by_cases h : ξ ∈ A
      · rw [Set.indicator_of_mem h, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left h.2 (by positivity)
      · rw [Set.indicator_of_notMem h, abs_zero]
        positivity)
    (hev _ fun ξ => by rw [norm_neg])
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
  have h0 := inner_zero_of_ssp_negSsp hx hyk hyl
  rw [Breakdown.Cert.Internal.SupBoundHalfSsp.inner_eq_integral] at h0
  have hexp : (fun ξ => inner ℝ ((k : L2C) ξ) ((x : L2C) ξ)) =ᵐ[volume]
      fun ξ => A.indicator (fun _ => (1 : ℝ)) ξ * ‖(x : L2C) ξ‖ ^ 2 := by
    filter_upwards [hk] with ξ e
    rw [e, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hnn : 0 ≤ᵐ[volume] fun ξ => inner ℝ ((k : L2C) ξ) ((x : L2C) ξ) := by
    filter_upwards [hexp] with ξ e
    rw [e]
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) ξ) (sq_nonneg _)
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn
    (L2.integrable_inner (𝕜 := ℝ) (k : L2C) (x : L2C))).1 h0
  filter_upwards [hz, hexp] with ξ e1 e2 h1 h2
  have e3 := e2.symm.trans e1
  rw [Pi.zero_apply, Set.indicator_of_mem (show ξ ∈ A from ⟨h1, h2⟩), one_mul] at e3
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 e3)

theorem eq_zero_of_negSsp_inner (x : Freq.X)
    (hx : ∀ ψ, IsTestField ψ → inner ℝ (Cert.solField (negSsp ψ)) x = 0) : x = 0 := by
  have h := fun n : ℕ => annulus_zero_of_negSsp x hx (r := 1 / ((n : ℝ) + 1)) (R := (n : ℝ) + 1)
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

end Internal.TestDensityProof

namespace Internal.TestDensityProof

def selectCLM (k : Fin 3) : Space →L[ℝ] Space :=
  (EuclideanSpace.proj k : Space →L[ℝ] ℝ).smulRight (unitVector 0)

theorem slice_memLp {X : ℝ → Space → Space}
    (hm : MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure) :
    ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) 1)), MemLp (X σ) 2 volume := by
  have hi := (memLp_two_iff_integrable_sq_norm hm.1).1 hm
  filter_upwards [hm.1.prodMk_left, hi.prod_right_ae] with σ h1 h2
  exact (memLp_two_iff_integrable_sq_norm h1).2 h2

theorem gradient_memLp {c : Space → ℝ} (hc : ContDiff ℝ ∞ c) (hcs : HasCompactSupport c) :
    MemLp (gradientAt c) 2 volume := by
  have hcont : Continuous (gradientAt c) := by
    unfold gradientAt
    exact continuous_finsetSum _ fun i _ =>
      ((hc.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const
  have hsupp : HasCompactSupport (gradientAt c) := by
    refine (hcs.fderiv (𝕜 := ℝ)).mono fun y hy => ?_
    intro h0
    apply hy
    unfold gradientAt
    simp [h0]
  exact hcont.memLp_of_hasCompactSupport hsupp

theorem select_pairing {F : Space → Space}
    (hL : ∀ φ : Space → Space, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ y, inner ℝ (F y) (Freq.negSsp φ y) = 0)
    (k : Fin 3) {ψ : Space → Space} (hψ : IsTestField ψ) :
    ∫ y, inner ℝ (selectCLM k (F y)) (Freq.negSsp ψ y) = 0 := by
  set L : Space →L[ℝ] Space :=
    (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).smulRight (unitVector k) with hLdef
  have hφ : ContDiff ℝ ∞ (fun x => L (ψ x)) := L.contDiff.comp hψ.1
  have hcs : HasCompactSupport (fun x => L (ψ x)) := hψ.2.1.comp_left (map_zero L)
  have hssp : Freq.negSsp (fun x => L (ψ x)) = fun x => L (Freq.negSsp ψ x) := by
    rw [Freq.Internal.NiceApprox.negSsp_eq _ hφ, Freq.Internal.NiceApprox.negSsp_eq _ hψ.1]
    funext x
    have e : ∀ i : Fin 3, Freq.Internal.NiceApprox.pd (unitVector i)
        (Freq.Internal.NiceApprox.pd (unitVector i) (fun x => L (ψ x))) =
        fun x => L (Freq.Internal.NiceApprox.pd (unitVector i)
          (Freq.Internal.NiceApprox.pd (unitVector i) ψ) x) := by
      intro i
      rw [Freq.Internal.NiceApprox.pd_clm L (hψ.1.differentiable (by simp)),
        Freq.Internal.NiceApprox.pd_clm L (Freq.Internal.NiceApprox.differentiable_pd hψ.1 _)]
    simp only [e, map_neg, map_sum]
  have h := hL _ hφ hcs
  rw [hssp] at h
  rw [← h]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [selectCLM, hLdef, ContinuousLinearMap.smulRight_apply, real_inner_smul_left,
    real_inner_smul_right, unitVector, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right]
  simp
  ring

theorem integrable_inner_of_memLp' {f g : Space → Space} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) : Integrable (fun y => inner ℝ (f y) (g y)) volume := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
  rw [h1, h2]

open Freq.Internal.NiceApprox in
theorem pd_curlField {A : Space → Space} (hA : ContDiff ℝ ∞ A) (m : Fin 3) (y : Space) :
    pd (unitVector m) (curlField A) y =
      ∑ j : Fin 3, crossL (unitVector j) (pd (unitVector m) (pd (unitVector j) A) y) := by
  have e1 : pd (unitVector m) (curlField A) = fun x => ∑ j : Fin 3,
      pd (unitVector m) (fun x => crossL (unitVector j) (pd (unitVector j) A x)) x :=
    pd_sum _ _ (fun j => ((crossL (unitVector j)).contDiff.comp (contDiff_pd hA _)).differentiable
      (by simp)) _
  rw [e1]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [pd_clm _ (differentiable_pd hA _)]

open Freq.Internal.NiceApprox in
theorem curl_curl_algebra (D : Fin 3 → Fin 3 → Space) (hD : ∀ i j, D i j = D j i) :
    -∑ i : Fin 3, D i i = ∑ m : Fin 3, ∑ j : Fin 3, crossL (unitVector m) (crossL (unitVector j) (D m j))
      - ∑ i : Fin 3, (∑ j : Fin 3, D i j j) • unitVector i := by
  simp only [Fin.sum_univ_three]
  rw [hD 1 0, hD 2 0, hD 2 1]
  ext c
  fin_cases c <;> simp [crossL_apply, unitVector] <;> ring

open Freq.Internal.NiceApprox in
theorem gradient_divergence {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (y : Space) :
    gradientAt (divergenceAt φ) y =
      ∑ i : Fin 3, (∑ j : Fin 3, pd (unitVector i) (pd (unitVector j) φ) y j) • unitVector i := by
  unfold gradientAt
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have e : divergenceAt φ = fun x => ∑ j : Fin 3, pd (unitVector j) φ x j :=
    funext fun x => divergence_eq_sum φ x
  show pd (unitVector i) (divergenceAt φ) y = _
  rw [e, pd_sum _ _ (fun j => (contDiff_coord (contDiff_pd hφ _) j).differentiable (by simp))]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (pd_apply_coord (differentiable_pd hφ (unitVector j)) (unitVector i) y j).symm

open Freq.Internal.NiceApprox in
theorem negSsp_curl_curl {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (y : Space) :
    Freq.negSsp φ y = curlField (curlField φ) y - gradientAt (divergenceAt φ) y := by
  have hc : curlField (curlField φ) y = ∑ m : Fin 3, ∑ j : Fin 3,
      crossL (unitVector m) (crossL (unitVector j) (pd (unitVector m) (pd (unitVector j) φ) y)) := by
    show ∑ m : Fin 3, crossL (unitVector m) (pd (unitVector m) (curlField φ) y) = _
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [pd_curlField hφ, map_sum]
  rw [negSsp_eq φ hφ, gradient_divergence hφ, hc]
  exact curl_curl_algebra (fun i j => pd (unitVector i) (pd (unitVector j) φ) y)
    (fun i j => congrFun (pd_comm hφ _ _) y)

open Freq.Internal.NiceApprox in
theorem negSsp_pairing {F : Space → Space} (hF : MemLp F 2 volume)
    (h1 : ∀ c : Space → ℝ, ContDiff ℝ ∞ c → HasCompactSupport c →
      ∫ y, inner ℝ (F y) (gradientAt c y) = 0)
    (h2 : ∀ w, IsTestField w → ∫ y, inner ℝ (F y) (w y) = 0)
    {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∫ y, inner ℝ (F y) (Freq.negSsp φ y) = 0 := by
  have hcc : IsTestField (curlField (curlField φ)) :=
    ⟨contDiff_curlField (contDiff_curlField hφ),
      hasCompactSupport_curlField (hasCompactSupport_curlField hc),
      divergence_curlField (contDiff_curlField hφ)⟩
  have e0 : divergenceAt φ = fun x => ∑ j : Fin 3, pd (unitVector j) φ x j :=
    funext fun x => divergence_eq_sum φ x
  have hdc : ContDiff ℝ ∞ (divergenceAt φ) := by
    rw [e0]
    exact ContDiff.sum fun j _ => contDiff_coord (contDiff_pd hφ _) j
  have hds : HasCompactSupport (divergenceAt φ) := by
    refine (hc.fderiv (𝕜 := ℝ)).mono fun y hy => ?_
    intro h0
    apply hy
    unfold divergenceAt
    simp [h0]
  have e : (fun y => inner ℝ (F y) (Freq.negSsp φ y)) = fun y =>
      inner ℝ (F y) (curlField (curlField φ) y) - inner ℝ (F y) (gradientAt (divergenceAt φ) y) := by
    funext y
    rw [negSsp_curl_curl hφ y, inner_sub_right]
  rw [e, integral_sub (integrable_inner_of_memLp' hF
      (Freq.Internal.BilinTestFormula.test_memLp hcc 2))
    (integrable_inner_of_memLp' hF (gradient_memLp hdc hds)),
    h2 _ hcc, h1 _ hdc hds, sub_zero]

def selectC (k : Fin 3) : Freq.CSpace →L[ℂ] Freq.CSpace :=
  (EuclideanSpace.proj k : Freq.CSpace →L[ℂ] ℂ).smulRight (EuclideanSpace.single (0 : Fin 3) (1 : ℂ))

theorem complexifyVec_select (k : Fin 3) (v : Space) :
    Freq.complexifyVec (selectCLM k v) = selectC k (Freq.complexifyVec v) := by
  ext i
  fin_cases i <;> simp [selectCLM, selectC, Freq.complexifyVec, unitVector]

theorem complexify_toLp_select (k : Fin 3) {F : Space → Space} (hF : MemLp F 2 volume) :
    Freq.complexify (Freq.toLpOrZero 2 (fun y => selectCLM k (F y))) =
      ContinuousLinearMap.compLpL 2 volume ((selectC k).restrictScalars ℝ)
        (Freq.complexify (Freq.toLpOrZero 2 F)) := by
  have hs : MemLp (fun y => selectCLM k (F y)) 2 volume := (selectCLM k).comp_memLp' hF
  apply Lp.ext
  have e1 := ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) Freq.complexifyVec
    (Freq.toLpOrZero 2 (fun y => selectCLM k (F y)))
  have e2 := ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume)
    ((selectC k).restrictScalars ℝ) (Freq.complexify (Freq.toLpOrZero 2 F))
  have e3 := ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) Freq.complexifyVec
    (Freq.toLpOrZero 2 F)
  simp only [Freq.complexify] at e1 e2 e3 ⊢
  filter_upwards [e1, e2, e3, Freq.Internal.H1Consistency.toLpOrZero_ae hs,
    Freq.Internal.H1Consistency.toLpOrZero_ae hF] with y h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, h5]
  simpa using complexifyVec_select k (F y)

theorem transform_comp_clm (L : Freq.CSpace →L[ℂ] Freq.CSpace) {f : Space → Freq.CSpace}
    (hf : Integrable f volume) (w : Space) :
    FourierTransform.fourier (fun v => L (f v)) w = L (FourierTransform.fourier f w) := by
  have hint : Integrable (fun v : Space => Real.fourierChar (-inner ℝ v w) • f v) volume :=
    (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (L := innerₗ Space) continuous_inner w).2 hf
  rw [Real.fourier_eq, Real.fourier_eq, ← L.integral_comp_comm hint]
  congr 1
  funext v
  rw [Circle.smul_def, Circle.smul_def, map_smul]

theorem freqTrR_compLpL (L : Freq.CSpace →L[ℂ] Freq.CSpace) (g : Freq.L2C) :
    Freq.freqTrR (ContinuousLinearMap.compLpL 2 volume (L.restrictScalars ℝ) g) =
      ContinuousLinearMap.compLpL 2 volume (L.restrictScalars ℝ) (Freq.freqTrR g) := by
  have hd := SchwartzMap.denseRange_toLpCLM (E := Space) (F := Freq.CSpace) (p := 2)
    (μ := volume) ENNReal.ofNat_ne_top
  refine hd.induction_on g (isClosed_eq
    (Freq.freqTrR.continuous.comp (ContinuousLinearMap.continuous _))
    ((ContinuousLinearMap.continuous _).comp Freq.freqTrR.continuous)) fun f => ?_
  have h1 : MemLp (f : Space → Freq.CSpace) 1 volume := f.memLp 1 volume
  have h2 : MemLp (f : Space → Freq.CSpace) 2 volume := f.memLp 2 volume
  have h1' : MemLp (fun v => L (f v)) 1 volume := (L.restrictScalars ℝ).comp_memLp' h1
  have h2' : MemLp (fun v => L (f v)) 2 volume := (L.restrictScalars ℝ).comp_memLp' h2
  have eT : SchwartzMap.toLpCLM ℝ Freq.CSpace 2 volume f = Freq.toLpOrZero 2 f := by
    apply Lp.ext
    filter_upwards [SchwartzMap.coeFn_toLp f 2 volume,
      Freq.Internal.BilinTestFormula.toLpOrZero_ae h2] with v a b
    rw [SchwartzMap.toLpCLM_apply, a, b]
  have eC : ContinuousLinearMap.compLpL 2 volume (L.restrictScalars ℝ) (Freq.toLpOrZero 2 f) =
      Freq.toLpOrZero 2 (fun v => L (f v)) := by
    apply Lp.ext
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) (L.restrictScalars ℝ)
      (Freq.toLpOrZero 2 f), Freq.Internal.BilinTestFormula.toLpOrZero_ae h2,
      Freq.Internal.BilinTestFormula.toLpOrZero_ae h2'] with v a b c
    rw [a, b, c]
    rfl
  rw [eT, eC]
  apply Lp.ext
  have hF1 := Freq.freqTrL1L2.1 _ h1' h2'
  have hF2 := Freq.freqTrL1L2.1 _ h1 h2
  filter_upwards [hF1, hF2, ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume)
    (L.restrictScalars ℝ) (Freq.freqTrR (Freq.toLpOrZero 2 f))] with ξ a b c
  rw [c]
  change (Freq.freqTrL2 (Freq.toLpOrZero 2 (fun v => L (f v))) : Space → Freq.CSpace) ξ =
    L ((Freq.freqTrL2 (Freq.toLpOrZero 2 f) : Space → Freq.CSpace) ξ)
  rw [a, b, transform_comp_clm L (memLp_one_iff_integrable.1 h1)]

theorem ae_ne_zero_coord : ∀ᵐ ξ : Space, ξ 1 ≠ 0 := by
  set s : Submodule ℝ Space := LinearMap.ker (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).toLinearMap
  have hs : s ≠ ⊤ := by
    intro htop
    have hm : EuclideanSpace.single (1 : Fin 3) (1 : ℝ) ∈ s := htop ▸ Submodule.mem_top
    simp [s] at hm
  have h0 := Measure.addHaar_submodule (volume : Measure Space) s hs
  rw [ae_iff]
  refine measure_mono_null (fun ξ hξ => ?_) h0
  simp only [Set.mem_ofPred_eq, not_not] at hξ
  simp [s, hξ]

theorem coord_zero_of_longitudinal {ξ : Space} (hξ : ξ 1 ≠ 0) (z : Freq.CSpace) (k : Fin 3)
    (h : ((selectC k).restrictScalars ℝ) z =
      Freq.longitudinal ξ (((selectC k).restrictScalars ℝ) z)) : z k = 0 := by
  have e0 := congrArg (fun v : Freq.CSpace => v 0) h
  simp [selectC, Cert.Internal.ProjectionSpec.longitudinal_eq, Freq.freqVec, Freq.complexifyVec,
    EuclideanSpace.inner_single_right] at e0
  have hr : (‖ξ‖ ^ 2 : ℝ) = ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
      Fin.sum_univ_three]
    simp [Real.norm_eq_abs, sq_abs]
  have h1 : 0 < ξ 1 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hξ))
  have hpos : 0 < ‖ξ‖ ^ 2 - ξ 0 ^ 2 := by rw [hr]; nlinarith [sq_nonneg (ξ 2)]
  have hn : (‖ξ‖ ^ 2 : ℝ) ≠ 0 := by rw [hr]; nlinarith [sq_nonneg (ξ 2), sq_nonneg (ξ 0)]
  have hne : ((‖ξ‖ ^ 2 - ξ 0 ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hn' : ((‖ξ‖ : ℝ) : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hn
  have hn0 : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := fun h0 => hn' (by rw [h0]; ring)
  have e1 : z k * ((‖ξ‖ : ℂ) ^ 2) = z k * ((ξ 0 : ℂ) ^ 2) := by
    conv_lhs => rw [e0]
    field_simp
  have key : z k * ((‖ξ‖ ^ 2 - ξ 0 ^ 2 : ℝ) : ℂ) = 0 := by
    push_cast
    linear_combination e1
  exact (mul_eq_zero.1 key).resolve_right hne

theorem ae_zero_of_select {F : Space → Space} (hF : MemLp F 2 volume)
    (h : ∀ k, Cert.solField (fun y => selectCLM k (F y)) = 0) : ∀ᵐ y, F y = 0 := by
  set G : Freq.L2C := Freq.freqTrR (Freq.complexify (Freq.toLpOrZero 2 F)) with hGdef
  have hk : ∀ k : Fin 3, ∀ᵐ ξ, ξ 1 ≠ 0 → G ξ k = 0 := by
    intro k
    set S : Freq.CSpace →L[ℝ] Freq.CSpace := (selectC k).restrictScalars ℝ with hS
    have hc : Freq.freqTrR (Freq.complexify (Freq.toLpOrZero 2 (fun y => selectCLM k (F y)))) =
        Freq.fieldOp id Freq.longitudinal
          (Freq.freqTrR (Freq.complexify (Freq.toLpOrZero 2 (fun y => selectCLM k (F y))))) := by
      have h0 := congrArg (fun x : Freq.X => (x : Freq.L2C)) (h k)
      simp only [Cert.solField, Cert.solProj_coe, ZeroMemClass.coe_zero] at h0
      exact sub_eq_zero.1 h0
    rw [complexify_toLp_select k hF, freqTrR_compLpL, ← hGdef] at hc
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) S G,
      Cert.Internal.ProjectionSpec.fieldOp_longitudinal_ae
        (ContinuousLinearMap.compLpL 2 volume S G)] with ξ e1 e2 hξ
    have key : S (G ξ) = Freq.longitudinal ξ (S (G ξ)) := by
      calc S (G ξ) = (ContinuousLinearMap.compLpL 2 volume S G) ξ := e1.symm
        _ = (Freq.fieldOp id Freq.longitudinal (ContinuousLinearMap.compLpL 2 volume S G)) ξ := by
          rw [← hc]
        _ = Freq.longitudinal ξ ((ContinuousLinearMap.compLpL 2 volume S G) ξ) := e2
        _ = Freq.longitudinal ξ (S (G ξ)) := by rw [e1]
    exact coord_zero_of_longitudinal hξ (G ξ) k key
  have hG0 : G = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [ae_ne_zero_coord, hk 0, hk 1, hk 2] with ξ hξ a b c
    ext i
    fin_cases i <;> simp [a hξ, b hξ, c hξ]
  have hc0 : Freq.complexify (Freq.toLpOrZero 2 F) = 0 := by
    rw [← norm_eq_zero, ← Cert.Internal.ProjectionSpec.norm_freqTrR, ← hGdef, hG0, norm_zero]
  have ht0 : Freq.toLpOrZero 2 F = 0 := by
    rw [← norm_eq_zero, ← Cert.Internal.SliceFieldsIsometry.norm_complexify, hc0, norm_zero]
  filter_upwards [Freq.Internal.H1Consistency.toLpOrZero_ae hF,
    Lp.coeFn_zero Space 2 (volume : Measure Space)] with y a b
  rw [← a, ht0]
  exact b

theorem slice_zero {F : Space → Space} (hF : MemLp F 2 volume)
    (h1 : ∀ c : Space → ℝ, ContDiff ℝ ∞ c → HasCompactSupport c →
      ∫ y, inner ℝ (F y) (gradientAt c y) = 0)
    (h2 : ∀ w, IsTestField w → ∫ y, inner ℝ (F y) (w y) = 0) : ∀ᵐ y, F y = 0 := by
  have hL := fun φ hφ hc => negSsp_pairing hF h1 h2 (φ := φ) hφ hc
  refine ae_zero_of_select hF fun k => eq_zero_of_negSsp_inner _ fun ψ hψ => ?_
  have hn := Freq.Internal.NiceApprox.negSsp_isTestField hψ
  rw [real_inner_comm, Cert.inner_solField_test _ hn.1 hn.2.1 hn.2.2 (fun y => selectCLM k (F y))
    ((selectCLM k).comp_memLp' hF)]
  exact select_pairing hL k hψ

end Internal.TestDensityProof

open Internal.TestDensityProof in
theorem gradSolenoidalDensityHolds_proof : GradSolenoidalDensityHolds := by
  intro X hX hper h2 hq hψ
  have hm := memLp_of hX h2
  refine ae_of_period hper ?_
  refine ae_period_of_slices (aestronglyMeasurable_period hX) ?_
  have hmem := slice_memLp hm
  have hfield : ∀ w, IsTestField w → ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ∫ y, inner ℝ (X σ y) (w y) = 0 := by
    intro w hw
    refine ae_zero_of_periodic_tests
      (integrableOn_slicePairing hm (Freq.Internal.BilinTestFormula.test_memLp hw 2)) ?_
    intro a ha has _
    refine Eq.trans ?_ (hψ _ (isPeriodicTestField_prod ha has hw))
    refine setIntegral_congr_fun measurableSet_Icc (fun σ _ => ?_)
    simp only [real_inner_smul_right]
    rw [integral_const_mul]
  have hpot : ∀ c : Space → ℝ, ContDiff ℝ ∞ c → HasCompactSupport c →
      ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) 1)), ∫ y, inner ℝ (X σ y) (gradientAt c y) = 0 := by
    intro c hc hcs
    refine ae_zero_of_periodic_tests (integrableOn_slicePairing hm (gradient_memLp hc hcs)) ?_
    intro a ha has _
    refine Eq.trans ?_ (hq _ (isPeriodicTestPotential_prod ha has hc hcs))
    refine setIntegral_congr_fun measurableSet_Icc (fun σ _ => ?_)
    simp only [gradientAt_const_mul _ (hc.differentiable (by simp)), real_inner_smul_right]
    rw [integral_const_mul]
  have hA := ae_forall_inner_zero (μ := volume.restrict (Icc (0 : ℝ) 1))
    (fun σ => Freq.toLpOrZero 2 (X σ))
    {v | ∃ w, IsTestField w ∧ Freq.toLpOrZero 2 w = v} (by
      rintro v ⟨w, hw, rfl⟩
      filter_upwards [hmem, hfield w hw] with σ h1 h3
      rw [inner_toLp_eq h1 (Freq.Internal.BilinTestFormula.test_memLp hw 2), h3])
  have hB := ae_forall_inner_zero (μ := volume.restrict (Icc (0 : ℝ) 1))
    (fun σ => Freq.toLpOrZero 2 (X σ))
    {v | ∃ c : Space → ℝ, ContDiff ℝ ∞ c ∧ HasCompactSupport c ∧
      Freq.toLpOrZero 2 (gradientAt c) = v} (by
      rintro v ⟨c, hc, hcs, rfl⟩
      filter_upwards [hmem, hpot c hc hcs] with σ h1 h3
      rw [inner_toLp_eq h1 (gradient_memLp hc hcs), h3])
  filter_upwards [hmem, hA, hB] with σ h1 h3 h4
  refine slice_zero h1 (fun c hc hcs => ?_) (fun w hw => ?_)
  · rw [← inner_toLp_eq h1 (gradient_memLp hc hcs)]
    exact h4 _ ⟨c, hc, hcs, rfl⟩
  · rw [← inner_toLp_eq h1 (Freq.Internal.BilinTestFormula.test_memLp hw 2)]
    exact h3 _ ⟨w, hw, rfl⟩

end Breakdown.Coercive
