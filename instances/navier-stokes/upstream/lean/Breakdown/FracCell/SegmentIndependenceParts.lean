import Breakdown.FracCell.SegmentPairDefs
import Breakdown.FracCell.SegmentModesGradient
import Breakdown.FracCell.SegmentModesHeight
import Breakdown.FracCell.CornerIndependenceParts

open scoped ContDiff
open MeasureTheory Filter Set
open scoped Topology

noncomputable section
namespace Breakdown.FracInternal.SegmentParts

open Breakdown.FracInternal.CornerParts Breakdown.CellCert.CellFormula

theorem prod_int {Φ : ℝ × ℝ → ℂ} {A B : Set ℝ} (h : IntegrableOn Φ (A ×ˢ B)) :
    Integrable Φ ((volume.restrict A).prod (volume.restrict B)) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact h

theorem nz_set {K : Set ℝ} (hK : IsCompact K) (hKU : ∀ r ∈ K, r ≠ 0) :
    ∃ δ > 0, ∃ R : ℝ, ∀ r ∈ K, δ ≤ |r| ∧ |r| ≤ R := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  by_cases h : K.Nonempty
  · obtain ⟨r0, hr0, hmin⟩ := hK.exists_isMinOn h continuous_abs.continuousOn
    refine ⟨|r0|, abs_pos.2 (hKU r0 hr0), R, fun r hr => ⟨hmin hr, ?_⟩⟩
    have := hR hr
    rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  · exact ⟨1, one_pos, 0, fun r hr => absurd ⟨r, hr⟩ h⟩

theorem fst_slice {Φ : ℝ × ℝ → ℂ} {s U : Set ℝ} (hs : MeasurableSet s) (hU : IsOpen U)
    (hnull : volume Uᶜ = 0) (hΦs : ∀ p : ℝ × ℝ, p.2 ∉ s → Φ p = 0)
    (hint : ∀ K, K ⊆ U → IsCompact K → IntegrableOn Φ (K ×ˢ s))
    (hχ : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ U →
      ∫ p, (χ p.1 : ℂ) * Φ p = 0)
    (w : ℝ → ℂ) {A : Set ℝ} :
    ∫ p in A ×ˢ s, w p.1 * Φ p = 0 := by
  set g : ℝ → ℂ := fun x => ∫ y in s, Φ (x, y) with hg
  have hloc : LocallyIntegrableOn g U volume := by
    refine (locallyIntegrableOn_iff hU.isLocallyClosed).2 fun K hKU hK => ?_
    exact (prod_int (hint K hKU hK)).integral_prod_left
  have hz : ∀ᵐ x, x ∈ U → g x = 0 := by
    refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun χ hχs hχc hχU => ?_
    obtain ⟨C, hC⟩ := hχc.exists_bound_of_continuous hχs.continuous
    have hK := hint _ hχU hχc.isCompact
    have hI : Integrable (fun p : ℝ × ℝ => (χ p.1 : ℂ) * Φ p) := by
      have h1 := ((integrable_indicator_iff ((isClosed_tsupport χ).measurableSet.prod hs)).2 hK).bdd_mul
        (c := C) (f := fun p : ℝ × ℝ => (χ p.1 : ℂ))
        (Complex.continuous_ofReal.comp (hχs.continuous.comp continuous_fst)).aestronglyMeasurable
        (Eventually.of_forall fun p => by rw [Complex.norm_real]; exact hC _)
      refine h1.congr (Eventually.of_forall fun p => ?_)
      by_cases hp : p ∈ tsupport χ ×ˢ s
      · simp only [Set.indicator_of_mem hp]
      · rcases not_and_or.1 (show ¬ (p.1 ∈ tsupport χ ∧ p.2 ∈ s) from hp) with h | h
        · simp [image_eq_zero_of_notMem_tsupport h]
        · simp [hΦs p h]
    have hI' : Integrable (fun p : ℝ × ℝ => (χ p.1 : ℂ) * Φ p) (volume.prod (volume.restrict s)) := by
      have := hI.restrict (s := univ ×ˢ s)
      rwa [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at this
    calc ∫ x, χ x • g x = ∫ x, ∫ y in s, (χ x : ℂ) * Φ (x, y) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [hg, Complex.real_smul]
          exact (integral_const_mul _ _).symm
      _ = ∫ p in univ ×ˢ s, (χ p.1 : ℂ) * Φ p := by
          rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ, integral_prod _ hI']
      _ = ∫ p, (χ p.1 : ℂ) * Φ p := by
          refine setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_
          have : p.2 ∉ s := fun h => hp ⟨trivial, h⟩
          simp [hΦs p this]
      _ = 0 := hχ χ hχs hχc hχU
  have hU' : ∀ᵐ x, x ∈ U := by rw [ae_iff]; exact hnull
  have hz' : ∀ᵐ x, g x = 0 := by
    filter_upwards [hz, hU'] with x h1 h2 using h1 h2
  by_cases hI : IntegrableOn (fun p : ℝ × ℝ => w p.1 * Φ p) (A ×ˢ s)
  swap
  · exact integral_undef hI
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ (prod_int hI)]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_restrict_of_ae hz'] with x hx
  show ∫ y in s, w x * Φ (x, y) = 0
  rw [integral_const_mul]
  simp only [hg] at hx
  rw [hx, mul_zero]

theorem snd_slice {Φ : ℝ × ℝ → ℂ} {s : Set ℝ} (hs : MeasurableSet s)
    (hΦs : ∀ p : ℝ × ℝ, p.1 ∉ s → Φ p = 0)
    (hint : ∀ K, IsCompact K → IntegrableOn Φ (s ×ˢ K))
    (hχ : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → ∫ p, (χ p.2 : ℂ) * Φ p = 0)
    (w : ℝ → ℂ) {A : Set ℝ} :
    ∫ p in s ×ˢ A, w p.2 * Φ p = 0 := by
  set g : ℝ → ℂ := fun y => ∫ x in s, Φ (x, y) with hg
  have hloc : LocallyIntegrable g volume := by
    refine locallyIntegrable_iff.2 fun K hK => ?_
    exact (prod_int (hint K hK)).integral_prod_right
  have hz : ∀ᵐ y, g y = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun χ hχs hχc => ?_
    obtain ⟨C, hC⟩ := hχc.exists_bound_of_continuous hχs.continuous
    have hK := hint _ hχc.isCompact
    have hI : Integrable (fun p : ℝ × ℝ => (χ p.2 : ℂ) * Φ p) := by
      have h1 := ((integrable_indicator_iff (hs.prod (isClosed_tsupport χ).measurableSet)).2 hK).bdd_mul
        (c := C) (f := fun p : ℝ × ℝ => (χ p.2 : ℂ))
        (Complex.continuous_ofReal.comp (hχs.continuous.comp continuous_snd)).aestronglyMeasurable
        (Eventually.of_forall fun p => by rw [Complex.norm_real]; exact hC _)
      refine h1.congr (Eventually.of_forall fun p => ?_)
      by_cases hp : p ∈ s ×ˢ tsupport χ
      · simp only [Set.indicator_of_mem hp]
      · rcases not_and_or.1 (show ¬ (p.1 ∈ s ∧ p.2 ∈ tsupport χ) from hp) with h | h
        · simp [hΦs p h]
        · simp [image_eq_zero_of_notMem_tsupport h]
    have hI' : Integrable (fun p : ℝ × ℝ => (χ p.2 : ℂ) * Φ p) ((volume.restrict s).prod volume) := by
      have := hI.restrict (s := s ×ˢ univ)
      rwa [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at this
    calc ∫ y, χ y • g y = ∫ y, ∫ x in s, (χ y : ℂ) * Φ (x, y) := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp only [hg, Complex.real_smul]
          exact (integral_const_mul _ _).symm
      _ = ∫ p in s ×ˢ univ, (χ p.2 : ℂ) * Φ p := by
          rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ, integral_prod_symm _ hI']
      _ = ∫ p, (χ p.2 : ℂ) * Φ p := by
          refine setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_
          have : p.1 ∉ s := fun h => hp ⟨h, trivial⟩
          simp [hΦs p this]
      _ = 0 := hχ χ hχs hχc
  by_cases hI : IntegrableOn (fun p : ℝ × ℝ => w p.2 * Φ p) (s ×ˢ A)
  swap
  · exact integral_undef hI
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ (prod_int hI)]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_restrict_of_ae hz] with y hy
  show ∫ x in s, w y * Φ (x, y) = 0
  rw [integral_const_mul]
  simp only [hg] at hy
  rw [hy, mul_zero]

end Breakdown.FracInternal.SegmentParts

namespace Breakdown.FracInternal.SegmentParts

open Breakdown.FracInternal.CornerParts Breakdown.CellCert.CellFormula

theorem height_core_nz {F G : ℝ × ℝ → ℂ}
    (hF : ∀ δ R Z : ℝ, 0 < δ → IntegrableOn F {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z})
    (hG : ∀ δ R Z : ℝ, 0 < δ → IntegrableOn G {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z})
    (hw : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, p.1 ≠ 0) →
      ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * F p = -∫ p, (ψ p : ℂ) * G p)
    {a c b : ℝ} (hac : a < c) (hcb : c < b) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχp : ∀ r ∈ tsupport χ, r ≠ 0) :
    ∫ p, ((χ p.1 * tentSlope a c b p.2 : ℝ) : ℂ) * F p = -∫ p, ((χ p.1 * tentFn a c b p.2 : ℝ) : ℂ) * G p := by
  obtain ⟨δ, hδ, R, hR⟩ := nz_set hχc.isCompact hχp
  obtain ⟨K, hK⟩ := tent_slope a c b
  obtain ⟨Cχ, hCχ⟩ := hχc.exists_bound_of_continuous hχ.continuous
  set Z := |a| + |b| + 1 with hZd
  set S : Set (ℝ × ℝ) := {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} with hSd
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_const (continuous_abs.measurable.comp measurable_fst)).inter
      ((measurableSet_le (continuous_abs.measurable.comp measurable_fst) measurable_const).inter
        (measurableSet_le (continuous_abs.measurable.comp measurable_snd) measurable_const))
  have hCχ0 : 0 ≤ Cχ := (norm_nonneg _).trans (hCχ 0)
  have hχz : ∀ r, ¬ (δ ≤ |r| ∧ |r| ≤ R) → χ r = 0 := fun r hr =>
    image_eq_zero_of_notMem_tsupport fun hm => hr (hR r hm)
  have hcase : ∀ p : ℝ × ℝ, p ∉ S → χ p.1 = 0 ∨ p.2 ∉ Icc (-Z) Z := by
    intro p hp
    by_cases h1 : δ ≤ |p.1| ∧ |p.1| ≤ R
    · right
      intro hm
      exact hp ⟨h1.1, h1.2, abs_le.2 hm⟩
    · left
      exact hχz _ h1
  have hZ1 : ∀ n : ℕ, ∀ z, z ∉ Icc (-Z) Z → z ∉ Icc (a - 1 / ((n : ℝ) + 1)) (b + 1 / ((n : ℝ) + 1)) := by
    intro n z hz hm
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    exact hz ⟨by linarith [hm.1, neg_abs_le a, abs_nonneg b], by linarith [hm.2, le_abs_self b, abs_nonneg a]⟩
  refine limit_core hS (hF _ _ _ hδ) (hG _ _ _ hδ)
    (fun n p => χ p.1 * deriv (mollTent a c b n) p.2) (fun n p => χ p.1 * mollTent a c b n p.2)
    (fun p => χ p.1 * tentSlope a c b p.2) (fun p => χ p.1 * tentFn a c b p.2)
    (Cχ * max (K : ℝ) (K * (b - a + 2))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro n
    exact (hχ.continuous.comp continuous_fst).mul
      (((moll_smooth a c b n).continuous_deriv (by simp)).comp continuous_snd)
  · intro n
    exact (hχ.continuous.comp continuous_fst).mul ((moll_smooth a c b n).continuous.comp continuous_snd)
  · refine Eventually.of_forall fun n p hp => ?_
    rcases hcase p hp with h | h
    · simp [h]
    · have hv := moll_vanish a c b hac hcb n p.2 (hZ1 n _ h)
      simp [hv.1, hv.2]
  · intro p hp
    rcases hcase p hp with h | h
    · simp [h]
    · have h1 : p.2 ∉ Icc a b := fun hm =>
        h ⟨by linarith [hm.1, neg_abs_le a, abs_nonneg b], by linarith [hm.2, le_abs_self b, abs_nonneg a]⟩
      have ho := tent_out hac hcb h1
      simp [ho.1, ho.2]
  · intro n p
    have hb := moll_bound hac hcb hK n p.2
    have hc := hCχ p.1
    rw [Real.norm_eq_abs] at hc
    constructor
    · rw [abs_mul]
      exact mul_le_mul hc (hb.2.trans (le_max_left _ _)) (abs_nonneg _) hCχ0
    · rw [abs_mul]
      exact mul_le_mul hc (hb.1.trans (le_max_right _ _)) (abs_nonneg _) hCχ0
  · filter_upwards [ae_snd_ne a, ae_snd_ne c, ae_snd_ne b] with p h1 h2 h3
    exact (moll_deriv_tendsto hac hcb h1 h2 h3).const_mul _
  · intro p
    exact (moll_tendsto a c b p.2).const_mul _
  · refine Eventually.of_forall fun n => ?_
    have hsm : ContDiff ℝ ∞ (fun q : ℝ × ℝ => χ q.1 * mollTent a c b n q.2) :=
      (hχ.comp contDiff_fst).mul ((moll_smooth a c b n).comp contDiff_snd)
    have hcs : HasCompactSupport (fun q : ℝ × ℝ => χ q.1 * mollTent a c b n q.2) := by
      refine HasCompactSupport.intro (hχc.isCompact.prod (moll_hasCompactSupport hac hcb n).isCompact) ?_
      intro q hq
      rcases not_and_or.1 (show ¬ (q.1 ∈ tsupport χ ∧ q.2 ∈ tsupport (mollTent a c b n)) from hq) with h | h
      · simp [image_eq_zero_of_notMem_tsupport h]
      · simp [image_eq_zero_of_notMem_tsupport h]
    have hpos : ∀ q ∈ tsupport (fun q : ℝ × ℝ => χ q.1 * mollTent a c b n q.2), q.1 ≠ 0 := by
      intro q hq
      have hsub : tsupport (fun q : ℝ × ℝ => χ q.1 * mollTent a c b n q.2) ⊆ tsupport χ ×ˢ univ := by
        refine closure_minimal ?_ ((isClosed_tsupport χ).prod isClosed_univ)
        intro r hr
        refine ⟨subset_tsupport _ ?_, trivial⟩
        intro h0
        exact hr (by simp [h0])
      exact hχp _ (hsub hq).1
    have hfd := fun q => fderiv_prod_apply (hχ.differentiable (by simp))
      ((moll_smooth a c b n).differentiable (by simp)) q
    have := hw _ hsm hcs hpos
    simp only [(hfd _).2] at this
    exact this

def rphi (l m u : ℝ) (F dF : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  ((tentSlope l m u p.1 : ℝ) : ℂ) * F p + ((tentFn l m u p.1 : ℝ) : ℂ) * dF p

def hphi (l m u : ℝ) (F dF : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  ((tentSlope l m u p.2 : ℝ) : ℂ) * F p + ((tentFn l m u p.2 : ℝ) : ℂ) * dF p

theorem height_zero {wt : ℝ → ℝ} {F dF : ℝ × ℝ → ℂ} (h : IsHeightWeakPair wt F dF)
    {l m u : ℝ} (hlm : l < m) (hmu : m < u) (w : ℝ → ℂ) (A : Set ℝ) :
    ∫ p in A ×ˢ Icc l u, w p.1 * hphi l m u F dF p = 0 := by
  refine fst_slice (U := ({0} : Set ℝ)ᶜ) measurableSet_Icc isOpen_compl_singleton (by simp) ?_ ?_ ?_ w
  · intro p hp
    have := tent_out hlm hmu hp
    simp [hphi, this.1, this.2]
  · intro K hKU hK
    obtain ⟨δ, hδ, R, hR⟩ := nz_set hK (fun r hr => by simpa using hKU hr)
    set Z := |l| + |u|
    have hsub : K ×ˢ Icc l u ⊆ {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} := by
      intro p hp
      refine ⟨(hR _ hp.1).1, (hR _ hp.1).2, abs_le.2 ⟨?_, ?_⟩⟩
      · linarith [hp.2.1, neg_abs_le l, abs_nonneg u]
      · linarith [hp.2.2, le_abs_self u, abs_nonneg l]
    have hF := ((h.2.1 δ R Z hδ).1).mono_set hsub
    have hdF := ((h.2.1 δ R Z hδ).2).mono_set hsub
    obtain ⟨Bt, hBt⟩ := tentFn_bound hlm hmu
    refine (hF.bdd_mul (c := |1 / (m - l)| + |1 / (m - u)|)
      (Complex.measurable_ofReal.comp ((tentSlope_meas l m u).comp measurable_snd)).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)).add (hdF.bdd_mul (c := Bt)
      (Complex.continuous_ofReal.comp ((tent_cont l m u).comp continuous_snd)).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_))
    · show ‖((tentSlope l m u _ : ℝ) : ℂ)‖ ≤ _
      rw [Complex.norm_real, Real.norm_eq_abs]; exact tentSlope_bound _ _ _ _
    · show ‖((tentFn l m u _ : ℝ) : ℂ)‖ ≤ _
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hBt _
  · intro χ hχs hχc hχU
    have hχp : ∀ r ∈ tsupport χ, r ≠ 0 := fun r hr => by simpa using hχU hr
    obtain ⟨δ, hδ, R, hR⟩ := nz_set hχc.isCompact hχp
    set Z := |l| + |u|
    set s1 : Set ℝ := {r : ℝ | δ ≤ |r| ∧ |r| ≤ R}
    have hs1 : MeasurableSet s1 :=
      (measurableSet_le measurable_const continuous_abs.measurable).inter
        (measurableSet_le continuous_abs.measurable measurable_const)
    have hset : s1 ×ˢ Icc (-Z) Z = {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} := by
      ext p
      simp only [s1, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
      tauto
    have hab : ∀ z, z ∉ Icc (-Z) Z → z ∉ Icc l u := fun z hz hm =>
      hz ⟨by linarith [hm.1, neg_abs_le l, abs_nonneg u], by linarith [hm.2, le_abs_self u, abs_nonneg l]⟩
    have z1 : ∀ r, r ∉ s1 → χ r = 0 := fun r hr => image_eq_zero_of_notMem_tsupport fun hm => hr (hR r hm)
    obtain ⟨B1, hB1⟩ := bdd_of_csupp hχs.continuous hχc
    obtain ⟨Bt, hBt⟩ := tentFn_bound hlm hmu
    have zs : ∀ z, z ∉ Icc (-Z) Z → tentSlope l m u z = 0 := fun z hz => (tent_out hlm hmu (hab z hz)).1
    have zt : ∀ z, z ∉ Icc (-Z) Z → tentFn l m u z = 0 := fun z hz => (tent_out hlm hmu (hab z hz)).2
    have hFF := h.2.1 δ R Z hδ
    rw [← hset] at hFF
    have i1 := int_region hs1 measurableSet_Icc hFF.1 hχs.continuous.measurable
      (tentSlope_meas l m u) hB1 (tentSlope_bound l m u) z1 zs
    have i2 := int_region hs1 measurableSet_Icc hFF.2 hχs.continuous.measurable
      (tent_cont l m u).measurable hB1 hBt z1 zt
    have k := height_core_nz (fun δ R Z hδ => (h.2.1 δ R Z hδ).1) (fun δ R Z hδ => (h.2.1 δ R Z hδ).2) h.2.2
      hlm hmu hχs hχc hχp
    have e : (fun p : ℝ × ℝ => (χ p.1 : ℂ) * hphi l m u F dF p) = fun p =>
        ((χ p.1 * tentSlope l m u p.2 : ℝ) : ℂ) * F p + ((χ p.1 * tentFn l m u p.2 : ℝ) : ℂ) * dF p := by
      funext p; simp only [hphi]; push_cast; ring
    rw [e, integral_add i1 i2, k]
    ring

theorem radial_pos {F dF : ℝ × ℝ → ℂ} (h : IsRadialWeakPair F dF)
    {l m u : ℝ} (hl : 0 < l) (hlm : l < m) (hmu : m < u) (w : ℝ → ℂ) (A : Set ℝ) :
    ∫ p in Icc l u ×ˢ A, w p.2 * rphi l m u F dF p = 0 := by
  refine snd_slice measurableSet_Icc ?_ ?_ ?_ w
  · intro p hp
    have := tent_out hlm hmu hp
    simp [rphi, this.1, this.2]
  · intro K hK
    obtain ⟨Z, hZ⟩ := hK.isBounded.subset_closedBall 0
    have hsub1 : Icc l u ×ˢ K ⊆ Icc 0 u ×ˢ Icc (-Z) Z := by
      intro p hp
      have := hZ hp.2
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      exact ⟨⟨hl.le.trans hp.1.1, hp.1.2⟩, (abs_le.1 this).1, (abs_le.1 this).2⟩
    have hsub2 : Icc l u ×ˢ K ⊆ Icc l u ×ˢ Icc (-Z) Z := by
      intro p hp
      have := hZ hp.2
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      exact ⟨hp.1, (abs_le.1 this).1, (abs_le.1 this).2⟩
    have hF := ((h.1 u Z).1).mono_set hsub1
    have hdF := (h.2.1 l u Z hl).mono_set hsub2
    obtain ⟨Bt, hBt⟩ := tentFn_bound hlm hmu
    refine (hF.bdd_mul (c := |1 / (m - l)| + |1 / (m - u)|)
      (Complex.measurable_ofReal.comp ((tentSlope_meas l m u).comp measurable_fst)).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)).add (hdF.bdd_mul (c := Bt)
      (Complex.continuous_ofReal.comp ((tent_cont l m u).comp continuous_fst)).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_))
    · show ‖((tentSlope l m u _ : ℝ) : ℂ)‖ ≤ _
      rw [Complex.norm_real, Real.norm_eq_abs]; exact tentSlope_bound _ _ _ _
    · show ‖((tentFn l m u _ : ℝ) : ℂ)‖ ≤ _
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hBt _
  · intro χ hχs hχc
    obtain ⟨Z, hZ⟩ := sym_bound hχc
    obtain ⟨B1, hB1⟩ := bdd_of_csupp hχs.continuous hχc
    obtain ⟨Bt, hBt⟩ := tentFn_bound hlm hmu
    have hsub1 : Icc l u ×ˢ Icc (-Z) Z ⊆ Icc 0 u ×ˢ Icc (-Z) Z :=
      Set.prod_mono (Icc_subset_Icc_left hl.le) le_rfl
    have zs : ∀ x, x ∉ Icc l u → tentSlope l m u x = 0 := fun x hx => (tent_out hlm hmu hx).1
    have zt : ∀ x, x ∉ Icc l u → tentFn l m u x = 0 := fun x hx => (tent_out hlm hmu hx).2
    have i1 := int_region measurableSet_Icc measurableSet_Icc (((h.1 u Z).1).mono_set hsub1)
      (tentSlope_meas l m u) hχs.continuous.measurable (tentSlope_bound l m u) hB1 zs hZ
    have i2 := int_region measurableSet_Icc measurableSet_Icc (h.2.1 l u Z hl)
      (tent_cont l m u).measurable hχs.continuous.measurable hBt hB1 zt hZ
    have k := radial_core (fun δ R Z hδ => ((h.1 R Z).1).mono_set (Set.prod_mono (Icc_subset_Icc_left hδ.le) le_rfl))
      (fun δ R Z hδ => h.2.1 δ R Z hδ) h.2.2 hl hlm hmu hχs hχc
    have e : (fun p : ℝ × ℝ => (χ p.2 : ℂ) * rphi l m u F dF p) = fun p =>
        ((tentSlope l m u p.1 * χ p.2 : ℝ) : ℂ) * F p + ((tentFn l m u p.1 * χ p.2 : ℝ) : ℂ) * dF p := by
      funext p; simp only [rphi]; push_cast; ring
    rw [e, integral_add i1 i2, k]
    ring

end Breakdown.FracInternal.SegmentParts

namespace Breakdown.FracInternal.SegmentParts

open Breakdown.FracInternal.CornerParts Breakdown.CellCert.CellFormula

theorem slope_le {l m u x : ℝ} (hlm2 : l ≤ m / 2) (hm : 0 < m) :
    |tentSlope l m u x| ≤ 2 / m + |1 / (m - u)| := by
  have h2 : (0 : ℝ) ≤ 2 / m := by positivity
  unfold tentSlope
  split_ifs with h1 h3
  · have hml : 0 < m - l := by linarith
    rw [abs_of_pos (div_pos one_pos hml)]
    have : 1 / (m - l) ≤ 2 / m := by rw [div_le_div_iff₀ hml hm]; linarith
    linarith [abs_nonneg (1 / (m - u))]
  · linarith
  · rw [abs_zero]; positivity

theorem tent_le {l m u x : ℝ} (hx : 0 ≤ x) (hl : 0 ≤ l) (hlm2 : l ≤ m / 2) (hm : 0 < m) :
    |tentFn l m u x| ≤ 2 / m * x := by
  unfold tentFn
  rw [abs_of_nonneg (le_max_left _ _)]
  have hml : 0 < m - l := by linarith
  have h1 : 1 ≤ 2 / m * (m - l) := by rw [div_mul_eq_mul_div, le_div_iff₀ hm]; linarith
  have h2 : (x - l) / (m - l) ≤ 2 / m * x := by
    rw [div_le_iff₀ hml]
    nlinarith [mul_le_mul_of_nonneg_left h1 hx]
  exact max_le (by positivity) ((min_le_left _ _).trans h2)

theorem radial_zero {F dF : ℝ × ℝ → ℂ} (h : IsRadialWeakPair F dF) {lo hi m u : ℝ} {t : ℝ → ℝ}
    (ht : Continuous t) (hm : 0 < m) (hmu : m < u) :
    ∫ p in Icc 0 u ×ˢ Icc lo hi, ((t p.2 : ℝ) : ℂ) * rphi 0 m u F dF p = 0 := by
  set S := Icc (0 : ℝ) u ×ˢ Icc lo hi with hSd
  have hS : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  set w : ℝ → ℂ := fun y => ((t y : ℝ) : ℂ) with hw
  set ln : ℕ → ℝ := fun n => m / ((n : ℝ) + 2) with hln
  have hln0 : ∀ n, 0 < ln n := fun n => by simp only [hln]; positivity
  have hln2 : ∀ n, ln n ≤ m / 2 := fun n => by
    simp only [hln]
    exact div_le_div_of_nonneg_left hm.le (by norm_num) (by linarith [n.cast_nonneg (α := ℝ)])
  have hlnt : Tendsto ln atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hz : ∀ n, ∫ p in S, w p.2 * rphi (ln n) m u F dF p = 0 := by
    intro n
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hS
      (Set.prod_mono (Icc_subset_Icc_left (hln0 n).le) le_rfl) ?_]
    · exact radial_pos h (hln0 n) (by linarith [hln2 n]) hmu w _
    · intro p hp
      have h1 : p.1 ∉ Icc (ln n) u := fun hm' => hp.2 ⟨hm', hp.1.2⟩
      have := tent_out (show ln n < m by linarith [hln2 n]) hmu h1
      simp [rphi, this.1, this.2]
  set Z := |lo| + |hi|
  have hsub : S ⊆ Icc 0 u ×ˢ Icc (-Z) Z := by
    intro p hp
    refine ⟨hp.1, ?_, ?_⟩
    · linarith [hp.2.1, neg_abs_le lo, abs_nonneg hi]
    · linarith [hp.2.2, le_abs_self hi, abs_nonneg lo]
  have hF : IntegrableOn F S := ((h.1 u Z).1).mono_set hsub
  have hrdF : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) S := ((h.1 u Z).2).mono_set hsub
  obtain ⟨Ct, hCt⟩ := isCompact_Icc.exists_bound_of_continuousOn (ht.continuousOn (s := Icc lo hi))
  set C1 := 2 / m + |1 / (m - u)|
  have hdFm : AEStronglyMeasurable dF (volume.restrict S) := by
    have h2 := (Complex.measurable_ofReal.comp (measurable_fst.inv)).aestronglyMeasurable.mul
      hrdF.aestronglyMeasurable
    refine h2.congr ?_
    filter_upwards [ae_restrict_of_ae (ae_fst_ne 0)] with p hp
    show ((p.1⁻¹ : ℝ) : ℂ) * ((p.1 : ℂ) * dF p) = dF p
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hp, Complex.ofReal_one, one_mul]
  have hmeas : ∀ l : ℝ, AEStronglyMeasurable (fun p : ℝ × ℝ => w p.2 * rphi l m u F dF p) (volume.restrict S) := by
    intro l
    refine (Complex.continuous_ofReal.comp (ht.comp continuous_snd)).aestronglyMeasurable.mul ?_
    exact ((Complex.measurable_ofReal.comp ((tentSlope_meas l m u).comp measurable_fst)).aestronglyMeasurable.mul
      hF.aestronglyMeasurable).add
      ((Complex.continuous_ofReal.comp ((tent_cont l m u).comp continuous_fst)).aestronglyMeasurable.mul hdFm)
  have hbd : ∀ l, 0 ≤ l → l ≤ m / 2 → ∀ p ∈ S, ‖w p.2 * rphi l m u F dF p‖ ≤
      Ct * (C1 * ‖F p‖ + 2 / m * ‖(p.1 : ℂ) * dF p‖) := by
    intro l hl hl2 p hp
    have ht' : ‖t p.2‖ ≤ Ct := hCt _ hp.2
    rw [norm_mul]
    refine mul_le_mul ?_ ?_ (norm_nonneg _) ((norm_nonneg _).trans ht')
    · simpa [hw, Complex.norm_real] using ht'
    · simp only [rphi]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (slope_le hl2 hm) (norm_nonneg _)
      · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hp.1.1, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (tent_le hp.1.1 hl hl2 hm) (norm_nonneg _)
  have L := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict S) (l := atTop)
    (F := fun n p => w p.2 * rphi (ln n) m u F dF p) (f := fun p => w p.2 * rphi 0 m u F dF p)
    (fun p => Ct * (C1 * ‖F p‖ + 2 / m * ‖(p.1 : ℂ) * dF p‖))
    (Eventually.of_forall fun n => hmeas (ln n))
    (Eventually.of_forall fun n => (ae_restrict_iff' hS).2 (Eventually.of_forall (hbd (ln n) (hln0 n).le (hln2 n))))
    (((hF.norm.const_mul C1).add (hrdF.norm.const_mul (2 / m))).const_mul Ct) ?_
  · have L0 : Tendsto (fun n => ∫ p in S, w p.2 * rphi (ln n) m u F dF p) atTop (𝓝 0) := by
      simp only [hz]; exact tendsto_const_nhds
    exact tendsto_nhds_unique L L0
  · filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae (ae_fst_ne 0)] with p hpS hp0
    have hx : 0 < p.1 := lt_of_le_of_ne hpS.1.1 (Ne.symm hp0)
    have hxu : p.1 ≤ u := hpS.1.2
    have e : ∀ l, l ≤ p.1 → tentSlope l m u p.1 = if p.1 ≤ m then 1 / (m - l) else 1 / (m - u) := by
      intro l hlx
      unfold tentSlope
      rw [if_pos ⟨hlx, hxu⟩]
      split_ifs <;> rfl
    have hev : ∀ᶠ n in atTop, ln n ≤ p.1 := hlnt.eventually (eventually_le_nhds hx)
    have T1 : Tendsto (fun n => tentSlope (ln n) m u p.1) atTop (𝓝 (tentSlope 0 m u p.1)) := by
      rw [e 0 hx.le]
      refine Tendsto.congr' (hev.mono fun n hn => (e (ln n) hn).symm) ?_
      by_cases hxm : p.1 ≤ m
      · simp only [hxm, if_true]
        exact tendsto_const_nhds.div (tendsto_const_nhds.sub hlnt) (by simpa using hm.ne')
      · simp only [hxm, if_false]
        exact tendsto_const_nhds
    have hc : ContinuousAt (fun l => tentFn l m u p.1) 0 := by
      unfold tentFn
      exact continuousAt_const.max (((continuousAt_const.sub continuousAt_id).div
        (continuousAt_const.sub continuousAt_id) (by simpa using hm.ne')).min continuousAt_const)
    have T2 : Tendsto (fun n => tentFn (ln n) m u p.1) atTop (𝓝 (tentFn 0 m u p.1)) := hc.tendsto.comp hlnt
    simp only [rphi]
    exact tendsto_const_nhds.mul ((((Complex.continuous_ofReal.tendsto _).comp T1).mul_const _).add
      (((Complex.continuous_ofReal.tendsto _).comp T2).mul_const _))

end Breakdown.FracInternal.SegmentParts

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

theorem radialStrip_tent_zero {F dF : ℝ × ℝ → ℂ} (h : IsRadialWeakPair F dF) {lo hi l m u : ℝ} {t : ℝ → ℝ}
    (ht : Continuous t) (hl : 0 ≤ l) (hlm : l < m) (hmu : m < u) :
    ∫ p in Set.Icc l u ×ˢ Set.Icc lo hi,
      (if p.1 ≤ m then radialStripTerm m l F dF t p else radialStripTerm m u F dF t p) = 0 := by
  have hmeas : MeasurableSet (Set.Icc l u ×ˢ Set.Icc lo hi) := measurableSet_Icc.prod measurableSet_Icc
  have heq : Set.EqOn (fun p : ℝ × ℝ => if p.1 ≤ m then radialStripTerm m l F dF t p else radialStripTerm m u F dF t p)
      (fun p => ((t p.2 : ℝ) : ℂ) * Breakdown.FracInternal.SegmentParts.rphi l m u F dF p)
      (Set.Icc l u ×ˢ Set.Icc lo hi) := by
    intro p hp
    have hx := hp.1
    simp only [Breakdown.FracInternal.SegmentParts.rphi]
    rw [Breakdown.FracInternal.CornerParts.tent_eq_on hlm hmu hx]
    unfold Breakdown.FracInternal.CornerParts.tentSlope
    rw [if_pos hx]
    split_ifs <;> simp only [radialStripTerm] <;> push_cast <;> ring
  rw [setIntegral_congr_fun hmeas heq]
  rcases hl.lt_or_eq with hl' | hl'
  · exact Breakdown.FracInternal.SegmentParts.radial_pos h hl' hlm hmu (fun y => ((t y : ℝ) : ℂ)) _
  · subst hl'
    exact Breakdown.FracInternal.SegmentParts.radial_zero h ht hlm hmu

theorem heightStrip_tent_zero {wt : ℝ → ℝ} {F dF : ℝ × ℝ → ℂ} (h : IsHeightWeakPair wt F dF)
    (hwt : Continuous wt) {lo hi l m u : ℝ} {t : ℝ → ℝ} (ht : Continuous t) (hlm : l < m) (hmu : m < u) :
    ∫ p in Set.Icc lo hi ×ˢ Set.Icc l u,
      (if p.2 ≤ m then heightStripTerm m l wt F dF t p else heightStripTerm m u wt F dF t p) = 0 := by
  have hmeas : MeasurableSet (Set.Icc lo hi ×ˢ Set.Icc l u) := measurableSet_Icc.prod measurableSet_Icc
  have heq : Set.EqOn (fun p : ℝ × ℝ => if p.2 ≤ m then heightStripTerm m l wt F dF t p
      else heightStripTerm m u wt F dF t p)
      (fun p => ((wt p.1 * t p.1 : ℝ) : ℂ) * Breakdown.FracInternal.SegmentParts.hphi l m u F dF p)
      (Set.Icc lo hi ×ˢ Set.Icc l u) := by
    intro p hp
    have hz := hp.2
    simp only [Breakdown.FracInternal.SegmentParts.hphi]
    rw [Breakdown.FracInternal.CornerParts.tent_eq_on hlm hmu hz]
    unfold Breakdown.FracInternal.CornerParts.tentSlope
    rw [if_pos hz]
    split_ifs <;> simp only [heightStripTerm] <;> push_cast <;> ring
  rw [setIntegral_congr_fun hmeas heq]
  exact Breakdown.FracInternal.SegmentParts.height_zero h hlm hmu (fun x => ((wt x * t x : ℝ) : ℂ)) _

theorem segment_modes_weak {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k) (hx : IsAdmissible c x)
    (L : CellLayout) (hL : L.order = c.order) (n : ℤ) (a : Fin 3) :
    IsRadialWeakPair (L.velMode n x a) (L.gradModeOf n x a 0) ∧
    IsHeightWeakPair (fun _ => 1) (L.velMode n x a) (L.gradModeOf n x a 2) ∧
    IsRadialWeakPair (L.gradModeOf n x a 0) (L.secondModeOf n x a 0 0) ∧
    IsHeightWeakPair (fun r => r) (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 2) ∧
    IsRadialWeakPair (L.pressMode n x) (L.pressureGradMode n x 0) ∧
    IsHeightWeakPair (fun r => r) (L.pressMode n x) (L.pressureGradMode n x 2) :=
  ⟨⟨fun R Z => ⟨(modes_integrable_weighted c x hx L hL n a R Z).1, (modes_integrable_weighted c x hx L hL n a R Z).2.1⟩,
      fun δ R Z hδ => (modes_integrable_off c x hx L hL n a δ R Z hδ).1,
      fun ψ hψ hc hpos => (modes_weak_identities c x hx L hL n a ψ hψ hc hpos).1⟩,
    modes_height_pair_velocity c x hx L hL n a, modes_radial_pair_gradient c x hx L hL n a,
    modes_height_pair_gradient c x hx L hL n a, modes_radial_pair_pressure c x hx L hL n,
    modes_height_pair_pressure c x hx L hL n⟩

end Breakdown.CellCert.CellFormula
