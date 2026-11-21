import Breakdown.Weak.StatementsTime
import Breakdown.FreqTr.MildOfWeak
import Breakdown.FreqTr.Realization
import Mathlib.MeasureTheory.Measure.SeparableMeasure

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

open Freq

namespace Internal.GoodTimes

open Freq.Internal.MildOfWeak Freq.Internal.WeakInX

theorem sspRate_sub (u : X) {χ h χ' h' : X} (hl : IsSspOf χ h) (hl' : IsSspOf χ' h') :
    sspRate u h - sspRate u h' = sspRate u (h - h') := by
  unfold sspRate
  rw [tri_sub_third fieldOpRealized_holds trilinear_holds velocityInverts_holds u u hl hl',
    inner_sub_right]
  ring

theorem continuous_sspRate {χ h : X} (hl : IsSspOf χ h) :
    Continuous (fun u : X => sspRate u h) := by
  unfold sspRate
  exact (continuous_id.inner continuous_const).add
    (continuous_trilinear_diag trilinear_holds _
      (vel_two fieldOpRealized_holds velocityInverts_holds hl).1 (vel_six h).1)

theorem abs_sspRate_le {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ u v χ h : X, IsSspOf χ h →
      |trilinear u v (velocity h)| ≤ K * ‖u‖ * ‖v‖ * (‖χ‖ + ‖h‖))
    {u χ h : X} (hl : IsSspOf χ h) {A a b : ℝ} (hu : ‖u‖ ≤ A) (ha : ‖χ‖ ≤ a) (hb : ‖h‖ ≤ b) :
    |sspRate u h| ≤ A * b + K * A * A * (a + b) := by
  unfold sspRate
  have hA : 0 ≤ A := (norm_nonneg _).trans hu
  have h1 : |inner ℝ u h| ≤ A * b :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul hu hb (norm_nonneg _) hA)
  have h2 : K * ‖u‖ * ‖u‖ * (‖χ‖ + ‖h‖) ≤ K * A * A * (a + b) := by
    have e1 : K * ‖u‖ ≤ K * A := mul_le_mul_of_nonneg_left hu hK0
    have e2 : K * ‖u‖ * ‖u‖ ≤ K * A * A :=
      mul_le_mul e1 hu (norm_nonneg _) (mul_nonneg hK0 hA)
    exact mul_le_mul e2 (add_le_add ha hb) (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (mul_nonneg hK0 hA) hA)
  exact (abs_add_le _ _).trans (add_le_add h1 ((hK u u χ h hl).trans h2))

theorem integrableOn_comp {y : ℝ → X} {l r B : ℝ} {g : X → ℝ} (hg : Continuous g)
    (hy : AEStronglyMeasurable y (volume.restrict (Ioo l r)))
    (hb : ∀ t ∈ Ioo l r, ‖g (y t)‖ ≤ B) : IntegrableOn (fun t => g (y t)) (Ioo l r) :=
  Integrable.of_bound (hg.comp_aestronglyMeasurable hy) B
    ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ hb))

theorem pair_identity (hDR : ConstOfWeakDeriv) {y : ℝ → X} {l r M : ℝ} (hlr : l < r)
    (hM : ∀ t ∈ Ioo l r, ‖y t‖ ≤ M) (hy : AEStronglyMeasurable y (volume.restrict (Ioo l r)))
    (hW : IsTensorWeak y l r) {φ : Space → Space} (hφ : IsTestField φ) :
    ∃ c : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo l r)),
      inner ℝ (y t) (embedX φ) = c - ∫ τ in l..t, sspRate (y τ) (embedX (negSsp φ)) := by
  have hl := embedNegSsp_holds φ hφ
  obtain ⟨K, hK0, hK⟩ := tri_bound fieldOpRealized_holds trilinear_holds velocityInverts_holds
  have ha : IntegrableOn (fun t => inner ℝ (y t) (embedX φ)) (Ioo l r) :=
    integrableOn_comp (g := fun u => inner ℝ u (embedX φ)) (continuous_id.inner continuous_const)
      hy (B := M * ‖embedX φ‖) fun t ht => by
        rw [Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (hM t ht) (norm_nonneg _))
  have hb : IntegrableOn (fun t => sspRate (y t) (embedX (negSsp φ))) (Ioo l r) :=
    integrableOn_comp (g := fun u => sspRate u (embedX (negSsp φ))) (continuous_sspRate hl) hy
      (B := M * ‖embedX (negSsp φ)‖ + K * M * M * (‖embedX φ‖ + ‖embedX (negSsp φ)‖))
      fun t ht => by
        rw [Real.norm_eq_abs]
        exact abs_sspRate_le hK0 hK hl (hM t ht) le_rfl le_rfl
  have hwr : ∀ t, weakRate (y t) φ = sspRate (y t) (embedX (negSsp φ)) := fun t => by
    unfold weakRate sspRate
    rw [tri_congr _ _ (velocity_negSsp velocity_holds hφ)]
  refine hDR _ _ l r hlr ha hb fun θ hθ hc hs => ?_
  simpa only [hwr] using hW θ φ hθ hc hs hφ

theorem exists_near {D : Set (X × X)}
    (hTD : {p : X × X | ∃ φ, IsTestField φ ∧ p = (embedX φ, embedX (negSsp φ))} ⊆ closure D)
    {χ h : X} (hl : IsSspOf χ h) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q ∈ D, ‖χ - q.1‖ ≤ δ ∧ ‖h - q.2‖ ≤ δ := by
  have hε : 0 < δ / 2 := half_pos hδ
  obtain ⟨φ, hφ, hχ, hh⟩ := testDense_holds.1 χ h hl (δ / 2) hε
  have hmem : (embedX φ, embedX (negSsp φ)) ∈ closure D := hTD ⟨φ, hφ, rfl⟩
  obtain ⟨q, hqD, hdq⟩ := Metric.mem_closure_iff.1 hmem (δ / 2) hε
  have hdq' : max (dist (embedX φ) q.1) (dist (embedX (negSsp φ)) q.2) < δ / 2 := by
    rw [Prod.dist_eq] at hdq; exact hdq
  have hq1 : dist (embedX φ) q.1 < δ / 2 := (le_max_left _ _).trans_lt hdq'
  have hq2 : dist (embedX (negSsp φ)) q.2 < δ / 2 := (le_max_right _ _).trans_lt hdq'
  rw [dist_eq_norm] at hq1 hq2
  have e1 : ‖χ - q.1‖ ≤ ‖χ - embedX φ‖ + ‖embedX φ - q.1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  have e2 : ‖h - q.2‖ ≤ ‖h - embedX (negSsp φ)‖ + ‖embedX (negSsp φ) - q.2‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  rw [norm_sub_rev χ (embedX φ)] at e1
  rw [norm_sub_rev h (embedX (negSsp φ))] at e2
  exact ⟨q, hqD, by linarith, by linarith⟩

theorem approx_bound {y : ℝ → X} {l r K M' s t : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ u v χ h : X, IsSspOf χ h →
      |trilinear u v (velocity h)| ≤ K * ‖u‖ * ‖v‖ * (‖χ‖ + ‖h‖))
    (hM0 : 0 ≤ M') (hM' : ∀ τ ∈ Ioo l r, ‖y τ‖ ≤ M')
    (hint : ∀ {χ' h' : X}, IsSspOf χ' h' → IntervalIntegrable (fun τ => sspRate (y τ) h') volume s t)
    (hs : s ∈ Ioo l r) (ht : t ∈ Ioo l r) (hst : s ≤ t) {χ h χ' h' : X} (hl : IsSspOf χ h)
    (hl' : IsSspOf χ' h')
    (hz : inner ℝ (y t) χ' - inner ℝ (y s) χ' + ∫ τ in s..t, sspRate (y τ) h' = 0)
    {δ : ℝ} (d1 : ‖χ - χ'‖ ≤ δ) (d2 : ‖h - h'‖ ≤ δ) :
    |inner ℝ (y t) χ - inner ℝ (y s) χ + ∫ τ in s..t, sspRate (y τ) h| ≤
      (2 * M' + (M' + 2 * K * M' * M') * |t - s|) * δ := by
  have hdiff := isSspOf_sub hl hl'
  have eI : (∫ τ in s..t, sspRate (y τ) h) - ∫ τ in s..t, sspRate (y τ) h' =
      ∫ τ in s..t, sspRate (y τ) (h - h') := by
    rw [← intervalIntegral.integral_sub (hint hl) (hint hl')]
    congr 1
    funext τ
    exact sspRate_sub _ hl hl'
  have eL : inner ℝ (y t) χ - inner ℝ (y s) χ + ∫ τ in s..t, sspRate (y τ) h =
      (inner ℝ (y t) (χ - χ') - inner ℝ (y s) (χ - χ')) +
        ∫ τ in s..t, sspRate (y τ) (h - h') := by
    rw [← eI, inner_sub_right, inner_sub_right]
    linarith
  have b1 : |inner ℝ (y t) (χ - χ')| ≤ M' * δ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (hM' t ht) d1 (norm_nonneg _) hM0)
  have b2 : |inner ℝ (y s) (χ - χ')| ≤ M' * δ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (hM' s hs) d1 (norm_nonneg _) hM0)
  have b3 : ‖∫ τ in s..t, sspRate (y τ) (h - h')‖ ≤
      (M' * δ + K * M' * M' * (δ + δ)) * |t - s| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun τ hτ => ?_
    rw [uIoc_of_le hst] at hτ
    have hτI : τ ∈ Ioo l r := ⟨hs.1.trans hτ.1, hτ.2.trans_lt ht.2⟩
    rw [Real.norm_eq_abs]
    exact abs_sspRate_le hK0 hK hdiff (hM' τ hτI) d1 d2
  rw [Real.norm_eq_abs] at b3
  have b4 : |inner ℝ (y t) (χ - χ') - inner ℝ (y s) (χ - χ')| ≤ M' * δ + M' * δ :=
    (abs_sub _ _).trans (add_le_add b1 b2)
  rw [eL]
  refine (abs_add_le _ _).trans ?_
  have : (2 * M' + (M' + 2 * K * M' * M') * |t - s|) * δ =
      (M' * δ + M' * δ) + (M' * δ + K * M' * M' * (δ + δ)) * |t - s| := by ring
  rw [this]
  exact add_le_add b4 b3

theorem separableSpace_pair : TopologicalSpace.SeparableSpace (X × X) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have : SecondCountableTopology L2C := inferInstance
  have : SecondCountableTopology X := inferInstance
  infer_instance

end Internal.GoodTimes

open Internal.GoodTimes Freq.Internal.MildOfWeak

theorem goodTimes_holds : GoodTimes := by
  intro hDR y l r M hlr hM hy hW
  obtain ⟨K, hK0, hK⟩ := tri_bound fieldOpRealized_holds trilinear_holds velocityInverts_holds
  set M' := max M 0 with hM'def
  have hM0 : 0 ≤ M' := le_max_right _ _
  have hM' : ∀ t ∈ Ioo l r, ‖y t‖ ≤ M' := fun t ht => (hM t ht).trans (le_max_left _ _)
  have hint : ∀ {χ' h' : X}, IsSspOf χ' h' → ∀ a b, l ≤ a → a < r → l ≤ b → b < r →
      IntervalIntegrable (fun τ => sspRate (y τ) h') volume a b := by
    intro χ' h' hl' a b ha ha' hb hb'
    have hI : IntegrableOn (fun t => sspRate (y t) h') (Ioo l r) :=
      integrableOn_comp (g := fun u => sspRate u h') (continuous_sspRate hl') hy
        (B := M' * ‖h'‖ + K * M' * M' * (‖χ'‖ + ‖h'‖)) fun t ht => by
          rw [Real.norm_eq_abs]
          exact abs_sspRate_le hK0 hK hl' (hM' t ht) le_rfl le_rfl
    exact ⟨hI.mono_set fun x hx => ⟨ha.trans_lt hx.1, hx.2.trans_lt hb'⟩,
      hI.mono_set fun x hx => ⟨hb.trans_lt hx.1, hx.2.trans_lt ha'⟩⟩
  set T : Set (X × X) := {p | ∃ φ, IsTestField φ ∧ p = (embedX φ, embedX (negSsp φ))} with hT
  have := separableSpace_pair
  obtain ⟨D, hDT, hDc, hTD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace T).exists_countable_dense_subset
  have hsspD : ∀ p : D, IsSspOf p.1.1 p.1.2 := by
    intro p
    obtain ⟨φ, hφ, hp⟩ := hDT p.2
    rw [hp]
    exact embedNegSsp_holds φ hφ
  have hc : ∀ p : D, ∃ c : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo l r)),
      inner ℝ (y t) p.1.1 = c - ∫ τ in l..t, sspRate (y τ) p.1.2 := by
    intro p
    obtain ⟨φ, hφ, hp⟩ := hDT p.2
    rw [hp]
    exact pair_identity hDR hlr hM hy hW hφ
  choose c hc using hc
  have : Countable D := hDc.to_subtype
  refine ⟨Ioo l r ∩ ⋂ p : D,
    {t | inner ℝ (y t) p.1.1 = c p - ∫ τ in l..t, sspRate (y τ) p.1.2}, inter_subset_left, ?_, ?_⟩
  · refine measure_mono_null (t := ⋃ p : D, {t | ¬ (t ∈ Ioo l r →
        inner ℝ (y t) p.1.1 = c p - ∫ τ in l..t, sspRate (y τ) p.1.2)}) ?_ ?_
    · intro t ht
      obtain ⟨h1, h2⟩ := ht
      have h3 : ¬ ∀ p : D, inner ℝ (y t) p.1.1 = c p - ∫ τ in l..t, sspRate (y τ) p.1.2 :=
        fun h => h2 ⟨h1, mem_iInter.2 fun p => h p⟩
      obtain ⟨p, hp⟩ := not_forall.1 h3
      exact mem_iUnion.2 ⟨p, fun h => hp (h h1)⟩
    · exact measure_iUnion_null fun p => ae_iff.1 ((ae_restrict_iff' measurableSet_Ioo).1 (hc p))
  · intro s hs t ht hst χ h hl
    have hsI : s ∈ Ioo l r := hs.1
    have htI : t ∈ Ioo l r := ht.1
    refine ⟨hint hl s t hsI.1.le hsI.2 htI.1.le htI.2, ?_⟩
    have hD : ∀ p : D, inner ℝ (y t) p.1.1 - inner ℝ (y s) p.1.1 +
        ∫ τ in s..t, sspRate (y τ) p.1.2 = 0 := by
      intro p
      have e1 : inner ℝ (y t) p.1.1 = c p - ∫ τ in l..t, sspRate (y τ) p.1.2 :=
        mem_iInter.1 ht.2 p
      have e2 : inner ℝ (y s) p.1.1 = c p - ∫ τ in l..s, sspRate (y τ) p.1.2 :=
        mem_iInter.1 hs.2 p
      rw [e1, e2, ← intervalIntegral.integral_interval_sub_left
        (hint (hsspD p) l t le_rfl hlr htI.1.le htI.2) (hint (hsspD p) l s le_rfl hlr hsI.1.le hsI.2)]
      ring
    have hbound : ∀ δ > 0, |inner ℝ (y t) χ - inner ℝ (y s) χ + ∫ τ in s..t, sspRate (y τ) h| ≤
        (2 * M' + (M' + 2 * K * M' * M') * |t - s|) * δ := by
      intro δ hδ
      obtain ⟨q, hqD, d1, d2⟩ := exists_near hTD hl hδ
      exact approx_bound hK0 hK hM0 hM' (fun hl' => hint hl' s t hsI.1.le hsI.2 htI.1.le htI.2)
        hsI htI hst hl (hsspD ⟨q, hqD⟩) (hD ⟨q, hqD⟩) d1 d2
    have hB : 0 ≤ 2 * M' + (M' + 2 * K * M' * M') * |t - s| := by positivity
    have hL : |inner ℝ (y t) χ - inner ℝ (y s) χ + ∫ τ in s..t, sspRate (y τ) h| ≤ 0 := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      have hB1 : 0 < 2 * M' + (M' + 2 * K * M' * M') * |t - s| + 1 := by linarith
      refine (hbound _ (div_pos hδ hB1)).trans ?_
      rw [zero_add, mul_div_assoc', div_le_iff₀ hB1]
      nlinarith
    have := abs_nonpos_iff.1 hL
    linarith

end Breakdown.WeakProfile
