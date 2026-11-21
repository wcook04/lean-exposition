import Mathlib
import Breakdown.Cert.PeriodIntegral
import Breakdown.Cert.Basic

open scoped ENNReal ContDiff Interval
open MeasureTheory Set Filter

noncomputable section

universe u

namespace Breakdown.Cert

namespace Internal.TimeModulus

def transportRate (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (g : ℝ → Space → Space) (s : ℝ) (y : Space) : Space :=
  P • (g s y - (1 / 2 : ℝ) • v s y - (1 / 2 : ℝ) • G s y y)

def shiftIntegral (δ : ℝ) (Φ : ℝ × Space → ℝ) (z : ℝ × Space) : ℝ :=
  ∫ t in (0 : ℝ)..δ, Φ (z - t • ((1 : ℝ), (0 : Space)))

def transportDefect (P δ : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (g : ℝ → Space → Space) (z : ℝ × Space) : Space :=
  v (z.1 + δ) z.2 - v z.1 z.2 - ∫ t in (0 : ℝ)..δ, transportRate P v G g (z.1 + t) z.2

theorem contDiff_shift_integral {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (e : E) (a b : ℝ) (n : ℕ) :
    ∀ {Φ : E → F}, ContDiff ℝ n Φ → HasCompactSupport Φ →
      ContDiff ℝ n (fun x => ∫ t in a..b, Φ (x - t • e)) := by
  induction n generalizing F with
  | zero =>
    intro Φ hΦ _
    rw [Nat.cast_zero, contDiff_zero] at hΦ ⊢
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x t => Φ (x - t • e))
      (hΦ.comp (continuous_fst.sub (continuous_snd.smul continuous_const))) a b
  | succ n ih =>
    intro Φ hΦ hc
    have hΦ' : ContDiff ℝ (n + 1) Φ := by exact_mod_cast hΦ
    have hd : ContDiff ℝ n (fderiv ℝ Φ) := hΦ'.fderiv_right le_rfl
    have hdc : Continuous (fderiv ℝ Φ) := hΦ'.continuous_fderiv (by simp)
    have hdiff : Differentiable ℝ Φ := hΦ'.differentiable (by simp)
    obtain ⟨C, hC⟩ := hdc.bounded_above_of_compact_support (hc.fderiv (𝕜 := ℝ))
    have key := ih (F := E →L[ℝ] F) hd (hc.fderiv (𝕜 := ℝ))
    have hF : ∀ x₀ : E, HasFDerivAt (fun x => ∫ t in a..b, Φ (x - t • e))
        (∫ t in a..b, fderiv ℝ Φ (x₀ - t • e)) x₀ := by
      intro x₀
      refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F := fun x t => Φ (x - t • e)) (F' := fun x t => fderiv ℝ Φ (x - t • e))
        (bound := fun _ => C) (s := univ) univ_mem ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
      · exact Eventually.of_forall fun x =>
          (hΦ'.continuous.comp (continuous_const.sub (continuous_id.smul continuous_const))).aestronglyMeasurable
      · exact (hΦ'.continuous.comp (continuous_const.sub (continuous_id.smul continuous_const))).intervalIntegrable _ _
      · exact (hdc.comp (continuous_const.sub (continuous_id.smul continuous_const))).aestronglyMeasurable
      · exact Eventually.of_forall fun t _ x _ => hC _
      · refine Eventually.of_forall fun t _ x _ => ?_
        have h1 := (hdiff (x - t • e)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const (t • e))
        simp only [ContinuousLinearMap.comp_id] at h1
        exact h1
    have hres : ContDiff ℝ (n + 1) (fun x => ∫ t in a..b, Φ (x - t • e)) :=
      contDiff_succ_iff_hasFDerivAt.2 ⟨_, key, hF⟩
    exact_mod_cast hres

theorem hasDerivAt_shiftIntegral {δ : ℝ} {Φ : ℝ × Space → ℝ} (hΦ : Continuous Φ) (s : ℝ) (y : Space) :
    HasDerivAt (fun s => shiftIntegral δ Φ (s, y)) (Φ (s, y) - Φ (s - δ, y)) s := by
  have hf : Continuous (fun u : ℝ => Φ (u, y)) := hΦ.comp (continuous_id.prodMk continuous_const)
  have e1 : ∀ s : ℝ, shiftIntegral δ Φ (s, y) =
      (∫ u in (0 : ℝ)..s, Φ (u, y)) - ∫ u in (0 : ℝ)..(s - δ), Φ (u, y) := by
    intro s
    have e2 : ∀ t : ℝ, Φ ((s, y) - t • ((1 : ℝ), (0 : Space))) = (fun u => Φ (u, y)) (s - t) := by
      intro t
      simp
    unfold shiftIntegral
    simp_rw [e2]
    rw [intervalIntegral.integral_comp_sub_left (fun u => Φ (u, y)) s, sub_zero,
      intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
  simp_rw [e1]
  have h1 := (hf.integral_hasStrictDerivAt 0 s).hasDerivAt
  have h2 := ((hf.integral_hasStrictDerivAt 0 (s - δ)).hasDerivAt).comp_sub_const s δ
  exact h1.sub h2

theorem shiftIntegral_support {δ : ℝ} {Φ : ℝ × Space → ℝ} (hc : HasCompactSupport Φ) :
    ∃ K : Set (ℝ × Space), IsCompact K ∧ (∀ z ∉ K, shiftIntegral δ Φ z = 0) ∧
      ∀ z ∈ K, ∃ w ∈ tsupport Φ, z.2 = w.2 := by
  refine ⟨(fun p : (ℝ × Space) × ℝ => p.1 + p.2 • ((1 : ℝ), (0 : Space))) '' (tsupport Φ ×ˢ uIcc 0 δ),
    (hc.isCompact.prod isCompact_uIcc).image (by fun_prop), ?_, ?_⟩
  · intro z hz
    unfold shiftIntegral
    refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_).trans
      intervalIntegral.integral_zero
    by_contra hne
    refine hz ⟨(z - t • ((1 : ℝ), (0 : Space)), t), ⟨subset_tsupport _ hne, ht⟩, ?_⟩
    simp
  · rintro z ⟨⟨w, t⟩, ⟨hw, _⟩, rfl⟩
    exact ⟨w, hw, by simp⟩

theorem shiftIntegral_test {δ R : ℝ} {Φ : ℝ × Space → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hc : HasCompactSupport Φ)
    (hs : tsupport Φ ⊆ univ ×ˢ Metric.ball (0 : Space) R) :
    ContDiff ℝ ∞ (shiftIntegral δ Φ) ∧ HasCompactSupport (shiftIntegral δ Φ) ∧
      tsupport (shiftIntegral δ Φ) ⊆ univ ×ˢ Metric.ball (0 : Space) R := by
  obtain ⟨K, hK, hK0, hK1⟩ := shiftIntegral_support (δ := δ) hc
  refine ⟨?_, HasCompactSupport.intro hK hK0, ?_⟩
  · refine contDiff_infty.2 fun n => ?_
    exact contDiff_shift_integral (F := ℝ) ((1 : ℝ), (0 : Space)) 0 δ n (hΦ.of_le (by exact_mod_cast le_top)) hc
  · have hsub : Function.support (shiftIntegral δ Φ) ⊆ K := fun z hz => by
      by_contra h
      exact hz (hK0 z h)
    refine (closure_minimal hsub hK.isClosed).trans fun z hz => ?_
    obtain ⟨w, hw, hzw⟩ := hK1 z hz
    exact ⟨mem_univ _, hzw ▸ (hs hw).2⟩

theorem unit_strip_lintegral {F : ℝ → Space → ℝ≥0∞} (hper : IsTimePeriodic F) (S : Set Space) (m : ℤ) :
    ∫⁻ z in Icc (m : ℝ) (m + 1) ×ˢ S, F z.1 z.2 = ∫⁻ z in Icc (0 : ℝ) 1 ×ˢ S, F z.1 z.2 := by
  set c : ℝ × Space := ((m : ℝ), (0 : Space))
  have hmp := measurePreserving_add_right ((volume : Measure ℝ).prod (volume : Measure Space)) c
  have h := hmp.setLIntegral_comp_preimage_emb (MeasurableEquiv.addRight c).measurableEmbedding
    (fun z : ℝ × Space => F z.1 z.2) (Icc (m : ℝ) (m + 1) ×ˢ S)
  have hpre : (fun z : ℝ × Space => z + c) ⁻¹' (Icc (m : ℝ) (m + 1) ×ˢ S) = Icc (0 : ℝ) 1 ×ˢ S := by
    ext ⟨a, b⟩
    simp only [c, mem_preimage, mem_prod, Prod.fst_add, Prod.snd_add, add_zero, mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by linarith, by linarith⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by linarith, by linarith⟩, h3⟩
  have hF : ∀ z : ℝ × Space, F (z + c).1 (z + c).2 = F z.1 z.2 := by
    intro z
    have hp : Function.Periodic (fun σ => F σ z.2) 1 := fun σ => hper σ z.2
    have := hp.int_mul m z.1
    simp only [mul_one] at this
    simpa [c] using this
  rw [Measure.volume_eq_prod, ← h, hpre]
  simp only [hF]

theorem iter_lintegral_eq_prod {F : ℝ × Space → ℝ≥0∞} (hF : AEMeasurable F) (I : Set ℝ) (S : Set Space) :
    ∫⁻ σ in I, ∫⁻ y in S, F (σ, y) = ∫⁻ z in I ×ˢ S, F z := by
  have h' : AEMeasurable F ((volume.restrict I).prod (volume.restrict S)) := by
    rw [Measure.prod_restrict]
    exact hF.restrict
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact (lintegral_prod F h').symm

theorem enorm_le_one_add_sq {E : Type*} [NormedAddCommGroup E] (x : E) :
    ‖x‖ₑ ≤ 1 + ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]

theorem integrableOn_unit_strip {E : Type*} [NormedAddCommGroup E] {f : ℝ → Space → E}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume) (hper : IsTimePeriodic f)
    {S : Set Space} (hS : volume S ≠ ⊤)
    (hfin : ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in S, ENNReal.ofReal (‖f σ y‖ ^ 2) < ⊤) (m : ℤ) :
    IntegrableOn (fun z : ℝ × Space => f z.1 z.2) (Icc (m : ℝ) (m + 1) ×ˢ S) := by
  refine ⟨hm.restrict, ?_⟩
  have hq : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖f z.1 z.2‖ ^ 2)) volume :=
    (hm.norm.pow 2).aemeasurable.ennreal_ofReal
  have hper' : IsTimePeriodic (fun σ y => ENNReal.ofReal (‖f σ y‖ ^ 2)) := by
    intro σ y
    simp only [hper σ y]
  have hvol : (volume : Measure (ℝ × Space)) (Icc (m : ℝ) (m + 1) ×ˢ S) ≠ ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS
  have e1 := unit_strip_lintegral hper' S m
  have e2 := iter_lintegral_eq_prod hq (Icc (0 : ℝ) 1) S
  simp only at e1 e2
  unfold HasFiniteIntegral
  calc ∫⁻ z in Icc (m : ℝ) (m + 1) ×ˢ S, ‖f z.1 z.2‖ₑ
      ≤ ∫⁻ z in Icc (m : ℝ) (m + 1) ×ˢ S, (1 + ENNReal.ofReal (‖f z.1 z.2‖ ^ 2)) :=
        lintegral_mono fun z => enorm_le_one_add_sq _
    _ = (volume : Measure (ℝ × Space)) (Icc (m : ℝ) (m + 1) ×ˢ S) +
          ∫⁻ z in Icc (0 : ℝ) 1 ×ˢ S, ENNReal.ofReal (‖f z.1 z.2‖ ^ 2) := by
        rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ, one_mul, e1]
    _ < ⊤ := by
        rw [← e2]
        exact ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hvol, hfin⟩

theorem integrableOn_strip {E : Type*} [NormedAddCommGroup E] {f : ℝ → Space → E}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume) (hper : IsTimePeriodic f)
    {S : Set Space} (hS : volume S ≠ ⊤)
    (hfin : ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in S, ENNReal.ofReal (‖f σ y‖ ^ 2) < ⊤) (N : ℕ) :
    IntegrableOn (fun z : ℝ × Space => f z.1 z.2) (Icc (-(N : ℝ)) N ×ˢ S) := by
  have hu := integrableOn_unit_strip hm hper hS hfin
  induction N with
  | zero =>
    refine (hu 0).mono_set (prod_mono (fun x hx => ?_) le_rfl)
    simp only [Nat.cast_zero, neg_zero, mem_Icc] at hx
    simp only [Int.cast_zero, zero_add, mem_Icc]
    exact ⟨hx.1, by linarith [hx.2]⟩
  | succ N ih =>
    have h3 := ((hu (-((N : ℤ) + 1))).union ih).union (hu (N : ℤ))
    refine h3.mono_set fun z hz => ?_
    obtain ⟨⟨h1, h2⟩, hzS⟩ := hz
    push_cast at h1 h2 ⊢
    by_cases ha : z.1 ≤ -(N : ℝ)
    · exact Or.inl (Or.inl ⟨⟨by linarith, by linarith⟩, hzS⟩)
    · by_cases hb : z.1 ≤ (N : ℝ)
      · exact Or.inl (Or.inr ⟨⟨by linarith, hb⟩, hzS⟩)
      · exact Or.inr ⟨⟨by linarith, by linarith⟩, hzS⟩

theorem locallyIntegrableOn_of_strips {E : Type*} [NormedAddCommGroup E] {f : ℝ × Space → E} {R : ℝ}
    (hf : ∀ N : ℕ, IntegrableOn f (Icc (-(N : ℝ)) N ×ˢ Metric.closedBall (0 : Space) R)) :
    LocallyIntegrableOn f ((univ : Set ℝ) ×ˢ Metric.ball (0 : Space) R) := by
  rw [locallyIntegrableOn_iff (isOpen_univ.prod Metric.isOpen_ball).isLocallyClosed]
  intro k hk hkc
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 (hkc.image continuous_fst).isBounded
  refine (hf ⌈r⌉₊).mono_set fun z hz => ⟨?_, Metric.ball_subset_closedBall (hk hz).2⟩
  have h1 := hr (mem_image_of_mem Prod.fst hz)
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le] at h1
  have h2 := Nat.le_ceil r
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

theorem norm_apply_sq_le_matSq (L : Space →L[ℝ] Space) (y : Space) : ‖L y‖ ^ 2 ≤ matSq L * ‖y‖ ^ 2 := by
  have hLy : L y = ∑ i : Fin 3, y i • L (unitVector i) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr y]
    simp [unitVector, EuclideanSpace.basisFun_apply, map_sum, map_smul]
  have h1 : ‖L y‖ ≤ ∑ i : Fin 3, |y i| * ‖L (unitVector i)‖ := by
    rw [hLy]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_smul, Real.norm_eq_abs]
  have h2 : (∑ i : Fin 3, |y i| * ‖L (unitVector i)‖) ^ 2 ≤
      (∑ i : Fin 3, |y i| ^ 2) * ∑ i : Fin 3, ‖L (unitVector i)‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : ‖y‖ ^ 2 = ∑ i : Fin 3, |y i| ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp
  calc ‖L y‖ ^ 2 ≤ (∑ i : Fin 3, |y i| * ‖L (unitVector i)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2
    _ = matSq L * ‖y‖ ^ 2 := by rw [h3, mul_comm]; rfl

theorem ball_lintegral_le_period {f : ℝ → Space → ℝ} (R : ℝ) :
    ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (f σ y) ≤
      periodLIntegral f :=
  lintegral_mono fun _ => setLIntegral_le_lintegral _ _

theorem integrableOn_velocity_strip {P R : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation ∅ P v G H g)
    (hloc : periodBallLIntegral R (fun σ y => ‖v σ y‖ ^ 2) < ⊤) (N : ℕ) :
    IntegrableOn (fun z : ℝ × Space => v z.1 z.2) (Icc (-(N : ℝ)) N ×ˢ Metric.closedBall (0 : Space) R) :=
  integrableOn_strip hv.measurable_velocity hv.periodic_velocity (measure_closedBall_lt_top).ne hloc N

private theorem integrableOn_derivative_strip {P R : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation ∅ P v G H g) (N : ℕ) :
    IntegrableOn (fun z : ℝ × Space => g z.1 z.2) (Icc (-(N : ℝ)) N ×ˢ Metric.closedBall (0 : Space) R) :=
  integrableOn_strip hv.measurable_derivative hv.periodic_derivative measure_closedBall_lt_top.ne
    ((ball_lintegral_le_period R).trans_lt hv.derivative_finite) N

private theorem integrableOn_gradient_apply_strip {P R : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation ∅ P v G H g) (N : ℕ) :
    IntegrableOn (fun z : ℝ × Space => G z.1 z.2 z.2) (Icc (-(N : ℝ)) N ×ˢ Metric.closedBall (0 : Space) R) := by
  have hS : volume (Metric.closedBall (0 : Space) R) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hwm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2 z.2) volume :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hv.measurable_gradient.prodMk measurable_snd.aestronglyMeasurable)
  have hwp : IsTimePeriodic (fun σ y => G σ y y) := fun σ y => by simp only [hv.periodic_gradient σ y]
  have hwf : ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R,
      ENNReal.ofReal (‖G σ y y‖ ^ 2) < ⊤ := by
    have hb : ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R,
        ENNReal.ofReal (‖G σ y y‖ ^ 2) ≤
        ENNReal.ofReal (R ^ 2) * periodLIntegral (fun σ y => matSq (G σ y)) := by
      unfold periodLIntegral
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun σ => ?_
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine (setLIntegral_mono' Metric.isClosed_closedBall.measurableSet fun y hy => ?_).trans
        (setLIntegral_le_lintegral _ _)
      rw [← ENNReal.ofReal_mul (sq_nonneg R)]
      refine ENNReal.ofReal_le_ofReal ((norm_apply_sq_le_matSq _ _).trans ?_)
      have hyR : ‖y‖ ≤ R := mem_closedBall_zero_iff.1 hy
      have hf0 : 0 ≤ matSq (G σ y) := Finset.sum_nonneg fun _ _ => sq_nonneg _
      rw [mul_comm (R ^ 2)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hyR 2) hf0
    exact hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hv.gradient_finite)
  exact integrableOn_strip hwm hwp hS hwf N

theorem integrableOn_rate_strip {P R : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation ∅ P v G H g)
    (hloc : periodBallLIntegral R (fun σ y => ‖v σ y‖ ^ 2) < ⊤) (N : ℕ) :
    IntegrableOn (fun z : ℝ × Space => transportRate P v G g z.1 z.2)
      (Icc (-(N : ℝ)) N ×ˢ Metric.closedBall (0 : Space) R) := by
  unfold transportRate
  exact (((integrableOn_derivative_strip hv N).sub ((integrableOn_velocity_strip hv hloc N).smul (1 / 2 : ℝ))).sub
    ((integrableOn_gradient_apply_strip hv N).smul (1 / 2 : ℝ))).smul P

theorem integrableOn_shift_strip {E : Type*} [NormedAddCommGroup E] {f : ℝ × Space → E} {R : ℝ}
    (hf : ∀ N : ℕ, IntegrableOn f (Icc (-(N : ℝ)) N ×ˢ Metric.closedBall (0 : Space) R)) (δ : ℝ) (N : ℕ) :
    IntegrableOn (fun z : ℝ × Space => f (z.1 + δ, z.2)) (Icc (-(N : ℝ)) N ×ˢ Metric.closedBall (0 : Space) R) := by
  set c : ℝ × Space := (δ, (0 : Space))
  have hmp := measurePreserving_add_right ((volume : Measure ℝ).prod (volume : Measure Space)) c
  have key := (hmp.integrableOn_comp_preimage (MeasurableEquiv.addRight c).measurableEmbedding
    (f := f) (s := Icc (-((N + ⌈|δ|⌉₊ : ℕ) : ℝ)) ((N + ⌈|δ|⌉₊ : ℕ) : ℝ) ×ˢ Metric.closedBall (0 : Space) R)).2
    (by rw [← Measure.volume_eq_prod]; exact hf _)
  rw [← Measure.volume_eq_prod] at key
  have hfun : (f ∘ fun x => x + c) = fun z : ℝ × Space => f (z.1 + δ, z.2) := by
    funext z
    refine congrArg f (Prod.ext ?_ ?_) <;> simp [c]
  rw [hfun] at key
  refine key.mono_set fun z hz => ?_
  obtain ⟨⟨h1, h2⟩, h3⟩ := hz
  have hd := Nat.le_ceil |δ|
  have ha := abs_le.1 (le_refl |δ|)
  simp only [c, mem_preimage, mem_prod, mem_Icc, Prod.fst_add, Prod.snd_add, add_zero]
  push_cast
  exact ⟨⟨by linarith, by linarith⟩, h3⟩

theorem quasiMeasurePreserving_time_shift :
    Measure.QuasiMeasurePreserving (fun p : (ℝ × Space) × ℝ => p.1 + (p.2, (0 : Space)))
      volume volume := by
  refine ⟨by fun_prop, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply (by fun_prop) hs]
  change ((volume : Measure (ℝ × Space)).prod (volume : Measure ℝ)) _ = 0
  rw [Measure.prod_apply_symm (hs.preimage (by fun_prop))]
  have hsec : ∀ t : ℝ, (volume : Measure (ℝ × Space))
      ((fun x : ℝ × Space => (x, t)) ⁻¹' ((fun p : (ℝ × Space) × ℝ => p.1 + (p.2, (0 : Space))) ⁻¹' s)) = 0 := by
    intro t
    have := measure_preimage_add_right ((volume : Measure ℝ).prod (volume : Measure Space)) (t, (0 : Space)) s
    exact this.trans h0
  simp only [hsec, lintegral_zero]

theorem abs_le_of_mem_uIoc {t δ : ℝ} (ht : t ∈ Ι (0 : ℝ) δ) : |t| ≤ |δ| := by
  rcases mem_uIcc.1 (uIoc_subset_uIcc ht) with h | h
  · rw [abs_of_nonneg h.1, abs_of_nonneg (h.1.trans h.2)]
    exact h.2
  · rw [abs_of_nonpos h.2, abs_of_nonpos (h.1.trans h.2)]
    linarith [h.1]

theorem integrableOn_average_strip {f : ℝ × Space → Space} {R : ℝ} (hm : AEStronglyMeasurable f volume)
    (hf : ∀ N : ℕ, IntegrableOn f (Icc (-(N : ℝ)) N ×ˢ Metric.closedBall (0 : Space) R)) (δ : ℝ) (N : ℕ) :
    IntegrableOn (fun z : ℝ × Space => ∫ t in (0 : ℝ)..δ, f (z.1 + t, z.2))
      (Icc (-(N : ℝ)) N ×ˢ Metric.closedBall (0 : Space) R) := by
  set A := Icc (-(N : ℝ)) N ×ˢ Metric.closedBall (0 : Space) R
  set M : ℕ := N + ⌈|δ|⌉₊
  set B := Icc (-(M : ℝ)) M ×ˢ Metric.closedBall (0 : Space) R
  have hF : AEStronglyMeasurable (fun p : (ℝ × Space) × ℝ => f (p.1.1 + p.2, p.1.2)) volume := by
    refine (hm.comp_quasiMeasurePreserving quasiMeasurePreserving_time_shift).congr
      (Eventually.of_forall fun p => ?_)
    simp only [Function.comp]
    refine congrArg f (Prod.ext ?_ ?_) <;> simp
  have hF' : AEStronglyMeasurable (fun p : (ℝ × Space) × ℝ => f (p.1.1 + p.2, p.1.2))
      ((volume : Measure (ℝ × Space)).prod (volume.restrict (Ι (0 : ℝ) δ))) :=
    hF.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hmeas : AEStronglyMeasurable (fun z : ℝ × Space => ∫ t in (0 : ℝ)..δ, f (z.1 + t, z.2)) volume := by
    simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    exact (hF'.integral_prod_right').const_smul (if (0 : ℝ) ≤ δ then 1 else -1 : ℝ)
  refine ⟨hmeas.restrict, ?_⟩
  have hC : ∫⁻ z in B, ‖f z‖ₑ < ⊤ := (hf M).2
  have hin : ∀ t ∈ Ι (0 : ℝ) δ, ∫⁻ z in A, ‖f (z.1 + t, z.2)‖ₑ ≤ ∫⁻ z in B, ‖f z‖ₑ := by
    intro t ht
    have htd := abs_le_of_mem_uIoc ht
    set c : ℝ × Space := (t, (0 : Space))
    have hmp := measurePreserving_add_right ((volume : Measure ℝ).prod (volume : Measure Space)) c
    have e := hmp.setLIntegral_comp_preimage_emb (MeasurableEquiv.addRight c).measurableEmbedding
      (fun z => ‖f z‖ₑ) B
    have hsub : A ⊆ (fun z : ℝ × Space => z + c) ⁻¹' B := by
      rintro z ⟨⟨h1, h2⟩, h3⟩
      have hd := Nat.le_ceil |δ|
      have ht2 := abs_le.1 htd
      have hδ2 := abs_le.1 (le_refl |δ|)
      simp only [c, B, M, mem_preimage, mem_prod, mem_Icc, Prod.fst_add, Prod.snd_add, add_zero]
      push_cast
      exact ⟨⟨by linarith, by linarith⟩, h3⟩
    have hfun : ∀ z : ℝ × Space, ‖f (z + c)‖ₑ = ‖f (z.1 + t, z.2)‖ₑ := by
      intro z
      refine congrArg (fun w => ‖f w‖ₑ) (Prod.ext ?_ ?_) <;> simp [c]
    calc ∫⁻ z in A, ‖f (z.1 + t, z.2)‖ₑ ≤ ∫⁻ z in (fun z : ℝ × Space => z + c) ⁻¹' B, ‖f (z.1 + t, z.2)‖ₑ :=
          lintegral_mono_set hsub
      _ = ∫⁻ z in B, ‖f z‖ₑ := by
          simp_rw [← hfun]
          exact e
  have hsw : ∫⁻ z in A, ∫⁻ t in Ι (0 : ℝ) δ, ‖f (z.1 + t, z.2)‖ₑ =
      ∫⁻ t in Ι (0 : ℝ) δ, ∫⁻ z in A, ‖f (z.1 + t, z.2)‖ₑ := by
    refine lintegral_lintegral_swap ?_
    have h2 : AEMeasurable (fun p : (ℝ × Space) × ℝ => ‖f (p.1.1 + p.2, p.1.2)‖ₑ)
        ((volume : Measure (ℝ × Space)).prod (volume : Measure ℝ)) := hF.enorm
    rw [Measure.prod_restrict]
    exact h2.restrict
  unfold HasFiniteIntegral
  calc ∫⁻ z in A, ‖∫ t in (0 : ℝ)..δ, f (z.1 + t, z.2)‖ₑ
      ≤ ∫⁻ z in A, ∫⁻ t in Ι (0 : ℝ) δ, ‖f (z.1 + t, z.2)‖ₑ := by
        refine lintegral_mono fun z => ?_
        rw [← ofReal_norm, intervalIntegral.norm_intervalIntegral_eq, ofReal_norm]
        exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ t in Ι (0 : ℝ) δ, ∫⁻ z in A, ‖f (z.1 + t, z.2)‖ₑ := hsw
    _ ≤ ∫⁻ t in Ι (0 : ℝ) δ, ∫⁻ z in B, ‖f z‖ₑ := setLIntegral_mono' measurableSet_uIoc hin
    _ < ⊤ := by
        rw [lintegral_const, Measure.restrict_apply_univ]
        exact ENNReal.mul_lt_top hC ((measure_mono uIoc_subset_uIcc).trans_lt isCompact_uIcc.measure_lt_top)

theorem aestronglyMeasurable_rate {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation ∅ P v G H g) :
    AEStronglyMeasurable (fun z : ℝ × Space => transportRate P v G g z.1 z.2) volume := by
  have hwm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2 z.2) volume :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hv.measurable_gradient.prodMk measurable_snd.aestronglyMeasurable)
  unfold transportRate
  exact ((hv.measurable_derivative.sub (hv.measurable_velocity.const_smul (1 / 2 : ℝ))).sub
    (hwm.const_smul (1 / 2 : ℝ))).const_smul P

theorem integrableOn_transportDefect_strip {P R : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation ∅ P v G H g)
    (hloc : periodBallLIntegral R (fun σ y => ‖v σ y‖ ^ 2) < ⊤) (δ : ℝ) (N : ℕ) :
    IntegrableOn (transportDefect P δ v G g) (Icc (-(N : ℝ)) N ×ˢ Metric.closedBall (0 : Space) R) := by
  have h1 := integrableOn_shift_strip (f := fun z : ℝ × Space => v z.1 z.2) (integrableOn_velocity_strip hv hloc) δ N
  have h2 := integrableOn_velocity_strip hv hloc N
  have h3 := integrableOn_average_strip (f := fun z : ℝ × Space => transportRate P v G g z.1 z.2)
    (aestronglyMeasurable_rate hv) (integrableOn_rate_strip hv hloc) δ N
  exact (h1.sub h2).sub h3

private theorem integrable_smul_of_strips {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × Space → E} {R : ℝ}
    (hf : ∀ N : ℕ, IntegrableOn f (Icc (-(N : ℝ)) N ×ˢ Metric.closedBall (0 : Space) R))
    {c : ℝ × Space → ℝ} (hc : Continuous c) (hcs : HasCompactSupport c)
    (hs : tsupport c ⊆ univ ×ˢ Metric.closedBall (0 : Space) R) :
    Integrable (fun z => c z • f z) := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1
    (hcs.isCompact.image continuous_fst).isBounded
  have hK : IsCompact (Icc (-(⌈r⌉₊ : ℝ)) ⌈r⌉₊ ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hsub : tsupport c ⊆ Icc (-(⌈r⌉₊ : ℝ)) ⌈r⌉₊ ×ˢ Metric.closedBall (0 : Space) R := by
    intro z hz
    refine ⟨?_, (hs hz).2⟩
    have h1 := hr (mem_image_of_mem Prod.fst hz)
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le] at h1
    have h2 := Nat.le_ceil r
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have hI := (hf ⌈r⌉₊).continuousOn_smul hc.continuousOn hK
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 hI
  intro z hz
  by_contra hzK
  have h0 : c z = 0 := image_eq_zero_of_notMem_tsupport fun h => hzK (hsub h)
  exact hz (by simp [h0])

private theorem deriv_time_eq {Ψ : ℝ × Space → ℝ} (hΨ : Differentiable ℝ Ψ) (z : ℝ × Space) :
    deriv (fun s => Ψ (s, z.2)) z.1 = fderiv ℝ Ψ z ((1 : ℝ), (0 : Space)) := by
  have h : HasDerivAt (fun s : ℝ => (s, z.2)) ((1 : ℝ), (0 : Space)) z.1 :=
    (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
  exact ((hΨ (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.1 h).deriv

private theorem fderiv_space_eq {Ψ : ℝ × Space → ℝ} (hΨ : Differentiable ℝ Ψ) (s : ℝ) (y w : Space) :
    fderiv ℝ (fun y => Ψ (s, y)) y w = fderiv ℝ Ψ (s, y) ((0 : ℝ), w) := by
  have h := (hasFDerivAt_const (𝕜 := ℝ) s y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y)
  have e := ((hΨ (s, y)).hasFDerivAt.comp y h).fderiv
  simp only [Function.comp_def] at e
  rw [e]
  rfl

private theorem integrable_fderiv_smul_of_strips {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × Space → E} {R : ℝ}
    (hf : ∀ N : ℕ, IntegrableOn f (Icc (-(N : ℝ)) N ×ˢ Metric.closedBall (0 : Space) R))
    {Ψ : ℝ × Space → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hc : HasCompactSupport Ψ)
    (hs : tsupport Ψ ⊆ univ ×ˢ Metric.ball (0 : Space) R)
    {w : ℝ × Space → ℝ × Space} (hw : Continuous w) :
    Integrable (fun z => fderiv ℝ Ψ z (w z) • f z) := by
  have hcont : Continuous (fun z => fderiv ℝ Ψ z (w z)) :=
    (hΨ.continuous_fderiv (by simp)).clm_apply hw
  have hsupp : Function.support (fun z => fderiv ℝ Ψ z (w z)) ⊆ tsupport Ψ := by
    intro z hz
    by_contra h
    exact hz (by simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) h])
  have hts : tsupport (fun z => fderiv ℝ Ψ z (w z)) ⊆ tsupport Ψ :=
    closure_minimal hsupp (isClosed_tsupport _)
  exact integrable_smul_of_strips hf hcont (hc.mono' hsupp)
    (hts.trans (hs.trans (prod_mono subset_rfl Metric.ball_subset_closedBall)))

private theorem integrable_test_smul_of_strips {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × Space → E} {R : ℝ}
    (hf : ∀ N : ℕ, IntegrableOn f (Icc (-(N : ℝ)) N ×ˢ Metric.closedBall (0 : Space) R))
    {Ψ : ℝ × Space → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hc : HasCompactSupport Ψ)
    (hs : tsupport Ψ ⊆ univ ×ˢ Metric.ball (0 : Space) R) :
    Integrable (fun z => Ψ z • f z) :=
  integrable_smul_of_strips hf hΨ.continuous hc
    (hs.trans (prod_mono subset_rfl Metric.ball_subset_closedBall))

private theorem clm_apply_eq_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Space →L[ℝ] F)
    (y : Space) : L y = ∑ j : Fin 3, y j • L (unitVector j) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr y]
  simp [unitVector, EuclideanSpace.basisFun_apply, map_sum, map_smul]

private theorem eq_of_inner_unitVector {x y : Space}
    (h : ∀ k : Fin 3, inner ℝ (unitVector k) x = inner ℝ (unitVector k) y) : x = y := by
  ext k
  have := h k
  simpa [unitVector, EuclideanSpace.inner_single_left] using this


private theorem slice_test {Ψ : ℝ × Space → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hc : HasCompactSupport Ψ) (σ : ℝ) :
    ContDiff ℝ ∞ (fun y => Ψ (σ, y)) ∧ HasCompactSupport (fun y => Ψ (σ, y)) := by
  refine ⟨hΨ.comp (contDiff_const.prodMk contDiff_id), ?_⟩
  refine HasCompactSupport.intro (hc.isCompact.image continuous_snd) fun y hy => ?_
  by_contra h
  exact hy ⟨(σ, y), subset_tsupport _ h, rfl⟩

private theorem fderiv_apply_compact {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    {w : Space → Space} (hw : Continuous w) :
    Continuous (fun y => fderiv ℝ ψ y (w y)) ∧ HasCompactSupport (fun y => fderiv ℝ ψ y (w y)) := by
  refine ⟨(hψ.continuous_fderiv (by simp)).clm_apply hw, hc.mono' fun y hy => ?_⟩
  by_contra h
  exact hy (by simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) h])

private theorem slice_radial_identity {f : Space → Space} {F : Space → (Space →L[ℝ] Space)}
    (hw : IsWeakGradient f F) {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    ∫ y, fderiv ℝ ψ y y • f y = -(∫ y, ψ y • F y y) - (3 : ℝ) • ∫ y, ψ y • f y := by
  obtain ⟨hf, hF, hweak⟩ := hw
  have hdψ : ∀ y, DifferentiableAt ℝ ψ y := fun y => (hψ.differentiable (by simp)) y
  have hcoord : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y : Space => y j) := fun j =>
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff
  have hcs : ∀ j : Fin 3, HasCompactSupport (fun y : Space => y j * ψ y) := fun j =>
    hc.mul_left (f := fun y : Space => y j)
  have htest : ∀ j : Fin 3, IsTestFunction (fun y : Space => y j * ψ y) := fun j =>
    ⟨(hcoord j).mul hψ, hcs j⟩
  have hder : ∀ (j : Fin 3) (y : Space), fderiv ℝ (fun y : Space => y j * ψ y) y (unitVector j) =
      y j * fderiv ℝ ψ y (unitVector j) + ψ y := by
    intro j y
    rw [show (fun y : Space => y j * ψ y) = (fun y : Space => y j) * ψ from rfl,
      fderiv_mul ((hcoord j).differentiable (by simp) y) (hdψ y)]
    have : fderiv ℝ (fun y : Space => y j) y = EuclideanSpace.proj (𝕜 := ℝ) j :=
      (EuclideanSpace.proj (𝕜 := ℝ) j).fderiv
    simp [this, unitVector]
  have hIF : ∀ j : Fin 3, Integrable (fun y => (y j * ψ y) • F y (unitVector j)) := by
    intro j
    have := (hF.integrable_smul_left_of_hasCompactSupport ((hcoord j).continuous.mul hψ.continuous)
      (hcs j)).apply_continuousLinearMap (unitVector j)
    simpa using this
  have hIψ : Integrable (fun y => ψ y • f y) :=
    hf.integrable_smul_left_of_hasCompactSupport hψ.continuous hc
  have hIf : ∀ j : Fin 3, Integrable (fun y => (y j * fderiv ℝ ψ y (unitVector j) + ψ y) • f y) := by
    intro j
    obtain ⟨h1, h2⟩ := fderiv_apply_compact hψ hc (w := fun _ => unitVector j) continuous_const
    have hI1 := hf.integrable_smul_left_of_hasCompactSupport ((hcoord j).continuous.mul h1)
      (h2.mul_left (f := fun y : Space => y j))
    refine (hI1.add hIψ).congr (Eventually.of_forall fun y => ?_)
    simp only [add_smul, Pi.add_apply, Pi.mul_apply]
  obtain ⟨hD1, hD2⟩ := fderiv_apply_compact hψ hc (w := fun y => y) continuous_id
  have hID : Integrable (fun y => fderiv ℝ ψ y y • f y) :=
    hf.integrable_smul_left_of_hasCompactSupport hD1 hD2
  have hsum : ∑ j : Fin 3, (∫ y, (y j * ψ y) • F y (unitVector j)) =
      -∑ j : Fin 3, ∫ y, (y j * fderiv ℝ ψ y (unitVector j) + ψ y) • f y := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hweak _ (htest j) j]
    simp only [hder]
  rw [← integral_finsetSum _ fun j _ => hIF j, ← integral_finsetSum _ fun j _ => hIf j] at hsum
  have e1 : ∀ y : Space, ∑ j : Fin 3, (y j * ψ y) • F y (unitVector j) = ψ y • F y y := by
    intro y
    rw [clm_apply_eq_sum (F y) y, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm, mul_smul]
  have e2 : ∀ y : Space, ∑ j : Fin 3, (y j * fderiv ℝ ψ y (unitVector j) + ψ y) • f y =
      fderiv ℝ ψ y y • f y + (3 : ℝ) • (ψ y • f y) := by
    intro y
    rw [← Finset.sum_smul, Finset.sum_add_distrib, clm_apply_eq_sum (fderiv ℝ ψ y) y]
    simp only [smul_eq_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      add_smul, mul_smul]
    norm_num
  simp only [e1, e2] at hsum
  have hI3 : Integrable (fun y => (3 : ℝ) • (ψ y • f y)) := hIψ.smul (3 : ℝ)
  rw [integral_add hID hI3, integral_smul] at hsum
  rw [hsum]
  module


private theorem integral_prod_volume {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × Space → E) (hf : Integrable f) : ∫ z, f z = ∫ σ, ∫ y, f (σ, y) := by
  rw [Measure.volume_eq_prod] at hf ⊢
  exact integral_prod f hf

private theorem integrable_slice_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × Space → E} (hf : Integrable f) : Integrable (fun σ => ∫ y, f (σ, y)) := by
  rw [Measure.volume_eq_prod] at hf
  exact hf.integral_prod_left

private theorem isAddLeftInvariant_volume_prod : (volume : Measure (ℝ × Space)).IsAddLeftInvariant := by
  rw [Measure.volume_eq_prod]
  infer_instance

private theorem exists_time_bound_of_support {Φ : ℝ × Space → ℝ} {R : ℝ} (hc : HasCompactSupport Φ)
    (hs : tsupport Φ ⊆ univ ×ˢ Metric.ball (0 : Space) R) :
    ∃ N : ℕ, ∀ z : ℝ × Space, Φ z ≠ 0 → |z.1| ≤ N ∧ z.2 ∈ Metric.closedBall (0 : Space) R := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1
    (hc.isCompact.image continuous_fst).isBounded
  refine ⟨⌈r⌉₊, fun z hz => ?_⟩
  have hzt : z ∈ tsupport Φ := subset_tsupport _ hz
  have h1 := hr (mem_image_of_mem Prod.fst hzt)
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
  exact ⟨h1.trans (Nat.le_ceil r), Metric.ball_subset_closedBall (hs hzt).2⟩

private theorem shifted_support_subset {Φ : ℝ × Space → ℝ} {R : ℝ} {N : ℕ}
    (hN : ∀ z : ℝ × Space, Φ z ≠ 0 → |z.1| ≤ N ∧ z.2 ∈ Metric.closedBall (0 : Space) R)
    {t T : ℝ} (ht : |t| ≤ T) (z : ℝ × Space) (hz : Φ (z.1 - t, z.2) ≠ 0) :
    z ∈ Icc (-((N + ⌈T⌉₊ : ℕ) : ℝ)) ((N + ⌈T⌉₊ : ℕ) : ℝ) ×ˢ Metric.closedBall (0 : Space) R := by
  obtain ⟨h1, h2⟩ := hN _ hz
  have hT := Nat.le_ceil T
  have a1 := abs_le.1 h1
  have a2 := abs_le.1 ht
  simp only at a1 h2
  refine ⟨⟨?_, ?_⟩, h2⟩ <;> push_cast <;> linarith [a1.1, a1.2, a2.1, a2.2]

private theorem integrable_smul_of_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : ℝ × Space → ℝ} {f : ℝ × Space → E} {R : ℝ} {N : ℕ} (hψ : Continuous ψ)
    (hsupp : ∀ z, ψ z ≠ 0 → z ∈ Icc (-(N : ℝ)) N ×ˢ Metric.closedBall (0 : Space) R)
    (hf : IntegrableOn f (Icc (-(N : ℝ)) N ×ˢ Metric.closedBall (0 : Space) R)) :
    Integrable (fun z => ψ z • f z) := by
  have hK : IsCompact (Icc (-(N : ℝ)) N ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  refine (integrableOn_iff_integrable_of_support_subset fun z hz => ?_).1
    (hf.continuousOn_smul hψ.continuousOn hK)
  refine hsupp z fun h0 => hz ?_
  simp [h0]

private theorem integral_smul_average {f : ℝ × Space → Space} {Φ : ℝ × Space → ℝ} {R : ℝ}
    (hΦ : Continuous Φ) (hc : HasCompactSupport Φ)
    (hs : tsupport Φ ⊆ univ ×ˢ Metric.ball (0 : Space) R) (hm : AEStronglyMeasurable f volume)
    (hf : ∀ N : ℕ, IntegrableOn f (Icc (-(N : ℝ)) N ×ˢ Metric.closedBall (0 : Space) R)) (δ : ℝ) :
    ∫ z : ℝ × Space, Φ z • ∫ t in (0 : ℝ)..δ, f (z.1 + t, z.2) =
      ∫ z : ℝ × Space, shiftIntegral δ Φ z • f z := by
  obtain ⟨N, hN⟩ := exists_time_bound_of_support hc hs
  obtain ⟨C, hC⟩ := hΦ.bounded_above_of_compact_support hc
  set ν : Measure ℝ := volume.restrict (Ι (0 : ℝ) δ)
  set μ : Measure (ℝ × Space) := volume
  have : IsFiniteMeasure ν := ⟨by
    simp only [ν, Measure.restrict_apply_univ]
    exact (measure_mono uIoc_subset_uIcc).trans_lt isCompact_uIcc.measure_lt_top⟩
  set M : ℕ := N + ⌈|δ|⌉₊
  set K := Icc (-(M : ℝ)) M ×ˢ Metric.closedBall (0 : Space) R
  have hKm : MeasurableSet K := measurableSet_Icc.prod Metric.isClosed_closedBall.measurableSet
  set H' : ℝ × (ℝ × Space) → Space := fun p => Φ (p.2.1 - p.1, p.2.2) • f p.2
  set T : ℝ × (ℝ × Space) → ℝ × (ℝ × Space) := fun p => (p.1, (p.2.1 + p.1, p.2.2))
  have hLI : μ.IsAddLeftInvariant := isAddLeftInvariant_volume_prod
  have hT : MeasurePreserving T (ν.prod μ) (ν.prod μ) := by
    refine MeasurePreserving.skew_product (f := id) (g := fun (t : ℝ) (z : ℝ × Space) => (z.1 + t, z.2))
      (MeasurePreserving.id ν) (by fun_prop) (Eventually.of_forall fun t => ?_)
    have e : (fun z : ℝ × Space => (z.1 + t, z.2)) = fun z => ((t, (0 : Space)) : ℝ × Space) + z := by
      funext z
      refine Prod.ext ?_ ?_ <;> simp [add_comm]
    rw [e]
    exact map_add_left_eq_self μ _
  have hH'm : AEStronglyMeasurable H' (ν.prod μ) := by
    have h1 : Continuous fun p : ℝ × (ℝ × Space) => Φ (p.2.1 - p.1, p.2.2) := by fun_prop
    exact h1.aestronglyMeasurable.smul (hm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have hH' : Integrable H' (ν.prod μ) := by
    have hg : Integrable (fun z : ℝ × Space => C * ‖K.indicator f z‖) μ :=
      ((hf M).integrable_indicator hKm).norm.const_mul C
    refine ((integrable_const (1 : ℝ)).smul_prod hg).mono' hH'm ?_
    have hae : ∀ᵐ p ∂(ν.prod μ), p.1 ∈ Ι (0 : ℝ) δ :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_uIoc)
    filter_upwards [hae] with p hp
    simp only [H', one_smul]
    by_cases h0 : Φ (p.2.1 - p.1, p.2.2) = 0
    · rw [h0, zero_smul, norm_zero]
      exact mul_nonneg ((norm_nonneg _).trans (hC 0)) (norm_nonneg _)
    · have hpK := shifted_support_subset hN (abs_le_of_mem_uIoc hp) p.2 h0
      rw [indicator_of_mem hpK, norm_smul]
      exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  have hcomp : Integrable (H' ∘ T) (ν.prod μ) := (hT.integrable_comp hH'm).2 hH'
  have hint : ∫ p, (H' ∘ T) p ∂(ν.prod μ) = ∫ p, H' p ∂(ν.prod μ) := by
    have e := integral_map (μ := ν.prod μ) hT.measurable.aemeasurable (f := H') (by rw [hT.map_eq]; exact hH'm)
    rw [hT.map_eq] at e
    exact e.symm
  have hL : ∀ z : ℝ × Space, Φ z • ∫ t in (0 : ℝ)..δ, f (z.1 + t, z.2) =
      (if (0 : ℝ) ≤ δ then 1 else -1 : ℝ) • ∫ t, (H' ∘ T) (t, z) ∂ν := by
    intro z
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, smul_comm, ← integral_smul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [H', T, Function.comp, add_sub_cancel_right, Prod.mk.eta]
  have hR : ∀ z : ℝ × Space, shiftIntegral δ Φ z • f z =
      (if (0 : ℝ) ≤ δ then 1 else -1 : ℝ) • ∫ t, H' (t, z) ∂ν := by
    intro z
    have e : ∀ t : ℝ, Φ (z - t • ((1 : ℝ), (0 : Space))) = Φ (z.1 - t, z.2) := by
      intro t
      congr 1
      refine Prod.ext ?_ ?_ <;> simp
    unfold shiftIntegral
    simp only [e, H']
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_smul_const, smul_assoc]
  simp only [hL, hR]
  rw [integral_smul, integral_smul, ← integral_prod_symm _ hcomp, ← integral_prod_symm _ hH', hint]

theorem weak_time_derivative {P R : ℝ} (hP : 0 < P) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation ∅ P v G H g)
    (hloc : periodBallLIntegral R (fun σ y => ‖v σ y‖ ^ 2) < ⊤) {Ψ : ℝ × Space → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hc : HasCompactSupport Ψ)
    (hs : tsupport Ψ ⊆ univ ×ˢ Metric.ball (0 : Space) R) :
    (∫ z : ℝ × Space, deriv (fun s => Ψ (s, z.2)) z.1 • v z.1 z.2) +
      ∫ z : ℝ × Space, Ψ z • transportRate P v G g z.1 z.2 = 0 := by
  have hd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  have hV := integrableOn_velocity_strip hv hloc
  have hGs := integrableOn_derivative_strip hv (R := R)
  have hWs := integrableOn_gradient_apply_strip hv (R := R)
  have ea : ∀ z : ℝ × Space, deriv (fun s => Ψ (s, z.2)) z.1 = fderiv ℝ Ψ z ((1 : ℝ), (0 : Space)) :=
    deriv_time_eq hd
  have eb : ∀ z : ℝ × Space, fderiv ℝ (fun y => Ψ (z.1, y)) z.2 z.2 = fderiv ℝ Ψ z ((0 : ℝ), z.2) :=
    fun z => fderiv_space_eq hd z.1 z.2 z.2
  have hIa : Integrable (fun z : ℝ × Space => deriv (fun s => Ψ (s, z.2)) z.1 • v z.1 z.2) := by
    simp only [ea]
    exact integrable_fderiv_smul_of_strips hV hΨ hc hs (w := fun _ => ((1 : ℝ), (0 : Space)))
      continuous_const
  have hIb : Integrable (fun z : ℝ × Space => fderiv ℝ (fun y => Ψ (z.1, y)) z.2 z.2 • v z.1 z.2) := by
    simp only [eb]
    exact integrable_fderiv_smul_of_strips hV hΨ hc hs (w := fun z => ((0 : ℝ), z.2))
      (continuous_const.prodMk continuous_snd)
  have hIv : Integrable (fun z : ℝ × Space => Ψ z • v z.1 z.2) := integrable_test_smul_of_strips hV hΨ hc hs
  have hIg : Integrable (fun z : ℝ × Space => Ψ z • g z.1 z.2) := integrable_test_smul_of_strips hGs hΨ hc hs
  have hIw : Integrable (fun z : ℝ × Space => Ψ z • G z.1 z.2 z.2) :=
    integrable_test_smul_of_strips hWs hΨ hc hs
  have hrad : ∫ z : ℝ × Space, fderiv ℝ (fun y => Ψ (z.1, y)) z.2 z.2 • v z.1 z.2 =
      -(∫ z : ℝ × Space, Ψ z • G z.1 z.2 z.2) - (3 : ℝ) • ∫ z : ℝ × Space, Ψ z • v z.1 z.2 := by
    rw [integral_prod_volume _ hIb, integral_prod_volume _ hIw, integral_prod_volume _ hIv]
    dsimp only
    have hA : Integrable (fun σ => -∫ y, Ψ (σ, y) • G σ y y) := (integrable_slice_integral hIw).neg
    have hB : Integrable (fun σ => (3 : ℝ) • ∫ y, Ψ (σ, y) • v σ y) :=
      (integrable_slice_integral hIv).smul (3 : ℝ)
    rw [← integral_neg, ← integral_smul, ← integral_sub hA hB]
    refine integral_congr_ae ?_
    filter_upwards [hv.weak_gradient] with σ hσ
    obtain ⟨h1, h2⟩ := slice_test hΨ hc σ
    exact slice_radial_identity hσ h1 h2
  have hdt : ∀ z : ℝ × Space, DifferentiableAt ℝ (fun s => Ψ (s, z.2)) z.1 := fun z =>
    (hd.comp (differentiable_id.prodMk (differentiable_const _))) z.1
  have hdy : ∀ z : ℝ × Space, DifferentiableAt ℝ (fun y => Ψ (z.1, y)) z.2 := fun z =>
    (hd.comp ((differentiable_const _).prodMk differentiable_id)) z.2
  have htv : ∫ z : ℝ × Space, (-(1 / P) * deriv (fun s => Ψ (s, z.2)) z.1 - Ψ z -
      (1 / 2) * fderiv ℝ (fun y => Ψ (z.1, y)) z.2 z.2) • v z.1 z.2 = ∫ z : ℝ × Space, Ψ z • g z.1 z.2 := by
    have hI1 : Integrable (fun z : ℝ × Space => (-(1 / P) * deriv (fun s => Ψ (s, z.2)) z.1 - Ψ z -
        (1 / 2) * fderiv ℝ (fun y => Ψ (z.1, y)) z.2 z.2) • v z.1 z.2) := by
      refine (((hIa.smul (-(1 / P))).sub hIv).sub (hIb.smul (1 / 2 : ℝ))).congr
        (Eventually.of_forall fun z => ?_)
      simp only [Pi.sub_apply, Pi.smul_apply, sub_smul, mul_smul]
    refine eq_of_inner_unitVector fun k => ?_
    rw [← integral_inner hI1, ← integral_inner hIg]
    have hφ : IsSpaceTimeTestVector (fun s y => Ψ (s, y) • unitVector k) := by
      refine ⟨hΨ.smul contDiff_const, hc.mono fun z hz => ?_⟩
      by_contra h0
      exact hz (by simp [Function.notMem_support.1 h0])
    have ht := hv.transport _ hφ
    refine (integral_congr_ae (Eventually.of_forall fun z => ?_)).trans
      (ht.trans (integral_congr_ae (Eventually.of_forall fun z => ?_)))
    · rw [deriv_smul_const (hdt z), fderiv_smul_const (hdy z)]
      simp only [ContinuousLinearMap.smulRight_apply, inner_sub_right, real_inner_smul_right,
        inner_neg_right, neg_smul]
      rw [real_inner_comm (v z.1 z.2) (unitVector k)]
      ring
    · simp only [real_inner_smul_right, real_inner_comm]
  have hexp : ∫ z : ℝ × Space, (-(1 / P) * deriv (fun s => Ψ (s, z.2)) z.1 - Ψ z -
      (1 / 2) * fderiv ℝ (fun y => Ψ (z.1, y)) z.2 z.2) • v z.1 z.2 =
      (-(1 / P)) • (∫ z : ℝ × Space, deriv (fun s => Ψ (s, z.2)) z.1 • v z.1 z.2) -
        (∫ z : ℝ × Space, Ψ z • v z.1 z.2) -
        (1 / 2 : ℝ) • ∫ z : ℝ × Space, fderiv ℝ (fun y => Ψ (z.1, y)) z.2 z.2 • v z.1 z.2 := by
    have hA : Integrable (fun z : ℝ × Space => (-(1 / P)) • (deriv (fun s => Ψ (s, z.2)) z.1 • v z.1 z.2)) :=
      hIa.smul (-(1 / P))
    have hB : Integrable (fun z : ℝ × Space => (1 / 2 : ℝ) • (fderiv ℝ (fun y => Ψ (z.1, y)) z.2 z.2 • v z.1 z.2)) :=
      hIb.smul (1 / 2 : ℝ)
    have hAB : Integrable (fun z : ℝ × Space => (-(1 / P)) • (deriv (fun s => Ψ (s, z.2)) z.1 • v z.1 z.2) -
        Ψ z • v z.1 z.2) := hA.sub hIv
    rw [← integral_smul, ← integral_smul, ← integral_sub hA hIv, ← integral_sub hAB hB]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sub_smul, mul_smul]
  have hrate : ∫ z : ℝ × Space, Ψ z • transportRate P v G g z.1 z.2 =
      P • (∫ z : ℝ × Space, Ψ z • g z.1 z.2) - (P / 2) • (∫ z : ℝ × Space, Ψ z • v z.1 z.2) -
        (P / 2) • ∫ z : ℝ × Space, Ψ z • G z.1 z.2 z.2 := by
    have hA : Integrable (fun z : ℝ × Space => P • (Ψ z • g z.1 z.2)) := hIg.smul P
    have hB : Integrable (fun z : ℝ × Space => (P / 2) • (Ψ z • v z.1 z.2)) := hIv.smul (P / 2)
    have hC : Integrable (fun z : ℝ × Space => (P / 2) • (Ψ z • G z.1 z.2 z.2)) := hIw.smul (P / 2)
    have hAB : Integrable (fun z : ℝ × Space => P • (Ψ z • g z.1 z.2) - (P / 2) • (Ψ z • v z.1 z.2)) :=
      hA.sub hB
    rw [← integral_smul, ← integral_smul, ← integral_smul, ← integral_sub hA hB, ← integral_sub hAB hC]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [transportRate]
    module
  rw [hexp, hrad] at htv
  rw [hrate, ← htv]
  have e : P * (1 / P) = 1 := by field_simp
  simp only [smul_sub, smul_neg, smul_smul, neg_smul, e, one_smul]
  module


theorem transportDefect_locallyIntegrableOn {P R : ℝ} (_hP : 0 < P) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation ∅ P v G H g)
    (hloc : periodBallLIntegral R (fun σ y => ‖v σ y‖ ^ 2) < ⊤) (δ : ℝ) :
    LocallyIntegrableOn (transportDefect P δ v G g) (univ ×ˢ Metric.ball (0 : Space) R) volume := by
  exact locallyIntegrableOn_of_strips (integrableOn_transportDefect_strip hv hloc δ)

theorem integral_smul_transportDefect {P R : ℝ} (_hP : 0 < P) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation ∅ P v G H g)
    (hloc : periodBallLIntegral R (fun σ y => ‖v σ y‖ ^ 2) < ⊤) (δ : ℝ) {Φ : ℝ × Space → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hc : HasCompactSupport Φ)
    (hs : tsupport Φ ⊆ univ ×ˢ Metric.ball (0 : Space) R) :
    ∫ z : ℝ × Space, Φ z • transportDefect P δ v G g z =
      -((∫ z : ℝ × Space, deriv (fun s => shiftIntegral δ Φ (s, z.2)) z.1 • v z.1 z.2) +
        ∫ z : ℝ × Space, shiftIntegral δ Φ z • transportRate P v G g z.1 z.2) := by
  have hΦc : Continuous Φ := hΦ.continuous
  obtain ⟨N, hN⟩ := exists_time_bound_of_support hc hs
  have hsupp0 : ∀ z : ℝ × Space, Φ z ≠ 0 → z ∈ Icc (-(N : ℝ)) N ×ˢ Metric.closedBall (0 : Space) R :=
    fun z hz => ⟨abs_le.1 (hN z hz).1, (hN z hz).2⟩
  have hsuppδ : ∀ z : ℝ × Space, Φ (z.1 - δ, z.2) ≠ 0 →
      z ∈ Icc (-((N + ⌈|δ|⌉₊ : ℕ) : ℝ)) ((N + ⌈|δ|⌉₊ : ℕ) : ℝ) ×ˢ Metric.closedBall (0 : Space) R :=
    shifted_support_subset hN le_rfl
  have hvs := integrableOn_velocity_strip hv hloc
  have I1 : Integrable (fun z : ℝ × Space => Φ z • v (z.1 + δ) z.2) :=
    integrable_smul_of_support hΦc hsupp0
      (integrableOn_shift_strip (f := fun z : ℝ × Space => v z.1 z.2) hvs δ N)
  have I2 : Integrable (fun z : ℝ × Space => Φ z • v z.1 z.2) :=
    integrable_smul_of_support hΦc hsupp0 (hvs N)
  have I3 : Integrable (fun z : ℝ × Space => Φ z • ∫ t in (0 : ℝ)..δ, transportRate P v G g (z.1 + t) z.2) :=
    integrable_smul_of_support hΦc hsupp0
      (integrableOn_average_strip (f := fun z : ℝ × Space => transportRate P v G g z.1 z.2)
        (aestronglyMeasurable_rate hv) (integrableOn_rate_strip hv hloc) δ N)
  have I4 : Integrable (fun z : ℝ × Space => Φ (z.1 - δ, z.2) • v z.1 z.2) :=
    integrable_smul_of_support (hΦc.comp (by fun_prop)) hsuppδ (hvs _)
  have hsplit : ∫ z : ℝ × Space, Φ z • transportDefect P δ v G g z =
      (∫ z : ℝ × Space, Φ z • v (z.1 + δ) z.2) - (∫ z : ℝ × Space, Φ z • v z.1 z.2) -
        ∫ z : ℝ × Space, Φ z • ∫ t in (0 : ℝ)..δ, transportRate P v G g (z.1 + t) z.2 := by
    refine (integral_congr_ae ?_).trans ((integral_sub (I1.sub I2) I3).trans ?_)
    · refine Eventually.of_forall fun z => ?_
      simp only [transportDefect, smul_sub, Pi.sub_apply]
    · congr 1
      exact integral_sub I1 I2
  have hLI := isAddLeftInvariant_volume_prod
  have hshift : ∫ z : ℝ × Space, Φ z • v (z.1 + δ) z.2 = ∫ z : ℝ × Space, Φ (z.1 - δ, z.2) • v z.1 z.2 := by
    rw [← integral_add_left_eq_self (fun z : ℝ × Space => Φ (z.1 - δ, z.2) • v z.1 z.2) ((δ, (0 : Space)) : ℝ × Space)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Prod.fst_add, Prod.snd_add, zero_add, add_comm δ z.1, add_sub_cancel_right, Prod.mk.eta]
  have hderiv : ∀ z : ℝ × Space, deriv (fun s => shiftIntegral δ Φ (s, z.2)) z.1 • v z.1 z.2 =
      Φ z • v z.1 z.2 - Φ (z.1 - δ, z.2) • v z.1 z.2 := by
    intro z
    rw [(hasDerivAt_shiftIntegral hΦc z.1 z.2).deriv, Prod.mk.eta, sub_smul]
  have hD : ∫ z : ℝ × Space, deriv (fun s => shiftIntegral δ Φ (s, z.2)) z.1 • v z.1 z.2 =
      (∫ z : ℝ × Space, Φ z • v z.1 z.2) - ∫ z : ℝ × Space, Φ (z.1 - δ, z.2) • v z.1 z.2 := by
    simp only [hderiv]
    exact integral_sub I2 I4
  have hA := integral_smul_average (f := fun z : ℝ × Space => transportRate P v G g z.1 z.2) hΦc hc hs
    (aestronglyMeasurable_rate hv) (integrableOn_rate_strip hv hloc) δ
  simp only at hA
  rw [hsplit, hshift, hD, hA]
  abel


theorem transport_representation {P R : ℝ} (hP : 0 < P) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation ∅ P v G H g)
    (hloc : periodBallLIntegral R (fun σ y => ‖v σ y‖ ^ 2) < ⊤) (δ : ℝ) :
    ∀ᵐ z : ℝ × Space, z.2 ∈ Metric.closedBall (0 : Space) R →
      v (z.1 + δ) z.2 - v z.1 z.2 = ∫ t in (0 : ℝ)..δ, transportRate P v G g (z.1 + t) z.2 := by
  have hU : IsOpen ((univ : Set ℝ) ×ˢ Metric.ball (0 : Space) R) := isOpen_univ.prod Metric.isOpen_ball
  have hD := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (transportDefect_locallyIntegrableOn hP hv hloc δ) fun Φ hΦ hc hs => by
      rw [integral_smul_transportDefect hP hv hloc δ hΦ hc hs]
      obtain ⟨h1, h2, h3⟩ := shiftIntegral_test (δ := δ) hΦ hc hs
      rw [weak_time_derivative hP hv hloc h1 h2 h3, neg_zero]
  have hS0 : (volume : Measure (ℝ × Space)) ((univ : Set ℝ) ×ˢ Metric.sphere (0 : Space) R) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.addHaar_sphere (volume : Measure Space), mul_zero]
  filter_upwards [hD, measure_eq_zero_iff_ae_notMem.1 hS0] with z hz hzs hzB
  have hzU : z ∈ (univ : Set ℝ) ×ˢ Metric.ball (0 : Space) R := by
    refine ⟨mem_univ _, ?_⟩
    rw [← Metric.ball_union_sphere] at hzB
    rcases hzB with h | h
    · exact h
    · exact absurd ⟨mem_univ _, h⟩ hzs
  exact sub_eq_zero.1 (hz hzU)

end Internal.TimeModulus

end Breakdown.Cert
