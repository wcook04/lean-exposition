import Breakdown.Cert.Nodes
import Breakdown.Cert.ProjectionSpec
import Breakdown.Cert.PeriodIntegral
import Breakdown.Cert.JointRepresentative

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.TestPairing

variable {φ : ℝ → Space → Space}

theorem exists_bound (hc : HasCompactSupport (fun z : ℝ × Space => φ z.1 z.2)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ s y, φ s y ≠ 0 → |s| ≤ R ∧ ‖y‖ ≤ R := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hc.isCompact.isBounded
  refine ⟨max R 0, le_max_right _ _, fun s y h => ?_⟩
  have hz : ‖((s, y) : ℝ × Space)‖ ≤ R := hR _ (subset_tsupport _ h)
  have h1 := norm_fst_le ((s, y) : ℝ × Space)
  have h2 := norm_snd_le ((s, y) : ℝ × Space)
  refine ⟨?_, ?_⟩
  · have h3 : ‖s‖ ≤ R := h1.trans hz
    rw [Real.norm_eq_abs] at h3
    exact h3.trans (le_max_left _ _)
  · exact (h2.trans hz).trans (le_max_left _ _)

theorem slice_contDiff (hs : ContDiff ℝ ∞ (fun z : ℝ × Space => φ z.1 z.2)) (s : ℝ) :
    ContDiff ℝ ∞ (φ s) :=
  hs.comp (contDiff_const.prodMk contDiff_id)

theorem slice_eq_zero {R : ℝ} (hR : ∀ s y, φ s y ≠ 0 → |s| ≤ R ∧ ‖y‖ ≤ R) {s : ℝ} {y : Space}
    (h : R < |s| ∨ R < ‖y‖) : φ s y = 0 := by
  by_contra hne
  have h1 := hR s y hne
  rcases h with h | h
  · linarith [h1.1]
  · linarith [h1.2]

theorem slice_hasCompactSupport {R : ℝ} (hR : ∀ s y, φ s y ≠ 0 → |s| ≤ R ∧ ‖y‖ ≤ R) (s : ℝ) :
    HasCompactSupport (φ s) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) fun y hy =>
    slice_eq_zero hR (Or.inr (by simpa using hy))

theorem slice_memLp (hs : ContDiff ℝ ∞ (fun z : ℝ × Space => φ z.1 z.2)) {R : ℝ}
    (hR : ∀ s y, φ s y ≠ 0 → |s| ≤ R ∧ ‖y‖ ≤ R) (s : ℝ) : MemLp (φ s) 2 :=
  (slice_contDiff hs s).continuous.memLp_of_hasCompactSupport (slice_hasCompactSupport hR s)

theorem periodize_eq_sum {R : ℝ} (hR : ∀ s y, φ s y ≠ 0 → |s| ≤ R ∧ ‖y‖ ≤ R) {S : ℝ} {M : ℕ}
    (hM : R + S < M) {σ : ℝ} (hσ : |σ| ≤ S) (y : Space) :
    periodize φ σ y = ∑ k ∈ Finset.range (2 * M), φ (σ + ((k : ℝ) - M)) y := by
  have hinj : Set.InjOn (fun k : ℕ => (k : ℤ) - M) ↑(Finset.range (2 * M)) := by
    intro a _ b _ h
    simp only at h
    omega
  rw [periodize, tsum_eq_sum (s := (Finset.range (2 * M)).image fun k : ℕ => (k : ℤ) - M),
    Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  · intro n hn
    by_contra hne
    have hb := (hR _ _ hne).1
    rw [abs_le] at hb hσ
    have h1 : -(M : ℝ) ≤ n := by linarith
    have h2 : (n : ℝ) < M := by linarith
    have h1' : -(M : ℤ) ≤ n := by exact_mod_cast h1
    have h2' : n < (M : ℤ) := by exact_mod_cast h2
    apply hn
    rw [Finset.mem_image]
    exact ⟨(n + M).toNat, by rw [Finset.mem_range]; omega, by omega⟩

theorem periodize_periodic : IsTimePeriodic (periodize φ) := by
  intro σ y
  have h := (Equiv.addRight (1 : ℤ)).tsum_eq (fun n : ℤ => φ (σ + n) y)
  simp only [periodize]
  rw [← h]
  refine tsum_congr fun n => ?_
  rw [show σ + 1 + (n : ℝ) = σ + (((Equiv.addRight (1 : ℤ)) n : ℤ) : ℝ) by
    simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one]; ring]

theorem periodize_continuous (hs : ContDiff ℝ ∞ (fun z : ℝ × Space => φ z.1 z.2)) {R : ℝ}
    (hR : ∀ s y, φ s y ≠ 0 → |s| ≤ R ∧ ‖y‖ ≤ R) :
    Continuous (fun z : ℝ × Space => periodize φ z.1 z.2) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  obtain ⟨M, hM⟩ := exists_nat_gt (R + (|z₀.1| + 1))
  have hcont : Continuous (fun z : ℝ × Space =>
      ∑ k ∈ Finset.range (2 * M), φ (z.1 + ((k : ℝ) - M)) z.2) := by
    refine continuous_finsetSum _ fun k _ => ?_
    exact hs.continuous.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
  refine hcont.continuousAt.congr ?_
  have hev : ∀ᶠ z : ℝ × Space in 𝓝 z₀, |z.1| < |z₀.1| + 1 :=
    (continuous_abs.comp continuous_fst).continuousAt.eventually_lt continuousAt_const (by simp)
  filter_upwards [hev] with z hz
  exact (periodize_eq_sum hR hM hz.le z.2).symm

theorem periodize_zero {R : ℝ} (hR : ∀ s y, φ s y ≠ 0 → |s| ≤ R ∧ ‖y‖ ≤ R) (σ : ℝ) {y : Space}
    (hy : R < ‖y‖) : periodize φ σ y = 0 := by
  simp only [periodize]
  exact (tsum_congr fun n : ℤ => slice_eq_zero hR (Or.inr hy)).trans tsum_zero

theorem periodize_lintegral_lt_top (hs : ContDiff ℝ ∞ (fun z : ℝ × Space => φ z.1 z.2))
    (hc : HasCompactSupport (fun z : ℝ × Space => φ z.1 z.2)) {R : ℝ}
    (hR : ∀ s y, φ s y ≠ 0 → |s| ≤ R ∧ ‖y‖ ≤ R) :
    periodLIntegral (fun σ y => ‖periodize φ σ y‖ ^ 2) < ⊤ := by
  obtain ⟨C, hC⟩ := hs.continuous.bounded_above_of_compact_support hc
  obtain ⟨M, hM⟩ := exists_nat_gt (R + 1)
  set B : ℝ := ((2 * M : ℕ) : ℝ) * C
  have hpt : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ y, ENNReal.ofReal (‖periodize φ σ y‖ ^ 2) ≤
      (Metric.closedBall (0 : Space) R).indicator (fun _ => ENNReal.ofReal (B ^ 2)) y := by
    intro σ hσ y
    have hσ' : |σ| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hσ.1, hσ.2]
    by_cases hy : y ∈ Metric.closedBall (0 : Space) R
    · rw [indicator_of_mem hy]
      apply ENNReal.ofReal_le_ofReal
      rw [periodize_eq_sum hR hM hσ' y]
      have h1 : ‖∑ k ∈ Finset.range (2 * M), φ (σ + ((k : ℝ) - M)) y‖ ≤ B :=
        calc ‖∑ k ∈ Finset.range (2 * M), φ (σ + ((k : ℝ) - M)) y‖
            ≤ ∑ k ∈ Finset.range (2 * M), ‖φ (σ + ((k : ℝ) - M)) y‖ := norm_sum_le _ _
          _ ≤ ∑ k ∈ Finset.range (2 * M), C :=
            Finset.sum_le_sum fun k _ => hC ((σ + ((k : ℝ) - M)), y)
          _ = B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    · rw [indicator_of_notMem hy, periodize_zero hR σ (by simpa using hy)]
      simp
  calc periodLIntegral (fun σ y => ‖periodize φ σ y‖ ^ 2)
      = ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖periodize φ σ y‖ ^ 2) := rfl
    _ ≤ ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y,
        (Metric.closedBall (0 : Space) R).indicator (fun _ => ENNReal.ofReal (B ^ 2)) y :=
      setLIntegral_mono' measurableSet_Icc fun σ hσ => lintegral_mono fun y => hpt σ hσ y
    _ = ∫⁻ σ in Icc (0 : ℝ) 1, ENNReal.ofReal (B ^ 2) * volume (Metric.closedBall (0 : Space) R) := by
      simp only [lintegral_indicator_const Metric.isClosed_closedBall.measurableSet]
    _ < ⊤ := by
      rw [setLIntegral_const, Real.volume_Icc]
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top)
        ENNReal.ofReal_lt_top

theorem periodize_isPeriodicField (hs : ContDiff ℝ ∞ (fun z : ℝ × Space => φ z.1 z.2))
    (hc : HasCompactSupport (fun z : ℝ × Space => φ z.1 z.2)) {R : ℝ}
    (hR : ∀ s y, φ s y ≠ 0 → |s| ≤ R ∧ ‖y‖ ≤ R) : IsPeriodicField (periodize φ) :=
  ⟨(periodize_continuous hs hR).aestronglyMeasurable, periodize_periodic,
    periodize_lintegral_lt_top hs hc hR⟩

theorem component_sum (s : Finset ℕ) (v : ℕ → Space) (i : Fin 3) :
    (∑ k ∈ s, v k) i = ∑ k ∈ s, v k i := by
  simp

theorem periodize_slice (hs : ContDiff ℝ ∞ (fun z : ℝ × Space => φ z.1 z.2)) {R : ℝ}
    (hR : ∀ s y, φ s y ≠ 0 → |s| ≤ R ∧ ‖y‖ ≤ R) (hdiv : ∀ s y, divergenceAt (φ s) y = 0)
    (σ : ℝ) : ContDiff ℝ ∞ (periodize φ σ) ∧ HasCompactSupport (periodize φ σ) ∧
      ∀ y, divergenceAt (periodize φ σ) y = 0 := by
  obtain ⟨M, hM⟩ := exists_nat_gt (R + |σ|)
  have heq : periodize φ σ = fun y => ∑ k ∈ Finset.range (2 * M), φ (σ + ((k : ℝ) - M)) y :=
    funext (periodize_eq_sum hR hM le_rfl)
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    exact ContDiff.sum fun k _ => slice_contDiff hs _
  · exact HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) fun y hy =>
      periodize_zero hR σ (by simpa using hy)
  · intro y
    have hd : ∀ k ∈ Finset.range (2 * M), DifferentiableAt ℝ (φ (σ + ((k : ℝ) - M))) y :=
      fun k _ => ((slice_contDiff hs _).differentiable (by simp)).differentiableAt
    rw [heq, divergenceAt, fderiv_fun_sum hd]
    simp only [FunLike.coe_sum, Finset.sum_apply, component_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun k _ => hdiv _ y

theorem integrable_inner_of_memLp {f g : Space → Space} (hf : MemLp f 2) (hg : MemLp g 2) :
    Integrable (fun y => inner ℝ (f y) (g y)) := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
  rw [h1, h2]


theorem shift_int {F : ℝ → Space → Space} (hp : IsTimePeriodic F) (σ : ℝ) (k M : ℕ) :
    F (σ + ((k : ℝ) - M)) = F σ := by
  refine JointRepresentativeInternal.periodic_of_coe_eq hp ?_
  have h0 : (((k : ℝ) - M : ℝ) : AddCircle (1 : ℝ)) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).2 ⟨(k : ℤ) - M, by simp⟩
  rw [AddCircle.coe_add, h0, add_zero]
theorem periodic_lintegral_lt_top (h : ℝ → ℝ≥0∞) (hp : ∀ s, h (s + 1) = h s)
    (h0 : ∫⁻ s in Icc (0 : ℝ) 1, h s < ⊤) (M : ℕ) : ∫⁻ s in Icc (-(M : ℝ)) M, h s < ⊤ := by
  have hper : Function.Periodic h 1 := hp
  have hpiece : ∀ t : ℝ, ∫⁻ s in Ioc t (t + 1), h s = ∫⁻ s in Icc (0 : ℝ) 1, h s := by
    intro t
    have e1 := AddCircle.lintegral_preimage (T := 1) t (hper.lift)
    have e2 := AddCircle.lintegral_preimage (T := 1) 0 (hper.lift)
    simp only [Function.Periodic.lift_coe, zero_add] at e1 e2
    rw [e1, ← e2]
    exact setLIntegral_congr Ioc_ae_eq_Icc
  set S : Finset ℤ := Finset.Icc (-(M : ℤ) - 1) M
  have hsub : Icc (-(M : ℝ)) M ⊆ ⋃ k ∈ S, Ioc (k : ℝ) (k + 1) := by
    intro s hs
    rw [mem_iUnion₂]
    refine ⟨⌈s⌉ - 1, ?_, ?_⟩
    · have h1 : -(M : ℤ) ≤ ⌈s⌉ := Int.le_ceil_iff.2 (by push_cast; linarith [hs.1])
      have h2 : ⌈s⌉ ≤ (M : ℤ) := Int.ceil_le.2 (by exact_mod_cast hs.2)
      rw [Finset.mem_Icc]
      omega
    · push_cast
      exact ⟨by linarith [Int.ceil_lt_add_one s], by linarith [Int.le_ceil s]⟩
  calc ∫⁻ s in Icc (-(M : ℝ)) M, h s ≤ ∫⁻ s in ⋃ k ∈ S, Ioc (k : ℝ) (k + 1), h s :=
        lintegral_mono_set hsub
    _ = volume.withDensity h (⋃ k ∈ S, Ioc (k : ℝ) (k + 1)) :=
        (withDensity_apply _ (Finset.measurableSet_biUnion _ fun k _ => measurableSet_Ioc)).symm
    _ ≤ ∑ k ∈ S, volume.withDensity h (Ioc (k : ℝ) (k + 1)) := measure_biUnion_finset_le _ _
    _ = ∑ k ∈ S, ∫⁻ s in Icc (0 : ℝ) 1, h s := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [withDensity_apply _ measurableSet_Ioc, hpiece]
    _ < ⊤ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) h0

theorem restrict_prod_eq (M : ℕ) :
    (volume : Measure (ℝ × Space)).restrict (Icc (-(M : ℝ)) M ×ˢ univ) =
      (volume.restrict (Icc (-(M : ℝ)) M)).prod (volume : Measure Space) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem integrableOn_sq {F : ℝ → Space → Space} (hF : IsPeriodicField F) (M : ℕ) :
    IntegrableOn (fun z : ℝ × Space => ‖F z.1 z.2‖ ^ 2) (Icc (-(M : ℝ)) M ×ˢ univ) := by
  have haem : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖F z.1 z.2‖ ^ 2))
      ((volume.restrict (Icc (-(M : ℝ)) M)).prod (volume : Measure Space)) := by
    rw [← restrict_prod_eq]
    exact ((hF.1.norm.pow 2).aemeasurable.ennreal_ofReal).restrict
  refine ⟨(hF.1.norm.pow 2).restrict, ?_⟩
  show ∫⁻ z in Icc (-(M : ℝ)) M ×ˢ univ, ‖‖F z.1 z.2‖ ^ 2‖ₑ < ⊤
  simp only [Real.enorm_of_nonneg (sq_nonneg _)]
  rw [restrict_prod_eq, lintegral_prod _ haem]
  refine periodic_lintegral_lt_top (fun s => ∫⁻ y, ENNReal.ofReal (‖F s y‖ ^ 2)) ?_ hF.2.2 M
  intro s
  simp only [hF.2.1 s]

theorem pairing_bound {F : ℝ → Space → Space} {R : ℝ}
    (hR : ∀ s y, φ s y ≠ 0 → |s| ≤ R ∧ ‖y‖ ≤ R) {M : ℕ} (hM : R < M) (z : ℝ × Space) :
    ‖inner ℝ (F z.1 z.2) (φ z.1 z.2)‖ ≤
      (Icc (-(M : ℝ)) M ×ˢ univ).indicator (fun z : ℝ × Space => ‖F z.1 z.2‖ ^ 2) z
        + ‖φ z.1 z.2‖ ^ 2 := by
  by_cases hz : z ∈ Icc (-(M : ℝ)) M ×ˢ univ
  · rw [indicator_of_mem hz]
    have h1 := abs_real_inner_le_norm (F z.1 z.2) (φ z.1 z.2)
    rw [Real.norm_eq_abs]
    nlinarith [norm_nonneg (F z.1 z.2), norm_nonneg (φ z.1 z.2)]
  · rw [indicator_of_notMem hz]
    have hz1 : R < |z.1| := by
      rw [lt_abs]
      by_contra h
      rw [not_or, not_lt, not_lt] at h
      exact hz ⟨⟨by linarith [h.2], by linarith [h.1]⟩, mem_univ _⟩
    rw [slice_eq_zero hR (Or.inl hz1), inner_zero_right, norm_zero]
    positivity

theorem integrable_pairing {F : ℝ → Space → Space} (hF : IsPeriodicField F)
    (hs : ContDiff ℝ ∞ (fun z : ℝ × Space => φ z.1 z.2))
    (hc : HasCompactSupport (fun z : ℝ × Space => φ z.1 z.2)) {R : ℝ}
    (hR : ∀ s y, φ s y ≠ 0 → |s| ≤ R ∧ ‖y‖ ≤ R) :
    Integrable (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (φ z.1 z.2)) := by
  obtain ⟨M, hM⟩ := exists_nat_gt R
  have hcont : Continuous (fun z : ℝ × Space => ‖φ z.1 z.2‖ ^ 2) :=
    (continuous_norm.comp hs.continuous).pow 2
  have hcs : HasCompactSupport (fun z : ℝ × Space => ‖φ z.1 z.2‖ ^ 2) :=
    hc.comp_left (g := fun x : Space => ‖x‖ ^ 2) (by simp)
  have hφ2 : Integrable (fun z : ℝ × Space => ‖φ z.1 z.2‖ ^ 2) :=
    hcont.integrable_of_hasCompactSupport hcs
  have h1 : Integrable ((Icc (-(M : ℝ)) M ×ˢ univ).indicator
      (fun z : ℝ × Space => ‖F z.1 z.2‖ ^ 2)) :=
    (integrableOn_sq hF M).integrable_indicator (measurableSet_Icc.prod MeasurableSet.univ)
  have h2 : AEStronglyMeasurable (fun z : ℝ × Space => φ z.1 z.2) volume :=
    hs.continuous.aestronglyMeasurable
  have h3 : AEStronglyMeasurable (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (φ z.1 z.2)) volume :=
    hF.1.inner h2
  exact (h1.add hφ2).mono' h3 (ae_of_all _ fun z => pairing_bound hR hM z)

set_option maxHeartbeats 1000000 in
theorem exists_curve (F : ℝ → Space → Space) (hF : IsPeriodicField F) :
    ∃ c : Lp (α := TimeCircle) L2R 2,
      ((physToHH F : HH) : TimeCircle → HBar) =ᵐ[volume] (fun t => solProj (c t)) ∧
      ∀ᵐ σ : ℝ, MemLp (F σ) 2 ∧ toLpOrZero 2 (F σ) = c (σ : TimeCircle) := by
  obtain ⟨c, hc, -⟩ := exists_curve_of_joint F hF.1 hF.2.1 hF.2.2
  have hae : ∀ᵐ σ : ℝ, MemLp (F σ) 2 ∧ toLpOrZero 2 (F σ) = c (σ : TimeCircle) := by
    filter_upwards [hc] with σ hσ
    have hm : MemLp (F σ) 2 := (Lp.memLp (c (σ : TimeCircle))).ae_eq hσ
    refine ⟨hm, ?_⟩
    rw [toLpOrZero, dif_pos hm]
    exact Lp.ext (hm.coeFn_toLp.trans hσ.symm)
  obtain ⟨e, he⟩ : ∃ e : HH, (e : TimeCircle → HBar) =ᵐ[volume] fun t => solProj (c t) :=
    ⟨_, ContinuousLinearMap.coeFn_compLpL solProj c⟩
  have hg : (onCircle fun σ => solField (F σ)) =ᵐ[volume] fun t => solProj (c t) := by
    show ∀ᵐ t : TimeCircle, (onCircle fun σ => solField (F σ)) t = solProj (c t)
    rw [ae_coe_iff]
    filter_upwards [hae] with σ h2
    have hr : ((circleRep (σ : TimeCircle) : ℝ) : TimeCircle) = (σ : TimeCircle) := AddCircle.coe_equivIco
    show solField (F (circleRep (σ : TimeCircle))) = solProj (c σ)
    rw [JointRepresentativeInternal.periodic_of_coe_eq hF.2.1 hr]
    exact congrArg solProj h2.2
  have hm : MemLp (onCircle fun σ => solField (F σ)) 2 volume := (Lp.memLp e).ae_eq (he.trans hg.symm)
  refine ⟨c, ?_, hae⟩
  rw [physToHH, circleLpOrZero, dif_pos hm]
  exact hm.coeFn_toLp.trans hg

theorem inner_eq_of_ae {g h : HH} {c d : Lp (α := TimeCircle) L2R 2}
    (hg : (g : TimeCircle → HBar) =ᵐ[volume] fun t => solProj (c t))
    (hh : (h : TimeCircle → HBar) =ᵐ[volume] fun t => solProj (d t)) :
    inner ℝ g h =
      ∫ σ in Icc (0 : ℝ) 1, inner ℝ (solProj (c (σ : TimeCircle))) (solProj (d (σ : TimeCircle))) := by
  rw [L2.inner_def]
  refine (integral_congr_ae ?_).trans
    (integral_Icc_coe (fun t : TimeCircle => inner ℝ (solProj (c t)) (solProj (d t)))).symm
  filter_upwards [hg, hh] with t h1 h2
  rw [h1, h2]

end Internal.TestPairing

open Internal.TestPairing

theorem testPairingHolds_proof : TestPairingHolds := by
  intro F hF φ hφ
  obtain ⟨hs, hc, hdiv⟩ := hφ
  obtain ⟨R, -, hR⟩ := exists_bound hc
  have hΦ : IsPeriodicField (periodize φ) := periodize_isPeriodicField hs hc hR
  obtain ⟨c, hcF, hcae⟩ := exists_curve F hF
  obtain ⟨d, hdΦ, hdae⟩ := exists_curve (periodize φ) hΦ
  obtain ⟨M, hM⟩ := exists_nat_gt (R + 1)
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ → ℝ, g = fun s => ∫ y, inner ℝ (F s y) (φ s y) := ⟨_, rfl⟩
  have hI := integrable_pairing hF hs hc hR
  have hg : Integrable g := by
    rw [hgdef]
    exact hI.integral_prod_left
  have hg0 : ∀ s, R < |s| → g s = 0 := by
    intro s hsR
    rw [hgdef]
    simp only [slice_eq_zero hR (Or.inl hsR), inner_zero_right, integral_zero]
  have step : ∀ᵐ σ : ℝ, σ ∈ Icc (0 : ℝ) 1 →
      inner ℝ (solProj (c (σ : TimeCircle))) (solProj (d (σ : TimeCircle))) =
        ∑ k ∈ Finset.range (2 * M), g (σ + ((k : ℝ) - M)) := by
    filter_upwards [hcae, hdae] with σ hσc hσd hσ
    have hσ' : |σ| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hσ.1, hσ.2]
    rw [← hσc.2, ← hσd.2]
    change inner ℝ (solField (F σ)) (solField (periodize φ σ)) = _
    obtain ⟨h1, h2, h3⟩ := periodize_slice hs hR hdiv σ
    rw [inner_solField_test _ h1 h2 h3 _ hσc.1]
    simp_rw [periodize_eq_sum hR hM hσ', inner_sum]
    rw [integral_finsetSum _ fun k _ => integrable_inner_of_memLp hσc.1 (slice_memLp hs hR _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hgdef]
    simp only [shift_int hF.2.1 σ k M]
  have hpiece : ∀ k : ℕ, ∫ σ in Icc (0 : ℝ) 1, g (σ + ((k : ℝ) - M)) =
      ∫ s in ((k : ℝ) - M)..(((k + 1 : ℕ) : ℝ) - M), g s := by
    intro k
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_comp_add_right]
    rw [show (0 : ℝ) + ((k : ℝ) - M) = (k : ℝ) - M by ring,
      show (1 : ℝ) + ((k : ℝ) - M) = ((k + 1 : ℕ) : ℝ) - M by push_cast; ring]
  calc inner ℝ (physToHH F) (testInHH φ)
      = ∫ σ in Icc (0 : ℝ) 1, inner ℝ (solProj (c (σ : TimeCircle))) (solProj (d (σ : TimeCircle))) :=
        inner_eq_of_ae hcF hdΦ
    _ = ∫ σ in Icc (0 : ℝ) 1, ∑ k ∈ Finset.range (2 * M), g (σ + ((k : ℝ) - M)) :=
        setIntegral_congr_ae measurableSet_Icc step
    _ = ∑ k ∈ Finset.range (2 * M), ∫ σ in Icc (0 : ℝ) 1, g (σ + ((k : ℝ) - M)) :=
        integral_finsetSum _ fun k _ => (hg.comp_add_right _).integrableOn
    _ = ∑ k ∈ Finset.range (2 * M), ∫ s in ((k : ℝ) - M)..(((k + 1 : ℕ) : ℝ) - M), g s :=
        Finset.sum_congr rfl fun k _ => hpiece k
    _ = ∫ s in (((0 : ℕ) : ℝ) - M)..(((2 * M : ℕ) : ℝ) - M), g s :=
        intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ) - M)
          fun k _ => hg.intervalIntegrable
    _ = ∫ s in Ioc (-(M : ℝ)) M, g s := by
        rw [show ((0 : ℕ) : ℝ) - M = -(M : ℝ) by simp, show ((2 * M : ℕ) : ℝ) - M = (M : ℝ) by push_cast; ring,
          intervalIntegral.integral_of_le (by linarith [(M.cast_nonneg : (0 : ℝ) ≤ M)])]
    _ = ∫ s, g s := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => hg0 s ?_
        rw [mem_Ioc, not_and_or, not_lt, not_le] at hs
        rw [lt_abs]
        rcases hs with h | h
        · right; linarith
        · left; linarith
    _ = ∫ z : ℝ × Space, inner ℝ (F z.1 z.2) (φ z.1 z.2) := by
        rw [hgdef]
        exact (integral_prod _ hI).symm

end Breakdown.Cert
