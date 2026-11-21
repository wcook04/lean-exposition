import Mathlib
import Breakdown.Cert.Statement

open scoped ENNReal Topology
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown.Cert

namespace Internal.HeldLimitProducts

theorem eLpNorm_two_eq_lintegral {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (f : α → E) :
    eLpNorm f 2 μ = (∫⁻ a, ENNReal.ofReal (‖f a‖ ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  congr 1
  refine lintegral_congr fun a => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ← ENNReal.rpow_natCast]
  norm_num

theorem memLp_two_of_lintegral {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {f : α → E} (hf : AEStronglyMeasurable f μ)
    (h : ∫⁻ a, ENNReal.ofReal (‖f a‖ ^ 2) ∂μ < ⊤) : MemLp f 2 μ :=
  ⟨hf, by
    rw [eLpNorm_two_eq_lintegral]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne⟩

theorem tendsto_eLpNorm_sub_of_lintegral {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (f : ℕ → α → E) (f₀ : α → E)
    (h : Tendsto (fun n => ∫⁻ a, ENNReal.ofReal (‖f n a - f₀ a‖ ^ 2) ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n - f₀) 2 μ) atTop (𝓝 0) := by
  have h1 := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp h
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h1
  exact h1.congr fun n => (eLpNorm_two_eq_lintegral (f n - f₀)).symm

theorem inner_real_eq_mul (x y : ℝ) : inner ℝ x y = x * y := by
  rw [RCLike.inner_apply', conj_trivial]

theorem integrable_mul_of_memLp {α : Type*} [MeasurableSpace α] {μ : Measure α} {u v : α → ℝ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) : Integrable (fun a => u a * v a) μ :=
  (L2.integrable_inner (𝕜 := ℝ) (hu.toLp u) (hv.toLp v)).congr (by
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with a h1 h2
    rw [h1, h2, inner_real_eq_mul])

theorem integral_mul_eq_inner {α : Type*} [MeasurableSpace α] {μ : Measure α} {u v : α → ℝ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    ∫ a, u a * v a ∂μ = inner ℝ (hu.toLp u) (hv.toLp v) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with a h1 h2
  rw [h1, h2, inner_real_eq_mul]

theorem eventually_memLp_of_eLpNorm {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : ℕ → α → ℝ) (f₀ : α → ℝ) (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hf₀ : MemLp f₀ 2 μ)
    (hfc : Tendsto (fun n => eLpNorm (f n - f₀) 2 μ) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, MemLp (f n) 2 μ := by
  filter_upwards [hfc.eventually (gt_mem_nhds ENNReal.zero_lt_top)] with n hn
  have h : MemLp (f n - f₀ + f₀) 2 μ := MemLp.add ⟨(hf n).sub hf₀.1, hn⟩ hf₀
  rwa [sub_add_cancel] at h

theorem tendsto_toLp_of_eLpNorm {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : ℕ → α → ℝ) (f₀ : α → ℝ) (hf₀ : MemLp f₀ 2 μ) (F : ℕ → Lp ℝ 2 μ)
    (hF : ∀ n (h : MemLp (f n) 2 μ), F n = h.toLp (f n)) (hm : ∀ᶠ n in atTop, MemLp (f n) 2 μ)
    (hfc : Tendsto (fun n => eLpNorm (f n - f₀) 2 μ) atTop (𝓝 0)) :
    Tendsto F atTop (𝓝 (hf₀.toLp f₀)) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm F f₀ hf₀]
  refine hfc.congr' ?_
  filter_upwards [hm] with n hn
  rw [hF n hn]
  exact eLpNorm_congr_ae (hn.coeFn_toLp.sub EventuallyEq.rfl).symm

theorem tendsto_integral_mul_of_eLpNorm {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g : ℕ → α → ℝ) (f₀ g₀ : α → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : ∀ n, AEStronglyMeasurable (g n) μ)
    (hf₀ : MemLp f₀ 2 μ) (hg₀ : MemLp g₀ 2 μ)
    (hfc : Tendsto (fun n => eLpNorm (f n - f₀) 2 μ) atTop (𝓝 0))
    (hgc : Tendsto (fun n => eLpNorm (g n - g₀) 2 μ) atTop (𝓝 0)) :
    (∀ᶠ n in atTop, Integrable (fun a => f n a * g n a) μ) ∧
      Integrable (fun a => f₀ a * g₀ a) μ ∧
      Tendsto (fun n => ∫ a, f n a * g n a ∂μ) atTop (𝓝 (∫ a, f₀ a * g₀ a ∂μ)) := by
  classical
  have memf := eventually_memLp_of_eLpNorm f f₀ hf hf₀ hfc
  have memg := eventually_memLp_of_eLpNorm g g₀ hg hg₀ hgc
  obtain ⟨F, hF⟩ : ∃ F : ℕ → Lp ℝ 2 μ, ∀ n (h : MemLp (f n) 2 μ), F n = h.toLp (f n) :=
    ⟨fun n => if h : MemLp (f n) 2 μ then h.toLp (f n) else 0, fun n h => dif_pos h⟩
  obtain ⟨G, hG⟩ : ∃ G : ℕ → Lp ℝ 2 μ, ∀ n (h : MemLp (g n) 2 μ), G n = h.toLp (g n) :=
    ⟨fun n => if h : MemLp (g n) 2 μ then h.toLp (g n) else 0, fun n h => dif_pos h⟩
  have tF := tendsto_toLp_of_eLpNorm f f₀ hf₀ F hF memf hfc
  have tG := tendsto_toLp_of_eLpNorm g g₀ hg₀ G hG memg hgc
  refine ⟨(memf.and memg).mono fun n h => integrable_mul_of_memLp h.1 h.2,
    integrable_mul_of_memLp hf₀ hg₀, ?_⟩
  rw [integral_mul_eq_inner hf₀ hg₀]
  refine (tF.inner tG).congr' ?_
  filter_upwards [memf, memg] with n h1 h2
  rw [hF n h1, hG n h2, integral_mul_eq_inner h1 h2]

theorem lintegral_unit_Icc {H : ℝ → ℝ≥0∞} (hH : ∀ σ, H (σ + 1) = H σ) (m : ℝ) :
    ∫⁻ σ in Icc m (m + 1), H σ = ∫⁻ σ in Icc 0 1, H σ := by
  have hp : Function.Periodic H 1 := hH
  have e : ∀ t : ℝ, ∫⁻ σ in Icc t (t + 1), H σ = ∫⁻ b : AddCircle (1 : ℝ), hp.lift b := by
    intro t
    rw [← AddCircle.lintegral_preimage 1 t, Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact lintegral_congr fun σ => (hp.lift_coe σ).symm
  have e0 := e 0
  rw [zero_add] at e0
  rw [e m, e0]

theorem lintegral_Icc_nat_le {H : ℝ → ℝ≥0∞} (hH : ∀ σ, H (σ + 1) = H σ) (N : ℕ) :
    ∫⁻ σ in Icc (-(N : ℝ)) N, H σ ≤ 2 * (N : ℝ≥0∞) * ∫⁻ σ in Icc 0 1, H σ := by
  induction N with
  | zero =>
    have h0 : volume (Icc (-((0 : ℕ) : ℝ)) ((0 : ℕ) : ℝ)) = 0 := by simp
    rw [setLIntegral_measure_zero _ _ h0]
    positivity
  | succ N ih =>
    have hsub : Icc (-((N + 1 : ℕ) : ℝ)) ((N + 1 : ℕ) : ℝ) ⊆
        Icc (-(N : ℝ) - 1) (-(N : ℝ) - 1 + 1) ∪ (Icc (-(N : ℝ)) N ∪ Icc (N : ℝ) (N + 1)) := by
      intro x hx
      push_cast at hx
      rcases le_or_gt x (-(N : ℝ)) with h | h
      · exact Or.inl ⟨by linarith [hx.1], by linarith⟩
      · rcases le_or_gt x N with h' | h'
        · exact Or.inr (Or.inl ⟨h.le, h'⟩)
        · exact Or.inr (Or.inr ⟨h'.le, by linarith [hx.2]⟩)
    calc ∫⁻ σ in Icc (-((N + 1 : ℕ) : ℝ)) ((N + 1 : ℕ) : ℝ), H σ
        ≤ ∫⁻ σ in Icc (-(N : ℝ) - 1) (-(N : ℝ) - 1 + 1) ∪
            (Icc (-(N : ℝ)) N ∪ Icc (N : ℝ) (N + 1)), H σ := lintegral_mono_set hsub
      _ ≤ (∫⁻ σ in Icc (-(N : ℝ) - 1) (-(N : ℝ) - 1 + 1), H σ) +
            ((∫⁻ σ in Icc (-(N : ℝ)) N, H σ) + ∫⁻ σ in Icc (N : ℝ) (N + 1), H σ) :=
          (lintegral_union_le _ _ _).trans (by
            gcongr
            exact lintegral_union_le _ _ _)
      _ ≤ (∫⁻ σ in Icc 0 1, H σ) + (2 * (N : ℝ≥0∞) * (∫⁻ σ in Icc 0 1, H σ) +
            ∫⁻ σ in Icc 0 1, H σ) := by
          rw [lintegral_unit_Icc hH (-(N : ℝ) - 1), lintegral_unit_Icc hH (N : ℝ)]
          gcongr
      _ = 2 * ((N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ σ in Icc 0 1, H σ := by
          push_cast
          ring

theorem lintegral_box_le (h : ℝ → Space → ℝ) (hp : IsTimePeriodic h) (N : ℕ) (R : ℝ) :
    ∫⁻ z in Icc (-(N : ℝ)) N ×ˢ Metric.closedBall (0 : Space) R, ENNReal.ofReal (h z.1 z.2) ≤
      2 * (N : ℝ≥0∞) * periodBallLIntegral R h := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  refine (lintegral_prod_le _).trans ?_
  unfold periodBallLIntegral
  exact lintegral_Icc_nat_le
    (H := fun σ => ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (h σ y))
    (fun σ => by simp only [hp σ]) N

theorem lt_top_of_box {P : ℝ≥0∞} (N : ℕ) (hP : P < ⊤) : 2 * (N : ℝ≥0∞) * P < ⊤ :=
  ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofNat_lt_top (ENNReal.natCast_lt_top N)) hP

theorem sq_inner_le {M : ℝ} {a b : Space} (hb : ‖b‖ ≤ M) :
    ‖inner ℝ a b‖ ^ 2 ≤ M ^ 2 * ‖a‖ ^ 2 := by
  have h1 : ‖inner ℝ a b‖ ≤ ‖a‖ * M :=
    (norm_inner_le_norm a b).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg a))
  calc ‖inner ℝ a b‖ ^ 2 ≤ (‖a‖ * M) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = M ^ 2 * ‖a‖ ^ 2 := by ring

theorem lintegral_inner_le {α : Type*} [MeasurableSpace α] {μ : Measure α} (u w : α → Space)
    {M : ℝ} (hM : ∀ z, ‖w z‖ ≤ M) :
    ∫⁻ z, ENNReal.ofReal (‖inner ℝ (u z) (w z)‖ ^ 2) ∂μ ≤
      ENNReal.ofReal (M ^ 2) * ∫⁻ z, ENNReal.ofReal (‖u z‖ ^ 2) ∂μ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun z => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg M)]
  exact ENNReal.ofReal_le_ofReal (sq_inner_le (hM z))

theorem lintegral_inner_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u v w : α → Space) {M : ℝ} (hM : ∀ z, ‖w z‖ ≤ M) :
    ∫⁻ z, ENNReal.ofReal (‖inner ℝ (u z) (w z) - inner ℝ (v z) (w z)‖ ^ 2) ∂μ ≤
      ENNReal.ofReal (M ^ 2) * ∫⁻ z, ENNReal.ofReal (‖u z - v z‖ ^ 2) ∂μ := by
  have h := lintegral_inner_le (μ := μ) (fun z => u z - v z) w hM
  simpa only [inner_sub_left] using h


end Internal.HeldLimitProducts

namespace Internal.HeldLimit

open Internal.HeldLimitProducts

theorem scalar_product_integral_tendsto (s : ℕ → ℝ → Space → ℝ) (c : ℕ → ℝ → Space → Space)
    (s₀ : ℝ → Space → ℝ) (c₀ : ℝ → Space → Space)
    (hs : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => s n z.1 z.2) volume)
    (hc : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => c n z.1 z.2) volume)
    (hs₀ : AEStronglyMeasurable (fun z : ℝ × Space => s₀ z.1 z.2) volume)
    (hc₀ : AEStronglyMeasurable (fun z : ℝ × Space => c₀ z.1 z.2) volume)
    (hps : ∀ n, IsTimePeriodic (s n)) (hpc : ∀ n, IsTimePeriodic (c n))
    (hps₀ : IsTimePeriodic s₀) (hpc₀ : IsTimePeriodic c₀)
    (hfs : ∀ R > 0, periodBallLIntegral R (fun σ y => ‖s₀ σ y‖ ^ 2) < ⊤)
    (hfc : ∀ R > 0, periodBallLIntegral R (fun σ y => ‖c₀ σ y‖ ^ 2) < ⊤)
    (hcs : ∀ R > 0, Tendsto (fun n => periodBallLIntegral R
      (fun σ y => ‖s n σ y - s₀ σ y‖ ^ 2)) atTop (𝓝 0))
    (hcc : ∀ R > 0, Tendsto (fun n => periodBallLIntegral R
      (fun σ y => ‖c n σ y - c₀ σ y‖ ^ 2)) atTop (𝓝 0))
    (φ : ℝ → Space → Space) (hφ : IsSpaceTimeTestField φ) :
    (∀ᶠ n in atTop, Integrable (fun z : ℝ × Space => s n z.1 z.2 * inner ℝ (c n z.1 z.2) (φ z.1 z.2))) ∧
    Integrable (fun z : ℝ × Space => s₀ z.1 z.2 * inner ℝ (c₀ z.1 z.2) (φ z.1 z.2)) ∧
    Tendsto (fun n => ∫ z : ℝ × Space, s n z.1 z.2 * inner ℝ (c n z.1 z.2) (φ z.1 z.2)) atTop
      (𝓝 (∫ z : ℝ × Space, s₀ z.1 z.2 * inner ℝ (c₀ z.1 z.2) (φ z.1 z.2))) := by
  have hcont : Continuous (fun z : ℝ × Space => φ z.1 z.2) := hφ.1.continuous
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support hφ.2.1
  obtain ⟨r, hr⟩ := hφ.2.1.isCompact.isBounded.subset_closedBall (0 : ℝ × Space)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, r ≤ N := ⟨⌈r⌉₊, Nat.le_ceil r⟩
  obtain ⟨R, hR0, hrR⟩ : ∃ R : ℝ, 0 < R ∧ r ≤ R :=
    ⟨max r 1, lt_max_of_lt_right one_pos, le_max_left _ _⟩
  obtain ⟨K, hKeq⟩ : ∃ K : Set (ℝ × Space), K = Icc (-(N : ℝ)) N ×ˢ Metric.closedBall (0 : Space) R :=
    ⟨_, rfl⟩
  have hK : ∀ z : ℝ × Space, z ∉ K → φ z.1 z.2 = 0 := by
    intro z hz
    by_contra hne
    have h1 : z ∈ Metric.closedBall (0 : ℝ × Space) r := hr (subset_tsupport _ hne)
    rw [mem_closedBall_zero_iff] at h1
    have h2 : |z.1| ≤ r := by
      have h3 := norm_fst_le z
      rw [Real.norm_eq_abs] at h3
      linarith
    have h4 : ‖z.2‖ ≤ r := (norm_snd_le z).trans h1
    apply hz
    rw [hKeq]
    exact ⟨⟨by linarith [neg_abs_le z.1], by linarith [le_abs_self z.1]⟩,
      mem_closedBall_zero_iff.2 (by linarith)⟩
  have hbox : ∀ h : ℝ → Space → ℝ, IsTimePeriodic h →
      ∫⁻ z in K, ENNReal.ofReal (h z.1 z.2) ≤ 2 * (N : ℝ≥0∞) * periodBallLIntegral R h := by
    intro h hp
    rw [hKeq]
    exact lintegral_box_le h hp N R
  have hgm : ∀ u : ℝ → Space → Space,
      AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) volume →
      AEStronglyMeasurable (fun z : ℝ × Space => inner ℝ (u z.1 z.2) (φ z.1 z.2))
        (volume.restrict K) :=
    fun u hu => (hu.inner hcont.aestronglyMeasurable).restrict
  have bs₀ : ∫⁻ z in K, ENNReal.ofReal (‖s₀ z.1 z.2‖ ^ 2) < ⊤ :=
    lt_of_le_of_lt (hbox (fun σ y => ‖s₀ σ y‖ ^ 2) (fun σ y => by simp only [hps₀ σ y]))
      (lt_top_of_box N (hfs R hR0))
  have bc₀ : ∫⁻ z in K, ENNReal.ofReal (‖c₀ z.1 z.2‖ ^ 2) < ⊤ :=
    lt_of_le_of_lt (hbox (fun σ y => ‖c₀ σ y‖ ^ 2) (fun σ y => by simp only [hpc₀ σ y]))
      (lt_top_of_box N (hfc R hR0))
  have hmf₀ : MemLp (fun z : ℝ × Space => s₀ z.1 z.2) 2 (volume.restrict K) :=
    memLp_two_of_lintegral hs₀.restrict bs₀
  have hmg₀ : MemLp (fun z : ℝ × Space => inner ℝ (c₀ z.1 z.2) (φ z.1 z.2)) 2
      (volume.restrict K) :=
    memLp_two_of_lintegral (hgm c₀ hc₀)
      (lt_of_le_of_lt (lintegral_inner_le (fun z : ℝ × Space => c₀ z.1 z.2)
        (fun z : ℝ × Space => φ z.1 z.2) hM) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top bc₀))
  have tS : Tendsto (fun n => eLpNorm ((fun z : ℝ × Space => s n z.1 z.2) -
      (fun z : ℝ × Space => s₀ z.1 z.2)) 2 (volume.restrict K)) atTop (𝓝 0) := by
    refine tendsto_eLpNorm_sub_of_lintegral (fun n (z : ℝ × Space) => s n z.1 z.2)
      (fun z : ℝ × Space => s₀ z.1 z.2) ?_
    have hu := ENNReal.Tendsto.const_mul (hcs R hR0)
      (Or.inr (lt_top_of_box (P := 1) N ENNReal.one_lt_top).ne)
    rw [mul_zero, mul_one] at hu
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu (fun _ => zero_le)
      (fun n => hbox (fun σ y => ‖s n σ y - s₀ σ y‖ ^ 2)
        (fun σ y => by simp only [hps n σ y, hps₀ σ y]))
  have tC : Tendsto (fun n => eLpNorm ((fun z : ℝ × Space => inner ℝ (c n z.1 z.2) (φ z.1 z.2)) -
      (fun z : ℝ × Space => inner ℝ (c₀ z.1 z.2) (φ z.1 z.2))) 2 (volume.restrict K)) atTop
      (𝓝 0) := by
    refine tendsto_eLpNorm_sub_of_lintegral
      (fun n (z : ℝ × Space) => inner ℝ (c n z.1 z.2) (φ z.1 z.2))
      (fun z : ℝ × Space => inner ℝ (c₀ z.1 z.2) (φ z.1 z.2)) ?_
    have hu := ENNReal.Tendsto.const_mul (hcc R hR0)
      (Or.inr (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := M ^ 2))
        (lt_top_of_box (P := 1) N ENNReal.one_lt_top)).ne)
    rw [mul_zero, mul_one] at hu
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu (fun _ => zero_le)
      (fun n => ?_)
    refine (lintegral_inner_sub_le (fun z : ℝ × Space => c n z.1 z.2)
      (fun z : ℝ × Space => c₀ z.1 z.2) (fun z : ℝ × Space => φ z.1 z.2) hM).trans ?_
    rw [mul_assoc]
    gcongr
    exact hbox (fun σ y => ‖c n σ y - c₀ σ y‖ ^ 2)
      (fun σ y => by simp only [hpc n σ y, hpc₀ σ y])
  have key := tendsto_integral_mul_of_eLpNorm (μ := volume.restrict K)
    (fun n (z : ℝ × Space) => s n z.1 z.2)
    (fun n (z : ℝ × Space) => inner ℝ (c n z.1 z.2) (φ z.1 z.2))
    (fun z : ℝ × Space => s₀ z.1 z.2) (fun z : ℝ × Space => inner ℝ (c₀ z.1 z.2) (φ z.1 z.2))
    (fun n => (hs n).restrict) (fun n => hgm (c n) (hc n)) hmf₀ hmg₀ tS tC
  have hsupp : ∀ (a : ℝ → Space → ℝ) (b : ℝ → Space → Space),
      Function.support (fun z : ℝ × Space => a z.1 z.2 * inner ℝ (b z.1 z.2) (φ z.1 z.2)) ⊆ K := by
    intro a b z hz
    by_contra hzK
    apply hz
    simp only [hK z hzK, inner_zero_right, mul_zero]
  have hint : ∀ (a : ℝ → Space → ℝ) (b : ℝ → Space → Space),
      ∫ z in K, a z.1 z.2 * inner ℝ (b z.1 z.2) (φ z.1 z.2) =
        ∫ z : ℝ × Space, a z.1 z.2 * inner ℝ (b z.1 z.2) (φ z.1 z.2) := by
    intro a b
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
    simp only [hK z hz, inner_zero_right, mul_zero]
  refine ⟨key.1.mono fun n h => (integrableOn_iff_integrable_of_support_subset (hsupp _ _)).1 h,
    (integrableOn_iff_integrable_of_support_subset (hsupp _ _)).1 key.2.1, ?_⟩
  have t := key.2.2.congr fun n => hint (s n) (c n)
  rwa [hint s₀ c₀] at t

end Internal.HeldLimit

end Breakdown.Cert
