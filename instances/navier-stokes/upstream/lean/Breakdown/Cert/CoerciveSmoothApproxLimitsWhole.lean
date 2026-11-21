import Breakdown.Cert.CoerciveSmoothApproxPeriodBound

open scoped ContDiff ENNReal Topology Convolution Pointwise
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothApprox

theorem kernel_integral_eq_one (n : ℕ) : ∫ t, kernel n t = 1 := by
  rw [Measure.volume_eq_prod]
  simp only [kernel]
  rw [integral_prod_mul, (timeBump n).integral_normed, (spaceBump n).integral_normed, mul_one]

theorem lintegral_kernel_eq_one (n : ℕ) : ∫⁻ t, ‖kernel n t‖ₑ = 1 := by
  have hint : Integrable (kernel n) volume :=
    (kernel_contDiff n).continuous.integrable_of_hasCompactSupport (kernel_hasCompactSupport n)
  calc ∫⁻ t, ‖kernel n t‖ₑ = ∫⁻ t, ENNReal.ofReal (kernel n t) :=
        lintegral_congr fun t => by
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (kernel_nonneg n t)]
    _ = ENNReal.ofReal (∫ t, kernel n t) :=
        (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (kernel_nonneg n))).symm
    _ = 1 := by rw [kernel_integral_eq_one, ENNReal.ofReal_one]

theorem kernel_support_subset_ball (n : ℕ) :
    Function.support (kernel n) ⊆ Metric.ball 0 (2 / ((n : ℝ) + 1)) := by
  intro t ht
  have h1 : (timeBump n).normed volume t.1 ≠ 0 := fun h0 => ht (by simp [kernel, h0])
  have h2 : (spaceBump n).normed volume t.2 ≠ 0 := fun h0 => ht (by simp [kernel, h0])
  have m1 : t.1 ∈ Function.support ((timeBump n).normed volume) := h1
  have m2 : t.2 ∈ Function.support ((spaceBump n).normed volume) := h2
  rw [(timeBump n).support_normed_eq, Metric.mem_ball] at m1
  rw [(spaceBump n).support_normed_eq, Metric.mem_ball] at m2
  rw [Metric.mem_ball, Prod.dist_eq]
  simp only [Prod.fst_zero, Prod.snd_zero]
  exact max_lt m1 m2

theorem radius_le_two (n : ℕ) : 2 / ((n : ℝ) + 1) ≤ 2 :=
  div_le_self (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

theorem kernel_support_tendsto :
    Tendsto (fun n => Function.support (kernel n)) atTop (𝓝 (0 : ℝ × Space)).smallSets := by
  rw [tendsto_smallSets_iff]
  intro s hs
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
  have h1 : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
    simpa [div_eq_mul_inv] using this
  filter_upwards [h1.eventually (Iio_mem_nhds hε)] with n hn
  exact (kernel_support_subset_ball n).trans ((Metric.ball_subset_ball (le_of_lt hn)).trans hball)

theorem whole_convolution_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℝ × Space → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) {h : ℝ × Space → E}
    (hh : AEStronglyMeasurable h volume) :
    ∫⁻ x, ‖∫ t, φ t • h (x - t)‖ₑ ^ 2 ≤ (∫⁻ t, ‖φ t‖ₑ) ^ 2 * ∫⁻ x, ‖h x‖ₑ ^ 2 := by
  have hH := volume_prod_invariantClass
  set F : ℝ × Space → ℝ≥0∞ := fun z => ‖h z‖ₑ ^ 2 with hFdef
  have hF : AEMeasurable F volume := hh.enorm.pow_const 2
  have hC : (∫⁻ t, ‖φ t‖ₑ) ≠ ⊤ := (hφ.integrable_of_hasCompactSupport hφc).2.ne
  have hpt : ∀ x : ℝ × Space, ‖∫ t, φ t • h (x - t)‖ₑ ^ 2 ≤
      (∫⁻ t, ‖φ t‖ₑ) * ∫⁻ t, ‖φ t‖ₑ * F (x - t) := by
    intro x
    have h1 : ‖∫ t, φ t • h (x - t)‖ₑ ≤ ∫⁻ t, ‖φ t‖ₑ * ‖h (x - t)‖ₑ :=
      (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (by simp only [enorm_smul]))
    have hm : AEMeasurable (fun t => ‖h (x - t)‖ₑ) volume :=
      hh.enorm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left volume x)
    calc ‖∫ t, φ t • h (x - t)‖ₑ ^ 2 ≤ (∫⁻ t, ‖φ t‖ₑ * ‖h (x - t)‖ₑ) ^ 2 := by gcongr
      _ ≤ (∫⁻ t, ‖φ t‖ₑ) * ∫⁻ t, ‖φ t‖ₑ * ‖h (x - t)‖ₑ ^ 2 :=
          sq_lintegral_mul_le_prod hφ.enorm.aemeasurable hm
  have hK0 : AEMeasurable (fun p : (ℝ × Space) × (ℝ × Space) => ‖φ p.2‖ₑ * F (p.1 - p.2))
      ((volume : Measure (ℝ × Space)).prod volume) :=
    (hφ.enorm.measurable.comp measurable_snd).aemeasurable.mul
      (hF.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant volume volume))
  calc ∫⁻ x, ‖∫ t, φ t • h (x - t)‖ₑ ^ 2
      ≤ ∫⁻ x, (∫⁻ t, ‖φ t‖ₑ) * ∫⁻ t, ‖φ t‖ₑ * F (x - t) := lintegral_mono hpt
    _ = (∫⁻ t, ‖φ t‖ₑ) * ∫⁻ t, ∫⁻ x, ‖φ t‖ₑ * F (x - t) := by
        rw [lintegral_const_mul' _ _ hC,
          lintegral_lintegral_swap (f := fun x t => ‖φ t‖ₑ * F (x - t)) hK0]
    _ = (∫⁻ t, ‖φ t‖ₑ) * ∫⁻ t, ‖φ t‖ₑ * ∫⁻ x, F x := by
        congr 1
        refine lintegral_congr fun t => ?_
        rw [lintegral_const_mul' _ _ enorm_ne_top, lintegral_sub_right_eq_self]
    _ = (∫⁻ t, ‖φ t‖ₑ) ^ 2 * ∫⁻ x, ‖h x‖ₑ ^ 2 := by
        rw [lintegral_mul_const _ hφ.enorm.measurable, sq, mul_assoc]

theorem eLpNorm_two_sq_eq_lintegral {E : Type*} [NormedAddCommGroup E] (f : ℝ × Space → E) :
    eLpNorm f 2 volume ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  have := eLpNorm_nnreal_pow_eq_lintegral (μ := (volume : Measure (ℝ × Space))) (f := f)
    (p := 2) two_ne_zero
  simpa using this

theorem eLpNorm_tendsto_of_sq {E : Type*} [NormedAddCommGroup E] {F : ℕ → ℝ × Space → E}
    (h : Tendsto (fun n => ∫⁻ x, ‖F n x‖ₑ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) 2 volume) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero] at h ⊢
  intro ε hε
  filter_upwards [h (ε ^ 2) (ENNReal.pow_pos hε 2)] with n hn
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, eLpNorm_two_sq_eq_lintegral]
  exact hn

theorem kernel_convolution_sub_eLpNorm_le (n : ℕ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f g : ℝ × Space → E} (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) :
    eLpNorm (fun x => (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
      (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) 2 volume ≤
      eLpNorm (f - g) 2 volume := by
  have hH := volume_prod_invariantClass
  have e : ∀ x, (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
      (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x =
      ∫ t, kernel n t • (f - g) (x - t) := by
    intro x
    have I1 : Integrable (fun t => kernel n t • f (x - t)) volume :=
      (kernel_hasCompactSupport n).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
        (kernel_contDiff n).continuous hf x
    have I2 : Integrable (fun t => kernel n t • g (x - t)) volume :=
      (kernel_hasCompactSupport n).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
        (kernel_contDiff n).continuous hg x
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, Pi.sub_apply, smul_sub]
    exact (integral_sub I1 I2).symm
  have hy := whole_convolution_sq_le (kernel_contDiff n).continuous (kernel_hasCompactSupport n)
    (hf.aestronglyMeasurable.sub hg.aestronglyMeasurable)
  rw [lintegral_kernel_eq_one, one_pow, one_mul] at hy
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, eLpNorm_two_sq_eq_lintegral,
    eLpNorm_two_sq_eq_lintegral]
  simp only [e]
  exact hy

theorem kernel_convolution_sq_tendsto_of_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {g : ℝ × Space → E} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    Tendsto (fun n => ∫⁻ x, ‖(kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x‖ₑ ^ 2)
      atTop (𝓝 0) := by
  have hH := volume_prod_invariantClass
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  set S : Set (ℝ × Space) := Metric.closedBall 0 2 + tsupport g with hSdef
  have hS : IsCompact S := (isCompact_closedBall 0 2).add hgc
  have hconv : ∀ n, Continuous (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := fun n =>
    ((kernel_hasCompactSupport n).contDiff_convolution_left _ (kernel_contDiff n)
      hg.locallyIntegrable).continuous
  have hsupp : ∀ n x, x ∉ S →
      (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x = 0 := by
    intro n x hx
    have h1 : (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x = 0 := by
      by_contra h
      exact hx (Set.add_subset_add
        ((kernel_support_subset_ball n).trans ((Metric.ball_subset_closedBall).trans
          (Metric.closedBall_subset_closedBall (radius_le_two n))))
        (subset_tsupport g) (support_convolution_subset _ h))
    have h2 : g x = 0 := by
      by_contra h
      exact hx ⟨0, Metric.mem_closedBall_self (by norm_num), x, subset_tsupport g h, zero_add x⟩
    simp [h1, h2]
  have hbd : ∀ n x, ‖(kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x‖ ≤ M := by
    intro n x
    have := dist_convolution_le (μ := volume) (x₀ := x) (R := 3) (z₀ := (0 : E))
      ((norm_nonneg _).trans (hM 0))
      ((kernel_support_subset_ball n).trans (Metric.ball_subset_ball ((radius_le_two n).trans
        (by norm_num))))
      (kernel_nonneg n) (kernel_integral_eq_one n) hg.aestronglyMeasurable
      (fun y _ => by simpa using hM y)
    simpa using this
  have hlim := tendsto_lintegral_of_dominated_convergence (μ := volume)
    (F := fun n x => ‖(kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x‖ₑ ^ 2)
    (f := fun _ => 0) (S.indicator fun _ => ENNReal.ofReal ((M + M) ^ 2))
    (fun n => (((hconv n).sub hg).enorm.measurable.pow_const 2))
    (fun n => Eventually.of_forall fun x => by
      by_cases hx : x ∈ S
      · dsimp only
        rw [Set.indicator_of_mem hx, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le_of_le (hbd n x) (hM x)) 2)
      · simp [hsupp n x hx])
    (by
      rw [lintegral_indicator_const hS.measurableSet]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS.measure_lt_top.ne)
    (Eventually.of_forall fun x => by
      have hc := convolution_tendsto_right (μ := volume) (g := fun _ : ℕ => g) (l := atTop)
        (x₀ := x) (z₀ := g x) (φ := kernel) (k := fun _ => x)
        (Eventually.of_forall fun n => kernel_nonneg n)
        (Eventually.of_forall fun n => kernel_integral_eq_one n) kernel_support_tendsto
        (Eventually.of_forall fun _ => hg.aestronglyMeasurable)
        ((hg.tendsto x).comp tendsto_snd) tendsto_const_nhds
      have := ((ENNReal.continuous_pow 2).tendsto _).comp
        ((hc.sub (tendsto_const_nhds (x := g x))).enorm)
      simpa [Function.comp_def] using this)
  simpa using hlim

theorem kernel_convolution_eLpNorm_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ × Space → E} (hf : MemLp f 2 volume) :
    Tendsto (fun n => eLpNorm (fun x => (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x
      - f x) 2 volume) atTop (𝓝 0) := by
  have hH := volume_prod_invariantClass
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : ε / 3 ≠ 0 := (ENNReal.div_pos hε.ne' (by norm_num)).ne'
  obtain ⟨g, hgc, hfg, hgcont, hgm⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hε3
  have hgl : LocallyIntegrable g volume := hgcont.locallyIntegrable
  have hlim := eLpNorm_tendsto_of_sq
    (F := fun n x => (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x)
    (kernel_convolution_sq_tendsto_of_continuous hgcont hgc)
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hlim (ε / 3) (pos_iff_ne_zero.2 hε3)] with n hn
  have hcf : Continuous (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) :=
    ((kernel_hasCompactSupport n).contDiff_convolution_left _ (kernel_contDiff n) hfl).continuous
  have hcg : Continuous (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) :=
    ((kernel_hasCompactSupport n).contDiff_convolution_left _ (kernel_contDiff n) hgl).continuous
  have e : (fun x => (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) =
      (fun x => (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
        (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) +
      (fun x => (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x) + (g - f) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
  rw [e]
  calc _ ≤ eLpNorm (fun x => (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x -
          (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) 2 volume +
        eLpNorm (fun x => (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x) 2 volume +
        eLpNorm (g - f) 2 volume := by
        refine (eLpNorm_add_le (((hcf.sub hcg).aestronglyMeasurable).add
          (hcg.sub hgcont).aestronglyMeasurable) (hgm.1.sub hf.1) (by norm_num)).trans ?_
        gcongr
        exact eLpNorm_add_le (hcf.sub hcg).aestronglyMeasurable (hcg.sub hgcont).aestronglyMeasurable
          (by norm_num)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact (kernel_convolution_sub_eLpNorm_le n hfl hgl).trans hfg
        · rw [eLpNorm_sub_comm]
          exact hfg
    _ = ε := ENNReal.add_thirds ε

theorem setLIntegral_prod_eq (s : Set ℝ) {F : ℝ × Space → ℝ≥0∞} (hF : AEMeasurable F volume) :
    ∫⁻ σ in s, ∫⁻ y, F (σ, y) = ∫⁻ z in s ×ˢ Set.univ, F z := by
  have hac : ((volume.restrict s).prod (volume : Measure Space)) ≪ volume := by
    rw [Measure.volume_eq_prod (α := ℝ) (β := Space)]
    exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).prod
      Measure.AbsolutelyContinuous.rfl
  refine (lintegral_prod F (hF.mono_ac hac)).symm.trans ?_
  rw [Measure.volume_eq_prod (α := ℝ) (β := Space), ← Measure.prod_restrict, Measure.restrict_univ]

theorem convolution_indicator_eq (n : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : ℝ → Space → E) {x : ℝ × Space} (hx : x.1 ∈ Set.Icc (0 : ℝ) 1) :
    (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (Set.Icc (-2 : ℝ) 3 ×ˢ Set.univ).indicator (joint w)) x =
      (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint w) x := by
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply]
  congr 1
  funext t
  by_cases hk : kernel n t = 0
  · simp [hk]
  have ht : ‖t‖ < 2 / ((n : ℝ) + 1) := mem_ball_zero_iff.1 (kernel_support_subset_ball n hk)
  have h1 : |t.1| < 2 := by
    have := norm_fst_le t
    rw [Real.norm_eq_abs] at this
    linarith [radius_le_two n]
  have hmem : x - t ∈ Set.Icc (-2 : ℝ) 3 ×ˢ Set.univ := by
    refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩ <;> simp only [Prod.fst_sub] <;>
      linarith [(abs_lt.1 h1).1, (abs_lt.1 h1).2, hx.1, hx.2]
  rw [Set.indicator_of_mem hmem]

theorem lintegral_five_periods (Φ : ℝ → ℝ≥0∞) (hΦ : ∀ σ, Φ (σ + 1) = Φ σ) :
    ∫⁻ σ in Set.Icc (-2 : ℝ) 3, Φ σ ≤ 5 * ∫⁻ σ in Set.Icc (0 : ℝ) 1, Φ σ := by
  have hsub : Set.Icc (-2 : ℝ) 3 ⊆ Set.Icc (-2) (-2 + 1) ∪ Set.Icc (-1) (-1 + 1) ∪
      Set.Icc 0 (0 + 1) ∪ Set.Icc 1 (1 + 1) ∪ Set.Icc 2 (2 + 1) := by
    intro σ hσ
    obtain ⟨h1, h2⟩ := hσ
    by_cases a : σ ≤ -1
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨h1, by linarith⟩)))
    by_cases b : σ ≤ 0
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨by linarith, by linarith⟩)))
    by_cases c : σ ≤ 1
    · exact Or.inl (Or.inl (Or.inr ⟨by linarith, by linarith⟩))
    by_cases d : σ ≤ 2
    · exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)
    · exact Or.inr ⟨by linarith, by linarith⟩
  have e := Breakdown.Cert.Internal.TranslationCriterion.lintegral_Icc_shift Φ hΦ
  calc ∫⁻ σ in Set.Icc (-2 : ℝ) 3, Φ σ
      ≤ ∫⁻ σ in Set.Icc (-2) (-2 + 1) ∪ Set.Icc (-1) (-1 + 1) ∪
          Set.Icc 0 (0 + 1) ∪ Set.Icc 1 (1 + 1) ∪ Set.Icc 2 (2 + 1), Φ σ := lintegral_mono_set hsub
    _ ≤ (∫⁻ σ in Set.Icc (-2 : ℝ) (-2 + 1), Φ σ) + (∫⁻ σ in Set.Icc (-1 : ℝ) (-1 + 1), Φ σ) +
          (∫⁻ σ in Set.Icc (0 : ℝ) (0 + 1), Φ σ) + (∫⁻ σ in Set.Icc (1 : ℝ) (1 + 1), Φ σ) +
          (∫⁻ σ in Set.Icc (2 : ℝ) (2 + 1), Φ σ) := by
        refine (lintegral_union_le _ _ _).trans (add_le_add ?_ le_rfl)
        refine (lintegral_union_le _ _ _).trans (add_le_add ?_ le_rfl)
        refine (lintegral_union_le _ _ _).trans (add_le_add ?_ le_rfl)
        exact lintegral_union_le _ _ _
    _ = 5 * ∫⁻ σ in Set.Icc (0 : ℝ) 1, Φ σ := by
        rw [e, e, e, e, e]
        ring

theorem periodLIntegral_sq_eq {E : Type*} [NormedAddCommGroup E] (w : ℝ → Space → E) :
    periodLIntegral (fun σ y => ‖w σ y‖ ^ 2) = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ‖w σ y‖ₑ ^ 2 := by
  unfold periodLIntegral
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem period_indicator_memLp {E : Type*} [NormedAddCommGroup E] {w : ℝ → Space → E}
    (hw : AEStronglyMeasurable (joint w) volume) (hper : IsTimePeriodic w)
    (hfin : periodLIntegral (fun σ y => ‖w σ y‖ ^ 2) < ⊤) :
    MemLp ((Set.Icc (-2 : ℝ) 3 ×ˢ Set.univ).indicator (joint w)) 2 volume := by
  have hAm : MeasurableSet (Set.Icc (-2 : ℝ) 3 ×ˢ (Set.univ : Set Space)) :=
    measurableSet_Icc.prod MeasurableSet.univ
  refine ⟨hw.indicator hAm, lt_top_iff_ne_top.2 fun htop => ?_⟩
  have e1 : (fun z => ‖(Set.Icc (-2 : ℝ) 3 ×ˢ Set.univ).indicator (joint w) z‖ₑ ^ 2) =
      (Set.Icc (-2 : ℝ) 3 ×ˢ Set.univ).indicator (fun z => ‖joint w z‖ₑ ^ 2) := by
    funext z
    by_cases h : z ∈ Set.Icc (-2 : ℝ) 3 ×ˢ (Set.univ : Set Space) <;> simp [h]
  have hsq := eLpNorm_two_sq_eq_lintegral ((Set.Icc (-2 : ℝ) 3 ×ˢ Set.univ).indicator (joint w))
  rw [e1, lintegral_indicator hAm, ← setLIntegral_prod_eq _ (hw.enorm.pow_const 2), htop,
    ENNReal.top_pow two_ne_zero] at hsq
  have hle := lintegral_five_periods (fun σ => ∫⁻ y, ‖w σ y‖ₑ ^ 2) (fun σ => by simp only [hper σ])
  rw [periodLIntegral_sq_eq] at hfin
  simp only [joint] at hsq
  rw [← hsq] at hle
  exact absurd (hle.trans_lt (ENNReal.mul_lt_top (by norm_num) hfin)) (lt_irrefl _)

theorem period_convolution_sq_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {w : ℝ → Space → E} (hw : AEStronglyMeasurable (joint w) volume)
    (hper : IsTimePeriodic w) (hfin : periodLIntegral (fun σ y => ‖w σ y‖ ^ 2) < ⊤) :
    Tendsto (fun n => periodLIntegral (fun σ y =>
      ‖(kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint w) (σ, y) - w σ y‖ ^ 2))
      atTop (𝓝 0) := by
  have hH := volume_prod_invariantClass
  set f := (Set.Icc (-2 : ℝ) 3 ×ˢ (Set.univ : Set Space)).indicator (joint w) with hfdef
  have hfm : MemLp f 2 volume := period_indicator_memLp hw hper hfin
  have hfl : LocallyIntegrable f volume := hfm.locallyIntegrable (by norm_num)
  have hlim := kernel_convolution_eLpNorm_tendsto hfm
  have hsq : Tendsto (fun n => eLpNorm (fun x =>
      (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) 2 volume ^ 2) atTop (𝓝 0) := by
    have := ((ENNReal.continuous_pow 2).tendsto _).comp hlim
    simpa [Function.comp_def] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsq (fun n => zero_le)
    (fun n => ?_)
  have hcf : Continuous (kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) :=
    ((kernel_hasCompactSupport n).contDiff_convolution_left _ (kernel_contDiff n) hfl).continuous
  have hG : AEMeasurable (fun z =>
      ‖(kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) z - f z‖ₑ ^ 2) volume :=
    (hcf.aestronglyMeasurable.sub hfm.1).enorm.pow_const 2
  dsimp only
  rw [eLpNorm_two_sq_eq_lintegral]
  calc periodLIntegral (fun σ y =>
        ‖(kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] joint w) (σ, y) - w σ y‖ ^ 2)
      = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
          ‖(kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) (σ, y) - f (σ, y)‖ₑ ^ 2 := by
        unfold periodLIntegral
        refine setLIntegral_congr_fun measurableSet_Icc (fun σ hσ => lintegral_congr fun y => ?_)
        have hmem : (σ, y) ∈ Set.Icc (-2 : ℝ) 3 ×ˢ (Set.univ : Set Space) :=
          ⟨⟨by linarith [hσ.1], by linarith [hσ.2]⟩, Set.mem_univ _⟩
        rw [hfdef, convolution_indicator_eq n w (x := (σ, y)) hσ, Set.indicator_of_mem hmem,
          ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
        rfl
    _ = ∫⁻ z in Set.Icc (0 : ℝ) 1 ×ˢ Set.univ,
          ‖(kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) z - f z‖ₑ ^ 2 :=
        setLIntegral_prod_eq _ hG
    _ ≤ ∫⁻ z, ‖(kernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) z - f z‖ₑ ^ 2 :=
        setLIntegral_le_lintegral _ _

end Internal.SmoothApprox

end Coercive

end Breakdown
