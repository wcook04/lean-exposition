import Breakdown.Torus.Basic
import Breakdown.Torus.StatementsCoeff
import Breakdown.Torus.StatementsAnalysis

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace Internal.Mild

def evalSeq (k : Lattice) : Seq →L[ℝ] Coef :=
  LinearMap.mkContinuous
    { toFun := fun a => a k
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    (fun a => by
      show ‖a k‖ ≤ 1 * ‖a‖
      rw [one_mul]
      exact lp.norm_apply_le_norm (by norm_num) a k)

def coeffL (k : Lattice) : V →L[ℝ] Coef :=
  (Real.sqrt (weight k))⁻¹ • ((evalSeq k).comp fieldSpace.subtypeL)

theorem coeffL_apply (k : Lattice) (u : V) : coeffL k u = coeff u k := rfl

theorem divPairing_add (k : Lattice) (a b : Coef) :
    divPairing k (a + b) = divPairing k a + divPairing k b := by
  simp [divPairing, mul_add, Finset.sum_add_distrib]

theorem divPairing_smul (k : Lattice) (z : ℂ) (a : Coef) :
    divPairing k (z • a) = z * divPairing k a := by
  simp only [divPairing, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem divPairing_real_smul (k : Lattice) (r : ℝ) (a : Coef) :
    divPairing k (r • a) = r * divPairing k a := by
  rw [← divPairing_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

def divFreeLin (k : Lattice) : Coef →ₗ[ℂ] Coef where
  toFun := divFree k
  map_add' a b := by
    unfold divFree
    split_ifs
    · rfl
    · rw [divPairing_add, add_div, add_smul]
      abel
  map_smul' z a := by
    unfold divFree
    split_ifs
    · rfl
    · rw [divPairing_smul, mul_div_assoc, mul_smul, RingHom.id_apply, smul_sub]

def divFreeL (k : Lattice) : Coef →L[ℂ] Coef := LinearMap.toContinuousLinearMap (divFreeLin k)

theorem divFreeL_apply (k : Lattice) (c : Coef) : divFreeL k c = divFree k c := rfl

theorem divFree_add (k : Lattice) (a b : Coef) : divFree k (a + b) = divFree k a + divFree k b :=
  (divFreeLin k).map_add a b

theorem divFree_of_div {k : Lattice} {c : Coef} (h : divPairing k c = 0) : divFree k c = c := by
  unfold divFree
  split_ifs <;> simp [h]

theorem freq_apply (k : Lattice) (i : Fin 3) : freq k i = k i := by
  simp [freq, unitVector, Pi.single_apply]

theorem norm_freq_sq (k : Lattice) : ‖freq k‖ ^ 2 = ∑ i, ((k i : ℝ)) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [freq_apply, sq_abs]

theorem divFree_latVec (k : Lattice) : divFree k (latVec k) = 0 := by
  by_cases hk : k = 0
  · subst hk
    ext i
    simp [divFree, latVec]
  · have hne : ‖freq k‖ ^ 2 ≠ 0 := by
      intro h0
      apply hk
      have h1 : freq k = 0 := by simpa using h0
      funext i
      have h2 := congrArg (fun v : Space => v i) h1
      simp only [freq_apply, PiLp.zero_apply] at h2
      exact_mod_cast h2
    have hd : divPairing k (latVec k) = ((‖freq k‖ ^ 2 : ℝ) : ℂ) := by
      rw [norm_freq_sq]
      simp [divPairing, latVec, sq]
    unfold divFree
    rw [if_neg hk, hd, div_self (by exact_mod_cast hne), one_smul, sub_self]

theorem divFree_coeff (a : V) (k : Lattice) : divFree k (coeff a k) = coeff a k := by
  apply divFree_of_div
  have h : (∀ k i, ((a : Seq) (-k)) i = starRingEnd ℂ (((a : Seq) k) i)) ∧
      ∀ k, divPairing k ((a : Seq) k) = 0 := a.2
  rw [coeff, divPairing_real_smul, h.2 k, mul_zero]

theorem heat_max (t : ℝ) : heat t = heat (max t 0) := by
  refine ContinuousLinearMap.ext fun x => ?_
  apply coeff_injective
  intro k
  rw [coeff_heat, coeff_heat]
  simp only [heatFactor, max_eq_left (le_max_right t 0)]

theorem heat_apply_continuous (x : V) : Continuous (fun t => heat t x) := by
  have h : (fun t => heat t x) = (fun t => heat (max t 0) x) := funext fun t => by rw [heat_max t]
  rw [h]
  exact (heat_continuousOn x).comp_continuous (continuous_id.max continuous_const)
    (fun t => le_max_right t 0)

theorem heat_tendsto {α : Type*} {l : Filter α} {σ : α → ℝ} {w : α → V} {σ₀ : ℝ} {w₀ : V}
    (hσ : Tendsto σ l (𝓝 σ₀)) (hw : Tendsto w l (𝓝 w₀)) :
    Tendsto (fun a => heat (σ a) (w a)) l (𝓝 (heat σ₀ w₀)) := by
  have h1 : Tendsto (fun a => heat (σ a) w₀) l (𝓝 (heat σ₀ w₀)) :=
    ((heat_apply_continuous w₀).tendsto σ₀).comp hσ
  have h2 : Tendsto (fun a => heat (σ a) (w a) - heat (σ a) w₀) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun a => norm_nonneg _) (fun a => ?_)
      (tendsto_iff_norm_sub_tendsto_zero.1 hw)
    rw [← map_sub]
    calc ‖heat (σ a) (w a - w₀)‖ ≤ ‖heat (σ a)‖ * ‖w a - w₀‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖w a - w₀‖ := by gcongr; exact norm_heat_le _
      _ = ‖w a - w₀‖ := one_mul _
  simpa using h2.add h1

theorem kernel_eq_heat {σ τ : ℝ} (hσ : 0 < σ) (h : σ ≤ τ) (x y : V) :
    kernel τ x y = heat (τ - σ) (kernel σ x y) := by
  rw [heat_kernel (τ - σ) σ (sub_nonneg.2 h) hσ, sub_add_cancel]

theorem kernel_tendsto {α : Type*} {l : Filter α} {τ : α → ℝ} {x y : α → V} {τ₀ : ℝ} {x₀ y₀ : V}
    (h0 : 0 < τ₀) (hτ : Tendsto τ l (𝓝 τ₀)) (hx : Tendsto x l (𝓝 x₀)) (hy : Tendsto y l (𝓝 y₀)) :
    Tendsto (fun a => kernel (τ a) (x a) (y a)) l (𝓝 (kernel τ₀ x₀ y₀)) := by
  have hσ : 0 < τ₀ / 2 := half_pos h0
  have hx' : Tendsto (fun a => kernel (τ₀ / 2) (x a)) l (𝓝 (kernel (τ₀ / 2) x₀)) :=
    ((kernel (τ₀ / 2)).continuous.tendsto x₀).comp hx
  have hB : Tendsto (fun a => kernel (τ₀ / 2) (x a) (y a)) l (𝓝 (kernel (τ₀ / 2) x₀ y₀)) :=
    ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := V) (F := V)).continuous.tendsto
      (kernel (τ₀ / 2) x₀, y₀)).comp (hx'.prodMk_nhds hy)
  have hH := heat_tendsto (hτ.sub_const (τ₀ / 2)) hB
  have hev : ∀ᶠ a in l, τ₀ / 2 ≤ τ a := hτ.eventually (le_mem_nhds (half_lt_self h0))
  rw [kernel_eq_heat hσ (half_le_self h0.le) x₀ y₀]
  exact hH.congr' (hev.mono fun a ha => (kernel_eq_heat hσ ha (x a) (y a)).symm)

theorem kernel_opNorm_anti {σ τ : ℝ} (hσ : 0 < σ) (h : σ ≤ τ) : ‖kernel τ‖ ≤ ‖kernel σ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (norm_nonneg _) fun x y => ?_
  rw [kernel_eq_heat hσ h x y]
  calc ‖heat (τ - σ) (kernel σ x y)‖ ≤ ‖heat (τ - σ)‖ * ‖kernel σ x y‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖kernel σ x y‖ := by gcongr; exact norm_heat_le _
    _ ≤ ‖kernel σ‖ * ‖x‖ * ‖y‖ := by rw [one_mul]; exact ContinuousLinearMap.le_opNorm₂ _ _ _

theorem kernel_norm_le (hK : KernelSharpBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ → ∀ x y : V,
      ‖kernel τ x y‖ ≤ (C * τ ^ (-(3 / 4 : ℝ)) + C) * ‖x‖ * ‖y‖ := by
  obtain ⟨C, hC, hb⟩ := hK
  refine ⟨C, hC, fun τ hτ x y => ?_⟩
  have h3 : 0 ≤ C * τ ^ (-(3 / 4 : ℝ)) := mul_nonneg hC.le (rpow_nonneg hτ.le _)
  have hop : ‖kernel τ‖ ≤ C * τ ^ (-(3 / 4 : ℝ)) + C := by
    rcases le_or_gt τ 1 with h | h
    · linarith [hb τ hτ h]
    · have h1 := hb 1 one_pos le_rfl
      rw [one_rpow, mul_one] at h1
      have h2 := kernel_opNorm_anti one_pos h.le
      linarith
  calc ‖kernel τ x y‖ ≤ ‖kernel τ‖ * ‖x‖ * ‖y‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ (C * τ ^ (-(3 / 4 : ℝ)) + C) * ‖x‖ * ‖y‖ := by gcongr

theorem integrable_kernel (hK : KernelSharpBound) {U : ℝ → V} {t : ℝ} (ht : 0 ≤ t)
    (hU : ContinuousOn U (Icc 0 t)) :
    IntervalIntegrable (fun s => kernel (t - s) (U s) (U s)) volume 0 t := by
  obtain ⟨C, hC, hb⟩ := kernel_norm_le hK
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hU
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, ht⟩)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht]
  have hg : IntegrableOn (fun s => (C * (t - s) ^ (-(3 / 4 : ℝ)) + C) * M * M) (Ioo 0 t) := by
    have h1 : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(3 / 4 : ℝ))) volume 0 t := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := t) (b := 0)
        (r := -(3 / 4 : ℝ)) (by norm_num)).comp_sub_left t
      simpa using this
    have h0 : IntervalIntegrable (fun _ : ℝ => C) volume 0 t := intervalIntegrable_const
    have h2 := (((h1.const_mul C).add h0).mul_const M).mul_const M
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht).1 h2
  refine Integrable.mono' hg ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable_of_isSeparable (fun s hs => ?_) measurableSet_Ioo
      (TopologicalSpace.IsSeparable.of_separableSpace _)
    have hUs : ContinuousWithinAt U (Ioo 0 t) s := (hU s (Ioo_subset_Icc_self hs)).mono Ioo_subset_Icc_self
    exact kernel_tendsto (sub_pos.2 hs.2)
      (((continuous_const.sub continuous_id).tendsto s).mono_left nhdsWithin_le_nhds) hUs hUs
  · refine ae_restrict_of_forall_mem measurableSet_Ioo fun s hs => ?_
    have hu := hM s (Ioo_subset_Icc_self hs)
    have hA : 0 ≤ C * (t - s) ^ (-(3 / 4 : ℝ)) + C :=
      add_nonneg (mul_nonneg hC.le (rpow_nonneg (sub_pos.2 hs.2).le _)) hC.le
    calc ‖kernel (t - s) (U s) (U s)‖
        ≤ (C * (t - s) ^ (-(3 / 4 : ℝ)) + C) * ‖U s‖ * ‖U s‖ := hb _ (sub_pos.2 hs.2) _ _
      _ ≤ (C * (t - s) ^ (-(3 / 4 : ℝ)) + C) * M * M := by gcongr


theorem contDiff_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Space → E}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Ici 0 ×ˢ univ)) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (f t) :=
  hf.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun _ => ⟨ht, trivial⟩)

theorem divergence_nonneg {u₀ : Space → Space} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (h : IsSmoothSolution 1 u₀ u p) (t : ℝ) (ht : 0 ≤ t) (x : Space) : divergenceAt (u t) x = 0 := by
  set S : Set (ℝ × Space) := Ici 0 ×ˢ univ
  set F : ℝ × Space → Space := fun z => u z.1 z.2
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hD : ∀ τ, 0 ≤ τ → HasFDerivAt (u τ)
      ((fderivWithin ℝ F S (τ, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) x := by
    intro τ hτ
    have h1 : HasFDerivWithinAt F (fderivWithin ℝ F S (τ, x)) S (τ, x) :=
      ((h.smooth_velocity.differentiableOn (by simp)) (τ, x) ⟨hτ, trivial⟩).hasFDerivWithinAt
    have h2 := h1.comp x (hasFDerivAt_prodMk_right τ x).hasFDerivWithinAt (s := univ)
      (fun _ _ => ⟨hτ, trivial⟩)
    exact hasFDerivWithinAt_univ.1 h2
  set G : ℝ → ℝ := fun τ => ∑ i, (fderivWithin ℝ F S (τ, x) (0, unitVector i)) i
  have hG : ∀ τ, 0 ≤ τ → divergenceAt (u τ) x = G τ := by
    intro τ hτ
    simp only [divergenceAt, (hD τ hτ).fderiv, G]
    rfl
  have hc : ContinuousOn G (Ici 0) := by
    have h1 : ContinuousOn (fun τ : ℝ => fderivWithin ℝ F S (τ, x)) (Ici 0) :=
      (h.smooth_velocity.continuousOn_fderivWithin hS (by simp)).comp
        (continuous_id.prodMk continuous_const).continuousOn (fun τ hτ => ⟨hτ, trivial⟩)
    refine continuousOn_finsetSum _ fun i _ => ?_
    exact (PiLp.continuous_apply 2 _ i).comp_continuousOn (h1.clm_apply continuousOn_const)
  have hG0 : G 0 = 0 := by
    have h1 : Tendsto G (𝓝[>] 0) (𝓝 (G 0)) := (hc 0 (mem_Ici.2 le_rfl)).mono Ioi_subset_Ici_self
    have h2 : Tendsto G (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun τ hτ => by
        rw [← hG τ (le_of_lt hτ)]
        exact (h.incompressible τ hτ x).symm)
    exact tendsto_nhds_unique h1 h2
  rcases ht.lt_or_eq with h' | h'
  · exact h.incompressible t h' x
  · subst h'
    rw [hG 0 le_rfl, hG0]

theorem cell_subset : cell ⊆ Metric.closedBall (0 : Space) 2 := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  have hi : ∀ i, ‖x i‖ ^ 2 ≤ 1 := fun i => by
    rw [Real.norm_eq_abs, sq_abs]
    have := hx i
    nlinarith [this.1, this.2]
  have hs : ∑ i, ‖x i‖ ^ 2 ≤ 2 ^ 2 := by
    rw [Fin.sum_univ_three]
    nlinarith [hi 0, hi 1, hi 2]
  calc Real.sqrt (∑ i, ‖x i‖ ^ 2) ≤ Real.sqrt (2 ^ 2) := Real.sqrt_le_sqrt hs
    _ = 2 := Real.sqrt_sq (by norm_num)

theorem continuous_character (k : Lattice) : Continuous (character k) := by
  unfold character
  exact Complex.continuous_exp.comp ((continuous_const.mul
    (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id))).neg)

theorem continuous_complexify : Continuous complexify := by
  unfold complexify
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ i))

theorem complexify_sub (a b : Space) : complexify (a - b) = complexify a - complexify b := by
  ext i
  simp [complexify]

theorem integrableOn_cell {f : Space → Space} (hf : Continuous f) (k : Lattice) :
    IntegrableOn (fun x => character k x • complexify (f x)) cell :=
  (((continuous_character k).smul (continuous_complexify.comp hf)).continuousOn.integrableOn_compact
    (isCompact_closedBall 0 2)).mono_set cell_subset

theorem freqTrCoef_sub {f g : Space → Space} (hf : Continuous f) (hg : Continuous g) (k : Lattice) :
    freqTrCoef (fun x => f x - g x) k = freqTrCoef f k - freqTrCoef g k := by
  unfold freqTrCoef
  rw [← integral_sub (integrableOn_cell hf k) (integrableOn_cell hg k)]
  congr 1
  funext x
  rw [complexify_sub, smul_sub]

theorem continuous_sumSecondPartialsAt {f : Space → Space} (hf : ContDiff ℝ ∞ f) :
    Continuous (sumSecondPartialsAt f) := by
  unfold sumSecondPartialsAt
  refine continuous_finsetSum _ fun i _ => ?_
  exact continuous_eval_const _ |>.comp (hf.continuous_iteratedFDeriv (by norm_cast))

theorem continuous_gradientAt {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) :
    Continuous (gradientAt g) := by
  unfold gradientAt
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((hg.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const

theorem continuous_advectionAt {f : Space → Space} (hf : ContDiff ℝ ∞ f) :
    Continuous (advectionAt f) := by
  unfold advectionAt
  exact (hf.continuous_fderiv (by simp)).clm_apply hf.continuous

theorem mode_deriv (hF : FreqTrSeriesSpec) (hL : CoefSumSecondPartials) (hG : CoefGradient)
    (hA : CoefAdvection) (hT : CoefTimeDeriv)
    {u₀ : Space → Space} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (h : IsSmoothSolution 1 u₀ u p) (hu : ∀ t ≥ 0, IsPeriodic (u t))
    (hp : ∀ t ≥ 0, IsPeriodic (p t)) (hdiv : ∀ t, 0 ≤ t → ∀ x, divergenceAt (u t) x = 0)
    (k : Lattice) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun σ => freqTrCoef (u σ) k)
      ((-(4 * π ^ 2 * ‖freq k‖ ^ 2)) • freqTrCoef (u τ) k
        - divFree k (advCoef (toV (u τ)) (toV (u τ)) k)) τ := by
  have hφ : ContDiff ℝ ∞ (u τ) := contDiff_slice h.smooth_velocity hτ.le
  have hq : ContDiff ℝ ∞ (p τ) := contDiff_slice h.smooth_pressure hτ.le
  have hd := (hT u h.smooth_velocity hu k).2 τ hτ
  have hm : (fun x => deriv (fun σ => u σ x) τ) =
      fun x => (sumSecondPartialsAt (u τ) x - gradientAt (p τ) x) - advectionAt (u τ) x := by
    funext x
    have := h.momentum τ hτ x
    rw [one_smul] at this
    exact eq_sub_of_add_eq this
  have hlg : Continuous (fun x => sumSecondPartialsAt (u τ) x - gradientAt (p τ) x) :=
    (continuous_sumSecondPartialsAt hφ).sub (continuous_gradientAt hq)
  rw [hm, freqTrCoef_sub hlg (continuous_advectionAt hφ),
    freqTrCoef_sub (continuous_sumSecondPartialsAt hφ) (continuous_gradientAt hq),
    hL _ (hφ.of_le ENat.LEInfty.out) (hu τ hτ.le),
    hG _ (hq.of_le ENat.LEInfty.out) (hp τ hτ.le),
    hA _ hφ (hu τ hτ.le) (h.incompressible τ hτ)] at hd
  have hfix : ∀ σ, 0 ≤ σ → divFree k (freqTrCoef (u σ) k) = freqTrCoef (u σ) k := by
    intro σ hσ
    rw [← (hF _ (contDiff_slice h.smooth_velocity hσ) (hu σ hσ) (hdiv σ hσ)).1 k, divFree_coeff]
  set LR : Coef →L[ℝ] Coef := (divFreeL k).restrictScalars ℝ with hLR
  have hL' := LR.hasFDerivAt.comp_hasDerivAt τ hd
  have hev : (fun σ => freqTrCoef (u σ) k) =ᶠ[𝓝 τ] (LR ∘ fun σ => freqTrCoef (u σ) k) := by
    filter_upwards [Ioi_mem_nhds hτ] with σ hσ
    exact (hfix σ (le_of_lt hσ)).symm
  refine (hL'.congr_of_eventuallyEq hev).congr_deriv ?_
  have e2 : LR ((2 * π * Complex.I * scalarCoef (p τ) k) • latVec k) = 0 := by
    show divFreeL k ((2 * π * Complex.I * scalarCoef (p τ) k) • latVec k) = 0
    rw [map_smul, divFreeL_apply, divFree_latVec, smul_zero]
  rw [map_sub, map_sub, map_smul, e2, sub_zero]
  show _ • divFree k _ - divFree k _ = _
  rw [hfix τ hτ.le]

theorem variation_of_constants {c B : ℝ → Coef} {l t : ℝ} (ht : 0 ≤ t)
    (hc : ContinuousOn c (Icc 0 t)) (hB : ContinuousOn B (Icc 0 t))
    (hd : ∀ s ∈ Ioo 0 t, HasDerivAt c ((-l) • c s - B s) s) :
    c t = Real.exp (-(l * t)) • c 0 + ∫ s in (0 : ℝ)..t, (-Real.exp (-(l * (t - s)))) • B s := by
  have hg : ∀ s ∈ Ioo 0 t, HasDerivAt (fun s => Real.exp (l * s) • c s)
      (-(Real.exp (l * s) • B s)) s := by
    intro s hs
    have he : HasDerivAt (fun s => Real.exp (l * s)) (Real.exp (l * s) * l) s := by
      simpa using ((hasDerivAt_id s).const_mul l).exp
    refine (he.smul (hd s hs)).congr_deriv ?_
    rw [smul_sub, smul_smul, mul_neg, neg_smul]
    abel
  have hexp : Continuous (fun s : ℝ => Real.exp (l * s)) := by fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun s => Real.exp (l * s) • c s) (f' := fun s => -(Real.exp (l * s) • B s)) ht
    (hexp.continuousOn.smul hc) hg
    ((hexp.continuousOn.smul hB).neg.intervalIntegrable_of_Icc ht)
  simp only [mul_zero, Real.exp_zero, one_smul] at hint
  have e1 : (fun s => (-Real.exp (-(l * (t - s)))) • B s) =
      fun s => Real.exp (-(l * t)) • (-(Real.exp (l * s) • B s)) := by
    funext s
    rw [show -(l * (t - s)) = -(l * t) + l * s by ring, smul_neg, smul_smul, ← Real.exp_add,
      neg_smul]
  rw [e1, intervalIntegral.integral_smul, hint, smul_sub,
    smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]
  abel

theorem mode_identity (hF : FreqTrSeriesSpec) (hL : CoefSumSecondPartials) (hG : CoefGradient)
    (hA : CoefAdvection) (hT : CoefTimeDeriv)
    {u₀ : Space → Space} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (h : IsSmoothSolution 1 u₀ u p) (hu : ∀ t ≥ 0, IsPeriodic (u t))
    (hp : ∀ t ≥ 0, IsPeriodic (p t)) (hdiv : ∀ t, 0 ≤ t → ∀ x, divergenceAt (u t) x = 0)
    (hUc : ContinuousOn (fun t => toV (u t)) (Ici 0)) {t : ℝ} (ht : 0 ≤ t) (k : Lattice) :
    coeff (toV (u t)) k = heatFactor t k • coeff (toV (u 0)) k +
      ∫ s in (0 : ℝ)..t, coeff (kernel (t - s) (toV (u s)) (toV (u s))) k := by
  have hcU : ∀ s, 0 ≤ s → coeff (toV (u s)) k = freqTrCoef (u s) k := fun s hs =>
    (hF _ (contDiff_slice h.smooth_velocity hs) (hu s hs) (hdiv s hs)).1 k
  have hpos : 0 < heatFactor 1 k := Real.exp_pos _
  have hB : ∀ s, divFree k (advCoef (toV (u s)) (toV (u s)) k) =
      (-(heatFactor 1 k)⁻¹) • coeff (kernel 1 (toV (u s)) (toV (u s))) k := by
    intro s
    rw [coeff_kernel 1 one_pos, divFree_add, ← two_smul ℝ (divFree k _), smul_smul, smul_smul,
      show -(heatFactor 1 k)⁻¹ * (-(1 / 2) * heatFactor 1 k) * 2 = 1 by field_simp, one_smul]
  have hUt : ContinuousOn (fun s => toV (u s)) (Icc 0 t) := hUc.mono Icc_subset_Ici_self
  have hBc : ContinuousOn (fun s => divFree k (advCoef (toV (u s)) (toV (u s)) k)) (Icc 0 t) := by
    simp only [hB]
    exact ((coeffL k).continuous.comp_continuousOn
      (((kernel 1).continuous.comp_continuousOn hUt).clm_apply hUt)).const_smul (-(heatFactor 1 k)⁻¹)
  have hcc : ContinuousOn (fun s => freqTrCoef (u s) k) (Icc 0 t) :=
    (hT u h.smooth_velocity hu k).1.mono Icc_subset_Ici_self
  have hv := variation_of_constants ht hcc hBc
    (fun s hs => mode_deriv hF hL hG hA hT h hu hp hdiv k hs.1)
  beta_reduce at hv
  have hh : heatFactor t k = Real.exp (-(4 * π ^ 2 * ‖freq k‖ ^ 2 * t)) := by
    simp only [heatFactor, max_eq_left ht]
  rw [hcU t ht, hcU 0 le_rfl, hv, hh]
  congr 1
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    rw [ae_iff]
    simp
  filter_upwards [hne] with s hs hmem
  rw [uIoc_of_le ht] at hmem
  have hst : 0 < t - s := sub_pos.2 (lt_of_le_of_ne hmem.2 hs)
  rw [coeff_kernel _ hst, divFree_add, ← two_smul ℝ (divFree k _), smul_smul, heatFactor,
    max_eq_left hst.le]
  congr 1
  ring

end Internal.Mild

open Internal.Mild in
theorem smoothPeriodicIsMild (hK : KernelSharpBound) (hD : CoefDeriv) (hL : CoefSumSecondPartials)
    (hG : CoefGradient) (hF : FreqTrSeriesSpec) (hA : CoefAdvection) (hT : CoefTimeDeriv)
    (hC : ToVContinuous) : SmoothPeriodicIsMild := by
  intro u₀ u p h hu hp T _
  have hdiv : ∀ t, 0 ≤ t → ∀ x, divergenceAt (u t) x = 0 := fun t ht x =>
    divergence_nonneg h t ht x
  have hUc : ContinuousOn (fun t => toV (u t)) (Ici 0) := hC u h.smooth_velocity hu hdiv
  refine ⟨hUc.mono Icc_subset_Ici_self, fun t ht => ?_⟩
  have hI : IntervalIntegrable (fun s => kernel (t - s) (toV (u s)) (toV (u s))) volume 0 t :=
    integrable_kernel (U := fun s => toV (u s)) hK ht.1 (hUc.mono Icc_subset_Ici_self)
  refine ⟨hI, ?_⟩
  apply coeff_injective
  intro k
  have e : coeff (heat (t - 0) (toV (u 0)) +
      ∫ s in (0 : ℝ)..t, kernel (t - s) (toV (u s)) (toV (u s))) k =
      coeff (heat t (toV (u 0))) k +
        ∫ s in (0 : ℝ)..t, coeff (kernel (t - s) (toV (u s)) (toV (u s))) k := by
    rw [sub_zero, ← coeffL_apply, map_add, ← (coeffL k).intervalIntegral_comp_comm hI]
    rfl
  rw [e, coeff_heat]
  exact mode_identity hF hL hG hA hT h hu hp hdiv hUc ht.1 k

end Breakdown.Periodic
