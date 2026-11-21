import Breakdown.Cert.CoerciveSmoothApproxKernel

open scoped ContDiff ENNReal Topology Convolution
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothApprox

theorem lintegral_mul_sixth_le {X : Type*} [MeasurableSpace X] {μ : Measure X} {A B W : X → ℝ≥0∞}
    (hA : AEMeasurable A μ) (hB : AEMeasurable B μ) (hW : AEMeasurable W μ)
    (hW0 : ∀ x, W x ≠ 0) (hWt : ∀ x, W x ≠ ⊤) :
    (∫⁻ x, A x * B x ∂μ) ^ 6 ≤ (∫⁻ x, A x * W x ∂μ) ^ 5 * ∫⁻ x, A x * (W x)⁻¹ ^ 5 * B x ^ 6 ∂μ := by
  have hpq : (6 / 5 : ℝ).HolderConjugate 6 :=
    (Real.holderConjugate_iff_eq_conjExponent (by norm_num)).2 (by norm_num)
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    (f := fun x => (A x * W x) ^ (5 / 6 : ℝ))
    (g := fun x => A x ^ (1 / 6 : ℝ) * (W x)⁻¹ ^ (5 / 6 : ℝ) * B x)
    ((hA.mul hW).pow_const _) (((hA.pow_const _).mul (hW.inv.pow_const _)).mul hB)
  have e1 : ∀ x, (A x * W x) ^ (5 / 6 : ℝ) * (A x ^ (1 / 6 : ℝ) * (W x)⁻¹ ^ (5 / 6 : ℝ) * B x) =
      A x * B x := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    calc A x ^ (5 / 6 : ℝ) * W x ^ (5 / 6 : ℝ) * (A x ^ (1 / 6 : ℝ) * (W x)⁻¹ ^ (5 / 6 : ℝ) * B x)
        = (A x ^ (5 / 6 : ℝ) * A x ^ (1 / 6 : ℝ)) * (W x * (W x)⁻¹) ^ (5 / 6 : ℝ) * B x := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
          ring
      _ = A x * B x := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num),
            ENNReal.mul_inv_cancel (hW0 x) (hWt x)]
          norm_num
  have e2 : ∀ x, ((A x * W x) ^ (5 / 6 : ℝ)) ^ (6 / 5 : ℝ) = A x * W x := by
    intro x
    rw [← ENNReal.rpow_mul]
    norm_num
  have e3 : ∀ x, (A x ^ (1 / 6 : ℝ) * (W x)⁻¹ ^ (5 / 6 : ℝ) * B x) ^ (6 : ℝ) =
      A x * (W x)⁻¹ ^ 5 * B x ^ 6 := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    have h5 : (5 / 6 : ℝ) * 6 = ((5 : ℕ) : ℝ) := by norm_num
    have h6 : (6 : ℝ) = ((6 : ℕ) : ℝ) := by norm_num
    rw [h5, ENNReal.rpow_natCast, h6, ENNReal.rpow_natCast]
    norm_num
  simp only [Pi.mul_apply, e1, e2, e3] at h
  calc (∫⁻ x, A x * B x ∂μ) ^ 6
      ≤ ((∫⁻ x, A x * W x ∂μ) ^ (1 / (6 / 5) : ℝ) *
          (∫⁻ x, A x * (W x)⁻¹ ^ 5 * B x ^ 6 ∂μ) ^ (1 / 6 : ℝ)) ^ 6 := by gcongr
    _ = (∫⁻ x, A x * W x ∂μ) ^ 5 * ∫⁻ x, A x * (W x)⁻¹ ^ 5 * B x ^ 6 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (n := 6), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        have h5 : (1 / (6 / 5) : ℝ) * ((6 : ℕ) : ℝ) = ((5 : ℕ) : ℝ) := by norm_num
        have h1 : (1 / 6 : ℝ) * ((6 : ℕ) : ℝ) = 1 := by norm_num
        rw [h5, h1, ENNReal.rpow_natCast, ENNReal.rpow_one]

theorem slice_sixth_le {f : Space → Space} {F : Space → (Space →L[ℝ] Space)}
    (hg : IsWeakGradient f F) (hdiv : ∀ᵐ y, ∑ i : Fin 3, (F y (unitVector i)) i = 0)
    (h6 : ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 6) < ⊤) (h2 : ∫⁻ y, ENNReal.ofReal (matSq (F y)) < ⊤) :
    ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 6) ≤
      ENNReal.ofReal ‖(Freq.velocity : Freq.X →L[ℝ] Freq.L6R)‖ ^ 6 *
        (∫⁻ y, ENNReal.ofReal (matSq (F y))) ^ 3 := by
  obtain ⟨x, hx1, hx2⟩ := PerturbationFacts.slice_embed hg hdiv h6 h2
  have e1 : ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 6) =
      ∫⁻ y, ‖(Freq.velocity x : Space → Space) y‖ₑ ^ (6 : ℝ) := by
    refine lintegral_congr_ae (hx1.mono fun y hy => ?_)
    dsimp only
    rw [hy, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num,
      ENNReal.rpow_natCast]
  have e2 : ∫⁻ y, ‖(Freq.velocity x : Space → Space) y‖ₑ ^ (6 : ℝ) =
      ENNReal.ofReal ‖Freq.velocity x‖ ^ 6 := by
    have h := lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := (Freq.velocity x : Space → Space))
      (μ := volume) (q := 6) (by norm_num)
    rw [h, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
      eLpNorm_eq_eLpNorm' (by norm_num) (by simp)]
    simp only [ENNReal.toReal_ofNat]
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  have hb : ENNReal.ofReal ‖Freq.velocity x‖ ≤
      ENNReal.ofReal ‖(Freq.velocity : Freq.X →L[ℝ] Freq.L6R)‖ * ENNReal.ofReal ‖x‖ := by
    rw [← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal ((Freq.velocity : Freq.X →L[ℝ] Freq.L6R).le_opNorm x)
  have hx3 : (∫⁻ y, ENNReal.ofReal (matSq (F y))) ^ 3 = ENNReal.ofReal ‖x‖ ^ 6 := by
    rw [← hx2, ENNReal.ofReal_pow (norm_nonneg x) 2]
    ring
  rw [e1, e2, hx3, ← mul_pow]
  exact pow_le_pow_left₀ zero_le hb 6

theorem lintegral_Ioc_window (Φ : ℝ → ℝ≥0∞) (hper : Function.Periodic Φ 1) (c : ℝ) :
    ∀ k : ℕ, ∫⁻ s in Set.Ioc c (c + k), Φ s ≤ k * ∫⁻ s in Set.Icc (0 : ℝ) 1, Φ s := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hu : Set.Ioc c (c + ((k + 1 : ℕ) : ℝ)) = Set.Ioc c (c + k) ∪ Set.Ioc (c + k) (c + k + 1) := by
      rw [Set.Ioc_union_Ioc_eq_Ioc (by simp) (by linarith)]
      push_cast
      ring_nf
    rw [hu]
    refine (lintegral_union_le _ _ _).trans ?_
    rw [Breakdown.Cert.Internal.CoerciveBordered.lintegral_Ioc_periodic Φ hper (c + k)]
    push_cast
    rw [add_mul, one_mul]
    gcongr

theorem timeBump_abs_le (n : ℕ) (s : ℝ) (h : (timeBump n).normed volume s ≠ 0) : |s| ≤ 2 := by
  have hm : s ∈ Function.support ((timeBump n).normed volume) := h
  rw [(timeBump n).support_normed_eq, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hm
  have hr : (timeBump n).rOut = 2 / ((n : ℝ) + 1) := rfl
  have hle : 2 / ((n : ℝ) + 1) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  linarith

theorem kernel_fst_abs_le (n : ℕ) (t : ℝ × Space) (ht : kernel n t ≠ 0) : |t.1| ≤ 2 := by
  refine timeBump_abs_le n t.1 ?_
  intro h0
  exact ht (by simp [kernel, h0])

theorem mollify_sixth_power_bound {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (n : ℕ) :
    ∀ σ, ∫⁻ y, ENNReal.ofReal (‖mollify n v σ y‖ ^ 6) < ⊤ := by
  intro σ
  have hH := volume_prod_invariantClass
  set c : ℝ := ‖(Freq.velocity : Freq.X →L[ℝ] Freq.L6R)‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  set F : ℝ → ℝ≥0∞ := fun s => ∫⁻ y, ENNReal.ofReal (matSq (G s y)) with hFdef
  have hFa : AEMeasurable F volume := PerturbationFacts.aemeasurable_matNorm hv.measurable_gradient
  have hFper : Function.Periodic F 1 := fun s => by simp only [hFdef, hv.periodic_gradient s]
  set Fm : ℝ → ℝ≥0∞ := hFa.mk F with hFmdef
  have hFmm : Measurable Fm := hFa.measurable_mk
  have hFe : F =ᵐ[volume] Fm := hFa.ae_eq_mk
  set M : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (1 + c * (1 + (Fm s).toReal)) with hMdef
  have hMm : Measurable M :=
    (measurable_const.add (measurable_const.mul (measurable_const.add hFmm.ennreal_toReal))).ennreal_ofReal
  have hMpos : ∀ s, 0 < 1 + c * (1 + (Fm s).toReal) := fun s => by positivity
  have hM0 : ∀ s, M s ≠ 0 := fun s => (ENNReal.ofReal_pos.2 (hMpos s)).ne'
  have hMt : ∀ s, M s ≠ ⊤ := fun s => ENNReal.ofReal_ne_top
  set Wn : Set ℝ := Set.Ioc (σ - 3) (σ - 3 + ((5 : ℕ) : ℝ)) with hWn
  have hWm : MeasurableSet Wn := measurableSet_Ioc
  have hWin : ∫⁻ s in Wn, F s < ⊤ := by
    refine lt_of_le_of_lt (lintegral_Ioc_window F hFper (σ - 3) 5) ?_
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top 5) hv.gradient_finite
  have hsupp : ∀ t1 : ℝ, |t1| ≤ 2 → σ - t1 ∈ Wn := by
    intro t1 h
    rw [abs_le] at h
    rw [hWn, Set.mem_Ioc]
    push_cast
    constructor <;> linarith
  set S : ℝ → ℝ≥0∞ := fun s => ∫⁻ y, ENNReal.ofReal (‖v s y‖ ^ 6) with hSdef
  have hSb : ∀ᵐ s, s ∈ Wn → S s ≤ M s ^ 6 := by
    have hfin : ∀ᵐ s, s ∈ Wn → F s < ⊤ :=
      (ae_restrict_iff' hWm).1 (ae_lt_top' hFa.restrict hWin.ne)
    filter_upwards [hv.weak_gradient, hv.divergence_free, hv.sixth_power, hfin, hFe] with
      s h1 h2 h3 h4 h5 hs
    have hF := h4 hs
    refine (slice_sixth_le h1 h2 h3 hF).trans ?_
    obtain ⟨f, hf0, hfF⟩ : ∃ f : ℝ, 0 ≤ f ∧ F s = ENNReal.ofReal f :=
      ⟨(F s).toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hF.ne).symm⟩
    have hM : M s = ENNReal.ofReal (1 + c * (1 + f)) := by
      show ENNReal.ofReal (1 + c * (1 + (Fm s).toReal)) = _
      rw [← h5, hfF, ENNReal.toReal_ofReal hf0]
    have hF' : ∫⁻ y, ENNReal.ofReal (matSq (G s y)) = ENNReal.ofReal f := hfF
    rw [hM, hF', ← hc, ← ENNReal.ofReal_pow hc0, ← ENNReal.ofReal_pow hf0,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h6 : f ^ 3 ≤ (1 + f) ^ 6 := by
      calc f ^ 3 ≤ ((1 + f) ^ 2) ^ 3 := pow_le_pow_left₀ hf0 (by nlinarith) 3
        _ = (1 + f) ^ 6 := by ring
    calc c ^ 6 * f ^ 3 ≤ c ^ 6 * (1 + f) ^ 6 := by gcongr
      _ = (c * (1 + f)) ^ 6 := by ring
      _ ≤ (1 + c * (1 + f)) ^ 6 := pow_le_pow_left₀ (by positivity) (by linarith) 6
  have hVa : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume := hv.measurable_velocity
  set V : ℝ × Space → Space := hVa.mk _ with hVdef
  have hVs : StronglyMeasurable V := hVa.stronglyMeasurable_mk
  have hVe : (fun z : ℝ × Space => v z.1 z.2) =ᵐ[volume] V := hVa.ae_eq_mk
  have hVm : Measurable (fun z => ‖V z‖ₑ) := hVs.measurable.enorm
  set S' : ℝ → ℝ≥0∞ := fun s => ∫⁻ y, ‖V (s, y)‖ₑ ^ 6 with hS'def
  have hSS : ∀ᵐ s, S' s = S s := by
    have h := hVe
    rw [Measure.volume_eq_prod] at h
    filter_upwards [Measure.ae_ae_of_ae_prod h] with s hs
    refine lintegral_congr_ae (hs.mono fun y hy => ?_)
    have hy' : v s y = V (s, y) := hy
    show ‖V (s, y)‖ₑ ^ 6 = ENNReal.ofReal (‖v s y‖ ^ 6)
    rw [← hy', ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hcomb : ∀ᵐ s, s ∈ Wn → S' s ≤ M s ^ 6 := by
    filter_upwards [hSS, hSb] with s h1 h2 hs
    rw [h1]
    exact h2 hs
  have hq : Measure.QuasiMeasurePreserving (fun t : ℝ × Space => σ - t.1) volume volume := by
    have h1 := (quasiMeasurePreserving_sub_left (volume : Measure ℝ) σ).comp
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ)) (ν := (volume : Measure Space)))
    rw [Measure.volume_eq_prod]
    exact h1
  have hpt : ∀ y, ‖mollify n v σ y‖ₑ ≤ ∫⁻ t, ‖kernel n t‖ₑ * ‖V ((σ, y) - t)‖ₑ := by
    intro y
    have e : mollify n v σ y = ∫ t, kernel n t • V ((σ, y) - t) := by
      simp only [mollify, convolution_def, ContinuousLinearMap.lsmul_apply]
      refine integral_congr_ae ?_
      have := (quasiMeasurePreserving_sub_left (volume : Measure (ℝ × Space)) (σ, y)).ae_eq hVe
      filter_upwards [this] with t ht
      have ht' : joint v ((σ, y) - t) = V ((σ, y) - t) := ht
      rw [ht']
    rw [e]
    exact (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (by simp only [enorm_smul]))
  set W : ℝ × Space → ℝ≥0∞ := fun t => M (σ - t.1) with hWdef
  have hWmeas : Measurable W := hMm.comp (measurable_const.sub measurable_fst)
  have hKm : Measurable (fun t : ℝ × Space => ‖kernel n t‖ₑ) :=
    (kernel_contDiff n).continuous.measurable.enorm
  set I1 : ℝ≥0∞ := ∫⁻ t, ‖kernel n t‖ₑ * W t with hI1d
  have hWM : ∫⁻ s in Wn, M s < ⊤ := by
    have hle : ∀ s, M s ≤ ENNReal.ofReal (1 + c) + ENNReal.ofReal c * Fm s := by
      intro s
      calc M s = ENNReal.ofReal ((1 + c) + c * (Fm s).toReal) := by
            show ENNReal.ofReal (1 + c * (1 + (Fm s).toReal)) = _
            congr 1
            ring
        _ ≤ ENNReal.ofReal (1 + c) + ENNReal.ofReal (c * (Fm s).toReal) := ENNReal.ofReal_add_le
        _ ≤ ENNReal.ofReal (1 + c) + ENNReal.ofReal c * Fm s := by
            rw [ENNReal.ofReal_mul hc0]
            gcongr
            exact ENNReal.ofReal_toReal_le
    refine lt_of_le_of_lt (lintegral_mono hle) ?_
    rw [lintegral_add_left measurable_const, setLIntegral_const, lintegral_const_mul _ hFmm,
      ← lintegral_congr_ae (ae_restrict_of_ae hFe)]
    refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hWin⟩
    rw [hWn, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hI1 : I1 < ⊤ := by
    obtain ⟨C, hC⟩ := ((timeBump n).continuous_normed (μ := volume)).bounded_above_of_compact_support
      ((timeBump n).hasCompactSupport_normed (μ := volume))
    have hA : Measurable (fun s => ‖(timeBump n).normed volume s‖ₑ * M (σ - s)) :=
      (timeBump n).continuous_normed.measurable.enorm.mul (hMm.comp (measurable_const.sub measurable_id))
    have e : I1 = (∫⁻ s, ‖(timeBump n).normed volume s‖ₑ * M (σ - s)) *
        ∫⁻ z, ‖(spaceBump n).normed volume z‖ₑ := by
      rw [hI1d, Measure.volume_eq_prod, ← lintegral_prod_mul hA.aemeasurable
        (spaceBump n).continuous_normed.measurable.enorm.aemeasurable]
      refine lintegral_congr fun t => ?_
      simp only [hWdef, kernel, enorm_mul]
      ring
    rw [e]
    refine ENNReal.mul_lt_top ?_ ((spaceBump n).integrable_normed (μ := volume)).2
    have hb : ∀ s, ‖(timeBump n).normed volume s‖ₑ * M (σ - s) ≤
        ENNReal.ofReal C * Wn.indicator M (σ - s) := by
      intro s
      by_cases h0 : (timeBump n).normed volume s = 0
      · simp [h0]
      · rw [Set.indicator_of_mem (hsupp s (timeBump_abs_le n s h0))]
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hC s)
    refine lt_of_le_of_lt (lintegral_mono hb) ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_sub_left_eq_self (fun s => Wn.indicator M s) σ, lintegral_indicator hWm]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hWM
  have hpt6 : ∀ y, ENNReal.ofReal (‖mollify n v σ y‖ ^ 6) ≤
      I1 ^ 5 * ∫⁻ t, ‖kernel n t‖ₑ * (W t)⁻¹ ^ 5 * ‖V ((σ, y) - t)‖ₑ ^ 6 := by
    intro y
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    refine (pow_le_pow_left₀ zero_le (hpt y) 6).trans ?_
    exact lintegral_mul_sixth_le hKm.aemeasurable
      (hVm.comp (measurable_const.sub measurable_id)).aemeasurable hWmeas.aemeasurable
      (fun t => hM0 _) (fun t => hMt _)
  have hmap : Measurable (fun p : Space × (ℝ × Space) => (σ, p.1) - p.2) :=
    ((continuous_const.prodMk continuous_fst).sub continuous_snd).measurable
  calc ∫⁻ y, ENNReal.ofReal (‖mollify n v σ y‖ ^ 6)
      ≤ ∫⁻ y, I1 ^ 5 * ∫⁻ t, ‖kernel n t‖ₑ * (W t)⁻¹ ^ 5 * ‖V ((σ, y) - t)‖ₑ ^ 6 :=
        lintegral_mono hpt6
    _ = I1 ^ 5 * ∫⁻ t, ∫⁻ y, ‖kernel n t‖ₑ * (W t)⁻¹ ^ 5 * ‖V ((σ, y) - t)‖ₑ ^ 6 := by
        rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top hI1.ne)]
        congr 1
        refine lintegral_lintegral_swap (f := fun y t => ‖kernel n t‖ₑ * (W t)⁻¹ ^ 5 *
          ‖V ((σ, y) - t)‖ₑ ^ 6) ?_
        exact (((hKm.comp measurable_snd).mul ((hWmeas.comp measurable_snd).inv.pow_const 5)).mul
          ((hVm.comp hmap).pow_const 6)).aemeasurable
    _ = I1 ^ 5 * ∫⁻ t, ‖kernel n t‖ₑ * (W t)⁻¹ ^ 5 * S' (σ - t.1) := by
        congr 1
        refine lintegral_congr fun t => ?_
        have hy : Measurable (fun y : Space => ‖V ((σ, y) - t)‖ₑ ^ 6) :=
          (hVm.comp ((continuous_const.prodMk continuous_id).sub continuous_const).measurable).pow_const 6
        rw [lintegral_const_mul _ hy]
        congr 1
        exact lintegral_sub_right_eq_self (μ := (volume : Measure Space))
          (fun y => ‖V (σ - t.1, y)‖ₑ ^ 6) t.2
    _ ≤ I1 ^ 5 * I1 := by
        refine mul_le_mul' le_rfl (lintegral_mono_ae ?_)
        filter_upwards [hq.ae hcomb] with t ht
        by_cases hk : kernel n t = 0
        · simp [hk]
        · have hs := ht (hsupp t.1 (kernel_fst_abs_le n t hk))
          rw [mul_assoc]
          refine mul_le_mul' le_rfl ?_
          calc (W t)⁻¹ ^ 5 * S' (σ - t.1) ≤ (W t)⁻¹ ^ 5 * W t ^ 6 := mul_le_mul' le_rfl hs
            _ = W t := by
              rw [show W t ^ 6 = W t ^ 5 * W t from pow_succ _ 5, ← mul_assoc, ← mul_pow, ENNReal.inv_mul_cancel (hM0 _) (hMt _), one_pow,
                one_mul]
    _ = I1 ^ 6 := by ring
    _ < ⊤ := ENNReal.pow_lt_top hI1

end Internal.SmoothApprox

end Coercive

end Breakdown
