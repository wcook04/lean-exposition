import Breakdown.Torus.StatementsApproxSteps
import Breakdown.Torus.Forced
import Breakdown.Torus.ForceSmoothing
import Breakdown.Transfer.Exports

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace ApproxResidual.Internal

def shift (x : Space) : Space := ∑ i, (round (x i - center i) : ℝ) • unitVector i

theorem wrap_eq_sub_shift (x : Space) : wrap x = x - shift x := rfl

theorem center_apply (j : Fin 3) : center j = 1 / 2 := by
  simp [center, unitVector, Pi.single_apply]

theorem shift_apply (x : Space) (j : Fin 3) : shift x j = round (x j - 1 / 2) := by
  simp [shift, unitVector, Pi.single_apply, center_apply]

theorem coord_le_dist (v w : Space) (j : Fin 3) : |v j - w j| ≤ dist v w := by
  rw [dist_eq_norm]
  have := PiLp.norm_apply_le (v - w) j
  rwa [Real.norm_eq_abs, PiLp.sub_apply] at this

theorem round_eq_of_close {d e : ℤ} (h : |(d : ℝ) - e| < 1) : d = e := by
  have h' : |d - e| < 1 := by exact_mod_cast h
  have := abs_lt.mp h'
  omega

theorem shift_eq_of_close {x y : Space}
    (h : ∀ j, |(round (y j - 1 / 2) : ℝ) - round (x j - 1 / 2)| < 1) : shift y = shift x := by
  ext j
  rw [shift_apply, shift_apply, round_eq_of_close (h j)]

theorem wrap_local {E : Type*} [Zero E] {f : Space → E} (hf : ∀ v, f v ≠ 0 → dist v center ≤ 1 / 8)
    (x y : Space) (hy : dist y x < 1 / 4) : f (wrap y) = f (y - shift x) := by
  have key : (∀ j, |(round (y j - 1 / 2) : ℝ) - round (x j - 1 / 2)| < 1) → f (wrap y) = f (y - shift x) := by
    intro h
    rw [wrap_eq_sub_shift, shift_eq_of_close h]
  by_cases h1 : f (wrap y) = 0
  · by_cases h2 : f (y - shift x) = 0
    · rw [h1, h2]
    · refine key fun j => ?_
      have a1 := (coord_le_dist _ _ j).trans (hf _ h2)
      rw [PiLp.sub_apply, shift_apply, center_apply] at a1
      have a2 := abs_sub_round (y j - 1 / 2)
      rw [abs_le] at a1 a2
      rw [abs_lt]
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  · refine key fun j => ?_
    have a1 := (coord_le_dist _ _ j).trans (hf _ h1)
    rw [wrap_eq_sub_shift, PiLp.sub_apply, shift_apply, center_apply] at a1
    have a2 := (coord_le_dist y x j).trans hy.le
    have a3 := abs_sub_round (x j - 1 / 2)
    rw [abs_le] at a1 a2 a3
    rw [abs_lt]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]

theorem wrap_eventually {E : Type*} [Zero E] {f : Space → E}
    (hf : ∀ v, f v ≠ 0 → dist v center ≤ 1 / 8) (x : Space) :
    (fun y => f (wrap y)) =ᶠ[𝓝 x] fun y => f (y - shift x) := by
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1 / 4)] with y hy
  exact wrap_local hf x y hy

theorem fderiv_wrap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Space → E}
    (hf : ∀ v, f v ≠ 0 → dist v center ≤ 1 / 8) (x : Space) :
    fderiv ℝ (fun y => f (wrap y)) x = fderiv ℝ f (wrap x) := by
  rw [(wrap_eventually hf x).fderiv_eq, fderiv_comp_sub, wrap_eq_sub_shift]

theorem iteratedFDeriv_wrap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Space → E}
    (hf : ∀ v, f v ≠ 0 → dist v center ≤ 1 / 8) (n : ℕ) (x : Space) :
    iteratedFDeriv ℝ n (fun y => f (wrap y)) x = iteratedFDeriv ℝ n f (wrap x) := by
  rw [((wrap_eventually hf x).iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_comp_sub, wrap_eq_sub_shift]

theorem contDiffOn_wrap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set ℝ}
    {Φ : ℝ × Space → E} (hΦ : ContDiffOn ℝ ∞ Φ (S ×ˢ univ))
    (hsupp : ∀ t ∈ S, ∀ v, Φ (t, v) ≠ 0 → dist v center ≤ 1 / 8) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => Φ (z.1, wrap z.2)) (S ×ˢ univ) := by
  apply contDiffOn_of_locally_contDiffOn
  rintro ⟨t, x⟩ -
  refine ⟨univ ×ˢ Metric.ball x (1 / 4), isOpen_univ.prod Metric.isOpen_ball,
    ⟨mem_univ _, Metric.mem_ball_self (by norm_num)⟩, ?_⟩
  have hc : ContDiffOn ℝ ∞ (fun z : ℝ × Space => Φ (z.1, z.2 - shift x)) (S ×ˢ univ) :=
    hΦ.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const)).contDiffOn
      (fun z hz => ⟨hz.1, mem_univ _⟩)
  refine (hc.mono inter_subset_left).congr fun z hz => ?_
  exact wrap_local (f := fun v => Φ (z.1, v)) (hsupp z.1 hz.1.1) x z.2 hz.2.2

theorem continuousOn_wrap {E : Type*} [NormedAddCommGroup E] {S : Set ℝ}
    {Φ : ℝ × Space → E} (hΦ : ContinuousOn Φ (S ×ˢ univ))
    (hsupp : ∀ t ∈ S, ∀ v, Φ (t, v) ≠ 0 → dist v center ≤ 1 / 8) :
    ContinuousOn (fun z : ℝ × Space => Φ (z.1, wrap z.2)) (S ×ˢ univ) := by
  apply continuousOn_of_locally_continuousOn
  rintro ⟨t, x⟩ -
  refine ⟨univ ×ˢ Metric.ball x (1 / 4), isOpen_univ.prod Metric.isOpen_ball,
    ⟨mem_univ _, Metric.mem_ball_self (by norm_num)⟩, ?_⟩
  have hc : ContinuousOn (fun z : ℝ × Space => Φ (z.1, z.2 - shift x)) (S ×ˢ univ) :=
    hΦ.comp (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousOn
      (fun z hz => ⟨hz.1, mem_univ _⟩)
  refine (hc.mono inter_subset_left).congr fun z hz => ?_
  exact wrap_local (f := fun v => Φ (z.1, v)) (hsupp z.1 hz.1.1) x z.2 hz.2.2

theorem wrap_add_unit (x : Space) (i : Fin 3) : wrap (x + unitVector i) = wrap x := by
  ext j
  rw [wrap_eq_sub_shift, wrap_eq_sub_shift, PiLp.sub_apply, PiLp.sub_apply, shift_apply, shift_apply,
    PiLp.add_apply]
  by_cases h : j = i
  · subst h
    have e : unitVector j j = 1 := by simp [unitVector]
    rw [e, show x j + 1 - 1 / 2 = (x j - 1 / 2) + 1 by ring, round_add_one]
    push_cast
    ring
  · have e : unitVector i j = 0 := by simp [unitVector, h]
    rw [e, add_zero]

theorem isPeriodic_wrap {E : Type*} (f : Space → E) : IsPeriodic (fun x => f (wrap x)) := by
  intro i x
  simp only [wrap_add_unit]

theorem slice_fderiv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Space → E}
    {O : Set (ℝ × Space)} (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) O)
    {t : ℝ} {v : Space} (hz : (t, v) ∈ O) (w : Space) :
    fderiv ℝ (f t) v w = fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (t, v) (0, w) := by
  have hd : DifferentiableAt ℝ (fun z : ℝ × Space => f z.1 z.2) (t, v) :=
    (hf.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hz)
  have h : HasFDerivAt (f t) ((fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (t, v)).comp
      (ContinuousLinearMap.inr ℝ ℝ Space)) v :=
    hd.hasFDerivAt.comp v (hasFDerivAt_prodMk_right t v)
  rw [h.fderiv]
  rfl

theorem time_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Space → E}
    {O : Set (ℝ × Space)} (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) O)
    {t : ℝ} {v : Space} (hz : (t, v) ∈ O) :
    deriv (fun τ => f τ v) t = fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (t, v) (1, 0) := by
  have hd : DifferentiableAt ℝ (fun z : ℝ × Space => f z.1 z.2) (t, v) :=
    (hf.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hz)
  have h := HasFDerivAt.comp (g := fun z : ℝ × Space => f z.1 z.2) t hd.hasFDerivAt
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) t v)
  rw [show (fun τ => f τ v) = (fun z : ℝ × Space => f z.1 z.2) ∘ (fun e => (e, v)) from rfl,
    h.hasDerivAt.deriv]
  rfl

theorem ssp_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Space → E}
    {O : Set (ℝ × Space)} (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) O)
    {t : ℝ} {v : Space} (ht : ∀ y, (t, y) ∈ O) (e : Space) :
    iteratedFDeriv ℝ 2 (f t) v ![e, e] =
      fderiv ℝ (fun z : ℝ × Space => fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (z.1, z.2) (0, e))
        (t, v) (0, e) := by
  have hs : ContDiff ℝ ∞ (f t) :=
    contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y _ => ht y))
  have hc : DifferentiableAt ℝ (fderiv ℝ (f t)) v :=
    ((hs.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) v
  have hg : ContDiffOn ℝ ∞
      (fun z : ℝ × Space => fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (z.1, z.2) (0, e)) O :=
    (hf.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const
  have e1 : (fun y => fderiv ℝ (f t) y e) =
      (fun y => fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (t, y) (0, e)) :=
    funext fun y => slice_fderiv_apply hO hf (ht y) e
  rw [iteratedFDeriv_two_apply]
  have e2 : fderiv ℝ (fderiv ℝ (f t)) v e e = fderiv ℝ (fun y => fderiv ℝ (f t) y e) v e := by
    rw [fderiv_clm_apply hc (differentiableAt_const e)]
    simp
  change fderiv ℝ (fderiv ℝ (f t)) v e e = _
  rw [e2, e1]
  exact slice_fderiv_apply (f := fun τ y => fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (τ, y) (0, e))
    hO hg (ht v) e

theorem continuousOn_residual (hA : ApproxFieldProperties) {W : ℝ → Space → Space}
    {q : ℝ → Space → ℝ} {C T : ℝ} (hW : IsSimilarityProfile W q C) (hT : 0 < T) :
    ContinuousOn (fun z : ℝ × Space => approxResidual W q T z.1 z.2) (Iio T ×ˢ univ) := by
  obtain ⟨hu, hp, -⟩ := hA W q C T hW hT
  have hO : IsOpen (Iio T ×ˢ (univ : Set Space)) := isOpen_Iio.prod isOpen_univ
  have hD := hu.continuousOn_fderiv_of_isOpen hO (by simp)
  have hDp := hp.continuousOn_fderiv_of_isOpen hO (by simp)
  have hL : ∀ i : Fin 3, ContinuousOn (fun z : ℝ × Space => fderiv ℝ (fun z : ℝ × Space =>
      fderiv ℝ (fun z : ℝ × Space => approxField W T z.1 z.2) (z.1, z.2) (0, unitVector i)) z
        (0, unitVector i)) (Iio T ×ˢ univ) := fun i =>
    (((hu.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn_fderiv_of_isOpen
      hO (by simp)).clm_apply continuousOn_const
  have hRc : ContinuousOn (fun z : ℝ × Space =>
      fderiv ℝ (fun z : ℝ × Space => approxField W T z.1 z.2) z (1, 0) +
        fderiv ℝ (fun z : ℝ × Space => approxField W T z.1 z.2) z (0, approxField W T z.1 z.2) -
        ∑ i : Fin 3, fderiv ℝ (fun z : ℝ × Space =>
          fderiv ℝ (fun z : ℝ × Space => approxField W T z.1 z.2) (z.1, z.2) (0, unitVector i)) z
            (0, unitVector i) +
        ∑ i : Fin 3, fderiv ℝ (fun z : ℝ × Space => approxPressure q T z.1 z.2) z (0, unitVector i) •
          unitVector i) (Iio T ×ˢ univ) :=
    (((hD.clm_apply continuousOn_const).add (hD.clm_apply (continuousOn_const.prodMk hu.continuousOn))).sub
      (continuousOn_finsetSum _ fun i _ => hL i)).add
      (continuousOn_finsetSum _ fun i _ => (hDp.clm_apply continuousOn_const).smul continuousOn_const)
  refine hRc.congr ?_
  rintro ⟨t, v⟩ hz
  have hz' : ∀ y, (t, y) ∈ Iio T ×ˢ (univ : Set Space) := fun y => ⟨hz.1, mem_univ y⟩
  simp only [approxResidual, advectionAt, sumSecondPartialsAt, gradientAt]
  rw [time_deriv hO hu (hz' v), slice_fderiv_apply hO hu (hz' v)]
  simp only [ssp_eq hO hu hz', slice_fderiv_apply hO hp (hz' v)]

theorem forced_solution (hA : ApproxFieldProperties) (hR : ApproxResidualBound)
    {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C T : ℝ} (hW : IsSimilarityProfile W q C) (hT : 0 < T)
    (hT1 : T ≤ 1) {a b : ℝ} (ha : 0 ≤ a) (hb : b < T) :
    IsForcedPeriodicSolution (approxPeriodic W T) (fun t x => approxPressure q T t (wrap x))
      (fun t x => approxResidual W q T t (wrap x)) a b := by
  obtain ⟨hu, hp, hrest⟩ := hA W q C T hW hT
  obtain ⟨K, hK⟩ := hR W q C hW
  have hsub : Icc a b ⊆ Iio T := fun t ht => ht.2.trans_lt hb
  have hsubI : Icc a b ⊆ Ico 0 T := fun t ht => ⟨ha.trans ht.1, ht.2.trans_lt hb⟩
  have hsu : ∀ t ∈ Iio T, ∀ v, approxField W T t v ≠ 0 → dist v center ≤ 1 / 8 := by
    intro t ht v hv
    by_contra h
    exact hv ((hrest t ht v).2.1 (by rw [centralRadius]; linarith)).1
  have hsp : ∀ t ∈ Iio T, ∀ v, approxPressure q T t v ≠ 0 → dist v center ≤ 1 / 8 := by
    intro t ht v hv
    by_contra h
    exact hv ((hrest t ht v).2.1 (by rw [centralRadius]; linarith)).2
  have hsr : ∀ t ∈ Ico 0 T, ∀ v, approxResidual W q T t v ≠ 0 → dist v center ≤ 1 / 8 := by
    intro t ht v hv
    have := ((hK T t hT hT1 ht.1 ht.2 v).2 hv).2
    rw [centralRadius] at this
    linarith
  refine ⟨(contDiffOn_wrap hu hsu).mono (prod_mono hsub subset_rfl),
    (contDiffOn_wrap hp hsp).mono (prod_mono hsub subset_rfl),
    (continuousOn_wrap ((continuousOn_residual hA hW hT).mono (prod_mono Ico_subset_Iio_self subset_rfl))
      hsr).mono (prod_mono hsubI subset_rfl),
    fun t _ => ⟨isPeriodic_wrap _, isPeriodic_wrap _, isPeriodic_wrap _⟩,
    fun t ht x => ?_, fun t ht x => ?_⟩
  · have htT : t ∈ Iio T := hsub ht
    change ∑ i : Fin 3, (fderiv ℝ (fun y => approxField W T t (wrap y)) x (unitVector i)) i = 0
    rw [fderiv_wrap (hsu t htT)]
    exact (hrest t htT (wrap x)).1
  · have htT : t ∈ Iio T := hsub (Ioo_subset_Icc_self ht)
    change deriv (fun τ => approxField W T τ (wrap x)) t +
      fderiv ℝ (fun y => approxField W T t (wrap y)) x (approxField W T t (wrap x)) -
      ∑ i : Fin 3, iteratedFDeriv ℝ 2 (fun y => approxField W T t (wrap y)) x ![unitVector i, unitVector i] +
      ∑ i : Fin 3, fderiv ℝ (fun y => approxPressure q T t (wrap y)) x (unitVector i) • unitVector i = _
    rw [fderiv_wrap (hsu t htT), iteratedFDeriv_wrap (hsu t htT), fderiv_wrap (hsp t htT)]
    rfl

theorem forceV_zero (G : Space → Space) : forceV 0 G = 0 := by
  apply Subtype.ext
  apply lp.ext
  funext k
  show forceSeq 0 G k = 0
  simp [forceSeq]

theorem sqrt_integral_le {G : Space → Space} {M : ℝ} (hM : 0 ≤ M) (hG : ∀ x, ‖G x‖ ≤ M) :
    Real.sqrt (∫ x in cell, ‖G x‖ ^ 2) ≤ M * Real.sqrt (volume.real cell) := by
  have h0 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := cell)
    (f := fun x => ‖G x‖ ^ 2) (C := M ^ 2) FreqTrSeries.Internal.isCompact_cell.measure_lt_top
    (fun x _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hG x) 2)
  have h1 : ∫ x in cell, ‖G x‖ ^ 2 ≤ M ^ 2 * volume.real cell :=
    (le_abs_self _).trans (by rwa [← Real.norm_eq_abs])
  calc Real.sqrt (∫ x in cell, ‖G x‖ ^ 2) ≤ Real.sqrt (M ^ 2 * volume.real cell) := Real.sqrt_le_sqrt h1
    _ = M * Real.sqrt (volume.real cell) := by rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM]

theorem force_bound {F : ℝ → Space → Space} {a b t M C0 : ℝ} (hC0 : 0 ≤ C0) (hM : 0 ≤ M)
    (hCst : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ G : Space → Space, Continuous G → IsPeriodic G →
      ‖forceV τ G‖ ≤ C0 * τ ^ (-(1 / 2 : ℝ)) * Real.sqrt (∫ x in cell, ‖G x‖ ^ 2))
    (hF : ∀ r ∈ Icc a b, Continuous (F r) ∧ IsPeriodic (F r) ∧ ∀ x, ‖F r x‖ ≤ M)
    (hba : b - a ≤ 1) (ht : t ∈ Icc a b) :
    ‖∫ r in a..t, forceV (t - r) (F r)‖ ≤
      C0 * (M * Real.sqrt (volume.real cell)) * (2 * (t - a) ^ (1 / 2 : ℝ)) := by
  obtain ⟨hta, htb⟩ := ht
  have hv := Real.sqrt_nonneg (volume.real cell)
  set B := C0 * (M * Real.sqrt (volume.real cell)) with hBdef
  have hB : 0 ≤ B := by positivity
  have hg : IntervalIntegrable (fun r => B * (t - r) ^ (-(1 / 2 : ℝ))) volume a t := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := t - a) (b := 0)
      (by norm_num : (-1 : ℝ) < -(1 / 2))).comp_sub_left t
    simp only [sub_sub_cancel, sub_zero] at h
    exact h.const_mul B
  have hbound : ∀ᵐ r ∂volume, r ∈ Ioc a t → ‖forceV (t - r) (F r)‖ ≤ B * (t - r) ^ (-(1 / 2 : ℝ)) := by
    refine Eventually.of_forall fun r hr => ?_
    rcases eq_or_lt_of_le hr.2 with h | h
    · rw [h, sub_self, forceV_zero, norm_zero]
      exact mul_nonneg hB (rpow_nonneg le_rfl _)
    · have hr' : r ∈ Icc a b := ⟨hr.1.le, h.le.trans htb⟩
      obtain ⟨hc, hp, hbd⟩ := hF r hr'
      have hτ : 0 < t - r := by linarith
      have hτ1 : t - r ≤ 1 := by linarith [hr.1]
      have hq : 0 ≤ C0 * (t - r) ^ (-(1 / 2 : ℝ)) := mul_nonneg hC0 (rpow_nonneg hτ.le _)
      calc ‖forceV (t - r) (F r)‖ ≤ C0 * (t - r) ^ (-(1 / 2 : ℝ)) * Real.sqrt (∫ x in cell, ‖F r x‖ ^ 2) :=
            hCst _ hτ hτ1 _ hc hp
        _ ≤ C0 * (t - r) ^ (-(1 / 2 : ℝ)) * (M * Real.sqrt (volume.real cell)) :=
            mul_le_mul_of_nonneg_left (sqrt_integral_le hM hbd) hq
        _ = B * (t - r) ^ (-(1 / 2 : ℝ)) := by rw [hBdef]; ring
  refine (intervalIntegral.norm_integral_le_of_norm_le hta hbound hg).trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) t, sub_self,
    integral_rpow (Or.inl (by norm_num)), show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by norm_num,
    Real.zero_rpow (by norm_num)]
  ring

set_option maxHeartbeats 2000000 in
theorem step_identity (hK : KernelSharpBound) {u : ℝ → V} {F : ℝ → Space → Space} {a μ L : ℝ}
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hL : 0 ≤ L) (hm : IsForcedMildOnIcc u F a (a + μ * L)) (P : Piece V L)
    (hP : ∀ s : Icc (0 : ℝ) L, P s = μ ^ (1 / 4 : ℝ) • u (a + μ * s)) (s : Icc (0 : ℝ) L) :
    P s - (stepFrame hK μ hμ hμ1).G s (extendPiece P 0) -
      ∫ σ in (0 : ℝ)..s, (stepFrame hK μ hμ hμ1).K (s - σ) (extendPiece P σ) (extendPiece P σ) =
      μ ^ (1 / 4 : ℝ) • ∫ r in a..a + μ * s, forceV (a + μ * s - r) (F r) := by
  obtain ⟨s, hs⟩ := s
  have hs0 : 0 ≤ s := hs.1
  have hs1 : s ≤ L := hs.2
  have ht : a + μ * s ∈ Icc a (a + μ * L) := ⟨by nlinarith, by nlinarith⟩
  obtain ⟨-, -, heq⟩ := hm.2 _ ht
  have hE : ∀ σ ∈ Icc (0 : ℝ) L, extendPiece P σ = μ ^ (1 / 4 : ℝ) • u (a + μ * σ) := by
    intro σ hσ
    rw [extendPiece, dif_pos hL, Set.IccExtend_of_mem hL P hσ, hP]
  have e34 : μ ^ (3 / 4 : ℝ) * μ ^ (1 / 4 : ℝ) = μ := by
    rw [← rpow_add hμ]; norm_num
  have hK' : EqOn (fun σ => (stepFrame hK μ hμ hμ1).K (s - σ) (extendPiece P σ) (extendPiece P σ))
      (fun σ => μ • (μ ^ (1 / 4 : ℝ) • kernel (a + μ * s - (a + μ * σ)) (u (a + μ * σ)) (u (a + μ * σ))))
      (uIcc (0 : ℝ) s) := by
    intro σ hσ
    dsimp only
    rw [uIcc_of_le hs0] at hσ
    rw [hE σ ⟨hσ.1, hσ.2.trans hs1⟩]
    show ((μ ^ (3 / 4 : ℝ)) • kernel (μ * (s - σ))) _ _ = _
    rw [show a + μ * s - (a + μ * σ) = μ * (s - σ) by ring]
    simp only [smul_apply, map_smul, smul_smul]
    congr 1
    linear_combination μ ^ (1 / 4 : ℝ) * e34
  have hc : ∫ σ in (0 : ℝ)..s, kernel (a + μ * s - (a + μ * σ)) (u (a + μ * σ)) (u (a + μ * σ)) =
      μ⁻¹ • ∫ r in a + μ * 0..a + μ * s, kernel (a + μ * s - r) (u r) (u r) :=
    intervalIntegral.integral_comp_add_mul (fun r => kernel (a + μ * s - r) (u r) (u r)) hμ.ne' a
  have hint : ∫ σ in (0 : ℝ)..s, (stepFrame hK μ hμ hμ1).K (s - σ) (extendPiece P σ) (extendPiece P σ) =
      μ ^ (1 / 4 : ℝ) • ∫ r in a..a + μ * s, kernel (a + μ * s - r) (u r) (u r) := by
    rw [intervalIntegral.integral_congr hK']
    rw [intervalIntegral.integral_smul]
    rw [intervalIntegral.integral_smul]
    rw [hc]
    rw [mul_zero, add_zero]
    generalize (∫ r in a..a + μ * s, kernel (a + μ * s - r) (u r) (u r)) = I
    rw [smul_smul, smul_smul]
    congr 1
    field_simp
  rw [hint, hP, hE 0 ⟨le_rfl, hL⟩, mul_zero, add_zero]
  change μ ^ (1 / 4 : ℝ) • u (a + μ * s) - heat (μ * s) (μ ^ (1 / 4 : ℝ) • u a) - _ = _
  rw [heq, add_sub_cancel_left, map_smul, smul_add, smul_add]
  abel

theorem scale_le {T lam θ : ℝ} (hT : 0 < T) (hl : 0 < lam) (hθ : lam ^ (1 / 4 : ℝ) < θ) (n : ℕ) :
    (stepScale T lam n) ^ (1 / 4 : ℝ) ≤ θ ^ n * T ^ (1 / 4 : ℝ) := by
  unfold stepScale
  rw [Real.mul_rpow hT.le (pow_nonneg hl.le n), ← Real.rpow_natCast lam n, ← Real.rpow_mul hl.le,
    mul_comm (n : ℝ), Real.rpow_mul hl.le, Real.rpow_natCast, mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (rpow_nonneg hl.le _) hθ.le n) (rpow_nonneg hT.le _)

theorem rate_le {μ lam s : ℝ} (hμ : 0 < μ) (hl : 0 < lam) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (μ * lam) ^ (-(1 / 2 : ℝ)) * (μ * s) ^ (1 / 2 : ℝ) ≤ lam ^ (-(1 / 2 : ℝ)) := by
  rw [Real.mul_rpow hμ.le hl.le, Real.mul_rpow hμ.le hs0]
  have e : μ ^ (-(1 / 2 : ℝ)) * μ ^ (1 / 2 : ℝ) = 1 := by
    rw [← rpow_add hμ]; norm_num
  have h1 : s ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hs0 hs1 (by norm_num)
  have h2 : 0 ≤ lam ^ (-(1 / 2 : ℝ)) := rpow_nonneg hl.le _
  calc μ ^ (-(1 / 2 : ℝ)) * lam ^ (-(1 / 2 : ℝ)) * (μ ^ (1 / 2 : ℝ) * s ^ (1 / 2 : ℝ))
      = lam ^ (-(1 / 2 : ℝ)) * s ^ (1 / 2 : ℝ) * (μ ^ (-(1 / 2 : ℝ)) * μ ^ (1 / 2 : ℝ)) := by ring
    _ ≤ lam ^ (-(1 / 2 : ℝ)) * 1 * 1 := by rw [e]; gcongr
    _ = lam ^ (-(1 / 2 : ℝ)) := by ring

end ApproxResidual.Internal

open ApproxResidual.Internal

set_option maxHeartbeats 2000000 in
theorem approxResidualSmall (hA : ApproxFieldProperties) (hR : ApproxResidualBound) (hL : ApproxLinks)
    (_hT : TransplantSmooth) : ApproxResidualSmall := by
  intro hK W q C lam θ hl hl1 hW hθ
  obtain ⟨K, hKb⟩ := hR W q C hW
  obtain ⟨C0, hC0, hCst⟩ := forceSmoothing
  have hv := Real.sqrt_nonneg (volume.real cell)
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have hlr : 0 ≤ lam ^ (-(1 / 2 : ℝ)) := rpow_nonneg hl.le _
  have hc0 : 0 ≤ 2 * C0 * (max K 0 * Real.sqrt (volume.real cell)) * lam ^ (-(1 / 2 : ℝ)) := by positivity
  have hθ0 : 0 ≤ θ := (rpow_nonneg hl.le _).trans hθ.le
  refine ⟨2 * C0 * (max K 0 * Real.sqrt (volume.real cell)) * lam ^ (-(1 / 2 : ℝ)), hc0,
    fun T hT hT1 n => ?_⟩
  have hμ := stepScale_pos hT hl n
  have hμ1 := stepScale_le_one hT1 hl hl1.le n
  have hμT : stepScale T lam n ≤ T := mul_le_of_le_one_right hT.le (pow_le_one₀ hl.le hl1.le)
  have hLm : 0 < 1 - lam := by linarith
  have ha : 0 ≤ stepStart T lam n := by unfold stepStart; linarith
  have hb : stepStart T lam n + stepScale T lam n * (1 - lam) < T := by
    unfold stepStart; nlinarith [mul_pos hμ hl]
  have hab : stepStart T lam n < stepStart T lam n + stepScale T lam n * (1 - lam) := by
    nlinarith [mul_pos hμ hLm]
  have hsol := forced_solution hA hR hW hT hT1 ha hb
  have hmild := forcedPeriodicIsMild hK _ _ _ _ _ hab hsol
  obtain ⟨hPB, -, hPF, -⟩ := pieceOperator V (stepFrame hK (stepScale T lam n) hμ hμ1) (1 - lam) hLm
  rw [ContinuousMap.norm_le _ (mul_nonneg (pow_nonneg hθ0 n) (mul_nonneg hc0 (rpow_nonneg hT.le _)))]
  intro s
  rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply, hPB, hPF,
    step_identity hK hμ hμ1 hLm.le hmild _ (hL W q C T lam hW hT hT1 hl hl1 n).1 s,
    norm_smul, Real.norm_of_nonneg (rpow_nonneg hμ.le _)]
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 - lam := s.2.2
  have hF : ∀ r ∈ Icc (stepStart T lam n) (stepStart T lam n + stepScale T lam n * (1 - lam)),
      Continuous (fun x => approxResidual W q T r (wrap x)) ∧
        IsPeriodic (fun x => approxResidual W q T r (wrap x)) ∧
        ∀ x, ‖approxResidual W q T r (wrap x)‖ ≤ max K 0 * (stepScale T lam n * lam) ^ (-(1 / 2 : ℝ)) := by
    intro r hr
    refine ⟨Forced.Internal.sliceContinuous hsol.2.2.1 hr, (hsol.2.2.2.1 r hr).2.2, fun x => ?_⟩
    have h1 := (hKb T r hT hT1 (ha.trans hr.1) (hr.2.trans_lt hb) (wrap x)).1
    have hTr : stepScale T lam n * lam ≤ T - r := by
      have := hr.2; unfold stepStart at this; nlinarith
    have h2 : (T - r) ^ (-(1 / 2 : ℝ)) ≤ (stepScale T lam n * lam) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos hμ hl) hTr (by norm_num)
    have h3 : 0 ≤ (T - r) ^ (-(1 / 2 : ℝ)) := rpow_nonneg (by linarith [hr.2]) _
    calc ‖approxResidual W q T r (wrap x)‖ ≤ K * (T - r) ^ (-(1 / 2 : ℝ)) := h1
      _ ≤ max K 0 * (T - r) ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right (le_max_left _ _) h3
      _ ≤ max K 0 * (stepScale T lam n * lam) ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left h2 hK0
  have hM : 0 ≤ max K 0 * (stepScale T lam n * lam) ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hK0 (rpow_nonneg (mul_pos hμ hl).le _)
  have hbd := force_bound hC0.le hM hCst hF (by nlinarith) (t := stepStart T lam n + stepScale T lam n * s)
    ⟨by nlinarith, by nlinarith⟩
  rw [add_sub_cancel_left] at hbd
  have hrate := rate_le hμ hl hs0 (by linarith)
  have hsc := scale_le hT hl hθ n
  have hμq : 0 ≤ stepScale T lam n ^ (1 / 4 : ℝ) := rpow_nonneg hμ.le _
  calc stepScale T lam n ^ (1 / 4 : ℝ) *
        ‖∫ r in stepStart T lam n..stepStart T lam n + stepScale T lam n * s,
          forceV (stepStart T lam n + stepScale T lam n * s - r) (fun x => approxResidual W q T r (wrap x))‖
      ≤ stepScale T lam n ^ (1 / 4 : ℝ) * (C0 * (max K 0 * (stepScale T lam n * lam) ^ (-(1 / 2 : ℝ)) *
          Real.sqrt (volume.real cell)) * (2 * (stepScale T lam n * s) ^ (1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hbd hμq
    _ = stepScale T lam n ^ (1 / 4 : ℝ) * (2 * C0 * (max K 0 * Real.sqrt (volume.real cell))) *
          ((stepScale T lam n * lam) ^ (-(1 / 2 : ℝ)) * (stepScale T lam n * s) ^ (1 / 2 : ℝ)) := by ring
    _ ≤ stepScale T lam n ^ (1 / 4 : ℝ) * (2 * C0 * (max K 0 * Real.sqrt (volume.real cell))) *
          lam ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hrate (by positivity)
    _ = (2 * C0 * (max K 0 * Real.sqrt (volume.real cell)) * lam ^ (-(1 / 2 : ℝ))) *
          stepScale T lam n ^ (1 / 4 : ℝ) := by ring
    _ ≤ (2 * C0 * (max K 0 * Real.sqrt (volume.real cell)) * lam ^ (-(1 / 2 : ℝ))) *
          (θ ^ n * T ^ (1 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hsc hc0
    _ = θ ^ n * ((2 * C0 * (max K 0 * Real.sqrt (volume.real cell)) * lam ^ (-(1 / 2 : ℝ))) *
          T ^ (1 / 4 : ℝ)) := by ring

end Breakdown.Periodic
