import Breakdown.Frac.StTorusApprox
import Breakdown.Frac.OpExports

open MeasureTheory Set Real Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace ApproxForced.Internal

open Breakdown.FracInternal

def nearIndex (x : Space) : Lattice := fun i => -round (x i - 1 / 2)

theorem freq_coord (k : Lattice) (i : Fin 3) : freq k i = k i := by
  simp [freq, unitVector, Pi.single_apply]

theorem center_coord (i : Fin 3) : center i = 1 / 2 := by
  simp [center, unitVector, Pi.single_apply]

theorem coord_le (v w : Space) (j : Fin 3) : |v j - w j| ≤ dist v w := by
  rw [dist_eq_norm]
  have := PiLp.norm_apply_le (v - w) j
  rwa [Real.norm_eq_abs, PiLp.sub_apply] at this

theorem periodize_local {E : Type*} [NormedAddCommGroup E] {f : Space → E}
    (hf : ∀ v, f v ≠ 0 → dist v center ≤ 1 / 8) (x y : Space) (hy : dist y x < 1 / 4) :
    latticePeriodize f y = f (y + freq (nearIndex x)) := by
  unfold latticePeriodize
  refine tsum_eq_single (nearIndex x) fun j hj => ?_
  by_contra h
  apply hj
  funext i
  have a1 := (coord_le _ _ i).trans (hf _ h)
  rw [PiLp.add_apply, freq_coord, center_coord] at a1
  have a2 := (coord_le y x i).trans hy.le
  have a3 := abs_sub_round (x i - 1 / 2)
  rw [abs_le] at a1 a2 a3
  have key : |((j i + round (x i - 1 / 2) : ℤ) : ℝ)| < 1 := by
    push_cast
    rw [abs_lt]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
  have h' : |j i + round (x i - 1 / 2)| < 1 := by exact_mod_cast key
  have := abs_lt.mp h'
  simp only [nearIndex]
  omega

theorem periodize_eventually {E : Type*} [NormedAddCommGroup E] {f : Space → E}
    (hf : ∀ v, f v ≠ 0 → dist v center ≤ 1 / 8) (x : Space) :
    latticePeriodize f =ᶠ[𝓝 x] fun y => f (y + freq (nearIndex x)) := by
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1 / 4)] with y hy
  exact periodize_local hf x y hy

theorem iteratedFDeriv_periodize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} (hf : ∀ v, f v ≠ 0 → dist v center ≤ 1 / 8) (n : ℕ) (x : Space) :
    iteratedFDeriv ℝ n (latticePeriodize f) x = iteratedFDeriv ℝ n f (x + freq (nearIndex x)) := by
  rw [((periodize_eventually hf x).iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_comp_add_right]

theorem fderiv_periodize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} (hf : ∀ v, f v ≠ 0 → dist v center ≤ 1 / 8) (x : Space) :
    fderiv ℝ (latticePeriodize f) x = fderiv ℝ f (x + freq (nearIndex x)) := by
  rw [(periodize_eventually hf x).fderiv_eq, fderiv_comp_add_right]

theorem contDiffOn_periodize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set ℝ}
    {Φ : ℝ → Space → E} (hΦ : ContDiffOn ℝ ∞ (fun z : ℝ × Space => Φ z.1 z.2) (S ×ˢ univ))
    (hsupp : ∀ t ∈ S, ∀ v, Φ t v ≠ 0 → dist v center ≤ 1 / 8) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => latticePeriodize (Φ z.1) z.2) (S ×ˢ univ) := by
  apply contDiffOn_of_locally_contDiffOn
  rintro ⟨t, x⟩ -
  refine ⟨univ ×ˢ Metric.ball x (1 / 4), isOpen_univ.prod Metric.isOpen_ball,
    ⟨mem_univ _, Metric.mem_ball_self (by norm_num)⟩, ?_⟩
  have hc : ContDiffOn ℝ ∞ (fun z : ℝ × Space => Φ z.1 (z.2 + freq (nearIndex x))) (S ×ˢ univ) :=
    hΦ.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const)).contDiffOn
      (fun z hz => ⟨hz.1, mem_univ _⟩)
  refine (hc.mono inter_subset_left).congr fun z hz => ?_
  exact periodize_local (hsupp z.1 hz.1.1) x z.2 hz.2.2

theorem freq_add_single (j : Lattice) (i : Fin 3) :
    freq (j + Pi.single i 1) = freq j + unitVector i := by
  ext k
  rw [PiLp.add_apply, freq_coord, freq_coord]
  by_cases h : k = i
  · subst h
    simp [unitVector]
  · simp [unitVector, h]

theorem periodize_add_unit {E : Type*} [NormedAddCommGroup E] (f : Space → E) (i : Fin 3)
    (x : Space) : latticePeriodize f (x + unitVector i) = latticePeriodize f x := by
  unfold latticePeriodize
  have h := (Equiv.addRight (Pi.single i 1 : Lattice)).tsum_eq (fun j => f (x + freq j))
  rw [← h]
  congr 1
  funext j
  simp only [Equiv.coe_addRight, freq_add_single]
  exact congrArg f (by abel)

theorem isPeriodic_periodize {E : Type*} [NormedAddCommGroup E] (f : Space → E) :
    IsPeriodic (latticePeriodize f) := fun i x => periodize_add_unit f i x

theorem fderiv_add_unit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : Space → E}
    (hv : IsPeriodic v) (i : Fin 3) (x : Space) :
    fderiv ℝ v (x + unitVector i) = fderiv ℝ v x := by
  rw [← fderiv_comp_add_right]
  congr 1
  funext y
  exact hv i y

theorem iteratedFDeriv_add_unit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : Space → E} (hv : IsPeriodic v) (n : ℕ) (i : Fin 3) (x : Space) :
    iteratedFDeriv ℝ n v (x + unitVector i) = iteratedFDeriv ℝ n v x := by
  rw [← iteratedFDeriv_comp_add_right]
  congr 1
  funext y
  exact hv i y

theorem fracPower_add_unit (α : ℝ) {v : Space → Space} (hv : IsPeriodic v) (i : Fin 3)
    (x : Space) : fractionalPowerAt α v (x + unitVector i) = fractionalPowerAt α v x := by
  unfold fractionalPowerAt
  congr 2
  funext z
  unfold secondOrderRemainder
  rw [fderiv_add_unit hv, iteratedFDeriv_add_unit hv, hv,
    show x + unitVector i + z = x + z + unitVector i by abel, hv]

theorem contDiffAt_slice_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : ℝ → Space → E} {z : ℝ × Space}
    (hK : ContDiffAt ℝ ∞ (fun q : ℝ × Space => K q.1 q.2) z) :
    ContDiffAt ℝ ∞ (fun q : ℝ × Space => fderiv ℝ (K q.1) q.2) z := by
  refine ContDiffAt.fderiv (f := fun (q : ℝ × Space) (y : Space) => K q.1 y) (g := Prod.snd)
    (n := ∞) ?_ contDiffAt_snd (by simp)
  exact hK.comp (z, z.2) (contDiff_fst.fst.prodMk contDiff_snd).contDiffAt

theorem contDiffAt_slice_iteratedFDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {O : Set (ℝ × Space)} (hO : IsOpen O) {G : ℝ → Space → E}
    (hG : ContDiffOn ℝ ∞ (fun z : ℝ × Space => G z.1 z.2) O) {z : ℝ × Space} (hz : z ∈ O)
    (n : ℕ) : ContDiffAt ℝ ∞ (fun q : ℝ × Space => iteratedFDeriv ℝ n (G q.1) q.2) z := by
  induction n with
  | zero =>
    have h0 : ContDiffAt ℝ ∞ (fun q : ℝ × Space => G q.1 q.2) z := hG.contDiffAt (hO.mem_nhds hz)
    have e : (fun q : ℝ × Space => iteratedFDeriv ℝ 0 (G q.1) q.2) =
        fun q => (continuousMultilinearCurryFin0 ℝ Space E).symm (G q.1 q.2) := by
      funext q
      rw [iteratedFDeriv_zero_eq_comp]
      rfl
    rw [e]
    exact (continuousMultilinearCurryFin0 ℝ Space E).symm.contDiff.contDiffAt.comp z h0
  | succ n ih =>
    have hd := contDiffAt_slice_fderiv (K := fun t y => iteratedFDeriv ℝ n (G t) y) ih
    have e : (fun q : ℝ × Space => iteratedFDeriv ℝ (n + 1) (G q.1) q.2) =
        fun q => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Space) E).symm
          (fderiv ℝ (fun y => iteratedFDeriv ℝ n (G q.1) y) q.2) := by
      funext q
      rw [iteratedFDeriv_succ_eq_comp_left]
      rfl
    rw [e]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Space) E).symm.contDiff.contDiffAt.comp
      z hd

theorem iteratedFDeriv_eq_zero_of_far {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} (hf : ∀ v, f v ≠ 0 → dist v center ≤ 1 / 8) (n : ℕ) {w : Space}
    (hw : 1 / 8 < dist w center) : iteratedFDeriv ℝ n f w = 0 := by
  have h : f =ᶠ[𝓝 w] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds hw]
      with v hv
    by_contra h
    exact absurd (hf v h) (not_le.mpr hv)
  rw [(h.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_fun_zero]
  rfl

theorem remainder_far {f : Space → Space} {x z : Space} {B0 B1 B2 : ℝ} (hz : 1 ≤ ‖z‖)
    (h0 : ∀ y, ‖f y‖ ≤ B0) (h1 : ‖fderiv ℝ f x‖ ≤ B1) (h2 : ‖iteratedFDeriv ℝ 2 f x‖ ≤ B2) :
    ‖secondOrderRemainder f x z‖ ≤ (2 * B0 + B1 + B2) * ‖z‖ ^ 2 := by
  have k2 : ‖iteratedFDeriv ℝ 2 f x ![z, z]‖ ≤ ‖iteratedFDeriv ℝ 2 f x‖ * (‖z‖ * ‖z‖) := by
    have := (iteratedFDeriv ℝ 2 f x).le_opNorm ![z, z]
    simpa [Fin.prod_univ_two] using this
  have k1 : ‖fderiv ℝ f x z‖ ≤ ‖fderiv ℝ f x‖ * ‖z‖ := (fderiv ℝ f x).le_opNorm z
  have ks : ‖(1 / 2 : ℝ) • iteratedFDeriv ℝ 2 f x ![z, z]‖ ≤ ‖iteratedFDeriv ℝ 2 f x ![z, z]‖ := by
    rw [norm_smul]
    have := norm_nonneg (iteratedFDeriv ℝ 2 f x ![z, z])
    norm_num
    linarith
  have e := norm_sub_le (f (x + z) - f x - fderiv ℝ f x z)
    ((1 / 2 : ℝ) • iteratedFDeriv ℝ 2 f x ![z, z])
  have e2 := norm_sub_le (f (x + z) - f x) (fderiv ℝ f x z)
  have e3 := norm_sub_le (f (x + z)) (f x)
  have a0 := h0 (x + z)
  have a1 := h0 x
  have n0 : 0 ≤ B0 := (norm_nonneg _).trans a1
  have hz2 : ‖z‖ ≤ ‖z‖ ^ 2 := by nlinarith
  have hz3 : 1 ≤ ‖z‖ ^ 2 := by nlinarith
  have m0 : B0 ≤ B0 * ‖z‖ ^ 2 := by nlinarith
  have m1 : ‖fderiv ℝ f x‖ * ‖z‖ ≤ B1 * ‖z‖ ^ 2 := by
    nlinarith [norm_nonneg (fderiv ℝ f x), norm_nonneg z]
  have m2 : ‖iteratedFDeriv ℝ 2 f x‖ * (‖z‖ * ‖z‖) ≤ B2 * ‖z‖ ^ 2 := by
    nlinarith [norm_nonneg (iteratedFDeriv ℝ 2 f x), norm_nonneg z]
  unfold secondOrderRemainder
  nlinarith

theorem time_deriv_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Space → E}
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

theorem continuousOn_slice_iteratedFDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {O : Set (ℝ × Space)} (hO : IsOpen O) {G : ℝ → Space → E}
    (hG : ContDiffOn ℝ ∞ (fun z : ℝ × Space => G z.1 z.2) O) (n : ℕ) :
    ContinuousOn (fun q : ℝ × Space => iteratedFDeriv ℝ n (G q.1) q.2) O :=
  fun _ hq => (contDiffAt_slice_iteratedFDeriv hO hG hq n).continuousAt.continuousWithinAt

theorem continuousOn_slice_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {O : Set (ℝ × Space)} (hO : IsOpen O) {G : ℝ → Space → E}
    (hG : ContDiffOn ℝ ∞ (fun z : ℝ × Space => G z.1 z.2) O) :
    ContinuousOn (fun q : ℝ × Space => fderiv ℝ (G q.1) q.2) O :=
  fun _ hq => (contDiffAt_slice_fderiv (K := G) (hG.contDiffAt (hO.mem_nhds hq))).continuousAt.continuousWithinAt

theorem continuousOn_fracPower {α : ℝ} (hα : 1 < α) (hα2 : α < 3 / 2) {T : ℝ}
    {G : ℝ → Space → Space} (hG : ContDiffOn ℝ ∞ (fun z : ℝ × Space => G z.1 z.2) (Iio T ×ˢ univ))
    {S : Set (ℝ × Space)} (hS : S ⊆ Iio T ×ˢ univ)
    (hB : ∀ n : ℕ, ∃ B : ℝ, ∀ p ∈ S, ∀ y, ‖iteratedFDeriv ℝ n (G p.1) y‖ ≤ B) :
    ContinuousOn (fun z : ℝ × Space => fractionalPowerAt α (G z.1) z.2) S := by
  have hO : IsOpen (Iio T ×ˢ (univ : Set Space)) := isOpen_Iio.prod isOpen_univ
  have hsl : ∀ p ∈ S, ContDiff ℝ ∞ (G p.1) := fun p hp =>
    contDiffOn_univ.mp (hG.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun y _ => ⟨(hS hp).1, mem_univ y⟩))
  obtain ⟨B0, hB0⟩ := hB 0
  obtain ⟨B1, hB1⟩ := hB 1
  obtain ⟨B2, hB2⟩ := hB 2
  obtain ⟨B3, hB3⟩ := hB 3
  have hK : Measurable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α))) := measurable_norm.pow_const _
  obtain ⟨bound, hbound⟩ : ∃ f : Space → ℝ,
      f = (ball (0 : Space) 1).indicator (fun z => B3 * ‖z‖ ^ (-(2 * α))) +
        (ball (0 : Space) 1)ᶜ.indicator (fun z => (2 * B0 + B1 + B2) * ‖z‖ ^ (-(1 + 2 * α))) :=
    ⟨_, rfl⟩
  have hbi : Integrable bound := by
    rw [hbound]
    refine Integrable.add ?_ ?_
    · have h1 : IntegrableOn (fun z : Space => B3 * ‖z‖ ^ (-(2 * α))) (ball (0 : Space) 1) :=
        (integrableOn_ball_norm_rpow (s := -(2 * α)) (by linarith)).const_mul B3
      exact h1.integrable_indicator measurableSet_ball
    · have h1 : IntegrableOn (fun z : Space => (2 * B0 + B1 + B2) * ‖z‖ ^ (-(1 + 2 * α)))
          (ball (0 : Space) 1)ᶜ :=
        (integrableOn_compl_ball_norm_rpow (s := -(1 + 2 * α)) (by linarith)).const_mul _
      exact h1.integrable_indicator measurableSet_ball.compl
  have hmeas : ∀ p ∈ S, AEStronglyMeasurable
      (fun z => ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder (G p.1) p.2 z) volume := fun p hp => by
    have c0 : Continuous (G p.1) := (hsl p hp).continuous
    have h1 : Continuous (fun z => secondOrderRemainder (G p.1) p.2 z) := by
      unfold secondOrderRemainder
      fun_prop
    exact hK.aestronglyMeasurable.smul h1.aestronglyMeasurable
  have hbd : ∀ p ∈ S, ∀ z : Space,
      ‖‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder (G p.1) p.2 z‖ ≤ bound z := by
    intro p hp z
    have hnorm : ‖‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder (G p.1) p.2 z‖ =
        ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder (G p.1) p.2 z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    rw [hnorm]
    by_cases hz : z ∈ ball (0 : Space) 1
    · have hz' : z ∉ (ball (0 : Space) 1)ᶜ := fun h => h hz
      simp only [hbound, Pi.add_apply, Set.indicator_of_mem hz, Set.indicator_of_notMem hz',
        add_zero]
      have hR := remainderBound (G p.1) ((hsl p hp).of_le (WithTop.coe_le_coe.mpr le_top)) p.2 z B3
        (fun y _ => hB3 p hp y)
      rcases eq_or_ne z 0 with rfl | hz0
      · rw [norm_zero, Real.zero_rpow (by linarith : -(3 + 2 * α) ≠ 0),
          Real.zero_rpow (by linarith : -(2 * α) ≠ 0)]
        simp
      · have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
        calc ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder (G p.1) p.2 z‖
            ≤ ‖z‖ ^ (-(3 + 2 * α)) * (B3 * ‖z‖ ^ 3) :=
              mul_le_mul_of_nonneg_left hR (Real.rpow_nonneg hpos.le _)
          _ = B3 * ‖z‖ ^ (-(2 * α)) := by
              rw [show -(2 * α) = -(3 + 2 * α) + ((3 : ℕ) : ℝ) by push_cast; ring,
                Real.rpow_add hpos, Real.rpow_natCast]
              ring
    · have hz' : z ∈ (ball (0 : Space) 1)ᶜ := hz
      simp only [hbound, Pi.add_apply, Set.indicator_of_mem hz', Set.indicator_of_notMem hz,
        zero_add]
      have hz1 : 1 ≤ ‖z‖ := by simpa using hz
      have hpos : 0 < ‖z‖ := by linarith
      have hf := remainder_far (f := G p.1) (x := p.2) (B1 := B1) hz1
        (fun y => by have := hB0 p hp y; rwa [norm_iteratedFDeriv_zero] at this)
        (by rw [← norm_iteratedFDeriv_one]; exact hB1 p hp p.2) (hB2 p hp p.2)
      calc ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder (G p.1) p.2 z‖
          ≤ ‖z‖ ^ (-(3 + 2 * α)) * ((2 * B0 + B1 + B2) * ‖z‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hf (Real.rpow_nonneg hpos.le _)
        _ = (2 * B0 + B1 + B2) * ‖z‖ ^ (-(1 + 2 * α)) := by
            rw [show -(1 + 2 * α) = -(3 + 2 * α) + ((2 : ℕ) : ℝ) by push_cast; ring,
              Real.rpow_add hpos, Real.rpow_natCast]
            ring
  have hcont : ∀ z : Space, ContinuousOn
      (fun p : ℝ × Space => ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder (G p.1) p.2 z) S := by
    intro z
    have c00 : ContinuousOn (fun q : ℝ × Space => G q.1 q.2) (Iio T ×ˢ univ) := hG.continuousOn
    have c0 : ContinuousOn (fun q : ℝ × Space => G q.1 (q.2 + z)) (Iio T ×ˢ univ) :=
      hG.continuousOn.comp (continuous_fst.prodMk (continuous_snd.add continuous_const)).continuousOn
        (fun q hq => ⟨hq.1, mem_univ _⟩)
    have c1 := (continuousOn_slice_fderiv hO hG).clm_apply (continuousOn_const (c := z))
    have c2 := (continuous_eval_const (![z, z] : Fin 2 → Space)).comp_continuousOn
      (continuousOn_slice_iteratedFDeriv hO hG 2)
    have hc := (((c0.sub c00).sub c1).sub (c2.const_smul (1 / 2 : ℝ))).const_smul
      (‖z‖ ^ (-(3 + 2 * α)))
    exact hc.mono hS
  have hc := continuousOn_of_dominated hmeas (fun p hp => ae_of_all _ (hbd p hp)) hbi
    (ae_of_all _ hcont)
  exact hc.const_smul ((fractionalNormalizer α)⁻¹)

theorem periodize_bounds {T t₁ t₂ : ℝ} (ht : t₂ < T) {Φ : ℝ → Space → Space}
    (hΦ : ContDiffOn ℝ ∞ (fun z : ℝ × Space => Φ z.1 z.2) (Iio T ×ˢ univ))
    (hs : ∀ t ∈ Iio T, ∀ v, Φ t v ≠ 0 → dist v center ≤ 1 / 8) (n : ℕ) :
    ∃ B : ℝ, ∀ p ∈ Icc t₁ t₂ ×ˢ (univ : Set Space), ∀ y,
      ‖iteratedFDeriv ℝ n (latticePeriodize (Φ p.1)) y‖ ≤ B := by
  have hO : IsOpen (Iio T ×ˢ (univ : Set Space)) := isOpen_Iio.prod isOpen_univ
  have hKc : IsCompact (Icc t₁ t₂ ×ˢ closedBall center (1 / 8)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hsub : Icc t₁ t₂ ×ˢ closedBall center (1 / 8) ⊆ Iio T ×ˢ (univ : Set Space) :=
    fun q hq => ⟨hq.1.2.trans_lt ht, mem_univ _⟩
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn
    ((continuousOn_slice_iteratedFDeriv hO hΦ n).mono hsub)
  refine ⟨max B 0, fun p hp y => ?_⟩
  have hpT : p.1 ∈ Iio T := hp.1.2.trans_lt ht
  rw [iteratedFDeriv_periodize (hs p.1 hpT) n y]
  by_cases hw : dist (y + freq (nearIndex y)) center ≤ 1 / 8
  · exact (hB (p.1, y + freq (nearIndex y)) ⟨hp.1, hw⟩).trans (le_max_left _ _)
  · rw [iteratedFDeriv_eq_zero_of_far (hs p.1 hpT) n (not_le.mp hw), norm_zero]
    exact le_max_right _ _

theorem residual_continuousOn {α : ℝ} (hα : 1 < α) (hα2 : α < 3 / 2) {T t₁ t₂ : ℝ} (ht : t₂ < T)
    {Φ : ℝ → Space → Space} {Ψ : ℝ → Space → ℝ}
    (hΦ : ContDiffOn ℝ ∞ (fun z : ℝ × Space => Φ z.1 z.2) (Iio T ×ˢ univ))
    (hΨ : ContDiffOn ℝ ∞ (fun z : ℝ × Space => Ψ z.1 z.2) (Iio T ×ˢ univ))
    (hsΦ : ∀ t ∈ Iio T, ∀ v, Φ t v ≠ 0 → dist v center ≤ 1 / 8)
    (hsΨ : ∀ t ∈ Iio T, ∀ v, Ψ t v ≠ 0 → dist v center ≤ 1 / 8) :
    ContinuousOn (fun z : ℝ × Space =>
      deriv (fun τ => latticePeriodize (Φ τ) z.2) z.1 + advectionAt (latticePeriodize (Φ z.1)) z.2
        + fractionalPowerAt α (latticePeriodize (Φ z.1)) z.2
        + gradientAt (latticePeriodize (Ψ z.1)) z.2) (Icc t₁ t₂ ×ˢ univ) := by
  have hO : IsOpen (Iio T ×ˢ (univ : Set Space)) := isOpen_Iio.prod isOpen_univ
  have hSO : Icc t₁ t₂ ×ˢ (univ : Set Space) ⊆ Iio T ×ˢ univ :=
    prod_mono (fun t h => h.2.trans_lt ht) subset_rfl
  have hG := contDiffOn_periodize hΦ hsΦ
  have hH := contDiffOn_periodize hΨ hsΨ
  have c1 : ContinuousOn (fun z : ℝ × Space => deriv (fun τ => latticePeriodize (Φ τ) z.2) z.1)
      (Iio T ×ˢ univ) := by
    refine ((hG.continuousOn_fderiv_of_isOpen hO (by simp)).clm_apply
      (continuousOn_const (c := ((1 : ℝ), (0 : Space))))).congr ?_
    rintro ⟨t, v⟩ hz
    exact time_deriv_eq (f := fun t y => latticePeriodize (Φ t) y) hO hG hz
  have c2 : ContinuousOn (fun z : ℝ × Space => advectionAt (latticePeriodize (Φ z.1)) z.2)
      (Iio T ×ˢ univ) :=
    (continuousOn_slice_fderiv (G := fun t => latticePeriodize (Φ t)) hO hG).clm_apply hG.continuousOn
  have c3 := continuousOn_fracPower (G := fun t => latticePeriodize (Φ t)) hα hα2 hG hSO
    (periodize_bounds ht hΦ hsΦ)
  have c4 : ContinuousOn (fun z : ℝ × Space => gradientAt (latticePeriodize (Ψ z.1)) z.2)
      (Iio T ×ˢ univ) :=
    continuousOn_finsetSum _ fun i _ =>
      ((continuousOn_slice_fderiv (G := fun t => latticePeriodize (Ψ t)) hO hH).clm_apply
        continuousOn_const).smul continuousOn_const
  exact (((c1.mono hSO).add (c2.mono hSO)).add c3).add (c4.mono hSO)

theorem fderiv_periodize_add_unit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Space → E) (i : Fin 3) (x : Space) :
    fderiv ℝ (latticePeriodize f) (x + unitVector i) = fderiv ℝ (latticePeriodize f) x :=
  fderiv_add_unit (isPeriodic_periodize f) i x

theorem fracPower_periodize_add_unit (α : ℝ) (f : Space → Space) (i : Fin 3) (x : Space) :
    fractionalPowerAt α (latticePeriodize f) (x + unitVector i) =
      fractionalPowerAt α (latticePeriodize f) x :=
  fracPower_add_unit α (isPeriodic_periodize f) i x

end ApproxForced.Internal

open ApproxForced.Internal

theorem fracApproxForcedSolution_of (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4)
    (hF : FracApproxFieldProperties α) (hC : CovarianceStatement)
    (hI : RemainderIntegrableStatement) : FracApproxForcedSolution α := by
  intro a U P hprof T t₁ t₂ hT h12 ht2
  obtain ⟨hu, hp, hrest⟩ := hF a U P hprof T hT
  have hsu : ∀ t ∈ Iio T, ∀ v, fracApproxField α a U T t v ≠ 0 → dist v center ≤ 1 / 8 := by
    intro t ht v hv
    by_contra h
    exact hv ((hrest t ht v).2.1 (by rw [centralRadius]; linarith)).1
  have hsp : ∀ t ∈ Iio T, ∀ v, fracApproxPressure α a P T t v ≠ 0 → dist v center ≤ 1 / 8 := by
    intro t ht v hv
    by_contra h
    exact hv ((hrest t ht v).2.1 (by rw [centralRadius]; linarith)).2
  have hsub : Icc t₁ t₂ ×ˢ (univ : Set Space) ⊆ Iio T ×ˢ univ :=
    prod_mono (fun t h => h.2.trans_lt ht2) subset_rfl
  refine ⟨(contDiffOn_periodize hu hsu).mono hsub, (contDiffOn_periodize hp hsp).mono hsub,
    residual_continuousOn h1 (by linarith) ht2 hu hp hsu hsp,
    fun t _ => ⟨isPeriodic_periodize _, isPeriodic_periodize _, ?_⟩, fun t ht x => ?_,
    fun t _ x => rfl⟩
  · intro i x
    unfold fracApproxResidual advectionAt gradientAt
    simp only [periodize_add_unit, fderiv_periodize_add_unit, fracPower_periodize_add_unit]
  · have htT : t ∈ Iio T := ht.2.trans_lt ht2
    unfold divergenceAt
    rw [fderiv_periodize (hsu t htT)]
    exact (hrest t htT _).1

end Breakdown.Periodic
