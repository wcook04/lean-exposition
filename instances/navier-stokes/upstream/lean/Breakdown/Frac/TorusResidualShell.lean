import Breakdown.Frac.StTorusApprox
import Breakdown.Torus.Cutoff

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace ResidualShell.Internal

open Cutoff.Internal

def ProfileDecay (α a : ℝ) (U : Space → Space) (P : Space → ℝ) (C : ℝ) : Prop :=
  ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x : Space,
    (∀ j : ℕ, j ≤ 3 → ‖iteratedFDeriv ℝ j (fracSelfSimilar α a U T t) x‖ ≤
      C * ((T - t) ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(2 * α - 1 + j))) ∧
    ‖deriv (fun τ => fracSelfSimilar α a U T τ x) t‖ ≤
      C * ((T - t) ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(4 * α - 1)) ∧
    ‖gradientAt (fracSelfSimilarPressure α a P T t) x‖ ≤
      C * ((T - t) ^ (1 / (2 * α)) + ‖x - center‖) ^ (-(4 * α - 1))

private theorem nat_le_infty (j : ℕ) : (j : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

private theorem norm_unitVector (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

private theorem norm_gradientAt_le (p : Space → ℝ) (x : Space) :
    ‖gradientAt p x‖ ≤ 3 * ‖fderiv ℝ p x‖ := by
  unfold gradientAt
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ i : Fin 3, ‖fderiv ℝ p x (unitVector i) • unitVector i‖ ≤ ‖fderiv ℝ p x‖ := by
    intro i
    rw [norm_smul, norm_unitVector, mul_one]
    exact ((fderiv ℝ p x).le_opNorm _).trans (le_of_eq (by rw [norm_unitVector, mul_one]))
  calc ∑ i : Fin 3, ‖fderiv ℝ p x (unitVector i) • unitVector i‖
      ≤ ∑ _i : Fin 3, ‖fderiv ℝ p x‖ := Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖fderiv ℝ p x‖ := by simp

private theorem fderiv_norm_le_gradient (p : Space → ℝ) (z : Space) :
    ‖fderiv ℝ p z‖ ≤ ‖gradientAt p z‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  have hv : v = v 0 • unitVector 0 + v 1 • unitVector 1 + v 2 • unitVector 2 := by
    ext i; fin_cases i <;> simp [unitVector_apply]
  have key : fderiv ℝ p z v = inner ℝ (gradientAt p z) v := by
    have hr : inner ℝ (gradientAt p z) v = fderiv ℝ p z (unitVector 0) * v 0 +
        fderiv ℝ p z (unitVector 1) * v 1 + fderiv ℝ p z (unitVector 2) * v 2 := by
      simp [gradientAt, Fin.sum_univ_three, inner_add_left, inner_smul_left, unitVector,
        EuclideanSpace.inner_single_left]
    rw [hr]
    conv_lhs => rw [hv]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  rw [key, Real.norm_eq_abs]
  exact abs_real_inner_le_norm _ _

private theorem slice_of_contDiffOn {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → Space → E} {T t : ℝ}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Iio T ×ˢ univ)) (htT : t < T) :
    ContDiff ℝ ∞ (f t) :=
  contDiffOn_univ.1 ((hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun _ _ => mk_mem_prod htT (mem_univ _))) : ContDiffOn ℝ ∞ (fun x : Space => f t x) univ)

private theorem bounded_iteratedFDeriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (j : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ K := by
  obtain ⟨K, hK⟩ := (hf.continuous_iteratedFDeriv (nat_le_infty j)).bounded_above_of_compact_support
    (hs.iteratedFDeriv j)
  exact ⟨max K 0, le_max_right _ _, fun x => (hK x).trans (le_max_left _ _)⟩

private theorem bounded_upto {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ K := by
  induction n with
  | zero =>
    obtain ⟨K, hK, h⟩ := bounded_iteratedFDeriv hf hs 0
    exact ⟨K, hK, fun j hj x => by rw [Nat.le_zero.1 hj]; exact h x⟩
  | succ n ih =>
    obtain ⟨K, hK, h⟩ := ih
    obtain ⟨K', _, h'⟩ := bounded_iteratedFDeriv hf hs (n + 1)
    refine ⟨max K K', le_max_of_le_left hK, fun j hj x => ?_⟩
    rcases Nat.lt_or_eq_of_le hj with hj | hj
    · exact (h j (Nat.lt_succ_iff.1 hj) x).trans (le_max_left _ _)
    · rw [hj]; exact (h' x).trans (le_max_right _ _)

private theorem centralCut_contDiff : ContDiff ℝ ∞ centralCut := centralBump.contDiff

private theorem centralCut_support : HasCompactSupport centralCut := centralBump.hasCompactSupport

private theorem gradient_contDiff {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (gradientAt χ) := by
  unfold gradientAt
  refine ContDiff.sum fun i _ => ?_
  exact ((hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).smul contDiff_const

private theorem gradient_support {χ : Space → ℝ} (hs : HasCompactSupport χ) :
    HasCompactSupport (gradientAt χ) := by
  refine (hs.fderiv (𝕜 := ℝ)).mono ?_
  intro x hx
  by_contra h
  apply hx
  simp only [Function.mem_support, not_not] at h
  simp [gradientAt, h]

private theorem centralCut_norm_le (x : Space) : ‖centralCut x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  have h0 : 0 ≤ centralCut x := centralBump.nonneg' x
  have h1 : centralCut x ≤ 1 := centralBump.le_one
  exact ⟨by linarith, h1⟩

private theorem gradient_coreCut_zero {y : Space} (hy : dist y center < centralRadius / 4) :
    gradientAt centralCut y = 0 := by
  have hU : Metric.ball center (centralRadius / 4) ∈ 𝓝 y := Metric.isOpen_ball.mem_nhds hy
  have h : centralCut =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    filter_upwards [hU] with w hw
    have hw' : w ∈ Metric.closedBall center centralBump.rIn := Metric.ball_subset_closedBall hw
    exact centralBump.one_of_mem_closedBall hw'
  unfold gradientAt
  rw [h.fderiv_eq]
  simp

private theorem binom_sum_le {a b : ℕ → ℝ} {M N : ℝ} {k : ℕ} (ha : ∀ i ≤ k, 0 ≤ a i ∧ a i ≤ M)
    (hb : ∀ i ≤ k, 0 ≤ b i ∧ b i ≤ N) :
    ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * a i * b (k - i) ≤ 2 ^ k * (M * N) := by
  calc ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * a i * b (k - i)
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (M * N) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have h1 := ha i hi'
        have h2 := hb (k - i) (Nat.sub_le k i)
        have hMN : a i * b (k - i) ≤ M * N := mul_le_mul h1.2 h2.2 h2.1 (h1.1.trans h1.2)
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hMN (Nat.cast_nonneg _)
    _ = 2 ^ k * (M * N) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose k

private theorem shift_norm_le {x c : Space} (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y : Space => y - c) x‖ ≤ max ‖x - c‖ 1 := by
  have hfd : fderiv ℝ (fun y : Space => y - c) = fun _ => ContinuousLinearMap.id ℝ Space := by
    funext y
    rw [fderiv_sub_const, fderiv_fun_id]
  rcases k with _ | k
  · rw [norm_iteratedFDeriv_zero]
    exact le_max_left _ _
  · rw [← norm_iteratedFDeriv_fderiv, hfd]
    rcases k with _ | k
    · rw [norm_iteratedFDeriv_zero]
      exact ContinuousLinearMap.norm_id_le.trans (le_max_right _ _)
    · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k), Pi.zero_apply, norm_zero]
      exact le_max_of_le_right zero_le_one

private theorem dilate_norm_le {g : Space → Space} (hg : ContDiff ℝ ∞ g) {s : ℝ} (hs : 0 ≤ s)
    (c x : Space) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => g (c + s • (y - c))) x‖ ≤
      ‖iteratedFDeriv ℝ k g (c + s • (x - c))‖ * s ^ k := by
  obtain ⟨L, hL⟩ : ∃ L : Space →L[ℝ] Space, L = s • ContinuousLinearMap.id ℝ Space := ⟨_, rfl⟩
  have hh : ContDiff ℝ ∞ (fun z => g (z + c)) := hg.comp (contDiff_id.add contDiff_const)
  have hfun : (fun y => g (c + s • (y - c))) = fun y => ((fun z => g (z + c)) ∘ L) (y - c) := by
    funext y
    rw [hL]
    simp only [Function.comp_apply, smul_apply, ContinuousLinearMap.id_apply, add_comm]
  have hLn : ‖L‖ ≤ s := by
    rw [hL]
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_nonneg hs]
    exact mul_le_of_le_one_right hs ContinuousLinearMap.norm_id_le
  rw [hfun, iteratedFDeriv_comp_sub, L.iteratedFDeriv_comp_right hh _ (nat_le_infty k)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, iteratedFDeriv_comp_add_right]
  have e : L (x - c) + c = c + s • (x - c) := by
    rw [hL, smul_apply, ContinuousLinearMap.id_apply, add_comm]
  rw [e]
  gcongr

private theorem decay_le {m ρ e E c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hm : 0 ≤ m) (hρ : c ≤ ρ)
    (he : 0 ≤ e) (heE : e ≤ E) : (m + ρ) ^ (-e) ≤ c ^ (-E) :=
  (rpow_le_rpow_of_nonpos hc (by linarith) (by linarith)).trans
    (rpow_le_rpow_of_exponent_ge hc hc1 (by linarith))

private theorem decay_nonneg {α : ℝ} (hD : FracSelfSimilarDecay α) {a : ℝ} {U : Space → Space}
    {P : Space → ℝ} (hU : IsRotatingProfile α a 1 U P) :
    ∃ C : ℝ, 0 ≤ C ∧ ProfileDecay α a U P C := by
  obtain ⟨C, hC⟩ := hD a U P hU
  refine ⟨C, ?_, hC⟩
  have h := (hC 1 0 one_pos le_rfl le_rfl one_pos center).1 0 (Nat.zero_le _)
  simp only [sub_zero, one_rpow, sub_self, norm_zero, add_zero, Nat.cast_zero, mul_one] at h
  exact (norm_nonneg _).trans h

private theorem field_region_bound {α a C : ℝ} {U : Space → Space} {P : Space → ℝ}
    (hα1 : 1 < α) (hC0 : 0 ≤ C) (hC : ProfileDecay α a U P C) {T t : ℝ} (hT : 0 < T)
    (hT1 : T ≤ 1) (ht : 0 ≤ t) (htT : t < T) {y : Space} (hy : 1 / 64 ≤ dist y center) {i : ℕ}
    (hi : i ≤ 3) :
    ‖iteratedFDeriv ℝ i (fracSelfSimilar α a U T t) y‖ ≤ C * (1 / 64 : ℝ) ^ (-(2 * α + 2)) := by
  refine ((hC T t hT hT1 ht htT y).1 i hi).trans (mul_le_mul_of_nonneg_left ?_ hC0)
  have hm : 0 ≤ (T - t) ^ (1 / (2 * α)) := rpow_nonneg (by linarith) _
  have hi' : (i : ℝ) ≤ 3 := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  rw [← dist_eq_norm]
  exact decay_le (by norm_num) (by norm_num) hm hy (by linarith) (by linarith)

private theorem scaled_bound {α a C : ℝ} {U : Space → Space} {P : Space → ℝ}
    (hα1 : 1 < α) (hC0 : 0 ≤ C) (hC : ProfileDecay α a U P C) {T t : ℝ} (hT : 0 < T)
    (hT1 : T ≤ 1) (ht : 0 ≤ t) (htT : t < T) {y : Space} (hy : 1 / 64 ≤ dist y center)
    {s : ℝ} (hs0 : 0 < s) {i : ℕ} (hi : i ≤ 3) :
    s ^ (i + 1) * ‖iteratedFDeriv ℝ i (fracSelfSimilar α a U T t) (center + s • (y - center))‖ ≤
      C * (1 / 64 : ℝ) ^ (-(2 * α + 2)) * s ^ (2 - 2 * α) := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = dist y center := ⟨_, rfl⟩
  have hρ1 : 1 / 64 ≤ ρ := by rw [hρ]; exact hy
  have hρ0 : 0 < ρ := by linarith
  have hz : ‖center + s • (y - center) - center‖ = s * ρ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs0, ← dist_eq_norm, hρ]
  have hb := (hC T t hT hT1 ht htT (center + s • (y - center))).1 i hi
  rw [hz] at hb
  have hm : 0 ≤ (T - t) ^ (1 / (2 * α)) := rpow_nonneg (by linarith) _
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = 2 * α - 1 + i := ⟨_, rfl⟩
  rw [← he] at hb
  have hi' : (i : ℝ) ≤ 3 := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have he0 : 0 ≤ e := by rw [he]; linarith
  have hsρ : 0 < s * ρ := mul_pos hs0 hρ0
  have h1 : ((T - t) ^ (1 / (2 * α)) + s * ρ) ^ (-e) ≤ (s * ρ) ^ (-e) :=
    rpow_le_rpow_of_nonpos hsρ (by linarith) (by linarith)
  have h2 : (s * ρ) ^ (-e) = s ^ (-e) * ρ ^ (-e) := mul_rpow hs0.le hρ0.le
  have h3 : ρ ^ (-e) ≤ (1 / 64 : ℝ) ^ (-(2 * α + 2)) := by
    have := decay_le (m := 0) (E := 2 * α + 2) (by norm_num : (0 : ℝ) < 1 / 64) (by norm_num) le_rfl hρ1 he0
      (by rw [he]; linarith)
    rwa [zero_add] at this
  have h4 : s ^ (i + 1) * s ^ (-e) = s ^ (2 - 2 * α) := by
    rw [← rpow_natCast, ← rpow_add hs0]
    congr 1
    rw [he]; push_cast; ring
  have hsp : 0 ≤ s ^ (i + 1) := pow_nonneg hs0.le _
  have hse : 0 ≤ s ^ (-e) := rpow_nonneg hs0.le _
  have hs2 : 0 ≤ s ^ (2 - 2 * α) := rpow_nonneg hs0.le _
  calc s ^ (i + 1) * ‖iteratedFDeriv ℝ i (fracSelfSimilar α a U T t) (center + s • (y - center))‖
      ≤ s ^ (i + 1) * (C * (s ^ (-e) * ρ ^ (-e))) :=
        mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left (h1.trans h2.le) hC0)) hsp
    _ = C * ρ ^ (-e) * (s ^ (i + 1) * s ^ (-e)) := by ring
    _ ≤ C * (1 / 64 : ℝ) ^ (-(2 * α + 2)) * s ^ (2 - 2 * α) := by
        rw [h4]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hC0) hs2

private theorem norm_iteratedFDeriv_integral_le (k : ℕ) : ∀ {G : Type} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] (F : ℝ × Space → G), ContDiff ℝ ∞ F → ∀ (x : Space)
    (h : ℝ → ℝ), IntervalIntegrable h volume 0 1 →
    (∀ s ∈ Ioc (0 : ℝ) 1, ‖iteratedFDeriv ℝ k (fun y => F (s, y)) x‖ ≤ h s) →
    ‖iteratedFDeriv ℝ k (fun y => ∫ s in (0 : ℝ)..1, F (s, y)) x‖ ≤ ∫ s in (0 : ℝ)..1, h s := by
  induction k with
  | zero =>
    intro G _ _ _ F _ x h hh hb
    rw [norm_iteratedFDeriv_zero]
    refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (ae_of_all _ fun s hs => ?_) hh
    have := hb s hs
    rwa [norm_iteratedFDeriv_zero] at this
  | succ k ih =>
    intro G _ _ _ F hF x h hh hb
    have h1 : ContDiff ℝ 1 F := hF.of_le (by simp)
    have hfd : fderiv ℝ (fun y => ∫ s in (0 : ℝ)..1, F (s, y)) =
        fun y => ∫ s in (0 : ℝ)..1, partialSecond F s y :=
      funext fun y => (hasFDerivAt_integral_unit F h1 y).fderiv
    rw [← norm_iteratedFDeriv_fderiv, hfd]
    refine ih (fun z => partialSecond F z.1 z.2)
      ((contDiff_infty_iff_fderiv.1 hF).2.clm_comp contDiff_const) x h hh (fun s hs => ?_)
    have hsl : (fun y => partialSecond F s y) = fderiv ℝ (fun y => F (s, y)) :=
      funext fun y => ((hasFDerivAt_partialSecond F h1 s y).fderiv).symm
    show ‖iteratedFDeriv ℝ k (fun y => partialSecond F s y) x‖ ≤ h s
    rw [hsl, norm_iteratedFDeriv_fderiv]
    exact hb s hs

private theorem potential_region_bound {α a C : ℝ} {U : Space → Space} {P : Space → ℝ}
    (hα1 : 1 < α) (hα3 : α < 3 / 2) (hS : FracSelfSimilarSolves α)
    (hU : IsRotatingProfile α a 1 U P) (hC0 : 0 ≤ C) (hC : ProfileDecay α a U P C) {T t : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1) (ht : 0 ≤ t) (htT : t < T) {y : Space}
    (hy1 : 1 / 64 ≤ dist y center) (hy2 : dist y center ≤ 1) {k : ℕ} (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (homotopyPotential center (fracSelfSimilar α a U T t)) y‖ ≤
      ∫ s in (0 : ℝ)..1, ‖crossBilinear‖ * 8 * (C * (1 / 64 : ℝ) ^ (-(2 * α + 2))) *
        s ^ (2 - 2 * α) := by
  have hg : ContDiff ℝ ∞ (fracSelfSimilar α a U T t) :=
    slice_of_contDiffOn (hS a U P hU T hT).1 htT
  have hΦ := contDiff_potentialIntegrand (x₀ := center) hg
  rw [homotopyPotential_eq]
  refine norm_iteratedFDeriv_integral_le k _ hΦ y _ ?_ (fun s hs => ?_)
  · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < 2 - 2 * α)).const_mul _
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = C * (1 / 64 : ℝ) ^ (-(2 * α + 2)) := ⟨_, rfl⟩
  rw [← hM]
  have hs0 := hs.1
  have hv : ∀ i ≤ k, 0 ≤ ‖iteratedFDeriv ℝ i (fun w : Space => w - center) y‖ ∧
      ‖iteratedFDeriv ℝ i (fun w : Space => w - center) y‖ ≤ 1 := fun i _ =>
    ⟨norm_nonneg _, (shift_norm_le i).trans (max_le (by rw [← dist_eq_norm]; exact hy2) le_rfl)⟩
  have hu : ∀ i ≤ k, 0 ≤ s * ‖iteratedFDeriv ℝ i
      (fun w => fracSelfSimilar α a U T t (center + s • (w - center))) y‖ ∧
      s * ‖iteratedFDeriv ℝ i (fun w => fracSelfSimilar α a U T t (center + s • (w - center))) y‖
        ≤ M * s ^ (2 - 2 * α) := by
    intro i hi
    refine ⟨mul_nonneg hs0.le (norm_nonneg _), ?_⟩
    have h1 := dilate_norm_le hg hs0.le center y i
    have h2 := scaled_bound hα1 hC0 hC hT hT1 ht htT hy1 hs0 (i := i) (by omega)
    rw [← hM] at h2
    calc s * ‖iteratedFDeriv ℝ i (fun w => fracSelfSimilar α a U T t (center + s • (w - center))) y‖
        ≤ s * (‖iteratedFDeriv ℝ i (fracSelfSimilar α a U T t) (center + s • (y - center))‖ * s ^ i) :=
          mul_le_mul_of_nonneg_left h1 hs0.le
      _ = s ^ (i + 1) * ‖iteratedFDeriv ℝ i (fracSelfSimilar α a U T t) (center + s • (y - center))‖ := by
          ring
      _ ≤ M * s ^ (2 - 2 * α) := h2
  have hu' : ContDiff ℝ ∞ (fun w => fracSelfSimilar α a U T t (center + s • (w - center))) :=
    hg.comp (contDiff_const.add (ContDiff.const_smul s (contDiff_id.sub contDiff_const)))
  have hv' : ContDiff ℝ ∞ (fun w : Space => w - center) := contDiff_id.sub contDiff_const
  have hfun : (fun w => potentialIntegrand center (fracSelfSimilar α a U T t) (s, w)) = fun w =>
      s • crossBilinear (fracSelfSimilar α a U T t (center + s • (w - center))) (w - center) := rfl
  have hB : ContDiff ℝ ∞ (fun w => crossBilinear (fracSelfSimilar α a U T t
      (center + s • (w - center))) (w - center)) := contDiff_cross hu' hv'
  rw [hfun, iteratedFDeriv_const_smul_apply' (hB.contDiffAt.of_le (nat_le_infty k)), norm_smul,
    Real.norm_eq_abs, abs_of_pos hs0]
  have hbil := crossBilinear.norm_iteratedFDeriv_le_of_bilinear hu' hv' y (nat_le_infty k)
  have hsum := binom_sum_le (a := fun i => s * ‖iteratedFDeriv ℝ i
    (fun w => fracSelfSimilar α a U T t (center + s • (w - center))) y‖)
    (b := fun i => ‖iteratedFDeriv ℝ i (fun w : Space => w - center) y‖) hu hv
  have h8 : (2 : ℝ) ^ k ≤ 8 := by
    calc (2 : ℝ) ^ k ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hk
      _ = 8 := by norm_num
  have hMs : 0 ≤ M * s ^ (2 - 2 * α) :=
    mul_nonneg (hM ▸ mul_nonneg hC0 (rpow_nonneg (by norm_num) _)) (rpow_nonneg hs0.le _)
  have h8' := mul_le_mul_of_nonneg_right h8 hMs
  calc s * ‖iteratedFDeriv ℝ k (fun w => crossBilinear (fracSelfSimilar α a U T t
        (center + s • (w - center))) (w - center)) y‖
      ≤ s * (‖crossBilinear‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun w => fracSelfSimilar α a U T t (center + s • (w - center))) y‖ *
          ‖iteratedFDeriv ℝ (k - i) (fun w : Space => w - center) y‖) :=
        mul_le_mul_of_nonneg_left hbil hs0.le
    _ = ‖crossBilinear‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        (s * ‖iteratedFDeriv ℝ i (fun w => fracSelfSimilar α a U T t
          (center + s • (w - center))) y‖) *
          ‖iteratedFDeriv ℝ (k - i) (fun w : Space => w - center) y‖ := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ‖crossBilinear‖ * (2 ^ k * (M * s ^ (2 - 2 * α) * 1)) :=
        mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ ≤ ‖crossBilinear‖ * 8 * M * s ^ (2 - 2 * α) := by
        rw [mul_one]
        nlinarith [mul_le_mul_of_nonneg_left h8' (norm_nonneg
          (crossBilinear : Space →L[ℝ] Space →L[ℝ] Space))]

private theorem potential_integral_nonneg {α C : ℝ} (hC0 : 0 ≤ C) :
    0 ≤ ∫ s in (0 : ℝ)..1, ‖crossBilinear‖ * 8 * (C * (1 / 64 : ℝ) ^ (-(2 * α + 2))) *
      s ^ (2 - 2 * α) := by
  refine intervalIntegral.integral_nonneg zero_le_one (fun s hs => ?_)
  exact mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (by norm_num))
    (mul_nonneg hC0 (rpow_nonneg (by norm_num) _))) (rpow_nonneg hs.1 _)

private theorem approx_region_bound {α a C : ℝ} {U : Space → Space} {P : Space → ℝ}
    (hα1 : 1 < α) (hα3 : α < 3 / 2) (hS : FracSelfSimilarSolves α)
    (hU : IsRotatingProfile α a 1 U P) (hC0 : 0 ≤ C) (hC : ProfileDecay α a U P C)
    (hH : HomotopyCurl) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ y : Space,
      1 / 64 ≤ dist y center → dist y center ≤ 1 → ∀ k ≤ 3,
        ‖iteratedFDeriv ℝ k (fracApproxField α a U T t) y‖ ≤ K := by
  obtain ⟨Kχ, hKχ, hχ⟩ := bounded_upto centralCut_contDiff centralCut_support 3
  obtain ⟨KG, hKG, hG⟩ := bounded_upto (gradient_contDiff centralCut_contDiff)
    (gradient_support centralCut_support) 3
  obtain ⟨KΨ, hKΨ⟩ : ∃ KΨ : ℝ, KΨ = ∫ s in (0 : ℝ)..1, ‖crossBilinear‖ * 8 *
      (C * (1 / 64 : ℝ) ^ (-(2 * α + 2))) * s ^ (2 - 2 * α) := ⟨_, rfl⟩
  have hKΨ0 : 0 ≤ KΨ := hKΨ ▸ potential_integral_nonneg hC0
  obtain ⟨Ku, hKu⟩ : ∃ Ku : ℝ, Ku = C * (1 / 64 : ℝ) ^ (-(2 * α + 2)) := ⟨_, rfl⟩
  have hKu0 : 0 ≤ Ku := hKu ▸ mul_nonneg hC0 (rpow_nonneg (by norm_num) _)
  refine ⟨2 ^ 3 * (Kχ * Ku) + ‖crossBilinear‖ * (2 ^ 3 * (KG * KΨ)), by positivity, ?_⟩
  intro T t hT hT1 ht htT y hy1 hy2 k hk
  have hg : ContDiff ℝ ∞ (fracSelfSimilar α a U T t) :=
    slice_of_contDiffOn (hS a U P hU T hT).1 htT
  have hdiv : ∀ y, divergenceAt (fracSelfSimilar α a U T t) y = 0 :=
    fun y => ((hS a U P hU T hT).2.2 t htT y).1
  have hψs : ContDiff ℝ ∞ (homotopyPotential center (fracSelfSimilar α a U T t)) :=
    (hH center _ hg hdiv).1
  have hGs := gradient_contDiff centralCut_contDiff
  have hsplit : fracApproxField α a U T t = (fun y => centralCut y • fracSelfSimilar α a U T t y) +
      (fun y => crossBilinear (gradientAt centralCut y)
        (homotopyPotential center (fracSelfSimilar α a U T t) y)) := rfl
  have h1 : ContDiff ℝ ∞ (fun y => centralCut y • fracSelfSimilar α a U T t y) :=
    centralCut_contDiff.smul hg
  have h2 : ContDiff ℝ ∞ (fun y => crossBilinear (gradientAt centralCut y)
      (homotopyPotential center (fracSelfSimilar α a U T t) y)) := contDiff_cross hGs hψs
  have h8 : (2 : ℝ) ^ k ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hk
  rw [hsplit, iteratedFDeriv_add_apply (h1.contDiffAt.of_le (nat_le_infty k))
    (h2.contDiffAt.of_le (nat_le_infty k))]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_iteratedFDeriv_smul_le centralCut_contDiff hg y (nat_le_infty k)).trans ?_
    refine (binom_sum_le (a := fun i => ‖iteratedFDeriv ℝ i centralCut y‖)
      (b := fun i => ‖iteratedFDeriv ℝ i (fracSelfSimilar α a U T t) y‖)
      (fun i hi => ⟨norm_nonneg _, hχ i (by omega) y⟩)
      (fun i hi => ⟨norm_nonneg _, hKu ▸ field_region_bound hα1 hC0 hC hT hT1 ht htT hy1
        (by omega)⟩)).trans ?_
    exact mul_le_mul_of_nonneg_right h8 (mul_nonneg hKχ hKu0)
  · refine (crossBilinear.norm_iteratedFDeriv_le_of_bilinear hGs hψs y (nat_le_infty k)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (binom_sum_le (a := fun i => ‖iteratedFDeriv ℝ i (gradientAt centralCut) y‖)
      (b := fun i => ‖iteratedFDeriv ℝ i (homotopyPotential center (fracSelfSimilar α a U T t)) y‖)
      (fun i hi => ⟨norm_nonneg _, hG i (by omega) y⟩)
      (fun i hi => ⟨norm_nonneg _, hKΨ ▸ potential_region_bound hα1 hα3 hS hU hC0 hC hT hT1 ht
        htT hy1 hy2 (by omega)⟩)).trans ?_
    exact mul_le_mul_of_nonneg_right h8 (mul_nonneg hKG hKΨ0)

private theorem potential_time_deriv {α b : ℝ} {U : Space → Space} {P : Space → ℝ}
    (hS : FracSelfSimilarSolves α) (hprof : IsRotatingProfile α b 1 U P) {T t : ℝ} (hT : 0 < T)
    (htT : t < T) (x : Space) :
    HasDerivAt (fun τ => homotopyPotential center (fracSelfSimilar α b U T τ) x)
      (∫ s in (0 : ℝ)..1, s • cross (deriv (fun τ => fracSelfSimilar α b U T τ (center + s • (x - center))) t)
        (x - center)) t := by
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ × Space → Space, G = fun z => fracSelfSimilar α b U T z.1 z.2 := ⟨_, rfl⟩
  have hG : ContDiffOn ℝ ∞ G (Iio T ×ˢ univ) := hGdef ▸ (hS b U P hprof T hT).1
  have hU : IsOpen (Iio T ×ˢ (univ : Set Space)) := isOpen_Iio.prod isOpen_univ
  have hfd : ContinuousOn (fderiv ℝ G) (Iio T ×ˢ univ) :=
    hG.continuousOn_fderiv_of_isOpen hU (by simp)
  have hGd : ∀ τ < T, ∀ z : Space,
      HasDerivAt (fun σ => fracSelfSimilar α b U T σ z) (fderiv ℝ G (τ, z) (1, 0)) τ := by
    intro τ hτ z
    have hJ : HasFDerivAt G (fderiv ℝ G (τ, z)) (τ, z) :=
      ((hG.contDiffAt (prod_mem_nhds (Iio_mem_nhds hτ) univ_mem)).differentiableAt
        (by simp)).hasFDerivAt
    have h := hJ.comp_hasDerivAt τ ((hasDerivAt_id' τ).prodMk (hasDerivAt_const τ z))
    have e : (G ∘ fun σ : ℝ => (σ, z)) = fun σ => fracSelfSimilar α b U T σ z := by
      rw [hGdef]
      rfl
    rw [e] at h
    exact h
  have hcr : Continuous (fun p : Space × Space => cross p.1 p.2) :=
    (Breakdown.Periodic.Cutoff.Internal.contDiff_cross (n := 0) contDiff_fst contDiff_snd).continuous
  obtain ⟨a, ha⟩ : ∃ a : Space, a = x - center := ⟨_, rfl⟩
  show HasDerivAt (fun τ => ∫ s in (0 : ℝ)..1,
    s • cross (fracSelfSimilar α b U T τ (center + s • (x - center))) (x - center)) _ t
  rw [← ha]
  have hline : Continuous (fun s : ℝ => center + s • a) :=
    continuous_const.add (continuous_id.smul continuous_const)
  obtain ⟨F', hF'def⟩ : ∃ F' : ℝ → ℝ → Space,
      F' = fun τ s => s • Breakdown.Periodic.Cutoff.Internal.crossBilinear
        (fderiv ℝ G (τ, center + s • a) (1, 0)) a := ⟨_, rfl⟩
  have hsub : Icc (t - (T - t) / 2) (t + (T - t) / 2) ∈ 𝓝 t :=
    Icc_mem_nhds (by linarith) (by linarith)
  have hST : ∀ τ ∈ Icc (t - (T - t) / 2) (t + (T - t) / 2), τ < T :=
    fun τ hτ => by linarith [hτ.2]
  have hcontF' : ContinuousOn (fun p : ℝ × ℝ => F' p.1 p.2)
      (Icc (t - (T - t) / 2) (t + (T - t) / 2) ×ˢ Icc 0 1) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ G (p.1, center + p.2 • a))
        (Icc (t - (T - t) / 2) (t + (T - t) / 2) ×ˢ Icc 0 1) :=
      hfd.comp (continuous_fst.prodMk (hline.comp continuous_snd)).continuousOn
        (fun p hp => ⟨hST p.1 hp.1, mem_univ _⟩)
    have h2 : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ G (p.1, center + p.2 • a) (1, 0))
        (Icc (t - (T - t) / 2) (t + (T - t) / 2) ×ˢ Icc 0 1) :=
      h1.clm_apply continuousOn_const
    have h4 : ContinuousOn (fun p : ℝ × ℝ => Breakdown.Periodic.Cutoff.Internal.crossBilinear
        (fderiv ℝ G (p.1, center + p.2 • a) (1, 0)) a)
        (Icc (t - (T - t) / 2) (t + (T - t) / 2) ×ˢ Icc 0 1) :=
      (Breakdown.Periodic.Cutoff.Internal.crossBilinear.continuous.comp_continuousOn h2).clm_apply
        continuousOn_const
    rw [hF'def]
    exact continuous_snd.continuousOn.smul h4
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcontF'
  have hF'cont : Continuous (F' t) := by
    have h1 : Continuous (fun s : ℝ => fderiv ℝ G (t, center + s • a)) :=
      hfd.comp_continuous (continuous_const.prodMk hline) (fun s => ⟨htT, mem_univ _⟩)
    have h3 : Continuous (fun s : ℝ => Breakdown.Periodic.Cutoff.Internal.crossBilinear
        (fderiv ℝ G (t, center + s • a) (1, 0)) a) :=
      (Breakdown.Periodic.Cutoff.Internal.crossBilinear.continuous.comp
        (h1.clm_apply continuous_const)).clm_apply continuous_const
    rw [hF'def]
    exact continuous_id.smul h3
  have hFcont : ∀ τ < T, Continuous (fun s : ℝ => s • cross (fracSelfSimilar α b U T τ (center + s • a)) a) := by
    intro τ hτ
    have h1 : Continuous (fun s : ℝ => fracSelfSimilar α b U T τ (center + s • a)) :=
      (slice_of_contDiffOn (hS b U P hprof T hT).1 hτ).continuous.comp hline
    have h2 : Continuous (fun s : ℝ => (fracSelfSimilar α b U T τ (center + s • a), a)) :=
      h1.prodMk (continuous_const (y := a))
    have h3 : Continuous (fun s : ℝ => cross (fracSelfSimilar α b U T τ (center + s • a)) a) := hcr.comp h2
    exact continuous_id.smul h3
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (a := 0) (b := 1) (bound := fun _ => K)
    (F := fun τ s => s • cross (fracSelfSimilar α b U T τ (center + s • a)) a) (F' := F') hsub
    (by filter_upwards [Iio_mem_nhds htT] with τ hτ using (hFcont τ hτ).aestronglyMeasurable)
    ((hFcont t htT).intervalIntegrable _ _) hF'cont.aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun s hs τ hτ => hK (τ, s) ⟨hτ, Ioc_subset_Icc_self
      (by rwa [uIoc_of_le zero_le_one] at hs)⟩)
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun s _ τ hτ => by
      have h := (s • (Breakdown.Periodic.Cutoff.Internal.crossBilinear.flip a)).hasFDerivAt.comp_hasDerivAt
        τ (hGd τ (hST τ hτ) (center + s • a))
      rw [smul_apply, ContinuousLinearMap.flip_apply] at h
      rw [hF'def]
      exact h)
  have heq : (∫ s in (0 : ℝ)..1, s • cross (deriv (fun τ => fracSelfSimilar α b U T τ (center + s • a)) t) a)
      = ∫ s in (0 : ℝ)..1, F' t s := by
    congr 1
    funext s
    rw [(hGd t htT (center + s • a)).deriv, hF'def]
    rfl
  rw [heq]
  exact hmain.2

private theorem rpow_integral_bound {m ρ e : ℝ} (hm : 0 < m) (hρ : 0 < ρ) (he : 2 < e) :
    ∫ s in (0 : ℝ)..1, (m + s * ρ) ^ (1 - e) ≤ ρ⁻¹ * (m ^ (2 - e) / (e - 2)) := by
  have hfun : (fun s : ℝ => (m + s * ρ) ^ (1 - e)) = fun s => (fun u : ℝ => u ^ (1 - e)) (ρ * s + m) := by
    funext s
    simp only
    rw [show m + s * ρ = ρ * s + m by ring]
  rw [hfun, intervalIntegral.integral_comp_mul_add (fun u : ℝ => u ^ (1 - e)) hρ.ne' m,
    mul_zero, zero_add, mul_one]
  have h0 : (0 : ℝ) ∉ uIcc m (ρ + m) := by
    rw [mem_uIcc]
    rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> linarith
  rw [integral_rpow (Or.inr ⟨by linarith, h0⟩), show 1 - e + 1 = 2 - e by ring, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hρ.le)
  have hp : 0 ≤ (ρ + m) ^ (2 - e) := rpow_nonneg (by linarith) _
  rw [show (2 - e) = -(e - 2) by ring, div_neg, ← neg_div]
  rw [← show (2 - e) = -(e - 2) by ring]
  exact (div_le_div_iff_of_pos_right (by linarith)).2 (by linarith)

private theorem potential_time_bound {α a C : ℝ} {U : Space → Space} {P : Space → ℝ}
    (hα1 : 1 < α) (hS : FracSelfSimilarSolves α) (hU : IsRotatingProfile α a 1 U P)
    (hC0 : 0 ≤ C) (hC : ProfileDecay α a U P C) {T t : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (ht : 0 ≤ t) (htT : t < T) {x : Space} (hx : 1 / 16 ≤ dist x center) :
    ‖deriv (fun τ => homotopyPotential center (fracSelfSimilar α a U T τ) x) t‖ ≤
      16 * ‖crossBilinear‖ * C / (4 * α - 1 - 2) * (T - t) ^ (-(2 - 3 / (2 * α))) := by
  rw [(potential_time_deriv hS hU hT htT x).deriv]
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (T - t) ^ (1 / (2 * α)) := ⟨_, rfl⟩
  have hm0 : 0 < m := hm ▸ rpow_pos_of_pos (by linarith) _
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = dist x center := ⟨_, rfl⟩
  have hρ1 : 1 / 16 ≤ ρ := by rw [hρ]; exact hx
  have hρ0 : 0 < ρ := by linarith
  have hρi : ρ⁻¹ ≤ 16 := by
    rw [inv_le_comm₀ hρ0 (by norm_num)]
    linarith
  have hxa : ‖x - center‖ = ρ := by rw [hρ, dist_eq_norm]
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = 4 * α - 1 := ⟨_, rfl⟩
  have he2 : 2 < e := by rw [he]; linarith
  have hα0 : α ≠ 0 := by positivity
  have hBC : 0 ≤ ‖crossBilinear‖ * C := mul_nonneg (norm_nonneg _) hC0
  have hpt : ∀ s ∈ Ioc (0 : ℝ) 1, ‖s • cross (deriv (fun τ => fracSelfSimilar α a U T τ
      (center + s • (x - center))) t) (x - center)‖ ≤ ‖crossBilinear‖ * C * (m + s * ρ) ^ (1 - e) := by
    intro s hs
    have hts := (hC T t hT hT1 ht htT (center + s • (x - center))).2.1
    have hz : ‖center + s • (x - center) - center‖ = s * ρ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs.1, hxa]
    rw [hz, ← hm, ← he] at hts
    have hcr : ‖cross (deriv (fun τ => fracSelfSimilar α a U T τ (center + s • (x - center))) t)
        (x - center)‖ ≤ ‖crossBilinear‖ *
          ‖deriv (fun τ => fracSelfSimilar α a U T τ (center + s • (x - center))) t‖ * ρ := by
      have h := crossBilinear.le_opNorm₂
        (deriv (fun τ => fracSelfSimilar α a U T τ (center + s • (x - center))) t) (x - center)
      rw [hxa] at h
      exact h
    have hpos : 0 < m + s * ρ := add_pos_of_pos_of_nonneg hm0 (mul_nonneg hs.1.le hρ0.le)
    have hsp : (m + s * ρ) ^ (1 - e) = (m + s * ρ) * (m + s * ρ) ^ (-e) := by
      rw [sub_eq_add_neg, rpow_add hpos, rpow_one]
    have hle : s * ρ ≤ m + s * ρ := by linarith
    have hr : 0 ≤ (m + s * ρ) ^ (-e) := rpow_nonneg hpos.le _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs.1, hsp]
    calc s * ‖cross (deriv (fun τ => fracSelfSimilar α a U T τ (center + s • (x - center))) t)
          (x - center)‖
        ≤ s * (‖crossBilinear‖ * (C * (m + s * ρ) ^ (-e)) * ρ) :=
          mul_le_mul_of_nonneg_left (hcr.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hts (norm_nonneg _)) hρ0.le)) hs.1.le
      _ = ‖crossBilinear‖ * C * ((s * ρ) * (m + s * ρ) ^ (-e)) := by ring
      _ ≤ ‖crossBilinear‖ * C * ((m + s * ρ) * (m + s * ρ) ^ (-e)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle hr) hBC
  have hcont : ContinuousOn (fun s : ℝ => ‖crossBilinear‖ * C * (m + s * ρ) ^ (1 - e))
      (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_const.mul ((continuousOn_const.add (continuousOn_id.mul continuousOn_const)).rpow_const
      (fun s hs => Or.inl (add_pos_of_pos_of_nonneg hm0 (mul_nonneg hs.1 hρ0.le)).ne'))
  have h1 := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (ae_of_all _ hpt) (hcont.intervalIntegrable (μ := volume))
  rw [intervalIntegral.integral_const_mul] at h1
  have h2 := rpow_integral_bound hm0 hρ0 he2
  have hmr : m ^ (2 - e) = (T - t) ^ (-(2 - 3 / (2 * α))) := by
    rw [hm, ← rpow_mul (by linarith)]
    congr 1
    rw [he]
    field_simp
    ring
  have hmp : 0 ≤ m ^ (2 - e) / (e - 2) := div_nonneg (rpow_nonneg hm0.le _) (by linarith)
  calc _ ≤ _ := h1
    _ ≤ ‖crossBilinear‖ * C * (ρ⁻¹ * (m ^ (2 - e) / (e - 2))) := mul_le_mul_of_nonneg_left h2 hBC
    _ ≤ ‖crossBilinear‖ * C * (16 * (m ^ (2 - e) / (e - 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρi hmp) hBC
    _ = 16 * ‖crossBilinear‖ * C / (4 * α - 1 - 2) * (T - t) ^ (-(2 - 3 / (2 * α))) := by
        rw [← hmr, he]
        ring

private theorem time_term_bound {α a C : ℝ} {U : Space → Space} {P : Space → ℝ}
    (hα1 : 1 < α) (hS : FracSelfSimilarSolves α) (hU : IsRotatingProfile α a 1 U P)
    (hC0 : 0 ≤ C) (hC : ProfileDecay α a U P C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x : Space,
      1 / 16 ≤ dist x center →
        ‖deriv (fun τ => fracApproxField α a U T τ x) t‖ ≤ K * (T - t) ^ (-(2 - 3 / (2 * α))) := by
  obtain ⟨KG, hKG, hG⟩ := bounded_iteratedFDeriv (gradient_contDiff centralCut_contDiff)
    (gradient_support centralCut_support) 0
  have he : 0 < 4 * α - 1 - 2 := by linarith
  have hA0 : 0 ≤ C * (1 / 16 : ℝ) ^ (-(4 * α - 1)) := mul_nonneg hC0 (rpow_nonneg (by norm_num) _)
  have hX0 : 0 ≤ 16 * ‖crossBilinear‖ * C / (4 * α - 1 - 2) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) hC0) he.le
  refine ⟨C * (1 / 16 : ℝ) ^ (-(4 * α - 1)) + ‖crossBilinear‖ * KG *
    (16 * ‖crossBilinear‖ * C / (4 * α - 1 - 2)),
    add_nonneg hA0 (mul_nonneg (mul_nonneg (norm_nonneg _) hKG) hX0), ?_⟩
  intro T t hT hT1 ht htT x hx
  have hPw : 1 ≤ (T - t) ^ (-(2 - 3 / (2 * α))) := by
    refine one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) (by linarith) ?_
    have : 3 / (2 * α) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  have hdΨ := potential_time_deriv hS hU hT htT x
  have hΨb := potential_time_bound hα1 hS hU hC0 hC hT hT1 ht htT hx
  have hJ : DifferentiableAt ℝ (fun z : ℝ × Space => fracSelfSimilar α a U T z.1 z.2) (t, x) :=
    ((hS a U P hU T hT).1.contDiffAt
      (prod_mem_nhds (Iio_mem_nhds htT) univ_mem)).differentiableAt (by simp)
  have hin : DifferentiableAt ℝ (fun τ : ℝ => (τ, x)) t :=
    differentiableAt_id.prodMk (differentiableAt_const x)
  have hgt0 : DifferentiableAt ℝ ((fun z : ℝ × Space => fracSelfSimilar α a U T z.1 z.2) ∘
      fun τ : ℝ => (τ, x)) t := hJ.comp t hin
  have hgt : DifferentiableAt ℝ (fun τ => fracSelfSimilar α a U T τ x) t := hgt0
  have hsplit : (fun τ => fracApproxField α a U T τ x) = fun τ => centralCut x • fracSelfSimilar α a U T τ x +
      crossBilinear (gradientAt centralCut x) (homotopyPotential center (fracSelfSimilar α a U T τ) x) := rfl
  have hd1 : HasDerivAt (fun τ => centralCut x • fracSelfSimilar α a U T τ x)
      (centralCut x • deriv (fun τ => fracSelfSimilar α a U T τ x) t) t :=
    hgt.hasDerivAt.const_smul (centralCut x)
  have hd2 : HasDerivAt (fun τ => crossBilinear (gradientAt centralCut x)
      (homotopyPotential center (fracSelfSimilar α a U T τ) x))
      (crossBilinear (gradientAt centralCut x)
        (deriv (fun τ => homotopyPotential center (fracSelfSimilar α a U T τ) x) t)) t :=
    (crossBilinear (gradientAt centralCut x)).hasFDerivAt.comp_hasDerivAt t
      hdΨ.differentiableAt.hasDerivAt
  have hd : HasDerivAt (fun τ => centralCut x • fracSelfSimilar α a U T τ x +
      crossBilinear (gradientAt centralCut x) (homotopyPotential center (fracSelfSimilar α a U T τ) x))
      (centralCut x • deriv (fun τ => fracSelfSimilar α a U T τ x) t +
        crossBilinear (gradientAt centralCut x)
          (deriv (fun τ => homotopyPotential center (fracSelfSimilar α a U T τ) x) t)) t := hd1.add hd2
  rw [hsplit, hd.deriv]
  have hm : 0 ≤ (T - t) ^ (1 / (2 * α)) := rpow_nonneg (by linarith) _
  have hu : ‖deriv (fun τ => fracSelfSimilar α a U T τ x) t‖ ≤ C * (1 / 16 : ℝ) ^ (-(4 * α - 1)) := by
    refine (hC T t hT hT1 ht htT x).2.1.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    rw [← dist_eq_norm]
    exact decay_le (by norm_num) (by norm_num) hm hx (by linarith) le_rfl
  have hGx : ‖gradientAt centralCut x‖ ≤ KG := by
    have := hG x
    rwa [norm_iteratedFDeriv_zero] at this
  have e1 : ‖centralCut x • deriv (fun τ => fracSelfSimilar α a U T τ x) t‖ ≤
      C * (1 / 16 : ℝ) ^ (-(4 * α - 1)) := by
    rw [norm_smul]
    exact (mul_le_mul (centralCut_norm_le x) hu (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul _))
  have e2 : ‖crossBilinear (gradientAt centralCut x)
      (deriv (fun τ => homotopyPotential center (fracSelfSimilar α a U T τ) x) t)‖ ≤
      ‖crossBilinear‖ * KG * (16 * ‖crossBilinear‖ * C / (4 * α - 1 - 2) *
        (T - t) ^ (-(2 - 3 / (2 * α)))) := by
    refine (crossBilinear.le_opNorm₂ _ _).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hGx (norm_nonneg _)) hΨb (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) hKG)
  refine (norm_add_le _ _).trans ?_
  have hB : 0 ≤ ‖crossBilinear‖ * KG := mul_nonneg (norm_nonneg _) hKG
  nlinarith [mul_le_mul_of_nonneg_left hPw hA0]

private theorem segment_far {a b : Space} (ha : 1 / 16 ≤ ‖a‖) (hb : 1 / 16 ≤ ‖b‖)
    (hab : 0 ≤ inner ℝ a b) {z : Space} (hz : z ∈ segment ℝ (center + a) (center + b)) :
    1 / 32 ≤ dist z center := by
  rw [segment_eq_image'] at hz
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hz
  rw [dist_eq_norm]
  have e : center + a + θ • (center + b - (center + a)) - center = (1 - θ) • a + θ • b := by
    rw [add_sub_add_left_eq_sub, smul_sub, sub_smul, one_smul]
    abel
  rw [e]
  have hA : (1 / 256 : ℝ) ≤ ‖a‖ ^ 2 := by nlinarith
  have hB : (1 / 256 : ℝ) ≤ ‖b‖ ^ 2 := by nlinarith
  have hsq : (1 / 32 : ℝ) ^ 2 ≤ ‖(1 - θ) • a + θ • b‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ),
      abs_of_nonneg h0]
    have hc : 0 ≤ (1 - θ) * (θ * inner ℝ a b) := mul_nonneg (by linarith) (mul_nonneg h0 hab)
    nlinarith [mul_le_mul_of_nonneg_left hA (sq_nonneg (1 - θ)),
      mul_le_mul_of_nonneg_left hB (sq_nonneg θ), sq_nonneg (2 * θ - 1)]
  nlinarith [norm_nonneg ((1 - θ) • a + θ • b)]

private theorem segment_difference {p : Space → ℝ} {K : ℝ} (hp : ContDiff ℝ ∞ p)
    (hD : ∀ z, 1 / 32 ≤ dist z center → ‖fderiv ℝ p z‖ ≤ K) {a b : Space} (ha : 1 / 16 ≤ ‖a‖)
    (hb : 1 / 16 ≤ ‖b‖) (hab : 0 ≤ inner ℝ a b) :
    |p (center + b) - p (center + a)| ≤ K * ‖b - a‖ := by
  have hbound : ∀ z ∈ segment ℝ (center + a) (center + b), ‖fderiv ℝ p z‖ ≤ K :=
    fun z hz => hD z (segment_far ha hb hab hz)
  have h := (convex_segment (center + a) (center + b)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hp.differentiable (by simp)) z) hbound (left_mem_segment ℝ _ _)
    (right_mem_segment ℝ _ _)
  rwa [Real.norm_eq_abs, add_sub_add_left_eq_sub] at h

private theorem pressure_difference {p : Space → ℝ} {K : ℝ} (hp : ContDiff ℝ ∞ p) (hK : 0 ≤ K)
    (hD : ∀ z, 1 / 32 ≤ dist z center → ‖fderiv ℝ p z‖ ≤ K) {x : Space}
    (hx1 : centralRadius / 4 ≤ dist x center) (hx2 : dist x center ≤ centralRadius / 2) :
    |p x - p pressureAnchor| ≤ K := by
  obtain ⟨a, ha⟩ : ∃ a : Space, a = x - center := ⟨_, rfl⟩
  have hxa : x = center + a := by rw [ha]; abel
  have hna : 1 / 16 ≤ ‖a‖ ∧ ‖a‖ ≤ 1 / 8 := by
    rw [ha, ← dist_eq_norm]
    norm_num [centralRadius] at hx1 hx2
    constructor <;> linarith
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = if 0 ≤ a 1 then 1 / 8 else -(1 / 8) := ⟨_, rfl⟩
  have hσn : |σ| = 1 / 8 := by rw [hσ]; split_ifs <;> norm_num
  have hσa : 0 ≤ σ * a 1 := by rw [hσ]; split_ifs with h <;> nlinarith
  obtain ⟨n, hn⟩ : ∃ n : Space, n = EuclideanSpace.single 1 σ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Space, b = ((3 / 8 : ℝ) * centralRadius) • unitVector 0 := ⟨_, rfl⟩
  have hanch : pressureAnchor = center + b := by rw [hb]; rfl
  have hnn : ‖n‖ = 1 / 8 := by rw [hn, PiLp.norm_single, Real.norm_eq_abs, hσn]
  have hnb : ‖b‖ = 3 / 32 := by
    rw [hb, norm_smul, norm_unitVector, mul_one, Real.norm_eq_abs]
    norm_num [centralRadius]
  have han : 0 ≤ inner ℝ a n := by
    rw [hn]
    simpa [EuclideanSpace.inner_single_right] using hσa
  have hnb' : 0 ≤ inner ℝ n b := by
    rw [hn, hb]
    simp [unitVector, inner_smul_right, EuclideanSpace.inner_single_left]
  have e1 := segment_difference hp hD hna.1 (by rw [hnn]; norm_num) han
  have e2 := segment_difference hp hD (by rw [hnn]; norm_num) (by rw [hnb]; norm_num) hnb'
  have d1 : ‖n - a‖ ≤ 1 / 4 := by linarith [norm_sub_le n a, hna.2]
  have d2 : ‖b - n‖ ≤ 1 / 4 := by linarith [norm_sub_le b n]
  rw [hxa, hanch]
  calc |p (center + a) - p (center + b)|
      ≤ |p (center + a) - p (center + n)| + |p (center + n) - p (center + b)| := abs_sub_le _ _ _
    _ = |p (center + n) - p (center + a)| + |p (center + b) - p (center + n)| := by
        rw [abs_sub_comm (p (center + n)) (p (center + a)),
          abs_sub_comm (p (center + b)) (p (center + n))]
    _ ≤ K * ‖n - a‖ + K * ‖b - n‖ := add_le_add e1 e2
    _ ≤ K := by nlinarith

private theorem pressure_term_bound {α a C : ℝ} {U : Space → Space} {P : Space → ℝ}
    (hα1 : 1 < α) (hS : FracSelfSimilarSolves α) (hU : IsRotatingProfile α a 1 U P)
    (hC0 : 0 ≤ C) (hC : ProfileDecay α a U P C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x : Space,
      centralRadius / 4 ≤ dist x center → dist x center ≤ centralRadius / 2 →
        ‖gradientAt (fracApproxPressure α a P T t) x‖ ≤ K := by
  obtain ⟨Kc, hKc, hc⟩ := bounded_iteratedFDeriv centralCut_contDiff centralCut_support 1
  obtain ⟨Kp, hKp⟩ : ∃ Kp : ℝ, Kp = C * (1 / 32 : ℝ) ^ (-(4 * α - 1)) := ⟨_, rfl⟩
  have hKp0 : 0 ≤ Kp := hKp ▸ mul_nonneg hC0 (rpow_nonneg (by norm_num) _)
  refine ⟨3 * (Kp + Kp * Kc), by positivity, ?_⟩
  intro T t hT hT1 ht htT x hx1 hx2
  have hp : ContDiff ℝ ∞ (fracSelfSimilarPressure α a P T t) :=
    slice_of_contDiffOn (hS a U P hU T hT).2.1 htT
  have hm : 0 ≤ (T - t) ^ (1 / (2 * α)) := rpow_nonneg (by linarith) _
  have hD : ∀ z, 1 / 32 ≤ dist z center → ‖fderiv ℝ (fracSelfSimilarPressure α a P T t) z‖ ≤ Kp := by
    intro z hz
    refine (fderiv_norm_le_gradient _ z).trans (((hC T t hT hT1 ht htT z).2.2).trans ?_)
    rw [hKp, ← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left (decay_le (by norm_num) (by norm_num) hm hz (by linarith) le_rfl) hC0
  have hdx := pressure_difference hp hKp0 hD hx1 hx2
  have hr : (1 / 32 : ℝ) ≤ dist x center := by norm_num [centralRadius] at hx1; linarith
  have hP' := hD x hr
  have hpd : DifferentiableAt ℝ (fun y => fracSelfSimilarPressure α a P T t y
      - fracSelfSimilarPressure α a P T t pressureAnchor) x :=
    ((hp.differentiable (by simp)) x).sub_const _
  have hcd : DifferentiableAt ℝ centralCut x := (centralCut_contDiff.differentiable (by simp)) x
  have hfun : fracApproxPressure α a P T t = fun y => centralCut y * (fracSelfSimilarPressure α a P T t y
      - fracSelfSimilarPressure α a P T t pressureAnchor) := rfl
  have hfd : fderiv ℝ (fun y => centralCut y * (fracSelfSimilarPressure α a P T t y
      - fracSelfSimilarPressure α a P T t pressureAnchor)) x = centralCut x • fderiv ℝ (fun y =>
      fracSelfSimilarPressure α a P T t y - fracSelfSimilarPressure α a P T t pressureAnchor) x
      + (fracSelfSimilarPressure α a P T t x - fracSelfSimilarPressure α a P T t pressureAnchor) •
      fderiv ℝ centralCut x := (hcd.hasFDerivAt.mul hpd.hasFDerivAt).fderiv
  refine (norm_gradientAt_le _ x).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  rw [hfun, hfd, fderiv_sub_const]
  have hχ' : ‖fderiv ℝ centralCut x‖ ≤ Kc := by
    have := hc x
    rwa [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at this
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs (_ - _)]
  have e1 : ‖centralCut x‖ * ‖fderiv ℝ (fracSelfSimilarPressure α a P T t) x‖ ≤ 1 * Kp :=
    mul_le_mul (centralCut_norm_le x) hP' (norm_nonneg _) zero_le_one
  have e2 : |fracSelfSimilarPressure α a P T t x - fracSelfSimilarPressure α a P T t pressureAnchor|
      * ‖fderiv ℝ centralCut x‖ ≤ Kp * Kc := mul_le_mul hdx hχ' (norm_nonneg _) hKp0
  linarith

private theorem majorant_integrable {β : ℝ} (hβ : β < 3) (C K : ℝ) :
    Integrable ((Metric.ball (0 : Space) (1 / 8)).indicator
      (fun w : Space => C * ‖w‖ ^ (-β) + K)) := by
  have h1 : IntegrableOn (fun w : Space => C * ‖w‖ ^ (-β)) (Metric.ball 0 (1 / 8)) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := |C|) (α := β) (by simp)
      (by simp; linarith) (ae_of_all _ fun w => ?_) ?_
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (rpow_nonneg (norm_nonneg _) _)]
    · exact (measurable_const.mul (measurable_norm.pow_const _)).aestronglyMeasurable
  have h2 : IntegrableOn (fun _ : Space => K) (Metric.ball 0 (1 / 8)) :=
    integrableOn_const measure_ball_lt_top.ne
  exact (integrable_indicator_iff measurableSet_ball).2 (h1.add h2)

private theorem far_integral {f : Space → Space} {G : Space → ℝ} (hf : Continuous f)
    (hsupp : ∀ y, 1 / 8 ≤ dist y center → f y = 0) (hG : Integrable G)
    (hmaj : ∀ y, y ≠ center → ‖f y‖ ≤ G (y - center)) {r β : ℝ} (hr : 0 < r) (hβ : 0 ≤ β)
    (x : Space) :
    IntegrableOn (fun z : Space => ‖z‖ ^ (-β) * ‖f (x + z)‖) {z | r < ‖z‖} ∧
      ∫ z in {z | r < ‖z‖}, ‖z‖ ^ (-β) * ‖f (x + z)‖ ≤ r ^ (-β) * ∫ w, G w := by
  have hcs : HasCompactSupport (fun z => ‖f (x + z)‖) := by
    refine HasCompactSupport.intro (isCompact_closedBall (center - x) (1 / 8)) (fun z hz => ?_)
    rw [Metric.mem_closedBall, not_le] at hz
    have hd : dist (x + z) center = dist z (center - x) := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      abel
    simp only [hsupp (x + z) (by rw [hd]; exact hz.le), norm_zero]
  have hcont : Continuous (fun z => ‖f (x + z)‖) := (hf.comp (continuous_const.add continuous_id)).norm
  have hS : MeasurableSet {z : Space | r < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hφc : Continuous (fun z : Space => (max ‖z‖ r) ^ (-β) * ‖f (x + z)‖) :=
    ((continuous_norm.max continuous_const).rpow_const
      (fun z => Or.inl (lt_max_of_lt_right hr).ne')).mul hcont
  have hφs : HasCompactSupport (fun z : Space => (max ‖z‖ r) ^ (-β) * ‖f (x + z)‖) :=
    hcs.mul_left
  have hInt1 : IntegrableOn (fun z : Space => ‖z‖ ^ (-β) * ‖f (x + z)‖) {z | r < ‖z‖} :=
    (hφc.integrable_of_hasCompactSupport hφs).integrableOn.congr_fun
      (fun z hz => by have hz' : r < ‖z‖ := hz; show (max ‖z‖ r) ^ (-β) * ‖f (x + z)‖ = _; rw [max_eq_left hz'.le]) hS
  have hInt2 : Integrable (fun z : Space => r ^ (-β) * ‖f (x + z)‖) :=
    (hcont.integrable_of_hasCompactSupport hcs).const_mul _
  refine ⟨hInt1, ?_⟩
  have hcs0 : HasCompactSupport f := by
    refine HasCompactSupport.intro (isCompact_closedBall center (1 / 8)) (fun y hy => ?_)
    rw [Metric.mem_closedBall, not_le] at hy
    exact hsupp y hy.le
  have hfi : Integrable (fun y => ‖f y‖) := (hf.integrable_of_hasCompactSupport hcs0).norm
  have hae : ∀ᵐ y ∂(volume : Measure Space), y ≠ center := by
    rw [ae_iff]
    simp
  calc ∫ z in {z | r < ‖z‖}, ‖z‖ ^ (-β) * ‖f (x + z)‖
      ≤ ∫ z in {z | r < ‖z‖}, r ^ (-β) * ‖f (x + z)‖ :=
        setIntegral_mono_on hInt1 hInt2.integrableOn hS (fun z hz =>
          mul_le_mul_of_nonneg_right (rpow_le_rpow_of_nonpos hr (le_of_lt hz) (by linarith))
            (norm_nonneg _))
    _ ≤ ∫ z, r ^ (-β) * ‖f (x + z)‖ :=
        setIntegral_le_integral hInt2 (ae_of_all _ fun z =>
          mul_nonneg (rpow_nonneg hr.le _) (norm_nonneg _))
    _ = r ^ (-β) * ∫ y, ‖f y‖ := by
        rw [integral_const_mul, integral_add_left_eq_self (fun y => ‖f y‖) x]
    _ ≤ r ^ (-β) * ∫ y, G (y - center) := by
        refine mul_le_mul_of_nonneg_left (integral_mono_ae hfi (hG.comp_sub_right center) ?_)
          (rpow_nonneg hr.le _)
        filter_upwards [hae] with y hy
        exact hmaj y hy
    _ = r ^ (-β) * ∫ w, G w := by rw [integral_sub_right_eq_self (fun w => G w) center]

private theorem norm_four_add_le (a b c d : Space) : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have e1 := norm_add_le (a + b + c) d
  have e2 := norm_add_le (a + b) c
  have e3 := norm_add_le a b
  linarith

private theorem approx_majorant {α a C : ℝ} {U : Space → Space} {P : Space → ℝ}
    (hα1 : 1 < α) (hα3 : α < 3 / 2) (hS : FracSelfSimilarSolves α)
    (hU : IsRotatingProfile α a 1 U P) (hC0 : 0 ≤ C) (hC : ProfileDecay α a U P C)
    (hF : FracApproxFieldProperties α) {KG : ℝ} (hKG : 0 ≤ KG)
    (hG : ∀ y, ‖iteratedFDeriv ℝ 0 (gradientAt centralCut) y‖ ≤ KG) {T t : ℝ} (hT : 0 < T)
    (hT1 : T ≤ 1) (ht : 0 ≤ t) (htT : t < T) (y : Space) (hy : y ≠ center) :
    ‖fracApproxField α a U T t y‖ ≤ (Metric.ball (0 : Space) (1 / 8)).indicator
      (fun w : Space => C * ‖w‖ ^ (-(2 * α - 1)) + ‖crossBilinear‖ * KG *
        (∫ s in (0 : ℝ)..1, ‖crossBilinear‖ * 8 * (C * (1 / 64 : ℝ) ^ (-(2 * α + 2))) *
          s ^ (2 - 2 * α))) (y - center) := by
  have hKΨ0 := potential_integral_nonneg (α := α) hC0
  by_cases hyb : dist y center < 1 / 8
  · have hmem : y - center ∈ Metric.ball (0 : Space) (1 / 8) := by
      rw [mem_ball_zero_iff, ← dist_eq_norm]
      exact hyb
    rw [indicator_of_mem hmem]
    have hsplit : fracApproxField α a U T t y = centralCut y • fracSelfSimilar α a U T t y +
        crossBilinear (gradientAt centralCut y) (homotopyPotential center (fracSelfSimilar α a U T t) y) :=
      rfl
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul]
      have hy0 : 0 < ‖y - center‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
      have hu := (hC T t hT hT1 ht htT y).1 0 (by norm_num)
      rw [norm_iteratedFDeriv_zero, Nat.cast_zero, add_zero] at hu
      have hm : 0 ≤ (T - t) ^ (1 / (2 * α)) := rpow_nonneg (by linarith) _
      have h1 : ((T - t) ^ (1 / (2 * α)) + ‖y - center‖) ^ (-(2 * α - 1)) ≤
          ‖y - center‖ ^ (-(2 * α - 1)) := rpow_le_rpow_of_nonpos hy0 (by linarith) (by linarith)
      calc ‖centralCut y‖ * ‖fracSelfSimilar α a U T t y‖
          ≤ 1 * (C * ‖y - center‖ ^ (-(2 * α - 1))) :=
            mul_le_mul (centralCut_norm_le y) (hu.trans (mul_le_mul_of_nonneg_left h1 hC0))
              (norm_nonneg _) zero_le_one
        _ = C * ‖y - center‖ ^ (-(2 * α - 1)) := one_mul _
    · refine (crossBilinear.le_opNorm₂ _ _).trans ?_
      by_cases hyi : dist y center < centralRadius / 4
      · rw [gradient_coreCut_zero hyi, norm_zero, mul_zero, zero_mul]
        exact mul_nonneg (mul_nonneg (norm_nonneg _) hKG) hKΨ0
      · rw [not_lt] at hyi
        have hΨ := potential_region_bound hα1 hα3 hS hU hC0 hC hT hT1 ht htT (y := y)
          (by norm_num [centralRadius] at hyi; linarith) (by linarith) (k := 0) (by norm_num)
        rw [norm_iteratedFDeriv_zero] at hΨ
        have hg := hG y
        rw [norm_iteratedFDeriv_zero] at hg
        exact mul_le_mul (mul_le_mul_of_nonneg_left hg (norm_nonneg _)) hΨ (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) hKG)
  · rw [not_lt] at hyb
    rw [(((hF a U P hU T hT).2.2 t htT y).2.1 (by norm_num [centralRadius]; linarith)).1, norm_zero]
    exact indicator_nonneg (fun w _ => add_nonneg (mul_nonneg hC0 (rpow_nonneg (norm_nonneg _) _))
      (mul_nonneg (mul_nonneg (norm_nonneg _) hKG) hKΨ0)) _

private theorem frac_term_bound {α a C : ℝ} {U : Space → Space} {P : Space → ℝ}
    (hα1 : 1 < α) (hα3 : α < 3 / 2) (hS : FracSelfSimilarSolves α)
    (hU : IsRotatingProfile α a 1 U P) (hC0 : 0 ≤ C) (hC : ProfileDecay α a U P C)
    (hH : HomotopyCurl) (hF : FracApproxFieldProperties α) (hP : FracPointwiseBound α)
    (hI : RemainderIntegrableStatement) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → ∀ x : Space,
      centralRadius / 4 ≤ dist x center → dist x center ≤ centralRadius / 2 →
        ‖fractionalPowerAt α (fracApproxField α a U T t) x‖ ≤ K := by
  obtain ⟨Kf, hKf, hf⟩ := approx_region_bound hα1 hα3 hS hU hC0 hC hH
  obtain ⟨KG, hKG, hG⟩ := bounded_iteratedFDeriv (gradient_contDiff centralCut_contDiff)
    (gradient_support centralCut_support) 0
  obtain ⟨G, hGdef⟩ : ∃ G : Space → ℝ, G = (Metric.ball (0 : Space) (1 / 8)).indicator
      (fun w : Space => C * ‖w‖ ^ (-(2 * α - 1)) + ‖crossBilinear‖ * KG *
        (∫ s in (0 : ℝ)..1, ‖crossBilinear‖ * 8 * (C * (1 / 64 : ℝ) ^ (-(2 * α + 2))) *
          s ^ (2 - 2 * α))) := ⟨_, rfl⟩
  have hGi : Integrable G := hGdef ▸ majorant_integrable (by linarith) _ _
  have hG0 : 0 ≤ ∫ w, G w := integral_nonneg fun w => by
    rw [hGdef]
    exact indicator_nonneg (fun w _ => add_nonneg (mul_nonneg hC0 (rpow_nonneg (norm_nonneg _) _))
      (mul_nonneg (mul_nonneg (norm_nonneg _) hKG) (potential_integral_nonneg hC0))) _
  obtain ⟨C0, hC0', hP'⟩ := hP
  refine ⟨C0 * (Kf * (1 / 64 : ℝ) ^ (3 - 2 * α) + Kf * (1 / 64 : ℝ) ^ (-(2 * α)) +
    (1 / 64 : ℝ) ^ (-(3 + 2 * α)) * ∫ w, G w), ?_, ?_⟩
  · exact mul_nonneg hC0'.le (add_nonneg (add_nonneg (mul_nonneg hKf (rpow_nonneg (by norm_num) _))
      (mul_nonneg hKf (rpow_nonneg (by norm_num) _))) (mul_nonneg (rpow_nonneg (by norm_num) _) hG0))
  intro T t hT hT1 ht htT x hx1 hx2
  have hũ : ContDiff ℝ ∞ (fracApproxField α a U T t) :=
    slice_of_contDiffOn (hF a U P hU T hT).1 htT
  have hsupp : ∀ y, 1 / 8 ≤ dist y center → fracApproxField α a U T t y = 0 := fun y hy =>
    (((hF a U P hU T hT).2.2 t htT y).2.1 (by norm_num [centralRadius]; linarith)).1
  have hcs : HasCompactSupport (fracApproxField α a U T t) := by
    refine HasCompactSupport.intro (isCompact_closedBall center (1 / 8)) (fun y hy => ?_)
    rw [Metric.mem_closedBall, not_le] at hy
    exact hsupp y hy.le
  obtain ⟨K0, _, hb0⟩ := bounded_iteratedFDeriv hũ hcs 0
  have hInt := hI α hα1 hα3 _ hũ (Or.inr ⟨K0, fun y => by
    have := hb0 y
    rwa [norm_iteratedFDeriv_zero] at this⟩) x
  have hmaj : ∀ y, y ≠ center → ‖fracApproxField α a U T t y‖ ≤ G (y - center) := fun y hy =>
    hGdef ▸ approx_majorant hα1 hα3 hS hU hC0 hC hF hKG hG hT hT1 ht htT y hy
  obtain ⟨hIon, hL⟩ := far_integral hũ.continuous hsupp hGi hmaj (by norm_num : (0 : ℝ) < 1 / 64)
    (by linarith : (0 : ℝ) ≤ 3 + 2 * α) x
  have hx1' : 1 / 16 ≤ dist x center := by norm_num [centralRadius] at hx1; linarith
  have hx2' : dist x center ≤ 1 / 8 := by norm_num [centralRadius] at hx2; linarith
  have hB : ∀ y ∈ Metric.closedBall x (1 / 64),
      ‖iteratedFDeriv ℝ 3 (fracApproxField α a U T t) y‖ ≤ Kf := by
    intro y hy
    rw [Metric.mem_closedBall] at hy
    have e1 := dist_triangle x y center
    have e2 := dist_triangle y x center
    rw [dist_comm x y] at e1
    exact hf T t hT hT1 ht htT y (by linarith) (by linarith) 3 le_rfl
  have hA0 := hf T t hT hT1 ht htT x (by linarith) (by linarith) 0 (by norm_num)
  have hA1 := hf T t hT hT1 ht htT x (by linarith) (by linarith) 1 (by norm_num)
  have hA2 := hf T t hT hT1 ht htT x (by linarith) (by linarith) 2 (by norm_num)
  rw [norm_iteratedFDeriv_zero] at hA0
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at hA1
  exact hP' _ (hũ.of_le (nat_le_infty 3)) x (1 / 64) Kf Kf _ (by norm_num) (by norm_num) hInt hB
    hA0 hA1 hA2 hIon hL

end ResidualShell.Internal

open ResidualShell.Internal in
theorem fracResidualShell_of (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4) (hS : FracSelfSimilarSolves α)
    (hD : FracSelfSimilarDecay α) (hF : FracApproxFieldProperties α) (hP : FracPointwiseBound α)
    (hI : RemainderIntegrableStatement) (hH : HomotopyCurl) :
    FracResidualRegionBound α shellRegion := by
  intro a U P hU
  have h3 : α < 3 / 2 := by linarith
  obtain ⟨C, hC0, hC⟩ := decay_nonneg hD hU
  obtain ⟨K1, hK1, ht1⟩ := time_term_bound h1 hS hU hC0 hC
  obtain ⟨Kf, hKf, hf⟩ := approx_region_bound h1 h3 hS hU hC0 hC hH
  obtain ⟨Kr, hKr, hr⟩ := frac_term_bound h1 h3 hS hU hC0 hC hH hF hP hI
  obtain ⟨Kp, hKp, hp⟩ := pressure_term_bound h1 hS hU hC0 hC
  refine ⟨K1 + Kf * Kf + Kr + Kp, fun T t hT hT1 ht htT x hx => ?_⟩
  obtain ⟨hx1, hx2⟩ := hx
  have hx1' : 1 / 16 ≤ dist x center := by norm_num [centralRadius] at hx1; linarith
  have hx2' : dist x center ≤ 1 := by norm_num [centralRadius] at hx2; linarith
  have hPw : 1 ≤ (T - t) ^ (-(2 - 3 / (2 * α))) := by
    refine one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) (by linarith) ?_
    have : 3 / (2 * α) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  have hv := hf T t hT hT1 ht htT x (by linarith) hx2' 0 (by norm_num)
  have hd := hf T t hT hT1 ht htT x (by linarith) hx2' 1 (by norm_num)
  rw [norm_iteratedFDeriv_zero] at hv
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at hd
  have ha : ‖advectionAt (fracApproxField α a U T t) x‖ ≤ Kf * Kf :=
    ((fderiv ℝ (fracApproxField α a U T t) x).le_opNorm _).trans
      (mul_le_mul hd hv (norm_nonneg _) hKf)
  have e1 := ht1 T t hT hT1 ht htT x hx1'
  have e3 := hr T t hT hT1 ht htT x hx1 hx2
  have e4 := hp T t hT hT1 ht htT x hx1 hx2
  unfold fracSpaceResidual
  refine (norm_four_add_le _ _ _ _).trans ?_
  have hrest : 0 ≤ Kf * Kf + Kr + Kp := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hPw hrest]

end Breakdown.Periodic
