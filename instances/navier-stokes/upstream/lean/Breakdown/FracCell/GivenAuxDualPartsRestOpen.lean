import Breakdown.FracCell.GivenAuxDefs
import Breakdown.FracCell.GivenAuxActuatorOpen
import Breakdown.FracCell.GivenAuxDualPartsRestOpenLeaves

open scoped ContDiff ENNReal Topology
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

namespace DualRestOpenInternal

open SteadyCert Filter Set

def pk (Q : MvPolynomial (Fin 2) ℂ) (p : ℝ × ℝ) : ℂ := MvPolynomial.eval ![(p.1 : ℂ), (p.2 : ℂ)] Q

theorem pk_contDiff (Q : MvPolynomial (Fin 2) ℂ) : ContDiff ℝ 1 (pk Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    have : pk (MvPolynomial.C a) = fun _ => a := by funext x; simp [pk]
    rw [this]; exact contDiff_const
  | add p q hp hq =>
    have : pk (p + q) = fun x => pk p x + pk q x := by funext x; simp [pk]
    rw [this]; exact hp.add hq
  | mul_X p i hp =>
    have : pk (p * MvPolynomial.X i) = fun x => pk p x * (![(x.1 : ℂ), (x.2 : ℂ)] i) := by
      funext x; simp [pk]
    rw [this]
    refine hp.mul ?_
    fin_cases i
    · have h := (Complex.ofRealCLM.contDiff (n := 1)).comp (contDiff_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (n := 1))
      simpa [Function.comp_def] using h
    · have h := (Complex.ofRealCLM.contDiff (n := 1)).comp (contDiff_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (n := 1))
      simpa [Function.comp_def] using h

def pkt (Q : MvPolynomial (Fin 2) ℂ) (t x : ℝ) : ℂ := fderiv ℝ (pk Q) (t, x) ((1 : ℝ), (0 : ℝ))

def pkx (Q : MvPolynomial (Fin 2) ℂ) (t x : ℝ) : ℂ := fderiv ℝ (pk Q) (t, x) ((0 : ℝ), (1 : ℝ))

theorem pk_hasDerivAt_t (Q : MvPolynomial (Fin 2) ℂ) (t x : ℝ) :
    HasDerivAt (fun s => pk Q (s, x)) (pkt Q t x) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact ((pk_contDiff Q).differentiable one_ne_zero (t, x)).hasFDerivAt.comp_hasDerivAt t h1

theorem pk_hasDerivAt_x (Q : MvPolynomial (Fin 2) ℂ) (t x : ℝ) :
    HasDerivAt (fun s => pk Q (t, s)) (pkx Q t x) x := by
  have h1 : HasDerivAt (fun s : ℝ => (t, s)) ((0 : ℝ), (1 : ℝ)) x :=
    (hasDerivAt_const x t).prodMk (hasDerivAt_id x)
  exact ((pk_contDiff Q).differentiable one_ne_zero (t, x)).hasFDerivAt.comp_hasDerivAt x h1

theorem pk_bound (Q : MvPolynomial (Fin 2) ℂ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t x : ℝ, |t| ≤ 1 → |x| ≤ 1 →
    ‖pk Q (t, x)‖ ≤ B ∧ ‖pkt Q t x‖ ≤ B ∧ ‖pkx Q t x‖ ≤ B := by
  have hK : IsCompact (Metric.closedBall (0 : ℝ × ℝ) 1) := isCompact_closedBall _ _
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn (pk_contDiff Q).continuous.continuousOn
  obtain ⟨C2, hC2⟩ := hK.exists_bound_of_continuousOn
    ((pk_contDiff Q).continuous_fderiv one_ne_zero).continuousOn
  refine ⟨max (max C1 C2) 0, le_max_right _ _, fun t x ht hx => ?_⟩
  have hm : (t, x) ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by
    rw [mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le ht hx
  have h1 := hC1 _ hm
  have h2 := hC2 _ hm
  have e1 : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have e2 : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  refine ⟨h1.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_, ?_⟩
  · calc ‖pkt Q t x‖ ≤ ‖fderiv ℝ (pk Q) (t, x)‖ * ‖((1 : ℝ), (0 : ℝ))‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ max (max C1 C2) 0 := by rw [e1, mul_one]; exact h2.trans ((le_max_right _ _).trans (le_max_left _ _))
  · calc ‖pkx Q t x‖ ≤ ‖fderiv ℝ (pk Q) (t, x)‖ * ‖((0 : ℝ), (1 : ℝ))‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ max (max C1 C2) 0 := by rw [e2, mul_one]; exact h2.trans ((le_max_right _ _).trans (le_max_left _ _))

theorem cellIndex_le (l : List ℝ) (u : ℝ) : cellIndex l u ≤ l.length := by
  unfold cellIndex
  calc _ ≤ ((l.drop 1).dropLast).length := List.length_filter_le _ _
    _ ≤ l.length := by simp only [List.length_dropLast, List.length_drop]; omega

theorem pieces_bound (S : Spline) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t x : ℝ, |t| ≤ 1 → |x| ≤ 1 →
    ∀ i j, i ≤ S.mesh.tBreaks.length → j ≤ S.mesh.xBreaks.length →
      ‖pk (S.piece i j) (t, x)‖ ≤ B ∧ ‖pkt (S.piece i j) t x‖ ≤ B ∧ ‖pkx (S.piece i j) t x‖ ≤ B := by
  choose B hB0 hB using fun ij : ℕ × ℕ => pk_bound (S.piece ij.1 ij.2)
  let R := Finset.range (S.mesh.tBreaks.length + 1) ×ˢ Finset.range (S.mesh.xBreaks.length + 1)
  have hle : ∀ ij ∈ R, B ij ≤ ∑ k ∈ R, B k := fun ij h => Finset.single_le_sum (fun k _ => hB0 k) h
  refine ⟨∑ k ∈ R, B k, Finset.sum_nonneg fun k _ => hB0 k, fun t x ht hx i j hi hj => ?_⟩
  have hmem : (i, j) ∈ R := Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩
  obtain ⟨h1, h2, h3⟩ := hB (i, j) t x ht hx
  exact ⟨h1.trans (hle _ hmem), h2.trans (hle _ hmem), h3.trans (hle _ hmem)⟩

theorem cellIndex_right (l : List ℝ) (u : ℝ) : ∀ᶠ s in 𝓝[≥] u, cellIndex l s = cellIndex l u := by
  have h : ∀ b ∈ ((l.drop 1).dropLast).toFinset, ∀ᶠ s in 𝓝[≥] u, decide (b ≤ s) = decide (b ≤ u) := by
    intro b _
    rcases le_or_gt b u with hb | hb
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : u ≤ s := hs
      simp [hb, hb.trans hs']
    · filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hb)] with s hs
      simp [not_le.2 hb, not_le.2 hs]
  filter_upwards [(Filter.eventually_all_finset _).2 h] with s hs
  unfold cellIndex
  congr 1
  exact List.filter_congr fun b hb => hs b (List.mem_toFinset.2 hb)

theorem cellIndex_left_neg (l : List ℝ) (u : ℝ) : ∀ᶠ s in 𝓝[≤] u, cellIndex l (-s) = cellIndex l (-u) := by
  have h : ∀ b ∈ ((l.drop 1).dropLast).toFinset, ∀ᶠ s in 𝓝[≤] u, decide (b ≤ -s) = decide (b ≤ -u) := by
    intro b _
    rcases le_or_gt b (-u) with hb | hb
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : s ≤ u := hs
      have : b ≤ -s := by linarith
      simp [hb, this]
    · filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds (show -b < u by linarith))] with s hs
      have : ¬ b ≤ -s := by linarith
      simp [not_le.2 hb, this]
  filter_upwards [(Filter.eventually_all_finset _).2 h] with s hs
  unfold cellIndex
  congr 1
  exact List.filter_congr fun b hb => hs b (List.mem_toFinset.2 hb)

theorem deriv_norm_le_of_eq {g h : ℝ → ℂ} {u : ℝ} {s : Set ℝ} (hs : UniqueDiffWithinAt ℝ s u)
    {h' : ℂ} (hh : HasDerivAt h h' u) (he : g =ᶠ[𝓝[s] u] h) (hu : g u = h u) :
    ‖deriv g u‖ ≤ ‖h'‖ := by
  by_cases hg : DifferentiableAt ℝ g u
  · have h1 : HasDerivWithinAt h (deriv g u) s u :=
      hg.hasDerivAt.hasDerivWithinAt.congr_of_eventuallyEq he.symm hu.symm
    rw [hs.eq_deriv _ h1 hh.hasDerivWithinAt]
  · rw [deriv_zero_of_not_differentiableAt hg, norm_zero]; exact norm_nonneg _

theorem sign_norm_le (b : Bool) : ‖(if b then (-1 : ℂ) else 1)‖ ≤ 1 := by
  split_ifs <;> simp

theorem shape_tderiv (S : Spline) (odd : Bool) : ∃ B : ℝ, 0 ≤ B ∧ ∀ (W : ℝ → ℂ) (c : ℂ) (x t : ℝ) (W' : ℂ),
    HasDerivAt W W' t → 0 ≤ t → t ≤ 1 → |x| ≤ 1 →
    ‖deriv (fun s => W s * c * S.eval odd s x) t‖ ≤ (‖W'‖ + ‖W t‖) * ‖c‖ * B := by
  obtain ⟨B, hB0, hB⟩ := pieces_bound S
  refine ⟨B, hB0, fun W c x t W' hW ht0 ht1 hx => ?_⟩
  set Q := S.piece (cellIndex S.mesh.tBreaks t) (cellIndex S.mesh.xBreaks |x|) with hQ
  set σ : ℂ := if (odd && decide (x < 0)) then -1 else 1 with hσ
  have hh : HasDerivAt (fun s => W s * c * (σ * pk Q (s, |x|)))
      (W' * c * (σ * pk Q (t, |x|)) + W t * c * (σ * pkt Q t |x|)) t :=
    (hW.mul_const c).mul ((pk_hasDerivAt_t Q t |x|).const_mul σ)
  have he : (fun s => W s * c * S.eval odd s x) =ᶠ[𝓝[≥] t] (fun s => W s * c * (σ * pk Q (s, |x|))) := by
    filter_upwards [cellIndex_right S.mesh.tBreaks t] with s hs
    simp only [Spline.eval, Spline.evalHalf, pk, hQ, hσ, hs]
  have hu : (fun s => W s * c * S.eval odd s x) t = (fun s => W s * c * (σ * pk Q (s, |x|))) t := by
    simp only [Spline.eval, Spline.evalHalf, pk, hQ, hσ]
  refine (deriv_norm_le_of_eq (uniqueDiffWithinAt_Ici t) hh he hu).trans ?_
  have hxa : |(|x|)| ≤ 1 := by rwa [abs_abs]
  have hta : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
  obtain ⟨b1, b2, -⟩ := hB t |x| hta hxa _ _ (cellIndex_le _ _) (cellIndex_le _ _)
  have hs1 : ‖σ‖ ≤ 1 := sign_norm_le _
  calc _ ≤ ‖W' * c * (σ * pk Q (t, |x|))‖ + ‖W t * c * (σ * pkt Q t |x|)‖ := norm_add_le _ _
    _ = ‖W'‖ * ‖c‖ * (‖σ‖ * ‖pk Q (t, |x|)‖) + ‖W t‖ * ‖c‖ * (‖σ‖ * ‖pkt Q t |x|‖) := by
        simp only [norm_mul]
    _ ≤ ‖W'‖ * ‖c‖ * (1 * B) + ‖W t‖ * ‖c‖ * (1 * B) := by gcongr
    _ = (‖W'‖ + ‖W t‖) * ‖c‖ * B := by ring


theorem shape_xderiv (S : Spline) (odd : Bool) : ∃ B : ℝ, 0 ≤ B ∧ ∀ (V : ℝ → ℂ) (c : ℂ) (t x : ℝ) (V' : ℂ),
    HasDerivAt V V' x → 0 ≤ t → t ≤ 1 → |x| ≤ 1 →
    ‖deriv (fun s => c * V s * S.eval odd t s) x‖ ≤ ‖c‖ * (‖V'‖ + ‖V x‖) * B := by
  obtain ⟨B, hB0, hB⟩ := pieces_bound S
  refine ⟨B, hB0, fun V c t x V' hV ht0 ht1 hx => ?_⟩
  have hta : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
  rcases le_or_gt 0 x with hx0 | hx0
  · set Q := S.piece (cellIndex S.mesh.tBreaks t) (cellIndex S.mesh.xBreaks x) with hQ
    have hh : HasDerivAt (fun s => c * V s * pk Q (t, s)) (c * V' * pk Q (t, x) + c * V x * pkx Q t x) x :=
      (hV.const_mul c).mul (pk_hasDerivAt_x Q t x)
    have he : (fun s => c * V s * S.eval odd t s) =ᶠ[𝓝[≥] x] (fun s => c * V s * pk Q (t, s)) := by
      filter_upwards [cellIndex_right S.mesh.xBreaks x, self_mem_nhdsWithin] with s hs hs0
      have hs0' : 0 ≤ s := le_trans hx0 hs0
      have hn : ¬ s < 0 := not_lt.2 hs0'
      simp only [Spline.eval, Spline.evalHalf, pk, hQ, abs_of_nonneg hs0', hs, hn, decide_false,
        Bool.and_false]
      simp
    have hu : (fun s => c * V s * S.eval odd t s) x = (fun s => c * V s * pk Q (t, s)) x := by
      have hn : ¬ x < 0 := not_lt.2 hx0
      simp only [Spline.eval, Spline.evalHalf, pk, hQ, abs_of_nonneg hx0, hn, decide_false, Bool.and_false]
      simp
    refine (deriv_norm_le_of_eq (uniqueDiffWithinAt_Ici x) hh he hu).trans ?_
    obtain ⟨b1, -, b3⟩ := hB t x hta hx _ _ (cellIndex_le _ _) (cellIndex_le _ _)
    calc _ ≤ ‖c * V' * pk Q (t, x)‖ + ‖c * V x * pkx Q t x‖ := norm_add_le _ _
      _ = ‖c‖ * ‖V'‖ * ‖pk Q (t, x)‖ + ‖c‖ * ‖V x‖ * ‖pkx Q t x‖ := by simp only [norm_mul]
      _ ≤ ‖c‖ * ‖V'‖ * B + ‖c‖ * ‖V x‖ * B := by gcongr
      _ = ‖c‖ * (‖V'‖ + ‖V x‖) * B := by ring
  · set Q := S.piece (cellIndex S.mesh.tBreaks t) (cellIndex S.mesh.xBreaks (-x)) with hQ
    set σ : ℂ := if odd then -1 else 1 with hσ
    have hh : HasDerivAt (fun s => c * V s * (σ * pk Q (t, -s)))
        (c * V' * (σ * pk Q (t, -x)) + c * V x * (σ * ((-1 : ℝ) • pkx Q t (-x)))) x :=
      (hV.const_mul c).mul (((pk_hasDerivAt_x Q t (-x)).scomp x (hasDerivAt_neg x)).const_mul σ)
    have he : (fun s => c * V s * S.eval odd t s) =ᶠ[𝓝[≤] x] (fun s => c * V s * (σ * pk Q (t, -s))) := by
      filter_upwards [cellIndex_left_neg S.mesh.xBreaks x,
        nhdsWithin_le_nhds (eventually_lt_nhds hx0)] with s hs hs0
      simp only [Spline.eval, Spline.evalHalf, pk, hQ, hσ, abs_of_neg hs0, hs, hs0, decide_true,
        Bool.and_true]
    have hu : (fun s => c * V s * S.eval odd t s) x = (fun s => c * V s * (σ * pk Q (t, -s))) x := by
      simp only [Spline.eval, Spline.evalHalf, pk, hQ, hσ, abs_of_neg hx0, hx0, decide_true, Bool.and_true]
    refine (deriv_norm_le_of_eq (uniqueDiffWithinAt_Iic x) hh he hu).trans ?_
    have hxa : |(-x)| ≤ 1 := by rwa [abs_neg]
    obtain ⟨b1, -, b3⟩ := hB t (-x) hta hxa _ _ (cellIndex_le _ _) (cellIndex_le _ _)
    have hs1 : ‖σ‖ ≤ 1 := sign_norm_le _
    calc _ ≤ ‖c * V' * (σ * pk Q (t, -x))‖ + ‖c * V x * (σ * ((-1 : ℝ) • pkx Q t (-x)))‖ := norm_add_le _ _
      _ = ‖c‖ * ‖V'‖ * (‖σ‖ * ‖pk Q (t, -x)‖) + ‖c‖ * ‖V x‖ * (‖σ‖ * ‖pkx Q t (-x)‖) := by
          simp only [norm_mul, norm_smul, norm_neg, norm_one, one_mul]
      _ ≤ ‖c‖ * ‖V'‖ * (1 * B) + ‖c‖ * ‖V x‖ * (1 * B) := by gcongr
      _ = ‖c‖ * (‖V'‖ + ‖V x‖) * B := by ring

theorem shape_bound (S : Spline) (odd : Bool) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t x : ℝ, 0 ≤ t → t ≤ 1 → |x| ≤ 1 →
    ‖S.eval odd t x‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := pieces_bound S
  refine ⟨B, hB0, fun t x ht0 ht1 hx => ?_⟩
  have hta : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
  have hxa : |(|x|)| ≤ 1 := by rwa [abs_abs]
  obtain ⟨b1, -, -⟩ := hB t |x| hta hxa _ _ (cellIndex_le S.mesh.tBreaks t) (cellIndex_le S.mesh.xBreaks |x|)
  simp only [Spline.eval, Spline.evalHalf, norm_mul]
  calc _ ≤ 1 * B := by gcongr; exact sign_norm_le _; exact b1
    _ = B := one_mul B

theorem w_bound (a : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ‖weightPoly a 3 t‖ ≤ (1 - t) ^ 2 := by
  have e1 : 0 ≤ 1 - t := by linarith
  have h3 : (1 - t) ^ 3 ≤ (1 - t) ^ 2 := pow_le_pow_of_le_one e1 (by linarith) (by norm_num)
  rw [weightPoly, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc t ^ a * (1 - t) ^ 3 ≤ 1 * (1 - t) ^ 2 := by gcongr; exact pow_le_one₀ ht0 ht1
    _ = (1 - t) ^ 2 := one_mul _

theorem w_deriv (a : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ W' : ℂ, HasDerivAt (fun s => weightPoly a 3 s) W' t ∧ ‖W'‖ ≤ ((a : ℝ) + 3) * (1 - t) ^ 2 := by
  have e1 : 0 ≤ 1 - t := by linarith
  have h3 : (1 - t) ^ 3 ≤ (1 - t) ^ 2 := pow_le_pow_of_le_one e1 (by linarith) (by norm_num)
  have hf : HasDerivAt (fun s : ℝ => s ^ a * (1 - s) ^ 3)
      ((a : ℝ) * t ^ (a - 1) * (1 - t) ^ 3 - 3 * t ^ a * (1 - t) ^ 2) t := by
    exact ((hasDerivAt_pow a t).mul (((hasDerivAt_id' t).const_sub 1).pow 3)).congr_deriv (by simp only [Pi.pow_apply]; push_cast; ring)
  refine ⟨_, hf.ofReal_comp, ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have hA : (a : ℝ) * t ^ (a - 1) * (1 - t) ^ 3 ≤ (a : ℝ) * (1 * (1 - t) ^ 2) := by
    rw [mul_assoc]; gcongr; exact pow_le_one₀ ht0 ht1
  have hB : 3 * t ^ a * (1 - t) ^ 2 ≤ 3 * 1 * (1 - t) ^ 2 := by
    gcongr; exact pow_le_one₀ ht0 ht1
  nlinarith

theorem v_deriv (N : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    ∃ V' : ℂ, HasDerivAt (fun s : ℝ => ((1 - s ^ 2 : ℝ) : ℂ) ^ N) V' x ∧ ‖V'‖ ≤ 2 * N ∧
      ‖((1 - x ^ 2 : ℝ) : ℂ) ^ N‖ ≤ 1 := by
  have hx2 : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hx
  have hq : ‖((1 - x ^ 2 : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> nlinarith [sq_nonneg x]
  have hf : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * x)) x := by
    exact ((hasDerivAt_pow 2 x).const_sub 1).congr_deriv (by norm_num)
  refine ⟨_, hf.ofReal_comp.pow N, ?_, ?_⟩
  · simp only [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_mul, abs_two]
    have hq' : |1 - x ^ 2| ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs] at hq; exact hq
    have h1 : |1 - x ^ 2| ^ (N - 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hq'
    calc (N : ℝ) * |1 - x ^ 2| ^ (N - 1) * (2 * |x|) ≤ N * 1 * (2 * 1) := by gcongr
      _ = 2 * N := by ring
  · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hq

theorem core_le (P : ChartParams) {t : ℝ} : |coreRatioT P t| ≤ 1 := by
  rw [coreRatioT, abs_of_nonneg (by positivity)]
  exact div_le_one_of_le₀ (by nlinarith [sq_nonneg (P.rc * (1 - t))]) (by positivity)

theorem twist_bound (P : ChartParams) (n : ℤ) (β : ℝ) (f : ℝ → ℝ → ℂ) {t x K1 K2 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (h1 : ‖deriv (fun t' => f t' x) t‖ ≤ K1) (h2 : ‖f t x‖ ≤ K2) :
    ‖twistedScale P n β f t x‖ ≤ K1 + (|(n : ℝ) * β| + |2 * P.eps|) * K2 := by
  have hs : ‖((t * (1 - t) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]; nlinarith
  have hc : ‖Complex.I * (((n : ℝ) * β * coreRatioT P t : ℝ) : ℂ) - ((2 * P.eps * t : ℝ) : ℂ)‖ ≤
      |(n : ℝ) * β| + |2 * P.eps| := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_mul, abs_mul (2 * P.eps)]
    have := core_le P (t := t)
    have ht : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
    gcongr
    · calc |(n : ℝ) * β| * |coreRatioT P t| ≤ |(n : ℝ) * β| * 1 := by gcongr
        _ = _ := mul_one _
    · calc |2 * P.eps| * |t| ≤ |2 * P.eps| * 1 := by gcongr
        _ = _ := mul_one _
  have hK1 : 0 ≤ K1 := (norm_nonneg _).trans h1
  unfold twistedScale radialScale
  calc _ ≤ ‖((t * (1 - t) : ℝ) : ℂ) * deriv (fun t' => f t' x) t‖ +
        ‖(Complex.I * (((n : ℝ) * β * coreRatioT P t : ℝ) : ℂ) - ((2 * P.eps * t : ℝ) : ℂ)) * f t x‖ :=
        norm_add_le _ _
    _ ≤ 1 * K1 + (|(n : ℝ) * β| + |2 * P.eps|) * K2 := by
        rw [norm_mul, norm_mul]; gcongr
    _ = _ := by ring

theorem reduced_bound (P : ChartParams) (D : FieldData) (hD3 : D.highOrder = 3) (n : ℤ) (β : ℝ) (k : Fin 3) :
    ∃ K : ℝ, ∀ t x : ℝ, 0 ≤ t → t ≤ 1 → |x| ≤ 1 → ‖reducedField P D n β t x k‖ ≤ K * (1 - t) ^ 2 := by
  by_cases h0 : n = 0
  · subst h0
    obtain ⟨Bt, hBt0, hBt⟩ := shape_tderiv (D.amp 0).streamAmp true
    obtain ⟨Bx, hBx0, hBx⟩ := shape_xderiv (D.amp 0).streamAmp true
    obtain ⟨BS, hBS0, hBS⟩ := shape_bound (D.amp 0).streamAmp true
    obtain ⟨BG, hBG0, hBG⟩ := shape_bound (D.amp 0).swirlAmp false
    fin_cases k
    · refine ⟨3 * Bx, fun t x ht0 ht1 hx => ?_⟩
      obtain ⟨V', hV, hV'1, hV'2⟩ := v_deriv 1 hx
      have e : reducedField P D 0 β t x 0 = -(weightPoly 1 3 t * deriv (fun s => 1 *
          (fun s : ℝ => ((1 - s ^ 2 : ℝ) : ℂ) ^ 1) s * (D.amp 0).streamAmp.eval true t s) x) := by
        simp only [reducedField, hD3, heightDeriv, ↓reduceIte, Matrix.cons_val_zero, one_mul, pow_one]
      have hd := hBx _ 1 t x V' hV ht0 ht1 hx
      simp only [Fin.zero_eta]
      rw [e, norm_neg, norm_mul]
      have hw := w_bound 1 ht0 ht1
      have hd' : ‖deriv (fun s => 1 * (fun s : ℝ => ((1 - s ^ 2 : ℝ) : ℂ) ^ 1) s *
          (D.amp 0).streamAmp.eval true t s) x‖ ≤ 3 * Bx := by
        refine hd.trans ?_
        rw [norm_one, one_mul]
        have : ‖V'‖ + ‖((1 - x ^ 2 : ℝ) : ℂ) ^ 1‖ ≤ 3 := by push_cast at hV'1; linarith
        nlinarith
      calc _ ≤ (1 - t) ^ 2 * (3 * Bx) := by gcongr
        _ = _ := by ring
    · refine ⟨5 * Bt + (|(0 : ℤ) * β| + |2 * P.eps|) * BS + 2 * BS, fun t x ht0 ht1 hx => ?_⟩
      obtain ⟨W', hW, hW'⟩ := w_deriv 1 ht0 ht1
      have hw := w_bound 1 ht0 ht1
      have e : reducedField P D 0 β t x 1 = -(twistedScale P 0 β (fun t' x' => weightPoly 1 3 t' *
          (D.amp 0).streamAmp.eval true t' x') t x + 2 * (weightPoly 1 3 t * (D.amp 0).streamAmp.eval true t x)) := by
        simp only [reducedField, hD3, ↓reduceIte, Matrix.cons_val_one, Matrix.cons_val_zero]
      simp only [Fin.mk_one]
      rw [e, norm_neg]
      have hd : ‖deriv (fun t' => weightPoly 1 3 t' * (D.amp 0).streamAmp.eval true t' x) t‖ ≤ (5 * Bt) * (1 - t) ^ 2 := by
        have h1 := hBt (fun s => weightPoly 1 3 s) 1 x t W' hW ht0 ht1 hx
        simp only [mul_one, norm_one] at h1
        refine h1.trans ?_
        have : ‖W'‖ + ‖weightPoly 1 3 t‖ ≤ 5 * (1 - t) ^ 2 := by push_cast at hW'; linarith
        nlinarith
      have hv : ‖weightPoly 1 3 t * (D.amp 0).streamAmp.eval true t x‖ ≤ BS * (1 - t) ^ 2 := by
        rw [norm_mul]
        calc _ ≤ (1 - t) ^ 2 * BS := by gcongr; exact hBS t x ht0 ht1 hx
          _ = _ := by ring
      have htw := twist_bound P 0 β (fun t' x' => weightPoly 1 3 t' * (D.amp 0).streamAmp.eval true t' x')
        ht0 ht1 hd hv
      calc _ ≤ ‖twistedScale P 0 β (fun t' x' => weightPoly 1 3 t' * (D.amp 0).streamAmp.eval true t' x') t x‖ +
            ‖(2 : ℂ)‖ * ‖weightPoly 1 3 t * (D.amp 0).streamAmp.eval true t x‖ := by
            rw [← norm_mul]; exact norm_add_le _ _
        _ ≤ (5 * Bt * (1 - t) ^ 2 + (|((0 : ℤ) : ℝ) * β| + |2 * P.eps|) * (BS * (1 - t) ^ 2)) + 2 * (BS * (1 - t) ^ 2) := by
            gcongr
            simp
        _ = _ := by push_cast; ring
    · refine ⟨BG, fun t x ht0 ht1 hx => ?_⟩
      have e : reducedField P D 0 β t x 2 = weightPoly 1 3 t * (D.amp 0).swirlAmp.eval false t x := by
        simp only [reducedField, hD3, ↓reduceIte, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      simp only [Fin.reduceFinMk]
      rw [e, norm_mul]
      calc _ ≤ (1 - t) ^ 2 * BG := by gcongr; exact w_bound 1 ht0 ht1; exact hBG t x ht0 ht1 hx
        _ = _ := by ring
  · obtain ⟨Bt, hBt0, hBt⟩ := shape_tderiv (D.amp n).radialAmp false
    obtain ⟨Bx, hBx0, hBx⟩ := shape_xderiv (D.amp n).polarAmp true
    obtain ⟨BR, hBR0, hBR⟩ := shape_bound (D.amp n).radialAmp false
    obtain ⟨BP, hBP0, hBP⟩ := shape_bound (D.amp n).polarAmp true
    set a := D.lowOrder n with ha
    set A := D.axisOrder n with hA
    have hur : ∀ t x, 0 ≤ t → t ≤ 1 → |x| ≤ 1 →
        ‖weightPoly a 3 t * ((1 - x ^ 2 : ℝ) : ℂ) ^ A * (D.amp n).radialAmp.eval false t x‖ ≤ BR * (1 - t) ^ 2 := by
      intro t x ht0 ht1 hx
      obtain ⟨_, _, _, hv⟩ := v_deriv A hx
      rw [norm_mul, norm_mul]
      calc _ ≤ (1 - t) ^ 2 * 1 * BR := by gcongr; exact w_bound a ht0 ht1; exact hBR t x ht0 ht1 hx
        _ = _ := by ring
    fin_cases k
    · refine ⟨BR, fun t x ht0 ht1 hx => ?_⟩
      have e : reducedField P D n β t x 0 =
          weightPoly a 3 t * ((1 - x ^ 2 : ℝ) : ℂ) ^ A * (D.amp n).radialAmp.eval false t x := by
        simp only [reducedField, hD3, h0, ↓reduceIte, Matrix.cons_val_zero, ha, hA]
      simp only [Fin.zero_eta]
      rw [e]; exact hur t x ht0 ht1 hx
    · refine ⟨BP, fun t x ht0 ht1 hx => ?_⟩
      have e : reducedField P D n β t x 1 =
          weightPoly a 3 t * ((1 - x ^ 2 : ℝ) : ℂ) ^ A * (D.amp n).polarAmp.eval true t x := by
        simp only [reducedField, hD3, h0, ↓reduceIte, Matrix.cons_val_one, Matrix.cons_val_zero, ha, hA]
      simp only [Fin.mk_one]
      rw [e]
      obtain ⟨_, _, _, hv⟩ := v_deriv A hx
      rw [norm_mul, norm_mul]
      calc _ ≤ (1 - t) ^ 2 * 1 * BP := by gcongr; exact w_bound a ht0 ht1; exact hBP t x ht0 ht1 hx
        _ = _ := by ring
    · refine ⟨‖Complex.I / (((n * (P.m : ℤ) : ℤ) : ℂ))‖ * (((a : ℝ) + 4) * Bt + (|(n : ℝ) * β| + |2 * P.eps|) * BR +
        2 * BR + (2 * ((A + 1 : ℕ) : ℝ) + 1) * Bx), fun t x ht0 ht1 hx => ?_⟩
      have e : reducedField P D n β t x 2 = (Complex.I / (((n * (P.m : ℤ) : ℤ) : ℂ))) *
          (twistedScale P n β (fun t' x' => weightPoly a 3 t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ A *
            (D.amp n).radialAmp.eval false t' x') t x +
           2 * (weightPoly a 3 t * ((1 - x ^ 2 : ℝ) : ℂ) ^ A * (D.amp n).radialAmp.eval false t x) -
           deriv (fun s => weightPoly a 3 t * (fun s : ℝ => ((1 - s ^ 2 : ℝ) : ℂ) ^ (A + 1)) s *
             (D.amp n).polarAmp.eval true t s) x) := by
        simp only [reducedField, hD3, h0, ↓reduceIte, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
          heightDeriv, ha, hA]
        congr 3
        funext s
        ring
      simp only [Fin.reduceFinMk]
      rw [e, norm_mul]
      obtain ⟨W', hW, hW'⟩ := w_deriv a ht0 ht1
      obtain ⟨V', hV, hV'1, hV'2⟩ := v_deriv (A + 1) hx
      obtain ⟨_, _, _, hvA⟩ := v_deriv A hx
      have hw := w_bound a ht0 ht1
      have hd : ‖deriv (fun t' => weightPoly a 3 t' * ((1 - x ^ 2 : ℝ) : ℂ) ^ A *
          (D.amp n).radialAmp.eval false t' x) t‖ ≤ ((a + 4) * Bt) * (1 - t) ^ 2 := by
        have h1 := hBt (fun s => weightPoly a 3 s) (((1 - x ^ 2 : ℝ) : ℂ) ^ A) x t W' hW ht0 ht1 hx
        refine h1.trans ?_
        have : ‖W'‖ + ‖weightPoly a 3 t‖ ≤ (a + 4) * (1 - t) ^ 2 := by linarith
        calc _ ≤ ((a + 4) * (1 - t) ^ 2) * 1 * Bt := by gcongr
          _ = _ := by ring
      have htw := twist_bound P n β (fun t' x' => weightPoly a 3 t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ A *
          (D.amp n).radialAmp.eval false t' x') ht0 ht1 hd (hur t x ht0 ht1 hx)
      have hx' := hBx (fun s : ℝ => ((1 - s ^ 2 : ℝ) : ℂ) ^ (A + 1)) (weightPoly a 3 t) t x V' hV ht0 ht1 hx
      have hx'' : ‖deriv (fun s => weightPoly a 3 t * (fun s : ℝ => ((1 - s ^ 2 : ℝ) : ℂ) ^ (A + 1)) s *
             (D.amp n).polarAmp.eval true t s) x‖ ≤ ((2 * ((A + 1 : ℕ) : ℝ) + 1) * Bx) * (1 - t) ^ 2 := by
        refine hx'.trans ?_
        have : ‖V'‖ + ‖((1 - x ^ 2 : ℝ) : ℂ) ^ (A + 1)‖ ≤ 2 * ((A + 1 : ℕ) : ℝ) + 1 := by linarith
        calc _ ≤ (1 - t) ^ 2 * (2 * ((A + 1 : ℕ) : ℝ) + 1) * Bx := by gcongr
          _ = _ := by ring
      have h2 : ‖(2 : ℂ) * (weightPoly a 3 t * ((1 - x ^ 2 : ℝ) : ℂ) ^ A * (D.amp n).radialAmp.eval false t x)‖ ≤
          2 * (BR * (1 - t) ^ 2) := by
        rw [norm_mul]; gcongr; simp; exact hur t x ht0 ht1 hx
      have hsum := (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add htw h2)) hx'')
      calc _ ≤ ‖Complex.I / (((n * (P.m : ℤ) : ℤ) : ℂ))‖ *
            ((a + 4) * Bt * (1 - t) ^ 2 + (|(n : ℝ) * β| + |2 * P.eps|) * (BR * (1 - t) ^ 2) + 2 * (BR * (1 - t) ^ 2) +
              (2 * ((A + 1 : ℕ) : ℝ) + 1) * Bx * (1 - t) ^ 2) := by gcongr
        _ = _ := by ring

theorem coord_le (y : Space) (i : Fin 3) : |y i| ≤ ‖y‖ := by
  have := PiLp.norm_apply_le y i
  rwa [Real.norm_eq_abs] at this

theorem ratio_le (y : Space) (i : Fin 3) : |y i / ‖y‖| ≤ 1 := by
  rw [abs_div, abs_norm]
  exact div_le_one_of_le₀ (coord_le y i) (norm_nonneg _)

theorem height_le (y : Space) : |heightRatio y| ≤ 1 := ratio_le y 2

theorem radial_le (y : Space) (i : Fin 3) : |radialVec y i| ≤ 1 := ratio_le y i

theorem polar_le (y : Space) (i : Fin 3) : |polarVecQ y i| ≤ 1 := by
  have hh := height_le y
  fin_cases i
  · simp only [polarVecQ, Fin.zero_eta, Matrix.cons_val_zero]
    rw [mul_div_assoc, abs_mul]
    exact (mul_le_mul hh (ratio_le y 0) (abs_nonneg _) zero_le_one).trans (by norm_num)
  · simp only [polarVecQ, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [mul_div_assoc, abs_mul]
    exact (mul_le_mul hh (ratio_le y 1) (abs_nonneg _) zero_le_one).trans (by norm_num)
  · simp only [polarVecQ, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, qOf]
    have h2 : heightRatio y ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 hh
    rw [abs_neg, abs_le]
    constructor <;> nlinarith [sq_nonneg (heightRatio y)]

theorem azim_le (y : Space) (i : Fin 3) : |azimVecQ y i| ≤ 1 := by
  fin_cases i
  · simp only [azimVecQ, Fin.zero_eta, Matrix.cons_val_zero]
    rw [neg_div, abs_neg]; exact ratio_le y 1
  · simp only [azimVecQ, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact ratio_le y 0
  · simp [azimVecQ]

theorem chartT_mem (P : ChartParams) (hP : IsChartParams P) (y : Space) : 0 ≤ chartT P y ∧ chartT P y ≤ 1 := by
  have hL := hP.L0_pos
  have hr := norm_nonneg y
  refine ⟨div_nonneg hr (by linarith), div_le_one_of_le₀ (by linarith) (by linarith)⟩

theorem decay_le (P : ChartParams) (hP : IsChartParams P) (y : Space) : ‖((decayFactor P y : ℝ) : ℂ)‖ ≤ 1 := by
  obtain ⟨h0, h1⟩ := chartT_mem P hP y
  have hs0 : 0 ≤ chartS P y := by rw [chartS]; linarith
  have hs1 : chartS P y ≤ 1 := by rw [chartS]; linarith
  rw [Complex.norm_real, Real.norm_eq_abs, decayFactor, abs_of_nonneg (Real.rpow_nonneg hs0 _)]
  exact Real.rpow_le_one hs0 hs1 (by linarith [hP.eps_pos])

theorem phase_norm (P : ChartParams) (n : ℤ) (β : ℝ) (y : Space) : ‖modePhase P n β y‖ = 1 := by
  rw [modePhase, mul_comm]; exact Complex.norm_exp_ofReal_mul_I _

theorem weight_le (P : ChartParams) (hP : IsChartParams P) (y : Space) :
    (1 - chartT P y) ^ 2 ≤ max P.L0 1 ^ 2 * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  have hL := hP.L0_pos
  have hr := norm_nonneg y
  have hm1 : 1 ≤ max P.L0 1 := le_max_right _ _
  have hmL : P.L0 ≤ max P.L0 1 := le_max_left _ _
  have e1 : 1 - chartT P y = P.L0 / (‖y‖ + P.L0) := by
    rw [chartT]; field_simp; ring
  have e2 : (1 + ‖y‖) ^ (-(2 : ℝ)) = ((1 + ‖y‖) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by linarith), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e1, e2, ← div_eq_mul_inv, ← div_pow]
  have hle : P.L0 / (‖y‖ + P.L0) ≤ max P.L0 1 / (1 + ‖y‖) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  exact pow_le_pow_left₀ (by positivity) hle 2

theorem comp_le (d ph R0 R1 R2 : ℂ) (u v w : ℝ) (hd : ‖d‖ ≤ 1) (hph : ‖ph‖ ≤ 1) (hu : |u| ≤ 1)
    (hv : |v| ≤ 1) (hw : |w| ≤ 1) :
    |(d * (ph * (R0 * u + R1 * v + R2 * w))).re| ≤ ‖R0‖ + ‖R1‖ + ‖R2‖ := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_mul]
  have h : ‖R0 * u + R1 * v + R2 * w‖ ≤ ‖R0‖ + ‖R1‖ + ‖R2‖ := by
    refine norm_add₃_le.trans ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have := norm_nonneg R0; have := norm_nonneg R1; have := norm_nonneg R2
    nlinarith [abs_nonneg u, abs_nonneg v, abs_nonneg w, mul_le_mul_of_nonneg_left hu (norm_nonneg R0),
      mul_le_mul_of_nonneg_left hv (norm_nonneg R1), mul_le_mul_of_nonneg_left hw (norm_nonneg R2)]
  calc _ ≤ 1 * (1 * (‖R0‖ + ‖R1‖ + ‖R2‖)) := by gcongr
    _ = _ := by ring

theorem ofComponents_norm_le (w : Fin 3 → ℝ) : ‖ofComponents w‖ ≤ |w 0| + |w 1| + |w 2| := by
  unfold ofComponents
  refine norm_add₃_le.trans ?_
  simp only [EuclideanSpace.norm_single, Real.norm_eq_abs, le_refl]

theorem mode_decay (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD3 : D.highOrder = 3)
    (n : ℤ) (β : ℝ) :
    ∃ C : ℝ, ∀ y, ‖(fun y => ofComponents (fun i => ((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re)) y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  obtain ⟨K0, hK0⟩ := reduced_bound P D hD3 n β 0
  obtain ⟨K1, hK1⟩ := reduced_bound P D hD3 n β 1
  obtain ⟨K2, hK2⟩ := reduced_bound P D hD3 n β 2
  refine ⟨3 * (|K0| + |K1| + |K2|) * max P.L0 1 ^ 2, fun y => ?_⟩
  obtain ⟨ht0, ht1⟩ := chartT_mem P hP y
  have hx := height_le y
  set t := chartT P y
  have hq : 0 ≤ (1 - t) ^ 2 := sq_nonneg _
  have hR : ∀ k : Fin 3, ∀ K : ℝ, (∀ t x : ℝ, 0 ≤ t → t ≤ 1 → |x| ≤ 1 →
      ‖reducedField P D n β t x k‖ ≤ K * (1 - t) ^ 2) →
      ‖reducedField P D n β t (heightRatio y) k‖ ≤ |K| * (1 - t) ^ 2 := fun k K h =>
    (h t _ ht0 ht1 hx).trans (by gcongr; exact le_abs_self K)
  have hc : ∀ i : Fin 3, |((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β t (heightRatio y) 0 * radialVec y i +
        reducedField P D n β t (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n β t (heightRatio y) 2 * azimVecQ y i))).re| ≤ (|K0| + |K1| + |K2|) * (1 - t) ^ 2 := by
    intro i
    refine (comp_le _ _ _ _ _ _ _ _ (decay_le P hP y) (phase_norm P n β y).le (radial_le y i) (polar_le y i)
      (azim_le y i)).trans ?_
    have := hR 0 K0 hK0; have := hR 1 K1 hK1; have := hR 2 K2 hK2
    nlinarith
  refine (ofComponents_norm_le _).trans ?_
  have hw := weight_le P hP y
  have h3 := add_le_add (add_le_add (hc 0) (hc 1)) (hc 2)
  have hS : 0 ≤ |K0| + |K1| + |K2| := by positivity
  calc _ ≤ 3 * ((|K0| + |K1| + |K2|) * (1 - t) ^ 2) := by linarith
    _ ≤ 3 * ((|K0| + |K1| + |K2|) * (max P.L0 1 ^ 2 * (1 + ‖y‖) ^ (-(2 : ℝ)))) := by gcongr
    _ = _ := by ring

theorem inv_weight (y : Space) (r : ℕ) : (1 + ‖y‖) ^ (-(r : ℝ)) = ((1 + ‖y‖) ^ r)⁻¹ := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

theorem far_weight (y : Space) (r k : ℕ) (hk : r ≤ k) (hy : 1 ≤ ‖y‖) :
    ‖y‖ ^ (-(k : ℝ)) ≤ 2 ^ r * (1 + ‖y‖) ^ (-(r : ℝ)) := by
  rw [inv_weight, Real.rpow_neg (by positivity), Real.rpow_natCast]
  have h0 : 0 < ‖y‖ := by linarith
  have h1 : ‖y‖ ^ r ≤ ‖y‖ ^ k := pow_le_pow_right₀ hy hk
  have h2 : (1 + ‖y‖) ^ r ≤ (2 * ‖y‖) ^ r := pow_le_pow_left₀ (by positivity) (by linarith) r
  rw [mul_pow] at h2
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc (‖y‖ ^ k)⁻¹ * (1 + ‖y‖) ^ r ≤ (‖y‖ ^ r)⁻¹ * (2 ^ r * ‖y‖ ^ r) := by
        gcongr
    _ = 2 ^ r := by field_simp

theorem near_weight (y : Space) (r : ℕ) {R : ℝ} (hR : 0 ≤ R) (hy : ‖y‖ ≤ R) :
    1 ≤ (1 + R) ^ r * (1 + ‖y‖) ^ (-(r : ℝ)) := by
  rw [inv_weight, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
  exact pow_le_pow_left₀ (by positivity) (by linarith) r

theorem grad_of_far {F : Space → Space} (hF : ContDiff ℝ 1 F) {R C : ℝ}
    (hfar : ∀ y : Space, R ≤ ‖y‖ → ‖fderiv ℝ F y‖ ≤ C * ‖y‖ ^ (-(4 : ℝ))) :
    ∃ C' : ℝ, ∀ y, ‖fderiv ℝ F y‖ ≤ C' * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  set R' := max R 1
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Space) R').exists_bound_of_continuousOn
    (hF.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨max (|B| * (1 + R') ^ 2) (|C| * 2 ^ 2), fun y => ?_⟩
  have hw : 0 ≤ (1 + ‖y‖) ^ (-(2 : ℝ)) := by positivity
  rcases le_or_gt ‖y‖ R' with hy | hy
  · have hb := hB y (mem_closedBall_zero_iff.2 hy)
    have hn := near_weight y 2 (by positivity : (0 : ℝ) ≤ R') hy
    push_cast at hn
    calc ‖fderiv ℝ F y‖ ≤ |B| * 1 := by rw [mul_one]; exact hb.trans (le_abs_self B)
      _ ≤ |B| * ((1 + R') ^ 2 * (1 + ‖y‖) ^ (-(2 : ℝ))) := by gcongr
      _ = (|B| * (1 + R') ^ 2) * (1 + ‖y‖) ^ (-(2 : ℝ)) := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · have h1 : 1 ≤ ‖y‖ := le_trans (le_max_right _ _) hy.le
    have hf := hfar y (le_trans (le_max_left _ _) hy.le)
    have hk := far_weight y 2 4 (by norm_num) h1
    push_cast at hk
    calc ‖fderiv ℝ F y‖ ≤ |C| * ‖y‖ ^ (-(4 : ℝ)) := hf.trans (by gcongr; exact le_abs_self C)
      _ ≤ |C| * (2 ^ 2 * (1 + ‖y‖) ^ (-(2 : ℝ))) := by gcongr
      _ = (|C| * 2 ^ 2) * (1 + ‖y‖) ^ (-(2 : ℝ)) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

theorem second_of_far {G : Space → (Space →L[ℝ] Space)} {K : NNReal} (hG : LipschitzWith K G) {R C : ℝ}
    (hfar : ∀ y : Space, R ≤ ‖y‖ → LipschitzOnWith (Real.toNNReal (C * ‖y‖ ^ (-(5 : ℝ)))) G (Metric.ball y 1)) :
    ∃ C' : ℝ, ∀ y, ‖fderiv ℝ G y‖ ≤ C' * (1 + ‖y‖) ^ (-(3 : ℝ)) := by
  set R' := max R 1
  refine ⟨max ((K : ℝ) * (1 + R') ^ 3) (|C| * 2 ^ 3), fun y => ?_⟩
  have hw : 0 ≤ (1 + ‖y‖) ^ (-(3 : ℝ)) := by positivity
  rcases le_or_gt ‖y‖ R' with hy | hy
  · have hb := norm_fderiv_le_of_lipschitz ℝ (x₀ := y) hG
    have hn := near_weight y 3 (by positivity : (0 : ℝ) ≤ R') hy
    push_cast at hn
    calc ‖fderiv ℝ G y‖ ≤ (K : ℝ) * 1 := by rw [mul_one]; exact hb
      _ ≤ (K : ℝ) * ((1 + R') ^ 3 * (1 + ‖y‖) ^ (-(3 : ℝ))) := by gcongr
      _ = ((K : ℝ) * (1 + R') ^ 3) * (1 + ‖y‖) ^ (-(3 : ℝ)) := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · have h1 : 1 ≤ ‖y‖ := le_trans (le_max_right _ _) hy.le
    have hf := norm_fderiv_le_of_lipschitzOn ℝ (Metric.ball_mem_nhds y one_pos)
      (hfar y (le_trans (le_max_left _ _) hy.le))
    have hk := far_weight y 3 5 (by norm_num) h1
    push_cast at hk
    have hp : 0 ≤ ‖y‖ ^ (-(5 : ℝ)) := by positivity
    have ht : ((Real.toNNReal (C * ‖y‖ ^ (-(5 : ℝ))) : NNReal) : ℝ) ≤ |C| * ‖y‖ ^ (-(5 : ℝ)) := by
      rw [Real.coe_toNNReal']
      exact max_le (by gcongr; exact le_abs_self C) (by positivity)
    calc ‖fderiv ℝ G y‖ ≤ |C| * ‖y‖ ^ (-(5 : ℝ)) := hf.trans ht
      _ ≤ |C| * (2 ^ 3 * (1 + ‖y‖) ^ (-(3 : ℝ))) := by gcongr
      _ = (|C| * 2 ^ 3) * (1 + ‖y‖) ^ (-(3 : ℝ)) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

theorem slope_of_far {G : Space → (Space →L[ℝ] Space)} (hloc : LocallyLipschitz G) {B : ℝ}
    (hB : ∀ y, ‖G y‖ ≤ B) {R C : ℝ}
    (hfar : ∀ y : Space, R ≤ ‖y‖ → LipschitzOnWith (Real.toNNReal (C * ‖y‖ ^ (-(5 : ℝ)))) G (Metric.ball y 1)) :
    ∃ K : NNReal, LipschitzWith K G := by
  set R' := max R 1
  obtain ⟨K1, hK1⟩ := hloc.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : Space) (R' + 1))
  refine ⟨max K1 (max (Real.toNNReal |C|) (Real.toNNReal (2 * B))), LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hK1' : (K1 : ℝ) ≤ (max K1 (max (Real.toNNReal |C|) (Real.toNNReal (2 * B))) : NNReal) := by
    exact_mod_cast le_max_left _ _
  have hC' : |C| ≤ ((max K1 (max (Real.toNNReal |C|) (Real.toNNReal (2 * B))) : NNReal) : ℝ) := by
    have : Real.toNNReal |C| ≤ max K1 (max (Real.toNNReal |C|) (Real.toNNReal (2 * B))) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    exact (Real.le_coe_toNNReal |C|).trans (by exact_mod_cast this)
  have hB' : 2 * B ≤ ((max K1 (max (Real.toNNReal |C|) (Real.toNNReal (2 * B))) : NNReal) : ℝ) := by
    have : Real.toNNReal (2 * B) ≤ max K1 (max (Real.toNNReal |C|) (Real.toNNReal (2 * B))) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    exact (Real.le_coe_toNNReal _).trans (by exact_mod_cast this)
  set K := max K1 (max (Real.toNNReal |C|) (Real.toNNReal (2 * B)))
  have hd0 := dist_nonneg (x := x) (y := y)
  rcases le_or_gt 1 (dist x y) with hxy | hxy
  · calc dist (G x) (G y) ≤ ‖G x‖ + ‖G y‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 * B := by linarith [hB x, hB y]
      _ ≤ (K : ℝ) * 1 := by rw [mul_one]; exact hB'
      _ ≤ (K : ℝ) * dist x y := by gcongr
  · rcases le_or_gt ‖x‖ R' with hx | hx
    · have hxm : x ∈ Metric.closedBall (0 : Space) (R' + 1) := mem_closedBall_zero_iff.2 (by linarith)
      have hym : y ∈ Metric.closedBall (0 : Space) (R' + 1) := by
        rw [mem_closedBall_zero_iff]
        have := norm_le_norm_add_norm_sub' y x
        rw [dist_eq_norm] at hxy
        have h2 : ‖y - x‖ = ‖x - y‖ := norm_sub_rev _ _
        linarith
      calc dist (G x) (G y) ≤ (K1 : ℝ) * dist x y := hK1.dist_le_mul x hxm y hym
        _ ≤ (K : ℝ) * dist x y := by gcongr
    · have h1 : 1 ≤ ‖x‖ := le_trans (le_max_right _ _) hx.le
      have hl := hfar x (le_trans (le_max_left _ _) hx.le)
      have hym : y ∈ Metric.ball x 1 := by rw [Metric.mem_ball, dist_comm]; exact hxy
      have hp : ‖x‖ ^ (-(5 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)
      have ht : ((Real.toNNReal (C * ‖x‖ ^ (-(5 : ℝ))) : NNReal) : ℝ) ≤ |C| := by
        rw [Real.coe_toNNReal']
        refine max_le ?_ (abs_nonneg _)
        calc C * ‖x‖ ^ (-(5 : ℝ)) ≤ |C| * ‖x‖ ^ (-(5 : ℝ)) := by
              gcongr; exact le_abs_self C
          _ ≤ |C| * 1 := by gcongr
          _ = |C| := mul_one _
      calc dist (G x) (G y) ≤ ((Real.toNNReal (C * ‖x‖ ^ (-(5 : ℝ))) : NNReal) : ℝ) * dist x y :=
            hl.dist_le_mul x (Metric.mem_ball_self one_pos) y hym
        _ ≤ (K : ℝ) * dist x y := by gcongr; exact ht.trans hC'

theorem seg_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Space → E} {C : ℝ}
    (hd : ∀ y, y ≠ 0 → DifferentiableAt ℝ f y) (hb : ∀ y, y ≠ 0 → ‖fderiv ℝ f y‖ ≤ C) {x y : Space}
    (h0 : (0 : Space) ∉ segment ℝ x y) : ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => hd z (fun h => h0 (h ▸ hz))) (fun z hz => hb z (fun h => h0 (h ▸ hz)))
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)

theorem to_origin_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Space → E} {C : ℝ} (hC : 0 ≤ C)
    (hc : Continuous f) (hd : ∀ y, y ≠ 0 → DifferentiableAt ℝ f y) (hb : ∀ y, y ≠ 0 → ‖fderiv ℝ f y‖ ≤ C)
    (x : Space) : ‖f x - f 0‖ ≤ C * ‖x‖ := by
  by_cases hx : x = 0
  · subst hx
    simp
  have hstep : ∀ k : ℕ, ‖f x - f ((1 / ((k : ℝ) + 1)) • x)‖ ≤ C * ‖x‖ := by
    intro k
    set ε : ℝ := 1 / ((k : ℝ) + 1) with hε
    have hε0 : 0 < ε := by positivity
    have hε1 : ε ≤ 1 := by
      rw [hε, div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have h0 : (0 : Space) ∉ segment ℝ (ε • x) x := by
      rintro ⟨a, b, ha, hb0, hab, h⟩
      rw [smul_smul, ← add_smul] at h
      have hpos : 0 < a * ε + b := by
        rcases eq_or_lt_of_le ha with h' | h'
        · rw [← h'] at hab ⊢
          linarith
        · have := mul_pos h' hε0
          linarith
      exact hx ((smul_eq_zero.1 h).resolve_left hpos.ne')
    calc ‖f x - f (ε • x)‖ ≤ C * ‖x - ε • x‖ := seg_le hd hb h0
      _ ≤ C * ‖x‖ := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          rw [show x - ε • x = (1 - ε) • x by rw [sub_smul, one_smul], norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (by linarith)]
          nlinarith [norm_nonneg x]
  have h1 : Filter.Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1)) • x) Filter.atTop (nhds ((0 : ℝ) • x)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.smul_const x
  rw [zero_smul] at h1
  exact le_of_tendsto' ((tendsto_const_nhds.sub ((hc.tendsto 0).comp h1)).norm) hstep

theorem slopeBound_of_punctured_open {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Space → E} {C : ℝ} (hC : 0 ≤ C)
    (hc : Continuous f) (hd : ∀ y, y ≠ 0 → DifferentiableAt ℝ f y) (hb : ∀ y, y ≠ 0 → ‖fderiv ℝ f y‖ ≤ C) :
    LipschitzWith (Real.toNNReal C) f := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ hC, dist_eq_norm, dist_eq_norm]
  by_cases h0 : (0 : Space) ∈ segment ℝ x y
  · have hr : SameRay ℝ (0 - x) (y - 0) := mem_segment_iff_sameRay.1 h0
    have hn : ‖x - y‖ = ‖x‖ + ‖y‖ := by
      have := hr.norm_add
      rw [zero_sub, sub_zero, norm_neg] at this
      rw [norm_sub_rev, ← this]
      congr 1
      abel
    calc ‖f x - f y‖ = ‖(f x - f 0) - (f y - f 0)‖ := by congr 1; abel
      _ ≤ ‖f x - f 0‖ + ‖f y - f 0‖ := norm_sub_le _ _
      _ ≤ C * ‖x‖ + C * ‖y‖ := add_le_add (to_origin_le hC hc hd hb x) (to_origin_le hC hc hd hb y)
      _ = C * ‖x - y‖ := by rw [hn]; ring
  · exact seg_le hd hb (x := y) (y := x) (fun h => h0 (segment_symm ℝ x y ▸ h))

theorem wt_continuous (r : ℝ) : Continuous (fun y : Space => (1 + ‖y‖) ^ (-r)) :=
  (continuous_const.add continuous_norm).rpow_const fun y => Or.inl (by positivity : (0 : ℝ) < 1 + ‖y‖).ne'

theorem wt_memLp (r : ℝ) (hr : 3 / 2 < r) : MemLp (fun y : Space => (1 + ‖y‖) ^ (-r)) 2 volume := by
  rw [memLp_two_iff_integrable_sq (wt_continuous r).aestronglyMeasurable]
  have hi : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(2 * r))) volume := by
    apply integrable_one_add_norm
    simp [finrank_euclideanSpace]
    linarith
  refine hi.congr (Filter.Eventually.of_forall fun y => ?_)
  have h0 : 0 < 1 + ‖y‖ := by positivity
  simp only
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le]
  congr 1
  push_cast
  ring

theorem memLp_of_wt {E : Type*} [NormedAddCommGroup E] {g : Space → E} (C r : ℝ) (hr : 3 / 2 < r)
    (hm : AEStronglyMeasurable g volume) (hb : ∀ᵐ y ∂volume, ‖g y‖ ≤ C * (1 + ‖y‖) ^ (-r)) :
    MemLp g 2 volume := by
  refine ((wt_memLp r hr).const_mul C).of_le hm ?_
  filter_upwards [hb] with y hy
  exact hy.trans (by rw [Real.norm_eq_abs]; exact le_abs_self _)

theorem invNorm_intOn (R : ℝ) : IntegrableOn (fun y : Space => ‖y‖⁻¹) (Metric.ball 0 R) volume := by
  refine (integrableOn_fun_norm_addHaar (E := Space) volume (f := fun r : ℝ => r⁻¹) (r := R)).2 ?_
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]
  refine IntegrableOn.congr_fun ((continuous_id.integrableOn_Icc (a := 0) (b := R)).mono_set Set.Ioo_subset_Icc_self)
    (fun y hy => ?_) measurableSet_Ioo
  have : y ≠ 0 := hy.1.ne'
  simp only [id]
  field_simp

theorem locInt_of_inv {E : Type*} [NormedAddCommGroup E] {g : Space → E} (hm : AEStronglyMeasurable g volume)
    (C : ℝ) (hb : ∀ᵐ y ∂volume, ‖g y‖ ≤ C * ‖y‖⁻¹) : LocallyIntegrable g volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball 0
  refine IntegrableOn.mono_set ?_ hR
  exact Integrable.mono' ((invNorm_intOn R).const_mul C) hm.restrict (ae_restrict_of_ae hb)

theorem inv_wt_le (y : Space) (r : ℝ) (hr : 0 ≤ r) : ‖y‖⁻¹ * (1 + ‖y‖) ^ (-r) ≤ ‖y‖⁻¹ :=
  mul_le_of_le_one_right (inv_nonneg.2 (norm_nonneg y))
    (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by linarith))

theorem norm_inv_mul_le (y : Space) : ‖y‖ * ‖y‖⁻¹ ≤ 1 := by
  rcases eq_or_ne ‖y‖ 0 with h | h
  · simp [h]
  · rw [mul_inv_cancel₀ h]

theorem locInt_of_wt {E : Type*} [NormedAddCommGroup E] {g : Space → E} (hm : AEStronglyMeasurable g volume)
    (C r : ℝ) (hr : 0 ≤ r) (hb : ∀ᵐ y ∂volume, ‖g y‖ ≤ C * (‖y‖⁻¹ * (1 + ‖y‖) ^ (-r))) :
    LocallyIntegrable g volume := by
  refine locInt_of_inv hm (max C 0) ?_
  filter_upwards [hb] with y hy
  have h0 : 0 ≤ ‖y‖⁻¹ * (1 + ‖y‖) ^ (-r) := by positivity
  calc ‖g y‖ ≤ max C 0 * (‖y‖⁻¹ * (1 + ‖y‖) ^ (-r)) := hy.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) h0)
    _ ≤ max C 0 * ‖y‖⁻¹ := mul_le_mul_of_nonneg_left (inv_wt_le y r hr) (le_max_right _ _)

theorem memLp_of_invWt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : Space → E}
    (hm : AEStronglyMeasurable g volume) (C r : ℝ) (hr : 3 / 2 < r)
    (hb : ∀ᵐ y ∂volume, ‖g y‖ ≤ C * (‖y‖⁻¹ * (1 + ‖y‖) ^ (-r))) :
    MemLp (fun y => ‖y‖ • g y) 2 volume := by
  refine memLp_of_wt (max C 0) r hr (continuous_norm.aestronglyMeasurable.smul hm) ?_
  filter_upwards [hb] with y hy
  have h0 : 0 ≤ ‖y‖⁻¹ * (1 + ‖y‖) ^ (-r) := by positivity
  have hw : 0 ≤ (1 + ‖y‖) ^ (-r) := by positivity
  rw [norm_smul, norm_norm]
  calc ‖y‖ * ‖g y‖ ≤ ‖y‖ * (max C 0 * (‖y‖⁻¹ * (1 + ‖y‖) ^ (-r))) := by
        gcongr; exact hy.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) h0)
    _ = max C 0 * (‖y‖ * ‖y‖⁻¹) * (1 + ‖y‖) ^ (-r) := by ring
    _ ≤ max C 0 * 1 * (1 + ‖y‖) ^ (-r) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_inv_mul_le y) (le_max_right _ _)) hw
    _ = max C 0 * (1 + ‖y‖) ^ (-r) := by ring

end DualRestOpenInternal

theorem atomScalar_slope (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (ha : a ≤ 1) (hS : IsAtomSpline (decide (a = 0)) S j) (hM : j = 0 → M.natAbs = a) :
    ∃ K : NNReal, LipschitzWith K (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) := by
  obtain ⟨hc, hd, C, hC⟩ := atomScalar_punctured P hP j a M β S ha hS hM
  refine ⟨_, DualRestOpenInternal.slopeBound_of_punctured_open (le_max_right C 0) hc hd fun y hy => ?_⟩
  have hw0 : 0 ≤ (1 + ‖y‖) ^ (-(2 : ℝ)) := by positivity
  have hw1 : (1 + ‖y‖) ^ (-(2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by norm_num)
  calc _ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := hC y hy
    _ ≤ max C 0 * (1 + ‖y‖) ^ (-(2 : ℝ)) := by gcongr; exact le_max_left _ _
    _ ≤ max C 0 * 1 := by gcongr
    _ = max C 0 := mul_one _

theorem atomScalar_gradDecay (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (ha : a ≤ 1) (hS : IsAtomSpline (decide (a = 0)) S j) (hM : j = 0 → M.natAbs = a) :
    ∃ C : ℝ, ∀ᵐ y ∂volume, ‖fderiv ℝ (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  obtain ⟨-, -, C, hC⟩ := atomScalar_punctured P hP j a M β S ha hS hM
  refine ⟨C, ?_⟩
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : Space))] with y hy
  exact hC y hy

theorem atomScalar_second (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (ha : a ≤ 1) (hS : IsAtomSpline (decide (a = 0)) S j) (hM : j = 0 → M.natAbs = a) :
    ∃ H : Fin 3 → Space → (Space →L[ℝ] ℂ),
      (∀ k : Fin 3, ∀ φ : Space → ℝ, IsTestScalar φ → ∀ i : Fin 3,
        ∫ y, fderiv ℝ φ y (unitVector i) • fderiv ℝ (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) y (unitVector k) =
          -∫ y, φ y • H k y (unitVector i)) ∧
      (∀ k i : Fin 3, LocallyIntegrable (fun y => H k y (unitVector i)) volume) ∧
      MemLp (fun y => ‖y‖ • ∑ k, H k y (unitVector k)) 2 volume := by
  obtain ⟨C, hC⟩ := atomScalar_secondBound P hP j a M β S ha hS hM
  have hw0 : ∀ y : Space, 0 ≤ ‖y‖⁻¹ * (1 + ‖y‖) ^ (-(3 : ℝ)) := fun y => by positivity
  have hpt : ∀ k i : Fin 3, ∀ᵐ y ∂volume,
      ‖fderiv ℝ (fun z => fderiv ℝ (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) z (unitVector k)) y (unitVector i)‖ ≤
        max C 0 * (‖y‖⁻¹ * (1 + ‖y‖) ^ (-(3 : ℝ))) := fun k i => by
    filter_upwards [hC k] with y hy
    calc _ ≤ ‖fderiv ℝ (fun z => fderiv ℝ (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) z (unitVector k)) y‖ * ‖unitVector i‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (fun z => fderiv ℝ (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) z (unitVector k)) y‖ := by
          rw [show ‖unitVector i‖ = 1 by simp [unitVector], mul_one]
      _ ≤ C * (‖y‖⁻¹ * (1 + ‖y‖) ^ (-(3 : ℝ))) := hy
      _ ≤ max C 0 * (‖y‖⁻¹ * (1 + ‖y‖) ^ (-(3 : ℝ))) := mul_le_mul_of_nonneg_right (le_max_left C 0) (hw0 y)
  have hmeas : ∀ k i : Fin 3, Measurable
      (fun y => fderiv ℝ (fun z => fderiv ℝ (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) z (unitVector k)) y (unitVector i)) :=
    fun k i => measurable_fderiv_apply_const ℝ _ (unitVector i)
  refine ⟨fun k => fderiv ℝ (fun z => fderiv ℝ (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) z (unitVector k)),
    atomScalar_weakSecond P hP j a M β S ha hS hM, fun k i => ?_, ?_⟩
  · exact DualRestOpenInternal.locInt_of_wt (hmeas k i).aestronglyMeasurable (max C 0) 3 (by norm_num) (hpt k i)
  · refine DualRestOpenInternal.memLp_of_invWt
      (Finset.measurable_sum _ fun k _ => hmeas k k).aestronglyMeasurable (3 * max C 0) 3 (by norm_num) ?_
    filter_upwards [hpt 0 0, hpt 1 1, hpt 2 2] with y h0 h1 h2
    rw [Fin.sum_univ_three]
    refine (norm_add₃_le).trans ?_
    linarith

theorem fieldMode_contDiffOne (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (n : ℤ) (hn : n ∈ D.modes) (β : ℝ) :
    ContDiff ℝ 1 (fun y => ofComponents (fun i => ((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re)) := by
  change ContDiff ℝ 1 (modeFieldOf P D β n)
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  by_cases h0 : n = 0
  · subst h0
    by_cases hy : y = 0
    · subst hy
      exact modeFieldOf_contDiffAt_origin_mean P hP hD β hn
    · have hph : modePhase P 0 β = fun _ => 1 := by
        funext z
        simp [modePhase]
      refine modeFieldOf_contDiffAt_of P hP D β 0 (reducedField_mean_contDiff P hP hD β hn) y hy ?_
      rw [hph]
      exact contDiffAt_const
  · by_cases hy : y = 0
    · subst hy
      exact modeFieldOf_contDiffAt_origin_wave P hP hD β n hn h0
    exact modeFieldOf_contDiffAt_axis_of P hP hD β n hn h0 y hy

theorem fieldMode_fderivSlope (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (n : ℤ) (hn : n ∈ D.modes) (β : ℝ) :
    ∃ K : NNReal, LipschitzWith K (fderiv ℝ (fun y => ofComponents (fun i => ((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re))) := by
  show ∃ K : NNReal, LipschitzWith K (fderiv ℝ (modeFieldOf P D β n))
  obtain ⟨R, C, h⟩ := fieldMode_farBounds P hP D hD β n hn
  obtain ⟨R2, C2, h2⟩ := fieldMode_farBounds P hP D hD β n hn
  obtain ⟨Cg, hg⟩ := DualRestOpenInternal.grad_of_far (F := modeFieldOf P D β n)
    (fieldMode_contDiffOne P hP D hD n hn β) (fun y hy => (h2 y hy).1)
  have hB : ∀ y, ‖fderiv ℝ (modeFieldOf P D β n) y‖ ≤ |Cg| := by
    intro y
    have hw0 : 0 ≤ (1 + ‖y‖) ^ (-(2 : ℝ)) := by positivity
    have hw1 : (1 + ‖y‖) ^ (-(2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by norm_num)
    calc _ ≤ Cg * (1 + ‖y‖) ^ (-(2 : ℝ)) := hg y
      _ ≤ |Cg| * (1 + ‖y‖) ^ (-(2 : ℝ)) := by gcongr; exact le_abs_self Cg
      _ ≤ |Cg| * 1 := by gcongr
      _ = |Cg| := mul_one _
  exact DualRestOpenInternal.slope_of_far (fieldMode_fderiv_localSlope P hP D hD β n hn) hB
    (fun y hy => (h y hy).2)

theorem fieldMode_decay (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (n : ℤ) (hn : n ∈ D.modes) (β : ℝ) :
    ∃ C : ℝ, ∀ y, ‖(fun y => ofComponents (fun i => ((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re)) y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  exact DualRestOpenInternal.mode_decay P hP D hD.highOrder_eq n β

theorem fieldMode_gradDecay (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (n : ℤ) (hn : n ∈ D.modes) (β : ℝ) :
    ∃ C : ℝ, ∀ y, ‖fderiv ℝ (fun y => ofComponents (fun i => ((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re)) y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  show ∃ C : ℝ, ∀ y, ‖fderiv ℝ (modeFieldOf P D β n) y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ))
  obtain ⟨R, C, h⟩ := fieldMode_farBounds P hP D hD β n hn
  exact DualRestOpenInternal.grad_of_far (F := modeFieldOf P D β n) (fieldMode_contDiffOne P hP D hD n hn β)
    (fun y hy => (h y hy).1)

theorem fieldMode_secondDecay (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (n : ℤ) (hn : n ∈ D.modes) (β : ℝ) :
    ∃ C : ℝ, ∀ᵐ y ∂volume, ‖fderiv ℝ (fderiv ℝ (fun y => ofComponents (fun i => ((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re))) y‖ ≤ C * (1 + ‖y‖) ^ (-(3 : ℝ)) := by
  show ∃ C : ℝ, ∀ᵐ y ∂volume, ‖fderiv ℝ (fderiv ℝ (modeFieldOf P D β n)) y‖ ≤ C * (1 + ‖y‖) ^ (-(3 : ℝ))
  obtain ⟨K, hK⟩ := fieldMode_fderivSlope P hP D hD n hn β
  obtain ⟨R, C, h⟩ := fieldMode_farBounds P hP D hD β n hn
  obtain ⟨C', hC'⟩ := DualRestOpenInternal.second_of_far (G := fderiv ℝ (modeFieldOf P D β n)) hK
    (fun y hy => (h y hy).2)
  exact ⟨C', Filter.Eventually.of_forall hC'⟩

theorem fluxScalar_radialDiv (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (hS : IsFluxSpline S) :
    ∃ d : Space → ℂ, (∀ φ : Space → ℝ, IsTestScalar φ →
      Integrable (fun y => fderiv ℝ φ y (‖y‖⁻¹ • y) • (((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y)) ∧
      ∫ y, fderiv ℝ φ y (‖y‖⁻¹ • y) • (((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) =
        -∫ y, φ y • d y) ∧
      LocallyIntegrable d volume ∧ MemLp (fun y => ‖y‖ • d y) 2 volume := by
  obtain ⟨hm, C, hC⟩ := fluxScalar_divBound P hP j a M β S hS
  exact ⟨_, fluxScalar_weak P hP j a M β S hS, DualRestOpenInternal.locInt_of_wt hm C 2 (by norm_num) hC,
    DualRestOpenInternal.memLp_of_invWt hm C 2 (by norm_num) hC⟩

end GivenFields

end CellCert

end Breakdown
