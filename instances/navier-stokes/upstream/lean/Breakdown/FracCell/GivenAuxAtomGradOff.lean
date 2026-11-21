import Breakdown.FracCell.GivenAuxActuatorOpen
import Breakdown.FracCell.GivenAuxPinSmoothLocalLeaves

open scoped ContDiff ENNReal Topology
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

namespace AtomGradOffInternal

open Filter Set

theorem eval_atFirst' (c : ℂ) (p : MvPolynomial (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    MvPolynomial.eval v (atFirst c p) = MvPolynomial.eval ![c, v 1] p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [atFirst]
  | add p q hp hq => simp only [atFirst, map_add] at *; rw [hp, hq]
  | mul_X p n hp =>
    simp only [atFirst, map_mul] at *
    rw [hp]
    fin_cases n <;> simp

theorem eval_atSecond' (c : ℂ) (p : MvPolynomial (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    MvPolynomial.eval v (atSecond c p) = MvPolynomial.eval ![v 0, c] p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [atSecond]
  | add p q hp hq => simp only [atSecond, map_add] at *; rw [hp, hq]
  | mul_X p n hp =>
    simp only [atSecond, map_mul] at *
    rw [hp]
    fin_cases n <;> simp

theorem cellIndex_le' (l : List ℝ) (u : ℝ) : cellIndex l u ≤ l.length - 1 - 1 := by
  unfold cellIndex
  calc _ ≤ ((l.drop 1).dropLast).length := List.length_filter_le _ _
    _ = l.length - 1 - 1 := by simp only [List.length_dropLast, List.length_drop]

theorem two_le_length' {l : List ℝ} (h0 : l.head? = some 0) (h1 : l.getLast? = some 1) : 2 ≤ l.length := by
  match l, h0, h1 with
  | [], h0, _ => simp at h0
  | [a], h0, h1 =>
    simp at h0 h1
    rw [h0] at h1
    norm_num at h1
  | _ :: _ :: _, _, _ => simp

theorem interior_lt_one' {l : List ℝ} (hs : l.Pairwise (· < ·)) (hl : l.getLast? = some 1) :
    ∀ e ∈ (l.drop 1).dropLast, e < 1 := by
  intro e he
  rw [List.dropLast_drop_eq_drop_dropLast] at he
  have he' := List.mem_of_mem_drop he
  have happ := List.dropLast_append_getLast? (l := l) 1 (by rw [Option.mem_def]; exact hl)
  rw [← happ, List.pairwise_append] at hs
  exact hs.2.2 e he' 1 (by simp)

theorem interior_pos' {l : List ℝ} (hs : l.Pairwise (· < ·)) (h0 : l.head? = some 0) :
    ∀ e ∈ (l.drop 1).dropLast, 0 < e := by
  intro e he
  match l, hs, h0, he with
  | a :: rest, hs, h0, he =>
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    simp only [List.drop_succ_cons, List.drop_zero] at he
    exact (List.pairwise_cons.1 hs).1 e (List.dropLast_subset _ he)

theorem cellIndex_zero' {l : List ℝ} (hs : l.Pairwise (· < ·)) (h0 : l.head? = some 0) : cellIndex l 0 = 0 := by
  unfold cellIndex
  rw [List.filter_eq_nil_iff.2 (fun e he => by simpa using interior_pos' hs h0 e he)]
  rfl

theorem cellIndex_one' {l : List ℝ} (hs : l.Pairwise (· < ·)) (h1 : l.getLast? = some 1) :
    cellIndex l 1 = l.length - 1 - 1 := by
  unfold cellIndex
  rw [List.filter_eq_self.2 (fun e he => by simpa using (interior_lt_one' hs h1 e he).le)]
  simp only [List.length_dropLast, List.length_drop]

theorem cell_lt (l : List ℝ) (h0 : l.head? = some 0) (h1 : l.getLast? = some 1) (u : ℝ) :
    cellIndex l u < cellCount l := by
  have := cellIndex_le' l u
  have := two_le_length' h0 h1
  unfold cellCount
  omega

theorem spline_t0 {odd : Bool} {j : ℕ} {S : Spline} (hS : IsAtomSpline odd S j) (x : ℝ) : S.eval odd 0 x = 0 := by
  have hm := hS.spline.mesh
  unfold Spline.eval Spline.evalHalf
  rw [cellIndex_zero' hm.t_sorted hm.t_first]
  have h := hS.at_origin _ (cell_lt _ hm.x_first hm.x_last |x|)
  have e := eval_atFirst' 0 (S.piece 0 (cellIndex S.mesh.xBreaks |x|)) ![(0 : ℂ), ((|x| : ℝ) : ℂ)]
  rw [h, map_zero] at e
  rw [Complex.ofReal_zero]
  have e' : MvPolynomial.eval ![(0 : ℂ), ((|x| : ℝ) : ℂ)] (S.piece 0 (cellIndex S.mesh.xBreaks |x|)) = 0 := e.symm
  rw [e', mul_zero]

theorem spline_t1 {odd : Bool} {j : ℕ} {S : Spline} (hS : IsAtomSpline odd S j) (x : ℝ) : S.eval odd 1 x = 0 := by
  have hm := hS.spline.mesh
  unfold Spline.eval Spline.evalHalf
  rw [cellIndex_one' hm.t_sorted hm.t_last]
  have h := (hS.at_infinity _ (cell_lt _ hm.x_first hm.x_last |x|)).1
  have e := eval_atFirst' 1 (S.piece (atomLastT S) (cellIndex S.mesh.xBreaks |x|)) ![(0 : ℂ), ((|x| : ℝ) : ℂ)]
  rw [h, map_zero] at e
  rw [Complex.ofReal_one]
  have e' : MvPolynomial.eval ![(1 : ℂ), ((|x| : ℝ) : ℂ)] (S.piece (atomLastT S) (cellIndex S.mesh.xBreaks |x|)) = 0 :=
    e.symm
  have hl : S.mesh.tBreaks.length - 1 - 1 = atomLastT S := by unfold atomLastT cellCount; rfl
  rw [hl, e', mul_zero]

theorem spline_x1 {odd : Bool} {j : ℕ} {S : Spline} (hS : IsAtomSpline odd S j) (hj : j ≠ 0) (t : ℝ) :
    S.evalHalf t 1 = 0 := by
  have hm := hS.spline.mesh
  unfold Spline.evalHalf
  rw [cellIndex_one' hm.x_sorted hm.x_last]
  have h := hS.at_axis hj _ (cell_lt _ hm.t_first hm.t_last t)
  have e := eval_atSecond' 1 (S.piece (cellIndex S.mesh.tBreaks t) (atomLastX S)) ![((t : ℝ) : ℂ), (0 : ℂ)]
  rw [h, map_zero] at e
  rw [Complex.ofReal_one]
  have hl : S.mesh.xBreaks.length - 1 - 1 = atomLastX S := by unfold atomLastX cellCount; rfl
  rw [hl]
  exact e.symm

theorem spline_bounds (j a : ℕ) (S : Spline) (hS : IsAtomSpline (decide (a = 0)) S j) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t x : ℝ, 0 ≤ t → t ≤ 1 → |x| ≤ 1 →
      ‖S.eval (decide (a = 0)) t x‖ ≤ K * (t * (1 - t)) ∧
      (j ≠ 0 → a = 0 → ‖S.eval (decide (a = 0)) t x‖ ≤ K * (t * (1 - t)) * (1 - x ^ 2)) ∧
      ‖fderiv ℝ (fun p : ℝ × ℝ => S.eval (decide (a = 0)) p.1 p.2) (t, x)‖ ≤ K ∧
      ‖fderiv ℝ (fun p : ℝ × ℝ => S.eval (decide (a = 0)) p.1 p.2) (t, x) (0, 1)‖ ≤ K * (t * (1 - t)) := by
  set F : ℝ × ℝ → ℂ := fun p => S.eval (decide (a = 0)) p.1 p.2 with hFdef
  have hC1 := spline_eval_contDiff S hS.spline le_rfl le_rfl
  have hFd : Differentiable ℝ F := hC1.differentiable one_ne_zero
  have hFc : Continuous (fderiv ℝ F) := hC1.continuous_fderiv one_ne_zero
  set B : Set (ℝ × ℝ) := Set.Icc ((0 : ℝ), (-1 : ℝ)) ((1 : ℝ), (1 : ℝ)) with hB
  have hBc : IsCompact B := isCompact_Icc
  have hBv : Convex ℝ B := convex_Icc _ _
  obtain ⟨C, hC⟩ := hBc.exists_bound_of_continuousOn hFc.continuousOn
  obtain ⟨Λ, hΛ⟩ := ((spline_eval_localSlope S hS.spline le_rfl le_rfl).locallyLipschitzOn (s := B)).exists_lipschitzOnWith_of_compact hBc
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set Λ' := (Λ : ℝ) with hΛ'
  have hΛ0 : 0 ≤ Λ' := Λ.2
  have hmem : ∀ s u : ℝ, 0 ≤ s → s ≤ 1 → |u| ≤ 1 → (s, u) ∈ B := fun s u h0 h1 hu =>
    ⟨Prod.mk_le_mk.2 ⟨h0, (abs_le.1 hu).1⟩, Prod.mk_le_mk.2 ⟨h1, (abs_le.1 hu).2⟩⟩
  have hF0 : ∀ u, F (0, u) = 0 := fun u => spline_t0 hS u
  have hF1 : ∀ u, F (1, u) = 0 := fun u => spline_t1 hS u
  have hgd : ∀ s u : ℝ, HasDerivAt (fun v : ℝ => F (s, v)) (fderiv ℝ F (s, u) (0, 1)) u := by
    intro s u
    have h1 : HasDerivAt (fun v : ℝ => (s, v)) ((0 : ℝ), (1 : ℝ)) u := (hasDerivAt_const u s).prodMk (hasDerivAt_id u)
    exact (hFd (s, u)).hasFDerivAt.comp_hasDerivAt u h1
  have hdx : ∀ s u : ℝ, (∀ v, F (s, v) = 0) → fderiv ℝ F (s, u) (0, 1) = 0 := by
    intro s u hz
    have h3 : HasDerivAt (fun v : ℝ => F (s, v)) 0 u := by
      have : (fun v : ℝ => F (s, v)) = fun _ => 0 := funext hz
      rw [this]; exact hasDerivAt_const _ _
    exact (hgd s u).unique h3
  have hL : ∀ p q, p ∈ B → q ∈ B → ‖fderiv ℝ F p - fderiv ℝ F q‖ ≤ Λ' * ‖p - q‖ := fun p q hp hq => by
    have := hΛ.dist_le_mul p hp q hq
    rwa [dist_eq_norm, dist_eq_norm] at this
  have n01 : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have nd0 : ∀ s u : ℝ, 0 ≤ s → ‖(s, u) - (0, u)‖ = s := fun s u hs => by
    simp [Prod.norm_def, abs_of_nonneg hs, hs]
  have nd1 : ∀ s u : ℝ, s ≤ 1 → ‖(s, u) - (1, u)‖ = 1 - s := fun s u hs => by
    simp [Prod.norm_def, abs_of_nonpos (sub_nonpos.2 hs), hs]
  refine ⟨2 * C' + 2 * Λ', by linarith, fun t x ht0 ht1 hx => ?_⟩
  have hxb : ∀ u : ℝ, |u| ≤ 1 → ‖fderiv ℝ F (t, u) (0, 1)‖ ≤ 2 * Λ' * (t * (1 - t)) := by
    intro u hu
    have hx1 : ‖fderiv ℝ F (t, u) (0, 1)‖ ≤ Λ' * t := by
      have e : fderiv ℝ F (t, u) (0, 1) = (fderiv ℝ F (t, u) - fderiv ℝ F (0, u)) (0, 1) := by
        rw [ContinuousLinearMap.sub_apply, hdx 0 u hF0, sub_zero]
      rw [e]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [n01, mul_one]
      exact (hL _ _ (hmem t u ht0 ht1 hu) (hmem 0 u le_rfl zero_le_one hu)).trans_eq (by rw [nd0 t u ht0])
    have hx2 : ‖fderiv ℝ F (t, u) (0, 1)‖ ≤ Λ' * (1 - t) := by
      have e : fderiv ℝ F (t, u) (0, 1) = (fderiv ℝ F (t, u) - fderiv ℝ F (1, u)) (0, 1) := by
        rw [ContinuousLinearMap.sub_apply, hdx 1 u hF1, sub_zero]
      rw [e]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [n01, mul_one]
      exact (hL _ _ (hmem t u ht0 ht1 hu) (hmem 1 u zero_le_one le_rfl hu)).trans_eq (by rw [nd1 t u ht1])
    have h1t : 0 ≤ 1 - t := by linarith
    have a1 := mul_le_mul_of_nonneg_right hx1 h1t
    have a2 := mul_le_mul_of_nonneg_right hx2 ht0
    calc ‖fderiv ℝ F (t, u) (0, 1)‖ = ‖fderiv ℝ F (t, u) (0, 1)‖ * (1 - t) + ‖fderiv ℝ F (t, u) (0, 1)‖ * t := by ring
      _ ≤ Λ' * t * (1 - t) + Λ' * (1 - t) * t := add_le_add a1 a2
      _ = 2 * Λ' * (t * (1 - t)) := by ring
  have hv1 : ‖F (t, x)‖ ≤ C' * t := by
    have := hBv.norm_image_sub_le_of_norm_fderiv_le (fun p _ => hFd p)
      (fun p hp => (hC p hp).trans (le_max_left C 0)) (hmem 0 x le_rfl zero_le_one hx) (hmem t x ht0 ht1 hx)
    rw [hF0 x, sub_zero] at this
    exact this.trans_eq (by rw [nd0 t x ht0])
  have hv2 : ‖F (t, x)‖ ≤ C' * (1 - t) := by
    have := hBv.norm_image_sub_le_of_norm_fderiv_le (fun p _ => hFd p)
      (fun p hp => (hC p hp).trans (le_max_left C 0)) (hmem 1 x zero_le_one le_rfl hx) (hmem t x ht0 ht1 hx)
    rw [hF1 x, sub_zero] at this
    exact this.trans_eq (by rw [nd1 t x ht1])
  have h1t : 0 ≤ 1 - t := by linarith
  have htt : 0 ≤ t * (1 - t) := mul_nonneg ht0 h1t
  have hvb : ‖F (t, x)‖ ≤ 2 * C' * (t * (1 - t)) := by
    have a1 := mul_le_mul_of_nonneg_right hv1 h1t
    have a2 := mul_le_mul_of_nonneg_right hv2 ht0
    calc ‖F (t, x)‖ = ‖F (t, x)‖ * (1 - t) + ‖F (t, x)‖ * t := by ring
      _ ≤ C' * t * (1 - t) + C' * (1 - t) * t := add_le_add a1 a2
      _ = 2 * C' * (t * (1 - t)) := by ring
  have hq : 0 ≤ 1 - x ^ 2 := by nlinarith [abs_le.1 hx, sq_abs x, abs_nonneg x]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ‖F (t, x)‖ ≤ _
    have e : (2 * C' + 2 * Λ') * (t * (1 - t)) = 2 * C' * (t * (1 - t)) + 2 * Λ' * (t * (1 - t)) := by ring
    rw [e]
    linarith [mul_nonneg hΛ0 htt]
  · intro hj ha0
    have hax : ‖F (t, x)‖ ≤ 2 * Λ' * (t * (1 - t)) * (1 - x ^ 2) := by
      have hodd : decide (a = 0) = true := by simp [ha0]
      have hE1 : F (t, 1) = 0 := by
        show S.eval (decide (a = 0)) t 1 = 0
        unfold Spline.eval
        rw [abs_one, spline_x1 hS hj t, mul_zero]
      have hE2 : F (t, -1) = 0 := by
        show S.eval (decide (a = 0)) t (-1) = 0
        unfold Spline.eval
        rw [abs_neg, abs_one, spline_x1 hS hj t, mul_zero]
      rcases le_total 0 x with hx0 | hx0
      · have := (convex_Icc x 1).norm_image_sub_le_of_norm_deriv_le (f := fun v => F (t, v))
          (fun v _ => (hgd t v).differentiableAt)
          (fun v hv => by
            rw [(hgd t v).deriv]
            exact hxb v (abs_le.2 ⟨by linarith [hv.1], hv.2⟩))
          (left_mem_Icc.2 (abs_le.1 hx).2) (right_mem_Icc.2 (abs_le.1 hx).2)
        rw [hE1, zero_sub, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by linarith [(abs_le.1 hx).2])] at this
        refine this.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        nlinarith [(abs_le.1 hx).2]
      · have := (convex_Icc (-1) x).norm_image_sub_le_of_norm_deriv_le (f := fun v => F (t, v))
          (fun v _ => (hgd t v).differentiableAt)
          (fun v hv => by
            rw [(hgd t v).deriv]
            exact hxb v (abs_le.2 ⟨hv.1, by linarith [hv.2]⟩))
          (left_mem_Icc.2 (abs_le.1 hx).1) (right_mem_Icc.2 (abs_le.1 hx).1)
        rw [hE2, sub_zero, Real.norm_eq_abs, abs_of_nonneg (by linarith [(abs_le.1 hx).1])] at this
        refine this.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        nlinarith [(abs_le.1 hx).1]
    show ‖F (t, x)‖ ≤ _
    refine hax.trans ?_
    have h5 : 0 ≤ t * (1 - t) * (1 - x ^ 2) := mul_nonneg htt hq
    have e : (2 * C' + 2 * Λ') * (t * (1 - t)) * (1 - x ^ 2) =
        2 * C' * (t * (1 - t) * (1 - x ^ 2)) + 2 * Λ' * (t * (1 - t)) * (1 - x ^ 2) := by ring
    rw [e]
    linarith [mul_nonneg hC'0 h5]
  · exact (hC _ (hmem t x ht0 ht1 hx)).trans ((le_max_left _ _).trans (by linarith))
  · refine (hxb x hx).trans ?_
    have e : (2 * C' + 2 * Λ') * (t * (1 - t)) = 2 * C' * (t * (1 - t)) + 2 * Λ' * (t * (1 - t)) := by ring
    rw [e]
    linarith [mul_nonneg hC'0 htt]


theorem q_eq {y : Space} (hy : y ≠ 0) :
    qOf y = ‖(⟨y 0, y 1⟩ : ℂ)‖ ^ 2 / ‖y‖ ^ 2 ∧ qOf y = 1 - heightRatio y ^ 2 := by
  refine ⟨?_, rfl⟩
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have e1 : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [sq_abs]
  have e2 : ‖(⟨y 0, y 1⟩ : ℂ)‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    show y 0 * y 0 + y 1 * y 1 = _
    ring
  unfold qOf heightRatio
  rw [e2, div_pow, eq_div_iff (by positivity), sub_mul, one_mul, div_mul_cancel₀ _ (by positivity)]
  linarith

theorem plane_le (y : Space) : ‖(⟨y 0, y 1⟩ : ℂ)‖ ≤ ‖y‖ := by
  have e1 : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [sq_abs]
  have e2 : ‖(⟨y 0, y 1⟩ : ℂ)‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    show y 0 * y 0 + y 1 * y 1 = _
    ring
  have h : ‖(⟨y 0, y 1⟩ : ℂ)‖ ^ 2 ≤ ‖y‖ ^ 2 := by rw [e1, e2]; nlinarith [sq_nonneg (y 2)]
  nlinarith [norm_nonneg (⟨y 0, y 1⟩ : ℂ), norm_nonneg y]

theorem height_abs_le (y : Space) : |heightRatio y| ≤ 1 := by
  unfold heightRatio
  rw [abs_div, abs_norm]
  rcases (norm_nonneg y).eq_or_lt with h | h
  · simp [← h]
  · rw [div_le_one h]; simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y 2

theorem normD {y : Space} (hy : y ≠ 0) :
    HasFDerivAt (fun z : Space => ‖z‖) (fderiv ℝ (fun z : Space => ‖z‖) y) y ∧
      ‖fderiv ℝ (fun z : Space => ‖z‖) y‖ ≤ 1 := by
  refine ⟨((contDiffAt_norm ℝ hy (n := 1)).differentiableAt one_ne_zero).hasFDerivAt, ?_⟩
  have := norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_one_norm (E := Space)) (x₀ := y)
  simpa using this

theorem plane_sub (z z' : Space) : (⟨z 0, z 1⟩ : ℂ) - ⟨z' 0, z' 1⟩ = ⟨(z - z') 0, (z - z') 1⟩ :=
  Complex.ext (by simp) (by simp)

theorem plane_slope : LipschitzWith 1 (fun z : Space => (⟨z 0, z 1⟩ : ℂ)) := by
  refine LipschitzWith.of_dist_le_mul fun z z' => ?_
  rw [dist_eq_norm, dist_eq_norm, plane_sub, NNReal.coe_one, one_mul]
  exact plane_le _

theorem plane_diff : Differentiable ℝ (fun z : Space => (⟨z 0, z 1⟩ : ℂ)) := by
  have e : (fun y : Space => (⟨y 0, y 1⟩ : ℂ)) = fun y => ((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I :=
    funext fun y => Complex.ext (by simp) (by simp)
  rw [e]
  have h0 : Differentiable ℝ (fun y : Space => y 0) := (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).differentiable
  have h1 : Differentiable ℝ (fun y : Space => y 1) := (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ).differentiable
  exact (Complex.ofRealCLM.differentiable.comp h0).add
    ((Complex.ofRealCLM.differentiable.comp h1).mul (differentiable_const _))

theorem planeD (y : Space) :
    HasFDerivAt (fun z : Space => (⟨z 0, z 1⟩ : ℂ)) (fderiv ℝ (fun z : Space => (⟨z 0, z 1⟩ : ℂ)) y) y ∧
      ‖fderiv ℝ (fun z : Space => (⟨z 0, z 1⟩ : ℂ)) y‖ ≤ 1 := by
  refine ⟨(plane_diff y).hasFDerivAt, ?_⟩
  simpa using norm_fderiv_le_of_lipschitz ℝ plane_slope (x₀ := y)

theorem planeNormD {y : Space} (hw : (⟨y 0, y 1⟩ : ℂ) ≠ 0) :
    HasFDerivAt (fun z : Space => ‖(⟨z 0, z 1⟩ : ℂ)‖) (fderiv ℝ (fun z : Space => ‖(⟨z 0, z 1⟩ : ℂ)‖) y) y ∧
      ‖fderiv ℝ (fun z : Space => ‖(⟨z 0, z 1⟩ : ℂ)‖) y‖ ≤ 1 := by
  have hd : DifferentiableAt ℝ (fun z : Space => ‖(⟨z 0, z 1⟩ : ℂ)‖) y :=
    ((contDiffAt_norm ℝ hw (n := 1)).differentiableAt one_ne_zero).comp y (plane_diff y)
  refine ⟨hd.hasFDerivAt, ?_⟩
  have hl : LipschitzWith 1 (fun z : Space => ‖(⟨z 0, z 1⟩ : ℂ)‖) := by
    have h := (lipschitzWith_one_norm (E := ℂ)).comp plane_slope
    simp only [mul_one] at h
    exact h
  simpa using norm_fderiv_le_of_lipschitz ℝ hl (x₀ := y)

theorem invD {f : Space → ℝ} {f' : Space →L[ℝ] ℝ} {y : Space} (hf : HasFDerivAt f f' y) (h : f y ≠ 0) :
    HasFDerivAt (fun z => (f z)⁻¹) ((-(f y ^ 2)⁻¹) • f') y :=
  (hasDerivAt_inv h).comp_hasFDerivAt y hf

theorem invD_norm (b : ℝ) (f' : Space →L[ℝ] ℝ) : ‖(-(b ^ 2)⁻¹) • f'‖ = (b ^ 2)⁻¹ * ‖f'‖ := by
  rw [norm_smul, norm_neg, norm_inv, norm_pow, Real.norm_eq_abs, sq_abs]

theorem chart_derivs (P : ChartParams) (hP : IsChartParams P) {y : Space} (hy : y ≠ 0) :
    ∃ T' X' : Space →L[ℝ] ℝ, HasFDerivAt (chartT P) T' y ∧ ‖T'‖ ≤ P.L0 / (‖y‖ + P.L0) ^ 2 ∧
      HasFDerivAt heightRatio X' y ∧ ‖X'‖ ≤ 2 / ‖y‖ := by
  obtain ⟨hN, hNn⟩ := normD hy
  set N' := fderiv ℝ (fun z : Space => ‖z‖) y
  have hL := hP.L0_pos
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hne : ‖y‖ + P.L0 ≠ 0 := by positivity
  have hT0 := ((invD (hN.add_const P.L0) hne).const_mul P.L0).const_sub 1
  have eT : (fun z : Space => 1 - P.L0 * (‖z‖ + P.L0)⁻¹) = chartT P := by
    funext z
    unfold chartT
    have : ‖z‖ + P.L0 ≠ 0 := by positivity
    field_simp
    ring
  rw [eT] at hT0
  have hP2 : HasFDerivAt (fun z : Space => z 2) (EuclideanSpace.proj 2 : Space →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj 2 : Space →L[ℝ] ℝ).hasFDerivAt
  have hX0 := hP2.mul (invD hN hr.ne')
  have eX : ((fun z : Space => z 2) * fun z : Space => (‖z‖)⁻¹) = heightRatio := by
    funext z; simp only [Pi.mul_apply]; unfold heightRatio; rw [div_eq_mul_inv]
  rw [eX] at hX0
  refine ⟨_, _, hT0, ?_, hX0, ?_⟩
  · rw [norm_neg, norm_smul, invD_norm, Real.norm_of_nonneg hL.le]
    calc P.L0 * (((‖y‖ + P.L0) ^ 2)⁻¹ * ‖N'‖) ≤ P.L0 * (((‖y‖ + P.L0) ^ 2)⁻¹ * 1) := by gcongr
      _ = P.L0 / (‖y‖ + P.L0) ^ 2 := by ring
  · have hp : ‖(EuclideanSpace.proj 2 : Space →L[ℝ] ℝ)‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
      rw [one_mul]
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v 2
    have h2 : |y 2| ≤ ‖y‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y 2
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, invD_norm, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (‖y‖)⁻¹)]
    calc |y 2| * ((‖y‖ ^ 2)⁻¹ * ‖N'‖) + (‖y‖)⁻¹ * ‖(EuclideanSpace.proj 2 : Space →L[ℝ] ℝ)‖
        ≤ ‖y‖ * ((‖y‖ ^ 2)⁻¹ * 1) + (‖y‖)⁻¹ * 1 := by gcongr
      _ = 2 / ‖y‖ := by field_simp; ring

theorem sqrt_factor {y : Space} (hw : (⟨y 0, y 1⟩ : ℂ) ≠ 0) :
    ∃ c' : Space →L[ℝ] ℂ, HasFDerivAt (fun z => ((Real.sqrt (qOf z) ^ 1 : ℝ) : ℂ)) c' y ∧
      Real.sqrt (qOf y) = ‖(⟨y 0, y 1⟩ : ℂ)‖ / ‖y‖ ∧ ‖c'‖ ≤ 2 / ‖y‖ := by
  have hy : y ≠ 0 := by
    rintro rfl
    exact hw (Complex.ext (by simp) (by simp))
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hsq : ∀ z : Space, z ≠ 0 → Real.sqrt (qOf z) = ‖(⟨z 0, z 1⟩ : ℂ)‖ / ‖z‖ := by
    intro z hz
    rw [(q_eq hz).1, ← div_pow, Real.sqrt_sq (by positivity)]
  obtain ⟨hN, hNn⟩ := normD hy
  obtain ⟨hW, hWn⟩ := planeNormD hw
  have hf := hW.mul (invD hN hr.ne')
  have hfc := (Complex.ofRealCLM.hasFDerivAt (x := ‖(⟨y 0, y 1⟩ : ℂ)‖ * (‖y‖)⁻¹)).comp y hf
  refine ⟨_, hfc.congr_of_eventuallyEq ?_, hsq y hy, ?_⟩
  · filter_upwards [isOpen_ne.mem_nhds hy] with z hz
    simp only [Function.comp_apply, Complex.ofRealCLM_apply, pow_one]
    rw [hsq z hz, div_eq_mul_inv]
    rfl
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [Complex.ofRealCLM_norm, one_mul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, invD_norm, norm_smul, Real.norm_of_nonneg (norm_nonneg _),
      Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (‖y‖)⁻¹)]
    have hρ := plane_le y
    calc ‖(⟨y 0, y 1⟩ : ℂ)‖ * ((‖y‖ ^ 2)⁻¹ * ‖fderiv ℝ (fun z : Space => ‖z‖) y‖) +
          (‖y‖)⁻¹ * ‖fderiv ℝ (fun z : Space => ‖(⟨z 0, z 1⟩ : ℂ)‖) y‖
        ≤ ‖y‖ * ((‖y‖ ^ 2)⁻¹ * 1) + (‖y‖)⁻¹ * 1 := by gcongr
      _ = 2 / ‖y‖ := by field_simp; ring

theorem exp_arg_zpow' (w : ℂ) (hw : w ≠ 0) (k : ℤ) :
    Complex.exp (Complex.I * (((k : ℝ) * Complex.arg w : ℝ) : ℂ)) = (w * ((‖w‖⁻¹ : ℝ) : ℂ)) ^ k := by
  have h1 : Complex.I * (((k : ℝ) * Complex.arg w : ℝ) : ℂ) = (k : ℂ) * ((Complex.arg w : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h1, Complex.exp_int_mul]
  congr 1
  have h2 := Complex.norm_mul_exp_arg_mul_I w
  have h3 : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hw)
  rw [Complex.ofReal_inv, eq_mul_inv_iff_mul_eq₀ h3, mul_comm]
  exact h2

theorem angle_factor (M : ℤ) {y : Space} (hw : (⟨y 0, y 1⟩ : ℂ) ≠ 0) :
    ∃ E' : Space →L[ℝ] ℂ, HasFDerivAt (fun z => Complex.exp (Complex.I * (((M : ℝ) * angleOf z : ℝ) : ℂ))) E' y ∧
      ‖E'‖ ≤ 2 * |(M : ℝ)| / ‖(⟨y 0, y 1⟩ : ℂ)‖ := by
  have hρ0 : 0 < ‖(⟨y 0, y 1⟩ : ℂ)‖ := norm_pos_iff.2 hw
  obtain ⟨hP, hPn⟩ := planeD y
  obtain ⟨hN, hNn⟩ := planeNormD hw
  have hg := invD hN hρ0.ne'
  have hgc := (Complex.ofRealCLM.hasFDerivAt (x := (‖(⟨y 0, y 1⟩ : ℂ)‖)⁻¹)).comp y hg
  have hu := hP.mul hgc
  have hU0 : (⟨y 0, y 1⟩ : ℂ) * (((‖(⟨y 0, y 1⟩ : ℂ)‖)⁻¹ : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero hw (by exact_mod_cast inv_ne_zero hρ0.ne')
  have hUn : ‖(⟨y 0, y 1⟩ : ℂ) * (((‖(⟨y 0, y 1⟩ : ℂ)‖)⁻¹ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hρ0.le), mul_inv_cancel₀ hρ0.ne']
  have hz := (hasDerivAt_zpow M _ (Or.inl hU0)).comp_hasFDerivAt y hu
  refine ⟨_, hz.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [plane_diff.continuous.continuousAt.eventually_ne hw] with z hz
    simp only [Function.comp_apply, Pi.mul_apply]
    rw [angleOf, exp_arg_zpow' _ hz M]
    rfl
  · rw [norm_smul, norm_mul, norm_zpow, hUn, one_zpow, mul_one, Complex.norm_intCast]
    have hD : ‖(⟨y 0, y 1⟩ : ℂ) • (Complex.ofRealCLM.comp
        ((-(‖(⟨y 0, y 1⟩ : ℂ)‖ ^ 2)⁻¹) • fderiv ℝ (fun z : Space => ‖(⟨z 0, z 1⟩ : ℂ)‖) y)) +
        (Complex.ofRealCLM ((‖(⟨y 0, y 1⟩ : ℂ)‖)⁻¹)) • fderiv ℝ (fun z : Space => (⟨z 0, z 1⟩ : ℂ)) y‖ ≤
        2 / ‖(⟨y 0, y 1⟩ : ℂ)‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Complex.ofRealCLM_apply, Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.2 hρ0.le)]
      have h1 : ‖Complex.ofRealCLM.comp ((-(‖(⟨y 0, y 1⟩ : ℂ)‖ ^ 2)⁻¹) •
          fderiv ℝ (fun z : Space => ‖(⟨z 0, z 1⟩ : ℂ)‖) y)‖ ≤ (‖(⟨y 0, y 1⟩ : ℂ)‖ ^ 2)⁻¹ * 1 := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        rw [Complex.ofRealCLM_norm, one_mul, invD_norm]
        gcongr
      calc ‖(⟨y 0, y 1⟩ : ℂ)‖ * ‖Complex.ofRealCLM.comp ((-(‖(⟨y 0, y 1⟩ : ℂ)‖ ^ 2)⁻¹) •
            fderiv ℝ (fun z : Space => ‖(⟨z 0, z 1⟩ : ℂ)‖) y)‖ +
            (‖(⟨y 0, y 1⟩ : ℂ)‖)⁻¹ * ‖fderiv ℝ (fun z : Space => (⟨z 0, z 1⟩ : ℂ)) y‖
          ≤ ‖(⟨y 0, y 1⟩ : ℂ)‖ * ((‖(⟨y 0, y 1⟩ : ℂ)‖ ^ 2)⁻¹ * 1) + (‖(⟨y 0, y 1⟩ : ℂ)‖)⁻¹ * 1 := by gcongr
        _ = 2 / ‖(⟨y 0, y 1⟩ : ℂ)‖ := by field_simp; ring
    calc |(M : ℝ)| * ‖_‖ ≤ |(M : ℝ)| * (2 / ‖(⟨y 0, y 1⟩ : ℂ)‖) := by gcongr; exact hD
      _ = 2 * |(M : ℝ)| / ‖(⟨y 0, y 1⟩ : ℂ)‖ := by ring

theorem amp_factor (P : ChartParams) (hP : IsChartParams P) (jb : ℝ) :
    ∃ CA : ℝ, 0 ≤ CA ∧ ∀ y : Space, y ≠ 0 → ∃ A' : Space →L[ℝ] ℂ,
      HasFDerivAt (fun z => ((decayFactor P z : ℝ) : ℂ) * Complex.exp (Complex.I * ((jb * logPhase P z : ℝ) : ℂ))) A' y ∧
      ‖((decayFactor P y : ℝ) : ℂ) * Complex.exp (Complex.I * ((jb * logPhase P y : ℝ) : ℂ))‖ ≤ 1 ∧
      ‖A'‖ ≤ CA / (‖y‖ + P.L0) := by
  have hL := hP.L0_pos
  have hrc := hP.rc_pos
  have hε := hP.eps_pos
  have hε8 := hP.eps_lt
  refine ⟨2 * P.eps + |jb| * (1 + P.L0 / P.rc), by positivity, fun y hy => ?_⟩
  obtain ⟨hN, hNn⟩ := normD hy
  set r := ‖y‖ with hrdef
  have hr : 0 < r := norm_pos_iff.2 hy
  set L := P.L0 with hLdef
  have hrL : r + L ≠ 0 := by positivity
  have hrL' : 0 < r + L := by positivity
  set sv := 1 - r / (r + L) with hsvdef
  have hsvL : sv = L / (r + L) := by rw [hsvdef]; field_simp; ring
  have hsv0 : 0 < sv := by rw [hsvL]; positivity
  have hsv1 : sv ≤ 1 := by
    rw [hsvdef]
    have : 0 ≤ r / (r + L) := by positivity
    linarith
  have hT : HasDerivAt (fun ρ : ℝ => ρ / (ρ + L)) (L / (r + L) ^ 2) r :=
    ((hasDerivAt_id' r).div ((hasDerivAt_id' r).add_const L) hrL).congr_deriv (by ring)
  have hD := (hT.const_sub 1).rpow_const (p := 2 * P.eps) (Or.inl hsv0.ne')
  have hL1 : HasDerivAt (fun ρ : ℝ => 1 + ρ ^ 2 / P.rc ^ 2) (2 * r / P.rc ^ 2) r :=
    (((hasDerivAt_pow 2 r).div_const (P.rc ^ 2)).const_add 1).congr_deriv (by norm_num)
  have hpos1 : 1 + r ^ 2 / P.rc ^ 2 ≠ 0 := by positivity
  have hψ := ((hL1.log hpos1).const_mul (1 / 2)).const_mul jb
  have hE := ((hψ.ofReal_comp).const_mul Complex.I).cexp
  have hΦ := hD.ofReal_comp.mul hE
  have hF := hΦ.hasFDerivAt.comp y hN
  have hEn : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := fun x => by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x
  have hrp : sv ^ (2 * P.eps) ≤ 1 := Real.rpow_le_one hsv0.le hsv1 (by positivity)
  refine ⟨_, hF.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => rfl), ?_, ?_⟩
  · rw [norm_mul, hEn, mul_one, Complex.norm_real, Real.norm_eq_abs]
    unfold decayFactor chartS chartT
    rw [← hrdef, ← hLdef, ← hsvdef, abs_of_nonneg (by positivity)]
    exact hrp
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_left hNn (norm_nonneg _)).trans ?_
    rw [mul_one]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [ContinuousLinearMap.toSpanSingleton_apply, norm_smul, Real.norm_eq_abs, mul_comm]
    gcongr
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, hEn, mul_one, one_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |-(L / (r + L) ^ 2) * (2 * P.eps) * sv ^ (2 * P.eps - 1)| ≤ 2 * P.eps / (r + L) := by
      rw [Real.rpow_sub_one hsv0.ne', abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity),
        abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      calc L / (r + L) ^ 2 * (2 * P.eps) * (sv ^ (2 * P.eps) / sv)
          ≤ L / (r + L) ^ 2 * (2 * P.eps) * (1 / sv) := by gcongr
        _ = 2 * P.eps / (r + L) := by rw [hsvL]; field_simp
    have h2 : |jb * (1 / 2 * (2 * r / P.rc ^ 2 / (1 + r ^ 2 / P.rc ^ 2)))| ≤ |jb| * (1 + L / P.rc) / (r + L) := by
      have e : 1 / 2 * (2 * r / P.rc ^ 2 / (1 + r ^ 2 / P.rc ^ 2)) = r / (P.rc ^ 2 + r ^ 2) := by field_simp
      rw [e, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ r / (P.rc ^ 2 + r ^ 2)), mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [div_le_div_iff₀ (by positivity) hrL']
      have hk : 0 ≤ L / P.rc := by positivity
      have e3 : L = L / P.rc * P.rc := by field_simp
      have e4 : r * (r + L) = r ^ 2 + L / P.rc * P.rc * r := by rw [mul_add, ← e3]; ring
      rw [e4]
      nlinarith [mul_nonneg hk (sq_nonneg (P.rc - r)), sq_nonneg P.rc]
    have h4 : |(1 - r / (r + L)) ^ (2 * P.eps)| ≤ 1 := by
      rw [← hsvdef, abs_of_nonneg (by positivity)]; exact hrp
    calc |-(L / (r + L) ^ 2) * (2 * P.eps) * (1 - r / (r + L)) ^ (2 * P.eps - 1)| +
          |(1 - r / (r + L)) ^ (2 * P.eps)| * |jb * (1 / 2 * (2 * r / P.rc ^ 2 / (1 + r ^ 2 / P.rc ^ 2)))|
        ≤ 2 * P.eps / (r + L) + 1 * (|jb| * (1 + L / P.rc) / (r + L)) := by
          gcongr
      _ = (2 * P.eps + |jb| * (1 + L / P.rc)) / (r + L) := by ring

end AtomGradOffInternal

theorem atomScalar_offAxisGrad (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (ha : a ≤ 1) (hS : IsAtomSpline (decide (a = 0)) S j) (hM : j = 0 → M.natAbs = a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, (y 0 ≠ 0 ∨ y 1 ≠ 0) →
      DifferentiableAt ℝ (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) y ∧
      ‖fderiv ℝ (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) y‖ ≤
        C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  obtain ⟨K, hK0, hK⟩ := AtomGradOffInternal.spline_bounds j a S hS
  obtain ⟨CA, hCA0, hCA⟩ := AtomGradOffInternal.amp_factor P hP ((j : ℝ) * β)
  have hL := hP.L0_pos
  set C0 := (2 * |(M : ℝ)| + 5 + CA) * K * P.L0 with hC0
  have hC00 : 0 ≤ C0 := by positivity
  refine ⟨C0 * (1 + 1 / P.L0) ^ 2, by positivity, fun y hy => ?_⟩
  have hw : (⟨y 0, y 1⟩ : ℂ) ≠ 0 := by
    intro h
    rcases hy with h0 | h1
    · exact h0 (by simpa using congrArg Complex.re h)
    · exact h1 (by simpa using congrArg Complex.im h)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hw (Complex.ext (by simp) (by simp))
  set r := ‖y‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 hy0
  set ρ := ‖(⟨y 0, y 1⟩ : ℂ)‖ with hρ
  have hρ0 : 0 < ρ := norm_pos_iff.2 hw
  have hqe := AtomGradOffInternal.q_eq hy0
  rw [← hρ, ← hr] at hqe
  have hρr : ρ ≤ r := AtomGradOffInternal.plane_le y
  set W := 1 / (r + P.L0) with hW
  have hW0 : 0 < W := by positivity
  set t0 := chartT P y with ht0
  set x0 := heightRatio y with hx0
  have ht0e : t0 = r * W := by rw [ht0, hW]; unfold chartT; rw [← hr]; field_simp
  have ht1e : 1 - t0 = P.L0 * W := by rw [ht0e, hW]; field_simp; ring
  have hrW : r * W ≤ 1 := by rw [hW, mul_one_div, div_le_one (by positivity)]; linarith
  have ht00 : 0 ≤ t0 := by rw [ht0e]; positivity
  have ht01 : t0 ≤ 1 := by rw [ht0e]; exact hrW
  have hxa : |x0| ≤ 1 := AtomGradOffInternal.height_abs_le y
  obtain ⟨hF0, hFax, hFd, hFx⟩ := hK t0 x0 ht00 ht01 hxa
  set F := fun p : ℝ × ℝ => S.eval (decide (a = 0)) p.1 p.2 with hFdef
  have hFdiff : Differentiable ℝ F := (spline_eval_contDiff S hS.spline le_rfl le_rfl).differentiable one_ne_zero
  obtain ⟨T', X', hT, hTn, hX, hXn⟩ := AtomGradOffInternal.chart_derivs P hP hy0
  set F' := fderiv ℝ F (t0, x0) with hF'
  rw [← hr] at hTn hXn
  have hG : HasFDerivAt (fun z => S.eval (decide (a = 0)) (chartT P z) (heightRatio z)) (F'.comp (T'.prod X')) y := by
    have h := HasFDerivAt.comp (g := F) y (hFdiff (t0, x0)).hasFDerivAt (hT.prodMk hX)
    exact h
  have hmG : ‖S.eval (decide (a = 0)) t0 x0‖ ≤ K * (r * W * (P.L0 * W)) := by
    rw [← ht0e, ← ht1e]; exact hF0
  have hdG : ‖F'.comp (T'.prod X')‖ ≤ 3 * K * P.L0 * W ^ 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have e : (F'.comp (T'.prod X')) v = T' v • F' (1, 0) + X' v • F' (0, 1) := by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ← map_smul, ← map_smul, ← map_add]
      congr 1
      ext <;> simp
    rw [e]
    have n10 : ‖F' (1, 0)‖ ≤ K := by
      refine (F'.le_opNorm _).trans ?_
      have : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp [Prod.norm_def]
      rw [this, mul_one]; exact hFd
    have n01 : ‖F' (0, 1)‖ ≤ K * (r * W * (P.L0 * W)) := by rw [← ht0e, ← ht1e]; exact hFx
    have hTv : ‖T' v‖ ≤ P.L0 * W ^ 2 * ‖v‖ := by
      refine (T'.le_opNorm v).trans (mul_le_mul_of_nonneg_right (hTn.trans_eq ?_) (norm_nonneg _))
      rw [hW]; field_simp
    have hXv : ‖X' v‖ ≤ 2 / r * ‖v‖ := (X'.le_opNorm v).trans (mul_le_mul_of_nonneg_right hXn (norm_nonneg _))
    calc ‖T' v • F' (1, 0) + X' v • F' (0, 1)‖ ≤ ‖T' v‖ * ‖F' (1, 0)‖ + ‖X' v‖ * ‖F' (0, 1)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul]
      _ ≤ (P.L0 * W ^ 2 * ‖v‖) * K + (2 / r * ‖v‖) * (K * (r * W * (P.L0 * W))) := by gcongr
      _ = 3 * K * P.L0 * W ^ 2 * ‖v‖ := by field_simp; ring
  have hcG : ∃ cG' : Space →L[ℝ] ℂ, HasFDerivAt (fun z => ((Real.sqrt (qOf z) ^ a : ℝ) : ℂ) *
        S.eval (decide (a = 0)) (chartT P z) (heightRatio z)) cG' y ∧
      ‖((Real.sqrt (qOf y) ^ a : ℝ) : ℂ) * S.eval (decide (a = 0)) t0 x0‖ ≤ K * (r * W * (P.L0 * W)) ∧
      (M ≠ 0 → ‖((Real.sqrt (qOf y) ^ a : ℝ) : ℂ) * S.eval (decide (a = 0)) t0 x0‖ ≤ K * ρ * P.L0 * W ^ 2) ∧
      ‖cG'‖ ≤ 5 * K * P.L0 * W ^ 2 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha with rfl | rfl
    · refine ⟨F'.comp (T'.prod X'), by simpa using hG, by simpa using hmG, fun hM0 => ?_, ?_⟩
      swap
      · have : 0 ≤ K * P.L0 * W ^ 2 := by positivity
        simp only [Complex.ofReal_one, one_mul]
        linarith
      have hj : j ≠ 0 := fun hj => hM0 (Int.natAbs_eq_zero.1 (hM hj))
      have h1 := hFax hj rfl
      simp only [pow_zero, Complex.ofReal_one, one_mul]
      refine h1.trans ?_
      have e1 : t0 * (1 - t0) = r * W * (P.L0 * W) := by rw [ht1e, ht0e]
      have e2 : 1 - x0 ^ 2 = ρ ^ 2 / r ^ 2 := by rw [← hqe.2, hqe.1]
      rw [e1, e2]
      have : r * W * (P.L0 * W) * (ρ ^ 2 / r ^ 2) = P.L0 * W ^ 2 * ρ * (ρ / r) := by field_simp
      rw [mul_assoc, this]
      have hρr' : ρ / r ≤ 1 := by rw [div_le_one hr0]; exact hρr
      have : 0 ≤ P.L0 * W ^ 2 * ρ := by positivity
      calc K * (P.L0 * W ^ 2 * ρ * (ρ / r)) ≤ K * (P.L0 * W ^ 2 * ρ * 1) := by gcongr
        _ = K * ρ * P.L0 * W ^ 2 := by ring
    · obtain ⟨c', hc', hce, hcn⟩ := AtomGradOffInternal.sqrt_factor hw
      refine ⟨_, hc'.mul hG, ?_, fun _ => ?_, ?_⟩
      · rw [norm_mul, pow_one, hce, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        have hρr' : ρ / r ≤ 1 := by rw [div_le_one hr0]; exact hρr
        calc ρ / r * ‖S.eval (decide (1 = 0)) t0 x0‖ ≤ 1 * (K * (r * W * (P.L0 * W))) := by
              gcongr
          _ = _ := one_mul _
      · rw [norm_mul, pow_one, hce, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        calc ρ / r * ‖S.eval (decide (1 = 0)) t0 x0‖ ≤ ρ / r * (K * (r * W * (P.L0 * W))) := by gcongr
          _ = K * ρ * P.L0 * W ^ 2 := by field_simp
      · refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, pow_one, hce, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        have hρr' : ρ / r ≤ 1 := by rw [div_le_one hr0]; exact hρr
        calc ρ / r * ‖F'.comp (T'.prod X')‖ + ‖S.eval (decide (1 = 0)) (chartT P y) (heightRatio y)‖ * ‖c'‖
            ≤ 1 * (3 * K * P.L0 * W ^ 2) + K * (r * W * (P.L0 * W)) * (2 / r) := by
              gcongr
          _ = 5 * K * P.L0 * W ^ 2 := by field_simp; ring
  obtain ⟨cG', hcG', hm1, hm2, hd1⟩ := hcG
  obtain ⟨E', hE', hEn⟩ := AtomGradOffInternal.angle_factor M hw
  obtain ⟨A', hA', hAm, hAn⟩ := hCA y hy0
  have hEy : ‖Complex.exp (Complex.I * (((M : ℝ) * angleOf y : ℝ) : ℂ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  have hB := hE'.mul hcG'
  have hU := hA'.mul hB
  have hfun : (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) =
      fun z => (((decayFactor P z : ℝ) : ℂ) * Complex.exp (Complex.I * (((j : ℝ) * β * logPhase P z : ℝ) : ℂ))) *
        (Complex.exp (Complex.I * (((M : ℝ) * angleOf z : ℝ) : ℂ)) *
          (((Real.sqrt (qOf z) ^ a : ℝ) : ℂ) * S.eval (decide (a = 0)) (chartT P z) (heightRatio z))) := by
    funext z
    unfold atomTerm
    rw [show ((((j : ℝ) * β * logPhase P z + (M : ℝ) * angleOf z : ℝ)) : ℂ) =
        (((j : ℝ) * β * logPhase P z : ℝ) : ℂ) + (((M : ℝ) * angleOf z : ℝ) : ℂ) by push_cast; ring,
      mul_add, Complex.exp_add]
    ring
  rw [hfun]
  refine ⟨hU.differentiableAt, ?_⟩
  have hUf : fderiv ℝ (fun z => (((decayFactor P z : ℝ) : ℂ) * Complex.exp (Complex.I * (((j : ℝ) * β * logPhase P z : ℝ) : ℂ))) *
        (Complex.exp (Complex.I * (((M : ℝ) * angleOf z : ℝ) : ℂ)) *
          (((Real.sqrt (qOf z) ^ a : ℝ) : ℂ) * S.eval (decide (a = 0)) (chartT P z) (heightRatio z)))) y = _ :=
    hU.fderiv
  rw [hUf]
  have hBm : ‖Complex.exp (Complex.I * (((M : ℝ) * angleOf y : ℝ) : ℂ)) *
      (((Real.sqrt (qOf y) ^ a : ℝ) : ℂ) * S.eval (decide (a = 0)) (chartT P y) (heightRatio y))‖ ≤
      K * (r * W * (P.L0 * W)) := by
    rw [norm_mul, hEy, one_mul]; exact hm1
  have hBd : ‖Complex.exp (Complex.I * (((M : ℝ) * angleOf y : ℝ) : ℂ)) • cG' +
      (((Real.sqrt (qOf y) ^ a : ℝ) : ℂ) * S.eval (decide (a = 0)) (chartT P y) (heightRatio y)) • E'‖ ≤
      (2 * |(M : ℝ)| + 5) * K * P.L0 * W ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, hEy, one_mul]
    have h2 : ‖((Real.sqrt (qOf y) ^ a : ℝ) : ℂ) * S.eval (decide (a = 0)) (chartT P y) (heightRatio y)‖ * ‖E'‖ ≤
        2 * |(M : ℝ)| * K * P.L0 * W ^ 2 := by
      by_cases hM0 : M = 0
      · have : ‖E'‖ ≤ 0 := by simpa [hM0] using hEn
        have : ‖E'‖ = 0 := le_antisymm this (norm_nonneg _)
        rw [this, mul_zero]; positivity
      · calc _ ≤ (K * ρ * P.L0 * W ^ 2) * (2 * |(M : ℝ)| / ρ) := by
              gcongr
              · exact hm2 hM0
          _ = 2 * |(M : ℝ)| * K * P.L0 * W ^ 2 := by field_simp
    linarith
  have hfin : ‖(((decayFactor P y : ℝ) : ℂ) * Complex.exp (Complex.I * (((j : ℝ) * β * logPhase P y : ℝ) : ℂ))) •
      (Complex.exp (Complex.I * (((M : ℝ) * angleOf y : ℝ) : ℂ)) • cG' +
        (((Real.sqrt (qOf y) ^ a : ℝ) : ℂ) * S.eval (decide (a = 0)) (chartT P y) (heightRatio y)) • E') +
      (Complex.exp (Complex.I * (((M : ℝ) * angleOf y : ℝ) : ℂ)) *
        (((Real.sqrt (qOf y) ^ a : ℝ) : ℂ) * S.eval (decide (a = 0)) (chartT P y) (heightRatio y))) • A'‖ ≤
      C0 * W ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul]
    have hA2 : ‖A'‖ ≤ CA * W := by rw [hW, mul_one_div]; exact hAn
    calc _ ≤ 1 * ((2 * |(M : ℝ)| + 5) * K * P.L0 * W ^ 2) + K * (r * W * (P.L0 * W)) * (CA * W) := by
          gcongr
      _ = (2 * |(M : ℝ)| + 5) * K * P.L0 * W ^ 2 + (r * W) * (CA * K * P.L0 * W ^ 2) := by ring
      _ ≤ (2 * |(M : ℝ)| + 5) * K * P.L0 * W ^ 2 + 1 * (CA * K * P.L0 * W ^ 2) := by gcongr
      _ = C0 * W ^ 2 := by rw [hC0]; ring
  refine hfin.trans ?_
  have hkey : 1 + r ≤ (1 + 1 / P.L0) * (r + P.L0) := by
    have h1 : 0 ≤ r / P.L0 := by positivity
    have e : (1 + 1 / P.L0) * (r + P.L0) = r + P.L0 + r / P.L0 + 1 := by field_simp; ring
    linarith
  have hW2 : W ≤ (1 + 1 / P.L0) / (1 + r) := by
    rw [hW, div_le_div_iff₀ (by positivity) (by positivity), one_mul]; exact hkey
  have hW3 : W ^ 2 ≤ ((1 + 1 / P.L0) / (1 + r)) ^ 2 := pow_le_pow_left₀ hW0.le hW2 2
  have e : ((1 + 1 / P.L0) / (1 + r)) ^ 2 = (1 + 1 / P.L0) ^ 2 * (1 + r) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two, div_pow, div_eq_mul_inv]
  calc C0 * W ^ 2 ≤ C0 * ((1 + 1 / P.L0) ^ 2 * (1 + r) ^ (-(2 : ℝ))) := by rw [← e]; gcongr
    _ = C0 * (1 + 1 / P.L0) ^ 2 * (1 + ‖y‖) ^ (-(2 : ℝ)) := by ring

end GivenFields

end CellCert

end Breakdown
