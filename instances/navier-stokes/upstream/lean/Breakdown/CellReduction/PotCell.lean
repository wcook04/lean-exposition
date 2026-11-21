import Breakdown.CellReduction.PotentialShape
import Breakdown.CertCell.ShapeSplineSmooth
import Breakdown.CertCell.ShapeSplineSlope
import Breakdown.CertCell.ShapeJetJoin
import Breakdown.CertCell.ShapeActuator
import Breakdown.FracCell.GivenAuxDualPartsRest

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace PotentialShape

namespace CellField

namespace Internal

open CertCell CertCell.GivenShape CertCell.GivenShape.Internal CertCell.GivenShape.Internal.JoinedSpline
open CellCert.GivenFields (cellIndex cellCount atFirst atSecond tDeriv xDeriv)

theorem jet_atFirst_join (H : JetSpline) (hs : H.tAxis.breaks.Pairwise (· < ·)) (hd : 1 ≤ H.tAxis.depth)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i < cellCount H.tAxis.breaks) (j : ℕ) :
    atFirst ((H.tAxis.breaks.getD i 0 : ℝ) : ℂ) (H.toSpline.piece (i - 1) j) =
      atFirst ((H.tAxis.breaks.getD i 0 : ℝ) : ℂ) (H.toSpline.piece i j) := by
  rw [toSpline_piece, toSpline_piece, atFirst_sum, atFirst_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [atFirst_sum, atFirst_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [atFirst_term, atFirst_term]
  have h := dofPoly_jets_agree (fun n p o _ _ hab ho => iterate_derivative_nodalLeft_eval_left n p o hab ho)
    (fun n p o _ _ hab ho => iterate_derivative_nodalLeft_eval_right n p o hab ho)
    (fun n p o _ _ hab ho => iterate_derivative_nodalRight_eval_right n p o hab ho)
    (fun n p o _ _ hab ho => iterate_derivative_nodalRight_eval_left n p o hab ho)
    (fun n s o a b ho => iterate_derivative_bubblePoly_eval_left n s o a b ho)
    (fun n s o a b ho => iterate_derivative_bubblePoly_eval_right n s o a b ho)
    H.tAxis hs i hi1 hi 0 hd d
  simp only [Function.iterate_zero, id] at h
  rw [h]

theorem jet_atSecond_join (H : JetSpline) (hs : H.xAxis.breaks.Pairwise (· < ·)) (hd : 1 ≤ H.xAxis.depth)
    (j : ℕ) (hj1 : 1 ≤ j) (hj : j < cellCount H.xAxis.breaks) (i : ℕ) :
    atSecond ((H.xAxis.breaks.getD j 0 : ℝ) : ℂ) (H.toSpline.piece i (j - 1)) =
      atSecond ((H.xAxis.breaks.getD j 0 : ℝ) : ℂ) (H.toSpline.piece i j) := by
  rw [toSpline_piece, toSpline_piece, atSecond_sum, atSecond_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [atSecond_sum, atSecond_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [atSecond_term, atSecond_term]
  have h := dofPoly_jets_agree (fun n p o _ _ hab ho => iterate_derivative_nodalLeft_eval_left n p o hab ho)
    (fun n p o _ _ hab ho => iterate_derivative_nodalLeft_eval_right n p o hab ho)
    (fun n p o _ _ hab ho => iterate_derivative_nodalRight_eval_right n p o hab ho)
    (fun n p o _ _ hab ho => iterate_derivative_nodalRight_eval_left n p o hab ho)
    (fun n s o a b ho => iterate_derivative_bubblePoly_eval_left n s o a b ho)
    (fun n s o a b ho => iterate_derivative_bubblePoly_eval_right n s o a b ho)
    H.xAxis hs j hj1 hj 0 hd e
  simp only [Function.iterate_zero, id] at h
  rw [h]

theorem jet_joins (H : JetSpline) {a b c d : ℝ} (hab : a < b) (hcd : c < d) (ht : IsJetAxis H.tAxis a b)
    (hx : IsJetAxis H.xAxis c d) :
    Joins ((H.tAxis.breaks.drop 1).dropLast) ((H.xAxis.breaks.drop 1).dropLast) 0 0 H.toSpline.piece := by
  obtain ⟨-, ct, gt⟩ := inner_facts _ hab ht.sorted ht.first ht.last
  obtain ⟨-, cx, gx⟩ := inner_facts _ hcd hx.sorted hx.first hx.last
  refine ⟨fun k hk j _ o ho x => ?_, fun k hk i _ o ho t => ?_⟩
  · obtain rfl : o = 0 := Nat.le_zero.mp ho
    rw [gt k hk]
    have h := jet_atFirst_join H ht.sorted ht.depth_pos (k + 1) (by omega) (by omega) j
    rw [Nat.add_sub_cancel] at h
    exact join_t h x
  · obtain rfl : o = 0 := Nat.le_zero.mp ho
    rw [gx k hk]
    have h := jet_atSecond_join H hx.sorted hx.depth_pos (k + 1) (by omega) (by omega) i
    rw [Nat.add_sub_cancel] at h
    exact join_x h t

theorem amp_continuous (H : JetSpline) {a b c d : ℝ} (hab : a < b) (hcd : c < d) (ht : IsJetAxis H.tAxis a b)
    (hx : IsJetAxis H.xAxis c d) : Continuous (fun z : ℝ × ℝ => H.toSpline.evalHalf z.1 z.2) := by
  have st := (inner_facts _ hab ht.sorted ht.first ht.last).1
  have sx := (inner_facts _ hcd hx.sorted hx.first hx.last).1
  have e : (fun z : ℝ × ℝ => H.toSpline.evalHalf z.1 z.2) =
      spl ((H.tAxis.breaks.drop 1).dropLast) ((H.xAxis.breaks.drop 1).dropLast) H.toSpline.piece := by
    funext z
    rfl
  rw [e]
  exact spl_continuous st sx (jet_joins H hab hcd ht hx)

theorem amp_box (H : JetSpline) (hc : Continuous (fun z : ℝ × ℝ => H.toSpline.evalHalf z.1 z.2)) (R : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ z w : ℝ × ℝ, |z.1| ≤ R → |z.2| ≤ R → |w.1| ≤ R → |w.2| ≤ R →
      ‖H.toSpline.evalHalf z.1 z.2 - H.toSpline.evalHalf w.1 w.2‖ ≤ M * (|z.1 - w.1| + |z.2 - w.2|) :=
  pieceEval_box H.toSpline.mesh.tBreaks H.toSpline.mesh.xBreaks H.toSpline.piece hc R

theorem amp_bounded (H : JetSpline) (R : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ t x : ℝ, |t| ≤ R → |x| ≤ R → ‖H.toSpline.evalHalf t x‖ ≤ M :=
  pieceEval_bounded H.toSpline.mesh.tBreaks H.toSpline.mesh.xBreaks H.toSpline.piece R

theorem le_cellIndex_of_getElem {l : List ℝ} (hs : l.Pairwise (· < ·)) {k : ℕ} (hk : k + 1 < l.length) {u : ℝ}
    (hu : l[k] ≤ u) : k ≤ cellIndex l u := by
  unfold cellIndex
  have hsub : ((l.drop 1).take k).Sublist (l.drop 1).dropLast := by
    rw [List.dropLast_eq_take]
    apply List.take_sublist_take_left
    simp only [List.length_drop]
    omega
  have hall : ∀ b ∈ (l.drop 1).take k, decide (b ≤ u) = true := by
    intro b hb
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
    simp only [List.length_take, List.length_drop] at hj
    simp only [List.getElem_take, List.getElem_drop, decide_eq_true_eq]
    refine le_trans ?_ hu
    rcases Nat.lt_or_ge (1 + j) k with h | h
    · exact (List.pairwise_iff_getElem.1 hs (1 + j) k (by omega) (by omega) h).le
    · have he : 1 + j = k := by omega
      simp only [he, le_refl]
  have hfil : ((l.drop 1).take k).filter (fun b => decide (b ≤ u)) = (l.drop 1).take k :=
    List.filter_eq_self.2 hall
  have hle := (hsub.filter (fun b => decide (b ≤ u))).length_le
  rw [hfil] at hle
  have hlen : ((l.drop 1).take k).length = k := by
    simp only [List.length_take, List.length_drop]
    omega
  omega

theorem cellIndex_succ_lt (l : List ℝ) (hl : 2 ≤ l.length) (u : ℝ) : cellIndex l u + 1 < l.length := by
  have h := List.length_filter_le (fun b => decide (b ≤ u)) ((l.drop 1).dropLast)
  simp only [List.length_dropLast, List.length_drop] at h
  unfold cellIndex
  omega

theorem cellIndex_lt_of_lt {l : List ℝ} (hs : l.Pairwise (· < ·)) {k : ℕ} (hk : k < l.length) (hk1 : 1 ≤ k)
    {u : ℝ} (hu : u < l[k]) : cellIndex l u + 1 ≤ k := by
  unfold cellIndex
  have h1 := ((List.dropLast_sublist (l.drop 1)).filter (fun b => decide (b ≤ u))).length_le
  have h2 : (l.drop 1).filter (fun b => decide (b ≤ u)) =
      ((l.drop 1).take (k - 1)).filter (fun b => decide (b ≤ u)) := by
    have hnil : ((l.drop 1).drop (k - 1)).filter (fun b => decide (b ≤ u)) = [] := by
      refine List.filter_eq_nil_iff.2 fun b hb => ?_
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
      simp only [List.length_drop] at hj
      simp only [List.getElem_drop, decide_eq_true_eq, not_le]
      refine lt_of_lt_of_le hu ?_
      rcases Nat.lt_or_ge k (1 + (k - 1 + j)) with h | h
      · exact (List.pairwise_iff_getElem.1 hs k _ hk (by omega) h).le
      · have he : k = 1 + (k - 1 + j) := by omega
        simp only [← he, le_refl]
    conv_lhs => rw [← List.take_append_drop (k - 1) (l.drop 1)]
    rw [List.filter_append, hnil, List.append_nil]
  have h3 := List.length_filter_le (fun b => decide (b ≤ u)) ((l.drop 1).take (k - 1))
  have h4 : ((l.drop 1).take (k - 1)).length ≤ k - 1 := by
    simp only [List.length_take]
    omega
  rw [h2] at h1
  omega

theorem beyond_of_ge {l : List ℝ} (hs : l.Pairwise (· < ·)) {R hi : ℝ} (hl : l.getLast? = some hi) (hR : R < hi)
    (hmem : R ∈ l) {u : ℝ} (hu : R ≤ u) :
    R ≤ |l.getD (cellIndex l u) R| ∧ R ≤ |l.getD (cellIndex l u + 1) R| := by
  obtain ⟨s, hs1, hsR⟩ := List.getElem_of_mem hmem
  have hs2 : s + 1 < l.length := by
    by_contra hc
    have he : l.length - 1 = s := by omega
    rw [List.getLast?_eq_getElem?, he, List.getElem?_eq_getElem hs1] at hl
    have h := Option.some.inj hl
    linarith
  have hi1 := le_cellIndex_of_getElem hs hs2 (hsR ▸ hu)
  have hi2 := cellIndex_succ_lt l (by omega) u
  have mono : ∀ j (hj : j < l.length), s ≤ j → l[s] ≤ l[j] := fun j hj hsj => by
    rcases Nat.lt_or_ge s j with h | h
    · exact (List.pairwise_iff_getElem.1 hs s j hs1 hj h).le
    · have he : s = j := by omega
      simp only [he, le_refl]
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi2]
  have h1 := mono _ (by omega) hi1
  have h2 := mono _ hi2 (by omega)
  rw [hsR] at h1 h2
  exact ⟨h1.trans (le_abs_self _), h2.trans (le_abs_self _)⟩

theorem beyond_of_lt {l : List ℝ} (hs : l.Pairwise (· < ·)) {R lo : ℝ} (hl : l.head? = some lo) (hR : lo < -R)
    (hmem : -R ∈ l) {u : ℝ} (hu : u < -R) :
    R ≤ |l.getD (cellIndex l u) R| ∧ R ≤ |l.getD (cellIndex l u + 1) R| := by
  obtain ⟨a, ha, haR⟩ := List.getElem_of_mem hmem
  have ha1 : 1 ≤ a := by
    by_contra hc
    have he : a = 0 := by omega
    subst he
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem ha] at hl
    have h := Option.some.inj hl
    linarith
  have hi := cellIndex_lt_of_lt hs ha ha1 (haR ▸ hu)
  have mono : ∀ j (hj : j < l.length), j ≤ a → l[j] ≤ l[a] := fun j hj hja => by
    rcases Nat.lt_or_ge j a with h | h
    · exact (List.pairwise_iff_getElem.1 hs j a hj ha h).le
    · have he : j = a := by omega
      simp only [he, le_refl]
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  have h1 := mono (cellIndex l u) (by omega) (by omega)
  have h2 := mono (cellIndex l u + 1) (by omega) hi
  rw [haR] at h1 h2
  exact ⟨by linarith [neg_abs_le (l[cellIndex l u]'(by omega))],
    by linarith [neg_abs_le (l[cellIndex l u + 1]'(by omega))]⟩

theorem coef_or_tPoly (H : JetSpline) {R : ℝ} (hv : VanishesBeyond H R) {i : ℕ}
    (hc : R ≤ |H.tAxis.breaks.getD i R| ∧ R ≤ |H.tAxis.breaks.getD (i + 1) R|) (d e : JetDof) :
    H.coef d e = 0 ∨ H.tAxis.dofPoly i d = 0 := by
  cases d with
  | node k p =>
    by_cases hk : k = i
    · subst hk
      exact Or.inl (hv.1 k p e hc.1)
    · by_cases hk' : k = i + 1
      · subst hk'
        exact Or.inl (hv.1 _ p e hc.2)
      · right
        simp [JetAxis.dofPoly, hk, hk']
  | bubble i' s =>
    by_cases h : i' = i
    · subst h
      exact Or.inl (hv.2.1 i' s e hc.1 hc.2)
    · right
      simp [JetAxis.dofPoly, h]

theorem coef_or_xPoly (H : JetSpline) {R : ℝ} (hv : VanishesBeyond H R) {j : ℕ}
    (hc : R ≤ |H.xAxis.breaks.getD j R| ∧ R ≤ |H.xAxis.breaks.getD (j + 1) R|) (d e : JetDof) :
    H.coef d e = 0 ∨ H.xAxis.dofPoly j e = 0 := by
  cases e with
  | node k p =>
    by_cases hk : k = j
    · subst hk
      exact Or.inl (hv.2.2.1 d k p hc.1)
    · by_cases hk' : k = j + 1
      · subst hk'
        exact Or.inl (hv.2.2.1 d _ p hc.2)
      · right
        simp [JetAxis.dofPoly, hk, hk']
  | bubble i' s =>
    by_cases h : i' = j
    · subst h
      exact Or.inl (hv.2.2.2 d i' s hc.1 hc.2)
    · right
      simp [JetAxis.dofPoly, h]

theorem piece_zero (H : JetSpline) (i j : ℕ)
    (h : ∀ d e, H.coef d e = 0 ∨ H.tAxis.dofPoly i d = 0 ∨ H.xAxis.dofPoly j e = 0) :
    H.toSpline.piece i j = 0 := by
  rw [toSpline_piece]
  refine Finset.sum_eq_zero fun d _ => Finset.sum_eq_zero fun e _ => ?_
  rcases h d e with h | h | h <;> simp [h, embedFirst, embedSecond]

theorem amp_zero (H : JetSpline) {Rm Rs : ℝ} (hRs : 0 < Rs ∧ Rs < Rm) (ht : IsJetAxis H.tAxis 0 Rm)
    (hx : IsJetAxis H.xAxis (-Rm) Rm) (hb : Rs ∈ H.tAxis.breaks ∧ Rs ∈ H.xAxis.breaks ∧ -Rs ∈ H.xAxis.breaks)
    (hv : VanishesBeyond H Rs) {t x : ℝ} (h : Rs < t ∨ Rs < |x|) : H.toSpline.evalHalf t x = 0 := by
  have hz : H.toSpline.piece (cellIndex H.tAxis.breaks t) (cellIndex H.xAxis.breaks x) = 0 := by
    apply piece_zero
    intro d e
    rcases h with h | h
    · rcases coef_or_tPoly H hv (beyond_of_ge ht.sorted ht.last hRs.2 hb.1 h.le) d e with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · have hc : Rs ≤ |H.xAxis.breaks.getD (cellIndex H.xAxis.breaks x) Rs| ∧
          Rs ≤ |H.xAxis.breaks.getD (cellIndex H.xAxis.breaks x + 1) Rs| := by
        rcases le_or_gt 0 x with hx0 | hx0
        · rw [abs_of_nonneg hx0] at h
          exact beyond_of_ge hx.sorted hx.last hRs.2 hb.2.1 h.le
        · rw [abs_of_neg hx0] at h
          exact beyond_of_lt hx.sorted hx.first (by linarith) hb.2.2 (by linarith)
      rcases coef_or_xPoly H hv hc d e with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
  show MvPolynomial.eval _ (H.toSpline.piece (cellIndex H.tAxis.breaks t) (cellIndex H.xAxis.breaks x)) = 0
  rw [hz, map_zero]


def planeOf (y : Space) : ℂ := (y 0 : ℂ) + (y 1 : ℂ) * Complex.I

def turnScaled (k : ℤ) (w : ℂ) : ℂ := (‖w‖ : ℂ) * Complex.exp ((((k : ℝ) * w.arg : ℝ) : ℂ) * Complex.I)

def unitOf (w : ℂ) : ℂ := Complex.exp ((w.arg : ℂ) * Complex.I)

theorem unitOf_norm (w : ℂ) : ‖unitOf w‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem norm_mul_unitOf (w : ℂ) : (‖w‖ : ℂ) * unitOf w = w := Complex.norm_mul_exp_arg_mul_I w

theorem turnScaled_eq (k : ℤ) (w : ℂ) : turnScaled k w = (‖w‖ : ℂ) * unitOf w ^ k := by
  unfold turnScaled unitOf
  rw [← Complex.exp_int_mul]
  congr 2
  push_cast
  ring

theorem unit_pow_sub {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) : ∀ n : ℕ, ‖u ^ n - v ^ n‖ ≤ n * ‖u - v‖
  | 0 => by simp
  | n + 1 => by
    have h := unit_pow_sub hu hv n
    have e : u ^ (n + 1) - v ^ (n + 1) = u * (u ^ n - v ^ n) + (u - v) * v ^ n := by ring
    rw [e]
    calc ‖u * (u ^ n - v ^ n) + (u - v) * v ^ n‖ ≤ ‖u * (u ^ n - v ^ n)‖ + ‖(u - v) * v ^ n‖ :=
          norm_add_le _ _
      _ = ‖u ^ n - v ^ n‖ + ‖u - v‖ := by
          rw [norm_mul, norm_mul, norm_pow, hu, hv, one_pow, one_mul, mul_one]
      _ ≤ n * ‖u - v‖ + ‖u - v‖ := by linarith
      _ = ((n + 1 : ℕ) : ℝ) * ‖u - v‖ := by push_cast; ring

theorem unit_zpow_sub {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (k : ℤ) :
    ‖u ^ k - v ^ k‖ ≤ (k.natAbs : ℝ) * ‖u - v‖ := by
  rcases k with n | n
  · simpa using unit_pow_sub hu hv n
  · have hu' : u ^ (n + 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [hu]; exact one_ne_zero))
    have hv' : v ^ (n + 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [hv]; exact one_ne_zero))
    rw [zpow_negSucc, zpow_negSucc, inv_sub_inv hu' hv', norm_div, norm_mul, norm_pow, norm_pow, hu, hv,
      one_pow, one_mul, div_one, norm_sub_rev]
    simpa [Int.natAbs_negSucc] using unit_pow_sub hu hv (n + 1)

theorem scaled_unit_gap (w w' : ℂ) : ‖w'‖ * ‖unitOf w - unitOf w'‖ ≤ 2 * ‖w - w'‖ := by
  have e : (‖w'‖ : ℂ) * (unitOf w - unitOf w') = ((‖w'‖ - ‖w‖ : ℝ) : ℂ) * unitOf w + (w - w') := by
    have h1 := norm_mul_unitOf w
    have h2 := norm_mul_unitOf w'
    push_cast
    linear_combination h1 - h2
  have h3 : ‖(‖w'‖ : ℂ) * (unitOf w - unitOf w')‖ = ‖w'‖ * ‖unitOf w - unitOf w'‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  rw [← h3, e]
  calc ‖((‖w'‖ - ‖w‖ : ℝ) : ℂ) * unitOf w + (w - w')‖
      ≤ ‖((‖w'‖ - ‖w‖ : ℝ) : ℂ) * unitOf w‖ + ‖w - w'‖ := norm_add_le _ _
    _ = |‖w'‖ - ‖w‖| + ‖w - w'‖ := by rw [norm_mul, unitOf_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖w' - w‖ + ‖w - w'‖ := by linarith [abs_norm_sub_norm_le w' w]
    _ = 2 * ‖w - w'‖ := by rw [norm_sub_rev]; ring

theorem turnScaled_slope (k : ℤ) (w w' : ℂ) :
    ‖turnScaled k w - turnScaled k w'‖ ≤ (1 + 2 * (k.natAbs : ℝ)) * ‖w - w'‖ := by
  rw [turnScaled_eq, turnScaled_eq]
  have e : (‖w‖ : ℂ) * unitOf w ^ k - (‖w'‖ : ℂ) * unitOf w' ^ k =
      ((‖w‖ - ‖w'‖ : ℝ) : ℂ) * unitOf w ^ k + (‖w'‖ : ℂ) * (unitOf w ^ k - unitOf w' ^ k) := by
    push_cast
    ring
  rw [e]
  have hp := unit_zpow_sub (unitOf_norm w) (unitOf_norm w') k
  have hg := scaled_unit_gap w w'
  have hn : ‖unitOf w ^ k‖ = 1 := by rw [norm_zpow, unitOf_norm, one_zpow]
  have hk : (0 : ℝ) ≤ k.natAbs := Nat.cast_nonneg _
  calc ‖((‖w‖ - ‖w'‖ : ℝ) : ℂ) * unitOf w ^ k + (‖w'‖ : ℂ) * (unitOf w ^ k - unitOf w' ^ k)‖
      ≤ ‖((‖w‖ - ‖w'‖ : ℝ) : ℂ) * unitOf w ^ k‖ + ‖(‖w'‖ : ℂ) * (unitOf w ^ k - unitOf w' ^ k)‖ :=
        norm_add_le _ _
    _ = |‖w‖ - ‖w'‖| + ‖w'‖ * ‖unitOf w ^ k - unitOf w' ^ k‖ := by
        rw [norm_mul, norm_mul, hn, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_norm]
    _ ≤ ‖w - w'‖ + ‖w'‖ * ((k.natAbs : ℝ) * ‖unitOf w - unitOf w'‖) :=
        add_le_add (abs_norm_sub_norm_le w w') (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
    _ = ‖w - w'‖ + (k.natAbs : ℝ) * (‖w'‖ * ‖unitOf w - unitOf w'‖) := by ring
    _ ≤ ‖w - w'‖ + (k.natAbs : ℝ) * (2 * ‖w - w'‖) := by gcongr
    _ = (1 + 2 * (k.natAbs : ℝ)) * ‖w - w'‖ := by ring

theorem turnScaled_norm (k : ℤ) (w : ℂ) : ‖turnScaled k w‖ = ‖w‖ := by
  rw [turnScaled_eq, norm_mul, norm_zpow, unitOf_norm, one_zpow, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_norm]

theorem turnScaled_shift (M s : ℤ) (w : ℂ) :
    turnScaled (M + s) w = turnScaled M w * Complex.exp ((((s : ℝ) * w.arg : ℝ) : ℂ) * Complex.I) := by
  unfold turnScaled
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem turn_cos (M : ℤ) (w : ℂ) :
    turnScaled M w * Complex.cos (w.arg : ℂ) = (turnScaled (M + 1) w + turnScaled (M - 1) w) / 2 := by
  have h1 := turnScaled_shift M 1 w
  have h2 := turnScaled_shift M (-1) w
  rw [← sub_eq_add_neg] at h2
  have e1 : ((((1 : ℤ) : ℝ) * w.arg : ℝ) : ℂ) = (w.arg : ℂ) := by push_cast; ring
  have e2 : ((((-1 : ℤ) : ℝ) * w.arg : ℝ) : ℂ) = -(w.arg : ℂ) := by push_cast; ring
  rw [h1, h2, e1, e2, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  ring

theorem turn_sin (M : ℤ) (w : ℂ) :
    turnScaled M w * Complex.sin (w.arg : ℂ) = (turnScaled (M - 1) w - turnScaled (M + 1) w) * Complex.I / 2 := by
  have h1 := turnScaled_shift M 1 w
  have h2 := turnScaled_shift M (-1) w
  rw [← sub_eq_add_neg] at h2
  have e1 : ((((1 : ℤ) : ℝ) * w.arg : ℝ) : ℂ) = (w.arg : ℂ) := by push_cast; ring
  have e2 : ((((-1 : ℤ) : ℝ) * w.arg : ℝ) : ℂ) = -(w.arg : ℂ) := by push_cast; ring
  rw [h1, h2, e1, e2, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  linear_combination (turnScaled M w * Complex.sin (w.arg : ℂ)) * Complex.I_sq

def frameScaled (M : ℤ) (a : Fin 3) (w : ℂ) : Fin 3 → ℂ :=
  fun k => turnScaled M w * ((frameUnit w.arg a k : ℝ) : ℂ)

def upperWeight : Fin 3 → Fin 3 → ℂ :=
  ![![1 / 2, -Complex.I / 2, 0], ![Complex.I / 2, 1 / 2, 0], ![0, 0, 0]]

def lowerWeight : Fin 3 → Fin 3 → ℂ :=
  ![![1 / 2, Complex.I / 2, 0], ![-Complex.I / 2, 1 / 2, 0], ![0, 0, 0]]

def axialWeight : Fin 3 → Fin 3 → ℂ :=
  ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]]

theorem frameScaled_comb (M : ℤ) (a k : Fin 3) (w : ℂ) :
    frameScaled M a w k = upperWeight a k * turnScaled (M + 1) w + lowerWeight a k * turnScaled (M - 1) w +
      axialWeight a k * turnScaled M w := by
  have hc := turn_cos M w
  have hs := turn_sin M w
  fin_cases a <;> fin_cases k <;>
    simp [frameScaled, frameUnit, CellCert.CellAnalysis.radialUnit, CellCert.CellAnalysis.angularUnit,
      CellCert.CellAnalysis.axialUnit, upperWeight, lowerWeight, axialWeight] <;>
    first
    | linear_combination hc
    | linear_combination hs
    | linear_combination -hs

theorem weight_norm_le (a k : Fin 3) :
    ‖upperWeight a k‖ ≤ 1 ∧ ‖lowerWeight a k‖ ≤ 1 ∧ ‖axialWeight a k‖ ≤ 1 := by
  fin_cases a <;> fin_cases k <;> norm_num [upperWeight, lowerWeight, axialWeight, norm_div, Complex.norm_I]

def frameConst (M : ℤ) : ℝ := 3 + 2 * (((M + 1).natAbs : ℝ) + ((M - 1).natAbs : ℝ) + (M.natAbs : ℝ))

theorem frameScaled_slope (M : ℤ) (a : Fin 3) (w w' : ℂ) :
    ‖frameScaled M a w - frameScaled M a w'‖ ≤ frameConst M * ‖w - w'‖ := by
  have h0 : 0 ≤ frameConst M * ‖w - w'‖ := by unfold frameConst; positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun k => ?_
  obtain ⟨hu, hl, hx⟩ := weight_norm_le a k
  have t1 := turnScaled_slope (M + 1) w w'
  have t2 := turnScaled_slope (M - 1) w w'
  have t3 := turnScaled_slope M w w'
  have e : frameScaled M a w k - frameScaled M a w' k =
      upperWeight a k * (turnScaled (M + 1) w - turnScaled (M + 1) w') +
        lowerWeight a k * (turnScaled (M - 1) w - turnScaled (M - 1) w') +
          axialWeight a k * (turnScaled M w - turnScaled M w') := by
    rw [frameScaled_comb, frameScaled_comb]
    ring
  rw [Pi.sub_apply, e]
  have n1 : ‖upperWeight a k * (turnScaled (M + 1) w - turnScaled (M + 1) w')‖ ≤
      (1 + 2 * ((M + 1).natAbs : ℝ)) * ‖w - w'‖ := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hu).trans t1
  have n2 : ‖lowerWeight a k * (turnScaled (M - 1) w - turnScaled (M - 1) w')‖ ≤
      (1 + 2 * ((M - 1).natAbs : ℝ)) * ‖w - w'‖ := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hl).trans t2
  have n3 : ‖axialWeight a k * (turnScaled M w - turnScaled M w')‖ ≤ (1 + 2 * (M.natAbs : ℝ)) * ‖w - w'‖ := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans t3
  calc _ ≤ ‖upperWeight a k * (turnScaled (M + 1) w - turnScaled (M + 1) w')‖ +
        ‖lowerWeight a k * (turnScaled (M - 1) w - turnScaled (M - 1) w')‖ +
          ‖axialWeight a k * (turnScaled M w - turnScaled M w')‖ := norm_add₃_le
    _ ≤ _ := by unfold frameConst; linarith

theorem frameScaled_norm (M : ℤ) (a : Fin 3) (w : ℂ) : ‖frameScaled M a w‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun k => ?_
  have hf : |frameUnit w.arg a k| ≤ 1 := by
    fin_cases a <;> fin_cases k <;>
      simp [frameUnit, CellCert.CellAnalysis.radialUnit, CellCert.CellAnalysis.angularUnit,
        CellCert.CellAnalysis.axialUnit, Real.abs_cos_le_one, Real.abs_sin_le_one]
  simp only [frameScaled]
  rw [norm_mul, turnScaled_norm, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (norm_nonneg _) hf

theorem planeOf_sub (y y' : Space) : planeOf y - planeOf y' = planeOf (y - y') := by
  simp only [planeOf, PiLp.sub_apply, Complex.ofReal_sub]
  ring

theorem planeOf_norm (y : Space) : ‖planeOf y‖ = Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, Complex.normSq_apply]
  simp [planeOf]
  ring_nf

theorem space_norm_sq (y : Space) : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

theorem planeOf_norm_le (y : Space) : ‖planeOf y‖ ≤ ‖y‖ := by
  rw [planeOf_norm, ← Real.sqrt_sq (norm_nonneg y), space_norm_sq]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (y 2)])

theorem coord_two_le (y : Space) : |y 2| ≤ ‖y‖ := by
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq (norm_nonneg y), space_norm_sq]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)])

theorem plane_fst (y : Space) : (pointPlane y).1 = ‖planeOf y‖ := by
  rw [planeOf_norm]
  rfl

theorem realPartVec_at (v : Fin 3 → ℂ) (k : Fin 3) : realPartVec v k = (v k).re := rfl

theorem phase_split (m : ℕ) (ι : ℤ × ℤ) (σ θ : ℝ) :
    labelPhase m ι σ θ =
      labelPhase m ι σ 0 * Complex.exp ((((labelAzimuth m ι : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
  unfold labelPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem cyl_term (m : ℕ) (ι : ℤ × ℤ) (a : Fin 3) (B : ℂ) (σ : ℝ) (y : Space) :
    (labelPhase m ι σ (pointAngle y) * (((pointPlane y).1 : ℝ) : ℂ) * B).re • frameUnit (pointAngle y) a =
      realPartVec ((labelPhase m ι σ 0 * B) • frameScaled (labelAzimuth m ι) a (planeOf y)) := by
  ext k
  rw [realPartVec_at]
  have hθ : pointAngle y = (planeOf y).arg := rfl
  have key : (labelPhase m ι σ 0 * B) * frameScaled (labelAzimuth m ι) a (planeOf y) k =
      (labelPhase m ι σ (pointAngle y) * (((pointPlane y).1 : ℝ) : ℂ) * B) *
        ((frameUnit (pointAngle y) a k : ℝ) : ℂ) := by
    rw [phase_split m ι σ (pointAngle y), plane_fst, hθ]
    simp only [frameScaled, turnScaled]
    ring
  simp only [PiLp.smul_apply, smul_eq_mul, Pi.smul_apply]
  rw [key, Complex.re_mul_ofReal]

def ampAt (H : JetSpline) (y : Space) : ℂ := H.toSpline.evalHalf (pointPlane y).1 (pointPlane y).2

def cellTerm (m : ℕ) (G : CylModeData) (ι : ℤ × ℤ) (a : Fin 3) (σ : ℝ) (y : Space) : Space :=
  realPartVec ((labelPhase m ι σ 0 * ampAt (G.amp ι a) y) • frameScaled (labelAzimuth m ι) a (planeOf y))

theorem cylField_eq (m : ℕ) (G : CylModeData) (σ : ℝ) (y : Space) :
    cylField m G σ y = ∑ ι ∈ G.labels, ∑ a : Fin 3, cellTerm m G ι a σ y := by
  unfold cylField
  refine Finset.sum_congr rfl fun ι _ => Finset.sum_congr rfl fun a _ => ?_
  exact cyl_term m ι a _ σ y

theorem plane_box {R : ℝ} {y : Space} (hy : ‖y‖ ≤ R) : |(pointPlane y).1| ≤ R ∧ |(pointPlane y).2| ≤ R := by
  refine ⟨?_, (coord_two_le y).trans hy⟩
  rw [plane_fst, abs_norm]
  exact (planeOf_norm_le y).trans hy

theorem plane_gap (y y' : Space) :
    |(pointPlane y).1 - (pointPlane y').1| ≤ ‖y - y'‖ ∧ |(pointPlane y).2 - (pointPlane y').2| ≤ ‖y - y'‖ := by
  refine ⟨?_, ?_⟩
  · rw [plane_fst, plane_fst]
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [planeOf_sub]
    exact planeOf_norm_le _
  · have h := coord_two_le (y - y')
    rw [PiLp.sub_apply] at h
    exact h

theorem ampAt_slope (H : JetSpline) (hc : Continuous (fun z : ℝ × ℝ => H.toSpline.evalHalf z.1 z.2)) (R : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ y y' : Space, ‖y‖ ≤ R → ‖y'‖ ≤ R → ‖ampAt H y - ampAt H y'‖ ≤ M * ‖y - y'‖ := by
  obtain ⟨M, hM, hb⟩ := amp_box H hc R
  refine ⟨2 * M, by positivity, fun y y' hy hy' => ?_⟩
  obtain ⟨p1, p2⟩ := plane_box hy
  obtain ⟨q1, q2⟩ := plane_box hy'
  obtain ⟨d1, d2⟩ := plane_gap y y'
  calc ‖ampAt H y - ampAt H y'‖
      ≤ M * (|(pointPlane y).1 - (pointPlane y').1| + |(pointPlane y).2 - (pointPlane y').2|) :=
        hb (pointPlane y) (pointPlane y') p1 p2 q1 q2
    _ ≤ M * (‖y - y'‖ + ‖y - y'‖) := mul_le_mul_of_nonneg_left (add_le_add d1 d2) hM
    _ = 2 * M * ‖y - y'‖ := by ring

theorem labelPhase_zero_norm (m : ℕ) (ι : ℤ × ℤ) (σ : ℝ) : ‖labelPhase m ι σ 0‖ = 1 := by
  unfold labelPhase
  exact Complex.norm_exp_ofReal_mul_I _

theorem cellTerm_slope (m : ℕ) (G : CylModeData) (ι : ℤ × ℤ) (a : Fin 3)
    (hc : Continuous (fun z : ℝ × ℝ => (G.amp ι a).toSpline.evalHalf z.1 z.2)) (R : ℝ) :
    ∃ L, 0 ≤ L ∧ ∀ σ, ∀ y y' : Space, ‖y‖ ≤ R → ‖y'‖ ≤ R →
      ‖cellTerm m G ι a σ y - cellTerm m G ι a σ y'‖ ≤ L * ‖y - y'‖ := by
  obtain ⟨Ms, hMs, hs⟩ := ampAt_slope (G.amp ι a) hc R
  obtain ⟨B, hB, hb⟩ := amp_bounded (G.amp ι a) R
  have hK : 0 ≤ frameConst (labelAzimuth m ι) := by unfold frameConst; positivity
  refine ⟨‖realPartVec‖ * (B * frameConst (labelAzimuth m ι) + Ms * |R|), by positivity,
    fun σ y y' hy hy' => ?_⟩
  obtain ⟨p1, p2⟩ := plane_box hy
  have hAy : ‖ampAt (G.amp ι a) y‖ ≤ B := hb _ _ p1 p2
  have hF : ‖frameScaled (labelAzimuth m ι) a (planeOf y) - frameScaled (labelAzimuth m ι) a (planeOf y')‖ ≤
      frameConst (labelAzimuth m ι) * ‖y - y'‖ := by
    refine (frameScaled_slope _ a _ _).trans ?_
    rw [planeOf_sub]
    exact mul_le_mul_of_nonneg_left (planeOf_norm_le _) hK
  have hF' : ‖frameScaled (labelAzimuth m ι) a (planeOf y')‖ ≤ |R| :=
    (frameScaled_norm _ _ _).trans ((planeOf_norm_le _).trans (hy'.trans (le_abs_self _)))
  have e : (labelPhase m ι σ 0 * ampAt (G.amp ι a) y) • frameScaled (labelAzimuth m ι) a (planeOf y) -
      (labelPhase m ι σ 0 * ampAt (G.amp ι a) y') • frameScaled (labelAzimuth m ι) a (planeOf y') =
      labelPhase m ι σ 0 • (ampAt (G.amp ι a) y • (frameScaled (labelAzimuth m ι) a (planeOf y) -
        frameScaled (labelAzimuth m ι) a (planeOf y')) + (ampAt (G.amp ι a) y - ampAt (G.amp ι a) y') •
          frameScaled (labelAzimuth m ι) a (planeOf y')) := by
    module
  unfold cellTerm
  rw [← map_sub, e]
  refine (realPartVec.le_opNorm _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [norm_smul, labelPhase_zero_norm, one_mul]
  calc _ ≤ ‖ampAt (G.amp ι a) y • (frameScaled (labelAzimuth m ι) a (planeOf y) -
          frameScaled (labelAzimuth m ι) a (planeOf y'))‖ + ‖(ampAt (G.amp ι a) y - ampAt (G.amp ι a) y') •
          frameScaled (labelAzimuth m ι) a (planeOf y')‖ := norm_add_le _ _
    _ = ‖ampAt (G.amp ι a) y‖ * ‖frameScaled (labelAzimuth m ι) a (planeOf y) -
          frameScaled (labelAzimuth m ι) a (planeOf y')‖ + ‖ampAt (G.amp ι a) y - ampAt (G.amp ι a) y'‖ *
          ‖frameScaled (labelAzimuth m ι) a (planeOf y')‖ := by rw [norm_smul, norm_smul]
    _ ≤ B * (frameConst (labelAzimuth m ι) * ‖y - y'‖) + (Ms * ‖y - y'‖) * |R| :=
        add_le_add (mul_le_mul hAy hF (norm_nonneg _) hB)
          (mul_le_mul (hs y y' hy hy') hF' (norm_nonneg _) (by positivity))
    _ = (B * frameConst (labelAzimuth m ι) + Ms * |R|) * ‖y - y'‖ := by ring

theorem sum_slope {α : Type*} (s : Finset α) (f : α → ℝ → Space → Space) (R : ℝ)
    (h : ∀ i ∈ s, ∃ L, 0 ≤ L ∧ ∀ σ, ∀ y y' : Space, ‖y‖ ≤ R → ‖y'‖ ≤ R → ‖f i σ y - f i σ y'‖ ≤ L * ‖y - y'‖) :
    ∃ L, 0 ≤ L ∧ ∀ σ, ∀ y y' : Space, ‖y‖ ≤ R → ‖y'‖ ≤ R →
      ‖∑ i ∈ s, f i σ y - ∑ i ∈ s, f i σ y'‖ ≤ L * ‖y - y'‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, fun σ y y' _ _ => by simp⟩
  | insert j s hj ih =>
    obtain ⟨L1, h1, hL1⟩ := h j (Finset.mem_insert_self j s)
    obtain ⟨L2, h2, hL2⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨L1 + L2, add_nonneg h1 h2, fun σ y y' hy hy' => ?_⟩
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    calc _ = ‖(f j σ y - f j σ y') + (∑ i ∈ s, f i σ y - ∑ i ∈ s, f i σ y')‖ := by
          congr 1
          abel
      _ ≤ ‖f j σ y - f j σ y'‖ + ‖∑ i ∈ s, f i σ y - ∑ i ∈ s, f i σ y'‖ := norm_add_le _ _
      _ ≤ L1 * ‖y - y'‖ + L2 * ‖y - y'‖ := add_le_add (hL1 σ y y' hy hy') (hL2 σ y y' hy hy')
      _ = (L1 + L2) * ‖y - y'‖ := by ring

theorem slope_of_ball {f : Space → Space} {L R : ℝ} (hL : 0 ≤ L)
    (hon : ∀ y y' : Space, ‖y‖ ≤ R → ‖y'‖ ≤ R → ‖f y - f y'‖ ≤ L * ‖y - y'‖)
    (hz : ∀ y : Space, R ≤ ‖y‖ → f y = 0) : ∀ y y' : Space, ‖f y - f y'‖ ≤ L * ‖y - y'‖ := by
  have half : ∀ y y' : Space, ‖y‖ ≤ R → R < ‖y'‖ → ‖f y - f y'‖ ≤ L * ‖y - y'‖ := by
    intro y y' hy hy'
    have hcont : ContinuousOn (fun t : ℝ => ‖y + t • (y' - y)‖) (Set.Icc 0 1) :=
      (continuous_const.add (continuous_id.smul continuous_const)).norm.continuousOn
    have hmem : R ∈ Set.Icc ‖y + (0 : ℝ) • (y' - y)‖ ‖y + (1 : ℝ) • (y' - y)‖ := by
      simp only [zero_smul, add_zero, one_smul, add_sub_cancel]
      exact ⟨hy, hy'.le⟩
    obtain ⟨t, ht, hpt⟩ := intermediate_value_Icc zero_le_one hcont hmem
    have hp0 : f (y + t • (y' - y)) = 0 := hz _ hpt.ge
    have hy'0 : f y' = 0 := hz y' hy'.le
    have hdist : ‖y - (y + t • (y' - y))‖ ≤ ‖y - y'‖ := by
      have e : y - (y + t • (y' - y)) = t • (y - y') := by module
      rw [e, norm_smul, Real.norm_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    calc ‖f y - f y'‖ = ‖f y - f (y + t • (y' - y))‖ := by rw [hp0, hy'0]
      _ ≤ L * ‖y - (y + t • (y' - y))‖ := hon y _ hy hpt.le
      _ ≤ L * ‖y - y'‖ := mul_le_mul_of_nonneg_left hdist hL
  intro y y'
  rcases le_or_gt ‖y‖ R with hy | hy <;> rcases le_or_gt ‖y'‖ R with hy' | hy'
  · exact hon y y' hy hy'
  · exact half y y' hy hy'
  · rw [norm_sub_rev, norm_sub_rev y]
    exact half y' y hy' hy
  · rw [hz y hy.le, hz y' hy'.le, sub_self, norm_zero]
    positivity

theorem ampAt_far (H : JetSpline) {Rm Rs : ℝ} (hRs : 0 < Rs ∧ Rs < Rm) (ht : IsJetAxis H.tAxis 0 Rm)
    (hx : IsJetAxis H.xAxis (-Rm) Rm) (hb : Rs ∈ H.tAxis.breaks ∧ Rs ∈ H.xAxis.breaks ∧ -Rs ∈ H.xAxis.breaks)
    (hv : VanishesBeyond H Rs) {y : Space} (hy : 2 * Rs ≤ ‖y‖) : ampAt H y = 0 := by
  apply amp_zero H hRs ht hx hb hv
  by_contra hcon
  simp only [not_or, not_lt] at hcon
  have h1 : (pointPlane y).1 ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
  have h2 := space_norm_sq y
  have hnn : 0 ≤ (pointPlane y).1 := Real.sqrt_nonneg _
  have h3 : (pointPlane y).2 ^ 2 ≤ Rs ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hcon.2 2
  have h4 : (pointPlane y).1 ^ 2 ≤ Rs ^ 2 := pow_le_pow_left₀ hnn hcon.1 2
  have h5 : (2 * Rs) ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (by linarith) hy 2
  have h6 : (pointPlane y).2 = y 2 := rfl
  rw [h6] at h3
  nlinarith [mul_pos hRs.1 hRs.1]

theorem cellTerm_continuous (m : ℕ) (G : CylModeData) (ι : ℤ × ℤ) (a : Fin 3)
    (hc : Continuous (fun z : ℝ × ℝ => (G.amp ι a).toSpline.evalHalf z.1 z.2)) :
    Continuous (fun z : ℝ × Space => cellTerm m G ι a z.1 z.2) := by
  have hph : Continuous fun σ : ℝ => labelPhase m ι σ 0 := by
    unfold labelPhase
    fun_prop
  have hpl : Continuous planeOf :=
    (LipschitzWith.of_dist_le' (K := 1) fun y y' => by
      rw [dist_eq_norm, dist_eq_norm, planeOf_sub, one_mul]
      exact planeOf_norm_le _).continuous
  have hfr : Continuous (frameScaled (labelAzimuth m ι) a) :=
    (LipschitzWith.of_dist_le' (K := frameConst (labelAzimuth m ι)) fun w w' => by
      rw [dist_eq_norm, dist_eq_norm]
      exact frameScaled_slope _ a w w').continuous
  have hpp : Continuous pointPlane :=
    (LipschitzWith.of_dist_le' (K := 2) fun y y' => by
      rw [dist_eq_norm, dist_eq_norm, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
      obtain ⟨d1, d2⟩ := plane_gap y y'
      simp only [Prod.fst_sub, Prod.snd_sub]
      have h0 := norm_nonneg (y - y')
      exact max_le (by linarith) (by linarith)).continuous
  have hamp : Continuous (ampAt (G.amp ι a)) := hc.comp hpp
  unfold cellTerm
  exact realPartVec.continuous.comp (((hph.comp continuous_fst).mul (hamp.comp continuous_snd)).smul
    ((hfr.comp hpl).comp continuous_snd))

end Internal

end CellField

open CellField.Internal in
theorem cellPotentialRegular_holds : CellPotentialRegular := by
  intro m G Rmesh Rsupp hG
  have hRm : 0 < Rmesh := hG.support_lt.1.trans hG.support_lt.2
  have hcont : ∀ ι ∈ G.labels, ∀ a, Continuous fun z : ℝ × ℝ => (G.amp ι a).toSpline.evalHalf z.1 z.2 :=
    fun ι hι a => amp_continuous _ hRm (by linarith) (hG.axes ι hι a).1 (hG.axes ι hι a).2
  have hzero : ∀ σ (y : Space), 2 * Rsupp ≤ ‖y‖ → cylField m G σ y = 0 := by
    intro σ y hy
    rw [cylField_eq]
    refine Finset.sum_eq_zero fun ι hι => Finset.sum_eq_zero fun a _ => ?_
    have h0 := ampAt_far (G.amp ι a) hG.support_lt (hG.axes ι hι a).1 (hG.axes ι hι a).2
      (hG.support_break ι hι a) (hG.vanish ι hι a) hy
    simp [cellTerm, h0]
  have hjoint : Continuous (fun z : ℝ × Space => cylField m G z.1 z.2) := by
    have e : (fun z : ℝ × Space => cylField m G z.1 z.2) =
        fun z => ∑ ι ∈ G.labels, ∑ a : Fin 3, cellTerm m G ι a z.1 z.2 := by
      funext z
      exact cylField_eq m G z.1 z.2
    rw [e]
    exact continuous_finsetSum _ fun ι hι => continuous_finsetSum _ fun a _ =>
      cellTerm_continuous m G ι a (hcont ι hι a)
  obtain ⟨L, hL, hslope⟩ : ∃ L, 0 ≤ L ∧ ∀ σ, ∀ y y' : Space, ‖y‖ ≤ 2 * Rsupp → ‖y'‖ ≤ 2 * Rsupp →
      ‖cylField m G σ y - cylField m G σ y'‖ ≤ L * ‖y - y'‖ := by
    obtain ⟨L, hL, h⟩ := sum_slope G.labels (fun ι σ y => ∑ a : Fin 3, cellTerm m G ι a σ y) (2 * Rsupp)
      (fun ι hι => sum_slope Finset.univ (fun a σ y => cellTerm m G ι a σ y) (2 * Rsupp)
        (fun a _ => cellTerm_slope m G ι a (hcont ι hι a) (2 * Rsupp)))
    refine ⟨L, hL, fun σ y y' hy hy' => ?_⟩
    rw [cylField_eq, cylField_eq]
    exact h σ y y' hy hy'
  have hglob : ∀ σ, LipschitzWith (Real.toNNReal L) (cylField m G σ) := fun σ =>
    LipschitzWith.of_dist_le' fun y y' => by
      rw [dist_eq_norm, dist_eq_norm]
      exact slope_of_ball hL (hslope σ) (hzero σ) y y'
  have hfd_zero : ∀ σ (y : Space), 2 * Rsupp < ‖y‖ → fderiv ℝ (cylField m G σ) y = 0 := by
    intro σ y hy
    have hev : cylField m G σ =ᶠ[nhds y] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with x hx
      exact hzero σ x hx.le
    rw [hev.fderiv_eq]
    exact fderiv_const_apply 0
  have hfd_bound : ∀ σ (y : Space), ‖fderiv ℝ (cylField m G σ) y‖ ≤ L := fun σ y => by
    have h := norm_fderiv_le_of_lipschitz ℝ (hglob σ) (x₀ := y)
    rwa [Real.coe_toNNReal _ hL] at h
  refine ⟨hjoint.aestronglyMeasurable, (measurable_fderiv_with_param ℝ hjoint).aestronglyMeasurable,
    fun σ => ⟨(hglob σ).continuous.locallyIntegrable, ?_, fun φ hφ i => ?_⟩, ?_, fun σ y hy => hzero σ y hy⟩
  · have hint : Integrable (fun y => fderiv ℝ (cylField m G σ) y) := by
      have hT : MeasurableSet (Metric.closedBall (0 : Space) (2 * Rsupp)) := measurableSet_closedBall
      have hfin : volume (Metric.closedBall (0 : Space) (2 * Rsupp)) ≠ ⊤ := measure_closedBall_lt_top.ne
      refine Integrable.mono' ((integrable_indicator_iff hT).2 (integrableOn_const hfin (C := L)))
        (measurable_fderiv ℝ _).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
      by_cases hy : y ∈ Metric.closedBall (0 : Space) (2 * Rsupp)
      · rw [Set.indicator_of_mem hy]
        exact hfd_bound σ y
      · rw [Set.indicator_of_notMem hy, hfd_zero σ y (by simpa using hy), norm_zero]
    exact hint.locallyIntegrable
  · have h := CellCert.GivenFields.DualRestInternal.weak_of_slopeBound (hglob σ) φ hφ i
    rw [h, neg_neg]
  · refine CertCell.GivenShape.Internal.periodLIntegral_lt_top_of_bound _ (3 * L ^ 2) (2 * Rsupp)
      (fun σ y => ?_) (fun σ y hy => ?_)
    · have hi : ∀ i : Fin 3, ‖fderiv ℝ (cylField m G σ) y (unitVector i)‖ ^ 2 ≤ L ^ 2 := fun i => by
        have h1 := (fderiv ℝ (cylField m G σ) y).le_opNorm (unitVector i)
        have h2 : ‖unitVector i‖ = 1 := by simp [unitVector]
        rw [h2, mul_one] at h1
        exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans (hfd_bound σ y)) 2
      unfold matSq
      rw [Fin.sum_univ_three]
      linarith [hi 0, hi 1, hi 2]
    · rw [hfd_zero σ y hy]
      simp [matSq]

end PotentialShape

end Breakdown
