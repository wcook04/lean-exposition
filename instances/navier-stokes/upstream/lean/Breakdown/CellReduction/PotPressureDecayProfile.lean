import Breakdown.CellReduction.PotentialShape
import Breakdown.CertCell.ShapeSplineSlope
import Breakdown.CertCell.ShapeSplineSmooth
import Breakdown.CertCell.ShapeJetValid
import Breakdown.CertCell.ShapeJetJoin
import Breakdown.CertCell.ShapeSplineDeriv
import Breakdown.CertCell.ShapeTypeTwoDecayPhase
import Breakdown.CertCell.InstanceSlope

open scoped ContDiff Topology
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown

namespace PotentialShape

namespace Internal.PressureDecay

open CertCell CertCell.GivenShape
open CellCert.GivenFields (Spline cellIndex cellCount weightPoly heightRatio)

theorem interior_lt_last {l : List ℝ} (hs : l.Pairwise (· < ·)) {c : ℝ} (hl : l.getLast? = some c) :
    ∀ b ∈ (l.drop 1).dropLast, b < c := by
  intro b hb
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hb
  have hlen : ((l.drop 1).dropLast).length = l.length - 1 - 1 := by simp
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_some_iff] at hl
  obtain ⟨hc, rfl⟩ := hl
  have hp' := hp
  rw [hlen] at hp'
  rw [List.getElem_dropLast, List.getElem_drop]
  exact List.pairwise_iff_getElem.1 hs _ _ _ _ (by omega)

theorem exists_upper_lt_one : ∀ (l : List ℝ), (∀ b ∈ l, b < 1) → ∃ m < 1, ∀ b ∈ l, b ≤ m
  | [], _ => ⟨0, one_pos, fun b hb => by simp at hb⟩
  | b :: l, h => by
    obtain ⟨m, hm, hb⟩ := exists_upper_lt_one l (fun c hc => h c (by simp [hc]))
    refine ⟨max b m, max_lt (h b (by simp)) hm, fun c hc => ?_⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact le_max_left _ _
    · exact (hb c hc).trans (le_max_right _ _)

theorem cellIndex_top (l : List ℝ) {s : ℝ} (h : ∀ b ∈ (l.drop 1).dropLast, b ≤ s) :
    cellIndex l s = cellCount l - 1 := by
  unfold cellIndex cellCount
  rw [List.filter_eq_self.2 (fun b hb => by simpa using h b hb)]
  simp

theorem one_sub_comp_line {a : ℝ} (ha : a ≠ 1) :
    (1 : Polynomial ℂ) - Polynomial.C ((((1 : ℝ) - a)⁻¹ : ℝ) : ℂ) * (Polynomial.X - Polynomial.C (a : ℂ)) =
      Polynomial.C ((((1 : ℝ) - a)⁻¹ : ℝ) : ℂ) * (1 - Polynomial.X) := by
  have h1 : ((1 : ℝ) - a) ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  have hc : ((((1 : ℝ) - a)⁻¹ : ℝ) : ℂ) * (1 - (a : ℂ)) = 1 := by
    rw [show (1 - (a : ℂ)) = (((1 : ℝ) - a : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_mul,
      inv_mul_cancel₀ h1, Complex.ofReal_one]
  have h2 : Polynomial.C ((((1 : ℝ) - a)⁻¹ : ℝ) : ℂ) -
      Polynomial.C ((((1 : ℝ) - a)⁻¹ : ℝ) : ℂ) * Polynomial.C (a : ℂ) = 1 := by
    rw [← Polynomial.C_mul, ← Polynomial.C_sub, ← Polynomial.C_1]
    congr 1
    linear_combination hc
  linear_combination (-1 : Polynomial ℂ) * h2

theorem dvd_nodalLeft (n p : ℕ) {a b : ℝ} (hb : b = 1) (ha : a ≠ 1) :
    (1 - Polynomial.X : Polynomial ℂ) ^ n ∣ nodalLeft n p a b := by
  subst hb
  have hR : jetUnit n p = (1 - Polynomial.X) ^ n * (Polynomial.C ((p.factorial : ℂ)⁻¹) * Polynomial.X ^ p *
      ∑ s ∈ Finset.range (n - p), Polynomial.C ((Nat.choose (n - 1 + s) s : ℕ) : ℂ) * Polynomial.X ^ s) := by
    unfold jetUnit
    ring
  unfold nodalLeft
  rw [hR, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.one_comp,
    Polynomial.X_comp, one_sub_comp_line ha, mul_pow]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (dvd_mul_left _ _) _) _

theorem dvd_nodalRight (n p : ℕ) {a b : ℝ} (hb : b = 1) :
    (1 - Polynomial.X : Polynomial ℂ) ^ p ∣ nodalRight n p a b := by
  subst hb
  unfold nodalRight jetUnit
  simp only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp, Complex.ofReal_one, map_one]
  rw [mul_pow]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_mul_left _ _) _) _) _) _

theorem dvd_bubble (n s : ℕ) (a : ℝ) {b : ℝ} (hb : b = 1) :
    (1 - Polynomial.X : Polynomial ℂ) ^ n ∣ bubblePoly n s a b := by
  subst hb
  unfold bubblePoly
  simp only [Complex.ofReal_one, map_one]
  rw [mul_pow]
  exact Dvd.dvd.mul_right (dvd_mul_left _ _) _

theorem dvd_dofPoly_last (A : JetAxis) (hA : IsJetAxis A 0 1) {z : ℕ} (hz : z ≤ A.depth) (d : JetDof)
    (hd : ∀ p, d = JetDof.node (cellCount A.breaks) p → z ≤ p) :
    (1 - Polynomial.X : Polynomial ℂ) ^ z ∣ A.dofPoly (cellCount A.breaks - 1) d := by
  have hlen := GivenShape.Internal.two_le_length A.breaks (by norm_num) hA.first hA.last
  have hN : cellCount A.breaks - 1 + 1 = cellCount A.breaks := by unfold cellCount; omega
  have hb : A.breaks.getD (cellCount A.breaks - 1 + 1) 0 = 1 := by
    rw [hN]
    have hl := hA.last
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_some_iff] at hl
    obtain ⟨h, e⟩ := hl
    unfold cellCount
    rw [List.getD_eq_getElem _ _ h, e]
  have ha : A.breaks.getD (cellCount A.breaks - 1) 0 ≠ 1 := by
    have hlt := GivenShape.Internal.getD_lt_getD_of_sorted hA.sorted
      (i := cellCount A.breaks - 1) (j := cellCount A.breaks - 1 + 1) (by omega) (by unfold cellCount; omega)
    rw [hb] at hlt
    exact hlt.ne
  cases d with
  | node k p =>
    simp only [JetAxis.dofPoly]
    split_ifs with h1 h2 h3
    · exact (pow_dvd_pow _ hz).trans (dvd_nodalLeft _ _ hb ha)
    · exact (pow_dvd_pow _ (hd p (by rw [h3, hN]))).trans (dvd_nodalRight _ _ hb)
    · exact dvd_zero _
    · exact dvd_zero _
  | bubble i s =>
    simp only [JetAxis.dofPoly]
    split_ifs
    · exact (pow_dvd_pow _ hz).trans (dvd_bubble _ _ _ hb)
    · exact dvd_zero _

theorem lastPiece_factor (H : JetSpline) (hA : IsJetAxis H.tAxis 0 1) {z : ℕ} (hz : z ≤ H.tAxis.depth)
    (hv : EndVanishOrder H z) (j : ℕ) :
    ∃ Q : MvPolynomial (Fin 2) ℂ,
      H.toSpline.piece (cellCount H.tAxis.breaks - 1) j = (1 - MvPolynomial.X 0) ^ z * Q := by
  have hdiv : (1 - MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ^ z ∣
      H.toSpline.piece (cellCount H.tAxis.breaks - 1) j := by
    rw [GivenShape.Internal.toSpline_piece]
    refine Finset.dvd_sum fun d _ => Finset.dvd_sum fun e _ => ?_
    by_cases hc : H.coef d e = 0
    · rw [hc]
      simp
    · have hd : ∀ p, d = JetDof.node (cellCount H.tAxis.breaks) p → z ≤ p := by
        intro p hp
        by_contra hlt
        exact hc (by rw [hp]; exact hv p (not_le.1 hlt) e)
      have h1 := map_dvd (Polynomial.aeval (R := ℂ) (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ))
        (dvd_dofPoly_last H.tAxis hA hz d hd)
      have e1 : Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ)
          ((1 - Polynomial.X : Polynomial ℂ) ^ z) = (1 - MvPolynomial.X 0) ^ z := by simp
      rw [e1] at h1
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h1 _) _
  exact hdiv


def weightedSpline (S : PotScalar) (t x : ℝ) : ℂ := weightPoly S.lowOrder S.highOrder t * S.amp.toSpline.evalHalf t x

def EndOrderBound (S : PotScalar) : Prop :=
  ∃ z ≤ S.amp.tAxis.depth, 2 ≤ S.highOrder + z ∧ EndVanishOrder S.amp z

theorem weightedSpline_lastForm (S : PotScalar) (hcl : IsJetClass 0 0 S.amp) (hend : EndOrderBound S) :
    ∃ m < 1, ∃ n : ℕ, ∃ Qf : ℕ → MvPolynomial (Fin 2) ℂ, 2 ≤ n ∧
      ∀ s x, m ≤ s → weightedSpline S s x = ((s ^ S.lowOrder * (1 - s) ^ n : ℝ) : ℂ) *
        MvPolynomial.eval ![(s : ℂ), (x : ℂ)] (Qf (cellIndex S.amp.xAxis.breaks x)) := by
  obtain ⟨z, hz, hn, hv⟩ := hend
  have hlt := interior_lt_last hcl.t_axis.sorted hcl.t_axis.last
  obtain ⟨m, hm, hgap⟩ := exists_upper_lt_one _ hlt
  choose Qf hQf using lastPiece_factor S.amp hcl.t_axis hz hv
  refine ⟨m, hm, S.highOrder + z, Qf, hn, fun s x hs => ?_⟩
  have hc : cellIndex S.amp.tAxis.breaks s = cellCount S.amp.tAxis.breaks - 1 :=
    cellIndex_top _ fun b hb => (hgap b hb).trans hs
  unfold weightedSpline
  change weightPoly S.lowOrder S.highOrder s * MvPolynomial.eval ![(s : ℂ), (x : ℂ)]
    (S.amp.toSpline.piece (cellIndex S.amp.tAxis.breaks s) (cellIndex S.amp.xAxis.breaks x)) = _
  rw [hc, hQf]
  simp only [weightPoly, map_mul, map_pow, map_sub, map_one, MvPolynomial.eval_X, Matrix.cons_val_zero]
  push_cast
  ring

theorem weight_norm_le (a b : ℕ) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : ‖weightPoly a b s‖ ≤ 1 := by
  unfold weightPoly
  have hu : 0 ≤ 1 - s := by linarith
  have hp : 0 ≤ s ^ a * (1 - s) ^ b := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
  exact mul_le_one₀ (pow_le_one₀ h0 h1) (by positivity) (pow_le_one₀ hu (by linarith))

theorem real_weight_norm_le (a n : ℕ) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    ‖((s ^ a * (1 - s) ^ n : ℝ) : ℂ)‖ ≤ (1 - s) ^ n := by
  have hu : 0 ≤ 1 - s := by linarith
  have hp : 0 ≤ s ^ a * (1 - s) ^ n := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
  have : 0 ≤ (1 - s) ^ n := by positivity
  calc s ^ a * (1 - s) ^ n ≤ 1 * (1 - s) ^ n := mul_le_mul_of_nonneg_right (pow_le_one₀ h0 h1) this
    _ = (1 - s) ^ n := one_mul _

theorem pow_le_sq_of_two_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) {n : ℕ} (hn : 2 ≤ n) : u ^ n ≤ u ^ 2 :=
  pow_le_pow_of_le_one h0 h1 hn

theorem evalHalf_continuous (H : JetSpline) (hcl : IsJetClass 0 0 H) :
    Continuous fun z : ℝ × ℝ => H.toSpline.evalHalf z.1 z.2 :=
  (joinedSplineSmooth 0 0 _ (GivenShape.Internal.joinedSpline_of_jetClass jetSplineJoined hcl)).continuous

theorem weightedSpline_continuous (S : PotScalar) (hcl : IsJetClass 0 0 S.amp) :
    Continuous fun z : ℝ × ℝ => weightedSpline S z.1 z.2 := by
  unfold weightedSpline weightPoly
  exact (Complex.continuous_ofReal.comp (by fun_prop)).mul (evalHalf_continuous S.amp hcl)

theorem weightedSpline_value (S : PotScalar) (hcl : IsJetClass 0 0 S.amp) (hend : EndOrderBound S) :
    ∃ C, 0 ≤ C ∧ ∀ t x, 0 ≤ t → t ≤ 1 → |x| ≤ 1 → ‖weightedSpline S t x‖ ≤ C * (1 - t) ^ 2 := by
  obtain ⟨m, hm, n, Qf, hn, hform⟩ := weightedSpline_lastForm S hcl hend
  obtain ⟨M0, hM0, hb0⟩ := GivenShape.Internal.pieceEval_bounded S.amp.tAxis.breaks S.amp.xAxis.breaks
    S.amp.toSpline.piece 1
  obtain ⟨Mq, hMq, hbq⟩ := GivenShape.Internal.pieceEval_bounded S.amp.tAxis.breaks S.amp.xAxis.breaks
    (fun _ j => Qf j) 1
  have hm1 : 0 < 1 - m := by linarith
  refine ⟨Mq + M0 / (1 - m) ^ 2, by positivity, fun t x ht0 ht1 hx => ?_⟩
  have htR : |t| ≤ 1 := abs_le.2 ⟨by linarith, ht1⟩
  have hu0 : 0 ≤ 1 - t := by linarith
  have hsq : 0 ≤ (1 - t) ^ 2 := by positivity
  by_cases hmt : m ≤ t
  · rw [hform t x hmt, norm_mul]
    have e1 := real_weight_norm_le S.lowOrder n ht0 ht1
    have e2 : ‖MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (Qf (cellIndex S.amp.xAxis.breaks x))‖ ≤ Mq :=
      hbq t x htR hx
    have e3 := pow_le_sq_of_two_le hu0 (by linarith) hn
    calc _ ≤ (1 - t) ^ n * Mq := mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
      _ ≤ (1 - t) ^ 2 * Mq := mul_le_mul_of_nonneg_right e3 hMq
      _ ≤ (Mq + M0 / (1 - m) ^ 2) * (1 - t) ^ 2 := by
        have : 0 ≤ M0 / (1 - m) ^ 2 * (1 - t) ^ 2 := by positivity
        nlinarith
  · have hlt : t < m := not_le.1 hmt
    have e0 : ‖weightedSpline S t x‖ ≤ M0 := by
      unfold weightedSpline
      rw [norm_mul]
      calc _ ≤ 1 * M0 := mul_le_mul (weight_norm_le _ _ ht0 ht1) (hb0 t x htR hx) (norm_nonneg _) zero_le_one
        _ = M0 := one_mul _
    have hq : (1 - m) ^ 2 ≤ (1 - t) ^ 2 := pow_le_pow_left₀ hm1.le (by linarith) 2
    have e4 : M0 ≤ M0 / (1 - m) ^ 2 * (1 - t) ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left hq hM0
    calc _ ≤ M0 := e0
      _ ≤ M0 / (1 - m) ^ 2 * (1 - t) ^ 2 := e4
      _ ≤ (Mq + M0 / (1 - m) ^ 2) * (1 - t) ^ 2 := by nlinarith

def weightDeriv (a b : ℕ) (s : ℝ) : ℝ := a * s ^ (a - 1) * (1 - s) ^ b + s ^ a * (b * (1 - s) ^ (b - 1) * (-1))

theorem wpoly_hasDerivAt (a b : ℕ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => s ^ a * (1 - s) ^ b) (weightDeriv a b s) s :=
  (hasDerivAt_pow a s).mul (((hasDerivAt_id' s).const_sub 1).pow b)

theorem wpoly_deriv_bound (a b : ℕ) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    ‖((weightDeriv a b s : ℝ) : ℂ)‖ ≤ (a + b) * (1 - s) ^ (b - 1) := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold weightDeriv
  have hu : 0 ≤ 1 - s := by linarith
  have p1 : s ^ (a - 1) ≤ 1 := pow_le_one₀ h0 h1
  have p2 : s ^ a ≤ 1 := pow_le_one₀ h0 h1
  have p3 : (1 - s) ^ b ≤ (1 - s) ^ (b - 1) := pow_le_pow_of_le_one hu (by linarith) (Nat.sub_le b 1)
  have q1 : 0 ≤ s ^ (a - 1) := by positivity
  have q2 : 0 ≤ s ^ a := by positivity
  have q3 : 0 ≤ (1 - s) ^ b := by positivity
  have q4 : 0 ≤ (1 - s) ^ (b - 1) := by positivity
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have X1 : 0 ≤ s ^ (a - 1) * (1 - s) ^ b := mul_nonneg q1 q3
  have X1' : s ^ (a - 1) * (1 - s) ^ b ≤ (1 - s) ^ (b - 1) := by
    calc s ^ (a - 1) * (1 - s) ^ b ≤ 1 * (1 - s) ^ (b - 1) := mul_le_mul p1 p3 q3 zero_le_one
      _ = (1 - s) ^ (b - 1) := one_mul _
  have X2 : 0 ≤ s ^ a * (1 - s) ^ (b - 1) := mul_nonneg q2 q4
  have X2' : s ^ a * (1 - s) ^ (b - 1) ≤ (1 - s) ^ (b - 1) := by
    calc s ^ a * (1 - s) ^ (b - 1) ≤ 1 * (1 - s) ^ (b - 1) := mul_le_mul_of_nonneg_right p2 q4
      _ = (1 - s) ^ (b - 1) := one_mul _
  have e : (a : ℝ) * s ^ (a - 1) * (1 - s) ^ b + s ^ a * (b * (1 - s) ^ (b - 1) * (-1)) =
      a * (s ^ (a - 1) * (1 - s) ^ b) - b * (s ^ a * (1 - s) ^ (b - 1)) := by ring
  rw [e, abs_le]
  have m1 := mul_le_mul_of_nonneg_left X1' ha
  have m2 := mul_le_mul_of_nonneg_left X2' hb
  have m3 := mul_nonneg ha X1
  have m4 := mul_nonneg hb X2
  constructor <;> nlinarith

theorem weightedSpline_slope_t (S : PotScalar) (hcl : IsJetClass 0 0 S.amp) (hend : EndOrderBound S) :
    ∃ C, 0 ≤ C ∧ ∀ x, |x| ≤ 1 → ∀ t' t, 0 ≤ t' → t' ≤ t → t ≤ 1 →
      ‖weightedSpline S t x - weightedSpline S t' x‖ ≤ C * (1 - t') * (t - t') := by
  obtain ⟨m, hm, n, Qf, hn, hform⟩ := weightedSpline_lastForm S hcl hend
  obtain ⟨M0, hM0, hb0⟩ := GivenShape.Internal.pieceEval_bounded S.amp.tAxis.breaks S.amp.xAxis.breaks
    S.amp.toSpline.piece 1
  obtain ⟨M0t, hM0t, hb0t⟩ := GivenShape.Internal.pieceEval_bounded S.amp.tAxis.breaks S.amp.xAxis.breaks
    (fun i j => MvPolynomial.pderiv 0 (S.amp.toSpline.piece i j)) 1
  obtain ⟨Mq, hMq, hbq⟩ := GivenShape.Internal.pieceEval_bounded S.amp.tAxis.breaks S.amp.xAxis.breaks
    (fun _ j => Qf j) 1
  obtain ⟨Mqt, hMqt, hbqt⟩ := GivenShape.Internal.pieceEval_bounded S.amp.tAxis.breaks S.amp.xAxis.breaks
    (fun _ j => MvPolynomial.pderiv 0 (Qf j)) 1
  have hm1 : 0 < 1 - m := by linarith
  set e0 := S.lowOrder with he0
  set e1 := S.highOrder with he1
  set K1 : ℝ := ((e0 : ℝ) + n) * Mq + Mqt with hK1
  set K2 : ℝ := ((e0 : ℝ) + e1) * M0 + M0t with hK2
  have hK1p : 0 ≤ K1 := by positivity
  have hK2p : 0 ≤ K2 := by positivity
  refine ⟨K1 + K2 / (1 - m), by positivity, fun x hx t' t ht0 htt ht1 => ?_⟩
  have hcont : Continuous fun s => weightedSpline S s x :=
    (weightedSpline_continuous S hcl).comp (continuous_id.prodMk continuous_const)
  let D : ℝ → ℂ := fun s => if m ≤ s then
      (((weightDeriv e0 n s : ℝ) : ℂ) *
        MvPolynomial.eval ![(s : ℂ), (x : ℂ)] (Qf (cellIndex S.amp.xAxis.breaks x)) +
      ((s ^ e0 * (1 - s) ^ n : ℝ) : ℂ) *
        MvPolynomial.eval ![(s : ℂ), (x : ℂ)] (MvPolynomial.pderiv 0 (Qf (cellIndex S.amp.xAxis.breaks x))))
    else
      (((weightDeriv e0 e1 s : ℝ) : ℂ) *
        GivenShape.Internal.pieceEval S.amp.tAxis.breaks S.amp.xAxis.breaks S.amp.toSpline.piece s x +
      ((s ^ e0 * (1 - s) ^ e1 : ℝ) : ℂ) * GivenShape.Internal.pieceEval S.amp.tAxis.breaks S.amp.xAxis.breaks
        (fun i j => MvPolynomial.pderiv 0 (S.amp.toSpline.piece i j)) s x)
  have hderiv : ∀ s ∈ Ico t' t, HasDerivWithinAt (fun s => weightedSpline S s x) (D s) (Ici s) s := by
    intro s _
    by_cases hms : m ≤ s
    · simp only [D, if_pos hms]
      have h1 := ((wpoly_hasDerivAt e0 n s).ofReal_comp.mul
        (GivenShape.Internal.polyEval_hasDerivAt_first (Qf (cellIndex S.amp.xAxis.breaks x)) x s))
      exact h1.hasDerivWithinAt.congr (fun u hu => hform u x (hms.trans hu)) (hform s x hms)
    · simp only [D, if_neg hms]
      have h1 := ((wpoly_hasDerivAt e0 e1 s).ofReal_comp).hasDerivWithinAt (s := Ici s)
      have h2 := GivenShape.Internal.pieceEval_right_first S.amp.tAxis.breaks S.amp.xAxis.breaks
        S.amp.toSpline.piece x s
      exact h1.mul h2
  have hbound : ∀ s ∈ Ico t' t, ‖D s‖ ≤ (K1 + K2 / (1 - m)) * (1 - t') := by
    intro s hs
    have hs0 : 0 ≤ s := ht0.trans hs.1
    have hs1 : s ≤ 1 := hs.2.le.trans ht1
    have hsR : |s| ≤ 1 := abs_le.2 ⟨by linarith, hs1⟩
    have hu : 0 ≤ 1 - s := by linarith
    have hus : 1 - s ≤ 1 - t' := by linarith [hs.1]
    have ht'1 : 0 ≤ 1 - t' := by linarith
    by_cases hms : m ≤ s
    · simp only [D, if_pos hms]
      have w1 := wpoly_deriv_bound e0 n hs0 hs1
      have q1 : ‖MvPolynomial.eval ![(s : ℂ), (x : ℂ)] (Qf (cellIndex S.amp.xAxis.breaks x))‖ ≤ Mq :=
        hbq s x hsR hx
      have q2 : ‖MvPolynomial.eval ![(s : ℂ), (x : ℂ)]
          (MvPolynomial.pderiv 0 (Qf (cellIndex S.amp.xAxis.breaks x)))‖ ≤ Mqt := hbqt s x hsR hx
      have w2 := real_weight_norm_le e0 n hs0 hs1
      have pn1 : (1 - s) ^ (n - 1) ≤ 1 - s := by
        calc (1 - s) ^ (n - 1) ≤ (1 - s) ^ 1 := pow_le_pow_of_le_one hu (by linarith) (by omega)
          _ = 1 - s := pow_one _
      have pn : (1 - s) ^ n ≤ 1 - s := by
        calc (1 - s) ^ n ≤ (1 - s) ^ 1 := pow_le_pow_of_le_one hu (by linarith) (by omega)
          _ = 1 - s := pow_one _
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have h3 := mul_le_mul w1 q1 (norm_nonneg _) (by positivity)
      have h4 := mul_le_mul w2 q2 (norm_nonneg _) (by positivity)
      have h5 : ((e0 : ℝ) + n) * (1 - s) ^ (n - 1) * Mq ≤ ((e0 : ℝ) + n) * (1 - t') * Mq := by
        gcongr
        exact pn1.trans hus
      have h6 : (1 - s) ^ n * Mqt ≤ (1 - t') * Mqt := by
        gcongr
        exact pn.trans hus
      have h7 : 0 ≤ K2 / (1 - m) * (1 - t') := by positivity
      have e : (K1 + K2 / (1 - m)) * (1 - t') = ((e0 : ℝ) + n) * (1 - t') * Mq + (1 - t') * Mqt +
          K2 / (1 - m) * (1 - t') := by rw [hK1]; ring
      rw [e]
      linarith
    · simp only [D, if_neg hms]
      have hlt : s < m := not_le.1 hms
      have w1 : ‖((weightDeriv e0 e1 s : ℝ) : ℂ)‖ ≤ (e0 + e1) := by
        refine (wpoly_deriv_bound e0 e1 hs0 hs1).trans ?_
        have : (1 - s) ^ (e1 - 1) ≤ 1 := pow_le_one₀ hu (by linarith)
        have : (0 : ℝ) ≤ e0 + e1 := by positivity
        nlinarith
      have q1 : ‖GivenShape.Internal.pieceEval S.amp.tAxis.breaks S.amp.xAxis.breaks S.amp.toSpline.piece s x‖ ≤ M0 :=
        hb0 s x hsR hx
      have q2 : ‖GivenShape.Internal.pieceEval S.amp.tAxis.breaks S.amp.xAxis.breaks
          (fun i j => MvPolynomial.pderiv 0 (S.amp.toSpline.piece i j)) s x‖ ≤ M0t := hb0t s x hsR hx
      have w2 : ‖((s ^ e0 * (1 - s) ^ e1 : ℝ) : ℂ)‖ ≤ 1 := weight_norm_le e0 e1 hs0 hs1
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have h3 := mul_le_mul w1 q1 (norm_nonneg _) (by positivity)
      have h4 := mul_le_mul w2 q2 (norm_nonneg _) (by positivity)
      have h5 : K2 ≤ K2 / (1 - m) * (1 - t') := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hm1]
        exact mul_le_mul_of_nonneg_left (by linarith) hK2p
      have h6 : 0 ≤ K1 * (1 - t') := by positivity
      have e : (K1 + K2 / (1 - m)) * (1 - t') = K1 * (1 - t') + K2 / (1 - m) * (1 - t') := by ring
      rw [e]
      have : ((e0 : ℝ) + e1) * M0 + 1 * M0t = K2 := by rw [hK2]; ring
      linarith
  exact norm_image_sub_le_of_norm_deriv_right_le_segment (f := fun s => weightedSpline S s x) hcont.continuousOn hderiv
    hbound t ⟨htt, le_rfl⟩

theorem weightedSpline_slope_x (S : PotScalar) (hcl : IsJetClass 0 0 S.amp) (hend : EndOrderBound S) :
    ∃ C, 0 ≤ C ∧ ∀ t, 0 ≤ t → t ≤ 1 → ∀ x x', |x| ≤ 1 → |x'| ≤ 1 →
      ‖weightedSpline S t x - weightedSpline S t x'‖ ≤ C * (1 - t) ^ 2 * |x - x'| := by
  obtain ⟨m, hm, n, Qf, hn, hform⟩ := weightedSpline_lastForm S hcl hend
  obtain ⟨M0x, hM0x, hb0x⟩ := GivenShape.Internal.pieceEval_bounded S.amp.tAxis.breaks S.amp.xAxis.breaks
    (fun i j => MvPolynomial.pderiv 1 (S.amp.toSpline.piece i j)) 1
  obtain ⟨Mqx, hMqx, hbqx⟩ := GivenShape.Internal.pieceEval_bounded S.amp.tAxis.breaks S.amp.xAxis.breaks
    (fun _ j => MvPolynomial.pderiv 1 (Qf j)) 1
  have hm1 : 0 < 1 - m := by linarith
  refine ⟨Mqx + M0x / (1 - m) ^ 2, by positivity, fun t ht0 ht1 x x' hx hx' => ?_⟩
  have htR : |t| ≤ 1 := abs_le.2 ⟨by linarith, ht1⟩
  have hu : 0 ≤ 1 - t := by linarith
  have hcont : Continuous fun s => weightedSpline S t s :=
    (weightedSpline_continuous S hcl).comp (continuous_const.prodMk continuous_id)
  have hsq : 0 ≤ (1 - t) ^ 2 := by positivity
  by_cases hmt : m ≤ t
  · have hd : ∀ s : ℝ, HasDerivWithinAt (fun s => weightedSpline S t s)
        (((t ^ S.lowOrder * (1 - t) ^ n : ℝ) : ℂ) * MvPolynomial.eval ![(t : ℂ), (s : ℂ)]
          (MvPolynomial.pderiv 1 (Qf (cellIndex S.amp.xAxis.breaks s)))) (Ici s) s := by
      intro s
      have h1 := ((GivenShape.Internal.polyEval_hasDerivAt_second (Qf (cellIndex S.amp.xAxis.breaks s)) t s).const_mul
        (((t ^ S.lowOrder * (1 - t) ^ n : ℝ) : ℂ))).hasDerivWithinAt (s := Ici s)
      refine h1.congr_of_eventuallyEq ?_ (hform t s hmt)
      filter_upwards [GivenShape.Internal.cellIndex_eventually_right S.amp.xAxis.breaks s] with u hu
      rw [hform t u hmt, hu]
    have hb : ∀ s : ℝ, |s| ≤ 1 → ‖((t ^ S.lowOrder * (1 - t) ^ n : ℝ) : ℂ) * MvPolynomial.eval ![(t : ℂ), (s : ℂ)]
        (MvPolynomial.pderiv 1 (Qf (cellIndex S.amp.xAxis.breaks s)))‖ ≤ (Mqx + M0x / (1 - m) ^ 2) * (1 - t) ^ 2 := by
      intro s hs
      rw [norm_mul]
      have w := real_weight_norm_le S.lowOrder n ht0 ht1
      have q : ‖MvPolynomial.eval ![(t : ℂ), (s : ℂ)] (MvPolynomial.pderiv 1 (Qf (cellIndex S.amp.xAxis.breaks s)))‖ ≤ Mqx :=
        hbqx t s htR hs
      have e3 := pow_le_sq_of_two_le hu (by linarith) hn
      have h1 := mul_le_mul w q (norm_nonneg _) (by positivity)
      have h2 := mul_le_mul_of_nonneg_right e3 hMqx
      have h3 : 0 ≤ M0x / (1 - m) ^ 2 * (1 - t) ^ 2 := by positivity
      have e : (Mqx + M0x / (1 - m) ^ 2) * (1 - t) ^ 2 = (1 - t) ^ 2 * Mqx + M0x / (1 - m) ^ 2 * (1 - t) ^ 2 := by ring
      rw [e]
      linarith
    exact GivenShape.Internal.slice_diff_le hcont hd hb x x' hx hx'
  · have hlt : t < m := not_le.1 hmt
    have hd : ∀ s : ℝ, HasDerivWithinAt (fun s => weightedSpline S t s)
        (weightPoly S.lowOrder S.highOrder t * GivenShape.Internal.pieceEval S.amp.tAxis.breaks S.amp.xAxis.breaks
          (fun i j => MvPolynomial.pderiv 1 (S.amp.toSpline.piece i j)) t s) (Ici s) s := fun s =>
      (GivenShape.Internal.pieceEval_right_second S.amp.tAxis.breaks S.amp.xAxis.breaks
        S.amp.toSpline.piece t s).const_mul _
    have hq : (1 - m) ^ 2 ≤ (1 - t) ^ 2 := pow_le_pow_left₀ hm1.le (by linarith) 2
    have hb : ∀ s : ℝ, |s| ≤ 1 → ‖weightPoly S.lowOrder S.highOrder t * GivenShape.Internal.pieceEval
        S.amp.tAxis.breaks S.amp.xAxis.breaks (fun i j => MvPolynomial.pderiv 1 (S.amp.toSpline.piece i j)) t s‖ ≤
        (Mqx + M0x / (1 - m) ^ 2) * (1 - t) ^ 2 := by
      intro s hs
      rw [norm_mul]
      have h1 := mul_le_mul (weight_norm_le S.lowOrder S.highOrder ht0 ht1) (hb0x t s htR hs) (norm_nonneg _)
        zero_le_one
      have e4 : M0x ≤ M0x / (1 - m) ^ 2 * (1 - t) ^ 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left hq hM0x
      have h3 : 0 ≤ Mqx * (1 - t) ^ 2 := by positivity
      have e : (Mqx + M0x / (1 - m) ^ 2) * (1 - t) ^ 2 = Mqx * (1 - t) ^ 2 + M0x / (1 - m) ^ 2 * (1 - t) ^ 2 := by ring
      rw [e]
      linarith
    exact GivenShape.Internal.slice_diff_le hcont hd hb x x' hx hx'

def axisProfile (S : PotScalar) (t x : ℝ) : ℂ := (((1 - x ^ 2) ^ S.axisPower : ℝ) : ℂ) * weightedSpline S t x

theorem base_nonneg {x : ℝ} (hx : |x| ≤ 1) : 0 ≤ 1 - x ^ 2 := by
  have := (sq_le_one_iff_abs_le_one x).2 hx
  linarith

theorem base_le_one (x : ℝ) : 1 - x ^ 2 ≤ 1 := by
  have := sq_nonneg x
  linarith

theorem axisPow_nonneg (k : ℕ) {x : ℝ} (hx : |x| ≤ 1) : 0 ≤ (1 - x ^ 2) ^ k :=
  pow_nonneg (base_nonneg hx) k

theorem axisPow_le_one (k : ℕ) {x : ℝ} (hx : |x| ≤ 1) : (1 - x ^ 2) ^ k ≤ 1 :=
  pow_le_one₀ (base_nonneg hx) (base_le_one x)

theorem axisPow_slope (k : ℕ) {x x' : ℝ} (hx : |x| ≤ 1) (hx' : |x'| ≤ 1) :
    |(1 - x ^ 2) ^ k - (1 - x' ^ 2) ^ k| ≤ 2 * k * |x - x'| := by
  have h := abs_pow_sub_pow_le (1 - x ^ 2) (1 - x' ^ 2) k
  have h0 := base_nonneg hx
  have h0' := base_nonneg hx'
  have hm : max |1 - x ^ 2| |1 - x' ^ 2| ^ (k - 1) ≤ 1 := by
    refine pow_le_one₀ (le_max_of_le_left (abs_nonneg _)) (max_le ?_ ?_)
    · rw [abs_of_nonneg h0]
      exact base_le_one x
    · rw [abs_of_nonneg h0']
      exact base_le_one x'
  have hd : |(1 - x ^ 2) - (1 - x' ^ 2)| ≤ 2 * |x - x'| := by
    rw [show (1 - x ^ 2) - (1 - x' ^ 2) = (x' - x) * (x' + x) by ring, abs_mul, abs_sub_comm x' x]
    have : |x' + x| ≤ 2 := (abs_add_le _ _).trans (by linarith)
    have := abs_nonneg (x - x')
    nlinarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc _ ≤ |(1 - x ^ 2) - (1 - x' ^ 2)| * (k : ℝ) * max |1 - x ^ 2| |1 - x' ^ 2| ^ (k - 1) := h
    _ ≤ (2 * |x - x'|) * (k : ℝ) * 1 := by
      have := abs_nonneg ((1 - x ^ 2) - (1 - x' ^ 2))
      have := pow_nonneg (le_max_of_le_left (abs_nonneg (1 - x ^ 2)) : (0 : ℝ) ≤ max |1 - x ^ 2| |1 - x' ^ 2|) (k - 1)
      gcongr
    _ = 2 * k * |x - x'| := by ring

theorem axisProfile_bounds (S : PotScalar) (hcl : IsJetClass 0 0 S.amp) (hend : EndOrderBound S) :
    ∃ Cv Ct Cx : ℝ, 0 ≤ Cv ∧ 0 ≤ Ct ∧ 0 ≤ Cx ∧
      (∀ t x, 0 ≤ t → t ≤ 1 → |x| ≤ 1 → ‖axisProfile S t x‖ ≤ Cv * (1 - t) ^ 2 * (1 - x ^ 2) ^ S.axisPower) ∧
      (∀ x, |x| ≤ 1 → ∀ t t', 0 ≤ t → t ≤ 1 → 0 ≤ t' → t' ≤ 1 →
        ‖axisProfile S t x - axisProfile S t' x‖ ≤ Ct * max (1 - t) (1 - t') * |t - t'|) ∧
      (∀ t, 0 ≤ t → t ≤ 1 → ∀ x x', |x| ≤ 1 → |x'| ≤ 1 →
        ‖axisProfile S t x - axisProfile S t x'‖ ≤ Cx * (1 - t) ^ 2 * |x - x'|) := by
  obtain ⟨Cv, hCv, hv⟩ := weightedSpline_value S hcl hend
  obtain ⟨Ct, hCt, ht⟩ := weightedSpline_slope_t S hcl hend
  obtain ⟨Cx, hCx, hx⟩ := weightedSpline_slope_x S hcl hend
  refine ⟨Cv, Ct, 2 * S.axisPower * Cv + Cx, hCv, hCt, by positivity, ?_, ?_, ?_⟩
  · intro t x ht0 ht1 hx1
    unfold axisProfile
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (axisPow_nonneg _ hx1)]
    have := mul_le_mul_of_nonneg_left (hv t x ht0 ht1 hx1) (axisPow_nonneg S.axisPower hx1)
    linarith
  · intro x hx1 t t' ht0 ht1 ht0' ht1'
    unfold axisProfile
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (axisPow_nonneg _ hx1)]
    have hA := axisPow_le_one S.axisPower hx1
    have hA0 := axisPow_nonneg S.axisPower hx1
    have key : ‖weightedSpline S t x - weightedSpline S t' x‖ ≤ Ct * max (1 - t) (1 - t') * |t - t'| := by
      rcases le_total t' t with h | h
      · have := ht x hx1 t' t ht0' h ht1
        rw [max_eq_right (by linarith), abs_of_nonneg (by linarith)]
        exact this
      · have := ht x hx1 t t' ht0 h ht1'
        rw [norm_sub_rev, max_eq_left (by linarith), abs_of_nonpos (by linarith)]
        linarith
    have h0 : 0 ≤ ‖weightedSpline S t x - weightedSpline S t' x‖ := norm_nonneg _
    nlinarith
  · intro t ht0 ht1 x x' hx1 hx1'
    unfold axisProfile
    have e : (((1 - x ^ 2) ^ S.axisPower : ℝ) : ℂ) * weightedSpline S t x - (((1 - x' ^ 2) ^ S.axisPower : ℝ) : ℂ) * weightedSpline S t x' =
        ((((1 - x ^ 2) ^ S.axisPower - (1 - x' ^ 2) ^ S.axisPower : ℝ)) : ℂ) * weightedSpline S t x +
          (((1 - x' ^ 2) ^ S.axisPower : ℝ) : ℂ) * (weightedSpline S t x - weightedSpline S t x') := by
      push_cast
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (axisPow_nonneg _ hx1')]
    have a1 := axisPow_slope S.axisPower hx1 hx1'
    have a2 := axisPow_le_one S.axisPower hx1'
    have a3 := axisPow_nonneg S.axisPower hx1'
    have v1 := hv t x ht0 ht1 hx1
    have v2 := hx t ht0 ht1 x x' hx1 hx1'
    have p1 := mul_le_mul a1 v1 (norm_nonneg _) (by positivity)
    have p2 := mul_le_mul a2 v2 (norm_nonneg _) zero_le_one
    have e2 : (2 * S.axisPower * Cv + Cx) * (1 - t) ^ 2 * |x - x'| =
        2 * S.axisPower * |x - x'| * (Cv * (1 - t) ^ 2) + 1 * (Cx * (1 - t) ^ 2 * |x - x'|) := by ring
    rw [e2]
    linarith

end Internal.PressureDecay

end PotentialShape

end Breakdown
