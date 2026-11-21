import Breakdown.FracCell.GivenProfileSmoothField
import Breakdown.FracCell.GivenAuxPinSmoothLocal

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace FracCellInternal

open CellCert.GivenFields

private def chartQ (P : ChartParams) (t : ℝ) : ℝ := P.L0 ^ 2 * t ^ 2 + P.rc ^ 2 * (1 - t) ^ 2

private def phaseR (P : ChartParams) (r : ℝ) : ℝ := (1 / 2) * Real.log (1 + r ^ 2 / P.rc ^ 2)

private def innerAt (P : ChartParams) (D : FieldData) (β : ℝ) (n : ℤ) (r : ℝ) (y : Space) (i : Fin 3) : ℂ :=
  (((1 - r / (r + P.L0)) ^ (2 * P.eps) : ℝ) : ℂ) *
    (Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * angleOf y + n * β * phaseR P r : ℝ) : ℂ)) *
    (reducedField P D n β (r / (r + P.L0)) (heightRatio y) 0 * radialVec y i +
      reducedField P D n β (r / (r + P.L0)) (heightRatio y) 1 * polarVecQ y i +
      reducedField P D n β (r / (r + P.L0)) (heightRatio y) 2 * azimVecQ y i))

private def turnVec (φ : ℝ) (y : Space) : Space :=
  ofComponents ![Real.cos φ * y 0 - Real.sin φ * y 1, Real.sin φ * y 0 + Real.cos φ * y 1, y 2]

private def radialWeight (P : ChartParams) (e : ℕ) (κ : ℝ) (p : Polynomial ℝ) (r : ℝ) : ℂ :=
  (((1 - r / (r + P.L0)) ^ (2 * P.eps) * ((1 - r / (r + P.L0)) ^ e / chartQ P (r / (r + P.L0)) *
    p.eval (r / (r + P.L0))) : ℝ) : ℂ) * Complex.exp (Complex.I * ((κ * phaseR P r : ℝ) : ℂ))

private theorem modeFieldOf_eq_innerAt (P : ChartParams) (D : FieldData) (β : ℝ) (n : ℤ) (y : Space) :
    modeFieldOf P D β n y = ofComponents (fun i => (innerAt P D β n ‖y‖ y i).re) := rfl

private theorem chartQ_pos (P : ChartParams) (hP : IsChartParams P) (t : ℝ) : 0 < chartQ P t := by
  have hL := hP.L0_pos
  have hr := hP.rc_pos
  unfold chartQ
  by_cases ht : t = 0
  · subst ht
    simp
    positivity
  · have h1 : 0 < P.L0 ^ 2 * t ^ 2 := by positivity
    have h2 : 0 ≤ P.rc ^ 2 * (1 - t) ^ 2 := by positivity
    linarith

private def LocPoly (tL : ℝ) (N : ℕ) (F : ℝ → ℝ → ℂ) : Prop :=
  ∀ x : ℝ, ∃ Q : Polynomial ℂ, Q.natDegree ≤ N ∧ ∀ t : ℝ, tL < t → t < 1 → F t x = Q.eval (t : ℂ)

private theorem LocPoly.mono {tL tL' : ℝ} {N N' : ℕ} {F : ℝ → ℝ → ℂ} (h : LocPoly tL N F) (ht : tL ≤ tL')
    (hN : N ≤ N') : LocPoly tL' N' F := by
  intro x
  obtain ⟨Q, hQ, hF⟩ := h x
  exact ⟨Q, hQ.trans hN, fun t h1 h2 => hF t (by linarith) h2⟩

private theorem LocPoly.add {tL : ℝ} {N M : ℕ} {F G : ℝ → ℝ → ℂ} (hF : LocPoly tL N F) (hG : LocPoly tL M G) :
    LocPoly tL (max N M) (fun t x => F t x + G t x) := by
  intro x
  obtain ⟨Q, hQ, hF⟩ := hF x
  obtain ⟨R, hR, hG⟩ := hG x
  refine ⟨Q + R, (Polynomial.natDegree_add_le _ _).trans (max_le_max hQ hR), fun t h1 h2 => ?_⟩
  beta_reduce
  rw [hF t h1 h2, hG t h1 h2, Polynomial.eval_add]

private theorem LocPoly.mul {tL : ℝ} {N M : ℕ} {F G : ℝ → ℝ → ℂ} (hF : LocPoly tL N F) (hG : LocPoly tL M G) :
    LocPoly tL (N + M) (fun t x => F t x * G t x) := by
  intro x
  obtain ⟨Q, hQ, hF⟩ := hF x
  obtain ⟨R, hR, hG⟩ := hG x
  refine ⟨Q * R, Polynomial.natDegree_mul_le.trans (add_le_add hQ hR), fun t h1 h2 => ?_⟩
  beta_reduce
  rw [hF t h1 h2, hG t h1 h2, Polynomial.eval_mul]

private theorem LocPoly.const {tL : ℝ} (g : ℝ → ℂ) : LocPoly tL 0 (fun _ x => g x) := by
  intro x
  exact ⟨Polynomial.C (g x), by simp, fun t _ _ => by simp⟩

private theorem LocPoly.ofPoly {tL : ℝ} (R : Polynomial ℂ) (f : ℝ → ℂ) (hf : ∀ t : ℝ, f t = R.eval (t : ℂ)) :
    LocPoly tL R.natDegree (fun t _ => f t) := by
  intro x
  exact ⟨R, le_rfl, fun t _ _ => hf t⟩

private theorem LocPoly.eventually {tL : ℝ} {N : ℕ} {F : ℝ → ℝ → ℂ} (hF : LocPoly tL N F) (x t : ℝ) (h1 : tL < t)
    (h2 : t < 1) : ∃ Q : Polynomial ℂ, Q.natDegree ≤ N ∧
      (fun t' => F t' x) =ᶠ[nhds t] (fun t' : ℝ => Q.eval (t' : ℂ)) := by
  obtain ⟨Q, hQ, hFQ⟩ := hF x
  refine ⟨Q, hQ, ?_⟩
  filter_upwards [Ioo_mem_nhds h1 h2] with s hs using hFQ s hs.1 hs.2

private theorem LocPoly.hasDerivAt {tL : ℝ} {N : ℕ} {F : ℝ → ℝ → ℂ} (hF : LocPoly tL N F) (x t : ℝ) (h1 : tL < t)
    (h2 : t < 1) : HasDerivAt (fun t' => F t' x) (deriv (fun t' => F t' x) t) t := by
  obtain ⟨Q, -, hev⟩ := hF.eventually x t h1 h2
  have hd : HasDerivAt (fun t' : ℝ => Q.eval (t' : ℂ)) (Q.derivative.eval (t : ℂ)) t :=
    (Polynomial.hasDerivAt Q (t : ℂ)).comp_ofReal
  rw [hev.deriv_eq, hd.deriv]
  exact hd.congr_of_eventuallyEq hev

private theorem LocPoly.tderiv {tL : ℝ} {N : ℕ} {F : ℝ → ℝ → ℂ} (hF : LocPoly tL N F) :
    LocPoly tL N (fun t x => deriv (fun t' => F t' x) t) := by
  intro x
  obtain ⟨Q, hQ, hFQ⟩ := hF x
  refine ⟨Polynomial.derivative Q, (Polynomial.natDegree_derivative_le Q).trans (by omega), fun t h1 h2 => ?_⟩
  have hev : (fun t' => F t' x) =ᶠ[nhds t] (fun t' : ℝ => Q.eval (t' : ℂ)) := by
    filter_upwards [Ioo_mem_nhds h1 h2] with s hs using hFQ s hs.1 hs.2
  beta_reduce
  rw [hev.deriv_eq]
  exact ((Polynomial.hasDerivAt Q (t : ℂ)).comp_ofReal).deriv

private theorem LocPoly.xderiv {tL : ℝ} {N : ℕ} {F : ℝ → ℝ → ℂ} (hF : LocPoly tL N F) (htL : tL < 1)
    (hd : ∀ t, tL < t → t < 1 → ∀ x, DifferentiableAt ℝ (F t) x) :
    LocPoly tL N (fun t x => deriv (F t) x) := by
  classical
  set Tr : Fin (N + 1) → ℝ := fun j => 1 - (1 - tL) / ((j : ℕ) + 2 : ℝ) with hTdef
  set T : Fin (N + 1) → ℂ := fun j => ((Tr j : ℝ) : ℂ) with hTc
  have hdl : 0 < 1 - tL := by linarith
  have hTin : ∀ j, tL < Tr j ∧ Tr j < 1 := by
    intro j
    have hj : (2 : ℝ) ≤ (j : ℕ) + 2 := by have := (Nat.cast_nonneg (α := ℝ) (j : ℕ)); linarith
    have hpos : 0 < (1 - tL) / ((j : ℕ) + 2 : ℝ) := by positivity
    have hlt : (1 - tL) / ((j : ℕ) + 2 : ℝ) < 1 - tL := by
      rw [div_lt_iff₀ (by linarith)]
      nlinarith
    simp only [hTdef]
    constructor <;> linarith
  have hTinj : Function.Injective T := by
    intro i j hij
    simp only [hTc, Complex.ofReal_inj, hTdef] at hij
    have h2 : (1 - tL) / ((i : ℕ) + 2 : ℝ) = (1 - tL) / ((j : ℕ) + 2 : ℝ) := by linarith
    have hi : (0 : ℝ) < (i : ℕ) + 2 := by positivity
    have hj : (0 : ℝ) < (j : ℕ) + 2 := by positivity
    rw [div_eq_div_iff hi.ne' hj.ne'] at h2
    have h3 : ((i : ℕ) : ℝ) = (j : ℕ) := by
      have := mul_left_cancel₀ hdl.ne' (by linarith : (1 - tL) * ((j : ℕ) + 2 : ℝ) = (1 - tL) * ((i : ℕ) + 2 : ℝ))
      linarith
    exact Fin.ext (by exact_mod_cast h3)
  have hrep : ∀ t, tL < t → t < 1 → ∀ x', F t x' =
      ∑ j, F (Tr j) x' * (Lagrange.basis Finset.univ T j).eval (t : ℂ) := by
    intro t h1 h2 x'
    obtain ⟨Q, hQ, hFQ⟩ := hF x'
    have hdeg : Q.degree < (Finset.univ : Finset (Fin (N + 1))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hQ)
    have hI := Lagrange.eq_interpolate (s := Finset.univ) (v := T) hTinj.injOn hdeg
    rw [hFQ t h1 h2]
    conv_lhs => rw [hI]
    simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hFQ (Tr j) (hTin j).1 (hTin j).2]
  intro x
  refine ⟨∑ j, Polynomial.C (deriv (F (Tr j)) x) * Lagrange.basis Finset.univ T j, ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [Lagrange.natDegree_basis hTinj.injOn (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
    omega
  · intro t h1 h2
    have hfun : F t = fun x' => ∑ j, F (Tr j) x' * (Lagrange.basis Finset.univ T j).eval (t : ℂ) :=
      funext (hrep t h1 h2)
    have hder : HasDerivAt (fun x' => ∑ j, F (Tr j) x' * (Lagrange.basis Finset.univ T j).eval (t : ℂ))
        (∑ j, deriv (F (Tr j)) x * (Lagrange.basis Finset.univ T j).eval (t : ℂ)) x :=
      HasDerivAt.fun_sum fun j _ => ((hd (Tr j) (hTin j).1 (hTin j).2 x).hasDerivAt).mul_const _
    beta_reduce
    rw [hfun, hder.deriv, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C]

private def LP (tL : ℝ) (F : ℝ → ℝ → ℂ) : Prop := ∃ N, LocPoly tL N F

private theorem LP.add {tL : ℝ} {F G : ℝ → ℝ → ℂ} (hF : LP tL F) (hG : LP tL G) :
    LP tL (fun t x => F t x + G t x) := by
  obtain ⟨N, hN⟩ := hF
  obtain ⟨M, hM⟩ := hG
  exact ⟨_, hN.add hM⟩

private theorem LP.mul {tL : ℝ} {F G : ℝ → ℝ → ℂ} (hF : LP tL F) (hG : LP tL G) :
    LP tL (fun t x => F t x * G t x) := by
  obtain ⟨N, hN⟩ := hF
  obtain ⟨M, hM⟩ := hG
  exact ⟨_, hN.mul hM⟩

private theorem LP.const {tL : ℝ} (g : ℝ → ℂ) : LP tL (fun _ x => g x) := ⟨0, LocPoly.const g⟩

private theorem LP.cst {tL : ℝ} (c : ℂ) : LP tL (fun _ _ => c) := ⟨0, LocPoly.const (fun _ => c)⟩

private theorem LP.neg {tL : ℝ} {F : ℝ → ℝ → ℂ} (hF : LP tL F) : LP tL (fun t x => -F t x) := by
  have h := (LP.cst (tL := tL) (-1)).mul hF
  simpa using h

private theorem LP.sub {tL : ℝ} {F G : ℝ → ℝ → ℂ} (hF : LP tL F) (hG : LP tL G) :
    LP tL (fun t x => F t x - G t x) := by
  have h := hF.add hG.neg
  simpa [sub_eq_add_neg] using h

private theorem LP.tvar {tL : ℝ} : LP tL (fun t _ => (t : ℂ)) :=
  ⟨_, LocPoly.ofPoly Polynomial.X (fun t => (t : ℂ)) (fun t => by simp)⟩

private theorem LP.tpow {tL : ℝ} (k : ℕ) : LP tL (fun t _ => (t : ℂ) ^ k) :=
  ⟨_, LocPoly.ofPoly (Polynomial.X ^ k) (fun t => (t : ℂ) ^ k) (fun t => by simp)⟩

private theorem LP.tderiv {tL : ℝ} {F : ℝ → ℝ → ℂ} (hF : LP tL F) :
    LP tL (fun t x => deriv (fun t' => F t' x) t) := by
  obtain ⟨N, hN⟩ := hF
  exact ⟨N, hN.tderiv⟩

private theorem LP.xderiv {tL : ℝ} {F : ℝ → ℝ → ℂ} (hF : LP tL F) (htL : tL < 1)
    (hd : ∀ t, tL < t → t < 1 → ∀ x, DifferentiableAt ℝ (F t) x) :
    LP tL (fun t x => deriv (F t) x) := by
  obtain ⟨N, hN⟩ := hF
  exact ⟨N, hN.xderiv htL hd⟩

private theorem LP.quadQ (P : ChartParams) (tL : ℝ) : LP tL (fun t _ => ((chartQ P t : ℝ) : ℂ)) := by
  refine ⟨_, LocPoly.ofPoly (Polynomial.C ((P.L0 : ℂ) ^ 2) * Polynomial.X ^ 2 +
    Polynomial.C ((P.rc : ℂ) ^ 2) * (1 - Polynomial.X) ^ 2) (fun t => ((chartQ P t : ℝ) : ℂ)) (fun t => ?_)⟩
  simp [chartQ]

private theorem tail_bound (l : List ℝ) : ∃ tL : ℝ, 0 ≤ tL ∧ tL < 1 ∧ ∀ b ∈ l, b < 1 → b ≤ tL := by
  induction l with
  | nil => exact ⟨0, le_rfl, one_pos, by simp⟩
  | cons b l ih =>
    obtain ⟨tL, h0, h1, h⟩ := ih
    by_cases hb : b < 1
    · refine ⟨max b tL, le_max_of_le_right h0, max_lt hb h1, ?_⟩
      intro c hc hc1
      rcases List.mem_cons.1 hc with rfl | hc
      · exact le_max_left _ _
      · exact (h c hc hc1).trans (le_max_right _ _)
    · refine ⟨tL, h0, h1, ?_⟩
      intro c hc hc1
      rcases List.mem_cons.1 hc with rfl | hc
      · exact absurd hc1 hb
      · exact h c hc hc1

private theorem cellIndex_tail (l : List ℝ) (tL : ℝ) (hl : ∀ b ∈ l, b < 1 → b ≤ tL) (t t' : ℝ)
    (h1 : tL < t) (h2 : t < 1) (h1' : tL < t') (h2' : t' < 1) : cellIndex l t = cellIndex l t' := by
  unfold cellIndex
  congr 1
  apply List.filter_congr
  intro b hb
  have hb' : b ∈ l := List.mem_of_mem_drop (List.mem_of_mem_dropLast hb)
  by_cases hb1 : b < 1
  · have := hl b hb' hb1
    simp [show b ≤ t by linarith, show b ≤ t' by linarith]
  · simp [show ¬ b ≤ t by linarith, show ¬ b ≤ t' by linarith]

private theorem cellIndex_le (l : List ℝ) (u : ℝ) : cellIndex l u ≤ l.length := by
  unfold cellIndex
  refine (List.length_filter_le _ _).trans ?_
  simp
  omega

private def tPoly (c : ℂ) (Q : MvPolynomial (Fin 2) ℂ) : Polynomial ℂ :=
  ∑ d ∈ Q.support, Polynomial.C (MvPolynomial.coeff d Q * c ^ (d 1)) * Polynomial.X ^ (d 0)

private theorem tPoly_eval (c z : ℂ) (Q : MvPolynomial (Fin 2) ℂ) :
    (tPoly c Q).eval z = MvPolynomial.eval ![z, c] Q := by
  rw [MvPolynomial.eval_eq', tPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

private theorem tPoly_natDegree (c : ℂ) (Q : MvPolynomial (Fin 2) ℂ) :
    (tPoly c Q).natDegree ≤ Q.support.sup (fun d => d 0) :=
  Polynomial.natDegree_sum_le_of_forall_le _ _ fun _ hd =>
    (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Finset.le_sup (f := fun d : Fin 2 →₀ ℕ => d 0) hd)

private theorem spline_locPoly (S : Spline) (odd : Bool) :
    ∃ tL : ℝ, ∃ N : ℕ, 0 ≤ tL ∧ tL < 1 ∧ LocPoly tL N (fun t x => S.eval odd t x) := by
  obtain ⟨tL, h0, h1, hl⟩ := tail_bound S.mesh.tBreaks
  refine ⟨tL, (Finset.range (S.mesh.xBreaks.length + 1)).sup
    (fun j => (S.piece (cellIndex S.mesh.tBreaks ((tL + 1) / 2)) j).support.sup (fun d => d 0)), h0, h1, ?_⟩
  intro x
  have hj : cellIndex S.mesh.xBreaks |x| ≤ S.mesh.xBreaks.length := cellIndex_le _ _
  refine ⟨Polynomial.C (if odd && decide (x < 0) then -1 else 1) *
    tPoly ((|x| : ℝ) : ℂ) (S.piece (cellIndex S.mesh.tBreaks ((tL + 1) / 2)) (cellIndex S.mesh.xBreaks |x|)), ?_, ?_⟩
  · refine (Polynomial.natDegree_C_mul_le _ _).trans ((tPoly_natDegree _ _).trans ?_)
    exact Finset.le_sup (f := fun j => (S.piece (cellIndex S.mesh.tBreaks ((tL + 1) / 2)) j).support.sup
      (fun d => d 0)) (Finset.mem_range.2 (by omega))
  · intro t ht1 ht2
    have hi : cellIndex S.mesh.tBreaks t = cellIndex S.mesh.tBreaks ((tL + 1) / 2) :=
      cellIndex_tail _ _ hl _ _ ht1 ht2 (by linarith) (by linarith)
    simp only [Spline.eval, Spline.evalHalf, hi, Polynomial.eval_mul, Polynomial.eval_C, tPoly_eval]

private theorem spline_diffX (S : Spline) {a b : ℕ} {odd : Bool} (hS : IsSplineClass a b odd S) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (t x : ℝ) : DifferentiableAt ℝ (fun x' => S.eval odd t x') x := by
  have h := (spline_eval_contDiff S hS ha hb).differentiable (by norm_num)
  have hc : DifferentiableAt ℝ (fun x' : ℝ => (t, x')) x := (differentiableAt_const t).prodMk differentiableAt_id
  exact (h (t, x)).comp x hc

private theorem pow_deriv_one (e : ℕ) (t : ℝ) :
    HasDerivAt (fun t' : ℝ => (((1 - t') ^ e : ℝ) : ℂ)) ((-((e : ℝ) * (1 - t) ^ (e - 1)) : ℝ) : ℂ) t := by
  have h0 := (hasDerivAt_pow e (1 - t)).comp t ((hasDerivAt_id t).const_sub 1)
  have h : HasDerivAt (fun t' : ℝ => (1 - t') ^ e) ((e : ℝ) * (1 - t) ^ (e - 1) * (-1)) t := h0
  have h2 := h.ofReal_comp
  convert h2 using 1
  push_cast
  ring

private theorem twisted_eq (P : ChartParams) (hP : IsChartParams P) (e : ℕ) (n : ℤ) (β : ℝ) {tL : ℝ}
    {V : ℝ → ℝ → ℂ} (hV : LP tL V) (t x : ℝ) (h1 : tL < t) (h2 : t < 1) :
    ((chartQ P t : ℝ) : ℂ) * twistedScale P n β (fun t' x' => (((1 - t') ^ e : ℝ) : ℂ) * V t' x') t x =
      (((1 - t) ^ e : ℝ) : ℂ) * (((chartQ P t : ℝ) : ℂ) * ((-(e : ℂ) * t - 2 * (P.eps : ℂ) * t) * V t x +
        (t : ℂ) * (1 - t) * deriv (fun t' => V t' x) t) +
        Complex.I * ((n : ℂ) * β * (P.L0 : ℂ) ^ 2 * (t : ℂ) ^ 2) * V t x) := by
  obtain ⟨N, hN⟩ := hV
  have hd : HasDerivAt (fun t' => (((1 - t') ^ e : ℝ) : ℂ) * V t' x) _ t :=
    (pow_deriv_one e t).mul (hN.hasDerivAt x t h1 h2)
  unfold twistedScale radialScale
  beta_reduce
  rw [hd.deriv]
  have hQ : chartQ P t ≠ 0 := (chartQ_pos P hP t).ne'
  have hcr : coreRatioT P t = P.L0 ^ 2 * t ^ 2 / chartQ P t := rfl
  rw [hcr]
  have hQc : ((chartQ P t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hQ
  rcases e with _ | k
  · simp only [pow_zero, CharP.cast_eq_zero, zero_mul, neg_zero, Complex.ofReal_one, Complex.ofReal_zero, one_mul,
      zero_add]
    push_cast
    field_simp
    ring
  · simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

private def waveV (D : FieldData) (n : ℤ) (S : Spline) (odd : Bool) (t x : ℝ) : ℂ :=
  (t : ℂ) ^ D.lowOrder n * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * S.eval odd t x

private def waveW (D : FieldData) (n : ℤ) (S : Spline) (odd : Bool) (t x : ℝ) : ℂ :=
  ((1 - x ^ 2 : ℝ) : ℂ) * waveV D n S odd t x

private def meanV (S : Spline) (odd : Bool) (t x : ℝ) : ℂ := (t : ℂ) * S.eval odd t x

private def meanW (S : Spline) (t x : ℝ) : ℂ := ((1 - x ^ 2 : ℝ) : ℂ) * S.eval true t x

private theorem sq_diff (x : ℝ) : DifferentiableAt ℝ (fun x' : ℝ => ((1 - x' ^ 2 : ℝ) : ℂ)) x :=
  ((((hasDerivAt_id x).pow 2).const_sub 1).ofReal_comp).differentiableAt

private theorem far_wave (P : ChartParams) (hP : IsChartParams P) (D : FieldData)
    (c : ℝ) (n : ℤ) (hn0 : n ≠ 0) (hp : IsSplineClass 1 2 true (D.amp n).polarAmp) :
    ∃ tL : ℝ, 0 ≤ tL ∧ tL < 1 ∧ ∀ k : Fin 3, ∃ H : ℝ → ℝ → ℂ, LP tL H ∧ ∀ t x, tL < t → t < 1 →
      ((chartQ P t : ℝ) : ℂ) * reducedField P D n c t x k = (((1 - t) ^ D.highOrder : ℝ) : ℂ) * H t x := by
  obtain ⟨t1, N1, h10, h11, hS1⟩ := spline_locPoly (D.amp n).radialAmp false
  obtain ⟨t2, N2, h20, h21, hS2⟩ := spline_locPoly (D.amp n).polarAmp true
  have hS1' : LP (max t1 t2) (fun t x => (D.amp n).radialAmp.eval false t x) :=
    ⟨N1, hS1.mono (le_max_left _ _) le_rfl⟩
  have hS2' : LP (max t1 t2) (fun t x => (D.amp n).polarAmp.eval true t x) :=
    ⟨N2, hS2.mono (le_max_right _ _) le_rfl⟩
  have htL : max t1 t2 < 1 := max_lt h11 h21
  have hQ : LP (max t1 t2) (fun t _ => ((chartQ P t : ℝ) : ℂ)) := LP.quadQ P _
  have hVr : LP (max t1 t2) (waveV D n (D.amp n).radialAmp false) :=
    ((LP.tpow _).mul (LP.const (fun x => ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n))).mul hS1'
  have hVp : LP (max t1 t2) (waveV D n (D.amp n).polarAmp true) :=
    ((LP.tpow _).mul (LP.const (fun x => ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n))).mul hS2'
  have hdVr := hVr.tderiv
  have hdW : LP (max t1 t2) (fun t x => deriv (waveW D n (D.amp n).polarAmp true t) x) := by
    refine ((LP.const (fun x => ((1 - x ^ 2 : ℝ) : ℂ))).mul hVp).xderiv htL ?_
    intro t _ _ x
    have hs := spline_diffX _ hp (le_refl 1) (by norm_num) t x
    exact (sq_diff x).mul ((((differentiableAt_const _).mul ((sq_diff x).pow _))).mul hs)
  refine ⟨max t1 t2, le_max_of_le_left h10, htL, fun k => ?_⟩
  have hur : ∀ (S : Spline) (odd : Bool), (fun t' x' => weightPoly (D.lowOrder n) D.highOrder t' *
      ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * S.eval odd t' x') = fun t' x' =>
      (((1 - t') ^ D.highOrder : ℝ) : ℂ) * waveV D n S odd t' x' := by
    intro S odd
    funext t' x'
    simp only [weightPoly, waveV]
    push_cast
    ring
  have hpt : ∀ (S : Spline) (odd : Bool) (t x : ℝ), weightPoly (D.lowOrder n) D.highOrder t *
      ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * S.eval odd t x =
      (((1 - t) ^ D.highOrder : ℝ) : ℂ) * waveV D n S odd t x := fun S odd t x =>
    congrFun (congrFun (hur S odd) t) x
  fin_cases k
  · refine ⟨fun t x => ((chartQ P t : ℝ) : ℂ) * waveV D n (D.amp n).radialAmp false t x, hQ.mul hVr,
      fun t x _ _ => ?_⟩
    have r0 : reducedField P D n c t x 0 = weightPoly (D.lowOrder n) D.highOrder t *
        ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).radialAmp.eval false t x := by
      rw [reducedField, if_neg hn0]
      rfl
    show ((chartQ P t : ℝ) : ℂ) * reducedField P D n c t x 0 = _
    rw [r0, hpt]
    ring
  · refine ⟨fun t x => ((chartQ P t : ℝ) : ℂ) * waveV D n (D.amp n).polarAmp true t x, hQ.mul hVp,
      fun t x _ _ => ?_⟩
    have r1 : reducedField P D n c t x 1 = weightPoly (D.lowOrder n) D.highOrder t *
        ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).polarAmp.eval true t x := by
      rw [reducedField, if_neg hn0]
      rfl
    show ((chartQ P t : ℝ) : ℂ) * reducedField P D n c t x 1 = _
    rw [r1, hpt]
    ring
  · refine ⟨fun t x => Complex.I / ((n * P.m : ℤ) : ℂ) * ((((chartQ P t : ℝ) : ℂ) *
        ((-(D.highOrder : ℂ) * t - 2 * (P.eps : ℂ) * t) * waveV D n (D.amp n).radialAmp false t x +
        (t : ℂ) * (1 - t) * deriv (fun t' => waveV D n (D.amp n).radialAmp false t' x) t) +
        Complex.I * ((n : ℂ) * c * (P.L0 : ℂ) ^ 2 * (t : ℂ) ^ 2) * waveV D n (D.amp n).radialAmp false t x) +
        2 * (((chartQ P t : ℝ) : ℂ) * waveV D n (D.amp n).radialAmp false t x) -
        ((chartQ P t : ℝ) : ℂ) * deriv (waveW D n (D.amp n).polarAmp true t) x), ?_, fun t x h1 h2 => ?_⟩
    · repeat (first | exact hQ | exact hVr | exact hdVr | exact hdW | exact LP.tvar | exact LP.cst _ |
        exact LP.tpow _ | apply LP.add | apply LP.sub | apply LP.mul | apply LP.neg)
    · have r2 : reducedField P D n c t x 2 = (Complex.I / ((n * P.m : ℤ) : ℂ)) *
          (twistedScale P n c (fun t' x' => weightPoly (D.lowOrder n) D.highOrder t' *
            ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).radialAmp.eval false t' x') t x +
          2 * (weightPoly (D.lowOrder n) D.highOrder t * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
            (D.amp n).radialAmp.eval false t x) -
          heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly (D.lowOrder n) D.highOrder t' *
            ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).polarAmp.eval true t' x')) t x) := by
        rw [reducedField, if_neg hn0]
        rfl
      have hHD : heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly (D.lowOrder n) D.highOrder t' *
            ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).polarAmp.eval true t' x')) t x =
          (((1 - t) ^ D.highOrder : ℝ) : ℂ) * deriv (waveW D n (D.amp n).polarAmp true t) x := by
        unfold heightDeriv
        have hf : (fun x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly (D.lowOrder n) D.highOrder t *
            ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).polarAmp.eval true t x')) =
            fun x' => (((1 - t) ^ D.highOrder : ℝ) : ℂ) * waveW D n (D.amp n).polarAmp true t x' := by
          funext x'
          rw [hpt]
          simp only [waveW]
          ring
        beta_reduce
        rw [hf, deriv_const_mul_field']
      have htw := twisted_eq P hP D.highOrder n c hVr t x h1 h2
      show ((chartQ P t : ℝ) : ℂ) * reducedField P D n c t x 2 = _
      rw [r2, hur, hHD, hpt]
      linear_combination (Complex.I / ((n * P.m : ℤ) : ℂ)) * htw

private theorem far_mean (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (c : ℝ)
    (hs : IsSplineClass 2 2 true (D.amp 0).streamAmp) :
    ∃ tL : ℝ, 0 ≤ tL ∧ tL < 1 ∧ ∀ k : Fin 3, ∃ H : ℝ → ℝ → ℂ, LP tL H ∧ ∀ t x, tL < t → t < 1 →
      ((chartQ P t : ℝ) : ℂ) * reducedField P D 0 c t x k = (((1 - t) ^ D.highOrder : ℝ) : ℂ) * H t x := by
  obtain ⟨t1, N1, h10, h11, hS1⟩ := spline_locPoly (D.amp 0).streamAmp true
  obtain ⟨t2, N2, h20, h21, hS2⟩ := spline_locPoly (D.amp 0).swirlAmp false
  have hS1' : LP (max t1 t2) (fun t x => (D.amp 0).streamAmp.eval true t x) :=
    ⟨N1, hS1.mono (le_max_left _ _) le_rfl⟩
  have hS2' : LP (max t1 t2) (fun t x => (D.amp 0).swirlAmp.eval false t x) :=
    ⟨N2, hS2.mono (le_max_right _ _) le_rfl⟩
  have htL : max t1 t2 < 1 := max_lt h11 h21
  have hQ : LP (max t1 t2) (fun t _ => ((chartQ P t : ℝ) : ℂ)) := LP.quadQ P _
  have hV : LP (max t1 t2) (meanV (D.amp 0).streamAmp true) := LP.tvar.mul hS1'
  have hG : LP (max t1 t2) (meanV (D.amp 0).swirlAmp false) := LP.tvar.mul hS2'
  have hdV := hV.tderiv
  have hdW : LP (max t1 t2) (fun t x => deriv (meanW (D.amp 0).streamAmp t) x) := by
    refine ((LP.const (fun x => ((1 - x ^ 2 : ℝ) : ℂ))).mul hS1').xderiv htL ?_
    intro t _ _ x
    exact (sq_diff x).mul (spline_diffX _ hs (by norm_num) (by norm_num) t x)
  refine ⟨max t1 t2, le_max_of_le_left h10, htL, fun k => ?_⟩
  have hw : ∀ t : ℝ, weightPoly 1 D.highOrder t = (((1 - t) ^ D.highOrder : ℝ) : ℂ) * (t : ℂ) := by
    intro t
    simp only [weightPoly]
    push_cast
    ring
  fin_cases k
  · refine ⟨fun t x => -(((chartQ P t : ℝ) : ℂ) * (t : ℂ) * deriv (meanW (D.amp 0).streamAmp t) x),
      (hQ.mul LP.tvar).mul hdW |>.neg, fun t x _ _ => ?_⟩
    have r0 : reducedField P D 0 c t x 0 = -(weightPoly 1 D.highOrder t *
        heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (D.amp 0).streamAmp.eval true t' x') t x) := by
      rw [reducedField, if_pos rfl]
      rfl
    have hHD : heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (D.amp 0).streamAmp.eval true t' x') t x =
        deriv (meanW (D.amp 0).streamAmp t) x := rfl
    show ((chartQ P t : ℝ) : ℂ) * reducedField P D 0 c t x 0 = _
    rw [r0, hHD, hw]
    ring
  · refine ⟨fun t x => -((((chartQ P t : ℝ) : ℂ) *
        ((-(D.highOrder : ℂ) * t - 2 * (P.eps : ℂ) * t) * meanV (D.amp 0).streamAmp true t x +
        (t : ℂ) * (1 - t) * deriv (fun t' => meanV (D.amp 0).streamAmp true t' x) t) +
        Complex.I * (((0 : ℤ) : ℂ) * c * (P.L0 : ℂ) ^ 2 * (t : ℂ) ^ 2) * meanV (D.amp 0).streamAmp true t x) +
        2 * (((chartQ P t : ℝ) : ℂ) * meanV (D.amp 0).streamAmp true t x)), ?_, fun t x h1 h2 => ?_⟩
    · repeat (first | exact hQ | exact hV | exact hdV | exact LP.tvar | exact LP.cst _ |
        exact LP.tpow _ | apply LP.add | apply LP.sub | apply LP.mul | apply LP.neg)
    · have hur : (fun t' x' => weightPoly 1 D.highOrder t' * (D.amp 0).streamAmp.eval true t' x') =
          fun t' x' => (((1 - t') ^ D.highOrder : ℝ) : ℂ) * meanV (D.amp 0).streamAmp true t' x' := by
        funext t' x'
        rw [hw]
        simp only [meanV]
        ring
      have r1 : reducedField P D 0 c t x 1 = -(twistedScale P 0 c
          (fun t' x' => weightPoly 1 D.highOrder t' * (D.amp 0).streamAmp.eval true t' x') t x +
          2 * (weightPoly 1 D.highOrder t * (D.amp 0).streamAmp.eval true t x)) := by
        rw [reducedField, if_pos rfl]
        rfl
      have htw := twisted_eq P hP D.highOrder 0 c hV t x h1 h2
      show ((chartQ P t : ℝ) : ℂ) * reducedField P D 0 c t x 1 = _
      rw [r1, hur, hw]
      simp only [meanV] at htw ⊢
      linear_combination -htw
  · refine ⟨fun t x => ((chartQ P t : ℝ) : ℂ) * meanV (D.amp 0).swirlAmp false t x, hQ.mul hG,
      fun t x _ _ => ?_⟩
    have r2 : reducedField P D 0 c t x 2 = weightPoly 1 D.highOrder t * (D.amp 0).swirlAmp.eval false t x := by
      rw [reducedField, if_pos rfl]
      rfl
    show ((chartQ P t : ℝ) : ℂ) * reducedField P D 0 c t x 2 = _
    rw [r2, hw]
    simp only [meanV]
    ring

private theorem split_parts {tL : ℝ} {N : ℕ} {H : ℝ → ℝ → ℂ} (hH : LocPoly tL N H) (x : ℝ) :
    ∃ p q : Polynomial ℝ, p.degree < ((N + 1 : ℕ) : WithBot ℕ) ∧ q.degree < ((N + 1 : ℕ) : WithBot ℕ) ∧
      ∀ t, tL < t → t < 1 → H t x = ((p.eval t : ℝ) : ℂ) + Complex.I * ((q.eval t : ℝ) : ℂ) := by
  obtain ⟨Q, hQ, hHQ⟩ := hH x
  have hdeg : ∀ f : ℕ → ℝ, (∑ i ∈ Finset.range (N + 1), Polynomial.C (f i) * Polynomial.X ^ i).degree <
      ((N + 1 : ℕ) : WithBot ℕ) := by
    intro f
    refine (Polynomial.degree_le_of_natDegree_le (Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi =>
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))).trans_lt ?_
    exact_mod_cast Nat.lt_succ_self N
  refine ⟨∑ i ∈ Finset.range (N + 1), Polynomial.C (Q.coeff i).re * Polynomial.X ^ i,
    ∑ i ∈ Finset.range (N + 1), Polynomial.C (Q.coeff i).im * Polynomial.X ^ i, hdeg _, hdeg _, ?_⟩
  intro t h1 h2
  rw [hHQ t h1 h2, Polynomial.eval_eq_sum_range' (n := N + 1) (by omega)]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [← Complex.re_add_im (Q.coeff i)]
  ring

private theorem reducedField_far_poly (P : ChartParams) (hP : IsChartParams P) (e : ℕ) (D : FieldData)
    (hD : IsFieldData P e D) (c : ℝ) (n : ℤ) (hn : n ∈ D.modes) :
    ∃ (tL : ℝ) (K : ℕ), 0 ≤ tL ∧ tL < 1 ∧ ∀ (x : ℝ) (k : Fin 3), ∃ p q : Polynomial ℝ,
      p.degree < K ∧ q.degree < K ∧ ∀ t : ℝ, tL < t → t < 1 →
        ((chartQ P t : ℝ) : ℂ) * reducedField P D n c t x k =
          (((1 - t) ^ e : ℝ) : ℂ) * (((p.eval t : ℝ) : ℂ) + Complex.I * ((q.eval t : ℝ) : ℂ)) := by
  have hcomp : ∃ tL : ℝ, 0 ≤ tL ∧ tL < 1 ∧ ∀ k : Fin 3, ∃ H : ℝ → ℝ → ℂ, LP tL H ∧ ∀ t x, tL < t → t < 1 →
      ((chartQ P t : ℝ) : ℂ) * reducedField P D n c t x k = (((1 - t) ^ D.highOrder : ℝ) : ℂ) * H t x := by
    by_cases hn0 : n = 0
    · subst hn0
      exact far_mean P hP D c (hD.meanStream hn).1
    · exact far_wave P hP D c n hn0 (hD.wavePolar n hn hn0)
  rw [hD.highOrder_eq] at hcomp
  obtain ⟨tL, h0, h1, hk⟩ := hcomp
  choose H hH hid using hk
  choose N hN using hH
  refine ⟨tL, N 0 + N 1 + N 2 + 1, h0, h1, fun x k => ?_⟩
  have hNk : N k ≤ N 0 + N 1 + N 2 := by
    fin_cases k <;> simp <;> omega
  obtain ⟨p, q, hp, hq, hpq⟩ := split_parts ((hN k).mono le_rfl hNk) x
  refine ⟨p, q, hp, hq, fun t ht1 ht2 => ?_⟩
  rw [hid k t x ht1 ht2, hpq t ht1 ht2]

private theorem interp_real (K : ℕ) (T : Fin K → ℝ) (hT : Function.Injective T) (p : Polynomial ℝ)
    (hp : p.degree < K) (t : ℝ) :
    p.eval t = ∑ j, p.eval (T j) * (Lagrange.basis Finset.univ T j).eval t := by
  have h := Lagrange.eq_interpolate (s := Finset.univ) (v := T) (f := p) (hT.injOn) (by simpa using hp)
  conv_lhs => rw [h]
  simp [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, mul_comm]

private theorem reducedField_far_interp (P : ChartParams) (hP : IsChartParams P) (e : ℕ) (D : FieldData)
    (hD : IsFieldData P e D) (c : ℝ) (n : ℤ) (hn : n ∈ D.modes) :
    ∃ (tL : ℝ) (K : ℕ) (T : Fin K → ℝ) (p : Fin K → Polynomial ℝ), 0 ≤ tL ∧ tL < 1 ∧
      (∀ j, tL < T j ∧ T j < 1) ∧ ∀ t, tL < t → t < 1 → ∀ x k,
        reducedField P D n c t x k = ∑ j, (((1 - t) ^ e / chartQ P t * (p j).eval t : ℝ) : ℂ) *
          reducedField P D n c (T j) x k := by
  obtain ⟨tL, K, h0, h1, hpoly⟩ := reducedField_far_poly P hP e D hD c n hn
  set T : Fin K → ℝ := fun j => 1 - (1 - tL) / ((j : ℕ) + 2 : ℝ) with hTdef
  have hd : 0 < 1 - tL := by linarith
  have hTin : ∀ j, tL < T j ∧ T j < 1 := by
    intro j
    have hj : (2 : ℝ) ≤ (j : ℕ) + 2 := by have := (Nat.cast_nonneg (α := ℝ) (j : ℕ)); linarith
    have hpos : 0 < (1 - tL) / ((j : ℕ) + 2 : ℝ) := by positivity
    have hlt : (1 - tL) / ((j : ℕ) + 2 : ℝ) < 1 - tL := by
      rw [div_lt_iff₀ (by linarith)]
      nlinarith
    simp only [hTdef]
    constructor <;> linarith
  have hTinj : Function.Injective T := by
    intro i j hij
    simp only [hTdef] at hij
    have h2 : (1 - tL) / ((i : ℕ) + 2 : ℝ) = (1 - tL) / ((j : ℕ) + 2 : ℝ) := by linarith
    have hi : (0 : ℝ) < (i : ℕ) + 2 := by positivity
    have hj : (0 : ℝ) < (j : ℕ) + 2 := by positivity
    rw [div_eq_div_iff hi.ne' hj.ne'] at h2
    have h3 : ((i : ℕ) : ℝ) = (j : ℕ) := by
      have := mul_left_cancel₀ hd.ne' (by linarith : (1 - tL) * ((j : ℕ) + 2 : ℝ) = (1 - tL) * ((i : ℕ) + 2 : ℝ))
      linarith
    exact Fin.ext (by exact_mod_cast h3)
  refine ⟨tL, K, T, fun j => Polynomial.C (chartQ P (T j) / (1 - T j) ^ e) * Lagrange.basis Finset.univ T j,
    h0, h1, hTin, fun t ht1 ht2 x k => ?_⟩
  obtain ⟨p, q, hp, hq, hpq⟩ := hpoly x k
  have hQ : ∀ s, ((chartQ P s : ℝ) : ℂ) ≠ 0 := fun s => Complex.ofReal_ne_zero.2 (chartQ_pos P hP s).ne'
  have hE : ∀ s : ℝ, s < 1 → (((1 - s) ^ e : ℝ) : ℂ) ≠ 0 := fun s hs =>
    Complex.ofReal_ne_zero.2 (pow_ne_zero _ (by linarith))
  have hred : ∀ s, tL < s → s < 1 → reducedField P D n c s x k =
      (((1 - s) ^ e : ℝ) : ℂ) / ((chartQ P s : ℝ) : ℂ) * (((p.eval s : ℝ) : ℂ) + Complex.I * ((q.eval s : ℝ) : ℂ)) := by
    intro s hs1 hs2
    rw [div_mul_eq_mul_div, eq_div_iff (hQ s), mul_comm, hpq s hs1 hs2]
  rw [hred t ht1 ht2, interp_real K T hTinj p hp t, interp_real K T hTinj q hq t]
  have hnode : ∀ j, reducedField P D n c (T j) x k =
      (((1 - T j) ^ e : ℝ) : ℂ) / ((chartQ P (T j) : ℝ) : ℂ) *
        (((p.eval (T j) : ℝ) : ℂ) + Complex.I * ((q.eval (T j) : ℝ) : ℂ)) := fun j => hred (T j) (hTin j).1 (hTin j).2
  simp_rw [hnode]
  push_cast
  rw [Finset.mul_sum (a := Complex.I), ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  push_cast
  have a1 := hQ t
  have a2 := hQ (T j)
  have a3 := hE (T j) (hTin j).2
  push_cast at a1 a2 a3
  field_simp


private theorem norm_smul_pos {s : ℝ} (hs : 0 < s) (y : Space) : ‖s • y‖ = s * ‖y‖ := by
  rw [norm_smul, Real.norm_of_nonneg hs.le]

private theorem height_smul {s : ℝ} (hs : 0 < s) (y : Space) : heightRatio (s • y) = heightRatio y := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [smul_zero]
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  unfold heightRatio
  rw [norm_smul_pos hs, PiLp.smul_apply, smul_eq_mul]
  field_simp

private theorem radial_smul {s : ℝ} (hs : 0 < s) (y : Space) (i : Fin 3) : radialVec (s • y) i = radialVec y i := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [smul_zero]
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  unfold radialVec
  rw [norm_smul_pos hs, PiLp.smul_apply, smul_eq_mul]
  field_simp

private theorem polar_smul {s : ℝ} (hs : 0 < s) (y : Space) (i : Fin 3) : polarVecQ (s • y) i = polarVecQ y i := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [smul_zero]
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  unfold polarVecQ qOf
  rw [height_smul hs, norm_smul_pos hs]
  fin_cases i <;> simp [PiLp.smul_apply] <;> field_simp

private theorem azim_smul {s : ℝ} (hs : 0 < s) (y : Space) (i : Fin 3) : azimVecQ (s • y) i = azimVecQ y i := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [smul_zero]
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  unfold azimVecQ
  rw [norm_smul_pos hs]
  fin_cases i <;> simp [PiLp.smul_apply] <;> field_simp

private theorem angle_smul {s : ℝ} (hs : 0 < s) (y : Space) : angleOf (s • y) = angleOf y := by
  unfold angleOf
  have h : (⟨(s • y) 0, (s • y) 1⟩ : ℂ) = (s : ℂ) * ⟨y 0, y 1⟩ := by
    apply Complex.ext <;> simp [PiLp.smul_apply]
  rw [h, Complex.arg_real_mul _ hs]

private theorem innerAt_smul (P : ChartParams) (D : FieldData) (β : ℝ) (n : ℤ) (R : ℝ) {s : ℝ} (hs : 0 < s)
    (y : Space) (i : Fin 3) : innerAt P D β n R (s • y) i = innerAt P D β n R y i := by
  unfold innerAt
  rw [angle_smul hs, height_smul hs, radial_smul hs, polar_smul hs, azim_smul hs]

private theorem scale_dir {s : ℝ} (hs : 0 < s) (R : ℝ) (y : Space) :
    (R / ‖s • y‖) • (s • y) = (R / ‖y‖) • y := by
  rw [norm_smul_pos hs, smul_smul]
  rcases eq_or_ne ‖y‖ 0 with h | h
  · simp [h]
  · congr 1
    field_simp

private theorem norm_dir {R : ℝ} (hR : 0 < R) {y : Space} (hy : y ≠ 0) : ‖(R / ‖y‖) • y‖ = R := by
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  rw [norm_smul, Real.norm_of_nonneg (div_pos hR hn).le, div_mul_cancel₀ _ hn.ne']

private theorem exp_split (A B : ℝ) :
    Complex.exp (Complex.I * ((A + B : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (A : ℂ)) * Complex.exp (Complex.I * (B : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem modeField_diff (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) (y : Space) :
    DifferentiableAt ℝ (modeFieldOf P D β n) y := by
  by_cases h0 : n = 0
  · subst h0
    by_cases hy : y = 0
    · subst hy
      exact (modeFieldOf_contDiffAt_origin_mean P hP hD β hn).differentiableAt (by norm_num)
    · have hph : modePhase P 0 β = fun _ => 1 := by
        funext z
        simp [modePhase]
      refine (modeFieldOf_contDiffAt_of P hP D β 0 (reducedField_mean_contDiff P hP hD β hn) y hy ?_).differentiableAt
        (by norm_num)
      rw [hph]
      exact contDiffAt_const
  · by_cases hy : y = 0
    · subst hy
      exact (modeFieldOf_contDiffAt_origin_wave P hP hD β n hn h0).differentiableAt (by norm_num)
    · exact (modeFieldOf_contDiffAt_axis_of P hP hD β n hn h0 y hy).differentiableAt (by norm_num)

private theorem modeField_slope (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) :
    LocallyLipschitz (fderiv ℝ (modeFieldOf P D β n)) := by
  by_cases h0 : n = 0
  · subst h0
    exact modeFieldOf_fderiv_localSlope_mean P hP hD β hn
  · exact modeFieldOf_fderiv_localSlope_wave P hP hD β n hn h0

private theorem ofComponents_pair (K : ℕ) (f g : Fin K → ℝ) (u v : Fin K → Fin 3 → ℝ) :
    ofComponents (fun i => ∑ j, (f j * u j i + g j * v j i)) =
      ∑ j, (f j • ofComponents (u j) + g j • ofComponents (v j)) := by
  ext l
  fin_cases l <;> simp [ofComponents, Finset.sum_add_distrib]

private theorem turn_apply (φ : ℝ) (y : Space) :
    turnVec φ y 0 = Real.cos φ * y 0 - Real.sin φ * y 1 ∧ turnVec φ y 1 = Real.sin φ * y 0 + Real.cos φ * y 1 ∧
      turnVec φ y 2 = y 2 := by
  simp [turnVec, ofComponents]

private theorem turn_norm (φ : ℝ) (y : Space) : ‖turnVec φ y‖ = ‖y‖ := by
  have h : ‖turnVec φ y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_three]
    obtain ⟨h0, h1, h2⟩ := turn_apply φ y
    simp only [Real.norm_eq_abs, sq_abs, h0, h1, h2]
    linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq φ
  rw [← Real.sqrt_sq (norm_nonneg (turnVec φ y)), h, Real.sqrt_sq (norm_nonneg y)]

private theorem height_turn (φ : ℝ) (y : Space) : heightRatio (turnVec φ y) = heightRatio y := by
  unfold heightRatio
  rw [turn_norm, (turn_apply φ y).2.2]

private theorem frame_turn (φ : ℝ) (y : Space) :
    (radialVec (turnVec φ y) 0 = Real.cos φ * radialVec y 0 - Real.sin φ * radialVec y 1 ∧
      radialVec (turnVec φ y) 1 = Real.sin φ * radialVec y 0 + Real.cos φ * radialVec y 1 ∧
      radialVec (turnVec φ y) 2 = radialVec y 2) ∧
    (polarVecQ (turnVec φ y) 0 = Real.cos φ * polarVecQ y 0 - Real.sin φ * polarVecQ y 1 ∧
      polarVecQ (turnVec φ y) 1 = Real.sin φ * polarVecQ y 0 + Real.cos φ * polarVecQ y 1 ∧
      polarVecQ (turnVec φ y) 2 = polarVecQ y 2) ∧
    (azimVecQ (turnVec φ y) 0 = Real.cos φ * azimVecQ y 0 - Real.sin φ * azimVecQ y 1 ∧
      azimVecQ (turnVec φ y) 1 = Real.sin φ * azimVecQ y 0 + Real.cos φ * azimVecQ y 1 ∧
      azimVecQ (turnVec φ y) 2 = azimVecQ y 2) := by
  obtain ⟨h0, h1, h2⟩ := turn_apply φ y
  have hh := height_turn φ y
  simp only [radialVec, polarVecQ, azimVecQ, qOf, turn_norm, h0, h1, h2, hh]
  simp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> ring

private theorem exp_arg_pow (w : ℂ) (hw : w ≠ 0) (k : ℤ) :
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

private theorem angle_turn (φ : ℝ) (y : Space) (hw : (⟨y 0, y 1⟩ : ℂ) ≠ 0) (k : ℤ) :
    Complex.exp (Complex.I * (((k : ℝ) * angleOf (turnVec φ y) : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (((k : ℝ) * φ : ℝ) : ℂ)) * Complex.exp (Complex.I * (((k : ℝ) * angleOf y : ℝ) : ℂ)) := by
  set w : ℂ := ⟨y 0, y 1⟩ with hwd
  set u : ℂ := Complex.exp ((φ : ℂ) * Complex.I) with hu
  have hzu : (⟨turnVec φ y 0, turnVec φ y 1⟩ : ℂ) = u * w := by
    obtain ⟨h0, h1, -⟩ := turn_apply φ y
    rw [hu, Complex.exp_mul_I]
    apply Complex.ext
    · simp [h0, hwd, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    · simp [h1, hwd, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      ring
  have hu1 : ‖u‖ = 1 := by rw [hu]; exact Complex.norm_exp_ofReal_mul_I φ
  have hu0 : u ≠ 0 := by rw [hu]; exact Complex.exp_ne_zero _
  unfold angleOf
  rw [hzu, exp_arg_pow _ (mul_ne_zero hu0 hw), exp_arg_pow _ hw, norm_mul, hu1, one_mul]
  have e1 : u * w * ((‖w‖⁻¹ : ℝ) : ℂ) = u * (w * ((‖w‖⁻¹ : ℝ) : ℂ)) := by ring
  rw [e1, mul_zpow]
  congr 1
  rw [hu, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

private theorem turn_eq (P : ChartParams) (hP : IsChartParams P) (e : ℕ) (D : FieldData)
    (hD : IsFieldData P e D) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) (φ : ℝ) (y : Space) (hy : y ≠ 0) :
    modeFieldOf P D β n (turnVec φ y) = turnVec φ (ofComponents (fun i =>
      (Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * φ : ℝ) : ℂ)) * innerAt P D β n ‖y‖ y i).re)) := by
  rw [modeFieldOf_eq_innerAt, turn_norm]
  set E := Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * φ : ℝ) : ℂ)) with hE
  set V := innerAt P D β n ‖y‖ y with hV
  obtain ⟨⟨r0, r1, r2⟩, ⟨p0, p1, p2⟩, ⟨a0, a1, a2⟩⟩ := frame_turn φ y
  have key : innerAt P D β n ‖y‖ (turnVec φ y) 0 = E * (Real.cos φ * V 0 - Real.sin φ * V 1) ∧
      innerAt P D β n ‖y‖ (turnVec φ y) 1 = E * (Real.sin φ * V 0 + Real.cos φ * V 1) ∧
      innerAt P D β n ‖y‖ (turnVec φ y) 2 = E * V 2 := by
    by_cases hax : n ≠ 0 ∧ (⟨y 0, y 1⟩ : ℂ) = 0
    · obtain ⟨H, -, hRH⟩ := reducedField_wave_axisFactor_slope P hP hD β n hn hax.1
      have h01 : y 0 = 0 ∧ y 1 = 0 := ⟨congrArg Complex.re hax.2, congrArg Complex.im hax.2⟩
      have hq : 1 - heightRatio y ^ 2 = 0 := by
        have hn2 : ‖y‖ ^ 2 = y 2 ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
          simp [h01.1, h01.2]
        have hne : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
        unfold heightRatio
        rw [div_pow, ← hn2, div_self (pow_ne_zero 2 hne), sub_self]
      have hz : ∀ t k, reducedField P D n β t (heightRatio y) k = 0 := by
        intro t k
        rw [hRH, hq]
        simp
      simp only [hV, innerAt, height_turn, hz]
      simp
    · have hph : ∀ A : ℝ, Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * angleOf (turnVec φ y) + A : ℝ) : ℂ)) =
          E * Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * angleOf y + A : ℝ) : ℂ)) := by
        intro A
        rw [exp_split, exp_split, hE]
        by_cases h0 : n = 0
        · subst h0
          simp
        · have hw : (⟨y 0, y 1⟩ : ℂ) ≠ 0 := fun h => hax ⟨h0, h⟩
          rw [angle_turn φ y hw]
          ring
      simp only [hV, innerAt, height_turn, hph, r0, r1, r2, p0, p1, p2, a0, a1, a2]
      push_cast
      refine ⟨?_, ?_, ?_⟩ <;> ring
  obtain ⟨k0, k1, k2⟩ := key
  generalize hW : innerAt P D β n ‖y‖ (turnVec φ y) = W at k0 k1 k2 ⊢
  ext l
  fin_cases l <;> simp [turnVec, ofComponents, k0, k1, k2, Complex.mul_re, Complex.cos_ofReal_re,
    Complex.sin_ofReal_re] <;> ring

private theorem turn_turn (φ : ℝ) (y : Space) : turnVec (-φ) (turnVec φ y) = y := by
  ext i
  fin_cases i <;> simp [turnVec, ofComponents, Real.cos_neg, Real.sin_neg]
  · linear_combination (y 0) * Real.sin_sq_add_cos_sq φ
  · linear_combination (y 1) * Real.sin_sq_add_cos_sq φ

private def turnLin (φ : ℝ) : Space →ₗ[ℝ] Space where
  toFun := turnVec φ
  map_add' y z := by
    ext i
    fin_cases i <;> simp [turnVec, ofComponents] <;> ring
  map_smul' s y := by
    ext i
    fin_cases i <;> simp [turnVec, ofComponents] <;> ring

private def turnCLM (φ : ℝ) : Space →L[ℝ] Space := LinearMap.toContinuousLinearMap (turnLin φ)

private theorem turnCLM_apply (φ : ℝ) (y : Space) : turnCLM φ y = turnVec φ y := rfl

private theorem slopeAt_comp {f g : Space → (Space →L[ℝ] Space)} {x : Space}
    (hf : ∃ K, ∃ t ∈ nhds x, LipschitzOnWith K f t) (hg : ∃ K, ∃ t ∈ nhds x, LipschitzOnWith K g t) :
    ∃ K, ∃ t ∈ nhds x, LipschitzOnWith K (fun z => (f z).comp (g z)) t := by
  obtain ⟨K1, t1, ht1, h1⟩ := hf
  obtain ⟨K2, t2, ht2, h2⟩ := hg
  have hb : Metric.ball x 1 ∈ nhds x := Metric.ball_mem_nhds x one_pos
  set s := t1 ∩ t2 ∩ Metric.ball x 1
  have hs : s ∈ nhds x := Filter.inter_mem (Filter.inter_mem ht1 ht2) hb
  have hx : x ∈ s := mem_of_mem_nhds hs
  have bf : ∀ z ∈ s, ‖f z‖ ≤ ‖f x‖ + K1 := by
    intro z hz
    have d := h1.dist_le_mul z hz.1.1 x hx.1.1
    have dz : dist z x < 1 := hz.2
    rw [dist_eq_norm] at d
    have := norm_le_insert' (f z) (f x)
    nlinarith [K1.2, norm_nonneg (f z - f x)]
  have bg : ∀ z ∈ s, ‖g z‖ ≤ ‖g x‖ + K2 := by
    intro z hz
    have d := h2.dist_le_mul z hz.1.2 x hx.1.2
    have dz : dist z x < 1 := hz.2
    rw [dist_eq_norm] at d
    have := norm_le_insert' (g z) (g x)
    nlinarith [K2.2, norm_nonneg (g z - g x)]
  refine ⟨Real.toNNReal (K1 * (‖g x‖ + K2) + (‖f x‖ + K1) * K2), s, hs,
    LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_⟩
  have hK1 := K1.2
  have hK2 := K2.2
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm]
  have e : (f z).comp (g z) - (f w).comp (g w) = (f z - f w).comp (g z) + (f w).comp (g z - g w) := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  have d1 := h1.dist_le_mul z hz.1.1 w hw.1.1
  have d2 := h2.dist_le_mul z hz.1.2 w hw.1.2
  rw [dist_eq_norm] at d1 d2
  rw [e]
  have hd := dist_nonneg (x := z) (y := w)
  calc _ ≤ ‖(f z - f w).comp (g z)‖ + ‖(f w).comp (g z - g w)‖ := norm_add_le _ _
    _ ≤ ‖f z - f w‖ * ‖g z‖ + ‖f w‖ * ‖g z - g w‖ :=
        add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ (K1 * dist z w) * (‖g x‖ + K2) + (‖f x‖ + K1) * (K2 * dist z w) :=
        add_le_add (mul_le_mul d1 (bg z hz) (norm_nonneg _) (by positivity))
          (mul_le_mul (bf w hw) d2 (norm_nonneg _) (by positivity))
    _ = _ := by ring

private theorem slopeAt_const (A : Space →L[ℝ] Space) (x : Space) :
    ∃ K, ∃ t ∈ nhds x, LipschitzOnWith K (fun _ : Space => A) t :=
  ⟨0, Set.univ, Filter.univ_mem, LipschitzOnWith.of_dist_le_mul fun z _ w _ => by simp⟩

private theorem dir_smooth (R : ℝ) {y : Space} (hy : y ≠ 0) : ContDiffAt ℝ ⊤ (fun z : Space => (R / ‖z‖) • z) y :=
  (contDiffAt_const.div (contDiffAt_norm ℝ hy) (norm_ne_zero_iff.2 hy)).smul contDiffAt_id

private theorem angular_regular (F : Space → Space) (hF : ∀ y, DifferentiableAt ℝ F y)
    (hFl : LocallyLipschitz (fderiv ℝ F)) (L M : Space →L[ℝ] Space) (R : ℝ) :
    (∀ y : Space, y ≠ 0 → DifferentiableAt ℝ (fun z : Space => L (F (M ((R / ‖z‖) • z)))) y) ∧
    LocallyLipschitzOn {y : Space | y ≠ 0} (fderiv ℝ (fun z : Space => L (F (M ((R / ‖z‖) • z))))) := by
  set G : Space → Space := fun z => (R / ‖z‖) • z with hG
  have hGd : ∀ y : Space, y ≠ 0 → DifferentiableAt ℝ G y := fun y hy =>
    (dir_smooth R hy).differentiableAt (by simp)
  have hder : ∀ y : Space, y ≠ 0 → HasFDerivAt (fun z : Space => L (F (M (G z))))
      (L.comp ((fderiv ℝ F (M (G y))).comp (M.comp (fderiv ℝ G y)))) y := fun y hy =>
    L.hasFDerivAt.comp y ((hF _).hasFDerivAt.comp y (M.hasFDerivAt.comp y (hGd y hy).hasFDerivAt))
  refine ⟨fun y hy => (hder y hy).differentiableAt, ?_⟩
  intro y hy
  have hy0 : y ≠ 0 := hy
  have hB : ∃ K, ∃ t ∈ nhds y, LipschitzOnWith K (fderiv ℝ G) t :=
    ((dir_smooth R hy0).fderiv_right (m := 1) (by simp)).exists_lipschitzOnWith
  have hA : ∃ K, ∃ t ∈ nhds y, LipschitzOnWith K (fun z => fderiv ℝ F (M (G z))) t := by
    obtain ⟨K1, t1, ht1, h1⟩ := hFl (M (G y))
    have hMG : ContDiffAt ℝ 1 (fun z => M (G z)) y :=
      (M.contDiff.contDiffAt.comp y ((dir_smooth R hy0).of_le le_top))
    obtain ⟨K2, t2, ht2, h2⟩ := hMG.exists_lipschitzOnWith
    have hpre : (fun z => M (G z)) ⁻¹' t1 ∈ nhds y :=
      hMG.continuousAt.preimage_mem_nhds ht1
    refine ⟨K1 * K2, t2 ∩ (fun z => M (G z)) ⁻¹' t1, Filter.inter_mem ht2 hpre, ?_⟩
    exact h1.comp (h2.mono Set.inter_subset_left) (fun z hz => hz.2)
  obtain ⟨K, t, ht, hK⟩ := slopeAt_comp (slopeAt_const L y) (slopeAt_comp hA (slopeAt_comp (slopeAt_const M y) hB))
  have hne : {z : Space | z ≠ 0} ∈ nhds y := isOpen_ne.mem_nhds hy0
  refine ⟨K, t ∩ {z : Space | z ≠ 0}, mem_nhdsWithin_of_mem_nhds (Filter.inter_mem ht hne), ?_⟩
  have hmono : LipschitzOnWith K (fun z => L.comp ((fderiv ℝ F (M (G z))).comp (M.comp (fderiv ℝ G z))))
      (t ∩ {z : Space | z ≠ 0}) := hK.mono Set.inter_subset_left
  intro a ha b hb
  have ea := (hder a ha.2).fderiv
  have eb := (hder b hb.2).fderiv
  simp only [hG] at ea eb hmono ⊢
  rw [ea, eb]
  exact hmono ha hb

private theorem re_form (a : ℂ) (g θ : ℝ) :
    (a * ((g : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re = g * (a.re * Real.cos θ - a.im * Real.sin θ) := by
  rw [mul_comm Complex.I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private theorem abs_mul2_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

private theorem abs_mul3_le {a b c A B C : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) :
    |a * b * c| ≤ A * B * C :=
  abs_mul2_le (abs_mul2_le ha hb) hc

private theorem pow_to_r {L r β γ j s : ℝ} (hL : 0 < L) (hr : 1 < r) (hβγ : γ ≤ β) (hβ : 0 ≤ β) (hj : 0 ≤ j)
    (hs : 0 < s) (hsr : s ≤ L / r) : s ^ (β + j) ≤ L ^ (β + j) * r ^ (-(γ + j)) := by
  have hr0 : 0 < r := by linarith
  calc s ^ (β + j) ≤ (L / r) ^ (β + j) := Real.rpow_le_rpow hs.le hsr (by linarith)
    _ = L ^ (β + j) * r ^ (-(β + j)) := by
      rw [Real.div_rpow hL.le hr0.le, Real.rpow_neg hr0.le, div_eq_mul_inv]
    _ ≤ L ^ (β + j) * r ^ (-(γ + j)) := by
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hr.le (by linarith)) (by positivity)

private theorem sigma_facts (L r : ℝ) (hL : 0 < L) (hr : 1 < r) :
    1 - r / (r + L) = L / (r + L) ∧ 0 < 1 - r / (r + L) ∧ 1 - r / (r + L) < 1 ∧ 1 - r / (r + L) ≤ L / r ∧
      r⁻¹ ≤ (1 + L) / L * (1 - r / (r + L)) := by
  have hr0 : 0 < r := by linarith
  have hrl : 0 < r + L := by linarith
  have he : 1 - r / (r + L) = L / (r + L) := by field_simp; ring
  rw [he]
  refine ⟨rfl, div_pos hL hrl, (div_lt_one hrl).2 (by linarith), div_le_div_of_nonneg_left hL.le hr0 (by linarith), ?_⟩
  rw [inv_eq_one_div, div_mul_div_comm, div_le_div_iff₀ hr0 (by positivity)]
  nlinarith [mul_lt_mul_of_pos_left hr (mul_pos hL hL)]

private theorem sigma_deriv (L r : ℝ) (hL : 0 < L) (hr : 0 < r) :
    HasDerivAt (fun r => 1 - r / (r + L)) (-(1 - r / (r + L)) ^ 2 / L) r := by
  have hrl : r + L ≠ 0 := by positivity
  have h : HasDerivAt (fun r => 1 - r / (r + L)) _ r :=
    ((hasDerivAt_id r).div ((hasDerivAt_id r).add_const L) hrl).const_sub 1
  refine h.congr_deriv ?_
  simp only [id]
  field_simp
  ring

private theorem sigma1_deriv (L r : ℝ) (hL : 0 < L) (hr : 0 < r) :
    HasDerivAt (fun r => -(1 - r / (r + L)) ^ 2 / L) (2 * (1 - r / (r + L)) ^ 3 / L ^ 2) r := by
  have h : HasDerivAt (fun r => -(1 - r / (r + L)) ^ 2 / L) _ r :=
    (((sigma_deriv L r hL hr).pow 2).neg).div_const L
  refine h.congr_deriv ?_
  norm_num
  field_simp

private theorem phase_deriv (P : ChartParams) (hP : IsChartParams P) (r : ℝ) :
    HasDerivAt (phaseR P) (r / (P.rc ^ 2 + r ^ 2)) r := by
  have hrc := hP.rc_pos
  have hpos : (1 : ℝ) + r ^ 2 / P.rc ^ 2 ≠ 0 := by positivity
  have h : HasDerivAt (phaseR P) _ r :=
    (((((hasDerivAt_id r).pow 2).div_const (P.rc ^ 2)).const_add 1).log hpos).const_mul (1 / 2 : ℝ)
  refine h.congr_deriv ?_
  simp only [id, Pi.pow_apply]
  norm_num
  field_simp

private theorem phase1_deriv (P : ChartParams) (hP : IsChartParams P) (r : ℝ) :
    HasDerivAt (fun r => r / (P.rc ^ 2 + r ^ 2)) ((P.rc ^ 2 - r ^ 2) / (P.rc ^ 2 + r ^ 2) ^ 2) r := by
  have hrc := hP.rc_pos
  have hpos : P.rc ^ 2 + r ^ 2 ≠ 0 := by positivity
  have h : HasDerivAt (fun r => r / (P.rc ^ 2 + r ^ 2)) _ r :=
    (hasDerivAt_id r).div (((hasDerivAt_id r).pow 2).const_add (P.rc ^ 2)) hpos
  refine h.congr_deriv ?_
  simp only [id]
  norm_num
  field_simp
  ring

private def quotQ (P : ChartParams) (p : Polynomial ℝ) (s : ℝ) : ℝ := p.eval (1 - s) / chartQ P (1 - s)

private theorem quotQ_smooth (P : ChartParams) (hP : IsChartParams P) (p : Polynomial ℝ) :
    ContDiff ℝ ∞ (quotQ P p) := by
  have hp : ContDiff ℝ ∞ (fun x : ℝ => p.eval x) := by
    simpa using Polynomial.contDiff_aeval (𝕜 := ℝ) p ∞
  have hc : ContDiff ℝ ∞ (fun s : ℝ => chartQ P (1 - s)) := by
    unfold chartQ
    fun_prop
  exact (hp.comp (contDiff_const.sub contDiff_id)).div hc (fun s => (chartQ_pos P hP _).ne')

private def sg (P : ChartParams) (r : ℝ) : ℝ := 1 - r / (r + P.L0)

private def gF (P : ChartParams) (e : ℕ) (p : Polynomial ℝ) (s : ℝ) : ℝ :=
  s ^ (2 * P.eps + e) * quotQ P p s

private def gF1 (P : ChartParams) (e : ℕ) (p : Polynomial ℝ) (s : ℝ) : ℝ :=
  (2 * P.eps + e) * s ^ (2 * P.eps + e - 1) * quotQ P p s + s ^ (2 * P.eps + e) * deriv (quotQ P p) s

private def gF2 (P : ChartParams) (e : ℕ) (p : Polynomial ℝ) (s : ℝ) : ℝ :=
  (2 * P.eps + e) * ((2 * P.eps + e - 1) * s ^ (2 * P.eps + e - 1 - 1)) * quotQ P p s +
    (2 * P.eps + e) * s ^ (2 * P.eps + e - 1) * deriv (quotQ P p) s +
    ((2 * P.eps + e) * s ^ (2 * P.eps + e - 1) * deriv (quotQ P p) s +
      s ^ (2 * P.eps + e) * deriv (deriv (quotQ P p)) s)

private theorem quotQ_hasDeriv (P : ChartParams) (hP : IsChartParams P) (p : Polynomial ℝ) (s : ℝ) :
    HasDerivAt (quotQ P p) (deriv (quotQ P p) s) s ∧
      HasDerivAt (deriv (quotQ P p)) (deriv (deriv (quotQ P p)) s) s := by
  have hQ := quotQ_smooth P hP p
  have hQ1 : ContDiff ℝ ∞ (deriv (quotQ P p)) := by simpa using hQ.iterate_deriv 1
  exact ⟨((hQ.differentiable (by simp)) s).hasDerivAt, ((hQ1.differentiable (by simp)) s).hasDerivAt⟩

private theorem gF_hasDeriv (P : ChartParams) (hP : IsChartParams P) (e : ℕ) (p : Polynomial ℝ) (s : ℝ)
    (hs : 0 < s) : HasDerivAt (gF P e p) (gF1 P e p s) s ∧ HasDerivAt (gF1 P e p) (gF2 P e p s) s := by
  obtain ⟨h1, h2⟩ := quotQ_hasDeriv P hP p s
  refine ⟨(Real.hasDerivAt_rpow_const (Or.inl hs.ne')).mul h1, ?_⟩
  have h := (((Real.hasDerivAt_rpow_const (p := 2 * P.eps + e - 1) (Or.inl hs.ne')).const_mul
    (2 * P.eps + e)).mul h1).add ((Real.hasDerivAt_rpow_const (p := 2 * P.eps + e) (Or.inl hs.ne')).mul h2)
  exact h

private def hF (P : ChartParams) (κ : ℝ) (a : ℂ) (r : ℝ) : ℝ :=
  a.re * Real.cos (κ * phaseR P r) - a.im * Real.sin (κ * phaseR P r)

private def hF1 (P : ChartParams) (κ : ℝ) (a : ℂ) (r : ℝ) : ℝ :=
  -(a.re * Real.sin (κ * phaseR P r) + a.im * Real.cos (κ * phaseR P r)) * (κ * (r / (P.rc ^ 2 + r ^ 2)))

private def hF2 (P : ChartParams) (κ : ℝ) (a : ℂ) (r : ℝ) : ℝ :=
  -(a.re * Real.cos (κ * phaseR P r) - a.im * Real.sin (κ * phaseR P r)) * (κ * (r / (P.rc ^ 2 + r ^ 2))) ^ 2 -
    (a.re * Real.sin (κ * phaseR P r) + a.im * Real.cos (κ * phaseR P r)) *
      (κ * ((P.rc ^ 2 - r ^ 2) / (P.rc ^ 2 + r ^ 2) ^ 2))

private theorem hF_hasDeriv (P : ChartParams) (hP : IsChartParams P) (κ : ℝ) (a : ℂ) (r : ℝ) :
    HasDerivAt (hF P κ a) (hF1 P κ a r) r ∧ HasDerivAt (hF1 P κ a) (hF2 P κ a r) r := by
  have hθ : HasDerivAt (fun r => κ * phaseR P r) (κ * (r / (P.rc ^ 2 + r ^ 2))) r :=
    (phase_deriv P hP r).const_mul κ
  have hθ1 : HasDerivAt (fun r => κ * (r / (P.rc ^ 2 + r ^ 2)))
      (κ * ((P.rc ^ 2 - r ^ 2) / (P.rc ^ 2 + r ^ 2) ^ 2)) r := (phase1_deriv P hP r).const_mul κ
  constructor
  · have h : HasDerivAt (hF P κ a) _ r :=
      (((Real.hasDerivAt_cos _).comp r hθ).const_mul a.re).sub (((Real.hasDerivAt_sin _).comp r hθ).const_mul a.im)
    refine h.congr_deriv ?_
    simp only [hF1]
    ring
  · have hs : HasDerivAt (fun r => -(a.re * Real.sin (κ * phaseR P r) + a.im * Real.cos (κ * phaseR P r)))
        (-(a.re * (Real.cos (κ * phaseR P r) * (κ * (r / (P.rc ^ 2 + r ^ 2)))) +
          a.im * (-Real.sin (κ * phaseR P r) * (κ * (r / (P.rc ^ 2 + r ^ 2)))))) r :=
      ((((Real.hasDerivAt_sin _).comp r hθ).const_mul a.re).add
        (((Real.hasDerivAt_cos _).comp r hθ).const_mul a.im)).neg
    have h : HasDerivAt (hF1 P κ a) _ r := hs.mul hθ1
    refine h.congr_deriv ?_
    simp only [hF2]
    ring

private theorem hF_bounds (P : ChartParams) (hP : IsChartParams P) (κ : ℝ) (a : ℂ) (r : ℝ) (hr : 0 < r) :
    |hF P κ a r| ≤ |a.re| + |a.im| ∧ |hF1 P κ a r| ≤ (|a.re| + |a.im|) * (|κ| * r⁻¹) ∧
      |hF2 P κ a r| ≤ (|a.re| + |a.im|) * ((|κ| ^ 2 + |κ|) * r⁻¹ ^ 2) := by
  have hrc := hP.rc_pos
  have hd : 0 < P.rc ^ 2 + r ^ 2 := by positivity
  have hc1 : ∀ θ : ℝ, |a.re * Real.cos θ - a.im * Real.sin θ| ≤ |a.re| + |a.im| := by
    intro θ
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    · rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  have hc2 : ∀ θ : ℝ, |-(a.re * Real.sin θ + a.im * Real.cos θ)| ≤ |a.re| + |a.im| := by
    intro θ
    rw [abs_neg]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
    · rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hφ1 : |r / (P.rc ^ 2 + r ^ 2)| ≤ r⁻¹ := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ hd]
    rw [inv_mul_eq_div, le_div_iff₀ hr]
    nlinarith
  have hφ2 : |(P.rc ^ 2 - r ^ 2) / (P.rc ^ 2 + r ^ 2) ^ 2| ≤ r⁻¹ ^ 2 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (P.rc ^ 2 + r ^ 2) ^ 2), div_le_iff₀ (by positivity)]
    have h1 : |P.rc ^ 2 - r ^ 2| ≤ P.rc ^ 2 + r ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith
    have h2 : (P.rc ^ 2 + r ^ 2) ≤ r⁻¹ ^ 2 * (P.rc ^ 2 + r ^ 2) ^ 2 := by
      rw [inv_pow, inv_mul_eq_div, le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  refine ⟨hc1 _, ?_, ?_⟩
  · unfold hF1
    refine abs_mul2_le (hc2 _) ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hφ1 (abs_nonneg _)
  · unfold hF2
    refine (abs_sub _ _).trans ?_
    have e1 : |-(a.re * Real.cos (κ * phaseR P r) - a.im * Real.sin (κ * phaseR P r)) *
        (κ * (r / (P.rc ^ 2 + r ^ 2))) ^ 2| ≤ (|a.re| + |a.im|) * (|κ| ^ 2 * r⁻¹ ^ 2) := by
      refine abs_mul2_le (by rw [abs_neg]; exact hc1 _) ?_
      rw [abs_pow, abs_mul, mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hφ1 2) (by positivity)
    have e2 : |(a.re * Real.sin (κ * phaseR P r) + a.im * Real.cos (κ * phaseR P r)) *
        (κ * ((P.rc ^ 2 - r ^ 2) / (P.rc ^ 2 + r ^ 2) ^ 2))| ≤ (|a.re| + |a.im|) * (|κ| * r⁻¹ ^ 2) := by
      refine abs_mul2_le (by have := hc2 (κ * phaseR P r); rwa [abs_neg] at this) ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hφ2 (abs_nonneg _)
    nlinarith [e1, e2]

private theorem gF_bounds (P : ChartParams) (hP : IsChartParams P) (e : ℕ) (p : Polynomial ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      |gF P e p s| ≤ M * s ^ (2 * P.eps + e) ∧ |gF1 P e p s| ≤ M * (s ^ (2 * P.eps + e) / s) ∧
        |gF2 P e p s| ≤ M * (s ^ (2 * P.eps + e) / s / s) := by
  have hQ := quotQ_smooth P hP p
  have hQ1 : ContDiff ℝ ∞ (deriv (quotQ P p)) := by simpa using hQ.iterate_deriv 1
  have hQ2 : ContDiff ℝ ∞ (deriv (deriv (quotQ P p))) := by simpa using hQ.iterate_deriv 2
  obtain ⟨M0, hM0⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hQ.continuous.continuousOn
  obtain ⟨M1, hM1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hQ1.continuous.continuousOn
  obtain ⟨M2, hM2⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hQ2.continuous.continuousOn
  have h01 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hM0n : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0 h01)
  have hM1n : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0 h01)
  have hM2n : 0 ≤ M2 := (norm_nonneg _).trans (hM2 0 h01)
  have hβ : (0 : ℝ) ≤ 2 * P.eps + e := add_nonneg (by linarith [hP.eps_pos]) (Nat.cast_nonneg e)
  refine ⟨((2 * P.eps + e) * (|2 * P.eps + e - 1| + 2) + 1) * (M0 + M1 + M2), by positivity, fun s hs hs1 => ?_⟩
  have hq0 : |quotQ P p s| ≤ M0 := by simpa [Real.norm_eq_abs] using hM0 s ⟨hs.le, hs1⟩
  have hq1 : |deriv (quotQ P p) s| ≤ M1 := by simpa [Real.norm_eq_abs] using hM1 s ⟨hs.le, hs1⟩
  have hq2 : |deriv (deriv (quotQ P p)) s| ≤ M2 := by simpa [Real.norm_eq_abs] using hM2 s ⟨hs.le, hs1⟩
  have hX : 0 ≤ s ^ (2 * P.eps + e) := Real.rpow_nonneg hs.le _
  have e1 : s ^ (2 * P.eps + e - 1) = s ^ (2 * P.eps + e) / s := Real.rpow_sub_one hs.ne' _
  have e2 : s ^ (2 * P.eps + e - 1 - 1) = s ^ (2 * P.eps + e) / s / s := by
    rw [Real.rpow_sub_one hs.ne', Real.rpow_sub_one hs.ne']
  have hU : 0 ≤ s ^ (2 * P.eps + e) / s := by positivity
  have hV : 0 ≤ s ^ (2 * P.eps + e) / s / s := by positivity
  have hXU : s ^ (2 * P.eps + e) ≤ s ^ (2 * P.eps + e) / s := le_div_self hX hs hs1
  have hUV : s ^ (2 * P.eps + e) / s ≤ s ^ (2 * P.eps + e) / s / s := le_div_self hU hs hs1
  have hab : |2 * P.eps + e| ≤ 2 * P.eps + e := (abs_of_nonneg hβ).le
  have hS0 : M0 ≤ M0 + M1 + M2 := by linarith
  have hS1 : M1 ≤ M0 + M1 + M2 := by linarith
  have hS2 : M2 ≤ M0 + M1 + M2 := by linarith
  have hSn : 0 ≤ M0 + M1 + M2 := by linarith
  have hb1 : 0 ≤ |2 * P.eps + e - 1| := abs_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · unfold gF
    have h := abs_mul2_le (abs_of_nonneg hX).le hq0
    have h2 : s ^ (2 * P.eps + e) * M0 ≤ s ^ (2 * P.eps + e) * (M0 + M1 + M2) :=
      mul_le_mul_of_nonneg_left hS0 hX
    nlinarith [mul_nonneg (mul_nonneg hβ (add_nonneg hb1 zero_le_two)) (mul_nonneg hSn hX)]
  · unfold gF1
    rw [e1]
    have t1 := abs_mul3_le hab (abs_of_nonneg hU).le hq0
    have t2 := abs_mul2_le (abs_of_nonneg hX).le hq1
    have u1 : (2 * P.eps + e) * (s ^ (2 * P.eps + e) / s) * M0 ≤
        (2 * P.eps + e) * (s ^ (2 * P.eps + e) / s) * (M0 + M1 + M2) :=
      mul_le_mul_of_nonneg_left hS0 (mul_nonneg hβ hU)
    have u2 : s ^ (2 * P.eps + e) * M1 ≤ s ^ (2 * P.eps + e) / s * (M0 + M1 + M2) :=
      mul_le_mul hXU hS1 hM1n hU
    have u3 := mul_nonneg (mul_nonneg hβ (add_nonneg hb1 zero_le_one)) (mul_nonneg hSn hU)
    have ht := abs_add_le ((2 * P.eps + e) * (s ^ (2 * P.eps + e) / s) * quotQ P p s)
      (s ^ (2 * P.eps + e) * deriv (quotQ P p) s)
    nlinarith
  · unfold gF2
    rw [e1, e2]
    have t1 := abs_mul3_le hab (abs_mul2_le (le_refl |2 * P.eps + e - 1|) (abs_of_nonneg hV).le) hq0
    have t2 := abs_mul3_le hab (abs_of_nonneg hU).le hq1
    have t4 := abs_mul2_le (abs_of_nonneg hX).le hq2
    have u1 : (2 * P.eps + e) * (|2 * P.eps + e - 1| * (s ^ (2 * P.eps + e) / s / s)) * M0 ≤
        (2 * P.eps + e) * (|2 * P.eps + e - 1| * (s ^ (2 * P.eps + e) / s / s)) * (M0 + M1 + M2) :=
      mul_le_mul_of_nonneg_left hS0 (mul_nonneg hβ (mul_nonneg hb1 hV))
    have u2 : (2 * P.eps + e) * (s ^ (2 * P.eps + e) / s) * M1 ≤
        (2 * P.eps + e) * (s ^ (2 * P.eps + e) / s / s) * (M0 + M1 + M2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hUV hβ) hS1 hM1n (mul_nonneg hβ hV)
    have u4 : s ^ (2 * P.eps + e) * M2 ≤ s ^ (2 * P.eps + e) / s / s * (M0 + M1 + M2) :=
      mul_le_mul (hXU.trans hUV) hS2 hM2n hV
    have ha := abs_add_le ((2 * P.eps + e) * ((2 * P.eps + e - 1) * (s ^ (2 * P.eps + e) / s / s)) * quotQ P p s +
      (2 * P.eps + e) * (s ^ (2 * P.eps + e) / s) * deriv (quotQ P p) s)
      ((2 * P.eps + e) * (s ^ (2 * P.eps + e) / s) * deriv (quotQ P p) s +
        s ^ (2 * P.eps + e) * deriv (deriv (quotQ P p)) s)
    have hb := abs_add_le ((2 * P.eps + e) * ((2 * P.eps + e - 1) * (s ^ (2 * P.eps + e) / s / s)) * quotQ P p s)
      ((2 * P.eps + e) * (s ^ (2 * P.eps + e) / s) * deriv (quotQ P p) s)
    have hc := abs_add_le ((2 * P.eps + e) * (s ^ (2 * P.eps + e) / s) * deriv (quotQ P p) s)
      (s ^ (2 * P.eps + e) * deriv (deriv (quotQ P p)) s)
    have t1' : |(2 * P.eps + e) * ((2 * P.eps + e - 1) * (s ^ (2 * P.eps + e) / s / s)) * quotQ P p s| ≤
        (2 * P.eps + e) * (|2 * P.eps + e - 1| * (s ^ (2 * P.eps + e) / s / s)) * M0 := by
      refine abs_mul3_le hab ?_ hq0
      rw [abs_mul, abs_of_nonneg hV]
    nlinarith

private theorem fin_bound {v B c Y Lp ρ C : ℝ} (hv : |v| ≤ B) (hB : B = c * Y) (hY : Y ≤ Lp * ρ) (hc : 0 ≤ c)
    (hC : c * Lp ≤ C) (hρ : 0 ≤ ρ) : |v| ≤ C * ρ := by
  calc |v| ≤ c * Y := hB ▸ hv
    _ ≤ c * (Lp * ρ) := mul_le_mul_of_nonneg_left hY hc
    _ = (c * Lp) * ρ := by ring
    _ ≤ C * ρ := mul_le_mul_of_nonneg_right hC hρ

private theorem abs_mul_le_of {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := abs_mul2_le ha hb

private theorem radialWeight_bounds (P : ChartParams) (hP : IsChartParams P) (e : ℕ) (κ : ℝ)
    (p : Polynomial ℝ) (a : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ContDiffOn ℝ 2 (fun r => (a * radialWeight P e κ p r).re) (Set.Ioi 1) ∧
      ∀ r : ℝ, 1 < r → |(a * radialWeight P e κ p r).re| ≤ C * r ^ (-((e : ℝ) + P.eps)) ∧
        |deriv (fun r => (a * radialWeight P e κ p r).re) r| ≤ C * r ^ (-((e : ℝ) + P.eps + 1)) ∧
        |deriv (deriv (fun r => (a * radialWeight P e κ p r).re)) r| ≤ C * r ^ (-((e : ℝ) + P.eps + 2)) := by
  have hL := hP.L0_pos
  have heps := hP.eps_pos
  have hβ0 : (0 : ℝ) ≤ 2 * P.eps + e := add_nonneg (by linarith) (Nat.cast_nonneg e)
  have hβγ : (e : ℝ) + P.eps ≤ 2 * P.eps + e := by linarith
  obtain ⟨M, hM0, hM⟩ := gF_bounds P hP e p
  have hsg_pos : ∀ r : ℝ, 0 < r → 0 < sg P r := by
    intro r hr
    have hrl : 0 < r + P.L0 := by linarith
    have he : sg P r = P.L0 / (r + P.L0) := by unfold sg; field_simp; ring
    rw [he]
    positivity
  have hfeq : ∀ r : ℝ, 0 < r → (a * radialWeight P e κ p r).re = gF P e p (sg P r) * hF P κ a r := by
    intro r hr
    have hs := hsg_pos r hr
    unfold radialWeight
    rw [re_form]
    unfold hF
    congr 1
    unfold sg at hs
    unfold gF quotQ sg
    rw [sub_sub_cancel, Real.rpow_add hs, Real.rpow_natCast]
    ring
  set F1 : ℝ → ℝ := fun r => gF1 P e p (sg P r) * (-(sg P r) ^ 2 / P.L0) * hF P κ a r +
    gF P e p (sg P r) * hF1 P κ a r with hF1def
  set F2 : ℝ → ℝ := fun r => (gF2 P e p (sg P r) * (-(sg P r) ^ 2 / P.L0) * (-(sg P r) ^ 2 / P.L0) +
      gF1 P e p (sg P r) * (2 * (sg P r) ^ 3 / P.L0 ^ 2)) * hF P κ a r +
      gF1 P e p (sg P r) * (-(sg P r) ^ 2 / P.L0) * hF1 P κ a r +
      (gF1 P e p (sg P r) * (-(sg P r) ^ 2 / P.L0) * hF1 P κ a r + gF P e p (sg P r) * hF2 P κ a r) with hF2def
  have dF : ∀ r : ℝ, 0 < r → HasDerivAt (fun r => gF P e p (sg P r) * hF P κ a r) (F1 r) r := by
    intro r hr
    have hσ : HasDerivAt (sg P) (-(sg P r) ^ 2 / P.L0) r := sigma_deriv P.L0 r hL hr
    have hG := gF_hasDeriv P hP e p (sg P r) (hsg_pos r hr)
    have hH := hF_hasDeriv P hP κ a r
    exact (hG.1.comp r hσ).mul hH.1
  have dF1 : ∀ r : ℝ, 0 < r → HasDerivAt F1 (F2 r) r := by
    intro r hr
    have hσ : HasDerivAt (sg P) (-(sg P r) ^ 2 / P.L0) r := sigma_deriv P.L0 r hL hr
    have hσ1 : HasDerivAt (fun r => -(sg P r) ^ 2 / P.L0) (2 * (sg P r) ^ 3 / P.L0 ^ 2) r :=
      sigma1_deriv P.L0 r hL hr
    have hG := gF_hasDeriv P hP e p (sg P r) (hsg_pos r hr)
    have hH := hF_hasDeriv P hP κ a r
    exact (((hG.2.comp r hσ).mul hσ1).mul hH.1).add ((hG.1.comp r hσ).mul hH.2)
  have hev : ∀ r : ℝ, 0 < r → (fun r => (a * radialWeight P e κ p r).re) =ᶠ[nhds r]
      (fun r => gF P e p (sg P r) * hF P κ a r) := by
    intro r hr
    filter_upwards [Ioi_mem_nhds hr] with y hy using hfeq y hy
  have hd1 : ∀ r : ℝ, 0 < r → deriv (fun r => (a * radialWeight P e κ p r).re) r = F1 r := by
    intro r hr
    rw [(hev r hr).deriv_eq, (dF r hr).deriv]
  have hd2 : ∀ r : ℝ, 0 < r → deriv (deriv (fun r => (a * radialWeight P e κ p r).re)) r = F2 r := by
    intro r hr
    have h : deriv (fun r => (a * radialWeight P e κ p r).re) =ᶠ[nhds r] F1 := by
      filter_upwards [Ioi_mem_nhds hr] with y hy using hd1 y hy
    rw [h.deriv_eq, (dF1 r hr).deriv]
  have hcont : ContDiffOn ℝ 2 (fun r => (a * radialWeight P e κ p r).re) (Set.Ioi 1) := by
    have hsgC : ContDiffOn ℝ 2 (sg P) (Set.Ioi 0) := by
      refine contDiffOn_const.sub (contDiffOn_id.div (contDiffOn_id.add contDiffOn_const) ?_)
      intro r hr
      have h0 : (0 : ℝ) < r := hr
      have h1 : (0 : ℝ) < r + P.L0 := by linarith
      simpa using h1.ne'
    have hGC : ContDiffOn ℝ 2 (gF P e p) (Set.Ioi 0) := by
      have hQ2 : ContDiff ℝ 2 (quotQ P p) := (quotQ_smooth P hP p).of_le (WithTop.coe_le_coe.2 le_top)
      exact (contDiffOn_id.rpow_const_of_ne (fun s hs => ne_of_gt hs)).mul hQ2.contDiffOn
    have hcomp : ContDiffOn ℝ 2 (fun r => gF P e p (sg P r)) (Set.Ioi 0) :=
      hGC.comp hsgC (fun r hr => hsg_pos r hr)
    have hφ : ContDiff ℝ 2 (phaseR P) := by
      have hrc := hP.rc_pos
      unfold phaseR
      exact contDiff_const.mul ((contDiff_const.add ((contDiff_id.pow 2).div_const _)).log
        (fun x => by simp only [id]; positivity))
    have hHC : ContDiff ℝ 2 (hF P κ a) :=
      (contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul hφ))).sub
        (contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul hφ)))
    refine ((hcomp.mul hHC.contDiffOn).mono (Set.Ioi_subset_Ioi zero_le_one)).congr ?_
    intro r hr
    exact hfeq r (lt_trans zero_lt_one hr)
  have hAh0 : 0 ≤ |a.re| + |a.im| := by positivity
  have hK0 : 0 ≤ (1 + P.L0) / P.L0 := div_nonneg (by linarith) hL.le
  have hc0 : 0 ≤ M * (|a.re| + |a.im|) := mul_nonneg hM0 hAh0
  have hc1 : 0 ≤ M * (|a.re| + |a.im|) / P.L0 + M * (|a.re| + |a.im|) * |κ| * ((1 + P.L0) / P.L0) := by
    have := abs_nonneg κ
    positivity
  have hc2 : 0 ≤ 3 * M * (|a.re| + |a.im|) / P.L0 ^ 2 +
      2 * M * (|a.re| + |a.im|) * |κ| * ((1 + P.L0) / P.L0) / P.L0 +
      M * (|a.re| + |a.im|) * (|κ| ^ 2 + |κ|) * ((1 + P.L0) / P.L0) ^ 2 := by
    have := abs_nonneg κ
    positivity
  have hL0 : 0 ≤ P.L0 ^ (2 * P.eps + (e : ℝ)) := Real.rpow_nonneg hL.le _
  have hL1 : 0 ≤ P.L0 ^ (2 * P.eps + (e : ℝ) + 1) := Real.rpow_nonneg hL.le _
  have hL2 : 0 ≤ P.L0 ^ (2 * P.eps + (e : ℝ) + 2) := Real.rpow_nonneg hL.le _
  refine ⟨M * (|a.re| + |a.im|) * P.L0 ^ (2 * P.eps + (e : ℝ)) +
    (M * (|a.re| + |a.im|) / P.L0 + M * (|a.re| + |a.im|) * |κ| * ((1 + P.L0) / P.L0)) *
      P.L0 ^ (2 * P.eps + (e : ℝ) + 1) +
    (3 * M * (|a.re| + |a.im|) / P.L0 ^ 2 + 2 * M * (|a.re| + |a.im|) * |κ| * ((1 + P.L0) / P.L0) / P.L0 +
      M * (|a.re| + |a.im|) * (|κ| ^ 2 + |κ|) * ((1 + P.L0) / P.L0) ^ 2) * P.L0 ^ (2 * P.eps + (e : ℝ) + 2),
    add_nonneg (add_nonneg (mul_nonneg hc0 hL0) (mul_nonneg hc1 hL1)) (mul_nonneg hc2 hL2), hcont,
    fun r hr => ?_⟩
  have hr0 : 0 < r := by linarith
  have hfacts := sigma_facts P.L0 r hL hr
  have hs0 : 0 < sg P r := hsg_pos r hr0
  have hs1 : sg P r ≤ 1 := hfacts.2.2.1.le
  have hsr : sg P r ≤ P.L0 / r := hfacts.2.2.2.1
  have hrinv : r⁻¹ ≤ (1 + P.L0) / P.L0 * sg P r := hfacts.2.2.2.2
  obtain ⟨hg0, hg1, hg2⟩ := hM (sg P r) hs0 hs1
  obtain ⟨hh0, hh1, hh2⟩ := hF_bounds P hP κ a r hr0
  have hh1' : |hF1 P κ a r| ≤ (|a.re| + |a.im|) * (|κ| * ((1 + P.L0) / P.L0 * sg P r)) :=
    hh1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrinv (abs_nonneg _)) hAh0)
  have hh2' : |hF2 P κ a r| ≤ (|a.re| + |a.im|) * ((|κ| ^ 2 + |κ|) * ((1 + P.L0) / P.L0 * sg P r) ^ 2) := by
    refine hh2.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) hAh0)
    exact pow_le_pow_left₀ (inv_nonneg.2 hr0.le) hrinv 2
  have hσ1 : |-(sg P r) ^ 2 / P.L0| ≤ (sg P r) ^ 2 / P.L0 := by
    rw [abs_div, abs_neg, abs_of_pos hL, abs_of_nonneg (sq_nonneg _)]
  have hσ2 : |2 * (sg P r) ^ 3 / P.L0 ^ 2| ≤ 2 * (sg P r) ^ 3 / P.L0 ^ 2 := (abs_of_nonneg (by positivity)).le
  have p0 : (sg P r) ^ (2 * P.eps + (e : ℝ)) ≤ P.L0 ^ (2 * P.eps + (e : ℝ)) * r ^ (-((e : ℝ) + P.eps)) := by
    have := pow_to_r (j := 0) hL hr hβγ hβ0 le_rfl hs0 hsr
    simpa using this
  have p1 : (sg P r) ^ (2 * P.eps + (e : ℝ)) * sg P r ≤
      P.L0 ^ (2 * P.eps + (e : ℝ) + 1) * r ^ (-((e : ℝ) + P.eps + 1)) := by
    rw [← Real.rpow_add_one hs0.ne']
    exact pow_to_r hL hr hβγ hβ0 zero_le_one hs0 hsr
  have p2 : (sg P r) ^ (2 * P.eps + (e : ℝ)) * (sg P r) ^ 2 ≤
      P.L0 ^ (2 * P.eps + (e : ℝ) + 2) * r ^ (-((e : ℝ) + P.eps + 2)) := by
    rw [← Real.rpow_two, ← Real.rpow_add hs0]
    exact pow_to_r hL hr hβγ hβ0 zero_le_two hs0 hsr
  have hρ0 : 0 ≤ r ^ (-((e : ℝ) + P.eps)) := Real.rpow_nonneg hr0.le _
  have hρ1 : 0 ≤ r ^ (-((e : ℝ) + P.eps + 1)) := Real.rpow_nonneg hr0.le _
  have hρ2 : 0 ≤ r ^ (-((e : ℝ) + P.eps + 2)) := Real.rpow_nonneg hr0.le _
  rw [hd1 r hr0, hd2 r hr0, hfeq r hr0]
  have hX : 0 ≤ (sg P r) ^ (2 * P.eps + (e : ℝ)) := Real.rpow_nonneg hs0.le _
  refine ⟨?_, ?_, ?_⟩
  · refine fin_bound (abs_mul2_le hg0 hh0) (c := M * (|a.re| + |a.im|)) ?_ p0 hc0 ?_ hρ0
    · ring
    · linarith [mul_nonneg hc1 hL1, mul_nonneg hc2 hL2]
  · have hb : |F1 r| ≤ M * ((sg P r) ^ (2 * P.eps + (e : ℝ)) / sg P r) * ((sg P r) ^ 2 / P.L0) *
        (|a.re| + |a.im|) + M * (sg P r) ^ (2 * P.eps + (e : ℝ)) *
        ((|a.re| + |a.im|) * (|κ| * ((1 + P.L0) / P.L0 * sg P r))) :=
      (abs_add_le _ _).trans (add_le_add (abs_mul3_le hg1 hσ1 hh0) (abs_mul2_le hg0 hh1'))
    refine fin_bound hb (c := M * (|a.re| + |a.im|) / P.L0 + M * (|a.re| + |a.im|) * |κ| * ((1 + P.L0) / P.L0))
      ?_ p1 hc1 ?_ hρ1
    · field_simp
    · linarith [mul_nonneg hc0 hL0, mul_nonneg hc2 hL2]
  · have hb : |F2 r| ≤ M * ((sg P r) ^ (2 * P.eps + (e : ℝ)) / sg P r / sg P r) * ((sg P r) ^ 2 / P.L0) *
          ((sg P r) ^ 2 / P.L0) * (|a.re| + |a.im|) +
        M * ((sg P r) ^ (2 * P.eps + (e : ℝ)) / sg P r) * (2 * (sg P r) ^ 3 / P.L0 ^ 2) * (|a.re| + |a.im|) +
        M * ((sg P r) ^ (2 * P.eps + (e : ℝ)) / sg P r) * ((sg P r) ^ 2 / P.L0) *
          ((|a.re| + |a.im|) * (|κ| * ((1 + P.L0) / P.L0 * sg P r))) +
        (M * ((sg P r) ^ (2 * P.eps + (e : ℝ)) / sg P r) * ((sg P r) ^ 2 / P.L0) *
          ((|a.re| + |a.im|) * (|κ| * ((1 + P.L0) / P.L0 * sg P r))) +
        M * (sg P r) ^ (2 * P.eps + (e : ℝ)) *
          ((|a.re| + |a.im|) * ((|κ| ^ 2 + |κ|) * ((1 + P.L0) / P.L0 * sg P r) ^ 2))) := by
      refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
      · exact (abs_mul_le_of (abs_add_le _ _) hh0).trans
          (mul_le_mul_of_nonneg_right (add_le_add (abs_mul3_le hg2 hσ1 hσ1) (abs_mul2_le hg1 hσ2)) hAh0) |>.trans_eq (by ring)
      · exact abs_mul3_le hg1 hσ1 hh1'
      · exact (abs_add_le _ _).trans (add_le_add (abs_mul3_le hg1 hσ1 hh1') (abs_mul2_le hg0 hh2'))
    refine fin_bound hb (c := 3 * M * (|a.re| + |a.im|) / P.L0 ^ 2 +
      2 * M * (|a.re| + |a.im|) * |κ| * ((1 + P.L0) / P.L0) / P.L0 +
      M * (|a.re| + |a.im|) * (|κ| ^ 2 + |κ|) * ((1 + P.L0) / P.L0) ^ 2) ?_ p2 hc2 ?_ hρ2
    · field_simp
      ring
    · linarith [mul_nonneg hc0 hL0, mul_nonneg hc1 hL1]

theorem modeFieldOf_radial_split (P : ChartParams) (hP : IsChartParams P) (e : ℕ) (D : FieldData)
    (hD : IsFieldData P e D) (c : ℝ) (n : ℤ) (hn : n ∈ D.modes) :
    ∃ (N : ℕ) (ρ : Fin N → ℝ → ℝ) (A : Fin N → Space → Space) (R0 C : ℝ), 0 < R0 ∧
      (∀ y : Space, R0 < ‖y‖ → modeFieldOf P D c n y = ∑ j, ρ j ‖y‖ • A j y) ∧
      (∀ j, ContDiffOn ℝ 2 (ρ j) (Set.Ioi R0)) ∧
      (∀ j, ∀ r : ℝ, R0 < r → |ρ j r| ≤ C * r ^ (-((e : ℝ) + P.eps)) ∧
        |deriv (ρ j) r| ≤ C * r ^ (-((e : ℝ) + P.eps + 1)) ∧
        |deriv (deriv (ρ j)) r| ≤ C * r ^ (-((e : ℝ) + P.eps + 2))) ∧
      (∀ j, ∀ s : ℝ, 0 < s → ∀ y : Space, A j (s • y) = A j y) ∧
      (∀ j, ∀ y : Space, y ≠ 0 → DifferentiableAt ℝ (A j) y) ∧
      (∀ j, LocallyLipschitzOn {y : Space | y ≠ 0} (fderiv ℝ (A j))) := by
  classical
  obtain ⟨tL, K, T, p, htL0, htL1, hT, hred⟩ := reducedField_far_interp P hP e D hD c n hn
  have hL := hP.L0_pos
  have hT0 : ∀ j, 0 < T j ∧ 0 < 1 - T j := fun j => ⟨by linarith [(hT j).1], by linarith [(hT j).2]⟩
  set Rn : Fin K → ℝ := fun j => P.L0 * T j / (1 - T j) with hRn
  have hRpos : ∀ j, 0 < Rn j := fun j => div_pos (mul_pos hL (hT0 j).1) (hT0 j).2
  have hRT : ∀ j, Rn j / (Rn j + P.L0) = T j := by
    intro j
    have h1 := (hT0 j).2.ne'
    simp only [hRn]
    field_simp
    ring
  set φ : ℝ := -(Real.pi / (2 * (((n * P.m : ℤ) : ℝ)))) with hφ
  set a : Fin K → ℂ := fun j => ((((1 - T j) ^ (2 * P.eps))⁻¹ : ℝ) : ℂ) *
    Complex.exp (-(Complex.I * (((n : ℝ) * c * phaseR P (Rn j) : ℝ) : ℂ))) with ha
  set ρ0 : Fin K → ℝ → ℝ := fun j r => (a j * radialWeight P e ((n : ℝ) * c) (p j) r).re with hρ0
  set ρ1 : Fin K → ℝ → ℝ := fun j r => ((Complex.I * a j) * radialWeight P e ((n : ℝ) * c) (p j) r).re with hρ1
  set A0 : Fin K → Space → Space := fun j z => (ContinuousLinearMap.id ℝ Space)
    (modeFieldOf P D c n ((ContinuousLinearMap.id ℝ Space) ((Rn j / ‖z‖) • z))) with hA0
  set A1 : Fin K → Space → Space := fun j z => turnCLM (-φ)
    (modeFieldOf P D c n (turnCLM φ ((Rn j / ‖z‖) • z))) with hA1
  have hW0 := fun j => radialWeight_bounds P hP e ((n : ℝ) * c) (p j) (a j)
  have hW1 := fun j => radialWeight_bounds P hP e ((n : ℝ) * c) (p j) (Complex.I * a j)
  choose C0 hC0 hcd0 hb0 using hW0
  choose C1 hC1 hcd1 hb1 using hW1
  set Ct : ℝ := ∑ j, (C0 j + C1 j) with hCt
  have hCt0 : ∀ j, C0 j ≤ Ct ∧ C1 j ≤ Ct := by
    intro j
    have h := Finset.single_le_sum (f := fun j => C0 j + C1 j) (fun i _ => add_nonneg (hC0 i) (hC1 i))
      (Finset.mem_univ j)
    exact ⟨by linarith [hC1 j], by linarith [hC0 j]⟩
  set R0 : ℝ := P.L0 * tL / (1 - tL) + 1 with hR0
  have hR01 : 1 ≤ R0 := by
    have : 0 ≤ P.L0 * tL / (1 - tL) := div_nonneg (mul_nonneg hL.le htL0) (by linarith)
    linarith
  have hFd := modeField_diff P hP hD c n hn
  have hFl := modeField_slope P hP hD c n hn
  refine ⟨K + K, Fin.append ρ0 ρ1, Fin.append A0 A1, R0, Ct, by linarith, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, norm_zero] at hy
      linarith
    have hr : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have ht1 : tL < ‖y‖ / (‖y‖ + P.L0) := by
      rw [lt_div_iff₀ (by linarith)]
      have h2 : P.L0 * tL / (1 - tL) < ‖y‖ := by linarith
      rw [div_lt_iff₀ (by linarith)] at h2
      nlinarith
    have ht2 : ‖y‖ / (‖y‖ + P.L0) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    have hinner : ∀ i, innerAt P D c n ‖y‖ y i =
        ∑ j, (a j * radialWeight P e ((n : ℝ) * c) (p j) ‖y‖) * innerAt P D c n (Rn j) y i := by
      intro i
      unfold innerAt
      simp_rw [hRT]
      rw [hred _ ht1 ht2 (heightRatio y) 0, hred _ ht1 ht2 (heightRatio y) 1, hred _ ht1 ht2 (heightRatio y) 2]
      simp only [Finset.sum_mul]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [exp_split, exp_split]
      simp only [ha, radialWeight]
      have hd : ((((1 - T j) ^ (2 * P.eps)) : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (hT0 j).2 _).ne'
      have hx : Complex.exp (Complex.I * (((n : ℝ) * c * phaseR P (Rn j) : ℝ) : ℂ)) ≠ 0 := Complex.exp_ne_zero _
      rw [Complex.exp_neg]
      push_cast at hd ⊢
      field_simp
    have hA0y : ∀ j, A0 j y = ofComponents (fun i => (innerAt P D c n (Rn j) y i).re) := by
      intro j
      simp only [hA0, ContinuousLinearMap.id_apply]
      rw [modeFieldOf_eq_innerAt, norm_dir (hRpos j) hy0]
      congr 1
      funext i
      rw [innerAt_smul P D c n (Rn j) (div_pos (hRpos j) hr)]
    have hA1y : ∀ j, A1 j y = ofComponents (fun i =>
        (Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * φ : ℝ) : ℂ)) * innerAt P D c n (Rn j) y i).re) := by
      intro j
      have hne : (Rn j / ‖y‖) • y ≠ 0 := smul_ne_zero (div_pos (hRpos j) hr).ne' hy0
      simp only [hA1, turnCLM_apply]
      rw [turn_eq P hP e D hD c n hn φ _ hne, turn_turn, norm_dir (hRpos j) hy0]
      congr 1
      funext i
      rw [innerAt_smul P D c n (Rn j) (div_pos (hRpos j) hr)]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, hA0y, hA1y, hρ0, hρ1]
    rw [← Finset.sum_add_distrib, ← ofComponents_pair, modeFieldOf_eq_innerAt]
    congr 1
    funext i
    rw [hinner i, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    set w := a j * radialWeight P e ((n : ℝ) * c) (p j) ‖y‖ with hw
    set V := innerAt P D c n (Rn j) y i
    rw [mul_assoc Complex.I, ← hw]
    by_cases h0 : n = 0
    · have hwim : w.im = 0 := by
        simp only [hw, ha, radialWeight, h0, Int.cast_zero, zero_mul, Complex.ofReal_zero, mul_zero, neg_zero,
          Complex.exp_zero, mul_one]
        rw [← Complex.ofReal_mul, Complex.ofReal_im]
      simp [Complex.mul_re, hwim]
    · have hm : (((n * P.m : ℤ) : ℝ)) ≠ 0 := by
        have := hP.m_pos
        exact_mod_cast mul_ne_zero h0 (by exact_mod_cast this.ne')
      have hE : Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * φ : ℝ) : ℂ)) = -Complex.I := by
        have h1 : (((n * P.m : ℤ) : ℝ) * φ : ℝ) = -(Real.pi / 2) := by
          rw [hφ]
          field_simp
        rw [h1, mul_comm, Complex.exp_mul_I]
        push_cast
        rw [Complex.cos_neg, Complex.sin_neg, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
        ring
      rw [hE]
      simp [Complex.mul_re]
      ring
  · intro j
    induction j using Fin.addCases with
    | left j =>
      rw [Fin.append_left]
      exact (hcd0 j).mono (Set.Ioi_subset_Ioi hR01)
    | right j =>
      rw [Fin.append_right]
      exact (hcd1 j).mono (Set.Ioi_subset_Ioi hR01)
  · intro j r hr
    have hr1 : 1 < r := lt_of_le_of_lt hR01 hr
    have hp0 : ∀ u : ℝ, 0 ≤ r ^ u := fun u => Real.rpow_nonneg (by linarith) u
    induction j using Fin.addCases with
    | left j =>
      rw [Fin.append_left]
      obtain ⟨b1, b2, b3⟩ := hb0 j r hr1
      refine ⟨b1.trans (mul_le_mul_of_nonneg_right (hCt0 j).1 (hp0 _)),
        b2.trans (mul_le_mul_of_nonneg_right (hCt0 j).1 (hp0 _)),
        b3.trans (mul_le_mul_of_nonneg_right (hCt0 j).1 (hp0 _))⟩
    | right j =>
      rw [Fin.append_right]
      obtain ⟨b1, b2, b3⟩ := hb1 j r hr1
      refine ⟨b1.trans (mul_le_mul_of_nonneg_right (hCt0 j).2 (hp0 _)),
        b2.trans (mul_le_mul_of_nonneg_right (hCt0 j).2 (hp0 _)),
        b3.trans (mul_le_mul_of_nonneg_right (hCt0 j).2 (hp0 _))⟩
  · intro j s hs y
    induction j using Fin.addCases with
    | left j =>
      simp only [Fin.append_left, hA0]
      rw [scale_dir hs]
    | right j =>
      simp only [Fin.append_right, hA1]
      rw [scale_dir hs]
  · intro j y hy
    induction j using Fin.addCases with
    | left j =>
      rw [Fin.append_left]
      exact (angular_regular _ hFd hFl _ _ (Rn j)).1 y hy
    | right j =>
      rw [Fin.append_right]
      exact (angular_regular _ hFd hFl _ _ (Rn j)).1 y hy
  · intro j
    induction j using Fin.addCases with
    | left j =>
      rw [Fin.append_left]
      exact (angular_regular _ hFd hFl _ _ (Rn j)).2
    | right j =>
      rw [Fin.append_right]
      exact (angular_regular _ hFd hFl _ _ (Rn j)).2

end FracCellInternal

end Breakdown
