import Breakdown.FracCell.GivenAuxDefs
import Breakdown.FracCell.GivenAuxActuatorOpen

open scoped ContDiff ENNReal Topology
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

namespace AtomAxisInternal

theorem dvd_sub_atSecond (P : MvPolynomial (Fin 2) ℂ) :
    (MvPolynomial.X 1 - 1 : MvPolynomial (Fin 2) ℂ) ∣ P - atSecond 1 P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [atSecond]
  | add p q hp hq =>
    have e : atSecond 1 (p + q) = atSecond 1 p + atSecond 1 q := by simp [atSecond, map_add]
    rw [e, show p + q - (atSecond 1 p + atSecond 1 q) = (p - atSecond 1 p) + (q - atSecond 1 q) by ring]
    exact dvd_add hp hq
  | mul_X p n hp =>
    have e : atSecond 1 (p * MvPolynomial.X n) =
        atSecond 1 p * (if n = 1 then MvPolynomial.C 1 else MvPolynomial.X 0) := by
      simp [atSecond, map_mul, MvPolynomial.bind₁_X_right]
    rw [e]
    fin_cases n
    · simp only [Fin.zero_eta, Fin.isValue, zero_ne_one, if_false]
      rw [show p * MvPolynomial.X 0 - atSecond 1 p * MvPolynomial.X 0 = (p - atSecond 1 p) * MvPolynomial.X 0 by ring]
      exact dvd_mul_of_dvd_left hp _
    · simp only [Fin.mk_one, Fin.isValue, if_true, map_one]
      rw [show p * MvPolynomial.X 1 - atSecond 1 p * 1 =
        (p - atSecond 1 p) * MvPolynomial.X 1 + atSecond 1 p * (MvPolynomial.X 1 - 1) by ring]
      exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_left _ _)

theorem factor_of_atSecond (P : MvPolynomial (Fin 2) ℂ) (h : atSecond 1 P = 0) :
    ∃ Q, P = (1 - MvPolynomial.X 1) * Q := by
  obtain ⟨Q, hQ⟩ := dvd_sub_atSecond P
  rw [h, sub_zero] at hQ
  exact ⟨-Q, by rw [hQ]; ring⟩

theorem tDeriv_mul_left (F Q : MvPolynomial (Fin 2) ℂ) (hF : MvPolynomial.pderiv 0 F = 0) (o : ℕ) :
    tDeriv o (F * Q) = F * tDeriv o Q := by
  induction o with
  | zero => simp [tDeriv]
  | succ o ih =>
    simp only [tDeriv, Function.iterate_succ_apply'] at ih ⊢
    rw [ih, Derivation.leibniz, hF]
    simp [smul_eq_mul]

theorem pderiv_one_sub : MvPolynomial.pderiv 0 (1 - MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) = 0 := by
  simp [MvPolynomial.pderiv_X]

theorem pderiv_X_one : MvPolynomial.pderiv 0 (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) = 0 := by
  simp [MvPolynomial.pderiv_X]

theorem atFirst_mul (c : ℂ) (A B : MvPolynomial (Fin 2) ℂ) : atFirst c (A * B) = atFirst c A * atFirst c B := by
  simp [atFirst, map_mul]

theorem atFirst_one_sub (c : ℂ) : atFirst c (1 - MvPolynomial.X 1) = 1 - MvPolynomial.X 1 := by
  simp [atFirst, MvPolynomial.bind₁_X_right]

theorem atFirst_X_one (c : ℂ) : atFirst c (MvPolynomial.X 1) = MvPolynomial.X 1 := by
  simp [atFirst, MvPolynomial.bind₁_X_right]

theorem one_sub_ne : (1 - MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (0 : ℂ))) h
  simp at this

open Classical in
def quotPiece (S : Spline) (i : ℕ) : MvPolynomial (Fin 2) ℂ :=
  if h : ∃ Q, S.piece i (atomLastX S) = (1 - MvPolynomial.X 1) * Q then h.choose else 0

theorem quotPiece_spec (S : Spline) (i : ℕ) (h : ∃ Q, S.piece i (atomLastX S) = (1 - MvPolynomial.X 1) * Q) :
    S.piece i (atomLastX S) = (1 - MvPolynomial.X 1) * quotPiece S i := by
  unfold quotPiece
  rw [dif_pos h]
  exact h.choose_spec

def quotSpline (S : Spline) : Spline :=
  ⟨⟨S.mesh.tBreaks, [0, 1]⟩, fun i _ => MvPolynomial.X 1 * quotPiece S i⟩

theorem length_two (l : List ℝ) (h0 : l.head? = some 0) (h1 : l.getLast? = some 1) : 2 ≤ l.length := by
  match l, h0, h1 with
  | [], h0, _ => simp at h0
  | [a], h0, h1 => simp at h0 h1; linarith
  | a :: b :: r, _, _ => simp

theorem interior_lt_one (l : List ℝ) (hs : l.Pairwise (· < ·)) (h1 : l.getLast? = some 1) :
    ∀ b ∈ (l.drop 1).dropLast, b < 1 := by
  intro b hb
  cases l with
  | nil => simp at hb
  | cons a r =>
    simp only [List.drop_succ_cons, List.drop_zero] at hb
    have hL : r ≠ [] := by intro h; rw [h] at hb; simp at hb
    have hs' : r.Pairwise (· < ·) := hs.of_cons
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil a r), List.getLast_cons hL] at h1
    have hlast : r.getLast hL = 1 := by simpa using h1
    have e := List.dropLast_append_getLast hL
    rw [← e, List.pairwise_append] at hs'
    have := hs'.2.2 b hb (r.getLast hL) (by simp)
    rwa [hlast] at this

theorem cellIndex_top (l : List ℝ) (u : ℝ) (hall : ∀ b ∈ (l.drop 1).dropLast, b ≤ u) :
    cellIndex l u = cellCount l - 1 := by
  unfold cellIndex cellCount
  rw [List.filter_eq_self.2 (by intro b hb; simpa using hall b hb)]
  simp [List.length_dropLast]

theorem cellIndex_lt (l : List ℝ) (u : ℝ) (h2 : 2 ≤ l.length) : cellIndex l u < cellCount l := by
  unfold cellIndex cellCount
  have h1 := List.length_filter_le (fun b => decide (b ≤ u)) ((l.drop 1).dropLast)
  have h3 : ((l.drop 1).dropLast).length = l.length - 1 - 1 := by rw [List.length_dropLast, List.length_drop]
  omega

theorem piece_factor {odd : Bool} {S : Spline} {j : ℕ} (hS : IsAtomSpline odd S j) (hj : j ≠ 0) (i : ℕ)
    (hi : i < cellCount S.mesh.tBreaks) :
    S.piece i (atomLastX S) = (1 - MvPolynomial.X 1) * quotPiece S i :=
  quotPiece_spec S i (factor_of_atSecond _ (hS.at_axis hj i hi))

theorem quotSpline_class {odd : Bool} {S : Spline} {j : ℕ} (hS : IsAtomSpline odd S j) (hj : j ≠ 0) :
    IsSplineClass 1 1 true (quotSpline S) := by
  have hm := hS.spline.mesh
  have hx2 := length_two _ hm.x_first hm.x_last
  refine ⟨⟨hm.t_sorted, by simp [quotSpline], hm.t_first, hm.t_last, by simp [quotSpline], by simp [quotSpline]⟩, ?_, ?_, ?_⟩
  · intro i hi1 hi j' _ o ho
    change i < cellCount S.mesh.tBreaks at hi
    simp only [quotSpline]
    have hlast : atomLastX S < cellCount S.mesh.xBreaks := by
      unfold atomLastX cellCount; omega
    have h := hS.spline.t_joins i hi1 hi (atomLastX S) hlast o ho
    rw [piece_factor hS hj (i - 1) (by omega), piece_factor hS hj i hi, tDeriv_mul_left _ _ pderiv_one_sub,
      tDeriv_mul_left _ _ pderiv_one_sub, atFirst_mul, atFirst_mul, atFirst_one_sub] at h
    have h' := mul_left_cancel₀ one_sub_ne h
    rw [tDeriv_mul_left _ _ pderiv_X_one, tDeriv_mul_left _ _ pderiv_X_one, atFirst_mul, atFirst_mul, h']
  · intro j' hj1 hj'
    simp [quotSpline, cellCount] at hj'
    omega
  · intro i _ o ho hev
    have ho0 : o = 0 := by
      have : Even o := by simpa using hev
      rcases Nat.even_or_odd o with h | h
      · interval_cases o
        · rfl
        · exact absurd h (by decide)
      · exact absurd this (Nat.not_even_iff_odd.2 h)
    subst ho0
    simp [xDeriv, atSecond, quotSpline, map_mul, MvPolynomial.bind₁_X_right]

theorem evalHalf_factor {odd : Bool} {S : Spline} {j : ℕ} (hS : IsAtomSpline odd S j) (hj : j ≠ 0) (t x : ℝ)
    (hx : 0 < x) (hall : ∀ b ∈ (S.mesh.xBreaks.drop 1).dropLast, b ≤ x) :
    (x : ℂ) * S.evalHalf t x = (1 - (x : ℂ)) * (quotSpline S).eval true t x := by
  have hm := hS.spline.mesh
  have hci : cellIndex S.mesh.xBreaks x = atomLastX S :=
    cellIndex_top _ _ hall
  have hti := cellIndex_lt S.mesh.tBreaks t (length_two _ hm.t_first hm.t_last)
  have hnx : ¬ x < 0 := not_lt.2 hx.le
  simp only [Spline.eval, Spline.evalHalf, abs_of_pos hx, hnx, decide_false, Bool.and_false]
  rw [hci, piece_factor hS hj _ hti]
  simp [quotSpline]
  ring

end AtomAxisInternal

namespace AtomAxisInternal

def planeW (z : Space) : ℂ := ⟨z 0, z 1⟩

theorem planeW_contDiff : ContDiff ℝ ⊤ planeW := by
  have e : planeW = fun y : Space => ((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I := by
    funext y
    apply Complex.ext <;> simp [planeW]
  rw [e]
  exact (Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).contDiff).add
    ((Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).contDiff).mul contDiff_const)

theorem norm_sq_split (z : Space) : ‖z‖ ^ 2 = ‖planeW z‖ ^ 2 + z 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Complex.sq_norm, Complex.normSq_apply]
  simp [planeW, sq_abs]
  ring

theorem ofReal_cd {f : Space → ℝ} {y : Space} (hf : ContDiffAt ℝ 1 f y) :
    ContDiffAt ℝ 1 (fun z => (f z : ℂ)) y :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp y hf

theorem norm_cd {y : Space} (hy : y ≠ 0) : ContDiffAt ℝ 1 (fun z : Space => ‖z‖) y :=
  contDiffAt_norm ℝ hy

theorem coord_cd (i : Fin 3) (y : Space) : ContDiffAt ℝ 1 (fun z : Space => z i) y :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.contDiffAt

theorem heightRatio_cd {y : Space} (hy : y ≠ 0) : ContDiffAt ℝ 1 heightRatio y :=
  (coord_cd 2 y).div (norm_cd hy) (norm_ne_zero_iff.2 hy)

theorem chartT_cd (P : ChartParams) (hP : IsChartParams P) {y : Space} (hy : y ≠ 0) :
    ContDiffAt ℝ 1 (chartT P) y := by
  have hne : ‖y‖ + P.L0 ≠ 0 := by have := hP.L0_pos; positivity
  exact (norm_cd hy).div ((norm_cd hy).add contDiffAt_const) hne

theorem decay_cd (P : ChartParams) (hP : IsChartParams P) {y : Space} (hy : y ≠ 0) :
    ContDiffAt ℝ 1 (decayFactor P) y := by
  have hs : chartS P y ≠ 0 := by
    unfold chartS chartT
    have hL := hP.L0_pos
    have hn : 0 ≤ ‖y‖ := norm_nonneg y
    have hd : 0 < ‖y‖ + P.L0 := by positivity
    rw [sub_ne_zero]
    intro h
    rw [eq_comm, div_eq_one_iff_eq hd.ne'] at h
    linarith
  exact (contDiffAt_const.sub (chartT_cd P hP hy)).rpow_const_of_ne hs

theorem logPhase_cd (P : ChartParams) (hP : IsChartParams P) (y : Space) : ContDiffAt ℝ 1 (logPhase P) y := by
  unfold logPhase
  refine contDiffAt_const.mul (ContDiffAt.log (contDiffAt_const.add ((contDiff_norm_sq ℝ).contDiffAt.div_const _)) ?_)
  have := hP.rc_pos
  positivity

def axisForm (P : ChartParams) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline) (s : ℝ) (z : Space) : ℂ :=
  ((decayFactor P z : ℝ) : ℂ) * Complex.exp (Complex.I * (((j : ℝ) * β * logPhase P z : ℝ) : ℂ)) *
    ((((‖planeW z‖ ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((((M - a : ℤ) : ℝ) * Complex.arg (planeW z) : ℝ) : ℂ))) *
      planeW z ^ a) *
    ((((‖z‖ ^ a)⁻¹ * (‖z‖ * (‖z‖ + s * z 2))⁻¹ * (s * heightRatio z)⁻¹ : ℝ)) : ℂ) *
    (if decide (a = 0) && decide (s < 0) then (-1 : ℂ) else 1) *
    (quotSpline S).eval true (chartT P z) (s * heightRatio z)

theorem point_identity (P : ChartParams) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (hS : IsAtomSpline (decide (a = 0)) S j) (hj : j ≠ 0) (s : ℝ) (hs2 : s = 1 ∨ s = -1) (z : Space) (hz : z ≠ 0)
    (hx : 0 < s * heightRatio z) (hall : ∀ b ∈ (S.mesh.xBreaks.drop 1).dropLast, b ≤ s * heightRatio z)
    (hd : 0 < ‖z‖ + s * z 2) :
    ((decayFactor P z : ℝ) : ℂ) * atomTerm P j a M β S z = axisForm P j a M β S s z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hsq := norm_sq_split z
  have hss : s * s = 1 := by rcases hs2 with h | h <;> rw [h] <;> norm_num
  have hev : S.eval (decide (a = 0)) (chartT P z) (heightRatio z) =
      (if decide (a = 0) && decide (s < 0) then (-1 : ℂ) else 1) *
        S.evalHalf (chartT P z) (s * heightRatio z) := by
    unfold Spline.eval
    rcases hs2 with rfl | rfl
    · have h1 : 0 < heightRatio z := by linarith
      have h2 : ¬ heightRatio z < 0 := not_lt.2 h1.le
      simp [h2, abs_of_pos h1]
    · have h1 : heightRatio z < 0 := by linarith
      simp [h1, abs_of_neg h1]
  have hhalf := evalHalf_factor hS hj (chartT P z) (s * heightRatio z) hx hall
  have hne : ((s * heightRatio z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hEH : S.evalHalf (chartT P z) (s * heightRatio z) =
      (((1 - s * heightRatio z) * (s * heightRatio z)⁻¹ : ℝ) : ℂ) *
        (quotSpline S).eval true (chartT P z) (s * heightRatio z) := by
    apply mul_left_cancel₀ hne
    rw [hhalf]
    have hne' : (s : ℂ) * (heightRatio z : ℂ) ≠ 0 := by push_cast at hne; exact hne
    have hs0 : (s : ℂ) ≠ 0 := left_ne_zero_of_mul hne'
    have hx0 : (heightRatio z : ℂ) ≠ 0 := right_ne_zero_of_mul hne'
    push_cast
    field_simp
  have hfac : 1 - s * heightRatio z = ‖planeW z‖ ^ 2 * (‖z‖ * (‖z‖ + s * z 2))⁻¹ := by
    have e1 : (1 - s * heightRatio z) * (‖z‖ * (‖z‖ + s * z 2)) = ‖z‖ ^ 2 - (s * s) * z 2 ^ 2 := by
      unfold heightRatio
      field_simp
      ring
    rw [← div_eq_mul_inv, eq_div_iff (mul_pos hn hd).ne', e1, hss, hsq]
    ring
  have hsqrt : Real.sqrt (qOf z) = ‖planeW z‖ * ‖z‖⁻¹ := by
    have e2 : qOf z = (‖planeW z‖ * ‖z‖⁻¹) ^ 2 := by
      unfold qOf heightRatio
      field_simp
      linear_combination hsq
    rw [e2, Real.sqrt_sq (by positivity)]
  have hθ : angleOf z = Complex.arg (planeW z) := rfl
  have hexp : Complex.exp (Complex.I * (((j : ℝ) * β * logPhase P z + (M : ℝ) * angleOf z : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (((j : ℝ) * β * logPhase P z : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((((M - a : ℤ) : ℝ) * Complex.arg (planeW z) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (((a : ℝ) * Complex.arg (planeW z) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, hθ]
    congr 1
    push_cast
    ring
  have hwa : planeW z ^ a = ((‖planeW z‖ : ℝ) : ℂ) ^ a *
      Complex.exp (Complex.I * (((a : ℝ) * Complex.arg (planeW z) : ℝ) : ℂ)) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (planeW z)]
    rw [mul_pow, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  unfold atomTerm axisForm
  rw [hexp, hsqrt, hev, hEH, hfac, hwa]
  push_cast
  ring

end AtomAxisInternal

namespace AtomAxisInternal

theorem axis_main (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (hS : IsAtomSpline (decide (a = 0)) S j) (hj : j ≠ 0) (y : Space) (hy : y ≠ 0)
    (h0 : y 0 = 0) (h1 : y 1 = 0) :
    ContDiffAt ℝ 1 (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) y := by
  set s : ℝ := if 0 < y 2 then 1 else -1 with hsdef
  have hw0 : planeW y = 0 := by apply Complex.ext <;> simp [planeW, h0, h1]
  have hny : ‖y‖ ^ 2 = y 2 ^ 2 := by rw [norm_sq_split, hw0]; simp
  have hnpos : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hsy : s * y 2 = ‖y‖ := by
    have habs : ‖y‖ = |y 2| := by
      rw [← Real.sqrt_sq (norm_nonneg y), hny, Real.sqrt_sq_eq_abs]
    rw [habs]
    by_cases h : 0 < y 2
    · simp [hsdef, h, abs_of_pos h]
    · have h' : y 2 ≤ 0 := not_lt.1 h
      simp [hsdef, h, abs_of_nonpos h']
  have hs2 : s = 1 ∨ s = -1 := by by_cases h : 0 < y 2 <;> simp [hsdef, h]
  have hxy : s * heightRatio y = 1 := by
    unfold heightRatio
    rw [← mul_div_assoc, hsy, div_self hnpos.ne']
  have hdy : ‖y‖ + s * y 2 = 2 * ‖y‖ := by rw [hsy]; ring
  have hcx : ContinuousAt (fun z => s * heightRatio z) y :=
    continuousAt_const.mul (heightRatio_cd hy).continuousAt
  have hcd : ContinuousAt (fun z : Space => ‖z‖ + s * z 2) y :=
    (norm_cd hy).continuousAt.add (continuousAt_const.mul (coord_cd 2 y).continuousAt)
  have E1 : ∀ᶠ z in 𝓝 y, z ≠ 0 := eventually_ne_nhds hy
  have E2 : ∀ᶠ z in 𝓝 y, 0 < s * heightRatio z :=
    hcx.eventually (lt_mem_nhds (by show 0 < s * heightRatio y; rw [hxy]; norm_num))
  have E3 : ∀ᶠ z in 𝓝 y, ∀ b ∈ ((S.mesh.xBreaks.drop 1).dropLast).toFinset, b ≤ s * heightRatio z := by
    rw [Filter.eventually_all_finset]
    intro b hb
    have hb1 := interior_lt_one _ hS.spline.mesh.x_sorted hS.spline.mesh.x_last b (List.mem_toFinset.1 hb)
    exact (hcx.eventually (lt_mem_nhds (by show b < s * heightRatio y; rw [hxy]; exact hb1))).mono fun z hz => hz.le
  have E4 : ∀ᶠ z in 𝓝 y, 0 < ‖z‖ + s * z 2 :=
    hcd.eventually (lt_mem_nhds (by show 0 < ‖y‖ + s * y 2; rw [hdy]; positivity))
  have heq : (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) =ᶠ[𝓝 y] axisForm P j a M β S s := by
    filter_upwards [E1, E2, E3, E4] with z hz hx hall hd
    exact point_identity P j a M β S hS hj s hs2 z hz hx (fun b hb => hall b (List.mem_toFinset.2 hb)) hd
  refine ContDiffAt.congr_of_eventuallyEq ?_ heq
  have hG : ContDiff ℝ 1 (fun p : ℝ × ℝ => (quotSpline S).eval true p.1 p.2) :=
    spline_eval_contDiff _ (quotSpline_class hS hj) le_rfl le_rfl
  have hpair : ContDiffAt ℝ 1 (fun z => (chartT P z, s * heightRatio z)) y :=
    (chartT_cd P hP hy).prodMk (contDiffAt_const.mul (heightRatio_cd hy))
  have cG : ContDiffAt ℝ 1 (fun z => (quotSpline S).eval true (chartT P z) (s * heightRatio z)) y :=
    hG.contDiffAt.comp y hpair
  have cD := ofReal_cd (decay_cd P hP hy)
  have cE : ContDiffAt ℝ 1 (fun z => Complex.exp (Complex.I * (((j : ℝ) * β * logPhase P z : ℝ) : ℂ))) y :=
    Complex.contDiff_exp.contDiffAt.comp y
      (contDiffAt_const.mul (ofReal_cd (contDiffAt_const.mul (logPhase_cd P hP y))))
  have cΦ := (planePhase_contDiff (M - a)).contDiffAt.comp y ((planeW_contDiff.of_le le_top).contDiffAt (x := y))
  have cWa : ContDiffAt ℝ 1 (fun z => planeW z ^ a) y := ((planeW_contDiff.of_le le_top).contDiffAt).pow a
  have hne2 : ‖y‖ * (‖y‖ + s * y 2) ≠ 0 := by
    rw [hdy]
    exact mul_ne_zero hnpos.ne' (mul_ne_zero two_ne_zero hnpos.ne')
  have cK : ContDiffAt ℝ 1 (fun z : Space => (‖z‖ ^ a)⁻¹ * (‖z‖ * (‖z‖ + s * z 2))⁻¹ * (s * heightRatio z)⁻¹) y :=
    ((((norm_cd hy).pow a).inv (pow_ne_zero _ hnpos.ne')).mul
      (((norm_cd hy).mul ((norm_cd hy).add (contDiffAt_const.mul (coord_cd 2 y)))).inv hne2)).mul
      ((contDiffAt_const.mul (heightRatio_cd hy)).inv (by rw [hxy]; norm_num))
  exact ((((cD.mul cE).mul (cΦ.mul cWa)).mul (ofReal_cd cK)).mul contDiffAt_const).mul cG

end AtomAxisInternal

theorem atomScalar_contDiffAt_axis (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (ha : a ≤ 1) (hS : IsAtomSpline (decide (a = 0)) S j) (hM : j = 0 → M.natAbs = a) :
    j ≠ 0 → ∀ y : Space, y ≠ 0 → y 0 = 0 → y 1 = 0 → ContDiffAt ℝ 1 (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) y := by
  intro hj y hy h0 h1
  clear hM ha
  exact AtomAxisInternal.axis_main P hP j a M β S hS hj y hy h0 h1

end GivenFields

end CellCert

end Breakdown
