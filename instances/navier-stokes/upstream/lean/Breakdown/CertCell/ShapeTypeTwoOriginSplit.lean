import Breakdown.CertCell.ShapeTypeTwoOriginScale
import Breakdown.CertCell.ShapeSplineDeriv

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline TensorMesh cellCount cellIndex atFirst atSecond tDeriv xDeriv weightPoly
  radialScale heightDeriv heightRatio qOf radialVec polarVecQ azimVecQ)

namespace Internal

namespace TypeTwoNear

theorem pos_lower_bound (L : List ℝ) (h : ∀ b ∈ L, 0 < b) : ∃ c > 0, ∀ b ∈ L, c ≤ b := by
  induction L with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons b L ih =>
    obtain ⟨c, hc, hcL⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨min b c, lt_min (h b (by simp)) hc, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hcL x hx)

theorem first_cell_zero (l : List ℝ) (hs : l.Pairwise (· < ·)) (h0 : l.head? = some 0) :
    ∃ c > 0, ∀ t < c, cellIndex l t = 0 := by
  obtain ⟨r, rfl⟩ : ∃ r, l = 0 :: r := by
    cases l with
    | nil => simp at h0
    | cons a r => simp at h0; exact ⟨r, by rw [h0]⟩
  obtain ⟨c, hc, hcr⟩ := pos_lower_bound r (fun b hb => List.rel_of_pairwise_cons hs hb)
  refine ⟨c, hc, fun t ht => ?_⟩
  unfold cellIndex
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro b hb
  have hb' : b ∈ r := by simpa using List.mem_of_mem_dropLast hb
  simpa using lt_of_lt_of_le ht (hcr b hb')

theorem atFirst_mul_X (c : ℂ) (p : MvPolynomial (Fin 2) ℂ) (i : Fin 2) :
    atFirst c (p * MvPolynomial.X i) =
      atFirst c p * (if i = 0 then MvPolynomial.C c else MvPolynomial.X 1) := by
  simp [atFirst]

theorem sub_atFirst_dvd (R : MvPolynomial (Fin 2) ℂ) : MvPolynomial.X 0 ∣ R - atFirst 0 R := by
  induction R using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp [atFirst]⟩
  | add p r hp hr =>
    have e : p + r - atFirst 0 (p + r) = (p - atFirst 0 p) + (r - atFirst 0 r) := by
      simp only [atFirst, map_add]
      ring
    rw [e]
    exact dvd_add hp hr
  | mul_X p i hp =>
    obtain ⟨q, hq⟩ := hp
    rw [atFirst_mul_X]
    fin_cases i
    · exact ⟨p, by simp; ring⟩
    · refine ⟨q * MvPolynomial.X 1, ?_⟩
      have e : p * MvPolynomial.X 1 - atFirst 0 p * MvPolynomial.X 1 = (p - atFirst 0 p) * MvPolynomial.X 1 := by ring
      simp only [Fin.mk_one, one_ne_zero, if_false]
      rw [e, hq]
      ring

theorem atSecond_X0_mul (c : ℂ) (q : MvPolynomial (Fin 2) ℂ) :
    atSecond c (MvPolynomial.X 0 * q) = MvPolynomial.X 0 * atSecond c q := by
  simp [atSecond]

theorem xDeriv_X0_mul (o : ℕ) (q : MvPolynomial (Fin 2) ℂ) :
    xDeriv o (MvPolynomial.X 0 * q) = MvPolynomial.X 0 * xDeriv o q := by
  induction o generalizing q with
  | zero => rfl
  | succ o ih =>
    simp only [xDeriv, Function.iterate_succ_apply] at ih ⊢
    have : MvPolynomial.pderiv 1 (MvPolynomial.X 0 * q) = MvPolynomial.X 0 * MvPolynomial.pderiv 1 q := by
      rw [Derivation.leibniz, MvPolynomial.pderiv_X_of_ne (by decide)]
      simp
    rw [this, ih]

theorem first_row_quotient {a b : ℕ} (S : Spline) (hS : IsJoinedSpline a b S)
    (h0 : ∀ j < cellCount S.mesh.xBreaks, atFirst 0 (S.piece 0 j) = 0) :
    ∃ T : Spline, IsJoinedSpline 2 b T ∧ ∃ c > 0, ∀ t < c, ∀ x : ℝ, S.evalHalf t x = (t : ℂ) * T.evalHalf t x := by
  have hQ : ∀ j, ∃ Q : MvPolynomial (Fin 2) ℂ, S.piece 0 j - atFirst 0 (S.piece 0 j) = MvPolynomial.X 0 * Q :=
    fun j => sub_atFirst_dvd (S.piece 0 j)
  choose Q hQ using hQ
  have hP : ∀ j < cellCount S.mesh.xBreaks, S.piece 0 j = MvPolynomial.X 0 * Q j := by
    intro j hj
    have := hQ j
    rwa [h0 j hj, sub_zero] at this
  have htl := Internal.two_le_length S.mesh.tBreaks (by norm_num) hS.mesh.t_first hS.mesh.t_last
  have hxl := Internal.two_le_length S.mesh.xBreaks (by norm_num) hS.mesh.x_first hS.mesh.x_last
  have hct : 0 < cellCount S.mesh.tBreaks := by unfold cellCount; omega
  obtain ⟨c, hc, hci⟩ := first_cell_zero _ hS.mesh.t_sorted hS.mesh.t_first
  have hX : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ≠ 0 := MvPolynomial.X_ne_zero 0
  refine ⟨⟨⟨[0, 1], S.mesh.xBreaks⟩, fun _ j => Q j⟩, ⟨⟨by simp, hS.mesh.x_sorted, by simp, by simp,
    hS.mesh.x_first, hS.mesh.x_last⟩, ?_, ?_⟩, c, hc, ?_⟩
  · intro i hi1 hi2
    simp [cellCount] at hi2
    omega
  · intro j hj1 hj2 i _ o ho
    have hj2' : j < cellCount S.mesh.xBreaks := hj2
    have h := hS.x_joins j hj1 hj2' 0 hct o ho
    rw [hP (j - 1) (by omega), hP j hj2', xDeriv_X0_mul, xDeriv_X0_mul, atSecond_X0_mul, atSecond_X0_mul] at h
    exact mul_left_cancel₀ hX h
  · intro t ht x
    have hj := Internal.cellIndex_lt_count _ hxl x
    have hT0 : cellIndex [0, 1] t = 0 := by simp [cellIndex]
    simp only [Spline.evalHalf, hci t ht, hP _ hj, map_mul, MvPolynomial.eval_X]
    simp

theorem spline_differentiable (hsm : JoinedSplineSmooth) {a b : ℕ} {S : Spline} (hS : IsJoinedSpline a b S)
    (ha : 1 ≤ a) (hb : 1 ≤ b) : Differentiable ℝ (fun p : ℝ × ℝ => S.evalHalf p.1 p.2) :=
  ((hsm a b S hS).of_le (le_min (by exact_mod_cast ha) (by exact_mod_cast hb))).differentiable one_ne_zero

theorem spline_tame (hsm : JoinedSplineSmooth) (hsl : JoinedSplineGradSlopeBound) {a b : ℕ} {S : Spline}
    (hS : IsJoinedSpline a b S) (ha : 1 ≤ a) (hb : 1 ≤ b) (q : ℝ × ℝ) :
    TameAt (fun p : ℝ × ℝ => S.evalHalf p.1 p.2) q :=
  tame_of_slope (spline_differentiable hsm hS ha hb) (hsl a b S hS ha hb) q

theorem spline_hasDerivAt_x (hsm : JoinedSplineSmooth) {a b : ℕ} {S : Spline} (hS : IsJoinedSpline a b S)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (t x : ℝ) :
    HasDerivAt (fun x' => S.evalHalf t x') ((xDerivSpline S).evalHalf t x) x := by
  have h1 : DifferentiableAt ℝ (fun x' : ℝ => (t, x')) x := (differentiableAt_const _).prodMk differentiableAt_id
  have hd : DifferentiableAt ℝ ((fun p : ℝ × ℝ => S.evalHalf p.1 p.2) ∘ (fun x' : ℝ => (t, x'))) x :=
    (spline_differentiable hsm hS ha hb (t, x)).comp x h1
  have e : ((fun p : ℝ × ℝ => S.evalHalf p.1 p.2) ∘ (fun x' : ℝ => (t, x'))) = fun x' => S.evalHalf t x' := rfl
  have h := hd.hasDerivAt
  rw [e] at h
  rwa [((splineDerivatives_holds a b S hS).2 hb).2 t x] at h

theorem spline_hasDerivAt_t (hsm : JoinedSplineSmooth) {a b : ℕ} {S : Spline} (hS : IsJoinedSpline a b S)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (t x : ℝ) :
    HasDerivAt (fun t' => S.evalHalf t' x) ((tDerivSpline S).evalHalf t x) t := by
  have h1 : DifferentiableAt ℝ (fun t' : ℝ => (t', x)) t := differentiableAt_id.prodMk (differentiableAt_const _)
  have hd : DifferentiableAt ℝ ((fun p : ℝ × ℝ => S.evalHalf p.1 p.2) ∘ (fun t' : ℝ => (t', x))) t :=
    (spline_differentiable hsm hS ha hb (t, x)).comp t h1
  have e : ((fun p : ℝ × ℝ => S.evalHalf p.1 p.2) ∘ (fun t' : ℝ => (t', x))) = fun t' => S.evalHalf t' x := rfl
  have h := hd.hasDerivAt
  rw [e] at h
  rwa [((splineDerivatives_holds a b S hS).1 ha).2 t x] at h

def wt (e : ℕ) (t : ℝ) : ℂ := (((1 - t) ^ e : ℝ) : ℂ)

def wtDeriv (e : ℕ) (t : ℝ) : ℂ := (((e : ℝ) * (1 - t) ^ (e - 1) * (-1) : ℝ) : ℂ)

def geomTail (e : ℕ) (t : ℝ) : ℂ := ((∑ i ∈ Finset.range e, (1 - t) ^ i : ℝ) : ℂ)

def profQuot (gq : Polynomial ℝ) (e : ℕ) (t : ℝ) : ℂ :=
  ((gq.eval t : ℝ) : ℂ) - geomTail e t - (t : ℂ) * geomTail e t * ((gq.eval t : ℝ) : ℂ)

def slopeQuot (P : ShapeParams) (t : ℝ) : ℝ :=
  2 * (P.chartLength / (1 - t)) ^ 2 * t * deriv P.radialPhase ((P.chartLength * t / (1 - t)) ^ 2)

def streamFull (P : ShapeParams) (A : KeyAmp) (t x : ℝ) : ℂ :=
  A.axisCoef * ((P.origin.poly.eval t * x : ℝ) : ℂ) + A.stream.evalHalf t x

def streamFullT (P : ShapeParams) (A : KeyAmp) (t x : ℝ) : ℂ :=
  A.axisCoef * ((P.origin.poly.derivative.eval t * x : ℝ) : ℂ) + (tDerivSpline A.stream).evalHalf t x

def leadComp (α : ℂ) (x : ℝ) : Fin 3 → ℂ := ![-(α * ((1 - 3 * x ^ 2 : ℝ) : ℂ)), -(3 * α * (x : ℂ)), 0]

def remComp (P : ShapeParams) (A : KeyAmp) (j : ℤ) (gq : Polynomial ℝ) (S1 G1 : Spline) (t x : ℝ) : Fin 3 → ℂ :=
  ![-(A.axisCoef * ((1 - 3 * x ^ 2 : ℝ) : ℂ) * profQuot gq A.highOrder t +
      wt A.highOrder t * (((-2 * x : ℝ) : ℂ) * S1.evalHalf t x + ((1 - x ^ 2 : ℝ) : ℂ) * (xDerivSpline S1).evalHalf t x)),
    -(3 * A.axisCoef * (x : ℂ) * profQuot gq A.highOrder t -
      A.axisCoef * (x : ℂ) * wt A.highOrder t * ((P.origin.poly.eval t : ℝ) : ℂ) +
      ((3 - t : ℝ) : ℂ) * wt A.highOrder t * S1.evalHalf t x +
      ((1 - t : ℝ) : ℂ) * (wtDeriv A.highOrder t * streamFull P A t x + wt A.highOrder t * streamFullT P A t x) +
      Complex.I * (((j : ℝ) * slopeQuot P t : ℝ) : ℂ) * (wt A.highOrder t * streamFull P A t x)),
    wt A.highOrder t * G1.evalHalf t x]

theorem reduced_split (hsm : JoinedSplineSmooth) (P : ShapeParams) (κ : FieldKey) (A : KeyAmp)
    (h0 : κ.label.1 = 0) (hstream : IsJoinedSpline 2 2 A.stream) (gq : Polynomial ℝ)
    (hgq : ∀ t, P.origin.poly.eval t = 1 + t * gq.eval t) (S1 G1 : Spline) (hS1 : IsJoinedSpline 2 2 S1)
    (T0 : ℝ) (hTe : T0 ≤ P.origin.edge)
    (hsS : ∀ t < T0, ∀ x, A.stream.evalHalf t x = (t : ℂ) * S1.evalHalf t x)
    (hsG : ∀ t < T0, ∀ x, A.swirl.evalHalf t x = (t : ℂ) * G1.evalHalf t x) (t : ℝ) (ht : t < T0) (x : ℝ)
    (k : Fin 3) :
    reducedComps P κ A t x k = (t : ℂ) * leadComp A.axisCoef x k +
      ((t ^ 2 : ℝ) : ℂ) * remComp P A κ.phaseIndex gq S1 G1 t x k := by
  have hg : ∀ t' < T0, P.origin.eval t' = P.origin.poly.eval t' := fun t' h' => by
    unfold OriginProfile.eval
    rw [if_pos (h'.le.trans hTe)]
  have hwgeom : ((1 - t) ^ A.highOrder : ℝ) = 1 - t * ∑ i ∈ Finset.range A.highOrder, (1 - t) ^ i := by
    have := geom_sum_mul (1 - t) A.highOrder
    linear_combination -this
  have hw : wt A.highOrder t = 1 - (t : ℂ) * geomTail A.highOrder t := by
    unfold wt geomTail
    rw [hwgeom]
    push_cast
    ring
  have hgc : ((P.origin.poly.eval t : ℝ) : ℂ) = 1 + (t : ℂ) * ((gq.eval t : ℝ) : ℂ) := by
    rw [hgq]
    push_cast
    ring
  have hwp : weightPoly 1 A.highOrder t = (t : ℂ) * wt A.highOrder t := by
    unfold weightPoly wt
    push_cast
    ring
  fin_cases k
  · have hS1x := spline_hasDerivAt_x hsm hS1 (by norm_num) (by norm_num) t x
    have hd1 : HasDerivAt (fun x' : ℝ => (((P.origin.poly.eval t) * (x' - x' ^ 3) : ℝ) : ℂ))
        (((P.origin.poly.eval t) * (1 - 3 * x ^ 2) : ℝ) : ℂ) x := by
      have h1 := (((hasDerivAt_id x).sub (hasDerivAt_pow 3 x)).const_mul (P.origin.poly.eval t)).ofReal_comp
      refine h1.congr_deriv ?_
      push_cast
      ring
    have hd2 : HasDerivAt (fun x' : ℝ => ((1 - x' ^ 2 : ℝ) : ℂ)) ((-2 * x : ℝ) : ℂ) x := by
      have h1 := ((hasDerivAt_pow 2 x).const_sub 1).ofReal_comp
      refine h1.congr_deriv ?_
      push_cast
      ring
    have hd := (hd1.const_mul A.axisCoef).add ((hd2.mul hS1x).const_mul (t : ℂ))
    have ef : (fun x' : ℝ => polarFactor x' * streamValue P A t x') =
        fun x' => A.axisCoef * (((P.origin.poly.eval t) * (x' - x' ^ 3) : ℝ) : ℂ) +
          (t : ℂ) * (((1 - x' ^ 2 : ℝ) : ℂ) * S1.evalHalf t x') := by
      funext x'
      simp only [polarFactor, streamValue, hg t ht, hsS t ht x']
      push_cast
      ring
    have hder : heightDeriv (fun t' x' => polarFactor x' * streamValue P A t' x') t x =
        A.axisCoef * (((P.origin.poly.eval t) * (1 - 3 * x ^ 2) : ℝ) : ℂ) +
          (t : ℂ) * (((-2 * x : ℝ) : ℂ) * S1.evalHalf t x + ((1 - x ^ 2 : ℝ) : ℂ) * (xDerivSpline S1).evalHalf t x) := by
      show deriv (fun x' => polarFactor x' * streamValue P A t x') x = _
      rw [ef]
      exact hd.deriv
    simp only [reducedComps, if_pos h0, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, leadComp, remComp]
    rw [hder, hwp]
    unfold profQuot
    push_cast
    linear_combination (-(A.axisCoef * (1 - 3 * (x : ℂ) ^ 2) * (t : ℂ) * ((P.origin.poly.eval t : ℝ) : ℂ))) * hw +
      (-(A.axisCoef * (1 - 3 * (x : ℂ) ^ 2) * (t : ℂ) * (1 - (t : ℂ) * geomTail A.highOrder t))) * hgc
  · have hev : (fun t' => weightPoly 1 A.highOrder t' * streamValue P A t' x) =ᶠ[nhds t]
        (fun t' => weightPoly 1 A.highOrder t' * streamFull P A t' x) := by
      filter_upwards [Iio_mem_nhds ht] with t' ht'
      simp only [streamValue, streamFull, hg t' ht']
    have hp : HasDerivAt (fun t' : ℝ => weightPoly 1 A.highOrder t')
        (wt A.highOrder t + (t : ℂ) * wtDeriv A.highOrder t) t := by
      have h1 := ((hasDerivAt_pow 1 t).mul (((hasDerivAt_id t).const_sub 1).pow A.highOrder)).ofReal_comp
      convert h1 using 1
      · funext t'
        simp [weightPoly]
      · simp only [wt, wtDeriv, id, Pi.pow_apply]
        push_cast
        ring
    have hΨ : HasDerivAt (fun t' => streamFull P A t' x) (streamFullT P A t x) t := by
      have h1 := (((Polynomial.hasDerivAt P.origin.poly t).mul_const x).ofReal_comp).const_mul A.axisCoef
      have h2 := spline_hasDerivAt_t hsm hstream (by norm_num) (by norm_num) t x
      exact h1.add h2
    have hder : deriv (fun t' => weightPoly 1 A.highOrder t' * streamValue P A t' x) t =
        (wt A.highOrder t + (t : ℂ) * wtDeriv A.highOrder t) * streamFull P A t x +
          weightPoly 1 A.highOrder t * streamFullT P A t x := by
      rw [hev.deriv_eq]
      exact (hp.mul hΨ).deriv
    have hph : ((phaseSlope P t : ℝ) : ℂ) = (t : ℂ) * (slopeQuot P t : ℂ) := by
      unfold phaseSlope chartRadius slopeQuot
      push_cast
      ring
    have hΨv : streamFull P A t x = A.axisCoef * (((P.origin.poly.eval t : ℝ) : ℂ) * (x : ℂ)) + (t : ℂ) * S1.evalHalf t x := by
      unfold streamFull
      rw [hsS t ht x]
      push_cast
      ring
    have hsv : streamValue P A t x = streamFull P A t x := by simp only [streamValue, streamFull, hg t ht]
    simp only [reducedComps, if_pos h0, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
      shiftedScale, radialScale, leadComp, remComp]
    rw [hder, hsv, hwp]
    unfold profQuot
    push_cast
    linear_combination (-((t : ℂ) * (3 - (t : ℂ)) * wt A.highOrder t)) * hΨv +
      (-(Complex.I * (κ.phaseIndex : ℂ) * (t : ℂ) * wt A.highOrder t * streamFull P A t x)) * hph +
      (-(3 * A.axisCoef * (x : ℂ) * (t : ℂ) * ((P.origin.poly.eval t : ℝ) : ℂ))) * hw +
      (-(3 * A.axisCoef * (x : ℂ) * (t : ℂ) * (1 - (t : ℂ) * geomTail A.highOrder t))) * hgc
  · simp only [reducedComps, if_pos h0, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, leadComp, remComp]
    rw [hwp, hsG t ht x]
    push_cast
    ring

end TypeTwoNear

end Internal

end GivenShape

end CertCell

end Breakdown
