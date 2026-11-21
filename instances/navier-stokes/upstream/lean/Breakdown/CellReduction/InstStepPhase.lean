import Breakdown.CellReduction.InstanceStatements

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape
open CellCert.GivenFields (cellCount cellIndex)

namespace Internal

theorem stepPoly_contDiff (P : Polynomial ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun x : ℝ => P.eval x) := by
  simpa using P.contDiff_aeval (𝕜 := ℝ) n

theorem stepGlue_contDiff (k : ℕ) : ∀ (P Q : Polynomial ℝ) (a : ℝ),
    (∀ o ≤ k, (Polynomial.derivative^[o] P).eval a = (Polynomial.derivative^[o] Q).eval a) →
    ContDiff ℝ k (fun t : ℝ => if a ≤ t then Q.eval t else P.eval t) := by
  induction k with
  | zero =>
    intro P Q a h
    have h0 := h 0 le_rfl
    simp only [Function.iterate_zero, id] at h0
    rw [Nat.cast_zero, contDiff_zero]
    exact Continuous.if_le (stepPoly_contDiff Q 0).continuous (stepPoly_contDiff P 0).continuous
      continuous_const continuous_id (fun x hx => by
        change a = x at hx
        rw [← hx]; exact h0.symm)
  | succ k ih =>
    intro P Q a h
    have h0 := h 0 (Nat.zero_le _)
    have h1 := h 1 (by omega)
    simp only [Function.iterate_zero, id, Function.iterate_one] at h0 h1
    have hd : ∀ t, HasDerivAt (fun t : ℝ => if a ≤ t then Q.eval t else P.eval t)
        (if a ≤ t then (Polynomial.derivative Q).eval t else (Polynomial.derivative P).eval t) t := by
      intro t
      rcases lt_trichotomy t a with hlt | heq | hgt
      · have hev : (fun t : ℝ => if a ≤ t then Q.eval t else P.eval t) =ᶠ[nhds t]
            fun t => P.eval t := by
          filter_upwards [Iio_mem_nhds hlt] with y hy
          rw [if_neg (not_le.mpr hy)]
        rw [if_neg (not_le.mpr hlt)]
        exact (P.hasDerivAt t).congr_of_eventuallyEq hev
      · rw [heq, if_pos le_rfl]
        have hQ : HasDerivWithinAt (fun t : ℝ => if a ≤ t then Q.eval t else P.eval t)
            ((Polynomial.derivative Q).eval a) (Set.Ici a) a :=
          (Q.hasDerivAt a).hasDerivWithinAt.congr_of_mem (fun y hy => if_pos hy) (Set.mem_Ici.mpr le_rfl)
        have hP : HasDerivWithinAt (fun t : ℝ => if a ≤ t then Q.eval t else P.eval t)
            ((Polynomial.derivative Q).eval a) (Set.Iic a) a := by
          rw [← h1]
          refine (P.hasDerivAt a).hasDerivWithinAt.congr_of_mem (fun y hy => ?_) (Set.mem_Iic.mpr le_rfl)
          by_cases hay : a ≤ y
          · rw [if_pos hay, le_antisymm hy hay, h0]
          · rw [if_neg hay]
        have hu := hP.union hQ
        rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at hu
      · have hev : (fun t : ℝ => if a ≤ t then Q.eval t else P.eval t) =ᶠ[nhds t]
            fun t => Q.eval t := by
          filter_upwards [Ioi_mem_nhds hgt] with y hy
          rw [if_pos (le_of_lt hy)]
        rw [if_pos (le_of_lt hgt)]
        exact (Q.hasDerivAt t).congr_of_eventuallyEq hev
    have hderiv : deriv (fun t : ℝ => if a ≤ t then Q.eval t else P.eval t) =
        fun t => if a ≤ t then (Polynomial.derivative Q).eval t else (Polynomial.derivative P).eval t :=
      funext fun t => (hd t).deriv
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by push_cast; rfl, contDiff_succ_iff_deriv]
    refine ⟨fun t => (hd t).differentiableAt, fun hk => absurd hk (by simp), ?_⟩
    rw [hderiv]
    refine ih _ _ a (fun o ho => ?_)
    have := h (o + 1) (by omega)
    simpa only [Function.iterate_succ_apply] using this

theorem stepFilter_sum (t : ℝ) : ∀ (m : List ℝ), m.Pairwise (· < ·) → ∀ (u : ℕ → ℝ),
    ∑ i ∈ Finset.range m.length, (if m.getD i 0 ≤ t then u i else 0) =
      ∑ i ∈ Finset.range (m.filter (fun b => decide (b ≤ t))).length, u i := by
  intro m
  induction m with
  | nil => intro _ u; simp
  | cons b m ih =>
    intro hm u
    rw [List.pairwise_cons] at hm
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    by_cases hb : b ≤ t
    · rw [List.filter_cons_of_pos (by simpa using hb), List.length_cons, Finset.sum_range_succ',
        ih hm.2 (fun i => u (i + 1)), if_pos hb]
    · have hnil : m.filter (fun x => decide (x ≤ t)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        have := hm.1 x hx
        simp only [decide_eq_true_eq, not_le]
        linarith [not_le.mp hb]
      rw [List.filter_cons_of_neg (by simpa using hb), hnil, if_neg hb, List.length_nil,
        Finset.sum_range_zero, add_zero]
      apply Finset.sum_eq_zero
      intro i hi
      have hi' : i < m.length := Finset.mem_range.mp hi
      have hlt := hm.1 (m.getD i 0) (by rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem hi')
      rw [if_neg (fun hle => hb (le_trans (le_of_lt hlt) hle))]

theorem stepEval_decomp (S : StepProfile) (hs : S.breaks.Pairwise (· < ·)) (t : ℝ) :
    S.eval t = (S.piece 0).eval t + ∑ i ∈ Finset.range ((S.breaks.drop 1).dropLast).length,
      (if ((S.breaks.drop 1).dropLast).getD i 0 ≤ t then (S.piece (i + 1) - S.piece i).eval t
        else 0) := by
  have hm : ((S.breaks.drop 1).dropLast).Pairwise (· < ·) :=
    List.Pairwise.sublist ((List.dropLast_sublist _).trans (List.drop_sublist _ _)) hs
  rw [stepFilter_sum t _ hm (fun i => (S.piece (i + 1) - S.piece i).eval t)]
  simp only [Polynomial.eval_sub]
  rw [Finset.sum_range_sub (fun i => (S.piece i).eval t)]
  simp only [StepProfile.eval, cellIndex]
  ring

theorem stepInterior_getD (l : List ℝ) (i : ℕ) (hi : i < ((l.drop 1).dropLast).length) :
    ((l.drop 1).dropLast).getD i 0 = l.getD (i + 1) 0 := by
  have hi' : i + 1 < l.length := by
    simp only [List.length_dropLast, List.length_drop] at hi; omega
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi', List.getElem_dropLast,
    List.getElem_drop]
  simp only [Nat.add_comm 1 i]

theorem stepEval_contDiff (S : StepProfile) (edge : ℝ) (hS : IsStepProfile S edge) :
    ContDiff ℝ 2 S.eval := by
  rw [show S.eval = fun t => (S.piece 0).eval t + ∑ i ∈ Finset.range ((S.breaks.drop 1).dropLast).length,
      (if ((S.breaks.drop 1).dropLast).getD i 0 ≤ t then (S.piece (i + 1) - S.piece i).eval t
        else 0) from funext (stepEval_decomp S hS.sorted)]
  refine (stepPoly_contDiff _ _).add (ContDiff.sum fun i hi => ?_)
  have hi' := Finset.mem_range.mp hi
  have hlen : i + 2 < S.breaks.length := by
    simp only [List.length_dropLast, List.length_drop] at hi'; omega
  have hg := stepGlue_contDiff 2 0 (S.piece (i + 1) - S.piece i)
    (((S.breaks.drop 1).dropLast).getD i 0) (fun o ho => by
      have hj := hS.joins (i + 1) (by omega) (by unfold cellCount; omega) o ho
      simp only [Nat.add_sub_cancel] at hj
      rw [stepInterior_getD _ _ hi', Polynomial.iterate_derivative_zero,
        Polynomial.iterate_derivative_sub, Polynomial.eval_sub, Polynomial.eval_zero, hj, sub_self])
  simpa only [Polynomial.eval_zero, Nat.cast_ofNat] using hg

theorem stepEval_zero_lt (S : StepProfile) (edge : ℝ) (hS : IsStepProfile S edge) (t : ℝ)
    (ht : t < edge) : S.eval t = 0 := by
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp hS.edge_mem
  have hmono : ∀ i j (hi : i < S.breaks.length) (hj : j < S.breaks.length), i < j →
      S.breaks[i] < S.breaks[j] :=
    fun i j hi hj hij => List.pairwise_iff_getElem.mp hS.sorted i j hi hj hij
  have hfirst : ∀ (l : List ℝ) (h : 0 < l.length), l.head? = some 0 → l[0] = 0 := by
    intro l h hh
    cases l with
    | nil => simp at h
    | cons x xs => simpa using hh
  have hk1 : k ≠ 0 := by
    rintro rfl
    have := hfirst S.breaks hk hS.first
    linarith [hS.edge_pos]
  rw [stepEval_decomp S hS.sorted t]
  have hP0 : S.piece 0 = 0 := by
    apply hS.zero_below 0 (by unfold cellCount; omega)
    rw [List.getD_eq_getElem _ _ (by omega), ← hke]
    rcases Nat.lt_or_ge 1 k with h | h
    · exact le_of_lt (hmono 1 k (by omega) hk h)
    · have : k = 1 := by omega
      subst this
      exact le_rfl
  rw [hP0, Polynomial.eval_zero, zero_add]
  apply Finset.sum_eq_zero
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hlen : i + 2 < S.breaks.length := by
    simp only [List.length_dropLast, List.length_drop] at hi'; omega
  split_ifs with hle
  · rw [stepInterior_getD _ _ hi', List.getD_eq_getElem _ _ (by omega)] at hle
    have hik : i + 1 < k := by
      by_contra hcon
      have hkle : S.breaks[k] ≤ S.breaks[i + 1] := by
        rcases Nat.lt_or_ge k (i + 1) with h | h
        · exact le_of_lt (hmono k (i + 1) hk (by omega) h)
        · have : k = i + 1 := by omega
          subst this
          exact le_rfl
      linarith
    have hz1 : S.piece i = 0 := hS.zero_below i (by unfold cellCount; omega) (by
      rw [List.getD_eq_getElem _ _ (by omega)]; linarith)
    have hz2 : S.piece (i + 1) = 0 := hS.zero_below (i + 1) (by unfold cellCount; omega) (by
      rw [List.getD_eq_getElem _ _ (by omega), ← hke]
      rcases Nat.lt_or_ge (i + 1 + 1) k with h | h
      · exact le_of_lt (hmono (i + 1 + 1) k (by omega) hk h)
      · have : k = i + 1 + 1 := by omega
        subst this
        exact le_rfl)
    rw [hz1, hz2, sub_zero, Polynomial.eval_zero]
  · rfl

theorem stepEval_zero_le (S : StepProfile) (edge : ℝ) (hS : IsStepProfile S edge) (t : ℝ)
    (ht : t ≤ edge) : S.eval t = 0 := by
  have hc : IsClosed {t : ℝ | S.eval t = 0} :=
    isClosed_eq (stepEval_contDiff S edge hS).continuous continuous_const
  have hsub : closure (Set.Iio edge) ⊆ {t : ℝ | S.eval t = 0} :=
    hc.closure_subset_iff.mpr (fun t ht => stepEval_zero_lt S edge hS t ht)
  rw [closure_Iio] at hsub
  exact hsub ht

theorem stepRatio_le (L edge r : ℝ) (he : edge < 1) (hr : -L < r)
    (hR : r ≤ L * edge / (1 - edge)) : r / (r + L) ≤ edge := by
  have h1 : 0 < 1 - edge := by linarith
  have h2 : 0 < r + L := by linarith
  rw [div_le_iff₀ h2]
  rw [le_div_iff₀ h1] at hR
  nlinarith

theorem stepRatio_ge (L t' r : ℝ) (hL : 0 < L) (ht : t' < 1) (hr : L * t' / (1 - t') ≤ r)
    (hr0 : 0 < r) : t' ≤ r / (r + L) := by
  rw [le_div_iff₀ (by linarith)]
  rw [div_le_iff₀ (by linarith)] at hr
  nlinarith

def stepIntegrand (L : ℝ) (S : StepProfile) (r : ℝ) : ℝ := S.eval (r / (r + L)) / r

def stepPrimitive (L : ℝ) (S : StepProfile) (x : ℝ) : ℝ := ∫ r in (0 : ℝ)..x, stepIntegrand L S r

theorem stepPhase_eq_primitive (L : ℝ) (S : StepProfile) (s : ℝ) :
    stepPhase L S s = stepPrimitive L S (Real.sqrt s) := rfl

variable {L edge : ℝ} {S : StepProfile}

theorem stepIntegrand_zero (hS : IsStepProfile S edge) (r : ℝ) (hr : -L < r)
    (hR : r ≤ L * edge / (1 - edge)) : stepIntegrand L S r = 0 := by
  unfold stepIntegrand
  rw [stepEval_zero_le S edge hS _ (stepRatio_le L edge r hS.edge_lt hr hR), zero_div]

theorem stepRadius_pos (hL : 0 < L) (hS : IsStepProfile S edge) : 0 < L * edge / (1 - edge) :=
  div_pos (mul_pos hL hS.edge_pos) (by linarith [hS.edge_lt])

theorem stepIntegrand_contDiffOn (hL : 0 < L) (hS : IsStepProfile S edge) :
    ContDiffOn ℝ 2 (stepIntegrand L S) (Set.Ioi (-L)) := by
  intro r hr
  have hr' : -L < r := hr
  apply ContDiffAt.contDiffWithinAt
  rcases lt_or_ge 0 r with h | h
  · have hχ := stepEval_contDiff S edge hS
    have hden : r + L ≠ 0 := by linarith
    show ContDiffAt ℝ 2 (fun r => S.eval (r / (r + L)) / r) r
    exact ((hχ.contDiffAt).comp r (contDiffAt_id.div (contDiffAt_id.add contDiffAt_const) hden)).div
      contDiffAt_id h.ne'
  · have hR := stepRadius_pos hL hS
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hr' (show r < L * edge / (1 - edge) by linarith)] with y hy
    exact stepIntegrand_zero hS y hy.1 hy.2.le

theorem stepIntegrand_intervalIntegrable (hL : 0 < L) (hS : IsStepProfile S edge) (a b : ℝ)
    (ha : -L < a) (hb : -L < b) : IntervalIntegrable (stepIntegrand L S) volume a b := by
  have hc : ContinuousOn (stepIntegrand L S) (Set.Ioi (-L)) :=
    (stepIntegrand_contDiffOn hL hS).continuousOn
  refine (hc.mono ?_).intervalIntegrable
  intro y hy
  rw [Set.mem_uIcc] at hy
  show -L < y
  rcases hy with h | h <;> linarith [h.1, h.2]

theorem stepPrimitive_hasDerivAt (hL : 0 < L) (hS : IsStepProfile S edge) (x : ℝ) (hx : -L < x) :
    HasDerivAt (stepPrimitive L S) (stepIntegrand L S x) x := by
  have hc : ContinuousOn (stepIntegrand L S) (Set.Ioi (-L)) :=
    (stepIntegrand_contDiffOn hL hS).continuousOn
  exact intervalIntegral.integral_hasDerivAt_right
    (stepIntegrand_intervalIntegrable hL hS 0 x (by linarith) hx)
    (hc.stronglyMeasurableAtFilter isOpen_Ioi x hx) (hc.continuousAt (Ioi_mem_nhds hx))

theorem stepPrimitive_contDiffOn (hL : 0 < L) (hS : IsStepProfile S edge) :
    ContDiffOn ℝ 3 (stepPrimitive L S) (Set.Ioi (-L)) := by
  rw [show (3 : WithTop ℕ∞) = 2 + 1 by norm_num, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun x hx => (stepPrimitive_hasDerivAt hL hS x hx).differentiableAt.differentiableWithinAt,
    fun h => absurd h (by simp), ?_⟩
  exact (stepIntegrand_contDiffOn hL hS).congr
    (fun x hx => (stepPrimitive_hasDerivAt hL hS x hx).deriv)

theorem stepPrimitive_zero (hL : 0 < L) (hS : IsStepProfile S edge) (x : ℝ) (hx0 : 0 ≤ x)
    (hx : x ≤ L * edge / (1 - edge)) : stepPrimitive L S x = 0 := by
  have heq : Set.EqOn (stepIntegrand L S) (fun _ => (0 : ℝ)) (Set.uIcc 0 x) := by
    intro r hr
    rw [Set.uIcc_of_le hx0] at hr
    exact stepIntegrand_zero hS r (by linarith [hr.1]) (le_trans hr.2 hx)
  unfold stepPrimitive
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_zero]

theorem stepPhase_zero (hL : 0 < L) (hS : IsStepProfile S edge) (s : ℝ)
    (hs : s ≤ (L * edge / (1 - edge)) ^ 2) : stepPhase L S s = 0 := by
  rw [stepPhase_eq_primitive]
  apply stepPrimitive_zero hL hS _ (Real.sqrt_nonneg _)
  calc Real.sqrt s ≤ Real.sqrt ((L * edge / (1 - edge)) ^ 2) := Real.sqrt_le_sqrt hs
    _ = _ := Real.sqrt_sq (stepRadius_pos hL hS).le

theorem stepPhase_contDiff (hL : 0 < L) (hS : IsStepProfile S edge) :
    ContDiff ℝ 3 (stepPhase L S) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  rcases lt_or_ge s ((L * edge / (1 - edge)) ^ 2) with hs | hs
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hs] with y hy
    exact stepPhase_zero hL hS y hy.le
  · have hs0 : 0 < s := lt_of_lt_of_le (pow_pos (stepRadius_pos hL hS) 2) hs
    have hq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
    have h1 : ContDiffAt ℝ 3 (stepPrimitive L S) (Real.sqrt s) :=
      (stepPrimitive_contDiffOn hL hS).contDiffAt (Ioi_mem_nhds (by linarith))
    exact h1.comp s (Real.contDiffAt_sqrt hs0.ne')

theorem stepPhase_tail (hL : 0 < L) (hS : IsStepProfile S edge) :
    ∃ x₀ > 0, ∃ C : ℝ, ∀ s, x₀ ^ 2 < s → stepPhase L S s = C + Real.log s / 2 := by
  obtain ⟨t₁, ht₁, hone⟩ := hS.one_above
  have ht'1 : max t₁ edge < 1 := max_lt ht₁ hS.edge_lt
  have ht'0 : 0 < max t₁ edge := lt_of_lt_of_le hS.edge_pos (le_max_right _ _)
  have hx₀pos : 0 < L * max t₁ edge / (1 - max t₁ edge) :=
    div_pos (mul_pos hL ht'0) (by linarith)
  have hint : ∀ r, L * max t₁ edge / (1 - max t₁ edge) ≤ r → stepIntegrand L S r = r⁻¹ := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le hx₀pos hr
    unfold stepIntegrand
    rw [hone _ (le_trans (le_max_left _ _) (stepRatio_ge L _ r hL ht'1 hr hr0))
      ((div_le_one (by linarith)).mpr (by linarith)), one_div]
  generalize L * max t₁ edge / (1 - max t₁ edge) = x₀ at hx₀pos hint
  refine ⟨x₀, hx₀pos, stepPrimitive L S x₀ - Real.log x₀, fun s hs => ?_⟩
  have hq : x₀ < Real.sqrt s := (Real.lt_sqrt hx₀pos.le).mpr hs
  have hq0 : 0 < Real.sqrt s := lt_trans hx₀pos hq
  have hs0 : 0 < s := lt_trans (pow_pos hx₀pos 2) hs
  have heq : Set.EqOn (stepIntegrand L S) (fun r => r⁻¹)
      (Set.uIcc x₀ (Real.sqrt s)) := by
    intro r hr
    rw [Set.uIcc_of_le hq.le] at hr
    exact hint r hr.1
  rw [stepPhase_eq_primitive]
  unfold stepPrimitive
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (stepIntegrand_intervalIntegrable hL hS 0 x₀ (by linarith) (by linarith))
    (stepIntegrand_intervalIntegrable hL hS x₀ (Real.sqrt s) (by linarith) (by linarith)),
    intervalIntegral.integral_congr heq, integral_inv_of_pos hx₀pos hq0,
    Real.log_div hq0.ne' hx₀pos.ne', Real.log_sqrt hs0.le]
  ring

theorem stepLog_derivs (C s : ℝ) (hs : s ≠ 0) :
    s * deriv (fun y => C + Real.log y / 2) s = 1 / 2 ∧
    s ^ 2 * iteratedDeriv 2 (fun y => C + Real.log y / 2) s = -1 / 2 ∧
    s ^ 3 * iteratedDeriv 3 (fun y => C + Real.log y / 2) s = 1 := by
  have h1 : deriv (fun y => C + Real.log y / 2) = fun y => y⁻¹ / 2 := by
    funext y
    rw [deriv_const_add, deriv_div_const, Real.deriv_log]
  have h2 : deriv (fun y : ℝ => y⁻¹ / 2) = fun y => -(y ^ 2)⁻¹ / 2 := by
    funext y
    rw [deriv_div_const, deriv_inv]
  have e2 : iteratedDeriv 2 (fun y => C + Real.log y / 2) = fun y => -(y ^ 2)⁻¹ / 2 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, h1, h2]
  have h3 : HasDerivAt (fun y : ℝ => -(y ^ 2)⁻¹ / 2)
      (-(-(((2 : ℕ) : ℝ) * s ^ (2 - 1)) / (s ^ 2) ^ 2) / 2) s :=
    (((hasDerivAt_pow 2 s).inv (pow_ne_zero 2 hs)).neg).div_const 2
  have e3 : iteratedDeriv 3 (fun y => C + Real.log y / 2) s = (s ^ 3)⁻¹ := by
    rw [iteratedDeriv_succ, e2]
    rw [h3.deriv]
    norm_num
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]
    field_simp
  · rw [e2]
    field_simp
  · rw [e3]
    field_simp

theorem stepPhase_scaled (hL : 0 < L) (hS : IsStepProfile S edge) :
    ∃ B : ℝ, ∀ s, 0 ≤ s → |s * deriv (stepPhase L S) s| ≤ B ∧
      |s ^ 2 * iteratedDeriv 2 (stepPhase L S) s| ≤ B ∧
      |s ^ 3 * iteratedDeriv 3 (stepPhase L S) s| ≤ B := by
  have hf := stepPhase_contDiff hL hS
  obtain ⟨x₀, hx₀, C, hC⟩ := stepPhase_tail hL hS
  have hc1 : ContinuousOn (fun s => s * deriv (stepPhase L S) s) (Set.Icc 0 (x₀ ^ 2 + 1)) :=
    (continuous_id.mul (hf.continuous_deriv (by norm_num))).continuousOn
  have hc2 : ContinuousOn (fun s => s ^ 2 * iteratedDeriv 2 (stepPhase L S) s)
      (Set.Icc 0 (x₀ ^ 2 + 1)) :=
    ((continuous_pow 2).mul (hf.continuous_iteratedDeriv 2 (by norm_num))).continuousOn
  have hc3 : ContinuousOn (fun s => s ^ 3 * iteratedDeriv 3 (stepPhase L S) s)
      (Set.Icc 0 (x₀ ^ 2 + 1)) :=
    ((continuous_pow 3).mul (hf.continuous_iteratedDeriv 3 (by norm_num))).continuousOn
  obtain ⟨M1, hStrain⟩ := isCompact_Icc.exists_bound_of_continuousOn hc1
  obtain ⟨M2, hM2⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2
  obtain ⟨M3, hM3⟩ := isCompact_Icc.exists_bound_of_continuousOn hc3
  have hB1 : M1 ≤ max (max M1 M2) (max M3 1) := le_trans (le_max_left _ _) (le_max_left _ _)
  have hB2 : M2 ≤ max (max M1 M2) (max M3 1) := le_trans (le_max_right _ _) (le_max_left _ _)
  have hB3 : M3 ≤ max (max M1 M2) (max M3 1) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hB4 : 1 ≤ max (max M1 M2) (max M3 1) := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨max (max M1 M2) (max M3 1), fun s hs => ?_⟩
  rcases le_or_gt s (x₀ ^ 2 + 1) with hsK | hsK
  · have hmem : s ∈ Set.Icc 0 (x₀ ^ 2 + 1) := ⟨hs, hsK⟩
    have a1 := hStrain s hmem
    have a2 := hM2 s hmem
    have a3 := hM3 s hmem
    rw [Real.norm_eq_abs] at a1 a2 a3
    exact ⟨a1.trans hB1, a2.trans hB2, a3.trans hB3⟩
  · have hev : stepPhase L S =ᶠ[nhds s] fun y => C + Real.log y / 2 := by
      filter_upwards [Ioi_mem_nhds (show x₀ ^ 2 < s by linarith)] with y hy
      exact hC y hy
    obtain ⟨d1, d2, d3⟩ := stepLog_derivs C s (lt_of_le_of_lt (by positivity) hsK).ne'
    rw [hev.deriv_eq, d1, hev.iteratedDeriv_eq 2, d2, hev.iteratedDeriv_eq 3, d3]
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_of_pos (by norm_num)]; linarith
    · rw [abs_of_neg (by norm_num)]; linarith
    · rw [abs_one]; exact hB4

end Internal

open Internal in
theorem stepPhase_holds : StepPhaseHolds := by
  intro L edge S hL hS
  refine ⟨⟨⟨1, one_pos, (stepPhase_contDiff hL hS).contDiffOn⟩, stepPhase_scaled hL hS⟩,
    fun s hs => stepPhase_zero hL hS s hs⟩

end Instantiation

end CellReduction

end Breakdown
