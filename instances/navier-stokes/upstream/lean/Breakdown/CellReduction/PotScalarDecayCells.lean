import Breakdown.CellReduction.PotThetaScalar
import Breakdown.CertCell.ShapeTypeOneDecay
import Breakdown.CertCell.ShapeJetUnit
import Breakdown.CertCell.ShapeJetJoin
import Breakdown.CertCell.ShapeJetValid

open scoped ContDiff Topology
open MeasureTheory Polynomial

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape AdjointDefect
open CellCert.GivenFields (heightRatio cellCount cellIndex weightPoly Spline)
open CertCell.GivenShape.Internal.KeyDecay

namespace Internal.ScalarDecay

theorem evalPair_comp_algebraMap (t x : ℂ) :
    (MvPolynomial.eval ![t, x]).comp (algebraMap ℂ (MvPolynomial (Fin 2) ℂ)) = RingHom.id ℂ := by
  ext c
  simp [MvPolynomial.algebraMap_eq]

theorem eval_embedFirst (P : ℂ[X]) (t x : ℂ) : MvPolynomial.eval ![t, x] (embedFirst P) = P.eval t := by
  rw [embedFirst, Polynomial.aeval_def, Polynomial.hom_eval₂, evalPair_comp_algebraMap, MvPolynomial.eval_X]
  rfl

theorem eval_embedSecond (P : ℂ[X]) (t x : ℂ) : MvPolynomial.eval ![t, x] (embedSecond P) = P.eval x := by
  rw [embedSecond, Polynomial.aeval_def, Polynomial.hom_eval₂, evalPair_comp_algebraMap, MvPolynomial.eval_X]
  rfl

theorem evalHalf_eq (H : JetSpline) (t x : ℝ) :
    H.toSpline.evalHalf t x = ∑ d ∈ H.tAxis.dofs, ∑ e ∈ H.xAxis.dofs, H.coef d e *
      (H.tAxis.dofPoly (cellIndex H.tAxis.breaks t) d).eval (t : ℂ) *
        (H.xAxis.dofPoly (cellIndex H.xAxis.breaks x) e).eval (x : ℂ) := by
  simp only [Spline.evalHalf, JetSpline.toSpline, map_sum, map_mul, MvPolynomial.eval_C, eval_embedFirst,
    eval_embedSecond]

theorem dvd_of_iterate_derivative {P : ℂ[X]} {z : ℕ} {b : ℂ} (h : ∀ o < z, (derivative^[o] P).eval b = 0) :
    (X - C b) ^ z ∣ P := by
  by_cases hP : P = 0
  · rw [hP]; exact dvd_zero _
  rcases Nat.eq_zero_or_pos z with hz | hz
  · rw [hz, pow_zero]; exact one_dvd _
  have hm : z - 1 < P.rootMultiplicity b :=
    (lt_rootMultiplicity_iff_isRoot_iterate_derivative hP).2 fun m hm => h m (by omega)
  exact (pow_dvd_pow _ (by omega)).trans (pow_rootMultiplicity_dvd P b)

theorem scalarValue_time (P : ShapeParams) (κ : FieldKey) (M : ℤ) (w : Bool) (S : PotScalar) (σ : ℝ)
    (y : Space) : scalarValue P κ M w S σ y =
      Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) * Complex.I) *
        scalarValue P κ M w S 0 y := by
  unfold scalarValue
  have e : (((2 * Real.pi * (labelTime κ.label : ℝ) * σ + (M : ℝ) * pointAngle y +
      (κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I) =
      (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) * Complex.I) +
      (((2 * Real.pi * (labelTime κ.label : ℝ) * 0 + (M : ℝ) * pointAngle y +
      (κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  rw [e, Complex.exp_add]
  ring

theorem farDecay_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℕ} {f : Space → E}
    (hf : FarDecay a f) (hba : b ≤ a) : FarDecay b f := by
  obtain ⟨C, R, hC, hR, h⟩ := hf
  refine ⟨C, R, hC, hR, fun y hy => ?_⟩
  have hw0 : 0 ≤ ‖y‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
  have hw1 : ‖y‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hR.trans hy)
  have hp : ∀ k : ℕ, C * ‖y‖⁻¹ ^ (a + k) ≤ C * ‖y‖⁻¹ ^ (b + k) := fun k =>
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hw0 hw1 (by omega)) hC
  exact ballData_mono (h y hy) (by simpa using hp 0) (hp 1) (hp 2)

theorem farDecay_congr_far {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a : ℕ} {f g : Space → E}
    (hg : FarDecay a g) (R0 : ℝ) (he : ∀ y : Space, R0 < ‖y‖ → f y = g y) : FarDecay a f := by
  obtain ⟨C, R, hC, hR, h⟩ := hg
  refine ⟨C, max R (R0 + 1), hC, le_max_of_le_left hR, fun y hy => ?_⟩
  obtain ⟨h1, h2⟩ := h y (le_of_max_le_left hy)
  have hin : ∀ z ∈ Metric.ball y 1, f =ᶠ[𝓝 z] g := by
    intro z hz
    have hz' : R0 < ‖z‖ := by
      have h1 : ‖z - y‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
      have := norm_sub_norm_le y z
      rw [norm_sub_rev] at this
      have := le_of_max_le_right hy
      linarith
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz'] with w hw using he w hw
  refine ⟨fun z hz => ?_, fun z hz w hw => ?_⟩
  · obtain ⟨d1, d2, d3⟩ := h1 z hz
    refine ⟨(hin z hz).differentiableAt_iff.2 d1, ?_, ?_⟩
    · rw [(hin z hz).eq_of_nhds]; exact d2
    · rw [(hin z hz).fderiv_eq]; exact d3
  · rw [(hin z hz).fderiv_eq, (hin w hw).fderiv_eq]
    exact h2 z hz w hw

theorem tailPow_farDecay {L : ℝ} (hL : 0 < L) (n : ℕ) :
    FarDecay n (fun z : Space => (((L * (‖z‖ + L)⁻¹ : ℝ)) : ℂ) ^ n) := by
  induction n with
  | zero => simpa using FarDecay.const (1 : ℂ)
  | succ n ih =>
    refine farDecay_congr_far (FarDecay.smul (tailC_farDecay hL) ih (by omega : 1 + n = n + 1)) 0 fun y _ => ?_
    simp [pow_succ, mul_comm]


theorem cellIndex_eq_zero {l : List ℝ} {u : ℝ} (h : ∀ b ∈ (l.drop 1).dropLast, u < b) :
    cellIndex l u = 0 := by
  unfold cellIndex
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro b hb
  simpa using h b hb

theorem cellIndex_eq_last {l : List ℝ} {u : ℝ} (h : ∀ b ∈ (l.drop 1).dropLast, b ≤ u) :
    cellIndex l u = cellCount l - 1 := by
  unfold cellIndex cellCount
  rw [List.filter_eq_self.2 (fun b hb => by simpa using h b hb)]
  simp [List.length_dropLast]

theorem cellIndex_le' (l : List ℝ) (u : ℝ) : cellIndex l u ≤ cellCount l - 1 := by
  unfold cellIndex cellCount
  refine (List.length_filter_le _ _).trans ?_
  simp [List.length_dropLast]

theorem inner_length (l : List ℝ) : ((l.drop 1).dropLast).length = cellCount l - 1 := by
  simp [cellCount, List.length_dropLast]

theorem inner_bounds {l : List ℝ} {lo hi : ℝ} (hs : l.Pairwise (· < ·)) (hf : l.head? = some lo)
    (hl : l.getLast? = some hi) : ∀ b ∈ (l.drop 1).dropLast, lo < b ∧ b < hi := by
  intro b hb
  refine ⟨?_, ?_⟩
  · match l, hs, hf, hb with
    | a :: rest, hs, hf, hb =>
      simp only [List.head?_cons, Option.some.injEq] at hf
      subst hf
      have hb' : b ∈ rest := by simpa using List.mem_of_mem_dropLast hb
      exact List.rel_of_pairwise_cons hs hb'
  · rw [List.dropLast_drop_eq_drop_dropLast] at hb
    have hb' := List.mem_of_mem_drop hb
    have e := List.dropLast_append_getLast? hi (by rw [hl]; rfl)
    rw [← e, List.pairwise_append] at hs
    exact hs.2.2 b hb' hi (by simp)

theorem length_two_le {l : List ℝ} {lo hi : ℝ} (hlt : lo < hi) (hf : l.head? = some lo)
    (hl : l.getLast? = some hi) : 1 ≤ cellCount l := by
  unfold cellCount
  match l, hf, hl with
  | [a], hf, hl =>
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at hf hl
    rw [← hf, ← hl] at hlt
    exact absurd hlt (lt_irrefl _)
  | a :: b :: rest, _, _ => simp

theorem getD_last {l : List ℝ} {hi : ℝ} (hl : l.getLast? = some hi) : l.getD (cellCount l) 0 = hi := by
  rw [List.getLast?_eq_getElem?] at hl
  unfold cellCount
  rw [List.getD_eq_getElem?_getD, hl]
  rfl

theorem exists_inner_upper {I : List ℝ} {lo hi : ℝ} (hlt : lo < hi) (h : ∀ b ∈ I, b < hi) :
    ∃ m, m < hi ∧ ∀ b ∈ I, b ≤ m := by
  induction I with
  | nil => exact ⟨lo, hlt, by simp⟩
  | cons a I ih =>
    obtain ⟨m, hm, hmI⟩ := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    refine ⟨max a m, max_lt (h a (by simp)) hm, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact le_max_left _ _
    · exact le_max_of_le_right (hmI b hb)

theorem exists_inner_ends {I : List ℝ} (hs : I.Pairwise (· < ·)) (h2 : 2 ≤ I.length) :
    ∃ α β, α ∈ I ∧ β ∈ I ∧ α < β ∧ ∀ b ∈ I, α ≤ b ∧ b ≤ β := by
  match I, hs, h2 with
  | a :: c :: rest, hs, _ =>
    have hne : (a :: c :: rest).toFinset.Nonempty := ⟨a, by simp⟩
    refine ⟨_, _, List.mem_toFinset.1 (Finset.min'_mem _ hne), List.mem_toFinset.1 (Finset.max'_mem _ hne),
      ?_, fun b hb => ⟨Finset.min'_le _ _ (List.mem_toFinset.2 hb), Finset.le_max' _ _ (List.mem_toFinset.2 hb)⟩⟩
    have hac : a < c := List.rel_of_pairwise_cons hs (by simp)
    exact lt_of_le_of_lt (Finset.min'_le _ _ (by simp)) (lt_of_lt_of_le hac (Finset.le_max' _ _ (by simp)))

def nodeValue (v : ℕ → ℂ) : JetDof → ℂ
  | .node k p => if p = 0 then v k else 0
  | .bubble _ _ => 0

def plateauSpline (xs : List ℝ) (v : ℕ → ℂ) : JetSpline :=
  ⟨⟨[0, 1], 2, 0⟩, ⟨xs, 2, 0⟩, fun d e => nodeValue (fun _ => 1) d * nodeValue v e⟩

theorem nodal_sum_eq_one {a b : ℝ} (hab : a ≠ b) (u : ℂ) :
    (nodalLeft 2 0 a b).eval u + (nodalRight 2 0 a b).eval u = 1 := by
  have hba : (b : ℂ) - a ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hab.symm)
  simp [nodalLeft, nodalRight, jetUnit, Finset.sum_range_succ]
  field_simp
  ring

theorem nodeValue_sum (A : JetAxis) (hd : A.depth = 2) (v : ℕ → ℂ) {i : ℕ}
    (hi : i < cellCount A.breaks) (u : ℂ) :
    ∑ d ∈ A.dofs, nodeValue v d * (A.dofPoly i d).eval u =
      v i * (nodalLeft 2 0 (A.breaks.getD i 0) (A.breaks.getD (i + 1) 0)).eval u +
        v (i + 1) * (nodalRight 2 0 (A.breaks.getD i 0) (A.breaks.getD (i + 1) 0)).eval u := by
  have hmem : ∀ k, k ≤ cellCount A.breaks → JetDof.node k 0 ∈ A.dofs := fun k hk =>
    Finset.mem_union_left _ (Finset.mem_image.2 ⟨(k, 0), by simp [hd]; omega, rfl⟩)
  rw [Finset.sum_eq_add (JetDof.node i 0) (JetDof.node (i + 1) 0) (by simp)]
  · simp [nodeValue, JetAxis.dofPoly, hd]
  · intro c _ hc
    cases c with
    | node k p =>
      simp only [nodeValue]
      split_ifs with hp
      · subst hp
        have h1 : k ≠ i := fun h => hc.1 (by rw [h])
        have h2 : k ≠ i + 1 := fun h => hc.2 (by rw [h])
        simp [JetAxis.dofPoly, h1, h2]
      · simp
    | bubble _ _ => simp [nodeValue]
  · exact fun h => absurd (hmem i hi.le) h
  · exact fun h => absurd (hmem (i + 1) hi) h

theorem plateau_evalHalf (xs : List ℝ) (v : ℕ → ℂ) (hx : 1 ≤ cellCount xs) (t x : ℝ) :
    (plateauSpline xs v).toSpline.evalHalf t x =
      v (cellIndex xs x) * (nodalLeft 2 0 (xs.getD (cellIndex xs x) 0)
        (xs.getD (cellIndex xs x + 1) 0)).eval (x : ℂ) +
      v (cellIndex xs x + 1) * (nodalRight 2 0 (xs.getD (cellIndex xs x) 0)
        (xs.getD (cellIndex xs x + 1) 0)).eval (x : ℂ) := by
  rw [evalHalf_eq]
  have ht : cellIndex [0, 1] t = 0 := by simp [cellIndex]
  have hj : cellIndex xs x < cellCount xs := (cellIndex_le' xs x).trans_lt (by omega)
  have htsum := nodeValue_sum ⟨[0, 1], 2, 0⟩ rfl (fun _ => 1) (i := 0) (by simp [cellCount]) (t : ℂ)
  have hxsum := nodeValue_sum ⟨xs, 2, 0⟩ rfl v hj (x : ℂ)
  have h01 := nodal_sum_eq_one (a := 0) (b := 1) (by norm_num) (t : ℂ)
  simp only [plateauSpline, ht]
  calc _ = (∑ d ∈ JetAxis.dofs ⟨[0, 1], 2, 0⟩, nodeValue (fun _ => 1) d *
        (JetAxis.dofPoly ⟨[0, 1], 2, 0⟩ 0 d).eval (t : ℂ)) *
        (∑ e ∈ JetAxis.dofs ⟨xs, 2, 0⟩, nodeValue v e *
          (JetAxis.dofPoly ⟨xs, 2, 0⟩ (cellIndex xs x) e).eval (x : ℂ)) := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
        ring
    _ = _ := by
        rw [htsum, hxsum]
        simp only [List.getD_cons_zero, List.getD_cons_succ] at h01 ⊢
        rw [one_mul, one_mul, h01, one_mul]

theorem plateau_jetClass {xs : List ℝ} (v : ℕ → ℂ) (hx : IsJetAxis ⟨xs, 2, 0⟩ (-1) 1) :
    IsJetClass 1 1 (plateauSpline xs v) := by
  have ht : IsJetAxis (⟨[0, 1], 2, 0⟩ : JetAxis) 0 1 := ⟨by simp, rfl, rfl, by norm_num⟩
  exact ⟨ht, hx, by show 1 + 1 ≤ 2; norm_num, by show 1 + 1 ≤ 2; norm_num⟩


theorem evalHalf_endCell_zero (H : JetSpline) (hv : AxisCellsVanish H) (t x : ℝ)
    (hj : cellIndex H.xAxis.breaks x = 0 ∨ cellIndex H.xAxis.breaks x = cellCount H.xAxis.breaks - 1) :
    H.toSpline.evalHalf t x = 0 := by
  rw [evalHalf_eq]
  generalize cellIndex H.xAxis.breaks x = j at hj ⊢
  refine Finset.sum_eq_zero fun d _ => Finset.sum_eq_zero fun e he => ?_
  by_cases hm : dofMeetsEndCells (cellCount H.xAxis.breaks) e
  · rw [hv d e he hm]; simp
  · have h0 : H.xAxis.dofPoly j e = 0 := by
      cases e with
      | node k p =>
        simp only [dofMeetsEndCells] at hm
        simp only [JetAxis.dofPoly]
        split_ifs <;> first | rfl | omega
      | bubble i s =>
        simp only [dofMeetsEndCells] at hm
        simp only [JetAxis.dofPoly]
        split_ifs <;> first | rfl | omega
    rw [h0]; simp

theorem plateau_tIndep (xs : List ℝ) (v : ℕ → ℂ) (hx : 1 ≤ cellCount xs) (t t' x : ℝ) :
    (plateauSpline xs v).toSpline.evalHalf t x = (plateauSpline xs v).toSpline.evalHalf t' x := by
  rw [plateau_evalHalf xs v hx t x, plateau_evalHalf xs v hx t' x]

theorem unitAxis : IsJetAxis (⟨[-1, 1], 2, 0⟩ : JetAxis) (-1) 1 := ⟨by simp, rfl, rfl, by norm_num⟩

theorem ones_evalHalf (t x : ℝ) : (plateauSpline [-1, 1] (fun _ => 1)).toSpline.evalHalf t x = 1 := by
  rw [plateau_evalHalf _ _ (by simp [cellCount]) t x]
  have hc : cellIndex [-1, 1] x = 0 := by simp [cellIndex]
  rw [hc]
  simpa using nodal_sum_eq_one (a := -1) (b := 1) (by norm_num) (x : ℂ)

theorem zero_evalHalf (t x : ℝ) : (plateauSpline [-1, 1] (fun _ => 0)).toSpline.evalHalf t x = 0 := by
  rw [plateau_evalHalf _ _ (by simp [cellCount]) t x]
  simp

theorem nodeValue_zero (e : JetDof) : nodeValue (fun _ => 0) e = 0 := by
  cases e <;> simp [nodeValue]

theorem cutoff_sorted {a α β b : ℝ} (h1 : -1 < a) (h2 : a < α) (h3 : α < β) (h4 : β < b) (h5 : b < 1) :
    [-1, a, α, β, b, 1].Pairwise (· < ·) := by
  simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp, forall_eq,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true, or_false]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> linarith

theorem exists_unit_spline {M : ℤ} {w : Bool} {S : PotScalar} (hS : IsJetClass 1 1 S.amp)
    (hadm : AxisAdmissible M w S) :
    ∃ U : JetSpline, IsJetClass 1 1 U ∧ AxisAdmissible M w ⟨U, 0, 0, S.axisPower⟩ ∧
      (∀ t t' x, U.toSpline.evalHalf t x = U.toSpline.evalHalf t' x) ∧
      ∀ t x, U.toSpline.evalHalf t x * S.amp.toSpline.evalHalf t x = S.amp.toSpline.evalHalf t x := by
  by_cases hA : 1 ≤ S.axisPower ∨ ¬ AxisCellsVanish S.amp
  · refine ⟨plateauSpline [-1, 1] (fun _ => 1), plateau_jetClass _ unitAxis, ?_,
      plateau_tIndep _ _ (by simp [cellCount]), fun t x => by rw [ones_evalHalf, one_mul]⟩
    have key : 1 ≤ S.axisPower ∨ AxisCellsVanish S.amp → 1 ≤ S.axisPower := fun h => by
      rcases h with h | h
      · exact h
      · rcases hA with h' | h'
        · exact h'
        · exact absurd h h'
    exact ⟨fun h1 h2 => Or.inl (key (hadm.1 h1 h2)), fun h1 h2 => Or.inl (key (hadm.2 h1 h2))⟩
  push_neg at hA
  obtain ⟨hκ, hv⟩ := hA
  have hax := hS.x_axis
  set N := cellCount S.amp.xAxis.breaks with hN
  by_cases hN2 : N ≤ 2
  · refine ⟨plateauSpline [-1, 1] (fun _ => 0), plateau_jetClass _ unitAxis, ?_,
      plateau_tIndep _ _ (by simp [cellCount]), fun t x => ?_⟩
    · have hz : AxisCellsVanish (plateauSpline [-1, 1] (fun _ => 0)) := fun d e _ _ => by
        show nodeValue (fun _ => 1) d * nodeValue (fun _ => 0) e = 0
        rw [nodeValue_zero, mul_zero]
      exact ⟨fun _ _ => Or.inr hz, fun _ _ => Or.inr hz⟩
    · have hle := cellIndex_le' S.amp.xAxis.breaks x
      rw [evalHalf_endCell_zero S.amp hv t x (by omega), mul_zero]
  push_neg at hN2
  have hbd := inner_bounds hax.sorted hax.first hax.last
  have hlen : 2 ≤ ((S.amp.xAxis.breaks.drop 1).dropLast).length := by rw [inner_length]; omega
  have hsorted : ((S.amp.xAxis.breaks.drop 1).dropLast).Pairwise (· < ·) :=
    hax.sorted.sublist ((List.dropLast_sublist _).trans (List.drop_sublist _ _))
  obtain ⟨α, β, hαI, hβI, hαβ, hends⟩ := exists_inner_ends hsorted hlen
  have hα1 := (hbd α hαI).1
  have hβ1 := (hbd β hβI).2
  set a : ℝ := (-1 + α) / 2
  set b : ℝ := (β + 1) / 2
  have ha1 : -1 < a := by simp only [a]; linarith
  have ha2 : a < α := by simp only [a]; linarith
  have hb1 : β < b := by simp only [b]; linarith
  have hb2 : b < 1 := by simp only [b]; linarith
  set v : ℕ → ℂ := fun k => if k = 2 ∨ k = 3 then 1 else 0 with hvdef
  have hxs : IsJetAxis (⟨[-1, a, α, β, b, 1], 2, 0⟩ : JetAxis) (-1) 1 :=
    ⟨cutoff_sorted ha1 ha2 hαβ hb1 hb2, rfl, rfl, by norm_num⟩
  have hc5 : cellCount [-1, a, α, β, b, 1] = 5 := rfl
  refine ⟨plateauSpline [-1, a, α, β, b, 1] v, plateau_jetClass _ hxs, ?_,
    plateau_tIndep _ _ (by rw [hc5]; norm_num), fun t x => ?_⟩
  · have hz : AxisCellsVanish (plateauSpline [-1, a, α, β, b, 1] v) := by
      intro d e _ he
      show nodeValue (fun _ => 1) d * nodeValue v e = 0
      cases e with
      | node k p =>
        have he' : k ≤ 1 ∨ 4 ≤ k := by
          have := he
          simp only [dofMeetsEndCells] at this
          exact this
        simp only [nodeValue, hvdef]
        split_ifs <;> first | omega | simp
      | bubble i s => simp [nodeValue]
    exact ⟨fun _ _ => Or.inr hz, fun _ _ => Or.inr hz⟩
  · by_cases hlo : ∀ c ∈ (S.amp.xAxis.breaks.drop 1).dropLast, x < c
    · rw [evalHalf_endCell_zero S.amp hv t x (Or.inl (cellIndex_eq_zero hlo)), mul_zero]
    by_cases hhi : ∀ c ∈ (S.amp.xAxis.breaks.drop 1).dropLast, c ≤ x
    · rw [evalHalf_endCell_zero S.amp hv t x (Or.inr (cellIndex_eq_last hhi)), mul_zero]
    push_neg at hlo hhi
    obtain ⟨c1, hc1, hc1x⟩ := hlo
    obtain ⟨c2, hc2, hc2x⟩ := hhi
    have hαx : α ≤ x := ((hends c1 hc1).1).trans hc1x
    have hxβ : x < β := lt_of_lt_of_le hc2x (hends c2 hc2).2
    have hci : cellIndex [-1, a, α, β, b, 1] x = 2 := by
      have h1 : a ≤ x := by linarith
      have h2 : ¬ β ≤ x := not_le.2 hxβ
      have h3 : ¬ b ≤ x := by intro h; linarith
      simp [cellIndex, List.filter, h1, hαx, h2, h3]
    rw [plateau_evalHalf _ _ (by rw [hc5]; norm_num) t x, hci]
    have hsum := nodal_sum_eq_one hαβ.ne (x : ℂ)
    simp only [hvdef, List.getD_cons_succ, List.getD_cons_zero]
    norm_num
    rw [hsum, one_mul]

end Internal.ScalarDecay

end PotentialShape

end Breakdown
