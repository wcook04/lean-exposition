import TorusEuler.EndpointSpatialRegularity

/-! The triangular spatial derivative hierarchy for the compressed operator. -/

open scoped InnerProductSpace

namespace TorusEuler

noncomputable section

/-- The derivative of a periodic field along every line in a fixed direction. -/
def endpointTorusHasSpatialDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Vec3) (f df : HalfHolder (UnitAddTorus (Fin 3)) E) : Prop :=
  ∀ (a : UnitAddTorus (Fin 3)) (s : ℝ), HasDerivAt
    (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) f)
    (HalfHolder.eval (a + toUnitTorus (s • u)) df) s

private theorem hasDerivAt_list_map_sum {α H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (l : List α) (F : α → ℝ → H) (D : α → H) (s : ℝ)
    (h : ∀ p ∈ l, HasDerivAt (F p) (D p) s) :
    HasDerivAt (fun r => (l.map fun p => F p r).sum) (l.map D).sum s := by
  induction l with
  | nil => simpa only [List.map_nil, List.sum_nil] using hasDerivAt_const s (0 : H)
  | cons p l ih =>
    have htail := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simpa only [List.map_cons, List.sum_cons, Pi.add_apply, Pi.add_def] using
      (h p List.mem_cons_self).add htail

/-- Ordered pairs of derivative words in the product rule with a positive coefficient order. -/
def endpointMixedCorrectionPairs {I : Type*} : List I → List (List I × List I)
  | [] => []
  | i :: t => ([i], t) :: (endpointMixedCorrectionPairs t).flatMap
    (fun p => [(i :: p.1, p.2), (p.1, i :: p.2)])

theorem endpointMixedCorrectionPairs_mem {I : Type*} {t : List I} {p : List I × List I}
    (h : p ∈ endpointMixedCorrectionPairs t) :
    1 ≤ p.1.length ∧ p.1.length + p.2.length = t.length ∧ p.2.length < t.length := by
  induction t generalizing p with
  | nil => simp [endpointMixedCorrectionPairs] at h
  | cons i t ih =>
    simp only [endpointMixedCorrectionPairs, List.mem_cons, List.mem_flatMap] at h
    rcases h with rfl | ⟨⟨v, w⟩, hvw, hp⟩
    · simp [Nat.add_comm]
    · obtain ⟨hv, heq, hw⟩ := ih hvw
      simp only [List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp only [List.length_cons] at * <;> omega

theorem endpointMixedCorrectionPairs_sum_cons {I W : Type*} [AddMonoid W]
    (i : I) (t : List I) (F : List I × List I → W) :
    ((endpointMixedCorrectionPairs (i :: t)).map F).sum =
      F ([i], t) + ((endpointMixedCorrectionPairs t).map
        (fun p => F (i :: p.1, p.2) + F (p.1, i :: p.2))).sum := by
  simp only [endpointMixedCorrectionPairs, List.map_cons, List.sum_cons]
  congr 1
  generalize endpointMixedCorrectionPairs t = l
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, ih]

section AllMixedSpatialOrders

local notation "A" => UnitAddTorus (Fin 3)

variable {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "W" => HalfHolder A H
local notation "M" => HalfHolder A (H →L[ℝ] H)

/-- The iterated Leibniz terms involving at least one coefficient derivative. -/
noncomputable def endpointMixedCorrection (B : List I → M) (w : List I → W) (t : List I) : W :=
  ((endpointMixedCorrectionPairs t).map fun p => (B p.1).coefficientMul (w p.2)).sum

omit [CompleteSpace H] in
private theorem endpointMixedCorrection_congr (B : List I → M) {v w : List I → W} (t : List I)
    (h : ∀ s : List I, s.length < t.length → v s = w s) :
    endpointMixedCorrection B v t = endpointMixedCorrection B w t := by
  unfold endpointMixedCorrection
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [h p.2 (endpointMixedCorrectionPairs_mem hp).2.2]

omit [CompleteSpace H] in
private theorem endpointMixedCorrection_hasDerivative
    (B : List I → M) (w : List I → W) (u : I → Vec3) (i : I) (t : List I)
    (hB : ∀ s : List I, s.length ≤ t.length →
      endpointTorusHasSpatialDerivative (u i) (B s) (B (i :: s)))
    (hw : ∀ s : List I, s.length < t.length →
      endpointTorusHasSpatialDerivative (u i) (w s) (w (i :: s))) :
    endpointTorusHasSpatialDerivative (u i) (endpointMixedCorrection B w t)
      (((endpointMixedCorrectionPairs t).map fun p =>
        (B (i :: p.1)).coefficientMul (w p.2) +
          (B p.1).coefficientMul (w (i :: p.2))).sum) := by
  intro a s
  let F (p : List I × List I) (r : ℝ) :=
    HalfHolder.eval (a + toUnitTorus (r • u i)) ((B p.1).coefficientMul (w p.2))
  let D (p : List I × List I) :=
    HalfHolder.eval (a + toUnitTorus (s • u i))
      ((B (i :: p.1)).coefficientMul (w p.2) +
        (B p.1).coefficientMul (w (i :: p.2)))
  have hterm (p : List I × List I) (hp : p ∈ endpointMixedCorrectionPairs t) :
      HasDerivAt (F p) (D p) s := by
    have hmem := endpointMixedCorrectionPairs_mem hp
    have hi : p.1.length ≤ t.length := by omega
    simpa only [F, D, map_add, HalfHolder.eval_coefficientMul] using
      (hB p.1 hi a s).clm_apply (hw p.2 hmem.2.2 a s)
  simpa only [endpointMixedCorrection, map_list_sum, List.map_map, F, D, Function.comp_def] using
    hasDerivAt_list_map_sum (endpointMixedCorrectionPairs t) F D s hterm

omit [CompleteSpace H] in
/-- Differentiate each lower-order term of the spatial Leibniz rule in the
same direction, preserving the ordered word multiplicities. -/
theorem endpointMixedCorrection_hasSpatialDerivative
    (B : List I → M) (w : List I → W) (u : I → Vec3) (i : I) (t : List I)
    (hB : ∀ s : List I, s.length ≤ t.length →
      endpointTorusHasSpatialDerivative (u i) (B s) (B (i :: s)))
    (hw : ∀ s : List I, s.length < t.length →
      endpointTorusHasSpatialDerivative (u i) (w s) (w (i :: s))) :
    endpointTorusHasSpatialDerivative (u i) (endpointMixedCorrection B w t)
      (((endpointMixedCorrectionPairs t).map fun p =>
        (B (i :: p.1)).coefficientMul (w p.2) +
          (B p.1).coefficientMul (w (i :: p.2))).sum) :=
  endpointMixedCorrection_hasDerivative B w u i t hB hw

/-- Corresponding coefficient and forcing derivatives give actual half-Hölder
solution derivatives for every word of directions up to the same finite order.
Prepending an index means differentiating in that direction. -/
theorem endpointSpatialAllFiniteMixedDerivatives
    (P : W →L[ℝ] W) (hP : ∀ z, P (P z) = P z)
    (C₂ : ℝ) (hC₂ : 0 ≤ C₂)
    (hWeak : ∀ z, ‖freezingHaarEmbedding (P z)‖ ≤ C₂ * ‖freezingHaarEmbedding z‖)
    (hpair : ∀ z (w : freezingFixedSpace P),
      ⟪freezingHaarEmbedding (P z), freezingHaarEmbedding w.val⟫_ℝ =
        ⟪freezingHaarEmbedding z, freezingHaarEmbedding w.val⟫_ℝ)
    (B : List I → M) (f : List I → W) (v : W) (u : I → Vec3)
    (hcomm : ∀ (i : I) (h : ℝ) z, P (HalfHolder.torusTranslate (toUnitTorus (h • u i)) z) =
      HalfHolder.torusTranslate (toUnitTorus (h • u i)) (P z))
    (hv : P v = v)
    (heq : P ((B []).coefficientMul v) = f [])
    (S : freezingFixedSpace P ≃L[ℝ] freezingFixedSpace P)
    (hS : (S : freezingFixedSpace P →L[ℝ] freezingFixedSpace P) =
      freezingCompression P (B []).coefficientMul hP)
    {μ : ℝ} (hμ : 0 < μ)
    (hcoercive : ∀ (z : freezingFixedSpace P) a, μ * ‖HalfHolder.eval a z.val‖ ^ 2 ≤
      ⟪HalfHolder.eval a (B []) (HalfHolder.eval a z.val), HalfHolder.eval a z.val⟫_ℝ)
    (N : ℕ)
    (hB : ∀ (i : I) (t : List I), t.length < N →
      endpointTorusHasSpatialDerivative (u i) (B t) (B (i :: t)))
    (hf : ∀ (i : I) (t : List I), t.length < N →
      endpointTorusHasSpatialDerivative (u i) (f t) (f (i :: t))) :
    ∃ w : List I → W, w [] = v ∧ (∀ t : List I, t.length ≤ N → P (w t) = w t) ∧
      (∀ t : List I, t.length ≤ N →
        P ((B []).coefficientMul (w t)) = f t - P (endpointMixedCorrection B w t)) ∧
      (∀ (i : I) (t : List I), t.length < N →
        endpointTorusHasSpatialDerivative (u i) (w t) (w (i :: t))) := by
  induction N with
  | zero =>
    refine ⟨fun _ => v, rfl, fun _ _ => hv, ?_, fun _ t ht => (Nat.not_lt_zero t.length ht).elim⟩
    intro t ht
    have h : t = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero ht)
    subst t
    simpa only [endpointMixedCorrection, endpointMixedCorrectionPairs, List.map_nil,
      List.sum_nil, map_zero, sub_zero] using heq
  | succ N ih =>
    obtain ⟨w, hw0, hfix, hEq, hD⟩ :=
      ih (fun i t ht => hB i t (by omega)) (fun i t ht => hf i t (by omega))
    have hstep (i : I) (t : List I) (ht : t.length = N) :
        ∃ z : W, P z = z ∧
          P ((B []).coefficientMul z) = f (i :: t) - P (endpointMixedCorrection B w (i :: t)) ∧
          endpointTorusHasSpatialDerivative (u i) (w t) z := by
      let c := endpointMixedCorrection B w t
      let dc := ((endpointMixedCorrectionPairs t).map fun p =>
        (B (i :: p.1)).coefficientMul (w p.2) + (B p.1).coefficientMul (w (i :: p.2))).sum
      let g := f t - P c
      let dg := f (i :: t) - P dc
      have hc : endpointTorusHasSpatialDerivative (u i) c dc :=
        endpointMixedCorrection_hasDerivative B w u i t
          (fun l hl => hB i l (by omega)) (fun l hl => hD i l (by omega))
      have hPc := freezingProjection_preserves_torusDirectionalDerivative_of_haar_bound
        P C₂ hC₂ hWeak (u i) (hcomm i) c dc hc
      have hg : endpointTorusHasSpatialDerivative (u i) g dg := by
        intro a s
        have h := (hf i t (by omega) a s).sub (hPc a s)
        change HasDerivAt (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u i)) (f t) -
          HalfHolder.eval (a + toUnitTorus (r • u i)) (P c)) _ s at h
        simpa only [g, dg, map_sub] using h
      obtain ⟨z, hzfix, hzEq, _, hz⟩ := endpointSpatialDerivative_of_haar_bound P hP C₂ hC₂ hWeak hpair
        (B []) (B [i]) (w t) g dg (u i) (hcomm i) (hfix t (by omega)) (hEq t (by omega))
        S hS hμ hcoercive hg (hB i [] (Nat.succ_pos N))
      have hzD : endpointTorusHasSpatialDerivative (u i) (w t) z :=
        (HalfHolder.hasLineDerivAt_lift_iff_torusLine_hasDerivAt (w t) z (u i)).mp hz
      have hrow : endpointMixedCorrection B w (i :: t) = (B [i]).coefficientMul (w t) + dc :=
        endpointMixedCorrectionPairs_sum_cons i t fun p => (B p.1).coefficientMul (w p.2)
      refine ⟨z, hzfix, ?_, hzD⟩
      rw [hzEq, hrow, map_add]
      dsimp [dg]
      abel
    classical
    let w' : List I → W
      | [] => w []
      | i :: t => if ht : t.length = N then Classical.choose (hstep i t ht) else w (i :: t)
    have hsame (t : List I) (ht : t.length ≤ N) : w' t = w t := by
      cases t with
      | nil => rfl
      | cons i t =>
        have hne : t.length ≠ N := by
          simp only [List.length_cons] at ht
          omega
        simp only [w', dite_eq_right hne]
    have hnew (i : I) (t : List I) (ht : t.length = N) :
        w' (i :: t) = Classical.choose (hstep i t ht) := by
      simp only [w', dite_eq_left ht]
    refine ⟨w', hw0, ?_, ?_, ?_⟩
    · intro t ht
      by_cases hold : t.length ≤ N
      · rw [hsame t hold]
        exact hfix t hold
      · cases t with
        | nil => exact (hold (Nat.zero_le N)).elim
        | cons i t =>
          simp only [List.length_cons] at ht hold
          have h : t.length = N := by omega
          rw [hnew i t h]
          exact (Classical.choose_spec (hstep i t h)).1
    · intro t ht
      rw [endpointMixedCorrection_congr B t (fun l hl => hsame l (by omega))]
      by_cases hold : t.length ≤ N
      · rw [hsame t hold]
        exact hEq t hold
      · cases t with
        | nil => exact (hold (Nat.zero_le N)).elim
        | cons i t =>
          simp only [List.length_cons] at ht hold
          have h : t.length = N := by omega
          rw [hnew i t h]
          exact (Classical.choose_spec (hstep i t h)).2.1
    · intro i t ht
      rw [hsame t (by omega)]
      by_cases h : t.length = N
      · rw [hnew i t h]
        exact (Classical.choose_spec (hstep i t h)).2.2
      · rw [hsame (i :: t) (by simp only [List.length_cons]; omega)]
        exact hD i t (by omega)

set_option maxHeartbeats 800000 in
omit [CompleteSpace H] in
/-- Bound the lower-order terms in the spatial Leibniz rule by the coefficient
and velocity norms. The pairs retain the multiplicities of repeated derivatives. -/
theorem norm_endpointMixedCorrection_le (B : List I → M) (w : List I → W) (t : List I) :
    ‖endpointMixedCorrection B w t‖ ≤
      ((endpointMixedCorrectionPairs t).map fun p => 2 * ‖B p.1‖ * ‖w p.2‖).sum := by
  unfold endpointMixedCorrection
  generalize endpointMixedCorrectionPairs t = pairs
  induction pairs with
  | nil => simp only [List.map_nil, List.sum_nil, norm_zero, le_refl]
  | cons p pairs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add
      ((B p.1).coefficientMul.le_of_opNorm_le (HalfHolder.norm_coefficientMul_le _) _) ih)

set_option maxHeartbeats 800000 in
omit [CompleteSpace H] in
/-- At every differentiated order, the same inverse controls the solution
by the forcing at that order and lower-order velocity derivatives. -/
theorem norm_endpointSpatialMixedDerivative_le_of_equation
    (P : W →L[ℝ] W) (hP : ∀ z, P (P z) = P z)
    (B : List I → M) (f : List I → W) (w : List I → W) (t : List I)
    (hw : P (w t) = w t)
    (heq : P ((B []).coefficientMul (w t)) = f t - P (endpointMixedCorrection B w t))
    (S : freezingFixedSpace P ≃L[ℝ] freezingFixedSpace P)
    (hS : (S : freezingFixedSpace P →L[ℝ] freezingFixedSpace P) =
      freezingCompression P (B []).coefficientMul hP) :
    ‖w t‖ ≤ ‖(S.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P)‖ *
      (‖f t‖ + ‖P‖ * ((endpointMixedCorrectionPairs t).map fun p =>
        2 * ‖B p.1‖ * ‖w p.2‖).sum) := by
  let z : freezingFixedSpace P := ⟨w t, (mem_freezingFixedSpace P _).mpr hw⟩
  let L : freezingFixedSpace P →L[ℝ] freezingFixedSpace P := S.symm
  have hz : (S z).val = f t - P (endpointMixedCorrection B w t) := by
    rw [show S z = freezingCompression P (B []).coefficientMul hP z from
      DFunLike.congr_fun hS z, freezingCompression_val]
    exact heq
  have hbound : ‖w t‖ ≤ ‖L‖ * ‖f t - P (endpointMixedCorrection B w t)‖ := by
    have h := L.le_opNorm (S z)
    change ‖S.symm (S z)‖ ≤ ‖L‖ * ‖S z‖ at h
    rw [S.symm_apply_apply, Submodule.coe_norm z, Submodule.coe_norm (S z), hz] at h
    exact h
  refine hbound.trans (mul_le_mul_of_nonneg_left ?_ L.opNorm_nonneg)
  apply (norm_sub_le _ _).trans
  exact add_le_add le_rfl ((P.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (norm_endpointMixedCorrection_le B w t) P.opNorm_nonneg))

end AllMixedSpatialOrders

end

end TorusEuler
