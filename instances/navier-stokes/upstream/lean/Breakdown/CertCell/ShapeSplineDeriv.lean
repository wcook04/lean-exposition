import Breakdown.CertCell.ShapeStatements

open Filter Topology

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline cellCount cellIndex atFirst atSecond tDeriv xDeriv)

namespace Internal

theorem pderiv_zero_one_comm (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 P) = MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl <;> simp [hp, MvPolynomial.pderiv_X] <;> ring

theorem xDeriv_pderiv_zero (o : ℕ) (P : MvPolynomial (Fin 2) ℂ) :
    xDeriv o (MvPolynomial.pderiv 0 P) = MvPolynomial.pderiv 0 (xDeriv o P) := by
  have h : Function.Commute (MvPolynomial.pderiv (R := ℂ) (0 : Fin 2)) (MvPolynomial.pderiv (R := ℂ) (1 : Fin 2)) :=
    fun Q => pderiv_zero_one_comm Q
  exact ((h.iterate_right o) P).symm

theorem tDeriv_pderiv_one (o : ℕ) (P : MvPolynomial (Fin 2) ℂ) :
    tDeriv o (MvPolynomial.pderiv 1 P) = MvPolynomial.pderiv 1 (tDeriv o P) := by
  have h : Function.Commute (MvPolynomial.pderiv (R := ℂ) (1 : Fin 2)) (MvPolynomial.pderiv (R := ℂ) (0 : Fin 2)) :=
    fun Q => (pderiv_zero_one_comm Q).symm
  exact ((h.iterate_right o) P).symm

theorem atSecond_pderiv_zero (c : ℂ) (Q : MvPolynomial (Fin 2) ℂ) :
    atSecond c (MvPolynomial.pderiv 0 Q) = MvPolynomial.pderiv 0 (atSecond c Q) := by
  unfold atSecond
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl <;> simp [hp, MvPolynomial.pderiv_X]

theorem atFirst_pderiv_one (c : ℂ) (Q : MvPolynomial (Fin 2) ℂ) :
    atFirst c (MvPolynomial.pderiv 1 Q) = MvPolynomial.pderiv 1 (atFirst c Q) := by
  unfold atFirst
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl <;> simp [hp, MvPolynomial.pderiv_X]

theorem eval_atFirst (c y : ℂ) (R : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval ![c, y] (atFirst c R) = MvPolynomial.eval ![c, y] R := by
  unfold atFirst
  induction R using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl <;> simp [hp]

theorem eval_atSecond (c y : ℂ) (R : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval ![y, c] (atSecond c R) = MvPolynomial.eval ![y, c] R := by
  unfold atSecond
  induction R using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl <;> simp [hp]

theorem hasDerivAt_eval_first (Q : MvPolynomial (Fin 2) ℂ) (y : ℂ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => MvPolynomial.eval ![(r : ℂ), y] Q)
      (MvPolynomial.eval ![(s : ℂ), y] (MvPolynomial.pderiv 0 Q)) s := by
  have h1 : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 s := by simpa using (hasDerivAt_id s).ofReal_comp
  induction Q using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const s a
  | add p q hp hq =>
    have h := hp.add hq
    simp only [map_add]
    exact h
  | mul_X p i hp =>
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl
    · have hf : (fun r : ℝ => MvPolynomial.eval ![(r : ℂ), y] (p * MvPolynomial.X 0)) =
          fun r : ℝ => MvPolynomial.eval ![(r : ℂ), y] p * (r : ℂ) := by
        funext r; simp
      rw [hf]
      refine (hp.mul h1).congr_deriv ?_
      simp
      ring
    · have hf : (fun r : ℝ => MvPolynomial.eval ![(r : ℂ), y] (p * MvPolynomial.X 1)) =
          fun r : ℝ => MvPolynomial.eval ![(r : ℂ), y] p * y := by
        funext r; simp
      rw [hf]
      refine (hp.mul_const y).congr_deriv ?_
      simp
      ring

theorem hasDerivAt_eval_second (Q : MvPolynomial (Fin 2) ℂ) (y : ℂ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => MvPolynomial.eval ![y, (r : ℂ)] Q)
      (MvPolynomial.eval ![y, (s : ℂ)] (MvPolynomial.pderiv 1 Q)) s := by
  have h1 : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 s := by simpa using (hasDerivAt_id s).ofReal_comp
  induction Q using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const s a
  | add p q hp hq =>
    have h := hp.add hq
    simp only [map_add]
    exact h
  | mul_X p i hp =>
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl
    · have hf : (fun r : ℝ => MvPolynomial.eval ![y, (r : ℂ)] (p * MvPolynomial.X 0)) =
          fun r : ℝ => MvPolynomial.eval ![y, (r : ℂ)] p * y := by
        funext r; simp
      rw [hf]
      refine (hp.mul_const y).congr_deriv ?_
      simp
      ring
    · have hf : (fun r : ℝ => MvPolynomial.eval ![y, (r : ℂ)] (p * MvPolynomial.X 1)) =
          fun r : ℝ => MvPolynomial.eval ![y, (r : ℂ)] p * (r : ℂ) := by
        funext r; simp
      rw [hf]
      refine (hp.mul h1).congr_deriv ?_
      simp
      ring

theorem two_le_length (l : List ℝ) {a b : ℝ} (hab : a ≠ b) (h0 : l.head? = some a)
    (h1 : l.getLast? = some b) : 2 ≤ l.length := by
  match l with
  | [] => simp at h0
  | [c] =>
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at h0 h1
    subst h0
    exact absurd h1 hab
  | c :: d :: r => simp

theorem cellIndex_lt_count (l : List ℝ) (hl : 2 ≤ l.length) (u : ℝ) : cellIndex l u < cellCount l := by
  have h : cellIndex l u ≤ ((l.drop 1).dropLast).length := List.length_filter_le _ _
  simp only [List.length_dropLast, List.length_drop] at h
  unfold cellCount
  omega

theorem cellIndex_right (l : List ℝ) (u : ℝ) : ∀ᶠ s in 𝓝[≥] u, cellIndex l s = cellIndex l u := by
  have hfin : {b | b ∈ (l.drop 1).dropLast}.Finite := ((l.drop 1).dropLast).finite_toSet
  have h : ∀ᶠ s in 𝓝[≥] u, ∀ b ∈ {b | b ∈ (l.drop 1).dropLast}, decide (b ≤ s) = decide (b ≤ u) := by
    rw [Filter.eventually_all_finite hfin]
    intro b _
    rcases le_or_gt b u with h | h
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : u ≤ s := hs
      simp [h, h.trans hs']
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds h)] with s hs
      have hs' : s < b := hs
      simp [not_le.2 h, not_le.2 hs']
  filter_upwards [h] with s hs
  unfold cellIndex
  congr 1
  exact List.filter_congr fun b hb => hs b hb

theorem cellIndex_left (l : List ℝ) (u : ℝ) :
    ∀ᶠ s in 𝓝[<] u, cellIndex l s = ((l.drop 1).dropLast.filter (fun b => decide (b < u))).length := by
  have hfin : {b | b ∈ (l.drop 1).dropLast}.Finite := ((l.drop 1).dropLast).finite_toSet
  have h : ∀ᶠ s in 𝓝[<] u, ∀ b ∈ {b | b ∈ (l.drop 1).dropLast}, decide (b ≤ s) = decide (b < u) := by
    rw [Filter.eventually_all_finite hfin]
    intro b _
    rcases lt_or_ge b u with h | h
    · filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds h)] with s hs
      have hs' : b < s := hs
      simp [h, hs'.le]
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : s < u := hs
      simp [not_lt.2 h, not_le.2 (lt_of_lt_of_le hs' h)]
  filter_upwards [h] with s hs
  unfold cellIndex
  congr 1
  exact List.filter_congr fun b hb => hs b hb

theorem sorted_counts (I : List ℝ) (hI : I.Pairwise (· < ·)) (p : ℕ) (hp : p < I.length) :
    (I.filter (fun b => decide (b < I[p]))).length = p ∧
      (I.filter (fun b => decide (b ≤ I[p]))).length = p + 1 := by
  induction I generalizing p with
  | nil => simp at hp
  | cons c r ih =>
    rw [List.pairwise_cons] at hI
    cases p with
    | zero =>
      simp only [List.getElem_cons_zero]
      have hr1 : r.filter (fun b => decide (b < c)) = [] :=
        List.filter_eq_nil_iff.2 fun b hb => by simpa using (hI.1 b hb).le
      have hr2 : r.filter (fun b => decide (b ≤ c)) = [] :=
        List.filter_eq_nil_iff.2 fun b hb => by simpa using hI.1 b hb
      simp [hr1, hr2]
    | succ q =>
      simp only [List.getElem_cons_succ]
      have hq : q < r.length := by simpa using hp
      have hc : c < r[q] := hI.1 _ (List.getElem_mem hq)
      obtain ⟨h1, h2⟩ := ih hI.2 q hq
      simp [hc, hc.le, h1, h2]

theorem piecewise_hasDerivAt (l : List ℝ) (hs : l.Pairwise (· < ·)) (f f' : ℕ → ℝ → ℂ)
    (hd : ∀ i s, HasDerivAt (f i) (f' i s) s)
    (h0 : ∀ i, 1 ≤ i → i < cellCount l → f (i - 1) (l.getD i 0) = f i (l.getD i 0))
    (h1 : ∀ i, 1 ≤ i → i < cellCount l → f' (i - 1) (l.getD i 0) = f' i (l.getD i 0)) (u : ℝ) :
    HasDerivAt (fun s => f (cellIndex l s) s) (f' (cellIndex l u) u) u := by
  have hR := cellIndex_right l u
  have hL := cellIndex_left l u
  by_cases hu : u ∈ (l.drop 1).dropLast
  · obtain ⟨p, hp, hpu⟩ := List.getElem_of_mem hu
    subst hpu
    have hIs : ((l.drop 1).dropLast).Pairwise (· < ·) :=
      List.Pairwise.sublist ((List.dropLast_sublist _).trans (List.drop_sublist 1 l)) hs
    obtain ⟨hlt, hle⟩ := sorted_counts _ hIs p hp
    have hk : cellIndex l ((l.drop 1).dropLast)[p] = p + 1 := hle
    have hlen : ((l.drop 1).dropLast).length = l.length - 1 - 1 := by simp
    have hcount : p + 1 < cellCount l := by unfold cellCount; omega
    have hget : l.getD (p + 1) 0 = ((l.drop 1).dropLast)[p] := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      simp [List.getElem_dropLast]
    have hv0 := h0 (p + 1) (by omega) hcount
    have hv1 := h1 (p + 1) (by omega) hcount
    simp only [Nat.add_sub_cancel, hget] at hv0 hv1
    rw [hk]
    have hRd : HasDerivWithinAt (fun s => f (cellIndex l s) s) (f' (p + 1) ((l.drop 1).dropLast)[p])
        (Set.Ici ((l.drop 1).dropLast)[p]) ((l.drop 1).dropLast)[p] := by
      refine (hd (p + 1) _).hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [hR] with s hs
        rw [hs, hk]
      · simp only [hk]
    have hLd : HasDerivWithinAt (fun s => f (cellIndex l s) s) (f' (p + 1) ((l.drop 1).dropLast)[p])
        (Set.Iic ((l.drop 1).dropLast)[p]) ((l.drop 1).dropLast)[p] := by
      rw [← hv1]
      refine HasDerivWithinAt.Iic_of_Iio ?_
      refine (hd p _).hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [hL] with s hs
        rw [hs, hlt]
      · simp only [hk, hv0]
    have h := hLd.union hRd
    rw [Set.Iic_union_Ici] at h
    exact hasDerivWithinAt_univ.1 h
  · have heq : ((l.drop 1).dropLast.filter (fun b => decide (b < u))) =
        (l.drop 1).dropLast.filter (fun b => decide (b ≤ u)) := by
      refine List.filter_congr fun b hb => ?_
      have hne : b ≠ u := fun h => hu (h ▸ hb)
      simp [lt_iff_le_and_ne, hne]
    have hev : ∀ᶠ s in 𝓝 u, cellIndex l s = cellIndex l u := by
      rw [← nhdsLT_sup_nhdsGE]
      refine Filter.eventually_sup.2 ⟨?_, hR⟩
      filter_upwards [hL] with s hs
      rw [hs, heq]
      rfl
    refine (hd (cellIndex l u) u).congr_of_eventuallyEq ?_
    filter_upwards [hev] with s hs
    rw [hs]

end Internal

theorem splineDerivatives_holds : SplineDerivatives := by
  intro a b S hS
  have htl := Internal.two_le_length S.mesh.tBreaks (by norm_num) hS.mesh.t_first hS.mesh.t_last
  have hxl := Internal.two_le_length S.mesh.xBreaks (by norm_num) hS.mesh.x_first hS.mesh.x_last
  refine ⟨fun ha => ⟨⟨hS.mesh, ?_, ?_⟩, ?_⟩, fun hb => ⟨⟨hS.mesh, ?_, ?_⟩, ?_⟩⟩
  · intro i hi1 hi2 j hj o ho
    have h := hS.t_joins i hi1 hi2 j hj (o + 1) (by omega)
    simpa only [tDerivSpline, tDeriv, Function.iterate_add_apply] using h
  · intro j hj1 hj2 i hi o ho
    have h := congrArg (MvPolynomial.pderiv 0) (hS.x_joins j hj1 hj2 i hi o ho)
    show atSecond _ (xDeriv o (tDeriv 1 _)) = atSecond _ (xDeriv o (tDeriv 1 _))
    simp only [tDeriv, Function.iterate_one]
    rw [Internal.xDeriv_pderiv_zero, Internal.xDeriv_pderiv_zero, Internal.atSecond_pderiv_zero,
      Internal.atSecond_pderiv_zero]
    exact h
  · intro t x
    have hj := Internal.cellIndex_lt_count _ hxl x
    exact (Internal.piecewise_hasDerivAt S.mesh.tBreaks hS.mesh.t_sorted
      (fun i s => MvPolynomial.eval ![(s : ℂ), (x : ℂ)] (S.piece i (cellIndex S.mesh.xBreaks x)))
      (fun i s => MvPolynomial.eval ![(s : ℂ), (x : ℂ)]
        (MvPolynomial.pderiv 0 (S.piece i (cellIndex S.mesh.xBreaks x))))
      (fun i s => Internal.hasDerivAt_eval_first _ _ s)
      (fun i h1 h2 => by
        have h := congrArg (MvPolynomial.eval ![((S.mesh.tBreaks.getD i 0 : ℝ) : ℂ), (x : ℂ)])
          (hS.t_joins i h1 h2 _ hj 0 (Nat.zero_le _))
        simpa only [tDeriv, Function.iterate_zero, id, Internal.eval_atFirst] using h)
      (fun i h1 h2 => by
        have h := congrArg (MvPolynomial.eval ![((S.mesh.tBreaks.getD i 0 : ℝ) : ℂ), (x : ℂ)])
          (hS.t_joins i h1 h2 _ hj 1 ha)
        simpa only [tDeriv, Function.iterate_one, Internal.eval_atFirst] using h) t).deriv
  · intro i hi1 hi2 j hj o ho
    have h := congrArg (MvPolynomial.pderiv 1) (hS.t_joins i hi1 hi2 j hj o ho)
    show atFirst _ (tDeriv o (xDeriv 1 _)) = atFirst _ (tDeriv o (xDeriv 1 _))
    simp only [xDeriv, Function.iterate_one]
    rw [Internal.tDeriv_pderiv_one, Internal.tDeriv_pderiv_one, Internal.atFirst_pderiv_one,
      Internal.atFirst_pderiv_one]
    exact h
  · intro j hj1 hj2 i hi o ho
    have h := hS.x_joins j hj1 hj2 i hi (o + 1) (by omega)
    simpa only [xDerivSpline, xDeriv, Function.iterate_add_apply] using h
  · intro t x
    have hi := Internal.cellIndex_lt_count _ htl t
    exact (Internal.piecewise_hasDerivAt S.mesh.xBreaks hS.mesh.x_sorted
      (fun j s => MvPolynomial.eval ![(t : ℂ), (s : ℂ)] (S.piece (cellIndex S.mesh.tBreaks t) j))
      (fun j s => MvPolynomial.eval ![(t : ℂ), (s : ℂ)]
        (MvPolynomial.pderiv 1 (S.piece (cellIndex S.mesh.tBreaks t) j)))
      (fun j s => Internal.hasDerivAt_eval_second _ _ s)
      (fun j h1 h2 => by
        have h := congrArg (MvPolynomial.eval ![(t : ℂ), ((S.mesh.xBreaks.getD j 0 : ℝ) : ℂ)])
          (hS.x_joins j h1 h2 _ hi 0 (Nat.zero_le _))
        simpa only [xDeriv, Function.iterate_zero, id, Internal.eval_atSecond] using h)
      (fun j h1 h2 => by
        have h := congrArg (MvPolynomial.eval ![(t : ℂ), ((S.mesh.xBreaks.getD j 0 : ℝ) : ℂ)])
          (hS.x_joins j h1 h2 _ hi 1 hb)
        simpa only [xDeriv, Function.iterate_one, Internal.eval_atSecond] using h) x).deriv

end GivenShape

end CertCell

end Breakdown
