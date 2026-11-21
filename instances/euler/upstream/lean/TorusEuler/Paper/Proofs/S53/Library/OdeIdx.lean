import TorusEuler.Paper.Proofs.S53.Library.OdeZero

/-!
# S53 library: the weighted word recurrence for a finite ordered set of directions, from Lemma D.3
-/

open Set
open scoped ContDiff


namespace TorusEuler.Paper.Lib.S53

noncomputable section

open TorusEuler

section Words

variable {Idx V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (s : Slab)

/-- Auxiliary fact `wordE` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem wordE (w : List Idx) (u : Esub Idx V s) :
    (appendixDerivativeWord (DE s) w u).1 = fun v => u.1 (w.reverse ++ v) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext v
    rw [appendixDerivativeWord_cons, DE_apply, ih]
    simp

/-- Auxiliary fact `wordA` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem wordA (w : List Idx) (a : Asub Idx V s) :
    (appendixDerivativeWord (DA s) w a).1 = fun v => a.1 (w.reverse ++ v) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext v
    rw [appendixDerivativeWord_cons, DA_apply, ih]
    simp

/-- Auxiliary fact `wordF_fst` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem wordF_fst (w : List Idx) (x : Fsub Idx V s) :
    (appendixDerivativeWord (DF s) w x).1.1 = fun v => x.1.1 (w.reverse ++ v) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext v
    rw [appendixDerivativeWord_cons, DF_apply_fst, ih]
    simp

/-- Auxiliary fact `wordF_snd` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem wordF_snd (w : List Idx) (x : Fsub Idx V s) :
    (appendixDerivativeWord (DF s) w x).1.2 = fun v => x.1.2 (w.reverse ++ v) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext v
    rw [appendixDerivativeWord_cons, DF_apply_snd, ih]
    simp

end Words

variable {Idx P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The weighted word recurrence at a fixed point for a finite ordered set of directions, from
Lemma D.3 (`hD3`): the constant `Cn` only depends on the index type, the order `n` and the bound
`q` of the product `K (r - l) C · #words`. -/
theorem odeIdx (hD3 : Statement.lemma_D_3) (Idx : Type) [Fintype Idx] [LinearOrder Idx] (n : ℕ)
    (q : ℝ) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (D : OdeData Idx P E) {C B H : ℝ}, 0 ≤ D.K → 0 ≤ C →
      (∀ w : List Idx, w.length ≤ n → ‖phaseOperatorWord (fun i _ => D.d i) w (D.x D.l) D.p‖ / D.g D.l ≤ B) →
      (∀ w : List Idx, w.length ≤ n → ∀ u ∈ Icc D.l D.r,
        ‖phaseOperatorWord (fun i _ => D.d i) w (D.f u) D.p‖ / D.g u ≤ H) →
      (∀ w : List Idx, w.length ≤ n → w ≠ [] → ∀ u ∈ Icc D.l D.r,
        ‖phaseOperatorWord (fun i _ => D.d i) w (D.A u) D.p‖ ≤ C) →
      D.K * (D.r - D.l) * C * ((hierarchyAdmissibleWords Idx n).card : ℝ) ≤ q →
      ∀ w ∈ hierarchyAdmissibleWords Idx n, ∀ u ∈ Icc D.l D.r,
        ‖phaseOperatorWord (fun i _ => D.d i) w (D.x u) D.p‖ / D.g u ≤
          Cn * ((hierarchyAdmissibleWords Idx n).card : ℝ) * D.K * (B + (D.r - D.l) * H) := by
  obtain ⟨Cn, hCn, h⟩ := jetD3 hD3 Idx n q
  refine ⟨Cn, hCn, fun {P E} _ _ _ _ _ _ D {C B H} hK hC0 hinit hsource hcoeff hq w hw u hu => ?_⟩
  set W : ℝ := ((hierarchyAdmissibleWords Idx n).card : ℝ) with hW
  have hlen : w.length ≤ n := (mem_hierarchyAdmissibleWords.mp hw).1
  let c := D.aE n hcoeff
  let xv := D.xE n
  let F := L0 D.slab xv + Tmap D.slab c xv
  have hlr : (0 : ℝ) ≤ D.r - D.l := sub_nonneg.mpr D.hlr.le
  have hSlow : ∀ m, 1 ≤ m → m ≤ n →
      D.K * ((D.slab.r - D.slab.l) * appendixExactOrderDerivativeNorm (pA D.slab Idx E)
        (DA D.slab) m c) ≤ q := by
    intro m hm hmn
    have hsum : appendixExactOrderDerivativeNorm (pA D.slab Idx E) (DA D.slab) m c ≤ W * C := by
      unfold appendixExactOrderDerivativeNorm
      have hterm : ∀ v ∈ (hierarchyAdmissibleWords Idx m).filter (fun v => v.length = m),
          pA D.slab Idx E (appendixDerivativeWord (DA D.slab) v c) ≤ C := by
        intro v hv
        obtain ⟨hv1, hv2⟩ := Finset.mem_filter.mp hv
        refine pA_le D.slab _ fun t ht => ?_
        rw [wordA]
        simp only [List.append_nil]
        have hvl : v.reverse.length = m := by simp [hv2]
        change ‖D.aj n v.reverse t‖ ≤ C
        rw [D.aj_of_mem (by omega) ht]
        exact hcoeff v.reverse (by omega) (by intro h0; rw [h0] at hvl; simp at hvl; omega) t ht
      refine (Finset.sum_le_card_nsmul _ _ C hterm).trans ?_
      rw [nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ hC0
      have hsub : (hierarchyAdmissibleWords Idx m).filter (fun v => v.length = m) ⊆
          hierarchyAdmissibleWords Idx n := by
        intro v hv
        obtain ⟨hv1, _⟩ := Finset.mem_filter.mp hv
        rw [mem_hierarchyAdmissibleWords] at hv1 ⊢
        exact ⟨hv1.1.trans hmn, hv1.2⟩
      rw [hW]
      exact_mod_cast Finset.card_le_card hsub
    have hexact0 : 0 ≤ appendixExactOrderDerivativeNorm (pA D.slab Idx E) (DA D.slab) m c :=
      Finset.sum_nonneg fun v _ => apply_nonneg _ _
    calc D.K * ((D.slab.r - D.slab.l) * appendixExactOrderDerivativeNorm (pA D.slab Idx E)
          (DA D.slab) m c) ≤ D.K * ((D.r - D.l) * (W * C)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hlr) hK
      _ = D.K * (D.r - D.l) * C * W := by ring
      _ ≤ q := hq
  have key := h D.slab D.K c hK (D.zeroOrder hcoeff hK) hSlow xv F rfl
  have hF_snd : ∀ v : List Idx, F.1.2 v = D.xj n v D.l := fun v => by
    have : F.1.2 v = (L0 D.slab xv).1.2 v + (Tmap D.slab c xv).1.2 v := rfl
    rw [this, L0_snd, Tmap_snd]
    simp only [add_zero]
    rfl
  have hRHS : appendixFiniteDerivativeNorm (pF D.slab Idx E) (DF D.slab) n F ≤
      W * ((D.r - D.l) * H + B) := by
    unfold appendixFiniteDerivativeNorm
    have hterm : ∀ v ∈ hierarchyAdmissibleWords Idx n,
        pF D.slab Idx E (appendixDerivativeWord (DF D.slab) v F) ≤ (D.r - D.l) * H + B := by
      intro v hv
      have hvl := (mem_hierarchyAdmissibleWords.mp hv).1
      have hrl : v.reverse.length ≤ n := by simpa using hvl
      refine pF_le D.slab _ (H := H) (B := B) (fun t ht => ?_) ?_
      · rw [wordF_fst]
        simp only [List.append_nil]
        rw [D.equation_fst hcoeff hrl ht]
        exact hsource v.reverse hrl t ht
      · rw [wordF_snd]
        simp only [List.append_nil]
        rw [hF_snd, D.xj_of_mem hrl ⟨le_rfl, D.hlr.le⟩]
        exact hinit v.reverse hrl
    refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
    rw [nsmul_eq_mul]
  have hLHS : ‖phaseOperatorWord (fun i _ => D.d i) w (D.x u) D.p‖ / D.g u ≤
      appendixFiniteDerivativeNorm (pE D.slab Idx E) (DE D.slab) n xv := by
    have h1 := pE_ge D.slab (appendixDerivativeWord (DE D.slab) w xv) u hu
    rw [wordE] at h1
    simp only [List.append_nil] at h1
    have h2 : xv.1 w.reverse = xv.1 w := xv.2.1 (List.reverse_perm w)
    rw [h2] at h1
    change ‖D.xj n w u‖ / D.g u ≤ _ at h1
    rw [D.xj_of_mem hlen hu] at h1
    refine h1.trans ?_
    unfold appendixFiniteDerivativeNorm
    exact Finset.single_le_sum (f := fun v => pE D.slab Idx E (appendixDerivativeWord (DE D.slab) v xv))
      (fun v _ => apply_nonneg _ _) hw
  calc _ ≤ _ := hLHS
    _ ≤ _ := key
    _ ≤ Cn * D.K * (W * ((D.r - D.l) * H + B)) :=
        mul_le_mul_of_nonneg_left hRHS (mul_nonneg hCn hK)
    _ = _ := by ring

end

end TorusEuler.Paper.Lib.S53
