import TorusEuler.Paper.SBD.Statements
import TorusEuler.Paper.Proofs.SBD.Library.HolderWords

/-! # Proof of display (D.2) (half-Hölder norms from supremum norms)

Conditional proof `Paper.Proof.Text.eq_D_2` of `Paper.Statement.Text.eq_D_2`
(`cc:uf:trunc:eq:holder-sup`, sections/appD_finite_norms.tex:30-40 of the
latest manuscript). The display is a leaf of the proof spine: its derivation
cites no numbered result, so the Lean proof has no hypotheses. -/

open MeasureTheory Set
open scoped ContDiff Pointwise

namespace TorusEuler.Paper

open AppendixD Lib.SBD

/-- Proof of **display (D.2)** (`cc:uf:trunc:eq:holder-sup`), following
sections/appD_finite_norms.tex:30-40. The derivation cites no numbered result,
so this leaf has no hypotheses.

* appD:31-33 (`[v]_{C^{0,1/2}} ≤ (2‖v‖_∞‖∇v‖_∞)^{1/2}`): the interpolation
  `Lib.SBD.norm_sub_sqrt_of_derivative'`, applied to `v = ∂_a^β c` inside the
  per-word bound `Lib.SBD.holderWord_le`; the gradient of the word `β` in the
  directions `ℓ_* e_i` is controlled by the words `β i` of order `m + 1`
  (`phaseOperatorWord_constantDirections_perm`), at the cost `ℓ_*^{-1}`.
* appD:34-37, first inequality of (D.2) at every order `m`, using
  `ℓ_* ≤ 1`: summing the per-word bound over the nondecreasing words of
  length `m`, each `β ↦ β i` is injective into the words of length `m + 1`
  (`Lib.SBD.appendSorted'_injective`); this gives the sharper per-order bound
  `ℓ_*^m |c|_{m,1/2} ≤ ℓ_*^{-1/2} (ℓ_*^m |c|_m + 3 ℓ_*^{m+1} |c|_{m+1})`
  (`key`), hence the first inequality with `C = 4`; the weighted words are
  `ℓ_*^m` times the unit words (`jetValues_labelDirection`).
* appD:38-39, "hence": `‖c‖_{[n]} ≤ ‖c‖_{[n],1/2}` because each half-Hölder
  word quantity contains the supremum one (the first part of
  `paperAppendixD_holderComparison`, own content of this row, re-run inline),
  and `‖c‖_{[n],1/2} ≤ 4 ℓ_*^{-1/2} ‖c‖_{[n+1]}` by summing `key` over
  `m ≤ n` (`holderFieldNorm_eq_sum`; both sums of `ℓ_*^m |c|_m` are at most
  `‖c‖_{[n+1]}`).

The library lemmas `paperAppendixD_holderComparison` and
`hierarchyFiniteWordNorm_holder_le` are not called: their proofs reach
`hierarchyFiniteWordNorm_constDerivative_le`, a content lemma of Lemma D.1,
which the derivation of (D.2) does not use. -/
theorem Proof.Text.eq_D_2 : Statement.Text.eq_D_2 := by
  intro I E _ _ ℓ hℓ hℓ₁ c
  let D := hierarchyLabelDirection ℓ
  have hsℓ : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ
  have bddℓ {k : ℕ} (hc : CoefficientNormFinite k c) (w : List (Fin 3))
      (hw : w ∈ hierarchyAdmissibleWords (Fin 3) k) :
      BddAbove (hierarchyJetValues False D w c) := by
    change BddAbove (hierarchyJetValues False (hierarchyLabelDirection ℓ) w c)
    rw [jetValues_labelDirection False ℓ w hc.1]
    exact (hc.2 w hw).smul_of_nonneg (norm_nonneg _)
  have hsSup (holder : Prop) (w : List (Fin 3)) (hcs : ∀ t, ContDiff ℝ ∞ (c t)) :
      sSup (hierarchyJetValues holder D w c) =
        ℓ ^ w.length * sSup (hierarchyJetValues holder (hierarchyLabelDirection 1) w c) := by
    change sSup (hierarchyJetValues holder (hierarchyLabelDirection ℓ) w c) = _
    rw [jetValues_labelDirection holder ℓ w hcs, Real.sSup_smul_of_nonneg (norm_nonneg _),
      smul_eq_mul, Real.norm_of_nonneg (pow_nonneg hℓ.le _)]
  -- the sharper per-order bound `ℓ^m |c|_{m,1/2} ≤ (ℓ^m |c|_m + 3 ℓ^{m+1} |c|_{m+1}) / √ℓ`
  have key : ∀ m : ℕ, CoefficientNormFinite (m + 1) c →
      (∀ w ∈ appendixCoefficientOrderWords m,
          BddAbove (hierarchyJetValues True (hierarchyLabelDirection 1) w c)) ∧
        0 ≤ ℓ ^ m * coefficientOrderNorm m c ∧
        0 ≤ ℓ ^ (m + 1) * coefficientOrderNorm (m + 1) c ∧
        ℓ ^ m * holderOrderNorm m c ≤
          (ℓ ^ m * coefficientOrderNorm m c +
            3 * (ℓ ^ (m + 1) * coefficientOrderNorm (m + 1) c)) / Real.sqrt ℓ := by
    intro m hc
    let W := appendixCoefficientOrderWords
    let A (w : List (Fin 3)) := sSup (hierarchyJetValues False D w c)
    have hWm (w : List (Fin 3)) (hw : w ∈ W m) : w ∈ hierarchyAdmissibleWords (Fin 3) m :=
      (Finset.mem_filter.mp hw).1
    have hlen {k : ℕ} (w : List (Fin 3)) (hw : w ∈ W k) : w.length = k :=
      (Finset.mem_filter.mp hw).2
    have hup {k : ℕ} (hk : k ≤ m + 1) (w : List (Fin 3)) (hw : w ∈ W k) :
        w ∈ hierarchyAdmissibleWords (Fin 3) (m + 1) := by
      obtain ⟨h1, h2⟩ := mem_hierarchyAdmissibleWords.mp (Finset.mem_filter.mp hw).1
      exact mem_hierarchyAdmissibleWords.mpr ⟨h1.trans hk, h2⟩
    have hupper (w : List (Fin 3)) (hw : w ∈ W m) :=
      holderWord_le ℓ hℓ hℓ₁ hc.1 w (bddℓ hc w (hup (Nat.le_succ m) w hw))
        (fun i => bddℓ hc _ (appendSorted'_mem i (hWm w hw)))
    have hA0 {k : ℕ} (hk : k ≤ m + 1) (w : List (Fin 3)) (hw : w ∈ W k) : 0 ≤ A w :=
      le_csSup (bddℓ hc w (hup hk w hw)) (Or.inl rfl)
    have hFk {k : ℕ} : ∑ w ∈ W k, A w = ℓ ^ k * coefficientOrderNorm k c := by
      unfold coefficientOrderNorm
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w hw => ?_
      exact (hsSup False w hc.1).trans (by rw [hlen w hw])
    have hF2 (i : Fin 3) : ∑ w ∈ W m, A (appendSorted' i w) ≤
        ℓ ^ (m + 1) * coefficientOrderNorm (m + 1) c := by
      have hinj : Set.InjOn (appendSorted' i) (W m : Set (List (Fin 3))) :=
        (appendSorted'_injective i (n := m)).mono fun w hw => hWm w hw
      rw [← Finset.sum_image (f := A) hinj]
      have hsub : (W m).image (appendSorted' i) ⊆ W (m + 1) := by
        intro u hu
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
        refine Finset.mem_filter.mpr ⟨appendSorted'_mem i (hWm w hw), ?_⟩
        rw [(appendSorted'_perm i w).length_eq, List.length_append, List.length_singleton,
          hlen w hw]
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun u hu _ => hA0 le_rfl u hu)).trans_eq hFk
    have hx : 0 ≤ ℓ ^ m * coefficientOrderNorm m c := by
      rw [← hFk]
      exact Finset.sum_nonneg fun w hw => hA0 (Nat.le_succ m) w hw
    have hy : 0 ≤ ℓ ^ (m + 1) * coefficientOrderNorm (m + 1) c := by
      rw [← hFk]
      exact Finset.sum_nonneg fun w hw => hA0 le_rfl w hw
    refine ⟨fun w hw => ?_, hx, hy, ?_⟩
    · have h : BddAbove (hierarchyJetValues True (hierarchyLabelDirection ℓ) w c) :=
        ⟨_, hupper w hw⟩
      rw [jetValues_labelDirection True ℓ w hc.1] at h
      have hpos : 0 < ‖ℓ ^ w.length‖ := norm_pos_iff.mpr (pow_ne_zero _ hℓ.ne')
      have h' := h.smul_of_nonneg (inv_nonneg.mpr hpos.le)
      rwa [inv_smul_smul₀ hpos.ne'] at h'
    · calc ℓ ^ m * holderOrderNorm m c
          = ∑ w ∈ W m, sSup (hierarchyJetValues True D w c) := by
            unfold holderOrderNorm
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun w hw => ?_
            rw [hsSup True w hc.1, hlen w hw]
        _ ≤ ∑ w ∈ W m, (A w + ∑ i : Fin 3, A (appendSorted' i w)) / Real.sqrt ℓ :=
            Finset.sum_le_sum fun w hw => csSup_le ⟨0, Or.inl rfl⟩ (hupper w hw)
        _ = ((∑ w ∈ W m, A w) + ∑ i : Fin 3, ∑ w ∈ W m, A (appendSorted' i w)) /
              Real.sqrt ℓ := by
            rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_comm (s := W m)]
        _ ≤ (ℓ ^ m * coefficientOrderNorm m c +
              ∑ _i : Fin 3, ℓ ^ (m + 1) * coefficientOrderNorm (m + 1) c) / Real.sqrt ℓ := by
            rw [hFk]
            exact div_le_div_of_nonneg_right (add_le_add le_rfl
              (Finset.sum_le_sum fun i _ => hF2 i)) hsℓ.le
        _ = _ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
  have hi : 0 ≤ (Real.sqrt ℓ)⁻¹ := inv_nonneg.mpr hsℓ.le
  refine ⟨fun m hc => ?_, fun n hc => ?_⟩
  · -- the first bound of (D.2), at order `m`
    obtain ⟨hB, hx, hy, hk⟩ := key m hc
    refine ⟨hB, hk.trans ?_⟩
    rw [div_eq_mul_inv]
    nlinarith [mul_nonneg hi hx, mul_nonneg hi hy]
  · -- "hence": the comparison of the norms of order `n`
    have hfin : HolderFieldNormFinite ℓ n c := by
      refine ⟨hc.1, fun w hw => ⟨_, holderWord_le ℓ hℓ hℓ₁ hc.1 w ?_
        (fun i => bddℓ hc _ (appendSorted'_mem i hw))⟩⟩
      obtain ⟨h1, h2⟩ := mem_hierarchyAdmissibleWords.mp hw
      exact bddℓ hc w (mem_hierarchyAdmissibleWords.mpr ⟨h1.trans (Nat.le_succ n), h2⟩)
    have hmono (m : ℕ) (hm : m ≤ n) : CoefficientNormFinite (m + 1) c := by
      refine ⟨hc.1, fun w hw => hc.2 w ?_⟩
      obtain ⟨h1, h2⟩ := mem_hierarchyAdmissibleWords.mp hw
      exact mem_hierarchyAdmissibleWords.mpr ⟨h1.trans (by omega), h2⟩
    refine ⟨hfin, ?_, ?_⟩
    · -- `‖c‖_{[n]} ≤ ‖c‖_{[n],1/2}`: each half-Hölder word quantity contains the supremum
      rw [coefficientNorm_eq_labelWordNorm hℓ.le n hc.1]
      unfold holderFieldNorm hierarchyFiniteWordNorm
      refine Finset.sum_le_sum fun w hw => csSup_le_csSup (hfin.2 w hw) ⟨0, Or.inl rfl⟩ ?_
      rintro r (h | h | ⟨h, _⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact h.elim
    · -- `‖c‖_{[n],1/2} ≤ 4 ℓ^{-1/2} ‖c‖_{[n+1]}`: sum the per-order bound over `m ≤ n`
      rw [holderFieldNorm_eq_sum hℓ.le n hc.1]
      let x : ℕ → ℝ := fun m => ℓ ^ m * coefficientOrderNorm m c
      have hx0 (m : ℕ) (hm : m ≤ n + 1) : 0 ≤ x m := by
        rcases Nat.lt_or_ge m (n + 1) with h | h
        · exact (key m (hmono m (by omega))).2.1
        · obtain rfl : m = n + 1 := by omega
          exact (key n (hmono n le_rfl)).2.2.1
      have hsum : ∑ m ∈ Finset.range (n + 1), ℓ ^ m * holderOrderNorm m c ≤
          ∑ m ∈ Finset.range (n + 1), (x m + 3 * x (m + 1)) / Real.sqrt ℓ :=
        Finset.sum_le_sum fun m hm =>
          (key m (hmono m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)))).2.2.2
      have hN1 : ∑ m ∈ Finset.range (n + 1), x m ≤ coefficientNorm ℓ (n + 1) c := by
        unfold coefficientNorm
        rw [Finset.sum_range_succ _ (n + 1)]
        exact le_add_of_nonneg_right (hx0 (n + 1) le_rfl)
      have hN2 : ∑ m ∈ Finset.range (n + 1), x (m + 1) ≤ coefficientNorm ℓ (n + 1) c := by
        unfold coefficientNorm
        rw [Finset.sum_range_succ' _ (n + 1)]
        exact le_add_of_nonneg_right (hx0 0 (Nat.zero_le _))
      refine hsum.trans ?_
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, div_eq_mul_inv]
      have h3 := mul_le_mul_of_nonneg_right
        (add_le_add hN1 (mul_le_mul_of_nonneg_left hN2 (by norm_num : (0 : ℝ) ≤ 3))) hi
      linarith

end TorusEuler.Paper
