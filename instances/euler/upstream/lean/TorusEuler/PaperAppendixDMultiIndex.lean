import TorusEuler.PaperAppendixDCoordinate

/-! The derivative sums indexed by ordinary multi-indices in Appendix D. -/

open Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

variable {I A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Each nondecreasing coordinate word of length `m` represents one
spatial multi-index of order `m`. -/
def appendixCoefficientOrderWords (m : ℕ) : Finset (List (Fin 3)) :=
  (hierarchyAdmissibleWords (Fin 3) m).filter fun w => w.length = m

/-- The sum of the exact-order coordinate derivative supremums. -/
def appendixCoefficientMultiIndexNorm (m : ℕ) (c : I → Vec3 → A) : ℝ :=
  ∑ w ∈ appendixCoefficientOrderWords m,
    sSup (hierarchyJetValues False (hierarchyLabelDirection 1) w c)

/-- The coefficient power bound of Appendix D using one term per multi-index. -/
def FiniteCoefficientMultiIndexPower (D : ℝ) (a : ℕ) (c : I → Vec3 → A) : Prop :=
  (∀ t, ContDiff ℝ ∞ (c t)) ∧ ∃ C : ℕ → ℝ, (∀ m, 1 ≤ C m) ∧
    (∀ m w, w ∈ appendixCoefficientOrderWords m →
      BddAbove (hierarchyJetValues False (hierarchyLabelDirection 1) w c)) ∧
    ∀ m, appendixCoefficientMultiIndexNorm m c ≤ C m * D ^ (a * (m + 1))

private theorem appendixLabelDirection_one :
    hierarchyLabelDirection 1 = fun j _ => coordinateDirection j := by
  funext j x
  exact one_smul ℝ (coordinateDirection j)

private theorem appendixDirectionalWord_eq_coordinate (m : ℕ) (β : Fin m → Fin 3)
    {f : Vec3 → A} (hf : ContDiff ℝ ∞ f) (x : Vec3) :
    phaseOperatorWord (hierarchyLabelDirection 1) (List.ofFn β) f x =
      iteratedFDeriv ℝ m f x (fun j => coordinateDirection (β j)) := by
  rw [appendixLabelDirection_one, phaseOperatorWord_constant_eq_iteratedFDeriv _ hf]
  simp only [List.get_ofFn]
  have h (k : ℕ) (hk : k = m) :
      iteratedFDeriv ℝ k f x (fun j => coordinateDirection (β (Fin.cast hk j))) =
        iteratedFDeriv ℝ m f x (fun j => coordinateDirection (β j)) := by subst k; rfl
  exact h _ List.length_ofFn

/-- The operator norm bounds and the manuscript's multi-index bounds
are equivalent without changing the power of the parent parameter. -/
theorem finiteCoefficientPower_iff_multiIndex {D : ℝ} (hD : 1 ≤ D) {a : ℕ} {c : I → Vec3 → A} :
    FiniteCoefficientPower D a c ↔ FiniteCoefficientMultiIndexPower D a c := by
  constructor
  · rintro ⟨hs, C, hC, h⟩
    have hb (m : ℕ) (w : List (Fin 3)) (hw : w ∈ appendixCoefficientOrderWords m) :
        C m * D ^ (a * (m + 1)) ∈ upperBounds (hierarchyJetValues False (hierarchyLabelDirection 1) w c) := by
      have hlen := (Finset.mem_filter.mp hw).2
      rintro y (rfl | ⟨t, x, rfl⟩ | ⟨hf, _⟩)
      · have := zero_le_one.trans hD
        exact mul_nonneg (zero_le_one.trans (hC m)) (by positivity)
      · rw [appendixLabelDirection_one, phaseOperatorWord_constant_eq_iteratedFDeriv _ (hs t)]
        refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
        calc
          _ ≤ C w.length * D ^ (a * (w.length + 1)) := by
            simpa [coordinateDirection] using h w.length t x
          _ = _ := by rw [hlen]
      · exact hf.elim
    refine ⟨hs, fun m => (1 + (appendixCoefficientOrderWords m).card) * C m, fun m =>
      one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (Nat.cast_nonneg _)) (hC m), fun m w hw => ⟨_, hb m w hw⟩, fun m => ?_⟩
    unfold appendixCoefficientMultiIndexNorm
    calc
      _ ≤ ∑ _w ∈ appendixCoefficientOrderWords m, C m * D ^ (a * (m + 1)) :=
        Finset.sum_le_sum fun w hw => csSup_le ⟨0, Or.inl rfl⟩ (hb m w hw)
      _ = ((appendixCoefficientOrderWords m).card : ℝ) * (C m * D ^ (a * (m + 1))) := by
        simp
      _ ≤ _ := by
        have h₀ : 0 ≤ C m * D ^ (a * (m + 1)) :=
          mul_nonneg (zero_le_one.trans (hC m)) (pow_nonneg (zero_le_one.trans hD) _)
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) h₀
  · rintro ⟨hs, C, hC, hb, h⟩
    apply (finiteCoefficientPower_iff_coordinate hD).mpr
    have hp (m : ℕ) (β : Fin m → Fin 3) (p : I × Vec3) :
        ‖iteratedFDeriv ℝ m (c p.1) p.2 (fun j => coordinateDirection (β j))‖ ≤
          C m * D ^ (a * (m + 1)) := by
      let w := (List.ofFn β).mergeSort (· ≤ ·)
      have hperm : w.Perm (List.ofFn β) := List.mergeSort_perm _ _
      have hlen : w.length = m := hperm.length_eq.trans List.length_ofFn
      have hw : w ∈ appendixCoefficientOrderWords m :=
        Finset.mem_filter.mpr ⟨mem_hierarchyAdmissibleWords.mpr
          ⟨hlen.le, List.pairwise_mergeSort' (· ≤ ·) _⟩, hlen⟩
      have hword := congrFun (phaseOperatorWord_constantDirections_perm coordinateDirection (hs p.1) hperm) p.2
      rw [← appendixDirectionalWord_eq_coordinate m β (hs p.1), appendixLabelDirection_one, ← hword,
        ← appendixLabelDirection_one]
      exact (le_csSup (hb m w hw) (Or.inr (Or.inl ⟨p.1, p.2, rfl⟩))).trans
        ((Finset.single_le_sum (fun v hv => le_csSup (hb m v hv) (Or.inl rfl)) hw).trans (h m))
    have hupper (m : ℕ) (β : Fin m → Fin 3) :
        C m * D ^ (a * (m + 1)) ∈ upperBounds (insert 0 (range fun p : I × Vec3 =>
          ‖iteratedFDeriv ℝ m (c p.1) p.2 (fun j => coordinateDirection (β j))‖)) := by
      rintro y (rfl | ⟨p, rfl⟩)
      · have := zero_le_one.trans hD
        exact mul_nonneg (zero_le_one.trans (hC m)) (by positivity)
      · exact hp m β p
    refine ⟨hs, fun m => (3 : ℝ) ^ m * C m, fun m =>
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (hC m),
      fun m β => ⟨_, hupper m β⟩, fun m => ?_⟩
    unfold appendixCoefficientCoordinateNorm
    calc
      _ ≤ ∑ _β : Fin m → Fin 3, C m * D ^ (a * (m + 1)) :=
        Finset.sum_le_sum fun β _ => csSup_le ⟨0, mem_insert _ _⟩ (hupper m β)
      _ = _ := by simp [mul_assoc]

/-- Lemma D.2(a) in the ordinary multi-index sums. -/
theorem paperLemmaD2_mul_multiIndex {D : ℝ} {a : ℕ} (hD : 1 ≤ D) {c d : I → Vec3 → A}
    (hc : FiniteCoefficientMultiIndexPower D a c) (hd : FiniteCoefficientMultiIndexPower D a d) :
    FiniteCoefficientMultiIndexPower D (2 * a) (fun t x => c t x * d t x) :=
  (finiteCoefficientPower_iff_multiIndex hD).mp (paperLemmaD2_mul hD
    ((finiteCoefficientPower_iff_multiIndex hD).mpr hc) ((finiteCoefficientPower_iff_multiIndex hD).mpr hd))

/-- Lemma D.2(b) in the ordinary multi-index sums. -/
theorem paperLemmaD2_inverse_multiIndex [CompleteSpace A] {D : ℝ} {a : ℕ} (hD : 1 ≤ D)
    {c : I → Vec3 → A} (hc : FiniteCoefficientMultiIndexPower D a c)
    (hUnit : ∀ t x, IsUnit (c t x)) (hInv : ∀ t x, ‖Ring.inverse (c t x)‖ ≤ D ^ a) :
    FiniteCoefficientMultiIndexPower D (3 * a) (fun t x => Ring.inverse (c t x)) :=
  (finiteCoefficientPower_iff_multiIndex hD).mp (paperLemmaD2_inverse hD
    ((finiteCoefficientPower_iff_multiIndex hD).mpr hc) hUnit hInv)

/-- Lemma D.2(c), including the portion of the radius retained whenever
at least one derivative falls on the coefficient. -/
theorem paperLemmaD2_weighted_multiIndex {D ℓ : ℝ} {a : ℕ} (hD : 1 ≤ D)
    (hℓ : 0 ≤ ℓ) (hscale : ℓ * D ^ a ≤ 1) {c : I → Vec3 → A}
    (hc : FiniteCoefficientMultiIndexPower D a c) :
    ∃ C : ℕ → ℝ,
      (∀ n, (∑ m ∈ Finset.range (n + 1), ℓ ^ m * appendixCoefficientMultiIndexNorm m c)
        ≤ (∑ m ∈ Finset.range (n + 1), C m) * D ^ a) ∧
      (∀ m ≥ 1, ℓ ^ m * appendixCoefficientMultiIndexNorm m c ≤ C m * D ^ (2 * a) * ℓ) := by
  obtain ⟨_, C, hC, _, hbound⟩ := hc
  have hgain m (hm : 1 ≤ m) := hierarchy_weighted_coefficient_le hD hℓ
    (zero_le_one.trans (hC m)) hscale hm (hbound m)
  refine ⟨C, ?_, hgain⟩
  intro n
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun m _ => ?_
  rcases m with _ | m
  · simpa using hbound 0
  · refine (hgain (m + 1) (by omega)).trans ?_
    calc
      _ = (ℓ * D ^ a) * (C (m + 1) * D ^ a) := by rw [two_mul, pow_add]; ring
      _ ≤ _ := mul_le_of_le_one_left
        (mul_nonneg (zero_le_one.trans (hC (m + 1))) (pow_nonneg (zero_le_one.trans hD) _)) hscale

end

end TorusEuler
