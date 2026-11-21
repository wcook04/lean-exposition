import Breakdown.FracCell.CellSystemDefs

noncomputable section

namespace Breakdown.CellCert.CellSystem

open Matrix
open SteadyCert Assembly Reduction GivenFields GivenModel Exterior Spectral CellAnalysis CellCoordinates CellFormula

theorem testReducer_bound_of_system {k N : ℕ} (c : FracCellData k N) {M : CellMesh} (RD : RowData M N) {slots : ℕ}
    (r : CellEntry M N k slots) (hν : 0 < c.splitVisc)
    (hsystem : ∀ w : Fin r.rows.reducerCount → ℝ,
      (r.systemReducer.transpose *ᵥ w) ⬝ᵥ (r.systemMultiplier *ᵥ (r.systemReducer.transpose *ᵥ w)) ≤ ∑ i, w i ^ 2) :
    ∀ w : Fin r.rows.reducerCount → ℝ,
      ((testReducerOf c RD r).transpose *ᵥ w) ⬝ᵥ (testMultiplierOf c RD r *ᵥ ((testReducerOf c RD r).transpose *ᵥ w))
        ≤ ∑ i, w i ^ 2 := by
  intro w
  have hσ : ∀ a, systemScale c RD a ≠ 0 := by
    intro a
    unfold systemScale systemWeight
    have : 0 < Real.sqrt c.splitVisc := Real.sqrt_pos.2 hν
    split_ifs <;> positivity
  have key : ((r.systemReducer * Matrix.diagonal (fun a => (systemScale c RD a)⁻¹)).transpose *ᵥ w) ⬝ᵥ
        ((Matrix.diagonal (systemScale c RD) * r.systemMultiplier * Matrix.diagonal (systemScale c RD)) *ᵥ
          ((r.systemReducer * Matrix.diagonal (fun a => (systemScale c RD a)⁻¹)).transpose *ᵥ w)) =
      (r.systemReducer.transpose *ᵥ w) ⬝ᵥ (r.systemMultiplier *ᵥ (r.systemReducer.transpose *ᵥ w)) := by
    have hv : (r.systemReducer * Matrix.diagonal (fun a => (systemScale c RD a)⁻¹)).transpose *ᵥ w =
        Matrix.diagonal (fun a => (systemScale c RD a)⁻¹) *ᵥ (r.systemReducer.transpose *ᵥ w) := by
      rw [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mulVec_mulVec]
    have h2 : Matrix.diagonal (systemScale c RD) * Matrix.diagonal (fun a => (systemScale c RD a)⁻¹) = (1 : Matrix (Fin N) (Fin N) ℝ) := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hσ i)
    have hM : (Matrix.diagonal (systemScale c RD) * r.systemMultiplier * Matrix.diagonal (systemScale c RD)) *ᵥ
        (Matrix.diagonal (fun a => (systemScale c RD a)⁻¹) *ᵥ (r.systemReducer.transpose *ᵥ w)) =
        Matrix.diagonal (systemScale c RD) *ᵥ (r.systemMultiplier *ᵥ (r.systemReducer.transpose *ᵥ w)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (Matrix.diagonal (systemScale c RD) * r.systemMultiplier), h2, Matrix.mul_one,
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [hv, hM]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp [hσ i]
  unfold testReducerOf testMultiplierOf
  rw [key]
  exact hsystem w

private theorem quad_restrict {N : ℕ} (S : Finset (Fin N)) (A : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ)
    (hv : ∀ a ∉ S, v a = 0) :
    v ⬝ᵥ (A *ᵥ v) = ∑ a ∈ S, ∑ b ∈ S, v a * A a b * v b := by
  symm
  calc ∑ a ∈ S, ∑ b ∈ S, v a * A a b * v b = ∑ a ∈ S, ∑ b, v a * A a b * v b :=
        Finset.sum_congr rfl fun a _ =>
          Finset.sum_subset (Finset.subset_univ S) (fun b _ hb => by simp [hv b hb])
    _ = ∑ a, ∑ b, v a * A a b * v b :=
        Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => Finset.sum_eq_zero fun b _ => by simp [hv a ha])
    _ = v ⬝ᵥ (A *ᵥ v) := by
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private theorem quad_restrict' {N : ℕ} (S : Finset (Fin N)) (A : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ)
    (hA : ∀ a b, (a ∉ S ∨ b ∉ S) → A a b = 0) :
    ∑ a ∈ S, ∑ b ∈ S, v a * A a b * v b = v ⬝ᵥ (A *ᵥ v) := by
  calc ∑ a ∈ S, ∑ b ∈ S, v a * A a b * v b = ∑ a ∈ S, ∑ b, v a * A a b * v b :=
        Finset.sum_congr rfl fun a _ =>
          Finset.sum_subset (Finset.subset_univ S) (fun b _ hb => by simp [hA a b (Or.inr hb)])
    _ = ∑ a, ∑ b, v a * A a b * v b :=
        Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => Finset.sum_eq_zero fun b _ => by simp [hA a b (Or.inl ha)])
    _ = v ⬝ᵥ (A *ᵥ v) := by
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private theorem congr_quad {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℝ) (A : Matrix n n ℝ) (w : m → ℝ) :
    (X.transpose *ᵥ w) ⬝ᵥ (A *ᵥ (X.transpose *ᵥ w)) = w ⬝ᵥ ((X * A * X.transpose) *ᵥ w) := by
  have e : (X * A * X.transpose) *ᵥ w = X *ᵥ (A *ᵥ (w ᵥ* X)) := by
    rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [e, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec w X]

theorem rowMultiplier_of_test (α : ℝ) {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (MD : ModelData M k)
    (RD : RowData M N) (Sp : CellSplit k N) (K₂ : Fin Sp.cellCount) (r : CellEntry M N k Sp.slots)
    (C : CellCoords k Sp.slots) (h : IsCellSystemFacts α c M MD RD Sp K₂ r C)
    (hmix : RD.mix * RD.testPairing * RD.mix.transpose = 1)
    (hblock : ∀ a b, RD.mix a b ≠ 0 → RD.cell a = RD.cell b ∧ RD.harmonic a = RD.harmonic b) :
    r.rows.multiplierMatrix.IsSymm ∧
      (∀ a b, (a ∉ r.rows.rowSet ∨ b ∉ r.rows.rowSet) → r.rows.multiplierMatrix a b = 0) ∧
      (∀ μ : Fin N → ℝ, (∀ a ∉ r.rows.rowSet, μ a = 0) →
        multiplierLHS c r μ ≤ ∑ a ∈ r.rows.rowSet, ∑ b ∈ r.rows.rowSet, μ a * r.rows.multiplierMatrix a b * μ b) ∧
      ∀ w : Fin r.rows.reducerCount → ℝ,
        (∑ a ∈ r.rows.rowSet, ∑ b ∈ r.rows.rowSet,
          (∑ i, r.rows.reducer i a * w i) * r.rows.multiplierMatrix a b * (∑ i, r.rows.reducer i b * w i))
          ≤ ∑ i, w i ^ 2 := by
  have hM := h.multiplier_of_test
  have hblk : ∀ a b, RD.mix a b ≠ 0 → (a ∈ r.rows.rowSet ↔ b ∈ r.rows.rowSet) := fun a b hm =>
    h.rowSet_blocks a b (hblock a b hm).1 (hblock a b hm).2
  have hdet0 : RD.mix.det ≠ 0 := by
    intro h0
    have e := congrArg Matrix.det hmix
    rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_one] at e
    simp at e
  have hdet : IsUnit RD.mix.det := isUnit_iff_ne_zero.mpr hdet0
  have hdetT : IsUnit RD.mix.transpose.det := by rwa [Matrix.det_transpose]
  have hTrows : ∀ a b, (a ∉ r.rows.rowSet ∨ b ∉ r.rows.rowSet) → testMultiplierOf c RD r a b = 0 := by
    intro a b hab
    simp only [testMultiplierOf, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [h.system_multiplier_rows a b hab]
    simp
  have hTsymm : (testMultiplierOf c RD r).transpose = testMultiplierOf c RD r := by
    unfold testMultiplierOf
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose, h.system_multiplier_symm.eq, Matrix.mul_assoc]
  have hMrows : ∀ a b, (a ∉ r.rows.rowSet ∨ b ∉ r.rows.rowSet) → r.rows.multiplierMatrix a b = 0 := by
    intro a b hab
    rw [hM]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    refine Finset.sum_eq_zero fun d _ => ?_
    rcases hab with ha | hb
    · have e : ∑ j, RD.mix a j * testMultiplierOf c RD r j d = 0 := Finset.sum_eq_zero fun j _ => by
        by_cases hm : RD.mix a j = 0
        · simp [hm]
        · have hj : j ∉ r.rows.rowSet := fun hj => ha ((hblk a j hm).2 hj)
          simp [hTrows j d (Or.inl hj)]
      rw [e, zero_mul]
    · by_cases hm : RD.mix b d = 0
      · simp [hm]
      · have hd : d ∉ r.rows.rowSet := fun hd => hb ((hblk b d hm).2 hd)
        have e : ∑ j, RD.mix a j * testMultiplierOf c RD r j d = 0 := Finset.sum_eq_zero fun j _ => by
          simp [hTrows j d (Or.inr hd)]
        rw [e, zero_mul]
  refine ⟨?_, hMrows, ?_, ?_⟩
  · unfold Matrix.IsSymm
    rw [hM, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hTsymm, Matrix.mul_assoc]
  · intro μ hμ
    have hsupp : ∀ a ∉ r.rows.rowSet, (RD.mix.transpose *ᵥ μ) a = 0 := by
      intro a ha
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hm : RD.mix b a = 0
      · simp [hm]
      · have hb : b ∉ r.rows.rowSet := fun hb => ha ((hblk b a hm).1 hb)
        simp [hμ b hb]
    have hb := h.test_multiplier_bound (RD.mix.transpose *ᵥ μ) hsupp
    have hback : (RD.mix.transpose)⁻¹ *ᵥ (RD.mix.transpose *ᵥ μ) = μ := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdetT, Matrix.one_mulVec]
    rw [hback, congr_quad RD.mix, ← hM, quad_restrict _ _ _ hμ] at hb
    exact hb
  · intro w
    have hv : ∀ a, (∑ i, r.rows.reducer i a * w i) = (r.rows.reducer.transpose *ᵥ w) a := by
      intro a
      simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
    simp only [hv]
    rw [quad_restrict' _ _ _ hMrows, congr_quad, h.reducer_of_test, hM]
    have hinv : RD.mix⁻¹ * RD.mix = 1 := Matrix.nonsing_inv_mul _ hdet
    have e1 : RD.mix.transpose * (RD.mix⁻¹).transpose = 1 := by
      rw [← Matrix.transpose_mul, hinv, Matrix.transpose_one]
    have key : testReducerOf c RD r * RD.mix⁻¹ * (RD.mix * testMultiplierOf c RD r * RD.mix.transpose) *
        (testReducerOf c RD r * RD.mix⁻¹).transpose =
        testReducerOf c RD r * testMultiplierOf c RD r * (testReducerOf c RD r).transpose := by
      rw [Matrix.transpose_mul]
      calc testReducerOf c RD r * RD.mix⁻¹ * (RD.mix * testMultiplierOf c RD r * RD.mix.transpose) *
            ((RD.mix⁻¹).transpose * (testReducerOf c RD r).transpose)
          = testReducerOf c RD r * (RD.mix⁻¹ * RD.mix) * testMultiplierOf c RD r *
              (RD.mix.transpose * (RD.mix⁻¹).transpose) * (testReducerOf c RD r).transpose := by
            simp only [Matrix.mul_assoc]
        _ = testReducerOf c RD r * testMultiplierOf c RD r * (testReducerOf c RD r).transpose := by
            rw [hinv, e1, Matrix.mul_one, Matrix.mul_one]
    rw [key, ← congr_quad]
    by_cases hν : 0 < c.splitVisc
    · exact testReducer_bound_of_system c RD r hν h.system_reducer_bound w
    · have hz : testMultiplierOf c RD r = 0 := by
        have hs : systemScale c RD = 0 := by
          funext a
          simp [systemScale, Real.sqrt_eq_zero'.mpr (not_lt.mp hν)]
        simp [testMultiplierOf, hs]
      rw [hz]
      simp only [Matrix.zero_mulVec, dotProduct_zero]
      exact Finset.sum_nonneg fun i _ => sq_nonneg _

end Breakdown.CellCert.CellSystem
