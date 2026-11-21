import Breakdown.CertCell.AssemblyStatements

open MeasureTheory Matrix
open scoped ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

open Coupling

theorem quadForm_submatrix_equiv {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m m ℂ) (e : n ≃ m)
    (x : n → ℂ) : quadForm (A.submatrix e e) x = quadForm A (x ∘ e.symm) := by
  unfold quadForm
  rw [submatrix_mulVec_equiv, ← comp_equiv_symm_dotProduct]
  rfl

theorem quadForm_blockDiagonal {o : Type*} [Fintype o] [DecidableEq o] {n : o → Type*}
    [∀ i, Fintype (n i)] (N : ∀ i, Matrix (n i) (n i) ℂ) (x : (Σ i, n i) → ℂ) :
    quadForm (blockDiagonal' N) x = ∑ i, quadForm (N i) (fun j => x ⟨i, j⟩) := by
  unfold quadForm
  rw [← Complex.re_sum]
  congr 1
  have hmv : ∀ s : Σ i, n i, (blockDiagonal' N *ᵥ x) s = (N s.1 *ᵥ fun j => x ⟨s.1, j⟩) s.2 := by
    rintro ⟨i, a⟩
    simp only [mulVec, dotProduct, Fintype.sum_sigma]
    rw [Fintype.sum_eq_single i]
    · exact Finset.sum_congr rfl fun b _ => by rw [blockDiagonal'_apply_eq]
    · intro i' hi'
      exact Finset.sum_eq_zero fun b _ => by rw [blockDiagonal'_apply_ne N a b (Ne.symm hi'), zero_mul]
  simp only [dotProduct, Fintype.sum_sigma, hmv, Pi.star_apply]

theorem quadForm_smul (t : ℝ) {n : Type*} [Fintype n] (A : Matrix n n ℂ) (x : n → ℂ) :
    quadForm ((t : ℂ) • A) x = t * quadForm A x := by
  unfold quadForm
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]

end Internal

open Coupling _root_.Breakdown.CertCell.Assembly.Internal

theorem rowShareStacked_holds : RowShareStackedHolds := by
  intro k C nE nM D R A _hReg _hTF tauMax hT hC K F
  classical
  set B := A.blocks K with hB
  let T := D.mesh.tested K
  let n : T → Type := fun ι => Fin (D.rows.testCount K ι.1)
  let τ : T → ℝ := fun ι => D.rows.testWeight K ι.1
  have hτ : ∀ ι : T, 0 < τ ι := fun ι => hT.weight_pos K ι.1 ι.2
  let M : ∀ ι : T, Matrix (n ι) (n ι) ℂ := fun ι => D.rows.testBlockMatrix D.mesh.box K ι.1
  have hM : ∀ ι : T, (M ι).PosDef := fun ι => hT.block_posDef K ι.1 ι.2
  let Γ : ℤ × ℤ → ℕ → ℕ → ℂ := fun ι i j => ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ c : Fin 3,
    (D.rows.testField K ι j c).eval (D.mesh.box K) p * starRingEnd ℂ ((D.rows.testField K ι i c).eval (D.mesh.box K) p)
  have hMΓ : ∀ ι : T, ∀ i j : n ι, M ι i j = Γ ι.1 i.1 j.1 := fun ι i j => rfl
  let f : Fin B.rowCount → Σ ι : T, n ι := fun i =>
    ⟨⟨B.rowLabel i, hC.label_tested K i⟩, ⟨B.rowTest i, hC.test_range K i⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i i' h
      have h1 : B.rowLabel i = B.rowLabel i' := congrArg (fun s : Σ ι : T, n ι => s.1.1) h
      have h2 : B.rowTest i = B.rowTest i' := congrArg (fun s : Σ ι : T, n ι => (s.2 : ℕ)) h
      exact hC.rows_injective K i i' h1 h2
    · rintro ⟨ι, j⟩
      obtain ⟨i, hi1, hi2⟩ := hC.rows_onto K ι.1 ι.2 j.1 j.2
      refine ⟨i, ?_⟩
      obtain ⟨ι, hι⟩ := ι
      obtain ⟨j, hj⟩ := j
      simp only at hi1 hi2
      subst hi1 hi2
      rfl
  let e : Fin B.rowCount ≃ Σ ι : T, n ι := Equiv.ofBijective f hf
  have hdiag : ∀ a b : Σ ι : T, n ι,
      blockDiagonal' (fun ι => ((τ ι : ℂ)⁻¹) • M ι) a b =
        if a.1.1 = b.1.1 then ((τ a.1 : ℂ)⁻¹) * Γ a.1.1 a.2.1 b.2.1 else 0 := by
    rintro ⟨a, x⟩ ⟨b, y⟩
    by_cases h : a = b
    · subst h
      rw [blockDiagonal'_apply_eq, if_pos rfl, Matrix.smul_apply, smul_eq_mul, hMΓ]
    · rw [blockDiagonal'_apply_ne _ _ _ h, if_neg (fun h' => h (Subtype.ext h'))]
  have hW : rowBaseWeight D K B = (blockDiagonal' fun ι => ((τ ι : ℂ)⁻¹) • M ι).submatrix e e := by
    ext i i'
    rw [submatrix_apply, hdiag]
    change (if B.rowLabel i = B.rowLabel i' then Γ (B.rowLabel i) (B.rowTest i) (B.rowTest i') else 0)
        / (D.rows.testWeight K (B.rowLabel i) : ℂ)
      = if B.rowLabel i = B.rowLabel i' then
          ((D.rows.testWeight K (B.rowLabel i) : ℂ)⁻¹) * Γ (B.rowLabel i) (B.rowTest i) (B.rowTest i') else 0
    split_ifs
    · rw [div_eq_inv_mul]
    · rw [zero_div]
  have hblock : (fun ι => (((τ ι : ℂ)⁻¹) • M ι) * ((τ ι : ℂ) • (M ι)⁻¹)) = fun ι => 1 := by
    funext ι
    have hu : IsUnit (M ι).det := (isUnit_iff_isUnit_det _).mp (hM ι).isUnit
    have hτc : (τ ι : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hτ ι).ne'
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hτc, one_smul, mul_nonsing_inv _ hu]
  have hinv : (blockDiagonal' fun ι => ((τ ι : ℂ)⁻¹) • M ι)⁻¹ = blockDiagonal' fun ι => (τ ι : ℂ) • (M ι)⁻¹ := by
    apply inv_eq_right_inv
    rw [← blockDiagonal'_mul, hblock]
    exact blockDiagonal'_one
  have hmom : ∀ i, rowMoment D K B F i = D.rows.cellMoment D.mesh.box D.azimuthOrder K (e i).1.1 F (e i).2 :=
    fun i => rfl
  unfold inverseWeightedSq CellCalculus.rowShare
  rw [hW, inv_submatrix_equiv, hinv, quadForm_submatrix_equiv, quadForm_blockDiagonal,
    ← Finset.sum_coe_sort (D.mesh.tested K)]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [quadForm_smul]
  congr 2
  funext j
  change _ = rowMoment D K B F (e.symm ⟨ι, j⟩)
  rw [hmom, e.apply_symm_apply]

end Assembly

end CertCell

end Breakdown
