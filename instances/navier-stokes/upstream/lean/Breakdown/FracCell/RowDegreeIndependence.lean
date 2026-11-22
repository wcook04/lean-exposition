import Breakdown.FracCell.CellSystemDefs
import Breakdown.FracCell.MeshRowFar
import Breakdown.FracCell.GivenModelCover

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellSystem

open SteadyCert Assembly Reduction GivenFields GivenModel Exterior Spectral CellAnalysis CellCoordinates CellFormula
open GivenModel.ModeCoverInternal

theorem multiplierLHS_rowDegree {k N : ℕ} (c : FracCellData k N) {M : CellMesh} {slots : ℕ}
    (r : CellEntry M N k slots) (E : ℕ) (hK : IsCellBox r.box) (hB : IsCellBases r.box r.bases)
    (hE : IsRowPolynomial c r.box r.scalars r.rows E)
    (hD : IsRowPolynomial c r.box r.scalars r.rows r.rowDegree) (μ : Fin N → ℝ) :
    multiplierLHS c { r with rowDegree := E } μ = multiplierLHS c r μ := by
  have h : CellScalars.rowSquareUpTo c r.box r.scalars r.bases r.rows E μ =
      CellScalars.rowSquareUpTo c r.box r.scalars r.bases r.rows r.rowDegree μ :=
    (rowFarFinite_holds c r.box r.scalars r.bases r.rows E hK hB hE μ).symm.trans
      (rowFarFinite_holds c r.box r.scalars r.bases r.rows r.rowDegree hK hB hD μ)
  unfold multiplierLHS
  exact congrArg (fun t => _ + t / (1 - r.rows.farShare)) h

theorem testMultiplierBound_of_systemDegree {k N : ℕ} (c : FracCellData k N) {M : CellMesh} (RD : RowData M N)
    {slots : ℕ} (r : CellEntry M N k slots) (E : ℕ) (hK : IsCellBox r.box) (hB : IsCellBases r.box r.bases)
    (hE : IsRowPolynomial c r.box r.scalars r.rows E)
    (hD : IsRowPolynomial c r.box r.scalars r.rows r.rowDegree)
    (hsystem : ∀ μ : Fin N → ℝ, (∀ a ∉ r.rows.rowSet, μ a = 0) →
      multiplierLHS c { r with rowDegree := E } ((RD.mix.transpose)⁻¹ *ᵥ μ) ≤ μ ⬝ᵥ (testMultiplierOf c RD r *ᵥ μ)) :
    ∀ μ : Fin N → ℝ, (∀ a ∉ r.rows.rowSet, μ a = 0) →
      multiplierLHS c r ((RD.mix.transpose)⁻¹ *ᵥ μ) ≤ μ ⬝ᵥ (testMultiplierOf c RD r *ᵥ μ) := by
  intro μ hμ
  rw [← multiplierLHS_rowDegree c r E hK hB hE hD]
  exact hsystem μ hμ

namespace RowDegreeInternal

theorem evalPoly_mem_of_coef_vanish {d e : ℕ} (P : CellPoly d)
    (h : ∀ j l : Fin (d + 1), e < (j : ℕ) ∨ e < (l : ℕ) → P j l = 0) :
    (fun p : ℝ × ℝ => evalPoly P p.1 p.2) ∈ polyFn e e := by
  show (fun p : ℝ × ℝ => ∑ j ∈ Finset.univ, ∑ l ∈ Finset.univ,
    P j l * ((p.1 : ℂ) ^ (j : ℕ)) * ((p.2 : ℂ) ^ (l : ℕ))) ∈ polyFn e e
  refine poly_sum' _ (fun j _ => poly_sum' _ (fun l _ => ?_))
  by_cases hjl : (j : ℕ) ≤ e ∧ (l : ℕ) ≤ e
  · refine poly_congr' (poly_smul' (P j l) (poly_mon' hjl.1 hjl.2)) (fun p => ?_)
    ring
  · have h0 : P j l = 0 := h j l (by omega)
    exact poly_congr' poly_zero' (fun p => by rw [h0, zero_mul, zero_mul])

theorem interiorPoly_mem_of_cell_coef (M : CellMesh) (K₀ : Fin M.cellCount) {d J e : ℕ}
    (E : Fin M.cellCount → Fin (J + 1) → CellPoly d) (n : ℤ)
    (h : ∀ (β : Fin (J + 1)) (j l : Fin (d + 1)), e < (j : ℕ) ∨ e < (l : ℕ) → E K₀ β j l = 0) :
    interiorPoly M K₀ E n ∈ polyFn e e := by
  have hq : ∀ q : Fin M.cellCount × Fin (J + 1),
      (fun p : ℝ × ℝ => if q.1 = K₀ then wt q.2 * evalPoly (E q.1 q.2) p.1 p.2 else 0) ∈ polyFn e e := by
    intro q
    by_cases hK : q.1 = K₀
    · refine poly_congr' (poly_smul' (wt q.2) (evalPoly_mem_of_coef_vanish (E K₀ q.2) (h q.2))) (fun p => ?_)
      simp only [hK, if_true]
    · exact poly_congr' poly_zero' (fun p => by simp only [hK, if_false])
  unfold interiorPoly
  exact poly_smul' _ (poly_sum' _ (fun q _ => poly_add' (poly_ite' _ (hq q)) (poly_ite' _ (poly_conj' (hq q)))))

end RowDegreeInternal

open RowDegreeInternal

theorem rowPolynomial_of_cellDegree {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (D : ModelData M k)
    (RD : RowData M N) (hM : IsCellMesh M) (hI : IsModelInstance c M D) (K₀ : Fin M.cellCount)
    (R : CellRows N slots k) (hRI : IsRowsInstance c M RD K₀ R) (hm : 0 < c.order) (S : CellScalars) (d E : ℕ)
    (hd : ∀ (β : Fin (D.harmonicCount + 1)) (a : Fin 3) (j l : Fin (D.degree + 1)), d < (j : ℕ) ∨ d < (l : ℕ) →
      D.velocity K₀ β a j l = 0 ∧ D.curl K₀ β a j l = 0)
    (hdeg : RD.degree + d + 2 ≤ E) :
    IsRowPolynomial c (M.box K₀) S R E := by
  have hB := hM.boxes K₀
  have hU : ∀ a n (p : ℝ × ℝ), p ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂ ×ˢ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂ →
      CellScalars.rowMode c a n p = fun j => rowPoly RD K₀ a n j p := by
    intro a n p hp
    funext j
    unfold CellScalars.rowMode
    rw [hRI.row_eq]
    exact row_interior M hM RD K₀ c.order hm a n j p hp.1 hp.2
  have hV : ∀ n n' (p : ℝ × ℝ), p ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂ ×ˢ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂ →
      modeVec c.order (n - n') c.modelVelocity p.1 p.2 =
        fun j => interiorPoly M K₀ (fun K β => D.velocity K β j) (n - n') p := by
    intro n n' p hp
    funext j
    rw [hI.velocity_eq]
    exact (vec_interior M hM K₀ c.order hm (n - n') D.velocity j p hp.1 hp.2).1
  have hW : ∀ n n' (p : ℝ × ℝ), p ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂ ×ˢ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂ →
      modeVec c.order (n - n') c.modelCurl p.1 p.2 =
        fun j => interiorPoly M K₀ (fun K β => D.curl K β j) (n - n') p := by
    intro n n' p hp
    funext j
    rw [hI.curl_eq]
    exact (vec_interior M hM K₀ c.order hm (n - n') D.curl j p hp.1 hp.2).2
  have hPv : ∀ (j : Fin 3) (n : ℤ), interiorPoly M K₀ (fun K β => D.velocity K β j) n ∈ polyFn d d :=
    fun j n => interiorPoly_mem_of_cell_coef M K₀ _ n (fun β a b hab => (hd β j a b hab).1)
  have hPc : ∀ (j : Fin 3) (n : ℤ), interiorPoly M K₀ (fun K β => D.curl K β j) n ∈ polyFn d d :=
    fun j n => interiorPoly_mem_of_cell_coef M K₀ _ n (fun β a b hab => (hd β j a b hab).2)
  have hYs : ∀ a n' (i l : Fin 3), (fun p => rHatPoly (M.box K₀) p * ∑ n ∈ R.rowModes,
      curlAdj (crossC (conjVec3 (fun j => interiorPoly M K₀ (fun K β => D.velocity K β j) (n - n') p))
        (fun j => rowPoly RD K₀ a n j p)) i l) ∈ polyFn E E := by
    intro a n' i l
    refine poly_mono' (d := 1 + (d + RD.degree)) (d' := 0 + (d + RD.degree)) (by omega) (by omega)
      (poly_mul' (rHatPoly_mem _) (poly_sum' _ (fun n _ => ?_)))
    exact curlAdj_poly (fun i' p => crossC (fun j => (starRingEnd ℂ) (interiorPoly M K₀ (fun K β => D.velocity K β j) (n - n') p))
        (fun j => rowPoly RD K₀ a n j p) i')
      (fun i' => cross_poly _ _ (fun j => poly_conj' (hPv j _)) (fun j => rowPoly_mem RD K₀ a n j) i') i l
  have hYv : ∀ a n' (i : Fin 3), (fun p => rHatPoly (M.box K₀) p * ∑ n ∈ R.rowModes,
      crossC (fun j => rowPoly RD K₀ a n j p)
        (conjVec3 (fun j => interiorPoly M K₀ (fun K β => D.curl K β j) (n - n') p)) i) ∈
        polyFn (1 + (RD.degree + d)) (1 + (RD.degree + d)) := by
    intro a n' i
    refine poly_mono' (d := 1 + (RD.degree + d)) (d' := 0 + (RD.degree + d)) le_rfl (by omega)
      (poly_mul' (rHatPoly_mem _) (poly_sum' _ (fun n _ => ?_)))
    exact cross_poly (fun j p => rowPoly RD K₀ a n j p)
      (fun j p => (starRingEnd ℂ) (interiorPoly M K₀ (fun K β => D.curl K β j) (n - n') p))
      (fun j => rowPoly_mem RD K₀ a n j) (fun j => poly_conj' (hPc j _)) i
  refine ⟨fun a _ n' _ i q => ?_, fun a _ n' _ i => ?_⟩
  · refine ⟨fun p => if n' ∈ S.resolved then
        rHatPoly (M.box K₀) p * ∑ n ∈ R.rowModes,
          curlAdj (crossC (conjVec3 (fun j => interiorPoly M K₀ (fun K β => D.velocity K β j) (n - n') p))
            (fun j => rowPoly RD K₀ a n j p)) i q
      else (rHatPoly (M.box K₀) p * ∑ n ∈ R.rowModes,
          curlAdj (crossC (conjVec3 (fun j => interiorPoly M K₀ (fun K β => D.velocity K β j) (n - n') p))
            (fun j => rowPoly RD K₀ a n j p)) i q +
        if q = 1 then (p.1 : ℂ) * turnAdjInv (azimuth c.order n') (fun i' => rHatPoly (M.box K₀) p *
          ∑ n ∈ R.rowModes, crossC (fun j => rowPoly RD K₀ a n j p)
            (conjVec3 (fun j => interiorPoly M K₀ (fun K β => D.curl K β j) (n - n') p)) i') i else 0), ?_, ?_⟩
    · by_cases hn : n' ∈ S.resolved
      · simp only [hn, if_true]
        exact hYs a n' i q
      · simp only [hn, if_false]
        refine poly_add' (hYs a n' i q) ?_
        by_cases hq : q = 1
        · simp only [hq, if_true]
          exact poly_mono' (d := 1 + (1 + (RD.degree + d))) (d' := 0 + (1 + (RD.degree + d))) (by omega) (by omega)
            (mulFst_poly (turn_poly _ _ (fun i' => hYv a n' i') i))
        · simp only [hq, if_false]
          exact poly_zero'
    · intro p hp _
      unfold CellScalars.rowCouplingFolded CellScalars.rowCouplingStrain CellScalars.rowCouplingVelocity foldVelocity
      simp only [hU a _ p hp, hV _ n' p hp, hW _ n' p hp, rHat_interior _ hB p hp.1]
      by_cases hn : n' ∈ S.resolved <;> by_cases hq : q = 1 <;> simp only [hn, hq, if_true, if_false, add_zero]
  · refine ⟨fun p => rHatPoly (M.box K₀) p * ∑ n ∈ R.rowModes, crossC (fun j => rowPoly RD K₀ a n j p)
        (conjVec3 (fun j => interiorPoly M K₀ (fun K β => D.curl K β j) (n - n') p)) i,
      poly_mono' (by omega) (by omega) (hYv a n' i), fun p hp _ => ?_⟩
    unfold CellScalars.rowCouplingVelocity
    simp only [hU a _ p hp, hW _ n' p hp, rHat_interior _ hB p hp.1]

theorem testMultiplierBound_of_cellDegree {k N : ℕ} (c : FracCellData k N) {M : CellMesh} (D : ModelData M k)
    (RD : RowData M N) (hM : IsCellMesh M) (hI : IsModelInstance c M D) (hm : 0 < c.order) {slots : ℕ}
    (r : CellEntry M N k slots) (hRI : IsRowsInstance c M RD r.meshCell r.rows) (d E : ℕ)
    (hd : ∀ (β : Fin (D.harmonicCount + 1)) (a : Fin 3) (j l : Fin (D.degree + 1)), d < (j : ℕ) ∨ d < (l : ℕ) →
      D.velocity r.meshCell β a j l = 0 ∧ D.curl r.meshCell β a j l = 0)
    (hdeg : RD.degree + d + 2 ≤ E) (hB : IsCellBases r.box r.bases)
    (hD : IsRowPolynomial c r.box r.scalars r.rows r.rowDegree)
    (hsystem : ∀ μ : Fin N → ℝ, (∀ a ∉ r.rows.rowSet, μ a = 0) →
      multiplierLHS c { r with rowDegree := E } ((RD.mix.transpose)⁻¹ *ᵥ μ) ≤ μ ⬝ᵥ (testMultiplierOf c RD r *ᵥ μ)) :
    ∀ μ : Fin N → ℝ, (∀ a ∉ r.rows.rowSet, μ a = 0) →
      multiplierLHS c r ((RD.mix.transpose)⁻¹ *ᵥ μ) ≤ μ ⬝ᵥ (testMultiplierOf c RD r *ᵥ μ) :=
  testMultiplierBound_of_systemDegree c RD r E (hM.boxes r.meshCell) hB
    (rowPolynomial_of_cellDegree c M D RD hM hI r.meshCell r.rows hRI hm r.scalars d E hd hdeg) hD hsystem

end CellSystem

end CellCert

end Breakdown
