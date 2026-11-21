import Breakdown.CertCell.CouplingStatements

open Matrix
open scoped ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Coupling

namespace InverseCreditInternal

lemma real_map_conjTranspose_eq {n : Type*} (M : Matrix n n ℝ) (hM : Mᵀ = M) :
    (M.map (fun s : ℝ => (s : ℂ)))ᴴ = M.map (fun s : ℝ => (s : ℂ)) := by
  ext i j
  have h := congrFun (congrFun hM j) i
  simp only [transpose_apply] at h
  simp [conjTranspose_apply, map_apply, h]

lemma real_map_mul_inv_eq_one {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ)
    (hM : IsUnit M.det) :
    M.map (fun s : ℝ => (s : ℂ)) * M⁻¹.map (fun s : ℝ => (s : ℂ)) = 1 := by
  have h : (M * M⁻¹).map (fun s : ℝ => (s : ℂ)) =
      M.map (fun s : ℝ => (s : ℂ)) * M⁻¹.map (fun s : ℝ => (s : ℂ)) :=
    Matrix.map_mul (f := Complex.ofRealHom)
  rw [← h, mul_nonsing_inv M hM]
  ext i j
  by_cases h : i = j <;> simp [h, one_apply]

end InverseCreditInternal

open InverseCreditInternal in
theorem inverseFormCredit : InverseFormCreditHolds := by
  intro N G t A hG hA hbound
  set Gc := G.map (fun s : ℝ => (s : ℂ)) with hGc
  set Hc := G⁻¹.map (fun s : ℝ => (s : ℂ)) with hHc
  have hdet : IsUnit G.det := (isUnit_iff_isUnit_det G).mp hG.isUnit
  have hsymm : (G⁻¹)ᵀ = G⁻¹ := by
    have h := hG.isHermitian.inv
    simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using h
  have hHh : Hcᴴ = Hc := real_map_conjTranspose_eq G⁻¹ hsymm
  set c := Hc *ᵥ t with hc
  have hGcc : Gc *ᵥ c = t := by
    rw [hc, mulVec_mulVec, hGc, hHc, real_map_mul_inv_eq_one G hdet, one_mulVec]
  have hct : star c ⬝ᵥ t = star t ⬝ᵥ (Hc *ᵥ t) := by
    rw [hc, star_mulVec, ← dotProduct_mulVec, hHh]
  set τ := realQuadForm G⁻¹ t with hτ
  have hτre : (star c ⬝ᵥ t).re = τ := by
    rw [hct, hτ]
    rfl
  have hquad : realQuadForm G c = τ := by
    show (star c ⬝ᵥ (Gc *ᵥ c)).re = τ
    rw [hGcc, hτre]
  have hsq : τ ^ 2 ≤ ‖star c ⬝ᵥ t‖ ^ 2 := by
    rw [← hτre]
    have h1 : |(star c ⬝ᵥ t).re| ≤ ‖star c ⬝ᵥ t‖ := Complex.abs_re_le_norm _
    have h2 := sq_le_sq' (neg_le_of_abs_le h1) (le_of_abs_le h1)
    simpa using h2
  have hmain : τ ^ 2 ≤ A * τ := by
    have := hbound c
    rw [hquad] at this
    linarith
  rcases le_or_gt τ 0 with hle | hpos
  · linarith
  · nlinarith
