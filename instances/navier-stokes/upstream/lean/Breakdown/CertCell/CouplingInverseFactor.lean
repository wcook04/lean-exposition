import Breakdown.CertCell.CouplingStatements

open Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Coupling

namespace InverseFactorInternal

lemma map_real_transpose {m n : Type*} (M : Matrix m n ℝ) :
    Mᵀ.map (fun t : ℝ => (t : ℂ)) = (M.map (fun t : ℝ => (t : ℂ)))ᴴ := by
  ext i j
  simp [conjTranspose_apply, transpose_apply, map_apply]

lemma map_real_mul {l m n : Type*} [Fintype m] (M : Matrix l m ℝ) (K : Matrix m n ℝ) :
    (M * K).map (fun t : ℝ => (t : ℂ)) =
      M.map (fun t : ℝ => (t : ℂ)) * K.map (fun t : ℝ => (t : ℂ)) :=
  Matrix.map_mul (f := Complex.ofRealHom)

lemma re_dot_comm {n : Type*} [Fintype n] (u w : n → ℂ) :
    (star u ⬝ᵥ w).re = (star w ⬝ᵥ u).re := by
  simp only [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma dot_conjTranspose_mulVec {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ)
    (x : n → ℂ) (w : m → ℂ) : star x ⬝ᵥ (Mᴴ *ᵥ w) = star (M *ᵥ x) ⬝ᵥ w := by
  rw [dotProduct_mulVec, star_mulVec]

lemma re_quad_nonneg_of_real {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ}
    (hM : M.PosSemidef) (v : n → ℂ) : 0 ≤ (star v ⬝ᵥ (M.map (fun t : ℝ => (t : ℂ)) *ᵥ v)).re := by
  set S := CFC.sqrt M with hSdef
  have hSS : S * S = M := CFC.sqrt_mul_sqrt_self M hM.nonneg
  have hSh : Sᵀ = S := by
    have h := (CFC.sqrt_nonneg M).posSemidef.isHermitian
    rw [← hSdef] at h
    simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using h
  have hMc : M.map (fun t : ℝ => (t : ℂ)) =
      (S.map (fun t : ℝ => (t : ℂ)))ᴴ * S.map (fun t : ℝ => (t : ℂ)) := by
    rw [← map_real_transpose, hSh, ← map_real_mul, hSS]
  rw [hMc]
  have h := (posSemidef_conjTranspose_mul_self (S.map (fun t : ℝ => (t : ℂ)))).dotProduct_mulVec_nonneg v
  exact (Complex.le_def.mp h).1

lemma cross_bound_inverse {n : Type*} [Fintype n] [DecidableEq n] {D H : Matrix n n ℂ} (hDh : Dᴴ = D)
    (hpos : ∀ v : n → ℂ, 0 ≤ (star v ⬝ᵥ (D *ᵥ v)).re) (hDH : D * H = 1) (x y : n → ℂ) :
    2 * (star y ⬝ᵥ x).re - (star y ⬝ᵥ (D *ᵥ y)).re ≤ (star x ⬝ᵥ (H *ᵥ x)).re := by
  set z := H *ᵥ x with hz
  have hDz : D *ᵥ z = x := by rw [hz, mulVec_mulVec, hDH, one_mulVec]
  have h0 := hpos (y - z)
  have hswap : (star z ⬝ᵥ (D *ᵥ y)).re = (star y ⬝ᵥ x).re := by
    rw [← hDh, dot_conjTranspose_mulVec, hDz, re_dot_comm]
  have hzx : (star z ⬝ᵥ x).re = (star x ⬝ᵥ z).re := re_dot_comm z x
  rw [star_sub, mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hDz] at h0
  simp only [Complex.sub_re] at h0
  linarith

lemma real_smul_dot_re {n : Type*} [Fintype n] (t : ℝ) (u w : n → ℂ) :
    (star ((t : ℂ) • u) ⬝ᵥ w).re = t * (star u ⬝ᵥ w).re := by
  rw [star_smul, Complex.star_def, Complex.conj_ofReal, smul_dotProduct, smul_eq_mul,
    Complex.re_ofReal_mul]

lemma real_smul_quad_re {n : Type*} [Fintype n] (t : ℝ) (D : Matrix n n ℂ) (u : n → ℂ) :
    (star ((t : ℂ) • u) ⬝ᵥ (D *ᵥ ((t : ℂ) • u))).re = t ^ 2 * (star u ⬝ᵥ (D *ᵥ u)).re := by
  rw [real_smul_dot_re, mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  ring

end InverseFactorInternal

open InverseFactorInternal in
theorem inverseFormFactor : InverseFormFactorHolds := by
  intro N p G L ε hG hε hC x
  set f : ℝ → ℂ := fun t => (t : ℂ) with hf
  set Gc := G.map f with hGc
  set Hc := G⁻¹.map f with hHc
  set Lc := L.map f with hLc
  have hGH : Gc * Hc = 1 := by
    rw [hGc, hHc, hf, ← map_real_mul,
      mul_nonsing_inv G ((isUnit_iff_isUnit_det G).mp hG.isUnit)]
    simp
  have hGh : Gcᴴ = Gc := by
    rw [hGc, hf, ← map_real_transpose]
    congr 1
    simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hG.isHermitian
  have hGpos : ∀ v : Fin N → ℂ, 0 ≤ (star v ⬝ᵥ (Gc *ᵥ v)).re :=
    re_quad_nonneg_of_real hG.posSemidef
  set v := Lc *ᵥ x with hv
  set u := Lcᴴ *ᵥ v with hu
  set a := (star v ⬝ᵥ v).re with ha
  set Q := (star v ⬝ᵥ ((Lc * Gc * Lcᴴ) *ᵥ v)).re with hQ
  have hLL : (Lᵀ * L).map f = Lcᴴ * Lc := by
    rw [hf, map_real_mul, map_real_transpose]
  have hA : realQuadForm (Lᵀ * L) x = a := by
    unfold realQuadForm
    rw [← hf, hLL, ← mulVec_mulVec, dot_conjTranspose_mulVec]
  have hB : realQuadForm G⁻¹ x = (star x ⬝ᵥ (Hc *ᵥ x)).re := rfl
  have hux : (star u ⬝ᵥ x).re = a := by
    rw [re_dot_comm, hu, dot_conjTranspose_mulVec]
  have huGu : (star u ⬝ᵥ (Gc *ᵥ u)).re = Q := by
    rw [hQ, re_dot_comm, hu, dot_conjTranspose_mulVec, re_dot_comm, ← mulVec_mulVec,
      ← mulVec_mulVec]
  have hCc : (((1 + ε) • (1 : Matrix (Fin p) (Fin p) ℝ) - L * G * Lᵀ).map f) =
      ((1 + ε : ℝ) : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) - Lc * Gc * Lcᴴ := by
    rw [← map_real_transpose, ← map_real_mul, ← map_real_mul]
    ext i j
    by_cases h : i = j <;> simp [h, hf]
  have hQa : Q ≤ (1 + ε) * a := by
    have h := re_quad_nonneg_of_real hC v
    rw [hCc, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
      smul_eq_mul, Complex.sub_re, Complex.re_ofReal_mul] at h
    linarith
  have hε1 : 0 < 1 + ε := by linarith
  set t : ℝ := (1 + ε)⁻¹ with ht
  have ht0 : 0 < t := inv_pos.mpr hε1
  have htt : t * (1 + ε) = 1 := inv_mul_cancel₀ hε1.ne'
  have hkey := cross_bound_inverse hGh hGpos hGH x ((t : ℂ) • u)
  rw [real_smul_dot_re, real_smul_quad_re, hux, huGu] at hkey
  have ha0 : 0 ≤ a := by
    rw [ha, re_dot_comm]
    exact (re_quad_nonneg_of_real (PosSemidef.one (n := Fin p) (R := ℝ)) v).trans_eq
      (by simp)
  have hQt : t ^ 2 * Q ≤ t * a := by
    have := mul_le_mul_of_nonneg_left hQa (sq_nonneg t)
    calc t ^ 2 * Q ≤ t ^ 2 * ((1 + ε) * a) := this
      _ = (t * (1 + ε)) * (t * a) := by ring
      _ = t * a := by rw [htt, one_mul]
  rw [hA, hB, div_eq_mul_inv, mul_comm, ← ht]
  linarith

end Coupling

end CertCell

end Breakdown
