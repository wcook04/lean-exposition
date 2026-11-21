import Breakdown.CertCell.AssemblyPotentialSharpSymbolForm
import Breakdown.CertCell.AssemblyPotentialSharpFrame
import Breakdown.CertCell.AssemblyPotentialModelTorusMeanFacts

open scoped ComplexConjugate
open Filter Topology Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

namespace Sharp

open Bridge Bridge.Internal.MeanStretch Coercive.StretchInternal Coercive.Internal.ModeRotation

def slotL : (Fin 12 → ℂ) →ₗ[ℂ] (Slot → ℂ) where
  toFun U := Sum.elim (velOf U) (gradOf U)
  map_add' U U' := by
    funext k
    rcases k with i | ij <;> rfl
  map_smul' c U := by
    funext k
    rcases k with i | ij <;> rfl

def slotC (U : Fin 12 → ℂ) : Slot → ℂ := fun k => conj (slotL U k)

theorem slotC_sum (U : Fin 12 → ℂ) : slotC U = ∑ i, conj (U i) • slotL (Pi.single i 1) := by
  have hU : U = ∑ i, U i • (Pi.single i 1 : Fin 12 → ℂ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  funext k
  unfold slotC
  conv_lhs => rw [hU]
  rw [map_sum, Finset.sum_apply, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
  congr 1
  rcases k with a | ⟨a, b⟩ <;> simp [slotL, velOf, gradOf, Pi.single_apply]

theorem slotL_sum (U : Fin 12 → ℂ) : slotL U = ∑ j, U j • slotL (Pi.single j 1) := by
  have hU : U = ∑ j, U j • (Pi.single j 1 : Fin 12 → ℂ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hU]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]

def tripleMatrix (gW : Fin 3 × Fin 3 → ℂ) (hW : Fin 3 × Fin 3 × Fin 3 → ℂ) : Matrix (Fin 12) (Fin 12) ℂ :=
  fun i j => (pairForm gW hW (slotL (Pi.single j 1)) (slotL (Pi.single i 1))
    + pairForm gW hW (slotL (Pi.single i 1)) (slotL (Pi.single j 1))) / 2

theorem sesq12_tripleMatrix (gW : Fin 3 × Fin 3 → ℂ) (hW : Fin 3 × Fin 3 × Fin 3 → ℂ) (U U' : Fin 12 → ℂ) :
    sesq12 (tripleMatrix gW hW) U U' = (pairForm gW hW (slotL U') (slotC U) + pairForm gW hW (slotC U) (slotL U')) / 2 := by
  have e1 : pairForm gW hW (slotL U') (slotC U) = pairLinear gW hW (slotL U') (slotC U) := rfl
  have e2 : pairForm gW hW (slotC U) (slotL U') = pairLinear gW hW (slotC U) (slotL U') := rfl
  rw [e1, e2, slotC_sum, slotL_sum U']
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have hA : (∑ x, conj (U x) * ∑ y, U' y * pairLinear gW hW (slotL (Pi.single y 1)) (slotL (Pi.single x 1)))
      = ∑ i, ∑ j, conj (U i) * U' j * pairForm gW hW (slotL (Pi.single j 1)) (slotL (Pi.single i 1)) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : pairLinear gW hW (slotL (Pi.single j 1)) (slotL (Pi.single i 1))
        = pairForm gW hW (slotL (Pi.single j 1)) (slotL (Pi.single i 1)) := rfl
    rw [this]; ring
  have hB : (∑ x, U' x * ∑ y, conj (U y) * pairLinear gW hW (slotL (Pi.single y 1)) (slotL (Pi.single x 1)))
      = ∑ i, ∑ j, conj (U i) * U' j * pairForm gW hW (slotL (Pi.single i 1)) (slotL (Pi.single j 1)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : pairLinear gW hW (slotL (Pi.single i 1)) (slotL (Pi.single j 1))
        = pairForm gW hW (slotL (Pi.single i 1)) (slotL (Pi.single j 1)) := rfl
    rw [this]; ring
  rw [hA, hB, ← Finset.sum_add_distrib, Finset.sum_div]
  unfold sesq12 tripleMatrix
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sesq12_add (A B : Matrix (Fin 12) (Fin 12) ℂ) (U U' : Fin 12 → ℂ) :
    sesq12 (A + B) U U' = sesq12 A U U' + sesq12 B U U' := by
  unfold sesq12
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.add_apply]
  ring

theorem sesq12_smul (c : ℂ) (A : Matrix (Fin 12) (Fin 12) ℂ) (U U' : Fin 12 → ℂ) :
    sesq12 (c • A) U U' = c * sesq12 A U U' := by
  unfold sesq12
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

theorem sesq12_symbol (B : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (gW : ℤ × ℤ → Fin 3 × Fin 3 → ℂ)
    (hW : ℤ × ℤ → Fin 3 × Fin 3 × Fin 3 → ℂ) (U : Fin 12 → ℂ) :
    sesq12 (∑ β ∈ B, c β • tripleMatrix (gW β) (hW β)) U U
      = (pairForm (∑ β ∈ B, c β • gW β) (∑ β ∈ B, c β • hW β) (slotL U) (slotC U)
        + pairForm (∑ β ∈ B, c β • gW β) (∑ β ∈ B, c β • hW β) (slotC U) (slotL U)) / 2 := by
  rw [sesq12_smul_sum]
  simp only [sesq12_tripleMatrix]
  rw [pairForm_sum_W, pairForm_sum_W]
  simp only [pairForm_smul_W]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

def curlVecK (k : Fin 3) : Fin 12 → ℂ := fun j => curlOfGrad (gradOf (Pi.single j 1)) k

theorem curlOfGrad_gradOf (U : Fin 12 → ℂ) (k : Fin 3) :
    curlOfGrad (gradOf U) k = ∑ j, U j * curlVecK k j := by
  have hU : U = ∑ j, U j • (Pi.single j 1 : Fin 12 → ℂ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hlin : ∀ (V : Fin 12 → ℂ), curlOfGrad (gradOf V) k
      = ∑ a : Fin 3, ∑ b : Fin 3, (alternatingSymbol k a b : ℂ) * V ⟨3 * b.val + a.val, by omega⟩ := by
    intro V; rfl
  rw [hlin]
  simp only [curlVecK, hlin, Finset.mul_sum]
  symm
  calc (∑ j : Fin 12, ∑ a : Fin 3, ∑ b : Fin 3,
        U j * ((alternatingSymbol k a b : ℂ) * (Pi.single j (1 : ℂ) : Fin 12 → ℂ) ⟨3 * b.val + a.val, by omega⟩))
      = ∑ a : Fin 3, ∑ j : Fin 12, ∑ b : Fin 3,
        U j * ((alternatingSymbol k a b : ℂ) * (Pi.single j (1 : ℂ) : Fin 12 → ℂ) ⟨3 * b.val + a.val, by omega⟩) :=
        Finset.sum_comm
    _ = ∑ a : Fin 3, ∑ b : Fin 3, ∑ j : Fin 12,
        U j * ((alternatingSymbol k a b : ℂ) * (Pi.single j (1 : ℂ) : Fin 12 → ℂ) ⟨3 * b.val + a.val, by omega⟩) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_eq_single (⟨3 * b.val + a.val, by omega⟩ : Fin 12)]
      · simp; ring
      · intro j _ hj
        simp [Ne.symm hj]
      · simp

def rankOne (c : Fin 12 → ℂ) : Matrix (Fin 12) (Fin 12) ℂ := Matrix.of fun i j => conj (c i) * c j

theorem re_sesq12_rankOne (c U : Fin 12 → ℂ) : (sesq12 (rankOne c) U U).re = ‖∑ j, U j * c j‖ ^ 2 := by
  have h : sesq12 (rankOne c) U U = conj (∑ j, U j * c j) * (∑ j, U j * c j) := by
    rw [map_sum, Finset.sum_mul_sum]
    unfold sesq12 rankOne
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.of_apply, map_mul]
    ring
  rw [h, Complex.conj_mul']
  norm_cast

def curlPairMatrix : Matrix (Fin 12) (Fin 12) ℂ := ∑ k : Fin 3, rankOne (curlVecK k)

def gradDiag : Matrix (Fin 12) (Fin 12) ℂ := Matrix.diagonal fun i => if i.val < 9 then 1 else 0

def velDiag : Matrix (Fin 12) (Fin 12) ℂ := Matrix.diagonal fun i => if i.val < 9 then 0 else 1

theorem re_sesq12_curlPairMatrix (U : Fin 12 → ℂ) :
    (sesq12 curlPairMatrix U U).re = cnormSq (curlOfGrad (gradOf U)) := by
  have h : sesq12 curlPairMatrix U U = ∑ k : Fin 3, sesq12 (rankOne (curlVecK k)) U U := by
    unfold curlPairMatrix
    rw [sesq12_eq, Matrix.sum_mulVec, dotProduct_sum]
    simp only [sesq12_eq]
  rw [h, Complex.re_sum]
  unfold cnormSq
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [re_sesq12_rankOne, curlOfGrad_gradOf]

theorem re_sesq12_diagonal (d : Fin 12 → ℝ) (U : Fin 12 → ℂ) :
    (sesq12 (Matrix.diagonal fun i => ((d i : ℝ) : ℂ)) U U).re = ∑ i, d i * ‖U i‖ ^ 2 := by
  unfold sesq12
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq, mul_comm (conj (U i)), mul_assoc, Complex.conj_mul', Complex.re_ofReal_mul]
    norm_cast
  · intro j _ hj
    simp [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
  · simp

theorem re_sesq12_gradDiag (U : Fin 12 → ℂ) : (sesq12 gradDiag U U).re = cnormSq (gradOf U) := by
  have e : gradDiag = Matrix.diagonal fun i => (((if i.val < 9 then 1 else 0 : ℝ)) : ℂ) := by
    unfold gradDiag; congr 1; funext i; split_ifs <;> simp
  rw [e, re_sesq12_diagonal]
  unfold cnormSq gradOf
  simp [Fin.sum_univ_succ, Fintype.sum_prod_type]
  ring

theorem re_sesq12_velDiag (U : Fin 12 → ℂ) : (sesq12 velDiag U U).re = cnormSq (velOf U) := by
  have e : velDiag = Matrix.diagonal fun i => (((if i.val < 9 then 0 else 1 : ℝ)) : ℂ) := by
    unfold velDiag; congr 1; funext i; split_ifs <;> simp
  rw [e, re_sesq12_diagonal]
  unfold cnormSq velOf
  simp [Fin.sum_univ_succ]

def lossMatrix (lam c1 c2 : ℝ) : Matrix (Fin 12) (Fin 12) ℂ :=
  (lam : ℂ) • curlPairMatrix + (c1 : ℂ) • gradDiag + (c2 : ℂ) • velDiag

theorem re_sesq12_lossMatrix (lam c1 c2 : ℝ) (U : Fin 12 → ℂ) :
    (sesq12 (lossMatrix lam c1 c2) U U).re
      = lam * cnormSq (curlOfGrad (gradOf U)) + c1 * cnormSq (gradOf U) + c2 * cnormSq (velOf U) := by
  unfold lossMatrix
  rw [sesq12_add, sesq12_add, sesq12_smul, sesq12_smul, sesq12_smul, Complex.add_re, Complex.add_re,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul, re_sesq12_curlPairMatrix, re_sesq12_gradDiag,
    re_sesq12_velDiag]

theorem sqrt_mul_le_split (a b ℓ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hℓ : 0 < ℓ) :
    Real.sqrt a * Real.sqrt b ≤ (1 / 2) * (ℓ * b + a / ℓ) := by
  have hx := Real.sq_sqrt ha
  have hy := Real.sq_sqrt hb
  set x := Real.sqrt a
  set y := Real.sqrt b
  have key : ℓ * ((1 / 2) * (ℓ * b + a / ℓ) - x * y) = (ℓ * y - x) ^ 2 / 2 := by
    rw [← hx, ← hy]; field_simp; ring
  have : 0 ≤ ℓ * ((1 / 2) * (ℓ * b + a / ℓ) - x * y) := by rw [key]; positivity
  have := (mul_nonneg_iff_of_pos_left hℓ).mp this
  linarith

theorem slot_vel_sq (U : Fin 12 → ℂ) : ∑ i : Fin 3, ‖slotL U (Sum.inl i)‖ ^ 2 = cnormSq (velOf U) := rfl

theorem slot_grad_sq (U : Fin 12 → ℂ) :
    ∑ l : Fin 3, ∑ j : Fin 3, ‖slotL U (Sum.inr (l, j))‖ ^ 2 = cnormSq (gradOf U) := by
  unfold cnormSq
  rw [Fintype.sum_prod_type]
  rfl

theorem slot_curl_sq (U : Fin 12 → ℂ) :
    ∑ i : Fin 3, ‖curlOfGrad (fun ij => slotL U (Sum.inr ij)) i‖ ^ 2 = cnormSq (curlOfGrad (gradOf U)) := rfl

theorem symbol_lower (B : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (gW : ℤ × ℤ → Fin 3 × Fin 3 → ℂ)
    (hW : ℤ × ℤ → Fin 3 × Fin 3 × Fin 3 → ℂ) (wg : Fin 3 → Fin 3 → ℝ) (wh : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hg : ∑ β ∈ B, c β • gW β = fun ij => ((wg ij.1 ij.2 : ℝ) : ℂ))
    (hh : ∑ β ∈ B, c β • hW β = fun ijl => ((wh ijl.1 ijl.2.1 ijl.2.2 : ℝ) : ℂ)) (lam K ℓ : ℝ)
    (hS : ∀ u : Fin 3 → ℝ, ∑ a : Fin 3, ∑ b : Fin 3, u a * ((wg a b + wg b a) / 2) * u b ≤ lam * ∑ a : Fin 3, u a ^ 2)
    (htr : curlGradReal wh 0 0 + curlGradReal wh 1 1 + curlGradReal wh 2 2 = 0) (hK0 : 0 ≤ K)
    (hK : ∀ x : Fin 3 → ℝ, ∑ j : Fin 3, matVec (curlGradReal wh) x j ^ 2 ≤ K ^ 2 * ∑ m : Fin 3, x m ^ 2)
    (hℓ : 0 < ℓ) (U : Fin 12 → ℂ) :
    -(sesq12 (lossMatrix lam ((1 / 2) * Real.sqrt (7 / 2) * K * ℓ) ((1 / 2) * Real.sqrt (7 / 2) * K / ℓ)) U U).re
      ≤ (sesq12 (∑ β ∈ B, c β • tripleMatrix (gW β) (hW β)) U U).re := by
  rw [sesq12_symbol, hg, hh, re_sesq12_lossMatrix]
  have h := triple_lower wg wh lam K hS htr hK0 hK (slotL U)
  rw [slot_vel_sq, slot_grad_sq, slot_curl_sq] at h
  have hs := sqrt_mul_le_split (cnormSq (velOf U)) (cnormSq (gradOf U)) ℓ
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _) hℓ
  have hk : 0 ≤ Real.sqrt (7 / 2) * K := by positivity
  have hs' := mul_le_mul_of_nonneg_left hs hk
  have e : (1 / 2) * Real.sqrt (7 / 2) * K * ℓ * cnormSq (gradOf U) + (1 / 2) * Real.sqrt (7 / 2) * K / ℓ * cnormSq (velOf U)
      = Real.sqrt (7 / 2) * K * ((1 / 2) * (ℓ * cnormSq (gradOf U) + cnormSq (velOf U) / ℓ)) := by
    field_simp
  unfold slotC at *
  nlinarith [h, hs', e]

theorem mean_lower (hW0 : Fin 3 × Fin 3 × Fin 3 → ℂ) (wh : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hh : hW0 = fun ijl => ((wh ijl.1 ijl.2.1 ijl.2.2 : ℝ) : ℂ)) (K : ℝ)
    (htr : curlGradReal wh 0 0 + curlGradReal wh 1 1 + curlGradReal wh 2 2 = 0) (hK0 : 0 ≤ K)
    (hK : ∀ x : Fin 3 → ℝ, ∑ j : Fin 3, matVec (curlGradReal wh) x j ^ 2 ≤ K ^ 2 * ∑ m : Fin 3, x m ^ 2)
    (U : Fin 12 → ℂ) :
    -(Real.sqrt (7 / 2) * K * Real.sqrt (cnormSq (velOf U)) * Real.sqrt (cnormSq (gradOf U)))
      ≤ (sesq12 (tripleMatrix 0 hW0) U U).re := by
  rw [sesq12_tripleMatrix, hh]
  have h0 : (0 : Fin 3 × Fin 3 → ℂ) = fun ij => (((fun _ _ => (0 : ℝ)) ij.1 ij.2 : ℝ) : ℂ) := by
    funext ij; simp
  rw [h0]
  have h := triple_lower (fun _ _ => 0) wh 0 K (fun u => by simp) htr hK0 hK (slotL U)
  rw [slot_vel_sq, slot_grad_sq, slot_curl_sq] at h
  unfold slotC
  linarith

theorem wavePhase_eq_phase (β : ℤ × ℤ) (τ φ : ℝ) : wavePhase β τ φ = phase β τ φ := rfl

theorem torusInt_of_cont (f : ℝ → ℝ → ℂ) (hf : Continuous fun z : ℝ × ℝ => f z.1 z.2) :
    IsTorusIntegrable f :=
  integrable_box_of_continuous hf

theorem torusMean_trig (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) :
    torusMean (fun τ φ => ∑ β ∈ S, phase β τ φ * c β) = if (0 : ℤ × ℤ) ∈ S then c 0 else 0 := by
  rw [TorusMean.torusMean_sum]
  · simp_rw [mul_comm _ (c _)]
    simp only [TorusMean.torusMean_const_mul, TorusMean.torusMean_phase, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
  · intro β _
    exact torusInt_of_cont (fun τ φ => phase β τ φ * c β)
      ((continuous_phase β).mul continuous_const)

theorem mean_vort_identity (S : Finset (ℤ × ℤ)) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (y0 : Space)
    (hE2 : ∀ τ φ a b c, ((frameSecondDeriv HW y0 τ φ a b c : ℝ) : ℂ) = ∑ β ∈ S, phase β τ φ * modeSecondDeriv β HW 0 y0 (a, b, c))
    (hV : ∀ τ φ j l, fibGrad (fun σ y => CoerciveWeak.vortGradMap (HW σ y)) y0 τ φ j l
      = curlGradReal (frameSecondDeriv HW y0 τ φ) j l)
    (j l : Fin 3) :
    modeGrad 0 (fun σ y => CoerciveWeak.vortGradMap (HW σ y)) 0 y0 (j, l)
      = ∑ a : Fin 3, ∑ b : Fin 3, (alternatingSymbol j a b : ℂ)
          * (if (0 : ℤ × ℤ) ∈ S then modeSecondDeriv 0 HW 0 y0 (b, l, a) else 0) := by
  rw [modeGrad_zero_eq]
  have e1 : ∀ τ φ, expFactor 0 τ φ * ((fibGrad (fun σ y => CoerciveWeak.vortGradMap (HW σ y)) y0 τ φ j l : ℝ) : ℂ)
      = ∑ a : Fin 3, ∑ b : Fin 3, (alternatingSymbol j a b : ℂ)
          * ∑ β ∈ S, phase β τ φ * modeSecondDeriv β HW 0 y0 (b, l, a) := by
    intro τ φ
    rw [hV]
    simp only [expFactor, Prod.fst_zero, Prod.snd_zero, Int.cast_zero, mul_zero, zero_mul, add_zero,
      Complex.ofReal_zero, neg_zero, Complex.exp_zero, one_mul, curlGradReal]
    push_cast
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hE2]
  simp_rw [e1]
  have e2 := torusMean_trig
  change torusMean (fun τ φ => ∑ a : Fin 3, ∑ b : Fin 3, (alternatingSymbol j a b : ℂ)
      * ∑ β ∈ S, phase β τ φ * modeSecondDeriv β HW 0 y0 (b, l, a)) = _
  rw [TorusMean.torusMean_sum]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [TorusMean.torusMean_sum]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [TorusMean.torusMean_const_mul, torusMean_trig]
    · intro b _
      exact torusInt_of_cont (fun τ φ => (alternatingSymbol j a b : ℂ)
          * ∑ β ∈ S, phase β τ φ * modeSecondDeriv β HW 0 y0 (b, l, a))
        (continuous_const.mul (continuous_finsetSum _ fun β _ => (continuous_phase β).mul continuous_const))
  · intro a _
    exact torusInt_of_cont (fun τ φ => ∑ b : Fin 3, (alternatingSymbol j a b : ℂ)
          * ∑ β ∈ S, phase β τ φ * modeSecondDeriv β HW 0 y0 (b, l, a))
      (continuous_finsetSum _ fun b _ => continuous_const.mul
        (continuous_finsetSum _ fun β _ => (continuous_phase β).mul continuous_const))

theorem le_iInf_mul {f : ℤ × ℤ → ℝ} {a b : ℝ} (hb : 0 ≤ b) (h : ∀ ι, a ≤ f ι * b) :
    a ≤ (⨅ ι, f ι) * b := by
  rcases hb.eq_or_lt with hb0 | hbpos
  · rw [← hb0, mul_zero]
    have := h 0
    rw [← hb0, mul_zero] at this
    exact this
  · have : a / b ≤ ⨅ ι, f ι := le_ciInf fun ι => (div_le_iff₀ hbpos).mpr (h ι)
    exact (div_le_iff₀ hbpos).mp this

theorem bdd_of_unit {f : ℤ × ℤ → ℝ} {a0 b0 : ℝ} (hb0 : 0 < b0) (h : ∀ ι, a0 ≤ f ι * b0) :
    BddBelow (Set.range f) := by
  refine ⟨a0 / b0, ?_⟩
  rintro _ ⟨ι, rfl⟩
  exact (div_le_iff₀ hb0).mpr (h ι)

theorem curlGradReal_trace (h : Fin 3 → Fin 3 → Fin 3 → ℝ) (hs : ∀ b k a, h b k a = h b a k) :
    curlGradReal h 0 0 + curlGradReal h 1 1 + curlGradReal h 2 2 = 0 := by
  simp only [curlGradReal, Fin.sum_univ_three, alternatingSymbol]
  norm_num
  have e1 := hs 0 1 2
  have e2 := hs 1 2 0
  have e3 := hs 2 0 1
  linarith

theorem curlGradReal_sub (h h' : Fin 3 → Fin 3 → Fin 3 → ℝ) (k n : Fin 3) :
    curlGradReal (fun a b c => h a b c - h' a b c) k n = curlGradReal h k n - curlGradReal h' k n := by
  simp only [curlGradReal, mul_sub, Finset.sum_sub_distrib]

theorem modeSecondDeriv_zero_real (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (y : Space) (i j l : Fin 3) :
    modeSecondDeriv 0 HW 0 y (i, j, l) = (((modeSecondDeriv 0 HW 0 y (i, j, l)).re : ℝ) : ℂ) := by
  have e : modeSecondDeriv 0 HW 0 y (i, j, l) = (((1 / (2 * Real.pi)) * ∫ τ in (0 : ℝ)..1,
      ∫ φ in (0 : ℝ)..(2 * Real.pi), frameSecondDeriv HW y τ φ i j l : ℝ) : ℂ) := by
    rw [modeSecondDeriv_zero_eq]
    simp only [expFactor, Prod.fst_zero, Prod.snd_zero, Int.cast_zero, mul_zero, zero_mul, add_zero,
      Complex.ofReal_zero, neg_zero, Complex.exp_zero, one_mul]
    rw [intervalIntegral.integral_congr (g := fun τ => (((∫ φ in (0 : ℝ)..(2 * Real.pi),
      frameSecondDeriv HW y τ φ i j l : ℝ)) : ℂ)) (fun τ _ => intervalIntegral.integral_ofReal)]
    rw [intervalIntegral.integral_ofReal]
    push_cast
    ring
  rw [e, Complex.ofReal_re]

theorem modeSecondDeriv_symm (β : ℤ × ℤ) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (hsym : ∀ σ y u w, HW σ y u w = HW σ y w u) (y : Space) (i j l : Fin 3) :
    modeSecondDeriv β HW 0 y (i, j, l) = modeSecondDeriv β HW 0 y (i, l, j) := by
  unfold modeSecondDeriv modeAverage
  simp only [hsym]

theorem frameSecondDeriv_symm (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (hsym : ∀ σ y u w, HW σ y u w = HW σ y w u) (y : Space) (τ φ : ℝ) (i j l : Fin 3) :
    frameSecondDeriv HW y τ φ i j l = frameSecondDeriv HW y τ φ i l j := by
  unfold frameSecondDeriv
  rw [hsym]

theorem tripleMatrix_split (g : Fin 3 × Fin 3 → ℂ) (h h' : Fin 3 × Fin 3 × Fin 3 → ℂ) :
    tripleMatrix g (h + h') = tripleMatrix g h + tripleMatrix 0 h' := by
  ext i j
  rw [Matrix.add_apply]
  have e1 := pairForm_add_W g 0 h h' (slotL (Pi.single j 1)) (slotL (Pi.single i 1))
  have e2 := pairForm_add_W g 0 h h' (slotL (Pi.single i 1)) (slotL (Pi.single j 1))
  rw [add_zero] at e1 e2
  show (pairForm g (h + h') (slotL (Pi.single j 1)) (slotL (Pi.single i 1))
      + pairForm g (h + h') (slotL (Pi.single i 1)) (slotL (Pi.single j 1))) / 2
    = (pairForm g h (slotL (Pi.single j 1)) (slotL (Pi.single i 1))
      + pairForm g h (slotL (Pi.single i 1)) (slotL (Pi.single j 1))) / 2
    + (pairForm 0 h' (slotL (Pi.single j 1)) (slotL (Pi.single i 1))
      + pairForm 0 h' (slotL (Pi.single i 1)) (slotL (Pi.single j 1))) / 2
  rw [e1, e2]
  ring

end Sharp

end Internal

end Assembly

end CertCell

end Breakdown
