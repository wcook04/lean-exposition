import Breakdown.FracCell.SharpYSharpEnergyTail
import Breakdown.FracCell.BasisEnergySum
import Breakdown.FracCell.ProjCoef
import Breakdown.FracCell.FieldModeSquare
import Breakdown.FracCell.ModeSquareIntegrable

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly SharpParts SharpEnergyTailParts

namespace ModeSquareSumInternal

theorem lw_cont (K : CellBox) : Continuous (fun p : ℝ × ℝ => K.lineWeight p.1) := by
  unfold CellBox.lineWeight
  split_ifs
  · exact continuous_fst
  · exact continuous_const

theorem lw_nonneg (K : CellBox) (hK : IsCellBox K) (p : ℝ × ℝ) (hp : p ∈ K.rect) : 0 ≤ K.lineWeight p.1 := by
  unfold CellBox.lineWeight
  split_ifs
  · exact le_trans hK.r_order.1 hp.1.1
  · exact zero_le_one

theorem rect_meas (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

theorem coef_const_mul (K : CellBox) (B : CellBases) (a : ℂ) (F : ℝ × ℝ → ℂ) (j l : ℕ) :
    B.coef K (fun p => a * F p) j l = a * B.coef K F j l := by
  unfold CellBases.coef
  rw [← integral_const_mul]
  congr 1
  funext p
  ring

theorem ws_const_mul (K : CellBox) (a : ℂ) {F : ℝ × ℝ → ℂ} (hF : IsWeightedSquare K F) :
    IsWeightedSquare K (fun p => a * F p) := by
  refine ⟨aestronglyMeasurable_const.mul hF.1, ?_⟩
  refine IntegrableOn.congr_fun (f := fun p => ‖a‖ ^ 2 * (K.lineWeight p.1 * ‖F p‖ ^ 2))
    (hF.2.const_mul (‖a‖ ^ 2)) (fun p _ => ?_) (rect_meas K)
  simp only [norm_mul, mul_pow]
  ring

theorem sq_expand {ι : Type} [Fintype ι] (w : ι → ℂ) :
    (((‖∑ i, w i‖ ^ 2 : ℝ)) : ℂ) = ∑ i, ∑ i', w i * (starRingEnd ℂ) (w i') := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]

theorem quad_hasSum (K : CellBox) (B : CellBases) (hK : IsCellBox K) (hB : IsCellBases K B)
    {κ ι : Type} [Fintype κ] [Fintype ι] (A : κ → ι → ℝ) (F : ι → ℝ × ℝ → ℂ)
    (hF : ∀ i, IsWeightedSquare K (F i)) :
    HasSum (fun jl : ℕ × ℕ => ∑ m, ‖∑ i, (A m i : ℂ) * B.coef K (F i) jl.1 jl.2‖ ^ 2)
      (∫ p in K.rect, K.lineWeight p.1 * ∑ m, ‖∑ i, (A m i : ℂ) * F i p‖ ^ 2) := by
  have hs := basisEnergySum_holds K B hK hB (κ × ι × ι)
    (fun t p => (A t.1 t.2.1 : ℂ) * F t.2.1 p) (fun t p => (A t.1 t.2.2 : ℂ) * F t.2.2 p)
    (fun t => ws_const_mul K _ (hF _)) (fun t => ws_const_mul K _ (hF _))
  have hre := hs.mapL Complex.reCLM
  have e1 : ∀ (w : ι → ℂ) (mm : κ), ∑ t : ι × ι, (A mm t.1 : ℂ) * w t.1 * (starRingEnd ℂ) ((A mm t.2 : ℂ) * w t.2)
      = ((‖∑ i, (A mm i : ℂ) * w i‖ ^ 2 : ℝ) : ℂ) := by
    intro w mm
    rw [sq_expand, Fintype.sum_prod_type]
  convert hre using 1
  · funext jl
    simp only [Complex.reCLM_apply, coef_const_mul]
    rw [Fintype.sum_prod_type]
    have e2 := fun m => e1 (fun i => B.coef K (F i) jl.1 jl.2) m
    rw [Finset.sum_congr rfl (fun m _ => e2 m), ← Complex.ofReal_sum, Complex.ofReal_re]
  · simp only [Complex.reCLM_apply]
    have hfun : (fun p : ℝ × ℝ => ((K.lineWeight p.1 : ℝ) : ℂ) * ∑ t : κ × ι × ι,
        (A t.1 t.2.1 : ℂ) * F t.2.1 p * (starRingEnd ℂ) ((A t.1 t.2.2 : ℂ) * F t.2.2 p))
        = fun p => ((K.lineWeight p.1 * ∑ m, ‖∑ i, (A m i : ℂ) * F i p‖ ^ 2 : ℝ) : ℂ) := by
      funext p
      rw [Fintype.sum_prod_type]
      simp only [e1 (fun i => F i p)]
      push_cast
      ring
    rw [hfun, integral_complex_ofReal, Complex.ofReal_re]

theorem quad_integrable (K : CellBox) (hK : IsCellBox K) {κ ι : Type} [Fintype κ] [Fintype ι]
    (A : κ → ι → ℝ) (F : ι → ℝ × ℝ → ℂ) (hF : ∀ i, IsWeightedSquare K (F i)) :
    IntegrableOn (fun p => K.lineWeight p.1 * ∑ m, ‖∑ i, (A m i : ℂ) * F i p‖ ^ 2) K.rect := by
  have hg : IntegrableOn (fun p => ∑ m, ∑ i, (Fintype.card ι : ℝ) * (A m i ^ 2 * (K.lineWeight p.1 * ‖F i p‖ ^ 2)))
      K.rect :=
    integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun i _ => ((hF i).2.const_mul _).const_mul _
  refine hg.mono' ?_ ?_
  · refine ((lw_cont K).comp_aestronglyMeasurable aestronglyMeasurable_id).mul ?_
    refine Finset.aestronglyMeasurable_fun_sum (f := fun m p => ‖∑ i, (A m i : ℂ) * F i p‖ ^ 2) _ fun m _ => ?_
    refine (Finset.aestronglyMeasurable_fun_sum (f := fun i p => (A m i : ℂ) * F i p) _ fun i _ => ?_).norm.pow 2
    exact aestronglyMeasurable_const.mul (hF i).1
  · refine (ae_restrict_iff' (rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_)
    have hlw := lw_nonneg K hK p hp
    have hm : ∀ m, ‖∑ i, (A m i : ℂ) * F i p‖ ^ 2 ≤ ∑ i, (Fintype.card ι : ℝ) * (A m i ^ 2 * ‖F i p‖ ^ 2) := by
      intro m
      calc ‖∑ i, (A m i : ℂ) * F i p‖ ^ 2 ≤ (∑ i, ‖(A m i : ℂ) * F i p‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
        _ ≤ (Finset.univ : Finset ι).card * ∑ i, ‖(A m i : ℂ) * F i p‖ ^ 2 := sq_sum_le_card_mul_sum_sq
        _ = ∑ i, (Fintype.card ι : ℝ) * (A m i ^ 2 * ‖F i p‖ ^ 2) := by
            rw [Finset.card_univ, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    have h0 : 0 ≤ K.lineWeight p.1 * ∑ m, ‖∑ i, (A m i : ℂ) * F i p‖ ^ 2 :=
      mul_nonneg hlw (Finset.sum_nonneg fun m _ => by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    calc K.lineWeight p.1 * ∑ m, ‖∑ i, (A m i : ℂ) * F i p‖ ^ 2
        ≤ K.lineWeight p.1 * ∑ m, ∑ i, (Fintype.card ι : ℝ) * (A m i ^ 2 * ‖F i p‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => hm m) hlw
      _ = ∑ m, ∑ i, (Fintype.card ι : ℝ) * (A m i ^ 2 * (K.lineWeight p.1 * ‖F i p‖ ^ 2)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring

def idMat {ι : Type} [DecidableEq ι] (m i : ι) : ℝ := if i = m then 1 else 0

theorem sumSq_quad (s : Fin 3 → Fin 3 → ℂ) :
    sumSq s = ∑ m : Fin 3 × Fin 3, ‖∑ i : Fin 3 × Fin 3, (idMat m i : ℂ) * s i.1 i.2‖ ^ 2 := by
  unfold sumSq idMat
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp [apply_ite (fun t : ℝ => (t : ℂ)), ite_mul, Finset.sum_ite_eq']

theorem vecSq_quad (v : Fin 3 → ℂ) :
    vecSq v = ∑ m : Fin 3, ‖∑ i : Fin 3, (idMat m i : ℂ) * v i‖ ^ 2 := by
  unfold vecSq idMat
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [apply_ite (fun t : ℝ => (t : ℂ)), ite_mul, Finset.sum_ite_eq']

def curlMat (m : Fin 3) (i : Fin 3 × Fin 3) : ℝ := CellCert.permSign m i.2 i.1

theorem curlSq_quad (s : Fin 3 → Fin 3 → ℂ) :
    curlSq s = ∑ m : Fin 3, ‖∑ i : Fin 3 × Fin 3, (curlMat m i : ℂ) * s i.1 i.2‖ ^ 2 := by
  unfold curlSq curlComp curlMat
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem par_sq (x y : ℂ) : ‖(x + y) / 2‖ ^ 2 + ‖(x - y) / 2‖ ^ 2 = (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
  have h1 := norm_add_sq_real x y
  have h2 := norm_sub_sq_real x y
  have h3 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [norm_div, norm_div, h3, div_pow, div_pow, h1, h2]
  ring

theorem sym_anti (s : Fin 3 → Fin 3 → ℂ) : symSq s + antiSq s = sumSq s := by
  unfold symSq antiSq sumSq
  rw [← Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib, par_sq]
  have e : ∑ a : Fin 3, ∑ b : Fin 3, ‖s b a‖ ^ 2 = ∑ a : Fin 3, ∑ b : Fin 3, ‖s a b‖ ^ 2 := Finset.sum_comm
  have e2 : ∑ a : Fin 3, ∑ b : Fin 3, (‖s a b‖ ^ 2 + ‖s b a‖ ^ 2) / 2
      = (∑ a : Fin 3, ∑ b : Fin 3, ‖s a b‖ ^ 2 + ∑ a : Fin 3, ∑ b : Fin 3, ‖s b a‖ ^ 2) / 2 := by
    simp only [Finset.sum_div, Finset.sum_add_distrib, add_div]
  rw [e2, e]
  ring

theorem half_sub (x y : ℂ) : ‖(x - y) / 2‖ ^ 2 = ‖x - y‖ ^ 2 / 4 := by
  have h3 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [norm_div, h3, div_pow]
  norm_num

theorem curl_anti (s : Fin 3 → Fin 3 → ℂ) : curlSq s = 2 * antiSq s := by
  unfold curlSq curlComp antiSq
  simp only [half_sub]
  simp [Fin.sum_univ_three, CellCert.permSign]
  rw [norm_sub_rev (s 0 1), norm_sub_rev (s 0 2), norm_sub_rev (s 1 2)]
  ring_nf
  rw [show -s 2 0 + s 0 2 = -(s 2 0 - s 0 2) by ring, norm_neg]
  ring

end ModeSquareSumInternal

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly SharpParts SharpEnergyTailParts

namespace ModeSquareSumInternal

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (x : FieldTuple k)

theorem sharp_ws (hK : IsCellBox K) (hB : IsCellBases K B) (n : ℤ)
    (hg : ∀ i q, IsWeightedSquare K (gradMode c.order n x.2.1 i q)) (a b : Fin 3) :
    IsWeightedSquare K (fun p => sharpGrad c K S x n p a b) := by
  by_cases hr : n ∈ S.resolved
  · have h := (projCoef_holds K B hK hB _ (hg a b) S.degHigh).1
    convert h using 2 with p
    simp only [sharpGrad, lowGrad, hr, if_true, CellBox.lowStrainAt, CellBox.lowStrain]
  · convert hg a b using 2 with p
    simp only [sharpGrad, lowGrad, hr, if_false, Pi.zero_apply, sub_zero]

open Classical in
theorem sharp_coef (hK : IsCellBox K) (hB : IsCellBases K B) (n : ℤ)
    (hg : ∀ i q, IsWeightedSquare K (gradMode c.order n x.2.1 i q)) (jl : ℕ × ℕ) :
    (fun a b => B.coef K (fun p => sharpGrad c K S x n p a b) jl.1 jl.2)
      = if strainIdx S n jl then sharpStrainCoef c K B x n jl.1 jl.2 else 0 := by
  funext a b
  by_cases hr : n ∈ S.resolved
  · have h := (projCoef_holds K B hK hB _ (hg a b) S.degHigh).2 jl.1 jl.2
    have e : (fun p => sharpGrad c K S x n p a b)
        = fun p => gradMode c.order n x.2.1 a b p - K.proj S.degHigh S.degHigh (gradMode c.order n x.2.1 a b) p := by
      funext p
      simp only [sharpGrad, lowGrad, hr, if_true, CellBox.lowStrainAt, CellBox.lowStrain]
    rw [e, h]
    by_cases hm : max jl.1 jl.2 ≤ S.degHigh
    · have hi : ¬ strainIdx S n jl := by
        unfold strainIdx
        push Not
        exact ⟨hr, hm⟩
      simp only [hm, if_true, hi, if_false, Pi.zero_apply]
    · have hi : strainIdx S n jl := Or.inr (not_le.1 hm)
      simp only [hm, if_false, hi, if_true]
      rfl
  · have hi : strainIdx S n jl := Or.inl hr
    have e : (fun p => sharpGrad c K S x n p a b) = gradMode c.order n x.2.1 a b := by
      funext p
      simp only [sharpGrad, lowGrad, hr, if_false, Pi.zero_apply, sub_zero]
    rw [e]
    simp only [hi, if_true]
    rfl

theorem vel_ws (hK : IsCellBox K) (hB : IsCellBases K B) (n : ℤ)
    (hv : ∀ i, IsWeightedSquare K (fun p : ℝ × ℝ => modeVec c.order n x.1 p.1 p.2 i)) (a : Fin 3) :
    IsWeightedSquare K (fun p => sharpVel c K S x n p a) := by
  by_cases hr : n ∈ S.resolved
  · have h := (projCoef_holds K B hK hB _ (hv a) (S.degHigh - 1)).1
    convert h using 2 with p
    simp only [sharpVel, lowVel, hr, if_true, CellBox.lowVelocityAt, CellBox.lowVelocity]
  · convert hv a using 2 with p
    simp only [sharpVel, lowVel, hr, if_false, Pi.zero_apply, sub_zero]

theorem vel_coef (hK : IsCellBox K) (hB : IsCellBases K B) (n : ℤ) (hr : n ∈ S.resolved) (hdeg : 1 ≤ S.degHigh)
    (hv : ∀ i, IsWeightedSquare K (fun p : ℝ × ℝ => modeVec c.order n x.1 p.1 p.2 i)) (jl : ℕ × ℕ) :
    (fun a => B.coef K (fun p => sharpVel c K S x n p a) jl.1 jl.2)
      = if S.degHigh ≤ max jl.1 jl.2 then sharpVelocityCoef c K B x n jl.1 jl.2 else 0 := by
  funext a
  have h := (projCoef_holds K B hK hB _ (hv a) (S.degHigh - 1)).2 jl.1 jl.2
  have e : (fun p => sharpVel c K S x n p a)
      = fun p => modeVec c.order n x.1 p.1 p.2 a
          - K.proj (S.degHigh - 1) (S.degHigh - 1) (fun p : ℝ × ℝ => modeVec c.order n x.1 p.1 p.2 a) p := by
    funext p
    simp only [sharpVel, lowVel, hr, if_true, CellBox.lowVelocityAt, CellBox.lowVelocity]
  rw [e, h]
  by_cases hm : S.degHigh ≤ max jl.1 jl.2
  · have hm' : ¬ max jl.1 jl.2 ≤ S.degHigh - 1 := by omega
    simp only [hm, if_true, hm', if_false]
    rfl
  · have hm' : max jl.1 jl.2 ≤ S.degHigh - 1 := by omega
    simp only [hm, if_false, hm', if_true, Pi.zero_apply]

theorem third_int (hK : IsCellBox K) (m : ℕ) (n : ℤ) {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (κ : Fin 3 → Fin 3 → ℂ)
    (cc : Fin 3) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖∑ a : Fin 3, ∑ b : Fin 3, κ a b * modeThird m n H a b cc p‖ ^ 2) K.rect :=
  ((modeSquareIntegrable K hK m v G H hs n κ).2.2 cc).2

theorem second_int (hK : IsCellBox K) (m : ℕ) (n : ℤ) {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * secondModeSq m n H p) K.rect := by
  have h : ∀ a b cc : Fin 3, IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖modeThird m n H a b cc p‖ ^ 2) K.rect := by
    intro a b cc
    refine (third_int K hK m n hs (fun a' b' => if a' = a ∧ b' = b then 1 else 0) cc).congr_fun
      (fun p _ => ?_) (rect_meas K)
    simp [ite_and, ite_mul, Finset.sum_ite_eq']
  have hsum : IntegrableOn (fun p : ℝ × ℝ => ∑ a : Fin 3, ∑ b : Fin 3, ∑ cc : Fin 3,
      p.1 * ‖modeThird m n H a b cc p‖ ^ 2) K.rect :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => integrable_finsetSum _ fun cc _ => h a b cc
  refine IntegrableOn.congr_fun hsum (fun p _ => ?_) (rect_meas K)
  simp only [secondModeSq, Finset.mul_sum]

theorem curl_int (hK : IsCellBox K) (m : ℕ) (n : ℤ) {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * curlGradModeSq m n H p) K.rect := by
  have h : ∀ i cc : Fin 3, IntegrableOn
      (fun p : ℝ × ℝ => p.1 * ‖curlComp (fun a b => modeThird m n H a b cc p) i‖ ^ 2) K.rect := by
    intro i cc
    refine (third_int K hK m n hs (fun a b => (CellCert.permSign i b a : ℂ)) cc).congr_fun
      (fun p _ => ?_) (rect_meas K)
    unfold curlComp
    rw [Finset.sum_comm]
  have hsum : IntegrableOn (fun p : ℝ × ℝ => ∑ i : Fin 3, ∑ cc : Fin 3,
      p.1 * ‖curlComp (fun a b => modeThird m n H a b cc p) i‖ ^ 2) K.rect :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun cc _ => h i cc
  refine IntegrableOn.congr_fun hsum (fun p _ => ?_) (rect_meas K)
  simp only [curlGradModeSq, Finset.mul_sum]

open Classical in
theorem strain_sum (hK : IsCellBox K) (hB : IsCellBases K B) (n : ℤ)
    (hg : ∀ i q, IsWeightedSquare K (gradMode c.order n x.2.1 i q)) :
    HasSum (fun jl => if strainIdx S n jl then symCoefSq c K B x n jl + antiCoefSq c K B x n jl else 0)
      (∫ p in K.rect, K.lineWeight p.1 * sumSq (sharpGrad c K S x n p)) := by
  have hsg : ∀ i : Fin 3 × Fin 3, IsWeightedSquare K (fun p => sharpGrad c K S x n p i.1 i.2) :=
    fun i => sharp_ws c K S B x hK hB n hg i.1 i.2
  have pS := quad_hasSum K B hK hB (idMat (ι := Fin 3 × Fin 3)) (fun i p => sharpGrad c K S x n p i.1 i.2) hsg
  have e1 : (fun jl => if strainIdx S n jl then symCoefSq c K B x n jl + antiCoefSq c K B x n jl else 0)
      = fun jl : ℕ × ℕ => ∑ m : Fin 3 × Fin 3, ‖∑ i : Fin 3 × Fin 3,
          (idMat m i : ℂ) * B.coef K ((fun i p => sharpGrad c K S x n p i.1 i.2) i) jl.1 jl.2‖ ^ 2 := by
    funext jl
    refine Eq.trans ?_ (sumSq_quad (fun a b => B.coef K (fun p => sharpGrad c K S x n p a b) jl.1 jl.2))
    rw [sharp_coef c K S B x hK hB n hg jl]
    by_cases hi : strainIdx S n jl
    · simp only [hi, if_true]
      exact sym_anti _
    · simp only [hi, if_false]
      simp [sumSq]
  have e2 : (∫ p in K.rect, K.lineWeight p.1 * sumSq (sharpGrad c K S x n p))
      = ∫ p in K.rect, K.lineWeight p.1 * ∑ m : Fin 3 × Fin 3, ‖∑ i : Fin 3 × Fin 3,
          (idMat m i : ℂ) * (fun i p => sharpGrad c K S x n p i.1 i.2) i p‖ ^ 2 := by
    simp only [sumSq_quad]
  rw [e1, e2]
  exact pS

open Classical in
theorem curl_sum (hK : IsCellBox K) (hB : IsCellBases K B) (n : ℤ)
    (hg : ∀ i q, IsWeightedSquare K (gradMode c.order n x.2.1 i q)) :
    HasSum (fun jl => if strainIdx S n jl then 2 * antiCoefSq c K B x n jl else 0)
      (∫ p in K.rect, K.lineWeight p.1 * curlSq (sharpGrad c K S x n p)) := by
  have hsg : ∀ i : Fin 3 × Fin 3, IsWeightedSquare K (fun p => sharpGrad c K S x n p i.1 i.2) :=
    fun i => sharp_ws c K S B x hK hB n hg i.1 i.2
  have pC := quad_hasSum K B hK hB curlMat (fun i p => sharpGrad c K S x n p i.1 i.2) hsg
  have e1 : (fun jl => if strainIdx S n jl then 2 * antiCoefSq c K B x n jl else 0)
      = fun jl : ℕ × ℕ => ∑ m : Fin 3, ‖∑ i : Fin 3 × Fin 3,
          (curlMat m i : ℂ) * B.coef K ((fun i p => sharpGrad c K S x n p i.1 i.2) i) jl.1 jl.2‖ ^ 2 := by
    funext jl
    refine Eq.trans ?_ (curlSq_quad (fun a b => B.coef K (fun p => sharpGrad c K S x n p a b) jl.1 jl.2))
    rw [sharp_coef c K S B x hK hB n hg jl]
    by_cases hi : strainIdx S n jl
    · simp only [hi, if_true]
      exact (curl_anti _).symm
    · simp only [hi, if_false]
      simp [curlSq, curlComp]
  have e2 : (∫ p in K.rect, K.lineWeight p.1 * curlSq (sharpGrad c K S x n p))
      = ∫ p in K.rect, K.lineWeight p.1 * ∑ m : Fin 3, ‖∑ i : Fin 3 × Fin 3,
          (curlMat m i : ℂ) * (fun i p => sharpGrad c K S x n p i.1 i.2) i p‖ ^ 2 := by
    simp only [curlSq_quad]
  rw [e1, e2]
  exact pC

theorem vel_sum (hK : IsCellBox K) (hB : IsCellBases K B) (n : ℤ) (hr : n ∈ S.resolved) (hdeg : 1 ≤ S.degHigh)
    (hv : ∀ i, IsWeightedSquare K (fun p : ℝ × ℝ => modeVec c.order n x.1 p.1 p.2 i)) :
    HasSum (fun jl : ℕ × ℕ => if S.degHigh ≤ max jl.1 jl.2 then velCoefSq c K B x n jl else 0)
      (∫ p in K.rect, K.lineWeight p.1 * vecSq (sharpVel c K S x n p)) := by
  have hsv : ∀ i : Fin 3, IsWeightedSquare K (fun p => sharpVel c K S x n p i) :=
    fun i => vel_ws c K S B x hK hB n hv i
  have pV := quad_hasSum K B hK hB idMat (fun i p => sharpVel c K S x n p i) hsv
  have e1 : (fun jl : ℕ × ℕ => if S.degHigh ≤ max jl.1 jl.2 then velCoefSq c K B x n jl else 0)
      = fun jl : ℕ × ℕ => ∑ m : Fin 3, ‖∑ i : Fin 3,
          (idMat m i : ℂ) * B.coef K ((fun i p => sharpVel c K S x n p i) i) jl.1 jl.2‖ ^ 2 := by
    funext jl
    refine Eq.trans ?_ (vecSq_quad (fun a => B.coef K (fun p => sharpVel c K S x n p a) jl.1 jl.2))
    rw [vel_coef c K S B x hK hB n hr hdeg hv jl]
    by_cases hi : S.degHigh ≤ max jl.1 jl.2
    · simp only [hi, if_true]
      rfl
    · simp only [hi, if_false]
      simp [vecSq]
  have e2 : (∫ p in K.rect, K.lineWeight p.1 * vecSq (sharpVel c K S x n p))
      = ∫ p in K.rect, K.lineWeight p.1 * ∑ m : Fin 3, ‖∑ i : Fin 3,
          (idMat m i : ℂ) * (fun i p => sharpVel c K S x n p i) i p‖ ^ 2 := by
    simp only [vecSq_quad]
  rw [e1, e2]
  exact pV

theorem strain_int (hK : IsCellBox K) (hB : IsCellBases K B) (n : ℤ)
    (hg : ∀ i q, IsWeightedSquare K (gradMode c.order n x.2.1 i q)) :
    IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * sumSq (sharpGrad c K S x n p)) K.rect ∧
      IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * curlSq (sharpGrad c K S x n p)) K.rect := by
  have hsg : ∀ i : Fin 3 × Fin 3, IsWeightedSquare K (fun p => sharpGrad c K S x n p i.1 i.2) :=
    fun i => sharp_ws c K S B x hK hB n hg i.1 i.2
  have iS := quad_integrable K hK (idMat (ι := Fin 3 × Fin 3)) (fun i p => sharpGrad c K S x n p i.1 i.2) hsg
  have iC := quad_integrable K hK curlMat (fun i p => sharpGrad c K S x n p i.1 i.2) hsg
  constructor
  · refine IntegrableOn.congr_fun iS (fun p _ => ?_) (rect_meas K)
    rw [sumSq_quad]
  · refine IntegrableOn.congr_fun iC (fun p _ => ?_) (rect_meas K)
    rw [curlSq_quad]

theorem vel_int (hK : IsCellBox K) (hB : IsCellBases K B) (n : ℤ)
    (hv : ∀ i, IsWeightedSquare K (fun p : ℝ × ℝ => modeVec c.order n x.1 p.1 p.2 i)) :
    IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * vecSq (sharpVel c K S x n p)) K.rect := by
  have hsv : ∀ i : Fin 3, IsWeightedSquare K (fun p => sharpVel c K S x n p i) :=
    fun i => vel_ws c K S B x hK hB n hv i
  have iV := quad_integrable K hK idMat (fun i p => sharpVel c K S x n p i) hsv
  refine IntegrableOn.congr_fun iV (fun p _ => ?_) (rect_meas K)
  rw [vecSq_quad]

end ModeSquareSumInternal

open ModeSquareSumInternal in
theorem modeEnergySum_holds : ModeEnergySumStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx n
  have hK := hd.box
  have hB := hd.bases
  have hdeg := hd.scalars.degrees
  have hfm := fieldModeSquare_holds K hK c.order x.1 x.2.1 x.2.2.1 hx.1 n
  have hI := strain_int c K S B x hK hB n hfm.1
  exact ⟨hI.1, hI.2, vel_int c K S B x hK hB n hfm.2, second_int K hK c.order n hx.1, curl_int K hK c.order n hx.1,
    strain_sum c K S B x hK hB n hfm.1, curl_sum c K S B x hK hB n hfm.1,
    fun hr => vel_sum c K S B x hK hB n hr (by omega) hfm.2⟩

end Breakdown.CellCert.CellAnalysis
