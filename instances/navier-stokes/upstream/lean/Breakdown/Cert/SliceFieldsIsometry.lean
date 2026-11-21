import Breakdown.FreqTr.Realization
import Breakdown.FreqTr.FreqTrConjSym
import Breakdown.FreqTr.PartialDecay

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.SliceFieldsIsometry

theorem vec_decomp (z : CSpace) :
    z = complexifyVec (realVec z) + Complex.I • complexifyVec (realVec ((-Complex.I) • z)) := by
  ext i
  apply Complex.ext <;> simp [complexifyVec, realVec]

def imagL : L2C →L[ℝ] L2R := realPart ∘L ContinuousLinearMap.compLpL 2 volume (cmul (-Complex.I))

theorem split (f : L2C) : f = complexify (realPart f) + Complex.I • complexify (imagL f) := by
  have e3 : (complexify (realPart f) : Space → CSpace) =ᵐ[volume]
      fun ξ => complexifyVec ((realPart f : Space → Space) ξ) :=
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec (realPart f)
  have e4 : (complexify (imagL f) : Space → CSpace) =ᵐ[volume]
      fun ξ => complexifyVec ((imagL f : Space → Space) ξ) :=
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec (imagL f)
  have e5 : (realPart f : Space → Space) =ᵐ[volume] fun ξ => realVec (f ξ) :=
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) realVec f
  have e6 : (imagL f : Space → Space) =ᵐ[volume]
      fun ξ => realVec ((ContinuousLinearMap.compLpL 2 volume (cmul (-Complex.I)) f : L2C) ξ) :=
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) realVec _
  have e7 : ((ContinuousLinearMap.compLpL 2 volume (cmul (-Complex.I)) f : L2C) : Space → CSpace)
      =ᵐ[volume] fun ξ => cmul (-Complex.I) (f ξ) :=
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) (cmul (-Complex.I)) f
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (complexify (realPart f)) (Complex.I • complexify (imagL f)),
    Lp.coeFn_smul Complex.I (complexify (imagL f)), e3, e4, e5, e6, e7]
    with ξ h1 h2 h3 h4 h5 h6 h7
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, h5, h6, h7]
  exact vec_decomp (f ξ)

theorem reflConj_I_smul (B : L2C) : reflConj (Complex.I • B) = -(Complex.I • reflConj B) := by
  apply Lp.ext
  filter_upwards [Freq.Internal.FreqTrConjSym.reflConj_ae fieldOpRealized_holds (Complex.I • B),
    Freq.Internal.FreqTrConjSym.reflConj_ae fieldOpRealized_holds B,
    Lp.coeFn_neg (Complex.I • reflConj B), Lp.coeFn_smul Complex.I (reflConj B),
    (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_smul Complex.I B)] with ξ h1 h2 h3 h4 h5
  rw [h1, h3, Pi.neg_apply, h4, Pi.smul_apply, h2]
  have h5' : (Complex.I • B : L2C) (-ξ) = Complex.I • B (-ξ) := h5
  rw [h5']
  ext i
  simp [conjVec]

theorem norm_complexifyVec' (v : Space) : ‖complexifyVec v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [complexifyVec]

theorem l2R_norm_sq (f : L2R) : ‖f‖ ^ 2 = ∫ ξ, ‖f ξ‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  ext ξ
  exact real_inner_self_eq_norm_sq _

theorem norm_complexify (r : L2R) : ‖complexify r‖ = ‖r‖ := by
  have h : ‖complexify r‖ ^ 2 = ‖r‖ ^ 2 := by
    rw [Freq.Internal.PartialDecay.l2_norm_sq, l2R_norm_sq]
    apply integral_congr_ae
    have e : (complexify r : Space → CSpace) =ᵐ[volume] fun ξ => complexifyVec (r ξ) :=
      ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec r
    filter_upwards [e] with ξ hξ
    rw [hξ, norm_complexifyVec']
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

end Internal.SliceFieldsIsometry

open Internal.SliceFieldsIsometry in
theorem norm_toPhys_of_mem_sig (F : Freq.L2C) (hF : F ∈ Freq.Sig) : ‖Freq.toPhys F‖ = ‖F‖ := by
  have hR : reflConj F = F := by
    have := (Submodule.mem_inf.1 hF).1
    rw [LinearMap.mem_ker] at this
    exact sub_eq_zero.1 this
  set f : L2C := freqTrL2.symm F with hf
  set r : L2R := realPart f with hr
  set A : L2C := freqTrL2 (complexify r) with hA
  set B : L2C := freqTrL2 (complexify (imagL f)) with hB
  have hFAB : F = A + Complex.I • B := by
    have h0 : F = freqTrL2 f := (freqTrL2.apply_symm_apply F).symm
    rw [h0, split f, map_add, map_smul]
  have hAr : reflConj A = A := freqTrConjSym fieldOpRealized_holds r
  have hBr : reflConj B = B := freqTrConjSym fieldOpRealized_holds (imagL f)
  have hRF : reflConj F = A + -(Complex.I • B) := by
    rw [hFAB, map_add, reflConj_I_smul, hAr, hBr]
  have hIB : Complex.I • B = 0 := by
    have h1 : A + Complex.I • B = A + -(Complex.I • B) := by rw [← hFAB, ← hRF, hR]
    have h2 := add_left_cancel h1
    have h3 : (2 : ℝ) • (Complex.I • B) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h2]
      exact neg_add_cancel _
    exact (smul_eq_zero.1 h3).resolve_left two_ne_zero
  have hFA : F = A := by rw [hFAB, hIB, add_zero]
  have htp : toPhys F = r := rfl
  rw [htp, hFA, hA, LinearIsometryEquiv.norm_map, norm_complexify]

end Breakdown.Cert
