import Breakdown.Cert.Basic
import Breakdown.Cert.SliceFieldsIsometry
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.ProjectionSpec

theorem longitudinal_eq (ξ : Space) (z : CSpace) :
    longitudinal ξ z = ((((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * inner ℂ (freqVec ξ) z) • freqVec ξ := by
  rw [mul_smul, Complex.coe_smul]
  rfl

theorem inner_freqVec_self (ξ : Space) :
    inner ℂ (freqVec ξ) (freqVec ξ) = ((‖ξ‖ : ℝ) : ℂ) ^ 2 := by
  rw [inner_self_eq_norm_sq_to_K, Freq.Internal.H1Consistency.norm_freqVec]
  rfl

theorem longitudinal_idem (ξ : Space) (z : CSpace) :
    longitudinal ξ (longitudinal ξ z) = longitudinal ξ z := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [longitudinal_eq, freqVec]
  · have hn : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hξ)
    rw [longitudinal_eq ξ (longitudinal ξ z), longitudinal_eq ξ z, inner_smul_right,
      inner_freqVec_self]
    congr 1
    push_cast
    field_simp

theorem inner_longitudinal_left (ξ : Space) (a b : CSpace) :
    inner ℂ (longitudinal ξ a) b = inner ℂ a (longitudinal ξ b) := by
  rw [longitudinal_eq, longitudinal_eq, inner_smul_left, inner_smul_right, map_mul,
    Complex.conj_ofReal, inner_conj_symm]
  ring

theorem real_inner_longitudinal_left (ξ : Space) (a b : CSpace) :
    inner ℝ (longitudinal ξ a) b = inner ℝ a (longitudinal ξ b) := by
  have e : ∀ u w : CSpace, inner ℝ u w = RCLike.re (inner ℂ u w) := fun u w => by
    simp only [PiLp.inner_apply, map_sum]
    rfl
  rw [e, e, inner_longitudinal_left]

theorem conjVec_longitudinal_neg (ξ : Space) (z : CSpace) :
    conjVec (longitudinal (-ξ) z) = longitudinal ξ (conjVec z) := by
  rw [longitudinal_eq, longitudinal_eq, norm_neg]
  ext i
  simp [conjVec, freqVec, complexifyVec, PiLp.inner_apply, map_sum, map_mul, Complex.conj_ofReal]

theorem fieldOp_longitudinal_ae (f : L2C) :
    (fieldOp id longitudinal f : Space → CSpace) =ᵐ[volume] fun ξ => longitudinal ξ (f ξ) :=
  Freq.Internal.H1Consistency.longitudinal_ae fieldOpRealized_holds f

theorem fieldOp_solenoidal :
    fieldOp id solenoidalSymbol = ContinuousLinearMap.id ℝ L2C - fieldOp id longitudinal := by
  apply fieldOp_eq_of_isRealizedBy
  intro f
  have e : (ContinuousLinearMap.id ℝ L2C - fieldOp id longitudinal) f = f - fieldOp id longitudinal f :=
    rfl
  rw [e]
  filter_upwards [Lp.coeFn_sub f (fieldOp id longitudinal f), fieldOp_longitudinal_ae f] with ξ h1 h2
  rw [h1, Pi.sub_apply, h2]
  rfl

theorem fieldOp_longitudinal_idem (f : L2C) :
    fieldOp id longitudinal (fieldOp id longitudinal f) = fieldOp id longitudinal f := by
  apply Lp.ext
  filter_upwards [fieldOp_longitudinal_ae (fieldOp id longitudinal f), fieldOp_longitudinal_ae f]
    with ξ h1 h2
  rw [h1, h2, longitudinal_idem]

theorem reflConj_fieldOp_longitudinal (f : L2C) :
    reflConj (fieldOp id longitudinal f) = fieldOp id longitudinal (reflConj f) := by
  apply Lp.ext
  filter_upwards [Freq.Internal.H1Consistency.reflConj_ae fieldOpRealized_holds (fieldOp id longitudinal f),
    Freq.Internal.H1Consistency.ae_comp_neg (fieldOp_longitudinal_ae f),
    fieldOp_longitudinal_ae (reflConj f),
    Freq.Internal.H1Consistency.reflConj_ae fieldOpRealized_holds f] with ξ h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  exact conjVec_longitudinal_neg ξ _

theorem inner_fieldOp_longitudinal (a b : L2C) :
    inner ℝ (fieldOp id longitudinal a) b = inner ℝ a (fieldOp id longitudinal b) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fieldOp_longitudinal_ae a, fieldOp_longitudinal_ae b] with ξ h1 h2
  rw [h1, h2]
  exact real_inner_longitudinal_left ξ _ _

theorem fieldOp_longitudinal_of_mem {x : L2C} (hx : x ∈ Sig) : fieldOp id longitudinal x = 0 :=
  ((Freq.Internal.H1Consistency.mem_sig_iff x).1 hx).2

theorem reflConj_of_mem {x : L2C} (hx : x ∈ Sig) : reflConj x = x :=
  ((Freq.Internal.H1Consistency.mem_sig_iff x).1 hx).1

theorem sub_longitudinal_mem (g : L2C) (hg : reflConj g = g) :
    g - fieldOp id longitudinal g ∈ Sig := by
  rw [Freq.Internal.H1Consistency.mem_sig_iff]
  refine ⟨?_, ?_⟩
  · rw [map_sub, reflConj_fieldOp_longitudinal, hg]
  · rw [map_sub, fieldOp_longitudinal_idem, sub_self]

def projRaw : L2R →L[ℝ] L2C := fieldOp id solenoidalSymbol ∘L freqTrR ∘L complexify

theorem projRaw_apply (F : L2R) :
    projRaw F = freqTrR (complexify F) - fieldOp id longitudinal (freqTrR (complexify F)) := by
  show fieldOp id solenoidalSymbol (freqTrR (complexify F)) = _
  rw [fieldOp_solenoidal]
  rfl

theorem projRaw_mem (F : L2R) : projRaw F ∈ Sig := by
  rw [projRaw_apply]
  exact sub_longitudinal_mem _ (freqTrConjSym fieldOpRealized_holds F)

def projCLM : L2R →L[ℝ] HBar := projRaw.codRestrict Sig projRaw_mem

theorem projCLM_spec : ProjSpec projCLM := fun _ => rfl

theorem norm_freqTrR (g : L2C) : ‖freqTrR g‖ = ‖g‖ :=
  freqTrL2.norm_map g

theorem freqTrR_complexify_toPhys {F : L2C} (hF : F ∈ Sig) : freqTrR (complexify (toPhys F)) = F := by
  have hR : reflConj F = F := reflConj_of_mem hF
  set f : L2C := freqTrL2.symm F
  set A : L2C := freqTrL2 (complexify (realPart f))
  set B : L2C := freqTrL2 (complexify (Internal.SliceFieldsIsometry.imagL f))
  have hFAB : F = A + Complex.I • B := by
    have h0 : F = freqTrL2 f := (freqTrL2.apply_symm_apply F).symm
    rw [h0, Internal.SliceFieldsIsometry.split f, map_add, map_smul]
  have hA : reflConj A = A := freqTrConjSym fieldOpRealized_holds _
  have hB : reflConj B = B := freqTrConjSym fieldOpRealized_holds _
  have hRF : reflConj F = A - Complex.I • B := by
    rw [hFAB, map_add, Internal.SliceFieldsIsometry.reflConj_I_smul, hA, hB, sub_eq_add_neg]
  have h2 : Complex.I • B = -(Complex.I • B) := by
    have h1 : A + Complex.I • B = A - Complex.I • B := by rw [← hFAB, ← hRF, hR]
    rw [sub_eq_add_neg] at h1
    exact add_left_cancel h1
  have hIB : Complex.I • B = 0 := by
    have h3 : (2 : ℝ) • (Complex.I • B) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h2]
      exact neg_add_cancel _
    exact (smul_eq_zero.1 h3).resolve_left two_ne_zero
  have hFA : F = A := by rw [hFAB, hIB, add_zero]
  have htp : toPhys F = realPart f := rfl
  rw [htp]
  exact hFA.symm

def transformIsometry : L2R →ₗᵢ[ℝ] L2C where
  toLinearMap := ((freqTrR ∘L complexify : L2R →L[ℝ] L2C) : L2R →ₗ[ℝ] L2C)
  norm_map' F := by
    show ‖freqTrR (complexify F)‖ = ‖F‖
    rw [norm_freqTrR, Internal.SliceFieldsIsometry.norm_complexify]

theorem inner_transform (F G : L2R) :
    inner ℝ (freqTrR (complexify F)) (freqTrR (complexify G)) = inner ℝ F G :=
  transformIsometry.inner_map_map F G

theorem norm_solenoidalSymbol_le (ξ : Space) : ‖solenoidalSymbol ξ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    rw [one_mul]
    exact Freq.Internal.NiceDense.norm_proj_le ξ z

theorem aesm_solenoidalSymbol : AEStronglyMeasurable solenoidalSymbol volume :=
  aestronglyMeasurable_const.sub Freq.Internal.H1Consistency.aesm_longitudinal

end Internal.ProjectionSpec

open Internal.ProjectionSpec

theorem exists_projSpec : ∃ T, ProjSpec T := ⟨projCLM, projCLM_spec⟩

theorem solProj_spec : ProjSpec solProj := by
  have h := exists_projSpec
  rw [solProj, dif_pos h]
  exact h.choose_spec

theorem solProj_coe (F : L2R) :
    (solProj F : L2C) = freqTrR (complexify F) - fieldOp id longitudinal (freqTrR (complexify F)) := by
  rw [solProj_spec F, fieldOp_solenoidal]
  rfl

theorem norm_toPhysH (x : HBar) : ‖toPhysH x‖ = ‖x‖ :=
  norm_toPhys_of_mem_sig x x.2

theorem norm_solProj_le (F : L2R) : ‖solProj F‖ ≤ ‖F‖ := by
  have h := norm_fieldOp_id_apply_le aesm_solenoidalSymbol norm_solenoidalSymbol_le (freqTrR (complexify F))
  rw [one_mul, norm_freqTrR, Internal.SliceFieldsIsometry.norm_complexify, ← solProj_spec F] at h
  exact h

theorem toPhysH_apply (x : HBar) : toPhysH x = toPhys (x : L2C) := rfl

theorem inner_solProj (F : L2R) (x : HBar) : inner ℝ (solProj F) x = inner ℝ F (toPhysH x) := by
  change inner ℝ (solProj F : L2C) (x : L2C) = _
  rw [solProj_coe, inner_sub_left, inner_fieldOp_longitudinal, fieldOp_longitudinal_of_mem x.2,
    inner_zero_right, sub_zero, toPhysH_apply, ← inner_transform, freqTrR_complexify_toPhys x.2]

theorem solProj_toPhysH (x : HBar) : solProj (toPhysH x) = x := by
  apply Subtype.ext
  rw [solProj_coe, toPhysH_apply, freqTrR_complexify_toPhys x.2, fieldOp_longitudinal_of_mem x.2,
    sub_zero]

theorem toPhysH_solField_test {φ : Space → Space} (hφ : IsTestField φ) :
    toPhysH (solField φ) = toLpOrZero 2 φ := by
  have hH : IsH1Field φ :=
    ⟨hφ.1, hφ.2.2, Freq.Internal.BilinTestFormula.test_memLp hφ 2,
      fun k => Freq.Internal.BilinTestFormula.partialField_memLp hφ k 2⟩
  have hs := Freq.Internal.H1Consistency.hat_mem_sig fieldOpRealized_holds
    (freqTrConjSym fieldOpRealized_holds) hH
  rw [toPhysH_apply, solField, solProj_coe, fieldOp_longitudinal_of_mem hs, sub_zero]
  exact Lp.ext (Freq.Internal.H1Consistency.toPhys_freqTr_complexify _)

theorem inner_solField_test (φ : Space → Space) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hdiv : ∀ y, divergenceAt φ y = 0) (F : Space → Space) (hF : MemLp F 2) :
    inner ℝ (solField F) (solField φ) = ∫ y, inner ℝ (F y) (φ y) := by
  have ht : IsTestField φ := ⟨hφ, hc, hdiv⟩
  rw [solField, inner_solProj, toPhysH_solField_test ht, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Freq.Internal.H1Consistency.toLpOrZero_ae hF,
    Freq.Internal.H1Consistency.toLpOrZero_ae (Freq.Internal.BilinTestFormula.test_memLp ht 2)]
    with y h1 h2
  rw [h1, h2]

end Breakdown.Cert
