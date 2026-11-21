import Breakdown.FreqTr.Realization
import Breakdown.FreqTr.PartialDecay
import Breakdown.FreqTr.EmbedMem

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Cert.Internal.SliceFields

open Freq Freq.Internal.PartialDecay

def derivOp (j : Fin 3) : L2C →L[ℝ] L2C := fieldOp id (fun ξ => cmul (derivSymbol j ξ))

theorem derivOp_ae (j : Fin 3) (f : L2C) :
    (derivOp j f : Space → CSpace) =ᵐ[volume] fun ξ => derivSymbol j ξ • f ξ :=
  symbolOp_ae fieldOpRealized_holds _ (measurable_derivSymbol j)
    (fun ξ => by rw [norm_derivSymbol]; exact coord_div_le_one ξ j) f

theorem star_derivSymbol_neg (j : Fin 3) (ξ : Space) :
    star (derivSymbol j (-ξ)) = derivSymbol j ξ := by
  simp [derivSymbol, Complex.conj_ofReal, Complex.conj_I]

theorem longitudinal_smul (ξ : Space) (c : ℂ) (w : CSpace) :
    longitudinal ξ (c • w) = c • longitudinal ξ w := by
  show ((‖ξ‖ ^ 2)⁻¹ : ℝ) • (inner ℂ (freqVec ξ) (c • w) • freqVec ξ) =
    c • (((‖ξ‖ ^ 2)⁻¹ : ℝ) • (inner ℂ (freqVec ξ) w • freqVec ξ))
  rw [inner_smul_right, mul_smul, smul_comm ((‖ξ‖ ^ 2)⁻¹ : ℝ) c]

theorem derivOp_mem (j : Fin 3) {g : L2C} (hg : g ∈ Sig) : derivOp j g ∈ Sig := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hg
  rw [LinearMap.mem_ker] at h1 h2
  have hr : reflConj g = g := by
    simp only [ContinuousLinearMap.coe_coe, sub_apply,
      ContinuousLinearMap.id_apply, sub_eq_zero] at h1
    exact h1
  have hl : fieldOp id longitudinal g = 0 := h2
  have hG : (g : Space → CSpace) =ᵐ[volume] fun ξ => conjVec (g (-ξ)) := by
    have := Freq.Internal.EmbedMem.reflConj_ae fieldOpRealized_holds g
    rw [hr] at this
    exact this
  have hselfAdj : reflConj (derivOp j g) = derivOp j g := by
    apply Lp.ext
    filter_upwards [Freq.Internal.EmbedMem.reflConj_ae fieldOpRealized_holds (derivOp j g),
      Freq.Internal.EmbedMem.ae_comp_neg (derivOp_ae j g), derivOp_ae j g, hG] with ξ ha hb hc hd
    rw [ha, hb, hc, hd]
    ext i
    simp [conjVec, ← star_derivSymbol_neg j ξ]
  have hlong : fieldOp id longitudinal (derivOp j g) = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    have h0 : (fieldOp id longitudinal g : Space → CSpace) =ᵐ[volume] 0 := by
      rw [hl]
      exact Lp.coeFn_zero _ _ _
    filter_upwards [Freq.Internal.EmbedMem.longitudinal_ae fieldOpRealized_holds (derivOp j g),
      Freq.Internal.EmbedMem.longitudinal_ae fieldOpRealized_holds g, derivOp_ae j g, h0]
      with ξ ha hb hc hd
    rw [hb] at hd
    rw [ha, hc, Pi.zero_apply, longitudinal_smul, hd, Pi.zero_apply, smul_zero]
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [LinearMap.mem_ker]
    show reflConj (derivOp j g) - derivOp j g = 0
    rw [hselfAdj, sub_self]
  · rw [LinearMap.mem_ker]
    exact hlong

def derivX (j : Fin 3) : X →L[ℝ] X := restrictX (derivOp j)

theorem derivX_coe (j : Fin 3) (x : X) : (derivX j x : L2C) = derivOp j x :=
  restrictX_coe (fun _ hg => derivOp_mem j hg) x

theorem partialX_eq (j : Fin 3) (x : X) : partialX j x = toPhys (derivX j x : L2C) := by
  rw [derivX_coe]
  rfl

theorem derivX_ae (j : Fin 3) (x : X) :
    ((derivX j x : X) : L2C) =ᵐ[volume] fun ξ => derivSymbol j ξ • (x : L2C) ξ := by
  rw [derivX_coe]
  exact derivOp_ae j _

theorem sum_norm_derivSymbol_sq {ξ : Space} (hξ : ξ ≠ 0) :
    ∑ j : Fin 3, ‖derivSymbol j ξ‖ ^ 2 = 1 := by
  simp_rw [norm_derivSymbol, div_pow, sq_abs]
  rw [← Finset.sum_div, ← norm_sq_space]
  exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.2 hξ))

theorem sum_norm_derivX_sq (x : X) : ∑ j : Fin 3, ‖derivX j x‖ ^ 2 = ‖x‖ ^ 2 := by
  calc ∑ j : Fin 3, ‖derivX j x‖ ^ 2 = ∑ j : Fin 3, ‖((derivX j x : X) : L2C)‖ ^ 2 := rfl
    _ = ∫ ξ, ∑ j : Fin 3, ‖((derivX j x : X) : L2C) ξ‖ ^ 2 := by
        rw [integral_finsetSum _ (fun j _ => integrable_norm_sq _)]
        exact Finset.sum_congr rfl (fun j _ => l2_norm_sq _)
    _ = ∫ ξ, ‖(x : L2C) ξ‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [ae_all_iff.2 fun j => derivX_ae j x, ae_ne_zero] with ξ hξ h0
        simp only [hξ, norm_smul, mul_pow]
        rw [← Finset.sum_mul, sum_norm_derivSymbol_sq h0, one_mul]
    _ = ‖(x : L2C)‖ ^ 2 := (l2_norm_sq _).symm
    _ = ‖x‖ ^ 2 := rfl

theorem halfSsp_derivX (j : Fin 3) {x k : X} (h : IsHalfSspOf x k) :
    IsHalfSspOf (derivX j x) (derivX j k) := by
  unfold IsHalfSspOf
  filter_upwards [derivX_ae j x, derivX_ae j k, h] with ξ h1 h2 h3
  rw [h2, h1, h3, smul_comm]

theorem derivSymbol_mul_self (j : Fin 3) (ξ : Space) :
    derivSymbol j ξ * derivSymbol j ξ = -(((ξ j : ℝ) : ℂ) ^ 2) / ((‖ξ‖ : ℝ) : ℂ) ^ 2 := by
  simp only [derivSymbol]
  calc Complex.I * ((ξ j : ℝ) : ℂ) / ((‖ξ‖ : ℝ) : ℂ) * (Complex.I * ((ξ j : ℝ) : ℂ) / ((‖ξ‖ : ℝ) : ℂ))
      = Complex.I ^ 2 * ((ξ j : ℝ) : ℂ) ^ 2 / ((‖ξ‖ : ℝ) : ℂ) ^ 2 := by ring
    _ = _ := by rw [Complex.I_sq]; ring

theorem sum_derivSymbol_mul_self {ξ : Space} (hξ : ξ ≠ 0) :
    ∑ j : Fin 3, derivSymbol j ξ * derivSymbol j ξ = -1 := by
  have hn : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hξ)
  have hn2 : ((‖ξ‖ : ℝ) : ℂ) ^ 2 = ∑ k, ((ξ k : ℝ) : ℂ) ^ 2 := by
    exact_mod_cast norm_sq_space ξ
  simp only [derivSymbol_mul_self, neg_div]
  rw [Finset.sum_neg_distrib, ← Finset.sum_div, ← hn2, div_self (pow_ne_zero 2 hn)]

theorem sum_derivX_derivX (k : X) : ∑ j : Fin 3, derivX j (derivX j k) = -k := by
  have e1 : ∀ j, ((derivX j (derivX j k) : X) : L2C) =ᵐ[volume]
      fun ξ => derivSymbol j ξ • derivSymbol j ξ • (k : L2C) ξ := by
    intro j
    filter_upwards [derivX_ae j (derivX j k), derivX_ae j k] with ξ a b
    rw [a, b]
  apply Subtype.ext
  rw [Submodule.coe_sum, Submodule.coe_neg]
  apply Lp.ext
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j : Fin 3 => ((derivX j (derivX j k) : X) : L2C)),
    Lp.coeFn_neg (k : L2C), ae_all_iff.2 e1, ae_ne_zero] with ξ hs hn he h0
  rw [hs, hn, Finset.sum_apply, Pi.neg_apply]
  simp only [he, smul_smul]
  rw [← Finset.sum_smul, sum_derivSymbol_mul_self h0, neg_one_smul]

end Breakdown.Cert.Internal.SliceFields
