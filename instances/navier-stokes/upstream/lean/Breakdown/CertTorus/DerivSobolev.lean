import Breakdown.CertTorus.RegularStatements

open MeasureTheory Set Real Filter
open scoped ENNReal

noncomputable section

namespace Breakdown.FarField

open Freq SmoothFlow

namespace Internal.MonoSymbolCalculus

theorem norm_monoSymbol_sq {n : ℕ} (α : Fin n → Fin 3) (ξ : Space) :
    ‖monoSymbol α ξ‖ ^ 2 = ∏ i, (2 * π * ξ (α i)) ^ 2 := by
  rw [monoSymbol, norm_prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem sum_norm_monoSymbol_sq (n : ℕ) (ξ : Space) :
    ∑ α : Fin n → Fin 3, ‖monoSymbol α ξ‖ ^ 2 = (2 * π) ^ (2 * n) * ‖ξ‖ ^ (2 * n) := by
  simp_rw [norm_monoSymbol_sq]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (j : Fin 3) => (2 * π * ξ j) ^ 2), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, pow_mul, pow_mul, ← mul_pow]
  congr 1
  rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.norm_eq_abs, sq_abs, mul_pow]

theorem norm_monoSymbol_sq_le {n : ℕ} (α : Fin n → Fin 3) (ξ : Space) :
    ‖monoSymbol α ξ‖ ^ 2 ≤ (2 * π) ^ (2 * n) * ‖ξ‖ ^ (2 * n) := by
  rw [← sum_norm_monoSymbol_sq]
  exact Finset.single_le_sum (f := fun β : Fin n → Fin 3 => ‖monoSymbol β ξ‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ α)

theorem conj_monoSymbol_neg {n : ℕ} (α : Fin n → Fin 3) (ξ : Space) :
    starRingEnd ℂ (monoSymbol α (-ξ)) = monoSymbol α ξ := by
  rw [monoSymbol, monoSymbol, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I, PiLp.neg_apply]
  push_cast
  ring

theorem continuous_monoSymbol {n : ℕ} (α : Fin n → Fin 3) : Continuous (monoSymbol α) := by
  unfold monoSymbol
  fun_prop

theorem conjVec_smul (c : ℂ) (z : CSpace) : conjVec (c • z) = starRingEnd ℂ c • conjVec z := by
  ext i
  simp [conjVec]

theorem longitudinal_smul (ξ : Space) (c : ℂ) (z : CSpace) :
    longitudinal ξ (c • z) = c • longitudinal ξ z := by
  rw [Freq.Internal.H1Consistency.longitudinal_apply, Freq.Internal.H1Consistency.longitudinal_apply,
    inner_smul_right, mul_smul, smul_comm ((‖ξ‖ ^ 2)⁻¹ : ℝ) c]

theorem lintegral_enorm_sq_eq (f : L2C) :
    ∫⁻ ξ, ‖(f : Space → CSpace) ξ‖ₑ ^ 2 = ENNReal.ofReal (‖f‖ ^ 2) := by
  rw [Lp.norm_def, ← ENNReal.toReal_pow, ENNReal.ofReal_toReal (ENNReal.pow_ne_top (Lp.eLpNorm_ne_top f)),
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem memLp_monoSymbol_smul {n : ℕ} (α : Fin n → Fin 3) (x : X) (hx : homSob n x < ⊤) :
    MemLp (fun ξ => monoSymbol α ξ • symX x ξ) 2 volume := by
  have hg : AEStronglyMeasurable (symX x) volume := (Lp.aestronglyMeasurable (x : L2C))
  have hm : AEStronglyMeasurable (fun ξ => monoSymbol α ξ • symX x ξ) volume :=
    (continuous_monoSymbol α).aestronglyMeasurable.smul hg
  refine ⟨hm, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  suffices key : ∫⁻ ξ, ‖monoSymbol α ξ • symX x ξ‖ₑ ^ (2 : ℕ) < ⊤ by simpa using key
  have hle : ∀ ξ, ‖monoSymbol α ξ • symX x ξ‖ₑ ^ 2 ≤
      ENNReal.ofReal ((2 * π) ^ (2 * n)) * (ENNReal.ofReal (‖ξ‖ ^ (2 * n)) * ‖symX x ξ‖ₑ ^ 2) := by
    intro ξ
    rw [enorm_smul, mul_pow, ← mul_assoc, ← ofReal_norm (monoSymbol α ξ),
      ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    gcongr
    exact norm_monoSymbol_sq_le α ξ
  calc ∫⁻ ξ, ‖monoSymbol α ξ • symX x ξ‖ₑ ^ 2
      ≤ ∫⁻ ξ, ENNReal.ofReal ((2 * π) ^ (2 * n)) *
          (ENNReal.ofReal (‖ξ‖ ^ (2 * n)) * ‖symX x ξ‖ₑ ^ 2) := lintegral_mono hle
    _ = ENNReal.ofReal ((2 * π) ^ (2 * n)) * homSob n x := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rfl
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hx

theorem monoSymbol_smul_mem_sig {n : ℕ} (α : Fin n → Fin 3) (x : X) (y : L2C)
    (hy : (y : Space → CSpace) =ᵐ[volume] fun ξ => monoSymbol α ξ • symX x ξ) : y ∈ Sig := by
  have hx := (Freq.Internal.H1Consistency.mem_sig_iff (x : L2C)).1 x.2
  rw [Freq.Internal.H1Consistency.mem_sig_iff]
  obtain ⟨h1, h2⟩ := hx
  constructor
  · apply Lp.ext
    have hr := Freq.Internal.H1Consistency.reflConj_ae fieldOpRealized_holds (x : L2C)
    rw [h1] at hr
    filter_upwards [Freq.Internal.H1Consistency.reflConj_ae fieldOpRealized_holds y,
      Freq.Internal.H1Consistency.ae_comp_neg hy, hr, hy] with ξ e1 e2 e3 e4
    rw [e1, e2, e4, conjVec_smul, conj_monoSymbol_neg]
    unfold symX
    rw [← e3]
  · apply Lp.ext
    have hl := Freq.Internal.H1Consistency.longitudinal_ae fieldOpRealized_holds (x : L2C)
    rw [h2] at hl
    filter_upwards [Freq.Internal.H1Consistency.longitudinal_ae fieldOpRealized_holds y, hy, hl,
      Lp.coeFn_zero CSpace 2 (volume : Measure Space)] with ξ e1 e2 e3 e4
    rw [e1, e2, longitudinal_smul, e4]
    unfold symX
    rw [← e3, e4]
    simp

theorem exists_deriv {n : ℕ} (α : Fin n → Fin 3) (x : X) (hx : homSob n x < ⊤) :
    ∃ y, IsDerivX α x y := by
  have hf := memLp_monoSymbol_smul α x hx
  refine ⟨⟨hf.toLp _, monoSymbol_smul_mem_sig α x _ hf.coeFn_toLp⟩, ?_⟩
  exact hf.coeFn_toLp

theorem weight_mul_eq_sum (n : ℕ) (ξ : Space) (z : CSpace) :
    ENNReal.ofReal (‖ξ‖ ^ (2 * n)) * ‖z‖ₑ ^ 2 = ENNReal.ofReal (((2 * π) ^ (2 * n))⁻¹) *
      ∑ α : Fin n → Fin 3, ‖monoSymbol α ξ • z‖ₑ ^ 2 := by
  have hK : (0 : ℝ) < (2 * π) ^ (2 * n) := by positivity
  have hs : ∑ α : Fin n → Fin 3, ‖monoSymbol α ξ • z‖ₑ ^ 2 =
      ENNReal.ofReal ((2 * π) ^ (2 * n) * ‖ξ‖ ^ (2 * n)) * ‖z‖ₑ ^ 2 := by
    rw [← sum_norm_monoSymbol_sq, ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [enorm_smul, mul_pow, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [hs, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hK.le), ← mul_assoc,
    inv_mul_cancel₀ hK.ne', one_mul]

theorem homSob_eq_sum (n : ℕ) (x : X) :
    homSob n x = ENNReal.ofReal (((2 * π) ^ (2 * n))⁻¹) *
      ∑ α : Fin n → Fin 3, ∫⁻ ξ, ‖monoSymbol α ξ • symX x ξ‖ₑ ^ 2 := by
  have hg : AEStronglyMeasurable (symX x) volume := (Lp.aestronglyMeasurable (x : L2C))
  have e : homSob n x = ∫⁻ ξ, ENNReal.ofReal (((2 * π) ^ (2 * n))⁻¹) *
      ∑ α : Fin n → Fin 3, ‖monoSymbol α ξ • symX x ξ‖ₑ ^ 2 :=
    lintegral_congr fun ξ => weight_mul_eq_sum n ξ (symX x ξ)
  have hmeas : ∀ α : Fin n → Fin 3,
      AEMeasurable (fun ξ => ‖monoSymbol α ξ • symX x ξ‖ₑ ^ 2) volume := fun α =>
    ((continuous_monoSymbol α).aestronglyMeasurable.smul hg).enorm.pow_const 2
  rw [e, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  exact lintegral_finsetSum' _ fun α _ => hmeas α

end Internal.MonoSymbolCalculus

open Internal.MonoSymbolCalculus in
theorem derivSobolev_holds : DerivSobolev := by
  intro n
  refine ⟨((2 * π) ^ (2 * n))⁻¹ * 3 ^ n, fun x => ⟨fun hx α => exists_deriv α x hx, fun B hB => ?_⟩⟩
  have hK : (0 : ℝ) ≤ ((2 * π) ^ (2 * n))⁻¹ := by positivity
  have hterm : ∀ α : Fin n → Fin 3, ∫⁻ ξ, ‖monoSymbol α ξ • symX x ξ‖ₑ ^ 2 ≤ ENNReal.ofReal (B ^ 2) := by
    intro α
    obtain ⟨y, hy, hyB⟩ := hB α
    have e : ∫⁻ ξ, ‖monoSymbol α ξ • symX x ξ‖ₑ ^ 2 = ∫⁻ ξ, ‖symX y ξ‖ₑ ^ 2 :=
      lintegral_congr_ae (hy.mono fun ξ h => by simp only [h])
    rw [e, symX, lintegral_enorm_sq_eq]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hyB 2)
  rw [homSob_eq_sum]
  calc ENNReal.ofReal (((2 * π) ^ (2 * n))⁻¹) * ∑ α : Fin n → Fin 3, ∫⁻ ξ, ‖monoSymbol α ξ • symX x ξ‖ₑ ^ 2
      ≤ ENNReal.ofReal (((2 * π) ^ (2 * n))⁻¹) * ∑ _α : Fin n → Fin 3, ENNReal.ofReal (B ^ 2) := by
        gcongr with α
        exact hterm α
    _ = ENNReal.ofReal (((2 * π) ^ (2 * n))⁻¹ * 3 ^ n * B ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul hK]
        push_cast
        ring_nf

end Breakdown.FarField
