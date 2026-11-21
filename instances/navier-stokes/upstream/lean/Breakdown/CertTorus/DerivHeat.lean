import Breakdown.CertTorus.RegularStatements
import Breakdown.FreqTr.Heat
import Breakdown.FreqTr.H1Consistency

open MeasureTheory Set Real Filter
open scoped ENNReal Nat

noncomputable section

namespace Breakdown.FarField

open Freq

namespace Internal.DerivHeat

theorem conjVec_smul (c : ℂ) (z : CSpace) : conjVec (c • z) = (starRingEnd ℂ c) • conjVec z := by
  ext i
  simp [conjVec]

theorem longitudinal_smul (ξ : Space) (c : ℂ) (z : CSpace) :
    longitudinal ξ (c • z) = c • longitudinal ξ z := by
  simp only [longitudinal, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    inner_smul_right]
  rw [mul_smul]
  exact smul_comm _ _ _

theorem mem_sig_of_symbol (h1 : FieldOpRealized) {s h : L2C} (hs : s ∈ Sig) (c : Space → ℂ)
    (hc : ∀ ξ, starRingEnd ℂ (c (-ξ)) = c ξ)
    (hh : (h : Space → CSpace) =ᵐ[volume] fun ξ => c ξ • s ξ) : h ∈ Sig := by
  rw [Freq.Internal.H1Consistency.mem_sig_iff] at hs ⊢
  obtain ⟨hs1, hs2⟩ := hs
  constructor
  · apply Lp.ext
    have hsr := Freq.Internal.H1Consistency.reflConj_ae h1 s
    rw [hs1] at hsr
    filter_upwards [Freq.Internal.H1Consistency.reflConj_ae h1 h,
      Freq.Internal.H1Consistency.ae_comp_neg hh, hsr, hh] with ξ e1 e2 e3 e4
    rw [e1, e2, e4, conjVec_smul, hc, e3]
  · apply Lp.ext
    have hsl := Freq.Internal.H1Consistency.longitudinal_ae h1 s
    rw [hs2] at hsl
    filter_upwards [Freq.Internal.H1Consistency.longitudinal_ae h1 h, hh, hsl,
      Lp.coeFn_zero CSpace 2 (volume : Measure Space)] with ξ e1 e2 e3 e4
    rw [e1, e2, longitudinal_smul, ← e3, e4]
    simp

theorem conj_monoSymbol_neg {n : ℕ} (α : Fin n → Fin 3) (ξ : Space) :
    starRingEnd ℂ (monoSymbol α (-ξ)) = monoSymbol α ξ := by
  unfold monoSymbol
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, PiLp.neg_apply]
  push_cast
  ring

theorem continuous_monoSymbol {n : ℕ} (α : Fin n → Fin 3) : Continuous (monoSymbol α) := by
  unfold monoSymbol
  exact continuous_finsetProd _ fun i _ => by fun_prop

theorem norm_monoSymbol_le {n : ℕ} (α : Fin n → Fin 3) (ξ : Space) :
    ‖monoSymbol α ξ‖ ≤ (2 * π * ‖ξ‖) ^ n := by
  unfold monoSymbol
  rw [norm_prod]
  calc ∏ i, ‖(((2 * π * ξ (α i) : ℝ) : ℂ) * Complex.I)‖ ≤ ∏ _i : Fin n, (2 * π * ‖ξ‖) := by
        refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
        have hk : |ξ (α i)| ≤ ‖ξ‖ := by
          simpa [Real.norm_eq_abs] using PiLp.norm_apply_le ξ (α i)
        exact mul_le_mul_of_nonneg_left hk (by positivity)
    _ = (2 * π * ‖ξ‖) ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem pow_mul_exp_le (n : ℕ) {t : ℝ} (ht : 0 < t) {r : ℝ} (hr : 0 ≤ r) :
    r ^ n * Real.exp (-(t * r ^ 2)) ≤ (n ! : ℝ) * t ^ (-((n : ℝ) / 2)) := by
  have hf : (1 : ℝ) ≤ n ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero n)
  have hA : 0 ≤ r ^ n * Real.exp (-(t * r ^ 2)) := by positivity
  have hB : 0 ≤ (n ! : ℝ) * t ^ (-((n : ℝ) / 2)) := by positivity
  have htr : 0 ≤ t * r ^ 2 := by positivity
  have hexp := Real.pow_div_factorial_le_exp (t * r ^ 2) htr n
  have hfp : (0 : ℝ) < n ! := by positivity
  rw [div_le_iff₀ hfp] at hexp
  have hsq : (t ^ (-((n : ℝ) / 2))) ^ 2 = (t ^ n)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_natCast, ← Real.rpow_neg ht.le]
    congr 1
    push_cast
    ring
  have htn : 0 < t ^ n := pow_pos ht n
  have key : t ^ n * (r ^ n * Real.exp (-(t * r ^ 2))) ^ 2 ≤ (n ! : ℝ) := by
    have e : t ^ n * (r ^ n * Real.exp (-(t * r ^ 2))) ^ 2 =
        (t * r ^ 2) ^ n * Real.exp (-(t * r ^ 2)) * Real.exp (-(t * r ^ 2)) := by
      rw [mul_pow, ← pow_mul, mul_pow, pow_two (Real.exp _)]
      ring
    rw [e]
    calc (t * r ^ 2) ^ n * Real.exp (-(t * r ^ 2)) * Real.exp (-(t * r ^ 2))
        ≤ (Real.exp (t * r ^ 2) * n !) * Real.exp (-(t * r ^ 2)) * 1 := by
          gcongr
          exact Real.exp_le_one_iff.2 (by linarith)
      _ = n ! := by rw [mul_one, mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]; simp
  have h2 : (r ^ n * Real.exp (-(t * r ^ 2))) ^ 2 ≤ ((n ! : ℝ) * t ^ (-((n : ℝ) / 2))) ^ 2 := by
    rw [mul_pow (n ! : ℝ), hsq]
    calc (r ^ n * Real.exp (-(t * r ^ 2))) ^ 2 ≤ (n ! : ℝ) / t ^ n := (le_div_iff₀' htn).2 key
      _ = (n ! : ℝ) * (t ^ n)⁻¹ := div_eq_mul_inv _ _
      _ ≤ (n ! : ℝ) ^ 2 * (t ^ n)⁻¹ := by
          gcongr
          nlinarith
  exact (pow_le_pow_iff_left₀ hA hB two_ne_zero).1 h2

theorem heatSymbol_bound {n : ℕ} (α : Fin n → Fin 3) {t : ℝ} (ht : 0 < t) (ξ : Space) :
    ‖monoSymbol α ξ * ((heatFactor t ξ : ℝ) : ℂ)‖ ≤ (n ! : ℝ) * t ^ (-((n : ℝ) / 2)) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Freq.Internal.Heat.heatFactor_pos t ξ)]
  have e : heatFactor t ξ = Real.exp (-(t * (2 * π * ‖ξ‖) ^ 2)) := by
    unfold heatFactor
    rw [max_eq_left ht.le]
    congr 1
    ring
  rw [e]
  calc ‖monoSymbol α ξ‖ * Real.exp (-(t * (2 * π * ‖ξ‖) ^ 2))
      ≤ (2 * π * ‖ξ‖) ^ n * Real.exp (-(t * (2 * π * ‖ξ‖) ^ 2)) := by
        gcongr
        exact norm_monoSymbol_le α ξ
    _ ≤ _ := pow_mul_exp_le n ht (by positivity)

theorem heat_symX (t : ℝ) (x : X) :
    ∀ᵐ ξ ∂volume, symX (heatX t x) ξ = heatFactor t ξ • symX x ξ := by
  unfold symX
  rw [Freq.Internal.Heat.heatX_coe fieldOpRealized_holds]
  exact Freq.Internal.Heat.heat_ae fieldOpRealized_holds t x

theorem heat_comm_deriv {n : ℕ} (α : Fin n → Fin 3) (t : ℝ) (x y : X) (h : IsDerivX α x y) :
    IsDerivX α (heatX t x) (heatX t y) := by
  unfold IsDerivX at h ⊢
  filter_upwards [h, heat_symX t x, heat_symX t y] with ξ e1 e2 e3
  rw [e3, e2, e1, smul_comm]

def heatDerivSymbol {n : ℕ} (α : Fin n → Fin 3) (t : ℝ) (ξ : Space) : ℂ :=
  monoSymbol α ξ * ((heatFactor t ξ : ℝ) : ℂ)

theorem continuous_heatDerivSymbol {n : ℕ} (α : Fin n → Fin 3) (t : ℝ) :
    Continuous (heatDerivSymbol α t) :=
  (continuous_monoSymbol α).mul
    (Complex.continuous_ofReal.comp (Freq.Internal.Heat.continuous_heatFactor t))

theorem conj_heatDerivSymbol_neg {n : ℕ} (α : Fin n → Fin 3) (t : ℝ) (ξ : Space) :
    starRingEnd ℂ (heatDerivSymbol α t (-ξ)) = heatDerivSymbol α t ξ := by
  unfold heatDerivSymbol
  rw [map_mul, conj_monoSymbol_neg, Complex.conj_ofReal]
  unfold heatFactor
  rw [norm_neg]

theorem symbol_realized (c : Space → ℂ) (hc : Continuous c) (K : ℝ) (hb : ∀ ξ, ‖c ξ‖ ≤ K)
    (f : L2C) :
    (fieldOp id (fun ξ => cmul (c ξ)) f : Space → CSpace) =ᵐ[volume] fun ξ => c ξ • f ξ :=
  fieldOpRealized_holds (ContinuousLinearEquiv.refl ℝ Space) (fun ξ => cmul (c ξ)) K
    (Freq.Internal.H1Consistency.continuous_cmul.comp hc).aestronglyMeasurable
    (fun ξ => (Freq.Internal.H1Consistency.norm_cmul_le _).trans (hb ξ)) f

def heatDerivL2 {n : ℕ} (α : Fin n → Fin 3) (t : ℝ) : L2C →L[ℝ] L2C :=
  fieldOp id (fun ξ => cmul (heatDerivSymbol α t ξ))

theorem heatDerivL2_ae {n : ℕ} (α : Fin n → Fin 3) {t : ℝ} (ht : 0 < t) (f : L2C) :
    (heatDerivL2 α t f : Space → CSpace) =ᵐ[volume] fun ξ => heatDerivSymbol α t ξ • f ξ :=
  symbol_realized _ (continuous_heatDerivSymbol α t) _ (fun ξ => heatSymbol_bound α ht ξ) f

theorem heatDerivL2_mem {n : ℕ} (α : Fin n → Fin 3) {t : ℝ} (ht : 0 < t) (x : X) :
    heatDerivL2 α t (x : L2C) ∈ Sig :=
  mem_sig_of_symbol fieldOpRealized_holds x.2 _ (conj_heatDerivSymbol_neg α t)
    (heatDerivL2_ae α ht (x : L2C))

theorem heatDerivL2_isDeriv {n : ℕ} (α : Fin n → Fin 3) {t : ℝ} (ht : 0 < t) (x : X) :
    IsDerivX α (heatX t x) ⟨heatDerivL2 α t (x : L2C), heatDerivL2_mem α ht x⟩ := by
  unfold IsDerivX
  have e0 : symX (⟨heatDerivL2 α t (x : L2C), heatDerivL2_mem α ht x⟩ : X) =
      ((heatDerivL2 α t (x : L2C) : L2C) : Space → CSpace) := rfl
  rw [e0]
  filter_upwards [heatDerivL2_ae α ht (x : L2C), heat_symX t x] with ξ e1 e2
  rw [e1, e2, heatDerivSymbol, mul_smul, Complex.coe_smul]
  rfl

theorem heatDerivL2_norm {n : ℕ} (α : Fin n → Fin 3) {t : ℝ} (ht : 0 < t) (x : X) :
    ‖heatDerivL2 α t (x : L2C)‖ ≤ (n ! : ℝ) * t ^ (-((n : ℝ) / 2)) * ‖(x : L2C)‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [heatDerivL2_ae α ht (x : L2C)] with ξ e
  rw [e, norm_smul]
  exact mul_le_mul_of_nonneg_right (heatSymbol_bound α ht ξ) (norm_nonneg _)

theorem heat_deriv_exists {n : ℕ} (α : Fin n → Fin 3) {t : ℝ} (ht : 0 < t) (x : X) :
    ∃ y, IsDerivX α (heatX t x) y ∧ ‖y‖ ≤ (n ! : ℝ) * t ^ (-((n : ℝ) / 2)) * ‖x‖ :=
  ⟨⟨heatDerivL2 α t (x : L2C), heatDerivL2_mem α ht x⟩, heatDerivL2_isDeriv α ht x,
    heatDerivL2_norm α ht x⟩

end Internal.DerivHeat

open Internal.DerivHeat in
theorem derivHeat_holds : DerivHeat :=
  ⟨fun _ α t x y h => heat_comm_deriv α t x y h,
    fun n => ⟨(n ! : ℝ), fun α _t ht x => heat_deriv_exists α ht x⟩⟩

end Breakdown.FarField
