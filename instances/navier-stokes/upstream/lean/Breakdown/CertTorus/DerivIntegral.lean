import Breakdown.CertTorus.RegularStatements

open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.FarField

open Freq

namespace Internal.DerivIntegral

theorem cmul_apply (c : ℂ) (z : CSpace) : cmul c z = c • z := rfl

theorem norm_cmul_le (c : ℂ) : ‖cmul c‖ ≤ ‖c‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c) (fun z => by
    rw [cmul_apply, norm_smul])

theorem cmul_sub (c d : ℂ) : cmul c - cmul d = cmul (c - d) :=
  ContinuousLinearMap.ext fun z => by
    simp only [sub_apply, cmul_apply, sub_smul]

theorem continuous_cmul : Continuous cmul :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun c d => by
    rw [dist_eq_norm, dist_eq_norm, cmul_sub, NNReal.coe_one, one_mul]
    exact norm_cmul_le _).continuous

def multOp (c : Space → ℂ) : L2C →L[ℝ] L2C :=
  fieldOp (ContinuousLinearEquiv.refl ℝ Space) (fun ξ => cmul (c ξ))

theorem multOp_ae {c : Space → ℂ} (hc : Measurable c) {C : ℝ} (hC : ∀ ξ, ‖c ξ‖ ≤ C)
    (f : L2C) : (multOp c f : Space → CSpace) =ᵐ[volume] fun ξ => c ξ • f ξ := by
  have hm : AEStronglyMeasurable (fun ξ => cmul (c ξ)) volume :=
    continuous_cmul.comp_aestronglyMeasurable hc.aestronglyMeasurable
  have hb : ∀ ξ, ‖cmul (c ξ)‖ ≤ C := fun ξ => (norm_cmul_le _).trans (hC ξ)
  have h := fieldOpRealized_holds (ContinuousLinearEquiv.refl ℝ Space) _ C hm hb f
  filter_upwards [h] with ξ hξ
  rw [multOp, hξ]
  rfl

theorem continuous_monoSymbol {n : ℕ} (α : Fin n → Fin 3) : Continuous (monoSymbol α) := by
  unfold monoSymbol
  fun_prop

def truncSymbol {n : ℕ} (α : Fin n → Fin 3) (N : ℕ) (ξ : Space) : ℂ :=
  if ‖monoSymbol α ξ‖ ≤ N then monoSymbol α ξ else 0

def truncCut {n : ℕ} (α : Fin n → Fin 3) (N : ℕ) (ξ : Space) : ℂ :=
  if ‖monoSymbol α ξ‖ ≤ N then 1 else 0

theorem measurable_truncSymbol {n : ℕ} (α : Fin n → Fin 3) (N : ℕ) :
    Measurable (truncSymbol α N) :=
  Measurable.ite (measurableSet_le (continuous_monoSymbol α).measurable.norm measurable_const)
    (continuous_monoSymbol α).measurable measurable_const

theorem measurable_truncCut {n : ℕ} (α : Fin n → Fin 3) (N : ℕ) :
    Measurable (truncCut α N) :=
  Measurable.ite (measurableSet_le (continuous_monoSymbol α).measurable.norm measurable_const)
    measurable_const measurable_const

theorem norm_truncSymbol_le {n : ℕ} (α : Fin n → Fin 3) (N : ℕ) (ξ : Space) :
    ‖truncSymbol α N ξ‖ ≤ N := by
  unfold truncSymbol
  split_ifs with h
  · exact h
  · simp

theorem norm_truncCut_le {n : ℕ} (α : Fin n → Fin 3) (N : ℕ) (ξ : Space) :
    ‖truncCut α N ξ‖ ≤ 1 := by
  unfold truncCut
  split_ifs <;> simp

theorem truncate_eq {n : ℕ} (α : Fin n → Fin 3) (N : ℕ) (F G : ℝ → X) (a b : ℝ) (hab : a ≤ b)
    (hF : IntervalIntegrable F volume a b) (hG : IntervalIntegrable G volume a b)
    (hFG : ∀ s ∈ Ioo a b, IsDerivX α (F s) (G s)) :
    ∀ᵐ ξ ∂volume, truncCut α N ξ • symX (∫ s in a..b, G s) ξ =
      truncSymbol α N ξ • symX (∫ s in a..b, F s) ξ := by
  have hP := multOp_ae (measurable_truncSymbol α N) (norm_truncSymbol_le α N)
  have hQ := multOp_ae (measurable_truncCut α N) (norm_truncCut_le α N)
  let P : X →L[ℝ] L2C := multOp (truncSymbol α N) ∘L Sig.subtypeL
  let Q : X →L[ℝ] L2C := multOp (truncCut α N) ∘L Sig.subtypeL
  have hPx : ∀ x : X, P x = multOp (truncSymbol α N) (x : L2C) := fun x => rfl
  have hQx : ∀ x : X, Q x = multOp (truncCut α N) (x : L2C) := fun x => rfl
  have hpt : EqOn (fun s => P (F s)) (fun s => Q (G s)) (Ioo a b) := by
    intro s hs
    simp only [hPx, hQx]
    apply Lp.ext
    filter_upwards [hP (F s : L2C), hQ (G s : L2C), hFG s hs] with ξ h1 h2 h3
    rw [h1, h2]
    change truncSymbol α N ξ • symX (F s) ξ = truncCut α N ξ • symX (G s) ξ
    rw [h3]
    unfold truncSymbol truncCut
    split_ifs <;> simp
  have hint : P (∫ s in a..b, F s) = Q (∫ s in a..b, G s) := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm P hF,
      ← ContinuousLinearMap.intervalIntegral_comp_comm Q hG,
      intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo hpt
  rw [hPx, hQx] at hint
  filter_upwards [hP ((∫ s in a..b, F s : X) : L2C), hQ ((∫ s in a..b, G s : X) : L2C)]
    with ξ h1 h2
  change truncCut α N ξ • ((∫ s in a..b, G s : X) : L2C) ξ =
    truncSymbol α N ξ • ((∫ s in a..b, F s : X) : L2C) ξ
  rw [← h1, ← h2, hint]

end Internal.DerivIntegral

open Internal.DerivIntegral in
theorem derivIntegral_holds : DerivIntegral := by
  intro n α F G a b hab hF hG hFG
  have h := ae_all_iff.2 fun N : ℕ => truncate_eq α N F G a b hab hF hG hFG
  filter_upwards [h] with ξ hξ
  obtain ⟨N, hN⟩ := exists_nat_ge ‖monoSymbol α ξ‖
  have e := hξ N
  unfold truncSymbol truncCut at e
  rw [if_pos hN, if_pos hN, one_smul] at e
  exact e

end Breakdown.FarField
