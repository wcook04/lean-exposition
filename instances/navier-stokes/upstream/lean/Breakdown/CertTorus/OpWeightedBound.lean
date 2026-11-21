import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown.FarField

private lemma norm_tensorShift_le {F : ℝ → Space → Fin 3 → Fin 3 → ℝ} {γ A : ℝ}
    (hF : WeightedBound F γ A) (s τ : ℝ) (hτ : 0 < τ) (z : Space) :
    ‖tensorShift F s τ z‖ ≤ A * (1 + ‖z‖ / Real.sqrt (1 + τ)) ^ (-γ) := by
  have ha : 0 < Real.sqrt (1 + τ) := Real.sqrt_pos.2 (by linarith)
  have h := hF (s - Real.log (1 + τ)) ((Real.sqrt (1 + τ))⁻¹ • z)
  have hn : ‖(Real.sqrt (1 + τ))⁻¹ • z‖ = ‖z‖ / Real.sqrt (1 + τ) := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg ha.le, inv_mul_eq_div]
  rw [hn] at h
  have hb : 0 < 1 + ‖z‖ / Real.sqrt (1 + τ) := by positivity
  have hp : 0 < (1 + ‖z‖ / Real.sqrt (1 + τ)) ^ γ := Real.rpow_pos_of_pos hb γ
  unfold tensorShift
  rw [Real.rpow_neg hb.le, ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
  exact h

private lemma norm_kernel_coeff_le {C γ A τ : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i j k : Fin 3, ∀ τ : ℝ, ∀ x : Space, 0 < τ →
      |lerayKernel i j k τ x| ≤ C / (‖x‖ + Real.sqrt τ) ^ 4)
    {G : Space → Fin 3 → Fin 3 → ℝ} (hτ : 0 < τ)
    (hG : ∀ z, ‖G z‖ ≤ A * (1 + ‖z‖ / Real.sqrt (1 + τ)) ^ (-γ)) (i : Fin 3) (y z : Space) :
    ‖∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * G z j k‖ ≤
      9 * C * A * (((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹ * (1 + ‖z‖ / Real.sqrt (1 + τ)) ^ (-γ)) := by
  have hterm : ∀ j k : Fin 3, ‖lerayKernel i j k τ (y - z) * G z j k‖ ≤
      C * A * (((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹ * (1 + ‖z‖ / Real.sqrt (1 + τ)) ^ (-γ)) := by
    intro j k
    have h1 := hC i j k τ (y - z) hτ
    have h2 : ‖G z j k‖ ≤ ‖G z‖ := (norm_le_pi_norm (G z j) k).trans (norm_le_pi_norm (G z) j)
    rw [norm_mul, Real.norm_eq_abs]
    calc |lerayKernel i j k τ (y - z)| * ‖G z j k‖
        ≤ (C / (‖y - z‖ + Real.sqrt τ) ^ 4) * (A * (1 + ‖z‖ / Real.sqrt (1 + τ)) ^ (-γ)) :=
          mul_le_mul h1 (h2.trans (hG z)) (norm_nonneg _) (div_nonneg hC0 (by positivity))
      _ = _ := by rw [div_eq_mul_inv]; ring
  calc ‖∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * G z j k‖
      ≤ ∑ j : Fin 3, ∑ k : Fin 3, ‖lerayKernel i j k τ (y - z) * G z j k‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j : Fin 3, ∑ k : Fin 3,
          C * A * (((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹ * (1 + ‖z‖ / Real.sqrt (1 + τ)) ^ (-γ)) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hterm j k
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

private lemma norm_kernelConv_le {C γ A τ : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i j k : Fin 3, ∀ τ : ℝ, ∀ x : Space, 0 < τ →
      |lerayKernel i j k τ x| ≤ C / (‖x‖ + Real.sqrt τ) ^ 4)
    {G : Space → Fin 3 → Fin 3 → ℝ} (hτ : 0 < τ)
    (hG : ∀ z, ‖G z‖ ≤ A * (1 + ‖z‖ / Real.sqrt (1 + τ)) ^ (-γ)) (y : Space)
    (hInt : Integrable (fun z : Space =>
      ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹ * (1 + ‖z‖ / Real.sqrt (1 + τ)) ^ (-γ))) :
    ‖kernelConv τ G y‖ ≤ 27 * C * A * kernelWeightIntegral γ τ y := by
  have hci : ∀ i : Fin 3,
      ‖∫ z, ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * G z j k‖ ≤
        9 * C * A * kernelWeightIntegral γ τ y := by
    intro i
    rw [kernelWeightIntegral, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hInt.const_mul _)
      (ae_of_all _ fun z => norm_kernel_coeff_le hC0 hC hτ hG i y z)
  unfold kernelConv
  refine (norm_sum_le _ _).trans ?_
  have hsum : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      ‖(∫ z, ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * G z j k) • unitVector i‖ ≤
        9 * C * A * kernelWeightIntegral γ τ y := by
    intro i _
    rw [norm_smul, unitVector, PiLp.norm_single, norm_one, mul_one]
    exact hci i
  refine (Finset.sum_le_sum hsum).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

private lemma norm_profileOp_le (β c γ : ℝ) (F : ℝ → Space → Fin 3 → Fin 3 → ℝ) (s : ℝ)
    (y : Space) (g : ℝ → ℝ) (hg : IntegrableOn g (Ioi 0))
    (hbd : ∀ τ : ℝ, 0 < τ → ‖kernelConv τ (tensorShift F s τ) y‖ ≤ c * kernelWeightIntegral γ τ y)
    (hle : ∀ τ : ℝ, 0 < τ → (1 + τ) ^ (-β) * (c * kernelWeightIntegral γ τ y) ≤ g τ) :
    ‖profileOp β F s y‖ ≤ ∫ τ in Ioi (0 : ℝ), g τ := by
  unfold profileOp
  rw [norm_neg]
  refine norm_integral_le_of_norm_le hg ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono fun τ hτ => ?_
  have hτ' : 0 < τ := hτ
  have hw : 0 ≤ (1 + τ) ^ (-β) := Real.rpow_nonneg (by linarith) _
  rw [norm_smul, Real.norm_of_nonneg hw]
  exact (mul_le_mul_of_nonneg_left (hbd τ hτ') hw).trans (hle τ hτ')

theorem opWeightedBound_of_split :
    InnerSplitBound → OuterFarBound → OuterNearBound → SmallTimeIntegrable → OpWeightedBound := by
  intro hIn hOF hON hST hK n hn γ hγ hγ3 hγn
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ i j k : Fin 3, ∀ τ : ℝ, ∀ x : Space, 0 < τ →
      |lerayKernel i j k τ x| ≤ C / (‖x‖ + Real.sqrt τ) ^ 4 := by
    obtain ⟨C₀, hC₀⟩ := hK
    exact ⟨max C₀ 0, le_max_right _ _, fun i j k τ x hτ =>
      (hC₀ i j k τ x hτ).trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))⟩
  obtain ⟨Ci, hCi⟩ := hIn γ hγ hγ3
  obtain ⟨KF, hKF⟩ := hOF n hn γ hγ hγn
  obtain ⟨KN, hKN⟩ := hON n hn γ hγ
  have hS := hST n
  have hCi0 : 0 ≤ Ci := by
    have h := (hCi 1 one_pos 0).2.1
    have hnn : 0 ≤ kernelWeightIntegral γ 1 0 := by
      unfold kernelWeightIntegral
      exact integral_nonneg fun z => by positivity
    rw [Real.sqrt_one, inv_one, mul_one] at h
    linarith
  have hm0 : 0 ≤ min γ ((n : ℝ) + 1) := le_min hγ (by positivity)
  obtain ⟨M, hM0, hSM, hKM⟩ : ∃ M : ℝ, 0 ≤ M ∧
      (∫ τ in Ioi (0 : ℝ), (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * (Real.sqrt τ)⁻¹) ≤ M ∧
      KF + KN ≤ M := by
    refine ⟨max (∫ τ in Ioi (0 : ℝ), (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * (Real.sqrt τ)⁻¹) 0 +
      max KF 0 + max KN 0, ?_, ?_, ?_⟩
    · have h1 := le_max_right (∫ τ in Ioi (0 : ℝ), (1 + τ) ^ (-(1 + (n : ℝ) / 2)) *
        (Real.sqrt τ)⁻¹) 0
      have h2 := le_max_right KF 0
      have h3 := le_max_right KN 0
      linarith
    · have h1 := le_max_left (∫ τ in Ioi (0 : ℝ), (1 + τ) ^ (-(1 + (n : ℝ) / 2)) *
        (Real.sqrt τ)⁻¹) 0
      have h2 := le_max_right KF 0
      have h3 := le_max_right KN 0
      linarith
    · have h1 := le_max_right (∫ τ in Ioi (0 : ℝ), (1 + τ) ^ (-(1 + (n : ℝ) / 2)) *
        (Real.sqrt τ)⁻¹) 0
      have h2 := le_max_left KF 0
      have h3 := le_max_left KN 0
      linarith
  refine ⟨27 * C * Ci * 2 ^ min γ ((n : ℝ) + 1) * M,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) hCi0)
      (Real.rpow_nonneg (by norm_num) _)) hM0, ?_⟩
  intro F A hF s y
  have hA : 0 ≤ A :=
    (mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _)).trans (hF 0 0)
  have hcA : 0 ≤ 27 * C * A := mul_nonneg (mul_nonneg (by norm_num) hC0) hA
  have hP : 0 ≤ 27 * C * A * Ci := mul_nonneg hcA hCi0
  have hconv : ∀ τ : ℝ, 0 < τ →
      ‖kernelConv τ (tensorShift F s τ) y‖ ≤ 27 * C * A * kernelWeightIntegral γ τ y :=
    fun τ hτ => norm_kernelConv_le hC0 hC hτ (fun z => norm_tensorShift_le hF s τ hτ z) y
      (hCi τ hτ y).1
  have hβ : ∀ τ : ℝ, 0 < τ → 0 ≤ (1 + τ) ^ (-(1 + (n : ℝ) / 2)) :=
    fun τ hτ => Real.rpow_nonneg (by linarith) _
  have hsmall : ‖profileOp (1 + (n : ℝ) / 2) F s y‖ ≤ 27 * C * A * Ci *
      ∫ τ in Ioi (0 : ℝ), (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * (Real.sqrt τ)⁻¹ := by
    have hpt : ∀ τ : ℝ, 0 < τ → (1 + τ) ^ (-(1 + (n : ℝ) / 2)) *
        (27 * C * A * kernelWeightIntegral γ τ y) ≤
          27 * C * A * Ci * ((1 + τ) ^ (-(1 + (n : ℝ) / 2)) * (Real.sqrt τ)⁻¹) := by
      intro τ hτ
      calc (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * (27 * C * A * kernelWeightIntegral γ τ y)
          ≤ (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * (27 * C * A * (Ci * (Real.sqrt τ)⁻¹)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hCi τ hτ y).2.1 hcA) (hβ τ hτ)
        _ = _ := by ring
    have h : ‖profileOp (1 + (n : ℝ) / 2) F s y‖ ≤ ∫ τ in Ioi (0 : ℝ),
        27 * C * A * Ci * ((1 + τ) ^ (-(1 + (n : ℝ) / 2)) * (Real.sqrt τ)⁻¹) :=
      norm_profileOp_le _ _ γ F s y _ (hS.const_mul _) hconv hpt
    rwa [integral_const_mul] at h
  have hlarge : 1 ≤ ‖y‖ → ‖profileOp (1 + (n : ℝ) / 2) F s y‖ ≤
      27 * C * A * Ci * (M * ‖y‖ ^ (-min γ ((n : ℝ) + 1))) := by
    intro hy
    obtain ⟨hFi, hFb⟩ := hKF ‖y‖ hy
    obtain ⟨hNi, hNb⟩ := hKN ‖y‖ hy
    have hpt : ∀ τ : ℝ, 0 < τ → (1 + τ) ^ (-(1 + (n : ℝ) / 2)) *
        (27 * C * A * kernelWeightIntegral γ τ y) ≤
          27 * C * A * Ci * ((1 + τ) ^ (-(1 + (n : ℝ) / 2)) * farMajorant γ τ ‖y‖ +
            (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * nearMajorant γ τ ‖y‖) := by
      intro τ hτ
      calc (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * (27 * C * A * kernelWeightIntegral γ τ y)
          ≤ (1 + τ) ^ (-(1 + (n : ℝ) / 2)) *
              (27 * C * A * (Ci * (farMajorant γ τ ‖y‖ + nearMajorant γ τ ‖y‖))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left ((hCi τ hτ y).2.2 hy) hcA) (hβ τ hτ)
        _ = _ := by ring
    have h : ‖profileOp (1 + (n : ℝ) / 2) F s y‖ ≤ ∫ τ in Ioi (0 : ℝ),
        27 * C * A * Ci * ((1 + τ) ^ (-(1 + (n : ℝ) / 2)) * farMajorant γ τ ‖y‖ +
          (1 + τ) ^ (-(1 + (n : ℝ) / 2)) * nearMajorant γ τ ‖y‖) :=
      norm_profileOp_le _ _ γ F s y _ ((hFi.add hNi).const_mul _) hconv hpt
    rw [integral_const_mul, integral_add hFi hNi] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hP)
    have hR : 0 ≤ ‖y‖ ^ (-min γ ((n : ℝ) + 1)) := Real.rpow_nonneg (norm_nonneg _) _
    calc _ ≤ KF * ‖y‖ ^ (-min γ ((n : ℝ) + 1)) + KN * ‖y‖ ^ (-min γ ((n : ℝ) + 1)) :=
          add_le_add hFb hNb
      _ = (KF + KN) * ‖y‖ ^ (-min γ ((n : ℝ) + 1)) := by ring
      _ ≤ M * ‖y‖ ^ (-min γ ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_right hKM hR
  have hw : 0 ≤ (1 + ‖y‖) ^ min γ ((n : ℝ) + 1) := Real.rpow_nonneg (by positivity) _
  by_cases hy : 1 ≤ ‖y‖
  · have hRpos : 0 < ‖y‖ := by linarith
    have key : (1 + ‖y‖) ^ min γ ((n : ℝ) + 1) * ‖y‖ ^ (-min γ ((n : ℝ) + 1)) ≤
        2 ^ min γ ((n : ℝ) + 1) := by
      have h1 : (1 + ‖y‖) ^ min γ ((n : ℝ) + 1) ≤ (2 * ‖y‖) ^ min γ ((n : ℝ) + 1) :=
        Real.rpow_le_rpow (by positivity) (by linarith) hm0
      rw [Real.mul_rpow (by norm_num) hRpos.le] at h1
      calc (1 + ‖y‖) ^ min γ ((n : ℝ) + 1) * ‖y‖ ^ (-min γ ((n : ℝ) + 1))
          ≤ 2 ^ min γ ((n : ℝ) + 1) * ‖y‖ ^ min γ ((n : ℝ) + 1) *
              ‖y‖ ^ (-min γ ((n : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hRpos.le _)
        _ = 2 ^ min γ ((n : ℝ) + 1) := by
            rw [mul_assoc, ← Real.rpow_add hRpos, add_neg_cancel, Real.rpow_zero, mul_one]
    calc (1 + ‖y‖) ^ min γ ((n : ℝ) + 1) * ‖profileOp (1 + (n : ℝ) / 2) F s y‖
        ≤ (1 + ‖y‖) ^ min γ ((n : ℝ) + 1) *
            (27 * C * A * Ci * (M * ‖y‖ ^ (-min γ ((n : ℝ) + 1)))) :=
          mul_le_mul_of_nonneg_left (hlarge hy) hw
      _ = 27 * C * A * Ci * M *
            ((1 + ‖y‖) ^ min γ ((n : ℝ) + 1) * ‖y‖ ^ (-min γ ((n : ℝ) + 1))) := by ring
      _ ≤ 27 * C * A * Ci * M * 2 ^ min γ ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left key (mul_nonneg hP hM0)
      _ = 27 * C * Ci * 2 ^ min γ ((n : ℝ) + 1) * M * A := by ring
  · rw [not_le] at hy
    have h2 : (1 + ‖y‖) ^ min γ ((n : ℝ) + 1) ≤ 2 ^ min γ ((n : ℝ) + 1) :=
      Real.rpow_le_rpow (by positivity) (by linarith) hm0
    calc (1 + ‖y‖) ^ min γ ((n : ℝ) + 1) * ‖profileOp (1 + (n : ℝ) / 2) F s y‖
        ≤ 2 ^ min γ ((n : ℝ) + 1) * (27 * C * A * Ci * M) :=
          mul_le_mul h2 (hsmall.trans (mul_le_mul_of_nonneg_left hSM hP)) (norm_nonneg _)
            (Real.rpow_nonneg (by norm_num) _)
      _ = 27 * C * Ci * 2 ^ min γ ((n : ℝ) + 1) * M * A := by ring

end Breakdown.FarField
