import Breakdown.Torus.ShellTorusProduct
import Breakdown.Torus.ShellTorusTransplant
import Breakdown.Torus.ShellTorusPhi

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace ShellTorus.Internal

theorem advCoef_transplant (hT : TransplantSmooth) (hF : FreqTrSeriesSpec)
    (φ : Space → Space) (hφ : IsTestField φ) (b μ : ℝ) (hμ : IsShellScale μ b)
    (hsupp : tsupport φ ⊆ Metric.closedBall 0 b) (z : V) (k : Lattice) :
    advCoef ((μ ^ (1 / 4 : ℝ)) • toV (transplantField μ φ)) z k +
        advCoef z ((μ ^ (1 / 4 : ℝ)) • toV (transplantField μ φ)) k =
      μ⁻¹ • freqTrCoef (fun x => (advectShell φ hφ b (restrictTorus μ b z) : Space → Space)
        (simCoord μ x)) k := by
  obtain ⟨hTs, hTp, hTd, -⟩ := hT φ μ b hφ.1 hφ.2.2 hμ hsupp
  have hf : ContDiff ℝ ∞ (fun x => μ ^ (1 / 4 : ℝ) • transplantField μ φ x) := hTs.const_smul _
  have hp : IsPeriodic (fun x => μ ^ (1 / 4 : ℝ) • transplantField μ φ x) := fun i x => by
    simp only [hTp i x]
  have hd : ∀ x, divergenceAt (fun x => μ ^ (1 / 4 : ℝ) • transplantField μ φ x) x = 0 := fun x => by
    rw [divergenceAt_scale, hTd x, mul_zero]
  have ha : ∀ k, coeff ((μ ^ (1 / 4 : ℝ)) • toV (transplantField μ φ)) k =
      freqTrCoef (fun x => μ ^ (1 / 4 : ℝ) • transplantField μ φ x) k := fun k => by
    rw [coeff_smul_real, (hF _ hTs hTp hTd).1 k, freqTrCoef_scale]
  rw [advCoef_product hF hf hp hd _ z ha k, ← freqTrCoef_scale]
  exact freqTrCoef_congr (productField_transplant hT φ hφ b μ hμ hsupp z) k

theorem sourceOp_threeHalves (hTS : TrigHs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ μ b τ : ℝ, IsShellScale μ b → 0 < τ → μ * τ ≤ 1 → ∀ A : Freq.L2R,
      (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b → (A : Space → Space) y = 0) →
        ‖sourceOp μ τ A‖ ≤
          C * μ ^ (1 / 4 : ℝ) * τ ^ (-(3 / 4 : ℝ)) * (eLpNorm (A : Space → Space) (3 / 2) volume).toReal := by
  obtain ⟨C, hC0, hC⟩ := phiField_bound hTS
  refine ⟨C, hC0, fun μ b τ hμ hτ hμτ A hA => ?_⟩
  have hμ0 : 0 < μ := hμ.1
  have hs : 0 < μ * τ := mul_pos hμ0 hτ
  rw [sourceOp_apply hμ0]
  obtain ⟨hmem, hbd⟩ := hC (μ * τ) hs hμτ (forceV (μ * τ) fun x => (A : Space → Space) (simCoord μ x))
  obtain ⟨hint, hpair⟩ := pairing_transplant μ b hμ A hA _ hmem
  have hsq := norm_sq_forceV hs _ hint
  set u := forceV (μ * τ) fun x => (A : Space → Space) (simCoord μ x) with hu
  set a := (eLpNorm (A : Space → Space) (3 / 2) volume).toReal with ha
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hsp : 0 ≤ (μ * τ) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hs.le _
  have key : ‖u‖ * ‖u‖ ≤ (μ * a * C * (μ * τ) ^ (-(3 / 4 : ℝ))) * ‖u‖ := by
    rw [← sq, hsq]
    refine (le_abs_self _).trans (hpair.trans ?_)
    calc μ * a * (eLpNorm (phiField (μ * τ) u) 3 (volume.restrict cell)).toReal
        ≤ μ * a * (C * (μ * τ) ^ (-(3 / 4 : ℝ)) * ‖u‖) :=
          mul_le_mul_of_nonneg_left hbd (mul_nonneg hμ0.le ha0)
      _ = (μ * a * C * (μ * τ) ^ (-(3 / 4 : ℝ))) * ‖u‖ := by ring
  have hK : ‖u‖ ≤ μ * a * C * (μ * τ) ^ (-(3 / 4 : ℝ)) := by
    rcases (norm_nonneg u).eq_or_lt with h | h
    · rw [← h]
      positivity
    · exact le_of_mul_le_mul_right key h
  have e1 : (μ * τ) ^ (-(3 / 4 : ℝ)) = μ ^ (-(3 / 4 : ℝ)) * τ ^ (-(3 / 4 : ℝ)) :=
    Real.mul_rpow hμ0.le hτ.le
  have e2 : μ * μ ^ (-(3 / 4 : ℝ)) = μ ^ (1 / 4 : ℝ) := by
    calc μ * μ ^ (-(3 / 4 : ℝ)) = μ ^ (1 : ℝ) * μ ^ (-(3 / 4 : ℝ)) := by rw [Real.rpow_one]
      _ = μ ^ ((1 : ℝ) + -(3 / 4 : ℝ)) := (Real.rpow_add hμ0 _ _).symm
      _ = μ ^ (1 / 4 : ℝ) := by norm_num
  calc ‖u‖ ≤ μ * a * C * (μ * τ) ^ (-(3 / 4 : ℝ)) := hK
    _ = C * (μ * μ ^ (-(3 / 4 : ℝ))) * τ ^ (-(3 / 4 : ℝ)) * a := by rw [e1]; ring
    _ = C * μ ^ (1 / 4 : ℝ) * τ ^ (-(3 / 4 : ℝ)) * a := by rw [e2]

theorem rpow_scale {μ : ℝ} (hμ : 0 < μ) : μ ^ (3 / 4 : ℝ) * μ⁻¹ = μ ^ (-(1 / 4 : ℝ)) := by
  rw [← Real.rpow_neg_one, ← Real.rpow_add hμ]
  norm_num

end ShellTorus.Internal

open ShellTorus.Internal

theorem torusFactor (_hS : TorusSeriesSmooth) (hT : TransplantSmooth) (hF : FreqTrSeriesSpec) :
    TorusFactor := by
  intro φ hφ b μ hμ hsupp τ hτ z
  have hμ0 : 0 < μ := hμ.1
  have hs : 0 < μ * τ := mul_pos hμ0 hτ
  apply coeff_injective
  intro k
  rw [lambdaTorus_apply, coeff_neg_vec, coeff_smul_real, coeff_smul_real, sourceOp_apply hμ0,
    coeff_forceV hs, coeff_kernel _ hs, advCoef_transplant hT hF φ hφ b μ hμ hsupp z k,
    divFree_smul_real, smul_smul, smul_smul, ← neg_smul, smul_smul]
  congr 1
  rw [← rpow_scale hμ0]
  ring

theorem torusLambdaBound (hTS : TrigHs) (hG : Freq.GradSixDecay) (hE : Freq.EmbedNorm) :
    TorusLambdaBound := by
  obtain ⟨C1, hC1, h1⟩ := advectShell_threeHalves hG hE
  obtain ⟨C2, hC2, h2⟩ := sourceOp_threeHalves hTS
  refine ⟨C2 * C1, mul_nonneg hC2 hC1, ?_⟩
  intro φ hφ b μ τ hμ hτ hμτ ζ
  have hμ0 : 0 < μ := hμ.1
  have hq : 0 < μ ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hμ0 _
  have hA := h2 μ b τ hμ hτ hμτ _ (advectShell_ae_zero φ hφ b ζ)
  have hB := h1 φ hφ b ζ
  have ht : 0 ≤ τ ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hτ.le _
  rw [lambdaTorus_apply, norm_neg, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hμ0.le _)]
  calc μ ^ (-(1 / 4 : ℝ)) * ‖sourceOp μ τ (advectShell φ hφ b ζ)‖
      ≤ μ ^ (-(1 / 4 : ℝ)) * (C2 * μ ^ (1 / 4 : ℝ) * τ ^ (-(3 / 4 : ℝ)) *
          (eLpNorm (advectShell φ hφ b ζ : Space → Space) (3 / 2) volume).toReal) :=
        mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg hμ0.le _)
    _ = C2 * τ ^ (-(3 / 4 : ℝ)) *
          (eLpNorm (advectShell φ hφ b ζ : Space → Space) (3 / 2) volume).toReal := by
        rw [Real.rpow_neg hμ0.le]
        field_simp
    _ ≤ C2 * τ ^ (-(3 / 4 : ℝ)) * (C1 * ‖Freq.embedX φ‖ * ‖ζ‖) :=
        mul_le_mul_of_nonneg_left hB (mul_nonneg hC2 ht)
    _ = C2 * C1 * τ ^ (-(3 / 4 : ℝ)) * ‖Freq.embedX φ‖ * ‖ζ‖ := by ring

end Breakdown.Periodic
