import Breakdown.FracCell.EnergyRadialPairing
import Breakdown.FracCell.EnergyHeightProj

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.CellEnergy.RadialProjInternal

open CellAnalysis CellFormula SteadyCert Assembly RadialForm

theorem lineWeight_cont (K : CellBox) : Continuous K.lineWeight := by
  by_cases h : K.r₁ = 0
  · have : K.lineWeight = fun r => r := funext fun r => by simp [CellBox.lineWeight, h]
    rw [this]; exact continuous_id
  · have : K.lineWeight = fun _ => 1 := funext fun r => by simp [CellBox.lineWeight, h]
    rw [this]; exact continuous_const

theorem refR_cont (K : CellBox) : Continuous K.refR := by
  unfold CellBox.refR
  fun_prop

theorem radialPoly_diff (B : CellBases) (j : ℕ) : ContDiff ℝ 1 (B.radialPoly j) := by
  unfold CellBases.radialPoly
  exact ContDiff.sum fun i _ => contDiff_const.mul (contDiff_id.pow i)

theorem heightPoly_cont (B : CellBases) (l : ℕ) : Continuous (B.heightPoly l) := by
  unfold CellBases.heightPoly
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_id.pow i)

theorem slope_eq (B : CellBases) (j l : ℕ) (p : ℝ × ℝ) :
    radialSlope (basisFn B j l) p = deriv (B.radialPoly j) p.1 * B.heightPoly l p.2 := by
  show deriv (fun r => B.radialPoly j r * B.heightPoly l p.2) p.1 = _
  exact deriv_mul_const ((radialPoly_diff B j).differentiable (by norm_num) p.1) _

theorem slope_cont (B : CellBases) (j l : ℕ) : Continuous (radialSlope (basisFn B j l)) := by
  have : radialSlope (basisFn B j l) = fun p => deriv (B.radialPoly j) p.1 * B.heightPoly l p.2 :=
    funext (slope_eq B j l)
  rw [this]
  exact (((radialPoly_diff B j).continuous_deriv le_rfl).comp continuous_fst).mul
    ((heightPoly_cont B l).comp continuous_snd)

theorem deriv_basis_sum (B : CellBases) (Q : ℕ) (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) (p : ℝ × ℝ) :
    CellBox.radialDeriv (fun p => ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), c j l * ((basisFn B j l p : ℝ) : ℂ)) p =
      ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), c j l * ((radialSlope (basisFn B j l) p : ℝ) : ℂ) := by
  unfold CellBox.radialDeriv
  have h : ∀ j l : Fin (Q + 1), HasDerivAt (fun r : ℝ => c j l * ((basisFn B j l (r, p.2) : ℝ) : ℂ))
      (c j l * ((radialSlope (basisFn B j l) p : ℝ) : ℂ)) p.1 := by
    intro j l
    rw [slope_eq]
    have h1 : HasDerivAt (fun r => B.radialPoly j r * B.heightPoly l p.2)
        (deriv (B.radialPoly j) p.1 * B.heightPoly l p.2) p.1 :=
      (((radialPoly_diff B j).differentiable (by norm_num) p.1).hasDerivAt).mul_const _
    exact (h1.ofReal_comp).const_mul (c j l)
  exact (HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun l _ => h j l).deriv

theorem row_value {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ}
    (K : CellBox) (B : CellBases) (I : LowIndex D modes Q q) (m : ℕ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (u : D → ℂ)
    (hR : Represents K B I m v G H u) (n : modes) (C : Fin 3 → Fin 3 → ℂ)
    (hint : ∀ a b, IntegrableOn (gradMode m n G a b) K.rect) (j l : Fin (Q + 1)) :
    rowApply (lowRow I n C j l) u = B.coef K (strainField m n G C) j l := by
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have h1 : rowApply (lowRow I n C j l) u = ∑ a : Fin 3, ∑ b : Fin 3, C a b * u (I.strainSlot n a b j l) := by
    unfold rowApply lowRow
    calc ∑ d, (∑ a : Fin 3, ∑ b : Fin 3, C a b * (if d = I.strainSlot n a b j l then 1 else 0)) * u d
        = ∑ d, ∑ a : Fin 3, ∑ b : Fin 3, C a b * ((if d = I.strainSlot n a b j l then 1 else 0) * u d) := by
          simp only [Finset.sum_mul, mul_assoc]
      _ = ∑ a : Fin 3, ∑ b : Fin 3, ∑ d, C a b * ((if d = I.strainSlot n a b j l then 1 else 0) * u d) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ a : Fin 3, ∑ b : Fin 3, C a b * u (I.strainSlot n a b j l) := by
          simp [ite_mul, Finset.sum_ite_eq']
  rw [h1]
  simp only [hR.strain]
  unfold CellBases.coef strainField
  simp only [Finset.mul_sum, Finset.sum_mul]
  have hi : ∀ a b : Fin 3, IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * (C a b * gradMode m n G a b p) *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect := by
    intro a b
    have hc : ContinuousOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * C a b *
        ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect := by
      apply Continuous.continuousOn
      exact ((Complex.continuous_ofReal.comp ((lineWeight_cont K).comp continuous_fst)).mul continuous_const).mul
        (Complex.continuous_ofReal.comp ((((radialPoly_diff B j).continuous).comp continuous_fst).mul
          ((heightPoly_cont B l).comp continuous_snd)))
    refine ((hint a b).continuousOn_mul hc hcomp).congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
    ring
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hi a b]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => hi a b]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← integral_const_mul]
  congr 1
  funext p
  ring

end Breakdown.CellCert.CellEnergy.RadialProjInternal
