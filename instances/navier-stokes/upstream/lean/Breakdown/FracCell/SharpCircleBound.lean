import Breakdown.FracCell.SharpYSharpSupremum

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly SharpParts SharpSupremumParts

namespace SharpCircleBoundParts

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

def strainWave (n n' : ℤ) (p : ℝ × ℝ) : ℂ :=
  -(∑ a : Fin 3, (starRingEnd ℂ) (curlComp (sharpGrad c K S x n p) a) *
      ∑ b : Fin 3, CellScalars.strainMode c (n - n') p a b * curlComp (sharpGrad c K S x n' p) b)

def couplingWave (n n' : ℤ) (p : ℝ × ℝ) : ℂ :=
  (1 / 2 : ℂ) * entryPairing (couplingMap (CellScalars.curlGradMode c (n - n') p) (sharpVel c K S x n' p))
      (sharpGrad c K S x n p)
    + (1 / 2 : ℂ) * entryPairing (sharpGrad c K S x n' p)
      (couplingMap (CellScalars.curlGradMode c (n' - n) p) (sharpVel c K S x n p))

def couplingLoss (n : ℤ) (p : ℝ × ℝ) : ℝ :=
  Exterior.traceFreeConst * S.meanGradBound p * Real.sqrt (sumSq (sharpGrad c K S x n p))
      * Real.sqrt (vecSq (sharpVel c K S x n p))
    + (1 / 2) * Exterior.traceFreeConst * S.waveGradBound p
      * (S.splitLength * sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p) / S.splitLength)

def meanLoss (n : ℤ) (p : ℝ × ℝ) : ℝ :=
  Exterior.traceFreeConst * S.meanGradBound p * Real.sqrt (sumSq (sharpGrad c K S x n p))
      * Real.sqrt (vecSq (sharpVel c K S x n p))

def waveLoss (n : ℤ) (p : ℝ × ℝ) : ℝ :=
  (1 / 2) * Exterior.traceFreeConst * S.waveGradBound p
      * (S.splitLength * sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p) / S.splitLength)

def offWave (n n' : ℤ) (p : ℝ × ℝ) : ℂ := if n' = n then 0 else couplingWave c K S x n n' p

end SharpCircleBoundParts

open SharpCircleBoundParts

def SharpCircleMeanStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ᵐ p ∂(volume.restrict K.rect), Summable (fun n : ℤ => sumSq (sharpGrad c K S x n p)) →
        Summable (fun n : ℤ => vecSq (sharpVel c K S x n p)) →
        Summable (fun n : ℤ => couplingWave c K S x n n p) ∧
        ∀ n : ℤ, -meanLoss c K S x n p ≤ (couplingWave c K S x n n p).re

def SharpCircleWaveStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ᵐ p ∂(volume.restrict K.rect), Summable (fun n : ℤ => sumSq (sharpGrad c K S x n p)) →
        Summable (fun n : ℤ => vecSq (sharpVel c K S x n p)) →
        (∀ n : ℤ, Summable (fun n' : ℤ => offWave c K S x n n' p)) ∧
        Summable (fun n : ℤ => ∑' n' : ℤ, offWave c K S x n n' p) ∧
        -(∑' n : ℤ, waveLoss c K S x n p) ≤ (∑' n : ℤ, ∑' n' : ℤ, offWave c K S x n n' p).re

def SharpCircleStrainStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ᵐ p ∂(volume.restrict K.rect), Summable (fun n : ℤ => sumSq (sharpGrad c K S x n p)) →
        Summable (fun n : ℤ => vecSq (sharpVel c K S x n p)) →
        (∀ n : ℤ, Summable (fun n' : ℤ => strainWave c K S x n n' p)) ∧
        Summable (fun n : ℤ => ∑' n' : ℤ, strainWave c K S x n n' p) ∧
        -(∑' n : ℤ, S.strainBound p * curlSq (sharpGrad c K S x n p))
          ≤ (∑' n : ℤ, ∑' n' : ℤ, strainWave c K S x n n' p).re

def SharpCircleCouplingStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ᵐ p ∂(volume.restrict K.rect), Summable (fun n : ℤ => sumSq (sharpGrad c K S x n p)) →
        Summable (fun n : ℤ => vecSq (sharpVel c K S x n p)) →
        (∀ n : ℤ, Summable (fun n' : ℤ => couplingWave c K S x n n' p)) ∧
        Summable (fun n : ℤ => ∑' n' : ℤ, couplingWave c K S x n n' p) ∧
        -(∑' n : ℤ, couplingLoss c K S x n p) ≤ (∑' n : ℤ, ∑' n' : ℤ, couplingWave c K S x n n' p).re

namespace SharpCircleBoundParts

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

private theorem sumSq_nonneg' (s : Fin 3 → Fin 3 → ℂ) : 0 ≤ sumSq s := by unfold sumSq; positivity

private theorem vecSq_nonneg' (v : Fin 3 → ℂ) : 0 ≤ vecSq v := by unfold vecSq; positivity

private theorem curlSq_nonneg' (s : Fin 3 → Fin 3 → ℂ) : 0 ≤ curlSq s := by unfold curlSq; positivity

private theorem sq_sum_three (f : Fin 3 → ℝ) : (∑ i, f i) ^ 2 ≤ 3 * ∑ i, f i ^ 2 := by
  simp only [Fin.sum_univ_three]
  nlinarith [sq_nonneg (f 0 - f 1), sq_nonneg (f 1 - f 2), sq_nonneg (f 0 - f 2)]

private theorem sign_norm_le (i j l : Fin 3) : ‖(CellCert.permSign i j l : ℂ)‖ ≤ 1 := by
  unfold CellCert.permSign
  split_ifs <;> simp

private theorem curlComp_norm_le (s : Fin 3 → Fin 3 → ℂ) (i : Fin 3) :
    ‖curlComp s i‖ ≤ ∑ j : Fin 3, ∑ l : Fin 3, ‖s l j‖ := by
  unfold curlComp
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans ?_)
  refine Finset.sum_le_sum fun l _ => ?_
  rw [norm_mul]
  calc ‖(CellCert.permSign i j l : ℂ)‖ * ‖s l j‖ ≤ 1 * ‖s l j‖ :=
        mul_le_mul_of_nonneg_right (sign_norm_le i j l) (norm_nonneg _)
    _ = ‖s l j‖ := one_mul _

private theorem curlSq_le' (s : Fin 3 → Fin 3 → ℂ) : curlSq s ≤ 27 * sumSq s := by
  have h : ∀ i, ‖curlComp s i‖ ^ 2 ≤ 9 * sumSq s := by
    intro i
    have h0 := curlComp_norm_le s i
    have h1 : ‖curlComp s i‖ ^ 2 ≤ (∑ j : Fin 3, ∑ l : Fin 3, ‖s l j‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h0 2
    have h2 : (∑ j : Fin 3, ∑ l : Fin 3, ‖s l j‖) ^ 2 ≤ 3 * ∑ j : Fin 3, (∑ l : Fin 3, ‖s l j‖) ^ 2 :=
      sq_sum_three (fun j => ∑ l : Fin 3, ‖s l j‖)
    have h3 : ∀ j : Fin 3, (∑ l : Fin 3, ‖s l j‖) ^ 2 ≤ 3 * ∑ l : Fin 3, ‖s l j‖ ^ 2 :=
      fun j => sq_sum_three (fun l => ‖s l j‖)
    have h4 : ∑ j : Fin 3, (∑ l : Fin 3, ‖s l j‖) ^ 2 ≤ ∑ j : Fin 3, 3 * ∑ l : Fin 3, ‖s l j‖ ^ 2 :=
      Finset.sum_le_sum fun j _ => h3 j
    have h5 : ∑ j : Fin 3, 3 * ∑ l : Fin 3, ‖s l j‖ ^ 2 = 3 * sumSq s := by
      rw [← Finset.mul_sum]
      unfold sumSq
      rw [Finset.sum_comm]
    linarith
  unfold curlSq
  calc ∑ i, ‖curlComp s i‖ ^ 2 ≤ ∑ _i : Fin 3, 9 * sumSq s := Finset.sum_le_sum fun i _ => h i
    _ = 27 * sumSq s := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

private theorem pairWave_split (n n' : ℤ) (p : ℝ × ℝ) :
    pairWave c n n' p (sharpGrad c K S x n p) (sharpVel c K S x n p) (sharpGrad c K S x n' p)
        (sharpVel c K S x n' p)
      = strainWave c K S x n n' p + couplingWave c K S x n n' p := by
  unfold pairWave waveForm strainWave couplingWave
  ring

private theorem supDensity_split (n : ℤ) (p : ℝ × ℝ) :
    supDensity c K S x n p = S.strainBound p * curlSq (sharpGrad c K S x n p) + couplingLoss c K S x n p := by
  unfold supDensity supremumLoss couplingLoss
  ring

private theorem sqrt_mul_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.sqrt a * Real.sqrt b ≤ a + b := by
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sqrt_nonneg a, Real.sqrt_nonneg b]

private theorem meanLoss_summable (p : ℝ × ℝ) (hg : 0 ≤ S.meanGradBound p)
    (hq : Summable (fun n : ℤ => sumSq (sharpGrad c K S x n p)))
    (hv : Summable (fun n : ℤ => vecSq (sharpVel c K S x n p))) :
    Summable (fun n : ℤ => meanLoss c K S x n p) := by
  have hT : 0 ≤ Exterior.traceFreeConst := by unfold Exterior.traceFreeConst; positivity
  have hTg : 0 ≤ Exterior.traceFreeConst * S.meanGradBound p := mul_nonneg hT hg
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) ((hq.add hv).mul_left
    (Exterior.traceFreeConst * S.meanGradBound p))
  · exact mul_nonneg (mul_nonneg hTg (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  · unfold meanLoss
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (sqrt_mul_le _ _ (sumSq_nonneg' _) (vecSq_nonneg' _)) hTg

private theorem waveLoss_summable (p : ℝ × ℝ)
    (hq : Summable (fun n : ℤ => sumSq (sharpGrad c K S x n p)))
    (hv : Summable (fun n : ℤ => vecSq (sharpVel c K S x n p))) :
    Summable (fun n : ℤ => waveLoss c K S x n p) :=
  ((hq.mul_left S.splitLength).add (hv.div_const S.splitLength)).mul_left _

private theorem couplingLoss_summable (p : ℝ × ℝ) (hg : 0 ≤ S.meanGradBound p)
    (hq : Summable (fun n : ℤ => sumSq (sharpGrad c K S x n p)))
    (hv : Summable (fun n : ℤ => vecSq (sharpVel c K S x n p))) :
    Summable (fun n : ℤ => couplingLoss c K S x n p) :=
  (meanLoss_summable c K S x p hg hq hv).add (waveLoss_summable c K S x p hq hv)

private theorem coupling_split (n n' : ℤ) (p : ℝ × ℝ) :
    couplingWave c K S x n n' p = (if n' = n then couplingWave c K S x n n p else 0) + offWave c K S x n n' p := by
  unfold offWave
  split_ifs with h
  · subst h; simp
  · simp

end SharpCircleBoundParts

theorem sharpCircleCoupling_of (hM : SharpCircleMeanStatement) (hW : SharpCircleWaveStatement) :
    SharpCircleCouplingStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx
  filter_upwards [hM α h1 h2 c hc K S B Cl R hd hw x hx, hW α h1 h2 c hc K S B Cl R hd hw x hx]
    with p hm hwv hq hv
  obtain ⟨hm1, hm2⟩ := hm hq hv
  obtain ⟨hw1, hw2, hw3⟩ := hwv hq hv
  have hsingle : ∀ n : ℤ, HasSum (fun n' : ℤ => if n' = n then couplingWave c K S x n n p else 0)
      (couplingWave c K S x n n p) := fun n => hasSum_ite_eq n _
  have hfun : ∀ n : ℤ, (fun n' : ℤ => couplingWave c K S x n n' p)
      = fun n' => (if n' = n then couplingWave c K S x n n p else 0) + offWave c K S x n n' p :=
    fun n => funext fun n' => SharpCircleBoundParts.coupling_split c K S x n n' p
  have hin : ∀ n : ℤ, Summable (fun n' : ℤ => couplingWave c K S x n n' p) := by
    intro n; rw [hfun n]; exact (hsingle n).summable.add (hw1 n)
  have hinner : ∀ n : ℤ, ∑' n' : ℤ, couplingWave c K S x n n' p
      = couplingWave c K S x n n p + ∑' n' : ℤ, offWave c K S x n n' p := by
    intro n; rw [hfun n, (hsingle n).summable.tsum_add (hw1 n), (hsingle n).tsum_eq]
  have hout : Summable (fun n : ℤ => couplingWave c K S x n n p + ∑' n' : ℤ, offWave c K S x n n' p) :=
    hm1.add hw2
  have hml := SharpCircleBoundParts.meanLoss_summable c K S x p (hd.scalars.grad_bounds_nonneg p).1 hq hv
  have hwl := SharpCircleBoundParts.waveLoss_summable c K S x p hq hv
  have hre : Summable (fun n : ℤ => (couplingWave c K S x n n p).re) :=
    (Complex.hasSum_re hm1.hasSum).summable
  have hmean : -(∑' n : ℤ, meanLoss c K S x n p) ≤ ∑' n : ℤ, (couplingWave c K S x n n p).re := by
    rw [← tsum_neg]
    exact hml.neg.tsum_le_tsum hm2 hre
  refine ⟨hin, ?_, ?_⟩
  · simp_rw [hinner]; exact hout
  · simp_rw [hinner]
    rw [hm1.tsum_add hw2, Complex.add_re, Complex.re_tsum hm1]
    have hsplit : ∑' n : ℤ, couplingLoss c K S x n p
        = (∑' n : ℤ, meanLoss c K S x n p) + ∑' n : ℤ, waveLoss c K S x n p := by
      rw [← hml.tsum_add hwl]; rfl
    rw [hsplit]
    linarith

theorem sharpCircleBound_of (hS : SharpCircleStrainStatement) (hC : SharpCircleCouplingStatement) :
    SharpCircleBoundStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx
  filter_upwards [hS α h1 h2 c hc K S B Cl R hd hw x hx, hC α h1 h2 c hc K S B Cl R hd hw x hx]
    with p hs hcp hq hv
  obtain ⟨hs1, hs2, hs3⟩ := hs hq hv
  obtain ⟨hc1, hc2, hc3⟩ := hcp hq hv
  have hcurl : Summable (fun n : ℤ => S.strainBound p * curlSq (sharpGrad c K S x n p)) :=
    (Summable.of_nonneg_of_le (fun n => SharpCircleBoundParts.curlSq_nonneg' _)
      (fun n => SharpCircleBoundParts.curlSq_le' _) (hq.mul_left 27)).mul_left _
  have hloss := SharpCircleBoundParts.couplingLoss_summable c K S x p
    (hd.scalars.grad_bounds_nonneg p).1 hq hv
  have hW : waveSum c K S x p = (∑' n : ℤ, ∑' n' : ℤ, strainWave c K S x n n' p)
      + ∑' n : ℤ, ∑' n' : ℤ, couplingWave c K S x n n' p := by
    unfold waveSum
    simp_rw [SharpCircleBoundParts.pairWave_split c K S x]
    rw [← hs2.tsum_add hc2]
    exact tsum_congr fun n => (hs1 n).tsum_add (hc1 n)
  have hD : ∑' n : ℤ, supDensity c K S x n p = (∑' n : ℤ, S.strainBound p * curlSq (sharpGrad c K S x n p))
      + ∑' n : ℤ, couplingLoss c K S x n p := by
    rw [← hcurl.tsum_add hloss]
    exact tsum_congr fun n => SharpCircleBoundParts.supDensity_split c K S x n p
  rw [hW, hD, Complex.add_re]
  linarith

end CellAnalysis

end CellCert

end Breakdown
