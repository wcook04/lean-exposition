import Breakdown.FracCell.SharpYSharpCross

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly SharpParts

def YUnfoldedRegularStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      (∀ m ∈ R.yModes, IntegrableOn (fun p : ℝ × ℝ => ((K.lineWeight p.1 : ℝ) : ℂ) *
          entryPairing (sharpGrad c K S x m p) (CellScalars.yStrain c K S x.2.2.2.1 ζ x.1 x.2.1 m p)) K.rect) ∧
      (∀ m ∈ R.yModes, IntegrableOn (fun p : ℝ × ℝ => ((K.lineWeight p.1 : ℝ) : ℂ) *
          CellScalars.vecPair (sharpVel c K S x m p) (CellScalars.yVelocity c K S x.1 x.2.1 m p)) K.rect) ∧
      (∀ n ∈ S.resolved, ∀ m ∈ S.resolved ∪ S.band, IntegrableOn (fun p : ℝ × ℝ => p.1 *
          (pairWave c n m p (lowGrad c K S x n p) (lowVel c K S x n p) (sharpGrad c K S x m p) (sharpVel c K S x m p)
            + pairWave c m n p (sharpGrad c K S x m p) (sharpVel c K S x m p) (lowGrad c K S x n p)
              (lowVel c K S x n p)).re) K.rect) ∧
      (∀ m ∈ S.resolved, IntegrableOn (fun p : ℝ × ℝ => p.1 * matrixCrossDensity c K S x m p) K.rect)

def WaveCrossRegularStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ n ∈ S.resolved, ∀ m ∈ S.resolved ∪ S.band, IntegrableOn (fun p : ℝ × ℝ => p.1 *
          (pairWave c n m p (lowGrad c K S x n p) (lowVel c K S x n p) (sharpGrad c K S x m p) (sharpVel c K S x m p)
            + pairWave c m n p (sharpGrad c K S x m p) (sharpVel c K S x m p) (lowGrad c K S x n p)
              (lowVel c K S x n p)).re) K.rect

namespace SharpCrossYUnfolded.Internal

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

def wavePart (m : ℤ) (p : ℝ × ℝ) : ℝ :=
  if m ∈ S.resolved ∪ S.band then ∑ n ∈ S.resolved,
      ((pairWave c n m p (lowGrad c K S x n p) (lowVel c K S x n p) (sharpGrad c K S x m p) (sharpVel c K S x m p)).re
        + (pairWave c m n p (sharpGrad c K S x m p) (sharpVel c K S x m p) (lowGrad c K S x n p) (lowVel c K S x n p)).re)
    else 0

def matPart (m : ℤ) (p : ℝ × ℝ) : ℝ :=
  if m ∈ S.resolved then matrixCrossDensity c K S x m p else 0

def linPart (ζ : Fin k → ℝ) (m : ℤ) (p : ℝ × ℝ) : ℝ :=
  (∑ i : Fin k, (((x.2.2.2.1 i : ℝ) : ℂ) * entryPairing (sharpGrad c K S x m p)
      (fun a b => modeMat c.order m (c.modelActuatorGrad i) p.1 p.2 a b)
    + ((2 * ζ i : ℝ) : ℂ) * entryPairing (sharpGrad c K S x m p)
      (fun a b => modeMat c.order m (c.modelPinField i) p.1 p.2 a b))).re

theorem pointwise (hsy : ModelStrainSymmetric c) (hA : ∀ n p, (S.localMatrix n p).IsHermitian)
    (ζ : Fin k → ℝ) (m : ℤ) (p : ℝ × ℝ) :
    2 * (((K.lineWeight p.1 : ℝ) : ℂ) * entryPairing (sharpGrad c K S x m p)
          (CellScalars.yStrain c K S x.2.2.2.1 ζ x.1 x.2.1 m p)
        + ((K.lineWeight p.1 : ℝ) : ℂ) * CellScalars.vecPair (sharpVel c K S x m p)
          (CellScalars.yVelocity c K S x.1 x.2.1 m p)).re
      = p.1 * (wavePart c K S x m p + matPart c K S x m p + linPart c K S x ζ m p) :=
  SharpYSharpCross.Internal.unfolded_pointwise c K S x hsy hA ζ m p


variable {c K S x} in
theorem mode_split (hsy : ModelStrainSymmetric c) (hA : ∀ n p, (S.localMatrix n p).IsHermitian)
    (ζ : Fin k → ℝ) (m : ℤ)
    (hE : IntegrableOn (fun p : ℝ × ℝ => ((K.lineWeight p.1 : ℝ) : ℂ) *
      entryPairing (sharpGrad c K S x m p) (CellScalars.yStrain c K S x.2.2.2.1 ζ x.1 x.2.1 m p)) K.rect)
    (hV : IntegrableOn (fun p : ℝ × ℝ => ((K.lineWeight p.1 : ℝ) : ℂ) *
      CellScalars.vecPair (sharpVel c K S x m p) (CellScalars.yVelocity c K S x.1 x.2.1 m p)) K.rect)
    (hW : IntegrableOn (fun p : ℝ × ℝ => p.1 * wavePart c K S x m p) K.rect)
    (hM : IntegrableOn (fun p : ℝ × ℝ => p.1 * matPart c K S x m p) K.rect) :
    yStrainUnfolded c K S x ζ m + yVelocityPairing c K S x m
      = (∫ p in K.rect, p.1 * wavePart c K S x m p) + (∫ p in K.rect, p.1 * matPart c K S x m p)
        + ∫ p in K.rect, p.1 * linPart c K S x ζ m p := by
  have ht : IntegrableOn (fun p : ℝ × ℝ => p.1 * (wavePart c K S x m p + matPart c K S x m p
      + linPart c K S x ζ m p)) K.rect := by
    refine ((hE.add hV).re.const_mul 2).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.add_apply, RCLike.re_to_complex]
    exact pointwise c K S x hsy hA ζ m p
  have hL : IntegrableOn (fun p : ℝ × ℝ => p.1 * linPart c K S x ζ m p) K.rect := by
    refine (ht.sub (hW.add hM)).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hWM : IntegrableOn (fun p : ℝ × ℝ => p.1 * wavePart c K S x m p + p.1 * matPart c K S x m p) K.rect :=
    hW.add hM
  have e := integral_re (hE.add hV)
  simp only [Pi.add_apply, RCLike.re_to_complex] at e
  have e1 : yStrainUnfolded c K S x ζ m + yVelocityPairing c K S x m
      = ∫ p in K.rect, 2 * (((K.lineWeight p.1 : ℝ) : ℂ) * entryPairing (sharpGrad c K S x m p)
          (CellScalars.yStrain c K S x.2.2.2.1 ζ x.1 x.2.1 m p)
        + ((K.lineWeight p.1 : ℝ) : ℂ) * CellScalars.vecPair (sharpVel c K S x m p)
          (CellScalars.yVelocity c K S x.1 x.2.1 m p)).re := by
    unfold yStrainUnfolded yVelocityPairing
    rw [integral_const_mul, e, integral_add hE hV, Complex.add_re]
    ring
  rw [e1]
  simp only [pointwise c K S x hsy hA ζ m, mul_add]
  rw [integral_add hWM hL, integral_add hW hM]

theorem wave_integrable
    (hC : ∀ n ∈ S.resolved, ∀ m ∈ S.resolved ∪ S.band, IntegrableOn (fun p : ℝ × ℝ => p.1 *
      (pairWave c n m p (lowGrad c K S x n p) (lowVel c K S x n p) (sharpGrad c K S x m p) (sharpVel c K S x m p)
        + pairWave c m n p (sharpGrad c K S x m p) (sharpVel c K S x m p) (lowGrad c K S x n p)
          (lowVel c K S x n p)).re) K.rect) (m : ℤ) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * wavePart c K S x m p) K.rect := by
  unfold wavePart
  by_cases hm : m ∈ S.resolved ∪ S.band
  · simp only [hm, if_true, Finset.mul_sum]
    refine integrable_finsetSum _ fun n hn => ?_
    refine (hC n hn m hm).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Complex.add_re]
  · simp only [hm, if_false, mul_zero]
    exact integrableOn_zero

theorem mat_integrable
    (hM : ∀ m ∈ S.resolved, IntegrableOn (fun p : ℝ × ℝ => p.1 * matrixCrossDensity c K S x m p) K.rect) (m : ℤ) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * matPart c K S x m p) K.rect := by
  unfold matPart
  by_cases hm : m ∈ S.resolved
  · simp only [hm, if_true]
    exact hM m hm
  · simp only [hm, if_false, mul_zero]
    exact integrableOn_zero

theorem wave_sum_eq {T : Finset ℤ} (hTY : S.resolved ∪ S.band ⊆ T)
    (hC : ∀ n ∈ S.resolved, ∀ m ∈ S.resolved ∪ S.band, IntegrableOn (fun p : ℝ × ℝ => p.1 *
      (pairWave c n m p (lowGrad c K S x n p) (lowVel c K S x n p) (sharpGrad c K S x m p) (sharpVel c K S x m p)
        + pairWave c m n p (sharpGrad c K S x m p) (sharpVel c K S x m p) (lowGrad c K S x n p)
          (lowVel c K S x n p)).re) K.rect) :
    ∑ m ∈ T, ∫ p in K.rect, p.1 * wavePart c K S x m p = crossOn c K S x (↑(S.resolved ∪ S.band)) := by
  have h1 : ∀ m, ∫ p in K.rect, p.1 * wavePart c K S x m p
      = if m ∈ S.resolved ∪ S.band then ∑ n ∈ S.resolved, ∫ p in K.rect, p.1 *
          (pairWave c n m p (lowGrad c K S x n p) (lowVel c K S x n p) (sharpGrad c K S x m p) (sharpVel c K S x m p)
            + pairWave c m n p (sharpGrad c K S x m p) (sharpVel c K S x m p) (lowGrad c K S x n p)
              (lowVel c K S x n p)).re
        else 0 := by
    intro m
    unfold wavePart
    by_cases hm : m ∈ S.resolved ∪ S.band
    · simp only [hm, if_true, Finset.mul_sum]
      rw [integral_finsetSum _ fun n hn => (hC n hn m hm).congr (Filter.Eventually.of_forall fun p => by
        simp only [Complex.add_re])]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [Complex.add_re]
    · simp only [hm, if_false, mul_zero, integral_zero]
  rw [Finset.sum_congr rfl fun m _ => h1 m, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hTY, Finset.sum_comm]
  unfold crossOn
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [tsum_eq_sum (s := S.resolved ∪ S.band) (fun m hm => by
    simp only [Finset.mem_coe, hm, ↓reduceIte, Complex.zero_re, mul_zero, integral_zero])]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finset.mem_coe, hm, ↓reduceIte]

theorem mat_sum_eq {T : Finset ℤ} (hRY : S.resolved ⊆ T) :
    ∑ m ∈ T, ∫ p in K.rect, p.1 * matPart c K S x m p = matrixCross c K S x := by
  have h1 : ∀ m, ∫ p in K.rect, p.1 * matPart c K S x m p
      = if m ∈ S.resolved then ∫ p in K.rect, p.1 * matrixCrossDensity c K S x m p else 0 := by
    intro m
    unfold matPart
    by_cases hm : m ∈ S.resolved
    · simp only [hm, if_true]
    · simp only [hm, if_false, mul_zero, integral_zero]
  rw [Finset.sum_congr rfl fun m _ => h1 m, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hRY]
  rfl

theorem lin_zero {α : ℝ} {B : CellBases} {Cl : CellClasses} {slots : ℕ} {R : CellRows N slots k}
    (hd : IsCellData α c K S B Cl R) (ζ : Fin k → ℝ) (m : ℤ) (hm : m ∉ R.yModes) :
    ∫ p in K.rect, p.1 * linPart c K S x ζ m p = 0 := by
  apply integral_eq_zero_of_ae
  have hU : (Ioo K.r₁ K.r₂ ×ˢ Ioo K.z₁ K.z₂ : Set (ℝ × ℝ)) =ᵐ[volume] K.rect :=
    Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc
  rw [← Measure.restrict_congr_set hU]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
  by_cases h0 : p.1 = 0
  · simp [h0]
  · have hz := fun i => hd.linear_modes m hm p hp h0 i
    have h1 : ∀ i, modeMat c.order m (c.modelActuatorGrad i) p.1 p.2 = 0 := fun i => (hz i).1
    have h2 : ∀ i, modeMat c.order m (c.modelPinField i) p.1 p.2 = 0 := fun i => (hz i).2
    unfold linPart
    simp [h1, h2, entryPairing]

theorem lin_sum_eq {α : ℝ} {B : CellBases} {Cl : CellClasses} {slots : ℕ} {R : CellRows N slots k}
    (hd : IsCellData α c K S B Cl R) (ζ : Fin k → ℝ) :
    ∑ m ∈ R.yModes, ∫ p in K.rect, p.1 * linPart c K S x ζ m p = linearSharp c K S x ζ := by
  have e : linearSharp c K S x ζ = ∑' m : ℤ, ∫ p in K.rect, p.1 * linPart c K S x ζ m p := rfl
  rw [e, tsum_eq_sum (s := R.yModes) (fun m hm => lin_zero c K S x hd ζ m hm)]

end SharpCrossYUnfolded.Internal

open SharpCrossYUnfolded.Internal in
theorem yUnfolded_holds (hReg : YUnfoldedRegularStatement) : YUnfoldedStatement := by
  intro α ha1 ha2 k N c hc hsy K S B Cl slots R hd hw x hx ζ
  obtain ⟨hE, hV, hC, hM⟩ := hReg α ha1 ha2 c hc K S B Cl R hd hw x hx ζ
  have hA := hd.scalars.localMatrix_selfAdjoint
  have hTY : S.resolved ∪ S.band ⊆ R.yModes := hd.yModes_contain
  have hRY : S.resolved ⊆ R.yModes := fun n hn => hTY (Finset.mem_union_left _ hn)
  rw [Finset.sum_congr rfl fun m hm => mode_split hsy hA ζ m (hE m hm) (hV m hm)
    (wave_integrable c K S x hC m) (mat_integrable c K S x hM m),
    Finset.sum_add_distrib, Finset.sum_add_distrib, wave_sum_eq c K S x hTY hC, mat_sum_eq c K S x hRY,
    lin_sum_eq c K S x hd ζ]
  linarith

namespace SharpCrossYUnfolded.Internal

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

theorem sharp_grad_square {B : CellBases} (h3 : ProjCoefStatement) (hK : IsCellBox K) (hB : IsCellBases K B) (m : ℤ)
    (hg : ∀ i q, IsWeightedSquare K (gradMode c.order m x.2.1 i q)) :
    ∀ i q, IsWeightedSquare K (fun p => sharpGrad c K S x m p i q) := by
  intro i q
  by_cases hm : m ∈ S.resolved
  · have e : (fun p => sharpGrad c K S x m p i q)
        = fun p => gradMode c.order m x.2.1 i q p - K.proj S.degHigh S.degHigh (gradMode c.order m x.2.1 i q) p := by
      funext p
      simp only [sharpGrad, lowGrad, hm, if_true, CellBox.lowStrainAt, CellBox.lowStrain]
    rw [e]
    exact (h3 K B hK hB _ (hg i q) S.degHigh).1
  · have e : (fun p => sharpGrad c K S x m p i q) = gradMode c.order m x.2.1 i q := by
      funext p
      simp only [sharpGrad, lowGrad, hm, if_false, Pi.zero_apply, sub_zero]
    rw [e]
    exact hg i q

theorem sharp_vel_square {B : CellBases} (h3 : ProjCoefStatement) (hK : IsCellBox K) (hB : IsCellBases K B) (m : ℤ)
    (hv : ∀ i, IsWeightedSquare K (fun p : ℝ × ℝ => modeVec c.order m x.1 p.1 p.2 i)) :
    ∀ i, IsWeightedSquare K (fun p => sharpVel c K S x m p i) := by
  intro i
  by_cases hm : m ∈ S.resolved
  · have e : (fun p => sharpVel c K S x m p i)
        = fun p => modeVec c.order m x.1 p.1 p.2 i - K.proj (S.degHigh - 1) (S.degHigh - 1)
            (fun p : ℝ × ℝ => modeVec c.order m x.1 p.1 p.2 i) p := by
      funext p
      simp only [sharpVel, lowVel, hm, if_true, CellBox.lowVelocityAt, CellBox.lowVelocity]
    rw [e]
    exact (h3 K B hK hB _ (hv i) (S.degHigh - 1)).1
  · have e : (fun p => sharpVel c K S x m p i) = fun p : ℝ × ℝ => modeVec c.order m x.1 p.1 p.2 i := by
      funext p
      simp only [sharpVel, lowVel, hm, if_false, Pi.zero_apply, sub_zero]
    rw [e]
    exact hv i

end SharpCrossYUnfolded.Internal

open SharpRowIdentity.Internal SharpCrossYUnfolded.Internal in
theorem yUnfoldedRegular_of (hF : FieldModeSquareStatement) (h3 : ProjCoefStatement) (hQ : YStrainSquareStatement)
    (hD : DensityRegularStatement) (hX : WaveCrossRegularStatement) : YUnfoldedRegularStatement := by
  intro α ha1 ha2 k N c hc K S B Cl slots R hd hw x hx ζ
  have hfm := hF K hd.box c.order x.1 x.2.1 x.2.2.1 hx.1
  obtain ⟨hQs, hQv⟩ := hQ α ha1 ha2 c hc K S B Cl R hd hw x hx ζ
  refine ⟨fun m hm => ?_, fun m hm => ?_, hX α ha1 ha2 c hc K S B Cl R hd hw x hx,
    (hD α ha1 ha2 c hc K S B Cl R hd hw x hx).2.2.2.2.2.1⟩
  · exact entry_int K hd.box (sharp_grad_square c K S x h3 hd.box hd.bases m (hfm m).1) (hQs m hm)
  · exact vec_int K hd.box (sharp_vel_square c K S x h3 hd.box hd.bases m (hfm m).2) (hQv m hm)

theorem yUnfolded_of_leaves (hF : FieldModeSquareStatement) (h3 : ProjCoefStatement) (hQ : YStrainSquareStatement)
    (hD : DensityRegularStatement) (hX : WaveCrossRegularStatement) : YUnfoldedStatement :=
  yUnfolded_holds (yUnfoldedRegular_of hF h3 hQ hD hX)

end CellAnalysis

end CellCert

end Breakdown
