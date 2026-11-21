import Breakdown.FracCell.SharpYChargeSt
import Breakdown.FracCell.SharpRowIdentity

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace SharpParts

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (x : FieldTuple k)

def yStrainCoefPart (ζ : Fin k → ℝ) (n : ℤ) (j l : ℕ) : ℝ :=
  if n ∉ S.resolved ∨ S.degHigh < max j l then
    strainLin (sharpStrainCoef c K B x n j l)
      (fun i q => B.coef K (fun p => CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p i q) j l)
  else 0

def yVelocityCoefPart (n : ℤ) (j l : ℕ) : ℝ :=
  if S.degHigh ≤ max j l then
    velLin (sharpVelocityCoef c K B x n j l)
      (fun i => B.coef K (fun p => CellScalars.yVelocity c K S x.1 x.2.1 n p i) j l)
  else 0

def yStrainPairing (ζ : Fin k → ℝ) (n : ℤ) : ℝ :=
  2 * (∫ p in K.rect, ((K.lineWeight p.1 : ℝ) : ℂ) *
    entryPairing (sharpGrad c K S x n p) (CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p)).re

def yVelocityPairing (n : ℤ) : ℝ :=
  2 * (∫ p in K.rect, ((K.lineWeight p.1 : ℝ) : ℂ) *
    CellScalars.vecPair (sharpVel c K S x n p) (CellScalars.yVelocity c K S x.1 x.2.1 n p)).re

end SharpParts

open SharpParts

def ModelStrainSymmetric {k N : ℕ} (c : FracCellData k N) : Prop :=
  ∀ y (u w : Space), inner ℝ (c.modelStrain y u) w = inner ℝ u (c.modelStrain y w)

def SharpCrossSymmStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c → ModelStrainSymmetric c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      CellScalars.sharpForm c K S R B (fun _ => 0) x.2.2.2.1 ζ x.1 x.2.1
          (sharpStrainCoef c K B x) (sharpVelocityCoef c K B x)
        ≤ weightedSharp c K S x B R + crossOn c K S x (↑(S.resolved ∪ S.band)) + linearSharp c K S x ζ
          + matrixCross c K S x

def YTargetSquareStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      (∀ n ∈ R.yModes, ∀ i q, IsWeightedSquare K (fun p => CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p i q)) ∧
      (∀ n ∈ S.resolved, ∀ i, IsWeightedSquare K (fun p => CellScalars.yVelocity c K S x.1 x.2.1 n p i))

def YPairingStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c → ModelStrainSymmetric c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      (∑ n ∈ R.yModes, yStrainPairing c K S x ζ n) + (∑ n ∈ S.resolved, yVelocityPairing c K S x n)
        ≤ crossOn c K S x (↑(S.resolved ∪ S.band)) + linearSharp c K S x ζ + matrixCross c K S x

namespace SharpYSharpCross.Internal

open SharpRowIdentity.Internal

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (x : FieldTuple k)

theorem strain_hasSum (ζ : Fin k → ℝ) (n : ℤ) (h2 : BasisEnergySumStatement) (h3 : ProjCoefStatement)
    (hK : IsCellBox K) (hB : IsCellBases K B)
    (hg : ∀ i q, IsWeightedSquare K (gradMode c.order n x.2.1 i q))
    (hW : ∀ i q, IsWeightedSquare K (fun p => CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p i q)) :
    HasSum (fun jl : ℕ × ℕ => yStrainCoefPart c K S B x ζ n jl.1 jl.2) (yStrainPairing c K S x ζ n) := by
  by_cases hr : n ∈ S.resolved
  · have hP := fun i q => h3 K B hK hB _ (hg i q) S.degHigh
    have hs := h2 K B hK hB (Fin 3 × Fin 3)
      (fun iq p => gradMode c.order n x.2.1 iq.1 iq.2 p - K.proj S.degHigh S.degHigh (gradMode c.order n x.2.1 iq.1 iq.2) p)
      (fun iq p => CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p iq.1 iq.2)
      (fun iq => (hP iq.1 iq.2).1) (fun iq => hW iq.1 iq.2)
    have hre := (hs.mapL Complex.reCLM).mul_left 2
    convert hre using 1
    · rfl
    · funext jl
      obtain ⟨j, l⟩ := jl
      simp only [Complex.reCLM_apply]
      unfold yStrainCoefPart
      by_cases hlt : S.degHigh < max j l
      · rw [if_pos (Or.inr hlt), strainLin_eq]
        congr 2
        unfold entryPairing sharpStrainCoef
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q _ => ?_
        rw [(hP i q).2 j l, if_neg (not_le.2 hlt)]
      · rw [if_neg (by simp [hr, hlt])]
        have h0 : ∀ i q : Fin 3, B.coef K (fun p => gradMode c.order n x.2.1 i q p
            - K.proj S.degHigh S.degHigh (gradMode c.order n x.2.1 i q) p) j l = 0 := fun i q => by
          rw [(hP i q).2 j l, if_pos (not_lt.1 hlt)]
        rw [Fintype.sum_prod_type]
        simp only [h0, zero_mul, Finset.sum_const_zero, Complex.zero_re, mul_zero]
    · simp only [Complex.reCLM_apply]
      unfold yStrainPairing
      congr 3
      funext p
      unfold entryPairing sharpGrad lowGrad
      rw [Fintype.sum_prod_type]
      simp only [hr, if_true, CellBox.lowStrainAt, CellBox.lowStrain]
  · have hs := h2 K B hK hB (Fin 3 × Fin 3)
      (fun iq p => gradMode c.order n x.2.1 iq.1 iq.2 p)
      (fun iq p => CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p iq.1 iq.2)
      (fun iq => hg iq.1 iq.2) (fun iq => hW iq.1 iq.2)
    have hre := (hs.mapL Complex.reCLM).mul_left 2
    convert hre using 1
    · rfl
    · funext jl
      obtain ⟨j, l⟩ := jl
      simp only [Complex.reCLM_apply]
      unfold yStrainCoefPart
      rw [if_pos (Or.inl hr), strainLin_eq]
      congr 2
      unfold entryPairing sharpStrainCoef
      rw [Fintype.sum_prod_type]
    · simp only [Complex.reCLM_apply]
      unfold yStrainPairing
      congr 3
      funext p
      unfold entryPairing sharpGrad lowGrad
      rw [Fintype.sum_prod_type]
      simp only [hr, if_false, Pi.zero_apply, sub_zero]

theorem velocity_hasSum (n : ℤ) (hn : n ∈ S.resolved)
    (hdeg : 1 ≤ S.degHigh) (h2 : BasisEnergySumStatement) (h3 : ProjCoefStatement)
    (hK : IsCellBox K) (hB : IsCellBases K B)
    (hv : ∀ i, IsWeightedSquare K (fun p : ℝ × ℝ => modeVec c.order n x.1 p.1 p.2 i))
    (hW : ∀ i, IsWeightedSquare K (fun p => CellScalars.yVelocity c K S x.1 x.2.1 n p i)) :
    HasSum (fun jl : ℕ × ℕ => yVelocityCoefPart c K S B x n jl.1 jl.2) (yVelocityPairing c K S x n) := by
  have hP := fun i => h3 K B hK hB _ (hv i) (S.degHigh - 1)
  have hs := h2 K B hK hB (Fin 3)
    (fun i p => modeVec c.order n x.1 p.1 p.2 i
      - K.proj (S.degHigh - 1) (S.degHigh - 1) (fun p : ℝ × ℝ => modeVec c.order n x.1 p.1 p.2 i) p)
    (fun i p => CellScalars.yVelocity c K S x.1 x.2.1 n p i)
    (fun i => (hP i).1) hW
  have hre := (hs.mapL Complex.reCLM).mul_left 2
  convert hre using 1
  · rfl
  · funext jl
    obtain ⟨j, l⟩ := jl
    simp only [Complex.reCLM_apply]
    unfold yVelocityCoefPart
    by_cases hlt : S.degHigh ≤ max j l
    · rw [if_pos hlt]
      unfold velLin CellScalars.vecPair sharpVelocityCoef
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [(hP i).2 j l, if_neg (by omega)]
    · rw [if_neg hlt]
      have h0 : ∀ i : Fin 3, B.coef K (fun p => modeVec c.order n x.1 p.1 p.2 i
          - K.proj (S.degHigh - 1) (S.degHigh - 1) (fun p : ℝ × ℝ => modeVec c.order n x.1 p.1 p.2 i) p) j l = 0 :=
        fun i => by rw [(hP i).2 j l, if_pos (by omega)]
      simp only [h0, zero_mul, Finset.sum_const_zero, Complex.zero_re, mul_zero]
  · simp only [Complex.reCLM_apply]
    unfold yVelocityPairing
    congr 3
    funext p
    unfold CellScalars.vecPair sharpVel lowVel
    simp only [hn, if_true, CellBox.lowVelocityAt, CellBox.lowVelocity]

end SharpYSharpCross.Internal


namespace SharpYSharpCross.Internal

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (x : FieldTuple k)

theorem strain_term_split (ζ : Fin k → ℝ) {slots : ℕ} (R : CellRows N slots k) (n : ℤ) (j l : ℕ) :
    CellScalars.sharpStrainTerm c K S R B (fun _ => 0) x.2.2.2.1 ζ x.1 x.2.1 (sharpStrainCoef c K B x) n j l
      = (if n ∉ S.resolved ∨ S.degHigh < max j l then
          S.symWeight n j l * symSq (sharpStrainCoef c K B x n j l)
            + S.antiWeight n j l * antiSq (sharpStrainCoef c K B x n j l)
        else 0) + yStrainCoefPart c K S B x ζ n j l := by
  have ht : CellScalars.targetStrain c K S R B (fun _ => 0) x.2.2.2.1 ζ x.1 x.2.1 n j l
      = fun i q => B.coef K (fun p => CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p i q) j l := by
    funext i q
    simp only [CellScalars.targetStrain]
    split_ifs <;> simp
  unfold CellScalars.sharpStrainTerm yStrainCoefPart
  split_ifs with h
  · rw [ht]
    unfold strainPen strainLin
    ring
  · simp

theorem velocity_term_split {slots : ℕ} (R : CellRows N slots k) (n : ℤ) (j l : ℕ) :
    CellScalars.sharpVelocityTerm c K S R B (fun _ => 0) x.1 x.2.1 (sharpVelocityCoef c K B x) n j l
      = (if S.degHigh ≤ max j l then S.velWeight n j l * vecSq (sharpVelocityCoef c K B x n j l) else 0)
        + yVelocityCoefPart c K S B x n j l := by
  have ht : CellScalars.targetVelocity c K S R B (fun _ => 0) x.1 x.2.1 n j l
      = fun i => B.coef K (fun p => CellScalars.yVelocity c K S x.1 x.2.1 n p i) j l := by
    funext i
    simp [CellScalars.targetVelocity]
  unfold CellScalars.sharpVelocityTerm yVelocityCoefPart
  split_ifs with h
  · rw [ht]
    unfold velPen velLin
    ring
  · simp

end SharpYSharpCross.Internal

open SharpRowIdentity.Internal SharpYSharpCross.Internal in
theorem sharpCross_of (h2 : BasisEnergySumStatement) (h3 : ProjCoefStatement) (hF : FieldModeSquareStatement)
    (hT : YTargetSquareStatement) (hE : SharpEnergyStatement) (hI : YPairingStatement) : SharpCrossSymmStatement := by
  intro α ha1 ha2 k N c hc hsy K S B Cl slots R hd hw x hx ζ
  have hK := hd.box
  have hB := hd.bases
  have hdeg := hd.scalars.degrees
  have hfm := hF K hK c.order x.1 x.2.1 x.2.2.1 hx.1
  obtain ⟨hTy, hTv⟩ := hT α ha1 ha2 c hc K S B Cl R hd hw x hx ζ
  have hS := fun n (hn : n ∈ R.yModes) => strain_hasSum c K S B x ζ n h2 h3 hK hB (hfm n).1 (hTy n hn)
  have hV := fun n (hn : n ∈ S.resolved) =>
    velocity_hasSum c K S B x n hn (by omega) h2 h3 hK hB (hfm n).2 (hTv n hn)
  have hWs : Summable (fun jl : ℕ × ℕ => if S.degNear < max jl.1 jl.2 then
        (∑ n ∈ R.yModes, if n ∉ S.resolved ∨ S.degHigh < max jl.1 jl.2 then
            S.symWeight n jl.1 jl.2 * symSq (sharpStrainCoef c K B x n jl.1 jl.2)
              + S.antiWeight n jl.1 jl.2 * antiSq (sharpStrainCoef c K B x n jl.1 jl.2)
          else 0)
        + ∑ n ∈ S.resolved, if S.degHigh ≤ max jl.1 jl.2 then
            S.velWeight n jl.1 jl.2 * vecSq (sharpVelocityCoef c K B x n jl.1 jl.2) else 0
      else 0) := by
    refine (hE α ha1 ha2 c hc K S B Cl R hd hw x hx).congr fun jl => ?_
    by_cases hj : S.degNear < max jl.1 jl.2
    · have h1 : S.degHigh < max jl.1 jl.2 := by omega
      have h1' : S.degHigh ≤ max jl.1 jl.2 := by omega
      simp only [hj, h1, h1', or_true, if_true]
    · simp only [hj, if_false]
  have hSf : ∀ n ∈ R.yModes, Summable (fun jl : ℕ × ℕ =>
      if S.degNear < max jl.1 jl.2 then yStrainCoefPart c K S B x ζ n jl.1 jl.2 else 0) :=
    fun n hn => summable_far S.degNear (fun j l => yStrainCoefPart c K S B x ζ n j l) (hS n hn).summable
  have hVf : ∀ n ∈ S.resolved, Summable (fun jl : ℕ × ℕ =>
      if S.degNear < max jl.1 jl.2 then yVelocityCoefPart c K S B x n jl.1 jl.2 else 0) :=
    fun n hn => summable_far S.degNear (fun j l => yVelocityCoefPart c K S B x n j l) (hV n hn).summable
  have hfar : ∑' jl : ℕ × ℕ, CellScalars.sharpFarTerm c K S R B (fun _ => 0) x.2.2.2.1 ζ x.1 x.2.1
        (sharpStrainCoef c K B x) (sharpVelocityCoef c K B x) jl
      = (∑' jl : ℕ × ℕ, if S.degNear < max jl.1 jl.2 then
          (∑ n ∈ R.yModes, if n ∉ S.resolved ∨ S.degHigh < max jl.1 jl.2 then
              S.symWeight n jl.1 jl.2 * symSq (sharpStrainCoef c K B x n jl.1 jl.2)
                + S.antiWeight n jl.1 jl.2 * antiSq (sharpStrainCoef c K B x n jl.1 jl.2)
            else 0)
          + ∑ n ∈ S.resolved, if S.degHigh ≤ max jl.1 jl.2 then
              S.velWeight n jl.1 jl.2 * vecSq (sharpVelocityCoef c K B x n jl.1 jl.2) else 0
        else 0)
        + ((∑ n ∈ R.yModes, ∑' jl : ℕ × ℕ,
            if S.degNear < max jl.1 jl.2 then yStrainCoefPart c K S B x ζ n jl.1 jl.2 else 0)
          + ∑ n ∈ S.resolved, ∑' jl : ℕ × ℕ,
            if S.degNear < max jl.1 jl.2 then yVelocityCoefPart c K S B x n jl.1 jl.2 else 0) := by
    have e : (fun jl : ℕ × ℕ => CellScalars.sharpFarTerm c K S R B (fun _ => 0) x.2.2.2.1 ζ x.1 x.2.1
        (sharpStrainCoef c K B x) (sharpVelocityCoef c K B x) jl)
        = fun jl : ℕ × ℕ => (if S.degNear < max jl.1 jl.2 then
          (∑ n ∈ R.yModes, if n ∉ S.resolved ∨ S.degHigh < max jl.1 jl.2 then
              S.symWeight n jl.1 jl.2 * symSq (sharpStrainCoef c K B x n jl.1 jl.2)
                + S.antiWeight n jl.1 jl.2 * antiSq (sharpStrainCoef c K B x n jl.1 jl.2)
            else 0)
          + ∑ n ∈ S.resolved, if S.degHigh ≤ max jl.1 jl.2 then
              S.velWeight n jl.1 jl.2 * vecSq (sharpVelocityCoef c K B x n jl.1 jl.2) else 0
        else 0)
        + ((∑ n ∈ R.yModes, if S.degNear < max jl.1 jl.2 then yStrainCoefPart c K S B x ζ n jl.1 jl.2 else 0)
          + ∑ n ∈ S.resolved, if S.degNear < max jl.1 jl.2 then yVelocityCoefPart c K S B x n jl.1 jl.2 else 0) := by
      funext jl
      unfold CellScalars.sharpFarTerm
      by_cases hj : S.degNear < max jl.1 jl.2
      · simp only [hj, if_true, strain_term_split, velocity_term_split, Finset.sum_add_distrib]
        ring
      · simp only [hj, if_false, Finset.sum_const_zero, add_zero]
    rw [e, Summable.tsum_add hWs ((summable_sum hSf).add (summable_sum hVf)),
      Summable.tsum_add (summable_sum hSf) (summable_sum hVf),
      Summable.tsum_finsetSum hSf, Summable.tsum_finsetSum hVf]
  have eY : ∑ n ∈ R.yModes, yStrainPairing c K S x ζ n
      = ∑ n ∈ R.yModes, ((∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
          yStrainCoefPart c K S B x ζ n j l)
        + ∑' jl : ℕ × ℕ, if S.degNear < max jl.1 jl.2 then yStrainCoefPart c K S B x ζ n jl.1 jl.2 else 0) :=
    Finset.sum_congr rfl fun n hn => (hS n hn).tsum_eq.symm.trans
      (tsum_split S.degNear (fun j l => yStrainCoefPart c K S B x ζ n j l) (hS n hn).summable)
  have eV : ∑ n ∈ S.resolved, yVelocityPairing c K S x n
      = ∑ n ∈ S.resolved, ((∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
          yVelocityCoefPart c K S B x n j l)
        + ∑' jl : ℕ × ℕ, if S.degNear < max jl.1 jl.2 then yVelocityCoefPart c K S B x n jl.1 jl.2 else 0) :=
    Finset.sum_congr rfl fun n hn => (hV n hn).tsum_eq.symm.trans
      (tsum_split S.degNear (fun j l => yVelocityCoefPart c K S B x n j l) (hV n hn).summable)
  have key : CellScalars.sharpForm c K S R B (fun _ => 0) x.2.2.2.1 ζ x.1 x.2.1
        (sharpStrainCoef c K B x) (sharpVelocityCoef c K B x)
      = weightedSharp c K S x B R + ((∑ n ∈ R.yModes, yStrainPairing c K S x ζ n)
        + ∑ n ∈ S.resolved, yVelocityPairing c K S x n) := by
    unfold CellScalars.sharpForm weightedSharp
    rw [hfar, eY, eV]
    simp only [strain_term_split, velocity_term_split, Finset.sum_add_distrib]
    ring
  have hI' := hI α ha1 ha2 c hc hsy K S B Cl R hd hw x hx ζ
  rw [key]
  linarith


namespace SharpParts

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

def yStrainUnfolded (ζ : Fin k → ℝ) (n : ℤ) : ℝ :=
  2 * (∫ p in K.rect, ((K.lineWeight p.1 : ℝ) : ℂ) *
    entryPairing (sharpGrad c K S x n p) (CellScalars.yStrain c K S x.2.2.2.1 ζ x.1 x.2.1 n p)).re

end SharpParts

def YStrainSquareStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      (∀ n ∈ R.yModes, ∀ i q, IsWeightedSquare K (fun p => CellScalars.yStrain c K S x.2.2.2.1 ζ x.1 x.2.1 n p i q)) ∧
      (∀ n ∈ R.yModes, ∀ i, IsWeightedSquare K (fun p => CellScalars.yVelocity c K S x.1 x.2.1 n p i))

def YUnfoldedStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c → ModelStrainSymmetric c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      (∑ n ∈ R.yModes, (yStrainUnfolded c K S x ζ n + yVelocityPairing c K S x n))
        ≤ crossOn c K S x (↑(S.resolved ∪ S.band)) + linearSharp c K S x ζ + matrixCross c K S x

open SharpRowIdentity.Internal in
theorem yPairing_of (hF : FieldModeSquareStatement) (hQ : YStrainSquareStatement) (hT : ModeTurnStatement)
    (hU : YUnfoldedStatement) : YPairingStatement := by
  intro α ha1 ha2 k N c hc hsy K S B Cl slots R hd hw x hx ζ
  have hfm := hF K hd.box c.order x.1 x.2.1 x.2.2.1 hx.1
  obtain ⟨hQs, hQv⟩ := hQ α ha1 ha2 c hc K S B Cl R hd hw x hx ζ
  have hRY : S.resolved ⊆ R.yModes := fun n hn => hd.yModes_contain (Finset.mem_union_left _ hn)
  have hm : ∀ n ∈ R.yModes, yStrainPairing c K S x ζ n
      = yStrainUnfolded c K S x ζ n + (if n ∈ S.resolved then 0 else yVelocityPairing c K S x n) := by
    intro n hn
    by_cases hres : n ∈ S.resolved
    · unfold yStrainPairing yStrainUnfolded CellScalars.yFolded
      simp only [hres, if_true, add_zero]
    · rw [if_neg hres]
      have hg : sharpGrad c K S x n = fun p a b => gradMode c.order n x.2.1 a b p := by
        funext p a b
        simp [sharpGrad, lowGrad, hres]
      have hv : sharpVel c K S x n = fun p a => modeVec c.order n x.1 p.1 p.2 a := by
        funext p a
        simp [sharpVel, lowVel, hres]
      have hmn := hd.scalars.unresolved_large n hres
      unfold modeNumber at hmn
      have hk : azimuth c.order n ≠ 0 := by
        intro h
        rw [h, abs_zero] at hmn
        norm_num at hmn
      have hk1 : azimuth c.order n ^ 2 ≠ 1 := by
        intro h
        have : |azimuth c.order n| ^ 2 = 1 := by rw [sq_abs]; exact h
        nlinarith
      unfold yStrainPairing yStrainUnfolded yVelocityPairing
      rw [hg, hv]
      have hae : ∀ᵐ p ∂(volume.restrict K.rect),
          ((K.lineWeight p.1 : ℝ) : ℂ) * entryPairing (fun a b => gradMode c.order n x.2.1 a b p)
              (CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p)
            = ((K.lineWeight p.1 : ℝ) : ℂ) * entryPairing (fun a b => gradMode c.order n x.2.1 a b p)
                (CellScalars.yStrain c K S x.2.2.2.1 ζ x.1 x.2.1 n p)
              + ((K.lineWeight p.1 : ℝ) : ℂ) * CellScalars.vecPair (fun a => modeVec c.order n x.1 p.1 p.2 a)
                (CellScalars.yVelocity c K S x.1 x.2.1 n p) := by
        filter_upwards [hT c.order x.1 x.2.1 x.2.2.1 hx.1 K hd.box n] with p hp
        unfold CellScalars.yFolded
        rw [if_neg hres]
        have e := foldPair _ p.1 hk hk1 (fun i q => gradMode c.order n x.2.1 i q p)
          (CellScalars.yStrain c K S x.2.2.2.1 ζ x.1 x.2.1 n p) (fun i => modeVec c.order n x.1 p.1 p.2 i)
          (CellScalars.yVelocity c K S x.1 x.2.1 n p) hp
        rw [e]
        ring
      rw [integral_congr_ae hae, integral_add (entry_int K hd.box (hfm n).1 (hQs n hn))
        (vec_int K hd.box (hfm n).2 (hQv n hn)), Complex.add_re]
      ring
  have hV : ∑ n ∈ S.resolved, yVelocityPairing c K S x n
      = ∑ n ∈ R.yModes, (if n ∈ S.resolved then yVelocityPairing c K S x n else 0) := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hRY]
  have hU' := hU α ha1 ha2 c hc hsy K S B Cl R hd hw x hx ζ
  rw [Finset.sum_congr rfl hm, hV, ← Finset.sum_add_distrib]
  refine le_trans (le_of_eq ?_) hU'
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> ring


namespace SharpYSharpCross.Internal

variable {k N : ℕ} (c : FracCellData k N)

theorem frameMat_strain_symm (hsy : ModelStrainSymmetric c) (θ : ℝ) (y : Space) (a b : Fin 3) :
    frameMat θ (c.modelStrain y) a b = frameMat θ (c.modelStrain y) b a := by
  unfold frameMat
  rw [hsy]
  exact real_inner_comm _ _

theorem strainMode_neg (hsy : ModelStrainSymmetric c) (β : ℤ) (p : ℝ × ℝ) (a b : Fin 3) :
    CellScalars.strainMode c (-β) p a b = (starRingEnd ℂ) (CellScalars.strainMode c β p b a) := by
  unfold CellScalars.strainMode modeMat
  have h2 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [intervalIntegral.integral_of_le h2, intervalIntegral.integral_of_le h2, map_mul, ← integral_conj]
  congr 1
  · rw [map_div₀, map_one, map_mul, map_ofNat, Complex.conj_ofReal]
  · congr 1
    funext θ
    rw [map_mul, ← Complex.exp_conj, Complex.conj_ofReal, frameMat_strain_symm c hsy θ]
    congr 2
    simp only [azimuth, Int.cast_neg, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring

theorem entry_re_swap (X Y : Fin 3 → Fin 3 → ℂ) :
    ((1 / 2 : ℂ) * entryPairing X Y).re = ((1 / 2 : ℂ) * entryPairing Y X).re := by
  have e : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  congr 1
  simp only [entryPairing, Fin.sum_univ_three, Complex.mul_re, Complex.add_re, Complex.conj_re, Complex.conj_im]
  ring

theorem pairWave_re_swap (n n' : ℤ) (p : ℝ × ℝ)
    (hS : ∀ a b, CellScalars.strainMode c (n' - n) p a b = (starRingEnd ℂ) (CellScalars.strainMode c (n - n') p b a))
    (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (s' : Fin 3 → Fin 3 → ℂ) (v' : Fin 3 → ℂ) :
    (pairWave c n n' p s v s' v').re = (pairWave c n' n p s' v' s v).re := by
  unfold pairWave waveForm
  simp only [Complex.add_re, Complex.neg_re]
  have h1 : (∑ a : Fin 3, (starRingEnd ℂ) (curlComp s a) *
        ∑ b : Fin 3, CellScalars.strainMode c (n - n') p a b * curlComp s' b).re
      = (∑ a : Fin 3, (starRingEnd ℂ) (curlComp s' a) *
        ∑ b : Fin 3, CellScalars.strainMode c (n' - n) p a b * curlComp s b).re := by
    simp only [hS]
    simp only [Fin.sum_univ_three, Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.add_im, Complex.mul_im]
    ring
  rw [h1, entry_re_swap (couplingMap _ v') s, entry_re_swap s' (couplingMap _ v)]
  ring

theorem pairWave_re_swap_of_symm (hsy : ModelStrainSymmetric c) (n n' : ℤ) (p : ℝ × ℝ)
    (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (s' : Fin 3 → Fin 3 → ℂ) (v' : Fin 3 → ℂ) :
    (pairWave c n n' p s v s' v').re = (pairWave c n' n p s' v' s v).re := by
  refine pairWave_re_swap c n n' p (fun a b => ?_) s v s' v'
  rw [← strainMode_neg c hsy (n - n') p a b, neg_sub]

end SharpYSharpCross.Internal


namespace SharpYSharpCross.Internal

variable {k N : ℕ} (c : FracCellData k N)

theorem coupling_adj (G : Fin 3 → Fin 3 → ℂ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) :
    CellScalars.vecPair v (couplingAdj G s) = (starRingEnd ℂ) (entryPairing s (couplingMap G v)) := by
  simp [CellScalars.vecPair, entryPairing, couplingAdj, couplingMap, bracketMat, Fin.sum_univ_three, CellCert.permSign, map_ofNat]
  ring

theorem curl_adj (s : Fin 3 → Fin 3 → ℂ) (u : Fin 3 → ℂ) :
    entryPairing s (curlAdj u) = ∑ i : Fin 3, curlComp s i * (starRingEnd ℂ) (u i) := by
  simp [entryPairing, curlAdj, curlComp, Fin.sum_univ_three, CellCert.permSign]
  ring

theorem wave_pair (hsy : ModelStrainSymmetric c) (m n : ℤ) (p : ℝ × ℝ)
    (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (Ls : Fin 3 → Fin 3 → ℂ) (Lv : Fin 3 → ℂ) :
    2 * (entryPairing s (waveActionStrain (CellScalars.strainMode c (m - n) p) (CellScalars.curlGradMode c (m - n) p) Ls Lv)
        + CellScalars.vecPair v (waveActionVelocity (CellScalars.curlGradMode c (n - m) p) Ls)).re
      = (pairWave c n m p Ls Lv s v).re + (pairWave c m n p s v Ls Lv).re := by
  rw [pairWave_re_swap_of_symm c hsy n m p Ls Lv s v]
  have e1 : entryPairing s (waveActionStrain (CellScalars.strainMode c (m - n) p) (CellScalars.curlGradMode c (m - n) p) Ls Lv)
      = -entryPairing s (curlAdj (matVec (CellScalars.strainMode c (m - n) p) (curlComp Ls)))
        + (1 / 2 : ℂ) * (starRingEnd ℂ) (entryPairing (couplingMap (CellScalars.curlGradMode c (m - n) p) Lv) s) := by
    simp only [waveActionStrain, entryPairing, map_mul, Complex.conj_conj, map_add, map_neg, map_div₀, map_one,
      map_ofNat, Fin.sum_univ_three]
    ring
  have e2 : CellScalars.vecPair v (waveActionVelocity (CellScalars.curlGradMode c (n - m) p) Ls)
      = (1 / 2 : ℂ) * (starRingEnd ℂ) (entryPairing Ls (couplingMap (CellScalars.curlGradMode c (n - m) p) v)) := by
    have h := coupling_adj (CellScalars.curlGradMode c (n - m) p) Ls v
    simp only [waveActionVelocity, CellScalars.vecPair, map_mul, map_div₀, map_one, map_ofNat] at h ⊢
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [e1, e2, curl_adj]
  unfold pairWave waveForm matVec
  simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.re_sum,
    Complex.im_sum, Complex.mul_im]
  norm_num
  ring

end SharpYSharpCross.Internal


namespace SharpYSharpCross.Internal

theorem split_pair (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (U : Fin 12 → ℂ) :
    entryPairing s (splitStrain U) + CellScalars.vecPair v (splitVelocity U)
      = ∑ i, pairVec s v i * (starRingEnd ℂ) (U i) := by
  simp [entryPairing, CellScalars.vecPair, splitStrain, splitVelocity, pairVec, Fin.sum_univ_succ]
  ring

theorem matrix_pair (A : Matrix (Fin 12) (Fin 12) ℂ) (hA : A.IsHermitian) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ)
    (Ls : Fin 3 → Fin 3 → ℂ) (Lv : Fin 3 → ℂ) :
    2 * (entryPairing s (splitStrain (matAct A (pairVec Ls Lv)))
        + CellScalars.vecPair v (splitVelocity (matAct A (pairVec Ls Lv)))).re
      = (∑ i, ∑ j, ((starRingEnd ℂ) (pairVec Ls Lv i) * A i j * pairVec s v j
          + (starRingEnd ℂ) (pairVec s v i) * A i j * pairVec Ls Lv j)).re := by
  rw [split_pair]
  have hX : (∑ i, pairVec s v i * (starRingEnd ℂ) (matAct A (pairVec Ls Lv) i))
      = ∑ i, ∑ j, (starRingEnd ℂ) (pairVec Ls Lv i) * A i j * pairVec s v j := by
    simp only [matAct, map_sum, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [show (starRingEnd ℂ) (A b a) = A a b from hA.apply a b]
    ring
  have hY : (∑ i, ∑ j, (starRingEnd ℂ) (pairVec s v i) * A i j * pairVec Ls Lv j)
      = (starRingEnd ℂ) (∑ i, pairVec s v i * (starRingEnd ℂ) (matAct A (pairVec Ls Lv) i)) := by
    simp only [matAct, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  simp only [Finset.sum_add_distrib, Complex.add_re]
  rw [← hX, hY, Complex.conj_re]
  ring

end SharpYSharpCross.Internal

namespace SharpYSharpCross.Internal

theorem lw_rHat (K : CellBox) (p : ℝ × ℝ) : K.lineWeight p.1 * CellScalars.rHat K p = p.1 := by
  unfold CellScalars.rHat CellBox.lineWeight
  split_ifs
  · by_cases h : p.1 = 0
    · simp [h]
    · field_simp
  · simp

theorem ep_scale3 (s W M L : Fin 3 → Fin 3 → ℂ) (r : ℝ) :
    entryPairing s (fun a b => (r : ℂ) * (W a b + M a b + L a b))
      = (r : ℂ) * (entryPairing s W + entryPairing s M + entryPairing s L) := by
  simp only [entryPairing, Fin.sum_univ_three, map_add, map_mul, Complex.conj_ofReal]
  ring

theorem vp_scale2 (v W M : Fin 3 → ℂ) (r : ℝ) :
    CellScalars.vecPair v (fun a => (r : ℂ) * (W a + M a))
      = (r : ℂ) * (CellScalars.vecPair v W + CellScalars.vecPair v M) := by
  simp only [CellScalars.vecPair, Fin.sum_univ_three, map_add, map_mul, Complex.conj_ofReal]
  ring

theorem ep_finsum {ι : Type} (T : Finset ι) (s : Fin 3 → Fin 3 → ℂ) (X : ι → Fin 3 → Fin 3 → ℂ) :
    entryPairing s (fun a b => ∑ n ∈ T, X n a b) = ∑ n ∈ T, entryPairing s (X n) := by
  simp only [entryPairing, map_sum, Finset.mul_sum]
  exact (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans Finset.sum_comm

theorem vp_finsum {ι : Type} (T : Finset ι) (v : Fin 3 → ℂ) (X : ι → Fin 3 → ℂ) :
    CellScalars.vecPair v (fun a => ∑ n ∈ T, X n a) = ∑ n ∈ T, CellScalars.vecPair v (X n) := by
  simp only [CellScalars.vecPair, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem ep_lin {k : ℕ} (s : Fin 3 → Fin 3 → ℂ) (κ ζ : Fin k → ℝ) (P Q : Fin k → Fin 3 → Fin 3 → ℂ) :
    2 * (entryPairing s (fun a b => ∑ i : Fin k, (((κ i / 2 : ℝ) : ℂ) * P i a b + ((ζ i : ℝ) : ℂ) * Q i a b))).re
      = (∑ i : Fin k, (((κ i : ℝ) : ℂ) * entryPairing s (P i) + ((2 * ζ i : ℝ) : ℂ) * entryPairing s (Q i))).re := by
  have e : entryPairing s (fun a b => ∑ i : Fin k, (((κ i / 2 : ℝ) : ℂ) * P i a b + ((ζ i : ℝ) : ℂ) * Q i a b))
      = ∑ i : Fin k, (((κ i / 2 : ℝ) : ℂ) * entryPairing s (P i) + ((ζ i : ℝ) : ℂ) * entryPairing s (Q i)) := by
    rw [ep_finsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [entryPairing, Fin.sum_univ_three, map_add, map_mul, Complex.conj_ofReal]
    ring
  rw [e, ← Complex.re_ofReal_mul]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

end SharpYSharpCross.Internal

namespace SharpYSharpCross.Internal

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

theorem wave_sum (hsy : ModelStrainSymmetric c) (m : ℤ) (p : ℝ × ℝ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) :
    2 * (entryPairing s (fun a b => ∑ n ∈ S.resolved, waveActionStrain (CellScalars.strainMode c (m - n) p)
          (CellScalars.curlGradMode c (m - n) p) (K.lowStrainAt c.order n S.degHigh x.2.1 p)
          (K.lowVelocityAt c.order n S.degHigh x.1 p) a b)
        + CellScalars.vecPair v (fun b => ∑ n ∈ S.resolved, waveActionVelocity (CellScalars.curlGradMode c (n - m) p)
          (K.lowStrainAt c.order n S.degHigh x.2.1 p) b)).re
      = ∑ n ∈ S.resolved, ((pairWave c n m p (lowGrad c K S x n p) (lowVel c K S x n p) s v).re
          + (pairWave c m n p s v (lowGrad c K S x n p) (lowVel c K S x n p)).re) := by
  rw [ep_finsum, vp_finsum, ← Finset.sum_add_distrib, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hg : lowGrad c K S x n p = K.lowStrainAt c.order n S.degHigh x.2.1 p := by simp [lowGrad, hn]
  have hv : lowVel c K S x n p = K.lowVelocityAt c.order n S.degHigh x.1 p := by simp [lowVel, hn]
  rw [hg, hv]
  exact wave_pair c hsy m n p s v _ _

theorem unfolded_pointwise (hsy : ModelStrainSymmetric c) (hA : ∀ n p, (S.localMatrix n p).IsHermitian)
    (ζ : Fin k → ℝ) (m : ℤ) (p : ℝ × ℝ) :
    2 * (((K.lineWeight p.1 : ℝ) : ℂ) * entryPairing (sharpGrad c K S x m p)
          (CellScalars.yStrain c K S x.2.2.2.1 ζ x.1 x.2.1 m p)
        + ((K.lineWeight p.1 : ℝ) : ℂ) * CellScalars.vecPair (sharpVel c K S x m p)
          (CellScalars.yVelocity c K S x.1 x.2.1 m p)).re
      = p.1 * ((if m ∈ S.resolved ∪ S.band then ∑ n ∈ S.resolved,
            ((pairWave c n m p (lowGrad c K S x n p) (lowVel c K S x n p) (sharpGrad c K S x m p) (sharpVel c K S x m p)).re
              + (pairWave c m n p (sharpGrad c K S x m p) (sharpVel c K S x m p) (lowGrad c K S x n p) (lowVel c K S x n p)).re)
          else 0)
        + (if m ∈ S.resolved then matrixCrossDensity c K S x m p else 0)
        + (∑ i : Fin k, (((x.2.2.2.1 i : ℝ) : ℂ) * entryPairing (sharpGrad c K S x m p)
              (fun a b => modeMat c.order m (c.modelActuatorGrad i) p.1 p.2 a b)
            + ((2 * ζ i : ℝ) : ℂ) * entryPairing (sharpGrad c K S x m p)
              (fun a b => modeMat c.order m (c.modelPinField i) p.1 p.2 a b))).re) := by
  have hl : ((K.lineWeight p.1 : ℝ) : ℂ) * ((CellScalars.rHat K p : ℝ) : ℂ) = ((p.1 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, lw_rHat]
  unfold CellScalars.yStrain CellScalars.yVelocity
  rw [ep_scale3, vp_scale2, ← mul_assoc, ← mul_assoc, hl, ← mul_add, Complex.re_ofReal_mul,
    show ∀ z w : ℝ, (2 : ℝ) * (z * w) = z * (2 * w) from fun z w => by ring]
  congr 1
  have hlin := ep_lin (sharpGrad c K S x m p) x.2.2.2.1 ζ
    (fun i a b => modeMat c.order m (c.modelActuatorGrad i) p.1 p.2 a b)
    (fun i a b => modeMat c.order m (c.modelPinField i) p.1 p.2 a b)
  by_cases hR : m ∈ S.resolved
  · have hRB : m ∈ S.resolved ∪ S.band := Finset.mem_union_left _ hR
    simp only [hRB, hR, if_true]
    have hw := wave_sum c K S x hsy m p (sharpGrad c K S x m p) (sharpVel c K S x m p)
    have hm := matrix_pair (S.localMatrix m p) (hA m p) (sharpGrad c K S x m p) (sharpVel c K S x m p)
      (K.lowStrainAt c.order m S.degHigh x.2.1 p) (K.lowVelocityAt c.order m S.degHigh x.1 p)
    have hmd : matrixCrossDensity c K S x m p
        = (∑ i, ∑ j, ((starRingEnd ℂ) (pairVec (K.lowStrainAt c.order m S.degHigh x.2.1 p)
              (K.lowVelocityAt c.order m S.degHigh x.1 p) i) * S.localMatrix m p i j
            * pairVec (sharpGrad c K S x m p) (sharpVel c K S x m p) j
          + (starRingEnd ℂ) (pairVec (sharpGrad c K S x m p) (sharpVel c K S x m p) i) * S.localMatrix m p i j
            * pairVec (K.lowStrainAt c.order m S.degHigh x.2.1 p) (K.lowVelocityAt c.order m S.degHigh x.1 p) j)).re := by
      simp only [matrixCrossDensity, lowGrad, lowVel, hR, if_true]
    rw [hmd, ← hw, ← hm, ← hlin]
    simp only [Complex.add_re]
    ring
  · simp only [hR, if_false]
    by_cases hRB : m ∈ S.resolved ∪ S.band
    · simp only [hRB, if_true]
      have hw := wave_sum c K S x hsy m p (sharpGrad c K S x m p) (sharpVel c K S x m p)
      rw [← hw, ← hlin]
      simp only [entryPairing, CellScalars.vecPair, map_zero, mul_zero, Finset.sum_const_zero, Complex.add_re, Complex.zero_re]
      ring
    · simp only [hRB, if_false]
      rw [← hlin]
      simp only [entryPairing, CellScalars.vecPair, map_zero, mul_zero, Finset.sum_const_zero, Complex.add_re, Complex.zero_re]
      ring

end SharpYSharpCross.Internal

theorem sharpCross_of_leaves (h2 : BasisEnergySumStatement) (h3 : ProjCoefStatement) (hF : FieldModeSquareStatement)
    (hT : YTargetSquareStatement) (hQ : YStrainSquareStatement) (hM : ModeTurnStatement) (hE : SharpEnergyStatement)
    (hU : YUnfoldedStatement) : SharpCrossSymmStatement :=
  sharpCross_of h2 h3 hF hT hE (yPairing_of hF hQ hM hU)

end CellAnalysis

end CellCert

end Breakdown
