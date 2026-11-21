import Breakdown.FracCell.SharpBoundCore

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace CellScalars

def rowStrainPart {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) {slots : ℕ}
    (R : CellRows N slots k) (B : CellBases) (x : FieldTuple k) (a : Fin N) (n : ℤ) (j l : ℕ) : ℝ :=
  if n ∉ S.resolved ∨ S.degHigh < max j l then
    (if n ∈ S.resolved ∪ S.band then
      strainLin (sharpStrainCoef c K B x n j l)
        (fun i q => B.coef K (fun p => rowCouplingFolded c K S R a n p i q) j l)
    else 0)
  else 0

def rowVelocityPart {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) {slots : ℕ}
    (R : CellRows N slots k) (B : CellBases) (x : FieldTuple k) (a : Fin N) (n : ℤ) (j l : ℕ) : ℝ :=
  if S.degHigh ≤ max j l then
    velLin (sharpVelocityCoef c K B x n j l)
      (fun i => B.coef K (fun p => rowCouplingVelocity c K R a n p i) j l)
  else 0

end CellScalars

def RowPairFormStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ a ∈ R.rowSet,
      (∀ n ∈ R.yModes, Summable (fun jl : ℕ × ℕ => CellScalars.rowStrainPart c K S R B x a n jl.1 jl.2)) ∧
      (∀ n ∈ S.resolved, Summable (fun jl : ℕ × ℕ => CellScalars.rowVelocityPart c K S R B x a n jl.1 jl.2)) ∧
      2 / (4 * Real.pi) * l2Pair (CellScalars.highCouplingField c K S x.1 x.2.1) (c.row a)
        = (∑ n ∈ R.yModes, ∑' jl : ℕ × ℕ, CellScalars.rowStrainPart c K S R B x a n jl.1 jl.2)
          + (∑ n ∈ S.resolved, ∑' jl : ℕ × ℕ, CellScalars.rowVelocityPart c K S R B x a n jl.1 jl.2)
          + 2 * ∑' n : ℤ, CellScalars.unresolvedRowPair c K S R x a n


def IsWeightedSquare (K : CellBox) (F : ℝ × ℝ → ℂ) : Prop :=
  AEStronglyMeasurable F (volume.restrict K.rect) ∧ IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect

namespace CellScalars

def highRowPair {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) {slots : ℕ}
    (R : CellRows N slots k) (x : FieldTuple k) (a : Fin N) (n : ℤ) : ℝ :=
  (∫ p in K.rect, ((K.lineWeight p.1 : ℝ) : ℂ) *
    entryPairing (fun i q => gradMode c.order n x.2.1 i q p
        - (if n ∈ S.resolved then K.lowStrain c.order n S.degHigh x.2.1 i q p else 0))
        (rowCouplingFolded c K S R a n p)).re
  + (if n ∈ S.resolved then
      (∫ p in K.rect, ((K.lineWeight p.1 : ℝ) : ℂ) *
        vecPair (fun i => modeVec c.order n x.1 p.1 p.2 i - K.lowVelocity c.order n S.degHigh x.1 i p)
          (rowCouplingVelocity c K R a n p)).re
    else 0)

end CellScalars

def RowModeSplitStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ a ∈ R.rowSet,
      l2Pair (CellScalars.highCouplingField c K S x.1 x.2.1) (c.row a)
        = 4 * Real.pi * ((∑ n ∈ S.resolved ∪ S.band, CellScalars.highRowPair c K S R x a n)
          + ∑' n : ℤ, CellScalars.unresolvedRowPair c K S R x a n)

def ModeSquareStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      (∀ n i q, IsWeightedSquare K (gradMode c.order n x.2.1 i q)) ∧
      (∀ n i, IsWeightedSquare K (fun p : ℝ × ℝ => modeVec c.order n x.1 p.1 p.2 i)) ∧
      ∀ a ∈ R.rowSet, ∀ n,
        (∀ i q, IsWeightedSquare K (fun p => CellScalars.rowCouplingStrain c K R a n p i q)) ∧
        (∀ i, IsWeightedSquare K (fun p => CellScalars.rowCouplingVelocity c K R a n p i)) ∧
        (∀ i q, IsWeightedSquare K (fun p => CellScalars.rowCouplingFolded c K S R a n p i q))

def FieldModeSquareStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ)
    (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
      IsSecondOrderField m v G H → ∀ n : ℤ,
        (∀ i q, IsWeightedSquare K (gradMode m n G i q)) ∧
        ∀ i, IsWeightedSquare K (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 i)

def RowCouplingSquareStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
      ∀ a ∈ R.rowSet, ∀ n,
        (∀ i q, IsWeightedSquare K (fun p => CellScalars.rowCouplingStrain c K R a n p i q)) ∧
        (∀ i, IsWeightedSquare K (fun p => CellScalars.rowCouplingVelocity c K R a n p i)) ∧
        (∀ i q, IsWeightedSquare K (fun p => CellScalars.rowCouplingFolded c K S R a n p i q))

theorem modeSquare_of (hF : FieldModeSquareStatement) (hR : RowCouplingSquareStatement) : ModeSquareStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx
  exact ⟨fun n => (hF K hd.box c.order x.1 x.2.1 x.2.2.1 hx.1 n).1,
    fun n => (hF K hd.box c.order x.1 x.2.1 x.2.2.1 hx.1 n).2, hR α h1 h2 c hc K S B Cl R hd hw⟩

def BasisEnergySumStatement : Prop :=
  ∀ (K : CellBox) (B : CellBases), IsCellBox K → IsCellBases K B →
    ∀ (ι : Type) [Fintype ι] (F W : ι → ℝ × ℝ → ℂ), (∀ i, IsWeightedSquare K (F i)) → (∀ i, IsWeightedSquare K (W i)) →
      HasSum (fun jl : ℕ × ℕ => ∑ i, B.coef K (F i) jl.1 jl.2 * (starRingEnd ℂ) (B.coef K (W i) jl.1 jl.2))
        (∫ p in K.rect, ((K.lineWeight p.1 : ℝ) : ℂ) * ∑ i, F i p * (starRingEnd ℂ) (W i p))

def ProjCoefStatement : Prop :=
  ∀ (K : CellBox) (B : CellBases), IsCellBox K → IsCellBases K B →
    ∀ F : ℝ × ℝ → ℂ, IsWeightedSquare K F → ∀ d : ℕ,
      IsWeightedSquare K (fun p => F p - K.proj d d F p) ∧
      ∀ j l, B.coef K (fun p => F p - K.proj d d F p) j l = if max j l ≤ d then 0 else B.coef K F j l

def ModeTurnStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    IsSecondOrderField m v G H → ∀ K : CellBox, IsCellBox K → ∀ n : ℤ,
      ∀ᵐ p ∂(volume.restrict K.rect),
        turnVec (azimuth m n) (modeVec m n v p.1 p.2) = fun a => (p.1 : ℂ) * gradMode m n G a 1 p

namespace CellScalars

def unfoldedRowPair {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) {slots : ℕ}
    (R : CellRows N slots k) (x : FieldTuple k) (a : Fin N) (n : ℤ) : ℝ :=
  (∫ p in K.rect, ((K.lineWeight p.1 : ℝ) : ℂ) *
    entryPairing (fun i q => gradMode c.order n x.2.1 i q p
        - (if n ∈ S.resolved then K.lowStrain c.order n S.degHigh x.2.1 i q p else 0))
        (rowCouplingStrain c K R a n p)).re
  + (∫ p in K.rect, ((K.lineWeight p.1 : ℝ) : ℂ) *
      vecPair (fun i => modeVec c.order n x.1 p.1 p.2 i
        - (if n ∈ S.resolved then K.lowVelocity c.order n S.degHigh x.1 i p else 0))
        (rowCouplingVelocity c K R a n p)).re

end CellScalars

def RowModeUnfoldedStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ a ∈ R.rowSet,
      l2Pair (CellScalars.highCouplingField c K S x.1 x.2.1) (c.row a)
        = 4 * Real.pi * ((∑ n ∈ S.resolved ∪ S.band, CellScalars.unfoldedRowPair c K S R x a n)
          + ∑' n : ℤ, CellScalars.unresolvedRowPair c K S R x a n)

def FoldPairStatement : Prop :=
  ∀ (k r : ℝ), k ≠ 0 → k ^ 2 ≠ 1 → ∀ (s Ys : Fin 3 → Fin 3 → ℂ) (v Yv : Fin 3 → ℂ),
    turnVec k v = (fun a => (r : ℂ) * s a 1) →
      entryPairing s (foldVelocity k r Ys Yv) = entryPairing s Ys + CellScalars.vecPair v Yv

namespace SharpRowIdentity.Internal

theorem entry_split (σ W : Fin 3 → Fin 3 → ℂ) :
    entryPairing (fun a b => (σ a b + σ b a) / 2) (fun a b => (W a b + W b a) / 2)
      + entryPairing (fun a b => (σ a b - σ b a) / 2) (fun a b => (W a b - W b a) / 2) = entryPairing σ W := by
  simp only [entryPairing, Fin.sum_univ_three, map_add, map_sub, map_div₀, map_ofNat]
  ring

theorem strainLin_eq (σ W : Fin 3 → Fin 3 → ℂ) : strainLin σ W = 2 * (entryPairing σ W).re := by
  unfold strainLin
  rw [entry_split]

theorem entry_sum {ι : Type} (s : Finset ι) (μ : ι → ℝ) (σ : Fin 3 → Fin 3 → ℂ) (W : ι → Fin 3 → Fin 3 → ℂ) :
    entryPairing σ (fun i q => ∑ a ∈ s, ((μ a : ℝ) : ℂ) * W a i q) = ∑ a ∈ s, ((μ a : ℝ) : ℂ) * entryPairing σ (W a) := by
  unfold entryPairing
  have h1 : ∀ i q : Fin 3, σ i q * (starRingEnd ℂ) (∑ a ∈ s, ((μ a : ℝ) : ℂ) * W a i q)
      = ∑ a ∈ s, ((μ a : ℝ) : ℂ) * (σ i q * (starRingEnd ℂ) (W a i q)) := by
    intro i q
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    ring
  simp_rw [h1]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

theorem vec_sum {ι : Type} (s : Finset ι) (μ : ι → ℝ) (τ : Fin 3 → ℂ) (W : ι → Fin 3 → ℂ) :
    CellScalars.vecPair τ (fun i => ∑ a ∈ s, ((μ a : ℝ) : ℂ) * W a i) = ∑ a ∈ s, ((μ a : ℝ) : ℂ) * CellScalars.vecPair τ (W a) := by
  unfold CellScalars.vecPair
  have h1 : ∀ i : Fin 3, τ i * (starRingEnd ℂ) (∑ a ∈ s, ((μ a : ℝ) : ℂ) * W a i)
      = ∑ a ∈ s, ((μ a : ℝ) : ℂ) * (τ i * (starRingEnd ℂ) (W a i)) := by
    intro i
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]

theorem re_sum_real {ι : Type} (s : Finset ι) (μ : ι → ℝ) (z : ι → ℂ) :
    (∑ a ∈ s, ((μ a : ℝ) : ℂ) * z a).re = ∑ a ∈ s, μ a * (z a).re := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.re_ofReal_mul]

theorem strain_term {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) {slots : ℕ}
    (R : CellRows N slots k) (B : CellBases) (x : FieldTuple k) (μ : Fin N → ℝ) (n : ℤ) (j l : ℕ) :
    CellScalars.rowStrainTerm c K S R B μ (sharpStrainCoef c K B x) n j l
      = ∑ a ∈ R.rowSet, μ a * CellScalars.rowStrainPart c K S R B x a n j l := by
  unfold CellScalars.rowStrainTerm CellScalars.rowStrainPart CellScalars.rowStrainTarget
  by_cases h1 : n ∉ S.resolved ∨ S.degHigh < max j l
  · by_cases h2 : n ∈ S.resolved ∪ S.band
    · simp only [h1, h2, if_true]
      rw [strainLin_eq, entry_sum, re_sum_real, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [strainLin_eq]
      ring
    · simp only [h1, h2, if_true, if_false, mul_zero, Finset.sum_const_zero]
      rw [strainLin_eq]
      simp [entryPairing]
  · simp only [h1, if_false, mul_zero, Finset.sum_const_zero]

theorem velocity_term {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) {slots : ℕ}
    (R : CellRows N slots k) (B : CellBases) (x : FieldTuple k) (μ : Fin N → ℝ) (n : ℤ) (j l : ℕ) :
    CellScalars.rowVelocityTerm c K S R B μ (sharpVelocityCoef c K B x) n j l
      = ∑ a ∈ R.rowSet, μ a * CellScalars.rowVelocityPart c K S R B x a n j l := by
  unfold CellScalars.rowVelocityTerm CellScalars.rowVelocityPart CellScalars.rowVelocityTarget
  by_cases h1 : S.degHigh ≤ max j l
  · simp only [h1, if_true]
    unfold velLin
    rw [vec_sum, re_sum_real, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  · simp only [h1, if_false, mul_zero, Finset.sum_const_zero]

theorem summable_far (d : ℕ) (T : ℕ → ℕ → ℝ) (hT : Summable (fun jl : ℕ × ℕ => T jl.1 jl.2)) :
    Summable (fun jl : ℕ × ℕ => if d < max jl.1 jl.2 then T jl.1 jl.2 else 0) := by
  refine (hT.indicator {jl : ℕ × ℕ | d < max jl.1 jl.2}).congr fun jl => ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]

theorem tsum_split (d : ℕ) (T : ℕ → ℕ → ℝ) (hT : Summable (fun jl : ℕ × ℕ => T jl.1 jl.2)) :
    ∑' jl : ℕ × ℕ, T jl.1 jl.2 = (∑ j ∈ Finset.range (d + 1), ∑ l ∈ Finset.range (d + 1), T j l)
      + ∑' jl : ℕ × ℕ, (if d < max jl.1 jl.2 then T jl.1 jl.2 else 0) := by
  have hs := tsum_subtype ((↑(Finset.range (d + 1) ×ˢ Finset.range (d + 1)) : Set (ℕ × ℕ))ᶜ)
    (fun jl : ℕ × ℕ => T jl.1 jl.2)
  rw [← hT.sum_add_tsum_compl (s := Finset.range (d + 1) ×ˢ Finset.range (d + 1)), hs,
    Finset.sum_product]
  congr 1
  congr 1
  funext jl
  simp only [Set.indicator_apply, Set.mem_compl_iff, Finset.coe_product, Set.mem_prod, Finset.coe_range,
    Set.mem_Iio, not_and_or, not_lt, Nat.succ_le_iff, lt_max_iff]

theorem strain_mode {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) {slots : ℕ}
    (R : CellRows N slots k) (B : CellBases) (x : FieldTuple k) (a : Fin N) (n : ℤ)
    (hn : n ∈ S.resolved ∪ S.band) (h2 : BasisEnergySumStatement) (h3 : ProjCoefStatement)
    (hK : IsCellBox K) (hB : IsCellBases K B)
    (hg : ∀ i q, IsWeightedSquare K (gradMode c.order n x.2.1 i q))
    (hW : ∀ i q, IsWeightedSquare K (fun p => CellScalars.rowCouplingFolded c K S R a n p i q)) :
    HasSum (fun jl : ℕ × ℕ => CellScalars.rowStrainPart c K S R B x a n jl.1 jl.2)
      (2 * (∫ p in K.rect, ((K.lineWeight p.1 : ℝ) : ℂ) *
        entryPairing (fun i q => gradMode c.order n x.2.1 i q p
          - (if n ∈ S.resolved then K.lowStrain c.order n S.degHigh x.2.1 i q p else 0))
          (CellScalars.rowCouplingFolded c K S R a n p)).re) := by
  by_cases hr : n ∈ S.resolved
  · have hP := fun i q => h3 K B hK hB _ (hg i q) S.degHigh
    have hs := h2 K B hK hB (Fin 3 × Fin 3)
      (fun iq p => gradMode c.order n x.2.1 iq.1 iq.2 p - K.proj S.degHigh S.degHigh (gradMode c.order n x.2.1 iq.1 iq.2) p)
      (fun iq p => CellScalars.rowCouplingFolded c K S R a n p iq.1 iq.2)
      (fun iq => (hP iq.1 iq.2).1) (fun iq => hW iq.1 iq.2)
    have hre := (hs.mapL Complex.reCLM).mul_left 2
    convert hre using 1
    · rfl
    · funext jl
      obtain ⟨j, l⟩ := jl
      simp only [Complex.reCLM_apply]
      unfold CellScalars.rowStrainPart
      rw [if_pos hn]
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
    · simp only [Complex.reCLM_apply, hr, if_true, CellBox.lowStrain]
      congr 3
      funext p
      unfold entryPairing
      rw [Fintype.sum_prod_type]
  · have hs := h2 K B hK hB (Fin 3 × Fin 3)
      (fun iq p => gradMode c.order n x.2.1 iq.1 iq.2 p)
      (fun iq p => CellScalars.rowCouplingFolded c K S R a n p iq.1 iq.2)
      (fun iq => hg iq.1 iq.2) (fun iq => hW iq.1 iq.2)
    have hre := (hs.mapL Complex.reCLM).mul_left 2
    convert hre using 1
    · rfl
    · funext jl
      obtain ⟨j, l⟩ := jl
      simp only [Complex.reCLM_apply]
      unfold CellScalars.rowStrainPart
      rw [if_pos hn, if_pos (Or.inl hr), strainLin_eq]
      congr 2
      unfold entryPairing sharpStrainCoef
      rw [Fintype.sum_prod_type]
    · simp only [Complex.reCLM_apply, hr, if_false, sub_zero]
      congr 3
      funext p
      unfold entryPairing
      rw [Fintype.sum_prod_type]

theorem velocity_mode {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) {slots : ℕ}
    (R : CellRows N slots k) (B : CellBases) (x : FieldTuple k) (a : Fin N) (n : ℤ)
    (hdeg : 1 ≤ S.degHigh) (h2 : BasisEnergySumStatement) (h3 : ProjCoefStatement)
    (hK : IsCellBox K) (hB : IsCellBases K B)
    (hv : ∀ i, IsWeightedSquare K (fun p : ℝ × ℝ => modeVec c.order n x.1 p.1 p.2 i))
    (hW : ∀ i, IsWeightedSquare K (fun p => CellScalars.rowCouplingVelocity c K R a n p i)) :
    HasSum (fun jl : ℕ × ℕ => CellScalars.rowVelocityPart c K S R B x a n jl.1 jl.2)
      (2 * (∫ p in K.rect, ((K.lineWeight p.1 : ℝ) : ℂ) *
        CellScalars.vecPair (fun i => modeVec c.order n x.1 p.1 p.2 i - K.lowVelocity c.order n S.degHigh x.1 i p)
          (CellScalars.rowCouplingVelocity c K R a n p)).re) := by
  have hP := fun i => h3 K B hK hB _ (hv i) (S.degHigh - 1)
  have hs := h2 K B hK hB (Fin 3)
    (fun i p => modeVec c.order n x.1 p.1 p.2 i
      - K.proj (S.degHigh - 1) (S.degHigh - 1) (fun p : ℝ × ℝ => modeVec c.order n x.1 p.1 p.2 i) p)
    (fun i p => CellScalars.rowCouplingVelocity c K R a n p i)
    (fun i => (hP i).1) hW
  have hre := (hs.mapL Complex.reCLM).mul_left 2
  convert hre using 1
  · rfl
  · funext jl
    obtain ⟨j, l⟩ := jl
    simp only [Complex.reCLM_apply]
    unfold CellScalars.rowVelocityPart
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
  · simp only [Complex.reCLM_apply, CellBox.lowVelocity]
    rfl

theorem strain_zero {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) {slots : ℕ}
    (R : CellRows N slots k) (B : CellBases) (x : FieldTuple k) (a : Fin N) (n : ℤ)
    (hn : n ∉ S.resolved ∪ S.band) (j l : ℕ) : CellScalars.rowStrainPart c K S R B x a n j l = 0 := by
  unfold CellScalars.rowStrainPart
  rw [if_neg hn]
  split_ifs <;> rfl

theorem fold_core (k : ℝ) (hk : k ≠ 0) (hk1 : k ^ 2 ≠ 1) (v w : Fin 3 → ℂ) :
    ∑ a, turnVec k v a * (starRingEnd ℂ) (turnAdjInv k w a) = ∑ a, v a * (starRingEnd ℂ) (w a) := by
  have h1 : (1 - (k : ℂ) ^ 2) ≠ 0 := by
    intro h
    apply hk1
    have e : ((k ^ 2 : ℝ) : ℂ) = 1 := by push_cast; linear_combination -h
    exact_mod_cast e
  have h0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  simp only [Fin.sum_univ_three, turnVec, turnAdjInv, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_mul, map_sub, map_neg, map_div₀, map_one,
    map_pow, Complex.conj_ofReal, Complex.conj_I]
  field_simp
  linear_combination ((k : ℂ) ^ 2 * (v 0 * (starRingEnd ℂ) (w 0) + v 1 * (starRingEnd ℂ) (w 1))) * Complex.I_sq

end SharpRowIdentity.Internal

open SharpRowIdentity.Internal in
theorem foldPair : FoldPairStatement := by
  intro k r hk hk1 s Ys v Yv ht
  have hsplit : entryPairing s (foldVelocity k r Ys Yv) = entryPairing s Ys
      + ∑ a, s a 1 * (starRingEnd ℂ) ((r : ℂ) * turnAdjInv k Yv a) := by
    unfold entryPairing foldVelocity
    simp only [map_add, mul_add, Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Fin.sum_univ_three]
  rw [hsplit]
  congr 1
  have e : ∀ a, s a 1 * (starRingEnd ℂ) ((r : ℂ) * turnAdjInv k Yv a)
      = turnVec k v a * (starRingEnd ℂ) (turnAdjInv k Yv a) := by
    intro a
    simp only [ht]
    rw [map_mul, Complex.conj_ofReal]
    ring
  simp_rw [e]
  unfold CellScalars.vecPair
  exact fold_core k hk hk1 v Yv

namespace SharpRowIdentity.Internal

theorem lw_nonneg_rect (K : CellBox) (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) : 0 ≤ K.lineWeight p.1 := by
  unfold CellBox.lineWeight
  split_ifs
  · linarith [hp.1.1, hK.r_order.1]
  · norm_num

theorem pair_int (K : CellBox) (hK : IsCellBox K) {F W : ℝ × ℝ → ℂ} (hF : IsWeightedSquare K F)
    (hW : IsWeightedSquare K W) :
    IntegrableOn (fun p => ((K.lineWeight p.1 : ℝ) : ℂ) * F p * (starRingEnd ℂ) (W p)) K.rect := by
  have hw : Continuous K.lineWeight := by
    unfold CellBox.lineWeight
    split_ifs
    · exact continuous_id
    · exact continuous_const
  refine Integrable.mono' (hF.2.add hW.2) ?_ ?_
  · exact (((Complex.continuous_ofReal.comp (hw.comp continuous_fst)).aestronglyMeasurable).mul hF.1).mul
      (Complex.continuous_conj.comp_aestronglyMeasurable hW.1)
  · refine (ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).2 (ae_of_all _ (fun p hp => ?_))
    have h0 : 0 ≤ K.lineWeight p.1 := lw_nonneg_rect K hK hp
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0, Complex.norm_conj, Pi.add_apply]
    nlinarith [sq_nonneg (‖F p‖ - ‖W p‖), norm_nonneg (F p), norm_nonneg (W p),
      mul_nonneg h0 (sq_nonneg (‖F p‖ - ‖W p‖)), mul_nonneg h0 (mul_nonneg (norm_nonneg (F p)) (norm_nonneg (W p)))]

theorem entry_int (K : CellBox) (hK : IsCellBox K) {F W : Fin 3 → Fin 3 → ℝ × ℝ → ℂ}
    (hF : ∀ i q, IsWeightedSquare K (F i q)) (hW : ∀ i q, IsWeightedSquare K (W i q)) :
    IntegrableOn (fun p => ((K.lineWeight p.1 : ℝ) : ℂ) * entryPairing (fun i q => F i q p) (fun i q => W i q p)) K.rect := by
  have h := integrable_finsetSum (Finset.univ : Finset (Fin 3)) fun i _ =>
    integrable_finsetSum (Finset.univ : Finset (Fin 3)) fun q _ => pair_int K hK (hF i q) (hW i q)
  refine h.congr (ae_of_all _ fun p => ?_)
  simp only [entryPairing, Finset.mul_sum, mul_assoc]

theorem vec_int (K : CellBox) (hK : IsCellBox K) {F W : Fin 3 → ℝ × ℝ → ℂ}
    (hF : ∀ i, IsWeightedSquare K (F i)) (hW : ∀ i, IsWeightedSquare K (W i)) :
    IntegrableOn (fun p => ((K.lineWeight p.1 : ℝ) : ℂ) * CellScalars.vecPair (fun i => F i p) (fun i => W i p)) K.rect := by
  have h := integrable_finsetSum (Finset.univ : Finset (Fin 3)) fun i _ => pair_int K hK (hF i) (hW i)
  refine h.congr (ae_of_all _ fun p => ?_)
  simp only [CellScalars.vecPair, Finset.mul_sum, mul_assoc]

end SharpRowIdentity.Internal

open SharpRowIdentity.Internal in
theorem rowModeSplit_of (h0 : ModeSquareStatement) (hU : RowModeUnfoldedStatement) (hT : ModeTurnStatement) :
    RowModeSplitStatement := by
  intro α ha1 ha2 k N c hc K S B Cl slots R hd hw x hx a ha
  obtain ⟨hg, hv, hr⟩ := h0 α ha1 ha2 c hc K S B Cl R hd hw x hx
  rw [hU α ha1 ha2 c hc K S B Cl R hd hw x hx a ha]
  congr 2
  refine Finset.sum_congr rfl fun n hn => ?_
  by_cases hres : n ∈ S.resolved
  · unfold CellScalars.unfoldedRowPair CellScalars.highRowPair CellScalars.rowCouplingFolded
    simp only [hres, if_true]
  · unfold CellScalars.unfoldedRowPair CellScalars.highRowPair
    simp only [hres, if_false, sub_zero, add_zero]
    have hm := hd.scalars.unresolved_large n hres
    unfold modeNumber at hm
    have hk : azimuth c.order n ≠ 0 := by
      intro h
      rw [h, abs_zero] at hm
      norm_num at hm
    have hk1 : azimuth c.order n ^ 2 ≠ 1 := by
      intro h
      have : |azimuth c.order n| ^ 2 = 1 := by rw [sq_abs]; exact h
      nlinarith
    have hae : ∀ᵐ p ∂(volume.restrict K.rect),
        ((K.lineWeight p.1 : ℝ) : ℂ) * entryPairing (fun i q => gradMode c.order n x.2.1 i q p)
            (CellScalars.rowCouplingFolded c K S R a n p)
          = ((K.lineWeight p.1 : ℝ) : ℂ) * entryPairing (fun i q => gradMode c.order n x.2.1 i q p)
              (CellScalars.rowCouplingStrain c K R a n p)
            + ((K.lineWeight p.1 : ℝ) : ℂ) * CellScalars.vecPair (fun i => modeVec c.order n x.1 p.1 p.2 i)
              (CellScalars.rowCouplingVelocity c K R a n p) := by
      filter_upwards [hT c.order x.1 x.2.1 x.2.2.1 hx.1 K hd.box n] with p hp
      unfold CellScalars.rowCouplingFolded
      rw [if_neg hres]
      have e := foldPair _ p.1 hk hk1 (fun i q => gradMode c.order n x.2.1 i q p)
        (CellScalars.rowCouplingStrain c K R a n p) (fun i => modeVec c.order n x.1 p.1 p.2 i)
        (CellScalars.rowCouplingVelocity c K R a n p) hp
      rw [e]
      ring
    rw [integral_congr_ae hae, integral_add (entry_int K hd.box (hg n) (hr a ha n).1)
      (vec_int K hd.box (hv n) (hr a ha n).2.1), Complex.add_re]

open SharpRowIdentity.Internal in
theorem rowPairForm_of (h0 : ModeSquareStatement) (h1 : RowModeSplitStatement) (h2 : BasisEnergySumStatement)
    (h3 : ProjCoefStatement) : RowPairFormStatement := by
  intro α ha1 ha2 k N c hc K S B Cl slots R hd hw x hx a ha
  obtain ⟨hg, hv, hr⟩ := h0 α ha1 ha2 c hc K S B Cl R hd hw x hx
  have hK := hd.box
  have hB := hd.bases
  have hdeg : 1 ≤ S.degHigh := by have := hd.scalars.degrees; omega
  have hS := fun n (hn : n ∈ S.resolved ∪ S.band) =>
    strain_mode c K S R B x a n hn h2 h3 hK hB (hg n) (hr a ha n).2.2
  have hV := fun n => velocity_mode c K S R B x a n hdeg h2 h3 hK hB (hv n) (hr a ha n).2.1
  refine ⟨fun n _ => ?_, fun n _ => (hV n).summable, ?_⟩
  · by_cases hn : n ∈ S.resolved ∪ S.band
    · exact (hS n hn).summable
    · simp_rw [strain_zero c K S R B x a n hn]
      exact summable_zero
  rw [h1 α ha1 ha2 c hc K S B Cl R hd hw x hx a ha]
  have eY : (∑ n ∈ R.yModes, ∑' jl : ℕ × ℕ, CellScalars.rowStrainPart c K S R B x a n jl.1 jl.2)
      = ∑ n ∈ S.resolved ∪ S.band, ∑' jl : ℕ × ℕ, CellScalars.rowStrainPart c K S R B x a n jl.1 jl.2 := by
    refine (Finset.sum_subset hd.yModes_contain fun n _ hn => ?_).symm
    simp_rw [strain_zero c K S R B x a n hn]
    exact tsum_zero
  rw [eY, Finset.sum_congr rfl fun n hn => (hS n hn).tsum_eq, Finset.sum_congr rfl fun n _ => (hV n).tsum_eq]
  unfold CellScalars.highRowPair
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.union_inter_cancel_left]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  field_simp

open SharpRowIdentity.Internal in
theorem sharpRowIdentity_of (h : RowPairFormStatement) : SharpRowIdentityStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx μ hμ
  have hA := fun a (ha : a ∈ R.rowSet) => h α h1 h2 c hc K S B Cl R hd hw x hx a ha
  have hSsum : ∀ n ∈ R.yModes, Summable (fun jl : ℕ × ℕ =>
      CellScalars.rowStrainTerm c K S R B μ (sharpStrainCoef c K B x) n jl.1 jl.2) := by
    intro n hn
    simp_rw [strain_term]
    exact summable_sum fun a ha => ((hA a ha).1 n hn).mul_left (μ a)
  have hVsum : ∀ n ∈ S.resolved, Summable (fun jl : ℕ × ℕ =>
      CellScalars.rowVelocityTerm c K S R B μ (sharpVelocityCoef c K B x) n jl.1 jl.2) := by
    intro n hn
    simp_rw [velocity_term]
    exact summable_sum fun a ha => ((hA a ha).2.1 n hn).mul_left (μ a)
  have hfar : ∑' jl : ℕ × ℕ, CellScalars.rowFarTerm c K S R B μ (sharpStrainCoef c K B x) (sharpVelocityCoef c K B x) jl
      = (∑ n ∈ R.yModes, ∑' jl : ℕ × ℕ, if S.degNear < max jl.1 jl.2 then
          CellScalars.rowStrainTerm c K S R B μ (sharpStrainCoef c K B x) n jl.1 jl.2 else 0)
        + (∑ n ∈ S.resolved, ∑' jl : ℕ × ℕ, if S.degNear < max jl.1 jl.2 then
          CellScalars.rowVelocityTerm c K S R B μ (sharpVelocityCoef c K B x) n jl.1 jl.2 else 0) := by
    have e : (fun jl : ℕ × ℕ => CellScalars.rowFarTerm c K S R B μ (sharpStrainCoef c K B x) (sharpVelocityCoef c K B x) jl)
        = fun jl : ℕ × ℕ => (∑ n ∈ R.yModes, if S.degNear < max jl.1 jl.2 then
            CellScalars.rowStrainTerm c K S R B μ (sharpStrainCoef c K B x) n jl.1 jl.2 else 0)
          + (∑ n ∈ S.resolved, if S.degNear < max jl.1 jl.2 then
            CellScalars.rowVelocityTerm c K S R B μ (sharpVelocityCoef c K B x) n jl.1 jl.2 else 0) := by
      funext jl
      unfold CellScalars.rowFarTerm
      by_cases hj : S.degNear < max jl.1 jl.2
      · simp only [hj, if_true]
      · simp only [hj, if_false, Finset.sum_const_zero, add_zero]
    rw [e, Summable.tsum_add (summable_sum fun n hn => summable_far _ _ (hSsum n hn))
        (summable_sum fun n hn => summable_far _ _ (hVsum n hn)),
      Summable.tsum_finsetSum fun n hn => summable_far _ _ (hSsum n hn),
      Summable.tsum_finsetSum fun n hn => summable_far _ _ (hVsum n hn)]
  have hform : CellScalars.sharpRowForm c K S R B μ (sharpStrainCoef c K B x) (sharpVelocityCoef c K B x)
      = (∑ n ∈ R.yModes, ∑' jl : ℕ × ℕ, CellScalars.rowStrainTerm c K S R B μ (sharpStrainCoef c K B x) n jl.1 jl.2)
        + (∑ n ∈ S.resolved, ∑' jl : ℕ × ℕ,
            CellScalars.rowVelocityTerm c K S R B μ (sharpVelocityCoef c K B x) n jl.1 jl.2) := by
    unfold CellScalars.sharpRowForm
    rw [hfar, Finset.sum_congr rfl fun n hn => tsum_split S.degNear _ (hSsum n hn),
      Finset.sum_congr rfl fun n hn => tsum_split S.degNear _ (hVsum n hn),
      Finset.sum_add_distrib, Finset.sum_add_distrib]
    ring
  have e3 : ∀ n ∈ R.yModes, ∑' jl : ℕ × ℕ, CellScalars.rowStrainTerm c K S R B μ (sharpStrainCoef c K B x) n jl.1 jl.2
      = ∑ a ∈ R.rowSet, μ a * ∑' jl : ℕ × ℕ, CellScalars.rowStrainPart c K S R B x a n jl.1 jl.2 := by
    intro n hn
    simp_rw [strain_term]
    rw [Summable.tsum_finsetSum fun a ha => ((hA a ha).1 n hn).mul_left (μ a)]
    simp_rw [tsum_mul_left]
  have e4 : ∀ n ∈ S.resolved, ∑' jl : ℕ × ℕ,
      CellScalars.rowVelocityTerm c K S R B μ (sharpVelocityCoef c K B x) n jl.1 jl.2
      = ∑ a ∈ R.rowSet, μ a * ∑' jl : ℕ × ℕ, CellScalars.rowVelocityPart c K S R B x a n jl.1 jl.2 := by
    intro n hn
    simp_rw [velocity_term]
    rw [Summable.tsum_finsetSum fun a ha => ((hA a ha).2.1 n hn).mul_left (μ a)]
    simp_rw [tsum_mul_left]
  rw [hform, Finset.sum_congr rfl e3, Finset.sum_congr rfl e4, Finset.sum_comm (s := R.yModes),
    Finset.sum_comm (s := S.resolved), Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  have e5 : 2 / (4 * Real.pi) * (μ a * l2Pair (CellScalars.highCouplingField c K S x.1 x.2.1) (c.row a))
      = μ a * (2 / (4 * Real.pi) * l2Pair (CellScalars.highCouplingField c K S x.1 x.2.1) (c.row a)) := by ring
  rw [e5, (hA a ha).2.2, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem sharpRowIdentity_of_parts (h0 : ModeSquareStatement) (hU : RowModeUnfoldedStatement)
    (hT : ModeTurnStatement) (h2 : BasisEnergySumStatement) (h3 : ProjCoefStatement) :
    SharpRowIdentityStatement :=
  sharpRowIdentity_of (rowPairForm_of h0 (rowModeSplit_of h0 hU hT) h2 h3)

end CellAnalysis

end CellCert

end Breakdown
