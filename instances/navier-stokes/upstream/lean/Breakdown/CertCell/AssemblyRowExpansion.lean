import Breakdown.CertCell.AssemblyRowParts
import Breakdown.CertCell.AssemblyRowExpansionCombineAlgebra

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

namespace RowExpansion

namespace Internal

open Coupling.LabelScale

theorem rowGram_block {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) {V : Type}
    (K : Fin D.mesh.count) (B : CellBlocks V) : IsLabelBlock (rowGram D K B) B.rowLabel := by
  intro i j h
  simp only [rowGram, if_neg h]

theorem scaled_eq {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) {V : Type}
    (K : Fin D.mesh.count) (B : CellBlocks V) (hdet : IsUnit (rowGram D K B).det) (c : ℤ × ℤ → ℝ)
    (hpos : ∀ i, 0 < c (B.rowLabel i)) (y : Fin B.rowCount → ℂ) :
    Coupling.inverseWeightedSq (scaledRowGram D K B c) y
      = Coupling.quadForm (rowGram D K B)⁻¹ (scaleVec (fun i => Real.sqrt (c (B.rowLabel i))) y) :=
  inverseWeightedSq_scaled (rowGram_block D K B) hdet (fun i => c (B.rowLabel i))
    (fun i j h => by simp only [h]) hpos y

theorem freq_zero {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) {V : Type}
    (K : Fin D.mesh.count) (B : CellBlocks V) (P : ℝ) (v : ℝ → Space → Space) (i : Fin B.rowCount)
    (h : labelTime (B.rowLabel i) = 0) : freqPiece D K B P v i = 0 := by
  simp [freqPiece, h]

theorem deact_zero {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) {V W : Type}
    (K : Fin D.mesh.count) (B : CellBlocks V) (P : PotentialData W) (j : Fin P.groupCount)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (i : Fin B.rowCount)
    (h : j ∉ activeGroups P (B.rowLabel i)) : deactGroupPiece D K B P j v G i = 0 := by
  unfold deactGroupPiece
  apply Finset.sum_eq_zero
  intro ι' hι'
  rw [if_neg]
  intro hh
  exact h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ι', hι', hh⟩)

theorem longAllowance_zero {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (R : CellCalculusEntry D) {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V)
    (h₁ : (R.long K).errVelocity = 0) (h₂ : (R.long K).errVorticity = 0) (S : Finset (ℤ × ℤ))
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) : longAllowance D R K B S v G = 0 := by
  simp [longAllowance, h₁, h₂]

theorem actuator_zero {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) {V : Type}
    (K : Fin D.mesh.count) (B : CellBlocks V) (κ : Fin k → ℝ) (i : Fin B.rowCount)
    (h : ∀ l, actuatorRow D K (B.rowLabel i) (rowTestPoly D K B i) (D.cert.actuator l)
      = actuatorRow D K (B.rowLabel i) (rowTestPoly D K B i) (B.actuatorModel (l : ℕ))) :
    actuatorPiece D K B κ i = 0 := by
  unfold actuatorPiece
  apply Finset.sum_eq_zero
  intro l _
  rw [h l, sub_self, mul_zero]

theorem kappaSq_cellState {k n : ℕ} (M : CellMesh) (K : Fin M.count) (A : CellModeLayouts) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (Pg : ℝ → Space → Space) (κ ζ : Fin k → ℝ) (η : Fin n → ℂ) :
    kappaSq (cellState M K A v G H Pg κ ζ η) = ∑ l, κ l ^ 2 := by
  unfold kappaSq cellState
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp only [Sum.elim_inr, Sum.elim_inl, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem scale_match {n : Type*} {a s w : n → ℝ} {y : n → ℂ} (h : ∀ i, y i ≠ 0 → a i * s i = w i) :
    scaleVec a (scaleVec s y) = scaleVec w y := by
  funext i
  simp only [scaleVec]
  by_cases hy : y i = 0
  · simp [hy]
  · rw [← mul_assoc, ← Complex.ofReal_mul, h i hy]

end Internal

end RowExpansion

open RowExpansion.Internal Coupling.LabelScale in
theorem rowCombine : RowCombineHolds := by
  classical
  intro k C nE nM D R A P states hstates hC hF hI hFr hEr hLo hDs hDe hAc hAl K q v G H g κ F Pg ht ζ η
  rw [hI K q v G H g κ F Pg ht ζ η]
  have hFb := hFr K q v G H g κ F Pg ht
  have hEb := hEr K q v G H g κ F Pg ht
  have hLb := hLo K q v G H g κ F Pg ht
  have hDb := hDe K q v G H g κ F Pg ht
  have hA := hAl K q v G H g κ F Pg ht
  have hAb := hAc K q v G H g κ F Pg ht
  have hbud := hF.leak_budget K
  set B := A.blocks K with hB
  set lab := B.rowLabel with hlab_def
  have hGpd : (rowGram D K B).PosDef := hC.gram_pos K
  have hdet : IsUnit (rowGram D K B).det := (Matrix.isUnit_iff_isUnit_det _).mp hGpd.isUnit
  have hMpd := hGpd.inv
  have hMb : IsLabelBlock (rowGram D K B)⁻¹ lab := inv_block (rowGram_block D K B) hdet
  obtain ⟨hcE, hcD, hcLl, hcLh, hcF⟩ := hF.costs_pos K
  obtain ⟨hcA, hAe⟩ := hF.actuator_pos K
  have hlab : ∀ i, lab i ∈ D.mesh.tested K := hC.label_tested K
  have hw : ∀ i, 0 < B.leakWeight (lab i) := fun i => hC.leak_weight_pos K _ (hlab i)
  have hcL : ∀ ι, 0 < longRowCost D R K B ι := by
    intro ι
    unfold longRowCost
    split_ifs
    · exact hcLl
    · exact hcLh
  have hcFi : ∀ i, 0 < B.freqCost (lab i) := fun i => hcF _ (hlab i)
  set f := freqPiece D K B (D.cert.period q) v with hf
  set e := errorPiece D R K B (P.potential K) v G with he
  set l := longPiece D R K B (P.potential K) v G with hl
  set d : Fin (P.potential K).groupCount → Fin B.rowCount → ℂ :=
    fun j => deactGroupPiece D K B (P.potential K) j v G with hd
  set act := actuatorPiece D K B κ with hact
  have hsplit : deactPiece D K B (P.potential K).harmonicLabels v G = ∑ j, d j := by
    funext i
    rw [Finset.sum_apply]
    exact hDs K q v G H g κ F Pg ht i
  rw [hsplit, show leakGram D K B = scaledRowGram D K B B.leakWeight from rfl, scaled_eq D K B hdet _ hw]
  have qF : Coupling.quadForm (rowGram D K B)⁻¹ (scaleVec (fun i => Real.sqrt (B.freqCost (lab i))) f)
      = Coupling.inverseWeightedSq (scaledRowGram D K B B.freqCost) f := (scaled_eq D K B hdet _ hcFi f).symm
  have qE : Coupling.quadForm (rowGram D K B)⁻¹ (scaleVec (fun _ => Real.sqrt B.errorCost) e)
      = Coupling.inverseWeightedSq (scaledRowGram D K B (fun _ => B.errorCost)) e :=
    (scaled_eq D K B hdet (fun _ => B.errorCost) (fun _ => hcE) e).symm
  have qL : Coupling.quadForm (rowGram D K B)⁻¹ (scaleVec (fun i => Real.sqrt (longRowCost D R K B (lab i))) l)
      = Coupling.inverseWeightedSq (scaledRowGram D K B (longRowCost D R K B)) l :=
    (scaled_eq D K B hdet _ (fun i => hcL _) l).symm
  have qA : Coupling.quadForm (rowGram D K B)⁻¹ (scaleVec (fun _ => Real.sqrt B.actuatorCost) act)
      = Coupling.inverseWeightedSq (scaledRowGram D K B (fun _ => B.actuatorCost)) act :=
    (scaled_eq D K B hdet (fun _ => B.actuatorCost) (fun _ => hcA) act).symm
  have qD : ∑ j, Coupling.quadForm (rowGram D K B)⁻¹ (scaleVec (fun _ => Real.sqrt B.deactCost) (d j))
      = B.deactCost * ∑ j, Coupling.inverseWeightedSq (rowGram D K B) (d j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [quad_scale_const _ hcD.le]
    rfl
  have hlong : ¬ ((R.long K).errVelocity = 0 ∧ (R.long K).errVorticity = 0) ∨ l = 0 := by
    by_cases hz : (R.long K).errVelocity = 0 ∧ (R.long K).errVorticity = 0
    · right
      have h0 : Coupling.quadForm (rowGram D K B)⁻¹
          (scaleVec (fun i => Real.sqrt (longRowCost D R K B (lab i))) l) ≤ 0 := by
        rw [qL]
        have := hLb
        simp only [longAllowance_zero D R K B hz.1 hz.2, add_zero] at this
        exact this
      have hz0 := eq_zero_of_quad_nonpos hMpd h0
      funext i
      have hi := congrFun hz0 i
      simp only [scaleVec, Pi.zero_apply, mul_eq_zero, Complex.ofReal_eq_zero] at hi
      rcases hi with hi | hi
      · exact absurd hi (Real.sqrt_pos.mpr (hcL _)).ne'
      · exact hi
    · left
      exact hz
  let aF : Fin B.rowCount → ℝ := fun i =>
    if labelTime (lab i) = 0 then 0 else Real.sqrt (B.leakWeight (lab i) / B.freqCost (lab i))
  let aE : Fin B.rowCount → ℝ := fun i => Real.sqrt (B.leakWeight (lab i) / B.errorCost)
  let aL : Fin B.rowCount → ℝ := fun i =>
    if (R.long K).errVelocity = 0 ∧ (R.long K).errVorticity = 0 then 0
    else Real.sqrt (B.leakWeight (lab i) / longRowCost D R K B (lab i))
  let aD : Fin (P.potential K).groupCount → Fin B.rowCount → ℝ := fun j i =>
    if j ∈ activeGroups (P.potential K) (lab i) then Real.sqrt (B.leakWeight (lab i) / B.deactCost) else 0
  let aA : Fin B.rowCount → ℝ := fun i =>
    if lab i ∈ B.actuatorRows then Real.sqrt (B.leakWeight (lab i) / B.actuatorCost) else 0
  have cA : IsLabelConst lab aA := by
    intro i j h
    simp only [aA, h]
  have cF : IsLabelConst lab aF := by
    intro i j h
    simp only [aF, h]
  have cE : IsLabelConst lab aE := by
    intro i j h
    simp only [aE, h]
  have cL : IsLabelConst lab aL := by
    intro i j h
    simp only [aL, h]
  have cD : ∀ j, IsLabelConst lab (aD j) := by
    intro j i i' h
    simp only [aD, h]
  have cX : ∀ X : Option (Fin (P.potential K).groupCount), IsLabelConst lab (X.elim aA aD) := by
    intro X
    rcases X with _ | j
    · exact cA
    · exact cD j
  have hsum : ∀ i, aF i ^ 2 + aE i ^ 2 + aL i ^ 2
      + ∑ X : Option (Fin (P.potential K).groupCount), (X.elim aA aD) i ^ 2 ≤ 1 := by
    intro i
    have hW := (hw i).le
    have sF : aF i ^ 2 = if labelTime (lab i) = 0 then 0 else B.leakWeight (lab i) / B.freqCost (lab i) := by
      simp only [aF]
      split_ifs
      · ring
      · exact Real.sq_sqrt (div_nonneg hW (hcFi i).le)
    have sE : aE i ^ 2 = B.leakWeight (lab i) / B.errorCost := Real.sq_sqrt (div_nonneg hW hcE.le)
    have sL : aL i ^ 2 = if (R.long K).errVelocity = 0 ∧ (R.long K).errVorticity = 0 then 0
        else B.leakWeight (lab i) / longRowCost D R K B (lab i) := by
      simp only [aL]
      split_ifs
      · ring
      · exact Real.sq_sqrt (div_nonneg hW (hcL _).le)
    have sD : ∑ j, aD j i ^ 2 = ((activeGroups (P.potential K) (lab i)).card : ℝ)
        * (B.leakWeight (lab i) / B.deactCost) :=
      sum_sq_ite_mem _ (div_nonneg hW hcD.le)
    have sA : aA i ^ 2 = if lab i ∈ B.actuatorRows then B.leakWeight (lab i) / B.actuatorCost else 0 := by
      simp only [aA]
      split_ifs
      · exact Real.sq_sqrt (div_nonneg hW hcA.le)
      · ring
    have hb := hbud (lab i) (hlab i)
    unfold longRowTerm at hb
    rw [Fintype.sum_option]
    simp only [Option.elim]
    rw [sF, sE, sL, sA, sD]
    split_ifs at hb ⊢ <;> (convert hb using 1; ring)
  have hcomb := combine_four hMb hMpd.posSemidef aF aE aL (fun X : Option (Fin (P.potential K).groupCount) => X.elim aA aD) cF cE cL cX hsum
    (scaleVec (fun i => Real.sqrt (B.freqCost (lab i))) f) (scaleVec (fun _ => Real.sqrt B.errorCost) e)
    (scaleVec (fun i => Real.sqrt (longRowCost D R K B (lab i))) l)
    (fun X : Option (Fin (P.potential K).groupCount) => X.elim (scaleVec (fun _ => Real.sqrt B.actuatorCost) act)
      (fun j => scaleVec (fun _ => Real.sqrt B.deactCost) (d j)))
  simp only [Fintype.sum_option, Option.elim] at hcomb
  have mF : scaleVec aF (scaleVec (fun i => Real.sqrt (B.freqCost (lab i))) f)
      = scaleVec (fun i => Real.sqrt (B.leakWeight (lab i))) f := by
    apply scale_match
    intro i hi
    have ht0 : labelTime (lab i) ≠ 0 := fun h0 => hi (freq_zero D K B _ v i h0)
    simp only [aF, if_neg ht0]
    exact sqrt_div_mul_sqrt (hw i).le (hcFi i)
  have mE : scaleVec aE (scaleVec (fun _ => Real.sqrt B.errorCost) e)
      = scaleVec (fun i => Real.sqrt (B.leakWeight (lab i))) e := by
    apply scale_match
    intro i _
    exact sqrt_div_mul_sqrt (hw i).le hcE
  have mL : scaleVec aL (scaleVec (fun i => Real.sqrt (longRowCost D R K B (lab i))) l)
      = scaleVec (fun i => Real.sqrt (B.leakWeight (lab i))) l := by
    apply scale_match
    intro i hi
    rcases hlong with hz | hz
    · simp only [aL, if_neg hz]
      exact sqrt_div_mul_sqrt (hw i).le (hcL _)
    · exact absurd (congrFun hz i) hi
  have mA : scaleVec aA (scaleVec (fun _ => Real.sqrt B.actuatorCost) act)
      = scaleVec (fun i => Real.sqrt (B.leakWeight (lab i))) act := by
    apply scale_match
    intro i hi
    have hr : lab i ∈ B.actuatorRows := by
      by_contra hn
      exact hi (actuator_zero D K B κ i (hF.actuator_off_rows K i hn))
    simp only [aA, if_pos hr]
    exact sqrt_div_mul_sqrt (hw i).le hcA
  have mD : ∀ j, scaleVec (aD j) (scaleVec (fun _ => Real.sqrt B.deactCost) (d j))
      = scaleVec (fun i => Real.sqrt (B.leakWeight (lab i))) (d j) := by
    intro j
    apply scale_match
    intro i hi
    have hj : j ∈ activeGroups (P.potential K) (lab i) := by
      by_contra hn
      exact hi (deact_zero D K B (P.potential K) j v G i hn)
    simp only [aD, if_pos hj]
    exact sqrt_div_mul_sqrt (hw i).le hcD
  rw [mF, mE, mL, mA] at hcomb
  simp only [mD] at hcomb
  have hvec : scaleVec (fun i => Real.sqrt (B.leakWeight (lab i))) (f + e + l + ∑ j, d j + act)
      = scaleVec (fun i => Real.sqrt (B.leakWeight (lab i))) f + scaleVec (fun i => Real.sqrt (B.leakWeight (lab i))) e
        + scaleVec (fun i => Real.sqrt (B.leakWeight (lab i))) l
        + (scaleVec (fun i => Real.sqrt (B.leakWeight (lab i))) act
          + ∑ j, scaleVec (fun i => Real.sqrt (B.leakWeight (lab i))) (d j)) := by
    rw [scaleVec_add, scaleVec_add, scaleVec_add, scaleVec_add, scaleVec_sum]
    abel
  rw [hvec]
  rw [qF, qE, qL, qA, qD] at hcomb
  have hks : kappaSq (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) = ∑ l, κ l ^ 2 :=
    kappaSq_cellState _ _ _ _ _ _ _ _ _ _
  have hk0 : 0 ≤ ∑ l, κ l ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hkap : B.actuatorCost * B.actuatorErr * ∑ l, κ l ^ 2 ≤ B.rowKappaCost * ∑ l, κ l ^ 2 :=
    mul_le_mul_of_nonneg_right (hF.actuator_kappa K) hk0
  rw [hks]
  linarith [hA.1, hA.2.1, hA.2.2]

end Assembly

end CertCell

end Breakdown
