import Breakdown.CertCell.AssemblyStatements
import Breakdown.CertCell.AssemblyRowRemovalAlgebra
import Breakdown.CertCell.LabelRowProfile
import Breakdown.CertCell.PeriodicSecondOrder
import Breakdown.CertCell.HarmonicProfiles
import Breakdown.CertCell.HarmonicPressureLift
import Breakdown.CertCell.VelocitySixthIntegral
import Breakdown.CertCell.SixthPower
import Breakdown.CertCell.SecondDerivEnergyIdentity

open MeasureTheory Matrix
open scoped ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCalculus

namespace Internal.RowRemoval

section Apply

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

lemma grad_facts (K : Fin D.mesh.count) (hK : IsCellBox (D.mesh.box K)) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {Pg : ℝ → Space → Space} (hv : IsPeriodicSecondOrder v G H) (hp : IsPeriodicPressure Pg)
    (ι : ℤ × ℤ) (d : ℕ) :
    (∀ a b, AEStronglyMeasurable (fun p => gradAt D.azimuthOrder ι G a b p
        - (D.mesh.box K).proj d d (fun p' => gradAt D.azimuthOrder ι G a b p') p)
        (volume.restrict (D.mesh.box K).rect) ∧
      Integrable (fun p => (D.mesh.box K).lineWeight p.1 * ‖gradAt D.azimuthOrder ι G a b p
        - (D.mesh.box K).proj d d (fun p' => gradAt D.azimuthOrder ι G a b p') p‖ ^ 2)
        (volume.restrict (D.mesh.box K).rect)) ∧
    (∀ a, AEStronglyMeasurable (fun p => velAt D.azimuthOrder ι v a p
        - (D.mesh.box K).proj d d (fun p' => velAt D.azimuthOrder ι v a p') p)
        (volume.restrict (D.mesh.box K).rect) ∧
      Integrable (fun p => (D.mesh.box K).lineWeight p.1 * ‖velAt D.azimuthOrder ι v a p
        - (D.mesh.box K).proj d d (fun p' => velAt D.azimuthOrder ι v a p') p‖ ^ 2)
        (volume.restrict (D.mesh.box K).rect)) := by
  have hI := CellCalculus.Internal.LabelRowProfile.profile_integrable harmonicLift_holds
    harmonicPressureLift_holds (D.mesh.box K) hK D.azimuthOrder v G H Pg hv hp ι
  obtain ⟨mV, mG, -, -⟩ := CellCalculus.Internal.LabelRowProfile.profile_measurable (D.mesh.box K) hK
    D.azimuthOrder v G H Pg hv hp ι
  have n1 := fun p => cnormSq_nonneg (velArray D.azimuthOrder ι v p)
  have n2 := fun p => cnormSq_nonneg (fun a => ∑ c, slopeAt D.azimuthOrder ι H a c c p)
  have n3 := fun p => cnormSq_nonneg (velArray D.azimuthOrder ι Pg p)
  have n4 := fun p => Finset.sum_nonneg (s := Finset.univ)
    (fun a _ => cnormSq_nonneg (gradArray D.azimuthOrder ι G p a))
  refine ⟨fun a b => tail_part hK (mG a b) hI (fun p _ => ?_) d d,
    fun a => tail_part hK (mV a) hI (fun p _ => ?_) d d⟩
  · have h1 : ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2 ≤ cnormSq (gradArray D.azimuthOrder ι G p a) := by
      simp only [cnormSq, gradArray]
      exact Finset.single_le_sum (f := fun b' => ‖gradAt D.azimuthOrder ι G a b' p‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ b)
    have h2 : cnormSq (gradArray D.azimuthOrder ι G p a) ≤ ∑ a', cnormSq (gradArray D.azimuthOrder ι G p a') :=
      Finset.single_le_sum (f := fun a' => cnormSq (gradArray D.azimuthOrder ι G p a'))
        (fun _ _ => cnormSq_nonneg _) (Finset.mem_univ a)
    linarith [n1 p, n2 p, n3 p]
  · have h1 : ‖velAt D.azimuthOrder ι v a p‖ ^ 2 ≤ cnormSq (velArray D.azimuthOrder ι v p) := by
      simp only [cnormSq, velArray]
      exact Finset.single_le_sum (f := fun a' => ‖velAt D.azimuthOrder ι v a' p‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ a)
    linarith [n2 p, n3 p, n4 p]

lemma profile_facts (K : Fin D.mesh.count) (hK : IsCellBox (D.mesh.box K)) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {Pg : ℝ → Space → Space} (hv : IsPeriodicSecondOrder v G H) (hp : IsPeriodicPressure Pg)
    (ι : ℤ × ℤ) (j : Fin 12) :
    AEStronglyMeasurable (fun p => tailProfile D R K ι v G p j) (volume.restrict (D.mesh.box K).rect) ∧
      Integrable (fun p => (D.mesh.box K).lineWeight p.1 * ‖tailProfile D R K ι v G p j‖ ^ 2)
        (volume.restrict (D.mesh.box K).rect) := by
  by_cases hj : j.val < 9
  · obtain ⟨hg, -⟩ := grad_facts D K hK hv hp ι ((R.layouts K).layout ι).degCoef
    have e : ∀ p, tailProfile D R K ι v G p j
        = gradAt D.azimuthOrder ι G ⟨j.val / 3, by omega⟩ ⟨j.val % 3, by omega⟩ p
          - (D.mesh.box K).proj ((R.layouts K).layout ι).degCoef ((R.layouts K).layout ι).degCoef
            (fun p' => gradAt D.azimuthOrder ι G ⟨j.val / 3, by omega⟩ ⟨j.val % 3, by omega⟩ p') p := by
      intro p
      simp only [tailProfile, pairVec, dif_pos hj]
    simp only [e]
    exact hg _ _
  · obtain ⟨-, hw⟩ := grad_facts D K hK hv hp ι (((R.layouts K).layout ι).degCoef - 1)
    have e : ∀ p, tailProfile D R K ι v G p j
        = velAt D.azimuthOrder ι v ⟨j.val - 9, by omega⟩ p
          - (D.mesh.box K).proj (((R.layouts K).layout ι).degCoef - 1) (((R.layouts K).layout ι).degCoef - 1)
            (fun p' => velAt D.azimuthOrder ι v ⟨j.val - 9, by omega⟩ p') p := by
      intro p
      simp only [tailProfile, pairVec, dif_neg hj]
    simp only [e]
    exact hw _

lemma strain_eq (K : Fin D.mesh.count) (hK : IsCellBox (D.mesh.box K)) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {Pg : ℝ → Space → Space} (hv : IsPeriodicSecondOrder v G H) (hp : IsPeriodicPressure Pg) (ι : ℤ × ℤ) :
    tailStrainSq D R K ι G = ∫ p in (D.mesh.box K).rect, (D.mesh.box K).lineWeight p.1 *
      ∑ j ∈ Finset.univ.filter (fun j : Fin 12 => decide (j.val < 9) = true),
        ‖tailProfile D R K ι v G p j‖ ^ 2 := by
  obtain ⟨hg, -⟩ := grad_facts D K hK hv hp ι ((R.layouts K).layout ι).degCoef
  have e : ∀ p, (D.mesh.box K).lineWeight p.1 *
      ∑ j ∈ Finset.univ.filter (fun j : Fin 12 => decide (j.val < 9) = true), ‖tailProfile D R K ι v G p j‖ ^ 2
      = ∑ a : Fin 3, ∑ b : Fin 3, (D.mesh.box K).lineWeight p.1 * ‖gradAt D.azimuthOrder ι G a b p
        - (D.mesh.box K).proj ((R.layouts K).layout ι).degCoef ((R.layouts K).layout ι).degCoef
            (fun p' => gradAt D.azimuthOrder ι G a b p') p‖ ^ 2 := by
    intro p
    simp only [tailProfile, pair_strain, Finset.mul_sum]
  simp only [e]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hg a b).2]
  simp only [tailStrainSq, CellBox.tailNormSq, CellBox.normSqOn, CellBox.lineWeightFn]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => (hg a b).2]

lemma vel_eq (K : Fin D.mesh.count) (hK : IsCellBox (D.mesh.box K)) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {Pg : ℝ → Space → Space} (hv : IsPeriodicSecondOrder v G H) (hp : IsPeriodicPressure Pg) (ι : ℤ × ℤ) :
    tailVelSq D R K ι v = ∫ p in (D.mesh.box K).rect, (D.mesh.box K).lineWeight p.1 *
      ∑ j ∈ Finset.univ.filter (fun j : Fin 12 => decide (j.val < 9) = false),
        ‖tailProfile D R K ι v G p j‖ ^ 2 := by
  obtain ⟨-, hw⟩ := grad_facts D K hK hv hp ι (((R.layouts K).layout ι).degCoef - 1)
  have e : ∀ p, (D.mesh.box K).lineWeight p.1 *
      ∑ j ∈ Finset.univ.filter (fun j : Fin 12 => decide (j.val < 9) = false), ‖tailProfile D R K ι v G p j‖ ^ 2
      = ∑ a : Fin 3, (D.mesh.box K).lineWeight p.1 * ‖velAt D.azimuthOrder ι v a p
        - (D.mesh.box K).proj (((R.layouts K).layout ι).degCoef - 1) (((R.layouts K).layout ι).degCoef - 1)
            (fun p' => velAt D.azimuthOrder ι v a p') p‖ ^ 2 := by
    intro p
    simp only [tailProfile, pair_vel, Finset.mul_sum]
  simp only [e]
  rw [integral_finsetSum _ fun a _ => (hw a).2]
  simp only [tailVelSq, CellBox.tailNormSq, CellBox.normSqOn, CellBox.lineWeightFn]

lemma pairMatrix_eq {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (b : Bool) (ι : ℤ × ℤ) :
    tailGramPart D K B b ι = fun i i' => ∫ p in (D.mesh.box K).rect, ((D.mesh.box K).lineWeight p.1 : ℂ) *
      ∑ j ∈ Finset.univ.filter (fun j : Fin 12 => decide (j.val < 9) = b),
        (starRingEnd ℂ) (B.rowTailTest i ι p j) * B.rowTailTest i' ι p j := by
  funext i i'
  simp only [tailGramPart, Finset.sum_filter]

def crossRow {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (b : Bool) (ι : ℤ × ℤ) : Fin B.rowCount → ℂ :=
  fun i => ∫ p in (D.mesh.box K).rect, ((D.mesh.box K).lineWeight p.1 : ℂ) *
    ∑ j ∈ Finset.univ.filter (fun j : Fin 12 => decide (j.val < 9) = b),
      tailProfile D R K ι v G p j * (starRingEnd ℂ) (B.rowTailTest i ι p j)

end Apply

section Split

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

lemma tailRow_split {V : Type} (K : Fin D.mesh.count) (hK : IsCellBox (D.mesh.box K)) (B : CellBlocks V)
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {Pg : ℝ → Space → Space}
    (hv : IsPeriodicSecondOrder v G H) (hp : IsPeriodicPressure Pg)
    (hb : ∀ i, ∀ ι ∈ D.mesh.resolved K, ∀ j, IsBoundedOnCell D K (fun p => B.rowTailTest i ι p j)) :
    tailRow D R K B v G = ∑ ι ∈ D.mesh.resolved K, (crossRow D R K B v G true ι + crossRow D R K B v G false ι) := by
  funext i
  simp only [tailRow, Finset.sum_apply, Pi.add_apply, crossRow]
  refine Finset.sum_congr rfl fun ι hι => ?_
  obtain ⟨C0, -, hb0⟩ := uniform_bound (rect_measurable _) (fun i p j => B.rowTailTest i ι p j)
    (fun i j => (hb i ι hι j).2)
  have hcross := fun b : Bool => int_cross (Finset.univ.filter (fun j : Fin 12 => decide (j.val < 9) = b))
    (fun p => (D.mesh.box K).lineWeight p.1) (tailProfile D R K ι v G) (fun i p j => B.rowTailTest i ι p j)
    (weight_integrable _) (weight_nonneg hK) (fun j _ => (profile_facts D R K hK hv hp ι j).1)
    (fun j _ => (profile_facts D R K hK hv hp ι j).2) (fun i j _ => (hb i ι hι j).1)
    (hb0.mono fun p hp i j _ => hp i j) i
  rw [← integral_add (hcross true) (hcross false)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only
  rw [← mul_add, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  cases decide (j.val < 9) <;> simp

lemma tail_bound {V : Type} (K : Fin D.mesh.count) (hK : IsCellBox (D.mesh.box K)) (B : CellBlocks V)
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {Pg : ℝ → Space → Space}
    (hv : IsPeriodicSecondOrder v G H) (hp : IsPeriodicPressure Pg) (ι : ℤ × ℤ)
    (hb : ∀ i j, IsBoundedOnCell D K (fun p => B.rowTailTest i ι p j)) (b : Bool) {c : ℝ} (hc : 0 < c)
    (y : Fin B.rowCount → ℂ) :
    0 ≤ c⁻¹ * Coupling.quadForm (tailGramPart D K B b ι) y ∧
      -(2 * (star (crossRow D R K B v G b ι) ⬝ᵥ y).re) - c⁻¹ * Coupling.quadForm (tailGramPart D K B b ι) y
        ≤ c * ∫ p in (D.mesh.box K).rect, (D.mesh.box K).lineWeight p.1 *
          ∑ j ∈ Finset.univ.filter (fun j : Fin 12 => decide (j.val < 9) = b),
            ‖tailProfile D R K ι v G p j‖ ^ 2 := by
  obtain ⟨C0, hC0, hb0⟩ := uniform_bound (rect_measurable _) (fun i p j => B.rowTailTest i ι p j)
    (fun i j => (hb i j).2)
  rw [pairMatrix_eq]
  exact tail_piece (Finset.univ.filter (fun j : Fin 12 => decide (j.val < 9) = b))
    (fun p => (D.mesh.box K).lineWeight p.1) (tailProfile D R K ι v G) (fun i p j => B.rowTailTest i ι p j)
    (weight_integrable _) (weight_nonneg hK) (fun j _ => (profile_facts D R K hK hv hp ι j).1)
    (fun j _ => (profile_facts D R K hK hv hp ι j).2) (fun i j _ => (hb i j).1) hC0
    (hb0.mono fun p hp i j _ => hp i j) hc y

end Split

end Internal.RowRemoval

open Internal.RowRemoval in
theorem rowRemoval_core {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)
    (A : AssemblyEntry D R) (tauMax : ℝ) (hT : Instance.IsRowValues D.mesh D.rows D.azimuthOrder tauMax)
    (hC : RowConditions D R A) (K : Fin D.mesh.count) (q : Fin k → ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g : ℝ → Space → Space) (κ : Fin k → ℝ) (F Pg : ℝ → Space → Space)
    (ht : IsCellTuple D K q v G H g κ F Pg) (ζ : Fin k → ℝ) (η : Fin (R.portCount K) → ℂ) :
    Coupling.inverseWeightedSq (A.blocks K).rowWeight
        (rowVector D K (A.blocks K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) (fun ι => bandProfile D ι v G))
      ≤ Coupling.inverseWeightedSq (rowBaseWeight D K (A.blocks K)) (rowMoment D K (A.blocks K) F)
        + ∑ ι ∈ D.mesh.resolved K, ((A.blocks K).rowStrainCost ι * tailStrainSq D R K ι G
            + (A.blocks K).rowVelCost ι * tailVelSq D R K ι v)
        + Coupling.inverseWeightedSq (leakGram D K (A.blocks K))
            (rowMoment D K (A.blocks K) F
              - rowVector D K (A.blocks K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)
                  (fun ι => bandProfile D ι v G)
              - tailRow D R K (A.blocks K) v G) := by
  have hv : IsPeriodicSecondOrder v G H :=
    periodicSecondOrder_of_perturbation (Bridge.velocitySixthIntegral ⟨_, sixthPowerGradientBound_four_thirds⟩)
      Bridge.secondDerivEnergyIdentity _ _ v G H g ht.perturbation
  have hK : IsCellBox (D.mesh.box K) := hC.mesh_valid.box_valid K
  have hsplit := tailRow_split D R K hK (A.blocks K) hv ht.pressure (hC.tail_test_bounded K)
  have hblock : ∀ i i', rowGram D K (A.blocks K) i i' ≠ 0 →
      (A.blocks K).rowLabel i = (A.blocks K).rowLabel i' := by
    intro i i' hne
    by_contra hl
    exact hne (by simp only [rowGram, if_neg hl])
  have hL : (leakGram D K (A.blocks K)).PosDef :=
    base_posDef (hC.gram_pos K) (fun i => (A.blocks K).leakWeight ((A.blocks K).rowLabel i))
      (fun i => hC.leak_weight_pos K _ (hC.label_tested K i)) (fun i i' h => by simp only [hblock i i' h])
      (fun i i' => rfl)
  have hW : ((A.blocks K).rowWeight - rowBaseWeight D K (A.blocks K)
      - ∑ ι ∈ D.mesh.resolved K, (((A.blocks K).rowStrainCost ι : ℂ))⁻¹ • tailGramPart D K (A.blocks K) true ι
      - ∑ ι ∈ D.mesh.resolved K, (((A.blocks K).rowVelCost ι : ℂ))⁻¹ • tailGramPart D K (A.blocks K) false ι
      - (((1 : ℝ) : ℂ))⁻¹ • leakGram D K (A.blocks K)).PosSemidef := by
    rw [Complex.ofReal_one, inv_one, one_smul]
    exact hC.weight_dominates K
  rw [← one_mul (Coupling.inverseWeightedSq (leakGram D K (A.blocks K)) _)]
  refine assemble (D.mesh.resolved K) (fun ι => tailGramPart D K (A.blocks K) true ι)
    (fun ι => tailGramPart D K (A.blocks K) false ι) (A.blocks K).rowStrainCost (A.blocks K).rowVelCost
    (rowVector D K (A.blocks K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) (fun ι => bandProfile D ι v G))
    (rowMoment D K (A.blocks K) F)
    (rowMoment D K (A.blocks K) F
      - rowVector D K (A.blocks K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) (fun ι => bandProfile D ι v G)
      - tailRow D R K (A.blocks K) v G)
    (fun ι => crossRow D R K (A.blocks K) v G true ι) (fun ι => crossRow D R K (A.blocks K) v G false ι)
    (fun ι => tailStrainSq D R K ι G) (fun ι => tailVelSq D R K ι v) ?_ hL one_pos hW ?_ ?_ ?_
  · refine base_posDef (hC.gram_pos K) (fun i => D.rows.testWeight K ((A.blocks K).rowLabel i))
      (fun i => hT.weight_pos K _ (hC.label_tested K i)) (fun i i' h => by simp only [hblock i i' h])
      (fun i i' => rfl)
  · intro ι hι y
    have h := tail_bound D R K hK (A.blocks K) hv ht.pressure ι (fun i j => hC.tail_test_bounded K i ι hι j) true
      (hC.costs_pos K ι hι).1 y
    rw [← strain_eq D R K hK hv ht.pressure ι] at h
    exact h
  · intro ι hι y
    have h := tail_bound D R K hK (A.blocks K) hv ht.pressure ι (fun i j => hC.tail_test_bounded K i ι hι j) false
      (hC.costs_pos K ι hι).2 y
    rw [← vel_eq D R K hK hv ht.pressure ι] at h
    exact h
  · rw [hsplit]
    abel

open Internal.RowRemoval in
theorem rowRemoval : RowRemovalHolds := by
  intro k C nE nM D R A _ _ tauMax hT hC _ K q v G H g κ F Pg ht ζ η
  exact rowRemoval_core D R A tauMax hT hC K q v G H g κ F Pg ht ζ η

end Assembly

end CertCell

end Breakdown
