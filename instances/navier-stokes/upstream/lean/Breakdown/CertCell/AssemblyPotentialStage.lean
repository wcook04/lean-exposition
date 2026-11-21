import Breakdown.CertCell.AssemblyPotentialParts

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

namespace Internal

theorem strainOfVec_pairVec (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) : strainOfVec (pairVec s v) = s := by
  funext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem velOf_pairVec (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) : velOf (pairVec s v) = v := by
  funext a
  fin_cases a <;> rfl

theorem gradOf_pairVec (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) : gradOf (pairVec s v) = pairArray s := by
  funext ab
  obtain ⟨a, b⟩ := ab
  fin_cases a <;> fin_cases b <;> rfl

theorem rect_measurable (B : CellBox) : MeasurableSet B.rect :=
  measurableSet_Icc.prod measurableSet_Icc

theorem fst_nonneg_of_mem (B : CellBox) (hB : IsCellBox B) {p : ℝ × ℝ} (hp : p ∈ B.rect) : 0 ≤ p.1 := by
  simp only [CellBox.rect, Set.mem_prod, Set.mem_Icc] at hp
  linarith [hp.1.1, hB.r_order.1]

theorem tailNormSq_nonneg (B : CellBox) (hB : IsCellBox B) (Q : ℕ) (F : ℝ × ℝ → ℂ) : 0 ≤ B.tailNormSq Q F := by
  unfold CellBox.tailNormSq CellBox.normSqOn
  refine setIntegral_nonneg (rect_measurable B) (fun p hp => mul_nonneg ?_ (sq_nonneg _))
  simp only [CellBox.lineWeightFn, CellBox.lineWeight]
  split_ifs
  · exact fst_nonneg_of_mem B hB hp
  · norm_num

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

theorem lowAt_coe (K : Fin D.mesh.count) (x : CellVars D R K → ℂ) (ι : D.mesh.resolved K) (p : ℝ × ℝ) :
    lowAt D R K x ι.1 p = lowProfile D R K ι x p := by
  unfold lowAt
  rw [dif_pos ι.2]

theorem leaf_term_eq (K : Fin D.mesh.count) (y : CellVars D R K → ℂ) :
    ∑ ι : D.mesh.resolved K, (∫ p in (D.mesh.box K).rect,
        p.1 * sesqValue ((R.leaves K).localMatrix ι.1 p) (lowProfile D R K ι y p))
      = leafPair D R K (lowAt D R K y) (lowAt D R K y) := by
  unfold leafPair
  rw [← Finset.sum_coe_sort (M := ℝ) (D.mesh.resolved K)]
  refine Finset.sum_congr rfl (fun ι _ => ?_)
  simp only [lowAt_coe]
  rfl

theorem absorb_term_eq (K : Fin D.mesh.count) (y : CellVars D R K → ℂ) :
    ∑ ι : D.mesh.resolved K, (∫ p in (D.mesh.box K).rect,
        (D.mesh.box K).lineWeight p.1 * absorbValue D R K ι y p)
      = alAmount D R K (lowAt D R K y) := by
  unfold alAmount
  rw [← Finset.sum_coe_sort (M := ℝ) (D.mesh.resolved K)]
  refine Finset.sum_congr rfl (fun ι _ => ?_)
  simp only [lowAt_coe, lowProfile, strainOfVec_pairVec, velOf_pairVec, absorbValue]

theorem charge_term_eq (K : Fin D.mesh.count) (y : CellVars D R K → ℂ)
    (f : (Fin 3 → ℂ) → (Fin 3 × Fin 3 → ℂ) → ℝ) :
    ∑ ι : D.mesh.resolved K, (∫ p in (D.mesh.box K).rect,
        p.1 * f (lowVel D R K ι y p) (pairArray (lowGrad D R K ι y p)))
      = formAmount D K (D.mesh.resolved K) f (lowAt D R K y) := by
  unfold formAmount
  rw [← Finset.sum_coe_sort (M := ℝ) (D.mesh.resolved K)]
  refine Finset.sum_congr rfl (fun ι _ => ?_)
  simp only [lowAt_coe, lowProfile, velOf_pairVec, gradOf_pairVec]

theorem long_term_eq (K : Fin D.mesh.count) (y : CellVars D R K → ℂ)
    (f : ℤ × ℤ → (Fin 3 → ℂ) → (Fin 3 × Fin 3 → ℂ) → ℝ) :
    ∑ ι : D.mesh.resolved K, (∫ p in (D.mesh.box K).rect,
        p.1 * f ι.1 (lowVel D R K ι y p) (pairArray (lowGrad D R K ι y p)))
      = labelFormAmount D K (D.mesh.resolved K) f (lowAt D R K y) := by
  unfold labelFormAmount
  rw [← Finset.sum_coe_sort (M := ℝ) (D.mesh.resolved K)]
  refine Finset.sum_congr rfl (fun ι _ => ?_)
  simp only [lowAt_coe, lowProfile, velOf_pairVec, gradOf_pairVec]

theorem group_term_eq (K : Fin D.mesh.count) (P : PotentialData (CellVars D R K)) (x : CellVars D R K → ℂ) :
    ∑ i, P.groupBalance i * ∑ ι : D.mesh.resolved K, (if ι.1 ∈ P.groupModes i then ∫ p in (D.mesh.box K).rect,
        p.1 * groupCharge P i
          (lowVel D R K ι (upperPart D R K P x) p) (pairArray (lowGrad D R K ι (upperPart D R K P x) p)) else 0)
      = groupOwnAmount D R K P (upperProfiles D R K P x) := by
  unfold groupOwnAmount formAmount upperProfiles
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  rw [← Finset.filter_mem_eq_inter, Finset.sum_filter, ← Finset.sum_coe_sort (M := ℝ) (D.mesh.resolved K)]
  refine Finset.sum_congr rfl (fun ι _ => ?_)
  split_ifs
  · simp only [lowAt_coe, lowProfile, velOf_pairVec, gradOf_pairVec]
  · rfl

theorem potentialExact_eq (K : Fin D.mesh.count) (P : PotentialData (CellVars D R K)) (x : CellVars D R K → ℂ) :
    potentialExact D R K P x
      = couplingPair D R K P (upperPart D R K P x) (upperPart D R K P x)
        + 2 * couplingPair D R K P (upperPart D R K P x) (bandPart D R K P x)
        - leafPair D R K (lowAt D R K (bandPart D R K P x)) (lowAt D R K (bandPart D R K P x))
        - alAmount D R K (lowAt D R K (bandPart D R K P x))
        - quadFormValue P.portForm x
        - groupOwnAmount D R K P (upperProfiles D R K P x)
        - formAmount D K (D.mesh.resolved K) (epsOwnCharge P) (upperProfiles D R K P x)
        - labelFormAmount D K (D.mesh.resolved K) (longOwnCharge P) (upperProfiles D R K P x) := by
  unfold potentialExact
  rw [long_term_eq D R K _ (longOwnCharge P), leaf_term_eq, absorb_term_eq, group_term_eq, charge_term_eq]
  rfl

end Internal

namespace Internal

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

theorem tailStrainSq_nonneg (hM : IsCellMesh D.mesh) (K : Fin D.mesh.count) (ι : ℤ × ℤ)
    (G : ℝ → Space → (Space →L[ℝ] Space)) : 0 ≤ tailStrainSq D R K ι G :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => tailNormSq_nonneg _ (hM.box_valid K) _ _))

theorem tailVelSq_nonneg (hM : IsCellMesh D.mesh) (K : Fin D.mesh.count) (ι : ℤ × ℤ)
    (v : ℝ → Space → Space) : 0 ≤ tailVelSq D R K ι v :=
  Finset.sum_nonneg (fun _ _ => tailNormSq_nonneg _ (hM.box_valid K) _ _)

theorem tailCurlSq_nonneg (hM : IsCellMesh D.mesh) (K : Fin D.mesh.count) (ι : ℤ × ℤ)
    (G : ℝ → Space → (Space →L[ℝ] Space)) : 0 ≤ tailCurlSq D R K ι G :=
  Finset.sum_nonneg (fun _ _ => tailNormSq_nonneg _ (hM.box_valid K) _ _)

theorem tail_costs_le (A : AssemblyEntry D R) (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hC : PotentialConditions D R A P states)
    (K : Fin D.mesh.count) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) :
    (∑ ι ∈ D.mesh.resolved K, ((R.leaves K).curlAbsorb ι * tailCurlSq D R K ι G
          + (R.leaves K).strainAbsorb ι * tailStrainSq D R K ι G + (R.leaves K).velocityAbsorb ι * tailVelSq D R K ι v))
      + (∑ ι ∈ D.mesh.resolved K, ((P.potential K).strainBalance ι * tailStrainSq D R K ι G
            + (P.potential K).velBalance ι * tailVelSq D R K ι v))
      + (∑ ι ∈ D.mesh.resolved K, (rHatMax D K * (2 * (P.potential K).highStrain / (P.potential K).youngCurl
            + 3 / (2 * Real.sqrt 2) * (P.potential K).highGrad / (P.potential K).youngVel) * tailStrainSq D R K ι G
          + rHatMax D K * (3 / (2 * Real.sqrt 2) * (P.potential K).highGrad / (P.potential K).youngStrain)
            * tailVelSq D R K ι v))
      ≤ ∑ ι ∈ D.mesh.resolved K, ((A.blocks K).potentialStrainCost ι * tailStrainSq D R K ι G
            + (A.blocks K).potentialVelCost ι * tailVelSq D R K ι v
            + (A.blocks K).potentialCurlCost ι * tailCurlSq D R K ι G) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun ι hι => ?_)
  have hs := hC.strain_cost K ι hι
  have hv := hC.vel_cost K ι hι
  have hc := hC.curl_cost K ι hι
  have tS := tailStrainSq_nonneg D R hC.mesh_valid K ι G
  have tV := tailVelSq_nonneg D R hC.mesh_valid K ι v
  have tC := tailCurlSq_nonneg D R hC.mesh_valid K ι G
  have e1 := mul_le_mul_of_nonneg_right hs tS
  have e2 := mul_le_mul_of_nonneg_right hv tV
  have e3 := mul_le_mul_of_nonneg_right hc tC
  linarith

end Internal

open _root_.Breakdown.CertCell.Assembly.Internal in
theorem potentialStage_of_stages {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (R : CellCalculusEntry D) (A : AssemblyEntry D R) (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hC : PotentialConditions D R A P states)
    (hSE : StretchExpansion D R P) (hSS : StretchSplit D R P) (hLS : LeafSplit D R)
    (hSh : SharpStage D R P) (hMo : ModelStage D R A P) (hTC : TailCrossStage D R P) (hGr : GroupStage D R P)
    (hCh : ChargeStage D R A P) (hTH : TailHighStage D R P) (hEps : EpsResolvedStage D R P)
    (hSI : SplitIdentities D R P) (hS : CellStatesIn D R states) : PotentialStage D R A := by
  intro K q v G H g κ F Pg ht ζ η
  have h1 := hSE K q v G H g κ F Pg ht
  have h2 := hSS K q v G H g κ F Pg ht ζ η
  have h3 := hLS K q v G H g κ F Pg ht ζ η
  have h4 := hSh K q v G H g κ F Pg ht ζ η
  have h5 := hMo K q v G H g κ F Pg ht ζ η
  have h6 := hTC K q v G H g κ F Pg ht ζ η
  have h7 := hGr K q v G H g κ F Pg ht ζ η
  have h8 := hCh K q v G H g κ F Pg ht
  have h9 := hTH K q v G H g κ F Pg ht
  have h10 := hEps K q v G H g κ F Pg ht ζ η
  obtain ⟨h11, h12, h13⟩ := hSI K q v G H g κ F Pg ht ζ η
  have hk := hC.kept_le K (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) (hS K q v G H g κ F Pg ht ζ η)
  rw [potentialExact_eq] at hk
  have hcost := tail_costs_le D R A P hC K v G
  linarith

theorem potentialAssembly_holds : PotentialAssemblyHolds := by
  intro k C nE nM D R A P states hstates _ _ _ hC hSE hSS hLS hSh hMo hTC hGr hCh hTH hEps hSI
  exact potentialStage_of_stages D R A P hC hSE hSS hLS hSh hMo hTC hGr hCh hTH hEps hSI hstates

end Assembly

end CertCell

end Breakdown
