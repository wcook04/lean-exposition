import Breakdown.CertCell.AssemblyPotentialParts
import Breakdown.CertCell.AssemblyPotentialGroups

open MeasureTheory Matrix
open scoped ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

def ModelCrossBoundStatement : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)
    (A : AssemblyEntry D R) (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop}, PotentialConditions D R A P states →
    ∀ (K : Fin D.mesh.count) (B : Finset (ℤ × ℤ)),
    (∀ ι ∈ D.mesh.resolved K, ∀ β ∈ B, -β ∈ modelLabels D K → ι + β ∉ D.mesh.resolved K →
      ι + β ∉ D.mesh.band K → ∃ i, ι ∈ (P.potential K).groupModes i ∧ ι + β ∈ (P.potential K).groupPartners i ∧
        β ∈ (P.potential K).groupHarmonics i) →
    (∀ i, (P.potential K).groupHarmonics i ⊆ B) →
    (∀ i j β, β ∈ (P.potential K).groupHarmonics i → β ∈ (P.potential K).groupHarmonics j → i = j) →
    ∀ (X Y : ℤ × ℤ → (Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ)), ∀ p ∈ (D.mesh.box K).rect,
    2 * ‖∑ ι ∈ D.mesh.resolved K, ∑ β ∈ B, if ι + β ∉ D.mesh.resolved K ∧ ι + β ∉ D.mesh.band K then
        modelTriple (fun a b => D.model.strain.planeValue D.mesh.box K β a b p)
          (fun a b => D.model.vorticityGrad.planeValue D.mesh.box K β a b p) (X ι).1 (X ι).2
          (star (Y (ι + β)).1) (star (Y (ι + β)).2) else 0‖
      ≤ ∑ i, ((P.potential K).groupBalance i * (∑ ι ∈ D.mesh.resolved K,
            if ι ∈ (P.potential K).groupModes i then groupCharge (P.potential K) i (X ι).1 (X ι).2 else 0)
          + ((P.potential K).groupBalance i)⁻¹ * (∑ ι' ∈ (P.potential K).groupPartners i,
            if ι' ∉ D.mesh.resolved K ∧ ι' ∉ D.mesh.band K then
              groupCharge (P.potential K) i (Y ι').1 (Y ι').2 else 0))

def CouplingModelReStatement : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)
    (A : AssemblyEntry D R) (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop}, PotentialConditions D R A P states →
    ∀ (K : Fin D.mesh.count) (α : ℤ × ℤ), ∀ p ∈ (D.mesh.box K).rect, ∀ U U' : Fin 12 → ℂ,
    (sesq12 ((P.potential K).couplingModel α p) U U').re
      = (modelTriple (fun a b => D.model.strain.planeValue D.mesh.box K (-α) a b p)
          (fun a b => D.model.vorticityGrad.planeValue D.mesh.box K (-α) a b p)
          (velOf U) (gradOf U) (star (velOf U')) (star (gradOf U'))).re

variable {k : ℕ} {C : Type} {nE nM : ℕ}

theorem rect_fst_nonneg (D : CellLayerData k C nE nM) (hM : IsCellMesh D.mesh) (K : Fin D.mesh.count)
    (p : ℝ × ℝ) (hp : p ∈ (D.mesh.box K).rect) : 0 ≤ p.1 :=
  le_trans (hM.box_valid K).r_order.1 hp.1.1

theorem upperProfiles_continuous (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (K : Fin D.mesh.count)
    (P : PotentialData (CellVars D R K)) (x : CellVars D R K → ℂ) (ι : ℤ × ℤ) (j : Fin 12) :
    Continuous (fun p => upperProfiles D R K P x ι p j) := by
  unfold upperProfiles lowAt
  by_cases h : ι ∈ D.mesh.resolved K
  · simp only [dif_pos h]
    unfold lowProfile pairVec lowGrad lowVel lowStrainOf lowVelocityOf CellCert.CellEnergy.basisFn CellBases.radialPoly
      CellBases.heightPoly
    split_ifs <;> fun_prop
  · simp only [dif_neg h]
    exact continuous_const

theorem cnormSq_nonneg' {β : Type*} [Fintype β] (x : β → ℂ) : 0 ≤ cnormSq x :=
  Finset.sum_nonneg (fun _ _ => by positivity)

theorem alternatingSymbol_abs_le (i j l : Fin 3) : |alternatingSymbol i j l| ≤ 1 := by
  unfold alternatingSymbol
  fin_cases i <;> fin_cases j <;> fin_cases l <;> norm_num

theorem curl_cnormSq_le (g : Fin 3 × Fin 3 → ℂ) : cnormSq (curlOfGrad g) ≤ 27 * cnormSq g := by
  have hi : ∀ i, ‖curlOfGrad g i‖ ^ 2 ≤ 9 * cnormSq g := by
    intro i
    have h1 : ‖curlOfGrad g i‖ ≤ ∑ j : Fin 3, ∑ l : Fin 3, ‖g (l, j)‖ := by
      unfold curlOfGrad
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun j _ => le_trans (norm_sum_le _ _)
        (Finset.sum_le_sum (fun l _ => ?_))))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact le_trans (mul_le_mul_of_nonneg_right (alternatingSymbol_abs_le i j l) (norm_nonneg _)) (by rw [one_mul])
    have h2 : (∑ j : Fin 3, ∑ l : Fin 3, ‖g (l, j)‖) ^ 2 ≤ 9 * cnormSq g := by
      have e : (∑ j : Fin 3, ∑ l : Fin 3, ‖g (l, j)‖) = ∑ lj : Fin 3 × Fin 3, ‖g lj‖ := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
      rw [e]
      have hs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 3 × Fin 3))) (f := fun lj => ‖g lj‖)
      simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hs
      unfold cnormSq
      norm_num at hs ⊢
      linarith
    exact le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2
  unfold cnormSq
  calc ∑ i : Fin 3, ‖curlOfGrad g i‖ ^ 2 ≤ ∑ _i : Fin 3, 9 * cnormSq g := Finset.sum_le_sum (fun i _ => hi i)
    _ = 27 * cnormSq g := by simp; ring

theorem gradOf_velOf_cnormSq (U : Fin 12 → ℂ) : cnormSq (gradOf U) + cnormSq (velOf U) = ∑ j, ‖U j‖ ^ 2 := by
  simp only [cnormSq, gradOf, velOf, Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp
  ring

theorem splitCharge_le (σc cs cv : ℝ) (hσ : 0 ≤ σc) (hs : 0 ≤ cs) (hv : 0 ≤ cv) (U : Fin 12 → ℂ) :
    splitCharge σc cs cv (velOf U) (gradOf U) ≤ (27 * σc + cs + cv) * ∑ j, ‖U j‖ ^ 2 := by
  unfold splitCharge
  have e := gradOf_velOf_cnormSq U
  have hg := cnormSq_nonneg' (gradOf U)
  have hv' := cnormSq_nonneg' (velOf U)
  have hc := curl_cnormSq_le (gradOf U)
  have h1 : σc * cnormSq (curlOfGrad (gradOf U)) ≤ 27 * σc * ∑ j, ‖U j‖ ^ 2 := by
    rw [← e]
    nlinarith
  have h2 : cs * cnormSq (gradOf U) ≤ cs * ∑ j, ‖U j‖ ^ 2 := by
    rw [← e]
    exact mul_le_mul_of_nonneg_left (by linarith) hs
  have h3 : cv * cnormSq (velOf U) ≤ cv * ∑ j, ‖U j‖ ^ 2 := by
    rw [← e]
    exact mul_le_mul_of_nonneg_left (by linarith) hv
  linarith

theorem groupsProfile_aemeasurable (μ : Measure (ℝ × ℝ)) (Y : ℝ × ℝ → Fin 12 → ℂ)
    (hY : ∀ j, AEStronglyMeasurable (fun p => Y p j) μ) : AEMeasurable Y μ :=
  aemeasurable_pi_iff.2 (fun j => (hY j).aemeasurable)

theorem splitCharge_continuous (σc cs cv : ℝ) :
    Continuous (fun U : Fin 12 → ℂ => splitCharge σc cs cv (velOf U) (gradOf U)) := by
  unfold splitCharge cnormSq curlOfGrad velOf gradOf
  fun_prop

theorem chargeY_integrable (μ : Measure (ℝ × ℝ)) (Y : ℝ × ℝ → Fin 12 → ℂ) (σc cs cv : ℝ) (hσ : 0 ≤ σc)
    (hs : 0 ≤ cs) (hv : 0 ≤ cv) (hY : ∀ j, AEStronglyMeasurable (fun p => Y p j) μ)
    (hI : Integrable (fun p => p.1 * ∑ j, ‖Y p j‖ ^ 2) μ) (hpos : ∀ᵐ p ∂μ, 0 ≤ p.1) :
    Integrable (fun p => p.1 * splitCharge σc cs cv (velOf (Y p)) (gradOf (Y p))) μ := by
  refine Integrable.mono' (hI.const_mul (27 * σc + cs + cv)) ?_ ?_
  · exact (continuous_fst.aemeasurable.mul ((splitCharge_continuous σc cs cv).measurable.comp_aemeasurable
      (groupsProfile_aemeasurable μ Y hY))).aestronglyMeasurable
  · filter_upwards [hpos] with p hp
    have h0 := splitCharge_nonneg hσ hs hv (velOf (Y p)) (gradOf (Y p))
    have h1 := splitCharge_le σc cs cv hσ hs hv (Y p)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp h0)]
    calc p.1 * splitCharge σc cs cv (velOf (Y p)) (gradOf (Y p))
        ≤ p.1 * ((27 * σc + cs + cv) * ∑ j, ‖Y p j‖ ^ 2) := mul_le_mul_of_nonneg_left h1 hp
      _ = _ := by ring

theorem groupCoeffs (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count)
    (i : Fin (P.potential K).groupCount) :
    0 ≤ (P.potential K).groupStrain i ∧
      0 ≤ (P.potential K).groupKappa i / 2 * (P.potential K).groupGrad i * (P.potential K).length ∧
      0 ≤ (P.potential K).groupKappa i / 2 * (P.potential K).groupGrad i / (P.potential K).length := by
  obtain ⟨-, hσ, hγ⟩ := hP.group_pos K i
  have hκ := kappa_nonneg (hP.group_kappa K i)
  have hℓ := hP.length_pos K
  exact ⟨hσ, by positivity, by positivity⟩

theorem groupCharge_nonneg (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count)
    (i : Fin (P.potential K).groupCount) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) :
    0 ≤ groupCharge (P.potential K) i a g := by
  obtain ⟨h1, h2, h3⟩ := groupCoeffs D R A P hP K i
  unfold groupCharge
  exact splitCharge_nonneg h1 h2 h3 a g

theorem groupCharge_continuous {V : Type} (P : PotentialData V) (i : Fin P.groupCount) :
    Continuous (fun U : Fin 12 → ℂ => groupCharge P i (velOf U) (gradOf U)) := by
  unfold groupCharge
  exact splitCharge_continuous _ _ _

theorem sesq_zero_right (M : Matrix (Fin 12) (Fin 12) ℂ) (U : Fin 12 → ℂ) : sesq12 M U 0 = 0 := by
  simp [sesq12]

private theorem sesq_zero_matrix (U U' : Fin 12 → ℂ) : sesq12 0 U U' = 0 := by
  simp [sesq12]

theorem sum_inter_eq_ite {β : Type*} [AddCommMonoid β] (S T : Finset (ℤ × ℤ)) (f : ℤ × ℤ → β) :
    ∑ ι ∈ S ∩ T, f ι = ∑ ι ∈ S, if ι ∈ T then f ι else 0 := by
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]

private theorem modelTriple_zero_left (S Gω : Fin 3 → Fin 3 → ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) :
    modelTriple S Gω 0 0 a g = 0 := by
  simp [modelTriple, modelBilin, curlOfGrad]

private theorem modelTriple_zero_right (S Gω : Fin 3 → Fin 3 → ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) :
    modelTriple S Gω a g 0 0 = 0 := by
  simp [modelTriple, modelBilin, curlOfGrad]

private theorem groupCharge_zero {V : Type} (P : PotentialData V) (i : Fin P.groupCount) :
    groupCharge P i 0 0 = 0 := by
  simp [groupCharge, splitCharge, cnormSq, curlOfGrad]

private theorem crossCover (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count) :
    ∀ ι ∈ D.mesh.resolved K, ∀ β ∈ (P.potential K).harmonicLabels.image Neg.neg, -β ∈ modelLabels D K →
      ι + β ∉ D.mesh.resolved K → ι + β ∉ D.mesh.band K →
      ∃ i, ι ∈ (P.potential K).groupModes i ∧ ι + β ∈ (P.potential K).groupPartners i ∧
        β ∈ (P.potential K).groupHarmonics i := by
  intro ι hι β hβ hm h1 h2
  obtain ⟨α, -, rfl⟩ := Finset.mem_image.1 hβ
  rw [neg_neg] at hm
  rw [← sub_eq_add_neg] at h1 h2 ⊢
  exact hP.group_link K ι hι α hm h1 h2

private theorem crossSub (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count) :
    ∀ i, (P.potential K).groupHarmonics i ⊆ (P.potential K).harmonicLabels.image Neg.neg := by
  intro i β hβ
  exact Finset.mem_image.2 ⟨-β, hP.group_in_labels K i β hβ, neg_neg β⟩

private theorem pairModelBound (hCross : ModelCrossBoundStatement) (D : CellLayerData k C nE nM)
    (R : CellCalculusEntry D) (A : AssemblyEntry D R) (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states)
    (K : Fin D.mesh.count) (ι ι' : ℤ × ℤ) (hι : ι ∈ D.mesh.resolved K) (h1 : ι' ∉ D.mesh.resolved K)
    (h2 : ι' ∉ D.mesh.band K) (hα : ι - ι' ∈ (P.potential K).harmonicLabels)
    (x y : (Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ)) (p : ℝ × ℝ) (hp : p ∈ (D.mesh.box K).rect) :
    2 * ‖modelTriple (fun a b => D.model.strain.planeValue D.mesh.box K (ι' - ι) a b p)
        (fun a b => D.model.vorticityGrad.planeValue D.mesh.box K (ι' - ι) a b p) x.1 x.2 (star y.1) (star y.2)‖
      ≤ ∑ i, ((P.potential K).groupBalance i * groupCharge (P.potential K) i x.1 x.2
          + ((P.potential K).groupBalance i)⁻¹ * groupCharge (P.potential K) i y.1 y.2) := by
  have h := hCross D R A P hP K _ (crossCover D R A P hP K) (crossSub D R A P hP K) (hP.group_disjoint K)
    (fun κ => if κ = ι then x else 0) (fun κ => if κ = ι' then y else 0) p hp
  have he : ι + (ι' - ι) = ι' := by abel
  have hβ : ι' - ι ∈ (P.potential K).harmonicLabels.image Neg.neg :=
    Finset.mem_image.2 ⟨ι - ι', hα, by abel⟩
  rw [Finset.sum_eq_single_of_mem ι hι (fun κ _ hκ => Finset.sum_eq_zero (fun β _ => by
      simp [hκ, modelTriple_zero_left])),
    Finset.sum_eq_single_of_mem (ι' - ι) hβ (fun β _ hβ' => by
      have hne : ι + β ≠ ι' := fun h => hβ' (by rw [← h]; abel)
      simp [hne, modelTriple_zero_right])] at h
  simp only [he, h1, h2, not_false_eq_true, and_self, if_true] at h
  refine le_trans h (Finset.sum_le_sum (fun i _ => ?_))
  obtain ⟨hbal, -, -⟩ := hP.group_pos K i
  have hx : (∑ κ ∈ D.mesh.resolved K, if κ ∈ (P.potential K).groupModes i then
      groupCharge (P.potential K) i (if κ = ι then x else 0).1 (if κ = ι then x else 0).2 else 0)
      ≤ groupCharge (P.potential K) i x.1 x.2 := by
    calc _ ≤ ∑ κ ∈ D.mesh.resolved K, if κ = ι then groupCharge (P.potential K) i x.1 x.2 else 0 := by
          refine Finset.sum_le_sum (fun κ _ => ?_)
          by_cases hκ : κ = ι
          · subst hκ
            simp only [if_true]
            split_ifs
            · exact le_rfl
            · exact groupCharge_nonneg D R A P hP K i _ _
          · simp [hκ, groupCharge_zero]
      _ = _ := by rw [Finset.sum_ite_eq' (D.mesh.resolved K) ι, if_pos hι]
  have hy : (∑ κ ∈ (P.potential K).groupPartners i, if κ ∉ D.mesh.resolved K ∧ κ ∉ D.mesh.band K then
      groupCharge (P.potential K) i (if κ = ι' then y else 0).1 (if κ = ι' then y else 0).2 else 0)
      ≤ groupCharge (P.potential K) i y.1 y.2 := by
    calc _ ≤ ∑ κ ∈ (P.potential K).groupPartners i, if κ = ι' then groupCharge (P.potential K) i y.1 y.2 else 0 := by
          refine Finset.sum_le_sum (fun κ _ => ?_)
          by_cases hκ : κ = ι'
          · subst hκ
            simp only [if_true]
            split_ifs
            · exact le_rfl
            · exact groupCharge_nonneg D R A P hP K i _ _
          · simp [hκ, groupCharge_zero]
      _ ≤ _ := by
          rw [Finset.sum_ite_eq' ((P.potential K).groupPartners i) ι']
          split_ifs
          · exact le_rfl
          · exact groupCharge_nonneg D R A P hP K i _ _
  exact add_le_add (mul_le_mul_of_nonneg_left hx hbal.le) (mul_le_mul_of_nonneg_left hy (inv_nonneg.2 hbal.le))

private theorem cellPoly_eval_continuous (B : CellBox) (Q : CellPoly) : Continuous (fun p : ℝ × ℝ => Q.eval B p) := by
  unfold CellPoly.eval CellBox.refR CellBox.refZ
  fun_prop

private theorem matPlaneValue_measurable {count : ℕ} (F : CellMatField count) (box : Fin count → CellBox)
    (K : Fin count) (α : ℤ × ℤ) (a b : Fin 3) : Measurable (fun p => F.planeValue box K α a b p) := by
  unfold CellMatField.planeValue labelValueAt
  refine Measurable.ite (measurableSet_le measurable_const measurable_snd)
    (cellPoly_eval_continuous _ _).measurable ?_
  exact ((cellPoly_eval_continuous _ _).comp (continuous_fst.prodMk continuous_snd.neg)).measurable.const_mul _

private theorem matPlane_measurable {count : ℕ} (F : CellMatField count) (box : Fin count → CellBox)
    (K : Fin count) (α : ℤ × ℤ) : Measurable (fun p => fun a b => F.planeValue box K α a b p) :=
  measurable_pi_lambda _ (fun a => measurable_pi_lambda _ (fun b => matPlaneValue_measurable F box K α a b))

private theorem modelRe_continuous :
    Continuous (fun z : (Fin 3 → Fin 3 → ℂ) × (Fin 3 → Fin 3 → ℂ) × (Fin 12 → ℂ) × (Fin 12 → ℂ) =>
      (modelTriple z.1 z.2.1 (velOf z.2.2.1) (gradOf z.2.2.1) (star (velOf z.2.2.2))
        (star (gradOf z.2.2.2))).re) := by
  unfold modelTriple modelBilin curlOfGrad velOf gradOf
  simp only [Pi.star_apply]
  fun_prop

private theorem modelIntegrand_integrable (hCross : ModelCrossBoundStatement) (hCoup : CouplingModelReStatement)
    (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count)
    (Xp Yp : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) (hXc : ∀ ι j, Continuous (fun p => Xp ι p j))
    (hYm : ∀ ι j, AEStronglyMeasurable (fun p => Yp ι p j) (volume.restrict (D.mesh.box K).rect))
    (hXi : ∀ i ι, Integrable (fun p => p.1 * groupCharge (P.potential K) i (velOf (Xp ι p)) (gradOf (Xp ι p)))
      (volume.restrict (D.mesh.box K).rect))
    (hYi : ∀ i ι, Integrable (fun p => p.1 * groupCharge (P.potential K) i (velOf (Yp ι p)) (gradOf (Yp ι p)))
      (volume.restrict (D.mesh.box K).rect))
    (ι : ℤ × ℤ) (hι : ι ∈ D.mesh.resolved K) (ι' : ℤ × ℤ) (h1 : ι' ∉ D.mesh.resolved K)
    (h2 : ι' ∉ D.mesh.band K) :
    Integrable (fun p => p.1 * (sesq12 ((P.potential K).couplingModel (ι - ι') p) (Xp ι p) (Yp ι' p)).re)
      (volume.restrict (D.mesh.box K).rect) := by
  have hms : MeasurableSet (D.mesh.box K).rect := measurableSet_Icc.prod measurableSet_Icc
  by_cases hα : ι - ι' ∈ (P.potential K).harmonicLabels
  · have hI : Integrable (fun p => ∑ i, ((P.potential K).groupBalance i / 2
          * (p.1 * groupCharge (P.potential K) i (velOf (Xp ι p)) (gradOf (Xp ι p)))
        + ((P.potential K).groupBalance i)⁻¹ / 2
          * (p.1 * groupCharge (P.potential K) i (velOf (Yp ι' p)) (gradOf (Yp ι' p)))))
        (volume.restrict (D.mesh.box K).rect) :=
      integrable_finsetSum _ (fun i _ => ((hXi i ι).const_mul ((P.potential K).groupBalance i / 2)).add
        ((hYi i ι').const_mul (((P.potential K).groupBalance i)⁻¹ / 2)))
    refine Integrable.mono' hI ?_ ?_
    · have hg : AEStronglyMeasurable (fun p => p.1 * (modelTriple
          (fun a b => D.model.strain.planeValue D.mesh.box K (ι - ι') a b p)
          (fun a b => D.model.vorticityGrad.planeValue D.mesh.box K (ι - ι') a b p)
          (velOf (Yp ι' p)) (gradOf (Yp ι' p)) (star (velOf (Xp ι p))) (star (gradOf (Xp ι p)))).re)
          (volume.restrict (D.mesh.box K).rect) := by
        have hxm : AEMeasurable (fun p => Xp ι p) (volume.restrict (D.mesh.box K).rect) :=
          (continuous_pi (fun j => hXc ι j)).aemeasurable
        have hym : AEMeasurable (fun p => Yp ι' p) (volume.restrict (D.mesh.box K).rect) :=
          groupsProfile_aemeasurable _ (Yp ι') (hYm ι')
        exact (continuous_fst.aemeasurable.mul (modelRe_continuous.measurable.comp_aemeasurable
          ((matPlane_measurable _ _ K _).aemeasurable.prodMk ((matPlane_measurable _ _ K _).aemeasurable.prodMk
            (hym.prodMk hxm))))).aestronglyMeasurable
      refine hg.congr ?_
      filter_upwards [ae_restrict_mem hms] with p hp
      rw [hP.coupling_model K (ι - ι') p hp]
    · filter_upwards [ae_restrict_mem hms] with p hp
      have hp1 : 0 ≤ p.1 := rect_fst_nonneg D hP.mesh_valid K p hp
      rw [hCoup D R A P hP K (ι - ι') p hp, neg_sub]
      have hb := pairModelBound hCross D R A P hP K ι ι' hι h1 h2 hα (velOf (Xp ι p), gradOf (Xp ι p))
        (velOf (Yp ι' p), gradOf (Yp ι' p)) p hp
      have hre := Complex.abs_re_le_norm (modelTriple (fun a b => D.model.strain.planeValue D.mesh.box K (ι' - ι) a b p)
        (fun a b => D.model.vorticityGrad.planeValue D.mesh.box K (ι' - ι) a b p) (velOf (Xp ι p)) (gradOf (Xp ι p))
        (star (velOf (Yp ι' p))) (star (gradOf (Yp ι' p))))
      have e : (∑ i, ((P.potential K).groupBalance i / 2
            * (p.1 * groupCharge (P.potential K) i (velOf (Xp ι p)) (gradOf (Xp ι p)))
          + ((P.potential K).groupBalance i)⁻¹ / 2
            * (p.1 * groupCharge (P.potential K) i (velOf (Yp ι' p)) (gradOf (Yp ι' p)))))
          = p.1 / 2 * ∑ i, ((P.potential K).groupBalance i
              * groupCharge (P.potential K) i (velOf (Xp ι p)) (gradOf (Xp ι p))
            + ((P.potential K).groupBalance i)⁻¹
              * groupCharge (P.potential K) i (velOf (Yp ι' p)) (gradOf (Yp ι' p))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp1, e]
      have hm := mul_le_mul_of_nonneg_left hre hp1
      have hb' := mul_le_mul_of_nonneg_left hb hp1
      nlinarith
  · refine (integrable_zero _ _ _).congr ?_
    filter_upwards [ae_restrict_mem hms] with p hp
    rw [hP.model_off_labels K _ hα p hp, sesq_zero_matrix]
    simp

private theorem modelPair_row_rewrite (hCoup : CouplingModelReStatement) (D : CellLayerData k C nE nM)
    (R : CellCalculusEntry D) (A : AssemblyEntry D R) (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states)
    (K : Fin D.mesh.count) (Xp Yp : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) (p : ℝ × ℝ) (hp : p ∈ (D.mesh.box K).rect)
    (ι : ℤ × ℤ) (hι : ι ∈ D.mesh.resolved K) :
    ∑ ι' ∈ deactPartners D R K (P.potential K),
        p.1 * (sesq12 ((P.potential K).couplingModel (ι - ι') p) (Xp ι p) (Yp ι' p)).re
      = p.1 * (∑ β ∈ (P.potential K).harmonicLabels.image Neg.neg,
          if ι + β ∉ D.mesh.resolved K ∧ ι + β ∉ D.mesh.band K then
            modelTriple (fun a b => D.model.strain.planeValue D.mesh.box K β a b p)
              (fun a b => D.model.vorticityGrad.planeValue D.mesh.box K β a b p) (velOf (Xp ι p)) (gradOf (Xp ι p))
              (star (velOf (Yp (ι + β) p))) (star (gradOf (Yp (ι + β) p))) else 0).re := by
  have hsub : (((P.potential K).harmonicLabels.image Neg.neg).filter
      (fun β => ι + β ∉ D.mesh.resolved K ∧ ι + β ∉ D.mesh.band K)).image (fun β => ι + β)
      ⊆ deactPartners D R K (P.potential K) := by
    intro ι' h
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨hβB, hc⟩ := Finset.mem_filter.1 hβ
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hβB
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(ι, α), Finset.mem_product.2 ⟨hι, hα⟩, ?_⟩, hc⟩
    simp [sub_eq_add_neg]
  have hz : ∀ ι' ∈ deactPartners D R K (P.potential K), ι' ∉ (((P.potential K).harmonicLabels.image Neg.neg).filter
      (fun β => ι + β ∉ D.mesh.resolved K ∧ ι + β ∉ D.mesh.band K)).image (fun β => ι + β) →
      p.1 * (sesq12 ((P.potential K).couplingModel (ι - ι') p) (Xp ι p) (Yp ι' p)).re = 0 := by
    intro ι' h hn
    have hc := (Finset.mem_filter.1 h).2
    have hα : ι - ι' ∉ (P.potential K).harmonicLabels := by
      intro hα
      apply hn
      refine Finset.mem_image.2 ⟨ι' - ι, Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨ι - ι', hα, by abel⟩, ?_⟩, by abel⟩
      rw [show ι + (ι' - ι) = ι' by abel]
      exact hc
    rw [hP.model_off_labels K _ hα p hp, sesq_zero_matrix]
    simp
  rw [← Finset.sum_subset (f := fun ι' => p.1 * (sesq12 ((P.potential K).couplingModel (ι - ι') p) (Xp ι p)
      (Yp ι' p)).re) hsub hz, Finset.sum_image (fun a _ b _ h => add_left_cancel h), Finset.sum_filter,
    Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun β hβ => ?_)
  split_ifs with hc
  · obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hβ
    rw [show ι - (ι + -α) = α by abel, hCoup D R A P hP K α p hp]
  · simp

theorem groupPointwise (hCross : ModelCrossBoundStatement) (hCoup : CouplingModelReStatement)
    (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count)
    (Xp Yp : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) (p : ℝ × ℝ) (hp : p ∈ (D.mesh.box K).rect) :
    -(∑ i, ((P.potential K).groupBalance i * ∑ ι ∈ D.mesh.resolved K ∩ (P.potential K).groupModes i,
        p.1 * groupCharge (P.potential K) i (velOf (Xp ι p)) (gradOf (Xp ι p))
      + (∑ ι ∈ (P.potential K).groupPartners i, p.1 * groupCharge (P.potential K) i (velOf (Yp ι p)) (gradOf (Yp ι p)))
        / (P.potential K).groupBalance i))
      ≤ 2 * ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ deactPartners D R K (P.potential K),
          p.1 * (sesq12 ((P.potential K).couplingModel (ι - ι') p) (Xp ι p) (Yp ι' p)).re := by
  have hp1 : 0 ≤ p.1 := rect_fst_nonneg D hP.mesh_valid K p hp
  rw [Finset.sum_congr rfl (fun ι hι => modelPair_row_rewrite hCoup D R A P hP K Xp Yp p hp ι hι),
    ← Finset.mul_sum, ← Complex.re_sum]
  have hb := hCross D R A P hP K _ (crossCover D R A P hP K) (crossSub D R A P hP K) (hP.group_disjoint K)
    (fun ι => (velOf (Xp ι p), gradOf (Xp ι p))) (fun ι => (velOf (Yp ι p), gradOf (Yp ι p))) p hp
  set z := ∑ ι ∈ D.mesh.resolved K, ∑ β ∈ (P.potential K).harmonicLabels.image Neg.neg,
    (if ι + β ∉ D.mesh.resolved K ∧ ι + β ∉ D.mesh.band K then
      modelTriple (fun a b => D.model.strain.planeValue D.mesh.box K β a b p)
        (fun a b => D.model.vorticityGrad.planeValue D.mesh.box K β a b p) (velOf (Xp ι p)) (gradOf (Xp ι p))
        (star (velOf (Yp (ι + β) p))) (star (gradOf (Yp (ι + β) p))) else 0) with hz
  have hre : -‖z‖ ≤ z.re := by
    have := Complex.abs_re_le_norm z
    linarith [neg_abs_le z.re]
  have hcost : ∀ i, (P.potential K).groupBalance i * (∑ ι ∈ D.mesh.resolved K,
        if ι ∈ (P.potential K).groupModes i then groupCharge (P.potential K) i (velOf (Xp ι p)) (gradOf (Xp ι p)) else 0)
      + ((P.potential K).groupBalance i)⁻¹ * (∑ ι' ∈ (P.potential K).groupPartners i,
        if ι' ∉ D.mesh.resolved K ∧ ι' ∉ D.mesh.band K then
          groupCharge (P.potential K) i (velOf (Yp ι' p)) (gradOf (Yp ι' p)) else 0)
      ≤ (P.potential K).groupBalance i * (∑ ι ∈ D.mesh.resolved K ∩ (P.potential K).groupModes i,
          groupCharge (P.potential K) i (velOf (Xp ι p)) (gradOf (Xp ι p)))
        + ((P.potential K).groupBalance i)⁻¹ * (∑ ι' ∈ (P.potential K).groupPartners i,
          groupCharge (P.potential K) i (velOf (Yp ι' p)) (gradOf (Yp ι' p))) := by
    intro i
    obtain ⟨hbal, hσ, hγ⟩ := hP.group_pos K i
    rw [sum_inter_eq_ite]
    refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ι' _ => ?_))
      (inv_nonneg.2 hbal.le))
    split_ifs
    · exact le_rfl
    · exact groupCharge_nonneg D R A P hP K i _ _
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcost i)
  have hlhs : (∑ i, ((P.potential K).groupBalance i * ∑ ι ∈ D.mesh.resolved K ∩ (P.potential K).groupModes i,
        p.1 * groupCharge (P.potential K) i (velOf (Xp ι p)) (gradOf (Xp ι p))
      + (∑ ι ∈ (P.potential K).groupPartners i, p.1 * groupCharge (P.potential K) i (velOf (Yp ι p)) (gradOf (Yp ι p)))
        / (P.potential K).groupBalance i))
      = p.1 * ∑ i, ((P.potential K).groupBalance i * (∑ ι ∈ D.mesh.resolved K ∩ (P.potential K).groupModes i,
          groupCharge (P.potential K) i (velOf (Xp ι p)) (gradOf (Xp ι p)))
        + ((P.potential K).groupBalance i)⁻¹ * (∑ ι' ∈ (P.potential K).groupPartners i,
          groupCharge (P.potential K) i (velOf (Yp ι' p)) (gradOf (Yp ι' p)))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.mul_sum, ← Finset.mul_sum, div_eq_inv_mul]
    ring
  rw [hlhs]
  have h1 := mul_le_mul_of_nonneg_left (le_trans hb hsum) hp1
  have h2 := mul_le_mul_of_nonneg_left hre hp1
  nlinarith

theorem groupStage_of (hCross : ModelCrossBoundStatement) (hCoup : CouplingModelReStatement)
    (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) (hT : TrueFieldRegular D) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) :
    GroupStage D R P := by
  intro K q v G H g κ F Pg ht ζ η
  have hreg := (hT.1 K q v G H g κ F Pg ht).1
  generalize cellState D.mesh K (R.layouts K) v G H Pg κ ζ η = x
  have hms : MeasurableSet (D.mesh.box K).rect := measurableSet_Icc.prod measurableSet_Icc
  have hpos : ∀ᵐ p ∂(volume.restrict (D.mesh.box K).rect), 0 ≤ p.1 :=
    ae_restrict_of_forall_mem hms (rect_fst_nonneg D hP.mesh_valid K)
  have hXc : ∀ ι j, Continuous (fun p => upperProfiles D R K (P.potential K) x ι p j) :=
    fun ι j => upperProfiles_continuous D R K (P.potential K) x ι j
  have hXi : ∀ i ι, Integrable (fun p => p.1 * groupCharge (P.potential K) i
      (velOf (upperProfiles D R K (P.potential K) x ι p)) (gradOf (upperProfiles D R K (P.potential K) x ι p)))
      (volume.restrict (D.mesh.box K).rect) := by
    intro i ι
    refine ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) (Continuous.continuousOn ?_)
    exact continuous_fst.mul ((groupCharge_continuous _ _).comp (continuous_pi (fun j => hXc ι j)))
  have hYi : ∀ i ι, Integrable (fun p => p.1 * groupCharge (P.potential K) i
      (velOf (trueProfiles D v G ι p)) (gradOf (trueProfiles D v G ι p))) (volume.restrict (D.mesh.box K).rect) := by
    intro i ι
    obtain ⟨h1, h2, h3⟩ := groupCoeffs D R A P hP K i
    unfold groupCharge
    exact chargeY_integrable _ (trueProfiles D v G ι) _ _ _ h1 h2 h3 (hreg ι).1 (hreg ι).2 hpos
  have hf : ∀ ι ∈ D.mesh.resolved K, ∀ ι' ∈ deactPartners D R K (P.potential K),
      Integrable (fun p => p.1 * (sesq12 ((P.potential K).couplingModel (ι - ι') p)
        (upperProfiles D R K (P.potential K) x ι p) (trueProfiles D v G ι' p)).re)
        (volume.restrict (D.mesh.box K).rect) := by
    intro ι hι ι' hι'
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hι').2
    exact modelIntegrand_integrable hCross hCoup D R A P hP K (upperProfiles D R K (P.potential K) x)
      (trueProfiles D v G) hXc (fun ι => (hreg ι).1) hXi hYi ι hι ι' h1 h2
  have e2 : modelPair D K (P.potential K).couplingModel (D.mesh.resolved K) (deactPartners D R K (P.potential K))
        (upperProfiles D R K (P.potential K) x) (trueProfiles D v G)
      = ∫ p in (D.mesh.box K).rect, ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ deactPartners D R K (P.potential K),
          p.1 * (sesq12 ((P.potential K).couplingModel (ι - ι') p) (upperProfiles D R K (P.potential K) x ι p)
            (trueProfiles D v G ι' p)).re := by
    unfold modelPair
    rw [integral_finsetSum _ (fun ι hι => integrable_finsetSum _ (fun ι' hι' => hf ι hι ι' hι'))]
    refine Finset.sum_congr rfl (fun ι hι => ?_)
    rw [integral_finsetSum _ (fun ι' hι' => hf ι hι ι' hι')]
  have hLi : ∀ i, Integrable (fun p => (P.potential K).groupBalance i
        * ∑ ι ∈ D.mesh.resolved K ∩ (P.potential K).groupModes i,
        p.1 * groupCharge (P.potential K) i (velOf (upperProfiles D R K (P.potential K) x ι p))
          (gradOf (upperProfiles D R K (P.potential K) x ι p))
      + (∑ ι ∈ (P.potential K).groupPartners i, p.1 * groupCharge (P.potential K) i (velOf (trueProfiles D v G ι p))
          (gradOf (trueProfiles D v G ι p))) / (P.potential K).groupBalance i)
      (volume.restrict (D.mesh.box K).rect) := fun i =>
    ((integrable_finsetSum _ (fun ι _ => hXi i ι)).const_mul _).add
      ((integrable_finsetSum _ (fun ι _ => hYi i ι)).div_const _)
  have e3 : (∫ p in (D.mesh.box K).rect, -(∑ i, ((P.potential K).groupBalance i
        * ∑ ι ∈ D.mesh.resolved K ∩ (P.potential K).groupModes i,
        p.1 * groupCharge (P.potential K) i (velOf (upperProfiles D R K (P.potential K) x ι p))
          (gradOf (upperProfiles D R K (P.potential K) x ι p))
      + (∑ ι ∈ (P.potential K).groupPartners i, p.1 * groupCharge (P.potential K) i (velOf (trueProfiles D v G ι p))
          (gradOf (trueProfiles D v G ι p))) / (P.potential K).groupBalance i)))
      = -groupOwnAmount D R K (P.potential K) (upperProfiles D R K (P.potential K) x)
        - groupPartnerAmount D R K (P.potential K) (trueProfiles D v G) := by
    rw [integral_neg, integral_finsetSum _ (fun i _ => hLi i)]
    have hi : ∀ i, (∫ p in (D.mesh.box K).rect, ((P.potential K).groupBalance i
        * ∑ ι ∈ D.mesh.resolved K ∩ (P.potential K).groupModes i,
        p.1 * groupCharge (P.potential K) i (velOf (upperProfiles D R K (P.potential K) x ι p))
          (gradOf (upperProfiles D R K (P.potential K) x ι p))
      + (∑ ι ∈ (P.potential K).groupPartners i, p.1 * groupCharge (P.potential K) i (velOf (trueProfiles D v G ι p))
          (gradOf (trueProfiles D v G ι p))) / (P.potential K).groupBalance i))
        = (P.potential K).groupBalance i * formAmount D K (D.mesh.resolved K ∩ (P.potential K).groupModes i)
            (groupCharge (P.potential K) i) (upperProfiles D R K (P.potential K) x)
          + formAmount D K ((P.potential K).groupPartners i) (groupCharge (P.potential K) i) (trueProfiles D v G)
            / (P.potential K).groupBalance i := by
      intro i
      rw [integral_add ((integrable_finsetSum _ (fun ι _ => hXi i ι)).const_mul _)
        ((integrable_finsetSum _ (fun ι _ => hYi i ι)).div_const _), integral_const_mul, integral_div,
        integral_finsetSum _ (fun ι _ => hXi i ι), integral_finsetSum _ (fun ι _ => hYi i ι)]
      rfl
    rw [Finset.sum_congr rfl (fun i _ => hi i)]
    unfold groupOwnAmount groupPartnerAmount
    rw [Finset.sum_add_distrib]
    ring
  rw [e2, ← e3, ← integral_const_mul]
  refine setIntegral_mono_on (integrable_finsetSum _ (fun i _ => hLi i)).neg
    ((integrable_finsetSum _ (fun ι hι => integrable_finsetSum _ (fun ι' hι' => hf ι hι ι' hι'))).const_mul 2) hms
    (fun p hp => ?_)
  exact groupPointwise hCross hCoup D R A P hP K (upperProfiles D R K (P.potential K) x) (trueProfiles D v G) p hp

theorem groupStageHolds_of (hCross : ModelCrossBoundStatement) (hCoup : CouplingModelReStatement) :
    GroupStageHolds := by
  intro k C nE nM D R A P states hstates _ hT hP
  exact groupStage_of hCross hCoup D R A P hT hP

end Internal

theorem groupStageHolds : GroupStageHolds :=
  Internal.groupStageHolds_of
    (fun D R A P _ hP K B hc hs hd X Y p hp => Internal.groupCrossBound D R A P hP K B hc hs hd X Y p hp)
    (fun D R A P _ hP K α p hp U U' => Internal.sesq_couplingModel D R A P hP K α p hp U U')

end Assembly

end CertCell

end Breakdown
