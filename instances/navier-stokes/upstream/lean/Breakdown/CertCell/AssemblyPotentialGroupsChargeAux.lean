import Breakdown.CertCell.AssemblyPotentialParts

open MeasureTheory Matrix
open scoped ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

namespace ChargeAux

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

variable {k : ℕ} {C : Type} {nE nM : ℕ}

theorem splitCharge_nonneg {σc cs cv : ℝ} (hσ : 0 ≤ σc) (hs : 0 ≤ cs) (hv : 0 ≤ cv) (a : Fin 3 → ℂ)
    (g : Fin 3 × Fin 3 → ℂ) : 0 ≤ splitCharge σc cs cv a g := by
  unfold splitCharge
  have h1 : 0 ≤ cnormSq (curlOfGrad g) := Finset.sum_nonneg (fun _ _ => by positivity)
  have h2 : 0 ≤ cnormSq g := Finset.sum_nonneg (fun _ _ => by positivity)
  have h3 : 0 ≤ cnormSq a := Finset.sum_nonneg (fun _ _ => by positivity)
  have := mul_nonneg hσ h1
  have := mul_nonneg hs h2
  have := mul_nonneg hv h3
  linarith

theorem kappa_nonneg {κ : ℝ} (hκ : κ = Real.sqrt (7 / 2) ∨ κ = Real.sqrt (9 / 2)) : 0 ≤ κ := by
  rcases hκ with rfl | rfl <;> exact Real.sqrt_nonneg _

theorem rect_fst_nonneg (D : CellLayerData k C nE nM) (hM : IsCellMesh D.mesh) (K : Fin D.mesh.count)
    (p : ℝ × ℝ) (hp : p ∈ (D.mesh.box K).rect) : 0 ≤ p.1 :=
  le_trans (hM.box_valid K).r_order.1 hp.1.1

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

theorem profile_aemeasurable (μ : Measure (ℝ × ℝ)) (Y : ℝ × ℝ → Fin 12 → ℂ)
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
      (profile_aemeasurable μ Y hY))).aestronglyMeasurable
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

theorem high_nonneg (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count) :
    0 ≤ (P.potential K).highStrain ∧ 0 ≤ (P.potential K).highGrad := by
  obtain ⟨-, -, -, -, -, -, h1, h2⟩ := (hP.cell_conditions.model_split K).errors_nonneg
  exact ⟨le_trans h1 (hP.high_ge K).1, le_trans h2 (hP.high_ge K).2⟩

theorem longFactor_pos {V : Type} (P : PotentialData V) (h : 0 < P.longBalance) (ι : ℤ × ℤ) :
    0 < longFactor P ι := by
  unfold longFactor
  split_ifs
  · exact h
  · positivity

theorem longCoeffs (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count) :
    0 ≤ (P.potential K).longStrain ∧
      0 ≤ 3 / (2 * Real.sqrt 2) * (P.potential K).longGrad * (P.potential K).epsLength ∧
      0 ≤ 3 / (2 * Real.sqrt 2) * (P.potential K).longGrad / (P.potential K).length := by
  obtain ⟨h1, h2, -⟩ := hP.long_pos K
  have hℓ := hP.length_pos K
  have hL := hP.eps_length_pos K
  exact ⟨h1, by positivity, by positivity⟩

end ChargeAux

end Internal

end Assembly

end CertCell

end Breakdown
