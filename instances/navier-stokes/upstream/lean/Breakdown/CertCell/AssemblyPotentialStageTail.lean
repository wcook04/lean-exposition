import Breakdown.CertCell.AssemblyPotentialStageLeaf
import Breakdown.FracCell.LowVelocityExpansion

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

namespace Internal

theorem lineWeight_bound (B : CellBox) (hB : IsCellBox B) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ p ∈ B.rect, 0 ≤ B.lineWeight p.1 ∧ B.lineWeight p.1 ≤ κ * p.1 := by
  by_cases h : B.r₁ = 0
  · refine ⟨1, zero_le_one, fun p hp => ?_⟩
    simp only [CellBox.lineWeight, if_pos h]
    exact ⟨fst_nonneg_of_mem B hB hp, by linarith⟩
  · have hr : 0 < B.r₁ := lt_of_le_of_ne hB.r_order.1 (Ne.symm h)
    refine ⟨B.r₁⁻¹, inv_nonneg.2 hr.le, fun p hp => ?_⟩
    simp only [CellBox.lineWeight, if_neg h]
    have hp1 : B.r₁ ≤ p.1 := by
      simp only [CellBox.rect, Set.mem_prod, Set.mem_Icc] at hp
      exact hp.1.1
    refine ⟨zero_le_one, ?_⟩
    rw [← div_eq_inv_mul, le_div_iff₀ hr]
    linarith

theorem continuous_lineWeight' (B : CellBox) : Continuous B.lineWeight := by
  unfold CellBox.lineWeight
  split_ifs
  · exact continuous_id
  · exact continuous_const

def ScalarReg (B : CellBox) (F : ℝ × ℝ → ℂ) : Prop :=
  AEStronglyMeasurable F (volume.restrict B.rect) ∧ IntegrableOn (fun p => p.1 * ‖F p‖ ^ 2) B.rect

theorem rect_compact (B : CellBox) : IsCompact B.rect := isCompact_Icc.prod isCompact_Icc

theorem scalarReg_lw_sq {B : CellBox} (hB : IsCellBox B) {F : ℝ × ℝ → ℂ} (hF : ScalarReg B F) :
    IntegrableOn (fun p => B.lineWeight p.1 * ‖F p‖ ^ 2) B.rect := by
  obtain ⟨κ, hκ, hw⟩ := lineWeight_bound B hB
  have hm : AEStronglyMeasurable (fun p => B.lineWeight p.1 * ‖F p‖ ^ 2) (volume.restrict B.rect) :=
    ((continuous_lineWeight' B).comp continuous_fst).aestronglyMeasurable.mul (hF.1.norm.pow 2)
  refine (hF.2.const_mul κ).mono' hm ((ae_restrict_iff' (rect_measurable B)).2 (Filter.Eventually.of_forall fun p hp => ?_))
  obtain ⟨h0, h1⟩ := hw p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (sq_nonneg _))]
  have := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖F p‖)
  linarith

theorem scalarReg_lw_mul {B : CellBox} (hB : IsCellBox B) {F : ℝ × ℝ → ℂ} (hF : ScalarReg B F) :
    IntegrableOn (fun p => (B.lineWeight p.1 : ℂ) * F p) B.rect := by
  have h1 : IntegrableOn (fun p => B.lineWeight p.1) B.rect :=
    ((continuous_lineWeight' B).comp continuous_fst).continuousOn.integrableOn_compact (rect_compact B)
  have h2 := scalarReg_lw_sq hB hF
  obtain ⟨κ, hκ, hw⟩ := lineWeight_bound B hB
  have hm : AEStronglyMeasurable (fun p => (B.lineWeight p.1 : ℂ) * F p) (volume.restrict B.rect) :=
    (Complex.continuous_ofReal.comp ((continuous_lineWeight' B).comp continuous_fst)).aestronglyMeasurable.mul hF.1
  refine (h1.add h2).mono' hm ((ae_restrict_iff' (rect_measurable B)).2 (Filter.Eventually.of_forall fun p hp => ?_))
  obtain ⟨h0, -⟩ := hw p hp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  have : ‖F p‖ ≤ 1 + ‖F p‖ ^ 2 := by nlinarith [sq_nonneg (‖F p‖ - 1), norm_nonneg (F p)]
  have := mul_le_mul_of_nonneg_left this h0
  simp only [Pi.add_apply]
  linarith

theorem scalarReg_sub {B : CellBox} (hB : IsCellBox B) {F G : ℝ × ℝ → ℂ} (hF : ScalarReg B F) (hG : ScalarReg B G) :
    ScalarReg B (fun p => F p - G p) := by
  refine ⟨hF.1.sub hG.1, ?_⟩
  have hm : AEStronglyMeasurable (fun p => p.1 * ‖F p - G p‖ ^ 2) (volume.restrict B.rect) :=
    continuous_fst.aestronglyMeasurable.mul ((hF.1.sub hG.1).norm.pow 2)
  refine ((hF.2.const_mul 2).add (hG.2.const_mul 2)).mono' hm
    ((ae_restrict_iff' (rect_measurable B)).2 (Filter.Eventually.of_forall fun p hp => ?_))
  have h0 := fst_nonneg_of_mem B hB hp
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (sq_nonneg _))]
  have := mul_le_mul_of_nonneg_left (norm_sub_sq_le (F p) (G p)) h0
  simp only [Pi.add_apply]
  linarith

theorem scalarReg_of_continuous {B : CellBox} {F : ℝ × ℝ → ℂ} (hF : Continuous F) : ScalarReg B F := by
  refine ⟨hF.aestronglyMeasurable, ?_⟩
  have : Continuous (fun p : ℝ × ℝ => p.1 * ‖F p‖ ^ 2) := by fun_prop
  exact this.continuousOn.integrableOn_compact (rect_compact B)

theorem proj_expand' {B : CellBox} (hB : IsCellBox B) {Bs : CellBases} (hBs : IsCellBases B Bs)
    {F : ℝ × ℝ → ℂ} (hF : ScalarReg B F) (Q : ℕ) (p : ℝ × ℝ) :
    B.proj Q Q F p = ∑ i ∈ Finset.range (Q + 1), ∑ l ∈ Finset.range (Q + 1),
      Bs.coef B F i l * CellCert.CellEnergy.TopFormInternal.basisC Bs i l p :=
  CellCert.CellEnergy.LowVelocityExpansion.Internal.proj_expand B hBs (scalarReg_lw_mul hB hF) Q Q p

theorem proj_continuous {B : CellBox} (hB : IsCellBox B) {Bs : CellBases} (hBs : IsCellBases B Bs)
    {F : ℝ × ℝ → ℂ} (hF : ScalarReg B F) (Q : ℕ) : Continuous (B.proj Q Q F) := by
  have e : B.proj Q Q F = fun p => ∑ i ∈ Finset.range (Q + 1), ∑ l ∈ Finset.range (Q + 1),
      Bs.coef B F i l * CellCert.CellEnergy.TopFormInternal.basisC Bs i l p :=
    funext (proj_expand' hB hBs hF Q)
  rw [e]
  unfold CellCert.CellEnergy.TopFormInternal.basisC CellCert.CellEnergy.basisFn CellBases.radialPoly
    CellBases.heightPoly
  fun_prop

theorem coef_sub {B : CellBox} (hB : IsCellBox B) (Bs : CellBases) {F G : ℝ × ℝ → ℂ} (hF : ScalarReg B F)
    (hG : ScalarReg B G) (i l : ℕ) :
    Bs.coef B (fun p => F p - G p) i l = Bs.coef B F i l - Bs.coef B G i l := by
  unfold CellBases.coef
  have hc : ContinuousOn (fun p : ℝ × ℝ => ((Bs.radialPoly i p.1 * Bs.heightPoly l p.2 : ℝ) : ℂ)) B.rect := by
    unfold CellBases.radialPoly CellBases.heightPoly
    fun_prop
  have i1 := (scalarReg_lw_mul hB hF).mul_continuousOn hc (rect_compact B)
  have i2 := (scalarReg_lw_mul hB hG).mul_continuousOn hc (rect_compact B)
  rw [← integral_sub i1 i2]
  congr 1
  funext p
  ring

theorem proj_sub {B : CellBox} (hB : IsCellBox B) {Bs : CellBases} (hBs : IsCellBases B Bs)
    {F G : ℝ × ℝ → ℂ} (hF : ScalarReg B F) (hG : ScalarReg B G) (Q : ℕ) :
    B.proj Q Q (fun p => F p - G p) = fun p => B.proj Q Q F p - B.proj Q Q G p := by
  funext p
  rw [proj_expand' hB hBs (scalarReg_sub hB hF hG), proj_expand' hB hBs hF, proj_expand' hB hBs hG,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [coef_sub hB Bs hF hG]
  ring

theorem tail_sq_integrable {B : CellBox} (hB : IsCellBox B) {Bs : CellBases} (hBs : IsCellBases B Bs)
    {F : ℝ × ℝ → ℂ} (hF : ScalarReg B F) (Q : ℕ) :
    IntegrableOn (fun p => B.lineWeight p.1 * ‖F p - B.proj Q Q F p‖ ^ 2) B.rect :=
  scalarReg_lw_sq hB (scalarReg_sub hB hF (scalarReg_of_continuous (proj_continuous hB hBs hF Q)))

end Internal

namespace Internal

theorem scalarReg_component {B : CellBox} (hB : IsCellBox B) {U : ℝ × ℝ → Fin 12 → ℂ} (hU : ProfileReg B.rect U)
    (j : Fin 12) : ScalarReg B (fun p => U p j) := by
  refine ⟨hU.1 j, ?_⟩
  have hm : AEStronglyMeasurable (fun p => p.1 * ‖U p j‖ ^ 2) (volume.restrict B.rect) :=
    continuous_fst.aestronglyMeasurable.mul ((hU.1 j).norm.pow 2)
  refine hU.2.mono' hm ((ae_restrict_iff' (rect_measurable B)).2 (Filter.Eventually.of_forall fun p hp => ?_))
  have h0 := fst_nonneg_of_mem B hB hp
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (sq_nonneg _))]
  have hs : ‖U p j‖ ^ 2 ≤ ∑ i, ‖U p i‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖U p i‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  exact mul_le_mul_of_nonneg_left hs h0

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

theorem tail_absorb_mode (hM : IsCellMesh D.mesh) (hcc : CellCalculusConditions D R) (K : Fin D.mesh.count)
    (ι : ℤ × ℤ) (hι : ι ∈ D.mesh.resolved K) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (hP : ProfileReg (D.mesh.box K).rect (fun p => bandProfile D ι v G p)) :
    ∫ p in (D.mesh.box K).rect, (D.mesh.box K).lineWeight p.1 *
        ((R.leaves K).curlAbsorb ι * curlSq (strainOfVec (tailProfiles D R K v G ι p))
          + (R.leaves K).strainAbsorb ι * sumSq (strainOfVec (tailProfiles D R K v G ι p))
          + (R.leaves K).velocityAbsorb ι * vecSq (velOf (tailProfiles D R K v G ι p)))
      = (R.leaves K).curlAbsorb ι * tailCurlSq D R K ι G + (R.leaves K).strainAbsorb ι * tailStrainSq D R K ι G
          + (R.leaves K).velocityAbsorb ι * tailVelSq D R K ι v := by
  have hB := hM.box_valid K
  have hsm := rect_measurable (D.mesh.box K)
  obtain ⟨_, _, _, _, hL⟩ := (hcc.layouts_valid K).layout_valid ι hι
  have hBs := hL.bases_valid
  set Q := ((R.layouts K).layout ι).degCoef with hQ
  set B := D.mesh.box K with hBdef
  have hg : ∀ a b : Fin 3, ScalarReg B (fun p => gradAt D.azimuthOrder ι G a b p) := by
    intro a b
    have h := scalarReg_component hB hP ⟨3 * a.val + b.val, by omega⟩
    have e : (fun p => gradAt D.azimuthOrder ι G a b p) = fun p => bandProfile D ι v G p ⟨3 * a.val + b.val, by omega⟩ :=
      funext fun p => gradAt_eq_profile D ι v G a b p
    rw [e]
    exact h
  have hw : ∀ a : Fin 3, ScalarReg B (fun p => velAt D.azimuthOrder ι v a p) := by
    intro a
    have h := scalarReg_component hB hP ⟨9 + a.val, by omega⟩
    have e : (fun p => velAt D.azimuthOrder ι v a p) = fun p => bandProfile D ι v G p ⟨9 + a.val, by omega⟩ :=
      funext fun p => velAt_eq_profile D ι v G a p
    rw [e]
    exact h
  have hcurlfun : ∀ i : Fin 3, ∃ a b a' b' : Fin 3, (fun p => curlComp (gradArray D.azimuthOrder ι G p) i)
      = (fun p => gradAt D.azimuthOrder ι G a b p - gradAt D.azimuthOrder ι G a' b' p) ∧
      ∀ s : Fin 3 → Fin 3 → ℂ, curlComp s i = s a b - s a' b' := by
    intro i
    fin_cases i
    · exact ⟨2, 1, 1, 2, funext fun p => (curlComp_apply _).1, fun s => (curlComp_apply s).1⟩
    · exact ⟨0, 2, 2, 0, funext fun p => (curlComp_apply _).2.1, fun s => (curlComp_apply s).2.1⟩
    · exact ⟨1, 0, 0, 1, funext fun p => (curlComp_apply _).2.2, fun s => (curlComp_apply s).2.2⟩
  have hc : ∀ i : Fin 3, ScalarReg B (fun p => curlComp (gradArray D.azimuthOrder ι G p) i) := by
    intro i
    obtain ⟨a, b, a', b', e, -⟩ := hcurlfun i
    rw [e]
    exact scalarReg_sub hB (hg a b) (hg a' b')
  have hcurl : ∀ (i : Fin 3) (p : ℝ × ℝ),
      curlComp (fun a b => gradAt D.azimuthOrder ι G a b p - B.proj Q Q (fun p' => gradAt D.azimuthOrder ι G a b p') p) i
        = curlComp (gradArray D.azimuthOrder ι G p) i
          - B.proj Q Q (fun p' => curlComp (gradArray D.azimuthOrder ι G p') i) p := by
    intro i p
    obtain ⟨a, b, a', b', e, hs⟩ := hcurlfun i
    rw [e, proj_sub hB hBs (hg a b) (hg a' b'), hs, hs]
    simp only [gradArray]
    ring
  have htl : ∀ p, tailProfiles D R K v G ι p = tailProfile D R K ι v G p := by
    intro p
    unfold tailProfiles restrictTo
    rw [if_pos (Finset.mem_coe.2 hι)]
  have iC : ∀ i : Fin 3, Integrable (fun p => B.lineWeight p.1 *
      ‖curlComp (gradArray D.azimuthOrder ι G p) i - B.proj Q Q (fun p' => curlComp (gradArray D.azimuthOrder ι G p') i) p‖ ^ 2)
      (volume.restrict B.rect) := fun i => tail_sq_integrable hB hBs (hc i) Q
  have iS : ∀ a b : Fin 3, Integrable (fun p => B.lineWeight p.1 *
      ‖gradAt D.azimuthOrder ι G a b p - B.proj Q Q (fun p' => gradAt D.azimuthOrder ι G a b p') p‖ ^ 2)
      (volume.restrict B.rect) := fun a b => tail_sq_integrable hB hBs (hg a b) Q
  have iV : ∀ a : Fin 3, Integrable (fun p => B.lineWeight p.1 *
      ‖velAt D.azimuthOrder ι v a p - B.proj (Q - 1) (Q - 1) (fun p' => velAt D.azimuthOrder ι v a p') p‖ ^ 2)
      (volume.restrict B.rect) := fun a => tail_sq_integrable hB hBs (hw a) (Q - 1)
  have sC := integral_finsetSum (μ := volume.restrict B.rect) Finset.univ (fun i _ => iC i)
  have sV := integral_finsetSum (μ := volume.restrict B.rect) Finset.univ (fun a _ => iV a)
  have sS : ∫ p in B.rect, ∑ a : Fin 3, ∑ b : Fin 3, B.lineWeight p.1 *
        ‖gradAt D.azimuthOrder ι G a b p - B.proj Q Q (fun p' => gradAt D.azimuthOrder ι G a b p') p‖ ^ 2
      = ∑ a : Fin 3, ∑ b : Fin 3, ∫ p in B.rect, B.lineWeight p.1 *
        ‖gradAt D.azimuthOrder ι G a b p - B.proj Q Q (fun p' => gradAt D.azimuthOrder ι G a b p') p‖ ^ 2 := by
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => iS a b))]
    exact Finset.sum_congr rfl (fun a _ => integral_finsetSum _ (fun b _ => iS a b))
  have iCs := integrable_finsetSum (μ := volume.restrict B.rect) Finset.univ (fun i _ => iC i)
  have iVs := integrable_finsetSum (μ := volume.restrict B.rect) Finset.univ (fun a _ => iV a)
  have iSs : Integrable (fun p => ∑ a : Fin 3, ∑ b : Fin 3, B.lineWeight p.1 *
      ‖gradAt D.azimuthOrder ι G a b p - B.proj Q Q (fun p' => gradAt D.azimuthOrder ι G a b p') p‖ ^ 2)
      (volume.restrict B.rect) := integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => iS a b))
  calc ∫ p in B.rect, B.lineWeight p.1 *
        ((R.leaves K).curlAbsorb ι * curlSq (strainOfVec (tailProfiles D R K v G ι p))
          + (R.leaves K).strainAbsorb ι * sumSq (strainOfVec (tailProfiles D R K v G ι p))
          + (R.leaves K).velocityAbsorb ι * vecSq (velOf (tailProfiles D R K v G ι p)))
      = ∫ p in B.rect, ((R.leaves K).curlAbsorb ι * ∑ i : Fin 3, B.lineWeight p.1 *
            ‖curlComp (gradArray D.azimuthOrder ι G p) i
              - B.proj Q Q (fun p' => curlComp (gradArray D.azimuthOrder ι G p') i) p‖ ^ 2
          + (R.leaves K).strainAbsorb ι * ∑ a : Fin 3, ∑ b : Fin 3, B.lineWeight p.1 *
            ‖gradAt D.azimuthOrder ι G a b p - B.proj Q Q (fun p' => gradAt D.azimuthOrder ι G a b p') p‖ ^ 2
          + (R.leaves K).velocityAbsorb ι * ∑ a : Fin 3, B.lineWeight p.1 *
            ‖velAt D.azimuthOrder ι v a p - B.proj (Q - 1) (Q - 1) (fun p' => velAt D.azimuthOrder ι v a p') p‖ ^ 2) := by
        refine setIntegral_congr_fun hsm (fun p _ => ?_)
        simp only [htl, tailProfile, strainOfVec_pairVec, velOf_pairVec]
        simp only [← hQ, ← hBdef]
        simp only [curlSq, sumSq, vecSq, hcurl]
        simp only [Fin.sum_univ_three]
        ring
    _ = (R.leaves K).curlAbsorb ι * tailCurlSq D R K ι G + (R.leaves K).strainAbsorb ι * tailStrainSq D R K ι G
          + (R.leaves K).velocityAbsorb ι * tailVelSq D R K ι v := by
        rw [integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul, sC, sS, sV]
        all_goals first
          | rfl
          | exact iCs.const_mul _
          | exact iSs.const_mul _
          | exact iVs.const_mul _
          | exact (iCs.const_mul _).add (iSs.const_mul _)

end Internal

open _root_.Breakdown.CertCell.Assembly.Internal in
theorem tailAbsorbIdentity_holds : TailAbsorbIdentityHolds := by
  intro k C nE nM D R hM hcc htf K q v G H g κ F Pg ht
  have hprof := (htf.1 K q v G H g κ F Pg ht).1
  unfold alAmount
  refine Finset.sum_congr rfl (fun ι hι => ?_)
  exact tail_absorb_mode D R hM hcc K ι hι v G (hprof ι)

theorem splitIdentities_holds : SplitIdentitiesHolds :=
  splitIdentities_of_tail tailAbsorbIdentity_holds

end Assembly

end CertCell

end Breakdown
