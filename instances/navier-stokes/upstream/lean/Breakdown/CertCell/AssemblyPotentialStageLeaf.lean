import Breakdown.CertCell.AssemblyPotentialStageCharge

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

namespace Internal

theorem pairVec_add (s s' : Fin 3 → Fin 3 → ℂ) (v v' : Fin 3 → ℂ) :
    pairVec (s + s') (v + v') = pairVec s v + pairVec s' v' := by
  funext j
  simp only [pairVec, Pi.add_apply]
  split_ifs <;> rfl

theorem sesq12_add_left (M : Matrix (Fin 12) (Fin 12) ℂ) (U U' V : Fin 12 → ℂ) :
    sesq12 M (U + U') V = sesq12 M U V + sesq12 M U' V := by
  unfold sesq12
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem sesq12_add_right (M : Matrix (Fin 12) (Fin 12) ℂ) (U V V' : Fin 12 → ℂ) :
    sesq12 M U (V + V') = sesq12 M U V + sesq12 M U V' := by
  unfold sesq12
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem sesq12_swap (M : Matrix (Fin 12) (Fin 12) ℂ) (hM : M.IsHermitian) (U V : Fin 12 → ℂ) :
    sesq12 M V U = (starRingEnd ℂ) (sesq12 M U V) := by
  unfold sesq12
  simp only [map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  have h := hM.apply i j
  rw [← h]
  simp only [RCLike.star_def, Complex.conj_conj]
  ring

theorem sesq12_re_swap (M : Matrix (Fin 12) (Fin 12) ℂ) (hM : M.IsHermitian) (U V : Fin 12 → ℂ) :
    (sesq12 M V U).re = (sesq12 M U V).re := by
  rw [sesq12_swap M hM U V, Complex.conj_re]

theorem leaf_point (M : Matrix (Fin 12) (Fin 12) ℂ) (hM : M.IsHermitian) (u b t : Fin 12 → ℂ) :
    (sesq12 M (u + b + t) (u + b + t)).re - (sesq12 M (u + b) (u + b)).re
      = 2 * (sesq12 M u t).re + (sesq12 M (b + t) (b + t)).re - (sesq12 M b b).re := by
  simp only [sesq12_add_left, sesq12_add_right, Complex.add_re]
  have := sesq12_re_swap M hM u t
  linarith

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

theorem lowProfile_add (K : Fin D.mesh.count) (ι : D.mesh.resolved K) (x y : CellVars D R K → ℂ) (p : ℝ × ℝ) :
    lowProfile D R K ι (x + y) p = lowProfile D R K ι x p + lowProfile D R K ι y p := by
  unfold lowProfile
  rw [← pairVec_add]
  congr 1
  · funext a b
    simp only [lowGrad, lowStrainOf, restrictData, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  · funext a
    simp only [lowVel, lowVelocityOf, restrictData, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem lowAt_add (K : Fin D.mesh.count) (x y : CellVars D R K → ℂ) (ι : ℤ × ℤ) (p : ℝ × ℝ) :
    lowAt D R K (x + y) ι p = lowAt D R K x ι p + lowAt D R K y ι p := by
  unfold lowAt
  split_ifs with h
  · exact lowProfile_add D R K ⟨ι, h⟩ x y p
  · simp

theorem lowAt_split (K : Fin D.mesh.count) (P : PotentialData (CellVars D R K)) (x : CellVars D R K → ℂ)
    (ι : ℤ × ℤ) (p : ℝ × ℝ) :
    lowAt D R K x ι p = lowAt D R K (upperPart D R K P x) ι p + lowAt D R K (bandPart D R K P x) ι p := by
  rw [← lowAt_add]
  congr 1
  unfold upperPart bandPart
  abel

theorem continuous_lowProfile (K : Fin D.mesh.count) (ι : D.mesh.resolved K) (x : CellVars D R K → ℂ) :
    Continuous (fun p => lowProfile D R K ι x p) := by
  refine continuous_pi (fun j => ?_)
  unfold lowProfile pairVec
  split_ifs
  · unfold lowGrad lowStrainOf CellCert.CellEnergy.basisFn CellBases.radialPoly CellBases.heightPoly
    fun_prop
  · unfold lowVel lowVelocityOf CellCert.CellEnergy.basisFn CellBases.radialPoly CellBases.heightPoly
    fun_prop

theorem continuous_lowAt (K : Fin D.mesh.count) (x : CellVars D R K → ℂ) (ι : ℤ × ℤ) :
    Continuous (fun p => lowAt D R K x ι p) := by
  unfold lowAt
  split_ifs with h
  · exact continuous_lowProfile D R K ⟨ι, h⟩ x
  · exact continuous_const

end Internal

namespace Internal

def ProfileReg (s : Set (ℝ × ℝ)) (U : ℝ × ℝ → Fin 12 → ℂ) : Prop :=
  (∀ j, AEStronglyMeasurable (fun p => U p j) (volume.restrict s)) ∧
    IntegrableOn (fun p => p.1 * ∑ j, ‖U p j‖ ^ 2) s

theorem profileReg_of_continuous {s : Set (ℝ × ℝ)} (hs : IsCompact s) {U : ℝ × ℝ → Fin 12 → ℂ}
    (hU : Continuous U) : ProfileReg s U := by
  refine ⟨fun j => ((continuous_apply j).comp hU).aestronglyMeasurable, ?_⟩
  have hc : Continuous (fun p : ℝ × ℝ => p.1 * ∑ j, ‖U p j‖ ^ 2) := by
    have : ∀ j, Continuous (fun p => U p j) := fun j => (continuous_apply j).comp hU
    fun_prop
  exact hc.continuousOn.integrableOn_compact hs

theorem profileReg_sub {s : Set (ℝ × ℝ)} (hsm : MeasurableSet s) (hpos : ∀ p ∈ s, 0 ≤ p.1)
    {U V : ℝ × ℝ → Fin 12 → ℂ} (hU : ProfileReg s U) (hV : ProfileReg s V) :
    ProfileReg s (fun p => U p - V p) := by
  refine ⟨fun j => (hU.1 j).sub (hV.1 j), ?_⟩
  have hg : IntegrableOn (fun p => 2 * (p.1 * ∑ j, ‖U p j‖ ^ 2) + 2 * (p.1 * ∑ j, ‖V p j‖ ^ 2)) s :=
    (hU.2.const_mul 2).add (hV.2.const_mul 2)
  have hm : AEStronglyMeasurable (fun p => p.1 * ∑ j, ‖(U p - V p) j‖ ^ 2) (volume.restrict s) := by
    refine AEMeasurable.aestronglyMeasurable ?_
    refine measurable_fst.aemeasurable.mul (Finset.aemeasurable_fun_sum _ (fun j _ => ?_))
    exact (((hU.1 j).sub (hV.1 j)).aemeasurable.norm).pow_const 2
  refine hg.mono' hm ((ae_restrict_iff' hsm).2 (Filter.Eventually.of_forall fun p hp => ?_))
  have h0 := hpos p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (by positivity))]
  have hs : ∑ j, ‖(U p - V p) j‖ ^ 2 ≤ 2 * ∑ j, ‖U p j‖ ^ 2 + 2 * ∑ j, ‖V p j‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => by simpa [Pi.sub_apply] using norm_sub_sq_le (U p j) (V p j))
  nlinarith

theorem sesq12_norm_le (M : Matrix (Fin 12) (Fin 12) ℂ) (U V : Fin 12 → ℂ) {c : ℝ} (hc : ∀ i j, ‖M i j‖ ≤ c) :
    ‖sesq12 M U V‖ ≤ 144 * (|c| * (∑ j, ‖U j‖ ^ 2 + ∑ j, ‖V j‖ ^ 2)) := by
  unfold sesq12
  calc ‖∑ i, ∑ j, (starRingEnd ℂ) (U i) * M i j * V j‖
      ≤ ∑ i, ∑ j, ‖(starRingEnd ℂ) (U i) * M i j * V j‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : Fin 12, ∑ _j : Fin 12, |c| * (∑ j, ‖U j‖ ^ 2 + ∑ j, ‖V j‖ ^ 2) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_conj]
        have hu : ‖U i‖ ^ 2 ≤ ∑ j, ‖U j‖ ^ 2 :=
          Finset.single_le_sum (f := fun j => ‖U j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        have hv : ‖V j‖ ^ 2 ≤ ∑ j, ‖V j‖ ^ 2 :=
          Finset.single_le_sum (f := fun j => ‖V j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ j)
        have hm : ‖M i j‖ ≤ |c| := (hc i j).trans (le_abs_self c)
        have h1 : ‖U i‖ * ‖V j‖ ≤ ∑ j, ‖U j‖ ^ 2 + ∑ j, ‖V j‖ ^ 2 := by
          nlinarith [sq_nonneg (‖U i‖ - ‖V j‖), norm_nonneg (U i), norm_nonneg (V j)]
        calc ‖U i‖ * ‖M i j‖ * ‖V j‖ = ‖M i j‖ * (‖U i‖ * ‖V j‖) := by ring
          _ ≤ |c| * (∑ j, ‖U j‖ ^ 2 + ∑ j, ‖V j‖ ^ 2) :=
            mul_le_mul hm h1 (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (abs_nonneg c)
    _ = 144 * (|c| * (∑ j, ‖U j‖ ^ 2 + ∑ j, ‖V j‖ ^ 2)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem sesq_integrable {s : Set (ℝ × ℝ)} (hsm : MeasurableSet s) (hpos : ∀ p ∈ s, 0 ≤ p.1)
    {A : ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ} (hA : ∀ i j, Measurable (fun p => A p i j)) {c : ℝ}
    (hAc : ∀ p ∈ s, ∀ i j, ‖A p i j‖ ≤ c) {U V : ℝ × ℝ → Fin 12 → ℂ} (hU : ProfileReg s U) (hV : ProfileReg s V) :
    IntegrableOn (fun p => p.1 * (sesq12 (A p) (U p) (V p)).re) s := by
  have hg : IntegrableOn (fun p => 144 * |c| * (p.1 * ∑ j, ‖U p j‖ ^ 2 + p.1 * ∑ j, ‖V p j‖ ^ 2)) s :=
    (hU.2.add hV.2).const_mul _
  have hterm : ∀ i j, AEMeasurable (fun p => (starRingEnd ℂ) (U p i) * A p i j * V p j) (volume.restrict s) :=
    fun i j => ((Complex.continuous_conj.measurable.comp_aemeasurable (hU.1 i).aemeasurable).mul
      (hA i j).aemeasurable).mul (hV.1 j).aemeasurable
  have hsum : AEMeasurable (fun p => sesq12 (A p) (U p) (V p)) (volume.restrict s) := by
    unfold sesq12
    exact Finset.aemeasurable_fun_sum _ (fun i _ => Finset.aemeasurable_fun_sum _ (fun j _ => hterm i j))
  have hm : AEStronglyMeasurable (fun p => p.1 * (sesq12 (A p) (U p) (V p)).re) (volume.restrict s) :=
    (measurable_fst.aemeasurable.mul (Complex.measurable_re.comp_aemeasurable hsum)).aestronglyMeasurable
  refine hg.mono' hm ((ae_restrict_iff' hsm).2 (Filter.Eventually.of_forall fun p hp => ?_))
  have h0 := hpos p hp
  have hb := sesq12_norm_le (A p) (U p) (V p) (hAc p hp)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
  have hre : |(sesq12 (A p) (U p) (V p)).re| ≤ ‖sesq12 (A p) (U p) (V p)‖ := Complex.abs_re_le_norm _
  calc p.1 * |(sesq12 (A p) (U p) (V p)).re| ≤ p.1 * (144 * (|c| * (∑ j, ‖U p j‖ ^ 2 + ∑ j, ‖V p j‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left (hre.trans hb) h0
    _ = 144 * |c| * (p.1 * ∑ j, ‖U p j‖ ^ 2 + p.1 * ∑ j, ‖V p j‖ ^ 2) := by ring

end Internal

namespace Internal

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

theorem leaf_split (hM : IsCellMesh D.mesh) (hcc : CellCalculusConditions D R) (K : Fin D.mesh.count) (q : Fin k → ℝ)
    (hq : q ∈ D.cert.params) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (P : PotentialData (CellVars D R K)) (x : CellVars D R K → ℂ)
    (hprof : ∀ ι, ProfileReg (D.mesh.box K).rect (fun p => bandProfile D ι v G p))
    (hlt : ∀ ι ∈ D.mesh.resolved K, ∀ᵐ p ∂(volume.restrict (D.mesh.box K).rect),
      trueProfiles D v G ι p = lowAt D R K x ι p + tailProfile D R K ι v G p) :
    leafPair D R K (trueProfiles D v G) (trueProfiles D v G) - leafPair D R K (lowAt D R K x) (lowAt D R K x)
      = 2 * leafPair D R K (upperProfiles D R K P x) (tailProfiles D R K v G)
        + leafPair D R K (otherProfiles D R K P x v G) (otherProfiles D R K P x v G)
        - leafPair D R K (lowAt D R K (bandPart D R K P x)) (lowAt D R K (bandPart D R K P x)) := by
  unfold leafPair
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun ι hι => ?_)
  have hsm := rect_measurable (D.mesh.box K)
  have hcpt : IsCompact (D.mesh.box K).rect := isCompact_Icc.prod isCompact_Icc
  have hpos : ∀ p ∈ (D.mesh.box K).rect, 0 ≤ p.1 := fun p hp => fst_nonneg_of_mem _ (hM.box_valid K) hp
  have hleaf := hcc.leaves_valid K q hq
  obtain ⟨hAm, c, hAc⟩ := hleaf.matrix_regular ι hι
  have hT : ProfileReg (D.mesh.box K).rect (fun p => trueProfiles D v G ι p) := hprof ι
  have hL : ProfileReg (D.mesh.box K).rect (fun p => lowAt D R K x ι p) :=
    profileReg_of_continuous hcpt (continuous_lowAt D R K x ι)
  have hUp : ProfileReg (D.mesh.box K).rect (fun p => upperProfiles D R K P x ι p) :=
    profileReg_of_continuous hcpt (continuous_lowAt D R K (upperPart D R K P x) ι)
  have hBy : ProfileReg (D.mesh.box K).rect (fun p => lowAt D R K (bandPart D R K P x) ι p) :=
    profileReg_of_continuous hcpt (continuous_lowAt D R K (bandPart D R K P x) ι)
  have hTL := profileReg_sub hsm hpos hT hL
  have hTU : ProfileReg (D.mesh.box K).rect (fun p => otherProfiles D R K P x v G ι p) :=
    profileReg_sub hsm hpos hT hUp
  have i1 := sesq_integrable hsm hpos hAm hAc hT hT
  have i2 := sesq_integrable hsm hpos hAm hAc hL hL
  have i3 := sesq_integrable hsm hpos hAm hAc hUp hTL
  have i4 := sesq_integrable hsm hpos hAm hAc hTU hTU
  have i5 := sesq_integrable hsm hpos hAm hAc hBy hBy
  have htail : ∫ p in (D.mesh.box K).rect, p.1 * (sesq12 ((R.leaves K).localMatrix ι p)
        (upperProfiles D R K P x ι p) (tailProfiles D R K v G ι p)).re
      = ∫ p in (D.mesh.box K).rect, p.1 * (sesq12 ((R.leaves K).localMatrix ι p)
        (upperProfiles D R K P x ι p) (trueProfiles D v G ι p - lowAt D R K x ι p)).re := by
    refine integral_congr_ae ?_
    filter_upwards [hlt ι hι] with p hp
    have e : tailProfiles D R K v G ι p = trueProfiles D v G ι p - lowAt D R K x ι p := by
      unfold tailProfiles restrictTo
      rw [if_pos (Finset.mem_coe.2 hι), hp]
      abel
    rw [e]
  rw [htail, ← integral_sub i1 i2, ← integral_const_mul, ← integral_add (i3.const_mul 2) i4, ← integral_sub _ i5]
  · refine setIntegral_congr_fun hsm (fun p hp => ?_)
    have hH := hleaf.matrix_hermitian ι hι p hp
    have hsplit := lowAt_split D R K P x ι p
    have key := leaf_point _ hH (upperProfiles D R K P x ι p) (lowAt D R K (bandPart D R K P x) ι p)
      (trueProfiles D v G ι p - lowAt D R K x ι p)
    have e1 : upperProfiles D R K P x ι p + lowAt D R K (bandPart D R K P x) ι p
        + (trueProfiles D v G ι p - lowAt D R K x ι p) = trueProfiles D v G ι p := by
      unfold upperProfiles
      rw [hsplit]
      abel
    have e2 : upperProfiles D R K P x ι p + lowAt D R K (bandPart D R K P x) ι p = lowAt D R K x ι p := by
      unfold upperProfiles
      rw [hsplit]
    have e3 : lowAt D R K (bandPart D R K P x) ι p + (trueProfiles D v G ι p - lowAt D R K x ι p)
        = otherProfiles D R K P x v G ι p := by
      unfold otherProfiles upperProfiles
      rw [hsplit]
      abel
    rw [e1, e2, e3] at key
    linear_combination p.1 * key
  · exact (i3.const_mul 2).add i4

end Internal

def TailAbsorbIdentityHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D),
    IsCellMesh D.mesh → CellCalculusConditions D R → TrueFieldRegular D →
    ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg →
      alAmount D R K (tailProfiles D R K v G)
        = ∑ ι ∈ D.mesh.resolved K, ((R.leaves K).curlAbsorb ι * tailCurlSq D R K ι G
            + (R.leaves K).strainAbsorb ι * tailStrainSq D R K ι G
            + (R.leaves K).velocityAbsorb ι * tailVelSq D R K ι v)

open _root_.Breakdown.CertCell.Assembly.Internal in
theorem splitIdentities_of_tail (hT : TailAbsorbIdentityHolds) : SplitIdentitiesHolds := by
  intro k C nE nM D R A P states hstates hreg htf hfin hC hlt K q v G H g κ F Pg ht ζ η
  have hprof := htf.1 K q v G H g κ F Pg ht
  refine ⟨offCharge_split D R hC.mesh_valid hreg.charges K q v G H hprof, ?_,
    hT D R hC.mesh_valid hC.cell_conditions htf K q v G H g κ F Pg ht⟩
  exact leaf_split D R hC.mesh_valid hC.cell_conditions K q ht.param v G (P.potential K)
    (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) (fun ι => hprof.1 ι) (hlt K q v G H g κ F Pg ht ζ η)

end Assembly

end CertCell

end Breakdown
