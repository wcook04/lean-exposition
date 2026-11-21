import Breakdown.CertCell.AssemblyPotentialLeafParts

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder

noncomputable section

namespace Breakdown.CertCell.Assembly

open CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy CellCalculus

namespace Internal.PotentialLeaf

section Leaf

variable {k : ℕ} {C : Type} {nE nM : ℕ} {D : CellLayerData k C nE nM} {R : CellCalculusEntry D}
  {K : Fin D.mesh.count} {q : Fin k → ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
  {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} {κ : Fin k → ℝ}
  {Fs Pg : ℝ → Space → Space}

theorem leaf_point (hK : IsCellBox (D.mesh.box K))
    (hLT : IsLeafValues (D.mesh.box K) (D.mesh.resolved K)
      (fun ι p => ModeCoefficients.ofPieces (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn
        D.azimuthOrder ι p) (D.charges (some K)) (R.leaves K))
    {ι : ℤ × ℤ} (hι : ι ∈ D.mesh.resolved K) (p : ℝ × ℝ) (hp : p ∈ (D.mesh.box K).rect) :
    p.1 * (sesq12 ((R.leaves K).localMatrix ι p) (trueProfiles D v G ι p) (trueProfiles D v G ι p)).re
        + p.1 * (R.leaves K).boxPenalty ι (gradArray D.azimuthOrder ι G p) (velArray D.azimuthOrder ι v p)
        + (R.leaves K).hessFloor ι * (p.1 * slopeSq D.azimuthOrder ι H p)
        + (R.leaves K).curlHessFloor ι * (p.1 * curlSlopeSq D.azimuthOrder ι H p)
      ≤ D.labelDensity q v G H ι p * p.1 := by
  rcases (hK.r_order.1.trans hp.1.1).eq_or_lt with h | h
  · rw [← h]
    simp
  · obtain ⟨n1, n2, n3, n4, n5⟩ := leafNorms_holds D.azimuthOrder ι v G H p h
    have hd := leafDensityLower_holds _ hK _ _ _ _ hLT ι hι p hp (Real.sqrt (slopeSq D.azimuthOrder ι H p))
      (Real.sqrt (curlSlopeSq D.azimuthOrder ι H p)) (gradArray D.azimuthOrder ι G p) (velArray D.azimuthOrder ι v p)
    have hden : D.labelDensity q v G H ι p
        = (ModeCoefficients.ofPieces (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn D.azimuthOrder ι p).value
          (Real.sqrt (slopeSq D.azimuthOrder ι H p)) (Real.sqrt (curlSlopeSq D.azimuthOrder ι H p))
          (Real.sqrt (sumSq (gradArray D.azimuthOrder ι G p))) (Real.sqrt (curlSq (gradArray D.azimuthOrder ι G p)))
          (Real.sqrt (vecSq (velArray D.azimuthOrder ι v p))) := by
      rw [← n1, ← n2, ← n3, ← n4, ← n5]
      exact ModeCoefficients.modeDensity_eq_value _ _ _ _ _ _ _ _ _ _ _ _
    have s1 : 0 ≤ slopeSq D.azimuthOrder ι H p := Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    have s2 : 0 ≤ curlSlopeSq D.azimuthOrder ι H p := Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => by positivity
    rw [Real.sq_sqrt s1, Real.sq_sqrt s2] at hd
    rw [hden]
    have hs : (sesq12 ((R.leaves K).localMatrix ι p) (trueProfiles D v G ι p) (trueProfiles D v G ι p)).re
        = sesqValue ((R.leaves K).localMatrix ι p)
          (pairVec (gradArray D.azimuthOrder ι G p) (velArray D.azimuthOrder ι v p)) := rfl
    rw [hs]
    nlinarith [mul_le_mul_of_nonneg_left hd h.le]

theorem leaf_key (hA : AssemblyRegular D R) (hT : TrueFieldRegular D) (hF : CellPiecesFinite D R)
    (hC : CellCalculusConditions D R) (ht : IsCellTuple D K q v G H g κ Fs Pg) {ι : ℤ × ℤ}
    (hι : ι ∈ D.mesh.resolved K) :
    (∫ p in (D.mesh.box K).rect, p.1 * (sesq12 ((R.leaves K).localMatrix ι p)
        (trueProfiles D v G ι p) (trueProfiles D v G ι p)).re)
      + (∫ p in (D.mesh.box K).rect, p.1 *
        (R.leaves K).boxPenalty ι (gradArray D.azimuthOrder ι G p) (velArray D.azimuthOrder ι v p))
      + ((R.leaves K).hessFloor ι * ∫ p in (D.mesh.box K).rect, p.1 * slopeSq D.azimuthOrder ι H p)
      + ((R.leaves K).curlHessFloor ι * ∫ p in (D.mesh.box K).rect, p.1 * curlSlopeSq D.azimuthOrder ι H p)
    ≤ ∫ p in (D.mesh.box K).rect, D.labelDensity q v G H ι p * p.1 := by
  have hv : IsPeriodicSecondOrder v G H :=
    periodicSecondOrder_of_perturbation (Bridge.velocitySixthIntegral ⟨_, sixthPowerGradientBound_four_thirds⟩)
      Bridge.secondDerivEnergyIdentity _ _ v G H g ht.perturbation
  have hK : IsCellBox (D.mesh.box K) := hA.field.mesh_valid.box_valid K
  have hLT := hC.leaves_valid K q ht.param
  obtain ⟨hMm, c, hc⟩ := hLT.matrix_regular ι hι
  have I1 := pair_integrable hK hT ht ι hMm hc
  have I2 := box_integrable hK hT ht ι (R.leaves K)
  obtain ⟨I3, I4⟩ := slope_integrable hK D.azimuthOrder hv ι
  have I5 := density_integrable hT hF ht ι
  have e : (∫ p in (D.mesh.box K).rect, (p.1 * (sesq12 ((R.leaves K).localMatrix ι p)
        (trueProfiles D v G ι p) (trueProfiles D v G ι p)).re
      + p.1 * (R.leaves K).boxPenalty ι (gradArray D.azimuthOrder ι G p) (velArray D.azimuthOrder ι v p)
      + (R.leaves K).hessFloor ι * (p.1 * slopeSq D.azimuthOrder ι H p)
      + (R.leaves K).curlHessFloor ι * (p.1 * curlSlopeSq D.azimuthOrder ι H p)))
      = (∫ p in (D.mesh.box K).rect, p.1 * (sesq12 ((R.leaves K).localMatrix ι p)
        (trueProfiles D v G ι p) (trueProfiles D v G ι p)).re)
      + (∫ p in (D.mesh.box K).rect, p.1 *
        (R.leaves K).boxPenalty ι (gradArray D.azimuthOrder ι G p) (velArray D.azimuthOrder ι v p))
      + ((R.leaves K).hessFloor ι * ∫ p in (D.mesh.box K).rect, p.1 * slopeSq D.azimuthOrder ι H p)
      + ((R.leaves K).curlHessFloor ι * ∫ p in (D.mesh.box K).rect, p.1 * curlSlopeSq D.azimuthOrder ι H p) := by
    rw [integral_add, integral_add, integral_add, integral_const_mul, integral_const_mul]
    · exact I1
    · exact I2
    · exact I1.add I2
    · exact I3.const_mul _
    · exact (I1.add I2).add (I3.const_mul _)
    · exact I4.const_mul _
  rw [← e]
  exact setIntegral_mono_on (((I1.add I2).add (I3.const_mul _)).add (I4.const_mul _)) I5
    (RowLow.Internal.rect_meas _) (fun p hp => leaf_point hK hLT hι p hp)

theorem leaf_low (hC : CellCalculusConditions D R) (hq : q ∈ D.cert.params) (η : Fin (R.portCount K) → ℂ)
    (ζ : Fin k → ℝ) {ι : ℤ × ℤ} (hι : ι ∈ D.mesh.resolved K) :
    (∑ n : ((R.layouts K).layout ι).modes,
        (∫ p in (D.mesh.box K).rect, (p.1 : ℂ) *
          matrixSesq ((R.leaves K).localMatrix ι p)
            (pairVec (lowStrainOf ((R.layouts K).layout ι) (modeData (R.layouts K) ι v G H Pg) n · · p)
              (lowVelocityOf ((R.layouts K).layout ι) (modeData (R.layouts K) ι v G H Pg) n · p))
            (pairVec (lowStrainOf ((R.layouts K).layout ι) (modeData (R.layouts K) ι v G H Pg) n · · p)
              (lowVelocityOf ((R.layouts K).layout ι) (modeData (R.layouts K) ι v G H Pg) n · p))).re)
      = ∫ p in (D.mesh.box K).rect, p.1 * (sesq12 ((R.leaves K).localMatrix ι p)
          (lowAt D R K (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) ι p)
          (lowAt D R K (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) ι p)).re := by
  obtain ⟨c₀, S₀, -, hres, hL⟩ := (hC.layouts_valid K).layout_valid ι hι
  have hK : IsCellBox (D.mesh.box K) := hL.box_valid
  have hmodes : ((R.layouts K).layout ι).modes = {ι.1} := hL.modes_eq.trans hres
  obtain ⟨hMm, c, hc⟩ := (hC.leaves_valid K q hq).matrix_regular ι hι
  rw [sum_single _ hmodes]
  set W : ℝ × ℝ → Fin 12 → ℂ := fun p =>
    pairVec (lowStrainOf ((R.layouts K).layout ι) (modeData (R.layouts K) ι v G H Pg)
        ⟨ι.1, by rw [hmodes]; exact Finset.mem_singleton_self _⟩ · · p)
      (lowVelocityOf ((R.layouts K).layout ι) (modeData (R.layouts K) ι v G H Pg)
        ⟨ι.1, by rw [hmodes]; exact Finset.mem_singleton_self _⟩ · p) with hW
  have hlow : ∀ p, lowAt D R K (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) ι p = W p := by
    intro p
    simp only [lowAt, dif_pos hι, lowProfile]
    unfold lowGrad lowVel
    simp only [sum_single _ hmodes]
    rfl
  have hWc : Continuous W := by
    refine continuous_pi fun j => ?_
    simp only [hW, pairVec]
    split_ifs
    · exact continuous_finsetSum _ fun j' _ => continuous_finsetSum _ fun l _ =>
        continuous_const.mul (CellCert.CellEnergy.TopFormInternal.basisC_cont _ _ _)
    · exact continuous_finsetSum _ fun j' _ => continuous_finsetSum _ fun l _ =>
        continuous_const.mul (CellCert.CellEnergy.TopFormInternal.basisC_cont _ _ _)
  have hWI : IntegrableOn (fun p => p.1 * ∑ j, ‖W p j‖ ^ 2) (D.mesh.box K).rect :=
    (continuous_fst.mul (continuous_finsetSum _ fun j _ =>
      ((continuous_apply j).comp hWc).norm.pow 2)).continuousOn.integrableOn_compact
        (RowLow.Internal.rect_compact _)
  have hint := sesq_integrable (U := W) (RowLow.Internal.rect_meas _) (fun p hp => hK.r_order.1.trans hp.1.1)
    (fun j => ((continuous_apply j).comp hWc).aestronglyMeasurable) hWI
    (fun i j => (hMm i j).aestronglyMeasurable) hc
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  simp only [hlow]
  refine (congrArg Complex.re (?_ : _ = ∫ p in (D.mesh.box K).rect,
    (p.1 : ℂ) * sesq12 ((R.leaves K).localMatrix ι p) (W p) (W p))).trans (hre.symm.trans ?_)
  · rfl
  · refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [Complex.re_ofReal_mul]

end Leaf

end Internal.PotentialLeaf

open Internal.PotentialLeaf in
theorem lowTailSplit_holds : LowTailSplitHolds := by
  intro k C nE nM D R _ _ hC K q v G H g κ F Pg ht ζ η ι hι
  have hv : IsPeriodicSecondOrder v G H :=
    periodicSecondOrder_of_perturbation (Bridge.velocitySixthIntegral ⟨_, sixthPowerGradientBound_four_thirds⟩)
      Bridge.secondDerivEnergyIdentity _ _ v G H g ht.perturbation
  refine Filter.Eventually.of_forall (fun p => ?_)
  have eG : lowGrad D R K ⟨ι, hι⟩ (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) p
      = fun a b => (D.mesh.box K).proj ((R.layouts K).layout ι).degCoef ((R.layouts K).layout ι).degCoef
          (fun p' => gradAt D.azimuthOrder ι G a b p') p :=
    funext fun a => funext fun b => low_grad_eq D R hC hv Pg κ ζ η hι p a b
  have eV : lowVel D R K ⟨ι, hι⟩ (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) p
      = fun a => (D.mesh.box K).proj (((R.layouts K).layout ι).degCoef - 1)
          (((R.layouts K).layout ι).degCoef - 1) (fun p' => velAt D.azimuthOrder ι v a p') p :=
    funext fun a => low_vel_eq D R hC hv Pg κ ζ η hι p a
  simp only [trueProfiles, lowAt, dif_pos hι, lowProfile]
  rw [eG, eV]
  exact pairVec_split _ _ _ _


open Internal.PotentialLeaf in
theorem leafSplit_holds : LeafSplitHolds := by
  intro k C nE nM D R hA hT hF hC K q v G H g κ Fs Pg ht ζ η
  have key : ∀ ι ∈ D.mesh.resolved K, _ := fun ι hι => leaf_key hA hT hF hC ht hι
  have hE : energyBudget D R K v G H Pg + tailCredit D R K G H
      = ∑ ι ∈ D.mesh.resolved K, (((R.leaves K).hessFloor ι * ∫ p in (D.mesh.box K).rect,
            p.1 * slopeSq D.azimuthOrder ι H p)
          + ((R.leaves K).curlHessFloor ι * ∫ p in (D.mesh.box K).rect, p.1 * curlSlopeSq D.azimuthOrder ι H p)
          + ∫ p in (D.mesh.box K).rect, p.1 * (sesq12 ((R.leaves K).localMatrix ι p)
            (lowAt D R K (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) ι p)
            (lowAt D R K (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) ι p)).re) := by
    unfold energyBudget tailCredit
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ι hι => ?_)
    rw [leaf_low hC ht.param η ζ hι]
    ring
  unfold leafPair boxAmount resolvedAmount
  rw [hE]
  have hs := Finset.sum_le_sum key
  simp only [Finset.sum_add_distrib] at hs ⊢
  linarith

end Breakdown.CertCell.Assembly
