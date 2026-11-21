import Breakdown.CertCell.AssemblyPotentialSharp

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

namespace Internal

namespace EpsResolved

theorem cnormSq_nonneg_aux {β : Type*} [Fintype β] (x : β → ℂ) : 0 ≤ cnormSq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem splitCharge_nonneg_aux (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (U : Fin 12 → ℂ) :
    0 ≤ splitCharge a b c (velOf U) (gradOf U) := by
  unfold splitCharge
  exact add_nonneg (add_nonneg (mul_nonneg ha (cnormSq_nonneg_aux _)) (mul_nonneg hb (cnormSq_nonneg_aux _)))
    (mul_nonneg hc (cnormSq_nonneg_aux _))

theorem splitCharge_le_boxPair (T : LeafValues) (ι : ℤ × ℤ) (a b c : ℝ)
    (h1 : a ≤ T.boxPairCurl ι) (h2 : b ≤ T.boxPairStrain ι) (h3 : c ≤ T.boxPairVelocity ι) (U : Fin 12 → ℂ) :
    splitCharge a b c (velOf U) (gradOf U) ≤ T.boxPairPenalty ι (strainOfVec U) (velOf U) := by
  unfold splitCharge LeafValues.boxPairPenalty
  rw [Internal.Sharp.curlSq_strainOfVec, Internal.Sharp.sumSq_strainOfVec, Internal.Sharp.vecSq_velOf]
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right h1 (cnormSq_nonneg_aux _))
    (mul_le_mul_of_nonneg_right h2 (cnormSq_nonneg_aux _))) (mul_le_mul_of_nonneg_right h3 (cnormSq_nonneg_aux _))

theorem setIntegral_add_le_of_nonneg {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) {f g h : ℝ × ℝ → ℝ}
    (hf0 : ∀ p ∈ S, 0 ≤ f p) (hg0 : ∀ p ∈ S, 0 ≤ g p) (hfg : ∀ p ∈ S, f p + g p ≤ h p)
    (hh : IntegrableOn h S) : (∫ p in S, f p) + (∫ p in S, g p) ≤ ∫ p in S, h p := by
  have hh0 : 0 ≤ ∫ p in S, h p :=
    setIntegral_nonneg hS fun p hp => (add_nonneg (hf0 p hp) (hg0 p hp)).trans (hfg p hp)
  by_cases hf : IntegrableOn f S
  · by_cases hg : IntegrableOn g S
    · rw [← integral_add hf hg]
      exact setIntegral_mono_on (hf.add hg) hh hS hfg
    · rw [integral_undef hg, add_zero]
      exact setIntegral_mono_on hf hh hS fun p hp => (le_add_of_nonneg_right (hg0 p hp)).trans (hfg p hp)
  · rw [integral_undef hf, zero_add]
    by_cases hg : IntegrableOn g S
    · exact setIntegral_mono_on hg hh hS fun p hp => (le_add_of_nonneg_left (hf0 p hp)).trans (hfg p hp)
    · rw [integral_undef hg]
      exact hh0

end EpsResolved

end Internal

open Internal.EpsResolved in
theorem epsResolvedStage_holds_of (hReg : Internal.Sharp.SharpRegularStatement) : EpsResolvedStageHolds := by
  intro k C nE nM D R A P states hstates hAR hTF hchk hLT K q v G H g κ F Pg ht ζ η
  obtain ⟨-, hloc, -⟩ := hReg D R A P states hAR hTF hchk hLT K q v G H g κ F Pg ht ζ η
  have hK : IsCellBox (D.mesh.box K) := hchk.mesh_valid.box_valid K
  have hS : MeasurableSet (D.mesh.box K).rect := measurableSet_Icc.prod measurableSet_Icc
  have h0 : ∀ p ∈ (D.mesh.box K).rect, 0 ≤ p.1 := fun p hp => hK.r_order.1.trans hp.1.1
  obtain ⟨hεS, hεG⟩ := hchk.eps_nonneg K
  obtain ⟨hlS, hlG, hlB⟩ := hchk.long_pos K
  have hℓ := hchk.length_pos K
  have hℓe := hchk.eps_length_pos K
  have hk : (0 : ℝ) ≤ 3 / (2 * Real.sqrt 2) := by positivity
  unfold formAmount labelFormAmount boxPairAmount
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ι hι => ?_
  have hfac : 0 ≤ longFactor (P.potential K) ι := by
    unfold longFactor
    split_ifs
    · exact hlB.le
    · exact add_nonneg zero_le_one (one_div_pos.2 hlB).le
  obtain ⟨e1, e2, e3⟩ := hchk.eps_box K ι hι
  set X := otherProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) v G with hX
  have hr : ∀ p, restrictTo (D.mesh.resolved K : Set (ℤ × ℤ)) X ι p = X ι p := fun p => by
    simp [restrictTo, hι]
  simp only [hr]
  refine setIntegral_add_le_of_nonneg hS (fun p hp => ?_) (fun p hp => ?_) (fun p hp => ?_) (hloc ι hι).2.1
  · beta_reduce
    refine mul_nonneg (h0 p hp) ?_
    unfold epsPartnerCharge
    exact splitCharge_nonneg_aux _ _ _ hεS (mul_nonneg (mul_nonneg hk hεG) hℓe.le)
      (div_nonneg (mul_nonneg hk hεG) hℓ.le) (X ι p)
  · beta_reduce
    refine mul_nonneg (h0 p hp) ?_
    unfold longPartnerCharge
    exact mul_nonneg hfac (splitCharge_nonneg_aux _ _ _ hlS (mul_nonneg (mul_nonneg hk hlG) hℓe.le)
      (div_nonneg (mul_nonneg hk hlG) hℓ.le) (X ι p))
  · beta_reduce
    have hpt := mul_le_mul_of_nonneg_left (splitCharge_le_boxPair (R.leaves K) ι _ _ _ e1 e2 e3 (X ι p)) (h0 p hp)
    refine le_trans (le_of_eq ?_) hpt
    unfold epsPartnerCharge longPartnerCharge splitCharge
    ring

end Assembly

end CertCell

end Breakdown
