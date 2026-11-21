import Breakdown.CertCell.AssemblyRowExpansionRestGram
import Breakdown.CertCell.AssemblyRowExpansionRestDeact

open MeasureTheory Matrix
open scoped ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open Coupling CellCert.CellAnalysis CellCert.CellFormula CellCalculus _root_.Breakdown.CertCell.Assembly.Internal

private theorem restPlane_facts {count : ℕ} (box : Fin count → CellBox) (K : Fin count) (hK : IsCellBox (box K))
    (F : CellVecField count) (α : ℤ × ℤ) :
    (∀ a, AEStronglyMeasurable (fun p => F.planeValue box K α a p) (volume.restrict (box K).rect)) ∧
    ∃ CW : ℝ, ∀ p ∈ (box K).rect, ∑ a, ‖F.planeValue box K α a p‖ ^ 2 ≤ CW := by
  have h : ∀ a, ∀ p ∈ (box K).rect, (F.comp K α a).eval (box K) p = F.planeValue box K α a p := by
    intro a p hp
    have h2 : 0 ≤ p.2 := le_trans hK.z_order.1 hp.2.1
    simp only [CellVecField.planeValue, labelValueAt, if_pos h2]
  refine ⟨fun a => (cellPoly_eval_continuous _ _).aestronglyMeasurable.congr
    (ae_restrict_of_forall_mem (rect_measurableSet _) (h a)), ?_⟩
  have hc : Continuous (fun p => ∑ a, ‖(F.comp K α a).eval (box K) p‖ ^ 2) := by
    refine continuous_finsetSum _ (fun a _ => ?_)
    exact ((cellPoly_eval_continuous _ _).norm).pow 2
  obtain ⟨CW, hCW⟩ := (rect_isCompact (box K)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨CW, fun p hp => ?_⟩
  have e : ∑ a, ‖F.planeValue box K α a p‖ ^ 2 = ∑ a, ‖(F.comp K α a).eval (box K) p‖ ^ 2 :=
    Finset.sum_congr rfl (fun a _ => by rw [h a p hp])
  rw [e]
  exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hCW p hp))

private theorem restWeighted_lin {K : CellBox} {X Z : ℝ × ℝ → ℝ}
    (hXi : IntegrableOn (fun p => p.1 * X p) K.rect) (hZi : IntegrableOn (fun p => p.1 * Z p) K.rect) (a b : ℝ) :
    ∫ p in K.rect, p.1 * (a * X p + b * Z p) = a * (∫ p in K.rect, p.1 * X p) + b * (∫ p in K.rect, p.1 * Z p) := by
  have h := weighted_two_eq hXi hZi 1 a b
  simpa only [one_mul] using h

theorem freqPieceBound_holds : FreqPieceBoundHolds := by
  intro k C nE nM D R A P states hstates _hReg hTF hC hF K q v G H g κ F Pg ht
  have hK := hC.mesh_valid.box_valid K
  have hcp := (hF.costs_pos K).2.2.2.2
  set c0 : ℤ × ℤ → ℝ := fun ℓ => 2 * Real.pi * (labelTime ℓ : ℝ) * (1 / D.cert.period q - D.model.periodInverse)
    with hc0
  let f : ℤ × ℤ → ℝ × ℝ → Fin 3 → ℂ := fun ℓ p a => ((c0 ℓ : ℝ) : ℂ) * Complex.I * velAt D.azimuthOrder ℓ v a p
  have hfm : ∀ ℓ ∈ D.mesh.tested K, ∀ a, AEStronglyMeasurable (fun p => f ℓ p a)
      (volume.restrict (D.mesh.box K).rect) := fun ℓ _ a =>
    aestronglyMeasurable_const.mul ((profile_facts D hTF ht ℓ).1 a)
  have hnorm : ∀ ℓ p a, ‖f ℓ p a‖ ^ 2 = c0 ℓ ^ 2 * ‖velAt D.azimuthOrder ℓ v a p‖ ^ 2 := by
    intro ℓ p a
    simp only [f, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_one, mul_pow, sq_abs]
  have hfi : ∀ ℓ ∈ D.mesh.tested K, ∀ a, IntegrableOn (fun p => p.1 * ‖f ℓ p a‖ ^ 2) (D.mesh.box K).rect := by
    intro ℓ _ a
    simp only [hnorm]
    refine ((profile_integrable D hTF hK ht ℓ).2.2 a).const_mul (c0 ℓ ^ 2) |>.congr ?_
    exact Filter.Eventually.of_forall (fun p => by simp only; ring)
  have hb := inverseWeightedSq_scaled_rows_le D R A hC K (A.blocks K).freqCost hcp f hfm hfi
    (freqPiece D K (A.blocks K) (D.cert.period q) v) (by
      intro i
      unfold freqPiece
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      simp only [f, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      ring)
  have hper := hF.period_box q ht.param K
  unfold freqAllowance
  refine hb.trans (Finset.sum_le_sum (fun ι hι => ?_))
  have hI : ∫ p in (D.mesh.box K).rect, p.1 * ∑ a, ‖f ι p a‖ ^ 2
      = c0 ι ^ 2 * ∫ p in (D.mesh.box K).rect, p.1 * modeVelSq D ι v p := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    simp only [hnorm, modeVelSq, ← Finset.mul_sum]
    ring
  rw [hI]
  have hI0 := weighted_integral_nonneg hK (fun p => by unfold modeVelSq; positivity : ∀ p, 0 ≤ modeVelSq D ι v p)
  have hd := abs_le.mp hper
  have hsq : (1 / D.cert.period q - D.model.periodInverse) ^ 2 ≤ (D.modelErrors K).periodInverse ^ 2 :=
    sq_le_sq' hd.1 hd.2
  have hc : c0 ι ^ 2 ≤ (2 * Real.pi * (labelTime ι : ℝ) * (D.modelErrors K).periodInverse) ^ 2 := by
    simp only [hc0, mul_pow]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hI0) (hcp ι hι).le

theorem deactPieceBound_holds : DeactPieceBoundHolds := by
  intro k C nE nM D R A P states hstates _hReg hTF hP hC hF K q v G H g κ F Pg ht
  classical
  have hK := hC.mesh_valid.box_valid K
  have hm : 1 ≤ D.azimuthOrder := hP.azimuth_pos
  obtain ⟨_, hdC, _, _, _⟩ := hF.costs_pos K
  set PK := P.potential K with hPK
  have hbpm : ∀ ι j, AEStronglyMeasurable (fun p => bandProfile D ι v G p j) (volume.restrict (D.mesh.box K).rect) :=
    fun ι j => ((hTF.1 K q v G H g κ F Pg ht).1 ι).1 j
  have hbpi : ∀ ι, IntegrableOn (fun p => p.1 * ∑ j, ‖bandProfile D ι v G p j‖ ^ 2) (D.mesh.box K).rect :=
    fun ι => ((hTF.1 K q v G H g κ F Pg ht).1 ι).2
  have hmv := fun α => restPlane_facts D.mesh.box K hK D.model.velocity α
  have hmw := fun α => restPlane_facts D.mesh.box K hK D.model.vorticity α
  have hφc : ∀ i c, Continuous (fun p => rowTestValue D K (A.blocks K) i p c) :=
    fun i c => rowTestValue_continuous D K (A.blocks K) i c
  have hterm : ∀ i ι', IntegrableOn (fun p => (p.1 : ℂ) * ∑ c, Internal.crossVec (bandProfile D ι' v G p)
      (modelVelocity D K ((A.blocks K).rowLabel i - ι') p) (modelVorticity D K ((A.blocks K).rowLabel i - ι') p) c
      * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p c)) (D.mesh.box K).rect := by
    intro i ι'
    obtain ⟨hvm, CW, hCW⟩ := hmv ((A.blocks K).rowLabel i - ι')
    obtain ⟨hwm, CΩ, hCΩ⟩ := hmw ((A.blocks K).rowLabel i - ι')
    exact crossVec_term_integrable hK (hbpm ι') (hbpi ι') hvm hwm
      (ae_restrict_of_forall_mem (rect_measurableSet _) hCW) (ae_restrict_of_forall_mem (rect_measurableSet _) hCΩ) (hφc i)
  let y : Fin PK.groupCount → ℤ × ℤ → ℝ × ℝ → Fin 3 → ℂ := fun j ℓ p c =>
    ∑ ι' ∈ PK.rowPartners j, (if ℓ - ι' ∈ PK.groupHarmonics j then
      Internal.crossVec (bandProfile D ι' v G p) (modelVelocity D K (ℓ - ι') p) (modelVorticity D K (ℓ - ι') p) c else 0)
  set Rd : Fin PK.groupCount → ℝ × ℝ → ℝ := fun j p =>
    2 * PK.groupVel j ^ 2 * ∑ ι' ∈ PK.rowPartners j, modeCurlSq D ι' G p
      + 2 * PK.groupCurl j ^ 2 * ∑ ι' ∈ PK.rowPartners j, modeVelSq D ι' v p with hRd
  have hcs := fun ι => (profile_integrable D hTF hK ht ι).2.1
  have hvs := fun ι => (profile_integrable D hTF hK ht ι).1
  have hRdi : ∀ j, IntegrableOn (fun p => p.1 * Rd j p) (D.mesh.box K).rect := by
    intro j
    have h : IntegrableOn (fun p => 2 * PK.groupVel j ^ 2 * ∑ ι' ∈ PK.rowPartners j, p.1 * modeCurlSq D ι' G p
        + 2 * PK.groupCurl j ^ 2 * ∑ ι' ∈ PK.rowPartners j, p.1 * modeVelSq D ι' v p) (D.mesh.box K).rect :=
      ((integrable_finsetSum _ (fun ι' _ => hcs ι')).const_mul _).add
        ((integrable_finsetSum _ (fun ι' _ => hvs ι')).const_mul _)
    refine h.congr (Filter.Eventually.of_forall (fun p => ?_))
    simp only [hRd, mul_add, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hpt : ∀ j, ∀ p ∈ (D.mesh.box K).rect, ∑ ℓ ∈ D.mesh.tested K, ∑ c, ‖y j ℓ p c‖ ^ 2 ≤ Rd j p :=
    fun j p hp => deact_pointwise D R A P hm hF K j (D.mesh.tested K) v G p hp
  have hfm : ∀ j, ∀ ℓ ∈ D.mesh.tested K, ∀ c, AEStronglyMeasurable (fun p => y j ℓ p c)
      (volume.restrict (D.mesh.box K).rect) := by
    intro j ℓ _ c
    refine Finset.aestronglyMeasurable_fun_sum _ (fun ι' _ => ?_)
    split_ifs
    · exact crossVec_measurable (hbpm ι') (hmv _).1 (hmw _).1 c
    · exact aestronglyMeasurable_const
  have hfi : ∀ j, ∀ ℓ ∈ D.mesh.tested K, ∀ c, IntegrableOn (fun p => p.1 * ‖y j ℓ p c‖ ^ 2)
      (D.mesh.box K).rect := by
    intro j ℓ hℓ c
    refine Integrable.mono' (hRdi j) (continuous_fst.aestronglyMeasurable.mul ((hfm j ℓ hℓ c).norm.pow 2)) ?_
    filter_upwards [ae_restrict_mem (rect_measurableSet (D.mesh.box K))] with p hp
    have hp0 := rect_first_nonneg hK hp
    rw [Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left (le_trans ?_ (hpt j p hp)) hp0
    refine le_trans ?_ (Finset.single_le_sum (f := fun ℓ => ∑ c, ‖y j ℓ p c‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)) hℓ)
    exact Finset.single_le_sum (f := fun c => ‖y j ℓ p c‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ c)
  have heq : ∀ j i, deactGroupPiece D K (A.blocks K) PK j v G i = ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) *
      ∑ c, y j ((A.blocks K).rowLabel i) p c * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p c) := by
    intro j i
    unfold deactGroupPiece
    have step : ∀ ι' ∈ PK.rowPartners j, (if (A.blocks K).rowLabel i - ι' ∈ PK.groupHarmonics j then
          ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ c, bandProfile D ι' v G p c * (starRingEnd ℂ)
            (crossTest (modelVelocity D K ((A.blocks K).rowLabel i - ι') p)
              (modelVorticity D K ((A.blocks K).rowLabel i - ι') p) (rowTestValue D K (A.blocks K) i p) c) else 0)
        = ∫ p in (D.mesh.box K).rect, (if (A.blocks K).rowLabel i - ι' ∈ PK.groupHarmonics j then
          (p.1 : ℂ) * ∑ c, Internal.crossVec (bandProfile D ι' v G p) (modelVelocity D K ((A.blocks K).rowLabel i - ι') p)
            (modelVorticity D K ((A.blocks K).rowLabel i - ι') p) c
            * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p c) else 0) := by
      intro ι' _
      split_ifs
      · simp only [crossTest_pairing]
      · simp
    rw [Finset.sum_congr rfl step, ← integral_finsetSum]
    · refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      simp only [y, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun ι' _ => ?_)
      split_ifs
      · rfl
      · simp
    · intro ι' _
      split_ifs
      · exact hterm i ι'
      · exact integrable_zero _ _ _
  have hb : ∀ j, inverseWeightedSq (rowGram D K (A.blocks K)) (deactGroupPiece D K (A.blocks K) PK j v G)
      ≤ ∑ ℓ ∈ D.mesh.tested K, ∫ p in (D.mesh.box K).rect, p.1 * ∑ c, ‖y j ℓ p c‖ ^ 2 :=
    fun j => inverseWeightedSq_rows_le D R A hC K (y j) (hfm j) (hfi j) _ (heq j)
  have hmr := rect_measurableSet (D.mesh.box K)
  have hsumi : ∀ j, ∀ ℓ ∈ D.mesh.tested K, IntegrableOn (fun p => p.1 * ∑ c, ‖y j ℓ p c‖ ^ 2)
      (D.mesh.box K).rect := by
    intro j ℓ hℓ
    simp only [Finset.mul_sum]
    exact integrable_finsetSum _ (fun c _ => hfi j ℓ hℓ c)
  have h1 : ∀ j, ∑ ℓ ∈ D.mesh.tested K, ∫ p in (D.mesh.box K).rect, p.1 * ∑ c, ‖y j ℓ p c‖ ^ 2
      ≤ ∫ p in (D.mesh.box K).rect, p.1 * Rd j p := by
    intro j
    rw [← integral_finsetSum _ (hsumi j)]
    refine setIntegral_mono_on (integrable_finsetSum _ (hsumi j)) (hRdi j) hmr (fun p hp => ?_)
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hpt j p hp) (rect_first_nonneg hK hp)
  have hL : ∀ ι, IntegrableOn (fun p => p.1 * (2 * (A.blocks K).deactCost *
      ((∑ j, if ι ∈ PK.rowPartners j then PK.groupVel j ^ 2 else 0) * modeCurlSq D ι G p
        + (∑ j, if ι ∈ PK.rowPartners j then PK.groupCurl j ^ 2 else 0) * modeVelSq D ι v p)))
      (D.mesh.box K).rect := by
    intro ι
    refine (((hcs ι).const_mul (2 * (A.blocks K).deactCost *
      ∑ j, if ι ∈ PK.rowPartners j then PK.groupVel j ^ 2 else 0)).add
      ((hvs ι).const_mul (2 * (A.blocks K).deactCost *
        ∑ j, if ι ∈ PK.rowPartners j then PK.groupCurl j ^ 2 else 0))).congr
      (Filter.Eventually.of_forall (fun p => ?_))
    simp only [Pi.add_apply]
    ring
  have h2 : (A.blocks K).deactCost * ∑ j, ∫ p in (D.mesh.box K).rect, p.1 * Rd j p
      = deactAllowance D K (A.blocks K) PK v G := by
    unfold deactAllowance
    rw [← integral_finsetSum _ (fun j _ => hRdi j), ← integral_const_mul, ← integral_finsetSum _ (fun ι _ => hL ι)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    beta_reduce
    have e1 : ∑ j, p.1 * Rd j p = p.1 * ∑ j, ∑ ι' ∈ PK.rowPartners j,
        (2 * PK.groupVel j ^ 2 * modeCurlSq D ι' G p + 2 * PK.groupCurl j ^ 2 * modeVelSq D ι' v p) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [hRd, Finset.sum_add_distrib, Finset.mul_sum]
    rw [e1, sum_partners_eq PK.rowPartners (A.blocks K).leakModes (hF.partners_leak K)]
    have e2 : ∀ ι, ∑ j, (if ι ∈ PK.rowPartners j then
          2 * PK.groupVel j ^ 2 * modeCurlSq D ι G p + 2 * PK.groupCurl j ^ 2 * modeVelSq D ι v p else 0)
        = 2 * ((∑ j, if ι ∈ PK.rowPartners j then PK.groupVel j ^ 2 else 0) * modeCurlSq D ι G p
          + (∑ j, if ι ∈ PK.rowPartners j then PK.groupCurl j ^ 2 else 0) * modeVelSq D ι v p) := by
      intro ι
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      split_ifs <;> ring
    have e3 : ∀ ι, p.1 * (2 * (A.blocks K).deactCost *
        ((∑ j, if ι ∈ PK.rowPartners j then PK.groupVel j ^ 2 else 0) * modeCurlSq D ι G p
          + (∑ j, if ι ∈ PK.rowPartners j then PK.groupCurl j ^ 2 else 0) * modeVelSq D ι v p))
        = (A.blocks K).deactCost * (p.1 * ∑ j, (if ι ∈ PK.rowPartners j then
          2 * PK.groupVel j ^ 2 * modeCurlSq D ι G p + 2 * PK.groupCurl j ^ 2 * modeVelSq D ι v p else 0)) := by
      intro ι
      rw [e2 ι]
      ring
    rw [Finset.sum_congr rfl (fun ι _ => e3 ι), ← Finset.mul_sum, ← Finset.mul_sum]
  rw [← h2, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ =>
    mul_le_mul_of_nonneg_left ((hb j).trans (h1 j)) hdC.le)

end Assembly

end CertCell

end Breakdown
