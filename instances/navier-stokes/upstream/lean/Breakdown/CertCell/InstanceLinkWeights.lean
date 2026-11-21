import Breakdown.CertCell.InstanceStatements

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Instance

open CellCert.GivenFields (ChartParams IsChartParams Spline TensorMesh IsTensorMesh)

private theorem splineJoins_mono {a b : ℕ} {S : Spline} (h : SplineJoins a S) (hba : b ≤ a) :
    SplineJoins b S where
  mesh := h.mesh
  t_joins := fun i hi hi' j hj o ho => h.t_joins i hi hi' j hj o (ho.trans hba)
  x_joins := fun j hj hj' i hi o ho => h.x_joins j hj hj' i hi o (ho.trans hba)

private theorem joinedScalar_zero_of_two {S : ChartScalar} (h : IsJoinedScalar 2 S) : IsJoinedScalar 0 S where
  upper := splineJoins_mono h.upper (Nat.zero_le _)
  lower := splineJoins_mono h.lower (Nat.zero_le _)
  same_t := h.same_t
  plane_joins := fun i hi o ho => h.plane_joins i hi o (ho.trans (Nat.zero_le _))

private theorem le_sum_abs_of {ι : Type} [Fintype ι] (B : ι → ℝ) (i : ι) : B i ≤ ∑ j, |B j| :=
  (le_abs_self _).trans
    (Finset.single_le_sum (f := fun j => |B j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))

theorem weightClauses_of_values_holds (hsm : ScalarSmoothOfJoins) (hdec : ScalarDerivativeDecay)
    (hlip : ScalarSlopeBoundOfJoins) (hrate : ScalarRateOfDecay) (hbas : ScalarBasicFacts)
    (hstep : StepBasicFacts) {C : Type} {nE nM : ℕ} (W : WeightValues C nE nM) (hW : IsWeightValues W)
    (epsFrame : Fin nE → ℝ) (muFrame : Fin nM → ℝ) (epsSpeed : Fin nE → Space → ℝ)
    (muSpeed : Fin nM → Space → ℝ) :
    AdmissibleWeightClauses (W.pieces epsFrame muFrame epsSpeed muSpeed) := by
  have hP := hW.chart_valid
  have : Finite C := hW.classes_finite
  have : Fintype C := Fintype.ofFinite C
  have hsc := fun S : ChartScalar => hbas W.chart S hP
  have hst := fun S : StepDatum => hstep W.chart S hP
  choose Be hBe using fun β => hrate W.chart (W.eps β).weight hP (hW.eps_joined β) (hW.eps_flat β)
  choose Bm hBm using fun β => hrate W.chart (W.mu β).weight hP (hW.mu_joined β) (hW.mu_flat β)
  choose Bd hBd using fun c => hdec W.chart (W.strainWeight c) W.centralRadius hP (hW.strain_joined c)
    (hW.strain_core c) (hW.strain_decay c)
  choose Bz hBz using fun c => hdec W.chart (W.vorticityWeight c) W.centralRadius hP (hW.vorticity_joined c)
    (hW.vorticity_core c) (hW.vorticity_decay c)
  exact
  { finite_classes := hW.classes_finite
    c_pos := hW.c_pos
    c_lt_one := hW.c_lt_one
    cμ_pos := hW.cμ_pos
    cμ_lt_one := hW.cμ_lt_one
    eps_wt_nonneg := fun β y => (hsc _).2.2 (hW.eps_nonneg β) y
    mu_wt_nonneg := fun β y => (hsc _).2.2 (hW.mu_nonneg β) y
    eps_slope_bound := fun β => hlip W.chart _ hP (hW.eps_joined β) (hW.eps_flat β)
    mu_slope_bound := fun β => hlip W.chart _ hP (hW.mu_joined β) (hW.mu_flat β)
    eps_axi := fun β => (hsc _).2.1
    mu_axi := fun β => (hsc _).2.1
    eps_decay := by
      refine ⟨∑ j, |Be j|, fun β y => ?_⟩
      have h1 := (hBe β y).2.1
      rw [hW.eps_decay β, pow_one] at h1
      have h2 : ‖y‖ * (W.eps β).weight.eval W.chart y ≤ ‖y‖ * |(W.eps β).weight.eval W.chart y| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (norm_nonneg _)
      exact h2.trans (h1.trans (le_sum_abs_of Be β))
    mu_decay := by
      refine ⟨∑ j, |Bm j|, fun β y => ⟨?_, ?_, ?_⟩⟩
      · exact (le_abs_self _).trans ((hBm β y).1.trans (le_sum_abs_of Bm β))
      · have h1 := (hBm β y).2.1
        rw [hW.mu_decay β] at h1
        have h2 : ‖y‖ ^ 2 * (W.mu β).weight.eval W.chart y ≤ ‖y‖ ^ 2 * |(W.mu β).weight.eval W.chart y| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
        exact h2.trans (h1.trans (le_sum_abs_of Bm β))
      · exact (hBm β y).2.2.trans (le_sum_abs_of Bm β)
    eps_free_pos := fun β y => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hW.eps_steps β
      exact ⟨(hst _).2.2 h1 y, (hst _).2.2 h2 y, (hst _).2.2 h3 y, (hst _).2.2 h4 y, (hst _).2.2 h5 y,
        (hst _).2.2 h6 y, (hst _).2.2 h7 y, (hst _).2.2 h8 y⟩
    mu_free_pos := fun β y => ⟨(hst _).2.2 (hW.mu_steps β).1 y, (hst _).2.2 (hW.mu_steps β).2 y⟩
    mu_eta_pos := hW.mu_eta_pos
    eps_free_measurable := fun β => ⟨(hst _).1, (hst _).1, (hst _).1, (hst _).1, (hst _).1, (hst _).1,
      (hst _).1, (hst _).1⟩
    mu_free_measurable := fun β => ⟨(hst _).1, (hst _).1⟩
    eps_free_axi := fun β => ⟨(hst _).2.1, (hst _).2.1, (hst _).2.1, (hst _).2.1, (hst _).2.1, (hst _).2.1,
      (hst _).2.1, (hst _).2.1⟩
    mu_free_axi := fun β => ⟨(hst _).2.1, (hst _).2.1⟩
    convD_even := fun ι y => by
      show (W.strainWeight (W.classOf (-ι))).eval W.chart y = (W.strainWeight (W.classOf ι)).eval W.chart y
      rw [(hW.class_neg ι).1]
    convZ_even := fun ι y => by
      show (W.vorticityWeight (W.classOf (-ι))).eval W.chart y
        = (W.vorticityWeight (W.classOf ι)).eval W.chart y
      rw [(hW.class_neg ι).2]
    convD_smooth := fun c => hsm W.chart _ W.centralRadius hP (hW.strain_joined c) (hW.strain_core c)
      (hW.strain_decay c)
    convZ_smooth := fun c => hsm W.chart _ W.centralRadius hP (hW.vorticity_joined c) (hW.vorticity_core c)
      (hW.vorticity_decay c)
    convD_nonneg := fun c y => (hsc _).2.2 (hW.strain_nonneg c) y
    convD_axi := fun c => (hsc _).2.1
    convZ_axi := fun c => (hsc _).2.1
    convD_decay := by
      refine ⟨∑ c, |Bd c|, fun c y j hj => ?_⟩
      have h1 : ‖y‖ ^ j ≤ (1 + ‖y‖) ^ j := pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_nonneg y]) j
      exact (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans
        ((hBd c y j hj).trans (le_sum_abs_of Bd c))
    convZ_decay := ⟨∑ c, |Bz c|, fun c y j hj => (hBz c y j hj).trans (le_sum_abs_of Bz c)⟩ }

theorem weightsFlip_of_values_holds (hmir : MirrorEval) {C : Type} {nE nM : ℕ} (W : WeightValues C nE nM)
    (hW : IsWeightValues W) (epsMirror : Equiv.Perm (Fin nE)) (muMirror : Equiv.Perm (Fin nM))
    (hF : IsFlipClosedValues W epsMirror muMirror) (epsFrame : Fin nE → ℝ) (muFrame : Fin nM → ℝ)
    (epsSpeed : Fin nE → Space → ℝ) (muSpeed : Fin nM → Space → ℝ)
    (hef : ∀ β, epsFrame (epsMirror β) = -epsFrame β) (hmf : ∀ β, muFrame (muMirror β) = -muFrame β)
    (hes : ∀ β y, epsSpeed (epsMirror β) (flipPoint y) = epsSpeed β y)
    (hms : ∀ β y, muSpeed (muMirror β) (flipPoint y) = muSpeed β y) :
    WeightFlipClauses (W.pieces epsFrame muFrame epsSpeed muSpeed) := by
  have hM := hmir W.chart hW.chart_valid
  refine ⟨fun ξ y => ?_, fun ξ y => ?_, ⟨epsMirror, fun β => ⟨?_, hef β, fun y => ⟨?_, hes β y, fun hy => ?_⟩⟩⟩,
    ⟨muMirror, fun β => ⟨?_, hmf β, ?_, fun y => ⟨?_, hms β y, fun hy => ?_⟩⟩⟩⟩
  · show (W.strainWeight (W.classOf (flipLabel ξ))).eval W.chart (flipPoint y)
      = (W.strainWeight (W.classOf ξ)).eval W.chart y
    rw [hF.strain_flip ξ]
    exact hM.1 _ (joinedScalar_zero_of_two (hW.strain_joined _)) y
  · show (W.vorticityWeight (W.classOf (flipLabel ξ))).eval W.chart (flipPoint y)
      = (W.vorticityWeight (W.classOf ξ)).eval W.chart y
    rw [hF.vorticity_flip ξ]
    exact hM.1 _ (joinedScalar_zero_of_two (hW.vorticity_joined _)) y
  · show (W.eps (epsMirror β)).modes = flipLabel '' (W.eps β).modes
    rw [hF.eps_flip β]
    rfl
  · show (W.eps (epsMirror β)).weight.eval W.chart (flipPoint y) = (W.eps β).weight.eval W.chart y
    rw [hF.eps_flip β]
    exact hM.1 _ (hW.eps_joined β) y
  · show (W.eps (epsMirror β)).share1.eval W.chart (flipPoint y) = (W.eps β).share1.eval W.chart y
      ∧ (W.eps (epsMirror β)).share2.eval W.chart (flipPoint y) = (W.eps β).share2.eval W.chart y
      ∧ (W.eps (epsMirror β)).len.eval W.chart (flipPoint y) = (W.eps β).len.eval W.chart y
      ∧ (W.eps (epsMirror β)).t0.eval W.chart (flipPoint y) = (W.eps β).t0.eval W.chart y
      ∧ (W.eps (epsMirror β)).t1.eval W.chart (flipPoint y) = (W.eps β).t1.eval W.chart y
      ∧ (W.eps (epsMirror β)).t2.eval W.chart (flipPoint y) = (W.eps β).t2.eval W.chart y
      ∧ (W.eps (epsMirror β)).t3.eval W.chart (flipPoint y) = (W.eps β).t3.eval W.chart y
      ∧ (W.eps (epsMirror β)).scale.eval W.chart (flipPoint y) = (W.eps β).scale.eval W.chart y
    rw [hF.eps_flip β]
    exact ⟨hM.2 _ y hy, hM.2 _ y hy, hM.2 _ y hy, hM.2 _ y hy, hM.2 _ y hy, hM.2 _ y hy, hM.2 _ y hy,
      hM.2 _ y hy⟩
  · show (W.mu (muMirror β)).modes = flipLabel '' (W.mu β).modes
    rw [hF.mu_flip β]
    rfl
  · show (W.mu (muMirror β)).eta = (W.mu β).eta
    rw [hF.mu_flip β]
    rfl
  · show (W.mu (muMirror β)).weight.eval W.chart (flipPoint y) = (W.mu β).weight.eval W.chart y
    rw [hF.mu_flip β]
    exact hM.1 _ (hW.mu_joined β) y
  · show (W.mu (muMirror β)).share.eval W.chart (flipPoint y) = (W.mu β).share.eval W.chart y
      ∧ (W.mu (muMirror β)).t4.eval W.chart (flipPoint y) = (W.mu β).t4.eval W.chart y
    rw [hF.mu_flip β]
    exact ⟨hM.2 _ y hy, hM.2 _ y hy⟩

theorem weightInstance_clauses_holds (hsm : ScalarSmoothOfJoins) (hdec : ScalarDerivativeDecay)
    (hlip : ScalarSlopeBoundOfJoins) (hrate : ScalarRateOfDecay) (hbas : ScalarBasicFacts)
    (hstep : StepBasicFacts) (hmir : MirrorEval) {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (W : WeightValues C nE nM) (epsFrame : (Fin k → ℝ) → Fin nE → ℝ) (muFrame : (Fin k → ℝ) → Fin nM → ℝ)
    (epsSpeed : Fin nE → Space → ℝ) (muSpeed : Fin nM → Space → ℝ)
    (epsMirror : Equiv.Perm (Fin nE)) (muMirror : Equiv.Perm (Fin nM))
    (h : IsWeightInstance D W epsFrame muFrame epsSpeed muSpeed epsMirror muMirror) :
    ∀ q ∈ D.cert.params, AdmissibleWeightClauses (D.pieces q) ∧ WeightFlipClauses (D.pieces q) ∧
      (D.pieces q).c = D.coercivity := by
  intro q hq
  rw [h.pieces_eq q hq]
  exact ⟨weightClauses_of_values_holds hsm hdec hlip hrate hbas hstep W h.values _ _ _ _,
    weightsFlip_of_values_holds hmir W h.values epsMirror muMirror h.flip _ _ _ _ (h.eps_frame_flip q)
      (h.mu_frame_flip q) h.eps_speed_flip h.mu_speed_flip, h.c_eq⟩

end Instance

end CertCell

end Breakdown
