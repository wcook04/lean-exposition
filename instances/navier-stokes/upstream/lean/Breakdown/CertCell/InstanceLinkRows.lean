import Breakdown.CertCell.InstanceStatements
import Breakdown.CertCell.InstanceLinkWeights
import Breakdown.CertCell.InstanceLinkActuators

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Instance

namespace Internal.LinkRows

theorem periodLIntegral_lt_top_of_le (g : ℝ → Space → ℝ) (C R : ℝ) (hg : ∀ σ y, g σ y ≤ C)
    (hs : ∀ σ y, R < ‖y‖ → g σ y ≤ 0) : periodLIntegral g < ⊤ := by
  unfold periodLIntegral
  have hin : ∀ σ, (∫⁻ y, ENNReal.ofReal (g σ y)) ≤
      ENNReal.ofReal C * volume (Metric.closedBall (0 : Space) R) := by
    intro σ
    rw [← lintegral_indicator_const Metric.isClosed_closedBall.measurableSet]
    refine lintegral_mono fun y => ?_
    by_cases hy : y ∈ Metric.closedBall (0 : Space) R
    · rw [Set.indicator_of_mem hy]
      exact ENNReal.ofReal_le_ofReal (hg σ y)
    · have hR : R < ‖y‖ := by
        simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy
      rw [ENNReal.ofReal_eq_zero.2 (hs σ y hR)]
      simp
  calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (g σ y))
      ≤ ∫⁻ _ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal C * volume (Metric.closedBall (0 : Space) R) :=
        lintegral_mono fun σ => hin σ
    _ = ENNReal.ofReal C * volume (Metric.closedBall (0 : Space) R) * volume (Set.Icc (0 : ℝ) 1) :=
        setLIntegral_const _ _
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top) ?_
        simp [Real.volume_Icc]

theorem rowField_regular (hreg : CellVecFieldRegular) {rowCount : ℕ} (M : CellMesh)
    (R : RowValues M.count rowCount) (m : ℕ) (hM : IsCellMesh M) (a : Fin rowCount) :
    AEStronglyMeasurable (fun z : ℝ × Space => R.rowFieldOf M.box m a z.1 z.2) volume ∧
    IsTimePeriodic (R.rowFieldOf M.box m a) ∧
    periodLIntegral (fun σ y => ‖R.rowFieldOf M.box m a σ y‖ ^ 2) < ⊤ := by
  have hg : ∀ b, AEStronglyMeasurable (fun z : ℝ × Space => R.generatorField M.box m b z.1 z.2) volume ∧
      IsTimePeriodic (R.generatorField M.box m b) ∧
      (∃ B Rb : ℝ, ∀ σ y, ‖R.generatorField M.box m b σ y‖ ≤ B ∧
        (Rb < ‖y‖ → R.generatorField M.box m b σ y = 0)) := fun b =>
    ⟨(hreg M (R.generator b) m hM).1, (hreg M (R.generator b) m hM).2.1, (hreg M (R.generator b) m hM).2.2.1⟩
  choose hmeas hper B Rb hB using hg
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.aestronglyMeasurable_fun_sum Finset.univ fun b _ => (hmeas b).const_smul (R.mix M.box m a b)
  · intro σ y
    simp only [RowValues.rowFieldOf]
    exact Finset.sum_congr rfl fun b _ => by rw [hper b σ y]
  · refine periodLIntegral_lt_top_of_le _ ((∑ b, |R.mix M.box m a b| * B b) ^ 2) (∑ b, |Rb b|) ?_ ?_
    · intro σ y
      have hle : ‖R.rowFieldOf M.box m a σ y‖ ≤ ∑ b, |R.mix M.box m a b| * B b := by
        simp only [RowValues.rowFieldOf]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hB b σ y).1 (abs_nonneg _)
      exact pow_le_pow_left₀ (norm_nonneg _) hle 2
    · intro σ y hy
      have hz : R.rowFieldOf M.box m a σ y = 0 := by
        simp only [RowValues.rowFieldOf]
        refine Finset.sum_eq_zero fun b _ => ?_
        have hb : Rb b < ‖y‖ := lt_of_le_of_lt ((le_abs_self _).trans
          (Finset.single_le_sum (f := fun j => |Rb j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ b))) hy
        rw [(hB b σ y).2 hb, smul_zero]
      rw [hz, norm_zero]
      norm_num

end Internal.LinkRows

open Internal.LinkRows

theorem rowInstance_clauses_holds (hreg : CellVecFieldRegular) (hpair : GeneratorPairingMatrixFormula)
    (hpd : RowPairingPosDef) (horth : RowFieldsOrthonormal) {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (tauMax : ℝ) (h : IsRowInstance D tauMax) :
    (∀ a, AEStronglyMeasurable (fun z : ℝ × Space => D.cert.rowField a z.1 z.2) volume) ∧
    (∀ a, IsTimePeriodic (D.cert.rowField a)) ∧
    (∀ a, periodLIntegral (fun σ y => ‖D.cert.rowField a σ y‖ ^ 2) < ⊤) ∧
    (∀ a b, periodPairing (D.cert.rowField a) (D.cert.rowField b) = if a = b then 1 else 0) ∧
    (∀ a, 0 ≤ D.cert.rowWeight a) ∧ (∀ a, D.cert.rowWeight a ≤ D.cert.rowBound ^ 2) := by
  have hM : IsCellMesh D.mesh := h.values.mesh_valid
  have hreg' := rowField_regular hreg D.mesh D.rows D.azimuthOrder hM
  have hG : (D.rows.fieldPairingMatrix D.mesh.box D.azimuthOrder).PosDef := by
    rw [hpair D.mesh D.rows D.azimuthOrder tauMax h.values]
    exact hpd D.mesh D.rows D.azimuthOrder tauMax h.values
  rw [h.rowField_eq, h.rowWeight_eq]
  exact ⟨fun a => (hreg' a).1, fun a => (hreg' a).2.1, fun a => (hreg' a).2.2,
    horth D.mesh D.rows D.azimuthOrder tauMax h.values hG,
    rowWeight_nonneg_of_values D.mesh D.rows h.values h.coercivity_pos,
    rowWeight_le_of_values D.mesh D.rows h.values h.coercivity_pos h.rowBound_ge⟩

theorem instanceConsequences_of_entry_of (hN : InstanceParts) {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM) (X : InstanceData k C nE nM) (h : IsInstanceEntry D X)
    (hact : ∀ q ∈ D.cert.params, ∀ i, ActuatorFacts (D.pieces q) (D.cert.actuator i))
    (hinv : ∀ i, ∀ γ ∈ D.cert.symmetries, ∀ᵐ z : ℝ × Space,
      D.cert.actuator i (z.1 + γ.2) (γ.1 z.2) = γ.1 (D.cert.actuator i z.1 z.2))
    (hpin : (∀ i, AEStronglyMeasurable (fun z : ℝ × Space => D.cert.pin i z.1 z.2) volume) ∧
      (∀ i, periodLIntegral (fun σ y => matSq (D.cert.pin i σ y)) < ⊤)) :
    InstanceConsequences D := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := rowInstance_clauses_holds hN.vec_regular hN.pairing_formula
    hN.pairing_posDef hN.orthonormal D X.rowWeightMax h.rows
  refine
    { rowField_measurable := h1
      rowField_periodic := h2
      rowField_finite := h3
      rowField_orthonormal := h4
      rowWeight_nonneg := h5
      rowWeight_le := h6
      rows_class_form := ?_
      weights := weightInstance_clauses_holds hN.smooth hN.derivative_decay hN.slope_bound hN.rate
        hN.scalar_basic hN.step_basic hN.mirror D X.weights X.epsFrame X.muFrame X.epsSpeed X.muSpeed
        X.epsMirror X.muMirror h.weights
      actuators := hact
      actuator_invariant := hinv
      pin_measurable := hpin.1
      pin_finite := hpin.2 }
  intro F hF1 hF2 hF3 hF4
  have hform := hN.class_form D.mesh D.rows D.azimuthOrder X.rowWeightMax D.coercivity h.rows.values
    h.rows.coercivity_pos F hF1 hF2 hF3 hF4
  simp only [ExtendedCertificateData.rows]
  rw [h.rows.rowField_eq, h.rows.rowWeight_eq]
  exact hform

theorem instanceConsequences_of_entry_holds (hN : InstanceParts) {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM) (X : InstanceData k C nE nM) (h : IsInstanceEntry D X)
    (hfmt : ∀ i, ActuatorShapeFacts D.azimuthOrder (X.actuatorModes i) (D.cert.actuator i)) :
    InstanceConsequences D :=
  instanceConsequences_of_entry_of hN D X h
    (fun q hq i => actuatorFacts_of_instance_holds D X.actuatorModes X.actuatorRange h.actuators hfmt q hq i)
    (actuatorInvariant_of_shape_holds D X.actuatorModes hfmt h.symmetries)
    (pinInstance_clauses_holds hN.mat_regular D h.pins)

end Instance

end CertCell

end Breakdown
