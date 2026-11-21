import Breakdown.CertCell.AssemblyRowExpansionRestGram
import Breakdown.CertCell.TailAngularPlane
import Breakdown.Cert.CoerciveModeL2
import Breakdown.Cert.CoerciveSmoothMuDecay
import Breakdown.Cert.CoerciveBase

open MeasureTheory Matrix
open scoped ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

namespace ActuatorPiece

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

theorem rot_coord_abs_le (φ : ℝ) (x : Space) (c : Fin 3) : |axialRot (-φ) x c| ≤ ‖x‖ := by
  have h := PiLp.norm_apply_le (axialRot (-φ) x) c
  rw [Real.norm_eq_abs, Coercive.BaseDensityInternal.norm_axialRot] at h
  exact h

theorem labelVel_norm_le (m : ℕ) (ι : ℤ × ℤ) {b : ℝ → Space → Space} {B : ℝ} (hb : ∀ σ y, ‖b σ y‖ ≤ B)
    (p : ℝ × ℝ) (c : Fin 3) : ‖labelVel m ι b p c‖ ≤ B := by
  unfold labelVel modeVel
  exact Coercive.Internal.MuSmooth.Decay.modeAverage_norm_le _ _ _
    (fun τ φ => (rot_coord_abs_le φ _ c).trans (hb _ _))

theorem rect_ae_le_halfPlane {K : CellBox} (hK : IsCellBox K) : K.rect ≤ᵐ[volume] halfPlane := by
  rw [ae_le_set]
  have hsub : K.rect \ halfPlane ⊆ ({0} ×ˢ Set.univ) ∪ (Set.univ ×ˢ {0}) := by
    rintro ⟨r, z⟩ ⟨hp, hn⟩
    have hr : 0 ≤ r := hK.r_order.1.trans hp.1.1
    have hz : 0 ≤ z := hK.z_order.1.trans hp.2.1
    by_cases h0 : r = 0
    · exact Or.inl ⟨h0, trivial⟩
    · refine Or.inr ⟨trivial, ?_⟩
      by_contra hz0
      exact hn ⟨lt_of_le_of_ne hr (Ne.symm h0), lt_of_le_of_ne hz (Ne.symm hz0)⟩
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

theorem labelVel_aesm_rect (m : ℕ) (ι : ℤ × ℤ) {b : ℝ → Space → Space}
    (hb : AEStronglyMeasurable (fun z : ℝ × Space => b z.1 z.2) volume) {K : CellBox} (hK : IsCellBox K)
    (c : Fin 3) : AEStronglyMeasurable (fun p => labelVel m ι b p c) (volume.restrict K.rect) := by
  have h := (TailBand.Internal.AngularPlane.aestronglyMeasurable_orbitAverage hb (labelHarmonic m ι)
    (fun φ x => axialRot (-φ) x c) (Coercive.ModeL2Internal.continuous_rotCoord c)).const_mul
      (1 / (2 * Real.pi) : ℂ)
  have hac : volume.restrict K.rect ≪ volume.restrict halfPlane :=
    (Measure.restrict_mono_ae (rect_ae_le_halfPlane hK)).absolutelyContinuous
  refine (h.mono_ac hac).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [labelVel, modeVel, modeAverage, Coercive.Internal.ModeRotation.expFactor, zero_add]

theorem weighted_sq_integrableOn {K : CellBox} {g : ℝ × ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict K.rect)) {B : ℝ} (hB : ∀ p, ‖g p‖ ≤ B) :
    IntegrableOn (fun p => p.1 * ‖g p‖ ^ 2) K.rect := by
  refine Integrable.mono' (integrableOn_rect_of_continuous (K := K)
    (g := fun p : ℝ × ℝ => |p.1| * B ^ 2) (by fun_prop)) ?_ ?_
  · exact continuous_fst.aestronglyMeasurable.mul (hg.norm.pow 2)
  · refine Filter.Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖g p‖ ^ 2)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hB p) 2) (abs_nonneg _)

theorem norm_sum_smul_sq_le {n : Type*} (s : Finset n) (κ : n → ℝ) (d : n → ℂ) :
    ‖∑ l ∈ s, (κ l : ℂ) * d l‖ ^ 2 ≤ (∑ l ∈ s, κ l ^ 2) * ∑ l ∈ s, ‖d l‖ ^ 2 := by
  have h1 : ‖∑ l ∈ s, (κ l : ℂ) * d l‖ ≤ ∑ l ∈ s, |κ l| * ‖d l‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun l _ => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun l => |κ l|) (fun l => ‖d l‖)
  have h3 : ∑ l ∈ s, |κ l| ^ 2 = ∑ l ∈ s, κ l ^ 2 := Finset.sum_congr rfl fun l _ => sq_abs _
  rw [h3] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem weighted_combo_le {n : Type*} [Fintype n] (κ : n → ℝ) (a b : n → Fin 3 → ℂ) {w : ℝ} (hw : 0 ≤ w) :
    w * ∑ c, ‖∑ l, (κ l : ℂ) * (a l c - b l c)‖ ^ 2
      ≤ (∑ l, κ l ^ 2) * (w * ∑ l, ∑ c, ‖a l c - b l c‖ ^ 2) := by
  have h : ∀ c, ‖∑ l, (κ l : ℂ) * (a l c - b l c)‖ ^ 2 ≤ (∑ l, κ l ^ 2) * ∑ l, ‖a l c - b l c‖ ^ 2 :=
    fun c => norm_sum_smul_sq_le Finset.univ κ (fun l => a l c - b l c)
  have h2 := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => h c)
  rw [← Finset.mul_sum, Finset.sum_comm] at h2
  calc w * ∑ c, ‖∑ l, (κ l : ℂ) * (a l c - b l c)‖ ^ 2
      ≤ w * ((∑ l, κ l ^ 2) * ∑ l, ∑ c, ‖a l c - b l c‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hw
    _ = (∑ l, κ l ^ 2) * (w * ∑ l, ∑ c, ‖a l c - b l c‖ ^ 2) := by ring

theorem weighted_diff_le {n : Type*} [Fintype n] (a b : n → Fin 3 → ℂ) {w : ℝ} (hw : 0 ≤ w) :
    w * ∑ l, ∑ c, ‖a l c - b l c‖ ^ 2
      ≤ ∑ l, ∑ c, (2 * (w * ‖a l c‖ ^ 2) + 2 * (w * ‖b l c‖ ^ 2)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  have := mul_le_mul_of_nonneg_left (norm_sub_sq_le_two (a l c) (b l c)) hw
  linarith

section Main

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

def actDiff (A : AssemblyEntry D R) (K : Fin D.mesh.count) (κ : Fin k → ℝ) (ℓ : ℤ × ℤ) (p : ℝ × ℝ) (c : Fin 3) : ℂ :=
  if ℓ ∈ (A.blocks K).actuatorRows then ∑ l, (κ l : ℂ) *
    (labelVel D.azimuthOrder ℓ (D.cert.actuator l) p c
      - labelVel D.azimuthOrder ℓ ((A.blocks K).actuatorModel (l : ℕ)) p c)
  else 0

theorem piece_eq (A : AssemblyEntry D R) (K : Fin D.mesh.count) (hK : IsCellBox (D.mesh.box K)) (κ : Fin k → ℝ)
    (hoff : ∀ i, (A.blocks K).rowLabel i ∉ (A.blocks K).actuatorRows → ∀ l,
      actuatorRow D K ((A.blocks K).rowLabel i) (rowTestPoly D K (A.blocks K) i) (D.cert.actuator l)
        = actuatorRow D K ((A.blocks K).rowLabel i) (rowTestPoly D K (A.blocks K) i)
          ((A.blocks K).actuatorModel (l : ℕ)))
    (hAm : ∀ (l : Fin k) ℓ c, AEStronglyMeasurable (fun p => labelVel D.azimuthOrder ℓ (D.cert.actuator l) p c)
      (volume.restrict (D.mesh.box K).rect))
    (hAi : ∀ (l : Fin k) ℓ c, IntegrableOn
      (fun p => p.1 * ‖labelVel D.azimuthOrder ℓ (D.cert.actuator l) p c‖ ^ 2) (D.mesh.box K).rect)
    (hMm : ∀ (l : Fin k) ℓ c, AEStronglyMeasurable
      (fun p => labelVel D.azimuthOrder ℓ ((A.blocks K).actuatorModel (l : ℕ)) p c)
      (volume.restrict (D.mesh.box K).rect))
    (hMi : ∀ (l : Fin k) ℓ c, IntegrableOn
      (fun p => p.1 * ‖labelVel D.azimuthOrder ℓ ((A.blocks K).actuatorModel (l : ℕ)) p c‖ ^ 2) (D.mesh.box K).rect)
    (i : Fin (A.blocks K).rowCount) :
    actuatorPiece D K (A.blocks K) κ i = ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) *
      ∑ c, actDiff D R A K κ ((A.blocks K).rowLabel i) p c * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p c) := by
  classical
  by_cases hrow : (A.blocks K).rowLabel i ∈ (A.blocks K).actuatorRows
  · have hint : ∀ b : ℝ → Space → Space,
        (∀ c, AEStronglyMeasurable (fun p => labelVel D.azimuthOrder ((A.blocks K).rowLabel i) b p c)
          (volume.restrict (D.mesh.box K).rect)) →
        (∀ c, IntegrableOn (fun p => p.1 * ‖labelVel D.azimuthOrder ((A.blocks K).rowLabel i) b p c‖ ^ 2)
          (D.mesh.box K).rect) →
        ∀ c, Integrable (fun p : ℝ × ℝ => (p.1 : ℂ) * (labelVel D.azimuthOrder ((A.blocks K).rowLabel i) b p c
          * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p c))) (volume.restrict (D.mesh.box K).rect) :=
      fun b hm hi c => integrable_weight_mul_conj (w := fun p : ℝ × ℝ => p.1) (ae_rect_first_nonneg hK)
        continuous_fst.aestronglyMeasurable (hm c) (rowTestValue_continuous D K (A.blocks K) i c).aestronglyMeasurable
        (hi c) (integrableOn_rect_of_continuous
          (continuous_fst.mul ((rowTestValue_continuous D K (A.blocks K) i c).norm.pow 2)))
    have eRow : ∀ b : ℝ → Space → Space,
        (∀ c, Integrable (fun p : ℝ × ℝ => (p.1 : ℂ) * (labelVel D.azimuthOrder ((A.blocks K).rowLabel i) b p c
          * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p c))) (volume.restrict (D.mesh.box K).rect)) →
        actuatorRow D K ((A.blocks K).rowLabel i) (rowTestPoly D K (A.blocks K) i) b
          = ∑ c, ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * (labelVel D.azimuthOrder ((A.blocks K).rowLabel i) b p c
            * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p c)) := by
      intro b hb
      rw [← integral_finsetSum _ (fun c _ => hb c)]
      unfold actuatorRow
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp only [Finset.mul_sum, rowTestValue]
    have hX : ∀ (l : Fin k) c, Integrable (fun p : ℝ × ℝ => (p.1 : ℂ) *
        (labelVel D.azimuthOrder ((A.blocks K).rowLabel i) (D.cert.actuator l) p c
          * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p c))) (volume.restrict (D.mesh.box K).rect) :=
      fun l => hint _ (hAm l _) (hAi l _)
    have hY : ∀ (l : Fin k) c, Integrable (fun p : ℝ × ℝ => (p.1 : ℂ) *
        (labelVel D.azimuthOrder ((A.blocks K).rowLabel i) ((A.blocks K).actuatorModel (l : ℕ)) p c
          * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p c))) (volume.restrict (D.mesh.box K).rect) :=
      fun l => hint _ (hMm l _) (hMi l _)
    calc actuatorPiece D K (A.blocks K) κ i
        = ∑ l, ∑ c, ∫ p in (D.mesh.box K).rect, (κ l : ℂ) *
            ((p.1 : ℂ) * (labelVel D.azimuthOrder ((A.blocks K).rowLabel i) (D.cert.actuator l) p c
                * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p c))
              - (p.1 : ℂ) * (labelVel D.azimuthOrder ((A.blocks K).rowLabel i) ((A.blocks K).actuatorModel (l : ℕ)) p c
                * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p c))) := by
          simp only [actuatorPiece]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [eRow _ (hX l), eRow _ (hY l), ← Finset.sum_sub_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [integral_const_mul, integral_sub (hX l c) (hY l c)]
      _ = ∫ p in (D.mesh.box K).rect, ∑ l, ∑ c, (κ l : ℂ) *
            ((p.1 : ℂ) * (labelVel D.azimuthOrder ((A.blocks K).rowLabel i) (D.cert.actuator l) p c
                * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p c))
              - (p.1 : ℂ) * (labelVel D.azimuthOrder ((A.blocks K).rowLabel i) ((A.blocks K).actuatorModel (l : ℕ)) p c
                * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p c))) := by
          have hZ : ∀ (l : Fin k) c, Integrable (fun p : ℝ × ℝ => (κ l : ℂ) *
              ((p.1 : ℂ) * (labelVel D.azimuthOrder ((A.blocks K).rowLabel i) (D.cert.actuator l) p c
                  * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p c))
                - (p.1 : ℂ) * (labelVel D.azimuthOrder ((A.blocks K).rowLabel i) ((A.blocks K).actuatorModel (l : ℕ)) p c
                  * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p c)))) (volume.restrict (D.mesh.box K).rect) :=
            fun l c => ((hX l c).sub (hY l c)).const_mul _
          rw [integral_finsetSum]
          · refine Finset.sum_congr rfl fun l _ => ?_
            rw [integral_finsetSum]
            intro c _
            exact hZ l c
          · intro l _
            exact integrable_finsetSum _ fun c _ => hZ l c
      _ = _ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          simp only [actDiff, if_pos hrow]
          rw [Finset.mul_sum, Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
  · have h0 : actuatorPiece D K (A.blocks K) κ i = 0 := by
      simp only [actuatorPiece]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [hoff i hrow l, sub_self, mul_zero]
    have h1 : ∀ p : ℝ × ℝ, (p.1 : ℂ) * ∑ c, actDiff D R A K κ ((A.blocks K).rowLabel i) p c
        * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p c) = 0 := fun p => by
      simp [actDiff, hrow]
    rw [h0]
    simp only [h1, integral_zero]

theorem actDiff_weighted_le (A : AssemblyEntry D R) (K : Fin D.mesh.count) (κ : Fin k → ℝ) (ℓ : ℤ × ℤ)
    (p : ℝ × ℝ) (hp : 0 ≤ p.1) :
    p.1 * ∑ c, ‖actDiff D R A K κ ℓ p c‖ ^ 2 ≤ (∑ l, κ l ^ 2) * (p.1 * ∑ l, ∑ c,
      ‖labelVel D.azimuthOrder ℓ (D.cert.actuator l) p c
        - labelVel D.azimuthOrder ℓ ((A.blocks K).actuatorModel (l : ℕ)) p c‖ ^ 2) := by
  classical
  by_cases h : ℓ ∈ (A.blocks K).actuatorRows
  · simp only [actDiff, if_pos h]
    exact weighted_combo_le κ (fun l c => labelVel D.azimuthOrder ℓ (D.cert.actuator l) p c)
      (fun l c => labelVel D.azimuthOrder ℓ ((A.blocks K).actuatorModel (l : ℕ)) p c) hp
  · simp only [actDiff, if_neg h, norm_zero]
    have h2 : (0 : ℝ) ≤ (∑ l, κ l ^ 2) * (p.1 * ∑ l, ∑ c,
        ‖labelVel D.azimuthOrder ℓ (D.cert.actuator l) p c
          - labelVel D.azimuthOrder ℓ ((A.blocks K).actuatorModel (l : ℕ)) p c‖ ^ 2) :=
      mul_nonneg (Finset.sum_nonneg fun l _ => sq_nonneg _)
        (mul_nonneg hp (Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun c _ => sq_nonneg _))
    simpa using h2

end Main

end ActuatorPiece

end Internal

open Breakdown.CertCell.Assembly.Internal Breakdown.CertCell.Assembly.Internal.ActuatorPiece
open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

theorem actuatorPieceBound_holds : ActuatorPieceBoundHolds := by
  intro k C nE nM D R A P states hstates hAR _hTF hC hF K q v G H g κ F Pg _hT
  classical
  have hK : IsCellBox (D.mesh.box K) := hC.mesh_valid.box_valid K
  have hAm : ∀ (l : Fin k) ℓ c, AEStronglyMeasurable
      (fun p => labelVel D.azimuthOrder ℓ (D.cert.actuator l) p c) (volume.restrict (D.mesh.box K).rect) := by
    intro l ℓ c
    obtain ⟨S, hS⟩ := hAR.field.actuators l
    exact labelVel_aesm_rect _ _ hS.measurable hK c
  have hAi : ∀ (l : Fin k) ℓ c, IntegrableOn
      (fun p => p.1 * ‖labelVel D.azimuthOrder ℓ (D.cert.actuator l) p c‖ ^ 2) (D.mesh.box K).rect := by
    intro l ℓ c
    obtain ⟨S, hS⟩ := hAR.field.actuators l
    obtain ⟨Bd, Rd, hBd⟩ := hS.bounded_support
    exact weighted_sq_integrableOn (hAm l ℓ c) (fun p => labelVel_norm_le _ _ (fun σ y => (hBd σ y).1) p c)
  have hMm : ∀ (l : Fin k) ℓ c, AEStronglyMeasurable
      (fun p => labelVel D.azimuthOrder ℓ ((A.blocks K).actuatorModel (l : ℕ)) p c)
      (volume.restrict (D.mesh.box K).rect) :=
    fun l ℓ c => (hF.actuator_model_regular K (l : ℕ) ℓ c).1
  have hMi : ∀ (l : Fin k) ℓ c, IntegrableOn
      (fun p => p.1 * ‖labelVel D.azimuthOrder ℓ ((A.blocks K).actuatorModel (l : ℕ)) p c‖ ^ 2)
      (D.mesh.box K).rect :=
    fun l ℓ c => (hF.actuator_model_regular K (l : ℕ) ℓ c).2
  have hcost : 0 < (A.blocks K).actuatorCost := (hF.actuator_pos K).1
  have hfm0 : ∀ ℓ a, AEStronglyMeasurable (fun p => actDiff D R A K κ ℓ p a)
      (volume.restrict (D.mesh.box K).rect) := by
    intro ℓ a
    by_cases h : ℓ ∈ (A.blocks K).actuatorRows
    · simp only [actDiff, if_pos h]
      exact Finset.aestronglyMeasurable_fun_sum _ fun l _ =>
        aestronglyMeasurable_const.mul ((hAm l ℓ a).sub (hMm l ℓ a))
    · simp only [actDiff, if_neg h]
      exact aestronglyMeasurable_const
  have hdom : ∀ ℓ, Integrable (fun p : ℝ × ℝ => ∑ l, ∑ c,
      (2 * (p.1 * ‖labelVel D.azimuthOrder ℓ (D.cert.actuator l) p c‖ ^ 2)
        + 2 * (p.1 * ‖labelVel D.azimuthOrder ℓ ((A.blocks K).actuatorModel (l : ℕ)) p c‖ ^ 2)))
      (volume.restrict (D.mesh.box K).rect) :=
    fun ℓ => integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun c _ =>
      ((hAi l ℓ c).const_mul 2).add ((hMi l ℓ c).const_mul 2)
  have hdiff : ∀ ℓ, Integrable (fun p : ℝ × ℝ => p.1 * ∑ l, ∑ c,
      ‖labelVel D.azimuthOrder ℓ (D.cert.actuator l) p c
        - labelVel D.azimuthOrder ℓ ((A.blocks K).actuatorModel (l : ℕ)) p c‖ ^ 2)
      (volume.restrict (D.mesh.box K).rect) := by
    intro ℓ
    refine Integrable.mono' (hdom ℓ) ?_ ?_
    · exact continuous_fst.aestronglyMeasurable.mul (Finset.aestronglyMeasurable_fun_sum _ fun l _ =>
        Finset.aestronglyMeasurable_fun_sum _ fun c _ => ((hAm l ℓ c).sub (hMm l ℓ c)).norm.pow 2)
    · filter_upwards [ae_rect_first_nonneg hK] with p hp
      rw [Real.norm_of_nonneg (mul_nonneg hp
        (Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun c _ => sq_nonneg _))]
      exact weighted_diff_le (fun l c => labelVel D.azimuthOrder ℓ (D.cert.actuator l) p c)
        (fun l c => labelVel D.azimuthOrder ℓ ((A.blocks K).actuatorModel (l : ℕ)) p c) hp
  have hfi : ∀ ℓ ∈ D.mesh.tested K, ∀ a, IntegrableOn (fun p => p.1 * ‖actDiff D R A K κ ℓ p a‖ ^ 2)
      (D.mesh.box K).rect := by
    intro ℓ _ a
    refine Integrable.mono' ((hdiff ℓ).const_mul (∑ l, κ l ^ 2)) ?_ ?_
    · exact continuous_fst.aestronglyMeasurable.mul ((hfm0 ℓ a).norm.pow 2)
    · filter_upwards [ae_rect_first_nonneg hK] with p hp
      rw [Real.norm_of_nonneg (mul_nonneg hp (sq_nonneg _))]
      have h1 : ‖actDiff D R A K κ ℓ p a‖ ^ 2 ≤ ∑ c, ‖actDiff D R A K κ ℓ p c‖ ^ 2 :=
        Finset.single_le_sum (fun c _ => sq_nonneg ‖actDiff D R A K κ ℓ p c‖) (Finset.mem_univ a)
      exact (mul_le_mul_of_nonneg_left h1 hp).trans (actDiff_weighted_le D R A K κ ℓ p hp)
  have hpiece := piece_eq D R A K hK κ (hF.actuator_off_rows K) hAm hAi hMm hMi
  have hb := inverseWeightedSq_scaled_rows_le D R A hC K (fun _ => (A.blocks K).actuatorCost) (fun _ _ => hcost)
    (actDiff D R A K κ) (fun ℓ _ => hfm0 ℓ) hfi (actuatorPiece D K (A.blocks K) κ) hpiece
  refine hb.trans ?_
  have hI0 : ∀ ℓ, ℓ ∉ (A.blocks K).actuatorRows →
      ∫ p in (D.mesh.box K).rect, p.1 * ∑ a, ‖actDiff D R A K κ ℓ p a‖ ^ 2 = 0 := by
    intro ℓ h
    simp [actDiff, h]
  have hIJ : ∀ ℓ, ∫ p in (D.mesh.box K).rect, p.1 * ∑ a, ‖actDiff D R A K κ ℓ p a‖ ^ 2
      ≤ (∑ l, κ l ^ 2) * ∫ p in (D.mesh.box K).rect, p.1 * ∑ l, ∑ c,
        ‖labelVel D.azimuthOrder ℓ (D.cert.actuator l) p c
          - labelVel D.azimuthOrder ℓ ((A.blocks K).actuatorModel (l : ℕ)) p c‖ ^ 2 := by
    intro ℓ
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg ?_ ((hdiff ℓ).const_mul _) ?_
    · filter_upwards [ae_rect_first_nonneg hK] with p hp
      exact mul_nonneg hp (Finset.sum_nonneg fun c _ => sq_nonneg _)
    · filter_upwards [ae_rect_first_nonneg hK] with p hp
      exact actDiff_weighted_le D R A K κ ℓ p hp
  have hJ0 : ∀ ℓ, 0 ≤ ∫ p in (D.mesh.box K).rect, p.1 * ∑ l, ∑ c,
      ‖labelVel D.azimuthOrder ℓ (D.cert.actuator l) p c
        - labelVel D.azimuthOrder ℓ ((A.blocks K).actuatorModel (l : ℕ)) p c‖ ^ 2 := by
    intro ℓ
    refine setIntegral_nonneg (rect_measurableSet _) fun p hp => ?_
    exact mul_nonneg (rect_first_nonneg hK hp)
      (Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun c _ => sq_nonneg _)
  have hk0 : 0 ≤ ∑ l, κ l ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  calc ∑ ℓ ∈ D.mesh.tested K, (A.blocks K).actuatorCost
        * ∫ p in (D.mesh.box K).rect, p.1 * ∑ a, ‖actDiff D R A K κ ℓ p a‖ ^ 2
      ≤ ∑ ℓ ∈ (D.mesh.tested K).filter (fun ℓ => ℓ ∈ (A.blocks K).actuatorRows),
          (A.blocks K).actuatorCost * ((∑ l, κ l ^ 2) * ∫ p in (D.mesh.box K).rect, p.1 * ∑ l, ∑ c,
            ‖labelVel D.azimuthOrder ℓ (D.cert.actuator l) p c
              - labelVel D.azimuthOrder ℓ ((A.blocks K).actuatorModel (l : ℕ)) p c‖ ^ 2) := by
        rw [Finset.sum_filter]
        refine Finset.sum_le_sum fun ℓ _ => ?_
        split_ifs with h
        · exact mul_le_mul_of_nonneg_left (hIJ ℓ) hcost.le
        · rw [hI0 ℓ h, mul_zero]
    _ ≤ ∑ ℓ ∈ (A.blocks K).actuatorRows,
          (A.blocks K).actuatorCost * ((∑ l, κ l ^ 2) * ∫ p in (D.mesh.box K).rect, p.1 * ∑ l, ∑ c,
            ‖labelVel D.azimuthOrder ℓ (D.cert.actuator l) p c
              - labelVel D.azimuthOrder ℓ ((A.blocks K).actuatorModel (l : ℕ)) p c‖ ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun ℓ hℓ => (Finset.mem_filter.1 hℓ).2)
          (fun ℓ _ _ => mul_nonneg hcost.le (mul_nonneg hk0 (hJ0 ℓ)))
    _ = (A.blocks K).actuatorCost * (∑ l, κ l ^ 2) * ∑ ℓ ∈ (A.blocks K).actuatorRows,
          ∫ p in (D.mesh.box K).rect, p.1 * ∑ l, ∑ c,
            ‖labelVel D.azimuthOrder ℓ (D.cert.actuator l) p c
              - labelVel D.azimuthOrder ℓ ((A.blocks K).actuatorModel (l : ℕ)) p c‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        ring
    _ ≤ (A.blocks K).actuatorCost * (∑ l, κ l ^ 2) * (A.blocks K).actuatorErr :=
        mul_le_mul_of_nonneg_left (hF.actuator_err K) (mul_nonneg hcost.le hk0)
    _ = (A.blocks K).actuatorCost * (A.blocks K).actuatorErr * ∑ l, κ l ^ 2 := by ring

end Assembly

end CertCell

end Breakdown
