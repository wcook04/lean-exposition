import TorusEuler.EndpointConcreteProjection
import TorusEuler.HalfHolderMultiplierUniform

/-! The mixed half-Hölder Leray bound uniform in the time slab. -/

open ContinuousLinearMap MeasureTheory Set UnitAddTorus
open scoped ContDiff

namespace TorusEuler

noncomputable section

local instance uniformLerayCircleMeasure : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance uniformLerayCircleHaar :
    (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance uniformLerayCircleProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The path-valued Leray projection in the spatial half-Hölder norm has a
bound independent of the length of the time slab. -/
theorem exists_norm_endpointStrongMixedLeray_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T → ‖endpointStrongMixedLeray T‖ ≤ C := by
  obtain ⟨L, hL, hMass⟩ := exists_annularLocalize_mass_universal_le
    dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero
  obtain ⟨K, hK, hNorm⟩ := exists_norm_universal_homogeneousHalfHolderMultiplier_le_mass
    dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero
  obtain ⟨J, hJ, _, hTime⟩ := exists_angularProjection_annular_fiveJets
  let C := K * (L * J ^ 5) + 1
  have hJ₀ : 0 ≤ J := zero_le_one.trans hJ
  refine ⟨C, by dsimp [C]; positivity, fun T hT => ?_⟩
  let X := endpointL2Complexification (volume.restrict (Ioc 0 T))
  let A := X.extendOperatorCLM ∘ angularTimeLeray T
  let s : Set Vec3 := {0}ᶜ
  have hs : IsOpen s := isOpen_compl_singleton
  have hA : ContDiffOn ℝ ∞ A s :=
    X.extendOperatorCLM.contDiff.comp_contDiffOn (contDiffOn_angularTimeLeray T)
  have hOp : ‖X.extendOperatorCLM‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro B
    rw [X.extendOperatorCLM_apply, X.norm_extendOperator, one_mul]
  have hJet (n : ℕ) (hn : n ≤ 5) (ξ : Vec3) (hlo : 1 / 2 ≤ ‖ξ‖) :
      ‖iteratedFDeriv ℝ n A ξ‖ ≤ J ^ 5 := by
    have hξ : ξ ∈ s := norm_pos_iff.mp ((by norm_num : 0 < (1 / 2 : ℝ)).trans_le hlo)
    have hAt : ContDiffAt ℝ n (angularTimeLeray T) ξ :=
      ((contDiffOn_angularTimeLeray (n := ∞) T).contDiffAt (hs.mem_nhds hξ)).of_le (by simp)
    calc
      _ ≤ ‖X.extendOperatorCLM‖ * ‖iteratedFDeriv ℝ n (angularTimeLeray T) ξ‖ :=
        X.extendOperatorCLM.norm_iteratedFDeriv_comp_left hAt le_rfl
      _ ≤ ‖iteratedFDeriv ℝ n (angularTimeLeray T) ξ‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hOp
      _ ≤ J ^ n := hTime T hT n hn ξ hlo
      _ ≤ J ^ 5 := pow_le_pow_right₀ hJ hn
  have hm : multiplierDerivativeMass (annularLocalize dyadicMultiplierCutoff A) ≤ L * J ^ 5 :=
    hMass hA (pow_nonneg hJ₀ _) (fun n hn ξ hlo _ => hJet n hn ξ hlo)
  have hz : ‖A 0‖ ≤ 1 := by
    change ‖X.extendOperator (angularTimeLeray T 0)‖ ≤ 1
    rw [X.norm_extendOperator]
    exact (isStarProjection_iff_isSymmetricProjection.mpr
      (angularTimeLeray_isSymmetricProjection hT 0)).norm_le
  change ‖realHomogeneousHalfHolderMultiplier X hA‖ ≤ C
  unfold realHomogeneousHalfHolderMultiplier
  refine (norm_realifyHalfHolderMultiplier_le X _).trans ((hNorm hA).trans ?_)
  exact add_le_add (mul_le_mul_of_nonneg_left hm hK) hz

end

end TorusEuler
