import Breakdown.Uniqueness.Restrict
import Breakdown.Uniqueness.SmoothUniqueness
import Breakdown.Uniqueness.LocalBlowup

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

theorem agree_of_mildRegular {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] {Rlz : Realization X} {vel : X →L[ℝ] Lp (α := Space) Space 6}
    (hR : MildRegular Rlz vel) {φ : Space → Space} (hφ : IsTestField φ) {u : ℝ → X}
    (hu : Rlz.F.IsMildOn u 0 1) (hu0 : u 0 = Rlz.embed φ) {v : ℝ → Space → Space}
    {q : ℝ → Space → ℝ} (hv : IsSmoothSolution 1 φ v q) (hE : HasBoundedEnergy v) :
    ∀ t ∈ Ico (0 : ℝ) 1, (vel (u t) : Space → Space) =ᵐ[volume] v t := by
  intro t ht
  have hT0 : (0 : ℝ) < (t + 1) / 2 := by linarith [ht.1]
  have hT1 : (t + 1) / 2 < 1 := by linarith [ht.2]
  have htT : t ∈ Icc 0 ((t + 1) / 2) := ⟨ht.1, by linarith [ht.2]⟩
  have hmild := Rlz.F.isMildOnIcc_of_isMildOn hu hT0.le hT1
  obtain ⟨U, P, hUs, hU0, hUE, hUB, hUv⟩ := hR φ hφ u ((t + 1) / 2) hT0 hmild hu0
  have hvs := isSolutionOn_of_isSmoothSolution hv hφ.2.2 ((t + 1) / 2)
  have h0 : U 0 = v 0 := by
    rw [hU0]
    funext x
    exact (hv.initial x).symm
  have heq := eq_of_isSolutionOn hUs hvs hUE (energyBoundedOn_of_hasBoundedEnergy hE _) hUB h0
  rw [← heq t htT]
  exact hUv t htT

theorem noBoundedSmoothSolution_of_exports (hT : TransferHolds) (hP : ProfileOrbitHolds)
    {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (Rlz : Realization X) (vel : X →L[ℝ] Lp (α := Space) Space 6) (hF : FieldReading Rlz vel)
    (hR : MildRegular Rlz vel) (hW : PeriodicSimilarityProfileExists) :
    ∃ u₀ : Space → Space, ContDiff ℝ ∞ u₀ ∧ HasCompactSupport u₀ ∧
      (∀ x, divergenceAt u₀ x = 0) ∧ NoBoundedSmoothSolution 1 u₀ := by
  obtain ⟨φ, hφ, u, w, P, R, C, κ, hu, hu0, hw, hκ, hrate⟩ := exists_blowup_datum hT hP Rlz hW
  refine ⟨φ, hφ.1, hφ.2.1, hφ.2.2, ?_⟩
  rintro ⟨v, q, hv, hE⟩
  have hcont : ContinuousOn (fun z : ℝ × Space => v z.1 z.2) (Icc 0 1 ×ˢ univ) :=
    hv.smooth_velocity.continuousOn.mono (Set.prod_mono Icc_subset_Ici_self Subset.rfl)
  exact false_of_orbit_rate hF hw hκ hrate hcont (agree_of_mildRegular hR hφ hu hu0 hv hE)

end Breakdown
