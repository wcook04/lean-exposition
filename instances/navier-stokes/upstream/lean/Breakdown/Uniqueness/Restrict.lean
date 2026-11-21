import Breakdown.Uniqueness.Basic

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

theorem isSolutionOn_of_isSmoothSolution {u₀ : Space → Space} {v : ℝ → Space → Space}
    {q : ℝ → Space → ℝ} (hv : IsSmoothSolution 1 u₀ v q) (hdiv : ∀ x, divergenceAt u₀ x = 0)
    (T : ℝ) : IsSolutionOn T v q := by
  have hsub : Icc (0 : ℝ) T ×ˢ (univ : Set Space) ⊆ Ici 0 ×ˢ univ :=
    prod_mono Icc_subset_Ici_self subset_rfl
  refine ⟨hv.smooth_velocity.mono hsub, hv.smooth_pressure.mono hsub, ?_, ?_⟩
  · intro t ht x
    have h := hv.momentum t ht.1 x
    rwa [one_smul] at h
  · intro t ht x
    rcases eq_or_lt_of_le ht.1 with h0 | hpos
    · subst h0
      have hfun : v 0 = u₀ := funext hv.initial
      rw [hfun]
      exact hdiv x
    · exact hv.incompressible t hpos x

theorem energyBoundedOn_of_hasBoundedEnergy {v : ℝ → Space → Space} (h : HasBoundedEnergy v)
    (T : ℝ) : EnergyBoundedOn T v := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun t ht => hC t ht.1⟩

theorem MildFramework.isMildOnIcc_of_isMildOn {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] (F : MildFramework X) {u : ℝ → X} {a b T : ℝ}
    (h : F.IsMildOn u a b) (haT : a ≤ T) (hTb : T < b) : F.IsMildOnIcc u a T := by
  have hsub : Icc a T ⊆ Ico a b := Icc_subset_Ico_right hTb
  exact ⟨h.1.mono hsub, fun t ht => h.2 t (hsub ht)⟩

private theorem contDiff_slice_of_contDiffOn {T : ℝ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → Space → E}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Icc 0 T ×ˢ univ)) {t : ℝ}
    (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (f t) := by
  have hpair : ContDiff ℝ ∞ (fun x : Space => (t, x)) := contDiff_const.prodMk contDiff_id
  exact hf.comp_contDiff hpair (fun x => mk_mem_prod ht (mem_univ x))

theorem IsSolutionOn.contDiff_velocity {T : ℝ} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (h : IsSolutionOn T u p) {t : ℝ} (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (u t) :=
  contDiff_slice_of_contDiffOn h.smooth_velocity ht

theorem IsSolutionOn.contDiff_pressure {T : ℝ} {u : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (h : IsSolutionOn T u p) {t : ℝ} (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (p t) :=
  contDiff_slice_of_contDiffOn h.smooth_pressure ht

theorem exists_blowup_datum (hT : TransferHolds) (hP : ProfileOrbitHolds)
    {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (Rlz : Realization X) (hW : PeriodicSimilarityProfileExists) :
    ∃ φ, IsTestField φ ∧ ∃ (u w : ℝ → X) (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space) (C κ : ℝ),
      Rlz.F.IsMildOn u 0 1 ∧ u 0 = Rlz.embed φ ∧ Rlz.F.IsOrbit (Rlz.rot R) w P ∧ 0 < κ ∧
      ∀ t ∈ Ico (0 : ℝ) 1, ‖Rlz.F.D (1 - t) (u t) - w (-Real.log (1 - t))‖ ≤ C * (1 - t) ^ κ := by
  obtain ⟨w, P, R, hw⟩ := hP X Rlz hW
  obtain ⟨u, hu0, -, hmild, C, κ, hκ, hbound⟩ :=
    hT X Rlz.F (Rlz.rot R) (Rlz.rot_commutes R) w P hw Rlz.test Rlz.test_dense 1 one_pos
  obtain ⟨φ, hφ, hembed⟩ := Rlz.test_spec (u 0) hu0
  exact ⟨φ, hφ, u, w, P, R, C, κ, hmild, hembed.symm, hw, hκ, hbound⟩

end Breakdown
