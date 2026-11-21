import Breakdown.CellReduction.InstanceStatements

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape

namespace Internal

theorem radialPhase_contDiffAt {f : ℝ → ℝ} {δ : ℝ} (hf : ContDiffOn ℝ 3 f (Set.Ioi (-δ)))
    (hδ : 0 < δ) {s : ℝ} (hs : 0 ≤ s) : ContDiffAt ℝ 3 f s :=
  hf.contDiffAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr (by linarith)))

theorem iteratedDeriv_combo {f g : ℝ → ℝ} {s : ℝ} (a : ℝ) (n : ℕ) (hn : n ≤ 3)
    (hf : ContDiffAt ℝ 3 f s) (hg : ContDiffAt ℝ 3 g s) :
    iteratedDeriv n (fun t => f t + a * g t) s = iteratedDeriv n f s + a * iteratedDeriv n g s := by
  have hle : ((n : ℕ) : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hn
  have hf' : ContDiffAt ℝ n f s := hf.of_le hle
  have hg' : ContDiffAt ℝ n (fun t => a * g t) s := contDiffAt_const.mul (hg.of_le hle)
  rw [iteratedDeriv_fun_add hf' hg', iteratedDeriv_const_mul_field]

theorem abs_combo_le {a u v B₁ B₂ : ℝ} (hu : |u| ≤ B₁) (hv : |v| ≤ B₂) :
    |u + a * v| ≤ B₁ + |a| * B₂ :=
  calc |u + a * v| ≤ |u| + |a * v| := abs_add_le _ _
    _ = |u| + |a| * |v| := by rw [abs_mul]
    _ ≤ B₁ + |a| * B₂ := add_le_add hu (mul_le_mul_of_nonneg_left hv (abs_nonneg a))

theorem radialPhase_combo {f g : ℝ → ℝ} (hf : IsRadialPhase f) (hg : IsRadialPhase g) (a : ℝ) :
    IsRadialPhase (fun s => f s + a * g s) := by
  obtain ⟨δ₁, hδ₁, hf₁⟩ := hf.smooth
  obtain ⟨δ₂, hδ₂, hg₁⟩ := hg.smooth
  obtain ⟨B₁, hB₁⟩ := hf.scaled_bounded
  obtain ⟨B₂, hB₂⟩ := hg.scaled_bounded
  have hsub₁ : Set.Ioi (-min δ₁ δ₂) ⊆ Set.Ioi (-δ₁) :=
    Set.Ioi_subset_Ioi (neg_le_neg (min_le_left _ _))
  have hsub₂ : Set.Ioi (-min δ₁ δ₂) ⊆ Set.Ioi (-δ₂) :=
    Set.Ioi_subset_Ioi (neg_le_neg (min_le_right _ _))
  refine ⟨⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, (hf₁.mono hsub₁).add (contDiffOn_const.mul (hg₁.mono hsub₂))⟩,
    ⟨B₁ + |a| * B₂, fun s hs => ?_⟩⟩
  have cf := radialPhase_contDiffAt hf₁ hδ₁ hs
  have cg := radialPhase_contDiffAt hg₁ hδ₂ hs
  have e1 : deriv (fun t => f t + a * g t) s = deriv f s + a * deriv g s := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_combo a 1 (by norm_num) cf cg
  have e2 := iteratedDeriv_combo a 2 (by norm_num) cf cg
  have e3 := iteratedDeriv_combo a 3 (by norm_num) cf cg
  obtain ⟨f1, f2, f3⟩ := hB₁ s hs
  obtain ⟨g1, g2, g3⟩ := hB₂ s hs
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, show s * (deriv f s + a * deriv g s) = s * deriv f s + a * (s * deriv g s) by ring]
    exact abs_combo_le f1 g1
  · rw [e2, show s ^ 2 * (iteratedDeriv 2 f s + a * iteratedDeriv 2 g s) =
      s ^ 2 * iteratedDeriv 2 f s + a * (s ^ 2 * iteratedDeriv 2 g s) by ring]
    exact abs_combo_le f2 g2
  · rw [e3, show s ^ 3 * (iteratedDeriv 3 f s + a * iteratedDeriv 3 g s) =
      s ^ 3 * iteratedDeriv 3 f s + a * (s ^ 3 * iteratedDeriv 3 g s) by ring]
    exact abs_combo_le f3 g3

end Internal

theorem movedParamsValid_holds : MovedParamsValidHolds := by
  intro P moving a hP hm
  exact ⟨hP.chartLength_pos, hP.azimuthOrder_pos, Internal.radialPhase_combo hP.phase hm a, hP.origin⟩

end Instantiation

end CellReduction

end Breakdown
