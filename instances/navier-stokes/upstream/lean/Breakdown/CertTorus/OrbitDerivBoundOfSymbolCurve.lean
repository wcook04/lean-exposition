import Breakdown.CertTorus.SymbolCurve

open MeasureTheory Set Real Filter
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Breakdown.FarField

open Freq SmoothFlow

namespace Internal.OrbitDerivBound

open Internal.SymbolCurve

theorem exists_bound_weight_orbit (hOH : OrbitHomSobolev) (hW : HomWiener) (hR : RotateSymbol)
    {w : ℝ → X} {P : ℝ} {R : Space ≃ₗᵢ[ℝ] Space}
    (hw : realization.F.IsOrbit (realization.rot R) w P) (k : ℕ) :
    ∃ B : ℝ, ∀ s, ‖toWeightL1 k (velSymbol (w s))‖ ≤ B := by
  have hc : ∀ m, IsHomSobolevCurve m w univ := hOH w P R hw
  have hcont : ContinuousOn (fun s => toWeightL1 k (velSymbol (w s))) univ :=
    continuousOn_toWeightL1_vel hW hc k
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := P)).exists_bound_of_continuousOn
    (hcont.mono (subset_univ _))
  have hper : Function.Periodic (fun s => ‖toWeightL1 k (velSymbol (w s))‖) P := by
    intro s
    show ‖toWeightL1 k (velSymbol (w (s + P)))‖ = ‖toWeightL1 k (velSymbol (w s))‖
    rw [hw.periodic s, realization_rot_eq]
    exact (hR R (w s)).2.1 k
  refine ⟨B, fun s => ?_⟩
  obtain ⟨t, ht, hts⟩ := hper.exists_mem_Ico₀ hw.pos s
  have hts' : ‖toWeightL1 k (velSymbol (w s))‖ = ‖toWeightL1 k (velSymbol (w t))‖ := hts
  rw [hts']
  exact hB t (Ico_subset_Icc_self ht)

end Internal.OrbitDerivBound

theorem orbitDerivBoundOfSymbolCurve_holds : OrbitDerivBoundOfSymbolCurve := by
  intro hOH hW hR hPd w P R hw
  choose C hC using hPd
  choose B hB using fun k => Internal.OrbitDerivBound.exists_bound_weight_orbit hOH hW hR hw k
  refine ⟨∑ i ∈ Finset.range 4, |C i| * |B i|, fun j hj s y => ?_⟩
  have hc : ∀ m, IsHomSobolevCurve m w univ := hOH w P R hw
  have hm : MemLp (velSymbol (w s)) 1 (weightL1Measure j) :=
    Internal.SymbolCurve.memLp_curve hW hc j (mem_univ s)
  have h0 : ‖iteratedFDeriv ℝ j (orbitField w s) y‖ ≤ C j * ‖toWeightL1 j (velSymbol (w s))‖ :=
    hC j _ hm y
  have h1 : C j * ‖toWeightL1 j (velSymbol (w s))‖ ≤ |C j| * |B j| :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left ((hB j s).trans (le_abs_self _)) (abs_nonneg _))
  have h2 : |C j| * |B j| ≤ ∑ i ∈ Finset.range 4, |C i| * |B i| :=
    Finset.single_le_sum (f := fun i => |C i| * |B i|) (fun i _ => by positivity)
      (Finset.mem_range.2 (by omega))
  exact h0.trans (h1.trans h2)

end Breakdown.FarField
