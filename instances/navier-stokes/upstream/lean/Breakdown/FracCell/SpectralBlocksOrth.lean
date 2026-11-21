import Breakdown.FracCell.SpectralBlocksFamily

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

def ModeOrthSameStatement : Prop :=
  ∀ g g' : CellBlock,
    g.innerRadius = g'.innerRadius → g.outerRadius = g'.outerRadius → g.lowerHeight = g'.lowerHeight →
      g.upperHeight = g'.upperHeight → g.mode ≠ g'.mode →
    (∀ F G : Space → Space, ModeField g F → ModeField g' G → MemLp F 2 volume → MemLp G 2 volume →
      ∫ y, inner ℝ (F y) (G y) = 0) ∧
    (∀ D D' : Space → (Space →L[ℝ] Space), ModeGradient g D → ModeGradient g' D' →
      AEStronglyMeasurable D volume → AEStronglyMeasurable D' volume →
      Integrable (fun y => entrySq (D y)) volume → Integrable (fun y => entrySq (D' y)) volume →
      ∫ y, entryInner (D y) (D' y) = 0)

namespace Internal.SpectralBlocksOrth

theorem field_outside {g : CellBlock} {F : Space → Space} (h : ModeField g F) {y : Space}
    (hy : ∀ s, y ∉ cellSolid g s) : F y = 0 := by
  obtain ⟨f, -, hf⟩ := h
  rw [hf y]
  exact Finset.sum_eq_zero fun s _ => Set.indicator_of_notMem (hy s) _

theorem grad_outside {g : CellBlock} {D : Space → (Space →L[ℝ] Space)} (h : ModeGradient g D) {y : Space}
    (hy : ∀ s, y ∉ cellSolid g s) : D y = 0 := by
  obtain ⟨f, -, hf⟩ := h
  rw [hf y]
  exact Finset.sum_eq_zero fun s _ => Set.indicator_of_notMem (hy s) _

theorem apart_ae {g g' : CellBlock} (h : volume (⋃ s, cellSolid g s ∩ ⋃ s, cellSolid g' s) = 0) :
    ∀ᵐ y ∂volume, (∀ s, y ∉ cellSolid g s) ∨ (∀ s, y ∉ cellSolid g' s) := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with y hy
  by_contra hc
  push Not at hc
  obtain ⟨⟨s, hs⟩, ⟨s', hs'⟩⟩ := hc
  exact hy (Set.mem_iUnion.2 ⟨s, hs, Set.mem_iUnion.2 ⟨s', hs'⟩⟩)

end Internal.SpectralBlocksOrth

open Internal.SpectralBlocksOrth in
theorem modeOrth_of_same (hS : ModeOrthSameStatement) : ModeOrthStatement := by
  intro g g' hap
  rcases hap with h | ⟨e1, e2, e3, e4, e5⟩
  · refine ⟨fun F G hF hG _ _ => ?_, fun D D' hD hD' _ _ _ _ => ?_⟩
    · refine integral_eq_zero_of_ae ?_
      filter_upwards [apart_ae h] with y hy
      rcases hy with hy | hy
      · simp [field_outside hF hy]
      · simp [field_outside hG hy]
    · refine integral_eq_zero_of_ae ?_
      filter_upwards [apart_ae h] with y hy
      rcases hy with hy | hy
      · simp [grad_outside hD hy, entryInner]
      · simp [grad_outside hD' hy, entryInner]
  · exact hS g g' e1 e2 e3 e4 e5
