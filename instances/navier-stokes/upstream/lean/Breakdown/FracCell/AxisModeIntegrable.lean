import Breakdown.FracCell.RelAxis
import Breakdown.FracCell.LowEntry

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

namespace AxisModeIntegrableInternal

private lemma cylPoint_shift (r θ z c : ℝ) :
    cylPoint r θ z + EuclideanSpace.single 2 c = cylPoint r θ (z + c) := by
  ext i
  fin_cases i <;> simp [cylPoint]

private lemma gradMode_shift (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (c : ℝ) (a b : Fin 3)
    (p : ℝ × ℝ) :
    gradMode m n (fun y => G (y + EuclideanSpace.single 2 c)) a b p = gradMode m n G a b (p.1, p.2 + c) := by
  simp only [gradMode, modeMat, cylPoint_shift]

end AxisModeIntegrableInternal

open AxisModeIntegrableInternal in
theorem axisModeIntegrable : AxisModeIntegrableStatement := by
  intro m v G H hsec R z₁ z₂ n a b
  set c : ℝ := z₁
  set w : Space := EuclideanSpace.single 2 c
  set G' : Space → (Space →L[ℝ] Space) := fun y => G (y + w)
  have hG1 : AEStronglyMeasurable G' volume :=
    hsec.measurable_gradient.comp_measurePreserving (measurePreserving_add_right volume w)
  have hG2 : Integrable (fun y => entrySq (G' y)) :=
    hsec.gradient_two.comp_add_right w
  let K : CellBox := ⟨0, max R 1, 0, max (z₂ - z₁) 1⟩
  have hK : IsCellBox K :=
    ⟨⟨le_rfl, lt_of_lt_of_le one_pos (le_max_right _ _)⟩, ⟨le_rfl, lt_of_lt_of_le one_pos (le_max_right _ _)⟩⟩
  have h := LowEntry.Internal.gradMode_int K hK m n hG1 hG2 a b
  have hw : K.lineWeight = fun r => r := funext fun r => by simp [CellBox.lineWeight, K]
  rw [hw] at h
  set f : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * gradMode m n G' a b p
  set e : ℝ × ℝ → ℝ × ℝ := fun p => p + ((0 : ℝ), -c)
  have he : MeasurePreserving e volume volume := measurePreserving_add_right volume _
  have hemb : MeasurableEmbedding e := (MeasurableEquiv.addRight ((0 : ℝ), -c)).measurableEmbedding
  have h2 : IntegrableOn (f ∘ e) (e ⁻¹' K.rect) volume := (he.integrableOn_comp_preimage hemb).2 h
  have hfe : (f ∘ e) = fun p : ℝ × ℝ => (p.1 : ℂ) * gradMode m n G a b p := by
    funext p
    simp only [Function.comp, f, e, G', w, gradMode_shift, Prod.fst_add, Prod.snd_add, add_zero]
    congr 2
    simp [c]
  rw [hfe] at h2
  refine h2.mono_set ?_
  rintro ⟨r, z⟩ ⟨⟨hr0, hrR⟩, ⟨hz1, hz2⟩⟩
  simp only [Set.mem_preimage, e, CellBox.rect, K, Set.mem_prod, Set.mem_Icc, Prod.fst_add, Prod.snd_add]
  refine ⟨⟨by simpa using hr0, by simpa using le_trans hrR (le_max_left _ _)⟩, ?_, ?_⟩
  · simp only [c]; linarith
  · simp only [c]
    have := le_max_left (z₂ - z₁) 1
    linarith

end Breakdown.CellCert.CellFormula
