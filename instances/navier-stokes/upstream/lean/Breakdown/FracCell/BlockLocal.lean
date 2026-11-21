import Breakdown.FracCell.SpectralBlocksMode
import Breakdown.FracCell.SpectralBlocksField

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

namespace Internal.BlockLocal

theorem frame_inner (d c : Fin 3) (y : Space) :
    inner ℝ (frameVector d y) (frameVector c y) = if d = c then 1 else 0 := by
  have h := Real.sin_sq_add_cos_sq (angleCoord y)
  fin_cases d <;> fin_cases c <;>
    simp [frameVector, unitVector, PiLp.inner_apply, Fin.sum_univ_three, -inner_self_eq_norm_sq_to_K] <;>
      first | ring1 | nlinarith [h]

theorem shape_sub (g : CellBlock) (a b : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (y : Space) :
    shapeField g a y - shapeField g b y = shapeField g (fun s c t r z => a s c t r z - b s c t r z) y := by
  unfold shapeField
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hy : y ∈ cellSolid g s
  · simp only [Set.indicator_of_mem hy]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← sub_smul]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  · simp [Set.indicator_of_notMem hy]

theorem mode_shaped {g : CellBlock} {F : Space → Space} (h : ModeField g F) : IsBlockShaped g F := by
  obtain ⟨f, hf, hF⟩ := h
  exact ⟨f, hf, Filter.Eventually.of_forall fun y => hF y⟩

theorem gradient_shaped {g : CellBlock} {D : Space → (Space →L[ℝ] Space)} (h : ModeGradient g D)
    (c' : Fin 3) : IsBlockShaped g (fun y => D y (frameVector c' y)) := by
  obtain ⟨f, hf, hD⟩ := h
  refine ⟨fun s c t r z => f s c c' t r z, fun s c t => hf s c c' t, Filter.Eventually.of_forall fun y => ?_⟩
  simp only []
  rw [hD y]
  unfold shapeField
  rw [_root_.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hy : y ∈ cellSolid g s
  · simp only [Set.indicator_of_mem hy]
    rw [_root_.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [_root_.sum_apply]
    simp only [_root_.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      frame_inner, ite_smul, one_smul, zero_smul, smul_ite, smul_zero]
    rw [Finset.sum_ite_eq' Finset.univ c']
    simp
  · simp [Set.indicator_of_notMem hy]

theorem inner_eq (sd : SpectralData) (β : ℕ) (lam : ℝ) : blockInner sd β lam = blockInnerValue sd β lam := by
  unfold blockInner blockInnerValue
  rfl

end Internal.BlockLocal

open Internal.BlockLocal Internal.SpectralBlocksSplit Internal.SpectralBlocksField in
theorem blockLocal_of_field (hW : FieldWitnessStatement) : BlockLocalStatement := by
  intro k N c sd hsd lam hlam x β hβ _
  classical
  obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hβ
  subst ha
  have hrowL : ∀ b, MemLp (c.row b) 2 volume := fun b =>
    row_memLp (hsd.rows_in_blocks b) (by rw [hsd.rows_orthonormal b b, if_pos rfl])
  have hpart : blockPart c x (c.blockIndex a)
      = fun y => ∑ b, (if c.blockIndex b = c.blockIndex a then x b else 0) • c.row b y := by
    funext y
    unfold blockPart
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  have hblk : IsBlockField (sd.block (c.blockIndex a)) (blockPart c x (c.blockIndex a)) := by
    rw [hpart]
    refine comb_blockField _ _ _ fun b hb => ?_
    have hb' : c.blockIndex b = c.blockIndex a := by
      by_contra hne
      exact hb (if_neg hne)
    rw [← hb']
    exact hsd.rows_in_blocks b
  have hφL : MemLp (blockPart c x (c.blockIndex a)) 2 volume := by
    rw [hpart]
    exact memLp_finsetSum _ fun b _ => (hrowL b).const_smul (if c.blockIndex b = c.blockIndex a then x b else 0)
  obtain ⟨ψ, Dψ, h1, h2, h3, h4, h5, h6, h7⟩ := hW c sd hsd lam hlam a _ hblk hφL
  refine ⟨ψ, Dψ, h1, h2, h3, h4, ?_, fun c' => gradient_shaped h5 c', ?_⟩
  · obtain ⟨f, hf, hF⟩ := mode_shaped h6
    obtain ⟨p, hp, hP⟩ := part_shaped hsd x (c.blockIndex a)
    refine ⟨fun s c t r z => p s c t r z - f s c t r z, fun s c t => (hp s c t).sub (hf s c t), ?_⟩
    filter_upwards [hF, hP] with y e1 e2
    rw [← shape_sub, ← e1, ← e2]
    abel
  · rw [← inner_eq]
    exact h7

theorem blockBound_of_field_cyl (h1 : IntervalIdentityStatement) (h2 : IntervalMinimalStatement)
    (h3 : IntervalMonotoneStatement) (h4 : IntervalClosedStatement) (h5 : AxisClosedStatement)
    (hW : FieldWitnessStatement) (hC : CylStatement) : BlockBoundStatement :=
  blockBound_of_cyl h1 h2 h3 h4 h5 (blockLocal_of_field hW) hC

end Spectral

end CellCert

end Breakdown
