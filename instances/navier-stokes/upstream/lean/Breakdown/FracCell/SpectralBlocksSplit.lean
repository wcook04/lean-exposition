import Breakdown.FracCell.SpectralBlocks

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

def shapeField (g : CellBlock) (a : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (y : Space) : Space :=
  ∑ s : Fin 2, Set.indicator (cellSolid g s)
    (fun w => ∑ c : Fin 3, (∑ t : Fin 2, trigMode t (g.mode * angleCoord w)
      * a s c t (radialCoord w) (w 2)) • frameVector c w) y

def IsBlockShaped (g : CellBlock) (F : Space → Space) : Prop :=
  ∃ a : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ, (∀ s c t, Measurable fun p : ℝ × ℝ => a s c t p.1 p.2) ∧
    F =ᵐ[volume] shapeField g a

def BlocksApart (g g' : CellBlock) : Prop :=
  volume (⋃ s, cellSolid g s ∩ ⋃ s, cellSolid g' s) = 0 ∨
    (g.innerRadius = g'.innerRadius ∧ g.outerRadius = g'.outerRadius ∧ g.lowerHeight = g'.lowerHeight ∧
      g.upperHeight = g'.upperHeight ∧ g.mode ≠ g'.mode)

def ShapeOrthStatement : Prop :=
  ∀ g g' : CellBlock, BlocksApart g g' → ∀ F G : Space → Space, IsBlockShaped g F → IsBlockShaped g' G →
    MemLp F 2 volume → MemLp G 2 volume → ∫ y, inner ℝ (F y) (G y) = 0

def BlockLocalStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (sd : SpectralData), IsSpectralData c sd →
    ∀ lam : ℝ, 0 < lam → ∀ (x : Fin N → ℝ) (β : ℕ), β ∈ Finset.univ.image c.blockIndex →
      blockInnerValue sd β lam < 1 →
        ∃ (ψ : Space → Space) (Dψ : Space → (Space →L[ℝ] Space)),
          MemLp ψ 2 volume ∧ AEStronglyMeasurable Dψ volume ∧ Integrable (fun y => entrySq (Dψ y)) ∧
            IsWeakGradientOf ψ Dψ ∧ IsBlockShaped (sd.block β) ψ ∧
            (∀ c' : Fin 3, IsBlockShaped (sd.block β) (fun y => Dψ y (frameVector c' y))) ∧
            (∫ y, ‖blockPart c x β y - ψ y‖ ^ 2) + (1 / lam) * ∫ y, entrySq (Dψ y)
              ≤ blockInnerValue sd β lam * ∫ y, ‖blockPart c x β y‖ ^ 2

namespace Internal.SpectralBlocksSplit

open Internal.SpectralBlocks

theorem frame_zero (y : Space) : frameVector 0 y =
    Real.cos (angleCoord y) • unitVector 0 + Real.sin (angleCoord y) • unitVector 1 := by
  ext i
  fin_cases i <;> simp [frameVector, unitVector]

theorem frame_one (y : Space) : frameVector 1 y =
    (-Real.sin (angleCoord y)) • unitVector 0 + Real.cos (angleCoord y) • unitVector 1 := by
  ext i
  fin_cases i <;> simp [frameVector, unitVector]

theorem frame_two (y : Space) : frameVector 2 y = unitVector 2 := rfl

theorem trace_frame (A B : Space →L[ℝ] Space) (y : Space) :
    entryInner A B = ∑ c : Fin 3, inner ℝ (A (frameVector c y)) (B (frameVector c y)) := by
  unfold entryInner
  rw [Fin.sum_univ_three, Fin.sum_univ_three, frame_zero, frame_one, frame_two]
  simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  have h := Real.sin_sq_add_cos_sq (angleCoord y)
  linear_combination (-(inner ℝ (A (unitVector 0)) (B (unitVector 0)))
    - inner ℝ (A (unitVector 1)) (B (unitVector 1))) * h

theorem frame_apply_le (A : Space →L[ℝ] Space) (y : Space) (c : Fin 3) :
    ‖A (frameVector c y)‖ ≤ ∑ j : Fin 3, ‖A (unitVector j)‖ := by
  rw [Fin.sum_univ_three]
  have n0 := norm_nonneg (A (unitVector 0))
  have n1 := norm_nonneg (A (unitVector 1))
  have n2 := norm_nonneg (A (unitVector 2))
  have hc := Real.abs_cos_le_one (angleCoord y)
  have hs := Real.abs_sin_le_one (angleCoord y)
  fin_cases c
  · show ‖A (frameVector 0 y)‖ ≤ _
    rw [frame_zero, map_add, map_smul, map_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    nlinarith [mul_le_mul_of_nonneg_right hc n0, mul_le_mul_of_nonneg_right hs n1]
  · show ‖A (frameVector 1 y)‖ ≤ _
    rw [frame_one, map_add, map_smul, map_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
    nlinarith [mul_le_mul_of_nonneg_right hs n0, mul_le_mul_of_nonneg_right hc n1]
  · show ‖A (frameVector 2 y)‖ ≤ _
    rw [frame_two]
    linarith

theorem frame_memLp {Dψ : Space → (Space →L[ℝ] Space)} (hD : AEStronglyMeasurable Dψ volume)
    (hc : ∀ j : Fin 3, MemLp (fun y => Dψ y (unitVector j)) 2 volume) (c : Fin 3) :
    MemLp (fun y => Dψ y (frameVector c y)) 2 volume := by
  have hg : MemLp (fun y => ∑ j : Fin 3, ‖Dψ y (unitVector j)‖) 2 volume :=
    memLp_finsetSum _ fun j _ => (hc j).norm
  have hm : AEStronglyMeasurable (fun y => Dψ y (frameVector c y)) volume :=
    (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hD.prodMk (frame_meas c).aestronglyMeasurable))
  refine hg.of_le hm (Filter.Eventually.of_forall fun y => ?_)
  refine (frame_apply_le (Dψ y) y c).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)]

variable {k N : ℕ} {c : FracCellData k N} {sd : SpectralData}

theorem part_shaped (hsd : IsSpectralData c sd) (x : Fin N → ℝ) (β : ℕ) :
    IsBlockShaped (sd.block β) (blockPart c x β) := by
  classical
  choose A hA using fun b => hsd.rows_in_blocks b
  refine ⟨fun s c' t r z => ∑ b ∈ Finset.univ.filter (fun b => c.blockIndex b = β),
    x b * twoVarEval (A b s c' t) r z, fun s c' t => ?_, ?_⟩
  · exact Finset.measurable_sum _ fun b _ => (twoVar_cont _).measurable.const_mul _
  · filter_upwards [ae_all_iff.2 fun b => (hA b).2.2] with y hy
    unfold blockPart shapeField
    have e : ∀ b ∈ Finset.univ.filter (fun b => c.blockIndex b = β), x b • c.row b y =
        x b • ∑ s : Fin 2, Set.indicator (cellSolid (sd.block β) s)
          (fun w => ∑ c' : Fin 3, (∑ t : Fin 2, trigMode t ((sd.block β).mode * angleCoord w)
            * twoVarEval (A b s c' t) (radialCoord w) (w 2)) • frameVector c' w) y := by
      intro b hb
      rw [hy b, (Finset.mem_filter.1 hb).2]
    rw [Finset.sum_congr rfl e]
    simp only [Set.indicator_apply, Finset.smul_sum, smul_ite, smul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hy : y ∈ cellSolid (sd.block β) s
    · simp only [hy, if_true, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun b _ => by ring
    · simp [hy]

theorem part_zero {x : Fin N → ℝ} {β : ℕ} (hβ : β ∉ Finset.univ.image c.blockIndex) (y : Space) :
    blockPart c x β y = 0 := by
  unfold blockPart
  refine Finset.sum_eq_zero fun b hb => ?_
  exact absurd ((Finset.mem_filter.1 hb).2 ▸ Finset.mem_image_of_mem c.blockIndex (Finset.mem_univ b)) hβ

end Internal.SpectralBlocksSplit

open Internal.SpectralBlocks Internal.SpectralBlocksSplit

theorem approx_of_split (hL : BlockLocalStatement) (hO : ShapeOrthStatement) : BlockApproxStatement := by
  intro k N c sd hsd lam hlam x
  classical
  set B : Finset ℕ := Finset.univ.image c.blockIndex with hB
  have hex : ∀ β, ∃ (ψ : Space → Space) (Dψ : Space → (Space →L[ℝ] Space)),
      (MemLp ψ 2 volume ∧ AEStronglyMeasurable Dψ volume ∧ Integrable (fun y => entrySq (Dψ y)) ∧
        IsWeakGradientOf ψ Dψ) ∧
      ((β ∈ B ∧ blockInnerValue sd β lam < 1) → IsBlockShaped (sd.block β) ψ ∧
        (∀ c' : Fin 3, IsBlockShaped (sd.block β) (fun y => Dψ y (frameVector c' y))) ∧
        (∫ y, ‖blockPart c x β y - ψ y‖ ^ 2) + (1 / lam) * ∫ y, entrySq (Dψ y)
          ≤ blockInnerValue sd β lam * ∫ y, ‖blockPart c x β y‖ ^ 2) ∧
      (¬(β ∈ B ∧ blockInnerValue sd β lam < 1) → ψ = (fun _ => 0) ∧ Dψ = (fun _ => 0)) := by
    intro β
    by_cases hp : β ∈ B ∧ blockInnerValue sd β lam < 1
    · obtain ⟨ψ, Dψ, h1, h2, h3, h4, h5, h6, h7⟩ := hL c sd hsd lam hlam x β hp.1 hp.2
      exact ⟨ψ, Dψ, ⟨h1, h2, h3, h4⟩, fun _ => ⟨h5, h6, h7⟩, fun h => absurd hp h⟩
    · refine ⟨fun _ => 0, fun _ => 0, ⟨MemLp.zero', aestronglyMeasurable_const, by simp [entrySq],
        fun φ _ j => by simp⟩, fun h => absurd h hp, fun _ => ⟨rfl, rfl⟩⟩
  choose ψ Dψ hadm hgood hzero using hex
  have apart : ∀ β β', β ≠ β' → β ∈ B → β' ∈ B → BlocksApart (sd.block β) (sd.block β') := by
    intro β β' h hβ hβ'
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hβ
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hβ'
    exact hsd.blocks_apart a b h
  refine ⟨ψ, Dψ, hadm, fun β β' h => ⟨?_, ?_, ?_⟩, fun β hβ hin => (hgood β ⟨hβ, hin⟩).2.2⟩
  · by_cases hq : β' ∈ B ∧ blockInnerValue sd β' lam < 1
    · by_cases hβ : β ∈ B
      · exact hO _ _ (apart β β' h hβ hq.1) _ _ (part_shaped hsd x β) (hgood β' hq).1
          (part_memLp hsd x β) (hadm β').1
      · simp [part_zero hβ]
    · rw [(hzero β' hq).1]
      simp
  · by_cases hp : β ∈ B ∧ blockInnerValue sd β lam < 1
    · by_cases hq : β' ∈ B ∧ blockInnerValue sd β' lam < 1
      · exact hO _ _ (apart β β' h hp.1 hq.1) _ _ (hgood β hp).1 (hgood β' hq).1 (hadm β).1 (hadm β').1
      · rw [(hzero β' hq).1]
        simp
    · rw [(hzero β hp).1]
      simp
  · by_cases hp : β ∈ B ∧ blockInnerValue sd β lam < 1
    · by_cases hq : β' ∈ B ∧ blockInnerValue sd β' lam < 1
      · have hc := comp_memLp (hadm β).2.1 (hadm β).2.2.1
        have hc' := comp_memLp (hadm β').2.1 (hadm β').2.2.1
        rw [integral_congr_ae (Filter.Eventually.of_forall fun y => trace_frame (Dψ β y) (Dψ β' y) y),
          integral_finsetSum _ fun c' _ => inner_integrable (frame_memLp (hadm β).2.1 hc c')
            (frame_memLp (hadm β').2.1 hc' c')]
        exact Finset.sum_eq_zero fun c' _ => hO _ _ (apart β β' h hp.1 hq.1) _ _ ((hgood β hp).2.1 c')
          ((hgood β' hq).2.1 c') (frame_memLp (hadm β).2.1 hc c') (frame_memLp (hadm β').2.1 hc' c')
      · rw [(hzero β' hq).2]
        simp [entryInner]
    · rw [(hzero β hp).2]
      simp [entryInner]

theorem blockBound_of_split (h1 : IntervalIdentityStatement) (h2 : IntervalMinimalStatement)
    (h3 : IntervalMonotoneStatement) (h4 : IntervalClosedStatement) (h5 : AxisClosedStatement)
    (hL : BlockLocalStatement) (hO : ShapeOrthStatement) : BlockBoundStatement :=
  blockBound_of h1 h2 h3 h4 h5 (approx_of_split hL hO)

def SameSolidOrthStatement : Prop :=
  ∀ g g' : CellBlock, g.innerRadius = g'.innerRadius → g.outerRadius = g'.outerRadius →
    g.lowerHeight = g'.lowerHeight → g.upperHeight = g'.upperHeight → g.mode ≠ g'.mode →
    ∀ F G : Space → Space, IsBlockShaped g F → IsBlockShaped g' G →
      MemLp F 2 volume → MemLp G 2 volume → ∫ y, inner ℝ (F y) (G y) = 0

namespace Internal.SpectralBlocksSplit

theorem shape_out {g : CellBlock} {a : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ} {y : Space}
    (hy : y ∉ ⋃ s, cellSolid g s) : shapeField g a y = 0 := by
  unfold shapeField
  refine Finset.sum_eq_zero fun s _ => Set.indicator_of_notMem (fun h => hy (Set.mem_iUnion.2 ⟨s, h⟩)) _

theorem disjoint_orth {g g' : CellBlock} (h : volume (⋃ s, cellSolid g s ∩ ⋃ s, cellSolid g' s) = 0)
    {F G : Space → Space} (hF : IsBlockShaped g F) (hG : IsBlockShaped g' G) :
    ∫ y, inner ℝ (F y) (G y) = 0 := by
  obtain ⟨a, -, ha⟩ := hF
  obtain ⟨b, -, hb⟩ := hG
  have hn := measure_eq_zero_iff_ae_notMem.1 h
  refine (integral_congr_ae (g := fun _ => (0 : ℝ)) ?_).trans (integral_zero Space ℝ)
  filter_upwards [ha, hb, hn] with y hy1 hy2 hy3
  rw [hy1, hy2]
  by_cases h1 : y ∈ ⋃ s, cellSolid g s
  · have h2 : y ∉ ⋃ s, cellSolid g' s := by
      intro h2
      obtain ⟨s, hs⟩ := Set.mem_iUnion.1 h1
      exact hy3 (Set.mem_iUnion.2 ⟨s, hs, h2⟩)
    rw [shape_out h2, inner_zero_right]
  · rw [shape_out h1, inner_zero_left]

end Internal.SpectralBlocksSplit

theorem shapeOrth_of_sameSolid (hM : SameSolidOrthStatement) : ShapeOrthStatement := by
  intro g g' hap F G hF hG hF2 hG2
  rcases hap with h | ⟨e1, e2, e3, e4, e5⟩
  · exact Internal.SpectralBlocksSplit.disjoint_orth h hF hG
  · exact hM g g' e1 e2 e3 e4 e5 F G hF hG hF2 hG2

theorem blockBound_of_local (h1 : IntervalIdentityStatement) (h2 : IntervalMinimalStatement)
    (h3 : IntervalMonotoneStatement) (h4 : IntervalClosedStatement) (h5 : AxisClosedStatement)
    (hL : BlockLocalStatement) (hM : SameSolidOrthStatement) : BlockBoundStatement :=
  blockBound_of_split h1 h2 h3 h4 h5 hL (shapeOrth_of_sameSolid hM)

end Spectral

end CellCert

end Breakdown
