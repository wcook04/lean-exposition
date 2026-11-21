import Breakdown.FracCell.GivenModelRowsParts

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenModel

open SteadyCert CellAnalysis RowsInternal

private theorem coord_continuous (i : Fin 3) : Continuous fun y : Space => y i :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).continuous

private theorem solid_measurableSet (K : CellBox) : MeasurableSet K.solid := by
  have h1 : Continuous cylRadius := by
    unfold cylRadius
    exact (((coord_continuous 0).pow 2).add ((coord_continuous 1).pow 2)).sqrt
  have h2 : Continuous fun y => |cylHeight y| := by unfold cylHeight; exact (coord_continuous 2).abs
  exact (measurableSet_le measurable_const h1.measurable).inter ((measurableSet_le h1.measurable measurable_const).inter
    ((measurableSet_le measurable_const h2.measurable).inter (measurableSet_le h2.measurable measurable_const)))

private theorem piece_measurableSet (M : CellMesh) (K : Fin M.cellCount) : MeasurableSet (M.piece K) := by
  unfold CellMesh.piece
  exact (solid_measurableSet _).diff (Finset.measurableSet_biUnion _ fun K' _ => solid_measurableSet _)

private theorem piece_subset (M : CellMesh) (K : Fin M.cellCount) : M.piece K ⊆ (M.box K).solid :=
  Set.sdiff_subset

private theorem piece_disjoint (M : CellMesh) {K K' : Fin M.cellCount} (h : K ≠ K') {y : Space}
    (hy : y ∈ M.piece K) : y ∉ M.piece K' := by
  intro hy'
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact hy'.2 (Set.mem_biUnion (Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt⟩) hy.1)
  · exact hy.2 (Set.mem_biUnion (Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt⟩) hy'.1)

private theorem cellWeightField_apply (M : CellMesh) (τ : Fin M.cellCount → ℝ) (y : Space) (K : Fin M.cellCount)
    (hy : y ∈ M.piece K) : cellWeightField M τ y = τ K := by
  unfold cellWeightField CellMesh.piecewise
  rw [Finset.sum_eq_single K]
  · exact Set.indicator_of_mem hy _
  · intro K' _ hK'
    exact Set.indicator_of_notMem (piece_disjoint M (Ne.symm hK') hy) _
  · intro h; exact absurd (Finset.mem_univ K) h

private theorem cellWeightField_zero (M : CellMesh) (τ : Fin M.cellCount → ℝ) (y : Space)
    (hy : ∀ K, y ∉ M.piece K) : cellWeightField M τ y = 0 := by
  unfold cellWeightField CellMesh.piecewise
  exact Finset.sum_eq_zero fun K _ => Set.indicator_of_notMem (hy K) _

private theorem inner_integrable {F E : Space → Space} (hF : MemLp F 2 volume) (hE : MemLp E 2 volume) :
    Integrable (fun y => inner ℝ (F y) (E y)) := by
  have h := hF.norm.integrable_mul hE.norm
  refine h.mono (hF.aestronglyMeasurable.inner hE.aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_)
  simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_norm]
  exact abs_real_inner_le_norm _ _

private theorem l2Pair_eq_inner {F E : Space → Space} (hF : MemLp F 2 volume) (hE : MemLp E 2 volume) :
    l2Pair F E = inner ℝ (hF.toLp F) (hE.toLp E) := by
  rw [MeasureTheory.L2.inner_def]
  unfold l2Pair
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp, hE.coeFn_toLp] with y h1 h2
  rw [h1, h2]

private theorem l2Pair_sum {n : ℕ} (f : Fin n → Space → Space) (hf : ∀ i, MemLp (f i) 2 volume)
    (u v : Fin n → ℝ) :
    l2Pair (fun y => ∑ i, u i • f i y) (fun y => ∑ j, v j • f j y) =
      ∑ i, ∑ j, u i * v j * l2Pair (f i) (f j) := by
  unfold l2Pair
  have hI : ∀ i j, Integrable (fun y => u i * v j * inner ℝ (f i y) (f j y)) := fun i j =>
    (inner_integrable (hf i) (hf j)).const_mul _
  have : (fun y => inner ℝ (∑ i, u i • f i y) (∑ j, v j • f j y)) =
      fun y => ∑ i, ∑ j, u i * v j * inner ℝ (f i y) (f j y) := by
    funext y
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_smul_right]
    simp only [conj_trivial]
    ring
  rw [this, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hI i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]


private def turnLin (m : ℕ) : Space →ₗ[ℝ] Space where
  toFun := turnStep m
  map_add' x y := by
    ext i
    fin_cases i <;> simp [turnStep] <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [turnStep] <;> ring

private def mirrorLin : Space →ₗ[ℝ] Space where
  toFun := mirror
  map_add' x y := by
    ext i
    fin_cases i <;> simp [mirror] <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [mirror]

private theorem solid_norm_le (K : CellBox) {y : Space} (hy : y ∈ K.solid) :
    ‖y‖ ≤ K.r₂ + K.z₂ := by
  obtain ⟨h1, h2, h3, h4⟩ := hy
  have hr0 : 0 ≤ cylRadius y := Real.sqrt_nonneg _
  have hrr : cylRadius y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
  have hz : |cylHeight y| ^ 2 = y 2 ^ 2 := by rw [sq_abs]; rfl
  have hz0 : 0 ≤ |cylHeight y| := abs_nonneg _
  have hsum : ∑ i : Fin 3, ‖y i‖ ^ 2 ≤ (K.r₂ + K.z₂) ^ 2 := by
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
    nlinarith
  rw [EuclideanSpace.norm_eq]
  calc Real.sqrt (∑ i : Fin 3, ‖y i‖ ^ 2) ≤ Real.sqrt ((K.r₂ + K.z₂) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = K.r₂ + K.z₂ := Real.sqrt_sq (by linarith)

private theorem rowField_zero {M : CellMesh} {N : ℕ} (R : RowData M N) (m : ℕ)
    (hmix : ∀ a b, R.mix a b ≠ 0 → R.cell a = R.cell b ∧ R.harmonic a = R.harmonic b) (a : Fin N) {y : Space}
    (hy : y ∉ (M.box (R.cell a)).solid) : R.rowField m a y = 0 := by
  unfold RowData.rowField
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases h : R.mix a b = 0
  · simp [h]
  · rw [show R.testField m b y = 0 from Set.indicator_of_notMem (by rwa [← (hmix a b h).1]) _, smul_zero]

theorem row_clauses {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (R : RowData M N)
    (hM : IsCellMesh M) (hR : IsRowData R c.order c.rowMax) (hI : IsRowInstance c M R) (hm : 0 < c.order) :
    (∀ a, MemLp (c.row a) 2 volume) ∧
    (∀ a b, l2Pair (c.row a) (c.row b) = if a = b then 1 else 0) ∧
    (∀ a, ∃ r : ℝ, ∀ y, r < ‖y‖ → c.row a y = 0) ∧
    (∀ a, IsClassField c.order (c.row a)) ∧
    (∀ a, 0 < c.rowWeight a) ∧ (∀ a, c.rowWeight a ≤ c.rowMax) ∧
    (∀ a, ∀ y ∉ c.cellRegion, c.row a y = 0) ∧
    Measurable c.cellWeight ∧ (∀ y, 0 ≤ c.cellWeight y) ∧ (∀ y, c.cellWeight y ≤ c.rowMax) ∧
    (∀ y ∉ c.cellRegion, c.cellWeight y = 0) ∧
    (∀ F : Space → Space, MemLp F 2 volume →
      c.toFracCertData.rows F ^ 2 ≤ ∫ y, c.cellWeight y * ‖F y‖ ^ 2) := by
  obtain ⟨hreg, hrow, hrw, hcw⟩ := hI
  have hmix := mix_spec R hR.pairing_posDef
  have hT : ∀ b, MemLp (R.testField c.order b) 2 volume := fun b => testField_memLp R hM c.order b
  have hrowfun : ∀ a, c.row a = fun y => ∑ b, R.mix a b • R.testField c.order b y := fun a => by
    rw [hrow]; rfl
  have hrowL2 : ∀ a, MemLp (c.row a) 2 volume := by
    intro a
    rw [hrowfun a]
    have h : (fun y => ∑ b, R.mix a b • R.testField c.order b y) = ∑ b, R.mix a b • R.testField c.order b := by
      funext y
      simp [Finset.sum_apply]
    rw [h]
    exact memLp_finsetSum' Finset.univ (fun b _ => (hT b).const_smul (R.mix a b))
  have hortho : ∀ a b, l2Pair (c.row a) (c.row b) = if a = b then 1 else 0 := by
    intro a b
    rw [hrowfun a, hrowfun b, l2Pair_sum _ hT]
    simp_rw [testField_pairing R hM hm]
    rw [← Matrix.one_apply, ← hmix.1]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsolid : ∀ a y, y ∉ (M.box (R.cell a)).solid → c.row a y = 0 := fun a y hy => by
    rw [hrow]; exact rowField_zero R c.order hmix.2 a hy
  have hregion : ∀ K, (M.box K).solid ⊆ c.cellRegion := fun K => by
    rw [hreg]; exact Set.subset_iUnion (fun K => (M.box K).solid) K
  have hpos : ∀ a, 0 < c.rowWeight a := fun a => by rw [hrw]; exact hR.cellWeight_pos _
  obtain ⟨K₀, -⟩ := hM.boxes_cover (0, 0) le_rfl hM.outerSize_pos.le le_rfl hM.outerSize_pos.le
  have hmax0 : 0 ≤ c.rowMax := (hR.cellWeight_pos K₀).le.trans (hR.cellWeight_le K₀)
  refine ⟨hrowL2, hortho, ?_, ?_, hpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    refine ⟨∑ K, ((M.box K).r₂ + (M.box K).z₂), fun y hy => hsolid a y fun hs => ?_⟩
    have h1 := solid_norm_le _ hs
    have h2 : (M.box (R.cell a)).r₂ + (M.box (R.cell a)).z₂ ≤ ∑ K, ((M.box K).r₂ + (M.box K).z₂) :=
      Finset.single_le_sum (f := fun K => (M.box K).r₂ + (M.box K).z₂)
        (fun K _ => by
          have := hM.boxes K
          linarith [this.r_order.1, this.r_order.2, this.z_order.1, this.z_order.2]) (Finset.mem_univ _)
    linarith
  · intro a
    have hb := fun b => testField_class R hm b
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_all_iff.2 fun b => (hb b).1] with y hy
      rw [hrowfun a]
      change _ = turnLin c.order _
      rw [map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_smul, hy b]
      rfl
    · filter_upwards [ae_all_iff.2 fun b => (hb b).2] with y hy
      rw [hrowfun a]
      change _ = mirrorLin _
      rw [map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_smul, hy b]
      rfl
  · intro a; rw [hrw]; exact hR.cellWeight_le _
  · intro a y hy
    exact hsolid a y fun hs => hy (hregion _ hs)
  · rw [hcw]
    unfold cellWeightField CellMesh.piecewise
    exact Finset.measurable_sum _ fun K _ => measurable_const.indicator (piece_measurableSet M K)
  · intro y
    rw [hcw]
    by_cases h : ∃ K, y ∈ M.piece K
    · obtain ⟨K, hK⟩ := h
      rw [cellWeightField_apply M _ y K hK]; exact (hR.cellWeight_pos K).le
    · simp only [not_exists] at h
      rw [cellWeightField_zero M _ y h]
  · intro y
    rw [hcw]
    by_cases h : ∃ K, y ∈ M.piece K
    · obtain ⟨K, hK⟩ := h
      rw [cellWeightField_apply M _ y K hK]; exact hR.cellWeight_le K
    · simp only [not_exists] at h
      rw [cellWeightField_zero M _ y h]; exact hmax0
  · intro y hy
    rw [hcw]
    exact cellWeightField_zero M _ y fun K hK => hy (hregion K (piece_subset M K hK))
  · intro F hF
    have hS : 0 ≤ ∑ a, c.rowWeight a * l2Pair F (c.row a) ^ 2 :=
      Finset.sum_nonneg fun a _ => mul_nonneg (hpos a).le (sq_nonneg _)
    show Real.sqrt (∑ a, c.rowWeight a * l2Pair F (c.row a) ^ 2) ^ 2 ≤ _
    rw [Real.sq_sqrt hS]
    have hF2 : Integrable (fun y => ‖F y‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hF.1).1 hF
    have hcell : ∀ K, ∑ a ∈ Finset.univ.filter (fun a => R.cell a = K), l2Pair F (c.row a) ^ 2 ≤
        ∫ y, (M.piece K).indicator (fun y => ‖F y‖ ^ 2) y := by
      intro K
      set G := (M.piece K).indicator F with hGdef
      have hG : MemLp G 2 volume := hF.indicator (piece_measurableSet M K)
      have hnull : volume ((M.box K).solid \ M.piece K) = 0 := by
        refine measure_mono_null (t := ⋃ K' ∈ Finset.univ.filter (fun K' => K' < K),
          (M.box K).solid ∩ (M.box K').solid) ?_ ?_
        · intro y hy
          have h2 : y ∈ ⋃ K' ∈ Finset.univ.filter (fun K' => K' < K), (M.box K').solid := by
            by_contra h
            exact hy.2 ⟨hy.1, h⟩
          simp only [Set.mem_iUnion] at h2 ⊢
          obtain ⟨K', hK', hy'⟩ := h2
          exact ⟨K', hK', hy.1, hy'⟩
        · refine (measure_biUnion_null_iff (Finset.univ.filter _).countable_toSet).2 fun K' hK' => ?_
          have hlt : K' < K := (Finset.mem_filter.1 hK').2
          exact solid_inter_null hM (ne_of_gt hlt)
      have hae := (measure_eq_zero_iff_ae_notMem).1 hnull
      have hpair : ∀ a, R.cell a = K → l2Pair F (c.row a) = l2Pair G (c.row a) := by
        intro a ha
        unfold l2Pair
        refine integral_congr_ae ?_
        filter_upwards [hae] with y hy
        by_cases h1 : y ∈ M.piece K
        · rw [hGdef, Set.indicator_of_mem h1]
        · by_cases h2 : y ∈ (M.box (R.cell a)).solid
          · exact absurd ⟨by rwa [ha] at h2, h1⟩ hy
          · rw [hsolid a y h2, inner_zero_right, inner_zero_right]
      have hon : Orthonormal ℝ (fun a => (hrowL2 a).toLp (c.row a)) := by
        rw [orthonormal_iff_ite]
        intro a b
        rw [← l2Pair_eq_inner (hrowL2 a) (hrowL2 b)]
        exact hortho a b
      have hsumInner := hon.sum_inner_products_le (s := Finset.univ.filter (fun a => R.cell a = K)) (hG.toLp G)
      have hnorm : ‖hG.toLp G‖ ^ 2 = ∫ y, (M.piece K).indicator (fun y => ‖F y‖ ^ 2) y := by
        rw [← real_inner_self_eq_norm_sq, ← l2Pair_eq_inner hG hG]
        unfold l2Pair
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [real_inner_self_eq_norm_sq]
        by_cases h1 : y ∈ M.piece K
        · rw [hGdef, Set.indicator_of_mem h1, Set.indicator_of_mem h1]
        · rw [hGdef, Set.indicator_of_notMem h1, Set.indicator_of_notMem h1, norm_zero]
          ring
      rw [← hnorm]
      refine le_trans (le_of_eq ?_) hsumInner
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [hpair a (Finset.mem_filter.1 ha).2, Real.norm_eq_abs, sq_abs, real_inner_comm,
        ← l2Pair_eq_inner hG (hrowL2 a)]
    have hsplit : ∑ a, c.rowWeight a * l2Pair F (c.row a) ^ 2 =
        ∑ K, R.cellWeight K * ∑ a ∈ Finset.univ.filter (fun a => R.cell a = K), l2Pair F (c.row a) ^ 2 := by
      rw [← Finset.sum_fiberwise Finset.univ R.cell (fun a => c.rowWeight a * l2Pair F (c.row a) ^ 2)]
      refine Finset.sum_congr rfl fun K _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [hrw]
      unfold RowData.rowWeightOf
      rw [(Finset.mem_filter.1 ha).2]
    have hright : ∫ y, c.cellWeight y * ‖F y‖ ^ 2 =
        ∑ K, R.cellWeight K * ∫ y, (M.piece K).indicator (fun y => ‖F y‖ ^ 2) y := by
      have hpt : (fun y => c.cellWeight y * ‖F y‖ ^ 2) =
          fun y => ∑ K, R.cellWeight K * (M.piece K).indicator (fun y => ‖F y‖ ^ 2) y := by
        funext y
        rw [hcw]
        unfold cellWeightField CellMesh.piecewise
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun K _ => ?_
        by_cases h1 : y ∈ M.piece K
        · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h1]
        · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h1]
          ring
      rw [hpt, integral_finsetSum _ fun K _ =>
        ((hF2.indicator (piece_measurableSet M K)).const_mul (R.cellWeight K))]
      refine Finset.sum_congr rfl fun K _ => ?_
      rw [integral_const_mul]
    rw [hsplit, hright]
    exact Finset.sum_le_sum fun K _ => mul_le_mul_of_nonneg_left (hcell K) (hR.cellWeight_pos K).le

end GivenModel

end CellCert

end Breakdown
