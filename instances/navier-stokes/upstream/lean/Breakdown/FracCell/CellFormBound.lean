import Breakdown.FracCell.CellFormBoundSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

private lemma row_square_step {w ρ μ h y L : ℝ} (hw : 0 < w) (hL : L = (ρ - h) / (4 * Real.pi)) :
    4 * Real.pi * (2 * (μ * (L - y))) + 4 * Real.pi * (2 * (μ * y)) + 2 * (μ * h)
      - 4 * Real.pi * (μ ^ 2 / (4 * Real.pi * w)) ≤ w * ρ ^ 2 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have h4 : 4 * Real.pi * L = ρ - h := by rw [hL]; field_simp
  have e1 : 4 * Real.pi * (μ ^ 2 / (4 * Real.pi * w)) = μ ^ 2 / w := by field_simp
  have e2 : w * ρ ^ 2 - (2 * μ * ρ - μ ^ 2 / w) = (w * ρ - μ) ^ 2 / w := by field_simp; ring
  have e3 : 0 ≤ (w * ρ - μ) ^ 2 / w := div_nonneg (sq_nonneg _) hw.le
  have e4 : 4 * Real.pi * (2 * (μ * (L - y))) + 4 * Real.pi * (2 * (μ * y)) = 2 * μ * (4 * Real.pi * L) := by
    ring
  rw [e1, e4, h4]
  linarith

theorem cellFormBound_of_modes (h1 : CellDensityModesStatement) (h5 : CellModeBoundStatement) :
    CellFormBoundStatement := by
  intro α hα1 hα2 k N c hc K S B Cl Sp R hd hax K₂ hcell hrow x hx ζ
  obtain ⟨hdens, hpin⟩ := h1 α hα1 hα2 c hc K hd.box hax hd.model_mirror hd.solid_in_region x hx
  have hπ : 0 < Real.pi := Real.pi_pos
  have hset : Finset.univ.filter (fun a => Sp.rowCell a = K₂) = R.rowSet := by
    ext a; simp [hrow]
  obtain ⟨wv, hwv⟩ : ∃ wv : Fin R.reducerCount → ℝ, ∀ b,
      wv b = ∑ a ∈ R.rowSet, R.reducer b a * CellScalars.rowResidual c K S R α B x ζ a :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨μ, hμ0, hμT⟩ : ∃ μ : Fin N → ℝ, (∀ a ∉ R.rowSet, μ a = 0) ∧
      ∀ a ∈ R.rowSet, μ a = ∑ b, R.reducer b a * wv b :=
    ⟨fun a => if a ∈ R.rowSet then ∑ b, R.reducer b a * wv b else 0,
      fun a ha => by simp [ha], fun a ha => by simp [ha]⟩
  have hbase := h5 α hα1 hα2 c hc K S B Cl R hd hax x hx ζ μ hμ0
  have hmult := hd.multiplier_bound μ hμ0
  have hred := hd.reducer_bound wv
  have hfar := hd.far_bound x hx ζ
  obtain ⟨hϑ0, _⟩ := hd.farShare_mem
  have hfar' := (div_le_div_iff_of_pos_right hϑ0).2 hfar
  have hMeq : (∑ a ∈ R.rowSet, ∑ b ∈ R.rowSet, μ a * R.multiplierMatrix a b * μ b) =
      ∑ a ∈ R.rowSet, ∑ b ∈ R.rowSet, (∑ i, R.reducer i a * wv i) * R.multiplierMatrix a b *
        (∑ i, R.reducer i b * wv i) := by
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    rw [hμT a ha, hμT b hb]
  have hres : (∑ a ∈ R.rowSet, μ a * CellScalars.rowResidual c K S R α B x ζ a) = ∑ b, wv b ^ 2 := by
    rw [Finset.sum_congr rfl fun a ha => by rw [hμT a ha]]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    calc ∑ a ∈ R.rowSet, R.reducer b a * wv b * CellScalars.rowResidual c K S R α B x ζ a
        = wv b * ∑ a ∈ R.rowSet, R.reducer b a * CellScalars.rowResidual c K S R α B x ζ a := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
      _ = wv b ^ 2 := by rw [← hwv b, sq]
  have hper : ∀ a ∈ R.rowSet,
      4 * Real.pi * (2 * (μ a * CellScalars.rowResidual c K S R α B x ζ a))
        + 4 * Real.pi * (2 * (μ a * CellScalars.rowYPair c K S R B x.2.2.2.1 ζ x.1 x.2.1 a))
        + 2 * (μ a * l2Pair (CellScalars.highCouplingField c K S x.1 x.2.1) (c.row a))
        - 4 * Real.pi * (μ a ^ 2 / (4 * Real.pi * c.rowWeight a))
      ≤ c.rowWeight a *
          l2Pair (fun y => c.modelFieldOf α x.1 x.2.1 x.2.2.1 x.2.2.2.1 y + x.2.2.2.2 y) (c.row a) ^ 2 :=
    fun a ha => row_square_step (L := CellScalars.lowRowValue c K S α x a)
      (y := CellScalars.rowYPair c K S R B x.2.2.2.1 ζ x.1 x.2.1 a) (hd.rowWeight_pos a ha) rfl
  have hsum := Finset.sum_le_sum hper
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have hpinE : (∑ i, 2 * ζ i * ∫ y in Sp.cell K₂, entryInner (x.2.1 y) (c.modelPinField i y)) =
      4 * Real.pi * ∑ i, 2 * ζ i * ∫ p in K.rect, p.1 * modeFieldPair c x.2.1 (c.modelPinField i) p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [setIntegral_congr_set hcell, hpin i]; ring
  have hX3 : ∀ t : ℝ, 4 * Real.pi * (2 / (4 * Real.pi) * t) = 2 * t := fun t => by field_simp
  have h4 : (0 : ℝ) ≤ 4 * Real.pi := by positivity
  have hcore4 := mul_le_mul_of_nonneg_left hbase h4
  have hmult4 := mul_le_mul_of_nonneg_left hmult h4
  have hred4 := mul_le_mul_of_nonneg_left hred h4
  have hfar4 := mul_le_mul_of_nonneg_left hfar' h4
  have hsq : (∑ b : Fin R.reducerCount,
      (∑ a ∈ R.rowSet, R.reducer b a * CellScalars.rowResidual c K S R α B x ζ a) ^ 2) = ∑ b, wv b ^ 2 :=
    Finset.sum_congr rfl fun b _ => by rw [hwv b]
  unfold CellSplit.cellPart CellScalars.cellForm
  rw [hset, hpinE, setIntegral_congr_set hcell, hdens, hsq]
  rw [hMeq] at hmult4
  rw [← hres] at hred4
  have hX := hX3 (∑ a ∈ R.rowSet, μ a * l2Pair (CellScalars.highCouplingField c K S x.1 x.2.1) (c.row a))
  nlinarith [hcore4, hmult4, hred4, hfar4, hsum, hX, hres]

theorem cellFormBound_of (h1 : CellDensityModesStatement) (_h2 : ResolvedEnergyStatement)
    (_h3 : UnresolvedEnergyStatement) (_h4 : VelocityTailStatement) (h5 : CellModeBoundStatement) :
    CellFormBoundStatement :=
  cellFormBound_of_modes h1 h5

end CellAnalysis

end CellCert

end Breakdown
