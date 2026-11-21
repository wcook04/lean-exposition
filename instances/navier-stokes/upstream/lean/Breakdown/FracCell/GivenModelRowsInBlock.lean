import Breakdown.FracCell.GivenModelDefs
import Breakdown.FracCell.GivenModelMixClauses

open MeasureTheory Polynomial

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenModel

open SteadyCert CellAnalysis

private theorem rib_mix_support {M : CellMesh} {N : ℕ} (R : RowData M N) (m : ℕ) (rowMax : ℝ)
    (hR : IsRowData R m rowMax) (a b : Fin N) (h : R.mix a b ≠ 0) :
    R.cell a = R.cell b ∧ R.harmonic a = R.harmonic b :=
  (mix_clauses R m rowMax hR).2.1 a b h

private theorem rib_plane_null : volume {y : Space | y 2 = 0} = 0 := by
  have h : {y : Space | y 2 = 0} =
      (LinearMap.ker (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).toLinearMap : Set Space) := by
    ext y; simp
  rw [h]
  refine Measure.addHaar_submodule _ _ ?_
  intro htop
  have h1 : EuclideanSpace.single (2 : Fin 3) (1 : ℝ) ∈
      LinearMap.ker (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).toLinearMap := by
    rw [htop]; trivial
  simp at h1

private def ribPoly (d : ℕ) (f : Fin (d + 1) → Fin (d + 1) → ℝ) : ℝ[X][X] :=
  ∑ j : Fin (d + 1), ∑ l : Fin (d + 1), monomial (j : ℕ) (monomial (l : ℕ) (f j l))

private theorem ribPoly_eval (d : ℕ) (f : Fin (d + 1) → Fin (d + 1) → ℝ) (r z : ℝ) :
    Spectral.twoVarEval (ribPoly d f) r z = ∑ j, ∑ l, f j l * r ^ (j : ℕ) * z ^ (l : ℕ) := by
  simp only [Spectral.twoVarEval, ribPoly, Polynomial.map_sum, Polynomial.map_monomial,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.coe_evalRingHom]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

private theorem ribPoly_natDegree (d : ℕ) (f : Fin (d + 1) → Fin (d + 1) → ℝ) :
    (ribPoly d f).natDegree ≤ d := by
  unfold ribPoly
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun l _ => ?_)
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp j.isLt)

private theorem ribPoly_coeff (d : ℕ) (f : Fin (d + 1) → Fin (d + 1) → ℝ) (i : ℕ) :
    (ribPoly d f).coeff i = ∑ j : Fin (d + 1), ∑ l : Fin (d + 1),
      if (j : ℕ) = i then monomial (l : ℕ) (f j l) else 0 := by
  simp only [ribPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]

private theorem ribPoly_coeff_natDegree (d : ℕ) (f : Fin (d + 1) → Fin (d + 1) → ℝ) (i : ℕ) :
    ((ribPoly d f).coeff i).natDegree ≤ d := by
  rw [ribPoly_coeff]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun l _ => ?_)
  split_ifs
  · exact (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp l.isLt)
  · simp

private theorem ribPoly_dvd (d : ℕ) (f : Fin (d + 1) → Fin (d + 1) → ℝ) (hf : ∀ l, f 0 l = 0) :
    X ∣ ribPoly d f := by
  rw [Polynomial.X_dvd_iff, ribPoly_coeff]
  refine Finset.sum_eq_zero (fun j _ => Finset.sum_eq_zero (fun l _ => ?_))
  split_ifs with h
  · have hj : j = 0 := Fin.ext h
    subst hj
    simp [hf l]
  · rfl

private theorem rib_eval_re {d : ℕ} (P : CellPoly d) (ρ zz φ : ℝ) :
    (evalPoly P ρ zz * Complex.exp ((φ : ℂ) * Complex.I)).re =
      ∑ j, ∑ l, ((P j l).re * Real.cos φ - (P j l).im * Real.sin φ) * ρ ^ (j : ℕ) * zz ^ (l : ℕ) := by
  unfold evalPoly
  rw [Finset.sum_mul, Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_mul, Complex.re_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [show P j l * (ρ : ℂ) ^ (j : ℕ) * (zz : ℂ) ^ (l : ℕ) * Complex.exp ((φ : ℂ) * Complex.I) =
      P j l * Complex.exp ((φ : ℂ) * Complex.I) * ((ρ ^ (j : ℕ) * zz ^ (l : ℕ) : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.re_mul_ofReal, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

private theorem rib_coeff_id {d N : ℕ} (w : Fin N → ℝ) (P : Fin N → CellPoly d) (σ ρ z zz φ : ℝ)
    (κ : ℕ → ℝ) (hκ : ∀ l : ℕ, σ * zz ^ l = κ l * z ^ l) :
    ∑ b, w b * (σ * (evalPoly (P b) ρ zz * Complex.exp ((φ : ℂ) * Complex.I)).re) =
      Real.cos φ * ∑ j : Fin (d + 1), ∑ l : Fin (d + 1),
          (κ l * (∑ b, (w b : ℂ) * P b j l).re) * ρ ^ (j : ℕ) * z ^ (l : ℕ)
        + Real.sin φ * ∑ j : Fin (d + 1), ∑ l : Fin (d + 1),
          (κ l * -(∑ b, (w b : ℂ) * P b j l).im) * ρ ^ (j : ℕ) * z ^ (l : ℕ) := by
  simp only [rib_eval_re, Complex.re_sum, Complex.im_sum, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    Finset.mul_sum, Finset.sum_mul]
  rw [← Finset.sum_add_distrib, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_add_distrib, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [← Finset.sum_neg_distrib]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  linear_combination (w b * ((P b j l).re * Real.cos φ - (P b j l).im * Real.sin φ) * ρ ^ (j : ℕ)) * hκ l

private def ribQ {M : CellMesh} {N : ℕ} (RD : RowData M N) (a : Fin N) (i : Fin 3) (j l : Fin (RD.degree + 1)) : ℂ :=
  ∑ b, ((RD.mix a b : ℝ) : ℂ) * RD.profile b i j l

private def ribA {M : CellMesh} {N : ℕ} (RD : RowData M N) (a : Fin N) : Fin 2 → Fin 3 → Fin 2 → ℝ[X][X] :=
  fun s i t => ribPoly RD.degree (fun j l =>
    (if s = 0 then 1 else (if i = 2 then -1 else 1) * (-1) ^ (l : ℕ)) *
      (if t = 0 then (ribQ RD a i j l).re else -(ribQ RD a i j l).im))

private theorem rib_angle (y : Space) : Spectral.angleCoord y = cylAngle y := by
  unfold Spectral.angleCoord cylAngle
  congr 1
  apply Complex.ext <;> simp

private theorem rib_frameVector (i : Fin 3) (y : Space) : Spectral.frameVector i y = frameUnit (cylAngle y) i := by
  fin_cases i <;> simp [Spectral.frameVector, frameUnit, rib_angle, radialUnit, angularUnit, axialUnit, unitVector]

private theorem rib_value {M : CellMesh} {N : ℕ} (RD : RowData M N) (m : ℕ) (a : Fin N) (s : Fin 2) (y : Space)
    (hκ : ∀ (i : Fin 3) (l : ℕ), vectorSign y i * |cylHeight y| ^ l =
      (if s = 0 then 1 else (if i = 2 then -1 else 1) * (-1) ^ l) * y 2 ^ l) :
    ∑ b, RD.mix a b • cartOfFrame (cylAngle y) (fun i => vectorSign y i *
      (evalPoly (RD.profile b i) (cylRadius y) |cylHeight y| *
        Complex.exp ((azimuth m (RD.harmonic a : ℤ) * cylAngle y : ℝ) * Complex.I)).re) =
    ∑ i : Fin 3, (∑ t : Fin 2, Spectral.trigMode t (((rowBlock M RD m a).mode : ℝ) * Spectral.angleCoord y) *
      Spectral.twoVarEval (ribA RD a s i t) (Spectral.radialCoord y) (y 2)) • Spectral.frameVector i y := by
  simp only [cartOfFrame, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_smul, rib_frameVector]
  congr 1
  have hφ : (((rowBlock M RD m a).mode : ℕ) : ℝ) * Spectral.angleCoord y = azimuth m (RD.harmonic a : ℤ) * cylAngle y := by
    simp only [rowBlock, rib_angle, azimuth]
    push_cast
    ring
  rw [hφ, Fin.sum_univ_two]
  simp only [Spectral.trigMode, ribA, ribPoly_eval, if_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false]
  have := rib_coeff_id (d := RD.degree) (fun b => RD.mix a b) (fun b => RD.profile b i) (vectorSign y i)
    (cylRadius y) (y 2) |cylHeight y| (azimuth m (RD.harmonic a : ℤ) * cylAngle y)
    (fun l => if s = 0 then 1 else (if i = 2 then -1 else 1) * (-1) ^ l) (hκ i)
  rw [this]
  simp only [ribQ, Spectral.radialCoord, cylRadius]

private theorem rib_point {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (hM : IsCellMesh M) (hR : IsRowData RD c.order c.rowMax) (hI : IsRowInstance c M RD) (a : Fin N) (y : Space)
    (hy : y 2 ≠ 0) :
    c.row a y = ∑ s : Fin 2, Set.indicator (Spectral.cellSolid (rowBlock M RD c.order a) s)
      (fun w => ∑ i : Fin 3, (∑ t : Fin 2, Spectral.trigMode t (((rowBlock M RD c.order a).mode : ℝ) * Spectral.angleCoord w)
        * Spectral.twoVarEval (ribA RD a s i t) (Spectral.radialCoord w) (w 2)) • Spectral.frameVector i w) y := by
  rw [hI.row_eq]
  unfold RowData.rowField
  have hz := (hM.boxes (RD.cell a)).z_order.1
  have step : ∀ b, RD.mix a b • RD.testField c.order b y = RD.mix a b • Set.indicator (M.box (RD.cell a)).solid
      (fun z => cartOfFrame (cylAngle z) (fun i => vectorSign z i *
        (evalPoly (RD.profile b i) (cylRadius z) |cylHeight z| *
          Complex.exp ((azimuth c.order (RD.harmonic a : ℤ) * cylAngle z : ℝ) * Complex.I)).re)) y := by
    intro b
    by_cases hb : RD.mix a b = 0
    · simp [hb]
    · obtain ⟨hc, hh⟩ := rib_mix_support RD c.order c.rowMax hR a b hb
      unfold RowData.testField
      rw [hc, hh]
  rw [Finset.sum_congr rfl (fun b _ => step b), Fin.sum_univ_two]
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · have h0 : y ∉ Spectral.cellSolid (rowBlock M RD c.order a) 0 := by
      intro h
      simp only [Spectral.cellSolid, rowBlock, Set.mem_ofPred_eq, if_true] at h
      linarith [h.2.2.1]
    have hiff : y ∈ Spectral.cellSolid (rowBlock M RD c.order a) 1 ↔ y ∈ (M.box (RD.cell a)).solid := by
      simp only [Spectral.cellSolid, CellBox.solid, rowBlock, Set.mem_ofPred_eq, cylHeight, abs_of_neg hneg,
        Spectral.radialCoord, cylRadius, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false]
    rw [Set.indicator_of_notMem h0, zero_add]
    by_cases hy' : y ∈ (M.box (RD.cell a)).solid
    · rw [Set.indicator_of_mem (hiff.2 hy')]
      simp only [Set.indicator_of_mem hy']
      refine rib_value RD c.order a 1 y (fun i l => ?_)
      have hv : vectorSign y i = if i = 2 then -1 else 1 := by
        unfold vectorSign cylHeight
        by_cases h : i = 2 <;> simp [h, hneg]
      have ha : |cylHeight y| = -y 2 := abs_of_neg hneg
      rw [hv, ha, neg_pow, if_neg (show (1 : Fin 2) ≠ 0 by decide)]
      split_ifs <;> ring
    · rw [Set.indicator_of_notMem (mt hiff.1 hy')]
      simp [Set.indicator_of_notMem hy']
  · have h1 : y ∉ Spectral.cellSolid (rowBlock M RD c.order a) 1 := by
      intro h
      simp only [Spectral.cellSolid, rowBlock, Set.mem_ofPred_eq, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one,
        if_false] at h
      linarith [h.2.2.1]
    have hiff : y ∈ Spectral.cellSolid (rowBlock M RD c.order a) 0 ↔ y ∈ (M.box (RD.cell a)).solid := by
      simp only [Spectral.cellSolid, CellBox.solid, rowBlock, Set.mem_ofPred_eq, cylHeight, abs_of_pos hpos,
        Spectral.radialCoord, cylRadius, if_true]
    rw [Set.indicator_of_notMem h1, add_zero]
    by_cases hy' : y ∈ (M.box (RD.cell a)).solid
    · rw [Set.indicator_of_mem (hiff.2 hy')]
      simp only [Set.indicator_of_mem hy']
      refine rib_value RD c.order a 0 y (fun i l => ?_)
      have hn : ¬ y 2 < 0 := not_lt.mpr hpos.le
      simp [vectorSign, cylHeight, hn, abs_of_pos hpos]
    · rw [Set.indicator_of_notMem (mt hiff.1 hy')]
      simp [Set.indicator_of_notMem hy']

private theorem rib_core {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (hM : IsCellMesh M) (hR : IsRowData RD c.order c.rowMax) (hI : IsRowInstance c M RD) (a : Fin N) :
    ∃ A : Fin 2 → Fin 3 → Fin 2 → ℝ[X][X],
    (∀ s i t, (A s i t).natDegree ≤ (rowBlock M RD c.order a).degree ∧
      ∀ j, ((A s i t).coeff j).natDegree ≤ (rowBlock M RD c.order a).degree) ∧
    ((rowBlock M RD c.order a).onAxis = true → ∀ s t, X ∣ A s 0 t ∧ X ∣ A s 1 t) ∧
    ∀ᵐ y ∂volume, c.row a y = ∑ s : Fin 2, Set.indicator (Spectral.cellSolid (rowBlock M RD c.order a) s)
      (fun w => ∑ i : Fin 3, (∑ t : Fin 2, Spectral.trigMode t ((rowBlock M RD c.order a).mode * Spectral.angleCoord w)
        * Spectral.twoVarEval (A s i t) (Spectral.radialCoord w) (w 2)) • Spectral.frameVector i w) y := by
  refine ⟨ribA RD a, fun s i t => ⟨ribPoly_natDegree _ _, fun j => ribPoly_coeff_natDegree _ _ j⟩, ?_, ?_⟩
  · intro hax s t
    have h0 : (M.box (RD.cell a)).r₁ = 0 := by simpa [rowBlock] using hax
    have hQ : ∀ i : Fin 3, (i = 0 ∨ i = 1) → ∀ l, ribQ RD a i 0 l = 0 := by
      intro i hi l
      unfold ribQ
      refine Finset.sum_eq_zero (fun b _ => ?_)
      by_cases hb : RD.mix a b = 0
      · simp [hb]
      · have hc := (rib_mix_support RD c.order c.rowMax hR a b hb).1
        have hb0 := hR.axis_regular b (by rw [← hc]; exact h0) l
        rcases hi with rfl | rfl
        · simp [hb0.1]
        · simp [hb0.2]
    exact ⟨ribPoly_dvd _ _ (fun l => by simp [hQ 0 (Or.inl rfl) l]),
      ribPoly_dvd _ _ (fun l => by simp [hQ 1 (Or.inr rfl) l])⟩
  · rw [ae_iff]
    refine measure_mono_null (fun y hy => ?_) rib_plane_null
    by_contra h2
    exact hy (rib_point c M RD hM hR hI a y h2)

theorem rowsInBlock_of {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (hM : IsCellMesh M) (hR : IsRowData RD c.order c.rowMax) (hI : IsRowInstance c M RD) (a : Fin N) :
    Spectral.IsBlockField (rowBlock M RD c.order a) (c.row a) :=
  rib_core c M RD hM hR hI a

end GivenModel

end CellCert

end Breakdown
