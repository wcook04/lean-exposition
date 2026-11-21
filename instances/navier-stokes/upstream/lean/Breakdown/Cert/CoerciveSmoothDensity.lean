import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.CoercivePairingSplit
import Breakdown.Cert.CoerciveSmoothDensityMeasure
import Breakdown.Cert.CoerciveSmoothDensitySquare
import Breakdown.Cert.CoerciveSmoothDensityIntegrable
import Breakdown.Cert.CoerciveSmoothDensityBase

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothDensity

open PairingSplitInternal (periodMeasure inner_integrable)
open ModeL2Internal (IsSquareField)

theorem iter_add_le (f g : ℝ → Space → ℝ≥0∞) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f σ y) + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, g σ y) ≤
      ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (f σ y + g σ y) :=
  (le_lintegral_add _ _).trans (lintegral_mono fun _ => le_lintegral_add _ _)

theorem iter_mono {f g : ℝ → Space → ℝ≥0∞} (h : ∀ σ y, f σ y ≤ g σ y) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f σ y) ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, g σ y :=
  lintegral_mono fun σ => lintegral_mono fun y => h σ y

theorem iter_add_left {f g : ℝ → Space → ℝ≥0∞}
    (hf : AEMeasurable (fun z : ℝ × Space => f z.1 z.2) periodMeasure) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (f σ y + g σ y) =
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f σ y) + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, g σ y := by
  have h1 : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), AEMeasurable (fun y => f σ y) volume := by
    filter_upwards [hf.aestronglyMeasurable.prodMk_left] with σ hσ
    exact hσ.aemeasurable
  have h2 : ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (f σ y + g σ y) =
      ∫⁻ σ in Set.Icc (0 : ℝ) 1, ((∫⁻ y, f σ y) + ∫⁻ y, g σ y) :=
    lintegral_congr_ae (h1.mono fun σ hσ => lintegral_add_left' hσ _)
  rw [h2, lintegral_add_left' (hf.lintegral_prod_right')]

theorem pos_neg_le (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a + ENNReal.ofReal (-(a.toReal - b.toReal)) ≤ ENNReal.ofReal (a.toReal - b.toReal) + b := by
  obtain ⟨x, hx, rfl⟩ : ∃ x, 0 ≤ x ∧ a = ENNReal.ofReal x :=
    ⟨a.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal ha).symm⟩
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ b = ENNReal.ofReal t :=
    ⟨b.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hb).symm⟩
  rw [ENNReal.toReal_ofReal hx, ENNReal.toReal_ofReal ht]
  rcases le_total t x with h | h
  · rw [ENNReal.ofReal_of_nonpos (p := -(x - t)) (by linarith), add_zero,
      ← ENNReal.ofReal_add (by linarith) ht]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · rw [ENNReal.ofReal_of_nonpos (p := x - t) (by linarith), zero_add,
      ← ENNReal.ofReal_add hx (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)

theorem max_split (x : ℝ) : max x 0 = x + max (-x) 0 := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring

theorem ofReal_four (a b c d : ℝ) :
    ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c + ENNReal.ofReal d
        + ENNReal.ofReal (-(a + b + c + d)) =
      ENNReal.ofReal (a + b + c + d) + (ENNReal.ofReal (-a) + ENNReal.ofReal (-b)
        + ENNReal.ofReal (-c) + ENNReal.ofReal (-d)) := by
  simp only [ENNReal.ofReal, ← ENNReal.coe_add, ENNReal.coe_inj]
  apply NNReal.eq
  simp only [NNReal.coe_add, Real.coe_toNNReal']
  have h1 := max_split a
  have h2 := max_split b
  have h3 := max_split c
  have h4 := max_split d
  have h5 := max_split (a + b + c + d)
  linarith

theorem ofReal_mode (pe pm bd re rm : ℝ) :
    ENNReal.ofReal (pe + pm) + ENNReal.ofReal (bd + re + rm)
        + (ENNReal.ofReal (-bd) + ENNReal.ofReal (-re) + ENNReal.ofReal (-rm)) ≤
      (ENNReal.ofReal pe + ENNReal.ofReal re) + (ENNReal.ofReal pm + ENNReal.ofReal rm) + ENNReal.ofReal bd
        + ENNReal.ofReal (-(bd + re + rm)) := by
  simp only [ENNReal.ofReal, ← ENNReal.coe_add, ENNReal.coe_le_coe]
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_add, Real.coe_toNNReal']
  have h0 : max (pe + pm) 0 ≤ max pe 0 + max pm 0 :=
    max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
      (add_nonneg (le_max_right _ _) (le_max_right _ _))
  have h1 := max_split bd
  have h2 := max_split re
  have h3 := max_split rm
  have h4 := max_split (bd + re + rm)
  linarith

theorem ofReal_neg_three (a b c : ℝ) :
    ENNReal.ofReal (-(a + b + c)) ≤ ENNReal.ofReal (-a) + ENNReal.ofReal (-b) + ENNReal.ofReal (-c) := by
  rw [neg_add, neg_add]
  exact ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)

theorem hbase {g pE pM pB jp nB nE nM jn r : ℝ → Space → ℝ≥0∞} {Xb Xj Xe Xm : ℝ}
    (hEi : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, pE σ y) + ENNReal.ofReal (-Xe) ≤
      ENNReal.ofReal Xe + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, nE σ y)
    (hMi : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, pM σ y) + ENNReal.ofReal (-Xm) ≤
      ENNReal.ofReal Xm + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, nM σ y)
    (hBi : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, pB σ y) + ENNReal.ofReal (-Xb) ≤
      ENNReal.ofReal Xb + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, nB σ y)
    (hJi : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, jp σ y) + ENNReal.ofReal (-Xj) ≤
      ENNReal.ofReal Xj + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, jn σ y)
    (fB : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, nB σ y) < ⊤)
    (fE : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, nE σ y) < ⊤)
    (fM : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, nM σ y) < ⊤)
    (fJ : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, jn σ y) < ⊤)
    (mE : AEMeasurable (fun z : ℝ × Space => pE z.1 z.2) periodMeasure)
    (mM : AEMeasurable (fun z : ℝ × Space => pM z.1 z.2) periodMeasure)
    (mB : AEMeasurable (fun z : ℝ × Space => pB z.1 z.2) periodMeasure)
    (mJ : AEMeasurable (fun z : ℝ × Space => jp z.1 z.2) periodMeasure)
    (hpt : ∀ σ y, g σ y + (nB σ y + nE σ y + nM σ y + jn σ y) ≤
      pE σ y + pM σ y + pB σ y + jp σ y + r σ y) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, g σ y) + ENNReal.ofReal (-(Xb + Xj + Xe + Xm)) ≤
      ENNReal.ofReal (Xb + Xj + Xe + Xm) + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, r σ y := by
  set I : (ℝ → Space → ℝ≥0∞) → ℝ≥0∞ := fun f => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f σ y with hI
  have hN : I nB + I nE + I nM + I jn ≤ I (fun σ y => nB σ y + nE σ y + nM σ y + jn σ y) := by
    calc I nB + I nE + I nM + I jn ≤ I (fun σ y => nB σ y + nE σ y) + I nM + I jn := by
          gcongr; exact iter_add_le _ _
      _ ≤ I (fun σ y => nB σ y + nE σ y + nM σ y) + I jn := by
          gcongr; exact iter_add_le (fun σ y => nB σ y + nE σ y) nM
      _ ≤ _ := iter_add_le (fun σ y => nB σ y + nE σ y + nM σ y) jn
  have hP : I (fun σ y => pE σ y + pM σ y + pB σ y + jp σ y + r σ y) =
      I pE + I pM + I pB + I jp + I r := by
    simp only [hI]
    rw [iter_add_left (f := fun σ y => pE σ y + pM σ y + pB σ y + jp σ y) (by exact ((mE.add mM).add mB).add mJ),
      iter_add_left (f := fun σ y => pE σ y + pM σ y + pB σ y) (by exact (mE.add mM).add mB),
      iter_add_left (f := fun σ y => pE σ y + pM σ y) (by exact mE.add mM), iter_add_left mE]
  have A1 : I g + (I nB + I nE + I nM + I jn) ≤ I pE + I pM + I pB + I jp + I r := by
    calc I g + (I nB + I nE + I nM + I jn) ≤ I g + I (fun σ y => nB σ y + nE σ y + nM σ y + jn σ y) := by
          gcongr
      _ ≤ I (fun σ y => g σ y + (nB σ y + nE σ y + nM σ y + jn σ y)) := iter_add_le _ _
      _ ≤ I (fun σ y => pE σ y + pM σ y + pB σ y + jp σ y + r σ y) := iter_mono hpt
      _ = _ := hP
  set S := ENNReal.ofReal (-Xb) + ENNReal.ofReal (-Xj) + ENNReal.ofReal (-Xe) + ENNReal.ofReal (-Xm) with hS
  set T := ENNReal.ofReal Xb + ENNReal.ofReal Xj + ENNReal.ofReal Xe + ENNReal.ofReal Xm with hT
  set N := I nB + I nE + I nM + I jn with hNdef
  have A2 : I pE + I pM + I pB + I jp + S ≤ T + N := by
    calc I pE + I pM + I pB + I jp + S = (I pB + ENNReal.ofReal (-Xb)) + (I jp + ENNReal.ofReal (-Xj))
          + (I pE + ENNReal.ofReal (-Xe)) + (I pM + ENNReal.ofReal (-Xm)) := by rw [hS]; ring
      _ ≤ (ENNReal.ofReal Xb + I nB) + (ENNReal.ofReal Xj + I jn) + (ENNReal.ofReal Xe + I nE)
          + (ENNReal.ofReal Xm + I nM) := add_le_add (add_le_add (add_le_add hBi hJi) hEi) hMi
      _ = T + N := by rw [hT, hNdef]; ring
  have hNfin : N ≠ ⊤ := by
    rw [hNdef]
    exact (ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨fB, fE⟩, fM⟩, fJ⟩).ne
  have hSfin : S ≠ ⊤ := by
    rw [hS]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
      ENNReal.ofReal_ne_top⟩, ENNReal.ofReal_ne_top⟩, ENNReal.ofReal_ne_top⟩
  have A3 : I g + S ≤ T + I r := by
    refine ENNReal.le_of_add_le_add_right hNfin ?_
    calc I g + S + N = (I g + N) + S := by ring
      _ ≤ (I pE + I pM + I pB + I jp + I r) + S := by gcongr
      _ = (I pE + I pM + I pB + I jp + S) + I r := by ring
      _ ≤ (T + N) + I r := by gcongr
      _ = T + I r + N := by ring
  have A4 : T + ENNReal.ofReal (-(Xb + Xj + Xe + Xm)) = ENNReal.ofReal (Xb + Xj + Xe + Xm) + S := by
    rw [hT, hS]; exact ofReal_four Xb Xj Xe Xm
  refine ENNReal.le_of_add_le_add_right hSfin ?_
  calc I g + ENNReal.ofReal (-(Xb + Xj + Xe + Xm)) + S = (I g + S) + ENNReal.ofReal (-(Xb + Xj + Xe + Xm)) := by
        ring
    _ ≤ (T + I r) + ENNReal.ofReal (-(Xb + Xj + Xe + Xm)) := by gcongr
    _ = (T + ENNReal.ofReal (-(Xb + Xj + Xe + Xm))) + I r := by ring
    _ = ENNReal.ofReal (Xb + Xj + Xe + Xm) + I r + S := by rw [A4]; ring

theorem combine {Pe Re Pm Rm Bd : ℝ → Space → ℤ × ℤ → ℝ} {J : ℝ → Space → ℝ} {Xe Xm Xb : ℝ}
    (hE : IsSplitLowerBound Xe Pe Re (fun _ _ => 0) (fun _ _ => 0))
    (hM : IsSplitLowerBound Xm Pm Rm (fun _ _ => 0) (fun _ _ => 0))
    (hB : IsDensityLowerBound Xb Bd)
    (hBfin : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal (-Bd σ y ι)) < ⊤)
    (hJ : Integrable (fun z : ℝ × Space => J z.1 z.2) periodMeasure)
    (mE : AEMeasurable (fun z : ℝ × Space =>
      (∑' ι, ENNReal.ofReal (Pe z.1 z.2 ι)) + ∑' ι, ENNReal.ofReal (Re z.1 z.2 ι)) periodMeasure)
    (mM : AEMeasurable (fun z : ℝ × Space =>
      (∑' ι, ENNReal.ofReal (Pm z.1 z.2 ι)) + ∑' ι, ENNReal.ofReal (Rm z.1 z.2 ι)) periodMeasure)
    (mB : AEMeasurable (fun z : ℝ × Space => ∑' ι, ENNReal.ofReal (Bd z.1 z.2 ι)) periodMeasure)
    (nB : AEMeasurable (fun z : ℝ × Space => ∑' ι, ENNReal.ofReal (-Bd z.1 z.2 ι)) periodMeasure)
    (nE : AEMeasurable (fun z : ℝ × Space => ∑' ι, ENNReal.ofReal (-Re z.1 z.2 ι)) periodMeasure) :
    IsSplitLowerBound (Xb + (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, J σ y) + Xe + Xm)
      (fun σ y ι => Pe σ y ι + Pm σ y ι) (fun σ y ι => Bd σ y ι + Re σ y ι + Rm σ y ι)
      (fun _ _ => 0) J := by
  obtain ⟨hE1, hE2⟩ := hE
  obtain ⟨hM1, hM2⟩ := hM
  simp only [neg_zero, ENNReal.ofReal_zero, add_zero] at hE1 hE2 hM1 hM2
  have jm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (J z.1 z.2)) periodMeasure :=
    hJ.aemeasurable.ennreal_ofReal
  have jnm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (-J z.1 z.2)) periodMeasure :=
    hJ.aemeasurable.neg.ennreal_ofReal
  have jp_eq : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (J σ y)) =
      ∫⁻ z, ENNReal.ofReal (J z.1 z.2) ∂periodMeasure := (lintegral_prod _ jm).symm
  have jn_eq : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-J σ y)) =
      ∫⁻ z, ENNReal.ofReal (-J z.1 z.2) ∂periodMeasure := (lintegral_prod _ jnm).symm
  have jint : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, J σ y) = ∫ z, J z.1 z.2 ∂periodMeasure :=
    (integral_prod _ hJ).symm
  have jpfin : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (J σ y)) < ⊤ := by
    rw [jp_eq]; exact hJ.lintegral_lt_top
  have jnfin : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-J σ y)) < ⊤ := by
    rw [jn_eq]; exact hJ.neg.lintegral_lt_top
  have hXj : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, J σ y) =
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (J σ y)).toReal
        - (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-J σ y)).toReal := by
    rw [jint, jp_eq, jn_eq]
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hJ
  have hJineq : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (J σ y))
      + ENNReal.ofReal (-(∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, J σ y)) ≤
      ENNReal.ofReal (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, J σ y)
        + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-J σ y) := by
    rw [hXj]
    exact pos_neg_le _ _ jpfin.ne jnfin.ne
  set Xj := ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, J σ y with hXjdef
  have negle : ∀ σ y, (∑' ι, ENNReal.ofReal (-(Bd σ y ι + Re σ y ι + Rm σ y ι))) ≤
      (∑' ι, ENNReal.ofReal (-Bd σ y ι)) + (∑' ι, ENNReal.ofReal (-Re σ y ι))
        + ∑' ι, ENNReal.ofReal (-Rm σ y ι) := by
    intro σ y
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum fun ι => ofReal_neg_three _ _ _
  have nsum : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ((∑' ι, ENNReal.ofReal (-Bd σ y ι))
        + (∑' ι, ENNReal.ofReal (-Re σ y ι)) + ∑' ι, ENNReal.ofReal (-Rm σ y ι))) =
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal (-Bd σ y ι))
        + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal (-Re σ y ι))
        + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal (-Rm σ y ι) := by
    rw [iter_add_left (by exact nB.add nE), iter_add_left (by exact nB)]
  refine ⟨?_, ?_⟩
  · simp only [neg_zero, ENNReal.ofReal_zero, add_zero]
    refine (iter_mono negle).trans_lt ?_
    rw [nsum]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨hBfin, hE1⟩, hM1⟩
  · simp only [neg_zero, ENNReal.ofReal_zero, add_zero]
    refine hbase (hEi := hE2) (hMi := hM2) (hBi := hB) (hJi := hJineq) (fB := hBfin) (fE := hE1) (fM := hM1)
      (fJ := jnfin) (mE := mE) (mM := mM) (mB := mB) (mJ := jm) ?_
    intro σ y
    have key : (∑' ι, ENNReal.ofReal (Pe σ y ι + Pm σ y ι))
        + (∑' ι, ENNReal.ofReal (Bd σ y ι + Re σ y ι + Rm σ y ι))
        + ((∑' ι, ENNReal.ofReal (-Bd σ y ι)) + (∑' ι, ENNReal.ofReal (-Re σ y ι))
          + ∑' ι, ENNReal.ofReal (-Rm σ y ι)) ≤
        ((∑' ι, ENNReal.ofReal (Pe σ y ι)) + ∑' ι, ENNReal.ofReal (Re σ y ι))
          + ((∑' ι, ENNReal.ofReal (Pm σ y ι)) + ∑' ι, ENNReal.ofReal (Rm σ y ι))
          + (∑' ι, ENNReal.ofReal (Bd σ y ι))
          + ∑' ι, ENNReal.ofReal (-(Bd σ y ι + Re σ y ι + Rm σ y ι)) := by
      simp only [← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum fun ι => ofReal_mode _ _ _ _ _
    calc _ = ((∑' ι, ENNReal.ofReal (Pe σ y ι + Pm σ y ι))
        + (∑' ι, ENNReal.ofReal (Bd σ y ι + Re σ y ι + Rm σ y ι))
        + ((∑' ι, ENNReal.ofReal (-Bd σ y ι)) + (∑' ι, ENNReal.ofReal (-Re σ y ι))
          + ∑' ι, ENNReal.ofReal (-Rm σ y ι))) + ENNReal.ofReal (J σ y) + ENNReal.ofReal (-J σ y) := by ring
      _ ≤ (((∑' ι, ENNReal.ofReal (Pe σ y ι)) + ∑' ι, ENNReal.ofReal (Re σ y ι))
          + ((∑' ι, ENNReal.ofReal (Pm σ y ι)) + ∑' ι, ENNReal.ofReal (Rm σ y ι))
          + (∑' ι, ENNReal.ofReal (Bd σ y ι))
          + ∑' ι, ENNReal.ofReal (-(Bd σ y ι + Re σ y ι + Rm σ y ι))) + ENNReal.ofReal (J σ y)
          + ENNReal.ofReal (-J σ y) := by gcongr
      _ = _ := by ring


theorem pairing_sum {k : ℕ} (X M : ℝ → Space → Space) (A : Fin k → ℝ → Space → Space) (κ : Fin k → ℝ)
    (hX : IsSquareField X) (hA : ∀ i, IsSquareField (A i)) (hM : IsSquareField M) :
    periodPairing (fun σ y => X σ y + ∑ i, κ i • A i σ y) M =
      periodPairing X M + ∑ i, κ i * periodPairing (A i) M := by
  have hint : ∀ {F : ℝ → Space → Space}, IsSquareField F →
      Integrable (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (M z.1 z.2)) periodMeasure :=
    fun hF => inner_integrable hF hM
  have hpe : ∀ {F : ℝ → Space → Space},
      Integrable (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (M z.1 z.2)) periodMeasure →
      periodPairing F M = ∫ z, inner ℝ (F z.1 z.2) (M z.1 z.2) ∂periodMeasure := fun h => by
    unfold periodPairing
    exact (integral_prod _ h).symm
  have hS : Integrable (fun z : ℝ × Space => ∑ i, κ i * inner ℝ (A i z.1 z.2) (M z.1 z.2)) periodMeasure :=
    integrable_finsetSum _ fun i _ => (hint (hA i)).const_mul (κ i)
  have hI : Integrable (fun z : ℝ × Space =>
      inner ℝ (X z.1 z.2 + ∑ i, κ i • A i z.1 z.2) (M z.1 z.2)) periodMeasure := by
    refine ((hint hX).add hS).congr (ae_of_all _ fun z => ?_)
    simp only [Pi.add_apply, inner_add_left, sum_inner, real_inner_smul_left]
  calc periodPairing (fun σ y => X σ y + ∑ i, κ i • A i σ y) M
      = ∫ z, inner ℝ (X z.1 z.2 + ∑ i, κ i • A i z.1 z.2) (M z.1 z.2) ∂periodMeasure :=
        hpe (F := fun σ y => X σ y + ∑ i, κ i • A i σ y) hI
    _ = ∫ z, (inner ℝ (X z.1 z.2) (M z.1 z.2) + ∑ i, κ i * inner ℝ (A i z.1 z.2) (M z.1 z.2))
          ∂periodMeasure := by
        congr 1
        funext z
        simp only [inner_add_left, sum_inner, real_inner_smul_left]
    _ = (∫ z, inner ℝ (X z.1 z.2) (M z.1 z.2) ∂periodMeasure)
          + ∑ i, κ i * ∫ z, inner ℝ (A i z.1 z.2) (M z.1 z.2) ∂periodMeasure := by
        rw [integral_add (hint hX) hS, integral_finsetSum _ fun i _ => (hint (hA i)).const_mul (κ i)]
        simp only [integral_const_mul]
    _ = _ := by
        rw [hpe (F := X) (hint hX)]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hpe (F := A i) (hint (hA i))]

theorem iterInt_add (f g : ℝ → Space → ℝ) (hf : Integrable (fun z : ℝ × Space => f z.1 z.2) periodMeasure)
    (hg : Integrable (fun z : ℝ × Space => g z.1 z.2) periodMeasure) :
    (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (f σ y + g σ y)) =
      (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, f σ y) + ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, g σ y := by
  have e1 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (f σ y + g σ y)) =
      ∫ z, (f z.1 z.2 + g z.1 z.2) ∂periodMeasure := (integral_prod _ (hf.add hg)).symm
  have e2 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, f σ y) = ∫ z, f z.1 z.2 ∂periodMeasure :=
    (integral_prod _ hf).symm
  have e3 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, g σ y) = ∫ z, g z.1 z.2 ∂periodMeasure :=
    (integral_prod _ hg).symm
  rw [e1, e2, e3, integral_add hf hg]

theorem aem_tsum {f : ℤ × ℤ → ℝ × Space → ℝ} (hf : ∀ ι, AEStronglyMeasurable (f ι) periodMeasure) :
    AEMeasurable (fun z => ∑' ι, ENNReal.ofReal (f ι z)) periodMeasure :=
  AEMeasurable.ennreal_tsum fun ι => (hf ι).aemeasurable.ennreal_ofReal

end Internal.SmoothDensity

open Internal.SmoothDensity in
theorem modeDensitySmoothHolds_of (hPars : ModeSquareSumHolds) (hSplit : ModePairingSplitSmoothHolds) (hI1 : EnergyIdentitySmoothHolds)
    (hBase : BaseDensitySmoothHolds) (hEps : ModeEpsEstimateSmoothHolds) (hMu : ModeMuEstimateSmoothHolds)
    (hSolenoidal : SolenoidalModeHolds) : ModeDensitySmoothHolds := by
  intro C m P b w k W act w₀ epsSup epsGradSup ratio hm hb hW hWp hWdiv hWdecay hwb hactm hactp hact2 v hv κ M hMF
  have hsq := smoothRight_square hv hW hWp hWdecay
  obtain ⟨Q, hQ, -⟩ := hSolenoidal _ hsq.1 hsq.2.1 hsq.2.2
  have hsplit := hSplit m P b w W hm hb hW hWp hWdiv hWdecay hwb v hv M Q hMF hQ
  have hI := hI1 P W v hm.period_pos hW hWp hWdiv hWdecay hv
  have hbase := hBase P m.classOf m.convD m.convZ m.c w w₀ hm.finite_classes hm.weight_pos hm.weight_lower hwb
    hm.weight_measurable hm.weight_axi hm.convD_smooth hm.convZ_smooth hm.convD_axi hm.convZ_axi
    hm.convD_decay hm.convZ_decay v hv
  have hE := hEps m P b w W hm hb hW hWp hWdiv hWdecay hwb v hv
  have hM := hMu m P b w W hm hb hW hWp hWdiv hWdecay hwb v hv Q hQ
  have hMsq : ModeL2Internal.IsSquareField M := ⟨hMF.1, hMF.2.1, hMF.2.2.1⟩
  have hlin := pairing_sum (smoothRight P W v) M act κ hsq (fun i => ⟨hactm i, hactp i, hact2 i⟩) hMsq
  have hJ := stretch_integrable hv hW hWdecay
  have hsplitI := iterInt_add
    (fun σ y => matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)
      + (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2)
    (fun σ y => stretchForm W v (gradField v) σ y) (vorticity_integrable hv) hJ
  beta_reduce at hsplitI
  have hX : m.multiplierGap P w act v (gradField v) (secondDerivField v) κ
      (fun σ y => smoothRight P W v σ y + ∑ i, κ i • act i σ y) M =
      (vorticityEnergy v - m.c * weightedEnergy w (gradField v) (secondDerivField v))
        + (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, stretchForm W v (gradField v) σ y)
        + epsPairing (fun ι y => m.epsW (m.classOf ι) y) v (smoothRight P W v)
        + (muPairing (fun ι y => m.muW (m.classOf ι) y) v Q - m.cμ * (m.frequencySeminormSq P v).toReal) := by
    unfold ModeWeights.multiplierGap
    rw [hlin, hsplit, hI, hsplitI]
    unfold vorticityEnergy
    ring
  rw [hX]
  exact combine hE hM hbase (base_neg_finite hPars hm hwb hv) hJ
    ((aem_tsum (f := fun ι z => modeEpsPos m P (gradField v) ι z.1 z.2) (aesm_epsPos hm hv)).add
      (aem_tsum (f := fun ι z => modeEpsRest m W v (gradField v) (secondDerivField v) ι z.1 z.2)
        (aesm_epsRest hm hW hv)))
    ((aem_tsum (f := fun ι z => modeMuPos m P v ι z.1 z.2) (aesm_muPos hm hv)).add
      (aem_tsum (f := fun ι z => modeMuRest m W v (gradField v) ι z.1 z.2) (aesm_muRest hm hW hv)))
    (aem_tsum (f := fun ι z => modeValues v ι z.1 z.2 (baseDensity m.convD m.convZ (m.classOf ι) m.c w z.2))
      (aesm_base hm hv))
    (aem_tsum (f := fun ι z => -modeValues v ι z.1 z.2 (baseDensity m.convD m.convZ (m.classOf ι) m.c w z.2))
      (fun ι => (aesm_base hm hv ι).neg))
    (aem_tsum (f := fun ι z => -modeEpsRest m W v (gradField v) (secondDerivField v) ι z.1 z.2)
      (fun ι => (aesm_epsRest hm hW hv ι).neg))

end Coercive

end Breakdown
