import Breakdown.FracCell.ReductionLossKernelBoundSheet
import Breakdown.FracCert.LinearSolveCore

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

private theorem gapDist_le_aux (aLo : ℝ) (aHi : Option ℝ) (bLo : ℝ) (bHi : Option ℝ) (s t : ℝ) (h1 : aLo ≤ s)
    (h2 : ∀ h, aHi = some h → s ≤ h) (h3 : bLo ≤ t) (h4 : ∀ h, bHi = some h → t ≤ h) :
    0 ≤ gapDist aLo aHi bLo bHi ∧ gapDist aLo aHi bLo bHi ≤ |s - t| := by
  refine ⟨le_max_left _ _, ?_⟩
  have hA : ∀ h, bHi = some h → aLo - h ≤ |s - t| := fun h hh => le_abs.2 (Or.inl (by linarith [h4 h hh]))
  have hB : ∀ h, aHi = some h → bLo - h ≤ |s - t| := fun h hh => le_abs.2 (Or.inr (by linarith [h2 h hh]))
  unfold gapDist
  refine max_le (abs_nonneg _) (max_le ?_ ?_)
  · cases bHi with
    | none => exact abs_nonneg _
    | some h => exact hA h rfl
  · cases aHi with
    | none => exact abs_nonneg _
    | some h => exact hB h rfl

private theorem sq_le_of_gap_aux {g u : ℝ} (h0 : 0 ≤ g) (h : g ≤ |u|) : g ^ 2 ≤ u ^ 2 := by
  rw [← sq_abs u]
  exact pow_le_pow_left₀ h0 h 2

private theorem horizontal_gap_aux (x y : Space) :
    (horizontalNorm x - horizontalNorm y) ^ 2 ≤ (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  unfold horizontalNorm
  have hx := Real.sq_sqrt (add_nonneg (sq_nonneg (x 0)) (sq_nonneg (x 1)))
  have hy := Real.sq_sqrt (add_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1)))
  have hx0 := Real.sqrt_nonneg (x 0 ^ 2 + x 1 ^ 2)
  have hy0 := Real.sqrt_nonneg (y 0 ^ 2 + y 1 ^ 2)
  set p := Real.sqrt (x 0 ^ 2 + x 1 ^ 2)
  set q := Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
  have hpq : x 0 * y 0 + x 1 * y 1 ≤ p * q := by
    have hsq : (x 0 * y 0 + x 1 * y 1) ^ 2 ≤ (p * q) ^ 2 := by
      rw [mul_pow, hx, hy]
      nlinarith [sq_nonneg (x 0 * y 1 - x 1 * y 0)]
    exact abs_le_of_sq_le_sq' hsq (mul_nonneg hx0 hy0) |>.2
  nlinarith

private theorem norm_sq_aux (v : Space) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [Fin.sum_univ_three]

private theorem horizontalNorm_mirror_aux (x : Space) : horizontalNorm (mirror x) = horizontalNorm x := by
  unfold horizontalNorm
  rw [(LinearSolveCore.mirror_apply x).1, (LinearSolveCore.mirror_apply x).2.1]

private theorem firstDist_le_aux (m : ℕ) (V : Space → ℝ) (D : CellSumData) (hD : IsCellSumData m V D)
    (a : Fin D.boxCount) (b : Fin D.pieceCount) (mirrored : Bool) (x : Space) (hz : 0 ≤ x 2)
    (hρlo : D.boxRhoLo a ≤ horizontalNorm x) (hρhi : ∀ h, D.boxRhoHi a = some h → horizontalNorm x ≤ h)
    (hzlo : D.boxZLo a ≤ x 2) (hzhi : ∀ h, D.boxZHi a = some h → x 2 ≤ h) (y : Space) (hy : y ∈ D.pieceSolid b) :
    D.sectorDist m a b mirrored 0 ≤ ‖(if mirrored then mirror x else x) - y‖ := by
  obtain ⟨p1, p2, p3, p4⟩ := hD.piece_solid b y hy
  obtain ⟨q1, q2, q3, q4⟩ := hD.piece_box b
  obtain ⟨r1, r2⟩ := hD.box_lower a
  have hρ := gapDist_le_aux (D.boxRhoLo a) (D.boxRhoHi a) (D.pieceRhoLo b) (D.pieceRhoHi b)
    (horizontalNorm x) (horizontalNorm y) hρlo hρhi p1 p2
  have hρsq := sq_le_of_gap_aux hρ.1 hρ.2
  have hh := horizontal_gap_aux x y
  unfold CellSumData.sectorDist
  simp only [CharP.cast_eq_zero, mul_zero, zero_div, Real.sin_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero]
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_aux]
  apply Real.sqrt_le_sqrt
  cases mirrored with
  | false =>
    have hzg := gapDist_le_aux (D.boxZLo a) (D.boxZHi a) (D.pieceZLo b) (D.pieceZHi b) (x 2) (y 2)
      hzlo hzhi p3 p4
    have hzsq := sq_le_of_gap_aux hzg.1 hzg.2
    simp only [Bool.false_eq_true, if_false, PiLp.sub_apply]
    linarith
  | true =>
    obtain ⟨m0, m1, m2⟩ := LinearSolveCore.mirror_apply x
    simp only [if_true, PiLp.sub_apply, m0, m1, m2]
    have hzsq : (D.boxZLo a + D.pieceZLo b) ^ 2 ≤ (-x 2 - y 2) ^ 2 := by
      nlinarith
    linarith

private theorem solid_integrable_aux (m : ℕ) (V : Space → ℝ) (D : CellSumData) (hD : IsCellSumData m V D)
    (b : Fin D.pieceCount) : IntegrableOn V (D.pieceSolid b) := hD.mass_integrable b

private theorem cover_integral_le_aux (K : Space → ℝ) (S : Set Space) (s : Finset ℕ) (T : ℕ → Set Space)
    (hK0 : ∀ y, 0 ≤ K y) (hKi : IntegrableOn K S) (hS : MeasurableSet S) (hT : ∀ j, MeasurableSet (T j))
    (hsub : ∀ j ∈ s, T j ⊆ S) (hcov : ∀ y ∈ S, ∃ j ∈ s, y ∈ T j) :
    (∫ y in S, K y) ≤ ∑ j ∈ s, ∫ y in T j, K y := by
  have hTi : ∀ j ∈ s, Integrable ((T j).indicator K) := fun j hj =>
    (integrable_indicator_iff (hT j)).2 (hKi.mono_set (hsub j hj))
  rw [← integral_indicator hS]
  have hsum : (∑ j ∈ s, ∫ y in T j, K y) = ∫ y, ∑ j ∈ s, (T j).indicator K y := by
    rw [integral_finsetSum _ hTi]
    exact Finset.sum_congr rfl fun j _ => (integral_indicator (hT j)).symm
  rw [hsum]
  refine integral_mono ((integrable_indicator_iff hS).2 hKi) (integrable_finsetSum _ hTi) fun y => ?_
  have hnn : ∀ j ∈ s, 0 ≤ (T j).indicator K y := fun j _ => Set.indicator_nonneg (fun y _ => hK0 y) y
  by_cases hy : y ∈ S
  · obtain ⟨j, hj, hyj⟩ := hcov y hy
    rw [Set.indicator_of_mem hy]
    refine le_trans (le_of_eq (Set.indicator_of_mem hyj K).symm) (Finset.single_le_sum hnn hj)
  · rw [Set.indicator_of_notMem hy]
    exact Finset.sum_nonneg hnn

private theorem reflect_sum_aux (f : ℕ → ℝ) (k : ℕ) :
    (∑ j ∈ Finset.range (k + k), f (min j (k + k - 1 - j))) = ∑ i ∈ Finset.range k, 2 * f i := by
  rw [Finset.sum_range_add]
  have h1 : (∑ j ∈ Finset.range k, f (min j (k + k - 1 - j))) = ∑ j ∈ Finset.range k, f j :=
    Finset.sum_congr rfl fun j hj => by
      rw [Finset.mem_range] at hj
      rw [Nat.min_eq_left (by omega)]
  have h2 : (∑ j ∈ Finset.range k, f (min (k + j) (k + k - 1 - (k + j)))) = ∑ j ∈ Finset.range k, f (k - 1 - j) :=
    Finset.sum_congr rfl fun j hj => by
      rw [Finset.mem_range] at hj
      rw [Nat.min_eq_right (by omega)]
      congr 1
      omega
  rw [h1, h2, Finset.sum_range_reflect f k, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem reflect_sum_inner_aux (f : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (∑ j ∈ Finset.Ico 1 (k + k - 1), f (min j (k + k - 1 - j))) = ∑ i ∈ Finset.Ico 1 k, 2 * f i := by
  have hfull := reflect_sum_aux f k
  have e1 : Finset.range (k + k) = Finset.Ico 0 (k + k - 1 + 1) := by
    rw [Finset.range_eq_Ico]
    congr 1
    omega
  set g : ℕ → ℝ := fun j => f (min j (k + k - 1 - j)) with hg
  have hA : (∑ j ∈ Finset.Ico 0 (k + k - 1 + 1), g j) = (∑ j ∈ Finset.Ico 0 (k + k - 1), g j) + g (k + k - 1) :=
    Finset.sum_Ico_succ_top (by omega) g
  have hB : (∑ j ∈ Finset.Ico 0 (k + k - 1), g j) = g 0 + ∑ j ∈ Finset.Ico (0 + 1) (k + k - 1), g j :=
    Finset.sum_eq_sum_Ico_succ_bot (by omega) g
  have hC : (∑ i ∈ Finset.Ico 0 k, 2 * f i) = 2 * f 0 + ∑ i ∈ Finset.Ico (0 + 1) k, 2 * f i :=
    Finset.sum_eq_sum_Ico_succ_bot (by omega) (fun i => 2 * f i)
  have e2 : g 0 = f 0 := by
    simp only [hg]
    congr 1
  have e3 : g (k + k - 1) = f 0 := by
    simp only [hg]
    congr 1
    omega
  rw [e1, hA, hB, Finset.range_eq_Ico, hC] at hfull
  rw [e2, e3] at hfull
  simp only [zero_add] at hfull
  linarith

private theorem sectorKernel_le (m : ℕ) (V : Space → ℝ) (D : CellSumData) (hD : IsCellSumData m V D)
    (a : Fin D.boxCount) (b : Fin D.pieceCount) (mirrored : Bool) (x : Space) (hz : 0 ≤ x 2)
    (hρlo : D.boxRhoLo a ≤ horizontalNorm x) (hρhi : ∀ h, D.boxRhoHi a = some h → horizontalNorm x ≤ h)
    (hzlo : D.boxZLo a ≤ x 2) (hzhi : ∀ h, D.boxZHi a = some h → x 2 ≤ h) :
    (∫ y in D.pieceSolid b, V y / (4 * Real.pi * ‖(if mirrored then mirror x else x) - y‖))
      ≤ D.sectorSum m a b mirrored 0 := by
  classical
  set x' := (if mirrored then mirror x else x) with hx'
  set S := D.pieceSolid b with hS
  set T : ℕ → Set Space := fun j => KernelSectors.sectorPart m x S j with hT
  have hKi : IntegrableOn (fun y => V y / (4 * Real.pi * ‖x' - y‖)) S :=
    (shellKernel_le_ae V S x' (D.pieceMass b) (D.pieceSup b) 0 (hD.solid_measurable b) hD.measurable hD.nonneg
      (hD.sup_nonneg b) (hD.sup_le b) (solid_integrable_aux m V D hD b) (hD.mass_le b) le_rfl
      fun y _ => norm_nonneg _).1
  have hK0 : ∀ y, 0 ≤ V y / (4 * Real.pi * ‖x' - y‖) := fun y => by
    have := hD.nonneg y
    positivity
  have hTm : ∀ j, MeasurableSet (T j) := fun j =>
    KernelSectors.sectorPart_measurable m x S (hD.solid_measurable b) j
  have hTS : ∀ j, T j ⊆ S := fun j y hy => hy.1
  obtain ⟨k, hk⟩ := hD.order_even.1
  have hm4 := hD.order_even.2
  have hm2 : m / 2 = k := by omega
  set f : ℕ → ℝ := fun i => kernelShell (D.pieceMass b / m) (D.pieceSup b) (D.sectorDist m a b mirrored i) with hf
  have hpart : ∀ j < m, (∫ y in T j, V y / (4 * Real.pi * ‖x' - y‖)) ≤ f (min j (m - 1 - j)) := by
    intro j hj
    exact (shellKernel_le_ae V (T j) x' (D.pieceMass b / m) (D.pieceSup b) _ (hTm j) hD.measurable hD.nonneg
      (hD.sup_nonneg b) ((hD.sup_le b).mono fun y hy hyT => hy (hTS j hyT))
      ((solid_integrable_aux m V D hD b).mono_set (hTS j))
      (KernelSectors.sectorPart_mass m V D hD b x j hj) (Real.sqrt_nonneg _)
      (fun y hy => KernelSectors.sectorPart_dist m V D hD a b mirrored x hz hρlo hρhi hzlo hzhi j hj y hy)).2
  have hcov := cover_integral_le_aux _ S (Finset.range m) T hK0 hKi (hD.solid_measurable b) hTm
    (fun j _ => hTS j) (fun y hy => by
      obtain ⟨j, hj, hyj⟩ := KernelSectors.sectorPart_cover m (by omega) x S y hy
      exact ⟨j, Finset.mem_range.2 hj, hyj⟩)
  have hsum := reflect_sum_aux f k
  rw [← hk] at hsum
  refine hcov.trans ((Finset.sum_le_sum fun j hj => hpart j (Finset.mem_range.1 hj)).trans (le_of_eq ?_))
  rw [hsum]
  unfold CellSumData.sectorSum
  rw [hm2, Finset.range_eq_Ico]

private theorem nearKernel_le (m : ℕ) (V : Space → ℝ) (D : CellSumData) (hD : IsCellSumData m V D)
    (a : Fin D.boxCount) (b : Fin D.pieceCount) (mirrored : Bool) (x : Space) (hz : 0 ≤ x 2)
    (hρlo : D.boxRhoLo a ≤ horizontalNorm x) (hρhi : ∀ h, D.boxRhoHi a = some h → horizontalNorm x ≤ h)
    (hzlo : D.boxZLo a ≤ x 2) (hzhi : ∀ h, D.boxZHi a = some h → x 2 ≤ h)
    (hrule : D.rule a b mirrored = 2) :
    (∫ y in D.pieceSolid b, V y / (4 * Real.pi * ‖(if mirrored then mirror x else x) - y‖))
      ≤ D.nearTerm m a b mirrored + D.sectorSum m a b mirrored 1 := by
  classical
  set x' := (if mirrored then mirror x else x) with hx'
  set S := D.pieceSolid b with hS
  set T : ℕ → Set Space := fun j => KernelSectors.sectorPart m x S j with hT
  have hKi : IntegrableOn (fun y => V y / (4 * Real.pi * ‖x' - y‖)) S :=
    (shellKernel_le_ae V S x' (D.pieceMass b) (D.pieceSup b) 0 (hD.solid_measurable b) hD.measurable hD.nonneg
      (hD.sup_nonneg b) (hD.sup_le b) (solid_integrable_aux m V D hD b) (hD.mass_le b) le_rfl
      fun y _ => norm_nonneg _).1
  have hK0 : ∀ y, 0 ≤ V y / (4 * Real.pi * ‖x' - y‖) := fun y => by
    have := hD.nonneg y
    positivity
  have hTm : ∀ j, MeasurableSet (T j) := fun j =>
    KernelSectors.sectorPart_measurable m x S (hD.solid_measurable b) j
  have hTS : ∀ j, T j ⊆ S := fun j y hy => hy.1
  obtain ⟨k, hk⟩ := hD.order_even.1
  have hm4 := hD.order_even.2
  have hm2 : m / 2 = k := by omega
  set f : ℕ → ℝ := fun i => kernelShell (D.pieceMass b / m) (D.pieceSup b) (D.sectorDist m a b mirrored i) with hf
  have hpart : ∀ j < m, (∫ y in T j, V y / (4 * Real.pi * ‖x' - y‖)) ≤ f (min j (m - 1 - j)) := by
    intro j hj
    exact (shellKernel_le_ae V (T j) x' (D.pieceMass b / m) (D.pieceSup b) _ (hTm j) hD.measurable hD.nonneg
      (hD.sup_nonneg b) ((hD.sup_le b).mono fun y hy hyT => hy (hTS j hyT))
      ((solid_integrable_aux m V D hD b).mono_set (hTS j))
      (KernelSectors.sectorPart_mass m V D hD b x j hj) (Real.sqrt_nonneg _)
      (fun y hy => KernelSectors.sectorPart_dist m V D hD a b mirrored x hz hρlo hρhi hzlo hzhi j hj y hy)).2
  set T' : ℕ → Set Space := fun j => if j = 0 then T 0 ∪ T (m - 1) else T j with hT'
  have hT'm : ∀ j, MeasurableSet (T' j) := fun j => by
    simp only [hT']
    split_ifs
    · exact (hTm 0).union (hTm (m - 1))
    · exact hTm j
  have hT'S : ∀ j, T' j ⊆ S := fun j => by
    simp only [hT']
    split_ifs
    · exact Set.union_subset (hTS 0) (hTS (m - 1))
    · exact hTS j
  have h0 : (0 : ℕ) ∉ Finset.Ico 1 (m - 1) := by simp
  have hcov := cover_integral_le_aux _ S (insert 0 (Finset.Ico 1 (m - 1))) T' hK0 hKi (hD.solid_measurable b) hT'm
    (fun j _ => hT'S j) (fun y hy => by
      obtain ⟨j, hj, hyj⟩ := KernelSectors.sectorPart_cover m (by omega) x S y hy
      by_cases hj0 : j = 0
      · subst hj0
        exact ⟨0, Finset.mem_insert_self _ _, by simp only [hT', if_pos rfl]; exact Or.inl hyj⟩
      · by_cases hjm : j = m - 1
        · subst hjm
          exact ⟨0, Finset.mem_insert_self _ _, by simp only [hT', if_pos rfl]; exact Or.inr hyj⟩
        · refine ⟨j, Finset.mem_insert_of_mem (Finset.mem_Ico.2 ⟨by omega, by omega⟩), ?_⟩
          simp only [hT', if_neg hj0]
          exact hyj)
  rw [Finset.sum_insert h0] at hcov
  have hnear : (∫ y in T' 0, V y / (4 * Real.pi * ‖x' - y‖)) ≤ D.nearTerm m a b mirrored := by
    simp only [hT', if_pos rfl]
    exact KernelSectors.twoSector_near m V D hD a b mirrored x hz hρlo hρhi hzlo hzhi hrule
  have hrest : (∑ j ∈ Finset.Ico 1 (m - 1), ∫ y in T' j, V y / (4 * Real.pi * ‖x' - y‖))
      ≤ D.sectorSum m a b mirrored 1 := by
    have hsum := reflect_sum_inner_aux f k (by omega)
    rw [← hk] at hsum
    refine (Finset.sum_le_sum (g := fun j => f (min j (m - 1 - j))) fun j hj => ?_).trans (le_of_eq ?_)
    · have hj' := Finset.mem_Ico.1 hj
      have hj0 : j ≠ 0 := by omega
      simp only [hT', if_neg hj0]
      exact hpart j (by omega)
    · rw [hsum]
      unfold CellSumData.sectorSum
      rw [hm2]
  linarith

theorem pieceKernel_le (m : ℕ) (V : Space → ℝ) (D : CellSumData) (hD : IsCellSumData m V D)
    (a : Fin D.boxCount) (b : Fin D.pieceCount) (mirrored : Bool) (x : Space) (hz : 0 ≤ x 2)
    (hρlo : D.boxRhoLo a ≤ horizontalNorm x) (hρhi : ∀ h, D.boxRhoHi a = some h → horizontalNorm x ≤ h)
    (hzlo : D.boxZLo a ≤ x 2) (hzhi : ∀ h, D.boxZHi a = some h → x 2 ≤ h) :
    IntegrableOn (fun y => V y / (4 * Real.pi * ‖(if mirrored then mirror x else x) - y‖)) (D.pieceSolid b) ∧
      (∫ y in D.pieceSolid b, V y / (4 * Real.pi * ‖(if mirrored then mirror x else x) - y‖))
        ≤ D.pairTerm m a b mirrored := by
  have hshell := fun d (hd : 0 ≤ d) (hdist : ∀ y ∈ D.pieceSolid b, d ≤ ‖(if mirrored then mirror x else x) - y‖) =>
    shellKernel_le_ae V (D.pieceSolid b) (if mirrored then mirror x else x) (D.pieceMass b) (D.pieceSup b) d
      (hD.solid_measurable b) hD.measurable hD.nonneg (hD.sup_nonneg b) (hD.sup_le b)
      (solid_integrable_aux m V D hD b) (hD.mass_le b) hd hdist
  refine ⟨(hshell 0 le_rfl fun y _ => norm_nonneg _).1, ?_⟩
  unfold CellSumData.pairTerm
  match hr : D.rule a b mirrored with
  | 0 => exact sectorKernel_le m V D hD a b mirrored x hz hρlo hρhi hzlo hzhi
  | 1 => exact (hshell _ (Real.sqrt_nonneg _)
      (firstDist_le_aux m V D hD a b mirrored x hz hρlo hρhi hzlo hzhi)).2
  | 2 => exact nearKernel_le m V D hD a b mirrored x hz hρlo hρhi hzlo hzhi hr

end Reduction

end CellCert

end Breakdown
