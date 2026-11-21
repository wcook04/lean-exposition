import Breakdown.FracCell.OnAxisLiftSt
import Breakdown.FracCell.CylIntegral

open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert Internal.SpectralBlocksMode

namespace Internal.OnAxisNorm

open Classical in
def cellInd (g : CellBlock) (s : Fin 2) (r z : ℝ) : ℝ :=
  if cylPoint r 0 z ∈ cellSolid g s then 1 else 0

def zLow (g : CellBlock) (s : Fin 2) : ℝ := if s = 0 then g.lowerHeight else -g.upperHeight

def zHigh (g : CellBlock) (s : Fin 2) : ℝ := if s = 0 then g.upperHeight else -g.lowerHeight

theorem mem_cell (g : CellBlock) (hin : g.innerRadius = 0) (s : Fin 2) {r : ℝ} (hr : 0 < r) (z : ℝ) :
    cylPoint r 0 z ∈ cellSolid g s ↔ r ≤ g.outerRadius ∧ zLow g s ≤ z ∧ z ≤ zHigh g s := by
  simp only [cellSolid, Set.mem_ofPred_eq, radial_cyl hr, cyl2, hin, zLow, zHigh]
  fin_cases s
  · simp only [Fin.zero_eta, if_true]
    constructor
    · rintro ⟨-, h1, h2, h3⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨hr.le, h1, h2, h3⟩
  · simp only [Fin.mk_one, one_ne_zero, if_false]
    constructor
    · rintro ⟨-, h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨hr.le, h1, by linarith, by linarith⟩

theorem field_cyl (g : CellBlock) (f : Fin 2 → Fin 3 → ℝ → ℝ → ℝ) {r : ℝ} (hr : 0 < r) {θ : ℝ}
    (hθ : θ ∈ Set.Ioc (-π) π) (z : ℝ) :
    ∑ s : Fin 2, Set.indicator (cellSolid g s)
        (fun w => ∑ c : Fin 3, f s c (radialCoord w) (w 2) • frameVector c w) (cylPoint r θ z)
      = ∑ c : Fin 3, (∑ s : Fin 2, cellInd g s r z * f s c r z) • frameAt c θ := by
  classical
  simp only [Set.indicator_apply, solid_iff g _ hr θ z, frame_eq, angle_cyl hr hθ, radial_cyl hr, cyl2, cellInd]
  simp only [Fin.sum_univ_two, Fin.sum_univ_three]
  split_ifs <;> simp only [one_mul, zero_mul, add_zero, zero_add, add_smul, zero_smul]; abel

theorem norm_cyl (g : CellBlock) (f : Fin 2 → Fin 3 → ℝ → ℝ → ℝ) {r : ℝ} (hr : 0 < r) {θ : ℝ}
    (hθ : θ ∈ Set.Ioc (-π) π) (z : ℝ) :
    ‖∑ s : Fin 2, Set.indicator (cellSolid g s)
        (fun w => ∑ c : Fin 3, f s c (radialCoord w) (w 2) • frameVector c w) (cylPoint r θ z)‖ ^ 2
      = ∑ c : Fin 3, (∑ s : Fin 2, cellInd g s r z * f s c r z) ^ 2 := by
  rw [field_cyl g f hr hθ z, ← real_inner_self_eq_norm_sq, inner_frame_sum]
  exact Finset.sum_congr rfl fun c _ => (sq _).symm

theorem ind_cases (g : CellBlock) (s : Fin 2) (r z : ℝ) : cellInd g s r z = 0 ∨ cellInd g s r z = 1 := by
  unfold cellInd
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem ind_cross (g : CellBlock) (hin : g.innerRadius = 0) (hlow : 0 ≤ g.lowerHeight) {r : ℝ} (hr : 0 < r)
    {z : ℝ} (hz : z ≠ 0) : cellInd g 0 r z * cellInd g 1 r z = 0 := by
  unfold cellInd
  split_ifs with h0 h1
  · exfalso
    have a := (mem_cell g hin 0 hr z).1 h0
    have b := (mem_cell g hin 1 hr z).1 h1
    simp only [zLow, zHigh, if_true, one_ne_zero, if_false] at a b
    exact hz (by linarith)
  all_goals simp

theorem sq_split (g : CellBlock) (hin : g.innerRadius = 0) (hlow : 0 ≤ g.lowerHeight)
    (f : Fin 2 → Fin 3 → ℝ → ℝ → ℝ) {r : ℝ} (hr : 0 < r) {z : ℝ} (hz : z ≠ 0) :
    r * ∑ c : Fin 3, (∑ s : Fin 2, cellInd g s r z * f s c r z) ^ 2
      = ∑ s : Fin 2, ∑ c : Fin 3, cellInd g s r z * (f s c r z ^ 2 * r) := by
  have hx := ind_cross g hin hlow hr hz
  simp only [Fin.sum_univ_two, Fin.sum_univ_three]
  rcases ind_cases g 0 r z with h0 | h0 <;> rcases ind_cases g 1 r z with h1 | h1 <;>
    rw [h0, h1] at hx ⊢
  all_goals first | (exfalso; norm_num at hx; done) | ring

theorem piece (g : CellBlock) (hin : g.innerRadius = 0) (hR : 0 < g.outerRadius) (hz : g.lowerHeight < g.upperHeight)
    (f₀ : ℝ → ℝ → ℝ) (hf : Continuous (Function.uncurry f₀)) (s : Fin 2) :
    IntegrableOn (fun q : ℝ × ℝ => cellInd g s q.1 q.2 * (f₀ q.1 q.2 ^ 2 * q.1))
        (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) ∧
      ∫ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), cellInd g s q.1 q.2 * (f₀ q.1 q.2 ^ 2 * q.1)
        = ∫ r in (0 : ℝ)..g.outerRadius, ∫ z in zLow g s..zHigh g s, f₀ r z ^ 2 * r := by
  have hSm : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  have hab : zLow g s ≤ zHigh g s := by
    unfold zLow zHigh
    split_ifs <;> linarith
  have hB : MeasurableSet (Set.Ioc 0 g.outerRadius ×ˢ Set.Icc (zLow g s) (zHigh g s)) :=
    measurableSet_Ioc.prod measurableSet_Icc
  have hBS : Set.Ioc 0 g.outerRadius ×ˢ Set.Icc (zLow g s) (zHigh g s) ⊆ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ) :=
    fun q hq => ⟨hq.1.1, Set.mem_univ _⟩
  have hc : Continuous (fun q : ℝ × ℝ => f₀ q.1 q.2 ^ 2 * q.1) := (hf.pow 2).mul continuous_fst
  have hInt : IntegrableOn (fun q : ℝ × ℝ => f₀ q.1 q.2 ^ 2 * q.1)
      (Set.Ioc 0 g.outerRadius ×ˢ Set.Icc (zLow g s) (zHigh g s)) :=
    (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self subset_rfl)
  have heq : ∀ q ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), cellInd g s q.1 q.2 * (f₀ q.1 q.2 ^ 2 * q.1)
      = (Set.Ioc 0 g.outerRadius ×ˢ Set.Icc (zLow g s) (zHigh g s)).indicator
          (fun q : ℝ × ℝ => f₀ q.1 q.2 ^ 2 * q.1) q := by
    intro q hq
    have hr : 0 < q.1 := hq.1
    unfold cellInd
    by_cases hm : cylPoint q.1 0 q.2 ∈ cellSolid g s
    · have h3 := (mem_cell g hin s hr q.2).1 hm
      rw [if_pos hm, one_mul, Set.indicator_of_mem]
      exact ⟨⟨hr, h3.1⟩, h3.2.1, h3.2.2⟩
    · rw [if_neg hm, zero_mul, Set.indicator_of_notMem]
      intro hq'
      exact hm ((mem_cell g hin s hr q.2).2 ⟨hq'.1.2, hq'.2.1, hq'.2.2⟩)
  constructor
  · refine (integrableOn_congr_fun (fun q hq => (heq q hq).symm) hSm).1 ?_
    exact (hInt.integrable_indicator hB).integrableOn
  · rw [setIntegral_congr_fun hSm heq, setIntegral_indicator hB, Set.inter_eq_right.mpr hBS,
      Measure.volume_eq_prod, setIntegral_prod _ hInt, intervalIntegral.integral_of_le hR.le]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    simp only []
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

end Internal.OnAxisNorm

open Internal.OnAxisNorm in
theorem axisNorm_holds : AxisNormStatement := by
  intro g f hin hR hz hlow hf hF2
  set F : Space → Space := fun y => ∑ s : Fin 2, Set.indicator (cellSolid g s)
      (fun w => ∑ c : Fin 3, f s c (radialCoord w) (w 2) • frameVector c w) y with hFdef
  have hI : Integrable (fun y => ‖F y‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hF2.1).1 hF2
  have hpi : -π ≤ π := by linarith [Real.pi_pos]
  have hSm : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  have hnull : ∀ᵐ q : ℝ × ℝ ∂volume, q.2 ≠ 0 := by
    have h0 : volume ((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ)) = 0 := by
      rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp
    rw [ae_iff]
    refine measure_mono_null (fun q hq => ?_) h0
    simp only [ne_eq, not_not, Set.mem_ofPred_eq] at hq
    exact ⟨Set.mem_univ _, hq⟩
  have step1 : ∫ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), q.1 * ∫ θ in (-π)..π, ‖F (cylPoint q.1 θ q.2)‖ ^ 2
      = ∫ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ),
          2 * π * ∑ s : Fin 2, ∑ c : Fin 3, cellInd g s q.1 q.2 * (f s c q.1 q.2 ^ 2 * q.1) := by
    refine setIntegral_congr_ae hSm ?_
    filter_upwards [hnull] with q hq hqS
    have hr : 0 < q.1 := hqS.1
    have e : ∫ θ in (-π)..π, ‖F (cylPoint q.1 θ q.2)‖ ^ 2
        = ∫ θ in (-π)..π, ∑ c : Fin 3, (∑ s : Fin 2, cellInd g s q.1 q.2 * f s c q.1 q.2) ^ 2 := by
      rw [intervalIntegral.integral_of_le hpi, intervalIntegral.integral_of_le hpi]
      exact setIntegral_congr_fun measurableSet_Ioc fun θ hθ => norm_cyl g f hr hθ q.2
    rw [e, intervalIntegral.integral_const, smul_eq_mul, ← sq_split g hin hlow f hr hq]
    ring
  rw [cylIntegral _ hI, step1, integral_const_mul]
  congr 1
  have hp := fun s c => piece g hin hR hz (f s c) (hf s c) s
  rw [integral_finsetSum _ fun s _ => integrable_finsetSum _ fun c _ => (hp s c).1]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_finsetSum _ fun c _ => (hp s c).1]
  exact Finset.sum_congr rfl fun c _ => (hp s c).2

end Spectral

end CellCert

end Breakdown
