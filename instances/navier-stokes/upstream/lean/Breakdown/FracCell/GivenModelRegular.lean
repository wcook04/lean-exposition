import Breakdown.FracCell.GivenModelDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenModel

open SteadyCert CellAnalysis

theorem weight_clauses {k N : ℕ} (c : FracCellData k N) (w₀ : ℝ) (hw : c.weight = fun _ => w₀)
    (hpos : 0 < w₀) (hmin : c.weightMin = w₀) (hmax : c.weightMax = w₀) :
    Measurable c.weight ∧ 0 < c.weightMin ∧ (∀ y, c.weightMin ≤ c.weight y) ∧ (∀ y, c.weight y ≤ c.weightMax) ∧
      IsClassScalar c.order c.weight ∧ ∀ K : CellBox, ∀ p ∈ K.rect, ∀ θ : ℝ, c.weight (cylPoint p.1 θ p.2) = CellScalars.sampleWeight c p := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hw]; exact measurable_const
  · rw [hmin]; exact hpos
  · intro y; rw [hw, hmin]
  · intro y; rw [hw, hmax]
  · refine ⟨fun y => ?_, fun y => ?_⟩ <;> rw [hw]
  · intro K p _ θ
    unfold CellScalars.sampleWeight
    rw [hw]

private theorem rHat_measurable (K : CellBox) : Measurable (CellScalars.rHat K) := by
  unfold CellScalars.rHat CellBox.lineWeight
  by_cases h : K.r₁ = 0
  · simp only [h, if_true]
    exact measurable_fst.div measurable_fst
  · simp only [h, if_false, div_one]
    exact measurable_fst

private theorem rHat_bound (K : CellBox) : ∀ p ∈ K.rect, |CellScalars.rHat K p| ≤ 1 + |K.r₁| + |K.r₂| := by
  intro p hp
  have h1 : K.r₁ ≤ p.1 := hp.1.1
  have h2 : p.1 ≤ K.r₂ := hp.1.2
  unfold CellScalars.rHat CellBox.lineWeight
  by_cases h : K.r₁ = 0
  · simp only [h, if_true]
    by_cases h0 : p.1 = 0
    · rw [h0, zero_div, abs_zero]; positivity
    · rw [div_self h0, abs_one]; linarith [abs_nonneg (0 : ℝ), abs_nonneg K.r₂]
  · simp only [h, if_false, div_one]
    rw [abs_le]
    constructor
    · have := neg_abs_le K.r₁
      have := abs_nonneg K.r₂
      linarith
    · have := le_abs_self K.r₂
      have := abs_nonneg K.r₁
      linarith

private theorem affine_bound (K : CellBox) (a b : ℝ) :
    ∀ p ∈ K.rect, |a + b * CellScalars.rHat K p| ≤ |a| + |b| * (1 + |K.r₁| + |K.r₂|) := by
  intro p hp
  calc |a + b * CellScalars.rHat K p| ≤ |a| + |b * CellScalars.rHat K p| := abs_add_le _ _
    _ = |a| + |b| * |CellScalars.rHat K p| := by rw [abs_mul]
    _ ≤ |a| + |b| * (1 + |K.r₁| + |K.r₂|) := by
        gcongr
        exact rHat_bound K p hp

theorem scalarsRegular_of_const (K : CellBox) (hK : IsCellBox K) (S : CellScalars)
    (A : ℤ → Matrix (Fin 12) (Fin 12) ℂ)
    (hm : ∀ n ∈ S.resolved, ∀ p, S.localMatrix n p = A n)
    (s₀ g₀ w₀ : ℝ) (hs : S.strainBound = fun _ => s₀) (hg : S.meanGradBound = fun _ => g₀)
    (hw : S.waveGradBound = fun _ => w₀) :
    (∀ n ∈ S.resolved, (∀ i j, Measurable (fun p => S.localMatrix n p i j)) ∧
      ∃ C : ℝ, ∀ p ∈ K.rect, ∀ i j, ‖S.localMatrix n p i j‖ ≤ C) ∧
    (Measurable S.strainBound ∧ ∃ C : ℝ, ∀ p ∈ K.rect, |S.strainBound p| ≤ C) ∧
    (Measurable S.meanGradBound ∧ ∃ C : ℝ, ∀ p ∈ K.rect, |S.meanGradBound p| ≤ C) ∧
    (Measurable S.waveGradBound ∧ ∃ C : ℝ, ∀ p ∈ K.rect, |S.waveGradBound p| ≤ C) := by
  refine ⟨fun n hn => ⟨fun i j => ?_, ?_⟩, ⟨?_, |s₀|, fun p _ => ?_⟩, ⟨?_, |g₀|, fun p _ => ?_⟩,
    ⟨?_, |w₀|, fun p _ => ?_⟩⟩
  · have : (fun p => S.localMatrix n p i j) = fun _ => A n i j := by
      funext p; rw [hm n hn p]
    rw [this]; exact measurable_const
  · refine ⟨∑ i, ∑ j, ‖A n i j‖, fun p _ i j => ?_⟩
    rw [hm n hn p]
    calc ‖A n i j‖ ≤ ∑ j', ‖A n i j'‖ :=
          Finset.single_le_sum (f := fun j' => ‖A n i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', ‖A n i' j'‖ :=
          Finset.single_le_sum (f := fun i' => ∑ j', ‖A n i' j'‖)
            (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ i)
  · rw [hs]; exact measurable_const
  · rw [hs]
  · rw [hg]; exact measurable_const
  · rw [hg]
  · rw [hw]; exact measurable_const
  · rw [hw]

theorem classesRegular_of_affine (K : CellBox) (hK : IsCellBox K) (Cl : CellClasses)
    (a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : Fin Cl.count → ℝ)
    (hs : ∀ i p, Cl.strainDev i p = a₁ i + b₁ i * CellScalars.rHat K p)
    (hg : ∀ i p, Cl.gradDev i p = a₂ i + b₂ i * CellScalars.rHat K p)
    (hv : ∀ i p, Cl.velocityDev i p = a₃ i + b₃ i * CellScalars.rHat K p)
    (hc : ∀ i p, Cl.curlDev i p = a₄ i + b₄ i * CellScalars.rHat K p) :
    ∀ i, Measurable (Cl.strainDev i) ∧ Measurable (Cl.gradDev i) ∧ Measurable (Cl.velocityDev i) ∧
      Measurable (Cl.curlDev i) ∧ ∃ C : ℝ, ∀ p ∈ K.rect, |Cl.strainDev i p| ≤ C ∧ |Cl.gradDev i p| ≤ C ∧
        |Cl.velocityDev i p| ≤ C ∧ |Cl.curlDev i p| ≤ C := by
  intro i
  have hR := rHat_measurable K
  have es : Cl.strainDev i = fun p => a₁ i + b₁ i * CellScalars.rHat K p := funext (hs i)
  have eg : Cl.gradDev i = fun p => a₂ i + b₂ i * CellScalars.rHat K p := funext (hg i)
  have ev : Cl.velocityDev i = fun p => a₃ i + b₃ i * CellScalars.rHat K p := funext (hv i)
  have ec : Cl.curlDev i = fun p => a₄ i + b₄ i * CellScalars.rHat K p := funext (hc i)
  set B := 1 + |K.r₁| + |K.r₂|
  refine ⟨?_, ?_, ?_, ?_, max (max (|a₁ i| + |b₁ i| * B) (|a₂ i| + |b₂ i| * B))
    (max (|a₃ i| + |b₃ i| * B) (|a₄ i| + |b₄ i| * B)), fun p hp => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [es]; exact measurable_const.add (measurable_const.mul hR)
  · rw [eg]; exact measurable_const.add (measurable_const.mul hR)
  · rw [ev]; exact measurable_const.add (measurable_const.mul hR)
  · rw [ec]; exact measurable_const.add (measurable_const.mul hR)
  · rw [hs]
    exact (affine_bound K _ _ p hp).trans (le_max_left _ _ |>.trans (le_max_left _ _))
  · rw [hg]
    exact (affine_bound K _ _ p hp).trans (le_max_right _ _ |>.trans (le_max_left _ _))
  · rw [hv]
    exact (affine_bound K _ _ p hp).trans (le_max_left _ _ |>.trans (le_max_right _ _))
  · rw [hc]
    exact (affine_bound K _ _ p hp).trans (le_max_right _ _ |>.trans (le_max_right _ _))

theorem localMatrixConst_of (K : CellBox) (S : CellScalars) (A : ℤ → Matrix (Fin 12) (Fin 12) ℂ)
    (hA : ∀ n ∈ S.resolved, ∀ p, S.localMatrix n p = A n) :
    ∀ n ∈ S.resolved, ∀ p ∈ K.rect, S.localMatrix n p = S.localMatrix n (K.r₁, K.z₁) := by
  intro n hn p _
  rw [hA n hn p, hA n hn]

end GivenModel

end CellCert

end Breakdown
