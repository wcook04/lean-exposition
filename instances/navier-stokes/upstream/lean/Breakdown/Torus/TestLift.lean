import Breakdown.Torus.StatementsInverse
import Breakdown.Torus.StatementsApproxSteps

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace Internal.TestLift

theorem diffAt_of_test {φ : Space → Space} (hφ : IsTestField φ) (y : Space) :
    DifferentiableAt ℝ φ y :=
  (hφ.1.differentiable (by simp)).differentiableAt

theorem isTest_add {φ ψ : Space → Space} (hφ : IsTestField φ) (hψ : IsTestField ψ) :
    IsTestField (φ + ψ) := by
  refine ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, fun y => ?_⟩
  have hd : fderiv ℝ (φ + ψ) y = fderiv ℝ φ y + fderiv ℝ ψ y :=
    fderiv_add (diffAt_of_test hφ y) (diffAt_of_test hψ y)
  have a := hφ.2.2 y
  have b := hψ.2.2 y
  unfold divergenceAt at a b ⊢
  simp only [hd, add_apply, PiLp.add_apply, Finset.sum_add_distrib, a, b, add_zero]

theorem isTest_smul (c : ℝ) {φ : Space → Space} (hφ : IsTestField φ) :
    IsTestField (c • φ) := by
  refine ⟨hφ.1.const_smul c, hφ.2.1.smul_left (f := fun _ : Space => c), fun y => ?_⟩
  have hd : fderiv ℝ (c • φ) y = c • fderiv ℝ φ y := fderiv_const_smul (diffAt_of_test hφ y) c
  have a := hφ.2.2 y
  unfold divergenceAt at a ⊢
  simp only [hd, smul_apply, PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, a,
    mul_zero]

theorem isTest_zero : IsTestField (0 : Space → Space) := by
  refine ⟨contDiff_const, HasCompactSupport.zero, fun y => ?_⟩
  unfold divergenceAt
  simp

theorem isDecay_of_isTest {φ : Space → Space} (hφ : IsTestField φ) : IsDecayField φ := by
  obtain ⟨hs, hc, hdiv⟩ := hφ
  refine ⟨hs, hdiv, ?_⟩
  obtain ⟨A, hA⟩ := hs.continuous.bounded_above_of_compact_support hc
  obtain ⟨B, hB⟩ := (hs.continuous_fderiv (by simp)).bounded_above_of_compact_support (hc.fderiv ℝ)
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  have hM : 0 ≤ max (max A B) 0 := le_max_right _ _
  refine ⟨max (max A B) 0 * (1 + max R 0) ^ 2, fun y => ?_⟩
  have hpos : 0 < 1 + ‖y‖ := by positivity
  have hS0 : 0 ≤ max R 0 := le_max_right _ _
  by_cases hy : y ∈ tsupport φ
  · have hyS : ‖y‖ ≤ max R 0 := by
      have h := hR hy
      rw [Metric.mem_closedBall, dist_zero_right] at h
      exact h.trans (le_max_left _ _)
    have h1 : 1 + ‖y‖ ≤ 1 + max R 0 := by linarith
    have hAy : ‖φ y‖ ≤ max (max A B) 0 := (hA y).trans ((le_max_left _ _).trans (le_max_left _ _))
    have hBy : ‖fderiv ℝ φ y‖ ≤ max (max A B) 0 :=
      (hB y).trans ((le_max_right _ _).trans (le_max_left _ _))
    constructor
    · rw [le_div_iff₀ hpos]
      calc ‖φ y‖ * (1 + ‖y‖) ≤ max (max A B) 0 * (1 + max R 0) := mul_le_mul hAy h1 hpos.le hM
        _ ≤ max (max A B) 0 * (1 + max R 0) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hM
          nlinarith
    · rw [le_div_iff₀ (by positivity)]
      exact mul_le_mul hBy (pow_le_pow_left₀ hpos.le h1 2) (by positivity) hM
  · have h0 : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
    have h0' : fderiv ℝ φ y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hy (tsupport_fderiv_subset ℝ h))
    rw [h0, h0', norm_zero, norm_zero]
    exact ⟨by positivity, by positivity⟩

theorem isTest_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℝ) (φ : ι → Space → Space)
    (hφ : ∀ i, IsTestField (φ i)) (hL : Freq.EmbedLinear) :
    IsTestField (∑ i ∈ s, c i • φ i) ∧
      Freq.embedX (∑ i ∈ s, c i • φ i) = ∑ i ∈ s, c i • Freq.embedX (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using isTest_zero, ?_⟩
    have h := hL.2.2 0 0 (isDecay_of_isTest isTest_zero)
    simpa using h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := isTest_smul (c a) (hφ a)
    refine ⟨isTest_add h1 ih.1, ?_⟩
    rw [hL.1 _ _ (isDecay_of_isTest h1) (isDecay_of_isTest ih.1),
      hL.2.2 _ _ (isDecay_of_isTest (hφ a)), ih.2]

theorem tsupport_sum_smul_subset {ι : Type*} (s : Finset ι) (c : ι → ℝ) (φ : ι → Space → Space)
    (K : Set Space) (hK : IsClosed K) (hφ : ∀ i, tsupport (φ i) ⊆ K) :
    tsupport (∑ i ∈ s, c i • φ i) ⊆ K := by
  refine closure_minimal (fun x hx => ?_) hK
  by_contra hxK
  apply hx
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Pi.smul_apply, image_eq_zero_of_notMem_tsupport (fun h => hxK (hφ i h)), smul_zero]

theorem transplantField_add (μ : ℝ) (f g : Space → Space) :
    transplantField μ (f + g) = transplantField μ f + transplantField μ g := by
  funext x
  simp only [transplantField, Pi.add_apply, smul_add]

theorem transplantField_smul (μ c : ℝ) (f : Space → Space) :
    transplantField μ (c • f) = c • transplantField μ f := by
  funext x
  simp only [transplantField, Pi.smul_apply]
  exact smul_comm _ _ _

theorem complexify_smul (c : ℝ) (v : Space) : complexify (c • v) = c • complexify v := by
  ext i
  simp [complexify, Complex.real_smul]

theorem freqTrCoef_smul (c : ℝ) (f : Space → Space) (k : Lattice) :
    freqTrCoef (c • f) k = c • freqTrCoef f k := by
  unfold freqTrCoef
  rw [← integral_smul]
  congr 1
  funext x
  rw [Pi.smul_apply, complexify_smul]
  exact smul_comm _ _ _

theorem weightedCoef_smul (c : ℝ) (f : Space → Space) :
    weightedCoef (c • f) = c • weightedCoef f := by
  funext k
  simp only [weightedCoef, freqTrCoef_smul, Pi.smul_apply]
  exact smul_comm _ _ _

theorem toV_coe {f : Space → Space}
    (h : ∃ hm : Memℓp (weightedCoef f) 2, (⟨weightedCoef f, hm⟩ : Seq) ∈ fieldSpace) :
    ((toV f : Seq) : Lattice → Coef) = weightedCoef f := by
  unfold toV
  rw [dif_pos h]

theorem toV_of_not {f : Space → Space}
    (h : ¬ ∃ hm : Memℓp (weightedCoef f) 2, (⟨weightedCoef f, hm⟩ : Seq) ∈ fieldSpace) :
    toV f = 0 := by
  unfold toV
  rw [dif_neg h]

theorem toV_smul_of_eq {f g : Space → Space} (a : ℝ) (hw : weightedCoef g = a • weightedCoef f)
    (h : ∃ hm : Memℓp (weightedCoef f) 2, (⟨weightedCoef f, hm⟩ : Seq) ∈ fieldSpace) :
    (∃ hm : Memℓp (weightedCoef g) 2, (⟨weightedCoef g, hm⟩ : Seq) ∈ fieldSpace) ∧
      toV g = a • toV f := by
  obtain ⟨hm, hmem⟩ := h
  have hm' : Memℓp (weightedCoef g) 2 := by
    rw [hw]
    exact hm.const_smul a
  have heq : (⟨weightedCoef g, hm'⟩ : Seq) = a • (⟨weightedCoef f, hm⟩ : Seq) :=
    lp.ext (by rw [lp.coeFn_smul]; exact hw)
  have h' : ∃ hm : Memℓp (weightedCoef g) 2, (⟨weightedCoef g, hm⟩ : Seq) ∈ fieldSpace := by
    refine ⟨hm', ?_⟩
    rw [heq]
    exact fieldSpace.smul_mem a hmem
  refine ⟨h', Subtype.ext (lp.ext ?_)⟩
  rw [toV_coe h', Submodule.coe_smul, lp.coeFn_smul, toV_coe ⟨hm, hmem⟩, hw]

theorem toV_smul (c : ℝ) (f : Space → Space) : toV (c • f) = c • toV f := by
  have hw : weightedCoef (c • f) = c • weightedCoef f := weightedCoef_smul c f
  by_cases h : ∃ hm : Memℓp (weightedCoef f) 2, (⟨weightedCoef f, hm⟩ : Seq) ∈ fieldSpace
  · exact (toV_smul_of_eq c hw h).2
  · rw [toV_of_not h, smul_zero]
    by_cases hc : c = 0
    · subst hc
      by_cases h0 : ∃ hm : Memℓp (weightedCoef ((0 : ℝ) • f)) 2,
          (⟨weightedCoef ((0 : ℝ) • f), hm⟩ : Seq) ∈ fieldSpace
      · refine Subtype.ext (lp.ext ?_)
        rw [toV_coe h0, hw, zero_smul]
        rfl
      · exact toV_of_not h0
    · refine toV_of_not fun h' => h ?_
      refine (toV_smul_of_eq c⁻¹ ?_ h').1
      rw [hw, inv_smul_smul₀ hc]

end Internal.TestLift

open Internal.TestLift

theorem testLiftExists (hS : Freq.TestSpanSpec) (hL : Freq.EmbedLinear) : TestLiftExists := by
  intro E _ _ _ J hJ
  classical
  let B := Module.finBasis ℝ E
  choose φ hφ hφJ using fun i => hS (J (B i)) (hJ (B i))
  have hKc : IsCompact (⋃ i, tsupport (φ i)) := isCompact_iUnion fun i => (hφ i).2.1
  obtain ⟨r, hr⟩ := hKc.isBounded.subset_closedBall (0 : Space)
  have hsub : ∀ i, tsupport (φ i) ⊆ Metric.closedBall 0 (max r 1) := fun i =>
    (subset_iUnion (fun i => tsupport (φ i)) i).trans
      (hr.trans (Metric.closedBall_subset_closedBall (le_max_left _ _)))
  have hval : ∀ e, B.constr ℝ φ e = ∑ i, B.equivFun e i • φ i := fun e =>
    B.constr_apply_fintype ℝ φ e
  refine ⟨max r 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    ⟨{ field := B.constr ℝ φ, isTest := fun e => ?_, support := fun e => ?_, embed := fun e => ?_ }⟩⟩
  · rw [hval]
    exact (isTest_sum_smul Finset.univ _ φ hφ hL).1
  · rw [hval]
    exact tsupport_sum_smul_subset _ _ _ _ Metric.isClosed_closedBall hsub
  · rw [hval, (isTest_sum_smul Finset.univ _ φ hφ hL).2]
    conv_rhs => rw [← B.sum_equivFun e]
    rw [map_sum]
    simp only [map_smul, hφJ]

theorem torusLiftExists (hA : ToVAdd) (hT : TransplantSmooth) : TorusLiftExists := by
  intro E _ _ _ J b ψ T hb hT0 hT1 hTb
  have hsh : IsShellScale T b := ⟨hT0, hT1, hb, hTb⟩
  have hprop : ∀ e, ContDiff ℝ ∞ (transplantField T (ψ.field e)) ∧
      IsPeriodic (transplantField T (ψ.field e)) ∧
        ∀ x, divergenceAt (transplantField T (ψ.field e)) x = 0 := fun e =>
    have h := hT (ψ.field e) T b (ψ.isTest e).1 (ψ.isTest e).2.2 hsh (ψ.support e)
    ⟨h.1, h.2.1, h.2.2.1⟩
  let L : E →ₗ[ℝ] V :=
    { toFun := fun e => (T ^ (1 / 4 : ℝ)) • toV (transplantField T (ψ.field e))
      map_add' := fun e e' => by
        rw [map_add, transplantField_add, hA _ _ (hprop e).1 (hprop e').1 (hprop e).2.1
          (hprop e').2.1 (hprop e).2.2 (hprop e').2.2, smul_add]
      map_smul' := fun c e => by
        rw [map_smul, transplantField_smul, toV_smul, RingHom.id_apply, smul_comm] }
  exact ⟨LinearMap.toContinuousLinearMap L, fun e => rfl⟩

end Breakdown.Periodic
