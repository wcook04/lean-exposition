import Breakdown.CellReduction.AdjointAssemblyBasics

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace Internal.CentreResidual

theorem norm_unitVector (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem component_eq_inner (x : Space) (c : Fin 3) : x c = inner ℝ (unitVector c) x := by
  simp [unitVector, EuclideanSpace.inner_single_left]

theorem adjoint_component (A : Space →L[ℝ] Space) (i c : Fin 3) :
    (ContinuousLinearMap.adjoint A (unitVector i)) c = A (unitVector c) i := by
  rw [component_eq_inner, ContinuousLinearMap.adjoint_inner_right, real_inner_comm, ← component_eq_inner]

theorem sum_component {ι : Type*} (s : Finset ι) (v : ι → Space) (c : Fin 3) :
    (∑ l ∈ s, v l) c = ∑ l ∈ s, v l c := by
  simp

theorem weak_component {f : Space → Space} {g : Space → (Space →L[ℝ] Space)} (hw : IsWeakGradient f g)
    {φ : Space → ℝ} (hφ : IsTestFunction φ) (i c : Fin 3) :
    Integrable (fun y => φ y * g y (unitVector i) c) ∧
      Integrable (fun y => fderiv ℝ φ y (unitVector i) * f y c) ∧
      ∫ y, φ y * g y (unitVector i) c = -∫ y, fderiv ℝ φ y (unitVector i) * f y c := by
  obtain ⟨hf, hg, he⟩ := hw
  have hdφ : Continuous (fun y => fderiv ℝ φ y (unitVector i)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have I1 : Integrable (fun y => φ y • g y) :=
    hg.integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
  have I1' : Integrable (fun y => φ y • g y (unitVector i)) := by
    have := (ContinuousLinearMap.apply ℝ Space (unitVector i)).integrable_comp I1
    simpa using this
  have I2 : Integrable (fun y => fderiv ℝ φ y (unitVector i) • f y) :=
    hf.integrable_smul_left_of_hasCompactSupport hdφ (hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector i))
  have A1 : Integrable (fun y => φ y * g y (unitVector i) c) := by
    have := (EuclideanSpace.proj (𝕜 := ℝ) c).integrable_comp I1'
    simpa using this
  have A2 : Integrable (fun y => fderiv ℝ φ y (unitVector i) * f y c) := by
    have := (EuclideanSpace.proj (𝕜 := ℝ) c).integrable_comp I2
    simpa using this
  refine ⟨A1, A2, ?_⟩
  have h := congrArg (EuclideanSpace.proj (𝕜 := ℝ) c) (he φ hφ i)
  rw [← (EuclideanSpace.proj (𝕜 := ℝ) c).integral_comp_comm I1', map_neg,
    ← (EuclideanSpace.proj (𝕜 := ℝ) c).integral_comp_comm I2] at h
  simpa using h

def WeakDivPair (K : Space → (Space →L[ℝ] Space)) (d : Space → Space) : Prop :=
  ∀ φ, IsTestFunction φ → ∀ c : Fin 3,
    Integrable (fun y => φ y * d y c) ∧
      Integrable (fun y => ∑ i : Fin 3, fderiv ℝ φ y (unitVector i) * K y (unitVector i) c) ∧
      ∫ y, φ y * d y c = -∫ y, ∑ i : Fin 3, fderiv ℝ φ y (unitVector i) * K y (unitVector i) c

theorem weakDivPair_zero : WeakDivPair (fun _ => 0) (fun _ => 0) := by
  intro φ _ c
  simp

theorem weakDivPair_add {K₁ K₂ : Space → (Space →L[ℝ] Space)} {d₁ d₂ : Space → Space}
    (h₁ : WeakDivPair K₁ d₁) (h₂ : WeakDivPair K₂ d₂) :
    WeakDivPair (fun y => K₁ y + K₂ y) (fun y => d₁ y + d₂ y) := by
  intro φ hφ c
  obtain ⟨a₁, b₁, e₁⟩ := h₁ φ hφ c
  obtain ⟨a₂, b₂, e₂⟩ := h₂ φ hφ c
  have ea : (fun y => φ y * (d₁ y + d₂ y) c) = fun y => φ y * d₁ y c + φ y * d₂ y c := by
    funext y
    simp [mul_add]
  have eb : (fun y => ∑ i : Fin 3, fderiv ℝ φ y (unitVector i) * (K₁ y + K₂ y) (unitVector i) c) =
      fun y => (∑ i : Fin 3, fderiv ℝ φ y (unitVector i) * K₁ y (unitVector i) c)
        + ∑ i : Fin 3, fderiv ℝ φ y (unitVector i) * K₂ y (unitVector i) c := by
    funext y
    simp [mul_add, Finset.sum_add_distrib]
  rw [ea, eb]
  refine ⟨a₁.add a₂, b₁.add b₂, ?_⟩
  rw [integral_add a₁ a₂, integral_add b₁ b₂, e₁, e₂]
  ring

theorem weakDivPair_sub {K₁ K₂ : Space → (Space →L[ℝ] Space)} {d₁ d₂ : Space → Space}
    (h₁ : WeakDivPair K₁ d₁) (h₂ : WeakDivPair K₂ d₂) :
    WeakDivPair (fun y => K₁ y - K₂ y) (fun y => d₁ y - d₂ y) := by
  intro φ hφ c
  obtain ⟨a₁, b₁, e₁⟩ := h₁ φ hφ c
  obtain ⟨a₂, b₂, e₂⟩ := h₂ φ hφ c
  have ea : (fun y => φ y * (d₁ y - d₂ y) c) = fun y => φ y * d₁ y c - φ y * d₂ y c := by
    funext y
    simp [mul_sub]
  have eb : (fun y => ∑ i : Fin 3, fderiv ℝ φ y (unitVector i) * (K₁ y - K₂ y) (unitVector i) c) =
      fun y => (∑ i : Fin 3, fderiv ℝ φ y (unitVector i) * K₁ y (unitVector i) c)
        - ∑ i : Fin 3, fderiv ℝ φ y (unitVector i) * K₂ y (unitVector i) c := by
    funext y
    simp [mul_sub, Finset.sum_sub_distrib]
  rw [ea, eb]
  refine ⟨a₁.sub a₂, b₁.sub b₂, ?_⟩
  rw [integral_sub a₁ a₂, integral_sub b₁ b₂, e₁, e₂]
  ring

theorem weakDivPair_smul {K : Space → (Space →L[ℝ] Space)} {d : Space → Space} (a : ℝ)
    (h : WeakDivPair K d) : WeakDivPair (fun y => a • K y) (fun y => a • d y) := by
  intro φ hφ c
  obtain ⟨a₁, b₁, e₁⟩ := h φ hφ c
  have ea : (fun y => φ y * (a • d y) c) = fun y => a * (φ y * d y c) := by
    funext y
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have eb : (fun y => ∑ i : Fin 3, fderiv ℝ φ y (unitVector i) * (a • K y) (unitVector i) c) =
      fun y => a * ∑ i : Fin 3, fderiv ℝ φ y (unitVector i) * K y (unitVector i) c := by
    funext y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [FunLike.coe_smul, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [ea, eb]
  refine ⟨a₁.const_mul a, b₁.const_mul a, ?_⟩
  rw [integral_const_mul, integral_const_mul, e₁]
  ring

theorem weakDivPair_sum {ι : Type*} (s : Finset ι) {K : ι → Space → (Space →L[ℝ] Space)}
    {d : ι → Space → Space} (h : ∀ l ∈ s, WeakDivPair (K l) (d l)) :
    WeakDivPair (fun y => ∑ l ∈ s, K l y) (fun y => ∑ l ∈ s, d l y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using weakDivPair_zero
  | insert a s ha ih =>
    have hs := ih (fun l hl => h l (Finset.mem_insert_of_mem hl))
    have hb := weakDivPair_add (h a (Finset.mem_insert_self a s)) hs
    simpa [Finset.sum_insert ha] using hb

theorem weakDivPair_grad {f : Space → Space}
    (hw : ∀ j : Fin 3, IsWeakGradient (fun y => fderiv ℝ f y (unitVector j))
      (fun y => (secondDeriv f y).flip (unitVector j))) :
    WeakDivPair (fun y => fderiv ℝ f y)
      (fun y => ∑ i : Fin 3, secondDeriv f y (unitVector i) (unitVector i)) := by
  intro φ hφ c
  have hc : ∀ i : Fin 3, _ := fun i => weak_component (hw i) hφ i c
  simp only [ContinuousLinearMap.flip_apply] at hc
  have ea : (fun y => φ y * (∑ i : Fin 3, secondDeriv f y (unitVector i) (unitVector i)) c) =
      fun y => ∑ i : Fin 3, φ y * secondDeriv f y (unitVector i) (unitVector i) c := by
    funext y
    rw [sum_component, Finset.mul_sum]
  rw [ea]
  refine ⟨integrable_finsetSum _ fun i _ => (hc i).1, integrable_finsetSum _ fun i _ => (hc i).2.1, ?_⟩
  rw [integral_finsetSum _ fun i _ => (hc i).1, integral_finsetSum _ fun i _ => (hc i).2.1,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => (hc i).2.2

theorem weakDivPair_adjoint {f : Space → Space}
    (hw : ∀ j : Fin 3, IsWeakGradient (fun y => fderiv ℝ f y (unitVector j))
      (fun y => (secondDeriv f y).flip (unitVector j))) :
    WeakDivPair (fun y => ContinuousLinearMap.adjoint (fderiv ℝ f y))
      (fun y => ∑ i : Fin 3, ContinuousLinearMap.adjoint (secondDeriv f y (unitVector i)) (unitVector i)) := by
  intro φ hφ c
  have hc : ∀ i : Fin 3, _ := fun i => weak_component (hw c) hφ i i
  simp only [ContinuousLinearMap.flip_apply] at hc
  have ea : (fun y => φ y *
      (∑ i : Fin 3, ContinuousLinearMap.adjoint (secondDeriv f y (unitVector i)) (unitVector i)) c) =
      fun y => ∑ i : Fin 3, φ y * secondDeriv f y (unitVector i) (unitVector c) i := by
    funext y
    rw [sum_component, Finset.mul_sum]
    simp only [adjoint_component]
  have eb : (fun y => ∑ i : Fin 3, fderiv ℝ φ y (unitVector i) *
      ContinuousLinearMap.adjoint (fderiv ℝ f y) (unitVector i) c) =
      fun y => ∑ i : Fin 3, fderiv ℝ φ y (unitVector i) * fderiv ℝ f y (unitVector c) i := by
    funext y
    simp only [adjoint_component]
  rw [ea, eb]
  refine ⟨integrable_finsetSum _ fun i _ => (hc i).1, integrable_finsetSum _ fun i _ => (hc i).2.1, ?_⟩
  rw [integral_finsetSum _ fun i _ => (hc i).1, integral_finsetSum _ fun i _ => (hc i).2.1,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => (hc i).2.2


theorem transposeApply_norm_le (A : Space →L[ℝ] Space) (z : Space) :
    ‖transposeApply A z‖ ≤ 3 * ‖A‖ * ‖z‖ := by
  unfold transposeApply
  calc ‖∑ i : Fin 3, inner ℝ (A (unitVector i)) z • unitVector i‖
      ≤ ∑ i : Fin 3, ‖inner ℝ (A (unitVector i)) z • unitVector i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖A‖ * ‖z‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, norm_unitVector, mul_one, Real.norm_eq_abs]
        calc |inner ℝ (A (unitVector i)) z| ≤ ‖A (unitVector i)‖ * ‖z‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖A‖ * ‖z‖ := by
            gcongr
            simpa [norm_unitVector] using A.le_opNorm (unitVector i)
    _ = 3 * ‖A‖ * ‖z‖ := by
        simp
        ring

theorem exists_bound_periodic {F : ℝ → Space → ℝ} (hc : Continuous (fun z : ℝ × Space => F z.1 z.2))
    (hp : ∀ σ y, F (σ + 1) y = F σ y) {R : ℝ} (hs : ∀ σ y, R < ‖y‖ → F σ y = 0) :
    ∃ B, 0 ≤ B ∧ ∀ σ y, F σ y ≤ B := by
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun σ y => ?_⟩
  by_cases hy : R < ‖y‖
  · rw [hs σ y hy]
    exact le_max_right _ _
  · have hper : Function.Periodic (fun s => F s y) 1 := fun s => hp s y
    have e : F σ y = F (Int.fract σ) y := by
      have h := hper.sub_int_mul_eq (x := σ) ⌊σ⌋
      simp only [mul_one] at h
      rw [Int.fract]
      exact h.symm
    have hm : ((Int.fract σ, y) : ℝ × Space) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R :=
      ⟨⟨Int.fract_nonneg σ, (Int.fract_lt_one σ).le⟩, by simpa using not_lt.mp hy⟩
    have hb := hB _ hm
    rw [Real.norm_eq_abs] at hb
    rw [e]
    exact (le_abs_self _).trans (hb.trans (le_max_left _ _))

theorem le_decay_of_support {B R e t x : ℝ} (hB : 0 ≤ B) (he : 0 ≤ e) (ht : 0 ≤ t) (hx : x ≤ B)
    (hz : R < t → x = 0) : x ≤ B * (1 + |R|) ^ e / (1 + t) ^ e := by
  have hpos : 0 < (1 + t) ^ e := Real.rpow_pos_of_pos (by linarith) e
  by_cases h : R < t
  · rw [hz h]
    positivity
  · rw [le_div_iff₀ hpos]
    have h1 : (1 + t) ^ e ≤ (1 + |R|) ^ e :=
      Real.rpow_le_rpow (by linarith) (by linarith [le_abs_self R, not_lt.mp h]) he
    calc x * (1 + t) ^ e ≤ B * (1 + t) ^ e := mul_le_mul_of_nonneg_right hx hpos.le
      _ ≤ B * (1 + |R|) ^ e := mul_le_mul_of_nonneg_left h1 hB

theorem fderiv_eq_zero_of_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Space → E} {R : ℝ} (hs : ∀ y, R < ‖y‖ → F y = 0) {y : Space} (hy : R < ‖y‖) :
    fderiv ℝ F y = 0 := by
  have h : F =ᶠ[nhds y] fun _ => (0 : E) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with x hx
    exact hs x hx
  rw [h.fderiv_eq]
  simp

theorem secondDeriv_eq_zero_of_support {F : Space → Space} {R : ℝ} (hs : ∀ y, R < ‖y‖ → F y = 0)
    {y : Space} (hy : R < ‖y‖) : secondDeriv F y = 0 := by
  unfold secondDeriv
  exact fderiv_eq_zero_of_support (fun x hx => fderiv_eq_zero_of_support hs hx) hy

def adjointLinear : (Space →L[ℝ] Space) →L[ℝ] (Space →L[ℝ] Space) :=
  LinearMap.mkContinuous
    { toFun := fun A => ContinuousLinearMap.adjoint A
      map_add' := fun A B => by simp
      map_smul' := fun a A => by simp }
    1 (fun A => by simp)

theorem adjointLinear_apply (A : Space →L[ℝ] Space) :
    adjointLinear A = ContinuousLinearMap.adjoint A := rfl

theorem adjointLinear_norm_le : ‖adjointLinear‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem norm_transport_le (a b c d e : Space) (s t : ℝ) :
    ‖-s • a - b - t • c + (d - e)‖ ≤ |s| * ‖a‖ + ‖b‖ + |t| * ‖c‖ + (‖d‖ + ‖e‖) := by
  calc ‖-s • a - b - t • c + (d - e)‖ ≤ ‖-s • a - b - t • c‖ + ‖d - e‖ := norm_add_le _ _
    _ ≤ (‖-s • a‖ + ‖b‖ + ‖t • c‖) + (‖d‖ + ‖e‖) :=
        add_le_add (norm_sub_le_of_le (norm_sub_le _ _) le_rfl) (norm_sub_le _ _)
    _ = |s| * ‖a‖ + ‖b‖ + |t| * ‖c‖ + (‖d‖ + ‖e‖) := by
        simp [norm_smul]

theorem norm_pinFlux_le {k : ℕ} (r : AdjointDefectEntry k) (σ : ℝ) (y : Space) :
    ‖r.pinFlux σ y‖ ≤ ‖fderiv ℝ (r.field σ) y‖ +
      ∑ l, |r.pinCoef l| * (2 * ‖fderiv ℝ (r.pins.generator l σ) y‖) := by
  unfold AdjointDefectEntry.pinFlux
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun l _ => ?_)))
  rw [norm_smul, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (le_of_eq ?_)) (abs_nonneg _)
  rw [LinearIsometryEquiv.norm_map]
  ring

theorem norm_secondCombo_le {k : ℕ} (A : Space →L[ℝ] Space →L[ℝ] Space) (c : Fin k → ℝ)
    (G : Fin k → Space →L[ℝ] Space →L[ℝ] Space) :
    ‖A - ∑ l, c l • (G l - adjointLinear.comp (G l))‖ ≤ ‖A‖ + ∑ l, |c l| * (2 * ‖G l‖) := by
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun l _ => ?_)))
  rw [norm_smul, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (abs_nonneg _)
  have h := (ContinuousLinearMap.opNorm_comp_le adjointLinear (G l)).trans
    (mul_le_of_le_one_left (norm_nonneg _) adjointLinear_norm_le)
  linarith

theorem norm_diagSum_le (A : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖∑ i : Fin 3, A (unitVector i) (unitVector i)‖ ≤ 3 * ‖A‖ := by
  calc ‖∑ i : Fin 3, A (unitVector i) (unitVector i)‖
      ≤ ∑ i : Fin 3, ‖A (unitVector i) (unitVector i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖A‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        simpa [norm_unitVector] using A.le_opNorm₂ (unitVector i) (unitVector i)
    _ = 3 * ‖A‖ := by
        simp

theorem diagSum_combo {k : ℕ} (A : Space →L[ℝ] Space →L[ℝ] Space) (c : Fin k → ℝ)
    (G : Fin k → Space →L[ℝ] Space →L[ℝ] Space) :
    ∑ i : Fin 3, (A - ∑ l, c l • (G l - adjointLinear.comp (G l))) (unitVector i) (unitVector i) =
      (∑ i : Fin 3, A (unitVector i) (unitVector i)) - ∑ l, c l •
        ((∑ i : Fin 3, G l (unitVector i) (unitVector i)) -
          ∑ i : Fin 3, ContinuousLinearMap.adjoint (G l (unitVector i)) (unitVector i)) := by
  simp only [sub_apply, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    adjointLinear_apply]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.smul_sum, Finset.sum_sub_distrib]

end Internal.CentreResidual

open Internal Internal.CentreResidual

theorem centreResidualField_proof : CentreResidualFieldHolds := by
  intro k r χ P C γ D C' R₀ W hζ hW hp
  have hC : 0 ≤ C := by
    have h0 := (hζ.decay 0 0).1
    simp only [norm_zero, add_zero, Real.one_rpow, div_one] at h0
    exact (norm_nonneg _).trans h0
  have hD : 0 ≤ D := flowPiece_nonneg hW
  have hγ : 0 ≤ γ := by linarith [hζ.rate_gt]
  have cdζ := slice_fderiv_continuous hζ.smooth
  have cdW := slice_fderiv_continuous hW.smooth
  have cdΞ : ∀ l, Continuous (fun z : ℝ × Space => fderiv ℝ (r.pins.generator l z.1) z.2) :=
    fun l => slice_fderiv_continuous (hp.generator_smooth l)
  have cT : Continuous (fun z : ℝ × Space => adjointTransport P W r.field z.1 z.2) := by
    have cζ : Continuous (fun z : ℝ × Space => r.field z.1 z.2) := hζ.smooth.continuous
    have cτ := timeDerivative_continuous hζ.smooth
    have cW : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.smooth.continuous
    unfold adjointTransport advectionShift transposeApply
    fun_prop
  have cK : Continuous (fun z : ℝ × Space => r.pinFlux z.1 z.2) := by
    unfold AdjointDefectEntry.pinFlux
    have ca : ∀ l, Continuous (fun z : ℝ × Space =>
        ContinuousLinearMap.adjoint (fderiv ℝ (r.pins.generator l z.1) z.2)) := fun l =>
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Space) (F := Space)).continuous.comp (cdΞ l)
    exact cdζ.sub (continuous_finsetSum _ fun l _ => ((cdΞ l).sub (ca l)).const_smul (r.pinCoef l))
  have eΞ : ∀ l σ, r.pins.generator l (σ + 1) = r.pins.generator l σ :=
    fun l σ => funext (hp.generator_periodic l σ)
  have sΞ : ∀ l σ y, R₀ < ‖y‖ → r.pins.generator l σ y = 0 :=
    fun l σ y hy => hp.generator_support l σ y hy.le
  obtain ⟨B, hB0, hB⟩ := exists_bound_periodic
    (F := fun σ y => ∑ l, |r.pinCoef l| * (2 * ‖fderiv ℝ (r.pins.generator l σ) y‖))
    (continuous_finsetSum _ fun l _ => continuous_const.mul (continuous_const.mul (cdΞ l).norm))
    (fun σ y => by simp only [eΞ]) (R := R₀)
    (fun σ y hy => by simp [fderiv_eq_zero_of_support (sΞ _ σ) hy])
  set B2 : ℝ := ∑ l, |r.pinCoef l| * (2 * max C' 0) with hB2
  have hB20 : 0 ≤ B2 := by positivity
  set CT : ℝ := (|1 / P| + 3 / 2 + 4 * D) * C with hCT
  set CK : ℝ := C + B * (1 + |R₀|) ^ (γ + 1) with hCK
  set CD : ℝ := 3 * (C + B2 * (1 + |R₀|) ^ γ) with hCD
  have hCT0 : 0 ≤ CT := by positivity
  have hCK0 : 0 ≤ CK := by positivity
  have hCD0 : 0 ≤ CD := by positivity
  have hTb : ∀ σ y, ‖adjointTransport P W r.field σ y‖ ≤ CT / (1 + ‖y‖) ^ γ := by
    intro σ y
    obtain ⟨d1, d2, d3⟩ := hζ.decay σ y
    obtain ⟨w1, w2⟩ := hW.decay σ y
    have ha : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
    have hapos : 0 < 1 + ‖y‖ := by linarith
    have hu0 : 0 ≤ C / (1 + ‖y‖) ^ γ := by positivity
    have e1 : C / (1 + ‖y‖) ^ (γ + 1) = C / (1 + ‖y‖) ^ γ / (1 + ‖y‖) := by
      rw [Real.rpow_add_one hapos.ne', div_div]
    rw [e1] at d3
    have g1 : ‖fderiv ℝ (r.field σ) y‖ * ‖y‖ ≤ C / (1 + ‖y‖) ^ γ := by
      calc ‖fderiv ℝ (r.field σ) y‖ * ‖y‖ ≤ C / (1 + ‖y‖) ^ γ / (1 + ‖y‖) * (1 + ‖y‖) :=
            mul_le_mul d3 (by linarith) (norm_nonneg _) (by positivity)
        _ = C / (1 + ‖y‖) ^ γ := by field_simp
    have g2 : ‖fderiv ℝ (r.field σ) y‖ ≤ C / (1 + ‖y‖) ^ γ := d3.trans (div_le_self hu0 ha)
    have g3 : ‖fderiv ℝ (W σ) y‖ ≤ D := w2.trans (div_le_self hD ha)
    have tA : ‖transposeApply (fderiv ℝ (W σ) y) (r.field σ y)‖ ≤ 3 * D * (C / (1 + ‖y‖) ^ γ) := by
      refine (transposeApply_norm_le _ _).trans ?_
      have := mul_le_mul g3 d1 (norm_nonneg _) hD
      nlinarith
    have gW : ‖fderiv ℝ (r.field σ) y (W σ y)‖ ≤ C / (1 + ‖y‖) ^ γ * D :=
      ((fderiv ℝ (r.field σ) y).le_opNorm (W σ y)).trans (mul_le_mul g2 w1 (norm_nonneg _) hu0)
    have gy : ‖fderiv ℝ (r.field σ) y y‖ ≤ C / (1 + ‖y‖) ^ γ :=
      ((fderiv ℝ (r.field σ) y).le_opNorm y).trans g1
    have h1 : |1 / P| * ‖timeDerivative r.field σ y‖ ≤ |1 / P| * (C / (1 + ‖y‖) ^ γ) :=
      mul_le_mul_of_nonneg_left d2 (abs_nonneg _)
    unfold adjointTransport advectionShift
    refine (norm_transport_le _ _ _ _ _ _ _).trans ?_
    rw [hCT, mul_div_assoc]
    have h2 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
    rw [h2]
    nlinarith
  have hKb : ∀ σ y, ‖r.pinFlux σ y‖ ≤ CK / (1 + ‖y‖) ^ (γ + 1) := by
    intro σ y
    refine (norm_pinFlux_le r σ y).trans ?_
    have hx := le_decay_of_support (R := R₀) hB0 (by linarith : (0 : ℝ) ≤ γ + 1) (norm_nonneg y) (hB σ y)
      (fun hy => by simp [fderiv_eq_zero_of_support (sΞ _ σ) hy])
    rw [hCK, add_div]
    exact add_le_add (hζ.decay σ y).2.2 hx
  have hgood : ∀ σ, ∀ᵐ y, matrixDivergence (r.pinFlux σ) y =
      (∑ i : Fin 3, secondDeriv (r.field σ) y (unitVector i) (unitVector i)) - ∑ l, r.pinCoef l •
        ((∑ i : Fin 3, secondDeriv (r.pins.generator l σ) y (unitVector i) (unitVector i)) -
          ∑ i : Fin 3, ContinuousLinearMap.adjoint
            (secondDeriv (r.pins.generator l σ) y (unitVector i)) (unitVector i)) ∧
      ‖matrixDivergence (r.pinFlux σ) y‖ ≤ CD / (1 + ‖y‖) ^ γ := by
    intro σ
    filter_upwards [hζ.second_differentiable σ, hζ.second_decay σ,
      ae_all_iff.2 (fun l => hp.generator_differentiable l σ),
      ae_all_iff.2 (fun l => hp.generatorSecond_bound l σ)] with y h1 h2 h3 h4
    have e : r.pinFlux σ = fun x => fderiv ℝ (r.field σ) x - ∑ l, r.pinCoef l •
        (fderiv ℝ (r.pins.generator l σ) x - adjointLinear (fderiv ℝ (r.pins.generator l σ) x)) := by
      funext x
      rfl
    have hd : HasFDerivAt (r.pinFlux σ) (secondDeriv (r.field σ) y - ∑ l, r.pinCoef l •
        (secondDeriv (r.pins.generator l σ) y - adjointLinear.comp (secondDeriv (r.pins.generator l σ) y))) y := by
      have hl : ∀ l, HasFDerivAt (fun x => r.pinCoef l • (fderiv ℝ (r.pins.generator l σ) x
          - adjointLinear (fderiv ℝ (r.pins.generator l σ) x)))
          (r.pinCoef l • (secondDeriv (r.pins.generator l σ) y
            - adjointLinear.comp (secondDeriv (r.pins.generator l σ) y))) y := fun l =>
        ((h3 l).hasFDerivAt.sub (adjointLinear.hasFDerivAt.comp y (h3 l).hasFDerivAt)).const_smul (r.pinCoef l)
      rw [e]
      exact h1.hasFDerivAt.sub (HasFDerivAt.fun_sum fun l _ => hl l)
    have em : matrixDivergence (r.pinFlux σ) y = ∑ i : Fin 3, (secondDeriv (r.field σ) y - ∑ l, r.pinCoef l •
        (secondDeriv (r.pins.generator l σ) y - adjointLinear.comp (secondDeriv (r.pins.generator l σ) y)))
          (unitVector i) (unitVector i) := by
      unfold matrixDivergence
      rw [hd.fderiv]
    refine ⟨em.trans (diagSum_combo _ _ _), ?_⟩
    rw [em]
    refine (norm_diagSum_le _).trans ?_
    refine (mul_le_mul_of_nonneg_left (norm_secondCombo_le _ _ _) (by norm_num)).trans ?_
    have hx := le_decay_of_support (x := ∑ l, |r.pinCoef l| * (2 * ‖secondDeriv (r.pins.generator l σ) y‖))
      hB20 hγ (norm_nonneg y)
      (Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ((h4 l).trans (le_max_left _ _)) (by norm_num)) (abs_nonneg _))
      (fun hy => by simp [secondDeriv_eq_zero_of_support (sΞ _ σ) hy]) (R := R₀)
    rw [hCD, mul_div_assoc, add_div]
    exact mul_le_mul_of_nonneg_left (add_le_add h2 hx) (by norm_num)
  refine ⟨CT + CK + CD, hζ.rate_gt, cT.aestronglyMeasurable, cK.aestronglyMeasurable, fun σ => ?_,
    fun σ y => ?_, fun σ => ?_⟩
  · have hKσ : Continuous (r.pinFlux σ) := cK.comp (continuous_const.prodMk continuous_id)
    have hE := weakDivPair_sub (weakDivPair_grad (hζ.second_weak σ))
      (weakDivPair_sum Finset.univ fun l _ => weakDivPair_smul (r.pinCoef l)
        (weakDivPair_sub (weakDivPair_grad (hp.generator_weak l σ))
          (weakDivPair_adjoint (hp.generator_weak l σ))))
    have hmeas : Measurable (matrixDivergence (r.pinFlux σ)) := by
      unfold matrixDivergence
      exact Finset.measurable_sum _ fun i _ =>
        (ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.measurable.comp
          (measurable_fderiv_apply_const ℝ (r.pinFlux σ) (unitVector i))
    refine ⟨hKσ.locallyIntegrable, ?_, fun φ hφ c => ?_⟩
    · refine (locallyIntegrable_iff).2 fun s hs => ?_
      have : IsFiniteMeasure (volume.restrict s) := ⟨by simpa using hs.measure_lt_top⟩
      refine Integrable.of_bound hmeas.aestronglyMeasurable CD (ae_restrict_of_ae ?_)
      filter_upwards [hgood σ] with y hy
      exact hy.2.trans (div_le_self hCD0 (Real.one_le_rpow (by linarith [norm_nonneg y]) hγ))
    · obtain ⟨-, -, he⟩ := hE φ hφ c
      rw [integral_congr_ae (g := fun y => φ y * ((∑ i : Fin 3, secondDeriv (r.field σ) y (unitVector i) (unitVector i)) - ∑ l, r.pinCoef l •
        ((∑ i : Fin 3, secondDeriv (r.pins.generator l σ) y (unitVector i) (unitVector i)) -
          ∑ i : Fin 3, ContinuousLinearMap.adjoint
            (secondDeriv (r.pins.generator l σ) y (unitVector i)) (unitVector i))) c)]
      · exact he
      · filter_upwards [hgood σ] with y hy
        rw [hy.1]
  · have p1 : 0 < (1 + ‖y‖) ^ γ := by positivity
    have p2 : 0 < (1 + ‖y‖) ^ (γ + 1) := by positivity
    exact ⟨(hTb σ y).trans (div_le_div_of_nonneg_right (by linarith) p1.le),
      (hKb σ y).trans (div_le_div_of_nonneg_right (by linarith) p2.le)⟩
  · filter_upwards [hgood σ] with y hy
    have p1 : 0 < (1 + ‖y‖) ^ γ := by positivity
    exact hy.2.trans (div_le_div_of_nonneg_right (by linarith) p1.le)

theorem centreResidualField_of_slope (h : WeakGradientSlopeHolds) : CentreResidualFieldHolds :=
  centreResidualField_proof

end AdjointDefect

end Breakdown
