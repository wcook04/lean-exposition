import Breakdown.Weak.StatementsOrbit

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown.WeakProfile

open Freq

private theorem eqOn_of_ae_interval (x : ℝ → X) (c : ℕ → ℝ → X)
    (hc : ∀ n : ℕ, ContinuousOn (c n) (Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1)) ∧
      ∀ᵐ σ ∂(volume.restrict (Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1))), c n σ = x σ)
    {m n : ℕ} (hmn : m ≤ n) :
    EqOn (c m) (c n) (Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1)) := by
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hsub : Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1) ⊆ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1) :=
    Ioo_subset_Ioo (by linarith) (by linarith)
  have h2 : ∀ᵐ σ ∂(volume.restrict (Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1))), c n σ = x σ :=
    ae_restrict_of_ae_restrict_of_subset hsub (hc n).2
  have h3 : c m =ᵐ[volume.restrict (Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1))] c n := by
    filter_upwards [(hc m).2, h2] with σ h1 h2 using h1.trans h2.symm
  exact Measure.eqOn_open_of_ae_eq h3 isOpen_Ioo (hc m).1 ((hc n).1.mono hsub)

theorem globalRepresentative_holds : GlobalRepresentative := by
  intro x hx
  have hex : ∀ n : ℕ, ∃ c : ℝ → X, ContinuousOn c (Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1)) ∧
      ∀ᵐ σ ∂(volume.restrict (Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1))), c σ = x σ :=
    fun n => hx _ _ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  choose c hc using hex
  have hmem : ∀ σ : ℝ, σ ∈ Ioo (-((⌈|σ|⌉₊ : ℝ) + 1)) ((⌈|σ|⌉₊ : ℝ) + 1) := by
    intro σ
    have h1 : |σ| ≤ (⌈|σ|⌉₊ : ℝ) := Nat.le_ceil _
    constructor
    · linarith [neg_abs_le σ]
    · linarith [le_abs_self σ]
  have hagree : ∀ m n : ℕ, ∀ σ, σ ∈ Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1) →
      σ ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1) → c m σ = c n σ := by
    intro m n σ hm hn
    rcases le_total m n with h | h
    · exact eqOn_of_ae_interval x c hc h hm
    · exact (eqOn_of_ae_interval x c hc h hn).symm
  refine ⟨fun σ => c ⌈|σ|⌉₊ σ, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro σ
    have hU : Ioo (-((⌈|σ|⌉₊ : ℝ) + 1)) ((⌈|σ|⌉₊ : ℝ) + 1) ∈ 𝓝 σ :=
      isOpen_Ioo.mem_nhds (hmem σ)
    have hcont : ContinuousAt (c ⌈|σ|⌉₊) σ := ((hc _).1).continuousAt hU
    refine hcont.congr ?_
    filter_upwards [hU] with τ hτ
    exact hagree _ _ τ hτ (hmem τ)
  · have hall : ∀ᵐ σ, ∀ n : ℕ, σ ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1) → c n σ = x σ := by
      rw [ae_all_iff]
      intro n
      exact (ae_restrict_iff' measurableSet_Ioo).mp (hc n).2
    filter_upwards [hall] with σ hσ
    exact hσ _ (hmem σ)

private theorem timeBack_forward (s₀ t : ℝ) (ht : t < 1) :
    1 - Real.exp (-((s₀ - Real.log (1 - t)) - s₀)) = t := by
  have h : 0 < 1 - t := by linarith
  rw [show -((s₀ - Real.log (1 - t)) - s₀) = Real.log (1 - t) by ring, Real.exp_log h]
  ring

private theorem timeBack_lt (s₀ σ : ℝ) : 1 - Real.exp (-(σ - s₀)) < 1 := by
  linarith [Real.exp_pos (-(σ - s₀))]

private theorem timeForward_back (s₀ σ : ℝ) :
    s₀ - Real.log (1 - (1 - Real.exp (-(σ - s₀)))) = σ := by
  rw [show 1 - (1 - Real.exp (-(σ - s₀))) = Real.exp (-(σ - s₀)) by ring, Real.log_exp]
  ring

theorem timeChangeNull_holds : TimeChangeNull := by
  intro s₀ p
  rw [ae_restrict_iff' measurableSet_Iio, ae_iff, ae_iff]
  simp only [Classical.not_imp, mem_Iio]
  constructor
  · intro h
    have hd : DifferentiableOn ℝ (fun σ : ℝ => 1 - Real.exp (-(σ - s₀))) {a | ¬p a} :=
      (by fun_prop : Differentiable ℝ fun σ : ℝ => 1 - Real.exp (-(σ - s₀))).differentiableOn
    refine measure_mono_null ?_ (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hd h)
    rintro t ⟨ht, hp⟩
    exact ⟨s₀ - Real.log (1 - t), hp, timeBack_forward s₀ t ht⟩
  · intro h
    have hd : DifferentiableOn ℝ (fun t : ℝ => s₀ - Real.log (1 - t))
        {a | a < 1 ∧ ¬p (s₀ - Real.log (1 - a))} := by
      intro t ht
      have hne : (1 - t) ≠ 0 := by
        have h1 : t < 1 := ht.1
        linarith
      exact ((differentiableAt_const _).sub
        (((differentiableAt_const _).sub differentiableAt_id).log hne)).differentiableWithinAt
    refine measure_mono_null ?_ (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hd h)
    intro σ hσ
    refine ⟨1 - Real.exp (-(σ - s₀)), ⟨timeBack_lt s₀ σ, ?_⟩, timeForward_back s₀ σ⟩
    rw [timeForward_back]
    exact hσ

private theorem timeChange_quasiMeasurePreserving (s₀ : ℝ) :
    Measure.QuasiMeasurePreserving (fun t : ℝ => s₀ - Real.log (1 - t))
      (volume.restrict (Iio 1)) volume := by
  have hm : Measurable (fun t : ℝ => s₀ - Real.log (1 - t)) :=
    measurable_const.sub (Real.measurable_log.comp (measurable_const.sub measurable_id))
  refine ⟨hm, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply hm hs]
  have h := (timeChangeNull_holds s₀ (fun σ => σ ∉ s)).mp (measure_eq_zero_iff_ae_notMem.mp h0)
  exact measure_eq_zero_iff_ae_notMem.mpr h

theorem physicalCurveMeasurable_holds : PhysicalCurveMeasurable := by
  intro s₀ x hx
  have hy : AEStronglyMeasurable (fun t => x (s₀ - Real.log (1 - t))) (volume.restrict (Iio 1)) :=
    hx.comp_quasiMeasurePreserving (timeChange_quasiMeasurePreserving s₀)
  have hJ : ContinuousOn (fun p : ℝ × X => dilX p.1 p.2) (Ioi 0 ×ˢ univ) :=
    dilateJointContinuous_holds X realization.F
  have hH : Continuous (fun p : ℝ × X => dilX (Real.exp p.1) p.2) :=
    hJ.comp_continuous (Real.continuous_exp.prodMap continuous_id)
      (fun p => ⟨Real.exp_pos p.1, mem_univ _⟩)
  have hl : AEStronglyMeasurable (fun t : ℝ => -Real.log (1 - t)) (volume.restrict (Iio 1)) :=
    (Real.measurable_log.comp (measurable_const.sub measurable_id)).neg.aestronglyMeasurable
  refine (hH.comp_aestronglyMeasurable (hl.prodMk hy)).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
  have h : 0 < 1 - t := by
    have h1 : t < 1 := ht
    linarith
  simp only [physicalCurve]
  rw [Real.exp_neg, Real.exp_log h]

end Breakdown.WeakProfile
