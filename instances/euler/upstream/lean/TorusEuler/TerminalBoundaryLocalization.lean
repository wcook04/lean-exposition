import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-! Local compactly supported Taylor data on the terminal spatial slice. -/

open Set Filter Topology
open scoped ContDiff

namespace TorusEuler

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The pure time component of the ambient Taylor jet at the terminal slice. -/
def terminalBoundaryTimeJet (f : ℝ × E → F) (s : Set (ℝ × E)) (T : ℝ) (n : ℕ)
    (y : E) : F :=
  iteratedFDerivWithin ℝ n f s (T, y) (fun _ => (1, 0))

/-- Smoothness on a right-closed slab makes each time jet smooth as a
function of the spatial variable in the open spatial set. -/
theorem contDiffOn_terminalBoundaryTimeJet {t₀ T : ℝ} (hT : t₀ < T) {O : Set E}
    (hO : IsOpen O) {f : ℝ × E → F}
    (hf : ContDiffOn ℝ ∞ f (Icc t₀ T ×ˢ O)) (n : ℕ) :
    ContDiffOn ℝ ∞ (terminalBoundaryTimeJet f (Icc t₀ T ×ˢ O) T n) O := by
  let s := Icc t₀ T ×ˢ O
  have hUnique : UniqueDiffOn ℝ s := (uniqueDiffOn_Icc hT).prod hO.uniqueDiffOn
  have hJoint : ContDiffOn ℝ ∞ (iteratedFDerivWithin ℝ n f s) s :=
    fun z hz => (hf z hz).iteratedFDerivWithin_right hUnique (by simp) hz
  have hSlice : ContDiff ℝ ∞ (fun y : E => (T, y)) := contDiff_const.prodMk contDiff_id
  have hInto : MapsTo (fun y : E => (T, y)) O s := fun _ hy => ⟨⟨hT.le, le_rfl⟩, hy⟩
  let eval : ((ℝ × E) [×n]→L[ℝ] F) →L[ℝ] F :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℝ × E) F (fun _ => (1, 0))
  exact eval.contDiff.comp_contDiffOn (hJoint.comp hSlice.contDiffOn hInto)

/-- One spatial cutoff localizes every coefficient at once. Each
localized coefficient is globally smooth and compactly supported. -/
theorem exists_terminalBoundaryLocalizedJets [FiniteDimensional ℝ E] {t₀ T : ℝ} (hT : t₀ < T)
    {O : Set E} (hO : IsOpen O) {f : ℝ × E → F}
    (hf : ContDiffOn ℝ ∞ f (Icc t₀ T ×ˢ O)) {x : E} (hx : x ∈ O) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧ ∃ g : ℕ → E → F,
      (∀ n, ContDiff ℝ ∞ (g n)) ∧ (∀ n, HasCompactSupport (g n)) ∧
      ∀ n y, y ∈ V → g n y = terminalBoundaryTimeJet f (Icc t₀ T ×ˢ O) T n y := by
  obtain ⟨r, hr, hrO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hx)
  let b : ContDiffBump x := ⟨r / 4, r / 2, by linarith, by linarith⟩
  let V := Metric.ball x b.rIn
  let jet (n : ℕ) := terminalBoundaryTimeJet f (Icc t₀ T ×ˢ O) T n
  let g (n : ℕ) (y : E) := b y • jet n y
  have hs : tsupport (b : E → ℝ) ⊆ O := by
    rw [b.tsupport_eq]
    exact (Metric.closedBall_subset_ball (show r / 2 < r by linarith)).trans hrO
  refine ⟨V, Metric.isOpen_ball, Metric.mem_ball_self b.rIn_pos,
    (Metric.ball_subset_ball (show r / 4 ≤ r by linarith)).trans hrO, g, ?_, ?_, ?_⟩
  · intro n
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ O
    · exact (b.contDiff.contDiffOn.smul (contDiffOn_terminalBoundaryTimeJet hT hO hf n)).contDiffAt
        (hO.mem_nhds hy)
    · have hny : y ∈ (tsupport (b : E → ℝ))ᶜ := fun hy' => hy (hs hy')
      have hz : g n =ᶠ[𝓝 y] fun _ => (0 : F) := by
        filter_upwards [((isClosed_tsupport (b : E → ℝ)).isOpen_compl.mem_nhds hny)] with u hu
        have hbu := Function.notMem_support.mp (fun h => hu (subset_tsupport _ h))
        simp only [g, hbu, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  · intro n
    exact b.hasCompactSupport.smul_right
  · intro n y hy
    change b y • jet n y = jet n y
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), one_smul]

end

end TorusEuler
