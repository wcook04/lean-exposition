import Breakdown.FracCell.FormulaDefs
import Breakdown.FracCell.MeshDefs

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellSystem

open SteadyCert Assembly CellAnalysis CellFormula

open Classical in
def zeroExtKernel {k : ℕ} (S₀ : Finset LowIndex)
    (Kr : LowIndex ⊕ (Fin k ⊕ Fin k) → LowIndex ⊕ (Fin k ⊕ Fin k) → ℂ) :
    LowIndex ⊕ (Fin k ⊕ Fin k) → LowIndex ⊕ (Fin k ⊕ Fin k) → ℂ := fun i i' =>
  if i ∈ S₀.disjSum Finset.univ ∧ i' ∈ S₀.disjSum Finset.univ then Kr i i' else 0

theorem zeroExtKernel_of_mem {k : ℕ} (S₀ : Finset LowIndex)
    (Kr : LowIndex ⊕ (Fin k ⊕ Fin k) → LowIndex ⊕ (Fin k ⊕ Fin k) → ℂ)
    {i i' : LowIndex ⊕ (Fin k ⊕ Fin k)} (hi : i ∈ S₀.disjSum Finset.univ)
    (hi' : i' ∈ S₀.disjSum Finset.univ) : zeroExtKernel S₀ Kr i i' = Kr i i' := by
  unfold zeroExtKernel
  rw [if_pos ⟨hi, hi'⟩]

theorem zeroExtKernel_of_not_mem_left {k : ℕ} (S₀ : Finset LowIndex)
    (Kr : LowIndex ⊕ (Fin k ⊕ Fin k) → LowIndex ⊕ (Fin k ⊕ Fin k) → ℂ)
    {i : LowIndex ⊕ (Fin k ⊕ Fin k)} (hi : i ∉ S₀.disjSum Finset.univ) (i' : LowIndex ⊕ (Fin k ⊕ Fin k)) :
    zeroExtKernel S₀ Kr i i' = 0 := by
  unfold zeroExtKernel
  rw [if_neg (fun hh => hi hh.1)]

theorem zeroExtKernel_of_not_mem_right {k : ℕ} (S₀ : Finset LowIndex)
    (Kr : LowIndex ⊕ (Fin k ⊕ Fin k) → LowIndex ⊕ (Fin k ⊕ Fin k) → ℂ)
    (i : LowIndex ⊕ (Fin k ⊕ Fin k)) {i' : LowIndex ⊕ (Fin k ⊕ Fin k)} (hi' : i' ∉ S₀.disjSum Finset.univ) :
    zeroExtKernel S₀ Kr i i' = 0 := by
  unfold zeroExtKernel
  rw [if_neg (fun hh => hi' hh.2)]

theorem kernelSum_zeroExt {k : ℕ} (S₀ S₁ : Finset LowIndex) (h : S₀ ⊆ S₁)
    (Kr : LowIndex ⊕ (Fin k ⊕ Fin k) → LowIndex ⊕ (Fin k ⊕ Fin k) → ℂ) (u : LowIndex ⊕ (Fin k ⊕ Fin k) → ℂ) :
    (∑ i ∈ S₁.disjSum Finset.univ, ∑ i' ∈ S₁.disjSum Finset.univ, (starRingEnd ℂ) (u i) * zeroExtKernel S₀ Kr i i' * u i')
      = ∑ i ∈ S₀.disjSum Finset.univ, ∑ i' ∈ S₀.disjSum Finset.univ, (starRingEnd ℂ) (u i) * Kr i i' * u i' := by
  have hsub : S₀.disjSum (Finset.univ : Finset (Fin k ⊕ Fin k)) ⊆ S₁.disjSum Finset.univ :=
    Finset.disjSum_mono h (le_refl _)
  have hout : ∀ i ∈ S₁.disjSum (Finset.univ : Finset (Fin k ⊕ Fin k)), i ∉ S₀.disjSum Finset.univ →
      ∑ i' ∈ S₁.disjSum Finset.univ, (starRingEnd ℂ) (u i) * zeroExtKernel S₀ Kr i i' * u i' = 0 := by
    intro i _ hi
    refine Finset.sum_eq_zero fun i' _ => ?_
    rw [zeroExtKernel_of_not_mem_left S₀ Kr hi i', mul_zero, zero_mul]
  rw [← Finset.sum_subset hsub hout]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : ∀ i' ∈ S₁.disjSum (Finset.univ : Finset (Fin k ⊕ Fin k)), i' ∉ S₀.disjSum Finset.univ →
      (starRingEnd ℂ) (u i) * zeroExtKernel S₀ Kr i i' * u i' = 0 := by
    intro i' _ hi'
    rw [zeroExtKernel_of_not_mem_right S₀ Kr i hi', mul_zero, zero_mul]
  rw [← Finset.sum_subset hsub hin]
  refine Finset.sum_congr rfl fun i' hi' => ?_
  rw [zeroExtKernel_of_mem S₀ Kr hi hi']

theorem farKernelDominates_of_system {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)
    (F : FarMajorantData) (S₀ : Finset LowIndex) (hS₀ : S₀ ⊆ lowSupport S)
    (Kr : LowIndex ⊕ (Fin k ⊕ Fin k) → LowIndex ⊕ (Fin k ⊕ Fin k) → ℂ)
    (hsystem : ∀ u : LowIndex ⊕ (Fin k ⊕ Fin k) → ℂ, CellScalars.farMajorantForm c K S F u
      ≤ (∑ i ∈ S₀.disjSum Finset.univ, ∑ i' ∈ S₀.disjSum Finset.univ, (starRingEnd ℂ) (u i) * Kr i i' * u i').re) :
    ∀ u : LowIndex ⊕ (Fin k ⊕ Fin k) → ℂ, CellScalars.farMajorantForm c K S F u
      ≤ (∑ i ∈ (lowSupport S).disjSum Finset.univ, ∑ i' ∈ (lowSupport S).disjSum Finset.univ,
          (starRingEnd ℂ) (u i) * zeroExtKernel S₀ Kr i i' * u i').re := by
  intro u
  rw [kernelSum_zeroExt S₀ (lowSupport S) hS₀ Kr u]
  exact hsystem u

theorem farMatrix_zeroExt {k N slots : ℕ} (S : CellScalars) (R : CellRows N slots k) (S₀ : Finset LowIndex)
    (Kr : LowIndex ⊕ (Fin k ⊕ Fin k) → LowIndex ⊕ (Fin k ⊕ Fin k) → ℂ) (hS₀ : S₀ ⊆ R.farSupport)
    (hK : R.farKernel = zeroExtKernel S₀ Kr) :
    farMatrix S R = farMatrix S ({ R with farSupport := S₀, farKernel := Kr } : CellRows N slots k) := by
  funext e e'
  unfold farMatrix
  rw [hK]
  unfold zeroExtKernel
  rcases e with ⟨i, hi⟩ | e <;> rcases e' with ⟨i', hi'⟩ | e' <;>
    simp [augToFar, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum]
  all_goals
    intro hF
    first
      | intro h1 h2; exact absurd (hS₀ h2) (hF (hS₀ h1))
      | intro h1; exact absurd (hS₀ h1) hF

end CellSystem

end CellCert

end Breakdown
