import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.CoerciveModeDerivative
import Breakdown.Cert.CoercivePerturbationFactsProof

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace CurlWeight.Internal

open Internal.PerturbationFacts

theorem reVec_apply (x : Fin 3 → ℂ) (n : Fin 3) : reVec x n = (x n).re := by
  fin_cases n <;> simp [reVec, unitVector, Fin.sum_univ_three]

theorem imVec_apply (x : Fin 3 → ℂ) (n : Fin 3) : imVec x n = (x n).im := by
  fin_cases n <;> simp [imVec, unitVector, Fin.sum_univ_three]

theorem reMat_apply_apply (g : Fin 3 × Fin 3 → ℂ) (j n : Fin 3) :
    reMat g (unitVector j) n = (g (n, j)).re := by
  rw [ModeDerivative.Internal.reMat_apply_unitVector]
  exact reVec_apply (fun i => g (i, j)) n

theorem imMat_apply_apply (g : Fin 3 × Fin 3 → ℂ) (j n : Fin 3) :
    imMat g (unitVector j) n = (g (n, j)).im := by
  rw [ModeDerivative.Internal.imMat_apply_unitVector]
  exact imVec_apply (fun i => g (i, j)) n

theorem locallyIntegrable_coord {f : Space → Space} (hf : LocallyIntegrable f volume) (n : Fin 3) :
    LocallyIntegrable (fun y => f y n) volume := by
  rw [locallyIntegrable_iff] at hf ⊢
  intro k hk
  exact (EuclideanSpace.proj n : Space →L[ℝ] ℝ).integrable_comp (hf k hk)

theorem locallyIntegrable_apply {D : Space → (Space →L[ℝ] Space)} (hD : LocallyIntegrable D volume)
    (u : Space) : LocallyIntegrable (fun y => D y u) volume := by
  rw [locallyIntegrable_iff] at hD ⊢
  intro k hk
  exact (hD k hk).apply_continuousLinearMap u

theorem locallyIntegrable_of_re_im {F : Space → ℂ} (hre : LocallyIntegrable (fun y => (F y).re) volume)
    (him : LocallyIntegrable (fun y => (F y).im) volume) : LocallyIntegrable F volume := by
  rw [locallyIntegrable_iff] at hre him ⊢
  intro k hk
  have h1 : Integrable (fun y => (F y).re) (volume.restrict k) := hre k hk
  have h2 : Integrable (fun y => (F y).im) (volume.restrict k) := him k hk
  exact Integrable.re_im_iff.1 ⟨by simpa using h1, by simpa using h2⟩

theorem weakPartial_coord {f : Space → Space} {D : Space → (Space →L[ℝ] Space)}
    (h : IsWeakGradient f D) (j n : Fin 3) :
    IsWeakPartial (fun y => f y n) (fun y => D y (unitVector j) n) j := by
  intro φ hφ
  have hL : Integrable (fun y => φ y • D y (unitVector j)) volume :=
    (h.2.1.integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2).apply_continuousLinearMap
      (unitVector j)
  have hc : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hR : Integrable (fun y => fderiv ℝ φ y (unitVector j) • f y) volume :=
    h.1.integrable_smul_left_of_hasCompactSupport hc (hφ.2.fderiv_apply (𝕜 := ℝ) _)
  have e := congrArg (EuclideanSpace.proj n : Space →L[ℝ] ℝ) (h.2.2 φ hφ j)
  rw [map_neg, ← (EuclideanSpace.proj n : Space →L[ℝ] ℝ).integral_comp_comm hL,
    ← (EuclideanSpace.proj n : Space →L[ℝ] ℝ).integral_comp_comm hR] at e
  simpa using e

theorem ae_modeSlice_weak (hD : ModeDerivativeHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (ι : ℤ × ℤ) :
    ∀ᵐ σ, (∀ n m : Fin 3, LocallyIntegrable (fun y => modeGrad ι G σ y (n, m)) volume) ∧
      (∀ n j m : Fin 3, LocallyIntegrable (fun y => modeSecondDeriv ι H σ y (n, j, m)) volume) ∧
      ∀ n j m : Fin 3,
        IsWeakPartial (fun y => (modeGrad ι G σ y (n, m)).re) (fun y => (modeSecondDeriv ι H σ y (n, j, m)).re) j ∧
        IsWeakPartial (fun y => (modeGrad ι G σ y (n, m)).im) (fun y => (modeSecondDeriv ι H σ y (n, j, m)).im) j := by
  filter_upwards [(hD Γ P v G H g hv ι).2.1] with σ hσ
  have hre : ∀ n j m : Fin 3, IsWeakPartial (fun y => (modeGrad ι G σ y (n, m)).re)
      (fun y => (modeSecondDeriv ι H σ y (n, j, m)).re) j := by
    intro n j m
    have h := weakPartial_coord (hσ m).1 j n
    simp only [reVec_apply, reMat_apply_apply] at h
    exact h
  have him : ∀ n j m : Fin 3, IsWeakPartial (fun y => (modeGrad ι G σ y (n, m)).im)
      (fun y => (modeSecondDeriv ι H σ y (n, j, m)).im) j := by
    intro n j m
    have h := weakPartial_coord (hσ m).2 j n
    simp only [imVec_apply, imMat_apply_apply] at h
    exact h
  refine ⟨fun n m => ?_, fun n j m => ?_, fun n j m => ⟨hre n j m, him n j m⟩⟩
  · refine locallyIntegrable_of_re_im ?_ ?_
    · have h := locallyIntegrable_coord (hσ m).1.1 n
      simp only [reVec_apply] at h
      exact h
    · have h := locallyIntegrable_coord (hσ m).2.1 n
      simp only [imVec_apply] at h
      exact h
  · refine locallyIntegrable_of_re_im ?_ ?_
    · have h := locallyIntegrable_coord (locallyIntegrable_apply (hσ m).1.2.1 (unitVector j)) n
      simp only [reMat_apply_apply] at h
      exact h
    · have h := locallyIntegrable_coord (locallyIntegrable_apply (hσ m).2.2.1 (unitVector j)) n
      simp only [imMat_apply_apply] at h
      exact h

end CurlWeight.Internal

end Coercive

end Breakdown
