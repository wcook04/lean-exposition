import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.PairingByParts

theorem dirDeriv_contDiff {h : Space → Space} (hh : ContDiff ℝ ∞ h) (v : Space) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ h y v) :=
  (hh.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).clm_apply contDiff_const

theorem integrable_inner_of_compact {a b : Space → Space} (ha : Continuous a) (hb : Continuous b)
    (hs : HasCompactSupport b) : Integrable (fun x => inner ℝ (a x) (b x)) := by
  refine (ha.inner hb).integrable_of_hasCompactSupport ?_
  exact hs.mono' (fun x hx => subset_tsupport _ (fun h => hx (by simp [h])))

theorem iteratedFDeriv_two_diag {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (x v : Space) :
    iteratedFDeriv ℝ 2 φ x ![v, v] = fderiv ℝ (fun y => fderiv ℝ φ y v) x v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).differentiable (by simp) x
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const v)]
  simp

theorem coord_ibp {f φ : Space → Space} (hf : ContDiff ℝ ∞ f) (hφs : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (v : Space) :
    ∫ x, inner ℝ (fderiv ℝ f x v) (fderiv ℝ φ x v) =
      -∫ x, inner ℝ (f x) (fderiv ℝ (fun y => fderiv ℝ φ y v) x v) := by
  have hg := dirDeriv_contDiff hφs v
  have hgg := dirDeriv_contDiff hg v
  have hgc : HasCompactSupport (fun y => fderiv ℝ φ y v) := hφc.fderiv_apply (𝕜 := ℝ) v
  have hggc : HasCompactSupport (fun y => fderiv ℝ (fun z => fderiv ℝ φ z v) y v) :=
    hgc.fderiv_apply (𝕜 := ℝ) v
  have key := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (μ := volume) (B := innerSL ℝ) (v := v) (f := f) (g := fun y => fderiv ℝ φ y v)
    (integrable_inner_of_compact (dirDeriv_contDiff hf v).continuous hg.continuous hgc)
    (integrable_inner_of_compact hf.continuous hgg.continuous hggc)
    (integrable_inner_of_compact hf.continuous hg.continuous hgc)
    (fun x _ => (hf.differentiable (by simp)) x)
    (fun x _ => (hg.differentiable (by simp)) x)
  change ∫ x, inner ℝ (f x) (fderiv ℝ (fun y => fderiv ℝ φ y v) x v) =
    -∫ x, inner ℝ (fderiv ℝ f x v) (fderiv ℝ φ x v) at key
  rw [key, neg_neg]

end Internal.PairingByParts

open Internal.PairingByParts in
theorem pairingByParts :
    PairingByParts := by
  intro f φ hf hφ
  obtain ⟨hfs, -, -⟩ := hf
  obtain ⟨hφs, hφc, -⟩ := hφ
  unfold gradientPairing fieldPairing negSsp sumSecondPartialsAt
  simp_rw [iteratedFDeriv_two_diag hφs, inner_neg_right, inner_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_inner_of_compact
      (dirDeriv_contDiff hfs (unitVector i)).continuous
      (dirDeriv_contDiff hφs (unitVector i)).continuous (hφc.fderiv_apply (𝕜 := ℝ) _)),
    integral_neg, integral_finsetSum _ (fun i _ => integrable_inner_of_compact hfs.continuous
      (dirDeriv_contDiff (dirDeriv_contDiff hφs (unitVector i)) (unitVector i)).continuous
      ((hφc.fderiv_apply (𝕜 := ℝ) _).fderiv_apply (𝕜 := ℝ) _)), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => coord_ibp hfs hφs hφc (unitVector i)

end Breakdown.Freq
