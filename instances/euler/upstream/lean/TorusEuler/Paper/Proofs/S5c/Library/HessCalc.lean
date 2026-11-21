import TorusEuler.Paper.Proofs.S5c.Library.FlowJets

/-!
# Glue for Lemma 5.9: first jets of label-phase profiles

* `jet_one_le`: the first derivative of a (vector-valued) smooth `Q(a,s)` on a vector `(α, σ)` is
  bounded by the scaled jets of `(x,s) ↦ Q(ℓ_*x, hs)`, each label component costing `ℓ_*⁻¹` and
  each phase component `h⁻¹` (used for the remaining tensors of (5.51),
  `sections/08_exact_wave.tex:172-204`).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5c

open InnerProductSpace ContinuousLinearMap

noncomputable section

/-- The inverse of the label-phase scaling `(x,s) ↦ (ℓx, hs)`. -/
def labelPhaseUnscale (ℓ h : ℝ) : (Vec3 × ℝ) →L[ℝ] (Vec3 × ℝ) :=
  (ℓ⁻¹ • fst ℝ Vec3 ℝ).prod (h⁻¹ • snd ℝ Vec3 ℝ)

/-- Norm bound for the unscaling of the label-phase jet. -/
theorem norm_labelPhaseUnscale_le {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) (w : Vec3 × ℝ) :
    ‖labelPhaseUnscale ℓ h w‖ ≤ ‖w.1‖ / ℓ + ‖w.2‖ / h := by
  change ‖((ℓ⁻¹ • w.1, h⁻¹ * w.2) : Vec3 × ℝ)‖ ≤ _
  rw [Prod.norm_def, norm_smul, norm_mul, Real.norm_eq_abs (ℓ⁻¹), Real.norm_eq_abs (h⁻¹),
    abs_of_pos (inv_pos.mpr hℓ), abs_of_pos (inv_pos.mpr hh), div_eq_inv_mul, div_eq_inv_mul]
  exact max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left (by positivity))

/-- Scaling then unscaling a jet is the identity. -/
theorem scaled_unscale {ℓ h : ℝ} (hℓ : ℓ ≠ 0) (hh : h ≠ 0) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Q : Vec3 × ℝ → E) :
    scaledPhaseProfile ℓ h (fun a s => Q (a, s)) ∘ labelPhaseUnscale ℓ h = Q := by
  funext z
  change Q (ℓ • (ℓ⁻¹ • z.1), h * (h⁻¹ * z.2)) = Q z
  rw [smul_smul, mul_inv_cancel₀ hℓ, one_smul, ← mul_assoc, mul_inv_cancel₀ hh, one_mul]

/-- The iterated derivatives of `Q` from those of its scaled form. -/
theorem norm_iteratedFDeriv_apply_le {ℓ h A : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Q : Vec3 × ℝ → E}
    (hQ : ContDiff ℝ ∞ Q) {n : ℕ} (hJ : PhaseJetBound n A (scaledPhaseProfile ℓ h (fun a s => Q (a, s))))
    {j : ℕ} (hj : j ≤ n) (z : Vec3 × ℝ) (m : Fin j → Vec3 × ℝ) :
    ‖iteratedFDeriv ℝ j Q z m‖ ≤ A * ∏ i, (‖(m i).1‖ / ℓ + ‖(m i).2‖ / h) := by
  let L := labelPhaseUnscale ℓ h
  let Sc := scaledPhaseProfile ℓ h (fun a s => Q (a, s))
  have hSc : ContDiff ℝ ∞ Sc := hQ.comp (labelPhaseScale ℓ h).contDiff
  have hEq : Sc ∘ L = Q := scaled_unscale hℓ.ne' hh.ne' Q
  have hit : iteratedFDeriv ℝ j Q z =
      (iteratedFDeriv ℝ j Sc (L z)).compContinuousLinearMap (fun _ => L) := by
    rw [← hEq]
    exact L.iteratedFDeriv_comp_right hSc z (by exact_mod_cast le_top)
  rw [hit, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  refine ((iteratedFDeriv ℝ j Sc (L z)).le_opNorm _).trans ?_
  refine mul_le_mul (hJ j hj (L z)) (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    fun i _ => norm_labelPhaseUnscale_le hℓ hh (m i)) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    ((norm_nonneg _).trans (hJ j hj (L z)))

/-- The first derivative of `Q` on `(α,σ)` from the scaled jets. -/
theorem jet_one_le {ℓ h A : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Q : Vec3 × ℝ → E}
    (hQ : ContDiff ℝ ∞ Q) {n : ℕ} (hn : 1 ≤ n)
    (hJ : PhaseJetBound n A (scaledPhaseProfile ℓ h (fun a s => Q (a, s))))
    (z w : Vec3 × ℝ) : ‖fderiv ℝ Q z w‖ ≤ A * (‖w.1‖ / ℓ + ‖w.2‖ / h) := by
  have h1 := norm_iteratedFDeriv_apply_le hℓ hh hQ hJ hn z (fun _ => w)
  rw [iteratedFDeriv_one_apply] at h1
  simpa using h1

end

end TorusEuler.Paper.Lib.S5c
