import Breakdown.CertCell.AssemblyPotentialModelPoint
import Breakdown.CertCell.OwnSolidOrbit
import Breakdown.CertCell.AssemblyPotentialModelTorusMeanFacts
import Breakdown.CertCell.AssemblyPotentialModelFrameFacts

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

namespace ModelPart

open Bridge

section Conclusion

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus
open Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation Coercive.StretchInternal

theorem scale_combo (r : ℝ) (hr : 0 ≤ r) (s u : Finset (ℤ × ℤ)) (f1 f2 f3 f4 f5 : ℤ × ℤ → ℤ × ℤ → ℝ)
    (c1 c2 c3 c4 c5 c6 : ℤ × ℤ → ℝ)
    (h : (∑ i ∈ s, ∑ j ∈ s, f1 i j + 2 * ∑ i ∈ s, ∑ j ∈ u, f2 i j)
        - (∑ i ∈ s, c1 i + ∑ i ∈ s, c2 i + ∑ i ∈ u, c3 i + ∑ i ∈ s, c4 i + ∑ i ∈ s, c5 i + ∑ i ∈ u, c6 i)
      ≤ (∑ i ∈ s, ∑ j ∈ s, f3 i j + 2 * ∑ i ∈ s, ∑ j ∈ u, f4 i j) - ∑ i ∈ s, ∑ j ∈ s, f5 i j) :
    (∑ i ∈ s, ∑ j ∈ s, r * f1 i j + 2 * ∑ i ∈ s, ∑ j ∈ u, r * f2 i j)
        - (∑ i ∈ s, r * c1 i + ∑ i ∈ s, r * c2 i + ∑ i ∈ u, r * c3 i + ∑ i ∈ s, r * c4 i + ∑ i ∈ s, r * c5 i
          + ∑ i ∈ u, r * c6 i)
      ≤ (∑ i ∈ s, ∑ j ∈ s, r * f3 i j + 2 * ∑ i ∈ s, ∑ j ∈ u, r * f4 i j) - ∑ i ∈ s, ∑ j ∈ s, r * f5 i j := by
  have h2 := mul_le_mul_of_nonneg_left h hr
  have hm : ∀ y : ℝ, r * (2 * y) = 2 * (r * y) := fun y => by ring
  simp only [mul_sub, mul_add, hm, Finset.mul_sum] at h2 ⊢
  exact h2

theorem integral_double_sum {μ : Measure (ℝ × ℝ)} (s t : Finset (ℤ × ℤ)) (f : ℤ × ℤ → ℤ × ℤ → ℝ × ℝ → ℝ)
    (hf : ∀ i ∈ s, ∀ j ∈ t, Integrable (f i j) μ) :
    ∫ p, ∑ i ∈ s, ∑ j ∈ t, f i j p ∂μ = ∑ i ∈ s, ∑ j ∈ t, ∫ p, f i j p ∂μ := by
  rw [integral_finsetSum _ fun i hi => integrable_finsetSum _ fun j hj => hf i hi j hj]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_finsetSum _ fun j hj => hf i hi j hj]

theorem integrable_double_sum {μ : Measure (ℝ × ℝ)} (s t : Finset (ℤ × ℤ)) (f : ℤ × ℤ → ℤ × ℤ → ℝ × ℝ → ℝ)
    (hf : ∀ i ∈ s, ∀ j ∈ t, Integrable (f i j) μ) :
    Integrable (fun p => ∑ i ∈ s, ∑ j ∈ t, f i j p) μ :=
  integrable_finsetSum _ fun i hi => integrable_finsetSum _ fun j hj => hf i hi j hj

theorem integral_single_sum {μ : Measure (ℝ × ℝ)} (s : Finset (ℤ × ℤ)) (f : ℤ × ℤ → ℝ × ℝ → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) μ) : ∫ p, ∑ i ∈ s, f i p ∂μ = ∑ i ∈ s, ∫ p, f i p ∂μ :=
  integral_finsetSum _ hf

theorem continuous_tripleMatrix_entry {S Gω : ℝ × ℝ → Fin 3 → Fin 3 → ℂ} (hS : ∀ a b, Continuous (fun p => S p a b))
    (hG : ∀ a b, Continuous (fun p => Gω p a b)) (i j : Fin 12) :
    Continuous (fun p => tripleMatrix (S p) (Gω p) i j) := by
  simp only [tripleMatrix, modelTriple_eq_coef]
  exact (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => (hS a b).mul continuous_const).add
    (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => (hG a b).mul continuous_const)

theorem integral_combo_two {μ : Measure (ℝ × ℝ)} {a b : ℝ × ℝ → ℝ} (ha : Integrable a μ) (hb : Integrable b μ) :
    ∫ p, (a p + 2 * b p) ∂μ = ∫ p, a p ∂μ + 2 * ∫ p, b p ∂μ := by
  have h2 : Integrable (fun p => 2 * b p) μ := hb.const_mul 2
  rw [integral_add ha h2, integral_const_mul]

theorem integral_combo_six {μ : Measure (ℝ × ℝ)} {a b c d e f : ℝ × ℝ → ℝ} (ha : Integrable a μ)
    (hb : Integrable b μ) (hc : Integrable c μ) (hd : Integrable d μ) (he : Integrable e μ) (hf : Integrable f μ) :
    ∫ p, (a p + b p + c p + d p + e p + f p) ∂μ
      = ∫ p, a p ∂μ + ∫ p, b p ∂μ + ∫ p, c p ∂μ + ∫ p, d p ∂μ + ∫ p, e p ∂μ + ∫ p, f p ∂μ := by
  have g2 : Integrable (fun p => a p + b p) μ := ha.add hb
  have g3 : Integrable (fun p => a p + b p + c p) μ := g2.add hc
  have g4 : Integrable (fun p => a p + b p + c p + d p) μ := g3.add hd
  have g5 : Integrable (fun p => a p + b p + c p + d p + e p) μ := g4.add he
  rw [integral_add g5 hf, integral_add g4 he, integral_add g3 hd, integral_add g2 hc, integral_add ha hb]

theorem sesq12_add_right (M : Matrix (Fin 12) (Fin 12) ℂ) (U V V' : Fin 12 → ℂ) :
    sesq12 M U (V + V') = sesq12 M U V + sesq12 M U V' := pairSesq_add_right M U V V'

theorem sesq12_smul_right (M : Matrix (Fin 12) (Fin 12) ℂ) (c : ℂ) (U V : Fin 12 → ℂ) :
    sesq12 M U (c • V) = c * sesq12 M U V := pairSesq_smul_right M c U V

theorem merge_three {μ : Measure (ℝ × ℝ)} {a b c f : ℝ × ℝ → ℝ} (ia : Integrable a μ) (ib : Integrable b μ)
    (ic : Integrable c μ) (h : ∀ᵐ p ∂μ, a p + 2 * b p + 2 * c p = f p) :
    ∫ p, a p ∂μ + 2 * ∫ p, b p ∂μ + 2 * ∫ p, c p ∂μ = ∫ p, f p ∂μ := by
  have ib2 : Integrable (fun p => 2 * b p) μ := ib.const_mul 2
  have ic2 : Integrable (fun p => 2 * c p) μ := ic.const_mul 2
  have iab : Integrable (fun p => a p + 2 * b p) μ := ia.add ib2
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add ia ib2, ← integral_add iab ic2]
  exact integral_congr_ae h

theorem merge_two {μ : Measure (ℝ × ℝ)} {a b f : ℝ × ℝ → ℝ} (ia : Integrable a μ) (ib : Integrable b μ)
    (h : ∀ p, a p + 2 * b p = f p) : ∫ p, a p ∂μ + 2 * ∫ p, b p ∂μ = ∫ p, f p ∂μ := by
  have ib2 : Integrable (fun p => 2 * b p) μ := ib.const_mul 2
  rw [← integral_const_mul, ← integral_add ia ib2]
  exact integral_congr_ae (ae_of_all _ h)

theorem sesq_split_three (r : ℝ) (M : Matrix (Fin 12) (Fin 12) ℂ) (U V W₁ W₂ O : Fin 12 → ℂ) (h : O = W₁ + W₂) :
    r * (sesq12 M U V).re + 2 * (r * (sesq12 M U W₁).re) + 2 * (r * (sesq12 M U W₂).re)
      = r * (sesq12 M U (V + (2 : ℂ) • O)).re := by
  rw [h, smul_add, sesq12_add_right, sesq12_add_right, sesq12_smul_right, sesq12_smul_right]
  simp only [Complex.add_re, Complex.mul_re]
  norm_num
  ring

theorem sesq_split_two (r : ℝ) (M : Matrix (Fin 12) (Fin 12) ℂ) (U V O : Fin 12 → ℂ) :
    r * (sesq12 M U V).re + 2 * (r * (sesq12 M U O).re) = r * (sesq12 M U (V + (2 : ℂ) • O)).re := by
  rw [sesq12_add_right, sesq12_smul_right]
  simp only [Complex.add_re, Complex.mul_re]
  norm_num
  ring


theorem integral_combo_three {μ : Measure (ℝ × ℝ)} {a b c : ℝ × ℝ → ℝ} (ha : Integrable a μ) (hb : Integrable b μ)
    (hc : Integrable c μ) :
    ∫ p, (a p + 2 * b p + 2 * c p) ∂μ = ∫ p, a p ∂μ + 2 * ∫ p, b p ∂μ + 2 * ∫ p, c p ∂μ := by
  have h2 : Integrable (fun p => 2 * b p) μ := hb.const_mul 2
  have h3 : Integrable (fun p => 2 * c p) μ := hc.const_mul 2
  have h12 : Integrable (fun p => a p + 2 * b p) μ := ha.add h2
  rw [integral_add h12 h3, integral_add ha h2, integral_const_mul, integral_const_mul]

theorem integral_combo_twelve {μ : Measure (ℝ × ℝ)} {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : ℝ × ℝ → ℝ}
    (h1 : Integrable a1 μ) (h2 : Integrable a2 μ) (h3 : Integrable a3 μ) (h4 : Integrable a4 μ) (h5 : Integrable a5 μ) (h6 : Integrable a6 μ) (h7 : Integrable a7 μ) (h8 : Integrable a8 μ) (h9 : Integrable a9 μ) (h10 : Integrable a10 μ) (h11 : Integrable a11 μ) (h12 : Integrable a12 μ) :
    ∫ p, (a1 p + a2 p + a3 p + a4 p + a5 p + a6 p + a7 p + a8 p + a9 p + a10 p + a11 p + a12 p) ∂μ
      = ∫ p, a1 p ∂μ + ∫ p, a2 p ∂μ + ∫ p, a3 p ∂μ + ∫ p, a4 p ∂μ + ∫ p, a5 p ∂μ + ∫ p, a6 p ∂μ + ∫ p, a7 p ∂μ + ∫ p, a8 p ∂μ + ∫ p, a9 p ∂μ + ∫ p, a10 p ∂μ + ∫ p, a11 p ∂μ + ∫ p, a12 p ∂μ := by
  have g2 : Integrable (fun p => a1 p + a2 p) μ := h1.add h2
  have g3 : Integrable (fun p => a1 p + a2 p + a3 p) μ := g2.add h3
  have g4 : Integrable (fun p => a1 p + a2 p + a3 p + a4 p) μ := g3.add h4
  have g5 : Integrable (fun p => a1 p + a2 p + a3 p + a4 p + a5 p) μ := g4.add h5
  have g6 : Integrable (fun p => a1 p + a2 p + a3 p + a4 p + a5 p + a6 p) μ := g5.add h6
  have g7 : Integrable (fun p => a1 p + a2 p + a3 p + a4 p + a5 p + a6 p + a7 p) μ := g6.add h7
  have g8 : Integrable (fun p => a1 p + a2 p + a3 p + a4 p + a5 p + a6 p + a7 p + a8 p) μ := g7.add h8
  have g9 : Integrable (fun p => a1 p + a2 p + a3 p + a4 p + a5 p + a6 p + a7 p + a8 p + a9 p) μ := g8.add h9
  have g10 : Integrable (fun p => a1 p + a2 p + a3 p + a4 p + a5 p + a6 p + a7 p + a8 p + a9 p + a10 p) μ := g9.add h10
  have g11 : Integrable (fun p => a1 p + a2 p + a3 p + a4 p + a5 p + a6 p + a7 p + a8 p + a9 p + a10 p + a11 p) μ := g10.add h11
  rw [integral_add g11 h12, integral_add g10 h11, integral_add g9 h10, integral_add g8 h9, integral_add g7 h8, integral_add g6 h7, integral_add g5 h6, integral_add g4 h5, integral_add g3 h4, integral_add g2 h3, integral_add h1 h2]

theorem scale_combo_wide (r : ℝ) (hr : 0 ≤ r) (s u w : Finset (ℤ × ℤ)) (f1 f2 f3 f4 f5 f6 f7 : ℤ × ℤ → ℤ × ℤ → ℝ)
    (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 : ℤ × ℤ → ℝ)
    (h : (∑ i ∈ s, ∑ j ∈ s, f1 i j + 2 * ∑ i ∈ s, ∑ j ∈ u, f2 i j + 2 * ∑ i ∈ s, ∑ j ∈ w, f3 i j)
        - (∑ i ∈ s, c1 i + ∑ i ∈ s, c2 i + ∑ i ∈ u, c3 i + ∑ i ∈ w, c4 i + ∑ i ∈ s, c5 i + ∑ i ∈ s, c6 i
          + ∑ i ∈ u, c7 i + ∑ i ∈ w, c8 i + ∑ i ∈ s, c9 i + ∑ i ∈ s, c10 i + ∑ i ∈ u, c11 i + ∑ i ∈ w, c12 i)
      ≤ (∑ i ∈ s, ∑ j ∈ s, f4 i j + 2 * ∑ i ∈ s, ∑ j ∈ u, f5 i j + 2 * ∑ i ∈ s, ∑ j ∈ w, f6 i j)
        - ∑ i ∈ s, ∑ j ∈ s, f7 i j) :
    (∑ i ∈ s, ∑ j ∈ s, r * f1 i j + 2 * ∑ i ∈ s, ∑ j ∈ u, r * f2 i j + 2 * ∑ i ∈ s, ∑ j ∈ w, r * f3 i j)
        - (∑ i ∈ s, r * c1 i + ∑ i ∈ s, r * c2 i + ∑ i ∈ u, r * c3 i + ∑ i ∈ w, r * c4 i + ∑ i ∈ s, r * c5 i
          + ∑ i ∈ s, r * c6 i + ∑ i ∈ u, r * c7 i + ∑ i ∈ w, r * c8 i + ∑ i ∈ s, r * c9 i + ∑ i ∈ s, r * c10 i
          + ∑ i ∈ u, r * c11 i + ∑ i ∈ w, r * c12 i)
      ≤ (∑ i ∈ s, ∑ j ∈ s, r * f4 i j + 2 * ∑ i ∈ s, ∑ j ∈ u, r * f5 i j + 2 * ∑ i ∈ s, ∑ j ∈ w, r * f6 i j)
        - ∑ i ∈ s, ∑ j ∈ s, r * f7 i j := by
  have h2 := mul_le_mul_of_nonneg_left h hr
  have hm : ∀ y : ℝ, r * (2 * y) = 2 * (r * y) := fun y => by ring
  simp only [mul_sub, mul_add, hm, Finset.mul_sum] at h2 ⊢
  exact h2

theorem longOwnCharge_chargeForm {V : Type} (Q : PotentialData V) (ι : ℤ × ℤ) (U : Fin 12 → ℂ) :
    longOwnCharge Q ι (velOf U) (gradOf U) = chargeForm (longFactor Q ι * (2 * Q.longStrain))
      (longFactor Q ι * (3 / (2 * Real.sqrt 2) * Q.longGrad * (Q.epsLength + Q.length)))
      (longFactor Q ι * (2 * (3 / (2 * Real.sqrt 2)) * Q.longGrad / Q.epsLength)) U := by
  unfold longOwnCharge splitCharge chargeForm
  ring

theorem longPartnerCharge_chargeForm {V : Type} (Q : PotentialData V) (ι : ℤ × ℤ) (U : Fin 12 → ℂ) :
    longPartnerCharge Q ι (velOf U) (gradOf U) = chargeForm (longFactor Q ι * Q.longStrain)
      (longFactor Q ι * (3 / (2 * Real.sqrt 2) * Q.longGrad * Q.epsLength))
      (longFactor Q ι * (3 / (2 * Real.sqrt 2) * Q.longGrad / Q.length)) U := by
  unfold longPartnerCharge splitCharge chargeForm
  ring

theorem mask_ae_eq {μ : Measure (ℝ × ℝ)} {S : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℂ} (hS : ∀ᵐ p ∂μ, p ∈ S) :
    S.indicator f =ᵐ[μ] f := by
  filter_upwards [hS] with p hp
  rw [Set.indicator_of_mem hp]

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)

theorem boundedOnCell_mask {K : Fin D.mesh.count} {S : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℂ}
    (hS : ∀ᵐ p ∂(volume.restrict (D.mesh.box K).rect), p ∈ S)
    (hm : AEStronglyMeasurable f (volume.restrict (D.mesh.box K).rect)) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ p ∈ (D.mesh.box K).rect, p ∈ S → ‖f p‖ ≤ c) : IsBoundedOnCell D K (S.indicator f) := by
  refine ⟨hm.congr (mask_ae_eq hS).symm, c, fun p hp => ?_⟩
  by_cases h : p ∈ S
  · rw [Set.indicator_of_mem h]
    exact hc p hp h
  · simp [h, hc0]

theorem trueStretch_congr_right (K : Fin D.mesh.count) (H S : Finset (ℤ × ℤ)) (X Z Z' : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ)
    (hX : ∀ ι ∉ S, ∀ p, X ι p = 0) (hZ : ∀ ι ∈ S, ∀ α ∈ H, Z (ι - α) = Z' (ι - α)) :
    trueStretch D K H X Z = trueStretch D K H X Z' := by
  unfold trueStretch
  refine tsum_congr fun ι => Finset.sum_congr rfl fun α hα => ?_
  by_cases hι : ι ∈ S
  · rw [hZ ι hι α hα]
  · refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [hX ι hι p, sesq12_zero_left]

def PointModelStatement : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ}, TorusFacts → FrameFacts → ∀ {D : CellLayerData k C nE nM}
    {R : CellCalculusEntry D} {A : AssemblyEntry D R} {P : CouplingEntries D R}
    {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop},
    PotentialConditions D R A P states → AssemblyRegular D R → ∀ (K : Fin D.mesh.count) {p : ℝ × ℝ},
    p ∈ (D.mesh.box K).rect → 0 < p.1 → (∀ L, L ≠ K → p ∉ (D.mesh.box L).rect) →
    (∀ σ θ : ℝ, CellCert.CellAnalysis.cylPoint p.1 θ p.2 ∈ CellCalculus.ownSolid D.mesh.box K →
      ‖CellCalculus.vorticityGradOf D.givenHess σ (CellCert.CellAnalysis.cylPoint p.1 θ p.2)
        - D.model.vorticityGrad.field D.mesh.box D.azimuthOrder σ (CellCert.CellAnalysis.cylPoint p.1 θ p.2)
        - (R.high K).vorticityGrad σ (CellCert.CellAnalysis.cylPoint p.1 θ p.2)
        - (R.long K).vorticityGrad σ (CellCert.CellAnalysis.cylPoint p.1 θ p.2)‖
        ≤ (D.modelErrors K).vorticityGrad) →
    (∀ τ φ a b, ((fibGrad (D.model.strain.field D.mesh.box D.azimuthOrder) (planePoint p) τ φ a b : ℝ) : ℂ)
      = ∑ α ∈ D.model.strain.labels K, labelPhase D.azimuthOrder α τ φ * D.model.strain.planeValue D.mesh.box K α a b p) →
    (∀ τ φ a b, ((fibGrad (D.model.vorticityGrad.field D.mesh.box D.azimuthOrder) (planePoint p) τ φ a b : ℝ) : ℂ)
      = ∑ α ∈ D.model.vorticityGrad.labels K,
          labelPhase D.azimuthOrder α τ φ * D.model.vorticityGrad.planeValue D.mesh.box K α a b p) →
    (∀ τ φ a b c, ((frameSecondDeriv D.givenHess (planePoint p) τ φ a b c : ℝ) : ℂ)
      = ∑ β ∈ D.givenLabels, phase β τ φ * modeSecondDeriv β D.givenHess 0 (planePoint p) (a, b, c)) →
    (∀ a b, AEStronglyMeasurable (fun z : ℝ × ℝ => fibGrad (R.high K).strain (planePoint p) z.1 z.2 a b)
      boxMeasure) →
    (∀ a b, AEStronglyMeasurable (fun z : ℝ × ℝ => fibGrad (R.high K).vorticityGrad (planePoint p) z.1 z.2 a b)
      boxMeasure) →
    (∀ a b, AEStronglyMeasurable (fun z : ℝ × ℝ => fibGrad (R.long K).strain (planePoint p) z.1 z.2 a b)
      boxMeasure) →
    (∀ a b, AEStronglyMeasurable (fun z : ℝ × ℝ => fibGrad (R.long K).vorticityGrad (planePoint p) z.1 z.2 a b)
      boxMeasure) →
    ∀ (Dd : Finset (ℤ × ℤ)), Disjoint (D.mesh.resolved K) Dd → Disjoint (D.mesh.band K) Dd →
    ∀ (X O Yl Tt B Dv : ℤ × ℤ → Fin 12 → ℂ), (∀ ι ∈ D.mesh.resolved K, O ι = Yl ι + Tt ι) →
    (∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.resolved K,
          (sesq12 ((P.potential K).couplingModel (ι - ι') p) (X ι) (X ι' + (2 : ℂ) • O ι')).re
        + 2 * ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.band K,
          (sesq12 ((P.potential K).couplingModel (ι - ι') p) (X ι) (B ι')).re
        + 2 * ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ Dd,
          (sesq12 ((P.potential K).couplingModel (ι - ι') p) (X ι) (Dv ι')).re)
      - (∑ ι ∈ D.mesh.resolved K, epsOwnCharge (P.potential K) (velOf (X ι)) (gradOf (X ι))
        + ∑ ι ∈ D.mesh.resolved K, epsPartnerCharge (P.potential K) (velOf (O ι)) (gradOf (O ι))
        + ∑ ι ∈ D.mesh.band K, epsPartnerCharge (P.potential K) (velOf (B ι)) (gradOf (B ι))
        + ∑ ι ∈ Dd, epsPartnerCharge (P.potential K) (velOf (Dv ι)) (gradOf (Dv ι))
        + ∑ ι ∈ D.mesh.resolved K, longOwnCharge (P.potential K) ι (velOf (X ι)) (gradOf (X ι))
        + ∑ ι ∈ D.mesh.resolved K, longPartnerCharge (P.potential K) ι (velOf (O ι)) (gradOf (O ι))
        + ∑ ι ∈ D.mesh.band K, longPartnerCharge (P.potential K) ι (velOf (B ι)) (gradOf (B ι))
        + ∑ ι ∈ Dd, longPartnerCharge (P.potential K) ι (velOf (Dv ι)) (gradOf (Dv ι))
        + ∑ ι ∈ D.mesh.resolved K, highOwnCharge (P.potential K) (X ι)
        + ∑ ι ∈ D.mesh.resolved K, highPartnerCharge (P.potential K) (Tt ι)
        + ∑ ι ∈ D.mesh.band K, highPartnerCharge (P.potential K) (B ι)
        + ∑ ι ∈ Dd, highPartnerCharge (P.potential K) (Dv ι))
    ≤ (∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.resolved K,
          (sesq12 (truncCoupling D (P.potential K).harmonicLabels (ι - ι') p) (X ι) (X ι' + (2 : ℂ) • O ι')).re
        + 2 * ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.band K,
          (sesq12 (truncCoupling D (P.potential K).harmonicLabels (ι - ι') p) (X ι) (B ι')).re
        + 2 * ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ Dd,
          (sesq12 (truncCoupling D (P.potential K).harmonicLabels (ι - ι') p) (X ι) (Dv ι')).re)
      - ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.resolved K,
          (sesq12 (tripleMatrix (fun a b => labelGrad D.azimuthOrder (ι - ι') (R.high K).strain p (a, b))
              (fun a b => labelGrad D.azimuthOrder (ι - ι') (R.high K).vorticityGrad p (a, b)))
            (X ι) (X ι' + (2 : ℂ) • Yl ι')).re

theorem modelStage_of_point (hpt : PointModelStatement) (hT : TorusFacts) (hF : FrameFacts) : ModelStageHolds := by
  intro k C nE nM D R A P states hstates hreg htrue hP hLT K q v G H g κ F Pg ht ζ η
  classical
  have hK : IsCellBox (D.mesh.box K) := hreg.field.mesh_valid.box_valid K
  have hC := hP.cell_conditions
  have hsplit := hC.model_split K
  obtain ⟨Bst, hst⟩ := hreg.field.model_state
  obtain ⟨hB0, hgB, hHB⟩ := given_bounds hst
  set Dd := deactPartners D R K (P.potential K) with hDd
  have hDR : Disjoint (D.mesh.resolved K) Dd := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [hDd, deactPartners, Finset.mem_filter] at hb
    exact hb.2.1 ha
  have hDB : Disjoint (D.mesh.band K) Dd := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [hDd, deactPartners, Finset.mem_filter] at hb
    exact hb.2.2 ha
  set x := cellState D.mesh K (R.layouts K) v G H Pg κ ζ η with hx
  set X := upperProfiles D R K (P.potential K) x with hX
  set Yl := lowAt D R K (bandPart D R K (P.potential K) x) with hYl
  set Tt := tailProfiles D R K v G with hTt
  set O := restrictTo (D.mesh.resolved K : Set (ℤ × ℤ)) (otherProfiles D R K (P.potential K) x v G) with hO
  set Bf := restrictTo (D.mesh.band K : Set (ℤ × ℤ)) (trueProfiles D v G) with hBf
  set Bd := restrictTo (Dd : Set (ℤ × ℤ)) (trueProfiles D v G) with hBd
  set μ := volume.restrict (D.mesh.box K).rect with hμ
  set Sown : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ ∀ L, L ≠ K → p ∉ (D.mesh.box L).rect} with hSown
  have hae_own : ∀ᵐ p ∂μ, p ∈ Sown := ae_own_point D.mesh hreg.field.mesh_valid K
  have hXb : ∀ ι j, IsBoundedOnCell D K (fun p => X ι p j) := fun ι j =>
    boundedOnCell_of_continuous_eq D (lowSpan_continuous (lowAt_mem_lowSpan D R hC K _ ι j)) (fun _ _ => rfl)
  have hYb : ∀ ι j, IsBoundedOnCell D K (fun p => Yl ι p j) := fun ι j =>
    boundedOnCell_of_continuous_eq D (lowSpan_continuous (lowAt_mem_lowSpan D R hC K _ ι j)) (fun _ _ => rfl)
  have hXsq : ∀ ι, IsSqOn D K (X ι) := fun ι => isSqOn_of_bounded D hK (hXb ι)
  have hYsq : ∀ ι, IsSqOn D K (Yl ι) := fun ι => isSqOn_of_bounded D hK (hYb ι)
  have htr : ∀ ι, IsSqOn D K (trueProfiles D v G ι) := fun ι => (htrue.1 K q v G H g κ F Pg ht).1 ι
  have hOsq : ∀ ι ∈ D.mesh.resolved K, IsSqOn D K (O ι) := by
    intro ι hι
    have e : O ι = fun p => trueProfiles D v G ι p + (-1 : ℂ) • X ι p := by
      funext p
      simp [hO, restrictTo, hι, otherProfiles, sub_eq_add_neg]
      rfl
    rw [e]
    exact isSqOn_add_smul D hK (htr ι) (hXsq ι) (-1)
  have hBsq : ∀ ι ∈ D.mesh.band K, IsSqOn D K (Bf ι) := by
    intro ι hι
    have e : Bf ι = trueProfiles D v G ι := by
      funext p
      simp [hBf, restrictTo, hι]
    rw [e]
    exact htr ι
  have hBdsq : ∀ ι ∈ Dd, IsSqOn D K (Bd ι) := by
    intro ι hι
    have e : Bd ι = trueProfiles D v G ι := by
      funext p
      simp [hBd, restrictTo, hι]
    rw [e]
    exact htr ι
  have hae_rect : ∀ᵐ p ∂μ, p ∈ (D.mesh.box K).rect := ae_restrict_mem (rect_measurableSet _)
  have hae_vg := ae_restrict_of_ae (s := (D.mesh.box K).rect) hsplit.vorticityGrad.rest_bound
  have hae_mS := hF.model_field D.mesh D.model.strain D.azimuthOrder K hreg.field.mesh_valid
    hsplit.model_conj_closed.2.2.1
  have hae_mG := hF.model_field D.mesh D.model.vorticityGrad D.azimuthOrder K hreg.field.mesh_valid
    hsplit.model_conj_closed.2.2.2
  have hae_sH := (hF.given_expansion D.givenLabels D.given D.givenHess Bst hreg.field.model_harmonics hst
    (D.mesh.box K) hK).2
  have hae_hS := (hF.grad_section (R.high K).strain hsplit.high_measurable.2.2.1 (D.mesh.box K) hK).1
  have hae_hG := (hF.grad_section (R.high K).vorticityGrad hsplit.high_measurable.2.2.2 (D.mesh.box K) hK).1
  have hae_lS := (hF.grad_section (R.long K).strain hsplit.long_regular.2.2.1 (D.mesh.box K) hK).1
  have hae_lG := (hF.grad_section (R.long K).vorticityGrad hsplit.long_regular.2.2.2 (D.mesh.box K) hK).1
  have hae_LT : ∀ᵐ p ∂μ, ∀ ι ∈ D.mesh.resolved K,
      trueProfiles D v G ι p = lowAt D R K x ι p + tailProfile D R K ι v G p :=
    (Filter.eventually_all_finset _).2 (hLT K q v G H g κ F Pg ht ζ η)
  have hae_O : ∀ᵐ p ∂μ, ∀ ι ∈ D.mesh.resolved K, O ι p = Yl ι p + Tt ι p := by
    filter_upwards [hae_LT] with p hp ι hι
    have h1 := hp ι hι
    rw [lowAt_split D R K (P.potential K) x ι p] at h1
    have e1 : O ι p = trueProfiles D v G ι p - lowAt D R K (upperPart D R K (P.potential K) x) ι p := by
      simp only [hO, restrictTo, Finset.mem_coe, hι, if_true, otherProfiles]
      rfl
    have e2 : Tt ι p = tailProfile D R K ι v G p := by
      simp only [hTt, tailProfiles, restrictTo, Finset.mem_coe, hι, if_true]
    have e3 : Yl ι p = lowAt D R K (bandPart D R K (P.potential K) x) ι p := rfl
    rw [e1, e2, e3, h1]
    abel
  have hMb : ∀ α i j, IsBoundedOnCell D K (fun p => (P.potential K).couplingModel α p i j) := by
    intro α i j
    refine boundedOnCell_of_continuous_eq D (g := fun p => tripleMatrix
      (fun a b => (D.model.strain.comp K α a b).eval (D.mesh.box K) p)
      (fun a b => (D.model.vorticityGrad.comp K α a b).eval (D.mesh.box K) p) i j)
      (continuous_tripleMatrix_entry (fun a b => cellPoly_eval_continuous _ _)
        (fun a b => cellPoly_eval_continuous _ _) i j) fun p hp => ?_
    have hz : 0 ≤ p.2 := hK.z_order.1.trans (Set.mem_prod.1 hp).2.1
    rw [matrix_eq_tripleMatrix_of_sesq (hP.coupling_model K α p hp)]
    simp only [CellMatField.planeValue, labelValueAt, if_pos hz]
  have hgm : AEStronglyMeasurable (fun z : ℝ × Space => gradField D.given z.1 z.2) volume :=
    (continuous_gradField hst.smooth).aestronglyMeasurable
  have hLg : ∀ α ab, IsBoundedOnCell D K (fun p => labelGrad D.azimuthOrder α (gradField D.given) p ab) := by
    intro α ab
    exact ⟨((hF.grad_section _ hgm (D.mesh.box K) hK).2 D.azimuthOrder α ab), Bst, fun p _ =>
      labelGrad_norm_le hF D.azimuthOrder α _ _ Bst (fun τ φ => hgB τ _) ab⟩
  have hLh : ∀ α abc, IsBoundedOnCell D K (fun p => labelHess D.azimuthOrder α D.givenHess p abc) := by
    intro α abc
    exact ⟨((hF.secondDeriv_section _ hst.secondDeriv_measurable (D.mesh.box K) hK).2 D.azimuthOrder α abc), Bst, fun p _ =>
      labelSecond_norm_le D.azimuthOrder α _ _ Bst (fun τ φ => hHB τ _) abc⟩
  have hTb : ∀ α i j, IsBoundedOnCell D K (fun p => truncCoupling D (P.potential K).harmonicLabels α p i j) := by
    intro α i j
    by_cases hα : α ∈ (P.potential K).harmonicLabels
    · have e : (fun p => truncCoupling D (P.potential K).harmonicLabels α p i j) = fun p => tripleMatrix
          (fun a b => (labelGrad D.azimuthOrder α (gradField D.given) p (a, b)
            + labelGrad D.azimuthOrder α (gradField D.given) p (b, a)) / 2)
          (fun a b => curlGradOfSecondDeriv (labelHess D.azimuthOrder α D.givenHess p) (a, b)) i j := by
        funext p
        simp only [truncCoupling, hα, if_true]
        rfl
      rw [e]
      refine boundedOnCell_tripleMatrix D (fun a b => ?_) (fun a b => ?_) i j
      · have := boundedOnCell_const_mul D (1 / 2 : ℂ) (boundedOnCell_add D (hLg α (a, b)) (hLg α (b, a)))
        simpa [div_eq_inv_mul] using this
      · simp only [curlGradOfSecondDeriv]
        exact boundedOnCell_sum D _ _ fun j' _ => boundedOnCell_sum D _ _ fun m' _ =>
          boundedOnCell_const_mul D _ (hLh α _)
    · have e : (fun p => truncCoupling D (P.potential K).harmonicLabels α p i j) = fun _ => 0 := by
        funext p
        simp [truncCoupling, hα]
      rw [e]
      exact ⟨aestronglyMeasurable_const, 0, fun p _ => by simp⟩
  have hHs : ∀ α ab, IsBoundedOnCell D K (Sown.indicator (fun p => labelGrad D.azimuthOrder α (R.high K).strain p ab)) := by
    intro α ab
    refine boundedOnCell_mask D hae_own ((hF.grad_section _ hsplit.high_measurable.2.2.1 (D.mesh.box K) hK).2
      D.azimuthOrder α ab) hsplit.errors_nonneg.2.2.2.2.2.2.1 fun p hp hs => ?_
    exact labelGrad_norm_le hF D.azimuthOrder α _ _ _
      (fun τ φ => hsplit.strain.high_bound τ _ (orbit_mem_ownSolid D.mesh.box K hK p hp hs.1 hs.2 φ)) ab
  have hHg : ∀ α ab, IsBoundedOnCell D K
      (Sown.indicator (fun p => labelGrad D.azimuthOrder α (R.high K).vorticityGrad p ab)) := by
    intro α ab
    refine boundedOnCell_mask D hae_own ((hF.grad_section _ hsplit.high_measurable.2.2.2 (D.mesh.box K) hK).2
      D.azimuthOrder α ab) hsplit.errors_nonneg.2.2.2.2.2.2.2 fun p hp hs => ?_
    exact labelGrad_norm_le hF D.azimuthOrder α _ _ _
      (fun τ φ => hsplit.vorticityGrad.high_bound τ _ (orbit_mem_ownSolid D.mesh.box K hK p hp hs.1 hs.2 φ)) ab
  have hZsq : ∀ ι ∈ D.mesh.resolved K, IsSqOn D K (fun p => X ι p + (2 : ℂ) • O ι p) :=
    fun ι hι => isSqOn_add_smul D hK (hXsq ι) (hOsq ι hι) 2
  have hTsq : ∀ ι ∈ D.mesh.resolved K, IsSqOn D K (Tt ι) := by
    intro ι hι
    refine isSqOn_congr D (isSqOn_add_smul D hK (hOsq ι hι) (hYsq ι) (-1)) ?_
    filter_upwards [hae_O] with p hp
    rw [hp ι hι]
    funext j
    simp
  have hW2 : ∀ ι, IsSqOn D K (fun p => X ι p + (2 : ℂ) • Yl ι p) := fun ι => isSqOn_add_smul D hK (hXsq ι) (hYsq ι) 2
  set f1 : ℤ × ℤ → ℤ × ℤ → ℝ × ℝ → ℝ := fun ι ι' p =>
    p.1 * (sesq12 ((P.potential K).couplingModel (ι - ι') p) (X ι p) (X ι' p + (2 : ℂ) • O ι' p)).re with hf1
  set f2 : ℤ × ℤ → ℤ × ℤ → ℝ × ℝ → ℝ := fun ι ι' p =>
    p.1 * (sesq12 ((P.potential K).couplingModel (ι - ι') p) (X ι p) (Bf ι' p)).re with hf2
  set f3 : ℤ × ℤ → ℤ × ℤ → ℝ × ℝ → ℝ := fun ι ι' p =>
    p.1 * (sesq12 ((P.potential K).couplingModel (ι - ι') p) (X ι p) (Bd ι' p)).re with hf3
  set f4 : ℤ × ℤ → ℤ × ℤ → ℝ × ℝ → ℝ := fun ι ι' p =>
    p.1 * (sesq12 (truncCoupling D (P.potential K).harmonicLabels (ι - ι') p) (X ι p) (X ι' p + (2 : ℂ) • O ι' p)).re
    with hf4
  set f5 : ℤ × ℤ → ℤ × ℤ → ℝ × ℝ → ℝ := fun ι ι' p =>
    p.1 * (sesq12 (truncCoupling D (P.potential K).harmonicLabels (ι - ι') p) (X ι p) (Bf ι' p)).re with hf5
  set f6 : ℤ × ℤ → ℤ × ℤ → ℝ × ℝ → ℝ := fun ι ι' p =>
    p.1 * (sesq12 (truncCoupling D (P.potential K).harmonicLabels (ι - ι') p) (X ι p) (Bd ι' p)).re with hf6
  set f7 : ℤ × ℤ → ℤ × ℤ → ℝ × ℝ → ℝ := fun ι ι' p =>
    p.1 * (sesq12 (tripleMatrix (fun a b => labelGrad D.azimuthOrder (ι - ι') (R.high K).strain p (a, b))
      (fun a b => labelGrad D.azimuthOrder (ι - ι') (R.high K).vorticityGrad p (a, b)))
      (X ι p) (X ι' p + (2 : ℂ) • Yl ι' p)).re with hf7
  set c1 : ℤ × ℤ → ℝ × ℝ → ℝ := fun ι p => p.1 * epsOwnCharge (P.potential K) (velOf (X ι p)) (gradOf (X ι p))
    with hc1
  set c2 : ℤ × ℤ → ℝ × ℝ → ℝ := fun ι p => p.1 * epsPartnerCharge (P.potential K) (velOf (O ι p)) (gradOf (O ι p))
    with hc2
  set c3 : ℤ × ℤ → ℝ × ℝ → ℝ := fun ι p => p.1 * epsPartnerCharge (P.potential K) (velOf (Bf ι p)) (gradOf (Bf ι p))
    with hc3
  set c4 : ℤ × ℤ → ℝ × ℝ → ℝ := fun ι p => p.1 * epsPartnerCharge (P.potential K) (velOf (Bd ι p)) (gradOf (Bd ι p))
    with hc4
  set c5 : ℤ × ℤ → ℝ × ℝ → ℝ := fun ι p =>
    p.1 * longOwnCharge (P.potential K) ι (velOf (X ι p)) (gradOf (X ι p)) with hc5
  set c6 : ℤ × ℤ → ℝ × ℝ → ℝ := fun ι p =>
    p.1 * longPartnerCharge (P.potential K) ι (velOf (O ι p)) (gradOf (O ι p)) with hc6
  set c7 : ℤ × ℤ → ℝ × ℝ → ℝ := fun ι p =>
    p.1 * longPartnerCharge (P.potential K) ι (velOf (Bf ι p)) (gradOf (Bf ι p)) with hc7
  set c8 : ℤ × ℤ → ℝ × ℝ → ℝ := fun ι p =>
    p.1 * longPartnerCharge (P.potential K) ι (velOf (Bd ι p)) (gradOf (Bd ι p)) with hc8
  set c9 : ℤ × ℤ → ℝ × ℝ → ℝ := fun ι p => p.1 * highOwnCharge (P.potential K) (X ι p) with hc9
  set c10 : ℤ × ℤ → ℝ × ℝ → ℝ := fun ι p => p.1 * highPartnerCharge (P.potential K) (Tt ι p) with hc10
  set c11 : ℤ × ℤ → ℝ × ℝ → ℝ := fun ι p => p.1 * highPartnerCharge (P.potential K) (Bf ι p) with hc11
  set c12 : ℤ × ℤ → ℝ × ℝ → ℝ := fun ι p => p.1 * highPartnerCharge (P.potential K) (Bd ι p) with hc12
  have i1 : ∀ ι ∈ D.mesh.resolved K, ∀ ι' ∈ D.mesh.resolved K, Integrable (f1 ι ι') μ :=
    fun ι _ ι' hι' => integrableOn_sesq_re D hK (fun i j => hMb _ i j) (hXb ι) (hZsq ι' hι')
  have i2 : ∀ ι ∈ D.mesh.resolved K, ∀ ι' ∈ D.mesh.band K, Integrable (f2 ι ι') μ :=
    fun ι _ ι' hι' => integrableOn_sesq_re D hK (fun i j => hMb _ i j) (hXb ι) (hBsq ι' hι')
  have i3 : ∀ ι ∈ D.mesh.resolved K, ∀ ι' ∈ Dd, Integrable (f3 ι ι') μ :=
    fun ι _ ι' hι' => integrableOn_sesq_re D hK (fun i j => hMb _ i j) (hXb ι) (hBdsq ι' hι')
  have i4 : ∀ ι ∈ D.mesh.resolved K, ∀ ι' ∈ D.mesh.resolved K, Integrable (f4 ι ι') μ :=
    fun ι _ ι' hι' => integrableOn_sesq_re D hK (fun i j => hTb _ i j) (hXb ι) (hZsq ι' hι')
  have i5 : ∀ ι ∈ D.mesh.resolved K, ∀ ι' ∈ D.mesh.band K, Integrable (f5 ι ι') μ :=
    fun ι _ ι' hι' => integrableOn_sesq_re D hK (fun i j => hTb _ i j) (hXb ι) (hBsq ι' hι')
  have i6 : ∀ ι ∈ D.mesh.resolved K, ∀ ι' ∈ Dd, Integrable (f6 ι ι') μ :=
    fun ι _ ι' hι' => integrableOn_sesq_re D hK (fun i j => hTb _ i j) (hXb ι) (hBdsq ι' hι')
  have i7 : ∀ ι ∈ D.mesh.resolved K, ∀ ι' ∈ D.mesh.resolved K, Integrable (f7 ι ι') μ := by
    intro ι _ ι' _
    refine (integrableOn_sesq_re D hK (M := fun p => tripleMatrix
        (fun a b => Sown.indicator (fun p => labelGrad D.azimuthOrder (ι - ι') (R.high K).strain p (a, b)) p)
        (fun a b => Sown.indicator (fun p => labelGrad D.azimuthOrder (ι - ι') (R.high K).vorticityGrad p (a, b)) p))
      (fun i j => boundedOnCell_tripleMatrix D (fun a b => hHs _ (a, b)) (fun a b => hHg _ (a, b)) i j)
      (hXb ι) (hW2 ι')).congr ?_
    filter_upwards [hae_own] with p hp
    simp only [hf7, Set.indicator_of_mem hp]
  have j1 : ∀ ι ∈ D.mesh.resolved K, Integrable (c1 ι) μ := by
    intro ι _
    simp only [hc1, epsOwnCharge_eq, epsOwnForm]
    exact integrableOn_chargeForm D hK (hXsq ι) _ _ _
  have j2 : ∀ ι ∈ D.mesh.resolved K, Integrable (c2 ι) μ := by
    intro ι hι
    simp only [hc2, epsPartnerCharge_eq, epsPartnerForm]
    exact integrableOn_chargeForm D hK (hOsq ι hι) _ _ _
  have j3 : ∀ ι ∈ D.mesh.band K, Integrable (c3 ι) μ := by
    intro ι hι
    simp only [hc3, epsPartnerCharge_eq, epsPartnerForm]
    exact integrableOn_chargeForm D hK (hBsq ι hι) _ _ _
  have j4 : ∀ ι ∈ Dd, Integrable (c4 ι) μ := by
    intro ι hι
    simp only [hc4, epsPartnerCharge_eq, epsPartnerForm]
    exact integrableOn_chargeForm D hK (hBdsq ι hι) _ _ _
  have j5 : ∀ ι ∈ D.mesh.resolved K, Integrable (c5 ι) μ := by
    intro ι _
    simp only [hc5, longOwnCharge_chargeForm]
    exact integrableOn_chargeForm D hK (hXsq ι) _ _ _
  have j6 : ∀ ι ∈ D.mesh.resolved K, Integrable (c6 ι) μ := by
    intro ι hι
    simp only [hc6, longPartnerCharge_chargeForm]
    exact integrableOn_chargeForm D hK (hOsq ι hι) _ _ _
  have j7 : ∀ ι ∈ D.mesh.band K, Integrable (c7 ι) μ := by
    intro ι hι
    simp only [hc7, longPartnerCharge_chargeForm]
    exact integrableOn_chargeForm D hK (hBsq ι hι) _ _ _
  have j8 : ∀ ι ∈ Dd, Integrable (c8 ι) μ := by
    intro ι hι
    simp only [hc8, longPartnerCharge_chargeForm]
    exact integrableOn_chargeForm D hK (hBdsq ι hι) _ _ _
  have j9 : ∀ ι ∈ D.mesh.resolved K, Integrable (c9 ι) μ := by
    intro ι _
    simp only [hc9, highOwnCharge_eq]
    exact integrableOn_chargeForm D hK (hXsq ι) _ _ _
  have j10 : ∀ ι ∈ D.mesh.resolved K, Integrable (c10 ι) μ := by
    intro ι hι
    simp only [hc10, highPartnerCharge_eq]
    exact integrableOn_chargeForm D hK (hTsq ι hι) _ _ _
  have j11 : ∀ ι ∈ D.mesh.band K, Integrable (c11 ι) μ := by
    intro ι hι
    simp only [hc11, highPartnerCharge_eq]
    exact integrableOn_chargeForm D hK (hBsq ι hι) _ _ _
  have j12 : ∀ ι ∈ Dd, Integrable (c12 ι) μ := by
    intro ι hι
    simp only [hc12, highPartnerCharge_eq]
    exact integrableOn_chargeForm D hK (hBdsq ι hι) _ _ _
  have hpw : ∀ᵐ p ∂μ,
      (∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.resolved K, f1 ι ι' p + 2 * ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.band K, f2 ι ι' p
          + 2 * ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ Dd, f3 ι ι' p)
        - (∑ ι ∈ D.mesh.resolved K, c1 ι p + ∑ ι ∈ D.mesh.resolved K, c2 ι p + ∑ ι ∈ D.mesh.band K, c3 ι p + ∑ ι ∈ Dd, c4 ι p
          + ∑ ι ∈ D.mesh.resolved K, c5 ι p + ∑ ι ∈ D.mesh.resolved K, c6 ι p + ∑ ι ∈ D.mesh.band K, c7 ι p + ∑ ι ∈ Dd, c8 ι p
          + ∑ ι ∈ D.mesh.resolved K, c9 ι p + ∑ ι ∈ D.mesh.resolved K, c10 ι p + ∑ ι ∈ D.mesh.band K, c11 ι p + ∑ ι ∈ Dd, c12 ι p)
      ≤ (∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.resolved K, f4 ι ι' p + 2 * ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.band K, f5 ι ι' p
          + 2 * ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ Dd, f6 ι ι' p)
        - ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.resolved K, f7 ι ι' p := by
    filter_upwards [hae_rect, hae_own, hae_mS, hae_mG, hae_sH, hae_hS, hae_hG, hae_lS, hae_lG, hae_O, hae_vg]
      with p hp hown h1 h2 h3 h4 h5 h6 h7 h8 h9
    have h0 : 0 ≤ p.1 := (rect_fst_bounds hK hp).1
    have hq := hpt hT hF hP hreg K hp hown.1 hown.2 h9 h1 h2 h3 h4 h5 h6 h7 Dd hDR hDB (fun ι => X ι p) (fun ι => O ι p)
      (fun ι => Yl ι p) (fun ι => Tt ι p) (fun ι => Bf ι p) (fun ι => Bd ι p) h8
    exact scale_combo_wide p.1 h0 (D.mesh.resolved K) (D.mesh.band K) Dd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq
  have iA1 := integrable_double_sum _ _ f1 i1
  have iA2 := integrable_double_sum _ _ f2 i2
  have iA3 := integrable_double_sum _ _ f3 i3
  have iA4 := integrable_double_sum _ _ f4 i4
  have iA5 := integrable_double_sum _ _ f5 i5
  have iA6 := integrable_double_sum _ _ f6 i6
  have iA7 := integrable_double_sum _ _ f7 i7
  have iC1 : Integrable (fun p => ∑ ι ∈ D.mesh.resolved K, c1 ι p) μ := integrable_finsetSum _ j1
  have iC2 : Integrable (fun p => ∑ ι ∈ D.mesh.resolved K, c2 ι p) μ := integrable_finsetSum _ j2
  have iC3 : Integrable (fun p => ∑ ι ∈ D.mesh.band K, c3 ι p) μ := integrable_finsetSum _ j3
  have iC4 : Integrable (fun p => ∑ ι ∈ Dd, c4 ι p) μ := integrable_finsetSum _ j4
  have iC5 : Integrable (fun p => ∑ ι ∈ D.mesh.resolved K, c5 ι p) μ := integrable_finsetSum _ j5
  have iC6 : Integrable (fun p => ∑ ι ∈ D.mesh.resolved K, c6 ι p) μ := integrable_finsetSum _ j6
  have iC7 : Integrable (fun p => ∑ ι ∈ D.mesh.band K, c7 ι p) μ := integrable_finsetSum _ j7
  have iC8 : Integrable (fun p => ∑ ι ∈ Dd, c8 ι p) μ := integrable_finsetSum _ j8
  have iC9 : Integrable (fun p => ∑ ι ∈ D.mesh.resolved K, c9 ι p) μ := integrable_finsetSum _ j9
  have iC10 : Integrable (fun p => ∑ ι ∈ D.mesh.resolved K, c10 ι p) μ := integrable_finsetSum _ j10
  have iC11 : Integrable (fun p => ∑ ι ∈ D.mesh.band K, c11 ι p) μ := integrable_finsetSum _ j11
  have iC12 : Integrable (fun p => ∑ ι ∈ Dd, c12 ι p) μ := integrable_finsetSum _ j12
  have iL1 : Integrable (fun p => ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.resolved K, f1 ι ι' p + 2 * ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.band K, f2 ι ι' p
          + 2 * ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ Dd, f3 ι ι' p) μ := (iA1.add (iA2.const_mul 2)).add (iA3.const_mul 2)
  have iL2 : Integrable (fun p => ∑ ι ∈ D.mesh.resolved K, c1 ι p + ∑ ι ∈ D.mesh.resolved K, c2 ι p + ∑ ι ∈ D.mesh.band K, c3 ι p + ∑ ι ∈ Dd, c4 ι p
          + ∑ ι ∈ D.mesh.resolved K, c5 ι p + ∑ ι ∈ D.mesh.resolved K, c6 ι p + ∑ ι ∈ D.mesh.band K, c7 ι p + ∑ ι ∈ Dd, c8 ι p
          + ∑ ι ∈ D.mesh.resolved K, c9 ι p + ∑ ι ∈ D.mesh.resolved K, c10 ι p + ∑ ι ∈ D.mesh.band K, c11 ι p + ∑ ι ∈ Dd, c12 ι p) μ :=
    ((((((((((iC1.add iC2).add iC3).add iC4).add iC5).add iC6).add iC7).add iC8).add iC9).add iC10).add iC11).add iC12
  have iR1 : Integrable (fun p => ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.resolved K, f4 ι ι' p + 2 * ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.band K, f5 ι ι' p
          + 2 * ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ Dd, f6 ι ι' p) μ := (iA4.add (iA5.const_mul 2)).add (iA6.const_mul 2)
  have hmono : ∫ p, ((∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.resolved K, f1 ι ι' p + 2 * ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.band K, f2 ι ι' p
          + 2 * ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ Dd, f3 ι ι' p)
        - (∑ ι ∈ D.mesh.resolved K, c1 ι p + ∑ ι ∈ D.mesh.resolved K, c2 ι p + ∑ ι ∈ D.mesh.band K, c3 ι p + ∑ ι ∈ Dd, c4 ι p
          + ∑ ι ∈ D.mesh.resolved K, c5 ι p + ∑ ι ∈ D.mesh.resolved K, c6 ι p + ∑ ι ∈ D.mesh.band K, c7 ι p + ∑ ι ∈ Dd, c8 ι p
          + ∑ ι ∈ D.mesh.resolved K, c9 ι p + ∑ ι ∈ D.mesh.resolved K, c10 ι p + ∑ ι ∈ D.mesh.band K, c11 ι p + ∑ ι ∈ Dd, c12 ι p)) ∂μ
      ≤ ∫ p, ((∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.resolved K, f4 ι ι' p + 2 * ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.band K, f5 ι ι' p
          + 2 * ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ Dd, f6 ι ι' p)
        - ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.resolved K, f7 ι ι' p) ∂μ :=
    integral_mono_ae (iL1.sub iL2) (iR1.sub iA7) hpw
  rw [integral_sub iL1 iL2, integral_sub iR1 iA7, integral_combo_three iA1 iA2 iA3, integral_combo_three iA4 iA5 iA6,
    integral_combo_twelve iC1 iC2 iC3 iC4 iC5 iC6 iC7 iC8 iC9 iC10 iC11 iC12, integral_double_sum _ _ _ i1,
    integral_double_sum _ _ _ i2, integral_double_sum _ _ _ i3, integral_double_sum _ _ _ i4,
    integral_double_sum _ _ _ i5, integral_double_sum _ _ _ i6, integral_single_sum _ _ j1,
    integral_single_sum _ _ j2, integral_single_sum _ _ j3, integral_single_sum _ _ j4, integral_single_sum _ _ j5,
    integral_single_sum _ _ j6, integral_single_sum _ _ j7, integral_single_sum _ _ j8, integral_single_sum _ _ j9,
    integral_single_sum _ _ j10, integral_single_sum _ _ j11, integral_single_sum _ _ j12] at hmono
  have hz7 : ∫ p, (∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.resolved K, f7 ι ι' p) ∂μ = 0 := by
    have hXl : ∀ ι k, (fun p => X ι p k) ∈ lowSpan (D.mesh.maxVolumeDeg K) (D.mesh.maxVolumeDeg K) :=
      fun ι k => lowAt_mem_lowSpan D R hC K _ ι k
    have hZl : ∀ ι k, (fun p => (X ι p + (2 : ℂ) • Yl ι p) k) ∈ lowSpan (D.mesh.maxVolumeDeg K) (D.mesh.maxVolumeDeg K) := by
      intro ι k
      have e : (fun p => (X ι p + (2 : ℂ) • Yl ι p) k) = fun p => X ι p k + 2 * Yl ι p k := by
        funext p
        simp [Pi.add_apply, Pi.smul_apply]
      rw [e]
      exact lowSpan_add (hXl ι k) (lowSpan_const_mul 2 (lowAt_mem_lowSpan D R hC K (bandPart D R K (P.potential K) x) ι k))
    have hv := highLow_vanish (K := D.mesh.box K) (Q := D.mesh.maxVolumeDeg K) (N := 2 * D.mesh.maxVolumeDeg K + 1)
      (by omega) (fun α p a b => labelGrad D.azimuthOrder α (R.high K).strain p (a, b))
      (fun α p a b => labelGrad D.azimuthOrder α (R.high K).vorticityGrad p (a, b))
      (fun α a b => (integrableOn_of_boundedOnCell D (hHs α (a, b))).congr (mask_ae_eq hae_own))
      (fun α a b => (integrableOn_of_boundedOnCell D (hHg α (a, b))).congr (mask_ae_eq hae_own))
      (fun α a b i j hi hj => hsplit.strain_orthogonal α a b i j hi hj)
      (fun α a b i j hi hj => hsplit.vorticityGrad_orthogonal α a b i j hi hj)
      (D.mesh.resolved K) X (fun ι p => X ι p + (2 : ℂ) • Yl ι p) hXl hZl
    rw [← hv]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [hf7, Finset.mul_sum]
    rfl
  have hcp1 : couplingPair D R K (P.potential K) (upperPart D R K (P.potential K) x) (upperPart D R K (P.potential K) x)
      = modelPair D K (P.potential K).couplingModel (D.mesh.resolved K) (D.mesh.resolved K) X X :=
    couplingPair_eq_modelPair D R K _ _ _
  have hcp2 : couplingPair D R K (P.potential K) (upperPart D R K (P.potential K) x) (bandPart D R K (P.potential K) x)
      = modelPair D K (P.potential K).couplingModel (D.mesh.resolved K) (D.mesh.resolved K) X Yl :=
    couplingPair_eq_modelPair D R K _ _ _
  have hbl : bandLinear D K (A.blocks K).potentialSource x (fun ι => bandProfile D ι v G)
      = 2 * modelPair D K (P.potential K).couplingModel (D.mesh.resolved K) (D.mesh.band K) X Bf :=
    bandLinear_eq D R hP K x (hstates K q v G H g κ F Pg ht ζ η) _ (fun ι _ => htr ι) hMb hXb
  have hmerge : modelPair D K (P.potential K).couplingModel (D.mesh.resolved K) (D.mesh.resolved K) X X
      + 2 * modelPair D K (P.potential K).couplingModel (D.mesh.resolved K) (D.mesh.resolved K) X Yl
      + 2 * modelPair D K (P.potential K).couplingModel (D.mesh.resolved K) (D.mesh.resolved K) X Tt
      = ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.resolved K, ∫ p, f1 ι ι' p ∂μ := by
    unfold modelPair
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ι hι => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ι' hι' => ?_
    refine merge_three (integrableOn_sesq_re D hK (fun i j => hMb (ι - ι') i j) (hXb ι) (hXsq ι'))
      (integrableOn_sesq_re D hK (fun i j => hMb (ι - ι') i j) (hXb ι) (hYsq ι'))
      (integrableOn_sesq_re D hK (fun i j => hMb (ι - ι') i j) (hXb ι) (hTsq ι' hι')) ?_
    filter_upwards [hae_O] with p hp
    exact sesq_split_three _ _ _ _ _ _ _ (hp ι' hι')
  have hdeL : modelPair D K (P.potential K).couplingModel (D.mesh.resolved K) Dd X (trueProfiles D v G)
      = ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ Dd, ∫ p, f3 ι ι' p ∂μ := by
    unfold modelPair
    refine Finset.sum_congr rfl fun ι _ => Finset.sum_congr rfl fun ι' hι' =>
      integral_congr_ae (ae_of_all _ fun p => ?_)
    simp [hf3, hBd, restrictTo, hι']
  have hXz : ∀ ι ∉ D.mesh.resolved K, ∀ p, X ι p = 0 := by
    intro ι hι p
    simp [hX, upperProfiles, lowAt, hι]
  have hOz : ∀ ι ∉ D.mesh.resolved K, ∀ p, O ι p = 0 := by
    intro ι hι p
    simp [hO, restrictTo, hι]
  have hBz : ∀ ι ∉ D.mesh.band K, ∀ p, Bf ι p = 0 := by
    intro ι hι p
    simp [hBf, restrictTo, hι]
  have hBdz : ∀ ι ∉ Dd, ∀ p, Bd ι p = 0 := by
    intro ι hι p
    simp [hBd, restrictTo, hι]
  have hts1 := trueStretch_eq_modelPair D K (P.potential K).harmonicLabels (D.mesh.resolved K) (D.mesh.resolved K)
    X X hXz hXz
  have hts2 := trueStretch_eq_modelPair D K (P.potential K).harmonicLabels (D.mesh.resolved K) (D.mesh.resolved K)
    X O hXz hOz
  have hts3 := trueStretch_eq_modelPair D K (P.potential K).harmonicLabels (D.mesh.resolved K) (D.mesh.band K)
    X Bf hXz hBz
  have hts4 : trueStretch D K (P.potential K).harmonicLabels X (restrictTo (deactivatedSet D K) (trueProfiles D v G))
      = modelPair D K (truncCoupling D (P.potential K).harmonicLabels) (D.mesh.resolved K) Dd X Bd := by
    rw [trueStretch_congr_right D K _ (D.mesh.resolved K) X _ Bd hXz ?_]
    · exact trueStretch_eq_modelPair D K _ _ _ X Bd hXz hBdz
    · intro ι hι α hα
      have hiff : ι - α ∈ deactivatedSet D K ↔ ι - α ∈ Dd := by
        rw [hDd, deactPartners, Finset.mem_filter]
        exact ⟨fun h => ⟨Finset.mem_image.2 ⟨(ι, α), Finset.mem_product.2 ⟨hι, hα⟩, rfl⟩, h⟩, fun h => h.2⟩
      funext p
      by_cases h : ι - α ∈ Dd
      · simp [hBd, restrictTo, h, hiff.2 h]
      · simp [hBd, restrictTo, h, mt hiff.1 h]
  have hmergeR : modelPair D K (truncCoupling D (P.potential K).harmonicLabels) (D.mesh.resolved K) (D.mesh.resolved K) X X
      + 2 * modelPair D K (truncCoupling D (P.potential K).harmonicLabels) (D.mesh.resolved K) (D.mesh.resolved K) X O
      = ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.resolved K, ∫ p, f4 ι ι' p ∂μ := by
    unfold modelPair
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ι hι => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ι' hι' => ?_
    exact merge_two (integrableOn_sesq_re D hK (fun i j => hTb (ι - ι') i j) (hXb ι) (hXsq ι'))
      (integrableOn_sesq_re D hK (fun i j => hTb (ι - ι') i j) (hXb ι) (hOsq ι' hι'))
      (fun p => sesq_split_two _ _ _ _ _)
  have hch1 : formAmount D K (D.mesh.resolved K) (epsOwnCharge (P.potential K)) X
      = ∑ ι ∈ D.mesh.resolved K, ∫ p, c1 ι p ∂μ := rfl
  have hch2 : formAmount D K (D.mesh.resolved K) (epsPartnerCharge (P.potential K)) (otherProfiles D R K (P.potential K) x v G)
      = ∑ ι ∈ D.mesh.resolved K, ∫ p, c2 ι p ∂μ := by
    refine Finset.sum_congr rfl fun ι hι => integral_congr_ae (ae_of_all _ fun p => ?_)
    simp [hc2, hO, restrictTo, hι]
  have hch3 : formAmount D K (D.mesh.band K) (epsPartnerCharge (P.potential K)) (trueProfiles D v G)
      = ∑ ι ∈ D.mesh.band K, ∫ p, c3 ι p ∂μ := by
    refine Finset.sum_congr rfl fun ι hι => integral_congr_ae (ae_of_all _ fun p => ?_)
    simp [hc3, hBf, restrictTo, hι]
  have hch4 : formAmount D K Dd (epsPartnerCharge (P.potential K)) (trueProfiles D v G)
      = ∑ ι ∈ Dd, ∫ p, c4 ι p ∂μ := by
    refine Finset.sum_congr rfl fun ι hι => integral_congr_ae (ae_of_all _ fun p => ?_)
    simp [hc4, hBd, restrictTo, hι]
  have hch5 : labelFormAmount D K (D.mesh.resolved K) (longOwnCharge (P.potential K)) X
      = ∑ ι ∈ D.mesh.resolved K, ∫ p, c5 ι p ∂μ := rfl
  have hch6 : labelFormAmount D K (D.mesh.resolved K) (longPartnerCharge (P.potential K))
        (otherProfiles D R K (P.potential K) x v G)
      = ∑ ι ∈ D.mesh.resolved K, ∫ p, c6 ι p ∂μ := by
    refine Finset.sum_congr rfl fun ι hι => integral_congr_ae (ae_of_all _ fun p => ?_)
    simp [hc6, hO, restrictTo, hι]
  have hch7 : labelFormAmount D K (D.mesh.band K) (longPartnerCharge (P.potential K)) (trueProfiles D v G)
      = ∑ ι ∈ D.mesh.band K, ∫ p, c7 ι p ∂μ := by
    refine Finset.sum_congr rfl fun ι hι => integral_congr_ae (ae_of_all _ fun p => ?_)
    simp [hc7, hBf, restrictTo, hι]
  have hch8 : labelFormAmount D K Dd (longPartnerCharge (P.potential K)) (trueProfiles D v G)
      = ∑ ι ∈ Dd, ∫ p, c8 ι p ∂μ := by
    refine Finset.sum_congr rfl fun ι hι => integral_congr_ae (ae_of_all _ fun p => ?_)
    simp [hc8, hBd, restrictTo, hι]
  have hch9 : highOwnAmount D K (P.potential K) (D.mesh.resolved K) X = ∑ ι ∈ D.mesh.resolved K, ∫ p, c9 ι p ∂μ := rfl
  have hch10 : highPartnerAmount D K (P.potential K) (D.mesh.resolved K) Tt
      = ∑ ι ∈ D.mesh.resolved K, ∫ p, c10 ι p ∂μ := rfl
  have hch11 : highPartnerAmount D K (P.potential K) (D.mesh.band K) (trueProfiles D v G)
      = ∑ ι ∈ D.mesh.band K, ∫ p, c11 ι p ∂μ := by
    refine Finset.sum_congr rfl fun ι hι => integral_congr_ae (ae_of_all _ fun p => ?_)
    simp [hc11, hBf, restrictTo, hι]
  have hch12 : highPartnerAmount D K (P.potential K) Dd (trueProfiles D v G)
      = ∑ ι ∈ Dd, ∫ p, c12 ι p ∂μ := by
    refine Finset.sum_congr rfl fun ι hι => integral_congr_ae (ae_of_all _ fun p => ?_)
    simp [hc12, hBd, restrictTo, hι]
  have hL2 : modelPair D K (P.potential K).couplingModel (D.mesh.resolved K) (D.mesh.band K) X Bf
      = ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.band K, ∫ p, f2 ι ι' p ∂μ := rfl
  have hR5 : modelPair D K (truncCoupling D (P.potential K).harmonicLabels) (D.mesh.resolved K) (D.mesh.band K) X Bf
      = ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ D.mesh.band K, ∫ p, f5 ι ι' p ∂μ := rfl
  have hR6 : modelPair D K (truncCoupling D (P.potential K).harmonicLabels) (D.mesh.resolved K) Dd X Bd
      = ∑ ι ∈ D.mesh.resolved K, ∑ ι' ∈ Dd, ∫ p, f6 ι ι' p ∂μ := rfl
  rw [hcp1, hcp2, hbl, hdeL, hts1, hts2, hts3, hts4, hch1, hch2, hch3, hch4, hch5, hch6, hch7, hch8, hch9, hch10,
    hch11, hch12]
  linarith [hmono, hz7, hmerge, hmergeR, hL2, hR5, hR6]

end Conclusion

end ModelPart

end Internal

end Assembly

end CertCell

end Breakdown
