import Breakdown.CertCell.AssemblyPotentialModelProfiles
import Breakdown.CertCell.OwnSolidOrbit

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

namespace ModelPart

open Bridge


section Bounded

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus
open Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation Coercive.StretchInternal

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)

theorem integrableOn_of_boundedOnCell {K : Fin D.mesh.count} {f : ℝ × ℝ → ℂ} (h : IsBoundedOnCell D K f) :
    IntegrableOn f (D.mesh.box K).rect := by
  obtain ⟨c, hc⟩ := boundedOnCell_ae_bound D h
  haveI : IsFiniteMeasure (volume.restrict (D.mesh.box K).rect) := isFiniteMeasure_restrict.2 (rect_finite _).ne
  exact Integrable.mono' (integrable_const c) h.1 hc

theorem boundedOnCell_of_continuous_eq {K : Fin D.mesh.count} {f g : ℝ × ℝ → ℂ} (hg : Continuous g)
    (h : ∀ p ∈ (D.mesh.box K).rect, f p = g p) : IsBoundedOnCell D K f := by
  have hc : IsCompact (D.mesh.box K).rect := isCompact_Icc.prod isCompact_Icc
  obtain ⟨c, hc'⟩ := hc.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨hg.aestronglyMeasurable.congr ((ae_restrict_iff' (rect_measurableSet _)).2
    (Filter.Eventually.of_forall fun p hp => (h p hp).symm)), c, fun p hp => ?_⟩
  rw [h p hp]
  exact hc' p hp

theorem boundedOnCell_add {K : Fin D.mesh.count} {f g : ℝ × ℝ → ℂ} (hf : IsBoundedOnCell D K f)
    (hg : IsBoundedOnCell D K g) : IsBoundedOnCell D K (fun p => f p + g p) := by
  obtain ⟨c₁, h₁⟩ := hf.2
  obtain ⟨c₂, h₂⟩ := hg.2
  exact ⟨hf.1.add hg.1, c₁ + c₂, fun p hp => (norm_add_le _ _).trans (add_le_add (h₁ p hp) (h₂ p hp))⟩

theorem boundedOnCell_const_mul {K : Fin D.mesh.count} (a : ℂ) {f : ℝ × ℝ → ℂ} (hf : IsBoundedOnCell D K f) :
    IsBoundedOnCell D K (fun p => a * f p) := by
  obtain ⟨c, h⟩ := hf.2
  refine ⟨hf.1.const_mul a, ‖a‖ * c, fun p hp => ?_⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (h p hp) (norm_nonneg a)

theorem boundedOnCell_mul_const {K : Fin D.mesh.count} (a : ℂ) {f : ℝ × ℝ → ℂ} (hf : IsBoundedOnCell D K f) :
    IsBoundedOnCell D K (fun p => f p * a) := by
  have := boundedOnCell_const_mul D a hf
  simpa [mul_comm] using this

theorem boundedOnCell_sum {K : Fin D.mesh.count} {σ : Type*} (s : Finset σ) (f : σ → ℝ × ℝ → ℂ)
    (hf : ∀ i ∈ s, IsBoundedOnCell D K (f i)) : IsBoundedOnCell D K (fun p => ∑ i ∈ s, f i p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨aestronglyMeasurable_const, 0, fun p _ => ?_⟩
    simp
  | insert a s ha ih =>
    have h := boundedOnCell_add D (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using h

theorem boundedOnCell_tripleMatrix {K : Fin D.mesh.count} {S Gω : ℝ × ℝ → Fin 3 → Fin 3 → ℂ}
    (hS : ∀ a b, IsBoundedOnCell D K (fun p => S p a b)) (hG : ∀ a b, IsBoundedOnCell D K (fun p => Gω p a b))
    (i j : Fin 12) : IsBoundedOnCell D K (fun p => tripleMatrix (S p) (Gω p) i j) := by
  simp only [tripleMatrix, modelTriple_eq_coef]
  exact boundedOnCell_add D (boundedOnCell_sum D _ _ fun a _ => boundedOnCell_sum D _ _ fun b _ =>
    boundedOnCell_mul_const D _ (hS a b)) (boundedOnCell_sum D _ _ fun a _ => boundedOnCell_sum D _ _ fun b _ =>
    boundedOnCell_mul_const D _ (hG a b))

theorem cellPoly_eval_continuous (B : CellBox) (Q : CellPoly) : Continuous (fun p : ℝ × ℝ => Q.eval B p) := by
  unfold CellPoly.eval CellBox.refR CellBox.refZ
  fun_prop

theorem labelGrad_norm_le (hF : FrameFacts) (m : ℕ) (α : ℤ × ℤ) (F : ℝ → Space → (Space →L[ℝ] Space))
    (y : Space) (c : ℝ) (hc : ∀ τ φ, ‖F τ (axialRot φ y)‖ ≤ c) (ab : Fin 3 × Fin 3) :
    ‖modeGrad (labelHarmonic m α) F 0 y ab‖ ≤ c := by
  unfold modeGrad
  refine Coercive.Internal.MuSmooth.Decay.modeAverage_norm_le _ _ _ fun τ φ => ?_
  have h := rotMat_entry_le hF (F (0 + τ) (axialRot φ y)) φ ab.1 ab.2
  simp only [rotMat, Complex.norm_real, Real.norm_eq_abs] at h
  exact h.trans (hc _ φ)

theorem labelSecond_norm_le (m : ℕ) (α : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (y : Space) (c : ℝ)
    (hc : ∀ τ φ, ‖H τ (axialRot φ y)‖ ≤ c) (abc : Fin 3 × Fin 3 × Fin 3) :
    ‖modeSecondDeriv (labelHarmonic m α) H 0 y abc‖ ≤ c := by
  unfold modeSecondDeriv
  refine Coercive.Internal.MuSmooth.Decay.modeAverage_norm_le _ _ _ fun τ φ => ?_
  have h1 := PiLp.norm_apply_le (axialRot (-φ) (H (0 + τ) (axialRot φ y) (axialRot φ (unitVector abc.2.1))
    (axialRot φ (unitVector abc.2.2)))) abc.1
  rw [Coercive.Internal.MuSmooth.Decay.rot_norm] at h1
  have h2 := (H (0 + τ) (axialRot φ y)).le_opNorm₂ (axialRot φ (unitVector abc.2.1)) (axialRot φ (unitVector abc.2.2))
  rw [Coercive.Internal.MuSmooth.Decay.rot_norm, Coercive.Internal.MuSmooth.Decay.rot_norm, norm_unitVector,
    norm_unitVector, mul_one, mul_one] at h2
  rw [← Real.norm_eq_abs]
  exact h1.trans (h2.trans (hc _ φ))

theorem given_bounds {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {B : ℝ}
    (h : CoerciveWeak.IsWeakSecondDerivState W HW B) :
    0 ≤ B ∧ (∀ σ y, ‖gradField W σ y‖ ≤ B) ∧ ∀ σ y, ‖HW σ y‖ ≤ B := by
  have hB : 0 ≤ B := by
    have := (h.decay 0 0).1
    simp only [norm_zero, add_zero, div_one] at this
    exact (norm_nonneg _).trans this
  refine ⟨hB, fun σ y => ?_, fun σ y => ?_⟩
  · have h1 := (h.decay σ y).2.1
    have h2 : B / (1 + ‖y‖) ^ 2 ≤ B := div_le_self hB (one_le_pow₀ (by linarith [norm_nonneg y]))
    exact h1.trans h2
  · have h1 := (h.decay σ y).2.2
    have h2 : B / (1 + ‖y‖) ^ 3 ≤ B := div_le_self hB (one_le_pow₀ (by linarith [norm_nonneg y]))
    exact h1.trans h2

end Bounded

section EpsForms

theorem epsOwnCharge_eq {V : Type} (Q : PotentialData V) (U : Fin 12 → ℂ) :
    epsOwnCharge Q (velOf U) (gradOf U) = epsOwnForm Q.epsStrain Q.epsGrad Q.epsLength Q.length U := by
  unfold epsOwnCharge splitCharge epsOwnForm chargeForm
  ring

theorem epsPartnerCharge_eq {V : Type} (Q : PotentialData V) (U : Fin 12 → ℂ) :
    epsPartnerCharge Q (velOf U) (gradOf U) = epsPartnerForm Q.epsStrain Q.epsGrad Q.epsLength Q.length U := by
  unfold epsPartnerCharge splitCharge epsPartnerForm chargeForm
  ring

theorem longOwnCharge_eq {V : Type} (Q : PotentialData V) (ι : ℤ × ℤ) (U : Fin 12 → ℂ) :
    longOwnCharge Q ι (velOf U) (gradOf U) = (if |ι.1| ≤ (Q.longCut : ℤ) then Q.longBalance else 1 + 1 / Q.longBalance)
      * epsOwnForm Q.longStrain Q.longGrad Q.epsLength Q.length U := by
  unfold longOwnCharge longFactor splitCharge epsOwnForm chargeForm
  ring

theorem longPartnerCharge_eq {V : Type} (Q : PotentialData V) (ι : ℤ × ℤ) (U : Fin 12 → ℂ) :
    longPartnerCharge Q ι (velOf U) (gradOf U) = (if |ι.1| ≤ (Q.longCut : ℤ) then Q.longBalance else 1 + 1 / Q.longBalance)
      * epsPartnerForm Q.longStrain Q.longGrad Q.epsLength Q.length U := by
  unfold longPartnerCharge longFactor splitCharge epsPartnerForm chargeForm
  ring

end EpsForms

section PointAt

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus
open Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation Coercive.StretchInternal

theorem tripleMatrix_zero : tripleMatrix (fun _ _ => 0) (fun _ _ => 0) = 0 := by
  ext i j
  simp [tripleMatrix, modelTriple_eq_coef]

variable {k : ℕ} {C : Type} {nE nM : ℕ}

theorem point_model_stage (hT : TorusFacts) (hTL : TorusLongStatement) (hF : FrameFacts) {D : CellLayerData k C nE nM}
    {R : CellCalculusEntry D} {A : AssemblyEntry D R} {P : CouplingEntries D R}
    {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (hreg : AssemblyRegular D R) (K : Fin D.mesh.count) {p : ℝ × ℝ}
    (hp : p ∈ (D.mesh.box K).rect) (hpos : 0 < p.1) (hL : ∀ L, L ≠ K → p ∉ (D.mesh.box L).rect)
    (hvg : ∀ σ θ : ℝ, cylPoint p.1 θ p.2 ∈ ownSolid D.mesh.box K →
      ‖vorticityGradOf D.givenHess σ (cylPoint p.1 θ p.2)
        - D.model.vorticityGrad.field D.mesh.box D.azimuthOrder σ (cylPoint p.1 θ p.2)
        - (R.high K).vorticityGrad σ (cylPoint p.1 θ p.2) - (R.long K).vorticityGrad σ (cylPoint p.1 θ p.2)‖
        ≤ (D.modelErrors K).vorticityGrad)
    (hmS : ∀ τ φ a b, ((fibGrad (D.model.strain.field D.mesh.box D.azimuthOrder) (planePoint p) τ φ a b : ℝ) : ℂ)
      = ∑ α ∈ D.model.strain.labels K, labelPhase D.azimuthOrder α τ φ * D.model.strain.planeValue D.mesh.box K α a b p)
    (hmG : ∀ τ φ a b, ((fibGrad (D.model.vorticityGrad.field D.mesh.box D.azimuthOrder) (planePoint p) τ φ a b : ℝ) : ℂ)
      = ∑ α ∈ D.model.vorticityGrad.labels K,
          labelPhase D.azimuthOrder α τ φ * D.model.vorticityGrad.planeValue D.mesh.box K α a b p)
    (hsH : ∀ τ φ a b c, ((frameSecondDeriv D.givenHess (planePoint p) τ φ a b c : ℝ) : ℂ)
      = ∑ β ∈ D.givenLabels, phase β τ φ * modeSecondDeriv β D.givenHess 0 (planePoint p) (a, b, c))
    (hhS : ∀ a b, AEStronglyMeasurable (fun z : ℝ × ℝ => fibGrad (R.high K).strain (planePoint p) z.1 z.2 a b)
      boxMeasure)
    (hhG : ∀ a b, AEStronglyMeasurable (fun z : ℝ × ℝ => fibGrad (R.high K).vorticityGrad (planePoint p) z.1 z.2 a b)
      boxMeasure)
    (hlS : ∀ a b, AEStronglyMeasurable (fun z : ℝ × ℝ => fibGrad (R.long K).strain (planePoint p) z.1 z.2 a b)
      boxMeasure)
    (hlG : ∀ a b, AEStronglyMeasurable (fun z : ℝ × ℝ => fibGrad (R.long K).vorticityGrad (planePoint p) z.1 z.2 a b)
      boxMeasure)
    (Dd : Finset (ℤ × ℤ)) (hDR : Disjoint (D.mesh.resolved K) Dd) (hDB : Disjoint (D.mesh.band K) Dd)
    (X O Yl Tt B Dv : ℤ × ℤ → Fin 12 → ℂ) (hO : ∀ ι ∈ D.mesh.resolved K, O ι = Yl ι + Tt ι) :
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
            (X ι) (X ι' + (2 : ℂ) • Yl ι')).re := by
  classical
  set m := D.azimuthOrder with hm_def
  have hm : 1 ≤ m := hreg.field.azimuth_pos
  have hK : IsCellBox (D.mesh.box K) := hreg.field.mesh_valid.box_valid K
  set y := planePoint p with hy
  obtain ⟨Bst, hst⟩ := hreg.field.model_state
  have hexp := (hF.given_expansion D.givenLabels D.given D.givenHess Bst hreg.field.model_harmonics hst
    (D.mesh.box K) hK).1 y
  have hsplit := hP.cell_conditions.model_split K
  have hsolid : ∀ φ, axialRot φ y ∈ ownSolid D.mesh.box K := fun φ => orbit_mem_ownSolid D.mesh.box K hK p hp hpos hL φ
  have hcyl : ∀ φ, axialRot φ y = cylPoint p.1 φ p.2 := by
    intro φ
    ext i
    fin_cases i <;> simp [hy, axialRot, planePoint, cylPoint, unitVector] <;> ring
  have hvgy : ∀ σ φ, ‖vorticityGradOf D.givenHess σ (axialRot φ y)
      - D.model.vorticityGrad.field D.mesh.box m σ (axialRot φ y)
      - (R.high K).vorticityGrad σ (axialRot φ y) - (R.long K).vorticityGrad σ (axialRot φ y)‖
      ≤ (D.modelErrors K).vorticityGrad := by
    intro σ φ
    rw [hcyl φ]
    exact hvg σ φ (hcyl φ ▸ hsolid φ)
  set SW : ℝ → ℝ → Fin 3 → Fin 3 → ℂ := fun τ φ a b =>
    (((fibGrad (gradField D.given) y τ φ a b : ℝ) : ℂ) + ((fibGrad (gradField D.given) y τ φ b a : ℝ) : ℂ)) / 2
    with hSW
  set GW : ℝ → ℝ → Fin 3 → Fin 3 → ℂ := fun τ φ a b => ((curlGradReal (frameSecondDeriv D.givenHess y τ φ) a b : ℝ) : ℂ)
    with hGW
  set Sm : ℝ → ℝ → Fin 3 → Fin 3 → ℂ := fun τ φ a b =>
    ((fibGrad (D.model.strain.field D.mesh.box m) y τ φ a b : ℝ) : ℂ) with hSm
  set Gm : ℝ → ℝ → Fin 3 → Fin 3 → ℂ := fun τ φ a b =>
    ((fibGrad (D.model.vorticityGrad.field D.mesh.box m) y τ φ a b : ℝ) : ℂ) with hGm
  set Sh : ℝ → ℝ → Fin 3 → Fin 3 → ℂ := fun τ φ a b => ((fibGrad (R.high K).strain y τ φ a b : ℝ) : ℂ) with hSh
  set Gh : ℝ → ℝ → Fin 3 → Fin 3 → ℂ := fun τ φ a b => ((fibGrad (R.high K).vorticityGrad y τ φ a b : ℝ) : ℂ)
    with hGh
  set Sl : ℝ → ℝ → Fin 3 → Fin 3 → ℂ := fun τ φ a b => ((fibGrad (R.long K).strain y τ φ a b : ℝ) : ℂ) with hSl
  set Gl : ℝ → ℝ → Fin 3 → Fin 3 → ℂ := fun τ φ a b => ((fibGrad (R.long K).vorticityGrad y τ φ a b : ℝ) : ℂ)
    with hGl
  have eSW : ∀ a b, (fun τ φ => SW τ φ a b) = fun τ φ => ∑ β ∈ D.givenLabels, phase β τ φ *
      ((modeGrad β (gradField D.given) 0 y (a, b) + modeGrad β (gradField D.given) 0 y (b, a)) / 2) := by
    intro a b
    funext τ φ
    simp only [hSW, hexp τ φ a b, hexp τ φ b a, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  have eGW : ∀ a b, (fun τ φ => GW τ φ a b) = fun τ φ => ∑ β ∈ D.givenLabels, phase β τ φ *
      (∑ i : Fin 3, ∑ j : Fin 3, (alternatingSymbol a i j : ℂ) * modeSecondDeriv β D.givenHess 0 y (j, b, i)) := by
    intro a b
    funext τ φ
    simp only [hGW, curlGradReal]
    push_cast
    simp only [hsH, Finset.mul_sum]
    rw [Finset.sum_comm (s := D.givenLabels)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm (s := D.givenLabels)]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun β _ => ?_
    ring
  have eSm : ∀ a b, (fun τ φ => Sm τ φ a b) = fun τ φ => ∑ α ∈ D.model.strain.labels K,
      labelPhase m α τ φ * D.model.strain.planeValue D.mesh.box K α a b p := by
    intro a b
    funext τ φ
    exact hmS τ φ a b
  have eGm : ∀ a b, (fun τ φ => Gm τ φ a b) = fun τ φ => ∑ α ∈ D.model.vorticityGrad.labels K,
      labelPhase m α τ φ * D.model.vorticityGrad.planeValue D.mesh.box K α a b p := by
    intro a b
    funext τ φ
    exact hmG τ φ a b
  have iSW : ∀ a b, IsTorusIntegrable (fun τ φ => SW τ φ a b) := by
    intro a b
    rw [eSW]
    exact torusIntegrable_of_cont (continuous_finsetSum _ fun β _ => (continuous_phase β).mul continuous_const)
  have iGW : ∀ a b, IsTorusIntegrable (fun τ φ => GW τ φ a b) := by
    intro a b
    rw [eGW]
    exact torusIntegrable_of_cont (continuous_finsetSum _ fun β _ => (continuous_phase β).mul continuous_const)
  have iSm : ∀ a b, IsTorusIntegrable (fun τ φ => Sm τ φ a b) := by
    intro a b
    rw [eSm]
    exact torusIntegrable_of_cont (continuous_finsetSum _ fun β _ =>
      (labelPhase_continuous_pair m β).mul continuous_const)
  have iGm : ∀ a b, IsTorusIntegrable (fun τ φ => Gm τ φ a b) := by
    intro a b
    rw [eGm]
    exact torusIntegrable_of_cont (continuous_finsetSum _ fun β _ =>
      (labelPhase_continuous_pair m β).mul continuous_const)
  have iSh : ∀ a b, IsTorusIntegrable (fun τ φ => Sh τ φ a b) := by
    intro a b
    refine hT.bounded _ (Complex.continuous_ofReal.comp_aestronglyMeasurable (hhS a b))
      ⟨(D.modelErrors K).strainHigh, fun τ φ _ _ _ _ => ?_⟩
    show ‖((fibGrad (R.high K).strain y τ φ a b : ℝ) : ℂ)‖ ≤ _
    rw [fibGrad_eq_rotMat]
    exact (rotMat_entry_le hF _ φ a b).trans (hsplit.strain.high_bound τ _ (hsolid φ))
  have iGh : ∀ a b, IsTorusIntegrable (fun τ φ => Gh τ φ a b) := by
    intro a b
    refine hT.bounded _ (Complex.continuous_ofReal.comp_aestronglyMeasurable (hhG a b))
      ⟨(D.modelErrors K).vorticityGradHigh, fun τ φ _ _ _ _ => ?_⟩
    show ‖((fibGrad (R.high K).vorticityGrad y τ φ a b : ℝ) : ℂ)‖ ≤ _
    rw [fibGrad_eq_rotMat]
    exact (rotMat_entry_le hF _ φ a b).trans (hsplit.vorticityGrad.high_bound τ _ (hsolid φ))
  have iSl : ∀ a b, IsTorusIntegrable (fun τ φ => Sl τ φ a b) := by
    intro a b
    refine hT.bounded _ (Complex.continuous_ofReal.comp_aestronglyMeasurable (hlS a b))
      ⟨(R.long K).errStrain, fun τ φ _ _ _ _ => ?_⟩
    show ‖((fibGrad (R.long K).strain y τ φ a b : ℝ) : ℂ)‖ ≤ _
    rw [fibGrad_eq_rotMat]
    exact (rotMat_entry_le hF _ φ a b).trans (hsplit.strain.long_bound τ _ (hsolid φ))
  have iGl : ∀ a b, IsTorusIntegrable (fun τ φ => Gl τ φ a b) := by
    intro a b
    refine hT.bounded _ (Complex.continuous_ofReal.comp_aestronglyMeasurable (hlG a b))
      ⟨(R.long K).errVorticityGrad, fun τ φ _ _ _ _ => ?_⟩
    show ‖((fibGrad (R.long K).vorticityGrad y τ φ a b : ℝ) : ℂ)‖ ≤ _
    rw [fibGrad_eq_rotMat]
    exact (rotMat_entry_le hF _ φ a b).trans (hsplit.vorticityGrad.long_bound τ _ (hsolid φ))
  have hH : ∀ α, α ∈ (P.potential K).harmonicLabels ↔ labelHarmonic m α ∈ D.givenLabels := fun α => hP.labels_iff K α
  have hcW : ∀ α, torusCoef m (fun τ φ => tripleMatrix (SW τ φ) (GW τ φ)) α
      = truncCoupling D (P.potential K).harmonicLabels α p := by
    intro α
    rw [torusCoef_tripleMatrix hT m SW GW iSW iGW]
    have hS' : ∀ a b, torusMean (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * SW τ φ a b)
        = if α ∈ (P.potential K).harmonicLabels then (labelGrad m α (gradField D.given) p (a, b)
          + labelGrad m α (gradField D.given) p (b, a)) / 2 else 0 := by
      intro a b
      have e2 : (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * SW τ φ a b)
          = fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * ∑ β ∈ D.givenLabels, phase β τ φ *
            ((modeGrad β (gradField D.given) 0 y (a, b) + modeGrad β (gradField D.given) 0 y (b, a)) / 2) := by
        funext τ φ
        rw [show SW τ φ a b = (fun τ φ => SW τ φ a b) τ φ from rfl, eSW a b]
      rw [e2, torusMean_conj_phase_sum hT m α D.givenLabels]
      by_cases h : α ∈ (P.potential K).harmonicLabels
      · rw [if_pos ((hH α).1 h), if_pos h]
        rfl
      · rw [if_neg (fun h' => h ((hH α).2 h')), if_neg h]
    have hG' : ∀ a b, torusMean (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * GW τ φ a b)
        = if α ∈ (P.potential K).harmonicLabels then curlGradOfSecondDeriv (labelHess m α D.givenHess p) (a, b) else 0 := by
      intro a b
      have e2 : (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * GW τ φ a b)
          = fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * ∑ β ∈ D.givenLabels, phase β τ φ *
            (∑ i : Fin 3, ∑ j : Fin 3, (alternatingSymbol a i j : ℂ) * modeSecondDeriv β D.givenHess 0 y (j, b, i)) := by
        funext τ φ
        rw [show GW τ φ a b = (fun τ φ => GW τ φ a b) τ φ from rfl, eGW a b]
      rw [e2, torusMean_conj_phase_sum hT m α D.givenLabels]
      by_cases h : α ∈ (P.potential K).harmonicLabels
      · rw [if_pos ((hH α).1 h), if_pos h]
        rfl
      · rw [if_neg (fun h' => h ((hH α).2 h')), if_neg h]
    simp only [hS', hG']
    by_cases hα : α ∈ (P.potential K).harmonicLabels
    · simp only [hα, if_true, truncCoupling]
      rfl
    · simp only [hα, if_false, truncCoupling]
      exact tripleMatrix_zero
  have hcM : ∀ α, torusCoef m (fun τ φ => tripleMatrix (Sm τ φ) (Gm τ φ)) α = (P.potential K).couplingModel α p := by
    intro α
    rw [torusCoef_tripleMatrix hT m Sm Gm iSm iGm]
    have hS' : ∀ a b, torusMean (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * Sm τ φ a b)
        = D.model.strain.planeValue D.mesh.box K α a b p := by
      intro a b
      have e2 : (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * Sm τ φ a b)
          = fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * ∑ β ∈ D.model.strain.labels K,
            labelPhase m β τ φ * D.model.strain.planeValue D.mesh.box K β a b p := by
        funext τ φ
        rw [show Sm τ φ a b = (fun τ φ => Sm τ φ a b) τ φ from rfl, eSm a b]
      rw [e2, torusMean_conj_label_sum hT hm α]
      split_ifs with h
      · rfl
      · exact (hP.strain_off_labels K α h p hp a b).symm
    have hG' : ∀ a b, torusMean (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * Gm τ φ a b)
        = D.model.vorticityGrad.planeValue D.mesh.box K α a b p := by
      intro a b
      have e2 : (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * Gm τ φ a b)
          = fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * ∑ β ∈ D.model.vorticityGrad.labels K,
            labelPhase m β τ φ * D.model.vorticityGrad.planeValue D.mesh.box K β a b p := by
        funext τ φ
        rw [show Gm τ φ a b = (fun τ φ => Gm τ φ a b) τ φ from rfl, eGm a b]
      rw [e2, torusMean_conj_label_sum hT hm α]
      split_ifs with h
      · rfl
      · exact (hP.vorticity_grad_off_labels K α h p hp a b).symm
    simp only [hS', hG']
    exact (matrix_eq_tripleMatrix_of_sesq (hP.coupling_model K α p hp)).symm
  have hcH : ∀ α, torusCoef m (fun τ φ => tripleMatrix (Sh τ φ) (Gh τ φ)) α
      = tripleMatrix (fun a b => labelGrad m α (R.high K).strain p (a, b))
          (fun a b => labelGrad m α (R.high K).vorticityGrad p (a, b)) := by
    intro α
    rw [torusCoef_tripleMatrix hT m Sh Gh iSh iGh]
    simp only [hSh, hGh, torusMean_fibGrad]
    rfl
  have hcL : ∀ α, torusCoef m (fun τ φ => tripleMatrix (Sl τ φ) (Gl τ φ)) α
      = tripleMatrix (fun a b => labelGrad m α (R.long K).strain p (a, b))
          (fun a b => labelGrad m α (R.long K).vorticityGrad p (a, b)) := by
    intro α
    rw [torusCoef_tripleMatrix hT m Sl Gl iSl iGl]
    simp only [hSl, hGl, torusMean_fibGrad]
    rfl
  have hsupp : ∀ α : ℤ × ℤ, |α.1| ≤ 2 * ((P.potential K).longCut : ℤ) →
      torusCoef m (fun τ φ => tripleMatrix (Sl τ φ) (Gl τ φ)) α = 0 := by
    intro α hα
    have hcut := hP.long_cut K
    have hc : |α.1| ≤ 2 * ((R.long K).cut : ℤ) := hα.trans (by omega)
    obtain ⟨_, _, h3, h4⟩ := hsplit.long_modes α hc p
    have e1 : (fun a b => labelGrad m α (R.long K).strain p (a, b)) = fun _ _ => 0 := by
      funext a b
      exact h3 a b
    have e2 : (fun a b => labelGrad m α (R.long K).vorticityGrad p (a, b)) = fun _ _ => 0 := by
      funext a b
      exact h4 a b
    rw [hcL, e1, e2]
    exact tripleMatrix_zero
  have hdisj : Disjoint (D.mesh.resolved K) (D.mesh.band K) := hreg.field.mesh_valid.band_apart K
  have hnn := hsplit.errors_nonneg
  have heps := hP.eps_ge K
  have hhi := hP.high_ge K
  have hyp := hP.young_pos K
  have hℓ := hP.length_pos K
  have hLen := hP.eps_length_pos K
  have hlp := hP.long_pos K
  have hlge := hP.long_ge K
  have hen := hP.eps_nonneg K
  have eSWrot : ∀ τ φ, SW τ φ = rotMat (strainOf D.given τ (axialRot φ y)) φ := by
    intro τ φ
    funext a b
    simp only [hSW, strainOf, rotMat]
    rw [hF.strain]
    push_cast
    rfl
  have eGWrot : ∀ τ φ, GW τ φ = rotMat (vorticityGradOf D.givenHess τ (axialRot φ y)) φ := by
    intro τ φ
    funext j l
    simp only [hGW, rotMat, vorticityGradOf]
    rw [hF.vorticity_grad (D.givenHess τ (axialRot φ y)) (fun u w => hreg.field.hessian_symmetric τ _ u w) φ j l]
    rfl
  have hrest : ∀ τ φ : ℝ, 0 < τ → τ ≤ 1 → 0 < φ → φ ≤ 2 * Real.pi →
      IsSymOpBound (P.potential K).epsStrain (SW τ φ - Sm τ φ - Sh τ φ - Sl τ φ) ∧
        IsOpBound (P.potential K).epsGrad (GW τ φ - Gm τ φ - Gh τ φ - Gl τ φ) := by
    intro τ φ _ _ _ _
    have e1 : SW τ φ - Sm τ φ - Sh τ φ - Sl τ φ = rotMat (strainOf D.given τ (axialRot φ y)
        - D.model.strain.field D.mesh.box m τ (axialRot φ y) - (R.high K).strain τ (axialRot φ y)
        - (R.long K).strain τ (axialRot φ y)) φ := by
      rw [rotMat_sub, rotMat_sub, rotMat_sub, eSWrot]
      rfl
    have e2 : GW τ φ - Gm τ φ - Gh τ φ - Gl τ φ = rotMat (vorticityGradOf D.givenHess τ (axialRot φ y)
        - D.model.vorticityGrad.field D.mesh.box m τ (axialRot φ y) - (R.high K).vorticityGrad τ (axialRot φ y)
        - (R.long K).vorticityGrad τ (axialRot φ y)) φ := by
      rw [rotMat_sub, rotMat_sub, rotMat_sub, eGWrot]
      rfl
    rw [e1, e2]
    exact ⟨symOpBound_rotMat hF _ φ _ ((hsplit.strain.rest_bound τ _ (hsolid φ)).trans heps.1),
      opBound_rotMat hF _ φ _ ((hvgy τ φ).trans heps.2)⟩
  have hhigh : ∀ τ φ : ℝ, 0 < τ → τ ≤ 1 → 0 < φ → φ ≤ 2 * Real.pi →
      IsSymOpBound (P.potential K).highStrain (Sh τ φ) ∧ IsOpBound (P.potential K).highGrad (Gh τ φ) := by
    intro τ φ _ _ _ _
    exact ⟨symOpBound_rotMat hF _ φ _ ((hsplit.strain.high_bound τ _ (hsolid φ)).trans hhi.1),
      opBound_rotMat hF _ φ _ ((hsplit.vorticityGrad.high_bound τ _ (hsolid φ)).trans hhi.2)⟩
  have hlong : ∀ τ φ : ℝ, 0 < τ → τ ≤ 1 → 0 < φ → φ ≤ 2 * Real.pi →
      IsSymOpBound (P.potential K).longStrain (Sl τ φ) ∧ IsOpBound (P.potential K).longGrad (Gl τ φ) := by
    intro τ φ _ _ _ _
    exact ⟨symOpBound_rotMat hF _ φ _ ((hsplit.strain.long_bound τ _ (hsolid φ)).trans hlge.1),
      opBound_rotMat hF _ φ _ ((hsplit.vorticityGrad.long_bound τ _ (hsolid φ)).trans hlge.2)⟩
  have hbase := torus_core hT hTL hm hdisj hDR hDB SW GW Sm Gm Sh Gh Sl Gl iSW iGW iSm iGm iSh iGh iSl iGl hen.1 hen.2 hLen hℓ
    (hnn.2.2.2.2.2.2.1.trans hhi.1) (hnn.2.2.2.2.2.2.2.trans hhi.2) hyp.1 hyp.2.1 hyp.2.2 hlp.1 hlp.2.1 hlp.2.2
    hrest hhigh hlong hsupp X O Yl Tt B Dv hO
  simp only [hcW, hcM, hcH, pairSesq_eq_sesq12] at hbase
  have c0 : ∀ U, epsOwnForm (P.potential K).epsStrain (P.potential K).epsGrad (P.potential K).epsLength
      (P.potential K).length U = epsOwnCharge (P.potential K) (velOf U) (gradOf U) :=
    fun U => (epsOwnCharge_eq (P.potential K) U).symm
  have c1 : ∀ U, epsPartnerForm (P.potential K).epsStrain (P.potential K).epsGrad (P.potential K).epsLength
      (P.potential K).length U = epsPartnerCharge (P.potential K) (velOf U) (gradOf U) :=
    fun U => (epsPartnerCharge_eq (P.potential K) U).symm
  have c2 : ∀ U, ownForm (P.potential K).highStrain (P.potential K).highGrad (P.potential K).youngCurl
      (P.potential K).youngStrain (P.potential K).youngVel U = highOwnCharge (P.potential K) U :=
    fun U => (highOwnCharge_eq (P.potential K) U).symm
  have c3 : ∀ U, partnerForm (P.potential K).highStrain (P.potential K).highGrad (P.potential K).youngCurl
      (P.potential K).youngStrain (P.potential K).youngVel U = highPartnerCharge (P.potential K) U :=
    fun U => (highPartnerCharge_eq (P.potential K) U).symm
  have c4 : ∀ ι U, (if |ι.1| ≤ ((P.potential K).longCut : ℤ) then (P.potential K).longBalance
      else 1 + 1 / (P.potential K).longBalance) * epsOwnForm (P.potential K).longStrain (P.potential K).longGrad
        (P.potential K).epsLength (P.potential K).length U = longOwnCharge (P.potential K) ι (velOf U) (gradOf U) :=
    fun ι U => (longOwnCharge_eq (P.potential K) ι U).symm
  have c5 : ∀ ι U, (if |ι.1| ≤ ((P.potential K).longCut : ℤ) then (P.potential K).longBalance
      else 1 + 1 / (P.potential K).longBalance) * epsPartnerForm (P.potential K).longStrain (P.potential K).longGrad
        (P.potential K).epsLength (P.potential K).length U = longPartnerCharge (P.potential K) ι (velOf U) (gradOf U) :=
    fun ι U => (longPartnerCharge_eq (P.potential K) ι U).symm
  simp only [c0, c1, c2, c3, c4, c5] at hbase
  linarith [hbase]

end PointAt

end ModelPart

end Internal

end Assembly

end CertCell

end Breakdown
