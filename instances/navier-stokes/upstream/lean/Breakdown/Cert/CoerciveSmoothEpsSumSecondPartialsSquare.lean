import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.CoerciveModeDerivative
import Breakdown.Cert.CoerciveRotation
import Breakdown.Cert.CoerciveSmoothPieceEpsSumSecondPartialsSlice

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothEpsSumSecondPartialsSquare

open ModeDerivative.Internal

theorem memLp_modeAverage_dom {β : Type*} (ι : ℤ × ℤ) (b : β) (F : Space → ℝ → ℝ → β → ℝ)
    (hF : Continuous (fun q : Space × ℝ × ℝ => F q.1 q.2.1 q.2.2 b)) (g : ℝ → Space → ℝ)
    (hg : Continuous (fun z : ℝ × Space => g z.1 z.2)) (hgp : IsTimePeriodic g)
    (hg2 : periodLIntegral (fun s x => g s x ^ 2) < ⊤) (σ : ℝ)
    (hdom : ∀ y τ φ, |F y τ φ b| ≤ g (σ + τ) (axialRot φ y)) :
    MemLp (fun y => modeAverage ι (F y) b) 2 volume :=
  Internal.ModeSlice.memLp_modeAverage_dom ι b F hF g hg hgp hg2 σ hdom

theorem memLp_modeGrad_entry {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hG : Continuous (fun z : ℝ × Space => G z.1 z.2)) (hGp : IsTimePeriodic G)
    (hG2 : periodLIntegral (fun s x => ‖G s x‖ ^ 2) < ⊤) (ι : ℤ × ℤ) (σ : ℝ) (ij : Fin 3 × Fin 3) :
    MemLp (fun y => modeGrad ι G σ y ij) 2 volume := by
  refine memLp_modeAverage_dom ι ij
    (fun y τ φ ij => axialRot (-φ) (G (σ + τ) (axialRot φ y) (axialRot φ (unitVector ij.2))) ij.1) ?_
    (fun s x => ‖G s x‖) hG.norm (fun s x => by simp only [hGp s x]) hG2 σ ?_
  · have h1 : Continuous (fun q : Space × ℝ × ℝ => G (σ + q.2.1) (axialRot q.2.2 q.1)) :=
      hG.comp ((continuous_const.add continuous_snd.fst).prodMk
        (continuous_axialRot_comp continuous_snd.snd continuous_fst))
    have h2 : Continuous (fun q : Space × ℝ × ℝ => axialRot q.2.2 (unitVector ij.2)) :=
      continuous_axialRot_comp continuous_snd.snd continuous_const
    exact (PiLp.continuous_apply 2 _ ij.1).comp
      (continuous_axialRot_comp continuous_snd.snd.neg (h1.clm_apply h2))
  · intro y τ φ
    rw [← Real.norm_eq_abs]
    refine (PiLp.norm_apply_le _ _).trans ?_
    rw [norm_axialRot axialRotationHolds_proof]
    refine ((G _ _).le_opNorm _).trans ?_
    rw [norm_axialRot axialRotationHolds_proof, norm_unitVector_one, mul_one]

theorem memLp_modeSecondDeriv_entry {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hH : Continuous (fun z : ℝ × Space => H z.1 z.2)) (hHp : IsTimePeriodic H)
    (hH2 : periodLIntegral (fun s x => ‖H s x‖ ^ 2) < ⊤) (ι : ℤ × ℤ) (σ : ℝ)
    (ijl : Fin 3 × Fin 3 × Fin 3) :
    MemLp (fun y => modeSecondDeriv ι H σ y ijl) 2 volume := by
  refine memLp_modeAverage_dom ι ijl
    (fun y τ φ ijl => axialRot (-φ) (H (σ + τ) (axialRot φ y) (axialRot φ (unitVector ijl.2.1))
      (axialRot φ (unitVector ijl.2.2))) ijl.1) ?_
    (fun s x => ‖H s x‖) hH.norm (fun s x => by simp only [hHp s x]) hH2 σ ?_
  · have h1 : Continuous (fun q : Space × ℝ × ℝ => H (σ + q.2.1) (axialRot q.2.2 q.1)) :=
      hH.comp ((continuous_const.add continuous_snd.fst).prodMk
        (continuous_axialRot_comp continuous_snd.snd continuous_fst))
    have h2 : ∀ k : Fin 3, Continuous (fun q : Space × ℝ × ℝ => axialRot q.2.2 (unitVector k)) :=
      fun k => continuous_axialRot_comp continuous_snd.snd continuous_const
    exact (PiLp.continuous_apply 2 _ ijl.1).comp
      (continuous_axialRot_comp continuous_snd.snd.neg ((h1.clm_apply (h2 _)).clm_apply (h2 _)))
  · intro y τ φ
    rw [← Real.norm_eq_abs]
    refine (PiLp.norm_apply_le _ _).trans ?_
    rw [norm_axialRot axialRotationHolds_proof]
    refine ((H _ _).le_opNorm₂ _ _).trans ?_
    rw [norm_axialRot axialRotationHolds_proof, norm_axialRot axialRotationHolds_proof,
      norm_unitVector_one, norm_unitVector_one, mul_one, mul_one]

theorem contDiff_four {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    ContDiff ℝ 4 (fun z : ℝ × Space => v z.1 z.2) :=
  hv.smooth.of_le (by norm_cast)

theorem contDiff_grad {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    ContDiff ℝ 3 (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
  ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => v z.1 y) (g := fun z => z.2)
    ((contDiff_four hv).comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (n := 3) (by norm_num)

theorem contDiff_secondDeriv {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    ContDiff ℝ 2 (fun z : ℝ × Space => fderiv ℝ (fun x => fderiv ℝ (v z.1) x) z.2) :=
  ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => fderiv ℝ (v z.1) y) (g := fun z => z.2)
    ((contDiff_grad hv).comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (n := 2) (by norm_num)

def traceMap : (Space →L[ℝ] Space →L[ℝ] Space) →L[ℝ] Space :=
  ∑ j : Fin 3, (ContinuousLinearMap.apply ℝ Space (unitVector j)).comp
    (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector j))

theorem traceMap_apply (K : Space →L[ℝ] Space →L[ℝ] Space) : traceMap K = secondDerivTrace K := by
  simp [traceMap, secondDerivTrace]

theorem norm_traceMap_le : ‖traceMap‖ ≤ 3 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun K => ?_
  rw [traceMap_apply, secondDerivTrace]
  calc ‖∑ j : Fin 3, K (unitVector j) (unitVector j)‖ ≤ ∑ j : Fin 3, ‖K (unitVector j) (unitVector j)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, ‖K‖ := Finset.sum_le_sum fun j _ => by
        refine (K.le_opNorm₂ _ _).trans ?_
        rw [norm_unitVector_one, mul_one, mul_one]
    _ = 3 * ‖K‖ := by simp

theorem ssp_eq {v : ℝ → Space → Space} (s : ℝ) (x : Space) :
    -secondDerivTrace (secondDerivField v s x) = -traceMap (fderiv ℝ (fun x => fderiv ℝ (v s) x) x) := by
  rw [traceMap_apply]
  rfl

def sspAt (v : ℝ → Space → Space) (z : ℝ × Space) : Space := -secondDerivTrace (secondDerivField v z.1 z.2)

theorem contDiff_ssp {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) :
    ContDiff ℝ 2 (sspAt v) := by
  have e : sspAt v =
      fun z => -traceMap (fderiv ℝ (fun x => fderiv ℝ (v z.1) x) z.2) := by
    funext z
    exact ssp_eq z.1 z.2
  rw [e]
  exact (traceMap.contDiff.comp (contDiff_secondDeriv hv)).neg

theorem slice_grad {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (s : ℝ) :
    ContDiff ℝ 3 (fun x => fderiv ℝ (v s) x) :=
  (contDiff_grad hv).comp (contDiff_const.prodMk contDiff_id)

theorem periodLIntegral_lt_top_of_le {f g : ℝ → Space → ℝ} (c : ℝ) (hc : 0 ≤ c)
    (hfg : ∀ s x, f s x ≤ c * g s x) (hg : periodLIntegral g < ⊤) : periodLIntegral f < ⊤ := by
  refine lt_of_le_of_lt (?_ : periodLIntegral f ≤ ENNReal.ofReal c * periodLIntegral g) ?_
  · unfold periodLIntegral
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun s => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.ofReal_mul hc]
    exact ENNReal.ofReal_le_ofReal (hfg s x)
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg

theorem memLp_grad_entry {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ)
    (σ : ℝ) (ij : Fin 3 × Fin 3) : MemLp (fun y => modeGrad ι (gradField v) σ y ij) 2 volume := by
  refine memLp_modeGrad_entry (contDiff_grad hv).continuous (fun s x => ?_) ?_ ι σ ij
  · simp only [gradField]
    rw [show v (s + 1) = v s from funext (hv.periodic s)]
  · have e : (fun s x => ‖gradField v s x‖ ^ 2) = fun s x => ‖iteratedFDeriv ℝ 1 (v s) x‖ ^ 2 := by
      funext s x
      rw [norm_iteratedFDeriv_one]
      rfl
    rw [e]
    exact hv.derivatives_finite 1 le_rfl

theorem memLp_secondDeriv_entry {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ)
    (σ : ℝ) (ijl : Fin 3 × Fin 3 × Fin 3) : MemLp (fun y => modeSecondDeriv ι (secondDerivField v) σ y ijl) 2 volume := by
  refine memLp_modeSecondDeriv_entry (contDiff_secondDeriv hv).continuous (fun s x => ?_) ?_ ι σ ijl
  · simp only [secondDerivField]
    rw [show v (s + 1) = v s from funext (hv.periodic s)]
  · have e : (fun s x => ‖secondDerivField v s x‖ ^ 2) = fun s x => ‖iteratedFDeriv ℝ 2 (v s) x‖ ^ 2 := by
      funext s x
      show ‖fderiv ℝ (fderiv ℝ (v s)) x‖ ^ 2 = _
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    rw [e]
    exact hv.derivatives_finite 2 (by norm_num)

theorem memLp_sspGrad_entry {P : ℝ} {v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v) (ι : ℤ × ℤ)
    (σ : ℝ) (ij : Fin 3 × Fin 3) :
    MemLp (fun y => modeGrad ι (gradField (fun s x => -secondDerivTrace (secondDerivField v s x))) σ y ij) 2 volume := by
  have hcomp : ContDiff ℝ 2 (fun p : (ℝ × Space) × Space => sspAt v (p.1.1, p.2)) :=
    (contDiff_ssp hv).comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hc' : Continuous (fun z : ℝ × Space => fderiv ℝ (fun y => sspAt v (z.1, y)) z.2) :=
    (ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => sspAt v (z.1, y))
      (g := fun z => z.2) hcomp contDiff_snd (n := 0) (by norm_num)).continuous
  have hc : Continuous (fun z : ℝ × Space => gradField (fun s x => -secondDerivTrace (secondDerivField v s x)) z.1 z.2) :=
    hc'
  refine memLp_modeGrad_entry hc (fun s x => ?_) ?_ ι σ ij
  · simp only [gradField, secondDerivField]
    rw [show v (s + 1) = v s from funext (hv.periodic s)]
  · refine periodLIntegral_lt_top_of_le 9 (by norm_num) (fun s x => ?_) (hv.derivatives_finite 3 (by norm_num))
    have hd : DifferentiableAt ℝ (fun x => fderiv ℝ (fun x => fderiv ℝ (v s) x) x) x :=
      (((slice_grad hv s).fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)) x
    have e : (fun x => -secondDerivTrace (secondDerivField v s x)) =
        fun x => -traceMap (fderiv ℝ (fun x => fderiv ℝ (v s) x) x) := by
      funext x
      exact ssp_eq s x
    have hf : fderiv ℝ (fun x => -secondDerivTrace (secondDerivField v s x)) x =
        -(traceMap.comp (fderiv ℝ (fun x => fderiv ℝ (fun x => fderiv ℝ (v s) x) x) x)) := by
      rw [e]
      exact ((traceMap.hasFDerivAt.comp x hd.hasFDerivAt).neg).fderiv
    have hn : ‖fderiv ℝ (fun x => fderiv ℝ (fun x => fderiv ℝ (v s) x) x) x‖ = ‖iteratedFDeriv ℝ 3 (v s) x‖ := by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
    have hb : ‖gradField (fun s x => -secondDerivTrace (secondDerivField v s x)) s x‖ ≤ 3 * ‖iteratedFDeriv ℝ 3 (v s) x‖ := by
      show ‖fderiv ℝ (fun x => -secondDerivTrace (secondDerivField v s x)) x‖ ≤ _
      rw [hf, norm_neg, ← hn]
      exact (traceMap.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_right norm_traceMap_le (norm_nonneg _))
    have h0 := norm_nonneg (gradField (fun s x => -secondDerivTrace (secondDerivField v s x)) s x)
    nlinarith [hb, h0]

end Internal.SmoothEpsSumSecondPartialsSquare

end Coercive

end Breakdown
