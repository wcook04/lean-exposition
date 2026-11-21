import Breakdown.FracCert.DecayFixedPointParts
import Breakdown.FracCert.FarFieldPairingParts
import Breakdown.FracCert.DecayFarField
import Breakdown.FracCert.WeakRegular
import Breakdown.FracCert.WeakSymbolL1
import Breakdown.FracCert.WeakFieldSmooth
import Breakdown.FracCert.WeakNiceSim
import Breakdown.FracCert.MildNiceHeat
import Breakdown.FracCert.ResidualNice
import Breakdown.Frac.NNiceField
import Breakdown.Uniqueness.RegPhysAuxDeriv
import Breakdown.FracCert.DecayBase
import Breakdown.FracCert.KernelDecay
import Breakdown.FracCert.KernelRingCutoff
import Breakdown.FracCert.KernelPiece
import Breakdown.FracCert.KernelDyadicSum
import Breakdown.FracCert.FarFieldGradientFree
import Breakdown.FracCert.DecayFixedPointGradient

open MeasureTheory Set Real
open scoped ENNReal ContDiff FourierTransform SchwartzMap

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

namespace FarFieldPairingInternal

open DecayFarField.Internal

theorem field_continuous (U : X) (hM : HasAllMoments U) : Continuous (profileField U) := by
  have h0 := (symbolL1OfMoments U hM).1 0
  simp only [pow_zero, one_mul] at h0
  exact WeakRegularInternal.continuous_physField_of
    ((integrable_norm_iff (WeakRegularInternal.aesm_symbolX U)).1 h0)

theorem field_bounded (U : X) (hM : HasAllMoments U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖profileField U y‖ ≤ C := by
  have hw := WeakRegularInternal.moments_clean U (symbolL1OfMoments U hM).1
  obtain ⟨-, hb⟩ := fieldSmoothOfMoments _ hw (WeakRegularInternal.cleanSymbol_conjSym _)
  obtain ⟨C, hC⟩ := hb 0
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  have h := hC y
  rw [norm_iteratedFDeriv_zero, WeakRegularInternal.physField_clean] at h
  exact h.trans (le_max_left _ _)

theorem tensor_continuous {V : Space → Space} (hV : Continuous V) : Continuous (tensorSq V) := by
  unfold tensorSq
  refine continuous_pi fun j => continuous_pi fun k => ?_
  exact ((continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp hV)).mul
    ((continuous_apply k).comp ((PiLp.continuous_ofLp 2 _).comp hV))

theorem tensor_norm_le {V : Space → Space} {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, ‖V y‖ ≤ C) (y : Space) :
    ‖tensorSq V y‖ ≤ C * C := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC0 hC0)).2 fun j => ?_
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC0 hC0)).2 fun k => ?_
  rw [tensorSq, norm_mul]
  exact mul_le_mul ((PiLp.norm_apply_le _ _).trans (hC y)) ((PiLp.norm_apply_le _ _).trans (hC y))
    (norm_nonneg _) hC0

theorem nice_props {φ : Space → Space} (hφ : IsNiceField φ) : Integrable φ ∧ Continuous φ := by
  obtain ⟨m, hm, rfl⟩ := hφ
  have e : niceField m = physField m := rfl
  rw [e, WeakRegularInternal.physField_of_rapid (s := m) (hm.2.1.toSchwartzMap hm.1) rfl]
  exact ⟨(realVec : CSpace →L[ℝ] Space).integrable_comp (SchwartzMap.integrable _),
    realVec.continuous.comp (SchwartzMap.continuous _)⟩

theorem integrand_continuousOn (α a : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ)
    (hc : ContinuousOn (fun p : ℝ × Space => heatDivConv α p.1 F p.2) (Ioi 0 ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × Space => integrand α a F p.1 p.2) (Ioi 0 ×ˢ univ) := by
  have hcexp : ∀ r : ℝ, Continuous (fun τ : ℝ => Real.exp (-τ) ^ r) := fun r =>
    Continuous.rpow_const (by fun_prop) fun τ => Or.inl (Real.exp_pos _).ne'
  have hrs : Continuous (fun p : ℝ × Space => (axialRotation (a * p.1)).symm p.2) :=
    ((rot_symm_clm_cont a).comp continuous_fst).clm_apply continuous_snd
  have hin : ContinuousOn (fun p : ℝ × Space => heatDivConv α (1 - Real.exp (-p.1)) F
      (Real.exp (-p.1) ^ (1 / (2 * α)) • (axialRotation (a * p.1)).symm p.2)) (Ioi 0 ×ˢ univ) := by
    refine hc.comp (f := fun p : ℝ × Space => (1 - Real.exp (-p.1),
      Real.exp (-p.1) ^ (1 / (2 * α)) • (axialRotation (a * p.1)).symm p.2)) ?_ ?_
    · refine Continuous.continuousOn (Continuous.prodMk (by fun_prop) ?_)
      exact ((hcexp _).comp continuous_fst).smul hrs
    · intro p hp
      exact ⟨t_pos hp.1, mem_univ _⟩
  have e : (fun p : ℝ × Space => integrand α a F p.1 p.2) = fun p =>
      ((axialRotation (a * p.1) : Space ≃ₗᵢ[ℝ] Space) : Space →L[ℝ] Space)
        (Real.exp (-p.1) ^ (1 - 1 / (2 * α)) • heatDivConv α (1 - Real.exp (-p.1)) F
          (Real.exp (-p.1) ^ (1 / (2 * α)) • (axialRotation (a * p.1)).symm p.2)) := by
    funext p
    rfl
  rw [e]
  exact ((rot_clm_cont a).comp continuous_fst).continuousOn.clm_apply
    (((hcexp _).comp continuous_fst).continuousOn.smul hin)

theorem change_vars (α a τ : ℝ) (G φ : Space → Space) :
    ∫ y, inner ℝ (pushForward (axialRotation (a * τ)) (scaleField α (Real.exp (-τ)) G) y) (φ y) =
      ∫ x, inner ℝ (G x) (simAdj α a (Real.exp τ) φ x) := by
  set R := axialRotation (a * τ) with hRdef
  set s := Real.exp (-τ) ^ (1 / (2 * α)) with hsdef
  set d := Real.exp (-τ) ^ (1 - 1 / (2 * α)) with hddef
  have hs : 0 < s := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have e1 : ∫ y, inner ℝ (pushForward R (scaleField α (Real.exp (-τ)) G) y) (φ y) =
      ∫ x, inner ℝ (d • G (s • x)) (R.symm (φ (R x))) := by
    have h := (R.measurePreserving).integral_comp' (f := R.toMeasurableEquiv)
      (fun y => inner ℝ (pushForward R (scaleField α (Real.exp (-τ)) G) y) (φ y))
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [LinearIsometryEquiv.coe_toMeasurableEquiv, pushForward, scaleField,
      LinearIsometryEquiv.symm_apply_apply]
    conv_lhs => rw [← R.apply_symm_apply (φ (R x))]
    rw [R.inner_map_map]
  have e2 := Measure.integral_comp_smul (μ := (volume : Measure Space))
    (fun z => inner ℝ (d • G z) (R.symm (φ (R (s⁻¹ • z))))) s
  simp only [inv_smul_smul₀ hs.ne', finrank_euclideanSpace_fin] at e2
  rw [e1, e2, ← integral_smul]
  have hsi : s⁻¹ = Real.exp τ ^ (1 / (2 * α)) := by
    rw [hsdef, Real.exp_neg, Real.inv_rpow (Real.exp_pos _).le, inv_inv]
  have hscal : |(s ^ 3)⁻¹| * d = Real.exp τ ^ (4 * (1 / (2 * α)) - 1) := by
    rw [abs_of_pos (by positivity), hsdef, hddef, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_mul,
      ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hR' : axialRotation (-(a * Real.log (Real.exp τ))) = R.symm := by
    rw [Real.log_exp, hRdef, Breakdown.axialRotationSpec.2.2.2.1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [simAdj, pushForward, hR', LinearIsometryEquiv.symm_symm, smul_eq_mul]
  rw [real_inner_smul_left, R.map_smul, R.symm.map_smul, real_inner_smul_right, hsi, ← hscal]
  ring

end FarFieldPairingInternal

open FarFieldPairingInternal DecayFarField.Internal in
theorem farFieldPairing_of (hR : HeatDivRegularStatement) (hP : HeatDivPairingStatement) :
    FarFieldPairingStatement := by
  intro α h1 h2 a U hM φ hφ
  obtain ⟨hφi, hφc⟩ := nice_props hφ
  obtain ⟨C, hC⟩ := hR α h1 h2 0 0 le_rfl (by norm_num)
  obtain ⟨CV, hCV0, hCV⟩ := field_bounded U hM
  set F := tensorSq (profileField U) with hFdef
  have hFb := tensor_norm_le hCV0 hCV
  have hFc : ContDiff ℝ ((0 : ℕ) : ℕ∞) F := contDiff_zero.2 (tensor_continuous (field_continuous U hM))
  obtain ⟨-, hcont, hbd⟩ := hC F (CV * CV) (CV * CV) hFc
    (fun y => by rw [norm_iteratedFDeriv_zero]; exact hFb y)
    (fun y => by rw [Real.rpow_zero, one_mul]; exact hFb y)
  have hc0 : ContinuousOn (fun p : ℝ × Space => heatDivConv α p.1 F p.2) (Ioi 0 ×ˢ univ) := by
    have h := (continuousMultilinearCurryFin0 ℝ Space Space).continuous.comp_continuousOn (hcont 0 le_rfl)
    refine h.congr fun p _ => ?_
    simp [iteratedFDeriv_zero_apply]
  have hjoint := integrand_continuousOn α a F hc0
  set g := 1 / (2 * α) with hgdef
  have hg0 : 0 ≤ g := by rw [hgdef]; positivity
  have hg1 : g < 1 := by rw [hgdef, div_lt_one (by linarith)]; linarith
  set w : ℝ → ℝ := fun τ => Real.exp (-((1 - g) * τ)) * (1 - Real.exp (-τ)) ^ (-g) with hwdef
  have hw : IntegrableOn w (Ioi 0) := weight_integrable g (1 - g) hg0 hg1 (by linarith)
  set K := C * (CV * CV + CV * CV) with hKdef
  have hnorm : ∀ τ : ℝ, 0 < τ → ∀ y, ‖integrand α a F τ y‖ ≤ K * w τ := by
    intro τ hτ y
    have ht := t_pos hτ
    have ht1 : 1 - Real.exp (-τ) ≤ 1 := by linarith [Real.exp_pos (-τ)]
    have hb := hbd 0 le_rfl _ ht ht1 (Real.exp (-τ) ^ (1 / (2 * α)) • (axialRotation (a * τ)).symm y)
    rw [norm_iteratedFDeriv_zero] at hb
    have hd0 : 0 ≤ Real.exp (-τ) ^ (1 - 1 / (2 * α)) := Real.rpow_nonneg (Real.exp_pos _).le _
    have e : ‖integrand α a F τ y‖ = Real.exp (-τ) ^ (1 - 1 / (2 * α)) *
        ‖heatDivConv α (1 - Real.exp (-τ)) F (Real.exp (-τ) ^ (1 / (2 * α)) • (axialRotation (a * τ)).symm y)‖ := by
      simp only [integrand, pushForward, scaleField, LinearIsometryEquiv.norm_map, norm_smul,
        Real.norm_of_nonneg hd0]
    have ed : Real.exp (-τ) ^ (1 - 1 / (2 * α)) = Real.exp (-((1 - g) * τ)) := by
      rw [← Real.exp_mul, hgdef]; congr 1; ring
    rw [e]
    calc Real.exp (-τ) ^ (1 - 1 / (2 * α)) * ‖heatDivConv α (1 - Real.exp (-τ)) F
          (Real.exp (-τ) ^ (1 / (2 * α)) • (axialRotation (a * τ)).symm y)‖
        ≤ Real.exp (-τ) ^ (1 - 1 / (2 * α)) * (C * (1 - Real.exp (-τ)) ^ (-(1 / (2 * α))) * (CV * CV + CV * CV)) :=
          mul_le_mul_of_nonneg_left hb hd0
      _ = K * w τ := by rw [ed, hKdef, hwdef, hgdef]; ring
  have hτint : ∀ y, Integrable (fun τ => integrand α a F τ y) (volume.restrict (Ioi 0)) := by
    intro y
    refine Integrable.mono' (hw.const_mul K) ?_ ?_
    · have hcy : ContinuousOn (fun τ : ℝ => integrand α a F τ y) (Ioi 0) :=
        hjoint.comp (f := fun τ : ℝ => ((τ, y) : ℝ × Space))
          (Continuous.continuousOn (continuous_id.prodMk continuous_const)) fun τ hτ => ⟨hτ, mem_univ _⟩
      exact hcy.aestronglyMeasurable measurableSet_Ioi
    · exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun τ hτ => hnorm τ hτ y)
  have hm : (volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure Space) =
      ((volume : Measure ℝ).prod (volume : Measure Space)).restrict (Ioi 0 ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hint : Integrable (Function.uncurry fun τ y => inner ℝ (integrand α a F τ y) (φ y))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure Space)) := by
    have hprod : Integrable (fun p : ℝ × Space => K * w p.1 * ‖φ p.2‖)
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure Space)) :=
      (hw.const_mul K).mul_prod hφi.norm
    refine Integrable.mono' hprod ?_ ?_
    · rw [hm]
      have hco : ContinuousOn (fun p : ℝ × Space => inner ℝ (integrand α a F p.1 p.2) (φ p.2))
          (Ioi 0 ×ˢ univ) := hjoint.inner (hφc.comp continuous_snd).continuousOn
      exact hco.aestronglyMeasurable (measurableSet_Ioi.prod MeasurableSet.univ)
    · rw [hm]
      refine (ae_restrict_iff' (measurableSet_Ioi.prod MeasurableSet.univ)).2
        (Filter.Eventually.of_forall fun p hp => ?_)
      have h := hnorm p.1 hp.1 p.2
      calc ‖inner ℝ (integrand α a F p.1 p.2) (φ p.2)‖ ≤ ‖integrand α a F p.1 p.2‖ * ‖φ p.2‖ :=
            norm_inner_le_norm _ _
        _ ≤ K * w p.1 * ‖φ p.2‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
  have step1 : ∫ y, inner ℝ (farFieldOp α a F y) (φ y) =
      -∫ y, ∫ τ in Ioi (0 : ℝ), inner ℝ (integrand α a F τ y) (φ y) := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have e : farFieldOp α a F y = -∫ τ in Ioi (0 : ℝ), integrand α a F τ y := rfl
    simp only [e, inner_neg_left]
    congr 1
    rw [real_inner_comm, ← integral_inner (hτint y)]
    simp only [real_inner_comm]
  have step2 : ∫ y, ∫ τ in Ioi (0 : ℝ), inner ℝ (integrand α a F τ y) (φ y) =
      ∫ τ in Ioi (0 : ℝ), ∫ y, inner ℝ (integrand α a F τ y) (φ y) :=
    (integral_integral_swap hint).symm
  have step3 : ∫ τ in Ioi (0 : ℝ), ∫ y, inner ℝ (integrand α a F τ y) (φ y) =
      ∫ τ in Ioi (0 : ℝ), trilinear U U (heatField α (1 - Real.exp (-τ)) (simAdj α a (Real.exp τ) φ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
    have ht1 : 1 - Real.exp (-τ) < 1 := by linarith [Real.exp_pos (-τ)]
    exact (change_vars α a τ _ φ).trans (hP α h1 h2 U hM _ (t_pos hτ) ht1 _
      (niceSimAdjClosed α a (Real.exp τ) (by linarith) (Real.exp_pos τ) φ hφ))
  rw [step1, step2, step3]


namespace FarFieldPairingInternal

theorem coord_abs_le (w : Space) (k : Fin 3) : |w k| ≤ ‖w‖ := by
  have h := PiLp.norm_apply_le w k
  rwa [Real.norm_eq_abs] at h

theorem abs_mul_le' {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

theorem integrable_bdd {f g : Space → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ y, |f y| ≤ C)
    (hg : Integrable g) : Integrable (fun y => f y * g y) :=
  hg.bdd_mul hf.aestronglyMeasurable (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hC y)

theorem coord_continuous {f : Space → Space} (hf : Continuous f) (j : Fin 3) : Continuous (fun y => f y j) :=
  (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp hf)

theorem coord_hasFDerivAt {f : Space → Space} {x : Space} (hf : DifferentiableAt ℝ f x) (k : Fin 3) :
    HasFDerivAt (fun y => f y k) ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).comp (fderiv ℝ f x)) x :=
  (EuclideanSpace.proj k : Space →L[ℝ] ℝ).hasFDerivAt.comp x hf.hasFDerivAt

theorem coord_fderiv {f : Space → Space} {x : Space} (hf : DifferentiableAt ℝ f x) (k : Fin 3) (v : Space) :
    fderiv ℝ (fun y => f y k) x v = fderiv ℝ f x v k := by
  rw [(coord_hasFDerivAt hf k).fderiv]
  simp

theorem coord_integrable {S : Space → Space} (hS : Integrable S) (k : Fin 3) : Integrable (fun y => S y k) := by
  simpa using (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integrable_comp hS

theorem dcoord_integrable {S : Space → Space} (hS : Integrable (fderiv ℝ S)) (e : Space) (k : Fin 3) :
    Integrable (fun y => fderiv ℝ S y e k) := by
  simpa using ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).comp (ContinuousLinearMap.apply ℝ Space e)).integrable_comp hS

theorem parts_jk {V S : Space → Space} (hV : ContDiff ℝ ∞ V) (hS : ContDiff ℝ ∞ S) {C0 C1 : ℝ}
    (hVpos : ∀ y, ‖V y‖ ≤ C0) (hV1 : ∀ y, ‖fderiv ℝ V y‖ ≤ C1) (hSi : Integrable S)
    (hDSi : Integrable (fderiv ℝ S)) (j k : Fin 3) :
    Integrable (fun y => V y k * fderiv ℝ V y (unitVector j) j * S y k) ∧
    ∫ y, V y j * fderiv ℝ V y (unitVector j) k * S y k =
      -(∫ y, V y k * fderiv ℝ V y (unitVector j) j * S y k) -
        ∫ y, V y k * V y j * fderiv ℝ S y (unitVector j) k := by
  set e := unitVector j with he
  have hVd : Differentiable ℝ V := hV.differentiable (by simp)
  have hSd : Differentiable ℝ S := hS.differentiable (by simp)
  have hVc := hV.continuous
  have hDV : Continuous (fun y => fderiv ℝ V y e) := (hV.continuous_fderiv (by simp)).clm_apply continuous_const
  have b0 : ∀ i y, |V y i| ≤ C0 := fun i y => (coord_abs_le _ i).trans (hVpos y)
  have b1 : ∀ i y, |fderiv ℝ V y e i| ≤ C1 * ‖e‖ := fun i y =>
    (coord_abs_le _ i).trans ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hV1 y) (norm_nonneg _)))
  have iS := coord_integrable hSi k
  have iDS := dcoord_integrable hDSi e k
  have cV : ∀ i, Continuous (fun y => V y i) := fun i => coord_continuous hVc i
  have cD : ∀ i, Continuous (fun y => fderiv ℝ V y e i) := fun i => coord_continuous hDV i
  have iA : Integrable (fun y => V y k * fderiv ℝ V y e j * S y k) :=
    integrable_bdd ((cV k).mul (cD j)) (fun y => abs_mul_le' (b0 k y) (b1 j y)) iS
  have iB : Integrable (fun y => V y k * V y j * fderiv ℝ S y e k) :=
    integrable_bdd ((cV k).mul (cV j)) (fun y => abs_mul_le' (b0 k y) (b0 j y)) iDS
  refine ⟨iA, ?_⟩
  have hfd : ∀ x, fderiv ℝ (fun y => V y k) x e = fderiv ℝ V x e k := fun x => coord_fderiv (hVd x) k e
  have hgd : ∀ x, fderiv ℝ (fun y => V y j * S y k) x e =
      fderiv ℝ V x e j * S x k + V x j * fderiv ℝ S x e k := by
    intro x
    have hm : HasFDerivAt (fun y => V y j * S y k)
        (V x j • ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).comp (fderiv ℝ S x)) +
          S x k • ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp (fderiv ℝ V x))) x :=
      (coord_hasFDerivAt (hVd x) j).mul (coord_hasFDerivAt (hSd x) k)
    rw [hm.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply]
    simp
    ring
  have hf'g : Integrable (fun x => fderiv ℝ (fun y => V y k) x e * (V x j * S x k)) := by
    simp only [hfd]
    refine (integrable_bdd ((cD k).mul (cV j)) (fun y => abs_mul_le' (b1 k y) (b0 j y)) iS).congr
      (ae_of_all _ fun x => ?_)
    simp only [Pi.mul_apply]
    ring
  have hfg' : Integrable (fun x => V x k * fderiv ℝ (fun y => V y j * S y k) x e) := by
    simp only [hgd]
    refine (iA.add iB).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hfg : Integrable (fun x => V x k * (V x j * S x k)) := by
    refine (integrable_bdd ((cV k).mul (cV j)) (fun y => abs_mul_le' (b0 k y) (b0 j y)) iS).congr
      (ae_of_all _ fun x => ?_)
    simp only [Pi.mul_apply]
    ring
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure Space)) hf'g hfg' hfg
    (fun x _ => (coord_hasFDerivAt (hVd x) k).differentiableAt)
    (fun x _ => ((coord_hasFDerivAt (hVd x) j).differentiableAt).mul
      ((coord_hasFDerivAt (hSd x) k).differentiableAt))
  simp only [hfd, hgd] at h
  have eA : ∫ x, V x k * (fderiv ℝ V x e j * S x k + V x j * fderiv ℝ S x e k) =
      (∫ x, V x k * fderiv ℝ V x e j * S x k) + ∫ x, V x k * V x j * fderiv ℝ S x e k := by
    rw [← integral_add iA iB]
    congr 1
    funext x
    ring
  have eD : ∫ x, fderiv ℝ V x e k * (V x j * S x k) = ∫ x, V x j * fderiv ℝ V x e k * S x k := by
    congr 1
    funext x
    ring
  linarith

end FarFieldPairingInternal

open FarFieldPairingInternal in
theorem trilinearByParts : TrilinearByPartsStatement := by
  intro U hM ψ hψ
  have hwm := (symbolL1OfMoments U hM).1
  have hvel := (symbolL1OfMoments U hM).2
  have hphys := WeakRegularInternal.physField_clean U
  obtain ⟨hV, hBd⟩ := fieldSmoothOfMoments _ (WeakRegularInternal.moments_clean U hwm)
    (WeakRegularInternal.cleanSymbol_conjSym _)
  rw [hphys] at hV hBd
  have hdiv : ∀ y, divergenceAt (physField (symbolX U)) y = 0 := by
    intro y
    rw [← hphys]
    exact Breakdown.SmoothFlow.divergenceAt_physField (WeakRegularInternal.memLp_clean U hwm 1)
      (WeakRegularInternal.cleanSymbol_div _) y
  have hg : ∀ j : Fin 3, (fun y => fderiv ℝ (physField (symbolX U)) y (unitVector j)) =ᵐ[volume]
      (partialX j U : Space → Space) := fun j =>
    Cert.Internal.Convection.partialX_ae_of_weakGradient (ResidualNiceInternal.isWeakGradient_of hV) U
      hvel.symm j
  unfold profileField
  set V := physField (symbolX U) with hVdef
  obtain ⟨C0, hC0⟩ := hBd 0
  obtain ⟨C1, hC1⟩ := hBd 1
  have hVpos : ∀ y, ‖V y‖ ≤ C0 := fun y => by simpa only [norm_iteratedFDeriv_zero] using hC0 y
  have hV1 : ∀ y, ‖fderiv ℝ V y‖ ≤ C1 := fun y => by simpa only [norm_iteratedFDeriv_one] using hC1 y
  obtain ⟨m, hm, rfl⟩ := hψ
  rw [← FracInternal.NiceField.fieldS_coe hm]
  set S := FracInternal.NiceField.fieldS hm
  have hSs : ContDiff ℝ ∞ (S : Space → Space) := S.smooth ⊤
  have hSi : Integrable (S : Space → Space) := S.integrable
  have hDSi : Integrable (fderiv ℝ (S : Space → Space)) := by
    exact (SchwartzMap.fderivCLM ℝ Space Space S).integrable
  have P := fun j k => parts_jk hV hSs hVpos hV1 hSi hDSi j k
  have hVd : Continuous (fderiv ℝ V) := hV.continuous_fderiv (by simp)
  have iT : ∀ j k : Fin 3, Integrable (fun y => V y j * fderiv ℝ V y (unitVector j) k * S y k) := by
    intro j k
    exact integrable_bdd ((coord_continuous hV.continuous j).mul
      (coord_continuous (hVd.clm_apply continuous_const) k))
      (fun y => abs_mul_le' ((coord_abs_le _ j).trans (hVpos y))
        ((coord_abs_le _ k).trans ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hV1 y) (norm_nonneg _))))) (coord_integrable hSi k)
  have e1 : trilinear U U S =
      ∑ j : Fin 3, ∑ k : Fin 3, ∫ y, V y j * fderiv ℝ V y (unitVector j) k * S y k := by
    unfold trilinear
    have hae : (fun x => ∑ j : Fin 3, (velocity U : Space → Space) x j *
        inner ℝ ((partialX j U : Space → Space) x) (S x)) =ᵐ[volume]
        fun x => ∑ j : Fin 3, ∑ k : Fin 3, V x j * fderiv ℝ V x (unitVector j) k * S x k := by
      filter_upwards [hvel, ae_all_iff.2 hg] with y h1 h2
      rw [h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← show fderiv ℝ V y (unitVector j) = (partialX j U : Space → Space) y from h2 j]
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [integral_congr_ae hae, integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => iT j k]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact integral_finsetSum _ fun k _ => iT j k
  have hzero : ∀ k : Fin 3, ∑ j : Fin 3, ∫ y, V y k * fderiv ℝ V y (unitVector j) j * S y k = 0 := by
    intro k
    rw [← integral_finsetSum _ fun j _ => (P j k).1]
    have h0 : ∀ y, ∑ j : Fin 3, V y k * fderiv ℝ V y (unitVector j) j * S y k = 0 := by
      intro y
      have hd := hdiv y
      unfold divergenceAt at hd
      rw [← Finset.sum_mul, ← Finset.mul_sum, hd, mul_zero, zero_mul]
    simp only [h0, integral_zero]
  rw [e1]
  calc ∑ j : Fin 3, ∑ k : Fin 3, ∫ y, V y j * fderiv ℝ V y (unitVector j) k * S y k
      = ∑ j : Fin 3, ∑ k : Fin 3, (-(∫ y, V y k * fderiv ℝ V y (unitVector j) j * S y k) -
          ∫ y, V y k * V y j * fderiv ℝ S y (unitVector j) k) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => (P j k).2
    _ = -(∑ k : Fin 3, ∑ j : Fin 3, ∫ y, V y k * fderiv ℝ V y (unitVector j) j * S y k) -
          ∑ k : Fin 3, ∑ j : Fin 3, ∫ y, V y k * V y j * fderiv ℝ S y (unitVector j) k := by
        simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
        rw [Finset.sum_comm (f := fun j k => ∫ y, V y k * fderiv ℝ V y (unitVector j) j * S y k),
          Finset.sum_comm (f := fun j k => ∫ y, V y k * V y j * fderiv ℝ S y (unitVector j) k)]
    _ = -∑ j : Fin 3, ∑ k : Fin 3, ∫ z, tensorSq V z j k * partialField (⇑S) k z j := by
        simp only [hzero, Finset.sum_const_zero, neg_zero, zero_sub, tensorSq, partialField]

open FarFieldPairingInternal in
theorem heatDivPairing_of (hT : HeatDivTransposeStatement) (hB : TrilinearByPartsStatement) :
    HeatDivPairingStatement := by
  intro α h1 h2 U hM t ht0 ht1 χ hχ
  obtain ⟨CV, hCV0, hCV⟩ := field_bounded U hM
  rw [hT α h1 h2 t ht0 ht1 _ (tensor_continuous (field_continuous U hM))
    ⟨CV * CV, tensor_norm_le hCV0 hCV⟩ χ hχ, hB U hM _ (niceHeat α t h1 ht0.le χ hχ).1]

open FarFieldPairingInternal in
theorem heatDivTranspose_of (hk : KernelDecayStatement) (hK : KernelTransposeStatement) :
    HeatDivTransposeStatement := by
  intro α h1 h2 t ht0 ht1 F hF hBex χ hχ
  obtain ⟨B, hB⟩ := hBex
  obtain ⟨hχi, hχc⟩ := nice_props hχ
  have hα : 0 < α := by linarith
  have hKc : ∀ i j k, Continuous (fun x => (projDivKernel α t i j k x).re) := fun i j k =>
    Complex.continuous_re.comp ((hk α hα i j k).1 t ht0).continuous
  have hKi : ∀ i j k, Integrable (fun x => projDivKernel α t i j k x) := fun i j k =>
    FarFieldAddInternal.kernel_integrable hk hα ht0 i j k
  have hFb : ∀ z j k, ‖F z j k‖ ≤ B := fun z j k =>
    (norm_le_pi_norm (F z j) k).trans ((norm_le_pi_norm (F z) j).trans (hB z))
  have hFc : ∀ j k, Continuous (fun z => F z j k) := fun j k =>
    (continuous_apply k).comp ((continuous_apply j).comp hF)
  have H : ∀ i j k, Integrable (fun p : Space × Space =>
      (projDivKernel α t i j k (p.1 - p.2)).re * F p.2 j k * χ p.1 i)
      ((volume : Measure Space).prod (volume : Measure Space)) := by
    intro i j k
    have hconv := Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ)
      (μ := (volume : Measure Space)) (ν := (volume : Measure Space))
      hχi.norm ((hKi i j k).comp_sub_left 0).norm
    refine (hconv.swap.const_mul B).mono' ?_ (ae_of_all _ fun p => ?_)
    · exact ((((hKc i j k).comp (continuous_fst.sub continuous_snd)).mul
        ((hFc j k).comp continuous_snd)).mul
        ((coord_continuous hχc i).comp continuous_fst)).aestronglyMeasurable
    · simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap, ContinuousLinearMap.mul_apply',
        zero_sub, neg_sub]
      have a1 : ‖(projDivKernel α t i j k (p.1 - p.2)).re‖ ≤ ‖projDivKernel α t i j k (p.1 - p.2)‖ := by
        rw [Real.norm_eq_abs]
        exact Complex.abs_re_le_norm _
      have a3 : ‖χ p.1 i‖ ≤ ‖χ p.1‖ := PiLp.norm_apply_le _ _
      rw [norm_mul, norm_mul]
      calc ‖(projDivKernel α t i j k (p.1 - p.2)).re‖ * ‖F p.2 j k‖ * ‖χ p.1 i‖
          ≤ ‖projDivKernel α t i j k (p.1 - p.2)‖ * B * ‖χ p.1‖ :=
            mul_le_mul (mul_le_mul a1 (hFb _ _ _) (norm_nonneg _) (norm_nonneg _)) a3 (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (hFb p.2 j k)))
        _ = B * (‖χ p.1‖ * ‖projDivKernel α t i j k (p.1 - p.2)‖) := by ring
  have eT : ∀ i j k, (fun y => (∫ z, (projDivKernel α t i j k (y - z)).re * F z j k) * χ y i) =
      fun y => ∫ z, (projDivKernel α t i j k (y - z)).re * F z j k * χ y i := by
    intro i j k
    funext y
    rw [integral_mul_const]
  have iT : ∀ i j k, Integrable (fun y => (∫ z, (projDivKernel α t i j k (y - z)).re * F z j k) * χ y i) := by
    intro i j k
    rw [eT i j k]
    exact (H i j k).integral_prod_left
  have eS : ∀ i j k, ∫ y, (∫ z, (projDivKernel α t i j k (y - z)).re * F z j k) * χ y i =
      ∫ z, F z j k * ∫ y, (projDivKernel α t i j k (y - z)).re * χ y i := by
    intro i j k
    calc ∫ y, (∫ z, (projDivKernel α t i j k (y - z)).re * F z j k) * χ y i
        = ∫ y, ∫ z, (projDivKernel α t i j k (y - z)).re * F z j k * χ y i := by
          rw [eT i j k]
      _ = ∫ z, ∫ y, (projDivKernel α t i j k (y - z)).re * F z j k * χ y i :=
          integral_integral_swap (H i j k)
      _ = ∫ z, F z j k * ∫ y, (projDivKernel α t i j k (y - z)).re * χ y i := by
          congr 1
          funext z
          rw [← integral_const_mul]
          congr 1
          funext y
          ring
  have iS : ∀ i j k, Integrable (fun z => F z j k * ∫ y, (projDivKernel α t i j k (y - z)).re * χ y i) := by
    intro i j k
    refine (H i j k).integral_prod_right.congr (ae_of_all _ fun z => ?_)
    dsimp only
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  have hL : ∀ y, inner ℝ (heatDivConv α t F y) (χ y) = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      (∫ z, (projDivKernel α t i j k (y - z)).re * F z j k) * χ y i := by
    intro y
    simp [heatDivConv, PiLp.inner_apply, Finset.mul_sum, mul_comm]
  calc ∫ y, inner ℝ (heatDivConv α t F y) (χ y)
      = ∫ y, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          (∫ z, (projDivKernel α t i j k (y - z)).re * F z j k) * χ y i := by
        congr 1
        funext y
        exact hL y
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          ∫ y, (∫ z, (projDivKernel α t i j k (y - z)).re * F z j k) * χ y i := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
          integrable_finsetSum _ fun k _ => iT i j k]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => iT i j k]
        exact Finset.sum_congr rfl fun j _ => integral_finsetSum _ fun k _ => iT i j k
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          ∫ z, F z j k * ∫ y, (projDivKernel α t i j k (y - z)).re * χ y i := by
        simp only [eS]
    _ = ∑ j : Fin 3, ∑ k : Fin 3, ∑ i : Fin 3,
          ∫ z, F z j k * ∫ y, (projDivKernel α t i j k (y - z)).re * χ y i := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j : Fin 3, ∑ k : Fin 3, ∫ z, -(F z j k * partialField (heatField α t χ) k z j) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        rw [← integral_finsetSum _ fun i _ => iS i j k]
        congr 1
        funext z
        rw [← Finset.mul_sum, hK α h1 h2 t ht0 ht1 χ hχ j k z, mul_neg]
    _ = -∑ j : Fin 3, ∑ k : Fin 3, ∫ z, F z j k * partialField (heatField α t χ) k z j := by
        simp only [integral_neg, Finset.sum_neg_distrib]

theorem farFieldPairing_of_transpose (hR : HeatDivRegularStatement) (hT : HeatDivTransposeStatement) :
    FarFieldPairingStatement :=
  farFieldPairing_of hR (heatDivPairing_of hT trilinearByParts)

theorem farFieldPairing_of_kernel (hR : HeatDivRegularStatement) (hK : KernelTransposeStatement) :
    FarFieldPairingStatement :=
  farFieldPairing_of_transpose hR (heatDivTranspose_of (kernelDecay_of ringCutoff pieceKernel dyadicSum) hK)

namespace FarFieldPairingInternal

theorem coord_inverseTransform {f : Space → CSpace} (hf : Integrable f) (w : Space) (i : Fin 3) :
    (𝓕⁻ f w) i = 𝓕⁻ (fun ξ => f ξ i) w := by
  have hi : Integrable (fun v : Space => Complex.exp (↑(2 * π * inner ℝ v w) * Complex.I) • f v) :=
    hf.bdd_smul 1 ((by fun_prop : Continuous fun v : Space =>
      Complex.exp (↑(2 * π * inner ℝ v w) * Complex.I)).aestronglyMeasurable)
      (ae_of_all _ fun v => by rw [Complex.norm_exp_ofReal_mul_I])
  rw [Real.fourierInv_eq', Real.fourierInv_eq']
  have h := (EuclideanSpace.proj i : CSpace →L[ℂ] ℂ).integral_comp_comm hi
  calc (∫ v, Complex.exp (↑(2 * π * inner ℝ v w) * Complex.I) • f v) i
      = (EuclideanSpace.proj i : CSpace →L[ℂ] ℂ)
          (∫ v, Complex.exp (↑(2 * π * inner ℝ v w) * Complex.I) • f v) := rfl
    _ = ∫ v, (EuclideanSpace.proj i : CSpace →L[ℂ] ℂ)
          (Complex.exp (↑(2 * π * inner ℝ v w) * Complex.I) • f v) := h.symm
    _ = ∫ v, Complex.exp (↑(2 * π * inner ℝ v w) * Complex.I) • f v i := by simp

theorem realVec_coord (w : CSpace) (i : Fin 3) : realVec w i = (w i).re := rfl

end FarFieldPairingInternal

open FarFieldPairingInternal in
theorem kernelTranspose : KernelTransposeStatement := by
  intro α h1 h2 t ht0 ht1 χ hχ j k z
  have hk : KernelDecayStatement := kernelDecay_of ringCutoff pieceKernel dyadicSum
  have hα : 0 < α := by linarith
  obtain ⟨n, hn, rfl⟩ := hχ
  have hni : Integrable n := hn.1.continuous.integrable_of_hasCompactSupport hn.2.1
  have hQi : ∀ i : Fin 3, Integrable (fun ξ => n ξ i) := fun i => by
    simpa using (EuclideanSpace.proj i : CSpace →L[ℂ] ℂ).integrable_comp hni
  obtain ⟨r, hr, h0⟩ := hn.2.2.1
  have hstep : ∀ i : Fin 3,
      Integrable (fun ξ => n ξ i * (Complex.exp ((2 * π * inner ℝ ξ z : ℝ) * Complex.I) *
        projDivSymbol α t i j k (-ξ))) ∧
      ∫ x, projDivKernel α t i j k (x - z) * 𝓕⁻ (fun ξ => n ξ i) x =
        ∫ ξ, n ξ i * (Complex.exp ((2 * π * inner ℝ ξ z : ℝ) * Complex.I) *
          projDivSymbol α t i j k (-ξ)) := by
    intro i
    have hQc : Continuous (fun ξ => n ξ i) := (continuous_apply i).comp ((PiLp.continuous_ofLp 2 _).comp hn.1.continuous)
    have hQs : HasCompactSupport (fun ξ => n ξ i) := hn.2.1.comp_left (g := fun v : CSpace => v i) rfl
    have hQ0 : (fun ξ => n ξ i) 0 = 0 := by
      simp only
      rw [h0 0 (by simpa using hr)]
      rfl
    have h := FarFieldGradientFreeInternal.kernel_pairing_step hk α t hα ht0 i j k z 1 one_pos
      (LinearIsometryEquiv.refl ℝ Space) _ hQc hQs hQ0
    have hs : ∀ ξ, (LinearIsometryEquiv.refl ℝ Space).symm ξ = ξ := fun ξ => rfl
    have hr' : ∀ x, (LinearIsometryEquiv.refl ℝ Space) x = x := fun x => rfl
    simp only [one_smul, hs, hr'] at h
    exact h
  have hL : ∀ i : Fin 3, ∫ y, (projDivKernel α t i j k (y - z)).re * niceField n y i =
      (∫ ξ, n ξ i * (Complex.exp ((2 * π * inner ℝ ξ z : ℝ) * Complex.I) *
        projDivSymbol α t i j k (-ξ))).re := by
    intro i
    rw [← (hstep i).2]
    have him : ∀ x, (projDivKernel α t i j k x).im = 0 := fun x =>
      ((kernelScaling_of hk) α hα i j k t ht0).2.1 x
    have hint : Integrable (fun y => projDivKernel α t i j k (y - z) * 𝓕⁻ (fun ξ => n ξ i) y) :=
      ((FarFieldAddInternal.kernel_integrable hk hα ht0 i j k).comp_sub_right z).mul_bdd
        (c := ∫ ξ, ‖n ξ i‖) (DecayGradientInternal.continuous_inverseTransform_of (hQi i)).aestronglyMeasurable
        (ae_of_all _ fun y => DecayGradientInternal.norm_inverseTransform_le_of _ y)
    refine Eq.trans ?_ (integral_re hint)
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [RCLike.re_to_complex]
    rw [Complex.mul_re, him, zero_mul, sub_zero, niceField, realVec_coord, coord_inverseTransform hni]
  simp only [hL]
  rw [← Complex.re_sum, ← integral_finsetSum _ fun i _ => (hstep i).1]
  rw [MildNiceHeatInternal.heatField_niceField α t hn]
  have hp := MildNiceHeatInternal.isNiceSymbol_heat α t hn
  set p := fun ξ => MildNiceHeatInternal.heatSym α t ξ • n ξ with hpdef
  set Ac : 𝓢(Space, CSpace) := 𝓕⁻ (FracInternal.NiceField.symbolS hp) with hAc
  have eN : niceField p = fun x => realVec (Ac x) := by
    funext x
    rw [hAc, SchwartzMap.fourierInv_coe]
    rfl
  set D : 𝓢(Space, CSpace) := LineDeriv.lineDerivOp (unitVector k) Ac with hD
  have eP : partialField (niceField p) k z j = (realVec (D z)) j := by
    rw [eN]
    have h := Freq.Internal.NiceApprox.pd_clm realVec Ac.differentiable (unitVector k)
    exact congrArg (fun f => f z j) h
  have hFD : ∀ ξ, 𝓕 (⇑D) ξ = (2 * π * Complex.I) • ((ξ k : ℝ) • p ξ) := by
    intro ξ
    rw [hD, ← SchwartzMap.fourier_coe, Freq.Internal.NiceApprox.freqTr_lineDeriv_apply, hAc,
      FourierTransform.fourier_fourierInv_eq]
    rfl
  have hDi : Integrable (𝓕 (⇑D)) := by
    rw [← SchwartzMap.fourier_coe]
    exact (𝓕 D).integrable
  have eDz : D z = 𝓕⁻ (𝓕 (⇑D)) z := by
    have hinv : (𝓕⁻ (𝓕 D : 𝓢(Space, CSpace)) : 𝓢(Space, CSpace)) = D := FourierTransform.fourierInv_fourier_eq D
    have h := congrArg (fun g : 𝓢(Space, CSpace) => g z) hinv
    simp only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] at h
    exact h.symm
  rw [eP, realVec_coord, eDz, coord_inverseTransform hDi, Real.fourierInv_eq', ← Complex.neg_re, ← integral_neg]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  simp only [hFD]
  have hd := hn.2.2.2.2 ξ
  rw [Fin.sum_univ_three] at hd
  simp only [hpdef, PiLp.smul_apply, smul_eq_mul, Complex.real_smul, projDivSymbol,
    MildNiceHeatInternal.heatSym, Fin.sum_univ_three, PiLp.neg_apply, norm_neg]
  generalize Complex.exp (↑(2 * π * inner ℝ ξ z) * Complex.I) = E
  generalize Real.exp (-(t * (2 * π * ‖ξ‖) ^ (2 * α))) = e
  fin_cases j <;> simp <;> push_cast <;> [linear_combination (E * (2 * (π : ℂ) * ((ξ k : ℝ) : ℂ) * Complex.I * (e : ℂ)) * ((ξ 0 : ℝ) : ℂ) / ((‖ξ‖ : ℝ) : ℂ) ^ 2) * hd; linear_combination (E * (2 * (π : ℂ) * ((ξ k : ℝ) : ℂ) * Complex.I * (e : ℂ)) * ((ξ 1 : ℝ) : ℂ) / ((‖ξ‖ : ℝ) : ℂ) ^ 2) * hd; linear_combination (E * (2 * (π : ℂ) * ((ξ k : ℝ) : ℂ) * Complex.I * (e : ℂ)) * ((ξ 2 : ℝ) : ℂ) / ((‖ξ‖ : ℝ) : ℂ) ^ 2) * hd]


theorem farFieldPairing_of_regular (hR : HeatDivRegularStatement) : FarFieldPairingStatement :=
  farFieldPairing_of_kernel hR kernelTranspose

end Breakdown.FracCert
