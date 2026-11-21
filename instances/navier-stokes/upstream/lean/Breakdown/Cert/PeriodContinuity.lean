import Breakdown.Cert.Nodes
import Breakdown.Cert.WeakCompact
import Breakdown.Cert.HalfOrderGraphMem
import Breakdown.Cert.GradInvSpec

open scoped ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.PeriodContinuity

theorem gradPart_eq_zero {q : XBar} (h : gradPart q = 0) : q = 0 := by
  have z1 : gradPart (0 : XBar) = (0 : Freq.X) := map_zero gradPart
  have z2 : secondPart (0 : XBar) = (0 : HBar) := map_zero secondPart
  have h0 : Freq.IsHalfSspOf (gradPart (0 : XBar)) (secondPart (0 : XBar)) := halfSsp_of_xbar 0
  have h1 : Freq.IsHalfSspOf (gradPart (0 : XBar)) (secondPart q) :=
    (congrArg (fun x : Freq.X => Freq.IsHalfSspOf x (secondPart q)) (h.trans z1.symm)).mp
      (halfSsp_of_xbar q)
  have h2 : secondPart q = secondPart (0 : XBar) := halfSsp_unique _ _ _ h1 h0
  have hA : ‖gradPart q‖ = 0 := (congrArg norm h).trans norm_zero
  have hB : ‖secondPart q‖ = 0 := (congrArg norm (h2.trans z2)).trans norm_zero
  have h3 : ‖q‖ ^ 2 = 0 := by
    have e := norm_xbar_sq q
    rw [hA, hB] at e
    exact e.trans (by norm_num)
  exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h3)

theorem gradCLM_ae (u : XX) :
    ∀ᵐ t ∂(volume : Measure TimeCircle), (gradCLM u : TimeCircle → HBar) t = gradPart (u t) :=
  ContinuousLinearMap.coeFn_compLpL gradPart u

theorem secondCLM_ae (u : XX) :
    ∀ᵐ t ∂(volume : Measure TimeCircle), (secondCLM u : TimeCircle → HBar) t = secondPart (u t) :=
  ContinuousLinearMap.coeFn_compLpL secondPart u

theorem gradCLM_injective : Function.Injective gradCLM := by
  intro u u' huu
  apply Lp.ext
  filter_upwards [gradCLM_ae u, gradCLM_ae u'] with t ht ht'
  have he : (gradCLM u : TimeCircle → HBar) t = (gradCLM u' : TimeCircle → HBar) t :=
    congrArg (fun w : HH => (w : TimeCircle → HBar) t) huu
  have hg : gradPart (u t) = gradPart (u' t) := ht.symm.trans (he.trans ht')
  have hz : gradPart (u t - u' t) = 0 := (map_sub gradPart (u t) (u' t)).trans (sub_eq_zero.2 hg)
  exact sub_eq_zero.1 (gradPart_eq_zero hz)

theorem norm_sq_lp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : Lp (α := TimeCircle) E 2) : ‖g‖ ^ 2 = ∫ t, ‖(g : TimeCircle → E) t‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with t
  rw [real_inner_self_eq_norm_sq]

theorem integrable_norm_sq_lp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : Lp (α := TimeCircle) E 2) : Integrable (fun t => ‖(g : TimeCircle → E) t‖ ^ 2) :=
  (L2.integrable_inner g g).congr (Eventually.of_forall fun _ => real_inner_self_eq_norm_sq _)

theorem norm_sq_xx (u : XX) : ‖u‖ ^ 2 = ‖gradCLM u‖ ^ 2 + ‖secondCLM u‖ ^ 2 := by
  have hae : (fun t => ‖(u : TimeCircle → XBar) t‖ ^ 2) =ᵐ[volume]
      fun t => ‖(gradCLM u : TimeCircle → HBar) t‖ ^ 2 + ‖(secondCLM u : TimeCircle → HBar) t‖ ^ 2 := by
    filter_upwards [gradCLM_ae u, secondCLM_ae u] with t h1 h2
    exact (norm_xbar_sq _).trans (congrArg₂ (fun a b : HBar => ‖a‖ ^ 2 + ‖b‖ ^ 2) h1.symm h2.symm)
  calc ‖u‖ ^ 2 = ∫ t, ‖(u : TimeCircle → XBar) t‖ ^ 2 := norm_sq_lp u
    _ = ∫ t, (‖(gradCLM u : TimeCircle → HBar) t‖ ^ 2 + ‖(secondCLM u : TimeCircle → HBar) t‖ ^ 2) :=
      integral_congr_ae hae
    _ = (∫ t, ‖(gradCLM u : TimeCircle → HBar) t‖ ^ 2) + ∫ t, ‖(secondCLM u : TimeCircle → HBar) t‖ ^ 2 :=
      integral_add (integrable_norm_sq_lp _) (integrable_norm_sq_lp _)
    _ = ‖gradCLM u‖ ^ 2 + ‖secondCLM u‖ ^ 2 :=
      congrArg₂ (fun a b : ℝ => a + b) (norm_sq_lp (gradCLM u)).symm (norm_sq_lp (secondCLM u)).symm

theorem le_two_mul_of_sq {a b c d : ℝ} (hd : 0 ≤ d) (h1 : a ^ 2 = b ^ 2 + c ^ 2)
    (h2 : c ^ 2 + 1 / 4 * b ^ 2 ≤ d ^ 2) : a ≤ 2 * d := by
  have h3 : a ^ 2 ≤ (2 * d) ^ 2 := by nlinarith [sq_nonneg c]
  nlinarith

theorem freeInv_spec (h : FreeInvHolds) {P : ℝ} (hP : 0 < P) : FreeInvSpec P (freeInv P) := by
  have hex := (h P hP).1
  rw [freeInv, dif_pos hex]
  exact hex.choose_spec

theorem norm_freeInv_le (h : FreeInvHolds) {P : ℝ} (hP : 0 < P) (f : HH) :
    ‖freeInv P f‖ ≤ 2 * ‖f‖ :=
  le_two_mul_of_sq (norm_nonneg _) (norm_sq_xx (freeInv P f)) ((h P hP).2 f)

theorem coeFn_shift (a : ℝ) (w : HH) : ∀ᵐ t : TimeCircle,
    ((shiftLp a : HH →L[ℝ] HH) w : TimeCircle → HBar) t = (w : TimeCircle → HBar) (t + a) := by
  have hw : (shiftLp a : HH →L[ℝ] HH) w = Lp.compMeasurePreserving
      (fun t : TimeCircle => t + (a : TimeCircle)) (measurePreserving_add_right volume (a : TimeCircle)) w :=
    rfl
  rw [hw]
  exact Lp.coeFn_compMeasurePreserving _ _

theorem shift_neg_shift (a : ℝ) (w : HH) :
    (shiftLp a : HH →L[ℝ] HH) ((shiftLp (-a) : HH →L[ℝ] HH) w) = w := by
  apply Lp.ext
  filter_upwards [coeFn_shift a ((shiftLp (-a) : HH →L[ℝ] HH) w),
    (measurePreserving_add_right (volume : Measure TimeCircle) (a : TimeCircle)).quasiMeasurePreserving.ae
      (coeFn_shift (-a) w)] with t h1 h2
  have hc : t + (a : TimeCircle) + ((-a : ℝ) : TimeCircle) = t := by
    rw [AddCircle.coe_neg, add_neg_cancel_right]
  exact h1.trans (h2.trans (congrArg (w : TimeCircle → HBar) hc))

theorem inner_shift (a : ℝ) (w f : HH) :
    inner ℝ w ((shiftLp a : HH →L[ℝ] HH) f) = inner ℝ ((shiftLp (-a) : HH →L[ℝ] HH) w) f := by
  have hi := (Lp.compMeasurePreservingₗᵢ ℝ (fun t : TimeCircle => t + (a : TimeCircle))
    (measurePreserving_add_right (volume : Measure TimeCircle) (a : TimeCircle))).inner_map_map
      ((shiftLp (-a) : HH →L[ℝ] HH) w) f
  have hw : (Lp.compMeasurePreservingₗᵢ ℝ (fun t : TimeCircle => t + (a : TimeCircle))
      (measurePreserving_add_right (volume : Measure TimeCircle) (a : TimeCircle)))
        ((shiftLp (-a) : HH →L[ℝ] HH) w) = w := shift_neg_shift a w
  have hf : (Lp.compMeasurePreservingₗᵢ ℝ (fun t : TimeCircle => t + (a : TimeCircle))
      (measurePreserving_add_right (volume : Measure TimeCircle) (a : TimeCircle))) f =
        (shiftLp a : HH →L[ℝ] HH) f := rfl
  exact (congrArg₂ (fun v v' : HH => inner ℝ v v') hw.symm hf.symm).trans hi

theorem continuous_shift (w : HH) : Continuous fun a : ℝ => (shiftLp a : HH →L[ℝ] HH) w := by
  let F : C(ℝ × TimeCircle, TimeCircle) :=
    ⟨fun q => q.2 + ((q.1 : ℝ) : TimeCircle),
      continuous_snd.add ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_fst)⟩
  exact continuous_const.compMeasurePreservingLp (ContinuousMap.curry F).continuous
    (fun a => measurePreserving_add_right volume ((a : ℝ) : TimeCircle)) (by norm_num)

def propOp (τ : ℝ) : HH →L[ℝ] HH :=
  ContinuousLinearMap.compLpL 2 (volume : Measure TimeCircle) (slicePropagator τ)

theorem integrand_eq (P τ : ℝ) (f : HH) :
    propagatorIntegrand P f τ = propOp τ ((shiftLp (-(τ / P)) : HH →L[ℝ] HH) f) := rfl

theorem inner_integrand (P τ : ℝ) (f z : HH) :
    inner ℝ z (propagatorIntegrand P f τ) =
      inner ℝ ((shiftLp (-(-(τ / P))) : HH →L[ℝ] HH) (ContinuousLinearMap.adjoint (propOp τ) z)) f :=
  ((congrArg (inner ℝ z) (integrand_eq P τ f)).trans
    (ContinuousLinearMap.adjoint_inner_left (propOp τ) ((shiftLp (-(τ / P)) : HH →L[ℝ] HH) f) z).symm).trans
    (inner_shift (-(τ / P)) (ContinuousLinearMap.adjoint (propOp τ) z) f)

theorem tendsto_inner_strong_weak {W : ℕ → HH} {W₀ : HH} (hW : Tendsto W atTop (𝓝 W₀))
    (f : ℕ → HH) (f₀ : HH) (C : ℝ) (hC : ∀ n, ‖f n‖ ≤ C)
    (hw : ∀ y : HH, Tendsto (fun n => inner ℝ (f n) y) atTop (𝓝 (inner ℝ f₀ y))) :
    Tendsto (fun n => inner ℝ (W n) (f n)) atTop (𝓝 (inner ℝ W₀ f₀)) := by
  have h0' : Tendsto (fun n => ‖W n - W₀‖ * C) atTop (𝓝 (0 * C)) :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hW).mul_const C
  have h0 : Tendsto (fun n => ‖W n - W₀‖ * C) atTop (𝓝 0) :=
    (congrArg (fun x : ℝ => Tendsto (fun n => ‖W n - W₀‖ * C) atTop (𝓝 x)) (zero_mul C)).mp h0'
  have h1 : Tendsto (fun n => inner ℝ (W n - W₀) (f n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (norm_inner_le_norm (W n - W₀) (f n)).trans
      (mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _))) h0
  have h2' : Tendsto (fun n => inner ℝ W₀ (f n)) atTop (𝓝 (inner ℝ f₀ W₀)) :=
    (hw W₀).congr (fun n => real_inner_comm W₀ (f n))
  have h2 : Tendsto (fun n => inner ℝ W₀ (f n)) atTop (𝓝 (inner ℝ W₀ f₀)) :=
    (congrArg (fun x : ℝ => Tendsto (fun n => inner ℝ W₀ (f n)) atTop (𝓝 x))
      (real_inner_comm W₀ f₀)).mp h2'
  have h3 : Tendsto (fun n => inner ℝ (W n - W₀) (f n) + inner ℝ W₀ (f n)) atTop
      (𝓝 (0 + inner ℝ W₀ f₀)) := h1.add h2
  have h4 : Tendsto (fun n => inner ℝ (W n - W₀) (f n) + inner ℝ W₀ (f n)) atTop
      (𝓝 (inner ℝ W₀ f₀)) :=
    (congrArg (fun x : ℝ => Tendsto (fun n => inner ℝ (W n - W₀) (f n) + inner ℝ W₀ (f n)) atTop
      (𝓝 x)) (zero_add (inner ℝ W₀ f₀))).mp h3
  exact h4.congr (fun n => (congrArg (fun x : ℝ => x + inner ℝ W₀ (f n))
    (inner_sub_left (W n) W₀ (f n))).trans (sub_add_cancel _ _))

theorem inner_gradInv_eq (P : ℝ) (f z : HH) :
    inner ℝ z (gradInv P f) = ∫ τ in Set.Ioi (0 : ℝ), inner ℝ z (propagatorIntegrand P f τ) :=
  (congrArg (inner ℝ z) (gradInv_spec P f)).trans
    (integral_inner (integrable_propagatorIntegrand P f) z).symm

theorem norm_inner_integrand_le (P : ℝ) (f z : HH) (C : ℝ) (hC : ‖f‖ ≤ C) {τ : ℝ} (hτ : 0 < τ) :
    ‖inner ℝ z (propagatorIntegrand P f τ)‖ ≤ ‖z‖ * C * GradInv.Internal.kernel τ := by
  have hk := GradInv.Internal.norm_propagatorIntegrand_le P f hτ
  have hk0 : 0 ≤ GradInv.Internal.kernel τ := (GradInv.Internal.kernel_pos hτ).le
  have e1 : ‖propagatorIntegrand P f τ‖ ≤ GradInv.Internal.kernel τ * C :=
    hk.trans (mul_le_mul_of_nonneg_left hC hk0)
  have e2 : ‖inner ℝ z (propagatorIntegrand P f τ)‖ ≤ ‖z‖ * (GradInv.Internal.kernel τ * C) :=
    (norm_inner_le_norm z (propagatorIntegrand P f τ)).trans
      (mul_le_mul_of_nonneg_left e1 (norm_nonneg z))
  have e3 : ‖z‖ * (GradInv.Internal.kernel τ * C) = ‖z‖ * C * GradInv.Internal.kernel τ :=
    (congrArg (fun x : ℝ => ‖z‖ * x) (mul_comm (GradInv.Internal.kernel τ) C)).trans
      (mul_assoc ‖z‖ C (GradInv.Internal.kernel τ)).symm
  exact e2.trans_eq e3

theorem tendsto_inner_integrand (P : ℕ → ℝ) (P₀ : ℝ) (f : ℕ → HH) (f₀ : HH) (hP₀ : 0 < P₀)
    (hlim : Tendsto P atTop (𝓝 P₀)) (C : ℝ) (hC : ∀ n, ‖f n‖ ≤ C)
    (hw : ∀ y : HH, Tendsto (fun n => inner ℝ (f n) y) atTop (𝓝 (inner ℝ f₀ y))) (z : HH) (τ : ℝ) :
    Tendsto (fun n => inner ℝ z (propagatorIntegrand (P n) (f n) τ)) atTop
      (𝓝 (inner ℝ z (propagatorIntegrand P₀ f₀ τ))) := by
  have harg : Tendsto (fun n => -(-(τ / P n))) atTop (𝓝 (-(-(τ / P₀)))) :=
    ((tendsto_const_nhds.div hlim hP₀.ne').neg).neg
  have hW : Tendsto (fun n => (shiftLp (-(-(τ / P n))) : HH →L[ℝ] HH)
      (ContinuousLinearMap.adjoint (propOp τ) z)) atTop
      (𝓝 ((shiftLp (-(-(τ / P₀))) : HH →L[ℝ] HH) (ContinuousLinearMap.adjoint (propOp τ) z))) :=
    ((continuous_shift (ContinuousLinearMap.adjoint (propOp τ) z)).tendsto _).comp harg
  have hT := tendsto_inner_strong_weak hW f f₀ C hC hw
  have hT' : Tendsto (fun n => inner ℝ z (propagatorIntegrand (P n) (f n) τ)) atTop
      (𝓝 (inner ℝ ((shiftLp (-(-(τ / P₀))) : HH →L[ℝ] HH)
        (ContinuousLinearMap.adjoint (propOp τ) z)) f₀)) :=
    hT.congr (fun n => (inner_integrand (P n) τ (f n) z).symm)
  exact (congrArg (fun x : ℝ => Tendsto (fun n => inner ℝ z (propagatorIntegrand (P n) (f n) τ))
    atTop (𝓝 x)) (inner_integrand P₀ τ f₀ z)).mpr hT'

theorem tendsto_inner_gradInv (P : ℕ → ℝ) (P₀ : ℝ) (f : ℕ → HH) (f₀ : HH) (hP₀ : 0 < P₀)
    (hlim : Tendsto P atTop (𝓝 P₀)) (C : ℝ) (hC : ∀ n, ‖f n‖ ≤ C)
    (hw : ∀ y : HH, Tendsto (fun n => inner ℝ (f n) y) atTop (𝓝 (inner ℝ f₀ y))) (z : HH) :
    Tendsto (fun n => inner ℝ z (gradInv (P n) (f n))) atTop
      (𝓝 (inner ℝ z (gradInv P₀ f₀))) := by
  have hEq : (fun n => inner ℝ z (gradInv (P n) (f n))) =
      fun n => ∫ τ in Set.Ioi (0 : ℝ), inner ℝ z (propagatorIntegrand (P n) (f n) τ) :=
    funext fun n => inner_gradInv_eq (P n) (f n) z
  have hD : Tendsto (fun n => ∫ τ in Set.Ioi (0 : ℝ), inner ℝ z (propagatorIntegrand (P n) (f n) τ))
      atTop (𝓝 (∫ τ in Set.Ioi (0 : ℝ), inner ℝ z (propagatorIntegrand P₀ f₀ τ))) :=
    tendsto_integral_of_dominated_convergence (fun τ => ‖z‖ * C * GradInv.Internal.kernel τ)
      (fun n => ((integrable_propagatorIntegrand (P n) (f n)).const_inner z).aestronglyMeasurable)
      (GradInv.Internal.integrableOn_kernel.const_mul (‖z‖ * C))
      (fun n => (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun τ hτ =>
        norm_inner_integrand_le (P n) (f n) z C (hC n) hτ))
      (Eventually.of_forall fun τ => tendsto_inner_integrand P P₀ f f₀ hP₀ hlim C hC hw z τ)
  have h1 : Tendsto (fun n => inner ℝ z (gradInv (P n) (f n))) atTop
      (𝓝 (∫ τ in Set.Ioi (0 : ℝ), inner ℝ z (propagatorIntegrand P₀ f₀ τ))) :=
    (congrArg (fun g : ℕ → ℝ => Tendsto g atTop
      (𝓝 (∫ τ in Set.Ioi (0 : ℝ), inner ℝ z (propagatorIntegrand P₀ f₀ τ)))) hEq).mpr hD
  exact (congrArg (fun x : ℝ => Tendsto (fun n => inner ℝ z (gradInv (P n) (f n))) atTop (𝓝 x))
    (inner_gradInv_eq P₀ f₀ z)).mpr h1

theorem exists_subseq (h : FreeInvHolds)
    (P : ℕ → ℝ) (P₀ : ℝ) (f : ℕ → HH) (f₀ : HH) (hP₀ : 0 < P₀) (hPn : ∀ n, 0 < P n)
    (hlim : Tendsto P atTop (𝓝 P₀)) (C : ℝ) (hC : ∀ n, ‖f n‖ ≤ C)
    (hw : ∀ y : HH, Tendsto (fun n => inner ℝ (f n) y) atTop (𝓝 (inner ℝ f₀ y))) :
    ∃ φ : ℕ → ℕ, ∀ y : XX, Tendsto (fun n => inner ℝ (freeInv (P (φ n)) (f (φ n))) y) atTop
      (𝓝 (inner ℝ (freeInv P₀ f₀) y)) := by
  have hb : ∀ n, ‖freeInv (P n) (f n)‖ ≤ 2 * C := fun n =>
    (norm_freeInv_le h (hPn n) (f n)).trans (mul_le_mul_of_nonneg_left (hC n) zero_le_two)
  have hex := exists_weakly_convergent_subseq (fun n => freeInv (P n) (f n)) (2 * C) hb
  obtain ⟨φ, x, hspec⟩ := hex
  have hφ : StrictMono φ := hspec.1
  have hx : ∀ y : XX, Tendsto (fun n => inner ℝ (freeInv (P (φ n)) (f (φ n))) y) atTop
      (𝓝 (inner ℝ x y)) := hspec.2.2
  have hg : ∀ n, gradCLM (freeInv (P n) (f n)) = gradInv (P n) (f n) :=
    fun n => freeInv_spec h (hPn n) (f n)
  have hgx : gradCLM x = gradInv P₀ f₀ := by
    refine ext_inner_left ℝ fun z => ?_
    have e : ∀ w : XX, inner ℝ w (ContinuousLinearMap.adjoint gradCLM z) = inner ℝ z (gradCLM w) :=
      fun w => (ContinuousLinearMap.adjoint_inner_right gradCLM w z).trans
        (real_inner_comm z (gradCLM w))
    have hA1 : Tendsto (fun n => inner ℝ z (gradInv (P (φ n)) (f (φ n)))) atTop
        (𝓝 (inner ℝ x (ContinuousLinearMap.adjoint gradCLM z))) :=
      (hx (ContinuousLinearMap.adjoint gradCLM z)).congr
        (fun n => (e _).trans (congrArg (inner ℝ z) (hg (φ n))))
    have hA : Tendsto (fun n => inner ℝ z (gradInv (P (φ n)) (f (φ n)))) atTop
        (𝓝 (inner ℝ z (gradCLM x))) :=
      (congrArg (fun v : ℝ => Tendsto (fun n => inner ℝ z (gradInv (P (φ n)) (f (φ n)))) atTop
        (𝓝 v)) (e x)).mp hA1
    have hB : Tendsto (fun n => inner ℝ z (gradInv (P (φ n)) (f (φ n)))) atTop
        (𝓝 (inner ℝ z (gradInv P₀ f₀))) :=
      tendsto_inner_gradInv (fun n => P (φ n)) P₀ (fun n => f (φ n)) f₀ hP₀
        (hlim.comp hφ.tendsto_atTop) C (fun n => hC (φ n)) (fun y => (hw y).comp hφ.tendsto_atTop) z
    exact tendsto_nhds_unique hA hB
  have hxe : x = freeInv P₀ f₀ := gradCLM_injective (hgx.trans (freeInv_spec h hP₀ f₀).symm)
  exact ⟨φ, fun y => (congrArg (fun v : XX => Tendsto (fun n => inner ℝ (freeInv (P (φ n)) (f (φ n))) y)
    atTop (𝓝 (inner ℝ v y))) hxe).mp (hx y)⟩

end Internal.PeriodContinuity

open Internal.PeriodContinuity in
theorem periodContinuityHolds_of (h : FreeInvHolds) : PeriodContinuityHolds := by
  intro P P₀ f f₀ hP₀ hPn hlim hbd hw y
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hex := exists_subseq h (fun n => P (ns n)) P₀ (fun n => f (ns n)) f₀ hP₀ (fun n => hPn (ns n))
    (hlim.comp hns) hbd.choose (fun n => hbd.choose_spec (ns n)) (fun y => (hw y).comp hns)
  exact ⟨hex.choose, hex.choose_spec y⟩

end Breakdown.Cert
