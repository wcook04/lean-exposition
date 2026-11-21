import TorusEuler.ReferenceComparison
import TorusEuler.FlowSecondVariation
import TorusEuler.LinearODEParameterDependence
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Weighted Duhamel estimates for the fixed transverse coordinates of §5.4. -/

open Set MeasureTheory
open scoped NNReal

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private noncomputable def weightedGenerator (A : E →L[ℝ] E) (g dg : ℝ) : E →L[ℝ] E :=
  A - (dg / g) • ContinuousLinearMap.id ℝ E

private theorem continuousOn_weightedGenerator {A : ℝ → E →L[ℝ] E} {g dg : ℝ → ℝ}
    {I : Set ℝ} (hA : ContinuousOn A I) (hg : ContinuousOn g I) (hdg : ContinuousOn dg I)
    (hg₀ : ∀ t ∈ I, 0 < g t) :
    ContinuousOn (fun t => weightedGenerator (A t) (g t) (dg t)) I :=
  hA.sub ((hdg.div hg fun t ht => (hg₀ t ht).ne').smul continuousOn_const)

private theorem hasDerivWithinAt_weighted {A : E →L[ℝ] E} {g : ℝ → ℝ} {dg : ℝ}
    {x : ℝ → E} {f : E} {I : Set ℝ} {t : ℝ} (hg₀ : 0 < g t)
    (hg : HasDerivWithinAt g dg I t) (hx : HasDerivWithinAt x (A (x t) + f) I t) :
    HasDerivWithinAt (fun u => (g u)⁻¹ • x u)
      (weightedGenerator A (g t) dg ((g t)⁻¹ • x t) + (g t)⁻¹ • f) I t := by
  refine ((hg.inv hg₀.ne').smul hx).congr_deriv ?_
  change (g t)⁻¹ • (A (x t) + f) + (-dg / g t ^ 2) • x t =
    (A - (dg / g t) • ContinuousLinearMap.id ℝ E) ((g t)⁻¹ • x t) + (g t)⁻¹ • f
  have heq : -dg / g t ^ 2 = -(dg / g t * (g t)⁻¹) := by field_simp
  calc
    _ = (g t)⁻¹ • A (x t) + (g t)⁻¹ • f - (dg / g t * (g t)⁻¹) • x t := by
      rw [smul_add, heq, neg_smul, sub_eq_add_neg]
    _ = _ := by
      rw [sub_apply, smul_apply, ContinuousLinearMap.id_apply, map_smul, smul_smul]
      abel

private theorem hasDerivWithinAt_unweighted {A : E →L[ℝ] E} {g : ℝ → ℝ} {dg : ℝ}
    {y : ℝ → E} {I : Set ℝ} {t : ℝ} (hg₀ : 0 < g t)
    (hg : HasDerivWithinAt g dg I t)
    (hy : HasDerivWithinAt y (weightedGenerator A (g t) dg (y t)) I t) :
    HasDerivWithinAt (fun u => g u • y u) (A (g t • y t)) I t := by
  refine (hg.smul hy).congr_deriv ?_
  change g t • ((A - (dg / g t) • ContinuousLinearMap.id ℝ E) (y t)) + dg • y t =
    A (g t • y t)
  simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply, smul_sub, smul_smul, map_smul]
  rw [show g t * (dg / g t) = dg by field_simp]
  abel

private theorem norm_inv_weight_smul (x : E) {g : ℝ} (hg : 0 < g) :
    ‖g⁻¹ • x‖ = ‖x‖ / g := by
  rw [norm_smul_of_nonneg (inv_nonneg.mpr hg.le), div_eq_mul_inv, mul_comm]

private theorem weightedGenerator_stable {A : ℝ → E →L[ℝ] E} {g dg : ℝ → ℝ} {a b K : ℝ}
    (hg₀ : ∀ t ∈ Icc a b, 0 < g t) (hg : ∀ t ∈ Icc a b, HasDerivWithinAt g (dg t) (Icc a b) t)
    (hStable : ∀ x : ℝ → E,
      (∀ t ∈ Icc a b, HasDerivWithinAt x (A t (x t)) (Icc a b) t) →
      ∀ u ∈ Icc a b, ∀ t ∈ Icc u b, ‖x t‖ / g t ≤ K * (‖x u‖ / g u)) :
    ∀ y : ℝ → E, (∀ t ∈ Icc a b,
      HasDerivWithinAt y (weightedGenerator (A t) (g t) (dg t) (y t)) (Icc a b) t) →
      ∀ u ∈ Icc a b, ∀ t ∈ Icc u b, ‖y t‖ ≤ K * ‖y u‖ := by
  intro y hy u hu t ht
  have ht' : t ∈ Icc a b := ⟨hu.1.trans ht.1, ht.2⟩
  have h := hStable (fun v => g v • y v)
    (fun v hv => hasDerivWithinAt_unweighted (hg₀ v hv) (hg v hv) (hy v hv)) u hu t ht
  simpa only [norm_smul_of_nonneg (hg₀ u hu).le, norm_smul_of_nonneg (hg₀ t ht').le,
    mul_comm (g u), mul_comm (g t), mul_div_cancel_right₀ _ (hg₀ u hu).ne',
    mul_div_cancel_right₀ _ (hg₀ t ht').ne'] using h

variable [CompleteSpace E]

/-- The weighted forward estimate for a forced linear ODE in fixed
coordinates, with the exact time integral of the normalized forcing. -/
theorem weighted_linearODE_forced_norm_le {A : ℝ → E →L[ℝ] E} {g dg : ℝ → ℝ}
    {x f : ℝ → E} {a b t K : ℝ}
    (hA : ContinuousOn A (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hg₀ : ∀ u ∈ Icc a b, 0 < g u)
    (hg : ∀ u ∈ Icc a b, HasDerivWithinAt g (dg u) (Icc a b) u)
    (hdg : ContinuousOn dg (Icc a b))
    (hStable : ∀ y : ℝ → E,
      (∀ u ∈ Icc a b, HasDerivWithinAt y (A u (y u)) (Icc a b) u) →
      ∀ u ∈ Icc a b, ∀ v ∈ Icc u b, ‖y v‖ / g v ≤ K * (‖y u‖ / g u))
    (hx : ∀ u ∈ Icc a b, HasDerivWithinAt x (A u (x u) + f u) (Icc a b) u)
    (ht : t ∈ Icc a b) :
    ‖x t‖ / g t ≤ K * (‖x a‖ / g a + ∫ u in a..t, ‖f u‖ / g u) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have hgc := HasDerivWithinAt.continuousOn hg
  have hW := continuousOn_weightedGenerator hA hgc hdg hg₀
  have hF : ContinuousOn (fun u => (g u)⁻¹ • f u) (Icc a b) :=
    (hgc.inv₀ fun u hu => (hg₀ u hu).ne').smul hf
  have h := linearODE_forced_norm_le hW hF (weightedGenerator_stable hg₀ hg hStable)
    (fun u hu => hasDerivWithinAt_weighted (hg₀ u hu) (hg u hu) (hx u hu)) ht
  rw [norm_inv_weight_smul _ (hg₀ t ht), norm_inv_weight_smul _ (hg₀ a ha)] at h
  have heq : (∫ u in a..t, K * ‖(g u)⁻¹ • f u‖) = ∫ u in a..t, K * (‖f u‖ / g u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    change K * ‖(g u)⁻¹ • f u‖ = K * (‖f u‖ / g u)
    rw [norm_inv_weight_smul _ (hg₀ u ⟨hu.1, hu.2.trans ht.2⟩)]
  rw [heq, intervalIntegral.integral_const_mul, ← mul_add] at h
  exact h

/-- A perturbation of the center coefficient preserves the weighted forward
estimate with the exponential of its integrated size. The second conclusion
also compares solutions at the label and center. -/
theorem weighted_linearODE_perturbation_bounds
    {A R : ℝ → E →L[ℝ] E} {g dg ρ : ℝ → ℝ} {x y : ℝ → E} {a b t K : ℝ}
    (hK : 0 ≤ K) (hA : ContinuousOn A (Icc a b)) (hR : ContinuousOn R (Icc a b))
    (hρ : ContinuousOn ρ (Icc a b)) (hRρ : ∀ u ∈ Icc a b, ‖R u‖ ≤ ρ u)
    (hg₀ : ∀ u ∈ Icc a b, 0 < g u)
    (hg : ∀ u ∈ Icc a b, HasDerivWithinAt g (dg u) (Icc a b) u)
    (hdg : ContinuousOn dg (Icc a b))
    (hStable : ∀ z : ℝ → E,
      (∀ u ∈ Icc a b, HasDerivWithinAt z (A u (z u)) (Icc a b) u) →
      ∀ u ∈ Icc a b, ∀ v ∈ Icc u b, ‖z v‖ / g v ≤ K * (‖z u‖ / g u))
    (hx : ∀ u ∈ Icc a b, HasDerivWithinAt x (A u (x u) + R u (x u)) (Icc a b) u)
    (hy : ∀ u ∈ Icc a b, HasDerivWithinAt y (A u (y u)) (Icc a b) u)
    (ht : t ∈ Icc a b) :
    let D := ∫ u in a..t, ρ u
    ‖x t‖ / g t ≤ K * (‖x a‖ / g a) * Real.exp (K * D) ∧
      ‖x t - y t‖ / g t ≤ K * (‖x a - y a‖ / g a) +
        K ^ 2 * (‖x a‖ / g a) * Real.exp (K * D) * D := by
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  let B (u : ℝ) := weightedGenerator (A u) (g u) (dg u)
  have hB : ContinuousOn B (Icc a b) :=
    continuousOn_weightedGenerator hA (HasDerivWithinAt.continuousOn hg) hdg hg₀
  have hx' (u : ℝ) (hu : u ∈ Icc a b) : HasDerivWithinAt (fun v => (g v)⁻¹ • x v)
      (B u ((g u)⁻¹ • x u) + R u ((g u)⁻¹ • x u)) (Icc a b) u := by
    simpa only [map_smul] using hasDerivWithinAt_weighted (hg₀ u hu) (hg u hu) (hx u hu)
  have hy' (u : ℝ) (hu : u ∈ Icc a b) : HasDerivWithinAt (fun v => (g v)⁻¹ • y v)
      (B u ((g u)⁻¹ • y u)) (Icc a b) u := by
    have h : HasDerivWithinAt y (A u (y u) + 0) (Icc a b) u := by simpa using hy u hu
    simpa only [smul_zero, add_zero] using hasDerivWithinAt_weighted (hg₀ u hu) (hg u hu) h
  have h := linearODE_perturbation_bounds hK hB hR hρ hRρ
    (weightedGenerator_stable hg₀ hg hStable) hx' hy' ht
  simpa only [← smul_sub, norm_inv_weight_smul _ (hg₀ t ht), norm_inv_weight_smul _ (hg₀ a ha)] using h

/-- In the fixed transverse coordinates, the origin propagator gives the
label propagator used in (5.23) when the coefficient change is at most the
reciprocal of the origin bound and the time interval has length at most one. -/
theorem weighted_near_label_forward {A A₁ : ℝ → E →L[ℝ] E} {g dg : ℝ → ℝ}
    {x : ℝ → E} {a b t K : ℝ}
    (hK : 0 < K) (hT : b - a ≤ 1) (hA : ContinuousOn A (Icc a b))
    (hA₁ : ContinuousOn A₁ (Icc a b))
    (hchange : ∀ u ∈ Icc a b, ‖A₁ u - A u‖ ≤ K⁻¹)
    (hg₀ : ∀ u ∈ Icc a b, 0 < g u)
    (hg : ∀ u ∈ Icc a b, HasDerivWithinAt g (dg u) (Icc a b) u)
    (hdg : ContinuousOn dg (Icc a b))
    (hCenter : ∀ z : ℝ → E,
      (∀ u ∈ Icc a b, HasDerivWithinAt z (A u (z u)) (Icc a b) u) →
      ∀ u ∈ Icc a b, ∀ v ∈ Icc u b, ‖z v‖ / g v ≤ K * (‖z u‖ / g u))
    (hx : ∀ u ∈ Icc a b, HasDerivWithinAt x (A₁ u (x u)) (Icc a b) u)
    (ht : t ∈ Icc a b) :
    ‖x t‖ / g t ≤ Real.exp 1 * K * (‖x a‖ / g a) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have hx' (u : ℝ) (hu : u ∈ Icc a b) :
      HasDerivWithinAt x (A u (x u) + (A₁ u - A u) (x u)) (Icc a b) u := by
    simpa only [sub_apply, add_sub_cancel] using hx u hu
  have hy (u : ℝ) (_ : u ∈ Icc a b) :
      HasDerivWithinAt (fun _ => (0 : E)) (A u 0) (Icc a b) u := by
    simpa only [map_zero] using hasDerivWithinAt_const u (Icc a b) (0 : E)
  have h := (weighted_linearODE_perturbation_bounds hK.le hA (hA₁.sub hA)
    continuousOn_const hchange hg₀ hg hdg hCenter hx' hy ht).1
  have hD : K * ∫ _ in a..t, K⁻¹ ≤ 1 := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm (t - a), ← mul_assoc,
      mul_inv_cancel₀ hK.ne', one_mul]
    linarith [ht.2]
  calc
    _ ≤ K * (‖x a‖ / g a) * Real.exp (K * ∫ _ in a..t, K⁻¹) := h
    _ ≤ K * (‖x a‖ / g a) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hD)
        (mul_nonneg hK.le (div_nonneg (norm_nonneg _) (hg₀ a ha).le))
    _ = _ := by ring

/-- The origin propagator and nearby coefficient bound together yield (5.23)
for the forced solve at the label. -/
theorem weighted_near_label_forced_norm_le
    {A A₁ : ℝ → E →L[ℝ] E} {g dg : ℝ → ℝ} {x f : ℝ → E} {a b t K : ℝ}
    (hK : 0 < K) (hT : b - a ≤ 1) (hA : ContinuousOn A (Icc a b))
    (hA₁ : ContinuousOn A₁ (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hchange : ∀ u ∈ Icc a b, ‖A₁ u - A u‖ ≤ K⁻¹)
    (hg₀ : ∀ u ∈ Icc a b, 0 < g u)
    (hg : ∀ u ∈ Icc a b, HasDerivWithinAt g (dg u) (Icc a b) u)
    (hdg : ContinuousOn dg (Icc a b))
    (hCenter : ∀ z : ℝ → E,
      (∀ u ∈ Icc a b, HasDerivWithinAt z (A u (z u)) (Icc a b) u) →
      ∀ u ∈ Icc a b, ∀ v ∈ Icc u b, ‖z v‖ / g v ≤ K * (‖z u‖ / g u))
    (hx : ∀ u ∈ Icc a b, HasDerivWithinAt x (A₁ u (x u) + f u) (Icc a b) u)
    (ht : t ∈ Icc a b) :
    ‖x t‖ / g t ≤ Real.exp 1 * K * (‖x a‖ / g a + ∫ u in a..t, ‖f u‖ / g u) := by
  refine weighted_linearODE_forced_norm_le hA₁ hf hg₀ hg hdg ?_ hx ht
  intro y hy u hu v hv
  have huu : u ∈ Icc u b := ⟨le_rfl, hu.2⟩
  have hsub : Icc u b ⊆ Icc a b := Icc_subset_Icc_left hu.1
  have hlocal (z : ℝ → E)
      (hz : ∀ s ∈ Icc u b, HasDerivWithinAt z (A s (z s)) (Icc u b) s)
      (s : ℝ) (hs : s ∈ Icc u b) (d : ℝ) (hd : d ∈ Icc s b) :
      ‖z d‖ / g d ≤ K * (‖z s‖ / g s) := by
    obtain ⟨w, hw₀, hw⟩ := linearODE_exists_Icc_of_mem hu hA (z u)
    have heq := linearODE_unique_of_mem ordConnected_Icc huu (hA.mono hsub)
      (fun s hs => (hw s (hsub hs)).mono hsub) hz hw₀
    have hd' : d ∈ Icc u b := ⟨hs.1.trans hd.1, hd.2⟩
    simpa only [heq hs, heq hd'] using hCenter w hw s (hsub hs) d hd
  refine weighted_near_label_forward hK (by linarith [hu.1]) (hA.mono hsub)
    (hA₁.mono hsub) (fun s hs => hchange s (hsub hs)) (fun s hs => hg₀ s (hsub hs))
    (fun s hs => (hg s (hsub hs)).mono hsub) (hdg.mono hsub) hlocal
    (fun s hs => (hy s (hsub hs)).mono hsub) hv

/-- The fundamental solution depends differentiably on the parameter
when the generator does. Its uniform bound and parameter continuity are
consequences of the coefficient bounds. -/
theorem exists_parameter_differentiable_fundamental
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {A : ℝ → P → E →L[ℝ] E} {DA : ℝ → P → P →L[ℝ] (E →L[ℝ] E)}
    {T : ℝ} {K L : ℝ≥0} (hT : 0 ≤ T)
    (hAb : ∀ t ∈ Icc 0 T, ∀ p, ‖A t p‖ ≤ K)
    (hAc : ∀ p, ContinuousOn (fun t => A t p) (Icc 0 T))
    (hAlip : ∀ t ∈ Icc 0 T, LipschitzWith L (A t))
    (hDA : ∀ t ∈ Icc 0 T, ∀ p, HasFDerivAt (A t) (DA t p) p)
    (hDAc : ∀ p, ContinuousOn (fun t => DA t p) (Icc 0 T)) :
    ∃ F : ℝ → P → E →L[ℝ] E, (∀ p, F 0 p = ContinuousLinearMap.id ℝ E) ∧
      (∀ p, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun u => F u p)
        ((A t p).comp (F t p)) (Icc 0 T) t) ∧
      ContinuousOn (Function.uncurry F) (Icc 0 T ×ˢ univ) ∧
      ∀ p, ∃ W : ℝ → P →L[ℝ] (E →L[ℝ] E), W 0 = 0 ∧
        (∀ t ∈ Icc 0 T, HasFDerivAt (F t) (W t) p) ∧
        ∀ t ∈ Icc 0 T, HasDerivWithinAt W
          (((ContinuousLinearMap.compL ℝ E E E (A t p)).comp (W t)) +
            (((ContinuousLinearMap.compL ℝ E E E).flip (F t p)).comp (DA t p))) (Icc 0 T) t := by
  let C := ContinuousLinearMap.compL ℝ E E E
  have hB (t : ℝ) (ht : t ∈ Icc 0 T) (p : P) : ‖C (A t p)‖ ≤ ‖C‖₊ * K :=
    (C.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hAb t ht p) (norm_nonneg C))
  have hBtime (p : P) : ContinuousOn (fun t => C (A t p)) (Icc 0 T) :=
    C.continuous.comp_continuousOn (hAc p)
  have hBlip (t : ℝ) (ht : t ∈ Icc 0 T) : LipschitzWith (‖C‖₊ * L) (fun p => C (A t p)) :=
    C.lipschitzWith.comp (hAlip t ht)
  have hF₀ : LipschitzWith 0 (fun _ : P => ContinuousLinearMap.id ℝ E) :=
    LipschitzWith.const _
  obtain ⟨F, hinit, hF', hnorm, Λ, hLip, hcont⟩ :=
    exists_jointly_continuous_parameterized_linearODE (f := fun _ _ => (0 : E →L[ℝ] E))
      (K := ‖C‖₊ * K) (H := 0) (C₀ := 1) (C₁ := 0)
      hT zero_le_one le_rfl hB hBtime hBlip
      (fun _ _ _ => by simp) (fun _ => continuousOn_const) (fun _ _ => LipschitzWith.const _)
      (fun _ => ContinuousLinearMap.id ℝ E) hF₀ (fun _ => ContinuousLinearMap.norm_id_le)
  have hF₀p (p : P) : F 0 p = ContinuousLinearMap.id ℝ E := congrFun hinit p
  have hF (p : P) (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun u => F u p) ((A t p).comp (F t p)) (Icc 0 T) t := by
    simpa only [add_zero, C, ContinuousLinearMap.compL_apply] using hF' p t ht
  refine ⟨F, hF₀p, hF, hcont, fun p => ?_⟩
  exact linearFundamental_parameterDerivative hT p hAc hAlip (fun t ht => hDA t ht p) (hDAc p) hF₀p hF
    (fun t ht => (hLip t ht).continuous.continuousAt) (fun q t ht => hnorm t ht q)

/-- For the forced equation, adjoining a constant scalar coordinate gives
the actual solution family with a Fréchet derivative in the joint parameter
at every time of the closed interval. -/
theorem exists_parameter_differentiable_forced_linearODE
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {A : ℝ → P → E →L[ℝ] E} {DA : ℝ → P → P →L[ℝ] (E →L[ℝ] E)}
    {f : ℝ → P → E} {Df : ℝ → P → P →L[ℝ] E}
    {T : ℝ} {K L F H : ℝ≥0} (hT : 0 ≤ T)
    (hAb : ∀ t ∈ Icc 0 T, ∀ p, ‖A t p‖ ≤ K)
    (hAc : ∀ p, ContinuousOn (fun t => A t p) (Icc 0 T))
    (hAlip : ∀ t ∈ Icc 0 T, LipschitzWith L (A t))
    (hDA : ∀ t ∈ Icc 0 T, ∀ p, HasFDerivAt (A t) (DA t p) p)
    (hDAc : ∀ p, ContinuousOn (fun t => DA t p) (Icc 0 T))
    (hfb : ∀ t ∈ Icc 0 T, ∀ p, ‖f t p‖ ≤ F)
    (hfc : ∀ p, ContinuousOn (fun t => f t p) (Icc 0 T))
    (hflip : ∀ t ∈ Icc 0 T, LipschitzWith H (f t))
    (hDf : ∀ t ∈ Icc 0 T, ∀ p, HasFDerivAt (f t) (Df t p) p)
    (hDfc : ∀ p, ContinuousOn (fun t => Df t p) (Icc 0 T))
    (x₀ : P → E) (hx₀ : Differentiable ℝ x₀) :
    ∃ x : ℝ → P → E, x 0 = x₀ ∧
      (∀ p, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun u => x u p)
        (A t p (x t p) + f t p) (Icc 0 T) t) ∧
      ContinuousOn (Function.uncurry x) (Icc 0 T ×ˢ univ) ∧
      ∀ t ∈ Icc 0 T, Differentiable ℝ (x t) := by
  let X := E × ℝ
  let inject := ContinuousLinearMap.inl ℝ E ℝ
  let Amap : (E →L[ℝ] E) →L[ℝ] (X →L[ℝ] X) :=
    (ContinuousLinearMap.compL ℝ X E X inject).comp
      ((ContinuousLinearMap.compL ℝ X E E).flip (ContinuousLinearMap.fst ℝ E ℝ))
  let fmap : E →L[ℝ] (X →L[ℝ] X) :=
    (ContinuousLinearMap.compL ℝ X E X inject).comp
      (ContinuousLinearMap.smulRightL ℝ X E (ContinuousLinearMap.snd ℝ E ℝ))
  let B (t : ℝ) (p : P) := Amap (A t p) + fmap (f t p)
  let DB (t : ℝ) (p : P) := Amap.comp (DA t p) + fmap.comp (Df t p)
  have hBapply (t : ℝ) (p : P) (z : X) :
      B t p z = (A t p z.1 + z.2 • f t p, 0) := by
    simp [B, Amap, fmap, inject, X]
  have hBb (t : ℝ) (ht : t ∈ Icc 0 T) (p : P) :
      ‖B t p‖ ≤ ‖Amap‖₊ * K + ‖fmap‖₊ * F :=
    (norm_add_le _ _).trans (add_le_add
      ((Amap.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hAb t ht p) (norm_nonneg Amap)))
      ((fmap.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hfb t ht p) (norm_nonneg fmap))))
  have hBc (p : P) : ContinuousOn (fun t => B t p) (Icc 0 T) :=
    (Amap.continuous.comp_continuousOn (hAc p)).add (fmap.continuous.comp_continuousOn (hfc p))
  have hBlip (t : ℝ) (ht : t ∈ Icc 0 T) :
      LipschitzWith (‖Amap‖₊ * L + ‖fmap‖₊ * H) (B t) :=
    (Amap.lipschitzWith.comp (hAlip t ht)).add (fmap.lipschitzWith.comp (hflip t ht))
  have hDB (t : ℝ) (ht : t ∈ Icc 0 T) (p : P) : HasFDerivAt (B t) (DB t p) p :=
    (Amap.hasFDerivAt.comp p (hDA t ht p)).add (fmap.hasFDerivAt.comp p (hDf t ht p))
  have hDBc (p : P) : ContinuousOn (fun t => DB t p) (Icc 0 T) :=
    ((ContinuousLinearMap.compL ℝ P (E →L[ℝ] E) (X →L[ℝ] X) Amap).continuous.comp_continuousOn
      (hDAc p)).add
      ((ContinuousLinearMap.compL ℝ P E (X →L[ℝ] X) fmap).continuous.comp_continuousOn (hDfc p))
  obtain ⟨Φ, hinit, hΦ, hΦc, hΦp⟩ :=
    exists_parameter_differentiable_fundamental
      (K := ‖Amap‖₊ * K + ‖fmap‖₊ * F) (L := ‖Amap‖₊ * L + ‖fmap‖₊ * H)
      hT hBb hBc hBlip hDB hDBc
  let z (t : ℝ) (p : P) : X := Φ t p (x₀ p, 1)
  let x (t : ℝ) (p : P) := (z t p).1
  have hinitz (p : P) : z 0 p = (x₀ p, 1) := by simp [z, hinit p]
  have hz (p : P) (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun u => z u p)
        (A t p (z t p).1 + (z t p).2 • f t p, 0) (Icc 0 T) t := by
    simpa only [ContinuousLinearMap.comp_apply, hBapply, map_zero, add_zero, z] using
      (hΦ p t ht).clm_apply (hasDerivWithinAt_const t (Icc 0 T) (x₀ p, (1 : ℝ)))
  have hone (p : P) (t : ℝ) (ht : t ∈ Icc 0 T) : (z t p).2 = 1 :=
    linearODE_unique_of_mem (A := fun _ => (0 : ℝ →L[ℝ] ℝ)) (y := fun _ => 1)
      ordConnected_Icc ⟨le_rfl, hT⟩ continuousOn_const
      (fun u hu => by
        have h := (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt.comp_hasDerivWithinAt u (hz p u hu)
        change HasDerivWithinAt (fun d => (z d p).2) (0 : ℝ) (Icc 0 T) u at h
        simpa only [zero_apply] using h)
      (fun u _ => by simpa only [zero_apply] using hasDerivWithinAt_const u (Icc 0 T) (1 : ℝ))
      (by simp [hinitz p]) ht
  refine ⟨x, funext (fun p => congrArg Prod.fst (hinitz p)), fun p t ht => ?_, ?_, fun t ht => ?_⟩
  · have h := (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt.comp_hasDerivWithinAt t (hz p t ht)
    change HasDerivWithinAt (fun d => (z d p).1)
      (A t p (z t p).1 + (z t p).2 • f t p) (Icc 0 T) t at h
    simpa only [x, hone p t ht, one_smul] using h
  · exact (hΦc.clm_apply
      ((hx₀.continuous.comp continuous_snd).prodMk continuous_const).continuousOn).fst
  · have hd : Differentiable ℝ (Φ t) := fun p => by
      obtain ⟨W, _, hW, _⟩ := hΦp p
      exact (hW t ht).differentiableAt
    exact (hd.clm_apply (hx₀.prodMk (differentiable_const (1 : ℝ)))).fst

end TorusEuler
