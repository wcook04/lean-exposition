import TorusEuler.LinearFlowExistence
import TorusEuler.ReferencePropagator

/-! # Perturbation bounds for the transverse reference flow -/

open Set MeasureTheory

namespace TorusEuler

section LinearODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Variation of constants using a fundamental solution and its inverse,
both normalized at the left endpoint. -/
theorem linearODE_variation_of_constants {A Φ Ψ : ℝ → E →L[ℝ] E} {z f : ℝ → E}
    {a b t : ℝ} (hA : ContinuousOn A (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hΦ₀ : Φ a = ContinuousLinearMap.id ℝ E) (hΨ₀ : Ψ a = ContinuousLinearMap.id ℝ E)
    (hΦ : ∀ r ∈ Icc a b, HasDerivWithinAt Φ ((A r).comp (Φ r)) (Icc a b) r)
    (hΨ : ∀ r ∈ Icc a b, HasDerivWithinAt Ψ (-((Ψ r).comp (A r))) (Icc a b) r)
    (hz : ∀ r ∈ Icc a b, HasDerivWithinAt z (A r (z r) + f r) (Icc a b) r)
    (ht : t ∈ Icc a b) :
    z t = Φ t (z a) + ∫ r in a..t, Φ t (Ψ r (f r)) := by
  have ha : a ∈ Icc a b := left_mem_Icc.2 (ht.1.trans ht.2)
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hInv := linearODE_fundamental_comp_inv ordConnected_Icc ha hA hΦ hΨ hΦ₀ hΨ₀
  have hD (r : ℝ) (hr : r ∈ Icc a b) :
      HasDerivWithinAt (fun u => Ψ u (z u)) (Ψ r (f r)) (Icc a b) r := by
    refine ((hΨ r hr).clm_apply (hz r hr)).congr_deriv ?_
    simp [map_add]
  have hInt : IntervalIntegrable (fun r => Ψ r (f r)) volume a t :=
    ((HasDerivWithinAt.continuousOn hΨ).clm_apply hf).mono hsub
      |>.intervalIntegrable_of_Icc ht.1
  have hFTC : (∫ r in a..t, Ψ r (f r)) = Ψ t (z t) - Ψ a (z a) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
      ((HasDerivWithinAt.continuousOn hD).mono hsub)
      (fun r hr =>
        (hD r (hsub (Ioo_subset_Icc_self hr))).hasDerivAt
          (Icc_mem_nhds hr.1 (hr.2.trans_le ht.2))) hInt
  have hsum : Ψ t (z t) = z a + ∫ r in a..t, Ψ r (f r) := by
    rw [hFTC, hΨ₀, ContinuousLinearMap.id_apply]
    abel
  calc
    z t = Φ t (Ψ t (z t)) := by
      exact (congrArg (fun L : E →L[ℝ] E => L (z t)) (hInv t ht)).symm
    _ = Φ t (z a) + ∫ r in a..t, Φ t (Ψ r (f r)) := by
      rw [hsum, map_add, (Φ t).intervalIntegral_comp_comm hInt]

/-- A forward bound on homogeneous solutions controls the forced equation
through the time integral of the forcing. -/
theorem linearODE_forced_norm_le {A : ℝ → E →L[ℝ] E} {z f : ℝ → E} {a b M : ℝ}
    (hA : ContinuousOn A (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hStable : ∀ (x : ℝ → E),
      (∀ r ∈ Icc a b, HasDerivWithinAt x (A r (x r)) (Icc a b) r) →
      ∀ r ∈ Icc a b, ∀ t ∈ Icc r b, ‖x t‖ ≤ M * ‖x r‖)
    (hz : ∀ r ∈ Icc a b, HasDerivWithinAt z (A r (z r) + f r) (Icc a b) r)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖z t‖ ≤ M * ‖z a‖ + ∫ r in a..t, M * ‖f r‖ := by
  have hab := ht.1.trans ht.2
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab
  obtain ⟨Φ, hΦ₀, hΦ⟩ := linearODE_exists_Icc (E := E →L[ℝ] E)
    (A := fun r => ContinuousLinearMap.compL ℝ E E E (A r)) hab
    ((ContinuousLinearMap.compL ℝ E E E).continuous.comp_continuousOn hA)
    (ContinuousLinearMap.id ℝ E)
  obtain ⟨Ψ, hΨ₀, hΨ⟩ := linearODE_exists_Icc (E := E →L[ℝ] E)
    (A := fun r => -(ContinuousLinearMap.compL ℝ E E E).flip (A r)) hab
    (((ContinuousLinearMap.compL ℝ E E E).flip.continuous.comp_continuousOn hA).neg)
    (ContinuousLinearMap.id ℝ E)
  have hΦ' (r : ℝ) (hr : r ∈ Icc a b) :
      HasDerivWithinAt Φ ((A r).comp (Φ r)) (Icc a b) r := by
    simpa only [ContinuousLinearMap.compL_apply] using hΦ r hr
  have hΨ' (r : ℝ) (hr : r ∈ Icc a b) :
      HasDerivWithinAt Ψ (-((Ψ r).comp (A r))) (Icc a b) r := by
    simpa only [ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
      neg_apply] using hΨ r hr
  have hInv := linearODE_fundamental_comp_inv ordConnected_Icc ha hA hΦ' hΨ' hΦ₀ hΨ₀
  have hPath (v : E) (r : ℝ) (hr : r ∈ Icc a b) :
      HasDerivWithinAt (fun s => Φ s v) (A r (Φ r v)) (Icc a b) r := by
    simpa using (hΦ' r hr).clm_apply (hasDerivWithinAt_const r (Icc a b) v)
  have hFirst : ‖Φ t (z a)‖ ≤ M * ‖z a‖ := by
    simpa [hΦ₀] using hStable (fun r => Φ r (z a)) (hPath (z a)) a ha t ht
  have hKernel (r : ℝ) (hr : r ∈ Icc a t) : ‖Φ t (Ψ r (f r))‖ ≤ M * ‖f r‖ := by
    have hr' : r ∈ Icc a b := ⟨hr.1, hr.2.trans ht.2⟩
    have hpoint : Φ r (Ψ r (f r)) = f r := by
      exact congrArg (fun L : E →L[ℝ] E => L (f r)) (hInv r hr')
    simpa only [hpoint] using hStable (fun u => Φ u (Ψ r (f r))) (hPath (Ψ r (f r)))
      r hr' t ⟨hr.2, ht.2⟩
  have hGc : ContinuousOn (fun r => Φ t (Ψ r (f r))) (Icc a t) :=
    (Φ t).continuous.comp_continuousOn
      (((HasDerivWithinAt.continuousOn hΨ').clm_apply hf).mono (Icc_subset_Icc_right ht.2))
  have hFc : ContinuousOn (fun r => M * ‖f r‖) (Icc a t) :=
    continuousOn_const.mul (hf.mono (Icc_subset_Icc_right ht.2)).norm
  have hI : ‖∫ r in a..t, Φ t (Ψ r (f r))‖ ≤ ∫ r in a..t, M * ‖f r‖ :=
    (intervalIntegral.norm_integral_le_integral_norm ht.1).trans
      (intervalIntegral.integral_mono_on ht.1 (hGc.norm.intervalIntegrable_of_Icc ht.1)
        (hFc.intervalIntegrable_of_Icc ht.1) hKernel)
  rw [linearODE_variation_of_constants hA hf hΦ₀ hΨ₀ hΦ' hΨ' hz ht]
  exact (norm_add_le _ _).trans (add_le_add hFirst hI)

end LinearODE

private theorem hasDerivWithinAt_integral_from_left {f : ℝ → ℝ} {a b t : ℝ}
    (hf : ContinuousOn f (Icc a b)) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun r => ∫ u in a..r, f u) (f t) (Icc a b) t := by
  let _ : Fact (t ∈ Icc a b) := ⟨ht⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right
    ((hf.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1)
    (hf.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hf t ht)

/-- Grönwall's integral inequality with a continuous time-dependent coefficient. -/
theorem le_exp_integral_of_volterra {u k : ℝ → ℝ} {a b c : ℝ}
    (hU : ContinuousOn u (Icc a b)) (hK : ContinuousOn k (Icc a b))
    (hk : ∀ t ∈ Icc a b, 0 ≤ k t)
    (hu : ∀ t ∈ Icc a b, u t ≤ c + ∫ r in a..t, k r * u r)
    {t : ℝ} (ht : t ∈ Icc a b) : u t ≤ c * Real.exp (∫ r in a..t, k r) := by
  let G (r : ℝ) := c + ∫ v in a..r, k v * u v
  let J (r : ℝ) := ∫ v in a..r, k v
  let F (r : ℝ) := G r * Real.exp (-J r)
  have hD (r : ℝ) (hr : r ∈ Icc a b) :
      HasDerivWithinAt F (k r * (u r - G r) * Real.exp (-J r)) (Icc a b) r := by
    refine (((hasDerivWithinAt_integral_from_left (hK.mul hU) hr).const_add c).mul
      (hasDerivWithinAt_integral_from_left hK hr).neg.exp).congr_deriv ?_
    change (k r * u r * Real.exp (-J r) + G r * (Real.exp (-J r) * -k r)) = _
    ring
  have hanti : AntitoneOn F (Icc a b) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
      (HasDerivWithinAt.continuousOn hD)
      (fun r hr => (hD r (interior_subset hr)).mono interior_subset) ?_
    intro r hr
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (hk r (interior_subset hr))
        (sub_nonpos.mpr (hu r (interior_subset hr)))) (Real.exp_pos _).le
  have hF : F t ≤ c := by
    simpa [F, G, J] using hanti (left_mem_Icc.2 (ht.1.trans ht.2)) ht ht.1
  have hG : G t ≤ c * Real.exp (J t) := by
    exact (div_le_iff₀ (Real.exp_pos _)).1 (by simpa [F, Real.exp_neg, div_eq_mul_inv] using hF)
  exact (hu t ht).trans hG

section LinearPerturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- For a perturbation bounded by `ρ`, the growth and the error relative to a
reference path use the integrated perturbation as their exponential argument. -/
theorem linearODE_perturbation_bounds {A R : ℝ → E →L[ℝ] E} {x y : ℝ → E} {ρ : ℝ → ℝ}
    {a b M : ℝ} (hM : 0 ≤ M) (hA : ContinuousOn A (Icc a b))
    (hR : ContinuousOn R (Icc a b)) (hρ : ContinuousOn ρ (Icc a b))
    (hRρ : ∀ r ∈ Icc a b, ‖R r‖ ≤ ρ r)
    (hStable : ∀ (z : ℝ → E),
      (∀ r ∈ Icc a b, HasDerivWithinAt z (A r (z r)) (Icc a b) r) →
      ∀ r ∈ Icc a b, ∀ t ∈ Icc r b, ‖z t‖ ≤ M * ‖z r‖)
    (hx : ∀ r ∈ Icc a b, HasDerivWithinAt x (A r (x r) + R r (x r)) (Icc a b) r)
    (hy : ∀ r ∈ Icc a b, HasDerivWithinAt y (A r (y r)) (Icc a b) r) {t : ℝ} (ht : t ∈ Icc a b) :
    let D := ∫ r in a..t, ρ r
    ‖x t‖ ≤ M * ‖x a‖ * Real.exp (M * D) ∧
      ‖x t - y t‖ ≤ M * ‖x a - y a‖ + M ^ 2 * ‖x a‖ * Real.exp (M * D) * D := by
  have hxC := HasDerivWithinAt.continuousOn hx
  have hforcing := hR.clm_apply hxC
  have hρ₀ (r : ℝ) (hr : r ∈ Icc a b) : 0 ≤ ρ r := (norm_nonneg _).trans (hRρ r hr)
  have hforcingBound (r : ℝ) (hr : r ∈ Icc a b) : ‖R r (x r)‖ ≤ ρ r * ‖x r‖ :=
    ((R r).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hRρ r hr) (norm_nonneg _))
  have hVolterra (s : ℝ) (hs : s ∈ Icc a b) :
      ‖x s‖ ≤ M * ‖x a‖ + ∫ r in a..s, (M * ρ r) * ‖x r‖ := by
    have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc_right hs.2
    have hC : ContinuousOn (fun r => (M * ρ r) * ‖x r‖) (Icc a s) :=
      (continuousOn_const.mul (hρ.mono hsub)).mul (hxC.mono hsub).norm
    refine (linearODE_forced_norm_le hA hforcing hStable hx hs).trans (add_le_add le_rfl ?_)
    apply intervalIntegral.integral_mono_on hs.1
      ((continuousOn_const.mul (hforcing.mono hsub).norm).intervalIntegrable_of_Icc hs.1)
      (hC.intervalIntegrable_of_Icc hs.1)
    intro r hr
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hforcingBound r (hsub hr)) hM
  have hxBound (s : ℝ) (hs : s ∈ Icc a b) :
      ‖x s‖ ≤ M * ‖x a‖ * Real.exp (M * ∫ r in a..s, ρ r) := by
    simpa only [intervalIntegral.integral_const_mul] using
      le_exp_integral_of_volterra (k := fun r => M * ρ r) hxC.norm (continuousOn_const.mul hρ)
        (fun r hr => mul_nonneg hM (hρ₀ r hr)) hVolterra hs
  refine ⟨hxBound t ht, ?_⟩
  have hd (r : ℝ) (hr : r ∈ Icc a b) :
      HasDerivWithinAt (fun s => x s - y s) (A r (x r - y r) + R r (x r)) (Icc a b) r := by
    refine ((hx r hr).sub (hy r hr)).congr_deriv ?_
    rw [map_sub]
    abel
  let D : ℝ := ∫ r in a..t, ρ r
  let C : ℝ := M ^ 2 * ‖x a‖ * Real.exp (M * D)
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hBound : (∫ r in a..t, M * ‖R r (x r)‖) ≤ C * D := by
    change (∫ r in a..t, M * ‖R r (x r)‖) ≤ C * ∫ r in a..t, ρ r
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on ht.1
      ((continuousOn_const.mul (hforcing.mono hsub).norm).intervalIntegrable_of_Icc ht.1)
      ((continuousOn_const.mul (hρ.mono hsub)).intervalIntegrable_of_Icc ht.1)
    intro r hr
    have hint : IntervalIntegrable ρ volume a t := (hρ.mono hsub).intervalIntegrable_of_Icc ht.1
    have hinc := intervalIntegral.integral_mono_interval (le_rfl (a := a)) hr.1 hr.2
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => hρ₀ s (hsub (Ioc_subset_Icc_self hs))))
      hint
    have hxD := (hxBound r (hsub hr)).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hinc hM)) (by positivity))
    calc
      M * ‖R r (x r)‖ ≤ M * (ρ r * ‖x r‖) :=
        mul_le_mul_of_nonneg_left (hforcingBound r (hsub hr)) hM
      _ ≤ M * (ρ r * (M * ‖x a‖ * Real.exp (M * D))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxD (hρ₀ r (hsub hr))) hM
      _ = C * ρ r := by dsimp [C]; ring
  exact (linearODE_forced_norm_le hA hforcing hStable hd ht).trans (add_le_add le_rfl hBound)

end LinearPerturbation

namespace ReferenceComparison

open ReferencePropagator
open ReferenceRiccati (s s_pos s_le_one rhs damping driving deviation hasDerivAt_s
  hasDerivWithinAt_deviation riccati_deviation_bounds)

noncomputable section

/-- Generator of the transverse model in the $(h,l)$ coordinates. -/
def triangularGenerator (scale e : ℝ → ℝ) (t : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  scale t • (ContinuousLinearMap.snd ℝ ℝ ℝ).prod 0 +
    (-(2 * scale t * (1 + e t))) • (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem triangularGenerator_apply (scale e : ℝ → ℝ) (t : ℝ) (v : ℝ × ℝ) :
    triangularGenerator scale e t v = (scale t * v.2, -(2 * scale t * (1 + e t)) * v.2) := by
  simp [triangularGenerator]

theorem continuousOn_triangularGenerator {scale e : ℝ → ℝ} {I : Set ℝ}
    (hs : ContinuousOn scale I) (he : ContinuousOn e I) :
    ContinuousOn (triangularGenerator scale e) I := by
  unfold triangularGenerator
  exact (hs.smul continuousOn_const).add
    (((continuousOn_const.mul hs).mul (continuousOn_const.add he)).neg.smul continuousOn_const)

private theorem triangularGenerator_norm_le {scale e : ℝ → ℝ} {a b : ℝ}
    (hs : ContinuousOn scale (Icc a b)) (he : ContinuousOn e (Icc a b))
    (hs₀ : ∀ t ∈ Icc a b, 0 ≤ scale t) (he₀ : ∀ t ∈ Icc a b, 0 ≤ e t)
    (z : ℝ → ℝ × ℝ)
    (hz : ∀ r ∈ Icc a b,
      HasDerivWithinAt z (triangularGenerator scale e r (z r)) (Icc a b) r)
    (r : ℝ) (hr : r ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc r b) : ‖z t‖ ≤ 2 * ‖z r‖ := by
  have hsub : Icc r t ⊆ Icc a b := Icc_subset_Icc hr.1 ht.2
  have hH (u : ℝ) (hu : u ∈ Icc r t) :
      HasDerivWithinAt (fun v => (z v).1) (scale u * (z u).2) (Icc r t) u := by
    simpa [Function.comp_def] using (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt u
      ((hz u (hsub hu)).mono hsub)
  have hL (u : ℝ) (hu : u ∈ Icc r t) :
      HasDerivWithinAt (fun v => (z v).2) (-(2 * scale u * (1 + e u)) * (z u).2) (Icc r t) u := by
    simpa [Function.comp_def] using (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt u
      ((hz u (hsub hu)).mono hsub)
  have hBound := triangular_propagator_abs_add_le ht.1 (hs.mono hsub) (he.mono hsub)
    (fun u hu => hs₀ u (hsub hu)) (fun u hu => he₀ u (hsub hu)) hH hL
  rw [Prod.norm_def, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.norm_eq_abs, Real.norm_eq_abs, two_mul]
  exact (max_le (le_add_of_nonneg_right (abs_nonneg _))
    (le_add_of_nonneg_left (abs_nonneg _))).trans
      (hBound.trans (add_le_add (le_max_left _ _) (le_max_right _ _)))

/-- Growth and comparison bounds for a matrix perturbation of the normalized triangular model.
The matrix and pair norms here use the maximum norm on `ℝ × ℝ`. -/
theorem triangular_perturbation_bounds {scale e ρ : ℝ → ℝ}
    {R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)} {x y : ℝ → ℝ × ℝ} {a b t : ℝ}
    (hs : ContinuousOn scale (Icc a b)) (he : ContinuousOn e (Icc a b))
    (hs₀ : ∀ r ∈ Icc a b, 0 ≤ scale r) (he₀ : ∀ r ∈ Icc a b, 0 ≤ e r)
    (hR : ContinuousOn R (Icc a b)) (hρ : ContinuousOn ρ (Icc a b))
    (hRρ : ∀ r ∈ Icc a b, ‖R r‖ ≤ ρ r)
    (hx : ∀ r ∈ Icc a b,
      HasDerivWithinAt x (triangularGenerator scale e r (x r) + R r (x r)) (Icc a b) r)
    (hy : ∀ r ∈ Icc a b, HasDerivWithinAt y (triangularGenerator scale e r (y r)) (Icc a b) r)
    (ht : t ∈ Icc a b) :
    let D := ∫ r in a..t, ρ r
    ‖x t‖ ≤ 2 * ‖x a‖ * Real.exp (2 * D) ∧
      ‖x t - y t‖ ≤ 2 * ‖x a - y a‖ + 4 * ‖x a‖ * Real.exp (2 * D) * D := by
  simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using
    linearODE_perturbation_bounds (M := 2) (by norm_num) (continuousOn_triangularGenerator hs he)
      hR hρ hRρ (triangularGenerator_norm_le hs he hs₀ he₀) hx hy ht

/-- Perturbation bounds with the clock factor and deviation from the reference Riccati solution. -/
theorem riccati_perturbation_bounds {ε T t : ℝ} {Y ρ : ℝ → ℝ}
    {R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)} {x y : ℝ → ℝ × ℝ}
    (hε : 0 < ε) (hY₀ : Y 0 = 1)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (hR : ContinuousOn R (Icc 0 T)) (hρ : ContinuousOn ρ (Icc 0 T))
    (hRρ : ∀ r ∈ Icc 0 T, ‖R r‖ ≤ ρ r)
    (hx : ∀ r ∈ Icc 0 T, HasDerivWithinAt x
      (triangularGenerator (s ε) (deviation ε Y) r (x r) + R r (x r)) (Icc 0 T) r)
    (hy : ∀ r ∈ Icc 0 T, HasDerivWithinAt y
      (triangularGenerator (s ε) (deviation ε Y) r (y r)) (Icc 0 T) r)
    (ht : t ∈ Icc 0 T) :
    let D := ∫ r in 0..t, ρ r
    ‖x t‖ ≤ 2 * ‖x 0‖ * Real.exp (2 * D) ∧
      ‖x t - y t‖ ≤ 2 * ‖x 0 - y 0‖ + 4 * ‖x 0‖ * Real.exp (2 * D) * D := by
  have hs : Continuous (s ε) := continuous_iff_continuousAt.2
    (fun r => (hasDerivAt_s ε r).continuousAt)
  have he : ContinuousOn (deviation ε Y) (Icc 0 T) :=
    HasDerivWithinAt.continuousOn (fun r hr => hasDerivWithinAt_deviation (hY r hr))
  exact triangular_perturbation_bounds hs.continuousOn he (fun r _ => (s_pos ε r).le)
    (fun r hr => (riccati_deviation_bounds hε hY₀ hY r hr).1) hR hρ hRρ hx hy ht

/-- The linear coordinate change before division by the growing reference factor. -/
def unscaledCoordinates (ε : ℝ) (Y : ℝ → ℝ) (t : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod 0 +
    (s ε t)⁻¹ • (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ) -
    (Y t / s ε t) • (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- Inverse of the linear coordinate change before inserting the growing reference factor. -/
def unscaledCoordinatesInv (ε : ℝ) (Y : ℝ → ℝ) (t : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ) +
    Y t • (ContinuousLinearMap.fst ℝ ℝ ℝ).prod 0 +
    s ε t • (ContinuousLinearMap.snd ℝ ℝ ℝ).prod 0

@[simp] theorem unscaledCoordinates_apply (ε : ℝ) (Y : ℝ → ℝ) (t : ℝ) (p : ℝ × ℝ) :
    unscaledCoordinates ε Y t p = (p.2, (p.1 - Y t * p.2) / s ε t) := by
  simp [unscaledCoordinates]
  ring

@[simp] theorem unscaledCoordinatesInv_apply (ε : ℝ) (Y : ℝ → ℝ) (t : ℝ) (p : ℝ × ℝ) :
    unscaledCoordinatesInv ε Y t p = (Y t * p.1 + s ε t * p.2, p.1) := by
  simp [unscaledCoordinatesInv]

/-- The raw matrix error after the time-dependent change of amplitude coordinates. -/
def normalizedMatrixError (ε : ℝ) (Y : ℝ → ℝ)
    (R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (t : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (unscaledCoordinates ε Y t).comp ((R t).comp (unscaledCoordinatesInv ε Y t))

theorem continuousOn_normalizedMatrixError {ε : ℝ} {Y : ℝ → ℝ}
    {R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)} {J : Set ℝ}
    (hY : ContinuousOn Y J) (hR : ContinuousOn R J) :
    ContinuousOn (normalizedMatrixError ε Y R) J := by
  have hs : Continuous (s ε) := continuous_iff_continuousAt.2
    (fun r => (hasDerivAt_s ε r).continuousAt)
  have hS₀ (r : ℝ) (_ : r ∈ J) : s ε r ≠ 0 := (s_pos ε r).ne'
  have hP : ContinuousOn (unscaledCoordinates ε Y) J := by
    unfold unscaledCoordinates
    exact (continuousOn_const.add ((hs.continuousOn.inv₀ hS₀).smul continuousOn_const)).sub
      ((hY.div hs.continuousOn hS₀).smul continuousOn_const)
  have hQ : ContinuousOn (unscaledCoordinatesInv ε Y) J := by
    unfold unscaledCoordinatesInv
    exact (continuousOn_const.add (hY.smul continuousOn_const)).add
      (hs.continuousOn.smul continuousOn_const)
  exact hP.clm_comp (hR.clm_comp hQ)

/-- The normalized state associated to a raw amplitude path. -/
def normalizedState (ε : ℝ) (Y U V : ℝ → ℝ) (t : ℝ) : ℝ × ℝ :=
  (normalizedH Y V t, normalizedL ε Y U V t)

/-- The exact normalized equation for the raw transverse system with a matrix error. -/
theorem hasDerivWithinAt_normalized_perturbed {ε T t : ℝ} {Y U V : ℝ → ℝ}
    {R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (ht : t ∈ Icc 0 T)
    (hU : HasDerivWithinAt U
      (-damping ε t * U t + driving ε t * V t + (R t (U t, V t)).1) (Icc 0 T) t)
    (hV : HasDerivWithinAt V (U t + (R t (U t, V t)).2) (Icc 0 T) t) :
    HasDerivWithinAt (normalizedState ε Y U V)
      (triangularGenerator (s ε) (deviation ε Y) t (normalizedState ε Y U V t) +
        normalizedMatrixError ε Y R t (normalizedState ε Y U V t)) (Icc 0 T) t := by
  have hg := hasDerivWithinAt_growingFactor (HasDerivWithinAt.continuousOn hY) ht
  have hg₀ := (growingFactor_pos Y t).ne'
  have hs := (hasDerivAt_s ε t).hasDerivWithinAt (s := Icc 0 T)
  have hs₀ := (s_pos ε t).ne'
  let f := R t (U t, V t)
  have hH : HasDerivWithinAt (normalizedH Y V)
      (s ε t * normalizedL ε Y U V t + f.2 / growingFactor Y t) (Icc 0 T) t := by
    refine (hV.div hg hg₀).congr_deriv ?_
    unfold normalizedL
    change ((U t + f.2) * growingFactor Y t - V t * (Y t * growingFactor Y t)) /
      growingFactor Y t ^ 2 = _
    field_simp
    ring
  have hL : HasDerivWithinAt (normalizedL ε Y U V)
      (-(2 * s ε t * (1 + deviation ε Y t)) * normalizedL ε Y U V t +
        (f.1 - Y t * f.2) / (s ε t * growingFactor Y t)) (Icc 0 T) t := by
    refine ((hU.sub ((hY t ht).mul hV)).div (hs.mul hg) (mul_ne_zero hs₀ hg₀)).congr_deriv ?_
    simp only [Pi.mul_apply, Pi.sub_apply, rhs, normalizedL, deviation]
    dsimp [f]
    field_simp
    ring
  have hInv : unscaledCoordinatesInv ε Y t (normalizedState ε Y U V t) =
      (growingFactor Y t)⁻¹ • (U t, V t) := by
    simp only [unscaledCoordinatesInv_apply, normalizedState, normalizedH, normalizedL,
      Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    constructor
    · field_simp
      ring
    · rw [div_eq_inv_mul]
  have hE : normalizedMatrixError ε Y R t (normalizedState ε Y U V t) =
      (f.2 / growingFactor Y t, (f.1 - Y t * f.2) / (s ε t * growingFactor Y t)) := by
    rw [normalizedMatrixError, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      hInv, map_smul, map_smul, unscaledCoordinates_apply]
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    constructor
    · dsimp [f]
      field_simp
    · dsimp [f]
      field_simp
  rw [triangularGenerator_apply, hE]
  exact hH.prodMk hL

theorem norm_normalizedMatrixError_le (ε : ℝ) (Y : ℝ → ℝ)
    (R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (t : ℝ) :
    ‖normalizedMatrixError ε Y R t‖ ≤ ((1 + |Y t|) ^ 2 / s ε t) * ‖R t‖ := by
  have hs := s_pos ε t
  have hs₁ := s_le_one ε t
  have hY : 0 ≤ |Y t| := abs_nonneg _
  have hfst (p : ℝ × ℝ) : |p.1| ≤ ‖p‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact le_max_left _ _
  have hsnd (p : ℝ × ℝ) : |p.2| ≤ ‖p‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact le_max_right _ _
  have hP : ‖unscaledCoordinates ε Y t‖ ≤ (1 + |Y t|) / s ε t := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro p
    rw [unscaledCoordinates_apply, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    apply max_le
    · exact (hsnd p).trans (le_mul_of_one_le_left (norm_nonneg _)
        ((le_div_iff₀ hs).2 (by linarith)))
    · rw [abs_div, abs_of_pos hs]
      have hsum : |p.1 - Y t * p.2| ≤ |p.1| + |Y t| * |p.2| := by
        simpa only [← sub_eq_add_neg, abs_neg, abs_mul] using abs_add_le p.1 (-(Y t * p.2))
      calc
        |p.1 - Y t * p.2| / s ε t ≤ (|p.1| + |Y t| * |p.2|) / s ε t :=
          div_le_div_of_nonneg_right hsum hs.le
        _ ≤ (‖p‖ + |Y t| * ‖p‖) / s ε t := div_le_div_of_nonneg_right
          (add_le_add (hfst p) (mul_le_mul_of_nonneg_left (hsnd p) hY)) hs.le
        _ = (1 + |Y t|) / s ε t * ‖p‖ := by ring
  have hQ : ‖unscaledCoordinatesInv ε Y t‖ ≤ 1 + |Y t| := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro p
    rw [unscaledCoordinatesInv_apply, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    apply max_le
    · calc
        |Y t * p.1 + s ε t * p.2| ≤ |Y t| * |p.1| + s ε t * |p.2| := by
          simpa only [abs_mul, abs_of_pos hs] using abs_add_le (Y t * p.1) (s ε t * p.2)
        _ ≤ |Y t| * ‖p‖ + 1 * ‖p‖ := add_le_add (mul_le_mul_of_nonneg_left (hfst p) hY)
          (mul_le_mul hs₁ (hsnd p) (abs_nonneg _) zero_le_one)
        _ = (1 + |Y t|) * ‖p‖ := by ring
    · exact (hfst p).trans (le_mul_of_one_le_left (norm_nonneg _) (by linarith))
  unfold normalizedMatrixError
  calc
    _ ≤ ‖unscaledCoordinates ε Y t‖ * (‖R t‖ * ‖unscaledCoordinatesInv ε Y t‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ ((1 + |Y t|) / s ε t) * (‖R t‖ * (1 + |Y t|)) :=
      mul_le_mul hP (mul_le_mul_of_nonneg_left hQ (norm_nonneg _)) (by positivity) (by positivity)
    _ = ((1 + |Y t|) ^ 2 / s ε t) * ‖R t‖ := by ring

/-- Comparison for the raw transverse system under a supplied pointwise matrix error bound.
Both output states are read in the growing reference coordinates. -/
theorem raw_matrix_comparison {ε T t : ℝ} {Y U V U₀ V₀ η : ℝ → ℝ}
    {R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (hε : 0 < ε) (hY₀ : Y 0 = 1)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (hR : ContinuousOn R (Icc 0 T)) (hη : ContinuousOn η (Icc 0 T))
    (hRη : ∀ r ∈ Icc 0 T, ‖R r‖ ≤ η r)
    (hU : ∀ r ∈ Icc 0 T, HasDerivWithinAt U
      (-damping ε r * U r + driving ε r * V r + (R r (U r, V r)).1) (Icc 0 T) r)
    (hV : ∀ r ∈ Icc 0 T, HasDerivWithinAt V (U r + (R r (U r, V r)).2) (Icc 0 T) r)
    (hU₀ : ∀ r ∈ Icc 0 T,
      HasDerivWithinAt U₀ (-damping ε r * U₀ r + driving ε r * V₀ r) (Icc 0 T) r)
    (hV₀ : ∀ r ∈ Icc 0 T, HasDerivWithinAt V₀ (U₀ r) (Icc 0 T) r)
    (ht : t ∈ Icc 0 T) :
    let z := normalizedState ε Y U V
    let z₀ := normalizedState ε Y U₀ V₀
    let D := ∫ r in 0..t, ((1 + |Y r|) ^ 2 / s ε r) * η r
    ‖z t‖ ≤ 2 * ‖z 0‖ * Real.exp (2 * D) ∧
      ‖z t - z₀ t‖ ≤ 2 * ‖z 0 - z₀ 0‖ + 4 * ‖z 0‖ * Real.exp (2 * D) * D := by
  have hYC := HasDerivWithinAt.continuousOn hY
  have hs : Continuous (s ε) := continuous_iff_continuousAt.2
    (fun r => (hasDerivAt_s ε r).continuousAt)
  let ρ (r : ℝ) := ((1 + |Y r|) ^ 2 / s ε r) * η r
  have hρ : ContinuousOn ρ (Icc 0 T) :=
    ((((continuousOn_const.add hYC.abs).pow 2).div hs.continuousOn
      (fun r _ => (s_pos ε r).ne')).mul hη)
  have hRρ (r : ℝ) (hr : r ∈ Icc 0 T) : ‖normalizedMatrixError ε Y R r‖ ≤ ρ r :=
    (norm_normalizedMatrixError_le ε Y R r).trans
      (mul_le_mul_of_nonneg_left (hRη r hr) (div_nonneg (sq_nonneg _) (s_pos ε r).le))
  refine riccati_perturbation_bounds hε hY₀ hY (continuousOn_normalizedMatrixError hYC hR)
    hρ hRρ (fun r hr => hasDerivWithinAt_normalized_perturbed hY hr (hU r hr) (hV r hr)) ?_ ht
  intro r hr
  rw [triangularGenerator_apply]
  obtain ⟨hH, hL⟩ := hasDerivWithinAt_normalized hY hr (hU₀ r hr) (hV₀ r hr)
  exact hH.prodMk hL

end

end ReferenceComparison

end TorusEuler
