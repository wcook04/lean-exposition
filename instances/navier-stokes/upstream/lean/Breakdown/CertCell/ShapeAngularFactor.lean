import Breakdown.CertCell.ShapeDefs

open scoped ContDiff Topology
open Filter Asymptotics

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (heightRatio)

namespace Internal

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_of_bounds_off_zero (n : ℕ) : ∀ (f : E → F), ContDiffOn ℝ n f {0}ᶜ → f 0 = 0 →
    (∀ a ≤ n, ∃ C : ℝ, ∀ x ≠ 0, ‖iteratedFDeriv ℝ a f x‖ ≤ C * ‖x‖ ^ (n + 1 - a)) →
    ContDiff ℝ n f := by
  induction n generalizing F with
  | zero =>
    intro f hf h0 hb
    rw [Nat.cast_zero, contDiff_zero]
    obtain ⟨C, hC⟩ := hb 0 le_rfl
    refine continuous_iff_continuousAt.2 fun x => ?_
    by_cases hx : x = 0
    · subst hx
      have hle : ∀ y : E, ‖f y‖ ≤ |C| * ‖y‖ := by
        intro y
        by_cases hy : y = 0
        · subst hy; simp [h0]
        · have := hC y hy
          rw [norm_iteratedFDeriv_zero] at this
          calc ‖f y‖ ≤ C * ‖y‖ ^ 1 := this
            _ ≤ |C| * ‖y‖ := by rw [pow_one]; exact mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg y)
      have ht : Tendsto (fun y : E => |C| * ‖y‖) (𝓝 0) (𝓝 0) := by
        have := (tendsto_const_nhds (x := |C|)).mul (continuous_norm.tendsto' (0 : E) 0 norm_zero)
        rwa [mul_zero] at this
      rw [ContinuousAt, h0]
      exact squeeze_zero_norm hle ht
    · exact hf.continuousOn.continuousAt (isOpen_compl_singleton.mem_nhds hx)
  | succ n ih =>
    intro f hf h0 hb
    obtain ⟨C, hC⟩ := hb 0 (Nat.zero_le _)
    have hO : f =O[𝓝 0] fun x : E => ‖x‖ ^ (n + 2) := by
      refine IsBigO.of_bound |C| (Eventually.of_forall fun y => ?_)
      by_cases hy : y = 0
      · subst hy; simp [h0]
      · have := hC y hy
        rw [norm_iteratedFDeriv_zero] at this
        rw [norm_pow, norm_norm]
        calc ‖f y‖ ≤ C * ‖y‖ ^ (n + 1 + 1 - 0) := this
          _ ≤ |C| * ‖y‖ ^ (n + 2) := by
            rw [Nat.sub_zero]
            exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    have hlo : f =o[𝓝 0] fun x : E => x := hO.trans_isLittleO (isLittleO_norm_pow_id (by omega))
    have hfd : HasFDerivAt f (0 : E →L[ℝ] F) 0 := by
      rw [hasFDerivAt_iff_isLittleO_nhds_zero]
      simpa [h0] using hlo
    have hdiff : Differentiable ℝ f := by
      intro x
      by_cases hx : x = 0
      · subst hx; exact hfd.differentiableAt
      · exact (hf.differentiableOn (by simp)).differentiableAt (isOpen_compl_singleton.mem_nhds hx)
    have hf' : ContDiffOn ℝ n (fderiv ℝ f) {0}ᶜ :=
      hf.fderiv_of_isOpen isOpen_compl_singleton (by push_cast; exact le_rfl)
    have hd : ContDiff ℝ n (fderiv ℝ f) := by
      refine ih (fderiv ℝ f) hf' hfd.fderiv fun a ha => ?_
      obtain ⟨C', hC'⟩ := hb (a + 1) (by omega)
      refine ⟨C', fun x hx => ?_⟩
      rw [norm_iteratedFDeriv_fderiv]
      have := hC' x hx
      have he : n + 1 + 1 - (a + 1) = n + 1 - a := by omega
      rwa [he] at this
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    exact ⟨hdiff, by simp, hd⟩

theorem norm_iteratedFDeriv_le_of_homogeneous (d a : ℕ) (ha : a ≤ d) (f : E → F)
    (hf : ContDiffOn ℝ a f {0}ᶜ) (hhom : ∀ t : ℝ, 0 < t → ∀ x, f (t • x) = t ^ d • f x) :
    ∃ C : ℝ, ∀ x ≠ 0, ‖iteratedFDeriv ℝ a f x‖ ≤ C * ‖x‖ ^ (d - a) := by
  have hopen : IsOpen ({0}ᶜ : Set E) := isOpen_compl_singleton
  have hcont : ContinuousOn (iteratedFDeriv ℝ a f) {0}ᶜ := by
    have h1 := hf.continuousOn_iteratedFDerivWithin le_rfl hopen.uniqueDiffOn
    exact h1.congr fun x hx => (iteratedFDerivWithin_of_isOpen a hopen hx).symm
  have hsph : Metric.sphere (0 : E) 1 ⊆ {0}ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at hx
    exact zero_ne_one hx
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn (hcont.mono hsph)
  refine ⟨M, fun x hx => ?_⟩
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  set t : ℝ := ‖x‖⁻¹ with ht_def
  have ht : 0 < t := inv_pos.2 hxn
  let e : E ≃L[ℝ] E := (LinearEquiv.smulOfNeZero ℝ E t ht.ne').toContinuousLinearEquiv
  have he : ∀ z, e z = t • z := fun z => rfl
  have hfe : f ∘ e = t ^ d • f := by
    funext z
    simp only [Function.comp_apply, he, Pi.smul_apply]
    exact hhom t ht z
  have hcomp : iteratedFDeriv ℝ a (f ∘ e) x =
      (iteratedFDeriv ℝ a f (e x)).compContinuousLinearMap fun _ => (e : E →L[ℝ] E) := by
    have := e.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (Set.mem_univ (e x)) a
    simpa [iteratedFDerivWithin_univ] using this
  have hxa : ContDiffAt ℝ a f x := hf.contDiffAt (hopen.mem_nhds hx)
  have hsm : iteratedFDeriv ℝ a (t ^ d • f) x = t ^ d • iteratedFDeriv ℝ a f x :=
    iteratedFDeriv_const_smul_apply hxa
  have hex : e x ∈ Metric.sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos ht, ht_def,
      inv_mul_cancel₀ hxn.ne']
  have hnorm_e : ‖(e : E →L[ℝ] E)‖ ≤ t := by
    refine ContinuousLinearMap.opNorm_le_bound _ ht.le fun z => ?_
    rw [ContinuousLinearEquiv.coe_coe, he, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have key : t ^ d * ‖iteratedFDeriv ℝ a f x‖ ≤ M * t ^ a := by
    have h2 : ‖iteratedFDeriv ℝ a (f ∘ e) x‖ ≤ M * t ^ a := by
      rw [hcomp]
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hM' := hM (e x) hex
      have hM0 : 0 ≤ M := (norm_nonneg _).trans hM'
      exact mul_le_mul hM' (pow_le_pow_left₀ (norm_nonneg _) hnorm_e a) (by positivity) hM0
    rw [hfe, hsm, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos ht d)] at h2
    exact h2
  have hsplit : ‖x‖ ^ d = ‖x‖ ^ (d - a) * ‖x‖ ^ a := by
    rw [← pow_add, Nat.sub_add_cancel ha]
  have htx : ‖x‖ * t = 1 := by rw [ht_def, mul_inv_cancel₀ hxn.ne']
  calc ‖iteratedFDeriv ℝ a f x‖ = ‖x‖ ^ d * (t ^ d * ‖iteratedFDeriv ℝ a f x‖) := by
        rw [← mul_assoc, ← mul_pow, htx, one_pow, one_mul]
    _ ≤ ‖x‖ ^ d * (M * t ^ a) := mul_le_mul_of_nonneg_left key (by positivity)
    _ = M * ‖x‖ ^ (d - a) * (‖x‖ * t) ^ a := by rw [hsplit, mul_pow]; ring
    _ = M * ‖x‖ ^ (d - a) := by rw [htx, one_pow, mul_one]

theorem contDiff_of_homogeneous (n : ℕ) (f : E → F) (hf : ContDiffOn ℝ n f {0}ᶜ) (h0 : f 0 = 0)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, f (t • x) = t ^ (n + 1) • f x) : ContDiff ℝ n f := by
  refine contDiff_of_bounds_off_zero n f hf h0 fun a ha => ?_
  exact norm_iteratedFDeriv_le_of_homogeneous (n + 1) a (by omega) f
    (hf.of_le (by exact_mod_cast ha)) hhom

theorem homogeneousPower_contDiff (m : ℕ) :
    ContDiff ℝ 3 (fun z : ℂ => (‖z‖ ^ 4) • (‖z‖⁻¹ • z) ^ m) := by
  have h := contDiff_of_homogeneous 3 (fun z : ℂ => (‖z‖ ^ 4) • (‖z‖⁻¹ • z) ^ m) ?_ ?_ ?_
  · exact_mod_cast h
  · intro z hz
    have hz' : z ≠ 0 := hz
    exact (((contDiffAt_norm ℝ hz').pow 4).smul ((((contDiffAt_norm ℝ hz').inv
      (norm_ne_zero_iff.2 hz')).smul contDiffAt_id).pow m)).contDiffWithinAt
  · simp
  · intro t ht z
    have hn : ‖t • z‖ = t * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have hu : (t * ‖z‖)⁻¹ • (t • z) = ‖z‖⁻¹ • z := by
      rw [smul_smul, mul_inv, mul_comm t⁻¹, mul_assoc, inv_mul_cancel₀ ht.ne', mul_one]
    rw [hn, hu, mul_pow, smul_smul]

theorem planeCoord_contDiff :
    ContDiff ℝ 3 (fun y : Space => ((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I) := by
  have h0 : ContDiff ℝ 3 (fun y : Space => y 0) := contDiff_euclidean.1 contDiff_id 0
  have h1 : ContDiff ℝ 3 (fun y : Space => y 1) := contDiff_euclidean.1 contDiff_id 1
  exact (Complex.ofRealCLM.contDiff.comp h0).add
    ((Complex.ofRealCLM.contDiff.comp h1).mul contDiff_const)

theorem angularFactor_eq (m : ℕ) (y : Space) (hy : y ≠ 0) :
    axisFactor (heightRatio y) * Complex.exp (((((m : ℤ) : ℝ) * pointAngle y : ℝ) : ℂ) * Complex.I) =
      (‖y‖ ^ 4)⁻¹ • ((‖((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I‖ ^ 4) •
        (‖((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I‖⁻¹ •
          (((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I)) ^ m) := by
  set ζ : ℂ := ((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I with hζ
  have hr0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have hr2 : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [Real.norm_eq_abs, sq_abs]
  have hρ2 : ‖ζ‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    rw [Complex.sq_norm, hζ, Complex.normSq_add_mul_I]
  have hq1 : 1 - (y 2 / ‖y‖) ^ 2 = ‖ζ‖ ^ 2 / ‖y‖ ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hr0), sub_mul, div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hr0),
      one_mul, hρ2, hr2]
    ring
  have hq : axisFactor (heightRatio y) = (((‖y‖ ^ 4)⁻¹ * ‖ζ‖ ^ 4 : ℝ) : ℂ) := by
    unfold axisFactor heightRatio
    rw [hq1]
    congr 1
    ring
  have hφ : pointAngle y = Complex.arg ζ := rfl
  rw [hq, hφ]
  by_cases hz : ζ = 0
  · rw [hz]
    simp
  · have hexp : Complex.exp (((((m : ℤ) : ℝ) * Complex.arg ζ : ℝ) : ℂ) * Complex.I) =
        (‖ζ‖⁻¹ • ζ) ^ m := by
      have h1 : (((((m : ℤ) : ℝ) * Complex.arg ζ : ℝ) : ℂ) * Complex.I) =
          (m : ℂ) * ((Complex.arg ζ : ℂ) * Complex.I) := by
        push_cast
        ring
      rw [h1, Complex.exp_nat_mul]
      congr 1
      have h2 := Complex.norm_mul_exp_arg_mul_I ζ
      have hn : (‖ζ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
      rw [Complex.real_smul]
      push_cast
      rw [eq_inv_mul_iff_mul_eq₀ hn, h2]
    rw [hexp]
    simp only [Complex.real_smul]
    push_cast
    ring

end Internal

theorem angularFactor_contDiffAt (k : ℤ) {y : Space} (hy : y ≠ 0) :
    ContDiffAt ℝ 3 (fun y : Space =>
      axisFactor (heightRatio y) * Complex.exp ((((k : ℝ) * pointAngle y : ℝ) : ℂ) * Complex.I)) y := by
  have hnat : ∀ m : ℕ, ContDiffAt ℝ 3 (fun y : Space =>
      axisFactor (heightRatio y) * Complex.exp (((((m : ℤ) : ℝ) * pointAngle y : ℝ) : ℂ) * Complex.I)) y := by
    intro m
    have hG := (Internal.homogeneousPower_contDiff m).comp Internal.planeCoord_contDiff
    have hF : ContDiffAt ℝ 3 (fun y : Space => (‖y‖ ^ 4)⁻¹ •
        ((fun z : ℂ => (‖z‖ ^ 4) • (‖z‖⁻¹ • z) ^ m) ∘
          (fun y : Space => ((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I)) y) y :=
      (((contDiffAt_norm ℝ hy).pow 4).inv (pow_ne_zero 4 (norm_ne_zero_iff.2 hy))).smul hG.contDiffAt
    refine hF.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hy] with z hz
    exact Internal.angularFactor_eq m z hz
  cases k with
  | ofNat m => exact hnat m
  | negSucc m =>
    have h := ((Complex.conjLIE.toContinuousLinearEquiv : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffAt
      y (hnat (m + 1))
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
    simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, Complex.conjLIE_apply, map_mul]
    rw [← Complex.exp_conj]
    unfold axisFactor
    rw [Complex.conj_ofReal, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 2
    push_cast
    ring

theorem angularFactor_contDiffOn (k : ℤ) :
    ContDiffOn ℝ 3 (fun y : Space =>
      axisFactor (heightRatio y) * Complex.exp ((((k : ℝ) * pointAngle y : ℝ) : ℂ) * Complex.I)) {0}ᶜ :=
  fun _ hy => (angularFactor_contDiffAt k hy).contDiffWithinAt

theorem angularFactor_axis (k : ℤ) (y : Space) (hy : y ≠ 0) (h0 : y 0 = 0) (h1 : y 1 = 0) :
    axisFactor (heightRatio y) * Complex.exp ((((k : ℝ) * pointAngle y : ℝ) : ℂ) * Complex.I) = 0 := by
  have hr0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have hr2 : ‖y‖ ^ 2 = y 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [Real.norm_eq_abs, sq_abs, h0, h1]
  have hq : 1 - heightRatio y ^ 2 = 0 := by
    unfold heightRatio
    rw [div_pow, ← hr2, div_self (pow_ne_zero 2 hr0), sub_self]
  unfold axisFactor
  rw [hq]
  simp

end GivenShape

end CertCell

end Breakdown
