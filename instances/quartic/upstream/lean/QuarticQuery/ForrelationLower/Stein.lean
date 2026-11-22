module

public import QuarticQuery.ForrelationLower.Cube

/-!
# The truncation and Stein's identity

Blueprint lemmas G1–G4. `Ψ = 1/(2q)`, `q = √(2+x²)`, and `φ = xΨ - Ψ'`, so that
`(Ψ · pdf)' = -φ · pdf`, which is Stein's identity.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MeasureTheory ProbabilityTheory Finset

namespace QuarticQuery.ForrelationLower

/-- `q(x) = √(2+x²)`. -/
noncomputable def qf (x : ℝ) : ℝ := Real.sqrt (2 + x ^ 2)
/-- `Ψ`. -/
noncomputable def psiS (x : ℝ) : ℝ := 1 / (2 * qf x)
/-- The truncation `φ`. -/
noncomputable def phiS (x : ℝ) : ℝ := x * (3 + x ^ 2) / (2 * qf x ^ 3)
/-- `φ'`. -/
noncomputable def dphi (x : ℝ) : ℝ := 3 / qf x ^ 5

/-- Support for blueprint G1–G4. -/
theorem qf_pos (x : ℝ) : 0 < qf x := Real.sqrt_pos.mpr (by positivity)
/-- Support for blueprint G1–G4. -/
theorem qf_sq (x : ℝ) : qf x ^ 2 = 2 + x ^ 2 := Real.sq_sqrt (by positivity)
/-- Support for blueprint G1–G4. -/
theorem one_le_qf (x : ℝ) : 1 ≤ qf x := by
  have := qf_pos x
  nlinarith [qf_sq x, sq_nonneg x]

/-- Support for blueprint G1–G4. -/
theorem hasDerivAt_sq (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
  simpa using hasDerivAt_pow 2 x

/-- Support for blueprint G1–G4. -/
theorem hasDerivAt_qf (x : ℝ) : HasDerivAt qf (x / qf x) x := by
  have h : HasDerivAt (fun y : ℝ => 2 + y ^ 2) (2 * x) x := (hasDerivAt_sq x).const_add 2
  have := h.sqrt (by positivity : (2 + x ^ 2) ≠ 0)
  have e : x / qf x = 2 * x / (2 * √(2 + x ^ 2)) := by
    have := qf_pos x
    unfold qf at *
    field_simp
  rw [e]
  exact this

/-- Support for blueprint G1–G4. -/
theorem continuous_qf : Continuous qf := by unfold qf; fun_prop
/-- Support for blueprint G1–G4. -/
theorem continuous_psiS : Continuous psiS :=
  continuous_const.div (continuous_const.mul continuous_qf) fun x => by
    have := qf_pos x; positivity
/-- Support for blueprint G1–G4. -/
theorem continuous_dphi : Continuous dphi :=
  continuous_const.div (continuous_qf.pow 5) fun x => by
    have := qf_pos x; positivity

/-- Support for blueprint G1–G4. -/
theorem hasDerivAt_psiS (x : ℝ) : HasDerivAt psiS (-x / (2 * qf x ^ 3)) x := by
  have hq := qf_pos x
  have h := ((hasDerivAt_qf x).const_mul 2).fun_inv (by positivity : 2 * qf x ≠ 0)
  have e : psiS = fun y => (2 * qf y)⁻¹ := by funext y; simp [psiS]
  rw [e]
  convert h using 1
  field_simp
  try ring

/-- Support for blueprint G1–G4. -/
theorem hasDerivAt_phiS (x : ℝ) : HasDerivAt phiS (dphi x) x := by
  have hq := qf_pos x
  have h4 : qf x ^ 2 = 2 + x ^ 2 := qf_sq x
  have hn := (hasDerivAt_id' x).fun_mul ((hasDerivAt_sq x).const_add 3)
  have h3q : HasDerivAt (fun y => qf y ^ 3) (3 * qf x * x) x := by
    have := (hasDerivAt_qf x).fun_pow 3
    convert this using 1
    field_simp
    try ring
  have hd := h3q.const_mul 2
  have h := hn.fun_div hd (by positivity)
  show HasDerivAt (fun y => y * (3 + y ^ 2) / (2 * qf y ^ 3)) _ x
  convert h using 1
  have num : (1 * (3 + x ^ 2) + x * (2 * x)) * (2 * qf x ^ 3) -
      x * (3 + x ^ 2) * (2 * (3 * qf x * x)) = 12 * qf x := by
    linear_combination (2 * qf x * (3 + 3 * x ^ 2)) * h4
  rw [num]
  unfold dphi
  field_simp
  try ring

/-- Support for blueprint G1–G4. -/
theorem abs_phiS_le (x : ℝ) : |phiS x| ≤ 1 / 2 := by
  have hq := qf_pos x
  have h4 : qf x ^ 2 = 2 + x ^ 2 := qf_sq x
  have h6 : qf x ^ 6 = (2 + x ^ 2) ^ 3 := by rw [← h4]; ring
  have key : (x * (3 + x ^ 2)) ^ 2 ≤ qf x ^ 6 := by
    rw [h6]; nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]
  have habs : |x * (3 + x ^ 2)| ≤ qf x ^ 3 := by
    apply abs_le_of_sq_le_sq' ?_ (by positivity) |> fun h => abs_le.mpr h
    calc _ ≤ qf x ^ 6 := key
      _ = _ := by ring
  unfold phiS
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * qf x ^ 3), div_le_iff₀ (by positivity)]
  linarith

/-- Support for blueprint G1–G4. -/
theorem phiS_neg (x : ℝ) : phiS (-x) = - phiS x := by
  simp [phiS, qf]; ring

/-- Support for blueprint G1–G4. -/
theorem psiS_pos (x : ℝ) : 0 < psiS x := by
  have := qf_pos x; unfold psiS; positivity
/-- Support for blueprint G1–G4. -/
theorem psiS_le (x : ℝ) : psiS x ≤ 1 := by
  have := one_le_qf x
  unfold psiS
  rw [div_le_one (by linarith)]
  linarith
/-- Support for blueprint G1–G4. -/
theorem dphi_pos (x : ℝ) : 0 < dphi x := by
  have := qf_pos x; unfold dphi; positivity
/-- Support for blueprint G1–G4. -/
theorem dphi_le (x : ℝ) : dphi x ≤ 3 := by
  have h := one_le_qf x
  unfold dphi
  rw [div_le_iff₀ (by positivity)]
  have : 1 ≤ qf x ^ 5 := one_le_pow₀ h
  linarith

/-- The sharp product bound for one edge of the Gaussian chain. -/
theorem psi_dphi_le_sharp (x y : ℝ) : psiS x * dphi y ≤ 3 / 16 := by
  have hx := qf_pos x
  have hy := qf_pos y
  have hxy : 2 ≤ qf x * qf y := by
    have hsq : 4 ≤ (qf x * qf y) ^ 2 := by
      rw [mul_pow, qf_sq, qf_sq]
      nlinarith [sq_nonneg x, sq_nonneg y, mul_nonneg (sq_nonneg x) (sq_nonneg y)]
    nlinarith [mul_pos hx hy]
  have hy4 : 4 ≤ qf y ^ 4 := by
    have h2 := qf_sq y
    nlinarith [sq_nonneg y, sq_nonneg (qf y ^ 2 - 2)]
  have hden : 16 ≤ 2 * qf x * qf y ^ 5 := by
    have := mul_le_mul hxy hy4 (by norm_num) (by positivity : 0 ≤ qf x * qf y)
    nlinarith [show (qf x * qf y) * qf y ^ 4 = qf x * qf y ^ 5 by ring]
  unfold psiS dphi
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- The product bound is attained when both Gaussian coordinates vanish. -/
theorem psi_dphi_eq_sharp_at_zero : psiS 0 * dphi 0 = 3 / 16 := by
  have hq := qf_sq 0
  have hp := qf_pos 0
  have h6 : qf 0 ^ 6 = 8 := by
    calc qf 0 ^ 6 = (qf 0 ^ 2) ^ 3 := by ring
      _ = 8 := by rw [qf_sq]; norm_num
  unfold psiS dphi
  field_simp
  nlinarith [h6]

/-- Stein in one variable. -/
theorem stein_one {g g' : ℝ → ℝ} {C C' : ℝ} (hg : Continuous g) (hg' : Continuous g')
    (hb : ∀ x, |g x| ≤ C) (hb' : ∀ x, |g' x| ≤ C') (hd : ∀ x, HasDerivAt g (g' x) x) :
    ∫ x, phiS x * g x ∂(gaussianReal 0 1) = ∫ x, psiS x * g' x ∂(gaussianReal 0 1) := by
  set c : ℝ := (√(2 * Real.pi * ((1 : NNReal) : ℝ)))⁻¹ with hcc
  set P : ℝ → ℝ := fun y => c * Real.exp (-y ^ 2 / 2) with hP
  have hPe : gaussianPDFReal 0 1 = P := by
    funext y; simp [hP, hcc, gaussianPDFReal]
  have hPd : ∀ x, HasDerivAt P (-x * P x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
      have := (hasDerivAt_sq x).fun_neg.div_const 2
      convert this using 1
      ring
    have h2 := h1.exp.const_mul c
    convert h2 using 1
    simp only [hP]
    ring
  have hPi : Integrable P := by rw [← hPe]; exact integrable_gaussianPDFReal 0 1
  have hF : ∀ x, HasDerivAt (fun y => psiS y * g y * P y)
      ((psiS x * g' x - phiS x * g x) * P x) x := by
    intro x
    have := ((hasDerivAt_psiS x).fun_mul (hd x)).fun_mul (hPd x)
    convert this using 1
    have hq := qf_pos x
    have h4 : qf x ^ 2 = 2 + x ^ 2 := qf_sq x
    have e : phiS x = x * psiS x + x / (2 * qf x ^ 3) := by
      unfold phiS psiS
      field_simp
      linear_combination (-x) * h4
    rw [e]
    ring
  have hi1 : Integrable fun x => psiS x * g' x * P x := by
    refine hPi.bdd_mul (c := C') ((continuous_psiS.mul hg').aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (psiS_pos x)]
    have := hb' x
    have := psiS_le x
    have := psiS_pos x
    nlinarith [abs_nonneg (g' x)]
  have hcphi : Continuous phiS := continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_phiS x).continuousAt
  have hi2 : Integrable fun x => phiS x * g x * P x := by
    refine hPi.bdd_mul (c := C) ((hcphi.mul hg).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have := hb x
    have := abs_phiS_le x
    nlinarith [abs_nonneg (g x), abs_nonneg (phiS x)]
  have hi3 : Integrable fun x => psiS x * g x * P x := by
    refine hPi.bdd_mul (c := C) ((continuous_psiS.mul hg).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (psiS_pos x)]
    have := hb x
    have := psiS_le x
    have := psiS_pos x
    nlinarith [abs_nonneg (g x)]
  have hi4 : Integrable fun x => (psiS x * g' x - phiS x * g x) * P x := by
    refine (hi1.sub hi2).congr (.of_forall fun x => ?_)
    simp [sub_mul]
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hF hi4 hi3
  have h1 : ∫ x, psiS x * g' x * P x - phiS x * g x * P x = 0 := by
    rw [← h0]; exact integral_congr_ae (.of_forall fun x => by simp only [sub_mul])
  rw [integral_sub hi1 hi2, sub_eq_zero] at h1
  rw [integral_gaussianReal_eq_integral_smul (by norm_num),
    integral_gaussianReal_eq_integral_smul (by norm_num), hPe]
  simp only [smul_eq_mul]
  calc _ = ∫ x, phiS x * g x * P x := integral_congr_ae (.of_forall fun x => by simp only []; ring)
    _ = _ := h1.symm
    _ = _ := integral_congr_ae (.of_forall fun x => by simp only []; ring)

/-! ## Product Gaussians -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The product Gaussian. -/
noncomputable def gP (ι : Type) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

instance : IsProbabilityMeasure (gP ι) := by unfold gP; infer_instance

/-- Support for blueprint G1–G4. -/
theorem measurable_update_pair (i : ι) :
    Measurable fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2 := by
  refine measurable_pi_iff.mpr fun j => ?_
  by_cases h : j = i
  · subst h
    simp only [Function.update_self]
    exact measurable_snd
  · simp only [Function.update_of_ne h]
    exact (measurable_pi_apply j).comp measurable_fst

/-- Resampling one coordinate preserves the product Gaussian. -/
theorem map_update_gP (i : ι) :
    ((gP ι).prod (gaussianReal 0 1)).map (fun p => Function.update p.1 i p.2) = gP ι := by
  unfold gP
  refine (Measure.pi_eq (μ := fun _ : ι => gaussianReal 0 1) fun s hs => ?_).symm
  rw [Measure.map_apply (measurable_update_pair i) (MeasurableSet.univ_pi hs)]
  have e : (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹' Set.univ.pi s =
      (Set.univ.pi fun j => if j = i then Set.univ else s j) ×ˢ s i := by
    ext ⟨u, t⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · simp [hj]
      · simpa [hj, Function.update_of_ne hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · simpa [hj, Function.update_of_ne hj] using h1 j
  rw [e, Measure.prod_prod, Measure.pi_pi]
  have h1 : ∏ j, (gaussianReal 0 1) (if j = i then Set.univ else s j) =
      ∏ j ∈ univ.erase i, (gaussianReal 0 1) (s j) := by
    rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
    simp only [if_true, measure_univ, one_mul]
    exact prod_congr rfl fun j hj => by simp [ne_of_mem_erase hj]
  rw [h1, ← Finset.mul_prod_erase univ (fun j => (gaussianReal 0 1) (s j)) (mem_univ i), mul_comm]

/-- Bounded measurable functions integrate slice by slice. -/
theorem integral_slice {F : (ι → ℝ) → ℝ} (hF : Measurable F) {C : ℝ} (hb : ∀ u, |F u| ≤ C)
    (i : ι) : ∫ u, F u ∂(gP ι) =
      ∫ u, ∫ t, F (Function.update u i t) ∂(gaussianReal 0 1) ∂(gP ι) := by
  have hm := measurable_update_pair (ι := ι) i
  conv_lhs => rw [← map_update_gP i]
  rw [integral_map hm.aemeasurable hF.aestronglyMeasurable]
  refine integral_prod _ ?_
  refine Integrable.of_bound (hF.comp hm).aestronglyMeasurable C (.of_forall fun p => ?_)
  simpa using hb _

/-- G3. Stein's identity in one coordinate of the product Gaussian. -/
theorem stein_pi (i : ι) {G G' : (ι → ℝ) → ℝ} {C C' : ℝ} (hG : Continuous G) (hG' : Continuous G')
    (hb : ∀ u, |G u| ≤ C) (hb' : ∀ u, |G' u| ≤ C')
    (hd : ∀ u t, HasDerivAt (fun s => G (Function.update u i s)) (G' (Function.update u i t)) t) :
    ∫ u, phiS (u i) * G u ∂(gP ι) = ∫ u, psiS (u i) * G' u ∂(gP ι) := by
  have hcphi : Continuous phiS := continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_phiS x).continuousAt
  have hc1 : Continuous fun u : ι → ℝ => phiS (u i) * G u :=
    (hcphi.comp (continuous_apply i)).mul hG
  have hc2 : Continuous fun u : ι → ℝ => psiS (u i) * G' u :=
    (continuous_psiS.comp (continuous_apply i)).mul hG'
  have hupd : ∀ u : ι → ℝ, Continuous fun t : ℝ => Function.update u i t := fun u =>
    continuous_const.update i continuous_id
  rw [integral_slice hc1.measurable (C := C) (fun u => ?_) i,
    integral_slice hc2.measurable (C := C') (fun u => ?_) i]
  · refine integral_congr_ae (.of_forall fun u => ?_)
    simp only [Function.update_self]
    exact stein_one (hG.comp (hupd u)) (hG'.comp (hupd u)) (fun x => hb _) (fun x => hb' _)
      (hd u)
  · rw [abs_mul, abs_of_pos (psiS_pos _)]
    have := hb' u
    have := psiS_le (u i)
    have := psiS_pos (u i)
    nlinarith [abs_nonneg (G' u)]
  · rw [abs_mul]
    have := hb u
    have := abs_phiS_le (u i)
    nlinarith [abs_nonneg (G u), abs_nonneg (phiS (u i))]

/-! ## Reflections and second moments -/

open scoped InnerProductSpace

/-- Support for blueprint G1–G4. -/
theorem map_toLp_gP :
    (gP ι).map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ ι) :=
  map_pi_eq_stdGaussian

/-- G4. A reflection preserves the product Gaussian. -/
theorem integral_reflect (e : ι → ℝ) (he : ∑ i, e i ^ 2 = 1) {F : (ι → ℝ) → ℝ}
    (hF : Measurable F) :
    ∫ u, F (fun i => u i - 2 * (∑ j, e j * u j) * e i) ∂(gP ι) = ∫ u, F u ∂(gP ι) := by
  set E := EuclideanSpace ℝ ι
  set v : E := WithLp.toLp 2 e with hv
  have hnv : ‖v‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [hv] using he
  have hnv1 : ‖v‖ = 1 := by nlinarith [norm_nonneg v, sq_nonneg (‖v‖ - 1), sq_nonneg (‖v‖ + 1)]
  let R : E ≃ₗᵢ[ℝ] E := (Submodule.span ℝ {v})ᗮ.reflection
  have hin : ∀ u : ι → ℝ, ⟪v, WithLp.toLp 2 u⟫_ℝ = ∑ j, e j * u j := by
    intro u
    simp only [hv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    exact sum_congr rfl fun j _ => mul_comm _ _
  have hR : ∀ u : ι → ℝ, (R (WithLp.toLp 2 u)).ofLp =
      fun i => u i - 2 * (∑ j, e j * u j) * e i := by
    intro u
    have h1 : R (WithLp.toLp 2 u) =
        WithLp.toLp 2 u - (2 * ⟪v, WithLp.toLp 2 u⟫_ℝ) • v := by
      simp only [R]
      rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply, hnv1]
      simp only [one_pow, div_one, neg_sub, mul_smul, two_smul]
      simp
    rw [h1, hin]
    funext i
    rw [hv]
    rfl
  let G : E → ℝ := fun x => F x.ofLp
  have hG : Measurable G := hF.comp (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurable
  have hmR : Measurable R := R.continuous.measurable
  have hmL : Measurable (WithLp.toLp 2 : (ι → ℝ) → E) :=
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable
  have h1 : ∫ x, G x ∂(stdGaussian E) = ∫ u, F u ∂(gP ι) := by
    rw [← map_toLp_gP]
    exact integral_map hmL.aemeasurable hG.aestronglyMeasurable
  have h2 : ∫ x, G (R x) ∂(stdGaussian E) =
      ∫ u, F (fun i => u i - 2 * (∑ j, e j * u j) * e i) ∂(gP ι) := by
    rw [← map_toLp_gP, integral_map hmL.aemeasurable
      (f := fun x => G (R x)) (hG.comp hmR).aestronglyMeasurable]
    exact integral_congr_ae (.of_forall fun u => by simp only [G, hR])
  have h3 : ∫ x, G x ∂((stdGaussian E).map R) = ∫ x, G (R x) ∂(stdGaussian E) :=
    integral_map hmR.aemeasurable hG.aestronglyMeasurable
  rw [stdGaussian_map R] at h3
  rw [← h2, ← h3, h1]

/-- The square of a linear form is integrable. -/
theorem integrable_dot_sq (e : ι → ℝ) :
    Integrable (fun u : ι → ℝ => (∑ j, e j * u j) ^ 2) (gP ι) := by
  set E := EuclideanSpace ℝ ι
  set v : E := WithLp.toLp 2 e with hv
  let L : StrongDual ℝ E := innerSL ℝ v
  have hmL : Measurable (WithLp.toLp 2 : (ι → ℝ) → E) :=
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable
  have h1 : MemLp L 2 (stdGaussian E) :=
    L.comp_memLp' (IsGaussian.memLp_two_id (μ := stdGaussian E))
  have h2 : Integrable (fun x => L x ^ 2) ((gP ι).map (WithLp.toLp 2)) := by
    rw [map_toLp_gP]; exact h1.integrable_sq
  have h3 := h2.comp_measurable hmL
  refine h3.congr (.of_forall fun u => ?_)
  simp only [Function.comp, L, innerSL_apply_apply, hv, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial]
  congr 1
  exact sum_congr rfl fun j _ => mul_comm _ _

/-- G4. A unit linear form has variance one. -/
theorem integral_dot_sq (e : ι → ℝ) (he : ∑ i, e i ^ 2 = 1) :
    ∫ u, (∑ j, e j * u j) ^ 2 ∂(gP ι) = 1 := by
  set E := EuclideanSpace ℝ ι
  set v : E := WithLp.toLp 2 e with hv
  have hnv : ‖v‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [hv] using he
  let L : StrongDual ℝ E := innerSL ℝ v
  have hmL : Measurable (WithLp.toLp 2 : (ι → ℝ) → E) :=
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable
  have hm : ∫ x, L x ∂(stdGaussian E) = 0 := integral_strongDual_stdGaussian L
  have hvar := variance_dual_stdGaussian L
  rw [variance_of_integral_eq_zero L.continuous.aemeasurable hm] at hvar
  have hL : ‖L‖ = ‖v‖ := by simp [L]
  rw [hL, hnv] at hvar
  rw [← hvar, ← map_toLp_gP, integral_map hmL.aemeasurable
    (f := fun x => L x ^ 2) (by fun_prop)]
  refine integral_congr_ae (.of_forall fun u => ?_)
  simp only [L, innerSL_apply_apply, hv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  congr 1
  exact sum_congr rfl fun j _ => mul_comm _ _

end QuarticQuery.ForrelationLower
