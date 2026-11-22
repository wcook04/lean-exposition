import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import PhyslibAlpha.ClassicalMechanics.CoupledSpringPotential

/-- The coupled spring potential plus the cubic `x₀³`. -/
noncomputable def cubicPerturbation (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  couplingPotential x + (x 0) ^ 3

/-- The cubic `x₀³` has zero second derivative at the origin. -/
lemma cube_iteratedFDeriv_two_zero (a b : EuclideanSpace ℝ (Fin 2)) :
    iteratedFDeriv ℝ 2 (fun x : EuclideanSpace ℝ (Fin 2) => (x 0) ^ 3) 0 ![a, b] = 0 := by
  have hcomp : (fun x : EuclideanSpace ℝ (Fin 2) => (x 0) ^ 3)
      = (fun t : ℝ => t ^ 3) ∘ (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) := rfl
  have hcd : ContDiff ℝ ⊤ (fun t : ℝ => t ^ 3) := contDiff_id.pow 3
  rw [hcomp, (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).iteratedFDeriv_comp_right hcd _ le_top]
  simp [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_pow]

/-- At the origin the second derivative of the perturbed potential is that of the coupled
spring potential. -/
lemma cubicPerturbation_iteratedFDeriv_two_zero (a b : EuclideanSpace ℝ (Fin 2)) :
    iteratedFDeriv ℝ 2 cubicPerturbation 0 ![a, b]
      = iteratedFDeriv ℝ 2 couplingPotential 0 ![a, b] := by
  have hU : ContDiffAt ℝ 2 couplingPotential (0 : EuclideanSpace ℝ (Fin 2)) :=
    (couplingPotential_analyticAt 0).contDiffAt
  have hg : ContDiffAt ℝ 2 (fun x : EuclideanSpace ℝ (Fin 2) => (x 0) ^ 3) 0 :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.pow 3).contDiffAt
  have hsplit : cubicPerturbation
      = couplingPotential + fun x : EuclideanSpace ℝ (Fin 2) => (x 0) ^ 3 := rfl
  rw [hsplit, iteratedFDeriv_add_apply hU hg]
  simp [cube_iteratedFDeriv_two_zero]

/-- The perturbed potential is analytic at every point. -/
lemma cubicPerturbation_analyticAt (z : EuclideanSpace ℝ (Fin 2)) :
    AnalyticAt ℝ cubicPerturbation z := by
  have h0 : AnalyticAt ℝ (fun x : EuclideanSpace ℝ (Fin 2) => x 0) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) 0).analyticAt z
  show AnalyticAt ℝ (fun x => couplingPotential x + (x 0) ^ 3) z
  exact (couplingPotential_analyticAt z).add (h0.pow 3)

/-- The gradient of the perturbed potential vanishes at the origin. -/
lemma cubicPerturbation_gradient_zero :
    gradient cubicPerturbation (0 : EuclideanSpace ℝ (Fin 2)) = 0 := by
  have h0 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 2) => x 0)
      (EuclideanSpace.proj (𝕜 := ℝ) 0) (0 : EuclideanSpace ℝ (Fin 2)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) 0).hasFDerivAt
  have hz : ∀ i : Fin 2, (0 : EuclideanSpace ℝ (Fin 2)) i = 0 := fun i => rfl
  have hzero : HasFDerivAt cubicPerturbation (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) 0 := by
    refine ((couplingPotential_hasFDerivAt 0).add (h0.pow 3)).congr_fderiv ?_
    simp only [hz]
    simp
  simp [gradient, hzero.fderiv]

/-- The second-derivative quadratic map of the perturbed potential is positive definite at
the origin. -/
lemma cubicPerturbation_posDef :
    (iteratedFDerivQuadraticMap cubicPerturbation (0 : EuclideanSpace ℝ (Fin 2))).PosDef := by
  intro y hy
  have h0 : (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) = 0 := by
    ext i
    fin_cases i <;> simp
  have hU := couplingPotential_posDef y hy
  rw [h0] at hU
  show 0 < iteratedFDeriv ℝ 2 cubicPerturbation 0 ![y, y]
  rw [cubicPerturbation_iteratedFDeriv_two_zero]
  exact hU

/-- Adding `x₀³` keeps a local minimum at the origin. The proof applies the analytic
second-derivative test from PhyslibAlpha, the test that proves the original theorem. -/
theorem cubicPerturbation_isLocalMin :
    IsLocalMin cubicPerturbation (0 : EuclideanSpace ℝ (Fin 2)) :=
  second_derivative_test_analyticAt cubicPerturbation_gradient_zero
    (cubicPerturbation_analyticAt 0) cubicPerturbation_posDef

/-- Near the origin the minimum is strict: if `|x₀| < 1/4` and `x ≠ 0`, the perturbed
potential is positive, because it is at least `(x₁ + x₀/2)² + x₀²/2`. -/
theorem cubicPerturbation_strict_near_origin :
    ∀ᶠ x in nhds (0 : EuclideanSpace ℝ (Fin 2)),
      x ≠ 0 → cubicPerturbation 0 < cubicPerturbation x := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin 2) => x 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous
  have ht : Filter.Tendsto (fun x : EuclideanSpace ℝ (Fin 2) => x 0) (nhds 0) (nhds 0) := by
    simpa using hc.tendsto (0 : EuclideanSpace ℝ (Fin 2))
  have hnear : ∀ᶠ x in nhds (0 : EuclideanSpace ℝ (Fin 2)), |x 0| < 1 / 4 := by
    filter_upwards [ht.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4))]
      with x hx
    simpa [Metric.mem_ball, Real.dist_eq] using hx
  filter_upwards [hnear] with x hx hne
  have hW0 : cubicPerturbation (0 : EuclideanSpace ℝ (Fin 2)) = 0 := by
    simp [cubicPerturbation, couplingPotential]
  rw [hW0]
  have hlo : -(1 / 4 : ℝ) < x 0 := (abs_lt.mp hx).1
  have hprod : 0 ≤ (x 0) ^ 2 * (x 0 + 1 / 4) := mul_nonneg (sq_nonneg _) (by linarith)
  have hbound : (x 1 + x 0 / 2) ^ 2 + (x 0) ^ 2 / 2 ≤ cubicPerturbation x := by
    unfold cubicPerturbation couplingPotential
    nlinarith [hprod]
  by_contra hlt
  have hle : cubicPerturbation x ≤ 0 := not_lt.mp hlt
  have hs : 0 ≤ (x 1 + x 0 / 2) ^ 2 := sq_nonneg _
  have h0 : x 0 = 0 := by
    have h0sq : (x 0) ^ 2 = 0 := by nlinarith [sq_nonneg (x 0)]
    exact (pow_eq_zero_iff two_ne_zero).mp h0sq
  have h1 : x 1 = 0 := by
    have h1sq : (x 1 + x 0 / 2) ^ 2 = 0 := by nlinarith [sq_nonneg (x 0)]
    have h1lin : x 1 + x 0 / 2 = 0 := (pow_eq_zero_iff two_ne_zero).mp h1sq
    linarith
  apply hne
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1

/-- The origin is not a global minimum after adding `x₀³`: the value at `(-2, 0)` is `-4`. -/
theorem cubicPerturbation_not_global :
    cubicPerturbation (!₂[-2, 0] : EuclideanSpace ℝ (Fin 2))
      < cubicPerturbation (0 : EuclideanSpace ℝ (Fin 2)) := by
  simp [cubicPerturbation, couplingPotential]
  norm_num
