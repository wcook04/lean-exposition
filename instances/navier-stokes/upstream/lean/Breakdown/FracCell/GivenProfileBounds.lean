import Breakdown.FracCell.GivenProfileDefs
import Breakdown.FracCell.GivenProfileBoundsField

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracCellInternal

open CellCert.GivenFields SteadyCert

private theorem ofComponents_eq (w : Fin 3 → ℝ) :
    ofComponents w = ∑ i : Fin 3, w i • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  fin_cases j <;> simp [ofComponents, Fin.sum_univ_three]

private theorem reducedField_diff (P : ChartParams) (F : FieldData) (n : ℤ) (t x : ℝ) (c : Fin 3) :
    Differentiable ℝ (fun β : ℝ => reducedField P F n β t x c) := by
  unfold reducedField twistedScale
  by_cases hn : n = 0
  · simp only [hn, if_true]
    fin_cases c <;> simp
  · simp only [hn, if_false]
    fin_cases c <;> simp <;> fun_prop

theorem fieldOf_phase_differentiable (P : ChartParams) (F : FieldData) (y : Space) :
    Differentiable ℝ (fun β : ℝ => fieldOf P F β y) := by
  unfold fieldOf
  simp only [ofComponents_eq]
  refine Differentiable.fun_sum (fun i _ => ?_)
  apply Differentiable.smul_const
  have hre : ∀ g : ℝ → ℂ, Differentiable ℝ g → Differentiable ℝ (fun β => (g β).re) :=
    fun g hg => Complex.reCLM.differentiable.comp hg
  apply hre
  have h : ∀ n c, Differentiable ℝ (fun β : ℝ => reducedField P F n β (chartT P y) (heightRatio y) c) :=
    fun n c => reducedField_diff P F n _ _ c
  unfold modePhase
  fun_prop

theorem fieldOf_phaseDeriv (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (β₀ : ℝ) :
    ∃ G : Space → Space, (∀ y, HasDerivAt (fun β => fieldOf P F β y) (G y) β₀) ∧
      ContDiff ℝ 1 G ∧ (∀ y, divergenceAt G y = 0) ∧
        ∃ C : ℝ, ∀ y, ‖G y‖ ≤ C * (1 + ‖y‖)⁻¹ ∧ ‖fderiv ℝ G y‖ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ) :=
  ⟨fun y => deriv (fun β => fieldOf P F β y) β₀,
    fun y => (fieldOf_phase_differentiable P F y β₀).hasDerivAt,
    fieldOf_phaseDeriv_regular P hP F hF β₀⟩

private theorem phase_bound {k : ℕ} (D : ProfileData k) (R : Fin k → ℝ) :
    ∃ B : ℝ, ∀ p ∈ box R, |D.phase p| ≤ B := by
  refine ⟨|2 * D.power * (D.chart.m : ℝ)| * (|D.baseRate| + ∑ j, |D.rateSlope j| * |R j|), ?_⟩
  intro p hp
  have hp' : ∀ i, |p i| ≤ R i := hp
  unfold ProfileData.phase ProfileData.rate
  rw [abs_neg, abs_mul]
  gcongr
  calc |D.baseRate + ∑ j, D.rateSlope j * p j| ≤ |D.baseRate| + |∑ j, D.rateSlope j * p j| :=
        abs_add_le _ _
    _ ≤ |D.baseRate| + ∑ j, |D.rateSlope j * p j| := by
        gcongr; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ |D.baseRate| + ∑ j, |D.rateSlope j| * |R j| := by
        gcongr with j
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ((hp' j).trans (le_abs_self _)) (abs_nonneg _)

private theorem monomial_bound {k : ℕ} (R : Fin k → ℝ) (p : Fin k → ℝ) (hp : p ∈ box R)
    (μ : Fin k → ℕ) : |ProfileData.monomialOf p μ| ≤ ∏ j, |R j| ^ μ j := by
  have hp' : ∀ i, |p i| ≤ R i := hp
  unfold ProfileData.monomialOf
  rw [Finset.abs_prod]
  apply Finset.prod_le_prod (fun j _ => abs_nonneg _)
  intro j _
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) ((hp' j).trans (le_abs_self _)) _

private theorem le_abs_mul {a c w : ℝ} (hw : 0 ≤ w) (h : a ≤ c * w) : a ≤ |c| * w :=
  h.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hw)

theorem profile_bounds_everywhere {k : ℕ} (D : ProfileData k) (hD : IsProfileData D)
    (R : Fin k → ℝ) :
    ∃ C : ℝ, ∀ p ∈ box R, ∀ y, ‖D.profile p y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧
      ‖fderiv ℝ (D.profile p) y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) ∧
        ‖D.second p y‖ ≤ C * (1 + ‖y‖) ^ (-(3 : ℝ)) := by
  obtain ⟨B, hB⟩ := phase_bound D R
  have hex : ∀ μ : Fin k → ℕ, ∃ C : ℝ, μ ∈ D.index → ∀ β : ℝ, |β| ≤ B →
      ContDiff ℝ 1 (fieldOf D.chart (D.part μ) β) ∧ ∀ y : Space,
        ‖fieldOf D.chart (D.part μ) β y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧
        ‖fderiv ℝ (fieldOf D.chart (D.part μ) β) y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) ∧
        LipschitzOnWith (Real.toNNReal (C * (1 + ‖y‖) ^ (-(3 : ℝ))))
          (fderiv ℝ (fieldOf D.chart (D.part μ) β)) (Metric.ball y 1) := by
    intro μ
    by_cases hμ : μ ∈ D.index
    · obtain ⟨C, hC⟩ := fieldOf_decay D.chart hD.chart (D.part μ) (hD.parts μ hμ) B
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h hμ⟩
  choose C hC using hex
  set M : (Fin k → ℕ) → ℝ := fun μ => ∏ j, |R j| ^ μ j with hM
  have hMnn : ∀ μ, 0 ≤ M μ := fun μ => Finset.prod_nonneg (fun j _ => pow_nonneg (abs_nonneg _) _)
  set K : ℝ := ∑ μ ∈ D.index, M μ * |C μ| with hK
  have hKnn : 0 ≤ K := Finset.sum_nonneg (fun μ _ => mul_nonneg (hMnn μ) (abs_nonneg _))
  refine ⟨K, ?_⟩
  intro p hp y
  have hβ := hB p hp
  have hmon : ∀ μ, |ProfileData.monomialOf p μ| ≤ M μ := fun μ => monomial_bound R p hp μ
  have key : ∀ (f : (Fin k → ℕ) → ℝ) (W : ℝ), 0 ≤ W → (∀ μ ∈ D.index, f μ ≤ |C μ| * W) →
      ∑ μ ∈ D.index, |ProfileData.monomialOf p μ| * f μ ≤ K * W := by
    intro f W hW hf
    rw [hK, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro μ hμ
    calc |ProfileData.monomialOf p μ| * f μ ≤ |ProfileData.monomialOf p μ| * (|C μ| * W) :=
          mul_le_mul_of_nonneg_left (hf μ hμ) (abs_nonneg _)
      _ ≤ M μ * (|C μ| * W) :=
          mul_le_mul_of_nonneg_right (hmon μ) (mul_nonneg (abs_nonneg _) hW)
      _ = M μ * |C μ| * W := by ring
  have hw : ∀ (z : Space) (e : ℝ), 0 < (1 + ‖z‖) ^ e := fun z e =>
    Real.rpow_pos_of_pos (by positivity) e
  have hdiff : ∀ μ ∈ D.index, Differentiable ℝ (fieldOf D.chart (D.part μ) (D.phase p)) :=
    fun μ hμ => ((hC μ hμ _ hβ).1).differentiable one_ne_zero
  have hfd : ∀ z, HasFDerivAt (D.profile p)
      (∑ μ ∈ D.index, ProfileData.monomialOf p μ •
        fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase p)) z) z := by
    intro z
    have hfun : D.profile p = ∑ μ ∈ D.index, ProfileData.monomialOf p μ •
        fieldOf D.chart (D.part μ) (D.phase p) := by
      funext w
      simp only [ProfileData.profile, Finset.sum_apply, Pi.smul_apply]
    rw [hfun]
    exact HasFDerivAt.sum (u := D.index)
      (fun μ hμ => ((hdiff μ hμ z).hasFDerivAt).const_smul (ProfileData.monomialOf p μ))
  have hgrad : fderiv ℝ (D.profile p) = fun z => ∑ μ ∈ D.index, ProfileData.monomialOf p μ •
      fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase p)) z := funext fun z => (hfd z).fderiv
  refine ⟨?_, ?_, ?_⟩
  · calc ‖D.profile p y‖ ≤ ∑ μ ∈ D.index,
          ‖ProfileData.monomialOf p μ • fieldOf D.chart (D.part μ) (D.phase p) y‖ := norm_sum_le _ _
      _ = ∑ μ ∈ D.index, |ProfileData.monomialOf p μ| *
          ‖fieldOf D.chart (D.part μ) (D.phase p) y‖ := by simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ K * (1 + ‖y‖) ^ (-(1 : ℝ)) :=
          key _ _ (hw y _).le (fun μ hμ => le_abs_mul (hw y _).le ((hC μ hμ _ hβ).2 y).1)
  · rw [hgrad]
    calc ‖∑ μ ∈ D.index, ProfileData.monomialOf p μ •
          fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase p)) y‖ ≤ ∑ μ ∈ D.index,
          ‖ProfileData.monomialOf p μ • fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase p)) y‖ :=
          norm_sum_le _ _
      _ = ∑ μ ∈ D.index, |ProfileData.monomialOf p μ| *
          ‖fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase p)) y‖ := by
          simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ K * (1 + ‖y‖) ^ (-(2 : ℝ)) :=
          key _ _ (hw y _).le (fun μ hμ => le_abs_mul (hw y _).le ((hC μ hμ _ hβ).2 y).2.1)
  · have hslope : LipschitzOnWith (Real.toNNReal (K * (1 + ‖y‖) ^ (-(3 : ℝ))))
        (fun z => ∑ μ ∈ D.index, ProfileData.monomialOf p μ •
          fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase p)) z) (Metric.ball y 1) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro a ha b hb
      rw [Real.coe_toNNReal _ (mul_nonneg hKnn (hw y _).le), dist_eq_norm,
        ← Finset.sum_sub_distrib]
      simp_rw [← smul_sub]
      calc ‖∑ μ ∈ D.index, ProfileData.monomialOf p μ •
            (fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase p)) a -
              fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase p)) b)‖
            ≤ ∑ μ ∈ D.index, ‖ProfileData.monomialOf p μ •
            (fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase p)) a -
              fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase p)) b)‖ := norm_sum_le _ _
        _ = ∑ μ ∈ D.index, |ProfileData.monomialOf p μ| *
            ‖fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase p)) a -
              fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase p)) b‖ := by
            simp only [norm_smul, Real.norm_eq_abs]
        _ ≤ K * ((1 + ‖y‖) ^ (-(3 : ℝ)) * dist a b) := by
            apply key _ _ (mul_nonneg (hw y _).le dist_nonneg)
            intro μ hμ
            have h1 := (((hC μ hμ _ hβ).2 y).2.2).dist_le_mul a ha b hb
            rw [Real.coe_toNNReal', dist_eq_norm] at h1
            calc _ ≤ max (C μ * (1 + ‖y‖) ^ (-(3 : ℝ))) 0 * dist a b := h1
              _ ≤ (|C μ| * (1 + ‖y‖) ^ (-(3 : ℝ))) * dist a b := by
                  apply mul_le_mul_of_nonneg_right _ dist_nonneg
                  exact max_le (le_abs_mul (hw y _).le le_rfl)
                    (mul_nonneg (abs_nonneg _) (hw y _).le)
              _ = |C μ| * ((1 + ‖y‖) ^ (-(3 : ℝ)) * dist a b) := by ring
        _ = K * (1 + ‖y‖) ^ (-(3 : ℝ)) * dist a b := by ring
    have h2 := norm_fderiv_le_of_lipschitzOn ℝ (Metric.ball_mem_nhds y one_pos) hslope
    rw [Real.coe_toNNReal _ (mul_nonneg hKnn (hw y _).le)] at h2
    unfold ProfileData.second
    rw [hgrad]
    exact h2

private theorem div_sum {ι : Type*} (s : Finset ι) (f : ι → Space → Space) (x : Space)
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    divergenceAt (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, divergenceAt (f i) x := by
  have hc : ∀ (v : ι → Space) (j : Fin 3), (∑ i ∈ s, v i) j = ∑ i ∈ s, v i j := by
    intro v j
    simpa using map_sum (EuclideanSpace.proj (𝕜 := ℝ) j) v s
  have hfun : (fun y => ∑ i ∈ s, f i y) = ∑ i ∈ s, f i := by
    funext y
    simp only [Finset.sum_apply]
  unfold divergenceAt
  rw [hfun, fderiv_sum hf]
  simp only [ContinuousLinearMap.sum_apply, hc]
  exact Finset.sum_comm

private theorem div_lin (a b : ℝ) (G F : Space → Space) (x : Space) (hG : DifferentiableAt ℝ G x)
    (hF : DifferentiableAt ℝ F x) :
    divergenceAt (fun y => a • G y + b • F y) x = a * divergenceAt G x + b * divergenceAt F x := by
  unfold divergenceAt
  rw [show (fun y => a • G y + b • F y) = a • G + b • F from rfl]
  rw [((hG.hasFDerivAt.const_smul a).add (hF.hasFDerivAt.const_smul b)).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]

private theorem sum_bound {ι : Type*} (s : Finset ι) (u v g h cg ch : ι → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hg : ∀ i ∈ s, g i ≤ cg i * W) (hh : ∀ i ∈ s, h i ≤ ch i * W) :
    ∑ i ∈ s, (|u i| * g i + |v i| * h i) ≤ (∑ i ∈ s, (|u i| * |cg i| + |v i| * |ch i|)) * W := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  calc |u i| * g i + |v i| * h i ≤ |u i| * (|cg i| * W) + |v i| * (|ch i| * W) :=
        add_le_add (mul_le_mul_of_nonneg_left (le_abs_mul hW (hg i hi)) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (le_abs_mul hW (hh i hi)) (abs_nonneg _))
    _ = (|u i| * |cg i| + |v i| * |ch i|) * W := by ring

private theorem norm_sum_bound {ι : Type*} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (s : Finset ι) (a b : ι → ℝ) (G F : ι → V) :
    ‖∑ i ∈ s, (a i • G i + b i • F i)‖ ≤ ∑ i ∈ s, (|a i| * ‖G i‖ + |b i| * ‖F i‖) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  simp only [norm_smul, Real.norm_eq_abs]

theorem profile_tangent_regular {k : ℕ} (D : ProfileData k) (hD : IsProfileData D) (i : Fin k) :
    ContDiff ℝ 1 (D.tangentField i) ∧ (∀ y, divergenceAt (D.tangentField i) y = 0) ∧
      ∃ C : ℝ, ∀ y, ‖D.tangentField i y‖ ≤ C * (1 + ‖y‖)⁻¹ ∧
        ‖fderiv ℝ (D.tangentField i) y‖ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ) := by
  have hexG : ∀ μ : Fin k → ℕ, ∃ G : Space → Space, ∃ C : ℝ, μ ∈ D.index →
      (∀ y, HasDerivAt (fun β => fieldOf D.chart (D.part μ) β y) (G y) (D.phase 0)) ∧
      ContDiff ℝ 1 G ∧ (∀ y, divergenceAt G y = 0) ∧
        ∀ y, ‖G y‖ ≤ C * (1 + ‖y‖)⁻¹ ∧ ‖fderiv ℝ G y‖ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ) := by
    intro μ
    by_cases hμ : μ ∈ D.index
    · obtain ⟨G, h1, h2, h3, C, h4⟩ :=
        fieldOf_phaseDeriv D.chart hD.chart (D.part μ) (hD.parts μ hμ) (D.phase 0)
      exact ⟨G, C, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨0, 0, fun h => absurd h hμ⟩
  choose G CG hG using hexG
  have hexF : ∀ μ : Fin k → ℕ, ∃ C : ℝ, μ ∈ D.index →
      ContDiff ℝ 1 (fieldOf D.chart (D.part μ) (D.phase 0)) ∧ ∀ y : Space,
        ‖fieldOf D.chart (D.part μ) (D.phase 0) y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧
        ‖fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase 0)) y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
    intro μ
    by_cases hμ : μ ∈ D.index
    · obtain ⟨C, hC⟩ := fieldOf_decay D.chart hD.chart (D.part μ) (hD.parts μ hμ) |D.phase 0|
      exact ⟨C, fun _ => ⟨(hC _ le_rfl).1, fun y => ⟨((hC _ le_rfl).2 y).1, ((hC _ le_rfl).2 y).2.1⟩⟩⟩
    · exact ⟨0, fun h => absurd h hμ⟩
  choose CF hF using hexF
  set F : (Fin k → ℕ) → Space → Space := fun μ => fieldOf D.chart (D.part μ) (D.phase 0) with hFdef
  have hdivF : ∀ μ ∈ D.index, ∀ y, divergenceAt (F μ) y = 0 := fun μ hμ y =>
    fieldOf_divergence D.chart hD.chart (D.part μ) (hD.parts μ hμ) (D.phase 0) y
  set a : (Fin k → ℕ) → ℝ := fun μ =>
    ProfileData.monomialOf 0 μ * fderiv ℝ D.phase 0 (Pi.single i 1) with ha
  set b : (Fin k → ℕ) → ℝ := fun μ =>
    fderiv ℝ (fun q : Fin k → ℝ => ProfileData.monomialOf q μ) 0 (Pi.single i 1) with hb
  have hphd : Differentiable ℝ D.phase := by
    unfold ProfileData.phase ProfileData.rate
    fun_prop
  have hmond : ∀ μ : Fin k → ℕ, Differentiable ℝ (fun q : Fin k → ℝ => ProfileData.monomialOf q μ) := by
    intro μ
    unfold ProfileData.monomialOf
    fun_prop
  have htan : D.tangentField i = fun y => ∑ μ ∈ D.index, (a μ • G μ y + b μ • F μ y) := by
    funext y
    have hterm : ∀ μ ∈ D.index, HasFDerivAt
        (fun q : Fin k → ℝ => ProfileData.monomialOf q μ • fieldOf D.chart (D.part μ) (D.phase q) y)
        (ProfileData.monomialOf 0 μ •
            ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (G μ y)).comp (fderiv ℝ D.phase 0)) +
          (fderiv ℝ (fun q : Fin k → ℝ => ProfileData.monomialOf q μ) 0).smulRight
            (fieldOf D.chart (D.part μ) (D.phase 0) y)) 0 := by
      intro μ hμ
      have hc : HasFDerivAt (fun q : Fin k → ℝ => fieldOf D.chart (D.part μ) (D.phase q) y)
          ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (G μ y)).comp (fderiv ℝ D.phase 0)) 0 :=
        (((hG μ hμ).1 y).hasFDerivAt).comp (0 : Fin k → ℝ) (hphd 0).hasFDerivAt
      exact ((hmond μ) 0).hasFDerivAt.smul hc
    have hfun : (fun q : Fin k → ℝ => D.profile q y) = ∑ μ ∈ D.index,
        (fun q : Fin k → ℝ => ProfileData.monomialOf q μ • fieldOf D.chart (D.part μ) (D.phase q) y) := by
      funext q
      simp only [ProfileData.profile, Finset.sum_apply]
    have hsum := HasFDerivAt.sum (u := D.index) hterm
    rw [← hfun] at hsum
    unfold ProfileData.tangentField
    rw [hsum.fderiv]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, smul_smul, ha, hb, hFdef]
  have hGd : ∀ μ ∈ D.index, Differentiable ℝ (G μ) := fun μ hμ =>
    (hG μ hμ).2.1.differentiable one_ne_zero
  have hFd : ∀ μ ∈ D.index, Differentiable ℝ (F μ) := fun μ hμ =>
    (hF μ hμ).1.differentiable one_ne_zero
  have hfd : ∀ z, HasFDerivAt (fun y => ∑ μ ∈ D.index, (a μ • G μ y + b μ • F μ y))
      (∑ μ ∈ D.index, (a μ • fderiv ℝ (G μ) z + b μ • fderiv ℝ (F μ) z)) z := by
    intro z
    have hfun : (fun y => ∑ μ ∈ D.index, (a μ • G μ y + b μ • F μ y)) =
        ∑ μ ∈ D.index, (fun y => a μ • G μ y + b μ • F μ y) := by
      funext y
      simp only [Finset.sum_apply]
    rw [hfun]
    exact HasFDerivAt.sum (u := D.index) (fun μ hμ =>
      (((hGd μ hμ) z).hasFDerivAt.const_smul (a μ)).add (((hFd μ hμ) z).hasFDerivAt.const_smul (b μ)))
  rw [htan]
  refine ⟨?_, ?_, ?_⟩
  · exact ContDiff.sum (fun μ hμ => (ContDiff.const_smul (a μ) (hG μ hμ).2.1).add
      (ContDiff.const_smul (b μ) (hF μ hμ).1))
  · intro y
    rw [div_sum D.index (fun μ y => a μ • G μ y + b μ • F μ y) y
      (fun μ hμ => (((hGd μ hμ) y).const_smul (a μ)).add (((hFd μ hμ) y).const_smul (b μ)))]
    apply Finset.sum_eq_zero
    intro μ hμ
    rw [div_lin (a μ) (b μ) (G μ) (F μ) y ((hGd μ hμ) y) ((hFd μ hμ) y), (hG μ hμ).2.2.1 y,
      hdivF μ hμ y]
    ring
  · refine ⟨∑ μ ∈ D.index, (|a μ| * |CG μ| + |b μ| * |CF μ|), fun y => ⟨?_, ?_⟩⟩
    · refine (norm_sum_bound _ _ _ _ _).trans (sum_bound _ _ _ _ _ _ _ _ (by positivity) ?_ ?_)
      · exact fun μ hμ => ((hG μ hμ).2.2.2 y).1
      · intro μ hμ
        have := ((hF μ hμ).2 y).1
        rwa [Real.rpow_neg_one] at this
    · rw [(hfd y).fderiv]
      refine (norm_sum_bound _ _ _ _ _).trans (sum_bound _ _ _ _ _ _ _ _
        (Real.rpow_pos_of_pos (by positivity) _).le ?_ ?_)
      · exact fun μ hμ => ((hG μ hμ).2.2.2 y).2
      · exact fun μ hμ => ((hF μ hμ).2 y).2

end FracCellInternal

namespace CellCert

namespace GivenFields

open SteadyCert

theorem shift_regular_of {k : ℕ} (D : ProfileData k) (hD : IsProfileData D) (i : Fin k) :
    ContDiff ℝ 1 (D.tangentField i) ∧ (∀ y, divergenceAt (D.tangentField i) y = 0) ∧
      ∃ C : ℝ, ∀ y, ‖D.tangentField i y‖ ≤ C * (1 + ‖y‖)⁻¹ ∧
        ‖fderiv ℝ (D.tangentField i) y‖ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ) :=
  FracCellInternal.profile_tangent_regular D hD i

theorem profile_bounds_of {k N : ℕ} (D : ProfileData k) (d : FracCertData k N)
    (hD : IsProfileData D) (hd : IsProfileInstance D d) :
    ∃ C : ℝ, ∀ p ∈ box d.radius, ∀ y,
      ‖d.profile p y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧ ‖d.gradProfile p y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) ∧
        (∀ᵐ z ∂volume, ‖d.profileSecond p z‖ ≤ C * (1 + ‖z‖) ^ (-(3 : ℝ))) := by
  obtain ⟨C, hC⟩ := FracCellInternal.profile_bounds_everywhere D hD d.radius
  refine ⟨C, fun p hp y => ?_⟩
  unfold FracCertData.gradProfile
  rw [hd.profile_eq, hd.second_eq]
  exact ⟨(hC p hp y).1, (hC p hp y).2.1, Filter.Eventually.of_forall fun z => (hC p hp z).2.2⟩

end GivenFields

end CellCert

end Breakdown
