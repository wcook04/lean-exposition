import Breakdown.Cert.CoerciveSmoothMuWave
import Breakdown.Cert.CoerciveSmoothMuDecay
import Breakdown.Cert.CoerciveSmoothPieceEpsBounds

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothEpsTailDeriv

theorem alternatingSymbol_abs_le (i j l : Fin 3) : |alternatingSymbol i j l| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> norm_num [alternatingSymbol]

theorem norm_curlVec_le (G : Space →L[ℝ] Space) {c : ℝ} (h : ∀ j l, |G (unitVector j) l| ≤ c) :
    ‖curlVec G‖ ≤ 27 * c := by
  have hin : ∀ i j : Fin 3, |∑ l : Fin 3, alternatingSymbol i j l * G (unitVector j) l| ≤ 3 * c := by
    intro i j
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ l : Fin 3, |alternatingSymbol i j l * G (unitVector j) l| ≤ ∑ _l : Fin 3, c := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [abs_mul]
          calc |alternatingSymbol i j l| * |G (unitVector j) l| ≤ 1 * c :=
                mul_le_mul (alternatingSymbol_abs_le i j l) (h j l) (abs_nonneg _) zero_le_one
            _ = c := one_mul c
      _ = 3 * c := by simp
  have hmid : ∀ i : Fin 3, |∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * G (unitVector j) l| ≤ 9 * c := by
    intro i
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j : Fin 3, |∑ l : Fin 3, alternatingSymbol i j l * G (unitVector j) l| ≤ ∑ _j : Fin 3, 3 * c :=
          Finset.sum_le_sum fun j _ => hin i j
      _ = 9 * c := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  unfold curlVec
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : Fin 3, ‖(∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * G (unitVector j) l) • unitVector i‖
      ≤ ∑ _i : Fin 3, 9 * c := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Internal.MuSmooth.Decay.unit_norm, mul_one, Real.norm_eq_abs]
        exact hmid i
    _ = 27 * c := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem slice_fderiv_eq {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (s : ℝ) (z : Space) :
    fderiv ℝ (W s) z
      = (fderiv ℝ (fun q : ℝ × Space => W q.1 q.2) (s, z)).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
  have hd : DifferentiableAt ℝ (fun q : ℝ × Space => W q.1 q.2) (s, z) := hW.differentiable (by norm_num) _
  exact (hd.hasFDerivAt.comp z (hasFDerivAt_prodMk_right s z)).fderiv

theorem slice_fderiv_continuous {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun q : ℝ × Space => fderiv ℝ (W q.1) q.2) := by
  have e : (fun q : ℝ × Space => fderiv ℝ (W q.1) q.2)
      = fun q => (fderiv ℝ (fun q : ℝ × Space => W q.1 q.2) q).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
    funext q
    exact slice_fderiv_eq hW q.1 q.2
  rw [e]
  exact (hW.continuous_fderiv (by norm_num)).clm_comp continuous_const

theorem gradIntegrand_continuous {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (σ : ℝ) (x : Space) (l j : Fin 3) :
    Continuous (fun p : ℝ × ℝ =>
      axialRot (-p.2) (gradField W (σ + p.1) (axialRot p.2 x) (axialRot p.2 (unitVector j))) l) := by
  have h1 : Continuous (fun p : ℝ × ℝ => fderiv ℝ (W (σ + p.1)) (axialRot p.2 x)) :=
    (slice_fderiv_continuous hW).comp ((continuous_const.add continuous_fst).prodMk
      (Internal.MuSmooth.Decay.rot_continuous continuous_snd continuous_const))
  have h2 : Continuous (fun p : ℝ × ℝ =>
      fderiv ℝ (W (σ + p.1)) (axialRot p.2 x) (axialRot p.2 (unitVector j))) :=
    h1.clm_apply (Internal.MuSmooth.Decay.rot_continuous continuous_snd continuous_const)
  exact (PiLp.continuous_apply 2 _ l).comp (Internal.MuSmooth.Decay.rot_continuous continuous_snd.neg h2)

theorem slice_fderiv_sub_le {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    {D : ℝ} (hD2 : ∀ s z, ‖fderiv ℝ (fderiv ℝ (W s)) z‖ ≤ D) (s : ℝ) (a c : Space) :
    ‖fderiv ℝ (W s) a - fderiv ℝ (W s) c‖ ≤ D * ‖a - c‖ := by
  have hs : ContDiff ℝ 2 (W s) := hW.comp (contDiff_const.prodMk contDiff_id)
  have hdiff : Differentiable ℝ (fderiv ℝ (W s)) :=
    (hs.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z) (fun z _ => hD2 s z) convex_univ
    (Set.mem_univ c) (Set.mem_univ a)

theorem meanField_fderiv_entry_sub {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W) {D : ℝ}
    (hD1 : ∀ s z, ‖fderiv ℝ (W s) z‖ ≤ D) (hD2 : ∀ s z, ‖fderiv ℝ (fderiv ℝ (W s)) z‖ ≤ D)
    (x y : Space) (j l : Fin 3) :
    |fderiv ℝ (meanField W) x (unitVector j) l - fderiv ℝ (meanField W) y (unitVector j) l| ≤ D * ‖x - y‖ := by
  rw [Internal.MuSmooth.meanField_fderiv_apply hW hD1 hWp 0 x l j,
    Internal.MuSmooth.meanField_fderiv_apply hW hD1 hWp 0 y l j, ← Complex.sub_re]
  refine (Complex.abs_re_le_norm _).trans ?_
  unfold modeGrad
  rw [Internal.MuSmooth.Decay.modeAverage_sub]
  · refine Internal.MuSmooth.Decay.modeAverage_norm_le _ _ (l, j) fun τ φ => ?_
    dsimp only
    rw [← PiLp.sub_apply, Internal.MuSmooth.Decay.rot_sub]
    refine (Internal.MuSmooth.Decay.coord_abs_le _ l).trans ?_
    rw [Internal.MuSmooth.Decay.rot_norm, ← sub_apply]
    refine ((gradField W (0 + τ) (axialRot φ x) - gradField W (0 + τ) (axialRot φ y)).le_opNorm _).trans ?_
    rw [Internal.MuSmooth.Decay.rot_norm, Internal.MuSmooth.Decay.unit_norm, mul_one]
    unfold gradField
    refine (slice_fderiv_sub_le hW hD2 _ _ _).trans ?_
    rw [Internal.MuSmooth.Decay.rot_sub, Internal.MuSmooth.Decay.rot_norm]
  · exact gradIntegrand_continuous hW 0 x l j
  · exact gradIntegrand_continuous hW 0 y l j

theorem meanField_curl_bounds {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W) {D : ℝ}
    (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖curlVec (fderiv ℝ (meanField W) y)‖ ≤ B ∧
      ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ ≤ B := by
  have hD0 : 0 ≤ D := by
    have h := hD 0 0 0 (by norm_num)
    have : 0 ≤ D / (1 + ‖(0 : Space)‖) ^ (0 + 1) := (norm_nonneg _).trans h
    simpa using this
  have hD1' : ∀ s z, ‖fderiv ℝ (W s) z‖ ≤ D / (1 + ‖z‖) ^ 2 := fun s z => by
    have h := hD s z 1 (by norm_num)
    rwa [norm_iteratedFDeriv_one] at h
  have hD1 : ∀ s z, ‖fderiv ℝ (W s) z‖ ≤ D := fun s z =>
    (hD1' s z).trans (div_le_self hD0 (one_le_pow₀ (by linarith [norm_nonneg z])))
  have hD2 : ∀ s z, ‖fderiv ℝ (fderiv ℝ (W s)) z‖ ≤ D := fun s z => by
    have h := hD s z 2 le_rfl
    have e : ‖fderiv ℝ (fderiv ℝ (W s)) z‖ = ‖iteratedFDeriv ℝ 2 (W s) z‖ := by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    rw [e]
    exact h.trans (div_le_self hD0 (one_le_pow₀ (by linarith [norm_nonneg z])))
  refine ⟨27 * (12 * D), by positivity, fun y => ⟨?_, ?_⟩⟩
  · refine norm_curlVec_le _ fun j l => ?_
    have hA := Internal.MuSmooth.Decay.meanField_fderiv_le hW hD1' hD0 y
    calc |fderiv ℝ (meanField W) y (unitVector j) l| ≤ ‖fderiv ℝ (meanField W) y (unitVector j)‖ :=
          Internal.MuSmooth.Decay.coord_abs_le _ l
      _ ≤ ‖fderiv ℝ (meanField W) y‖ * ‖unitVector j‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (meanField W) y‖ := by rw [Internal.MuSmooth.Decay.unit_norm, mul_one]
      _ ≤ 12 * D / (1 + ‖y‖) ^ 2 := hA
      _ ≤ 12 * D := div_le_self (by positivity) (one_le_pow₀ (by linarith [norm_nonneg y]))
  · have hincr : ∀ x, ‖curlVec (fderiv ℝ (meanField W) x) - curlVec (fderiv ℝ (meanField W) y)‖
        ≤ 27 * D * ‖x - y‖ := fun x => by
      have e : curlVec (fderiv ℝ (meanField W) x) - curlVec (fderiv ℝ (meanField W) y)
          = curlVec (fderiv ℝ (meanField W) x - fderiv ℝ (meanField W) y) :=
        (map_sub Internal.SmoothPieceEps.curlLinear _ _).symm
      rw [e]
      have h := norm_curlVec_le (fderiv ℝ (meanField W) x - fderiv ℝ (meanField W) y) (c := D * ‖x - y‖)
        fun j l => by
          rw [sub_apply, PiLp.sub_apply]
          exact meanField_fderiv_entry_sub hW hWp hD1 hD2 x y j l
      linarith
    have h := norm_fderiv_le_of_lip' ℝ (f := fun x => curlVec (fderiv ℝ (meanField W) x)) (x₀ := y)
      (C := 27 * D) (by positivity) (Filter.Eventually.of_forall hincr)
    linarith

end Internal.SmoothEpsTailDeriv

end Coercive

end Breakdown
