import TorusEuler.HierarchyPeriodicProfiles
import TorusEuler.PhaseProfileEstimates
import TorusEuler.TerminalIntegrals
import TorusEuler.WaveDivergence
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! The normalized phase potential and slow curl of (3.5), as maps on
the concrete smooth profile spaces of the finite hierarchy. -/

open ContinuousLinearMap Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

section PhaseMeanDerivative

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Label Fréchet differentiation commutes with phase averaging at fixed time. -/
theorem fderiv_phaseMean_eq_phaseMean_fderiv {f : P → ℝ → E}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (a : P) :
    fderiv ℝ (fun y => phaseMean (f y)) a =
      phaseMean (fun s => fderiv ℝ (fun y => f y s) a) := by
  let C := continuousMultilinearCurryFin1 ℝ P E
  have h (g : P → E) : C (iteratedFDeriv ℝ 1 g a) = fderiv ℝ g a := by
    ext v
    simp [C]
  let D (s : ℝ) := iteratedFDeriv ℝ 1 (fun y => f y s) a
  have hcomm := LinearIsometry.intervalIntegral_comp_comm (𝕜 := ℝ) (μ := volume)
    (a := 0) (b := 1) (E := P [×1]→L[ℝ] E) (F := P →L[ℝ] E) C.toLinearIsometry D
  change phaseMean (fun s => C (D s)) = C (phaseMean D) at hcomm
  calc
    _ = C (iteratedFDeriv ℝ 1 (fun y => phaseMean (f y)) a) := (h _).symm
    _ = C (phaseMean D) := congrArg C (iteratedFDeriv_phaseMean hf 1 a)
    _ = phaseMean (fun s => C (D s)) := hcomm.symm
    _ = _ := congrArg phaseMean (funext fun s => h (fun y => f y s))

end PhaseMeanDerivative

private theorem hasFDerivAt_composedLabelPhase {f : Vec3 → ℝ → Vec3}
    {A : Vec3 → Vec3} {φ : Vec3 → ℝ} {x : Vec3} {J : Vec3 →L[ℝ] Vec3} {κ : Vec3}
    (hA : HasFDerivAt A J x) (hφ : HasFDerivAt φ (innerSL ℝ κ) x)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (A x, φ x)) :
    HasFDerivAt (fun y => f (A y) (φ y))
      ((fderiv ℝ (fun a => f a (φ x)) (A x)).comp J +
        (innerSL ℝ κ).smulRight (deriv (f (A x)) (φ x))) x := by
  have h := (hasFDerivAt_profile_partials hf).comp x (hA.prodMk hφ)
  refine h.congr_fderiv ?_
  ext v i
  simp

private theorem divergence_composedLabelPhase {f : Vec3 → ℝ → Vec3}
    {A : Vec3 → Vec3} {φ : Vec3 → ℝ} {x : Vec3} {J : Vec3 →L[ℝ] Vec3} {κ : Vec3}
    (hA : HasFDerivAt A J x) (hφ : HasFDerivAt φ (innerSL ℝ κ) x)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (A x, φ x)) :
    divergence (fun y => f (A y) (φ y)) x =
      (∑ i : Fin 3, (fderiv ℝ (fun a => f a (φ x)) (A x) (J (EuclideanSpace.single i 1))) i) +
        ⟪κ, deriv (f (A x)) (φ x)⟫_ℝ := by
  rw [divergence, (hasFDerivAt_composedLabelPhase hA hφ hf).fderiv]
  simp only [add_apply, PiLp.add_apply, comp_apply, smulRight_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, one_mul, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, starRingEnd_apply, star_trivial,
    dotProduct, mul_comm]

/-- A curl completion has zero slow plus fast divergence at every label-phase
point. Shift the Eulerian phase graph to pass through the prescribed phase. -/
theorem slowFastDivergence_curlCompletedProfile {A : Vec3 → Vec3} {ψ : Vec3 → ℝ}
    {κ : Vec3 → Vec3} {Q V W : Vec3 → ℝ → Vec3}
    (hA : ContDiff ℝ 2 A) (hψ : ContDiff ℝ 2 ψ)
    (hκ : ∀ y, HasFDerivAt ψ (innerSL ℝ (κ y)) y)
    (hQ : ContDiff ℝ 2 (Function.uncurry Q))
    (hW : Differentiable ℝ (Function.uncurry W))
    (hV : ∀ y r, cross3 (κ y) (deriv (Q (A y)) r) = V (A y) r)
    (hC : ∀ y r, W (A y) r = V (A y) r + curlOfDerivative
      ((fderiv ℝ (fun a => Q a r) (A y)).comp (fderiv ℝ A y)))
    (x : Vec3) (s : ℝ) :
    (∑ i : Fin 3, (fderiv ℝ (fun a => W a s) (A x) (fderiv ℝ A x (EuclideanSpace.single i 1))) i) +
      ⟪κ x, deriv (W (A x)) s⟫_ℝ = 0 := by
  let φ (y : Vec3) := ψ y - ψ x + s
  have hφ : ContDiff ℝ 2 φ := (hψ.sub contDiff_const).add contDiff_const
  have hφD (y : Vec3) : HasFDerivAt φ (innerSL ℝ (κ y)) y :=
    ((hκ y).sub_const _).add_const _
  have hφx : φ x = s := by simp [φ]
  have hAD (y : Vec3) : HasFDerivAt A (fderiv ℝ A y) y :=
    (hA.differentiable (by simp) y).hasFDerivAt
  have hcurl (y : Vec3) : curl (fun z => Q (A z) (φ z)) y = W (A y) (φ y) := by
    have hrank : curlOfDerivative ((innerSL ℝ (κ y)).smulRight (deriv (Q (A y)) (φ y))) =
        cross3 (κ y) (deriv (Q (A y)) (φ y)) := coordinateCurl_rankOne _ _
    rw [curl, (hasFDerivAt_composedLabelPhase (hAD y) (hφD y)
      (hQ.differentiable (by simp) (A y, φ y))).fderiv,
      curlOfDerivative_add, hrank, hV, add_comm, ← hC]
  have hQeval : ContDiff ℝ 2 (fun y => Q (A y) (φ y)) := hQ.comp (hA.prodMk hφ)
  have hzero := divergence_curl (x := x) hQeval.contDiffAt
  rw [funext hcurl, divergence_composedLabelPhase (hAD x) (hφD x) (hW (A x, φ x)), hφx] at hzero
  exact hzero

namespace HierarchySmoothProfile

noncomputable section

variable {T : ℝ}

local notation "VP" => HierarchySmoothProfile T Vec3
local notation "VPmap" => HierarchySmoothProfile T (Vec3 →L[ℝ] Vec3)

theorem contDiff_labelPhase_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : HierarchySmoothProfile T E) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContDiff ℝ ∞ (fun x : Vec3 × ℝ => V.val (t, x)) :=
  contDiffOn_univ.mp ((smooth V).comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun _ _ => ⟨ht, mem_univ _⟩))

private theorem continuous_phase_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : HierarchySmoothProfile T E) {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) :
    Continuous (fun s => V.val (t, a, s)) :=
  (contDiff_labelPhase_slice V ht).continuous.comp (continuous_const.prodMk continuous_id)

private theorem contDiffOn_cross3_profile
    {a b : HierarchyProfilePoint → Vec3}
    (ha : ContDiffOn ℝ ∞ a (hierarchyProfileSlab T))
    (hb : ContDiffOn ℝ ∞ b (hierarchyProfileSlab T)) :
    ContDiffOn ℝ ∞ (fun x => cross3 (a x) (b x)) (hierarchyProfileSlab T) := by
  have ha' (i : Fin 3) := (contDiff_piLp_apply (i := i) 2).comp_contDiffOn ha
  have hb' (i : Fin 3) := (contDiff_piLp_apply (i := i) 2).comp_contDiffOn hb
  apply contDiffOn_piLp' 2
  intro i
  fin_cases i
  · change ContDiffOn ℝ ∞ (fun x => a x 1 * b x 2 - a x 2 * b x 1) _
    exact ((ha' 1).mul (hb' 2)).sub ((ha' 2).mul (hb' 1))
  · change ContDiffOn ℝ ∞ (fun x => a x 2 * b x 0 - a x 0 * b x 2) _
    exact ((ha' 2).mul (hb' 0)).sub ((ha' 0).mul (hb' 2))
  · change ContDiffOn ℝ ∞ (fun x => a x 0 * b x 1 - a x 1 * b x 0) _
    exact ((ha' 0).mul (hb' 1)).sub ((ha' 1).mul (hb' 0))

set_option maxHeartbeats 750000 in
private theorem contDiffOn_wavePotential_profile (hT : 0 < T) (κ V : VP)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val (t, a, 0) ≠ 0) :
    ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint =>
      wavePotential (κ.val (x.1, x.2.1, 0)) (fun s => V.val (x.1, x.2.1, s)) x.2.2)
      (hierarchyProfileSlab T) := by
  let S : Set (ℝ × Vec3) := Icc 0 T ×ˢ univ
  let K (x : HierarchyProfilePoint) := κ.val (x.1, x.2.1, 0)
  let I (x : HierarchyProfilePoint) := (-(‖K x‖ ^ 2)⁻¹) • cross3 (K x) (V.val x)
  have hK : ContDiffOn ℝ ∞ K (hierarchyProfileSlab T) :=
    (smooth κ).comp (contDiffOn_fst.prodMk (contDiffOn_snd.fst.prodMk contDiffOn_const))
      (fun _ hx => ⟨hx.1, mem_univ _⟩)
  have hKsq : ContDiffOn ℝ ∞ (fun x => ‖K x‖ ^ 2) (hierarchyProfileSlab T) :=
    hK.norm_sq ℝ
  have hKn (x : HierarchyProfilePoint) (hx : x ∈ hierarchyProfileSlab T) : ‖K x‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (hκ x.1 hx.1 x.2.1))
  have hi : ContDiffOn ℝ ∞ I (hierarchyProfileSlab T) :=
    (hKsq.inv hKn).neg.smul (contDiffOn_cross3_profile hK (smooth V))
  let F (p : ℝ × Vec3) (s : ℝ) := I (p.1, p.2, s)
  have hF : ContDiffOn ℝ ∞ (Function.uncurry F) (S ×ˢ (univ : Set ℝ)) :=
    hi.comp (contDiffOn_fst.fst.prodMk (contDiffOn_fst.snd.prodMk contDiffOn_snd))
      (fun z hz => ⟨hz.1.1, mem_univ _⟩)
  have hP : ContDiffOn ℝ ∞ (Function.uncurry (fun p => phasePrimitive (F p)))
      (S ×ˢ (univ : Set ℝ)) :=
    contDiffOn_phasePrimitive (S := S) (f := F) ((convex_Icc 0 T).prod convex_univ)
      ((uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ) hF
  let reindex (x : HierarchyProfilePoint) := ((x.1, x.2.1), x.2.2)
  have hR : ContDiffOn ℝ ∞ reindex (hierarchyProfileSlab T) :=
    (contDiffOn_fst.prodMk contDiffOn_snd.fst).prodMk contDiffOn_snd.snd
  have hMap : MapsTo reindex (hierarchyProfileSlab T) (S ×ˢ (univ : Set ℝ)) :=
    fun x hx => ⟨⟨hx.1, mem_univ _⟩, mem_univ _⟩
  change ContDiffOn ℝ ∞ (Function.uncurry (fun p => phasePrimitive (F p)) ∘ reindex) _
  exact hP.comp hR hMap

/-- The actual phase primitive defining `Q[V]`. The covector is read
at phase zero because the geometric covector is phase independent. -/
def profileWavePotential (hT : 0 < T) (κ : VP)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val (t, a, 0) ≠ 0) (V : VP) : VP :=
  ofSmooth _ (contDiffOn_wavePotential_profile hT κ V hκ)

theorem profileWavePotential_apply (hT : 0 < T) (κ : VP)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val (t, a, 0) ≠ 0) (V : VP)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (profileWavePotential hT κ hκ V).val (t, a, s) =
      wavePotential (κ.val (t, a, 0)) (fun σ => V.val (t, a, σ)) s :=
  ofSmooth_apply (contDiffOn_wavePotential_profile hT κ V hκ) ⟨ht, mem_univ _⟩

theorem profilePhaseAverage_wavePotential (hT : 0 < T) (κ : VP)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val (t, a, 0) ≠ 0) (V : VP) :
    profilePhaseAverage hT (profileWavePotential hT κ hκ V) = 0 := by
  apply ext
  intro x hx
  rw [profilePhaseAverage_apply _ _ hx]
  simp_rw [profileWavePotential_apply hT κ hκ V hx.1]
  exact phaseMean_wavePotential _ (continuous_phase_slice V hx.1 x.2.1)

private def profileLabelInclusion : Vec3 →L[ℝ] HierarchyProfilePoint :=
  (inr ℝ ℝ (Vec3 × ℝ)).comp (inl ℝ Vec3 ℝ)

/-- The label differential of a smooth profile, with time and phase held fixed. -/
def profileLabelDifferential (hT : 0 < T) : VP →ₗ[ℝ] VPmap :=
  (map ((compL ℝ Vec3 HierarchyProfilePoint Vec3).flip profileLabelInclusion)).comp (derivative hT)

theorem profileLabelDifferential_apply_eq_fderiv (hT : 0 < T) (Q : VP)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (profileLabelDifferential hT Q).val (t, a, s) =
      fderiv ℝ (fun b => Q.val (t, b, s)) a := by
  have hx : (t, a, s) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  have hF := ((smooth Q).differentiableOn (by simp) _ hx).hasFDerivWithinAt
  have hI : HasFDerivAt (fun b : Vec3 => (t, b, s)) profileLabelInclusion a := by
    exact (hasFDerivAt_prodMk_right (𝕜 := ℝ) t (a, s)).comp a
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) a s)
  have hmem : ∀ᶠ b : Vec3 in 𝓝 a, (t, b, s) ∈ hierarchyProfileSlab T :=
    Eventually.of_forall fun _ => ⟨ht, mem_univ _⟩
  have h := hF.comp_hasFDerivAt a hI hmem
  simp only [profileLabelDifferential, LinearMap.comp_apply, map_apply _ _ hx,
    derivative_apply _ _ hx]
  exact h.fderiv.symm

/-- The slow Eulerian curl of the potential in the label chart. -/
def profileSlowCurl (hT : 0 < T) (G : VPmap) : VP →ₗ[ℝ] VP :=
  (map curlOfDerivativeCLM).comp (((applyField.flip G).comp
    (map (compL ℝ Vec3 Vec3 Vec3))).comp (profileLabelDifferential hT))

theorem profileSlowCurl_apply (hT : 0 < T) (G : VPmap) (Q : VP)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (profileSlowCurl hT G Q).val (t, a, s) =
      curlOfDerivative ((fderiv ℝ (fun b => Q.val (t, b, s)) a).comp (G.val (t, a, s))) := by
  have hx : (t, a, s) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  simp only [profileSlowCurl, LinearMap.comp_apply, LinearMap.flip_apply, map_apply _ _ hx,
    applyField_eval _ _ hx, profileLabelDifferential_apply_eq_fderiv hT Q ht]
  rfl

/-- The slow curl commutes with phase averaging when the coframe is
phase independent. In particular it preserves the zero phase mean. -/
theorem profilePhaseAverage_slowCurl_eq_zero (hT : 0 < T) (G : VPmap) (Q : VP)
    (hG : ∀ t ∈ Icc 0 T, ∀ a s, G.val (t, a, s) = G.val (t, a, 0))
    (hQ : profilePhaseAverage hT Q = 0) :
    profilePhaseAverage hT (profileSlowCurl hT G Q) = 0 := by
  apply ext
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  let J (r : ℝ) := fderiv ℝ (fun b => Q.val (t, b, r)) a
  let L := curlOfDerivativeCLM.comp ((compL ℝ Vec3 Vec3 Vec3).flip (G.val (t, a, 0)))
  have hJ : Continuous J := by
    simpa only [profileLabelDifferential_apply_eq_fderiv hT Q ht] using
      continuous_phase_slice (profileLabelDifferential hT Q) ht a
  have hMean (b : Vec3) : phaseMean (fun r => Q.val (t, b, r)) = 0 := by
    have hb : (t, b, (0 : ℝ)) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
    rw [← profilePhaseAverage_apply hT Q hb, hQ]
    rfl
  have hJ₀ : phaseMean J = 0 := by
    rw [← fderiv_phaseMean_eq_phaseMean_fderiv
      (f := fun b r => Q.val (t, b, r)) (contDiff_labelPhase_slice Q ht) a,
      show (fun b => phaseMean (fun r => Q.val (t, b, r))) = fun _ => 0 from funext hMean]
    simp
  rw [profilePhaseAverage_apply _ _ hx]
  simp_rw [profileSlowCurl_apply hT G Q ht, hG t ht]
  change phaseMean (fun r => L (J r)) = 0
  rw [phaseMean, L.intervalIntegral_comp_comm (hJ.intervalIntegrable 0 1),
    ← phaseMean, hJ₀, map_zero]

/-- The smooth divergence correction, before restricting to profiles
of period one. -/
def profileCompletion (hT : 0 < T) (G : VPmap) (κ : VP)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val (t, a, 0) ≠ 0) (V : VP) : VP :=
  profileSlowCurl hT G (profileWavePotential hT κ hκ V)

theorem profilePhaseAverage_completion (hT : 0 < T) (G : VPmap) (κ : VP)
    (hG : ∀ t ∈ Icc 0 T, ∀ a s, G.val (t, a, s) = G.val (t, a, 0))
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val (t, a, 0) ≠ 0) (V : VP) :
    profilePhaseAverage hT (profileCompletion hT G κ hκ V) = 0 :=
  profilePhaseAverage_slowCurl_eq_zero hT G _ hG (profilePhaseAverage_wavePotential hT κ hκ V)

theorem profileWavePotential_phasePeriodic (hT : 0 < T) (κ : VP)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val (t, a, 0) ≠ 0) (V : VP) {t : ℝ}
    (ht : t ∈ Icc 0 T) (a : Vec3)
    (hV : Function.Periodic (fun s => V.val (t, a, s)) 1)
    (hV₀ : phaseMean (fun s => V.val (t, a, s)) = 0) :
    Function.Periodic (fun s => (profileWavePotential hT κ hκ V).val (t, a, s)) 1 := by
  intro s
  simp only [profileWavePotential_apply hT κ hκ V ht]
  exact periodic_wavePotential _ (continuous_phase_slice V ht a) hV hV₀ s

theorem profileSlowCurl_phasePeriodic (hT : 0 < T) (G : VPmap) (Q : VP)
    {t : ℝ} (ht : t ∈ Icc 0 T)
    (hG : ∀ a, Function.Periodic (fun s => G.val (t, a, s)) 1)
    (hQ : ∀ a, Function.Periodic (fun s => Q.val (t, a, s)) 1) (a : Vec3) :
    Function.Periodic (fun s => (profileSlowCurl hT G Q).val (t, a, s)) 1 := by
  intro s
  change (profileSlowCurl hT G Q).val (t, a, s + 1) = (profileSlowCurl hT G Q).val (t, a, s)
  simp only [profileSlowCurl_apply hT G Q ht]
  have hshift : (fun b => Q.val (t, b, s + 1)) = fun b => Q.val (t, b, s) :=
    funext fun b => hQ b s
  have hGshift : G.val (t, a, s + 1) = G.val (t, a, s) := hG a s
  rw [hshift, hGshift]

/-- At a fixed time the completed transverse profile has zero total
divergence over every phase at every label in the inverse chart. The
coframe and covector are supplied with their actual flow identities. -/
theorem profileCompletion_slowFastDivergence (hT : 0 < T) (G : VPmap) (κ V : VP)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val (t, a, 0) ≠ 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) {A : Vec3 → Vec3} (hA : ContDiff ℝ 2 A) (k : Vec3)
    (hG : ∀ y s, G.val (t, A y, s) = fderiv ℝ A y)
    (hκflow : ∀ y, κ.val (t, A y, 0) = (fderiv ℝ A y).adjoint k)
    (htrans : ∀ a s, ⟪κ.val (t, a, 0), V.val (t, a, s)⟫_ℝ = 0)
    (x : Vec3) (s : ℝ) :
    let W := V + profileCompletion hT G κ hκ V
    (∑ i : Fin 3, (fderiv ℝ (fun a => W.val (t, a, s)) (A x)
      (fderiv ℝ A x (EuclideanSpace.single i 1))) i) +
      ⟪κ.val (t, A x, 0), deriv (fun r => W.val (t, A x, r)) s⟫_ℝ = 0 := by
  let Q := profileWavePotential hT κ hκ V
  let W := V + profileCompletion hT G κ hκ V
  let ψ (y : Vec3) : ℝ := ⟪k, A y⟫_ℝ
  have hψ : ContDiff ℝ 2 ψ := (innerSL ℝ k).contDiff.comp hA
  have hψD (y : Vec3) : HasFDerivAt ψ (innerSL ℝ (κ.val (t, A y, 0))) y := by
    have h := (innerSL ℝ k).hasFDerivAt.comp y (hA.differentiable (by simp) y).hasFDerivAt
    refine h.congr_fderiv ?_
    ext v
    rw [hκflow]
    simp only [comp_apply, innerSL_apply_apply, adjoint_inner_left]
  have hQs : ContDiff ℝ 2 (Function.uncurry (fun a r => Q.val (t, a, r))) :=
    (contDiff_labelPhase_slice Q ht).of_le (by simp)
  have hWs : Differentiable ℝ (Function.uncurry (fun a r => W.val (t, a, r))) :=
    (contDiff_labelPhase_slice W ht).differentiable (by simp)
  have hFast (y : Vec3) (r : ℝ) :
      cross3 (κ.val (t, A y, 0)) (deriv (fun s => Q.val (t, A y, s)) r) =
        V.val (t, A y, r) := by
    rw [show (fun s => Q.val (t, A y, s)) =
      wavePotential (κ.val (t, A y, 0)) (fun s => V.val (t, A y, s)) from
        funext (profileWavePotential_apply hT κ hκ V ht (A y))]
    exact wavePotential_fast_curl (hκ t ht (A y)) (continuous_phase_slice V ht (A y))
      (htrans (A y)) r
  have hSlow (y : Vec3) (r : ℝ) :
      W.val (t, A y, r) = V.val (t, A y, r) +
        curlOfDerivative ((fderiv ℝ (fun a => Q.val (t, a, r)) (A y)).comp (fderiv ℝ A y)) := by
    change V.val (t, A y, r) + (profileSlowCurl hT G Q).val (t, A y, r) = _
    rw [profileSlowCurl_apply hT G Q ht, hG]
  exact slowFastDivergence_curlCompletedProfile (A := A) (ψ := ψ)
    (κ := fun y => κ.val (t, A y, 0)) (Q := fun a r => Q.val (t, a, r))
    (V := fun a r => V.val (t, a, r)) (W := fun a r => W.val (t, a, r))
    hA hψ hψD hQs hWs hFast hSlow x s

/-- The slow curl alone has zero slow divergence, since the phase is
fixed throughout this differentiation. -/
theorem profileSlowCurl_labelDivergence_zero (hT : 0 < T) (G : VPmap) (Q : VP)
    {t : ℝ} (ht : t ∈ Icc 0 T) {A : Vec3 → Vec3} (hA : ContDiff ℝ 2 A)
    (hG : ∀ y s, G.val (t, A y, s) = fderiv ℝ A y) (x : Vec3) (s : ℝ) :
    ∑ i : Fin 3,
      (fderiv ℝ (fun a => (profileSlowCurl hT G Q).val (t, a, s)) (A x)
        (fderiv ℝ A x (EuclideanSpace.single i 1))) i = 0 := by
  let C (a : Vec3) := (profileSlowCurl hT G Q).val (t, a, s)
  let P (a : Vec3) := Q.val (t, a, s)
  have hP : ContDiff ℝ 2 P :=
    ((contDiff_labelPhase_slice Q ht).comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
  have hC : ContDiff ℝ ∞ C :=
    (contDiff_labelPhase_slice (profileSlowCurl hT G Q) ht).comp
      (contDiff_id.prodMk contDiff_const)
  have heq : C ∘ A = curl (P ∘ A) := by
    funext y
    change (profileSlowCurl hT G Q).val (t, A y, s) = _
    rw [profileSlowCurl_apply hT G Q ht, hG, curl,
      (((hP.differentiable (by simp) (A y)).hasFDerivAt).comp y
        (hA.differentiable (by simp) y).hasFDerivAt).fderiv]
  have hdiv := divergence_curl (x := x) (hP.comp hA).contDiffAt
  rw [← heq, divergence,
    (((hC.differentiable (by simp) (A x)).hasFDerivAt).comp x
      (hA.differentiable (by simp) x).hasFDerivAt).fderiv] at hdiv
  exact hdiv

/-- The longitudinal derivative needed for phase integration by parts
is minus the slow divergence of the transverse oscillation. -/
theorem profileCompletion_longitudinal_derivative (hT : 0 < T) (G : VPmap) (κ V : VP)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val (t, a, 0) ≠ 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) {A : Vec3 → Vec3} (hA : ContDiff ℝ 2 A) (k : Vec3)
    (hG : ∀ y s, G.val (t, A y, s) = fderiv ℝ A y)
    (hκflow : ∀ y, κ.val (t, A y, 0) = (fderiv ℝ A y).adjoint k)
    (htrans : ∀ a s, ⟪κ.val (t, a, 0), V.val (t, a, s)⟫_ℝ = 0)
    (x : Vec3) (s : ℝ) :
    HasDerivAt (fun r => ⟪κ.val (t, A x, 0), (profileCompletion hT G κ hκ V).val (t, A x, r)⟫_ℝ)
      (-(∑ i : Fin 3,
        (fderiv ℝ (fun a => V.val (t, a, s)) (A x)
          (fderiv ℝ A x (EuclideanSpace.single i 1))) i)) s := by
  let C := profileCompletion hT G κ hκ V
  let L := innerSL ℝ (κ.val (t, A x, 0))
  let slow (f : VP) := ∑ i : Fin 3, (fderiv ℝ (fun a => f.val (t, a, s)) (A x)
    (fderiv ℝ A x (EuclideanSpace.single i 1))) i
  have hsp (f : VP) : Differentiable ℝ (fun a => f.val (t, a, s)) :=
    ((contDiff_labelPhase_slice f ht).comp (contDiff_id.prodMk contDiff_const)).differentiable
      (by simp)
  have hs (f : VP) : Differentiable ℝ (fun r => f.val (t, A x, r)) :=
    ((contDiff_labelPhase_slice f ht).comp (contDiff_const.prodMk contDiff_id)).differentiable
      (by simp)
  have hCslow : slow C = 0 :=
    profileSlowCurl_labelDivergence_zero hT G (profileWavePotential hT κ hκ V) ht hA hG x s
  have hVd := (L.hasFDerivAt.comp_hasDerivAt s (hs V s).hasDerivAt)
  change HasDerivAt (fun r => L (V.val (t, A x, r)))
    (L (deriv (fun r => V.val (t, A x, r)) s)) s at hVd
  have hVfast : L (deriv (fun r => V.val (t, A x, r)) s) = 0 := by
    have hz : (fun r => L (V.val (t, A x, r))) = fun _ => 0 := funext (htrans (A x))
    rw [← hVd.deriv, hz]
    simp
  have hsum := profileCompletion_slowFastDivergence hT G κ V hκ ht hA k hG hκflow htrans x s
  change slow (V + C) + L (deriv (fun r => V.val (t, A x, r) + C.val (t, A x, r)) s) = 0 at hsum
  have hSlow : slow (V + C) = slow V + slow C := by
    simp only [slow, Submodule.coe_add, Pi.add_apply,
      fderiv_fun_add (hsp V _) (hsp C _), add_apply, PiLp.add_apply,
      Finset.sum_add_distrib]
  rw [hSlow, hCslow, add_zero, deriv_fun_add (hs V s) (hs C s), map_add, hVfast, zero_add] at hsum
  have hd := L.hasFDerivAt.comp_hasDerivAt s (hs C s).hasDerivAt
  refine hd.congr_deriv ?_
  exact eq_neg_of_add_eq_zero_right hsum

end

end HierarchySmoothProfile

namespace HierarchyPeriodicProfile

noncomputable section

variable {T : ℝ}

local notation "VP" => HierarchyPeriodicProfile T Vec3
local notation "VPmap" => HierarchyPeriodicProfile T (Vec3 →L[ℝ] Vec3)

private def centeredCompletionInput (hT : 0 < T) (V : VP) : HierarchySmoothProfile T Vec3 :=
  V.val - HierarchySmoothProfile.profilePhaseAverage hT V.val

private theorem phaseAverage_centeredCompletionInput (hT : 0 < T) (V : VP) :
    HierarchySmoothProfile.profilePhaseAverage hT (centeredCompletionInput hT V) = 0 := by
  have hidem := congrArg Subtype.val (profilePhaseAverage_idempotent hT V)
  change HierarchySmoothProfile.profilePhaseAverage hT
    (HierarchySmoothProfile.profilePhaseAverage hT V.val) =
      HierarchySmoothProfile.profilePhaseAverage hT V.val at hidem
  rw [centeredCompletionInput, map_sub, hidem, sub_self]

private theorem phasePeriodic_centeredCompletionInput (hT : 0 < T) (V : VP)
    (t : ℝ) (ht : t ∈ Icc 0 T) (a : Vec3) :
    Function.Periodic (fun s => (centeredCompletionInput hT V).val (t, a, s)) 1 := by
  intro s
  have hp : V.val.val (t, a, s + 1) = V.val.val (t, a, s) := phasePeriodic V t a s
  have hs : (t, a, s) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  have hs' : (t, a, s + 1) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  simp only [centeredCompletionInput, Submodule.coe_sub, Pi.sub_apply,
    HierarchySmoothProfile.profilePhaseAverage_apply _ _ hs,
    HierarchySmoothProfile.profilePhaseAverage_apply _ _ hs', hp]

/-- The periodic completion is defined on the entire profile space by
first centering its input. On the admissible transverse subspace it
is the original completion of the frozen hierarchy. -/
def complete (hT : 0 < T) (G : VPmap) (κ : VP)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val (t, a, 0) ≠ 0) (V : VP) : VP := by
  let V₀ := centeredCompletionInput hT V
  let Q := HierarchySmoothProfile.profileWavePotential hT κ.val hκ V₀
  refine ofPeriodicSlices (HierarchySmoothProfile.profileCompletion hT G.val κ.val hκ V₀)
    (fun t ht a => ?_)
  change Function.Periodic (fun s => (HierarchySmoothProfile.profileSlowCurl hT G.val Q).val (t, a, s)) 1
  apply HierarchySmoothProfile.profileSlowCurl_phasePeriodic hT G.val Q ht (phasePeriodic G t) _ a
  intro b
  have hb : (t, b, (0 : ℝ)) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  have hzero : phaseMean (fun s => V₀.val (t, b, s)) = 0 := by
    rw [← HierarchySmoothProfile.profilePhaseAverage_apply hT V₀ hb,
      phaseAverage_centeredCompletionInput hT V]
    rfl
  exact HierarchySmoothProfile.profileWavePotential_phasePeriodic hT κ.val hκ V₀ ht b
    (phasePeriodic_centeredCompletionInput hT V t ht b) hzero

theorem complete_val_of_phaseMean_zero (hT : 0 < T) (G : VPmap) (κ : VP)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val (t, a, 0) ≠ 0) (V : VP)
    (hV : profilePhaseAverage hT V = 0) :
    (complete hT G κ hκ V).val = HierarchySmoothProfile.profileCompletion hT G.val κ.val hκ V.val := by
  have h := congrArg Subtype.val hV
  change HierarchySmoothProfile.profilePhaseAverage hT V.val = 0 at h
  change HierarchySmoothProfile.profileCompletion hT G.val κ.val hκ
    (centeredCompletionInput hT V) = _
  simp only [centeredCompletionInput, h, sub_zero]

/-- A phase-independent inverse coframe gives a zero-mean completion.
This supplies the `average_complete` field of the finite solver. -/
theorem average_complete (hT : 0 < T) (G M : VPmap) (κ : VP)
    (hG : PhaseIndependent G.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val (t, a, 0) ≠ 0) (V : VP) :
    (periodicHierarchyOperators hT G M κ).average (complete hT G κ hκ V) = 0 := by
  apply Subtype.ext
  change HierarchySmoothProfile.profilePhaseAverage hT
    (HierarchySmoothProfile.profileCompletion hT G.val κ.val hκ (centeredCompletionInput hT V)) = 0
  exact HierarchySmoothProfile.profilePhaseAverage_completion hT G.val κ.val
    (fun t ht a s => hG (t, a, 0) ⟨ht, mem_univ _⟩ s) hκ _

end
end HierarchyPeriodicProfile

end TorusEuler
