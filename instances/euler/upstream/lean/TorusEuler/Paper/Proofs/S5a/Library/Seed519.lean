import TorusEuler.Paper.S5.Vocabulary
import TorusEuler.Paper.Proofs.S5Bridge.Parent
import TorusEuler.Paper.Proofs.S5Bridge.Seed
import TorusEuler.Paper.Proofs.S5Bridge.Parent
import TorusEuler.Paper.S5.Statements
import TorusEuler.LocalizedAmplitudeComparison

/-!
# S5a library: the localized seed with the near-origin bounds (5.19) from (D.6)

Route of the TeX proof of Lemma 5.3 to (5.19) (`sections/06c_finite_hierarchy.tex:105-158`):
the label-Lipschitz bounds of the coframe `D_aX`, `(D_aX)^{-1}`, the material gradient `M` and the
projection `P_κ` come from the first label derivatives (D.6) of Proposition 5.1 (hypothesis
`hD6` below, supplied from `h5_1`), and the Duhamel construction in the fixed transverse coframe
(`exists_seedOn_of_coframe_bounds`, own content of row 5.3) proves the near-origin bounds.

Copies (library originals in `TorusEuler/LocalizedAmplitudeComparison.lean`):
* `exists_common_envelope_exponent_pow` is `LocalizedAmplitude.exists_common_envelope_exponent`
  (:1353) with the label-Lipschitz constant `c D^24` replaced by `c D^p` (the exponent `24` and the
  resulting `35` are replaced by `p` and `11 + p`);
* `continuousOn_inverse_coframe` is the private lemma of that name (:1428), unchanged;
* `labelLipschitz_of_D6` is `exists_parent_coefficient_label_lipschitz` (:756), whose call to the
  content `exists_parent_coefficientJetBounds` of row 5.1 is replaced by the hypothesis `hD6`
  (first label jets from (D.6));
* `exists_seedOn_of_D6` is `exists_seedOn_of_parent_bounds` (:1537) over the latter.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5a

noncomputable section

open HierarchyTwistedProfile LocalizedAmplitude

/-- One absolute envelope exponent enforces both the fixed-coordinate
Duhamel perturbation budget and the physical coupling budget. -/
theorem exists_common_envelope_exponent_pow (c : ℝ) (hc : 0 ≤ c) (p : ℕ) :
    ∃ A : ℕ, 3 ≤ A ∧ ∀ {D ell : ℝ}, 2 ≤ D → 0 ≤ ell → ell ≤ (D ^ A)⁻¹ →
      let L := c * D ^ p
      D ^ 3 * generatorLabelSlope D L L L L * (2 * ell) ≤ 1 ∧
        nearLabelSlope D L L L L * (2 * ell) ≤ (8 * D ^ 2)⁻¹ := by
  let C := (11 + 8 * Real.exp 1) * c
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  obtain ⟨A, hA, hRadius⟩ := exists_envelopeExponent_for_label_error C (1 / 8)
    hC (by norm_num) (11 + p) 2
  refine ⟨A, hA, ?_⟩
  intro D ell hD hell hEll
  let L := c * D ^ p
  let g := generatorLabelSlope D L L L L
  let a := amplitudeLabelSlope D L L L L
  let n := nearLabelSlope D L L L L
  change D ^ 3 * g * (2 * ell) ≤ 1 ∧ n * (2 * ell) ≤ (8 * D ^ 2)⁻¹
  have hD₀ : 0 ≤ D := by linarith
  have hD₁ : 1 ≤ D := by linarith
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hLd : L ≤ D * L := le_mul_of_one_le_left hL hD₁
  have hG : g ≤ 8 * D ^ 3 * L := by
    dsimp only [g, generatorLabelSlope]
    have h := show L + (L + D * L) + L ≤ 4 * (D * L) by linarith
    exact (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * D ^ 2)).trans_eq (by ring)
  have hD5 : D ^ 5 ≤ D ^ 11 := pow_le_pow_right₀ hD₁ (by norm_num)
  have hD6 : D ^ 6 ≤ D ^ 11 := pow_le_pow_right₀ hD₁ (by norm_num)
  have hD11 : D ≤ D ^ 11 := by
    simpa only [pow_one] using pow_le_pow_right₀ hD₁ (show (1 : ℕ) ≤ 11 by norm_num)
  have hDL : D * L ≤ D ^ 11 * L := mul_le_mul_of_nonneg_right hD11 hL
  have hBase : 0 ≤ D ^ 11 * L := by positivity
  have hAmp : a ≤ (3 + 8 * Real.exp 1) * (D ^ 11 * L) := by
    have h1 : D ^ 3 * (L + D * L) ≤ D ^ 3 * (2 * (D * L)) :=
      mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hD₀ _)
    have h2 : Real.exp 1 * (D ^ 3) ^ 2 * D * g ≤
        Real.exp 1 * (D ^ 3) ^ 2 * D * (8 * D ^ 3 * L) :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    calc
      a ≤ D * (D ^ 3 * (2 * (D * L)) +
          Real.exp 1 * (D ^ 3) ^ 2 * D * (8 * D ^ 3 * L)) + L * D := by
        dsimp only [a, amplitudeLabelSlope, g]
        exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add h1 h2) hD₀) le_rfl
      _ = 2 * (D ^ 5 * L) + 8 * Real.exp 1 * (D ^ 11 * L) + D * L := by ring
      _ ≤ 2 * (D ^ 11 * L) + 8 * Real.exp 1 * (D ^ 11 * L) + D ^ 11 * L := by
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hD5 hL) (by norm_num)) le_rfl) hDL
      _ = (3 + 8 * Real.exp 1) * (D ^ 11 * L) := by ring
  have hCoeff : (11 + 8 * Real.exp 1) * (D ^ 11 * L) = C * D ^ (11 + p) := by
    dsimp only [C, L]
    ring
  have hFgen : D ^ 3 * g ≤ C * D ^ (11 + p) := by
    rw [← hCoeff]
    calc
      _ ≤ D ^ 3 * (8 * D ^ 3 * L) := mul_le_mul_of_nonneg_left hG (by positivity)
      _ = 8 * (D ^ 6 * L) := by ring
      _ ≤ 8 * (D ^ 11 * L) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hD6 hL) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [Real.exp_pos 1]) hBase
  have hFnear : n ≤ C * D ^ (11 + p) := by
    rw [← hCoeff]
    dsimp only [n, nearLabelSlope]
    refine max_le (hAmp.trans (mul_le_mul_of_nonneg_right (by linarith) hBase)) ?_
    have hUpper : D ^ 11 * L ≤ (11 + 8 * Real.exp 1) * (D ^ 11 * L) :=
      le_mul_of_one_le_left hBase (by linarith [Real.exp_pos 1])
    have hLD : L * D ≤ D ^ 11 * L := by simpa only [mul_comm L D] using hDL
    exact max_le (hLD.trans hUpper) ((hLd.trans hDL).trans hUpper)
  have hr := hRadius hD hEll
  have hReq : (1 / 8 : ℝ) * (D ^ 2)⁻¹ = (8 * D ^ 2)⁻¹ := by field_simp
  rw [hReq] at hr
  have hInv : (8 * D ^ 2)⁻¹ ≤ 1 := by
    have hD2 : 1 ≤ D ^ 2 := one_le_pow₀ hD₁
    simpa only [inv_one] using inv_anti₀ (show (0 : ℝ) < 1 by norm_num)
      (show 1 ≤ 8 * D ^ 2 by linarith)
  exact ⟨((mul_le_mul_of_nonneg_right hFgen (by positivity)).trans hr).trans hInv,
    (mul_le_mul_of_nonneg_right hFnear (by positivity)).trans hr⟩


/-- Continuity of the pointwise inverse of a coframe family given by a left inverse. -/
theorem continuousOn_inverse_coframe
    {F G : ℝ → Vec3 →L[ℝ] Vec3} {I : Set ℝ} {D : ℝ}
    (hD : 0 < D) (hF : ContinuousOn F I)
    (hGF : ∀ t ∈ I, (G t).comp (F t) = .id ℝ Vec3)
    (hFG : ∀ t ∈ I, (F t).comp (G t) = .id ℝ Vec3)
    (hG : ∀ t ∈ I, ‖G t‖ ≤ D) : ContinuousOn G I := by
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hDsq : 0 < D ^ 2 := sq_pos_of_pos hD
  obtain ⟨δ, hδ, hFδ⟩ := Metric.continuousWithinAt_iff.mp (hF t ht)
    (ε / D ^ 2) (div_pos hε hDsq)
  refine ⟨δ, hδ, fun u hu hud => ?_⟩
  have heq : G u - G t = (G u).comp ((F t - F u).comp (G t)) := by
    apply ContinuousLinearMap.ext
    intro x
    change G u x - G t x = G u ((F t - F u) (G t x))
    have htu : F t (G t x) = x := DFunLike.congr_fun (hFG t ht) x
    have hut : G u (F u (G t x)) = G t x := DFunLike.congr_fun (hGF u hu) (G t x)
    rw [sub_apply, map_sub, htu, hut]
  have hnorm : ‖G u - G t‖ ≤ D ^ 2 * ‖F u - F t‖ := by
    rw [heq]
    calc
      _ ≤ ‖G u‖ * (‖F t - F u‖ * ‖G t‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ D * (‖F t - F u‖ * D) :=
        mul_le_mul (hG u hu) (mul_le_mul_of_nonneg_left (hG t ht) (norm_nonneg _))
          (by positivity) hD.le
      _ = _ := by rw [norm_sub_rev (F u) (F t)]; ring
  have h := hFδ hu hud
  rw [dist_eq_norm] at h ⊢
  exact hnorm.trans_lt ((mul_lt_mul_of_pos_left h hDsq).trans_eq
    (by field_simp))


/-- Difference bound for a label-dependent field from its first jet. -/
private theorem norm_label_difference_le_of_first_jet'
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : Vec3 → V} {C : ℝ}
    (hf : Differentiable ℝ f) (hC : ∀ a, ‖iteratedFDeriv ℝ 1 f a‖ ≤ C) (a b : Vec3) :
    ‖f a - f b‖ ≤ C * ‖a - b‖ :=
  (convex_univ : Convex ℝ (univ : Set Vec3)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hf x) (fun x _ => by simpa only [norm_iteratedFDeriv_one] using hC x)
    (mem_univ b) (mem_univ a)

/-- Copy of `exists_parent_coefficient_label_lipschitz`
(`LocalizedAmplitudeComparison.lean:756`) with the first label jets of the coefficients given by
the hypothesis `hD6` (the case `m = 1` of (D.6) of Proposition 5.1) instead of the library
content `exists_parent_coefficientJetBounds`. -/
theorem labelLipschitz_of_D6
    {T D lam t₀ : ℝ} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
    (hT : 0 < T) (hP : S5.Parent T U X pU D lam) (hL : S5.Launch T X k lam t₀)
    (c : ℝ) (p : ℕ) (hc : 0 ≤ c)
    (hD6 : ∀ t ∈ Icc 0 T, ∀ a : Vec3,
      ‖iteratedFDeriv ℝ 1 (fun b => fderiv ℝ (X 0 t) b) a‖ ≤ c * D ^ p ∧
      ‖iteratedFDeriv ℝ 1 (fun b => fderiv ℝ (X t 0) (X 0 t b)) a‖ ≤ c * D ^ p ∧
      ‖iteratedFDeriv ℝ 1 (S5.strainField U X t) a‖ ≤ c * D ^ p ∧
      ‖iteratedFDeriv ℝ 1 (fun b => lam⁻¹ • S5.waveVector X k t b) a‖ ≤ c * D ^ p ∧
      ‖iteratedFDeriv ℝ 1 (fun b => (‖S5.waveVector X k t b‖ ^ 2)⁻¹ •
        InnerProductSpace.rankOne ℝ (S5.waveVector X k t b) (S5.waveVector X k t b)) a‖ ≤
          c * D ^ p) :
    ∀ t ∈ Icc 0 T, ∀ a b : Vec3,
      let F := fderiv ℝ (X 0 t)
      let G (x : Vec3) := fderiv ℝ (X t 0) (X 0 t x)
      let M (x : Vec3) := fderiv ℝ (U t) (X 0 t x)
      let κ (x : Vec3) := labelWaveVector X 0 x k t
      ‖F a - F b‖ ≤ c * D ^ p * ‖a - b‖ ∧
      ‖G a - G b‖ ≤ c * D ^ p * ‖a - b‖ ∧
      ‖M a - M b‖ ≤ c * D ^ p * ‖a - b‖ ∧
      ‖κ a - κ b‖ ≤ c * D ^ (p + 2) * ‖a - b‖ * ‖κ b‖ ∧
      ‖oscillatoryTransverseProjection (κ a) - oscillatoryTransverseProjection (κ b)‖ ≤
        c * D ^ p * ‖a - b‖ := by
  have hX := hP.flow
  have hU := hP.velocity_smooth
  have hper := hP.velocity_periodic
  have hF := hP.deformation_le
  have hG := hP.inverse_deformation_le
  have hD : 1 ≤ D := by linarith [hP.scale_ge_two]
  have hΛ : 0 < lam := by linarith [hP.frequency_ge_one]
  have ht₀ : t₀ ∈ Icc 0 T := ⟨hL.start_nonneg, hL.start_lt.le⟩
  have hcenter : ‖labelWaveVector X 0 0 k t₀‖ = lam := hL.frequency
  intro t ht a b
  dsimp only
  let F := fderiv ℝ (X 0 t)
  let G (x : Vec3) := fderiv ℝ (X t 0) (X 0 t x)
  let M (x : Vec3) := fderiv ℝ (U t) (X 0 t x)
  let κ (x : Vec3) := labelWaveVector X 0 x k t
  let κN (x : Vec3) := lam⁻¹ • κ x
  let P (x : Vec3) := (‖κ x‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ (κ x) (κ x)
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hU₂ : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hU.of_le (by simp)
  have hFlow : ContDiff ℝ 2 (X 0 t) := (hX.labelJets_evolve 2 hT hU hper).1 t ht
  have hFd : ContDiff ℝ 1 F := hFlow.fderiv_right (by norm_num)
  have hGd : ContDiff ℝ 1 G :=
    hX.contDiff_inverseLabelDerivative hT hU₂ hper h₀ ht (n := 1) hFlow
  have hU' : ContDiff ℝ ∞ (U t) :=
    contDiffOn_univ.mp (hU.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  have hGrad : ContDiff ℝ 1 (fderiv ℝ (U t)) :=
    ((contDiff_infty_iff_fderiv.mp hU').2).of_le (by simp)
  have hMd : ContDiff ℝ 1 M := hGrad.comp (hFlow.of_le (by norm_num))
  let J := ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)
  have hκd : ContDiff ℝ 1 κ := (J.toContinuousLinearEquiv.contDiff.comp hGd).clm_apply contDiff_const
  have hκNd : ContDiff ℝ 1 κN := by
    change ContDiff ℝ 1 (fun x => lam⁻¹ • κ x)
    exact (contDiff_const (c := lam⁻¹)).smul hκd
  have hLower (x : Vec3) : (D ^ 2)⁻¹ ≤ ‖κN x‖ :=
    (hX.norm_normalizedLabelWaveVector_bounds hT hU₂ hper ht₀ ht x k hD hΛ hcenter
      (hF t₀ ht₀ 0) (hG t₀ ht₀ 0) (hF t ht x) (hG t ht x)).2.1
  have hκnz (x : Vec3) : κ x ≠ 0 := by
    intro hzero
    have h := hLower x
    simp only [κN, hzero, smul_zero, norm_zero] at h
    exact (not_le_of_gt (show 0 < (D ^ 2)⁻¹ by positivity)) h
  have hQ : ContDiff ℝ 1 (fun x => ‖κ x‖ ^ 2) := by
    simp_rw [← real_inner_self_eq_norm_sq]
    exact ((innerSL ℝ (E := Vec3)).contDiff.comp hκd).clm_apply hκd
  let A : Vec3 →L[ℝ] (Vec3 →L[ℝ] (Vec3 →L[ℝ] Vec3)) := InnerProductSpace.rankOne ℝ
  have hPRank : ContDiff ℝ 1 (fun x => InnerProductSpace.rankOne ℝ (κ x) (κ x)) := by
    change ContDiff ℝ 1 (fun x => A (κ x) (κ x))
    exact (A.contDiff.comp hκd).clm_apply hκd
  have hPd : ContDiff ℝ 1 P :=
    (hQ.inv fun x => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hκnz x))).smul hPRank
  have hJet (x : Vec3) := hD6 t ht x
  have hFdiff := norm_label_difference_le_of_first_jet' (hFd.differentiable (by norm_num))
    (fun x => (hJet x).1) a b
  have hGdiff := norm_label_difference_le_of_first_jet' (hGd.differentiable (by norm_num))
    (fun x => (hJet x).2.1) a b
  have hMdiff := norm_label_difference_le_of_first_jet' (hMd.differentiable (by norm_num))
    (fun x => (hJet x).2.2.1) a b
  have hκNdiff := norm_label_difference_le_of_first_jet' (hκNd.differentiable (by norm_num))
    (fun x => (hJet x).2.2.2.1) a b
  have hPdiff := norm_label_difference_le_of_first_jet' (hPd.differentiable (by norm_num))
    (fun x => (hJet x).2.2.2.2) a b
  have hNorm (v : Vec3) : ‖lam⁻¹ • v‖ = ‖v‖ / lam := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hΛ), div_eq_mul_inv, mul_comm]
  have hκAbs : ‖κ a - κ b‖ ≤ c * D ^ p * ‖a - b‖ * lam := by
    change ‖lam⁻¹ • κ a - lam⁻¹ • κ b‖ ≤ c * D ^ p * ‖a - b‖ at hκNdiff
    rw [← smul_sub, hNorm] at hκNdiff
    exact (div_le_iff₀ hΛ).mp hκNdiff
  have hΛbound : lam ≤ D ^ 2 * ‖κ b‖ := by
    have hx := hLower b
    change (D ^ 2)⁻¹ ≤ ‖lam⁻¹ • κ b‖ at hx
    rw [hNorm, ← one_div (D ^ 2)] at hx
    have hl := (div_le_div_iff₀ (by positivity : 0 < D ^ 2) hΛ).mp hx
    simpa only [one_mul, mul_one, mul_comm] using hl
  have hκdiff : ‖κ a - κ b‖ ≤ c * D ^ (p + 2) * ‖a - b‖ * ‖κ b‖ := by
    calc
      _ ≤ c * D ^ p * ‖a - b‖ * lam := hκAbs
      _ ≤ c * D ^ p * ‖a - b‖ * (D ^ 2 * ‖κ b‖) :=
        mul_le_mul_of_nonneg_left hΛbound
          (mul_nonneg (mul_nonneg hc (by positivity)) (norm_nonneg _))
      _ = _ := by ring
  have hQdiff :
      ‖oscillatoryTransverseProjection (κ a) - oscillatoryTransverseProjection (κ b)‖ =
        ‖P a - P b‖ := by
    change ‖(.id ℝ Vec3 - P a) - (.id ℝ Vec3 - P b)‖ = _
    rw [sub_sub_sub_cancel_left, norm_sub_rev]
  exact ⟨hFdiff, hGdiff, hMdiff, hκdiff, hQdiff.trans_le hPdiff⟩

/-- Copy of `exists_seedOn_of_parent_bounds` (`LocalizedAmplitudeComparison.lean:1537`) over the
standing parent of §5.1: the label-Lipschitz bounds come from `labelLipschitz_of_D6` (hypothesis
`hD6`, the first label jets (D.6)), and the amplitude comes from the Duhamel construction
`exists_seedOn_of_coframe_bounds` (own content of Lemma 5.3, TeX 105-158). The radius threshold is
`exists_common_envelope_exponent_pow`. -/
theorem exists_seedOn_of_D6 (c : ℝ) (hc : 0 ≤ c) (p : ℕ) :
    ∃ A : ℕ, 3 ≤ A ∧
      ∀ {T D lam t₀ ell : ℝ} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
        {center : ℝ → Vec3},
        0 < T → S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ →
        S5.Origin T U X k D lam t₀ center →
        (∀ t ∈ Icc 0 T, ∀ a : Vec3,
          ‖iteratedFDeriv ℝ 1 (fun b => fderiv ℝ (X 0 t) b) a‖ ≤ c * D ^ p ∧
          ‖iteratedFDeriv ℝ 1 (fun b => fderiv ℝ (X t 0) (X 0 t b)) a‖ ≤ c * D ^ p ∧
          ‖iteratedFDeriv ℝ 1 (S5.strainField U X t) a‖ ≤ c * D ^ p ∧
          ‖iteratedFDeriv ℝ 1 (fun b => lam⁻¹ • S5.waveVector X k t b) a‖ ≤ c * D ^ p ∧
          ‖iteratedFDeriv ℝ 1 (fun b => (‖S5.waveVector X k t b‖ ^ 2)⁻¹ •
            InnerProductSpace.rankOne ℝ (S5.waveVector X k t b) (S5.waveVector X k t b)) a‖ ≤
              c * D ^ p) →
        0 < ell → ell ≤ (D ^ A)⁻¹ →
        Nonempty (SeedOn (fun t a => fderiv ℝ (U t) (X 0 t a))
          (fun t a => labelWaveVector X 0 a k t) center t₀ T ell D
          (amplitudeLabelSlope D (c * D ^ (p + 2)) (c * D ^ (p + 2)) (c * D ^ (p + 2))
            (c * D ^ (p + 2)))) := by
  obtain ⟨A, hA, hRadius⟩ := exists_common_envelope_exponent_pow c hc (p + 2)
  refine ⟨A, hA, ?_⟩
  intro T D lam t₀ ell U X pU k center hT hP hL hO hD6 hell hellA
  have hX := hP.flow
  have hU := hP.velocity_smooth
  have hper := hP.velocity_periodic
  have hodd := hP.velocity_odd
  have hF := hP.deformation_le
  have hG := hP.inverse_deformation_le
  have hM := hP.gradient_le
  have hD : 2 ≤ D := hP.scale_ge_two
  have ht₀ : t₀ ∈ Icc 0 T := ⟨hL.start_nonneg, hL.start_lt.le⟩
  have hT₁ : T ≤ 1 := hP.time_le_one
  have hCenter := Bridge.Origin.centerWaveOn_gradient hP hL hO
  have hkdef := Bridge.Launch.carrier_eq hP hL
  generalize hκ : (fun t => S5.waveVector X k t 0) = κ at hCenter hkdef
  have hκt : κ t₀ = S5.waveVector X k t₀ 0 := by rw [← hκ]
  obtain ⟨hSmall, hNear⟩ := hRadius hD hell.le hellA
  let L := c * D ^ (p + 2)
  have hkdef' : (fderiv ℝ (X 0 t₀) (0 : Vec3)).adjoint (κ t₀) = k := by rw [hκt]; exact hkdef
  let F (t : ℝ) (a : Vec3) := fderiv ℝ (X 0 t) a
  let G (t : ℝ) (a : Vec3) := fderiv ℝ (X t 0) (X 0 t a)
  let M (t : ℝ) (a : Vec3) := fderiv ℝ (U t) (X 0 t a)
  have hDone : 1 ≤ D := by linarith
  have hDpos : 0 < D := by linarith
  have hL₀ : 0 ≤ L := by dsimp only [L]; positivity
  have hU₂ : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hU.of_le (by simp)
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hStart : t₀ ∈ Icc t₀ T := left_mem_Icc.mpr ht₀.2
  have hsub : Icc t₀ T ⊆ Icc 0 T := Icc_subset_Icc_left ht₀.1
  obtain ⟨Lp, hLp⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU₂.of_le (by norm_num)) hper
  have hFix (t : ℝ) (ht : t ∈ Icc 0 T) : X 0 t (0 : Vec3) = 0 := by
    have he := hX.odd hLp hodd h₀ ht (0 : Vec3)
    rw [neg_zero] at he
    ext i
    have hi := congrArg (fun y : Vec3 => y i) he
    simp only [PiLp.neg_apply] at hi
    simpa only [PiLp.zero_apply] using (show (X 0 t 0) i = 0 by linarith)
  have hMzero (t : ℝ) (ht : t ∈ Icc t₀ T) : M t 0 = fderiv ℝ (U t) 0 := by
    simp only [M, hFix t (hsub ht)]
  obtain ⟨hknz, hkc⟩ := hX.center_coframe_covector_eq hT hU₂ hper hodd ht₀ hCenter.covector
  rw [hkdef'] at hkc
  have hk : k ≠ 0 := by rw [← hkdef']; exact hknz (hCenter.nonzero t₀ hStart).1
  have hkeq (t : ℝ) (ht : t ∈ Icc t₀ T) : (G t 0).adjoint k = κ t := by
    simpa only [G, hFix t (hsub ht)] using hkc t ht
  have hΛ : 0 < ‖κ t₀‖ := norm_pos_iff.mpr (hCenter.nonzero t₀ hStart).1
  have hFreq : ‖labelWaveVector X 0 0 k t₀‖ = ‖κ t₀‖ :=
    congrArg norm (hkeq t₀ hStart)
  have hFder (a : Vec3) (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun u => F u a) ((M t a).comp (F t a)) (Icc 0 T) t :=
    (hX.labelDerivative_evolves hT hU₂ hper h₀ a).2 t ht
  have hInv (a : Vec3) (t : ℝ) (ht : t ∈ Icc 0 T) :
      (G t a).comp (F t a) = .id ℝ Vec3 ∧ (F t a).comp (G t a) = .id ℝ Vec3 :=
    hX.labelDerivative_inverse hT hU₂ hper h₀ ht a
  have hGtime (a : Vec3) : ContinuousOn (fun t => G t a) (Icc 0 T) :=
    continuousOn_inverse_coframe hDpos (HasDerivWithinAt.continuousOn (hFder a))
      (fun t ht => (hInv a t ht).1) (fun t ht => (hInv a t ht).2)
      (fun t ht => hG t ht a)
  have hMtime (a : Vec3) : ContinuousOn (fun t => M t a) (Icc 0 T) := by
    have hgrad : ContDiffOn ℝ 1 (fun p : ℝ × Vec3 => fderiv ℝ (U p.1) p.2)
        (Icc 0 T ×ˢ univ) :=
      contDiffOn_spatialDerivative_of_joint_contDiff (n := 1) (uniqueDiffOn_Icc hT) (by
        convert hU₂ using 1
        norm_num)
    exact hgrad.continuousOn.comp
      (continuous_id.continuousOn.prodMk (HasDerivWithinAt.continuousOn (hX.trajectory 0 h₀ a)))
      (fun t ht => ⟨ht, mem_univ _⟩)
  have hLC (q : ℕ) (hq : q ≤ p + 2) (a : Vec3) : c * D ^ q * ‖a‖ ≤ L * ‖a‖ := by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hDone hq) hc
  have hLactual (a : Vec3) (t : ℝ) (ht : t ∈ Icc t₀ T) :
      ‖F t a - F t 0‖ ≤ L * ‖a‖ ∧ ‖G t a - G t 0‖ ≤ L * ‖a‖ ∧
      ‖M t a - M t 0‖ ≤ L * ‖a‖ ∧
      ‖oscillatoryTransverseProjection ((G t a).adjoint k) -
        oscillatoryTransverseProjection ((G t 0).adjoint k)‖ ≤ L * ‖a‖ := by
    have hc' := labelLipschitz_of_D6 hT hP hL c p hc hD6 t (hsub ht) a 0
    simp only [sub_zero] at hc'
    exact ⟨hc'.1.trans (hLC p (by omega) a), hc'.2.1.trans (hLC p (by omega) a),
      hc'.2.2.1.trans (hLC p (by omega) a), hc'.2.2.2.2.trans (hLC p (by omega) a)⟩
  have hcBoth (t : ℝ) (ht : t ∈ Icc t₀ T) :
      center t ≠ 0 ∧ ⟪(G t 0).adjoint k, center t⟫_ℝ = 0 ∧
      HasDerivWithinAt center
        (affineWaveAmplitudeOperator (M t 0) ((G t 0).adjoint k) (center t)) (Icc t₀ T) t := by
    rw [hkeq t ht, hMzero t ht]
    exact ⟨(hCenter.nonzero t ht).2.1, (hCenter.nonzero t ht).2.2, hCenter.amplitude t ht⟩
  refine exists_seedOn_of_coframe_bounds hk ht₀.2 (by linarith [ht₀.1]) hDone
    (fun a t ht => (hFder a t (hsub ht)).mono hsub) (fun a => (hGtime a).mono hsub)
    (fun a => (hMtime a).mono hsub) (fun a t ht => hInv a t (hsub ht))
    (fun a t ht => ⟨hF t (hsub ht) a, hG t (hsub ht) a, hM t (hsub ht) (X 0 t a)⟩)
    hLactual ⟨hL₀, hL₀, hL₀, hL₀⟩ hcBoth ?_ ?_ hSmall hNear
  · intro z hz hp u v hu hv huv
    refine hCenter.stability z (fun t ht => ?_) (fun t ht => ?_) hu hv huv
    · rw [← hkeq t ht, ← hMzero t ht]
      exact hz t ht
    · rw [← hkeq t ht]
      exact hp t ht
  · intro t ht
    change D⁻¹ * (‖(G t 0).adjoint k‖ * ‖center t‖) ≤
      ⟪(G t 0).adjoint k, M t 0 (center t)⟫_ℝ
    rw [hkeq t ht, hMzero t ht]
    exact hCenter.coupling t ht

end

end TorusEuler.Paper.Lib.S5a
