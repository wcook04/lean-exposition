import Breakdown.FracCell.StCylModeWeak

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert CellAnalysis

private theorem weakCLM {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    {f : Space → F} {g : Space → (Space →L[ℝ] F)} (hf : LocallyIntegrable f volume)
    (hg : ∀ j, LocallyIntegrable (fun y => g y (unitVector j)) volume)
    (hw : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) • f y = -∫ y, φ y • g y (unitVector j))
    {Φ : Space → (F →L[ℝ] ℂ)} (hΦ : ContDiff ℝ ∞ Φ) (hc : HasCompactSupport Φ) (j : Fin 3) :
    ∫ y, fderiv ℝ Φ y (unitVector j) (f y) = -∫ y, Φ y (g y (unitVector j)) := by
  set B := Module.finBasis ℝ (F →L[ℝ] ℂ)
  let crd : Fin (Module.finrank ℝ (F →L[ℝ] ℂ)) → (F →L[ℝ] ℂ) →L[ℝ] ℝ :=
    fun i => LinearMap.toContinuousLinearMap (B.coord i)
  have hexp : ∀ (A : F →L[ℝ] ℂ) (u : F), A u = ∑ i, crd i A • B i u := by
    intro A u
    conv_lhs => rw [← B.sum_repr A]
    simp only [crd, LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply, FunLike.coe_sum,
      Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply]
  have hφ : ∀ i, IsTestScalar (fun y => crd i (Φ y)) := fun i =>
    ⟨(crd i).contDiff.comp hΦ, hc.comp_left (map_zero _)⟩
  have hd : ∀ i y v, fderiv ℝ (fun y => crd i (Φ y)) y v = crd i (fderiv ℝ Φ y v) := by
    intro i y v
    have hΦd : DifferentiableAt ℝ Φ y := hΦ.differentiable (by simp) y
    have h := ((crd i).hasFDerivAt.comp y hΦd.hasFDerivAt).fderiv
    simp only [Function.comp_def] at h
    rw [h]
    rfl
  have i1 : ∀ i, Integrable (fun y => fderiv ℝ (fun y => crd i (Φ y)) y (unitVector j) • f y) volume := fun i =>
    hf.integrable_smul_left_of_hasCompactSupport
      (((hφ i).1.continuous_fderiv (by simp)).clm_apply continuous_const) ((hφ i).2.fderiv_apply (𝕜 := ℝ) _)
  have i2 : ∀ i, Integrable (fun y => crd i (Φ y) • g y (unitVector j)) volume := fun i =>
    (hg j).integrable_smul_left_of_hasCompactSupport (hφ i).1.continuous (hφ i).2
  have L1 : ∫ y, fderiv ℝ Φ y (unitVector j) (f y) =
      ∑ i, B i (∫ y, fderiv ℝ (fun y => crd i (Φ y)) y (unitVector j) • f y) := by
    have e : ∀ y, fderiv ℝ Φ y (unitVector j) (f y) =
        ∑ i, B i (fderiv ℝ (fun y => crd i (Φ y)) y (unitVector j) • f y) := by
      intro y
      rw [hexp]
      simp only [hd, map_smul]
    simp_rw [e]
    rw [integral_finsetSum _ fun i _ => (B i).integrable_comp (i1 i)]
    exact Finset.sum_congr rfl fun i _ => (B i).integral_comp_comm (i1 i)
  have L2 : ∫ y, Φ y (g y (unitVector j)) = ∑ i, B i (∫ y, crd i (Φ y) • g y (unitVector j)) := by
    have e : ∀ y, Φ y (g y (unitVector j)) = ∑ i, B i (crd i (Φ y) • g y (unitVector j)) := by
      intro y
      rw [hexp]
      simp only [map_smul]
    simp_rw [e]
    rw [integral_finsetSum _ fun i _ => (B i).integrable_comp (i2 i)]
    exact Finset.sum_congr rfl fun i _ => (B i).integral_comp_comm (i2 i)
  rw [L1, L2, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hw _ (hφ i) j, map_neg]

private theorem coord_smooth (i : Fin 3) : ContDiff ℝ ∞ (fun y : Space => y i) :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff

private theorem rad_cont : Continuous cylRadius := by
  unfold cylRadius
  exact Real.continuous_sqrt.comp (((coord_smooth 0).continuous.pow 2).add ((coord_smooth 1).continuous.pow 2))

private theorem rad_smoothAt {y : Space} (hy : 0 < cylRadius y) : ContDiffAt ℝ ∞ cylRadius y := by
  have hne : y 0 ^ 2 + y 1 ^ 2 ≠ 0 := by
    unfold cylRadius at hy; exact (Real.sqrt_pos.1 hy).ne'
  exact ((((coord_smooth 0).pow 2).add ((coord_smooth 1).pow 2)).contDiffAt).sqrt hne

private theorem abs_coord_le (y : Space) (i : Fin 2) : |y i.castSucc| ≤ cylRadius y := by
  unfold cylRadius
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]

private theorem norm_le_coords (y : Space) : ‖y‖ ≤ |y 0| + |y 1| + |y 2| := by
  have h : y = ∑ j : Fin 3, y j • unitVector j := by
    ext i; fin_cases i <;> simp [unitVector, Fin.sum_univ_three]
  conv_lhs => rw [h]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp [Fin.sum_univ_three, norm_smul, unitVector]

private theorem smooth_of {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Θ : Space → E} {δ : ℝ}
    (hU : ∀ y, δ ≤ cylRadius y → ContDiffAt ℝ ∞ Θ y)
    (hZ : ∀ y, cylRadius y < δ → Θ y = 0) : ContDiff ℝ ∞ Θ := by
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  rcases lt_or_ge (cylRadius y) δ with hy | hy
  · have hev : Θ =ᶠ[nhds y] fun _ => 0 := by
      filter_upwards [(isOpen_lt rad_cont continuous_const).mem_nhds (show y ∈ {x : Space | cylRadius x < δ} from hy)]
        with x hx using hZ x hx
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact hU y hy

private theorem zero_near {E : Type} [NormedAddCommGroup E] {Θ : Space → E} {δ : ℝ} {y : Space}
    (hy : cylRadius y < δ) (hZ : ∀ y, cylRadius y < δ → Θ y = 0) : Θ =ᶠ[nhds y] fun _ => 0 := by
  filter_upwards [(isOpen_lt rad_cont continuous_const).mem_nhds (show y ∈ {x : Space | cylRadius x < δ} from hy)]
    with x hx using hZ x hx

private theorem supp_bounds {ψ : ℝ × ℝ → ℝ} (hc : HasCompactSupport ψ) (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) :
    ∃ δ > 0, ∃ R, ∀ p ∈ tsupport ψ, δ ≤ p.1 ∧ ‖p‖ ≤ R := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.exists_norm_le
  by_cases hne : (tsupport ψ).Nonempty
  · obtain ⟨p0, hp0, hmin⟩ := hc.isCompact.exists_isMinOn hne continuous_fst.continuousOn
    exact ⟨p0.1, hpos p0 hp0, R, fun p hp => ⟨hmin hp, hR p hp⟩⟩
  · exact ⟨1, one_pos, R, fun p hp => absurd ⟨p, hp⟩ hne⟩

private theorem off_supp {ψ a : ℝ × ℝ → ℝ} {δ R : ℝ} (hb : ∀ p ∈ tsupport ψ, δ ≤ p.1 ∧ ‖p‖ ≤ R)
    (ha : tsupport a ⊆ tsupport ψ) {y : Space} (hy : a (cylRadius y, y 2) ≠ 0) :
    δ ≤ cylRadius y ∧ ‖y‖ ≤ 3 * R := by
  have hm := hb _ (ha (subset_tsupport _ hy))
  refine ⟨hm.1, ?_⟩
  have h1 : |cylRadius y| ≤ R := (norm_fst_le (cylRadius y, y 2)).trans hm.2
  have h2 : |y 2| ≤ R := (norm_snd_le (cylRadius y, y 2)).trans hm.2
  have h0 := abs_coord_le y 0
  have h1' := abs_coord_le y 1
  simp only [Fin.castSucc_zero] at h0
  have hr : cylRadius y ≤ R := (le_abs_self _).trans h1
  refine (norm_le_coords y).trans ?_
  have : (1 : Fin 2).castSucc = (1 : Fin 3) := rfl
  rw [this] at h1'
  linarith

private theorem integrable_apply {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : Space → (F →L[ℝ] ℂ)} (hΦ : Continuous Φ) (hc : HasCompactSupport Φ) {X : Space → F}
    (hX : LocallyIntegrable X volume) : Integrable (fun y => Φ y (X y)) volume := by
  have h1 : Integrable (fun y => ‖Φ y‖ • X y) volume :=
    hX.integrable_smul_left_of_hasCompactSupport hΦ.norm hc.norm
  refine h1.norm.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hΦ.aestronglyMeasurable.prodMk hX.aestronglyMeasurable)
  · rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _)]
    exact (Φ y).le_opNorm (X y)

private def uvec (y : Space) : ℝ × ℝ := (y 0 / cylRadius y, y 1 / cylRadius y)

private theorem uvec_smoothAt {y : Space} (hy : 0 < cylRadius y) : ContDiffAt ℝ ∞ uvec y :=
  (((coord_smooth 0).contDiffAt).div (rad_smoothAt hy) hy.ne').prodMk
    (((coord_smooth 1).contDiffAt).div (rad_smoothAt hy) hy.ne')

private def fieldOf {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (W : ℝ × ℝ → (F →L[ℝ] ℂ))
    (a : ℝ × ℝ → ℝ) (k : ℕ) (y : Space) : F →L[ℝ] ℂ :=
  (a (cylRadius y, y 2) / cylRadius y ^ k) • W (uvec y)

private theorem pair_smoothAt {y : Space} (hy : 0 < cylRadius y) :
    ContDiffAt ℝ ∞ (fun y : Space => ((cylRadius y, y 2) : ℝ × ℝ)) y :=
  (rad_smoothAt hy).prodMk (coord_smooth 2).contDiffAt

private theorem fieldOf_smooth {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {W : ℝ × ℝ → (F →L[ℝ] ℂ)}
    (hW : ContDiff ℝ ∞ W) {ψ a : ℝ × ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ tsupport ψ) {δ R : ℝ}
    (hδ : 0 < δ) (hb : ∀ p ∈ tsupport ψ, δ ≤ p.1 ∧ ‖p‖ ≤ R) (k : ℕ) :
    ContDiff ℝ ∞ (fieldOf W a k) ∧ HasCompactSupport (fieldOf W a k) ∧
      ∀ y, cylRadius y < δ → fieldOf W a k y = 0 := by
  have hZ : ∀ y, cylRadius y < δ → fieldOf W a k y = 0 := by
    intro y hy
    have h0 : a (cylRadius y, y 2) = 0 := by
      by_contra hne
      exact absurd (off_supp hb hs hne).1 (not_le.2 hy)
    simp [fieldOf, h0]
  refine ⟨smooth_of (fun y hy => ?_) hZ, HasCompactSupport.intro (isCompact_closedBall (0 : Space) (3 * R))
    fun y hy => ?_, hZ⟩
  · have hρ : 0 < cylRadius y := hδ.trans_le hy
    exact ((ha.contDiffAt.comp y (pair_smoothAt hρ)).div ((rad_smoothAt hρ).pow k) (pow_ne_zero _ hρ.ne')).smul
      (hW.contDiffAt.comp y (uvec_smoothAt hρ))
  · have h0 : a (cylRadius y, y 2) = 0 := by
      by_contra hne
      exact hy (mem_closedBall_zero_iff.2 (off_supp hb hs hne).2)
    simp [fieldOf, h0]

private theorem coord_add_smul (y : Space) (t : ℝ) (w : Space) (i : Fin 3) : (y + t • w) i = y i + t * w i := by
  simp

private theorem deriv_z {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {W : ℝ × ℝ → (F →L[ℝ] ℂ)}
    (hW : ContDiff ℝ ∞ W) {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {δ R : ℝ}
    (hδ : 0 < δ) (hb : ∀ p ∈ tsupport ψ, δ ≤ p.1 ∧ ‖p‖ ≤ R) (y : Space) :
    fderiv ℝ (fieldOf W ψ 1) y (unitVector 2) = fieldOf W (fun p => fderiv ℝ ψ p (0, 1)) 1 y := by
  have F1 := fieldOf_smooth hW hψ subset_rfl hδ hb 1
  have F2 := fieldOf_smooth hW ((hψ.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).clm_apply contDiff_const)
    (tsupport_fderiv_apply_subset ℝ (0, 1)) hδ hb 1
  rcases lt_or_ge (cylRadius y) δ with hy | hy
  · rw [(zero_near hy F1.2.2).fderiv_eq, F2.2.2 y hy]
    simp
  · have hρ : 0 < cylRadius y := hδ.trans_le hy
    have hd : DifferentiableAt ℝ (fieldOf W ψ 1) y := F1.1.differentiable (by simp) y
    rw [← hd.lineDeriv_eq_fderiv, lineDeriv]
    have hline : (fun t : ℝ => fieldOf W ψ 1 (y + t • unitVector 2)) =
        fun t => (ψ (cylRadius y, y 2 + t) / cylRadius y ^ 1) • W (uvec y) := by
      funext t
      have e0 : (y + t • unitVector 2) 0 = y 0 := by simp [unitVector]
      have e1 : (y + t • unitVector 2) 1 = y 1 := by simp [unitVector]
      have e2 : (y + t • unitVector 2) 2 = y 2 + t := by simp [unitVector]
      simp only [fieldOf, uvec, cylRadius, e0, e1, e2]
    rw [hline]
    have h1 : HasDerivAt (fun t : ℝ => ((cylRadius y, y 2 + t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) 0 :=
      (hasDerivAt_const (0 : ℝ) (cylRadius y)).prodMk ((hasDerivAt_id (0 : ℝ)).const_add (y 2))
    have h2 : HasDerivAt (fun t => ψ (cylRadius y, y 2 + t)) (fderiv ℝ ψ (cylRadius y, y 2) (0, 1)) 0 := by
      have := (hψ.differentiable (by simp) (cylRadius y, y 2 + 0)).hasFDerivAt.comp_hasDerivAt 0 h1
      rw [add_zero] at this
      exact this
    exact ((h2.div_const _).smul_const _).deriv

private theorem fieldOf_apply {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (W : ℝ × ℝ → (F →L[ℝ] ℂ))
    (a : ℝ × ℝ → ℝ) (k : ℕ) (y : Space) (u : F) :
    fieldOf W a k y u = ((a (cylRadius y, y 2) / cylRadius y ^ k : ℝ) : ℂ) * W (uvec y) u := by
  simp [fieldOf, Complex.real_smul]

private theorem prod_deriv {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {Ξ : Space → (F →L[ℝ] ℂ)}
    {y : Space} (hΞ : DifferentiableAt ℝ Ξ y) (j : Fin 3) :
    fderiv ℝ (fun x : Space => x j • Ξ x) y (unitVector j) = y j • fderiv ℝ Ξ y (unitVector j) + Ξ y := by
  have hc : HasFDerivAt (fun x : Space => x j) (EuclideanSpace.proj j : Space →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt
  rw [show (fun x : Space => x j • Ξ x) = (fun x : Space => x j) • Ξ from rfl, (hc.smul hΞ.hasFDerivAt).fderiv]
  simp [unitVector]

private theorem deriv_r {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {W : ℝ × ℝ → (F →L[ℝ] ℂ)}
    (hW : ContDiff ℝ ∞ W) {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {δ R : ℝ}
    (hδ : 0 < δ) (hb : ∀ p ∈ tsupport ψ, δ ≤ p.1 ∧ ‖p‖ ≤ R) (y : Space) :
    fderiv ℝ (fun x : Space => x 0 • fieldOf W ψ 2 x) y (unitVector 0) +
      fderiv ℝ (fun x : Space => x 1 • fieldOf W ψ 2 x) y (unitVector 1) =
        fieldOf W (fun p => fderiv ℝ ψ p (1, 0)) 1 y := by
  have F1 := fieldOf_smooth hW hψ subset_rfl hδ hb 2
  have F2 := fieldOf_smooth hW ((hψ.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).clm_apply contDiff_const)
    (tsupport_fderiv_apply_subset ℝ (1, 0)) hδ hb 1
  rcases lt_or_ge (cylRadius y) δ with hy | hy
  · have e : ∀ j : Fin 3, (fun x : Space => x j • fieldOf W ψ 2 x) =ᶠ[nhds y] fun _ => 0 := by
      intro j
      filter_upwards [zero_near hy F1.2.2] with x hx
      simp [hx]
    rw [(e 0).fderiv_eq, (e 1).fderiv_eq, F2.2.2 y hy]
    simp
  · have hρ : 0 < cylRadius y := hδ.trans_le hy
    have hd : DifferentiableAt ℝ (fieldOf W ψ 2) y := F1.1.differentiable (by simp) y
    rw [prod_deriv hd 0, prod_deriv hd 1]
    set w : Space := y 0 • unitVector 0 + y 1 • unitVector 1 with hw_def
    have hsum : y 0 • fderiv ℝ (fieldOf W ψ 2) y (unitVector 0) + fieldOf W ψ 2 y +
        (y 1 • fderiv ℝ (fieldOf W ψ 2) y (unitVector 1) + fieldOf W ψ 2 y) =
        fderiv ℝ (fieldOf W ψ 2) y w + (2 : ℝ) • fieldOf W ψ 2 y := by
      rw [hw_def, map_add, map_smul, map_smul, two_smul]
      abel
    rw [hsum, ← hd.lineDeriv_eq_fderiv, lineDeriv]
    set ρ := cylRadius y with hρ_def
    have hcoord : ∀ t : ℝ, (y + t • w) 0 = (1 + t) * y 0 ∧ (y + t • w) 1 = (1 + t) * y 1 ∧ (y + t • w) 2 = y 2 := by
      intro t
      refine ⟨?_, ?_, ?_⟩ <;> simp [hw_def, unitVector] <;> ring
    have hrad : ∀ t : ℝ, 0 < 1 + t → cylRadius (y + t • w) = (1 + t) * ρ := by
      intro t ht
      rw [hρ_def]
      unfold cylRadius
      rw [(hcoord t).1, (hcoord t).2.1, show ((1 + t) * y 0) ^ 2 + ((1 + t) * y 1) ^ 2 =
        (1 + t) ^ 2 * (y 0 ^ 2 + y 1 ^ 2) by ring, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ht.le]
    have hev : (fun t : ℝ => fieldOf W ψ 2 (y + t • w)) =ᶠ[nhds 0]
        fun t => (ψ ((1 + t) * ρ, y 2) / ((1 + t) * ρ) ^ 2) • W (uvec y) := by
      filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with t ht
      have ht' : 0 < 1 + t := by simp only [Set.mem_Ioi] at ht; linarith
      have hu : uvec (y + t • w) = uvec y := by
        simp only [uvec, hrad t ht', (hcoord t).1, (hcoord t).2.1]
        rw [mul_div_mul_left _ _ ht'.ne', mul_div_mul_left _ _ ht'.ne']
      simp only [fieldOf, hrad t ht', (hcoord t).2.2, hu]
    have hA : HasDerivAt (fun t : ℝ => ψ ((1 + t) * ρ, y 2)) (ρ * fderiv ℝ ψ (ρ, y 2) (1, 0)) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => (((1 + t) * ρ, y 2) : ℝ × ℝ)) ((1 * ρ, 0) : ℝ × ℝ) 0 :=
        (((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const ρ).prodMk (hasDerivAt_const (0 : ℝ) (y 2))
      have := (hψ.differentiable (by simp) (((1 + 0) * ρ, y 2))).hasFDerivAt.comp_hasDerivAt 0 h1
      rw [show ((1 + 0) * ρ, y 2) = (ρ, y 2) by simp, show ((1 * ρ, 0) : ℝ × ℝ) = ρ • ((1 : ℝ), (0 : ℝ)) by
        ext <;> simp, map_smul, smul_eq_mul] at this
      exact this
    have hB : HasDerivAt (fun t : ℝ => ((1 + t) * ρ) ^ 2) (2 * ρ ^ 2) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => (1 + t) * ρ) ρ 0 := by
        simpa using ((hasDerivAt_id' (0 : ℝ)).const_add 1).mul_const ρ
      exact (h1.fun_pow 2).congr_deriv (by rw [show (2 : ℕ) - 1 = 1 from rfl]; push_cast; ring)
    have hB0 : ((1 + 0) * ρ) ^ 2 ≠ 0 := by simp [hρ.ne']
    have hder := ((hA.div hB hB0).smul_const (W (uvec y))).congr_of_eventuallyEq hev
    rw [hder.deriv]
    simp only [fieldOf]
    rw [← hρ_def, smul_smul, ← add_smul]
    congr 1
    simp only [add_zero, one_mul]
    field_simp
    ring

private theorem single_eq (i : Fin 3) (c : ℝ) : EuclideanSpace.single i c = c • unitVector i := by
  ext k
  by_cases h : k = i
  · subst h; simp [unitVector]
  · simp [unitVector, h]


private theorem key3_of {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (W : ℝ × ℝ → (F →L[ℝ] ℂ))
    (ψ : ℝ × ℝ → ℝ) (g : Space → (Space →L[ℝ] F)) (y : Space) :
    (y 0 • fieldOf W ψ 2 y) (g y (unitVector 0)) + (y 1 • fieldOf W ψ 2 y) (g y (unitVector 1)) =
      ((ψ (cylRadius y, y 2) / cylRadius y : ℝ) : ℂ) * W (y 0 / cylRadius y, y 1 / cylRadius y)
        (g y (EuclideanSpace.single 0 (y 0 / cylRadius y) + EuclideanSpace.single 1 (y 1 / cylRadius y))) := by
  rw [single_eq, single_eq, map_add, map_smul, map_smul, map_add, map_smul, map_smul]
  simp only [smul_apply, fieldOf_apply, Complex.real_smul, uvec]
  rcases eq_or_ne (cylRadius y) 0 with h | h
  · simp [h]
  · push_cast
    field_simp

private theorem prod_facts {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {W : ℝ × ℝ → (F →L[ℝ] ℂ)}
    (hW : ContDiff ℝ ∞ W) {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {δ R : ℝ}
    (hδ : 0 < δ) (hb : ∀ p ∈ tsupport ψ, δ ≤ p.1 ∧ ‖p‖ ≤ R) (j : Fin 3) :
    ContDiff ℝ ∞ (fun x : Space => x j • fieldOf W ψ 2 x) ∧
      HasCompactSupport (fun x : Space => x j • fieldOf W ψ 2 x) := by
  have F2 := fieldOf_smooth hW hψ subset_rfl hδ hb 2
  refine ⟨(coord_smooth j).smul F2.1, ?_⟩
  have h := F2.2.1.smul_left (f := fun x : Space => x j)
  exact h

private theorem deriv_facts {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : Space → (F →L[ℝ] ℂ)}
    (hΦ : ContDiff ℝ ∞ Φ) (hcΦ : HasCompactSupport Φ) (v : Space) :
    Continuous (fun y => fderiv ℝ Φ y v) ∧ HasCompactSupport (fun y => fderiv ℝ Φ y v) :=
  ⟨(hΦ.continuous_fderiv (by simp)).clm_apply continuous_const, hcΦ.fderiv_apply (𝕜 := ℝ) v⟩

theorem axisWeak : AxisWeakStatement := by
  intro F _ _ _ _ f g hf hg hw W hW ψ hψ hc hpos
  obtain ⟨δ, hδ, R, hb⟩ := supp_bounds hc hpos
  have hψr : ContDiff ℝ ∞ (fun p => fderiv ℝ ψ p (1, 0)) :=
    (hψ.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).clm_apply contDiff_const
  have hψz : ContDiff ℝ ∞ (fun p => fderiv ℝ ψ p (0, 1)) :=
    (hψ.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).clm_apply contDiff_const
  have F1 := fieldOf_smooth hW hψ subset_rfl hδ hb 1
  have F2 := fieldOf_smooth hW hψ subset_rfl hδ hb 2
  have Fr := fieldOf_smooth hW hψr (tsupport_fderiv_apply_subset ℝ (1, 0)) hδ hb 1
  have Fz := fieldOf_smooth hW hψz (tsupport_fderiv_apply_subset ℝ (0, 1)) hδ hb 1
  have hP := prod_facts hW hψ hδ hb
  have key3 := key3_of W ψ g
  have ia : Integrable (fun y => fderiv ℝ (fun x : Space => x 0 • fieldOf W ψ 2 x) y (unitVector 0) (f y)) volume :=
    integrable_apply (deriv_facts (hP 0).1 (hP 0).2 _).1 (deriv_facts (hP 0).1 (hP 0).2 _).2 hf
  have ib : Integrable (fun y => fderiv ℝ (fun x : Space => x 1 • fieldOf W ψ 2 x) y (unitVector 1) (f y)) volume :=
    integrable_apply (deriv_facts (hP 1).1 (hP 1).2 _).1 (deriv_facts (hP 1).1 (hP 1).2 _).2 hf
  have ic : Integrable (fun y => (y 0 • fieldOf W ψ 2 y) (g y (unitVector 0))) volume :=
    integrable_apply (hP 0).1.continuous (hP 0).2 (hg 0)
  have id' : Integrable (fun y => (y 1 • fieldOf W ψ 2 y) (g y (unitVector 1))) volume :=
    integrable_apply (hP 1).1.continuous (hP 1).2 (hg 1)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · refine (integrable_apply Fr.1.continuous Fr.2.1 hf).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [fieldOf_apply, pow_one]
    rfl
  · refine (integrable_apply Fz.1.continuous Fz.2.1 hf).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [fieldOf_apply, pow_one]
    rfl
  · exact (ic.add id').congr (Filter.Eventually.of_forall key3)
  · refine (integrable_apply F1.1.continuous F1.2.1 (hg 2)).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [fieldOf_apply, pow_one]
    rfl
  · have a0 := weakCLM hf hg hw (hP 0).1 (hP 0).2 0
    have a1 := weakCLM hf hg hw (hP 1).1 (hP 1).2 1
    calc ∫ y, ((fderiv ℝ ψ (cylRadius y, y 2) (1, 0) / cylRadius y : ℝ) : ℂ) *
          W (y 0 / cylRadius y, y 1 / cylRadius y) (f y)
        = ∫ y, (fderiv ℝ (fun x : Space => x 0 • fieldOf W ψ 2 x) y (unitVector 0) +
            fderiv ℝ (fun x : Space => x 1 • fieldOf W ψ 2 x) y (unitVector 1)) (f y) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          beta_reduce
          rw [deriv_r hW hψ hδ hb y, fieldOf_apply, pow_one]
          rfl
      _ = (∫ y, fderiv ℝ (fun x : Space => x 0 • fieldOf W ψ 2 x) y (unitVector 0) (f y)) +
            ∫ y, fderiv ℝ (fun x : Space => x 1 • fieldOf W ψ 2 x) y (unitVector 1) (f y) := by
          simp only [add_apply]
          exact integral_add ia ib
      _ = -(∫ y, (y 0 • fieldOf W ψ 2 y) (g y (unitVector 0))) +
            -∫ y, (y 1 • fieldOf W ψ 2 y) (g y (unitVector 1)) := by
          rw [a0, a1]
      _ = -∫ y, ((y 0 • fieldOf W ψ 2 y) (g y (unitVector 0)) + (y 1 • fieldOf W ψ 2 y) (g y (unitVector 1))) := by
          rw [integral_add ic id', neg_add]
      _ = _ := by
          congr 1
          exact integral_congr_ae (Filter.Eventually.of_forall key3)
  · have a2 := weakCLM hf hg hw F1.1 F1.2.1 2
    calc ∫ y, ((fderiv ℝ ψ (cylRadius y, y 2) (0, 1) / cylRadius y : ℝ) : ℂ) *
          W (y 0 / cylRadius y, y 1 / cylRadius y) (f y)
        = ∫ y, fderiv ℝ (fieldOf W ψ 1) y (unitVector 2) (f y) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          beta_reduce
          rw [deriv_z hW hψ hδ hb y, fieldOf_apply, pow_one]
          rfl
      _ = -∫ y, fieldOf W ψ 1 y (g y (unitVector 2)) := a2
      _ = _ := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          beta_reduce
          rw [fieldOf_apply, pow_one]
          rfl

end Breakdown.CellCert.CellFormula
