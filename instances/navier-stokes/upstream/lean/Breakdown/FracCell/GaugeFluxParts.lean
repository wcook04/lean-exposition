import Breakdown.FracCell.StFormulaProof

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis CellAnalysis.CellScalars

namespace Internal.GaugeFluxParts



abbrev e₀ : Space := EuclideanSpace.single 0 (1 : ℝ)
abbrev e₁ : Space := EuclideanSpace.single 1 (1 : ℝ)
abbrev e₂ : Space := EuclideanSpace.single 2 (1 : ℝ)

lemma single_eq' (i : Fin 3) (a : ℝ) :
    (EuclideanSpace.single i a : Space) = a • (EuclideanSpace.single i (1 : ℝ) : Space) := by
  ext j; by_cases h : j = i <;> simp [h]

lemma cyl_eq (r θ z : ℝ) : cylPoint r θ z = (r * Real.cos θ) • e₀ + (r * Real.sin θ) • e₁ + z • e₂ := by
  simp only [cylPoint]; rw [single_eq' 0, single_eq' 1, single_eq' 2]

lemma rad_eq (θ : ℝ) : radialUnit θ = Real.cos θ • e₀ + Real.sin θ • e₁ := by
  simp only [radialUnit]; rw [single_eq' 0, single_eq' 1]

lemma ang_eq (θ : ℝ) : angularUnit θ = (-Real.sin θ) • e₀ + Real.cos θ • e₁ := by
  simp only [angularUnit]; rw [single_eq' 0, single_eq' 1]

lemma cyl_cont (z : ℝ) : Continuous (fun p : ℝ × ℝ => cylPoint p.1 p.2 z) := by
  simp only [cyl_eq]; fun_prop

lemma frame_cont (b : Fin 3) :
    Continuous (fun θ => (![radialUnit θ, angularUnit θ, axialUnit] : Fin 3 → Space) b) := by
  fin_cases b
  · simp only [rad_eq]; simp; fun_prop
  · simp only [ang_eq]; simp; fun_prop
  · simp; fun_prop

lemma cyl_dr (s θ z : ℝ) : HasDerivAt (fun s => cylPoint s θ z) (radialUnit θ) s := by
  simp only [cyl_eq, rad_eq]
  have h := ((((hasDerivAt_id s).mul_const (Real.cos θ)).smul_const e₀).add
    (((hasDerivAt_id s).mul_const (Real.sin θ)).smul_const e₁)).add_const (z • e₂)
  simpa using h

lemma cyl_dz (s θ z : ℝ) : HasDerivAt (fun z => cylPoint s θ z) axialUnit z := by
  simp only [cyl_eq]
  have h := ((hasDerivAt_id z).smul_const e₂).const_add ((s * Real.cos θ) • e₀ + (s * Real.sin θ) • e₁)
  simpa [axialUnit] using h

lemma cyl_dt (s θ z : ℝ) : HasDerivAt (fun θ => cylPoint s θ z) (s • angularUnit θ) θ := by
  simp only [cyl_eq, ang_eq]
  have h := (((((Real.hasDerivAt_cos θ).const_mul s).smul_const e₀).add
    (((Real.hasDerivAt_sin θ).const_mul s).smul_const e₁)).add_const (z • e₂))
  refine h.congr_deriv ?_
  rw [smul_add, smul_smul, smul_smul]

lemma ang_dt (θ : ℝ) : HasDerivAt angularUnit (-radialUnit θ) θ := by
  have h := ((Real.hasDerivAt_sin θ).neg.smul_const e₀).add ((Real.hasDerivAt_cos θ).smul_const e₁)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  · rw [rad_eq, neg_add, neg_smul, neg_smul]
  · rw [ang_eq]; rfl

lemma cyl_per (r θ z : ℝ) : cylPoint r (θ + 2 * Real.pi) z = cylPoint r θ z := by
  simp only [cylPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]

lemma ang_per (θ : ℝ) : angularUnit (θ + 2 * Real.pi) = angularUnit θ := by
  simp only [angularUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]

lemma radius_cont : Continuous cylRadius := by
  unfold cylRadius
  have h0 : Continuous (fun y : Space => y 0) := (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).continuous
  have h1 : Continuous (fun y : Space => y 1) := (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).continuous
  fun_prop

lemma height_cont : Continuous (fun y : Space => y 2) :=
  (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous

lemma cyl_radius {r : ℝ} (hr : 0 ≤ r) (θ z : ℝ) : cylRadius (cylPoint r θ z) = r := by
  simp only [cylRadius, cylPoint]
  simp
  rw [show (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 by
    linear_combination r ^ 2 * Real.cos_sq_add_sin_sq θ]
  exact Real.sqrt_sq hr

lemma cyl_height (r θ z : ℝ) : (cylPoint r θ z) 2 = z := by simp [cylPoint]

lemma param_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {F F' : ℝ → ℝ → E} (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hF' : Continuous (fun p : ℝ × ℝ => F' p.1 p.2))
    (hd : ∀ s t, HasDerivAt (fun s => F s t) (F' s t) s) (a b x : ℝ) :
    HasDerivAt (fun s => ∫ t in a..b, F s t) (∫ t in a..b, F' x t) x := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn
    hF'.continuousOn
  have hFs : ∀ s, Continuous (F s) := fun s => hF.comp (continuous_const.prodMk continuous_id)
  have hF's : Continuous (F' x) := hF'.comp (continuous_const.prodMk continuous_id)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (bound := fun _ => C)
    (Metric.ball_mem_nhds x one_pos) (Filter.Eventually.of_forall fun s => (hFs s).aestronglyMeasurable)
    ((hFs x).intervalIntegrable a b) hF's.aestronglyMeasurable ?_ intervalIntegrable_const ?_).2
  · exact Filter.Eventually.of_forall fun t ht s hs =>
      hC (s, t) ⟨Metric.ball_subset_closedBall hs, Set.uIoc_subset_uIcc ht⟩
  · exact Filter.Eventually.of_forall fun t _ s _ => hd s t

lemma modeVec_zero (m : ℕ) (v : Space → Space) (r z : ℝ) (b : Fin 3) :
    modeVec m 0 v r z b = (((1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi), frameVec θ (v (cylPoint r θ z)) b : ℝ) : ℂ) := by
  simp only [modeVec, azimuth, Int.cast_zero, zero_mul, Complex.ofReal_zero, neg_zero, Complex.exp_zero, one_mul]
  rw [intervalIntegral.integral_ofReal]; push_cast; ring

lemma modeMat_zero (m : ℕ) (G : Space → (Space →L[ℝ] Space)) (r z : ℝ) (a b : Fin 3) :
    modeMat m 0 G r z a b = (((1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi), frameMat θ (G (cylPoint r θ z)) a b : ℝ) : ℂ) := by
  simp only [modeMat, azimuth, Int.cast_zero, zero_mul, Complex.ofReal_zero, neg_zero, Complex.exp_zero, one_mul]
  rw [intervalIntegral.integral_ofReal]; push_cast; ring

lemma frame_trace (θ : ℝ) (M : Space →L[ℝ] Space) :
    frameMat θ M 0 0 + frameMat θ M 1 1 + frameMat θ M 2 2 = ∑ i : Fin 3, inner ℝ (M (unitVector i)) (unitVector i) := by
  simp only [frameMat, Fin.sum_univ_three, unitVector]
  simp [rad_eq, ang_eq, axialUnit, map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  linear_combination (inner ℝ (M e₀) e₀ + inner ℝ (M e₁) e₁) * Real.sin_sq_add_cos_sq θ


lemma circ_deriv {f : Space → Space} (hf : ContDiff ℝ 2 f) (γ γ' : ℝ → ℝ → Space)
    (hγ : Continuous (fun p : ℝ × ℝ => γ p.1 p.2)) (hγ' : Continuous (fun p : ℝ × ℝ => γ' p.1 p.2))
    (hdγ : ∀ s θ, HasDerivAt (fun s => γ s θ) (γ' s θ) s) (u : ℝ → Space) (hu : Continuous u) (x : ℝ) :
    HasDerivAt (fun s => ∫ θ in (0 : ℝ)..(2 * Real.pi), inner ℝ (f (γ s θ)) (u θ))
      (∫ θ in (0 : ℝ)..(2 * Real.pi), inner ℝ (fderiv ℝ f (γ x θ) (γ' x θ)) (u θ)) x := by
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hdf : Differentiable ℝ f := hf.differentiable (by norm_num)
  refine param_deriv (F := fun s θ => inner ℝ (f (γ s θ)) (u θ))
    (F' := fun s θ => inner ℝ (fderiv ℝ f (γ s θ) (γ' s θ)) (u θ)) ?_ ?_ ?_ 0 (2 * Real.pi) x
  · exact (hf.continuous.comp hγ).inner (hu.comp continuous_snd)
  · exact ((hfd.comp hγ).clm_apply hγ').inner (hu.comp continuous_snd)
  · intro s θ
    have h := ((hdf (γ s θ)).hasFDerivAt.comp_hasDerivAt s (hdγ s θ)).inner ℝ (hasDerivAt_const s (u θ))
    simpa using h

lemma fm_cont {g : ℝ → (Space →L[ℝ] Space)} (hg : Continuous g) (i j : Fin 3) :
    Continuous (fun θ => frameMat θ (g θ) i j) := by
  simp only [frameMat]
  exact (hg.clm_apply (frame_cont j)).inner (frame_cont i)

theorem zero_calc {α : ℝ} {k N slots : ℕ} {c : FracCellData k N}
    {K : CellBox} {S : CellScalars} {B : CellBases} {Cl : CellClasses}
    {R : CellRows N slots k} (hR : IsCellData α c K S B Cl R) (hsh : IsRowShape c K S R) {a : Fin N}
    (ha : a ∈ R.rowSet) (x z : ℝ) (hx : x ∈ Set.Ioo K.r₁ K.r₂) (hz : z ∈ Set.Ioo K.z₁ K.z₂) :
    HasDerivAt (fun s => rowModeVec c a 0 (s, z) 0) (rowModeGrad c a 0 (x, z) 0 0) x ∧
      HasDerivAt (fun s => rowModeVec c a 0 (x, s) 2) (rowModeGrad c a 0 (x, z) 2 2) z ∧
      rowModeVec c a 0 (x, z) 0 = (x : ℂ) * rowModeGrad c a 0 (x, z) 1 1 ∧
      rowModeGrad c a 0 (x, z) 0 0 + rowModeGrad c a 0 (x, z) 1 1 + rowModeGrad c a 0 (x, z) 2 2 = 0 := by
  have hr1 := hR.box.r_order.1
  have hz1 := hR.box.z_order.1
  have hx0 : 0 < x := lt_of_le_of_lt hr1 hx.1
  obtain ⟨f, hf, hvf⟩ := hsh.row_smooth a ha (x / 2) (by linarith)
  set U : Set Space := {y | K.r₁ < cylRadius y ∧ cylRadius y < K.r₂ ∧ K.z₁ < y 2 ∧ y 2 < K.z₂ ∧
    x / 2 < cylRadius y} with hU
  have hUo : IsOpen U := by
    simp only [hU, Set.ofPred_and]
    exact (isOpen_lt continuous_const radius_cont).inter ((isOpen_lt radius_cont continuous_const).inter
      ((isOpen_lt continuous_const height_cont).inter ((isOpen_lt height_cont continuous_const).inter
        (isOpen_lt continuous_const radius_cont))))
  have hUs : ∀ y ∈ U, y ∈ K.solid := by
    rintro y ⟨h1, h2, h3, h4, _⟩
    have hpos : 0 ≤ y 2 := by linarith
    have e : |cylHeight y| = y 2 := abs_of_nonneg hpos
    exact ⟨h1.le, h2.le, by rw [e]; exact h3.le, by rw [e]; exact h4.le⟩
  have hUeq : ∀ y ∈ U, c.row a y = f y := by
    intro y hy
    exact hvf y (hUs y hy) (show 0 ≤ y 2 by linarith [hy.2.2.1]) hy.2.2.2.2.le
  have hcylU : ∀ s θ t, s ∈ Set.Ioo (max K.r₁ (x / 2)) K.r₂ → t ∈ Set.Ioo K.z₁ K.z₂ → cylPoint s θ t ∈ U := by
    intro s θ t hs ht
    obtain ⟨hs1, hs2⟩ := max_lt_iff.1 hs.1
    have hs0 : 0 ≤ s := by linarith
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [cyl_radius hs0]; exact hs1
    · rw [cyl_radius hs0]; exact hs.2
    · rw [cyl_height]; exact ht.1
    · rw [cyl_height]; exact ht.2
    · rw [cyl_radius hs0]; exact hs2
  have hx' : x ∈ Set.Ioo (max K.r₁ (x / 2)) K.r₂ := ⟨max_lt hx.1 (by linarith), hx.2⟩
  have hD : ∀ θ, fderiv ℝ (c.row a) (cylPoint x θ z) = fderiv ℝ f (cylPoint x θ z) := fun θ =>
    Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hUo.mem_nhds (hcylU x θ z hx' hz)) hUeq)
  have hG : ∀ i j, rowModeGrad c a 0 (x, z) i j =
      ((1 / (2 * Real.pi) * ∫ θ in (0 : ℝ)..(2 * Real.pi), frameMat θ (fderiv ℝ f (cylPoint x θ z)) i j : ℝ) : ℂ) := by
    intro i j
    simp only [rowModeGrad, modeMat_zero, hD]
  have hV : ∀ b, ∀ s ∈ Set.Ioo (max K.r₁ (x / 2)) K.r₂, ∀ t ∈ Set.Ioo K.z₁ K.z₂, rowModeVec c a 0 (s, t) b =
      ((1 / (2 * Real.pi) * ∫ θ in (0 : ℝ)..(2 * Real.pi), frameVec θ (f (cylPoint s θ t)) b : ℝ) : ℂ) := by
    intro b s hs t ht
    have e : ∀ θ, c.row a (cylPoint s θ t) = f (cylPoint s θ t) := fun θ => hUeq _ (hcylU s θ t hs ht)
    simp only [rowModeVec, modeVec_zero, e]
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hdf : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hMc : ∀ i j, Continuous (fun θ => frameMat θ (fderiv ℝ f (cylPoint x θ z)) i j) := fun i j =>
    fm_cont (hfd.comp ((cyl_cont z).comp (continuous_const.prodMk continuous_id))) i j
  refine ⟨?_, ?_, ?_, ?_⟩
  · have d1 := circ_deriv hf (fun s θ => cylPoint s θ z) (fun _ θ => radialUnit θ) (cyl_cont z)
      ((frame_cont 0).comp continuous_snd) (fun s θ => cyl_dr s θ z) radialUnit (frame_cont 0) x
    have e1 : (fun s => rowModeVec c a 0 (s, z) 0) =ᶠ[nhds x] (fun s => ((1 / (2 * Real.pi) *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), inner ℝ (f (cylPoint s θ z)) (radialUnit θ) : ℝ) : ℂ)) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx') fun s hs => hV 0 s hs z hz
    refine HasDerivAt.congr_of_eventuallyEq ?_ e1
    rw [hG 0 0]
    exact (d1.const_mul _).ofReal_comp
  · have hcz : Continuous (fun p : ℝ × ℝ => cylPoint x p.2 p.1) := by
      simp only [cyl_eq]; fun_prop
    have d2 := circ_deriv hf (fun s θ => cylPoint x θ s) (fun _ _ => axialUnit) hcz continuous_const
      (fun s θ => cyl_dz x θ s) (fun _ => axialUnit) continuous_const z
    have e2 : (fun s => rowModeVec c a 0 (x, s) 2) =ᶠ[nhds z] (fun s => ((1 / (2 * Real.pi) *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), inner ℝ (f (cylPoint x θ s)) axialUnit : ℝ) : ℂ)) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hz) fun s hs => hV 2 x hx' s hs
    refine HasDerivAt.congr_of_eventuallyEq ?_ e2
    rw [hG 2 2]
    exact (d2.const_mul _).ofReal_comp
  · rw [hV 0 x hx' z hz, hG 1 1]
    set A : ℝ → ℝ := fun θ => inner ℝ (f (cylPoint x θ z)) (radialUnit θ) with hA
    set Bf : ℝ → ℝ := fun θ => frameMat θ (fderiv ℝ f (cylPoint x θ z)) 1 1 with hB
    have hAc : Continuous A := (hf.continuous.comp ((cyl_cont z).comp (continuous_const.prodMk continuous_id))).inner
      (frame_cont 0)
    have hderiv : ∀ θ, HasDerivAt (fun θ => inner ℝ (f (cylPoint x θ z)) (angularUnit θ)) (-A θ + x * Bf θ) θ := by
      intro θ
      have h := ((hdf (cylPoint x θ z)).hasFDerivAt.comp_hasDerivAt θ (cyl_dt x θ z)).inner ℝ (ang_dt θ)
      refine h.congr_deriv ?_
      simp only [hA, hB, frameMat, Function.comp_apply, map_smul, inner_neg_right, real_inner_smul_left]
      rfl
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv θ)
      ((hAc.neg.add (continuous_const.mul (hMc 1 1))).intervalIntegrable (μ := volume) 0 (2 * Real.pi))
    have hper : inner ℝ (f (cylPoint x (2 * Real.pi) z)) (angularUnit (2 * Real.pi)) =
        inner ℝ (f (cylPoint x 0 z)) (angularUnit 0) := by
      have e1 := cyl_per x 0 z
      have e2 := ang_per 0
      rw [zero_add] at e1 e2
      rw [e1, e2]
    rw [hper, sub_self] at hint
    have hsplit := intervalIntegral.integral_add (μ := volume) (a := 0) (b := 2 * Real.pi) (f := fun y => -A y)
      (g := fun y => x * Bf y) (hAc.neg.intervalIntegrable _ _) ((continuous_const.mul (hMc 1 1)).intervalIntegrable _ _)
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hsplit
    have key : ∫ θ in (0 : ℝ)..(2 * Real.pi), frameVec θ (f (cylPoint x θ z)) 0 =
        x * ∫ θ in (0 : ℝ)..(2 * Real.pi), Bf θ := by
      have : ∫ θ in (0 : ℝ)..(2 * Real.pi), frameVec θ (f (cylPoint x θ z)) 0 = ∫ θ in (0 : ℝ)..(2 * Real.pi), A θ := rfl
      rw [this]; linarith [hsplit, hint]
    rw [key]; push_cast; ring
  · rw [hG 0 0, hG 1 1, hG 2 2]
    have hz0 : ∀ θ, frameMat θ (fderiv ℝ f (cylPoint x θ z)) 0 0 + frameMat θ (fderiv ℝ f (cylPoint x θ z)) 1 1 +
        frameMat θ (fderiv ℝ f (cylPoint x θ z)) 2 2 = 0 := by
      intro θ
      rw [frame_trace, ← hD θ]
      exact hsh.row_solenoidal a ha _ (hUs _ (hcylU x θ z hx' hz))
    have hsum : (∫ θ in (0 : ℝ)..(2 * Real.pi), frameMat θ (fderiv ℝ f (cylPoint x θ z)) 0 0) +
        (∫ θ in (0 : ℝ)..(2 * Real.pi), frameMat θ (fderiv ℝ f (cylPoint x θ z)) 1 1) +
        (∫ θ in (0 : ℝ)..(2 * Real.pi), frameMat θ (fderiv ℝ f (cylPoint x θ z)) 2 2) = 0 := by
      have h01 := intervalIntegral.integral_add ((hMc 0 0).intervalIntegrable (μ := volume) 0 (2 * Real.pi))
        ((hMc 1 1).intervalIntegrable (μ := volume) 0 (2 * Real.pi))
      have h012 := intervalIntegral.integral_add (((hMc 0 0).add (hMc 1 1)).intervalIntegrable (μ := volume) 0 (2 * Real.pi))
        ((hMc 2 2).intervalIntegrable (μ := volume) 0 (2 * Real.pi))
      simp only [Pi.add_apply] at h012
      have hzero : ∫ θ in (0 : ℝ)..(2 * Real.pi), (frameMat θ (fderiv ℝ f (cylPoint x θ z)) 0 0 +
          frameMat θ (fderiv ℝ f (cylPoint x θ z)) 1 1 + frameMat θ (fderiv ℝ f (cylPoint x θ z)) 2 2) = 0 := by
        simp only [hz0, intervalIntegral.integral_zero]
      linarith [h01, h012, hzero]
    rw [← Complex.ofReal_add, ← Complex.ofReal_add, ← mul_add, ← mul_add, hsum, mul_zero, Complex.ofReal_zero]

def IsP (F : ℝ → ℂ) : Prop := ∃ q : Polynomial ℂ, ∀ x : ℝ, F x = q.eval (x : ℂ)

lemma isP_const (a : ℂ) : IsP (fun _ => a) := ⟨Polynomial.C a, fun x => by simp⟩

lemma isP_add {F G : ℝ → ℂ} (hF : IsP F) (hG : IsP G) : IsP (fun x => F x + G x) := by
  obtain ⟨p, hp⟩ := hF; obtain ⟨q, hq⟩ := hG
  exact ⟨p + q, fun x => by simp [hp, hq]⟩

lemma isP_sub {F G : ℝ → ℂ} (hF : IsP F) (hG : IsP G) : IsP (fun x => F x - G x) := by
  obtain ⟨p, hp⟩ := hF; obtain ⟨q, hq⟩ := hG
  exact ⟨p - q, fun x => by simp [hp, hq]⟩

lemma isP_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℂ) (h : ∀ i ∈ s, IsP (F i)) :
    IsP (fun x => ∑ i ∈ s, F i x) := by
  have h' := Finset.sum_induction (fun i => F i) IsP (fun a b ha hb => isP_add ha hb) (isP_const 0) h
  obtain ⟨q, hq⟩ := h'
  exact ⟨q, fun x => by rw [← hq x, Finset.sum_apply]⟩

lemma isP_prim {F : ℝ → ℂ} (hF : IsP F) : IsP (fun x => ∫ ρ in (0 : ℝ)..x, F ρ) := by
  obtain ⟨q, hq⟩ := hF
  have e : ∀ x : ℝ, ∫ ρ in (0 : ℝ)..x, F ρ =
      ∑ n ∈ Finset.range (q.natDegree + 1), q.coeff n * ((x : ℂ) ^ (n + 1) / ((n : ℂ) + 1)) := by
    intro x
    have h1 : ∀ ρ : ℝ, F ρ = ∑ n ∈ Finset.range (q.natDegree + 1), q.coeff n * (ρ : ℂ) ^ n := fun ρ => by
      rw [hq, Polynomial.eval_eq_sum_range]
    simp_rw [h1]
    rw [intervalIntegral.integral_finsetSum (fun n _ =>
      (by fun_prop : Continuous fun ρ : ℝ => q.coeff n * (ρ : ℂ) ^ n).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have h2 : ∫ ρ in (0 : ℝ)..x, (ρ : ℂ) ^ n = ((∫ ρ in (0 : ℝ)..x, ρ ^ n : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]; push_cast; rfl
    rw [h2, integral_pow]; push_cast; simp
  refine ⟨∑ n ∈ Finset.range (q.natDegree + 1), Polynomial.C (q.coeff n / ((n : ℂ) + 1)) * Polynomial.X ^ (n + 1),
    fun x => ?_⟩
  dsimp only
  rw [e x, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

lemma isP_slice {d d' : ℕ} {PG : ℝ × ℝ → ℂ} (hPG : PG ∈ polyFn d d') (m : ℕ) (z₁ z₂ : ℝ) :
    IsP (fun x => ∫ t in z₁..z₂, (x : ℂ) ^ m * PG (x, t)) := by
  obtain ⟨cc, hcc⟩ := hPG
  have e : ∀ x : ℝ, ∫ t in z₁..z₂, (x : ℂ) ^ m * PG (x, t) = ∑ j : Fin (d + 1), ∑ l : Fin (d' + 1),
      cc j l * (∫ t in z₁..z₂, (t : ℂ) ^ (l : ℕ)) * (x : ℂ) ^ (m + (j : ℕ)) := by
    intro x
    simp_rw [hcc, Finset.mul_sum]
    rw [intervalIntegral.integral_finsetSum (fun j _ => (by fun_prop : Continuous fun t : ℝ => ∑ l : Fin (d' + 1),
      (x : ℂ) ^ m * (cc j l * (x : ℂ) ^ (j : ℕ) * (t : ℂ) ^ (l : ℕ))).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_finsetSum (fun l _ => (by fun_prop : Continuous fun t : ℝ =>
      (x : ℂ) ^ m * (cc j l * (x : ℂ) ^ (j : ℕ) * (t : ℂ) ^ (l : ℕ))).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm _ ((x : ℂ) ^ (m + (j : ℕ))), ← mul_assoc, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  refine ⟨∑ j : Fin (d + 1), ∑ l : Fin (d' + 1),
    Polynomial.C (cc j l * (∫ t in z₁..z₂, (t : ℂ) ^ (l : ℕ))) * Polynomial.X ^ (m + (j : ℕ)), fun x => ?_⟩
  dsimp only
  rw [e x, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

lemma isP_const_of_deriv {F : ℝ → ℂ} (hF : IsP F) {r₁ r₂ : ℝ} (h : r₁ < r₂)
    (hd : ∀ x ∈ Set.Ioo r₁ r₂, HasDerivAt F 0 x) (y : ℝ) : F y = F 0 := by
  obtain ⟨q, hq⟩ := hF
  have hq' : F = fun t : ℝ => q.eval (t : ℂ) := funext hq
  have hroot : Complex.ofReal '' Set.Ioo r₁ r₂ ⊆ {w | q.derivative.IsRoot w} := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : HasDerivAt (fun t : ℝ => q.eval (t : ℂ)) (q.derivative.eval (x : ℂ)) x :=
      (q.hasDerivAt (x : ℂ)).comp_ofReal
    rw [← hq'] at h1
    show Polynomial.IsRoot _ _
    exact h1.unique (hd x hx)
  have hinf : (Complex.ofReal '' Set.Ioo r₁ r₂).Infinite :=
    (Set.Ioo_infinite h).image Complex.ofReal_injective.injOn
  have h0 := Polynomial.eq_zero_of_infinite_isRoot _ (hinf.mono hroot)
  have hC := Polynomial.eq_C_of_derivative_eq_zero h0
  rw [hq y, hq 0, hC]
  simp

lemma ii_conj (f : ℝ → ℂ) (a b : ℝ) :
    ∫ t in a..b, (starRingEnd ℂ) (f t) = (starRingEnd ℂ) (∫ t in a..b, f t) := by
  simp only [intervalIntegral, integral_conj, map_sub]

lemma isP_cont {F : ℝ → ℂ} (hF : IsP F) : Continuous F := by
  obtain ⟨q, hq⟩ := hF
  rw [show F = fun x : ℝ => q.eval (x : ℂ) from funext hq]
  exact q.continuous.comp Complex.continuous_ofReal

lemma isP_test (Sg : FaceSegment) {n : ℕ} (cf : Fin n → ℂ) (P : ℝ → ℂ)
    (hP : ∀ t, P t = ∑ d, cf d * ((Sg.test (d : ℕ) t : ℝ) : ℂ)) : IsP (fun ρ => (ρ : ℂ) * P ρ) := by
  refine ⟨Polynomial.X * ∑ d : Fin n, Polynomial.C (cf d) * ∑ i ∈ Finset.range ((d : ℕ) + 1),
    Polynomial.C ((Sg.testCoef d i : ℝ) : ℂ) * Polynomial.X ^ i, fun ρ => ?_⟩
  simp only [hP, FaceSegment.test, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_finsetSum,
    Polynomial.eval_C, Polynomial.eval_pow]
  push_cast
  rfl

lemma param_deriv_cd {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ 1 G) (a b x : ℝ) :
    HasDerivAt (fun s => ∫ t in a..b, G (s, t)) (∫ t in a..b, fderiv ℝ G (x, t) (1, 0)) x ∧
      ∀ s t, HasDerivAt (fun s => G (s, t)) (fderiv ℝ G (s, t) (1, 0)) s := by
  have hd : ∀ s t, HasDerivAt (fun s => G (s, t)) (fderiv ℝ G (s, t) (1, 0)) s := fun s t =>
    ((hG.differentiable (by norm_num) (s, t)).hasFDerivAt).comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s t))
  refine ⟨param_deriv (F := fun s t => G (s, t)) (F' := fun s t => fderiv ℝ G (s, t) (1, 0))
    hG.continuous ((hG.continuous_fderiv (by norm_num)).clm_apply continuous_const) hd a b x, hd⟩

lemma solve_rhat {e : ℕ} {r ρ : ℝ} (hr : r ≠ 0) (hrh : (ρ : ℂ) * (r : ℂ) ^ e = (r : ℂ)) {u P : ℂ}
    (h : (ρ : ℂ) * u = P) : u = P * (r : ℂ) ^ e / (r : ℂ) := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr
  rw [eq_div_iff hr', ← h]
  calc u * (r : ℂ) = u * ((ρ : ℂ) * (r : ℂ) ^ e) := by rw [hrh]
    _ = (ρ : ℂ) * u * (r : ℂ) ^ e := by ring

theorem flux_main {α : ℝ} {k N slots : ℕ} {c : FracCellData k N}
    {K : CellBox} {S : CellScalars} {B : CellBases} {Cl : CellClasses}
    {R : CellRows N slots k} (hR : IsCellData α c K S B Cl R) (hsh : IsRowShape c K S R) {L : CellLayout}
    {a : Fin N} (ha : a ∈ R.rowSet)
    (hcalc : ∀ x ∈ Set.Ioo K.r₁ K.r₂, ∀ z ∈ Set.Ioo K.z₁ K.z₂,
      HasDerivAt (fun s => rowModeVec c a 0 (s, z) 0) (rowModeGrad c a 0 (x, z) 0 0) x ∧
      HasDerivAt (fun s => rowModeVec c a 0 (x, s) 2) (rowModeGrad c a 0 (x, z) 2 2) z ∧
      rowModeVec c a 0 (x, z) 0 = (x : ℂ) * rowModeGrad c a 0 (x, z) 1 1 ∧
      rowModeGrad c a 0 (x, z) 0 0 + rowModeGrad c a 0 (x, z) 1 1 + rowModeGrad c a 0 (x, z) 2 2 = 0)
    (P₁ P₂ : ℝ → ℂ)
    (hp₁ : ∃ s : Fin L.presCount, ∃ cf : Fin L.degSide → ℂ, ∀ t, P₁ t = ∑ d, cf d * ((L.presSegment s).test d t : ℂ))
    (hp₂ : ∃ s : Fin L.presCount, ∃ cf : Fin L.degSide → ℂ, ∀ t, P₂ t = ∑ d, cf d * ((L.presSegment s).test d t : ℂ))
    (h₁ : ∀ r ∈ Set.Icc K.r₁ K.r₂, rowModeVec c a 0 (r, K.z₁) 2 = P₁ r)
    (h₂ : ∀ r ∈ Set.Icc K.r₁ K.r₂, rowModeVec c a 0 (r, K.z₂) 2 = P₂ r) (x : ℝ) (hx : x ∈ Set.Icc K.r₁ K.r₂) :
    (x : ℂ) * (∫ z in K.z₁..K.z₂, rowModeVec c a 0 (x, z) 0)
      + (∫ ρ in (0 : ℝ)..x, (ρ : ℂ) * P₂ ρ) - (∫ ρ in (0 : ℝ)..x, (ρ : ℂ) * P₁ ρ) = 0 := by
  obtain ⟨hr0, hr12⟩ := hR.box.r_order
  obtain ⟨hz0, hz12⟩ := hR.box.z_order
  obtain ⟨e, he⟩ : ∃ e : ℕ, ∀ r, K.lineWeight r = r ^ e := by
    by_cases h : K.r₁ = 0
    · exact ⟨1, fun r => by simp [CellBox.lineWeight, h]⟩
    · exact ⟨0, fun r => by simp [CellBox.lineWeight, h]⟩
  have hrh : ∀ p : ℝ × ℝ, p.1 ≠ 0 → ((rHat K p : ℝ) : ℂ) * (p.1 : ℂ) ^ e = (p.1 : ℂ) := by
    intro p hp
    have hp' : (p.1 : ℂ) ^ e ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.2 hp)
    simp only [rHat, he]; push_cast
    exact div_mul_cancel₀ _ hp'
  obtain ⟨PV, hPVp, hPV⟩ := hsh.row_low_velocity a ha 0 0
  obtain ⟨PW, hPWp, hPW⟩ := hsh.row_low_velocity a ha 0 2
  obtain ⟨PG, hPGp, hPG⟩ := hsh.row_low_gradient a ha 0 1 1
  obtain ⟨PH, hPHp, hPH⟩ := hsh.row_low_gradient a ha 0 2 2
  obtain ⟨s₁, cf₁, hc₁⟩ := hp₁
  obtain ⟨s₂, cf₂, hc₂⟩ := hp₂
  have hI₁ := isP_test (L.presSegment s₁) cf₁ P₁ hc₁
  have hI₂ := isP_test (L.presSegment s₂) cf₂ P₂ hc₂
  have hPVc : Continuous PV := by
    obtain ⟨cc, hcc⟩ := hPVp; rw [show PV = _ from funext hcc]; fun_prop
  have hPWc : Continuous PW := by
    obtain ⟨cc, hcc⟩ := hPWp; rw [show PW = _ from funext hcc]; fun_prop
  have hPHc : Continuous PH := by
    obtain ⟨cc, hcc⟩ := hPHp; rw [show PH = _ from funext hcc]; fun_prop
  have hGcd : ContDiff ℝ 1 (fun p : ℝ × ℝ => (p.1 : ℂ) ^ (e + 1) * PG p) := by
    obtain ⟨cc, hcc⟩ := hPGp
    have hof : ContDiff ℝ 1 (fun r : ℝ => (r : ℂ)) := Complex.ofRealCLM.contDiff
    have h1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => (p.1 : ℂ)) := hof.comp contDiff_fst
    have h2 : ContDiff ℝ 1 (fun p : ℝ × ℝ => (p.2 : ℂ)) := hof.comp contDiff_snd
    simp only [hcc]
    exact (h1.pow _).mul (ContDiff.sum fun j _ => ContDiff.sum fun l _ =>
      (contDiff_const.mul (h1.pow _)).mul (h2.pow _))
  set Q1 : ℝ → ℂ := fun y => (∫ t in K.z₁..K.z₂, (y : ℂ) ^ e * PV (y, t))
    + (∫ ρ in (0 : ℝ)..y, (ρ : ℂ) * P₂ ρ) - (∫ ρ in (0 : ℝ)..y, (ρ : ℂ) * P₁ ρ) with hQ1
  set Q2 : ℝ → ℂ := fun y => (∫ t in K.z₁..K.z₂, (y : ℂ) ^ (e + 1) * PG (y, t))
    + (∫ ρ in (0 : ℝ)..y, (ρ : ℂ) * P₂ ρ) - (∫ ρ in (0 : ℝ)..y, (ρ : ℂ) * P₁ ρ) with hQ2
  have hQ1p : IsP Q1 := isP_sub (isP_add (isP_slice hPVp e _ _) (isP_prim hI₂)) (isP_prim hI₁)
  have hQ2p : IsP Q2 := isP_sub (isP_add (isP_slice hPGp (e + 1) _ _) (isP_prim hI₂)) (isP_prim hI₁)
  have hzI : Set.uIcc K.z₁ K.z₂ = Set.Icc K.z₁ K.z₂ := Set.uIcc_of_le hz12.le
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc K.z₁ K.z₂ → t ∈ Set.Ioo K.z₁ K.z₂ := by
    have h0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ K.z₂ := by
      rw [ae_iff]; simp
    filter_upwards [h0] with t ht hmem
    rw [Set.uIoc_of_le hz12.le] at hmem
    exact ⟨hmem.1, lt_of_le_of_ne hmem.2 ht⟩
  have hVG : ∀ y ∈ Set.Ioo K.r₁ K.r₂, ∀ t ∈ Set.Ioo K.z₁ K.z₂,
      (y : ℂ) * rowModeVec c a 0 (y, t) 0 = (y : ℂ) ^ (e + 1) * PG (y, t) := by
    intro y hy t ht
    have hy0 : y ≠ 0 := (lt_of_le_of_lt hr0 hy.1).ne'
    rw [(hcalc y hy t ht).2.2.1, solve_rhat hy0 (hrh (y, t) hy0) (hPG (y, t) ⟨hy, ht⟩ hy0)]
    field_simp
    ring
  have hQQ1 : ∀ y ∈ Set.Icc K.r₁ K.r₂, (y : ℂ) * (∫ z in K.z₁..K.z₂, rowModeVec c a 0 (y, z) 0)
      = ∫ t in K.z₁..K.z₂, (y : ℂ) ^ e * PV (y, t) := by
    intro y hy
    by_cases hy0 : y = 0
    · subst hy0
      have hax : K.r₁ = 0 := le_antisymm hy.1 hr0
      have hl : K.lineWeight 0 = 0 := by simp [CellBox.lineWeight, hax]
      rw [he] at hl
      have hl' : (0 : ℂ) ^ e = 0 := by exact_mod_cast hl
      simp only [Complex.ofReal_zero, hl', zero_mul, intervalIntegral.integral_zero, mul_zero]
    · rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [hzI] at ht
      have hy' : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy0
      rw [solve_rhat hy0 (hrh (y, t) hy0) (hPV (y, t) ⟨hy, ht⟩ hy0)]
      field_simp
  have hQQ2 : ∀ y ∈ Set.Ioo K.r₁ K.r₂, Q1 y = Q2 y := by
    intro y hy
    simp only [hQ1, hQ2]
    rw [← hQQ1 y ⟨hy.1.le, hy.2.le⟩, ← intervalIntegral.integral_const_mul]
    congr 2
    exact intervalIntegral.integral_congr_ae (hae.mono fun t ht hmem => hVG y hy t (ht hmem))
  have hderiv : ∀ y ∈ Set.Ioo K.r₁ K.r₂, HasDerivAt Q2 0 y := by
    intro y hy
    have hy0 : y ≠ 0 := (lt_of_le_of_lt hr0 hy.1).ne'
    obtain ⟨hD1, hD2⟩ := param_deriv_cd hGcd K.z₁ K.z₂ y
    set H' : ℝ → ℂ := fun t => PH (y, t) * (y : ℂ) ^ e / (y : ℂ) with hH'
    have hH'c : Continuous H' := by
      simp only [hH']
      exact ((hPHc.comp (continuous_const.prodMk continuous_id)).mul continuous_const).div_const _
    have hpt : ∀ t ∈ Set.Ioo K.z₁ K.z₂, fderiv ℝ (fun p : ℝ × ℝ => (p.1 : ℂ) ^ (e + 1) * PG p) (y, t) (1, 0)
        = -(y : ℂ) * H' t := by
      intro t ht
      have hc := hcalc y hy t ht
      have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * rowModeVec c a 0 (s, t) 0)
          (1 * rowModeVec c a 0 (y, t) 0 + (y : ℂ) * rowModeGrad c a 0 (y, t) 0 0) y := by
        have hid : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 y := by
          simpa using (hasDerivAt_id y).ofReal_comp
        exact hid.mul hc.1
      have h2 : (fun s : ℝ => (s : ℂ) ^ (e + 1) * PG (s, t)) =ᶠ[nhds y]
          (fun s : ℝ => (s : ℂ) * rowModeVec c a 0 (s, t) 0) :=
        Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hy) fun s hs => (hVG s hs t ht).symm
      have h3 := (hD2 y t).congr_of_eventuallyEq h2.symm
      have hg22 := solve_rhat hy0 (hrh (y, t) hy0) (hPH (y, t) ⟨hy, ht⟩ hy0)
      rw [← h1.unique h3]
      show _ = -(y : ℂ) * (PH (y, t) * (y : ℂ) ^ e / (y : ℂ))
      rw [← hg22]
      linear_combination hc.2.2.1 + (y : ℂ) * hc.2.2.2
    have hW : ∀ t ∈ Set.Icc K.z₁ K.z₂, rowModeVec c a 0 (y, t) 2 = PW (y, t) * (y : ℂ) ^ e / (y : ℂ) := fun t ht =>
      solve_rhat hy0 (hrh (y, t) hy0) (hPW (y, t) ⟨⟨hy.1.le, hy.2.le⟩, ht⟩ hy0)
    have hWc : ContinuousOn (fun t => rowModeVec c a 0 (y, t) 2) (Set.Icc K.z₁ K.z₂) :=
      (((hPWc.comp (continuous_const.prodMk continuous_id)).mul continuous_const).div_const
        (y : ℂ)).continuousOn.congr (fun t ht => hW t ht)
    have hWd : ∀ t ∈ Set.Ioo K.z₁ K.z₂, HasDerivAt (fun s => rowModeVec c a 0 (y, s) 2) (H' t) t := by
      intro t ht
      have h := (hcalc y hy t ht).2.1
      rwa [solve_rhat hy0 (hrh (y, t) hy0) (hPH (y, t) ⟨hy, ht⟩ hy0)] at h
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hz12.le hWc hWd (hH'c.intervalIntegrable _ _)
    rw [h₂ y ⟨hy.1.le, hy.2.le⟩, h₁ y ⟨hy.1.le, hy.2.le⟩] at hftc
    have hint : ∫ t in K.z₁..K.z₂, fderiv ℝ (fun p : ℝ × ℝ => (p.1 : ℂ) ^ (e + 1) * PG p) (y, t) (1, 0)
        = -(y : ℂ) * (P₂ y - P₁ y) := by
      rw [← hftc, ← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr_ae (hae.mono fun t ht hmem => hpt t (ht hmem))
    have hc₂' := ((isP_cont hI₂).integral_hasStrictDerivAt 0 y).hasDerivAt
    have hc₁' := ((isP_cont hI₁).integral_hasStrictDerivAt 0 y).hasDerivAt
    have hsum := (hD1.add hc₂').sub hc₁'
    rw [hint] at hsum
    refine hsum.congr_deriv ?_
    ring
  have hQ20 : ∀ y, Q2 y = 0 := by
    intro y
    rw [isP_const_of_deriv hQ2p hr12 hderiv y]
    simp [hQ2]
  have hQ1z : ∀ y ∈ Set.Icc K.r₁ K.r₂, Q1 y = 0 := by
    have hcl : closure (Set.Ioo K.r₁ K.r₂) ⊆ {y | Q1 y = 0} :=
      closure_minimal (fun y hy => (hQQ2 y hy).trans (hQ20 y)) (isClosed_eq (isP_cont hQ1p) continuous_const)
    rw [closure_Ioo hr12.ne] at hcl
    exact hcl
  have hfin := hQ1z x hx
  simp only [hQ1] at hfin
  rw [hQQ1 x hx]
  exact hfin

end Internal.GaugeFluxParts

theorem rowMode_zero_calc {α : ℝ} {k N slots : ℕ} {c : FracCellData k N}
    (hc : IsFormData α c) {K : CellBox} {S : CellScalars} {B : CellBases} {Cl : CellClasses}
    {R : CellRows N slots k} (hR : IsCellData α c K S B Cl R) (hsh : IsRowShape c K S R) {a : Fin N}
    (ha : a ∈ R.rowSet) (x z : ℝ) (hx : x ∈ Set.Ioo K.r₁ K.r₂) (hz : z ∈ Set.Ioo K.z₁ K.z₂) :
    HasDerivAt (fun s => rowModeVec c a 0 (s, z) 0) (rowModeGrad c a 0 (x, z) 0 0) x ∧
      HasDerivAt (fun s => rowModeVec c a 0 (x, s) 2) (rowModeGrad c a 0 (x, z) 2 2) z ∧
      rowModeVec c a 0 (x, z) 0 = (x : ℂ) * rowModeGrad c a 0 (x, z) 1 1 ∧
      rowModeGrad c a 0 (x, z) 0 0 + rowModeGrad c a 0 (x, z) 1 1 + rowModeGrad c a 0 (x, z) 2 2 = 0 :=
  Internal.GaugeFluxParts.zero_calc hR hsh ha x z hx hz

theorem presSide_flux_of_calc {α : ℝ} {k N slots : ℕ} {c : FracCellData k N}
    {K : CellBox} {S : CellScalars} {B : CellBases} {Cl : CellClasses}
    {R : CellRows N slots k} (hR : IsCellData α c K S B Cl R) (hsh : IsRowShape c K S R) {L : CellLayout}
    (hL : IsPressureLayout c K S B L) {a : Fin N} (ha : a ∈ R.rowSet)
    (hcalc : ∀ x ∈ Set.Ioo K.r₁ K.r₂, ∀ z ∈ Set.Ioo K.z₁ K.z₂,
      HasDerivAt (fun s => rowModeVec c a 0 (s, z) 0) (rowModeGrad c a 0 (x, z) 0 0) x ∧
      HasDerivAt (fun s => rowModeVec c a 0 (x, s) 2) (rowModeGrad c a 0 (x, z) 2 2) z ∧
      rowModeVec c a 0 (x, z) 0 = (x : ℂ) * rowModeGrad c a 0 (x, z) 1 1 ∧
      rowModeGrad c a 0 (x, z) 0 0 + rowModeGrad c a 0 (x, z) 1 1 + rowModeGrad c a 0 (x, z) 2 2 = 0)
    (P₁ P₂ : ℝ → ℂ)
    (hp₁ : ∃ s : Fin L.presCount, ∃ cf : Fin L.degSide → ℂ, ∀ t, P₁ t = ∑ d, cf d * ((L.presSegment s).test d t : ℂ))
    (hp₂ : ∃ s : Fin L.presCount, ∃ cf : Fin L.degSide → ℂ, ∀ t, P₂ t = ∑ d, cf d * ((L.presSegment s).test d t : ℂ))
    (h₁ : ∀ r ∈ Set.Icc K.r₁ K.r₂, rowModeVec c a 0 (r, K.z₁) 2 = P₁ r)
    (h₂ : ∀ r ∈ Set.Icc K.r₁ K.r₂, rowModeVec c a 0 (r, K.z₂) 2 = P₂ r) (x : ℝ) (hx : x ∈ Set.Icc K.r₁ K.r₂) :
    (x : ℂ) * (∫ z in K.z₁..K.z₂, (starRingEnd ℂ) (rowModeVec c a 0 (x, z) 0))
      + (∫ ρ in (0 : ℝ)..x, (ρ : ℂ) * (starRingEnd ℂ) (P₂ ρ)) - (∫ ρ in (0 : ℝ)..x, (ρ : ℂ) * (starRingEnd ℂ) (P₁ ρ)) = 0 := by
  have h := Internal.GaugeFluxParts.flux_main hR hsh ha hcalc P₁ P₂ hp₁ hp₂ h₁ h₂ x hx
  have hcj : ∀ P : ℝ → ℂ, ∫ ρ in (0 : ℝ)..x, (ρ : ℂ) * (starRingEnd ℂ) (P ρ) =
      (starRingEnd ℂ) (∫ ρ in (0 : ℝ)..x, (ρ : ℂ) * P ρ) := by
    intro P
    rw [← Internal.GaugeFluxParts.ii_conj]
    refine intervalIntegral.integral_congr fun ρ _ => ?_
    simp [map_mul, Complex.conj_ofReal]
  rw [hcj P₂, hcj P₁, Internal.GaugeFluxParts.ii_conj]
  have h' := congrArg (starRingEnd ℂ) h
  simpa [map_add, map_sub, map_mul, Complex.conj_ofReal] using h'

end CellFormula

end CellCert

end Breakdown
