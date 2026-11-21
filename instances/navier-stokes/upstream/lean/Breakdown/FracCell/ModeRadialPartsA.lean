import Breakdown.FracCell.ResolvedEnergySt
import Breakdown.FracCell.CylModeWeak
import Breakdown.FracCell.LowEntry
import Breakdown.FracCell.ModeGradSquare

open scoped ContDiff Convolution Pointwise
open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellAnalysis.ModeRadialPartsA.Internal

open SteadyCert Assembly CellFormula

def unitAt (q : ℝ × ℝ) : Fin 3 → Space :=
  ![EuclideanSpace.single 0 q.1 + EuclideanSpace.single 1 q.2,
    EuclideanSpace.single 0 (-q.2) + EuclideanSpace.single 1 q.1, axialUnit]

theorem unitAt_circle (θ : ℝ) : unitAt (Real.cos θ, Real.sin θ) = frameUnit θ := rfl

def rowQ (a : Fin 3) (q : ℝ × ℝ) : Space →L[ℝ] ℝ :=
  ∑ k : Fin 3, unitAt q a k • EuclideanSpace.proj k

theorem rowQ_apply (a : Fin 3) (θ : ℝ) (u : Space) :
    rowQ a (Real.cos θ, Real.sin θ) u = inner ℝ u (frameUnit θ a) := by
  simp [rowQ, unitAt_circle, PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

theorem unitAt_coord_smooth (a k : Fin 3) : ContDiff ℝ ∞ (fun q : ℝ × ℝ => unitAt q a k) := by
  fin_cases a <;> fin_cases k <;>
    simp [unitAt, axialUnit] <;>
    first | exact contDiff_const | exact contDiff_fst | exact contDiff_snd | exact contDiff_snd.neg

theorem unitAt_smooth (a : Fin 3) : ContDiff ℝ ∞ (fun q : ℝ × ℝ => unitAt q a) :=
  (contDiff_piLp 2).2 fun k => unitAt_coord_smooth a k

theorem rowQ_smooth (a : Fin 3) : ContDiff ℝ ∞ (rowQ a) := by
  unfold rowQ
  exact ContDiff.sum fun k _ => (unitAt_coord_smooth a k).smul contDiff_const

def entryQ (a b : Fin 3) (q : ℝ × ℝ) : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  (rowQ a q).comp (ContinuousLinearMap.apply ℝ Space (unitAt q b))

theorem entryQ_smooth (a b : Fin 3) : ContDiff ℝ ∞ (entryQ a b) :=
  (rowQ_smooth a).clm_comp ((ContinuousLinearMap.apply ℝ Space).contDiff.comp (unitAt_smooth b))

theorem entryQ_apply (a b : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space) :
    entryQ a b (Real.cos θ, Real.sin θ) M = inner ℝ (M (frameUnit θ b)) (frameUnit θ a) := by
  simp only [entryQ, unitAt_circle, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  exact rowQ_apply a θ _

theorem vec_expand (u : Space) : u = ∑ j : Fin 3, u j • unitVector j := by
  ext i; fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

theorem norm_le_cols {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : Space →L[ℝ] E) :
    ‖A‖ ≤ ∑ i : Fin 3, ‖A (unitVector i)‖ := by
  refine A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun u => ?_
  conv_lhs => rw [vec_expand u]
  rw [map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_smul, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u i) (norm_nonneg _)

theorem loc_norm {E : Type} [NormedAddCommGroup E] {f : Space → E} (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun y => ‖f y‖) volume :=
  hf.mono hf.aestronglyMeasurable.norm (Filter.Eventually.of_forall fun y => by simp)

theorem loc_of_cols {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Space → (Space →L[ℝ] E)} (hm : AEStronglyMeasurable A volume)
    (hc : ∀ i, LocallyIntegrable (fun y => A y (unitVector i)) volume) : LocallyIntegrable A volume := by
  have hs : LocallyIntegrable (fun y => ∑ i : Fin 3, ‖A y (unitVector i)‖) volume := by
    simp only [Fin.sum_univ_three]
    exact ((loc_norm (hc 0)).add (loc_norm (hc 1))).add (loc_norm (hc 2))
  refine hs.mono hm (Filter.Eventually.of_forall fun y => ?_)
  refine (norm_le_cols (A y)).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]

theorem memLp_col {G : Space → (Space →L[ℝ] Space)} (hm : AEStronglyMeasurable G volume)
    (hi : Integrable (fun y => entrySq (G y))) (j : Fin 3) : MemLp (fun y => G y (unitVector j)) 2 volume := by
  have hmj : AEStronglyMeasurable (fun y => G y (unitVector j)) volume :=
    hm.apply_continuousLinearMap (unitVector j)
  refine (memLp_two_iff_integrable_sq_norm hmj).2 (hi.mono' (hmj.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_))
  simp only [Real.norm_eq_abs, abs_pow, sq_abs]
  unfold entrySq
  exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ j)

theorem memLp_col2 {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hm : AEStronglyMeasurable H volume)
    (hi : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)) (j i : Fin 3) :
    MemLp (fun y => H y (unitVector j) (unitVector i)) 2 volume := by
  have hmj : AEStronglyMeasurable (fun y => H y (unitVector j) (unitVector i)) volume :=
    (hm.apply_continuousLinearMap (unitVector j)).apply_continuousLinearMap (unitVector i)
  refine (memLp_two_iff_integrable_sq_norm hmj).2 (hi.mono' (hmj.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_))
  simp only [Real.norm_eq_abs, abs_pow, sq_abs]
  calc ‖H y (unitVector j) (unitVector i)‖ ^ 2 ≤ ∑ i' : Fin 3, ‖H y (unitVector j) (unitVector i')‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ‖H y (unitVector j) (unitVector i')‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ i)
    _ ≤ ∑ j' : Fin 3, ∑ i' : Fin 3, ‖H y (unitVector j') (unitVector i')‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ∑ i' : Fin 3, ‖H y (unitVector j') (unitVector i')‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)

theorem locG {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) :
    LocallyIntegrable G volume :=
  loc_of_cols hs.measurable_gradient fun j =>
    (memLp_col hs.measurable_gradient hs.gradient_two j).locallyIntegrable (by norm_num)

theorem locHc {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (j : Fin 3) :
    LocallyIntegrable (fun y => H y (unitVector j)) volume :=
  loc_of_cols (hs.measurable_second.apply_continuousLinearMap (unitVector j)) fun i =>
    (memLp_col2 hs.measurable_second hs.second_two j i).locallyIntegrable (by norm_num)

theorem locH {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) :
    LocallyIntegrable H volume :=
  loc_of_cols hs.measurable_second (locHc hs)

theorem weakG {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) :
    ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) • G y = -∫ y, φ y • H y (unitVector j) := by
  intro φ hφ j
  have hd : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have i1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • G y) volume :=
    (locG hs).integrable_smul_left_of_hasCompactSupport hd (hφ.2.fderiv_apply (𝕜 := ℝ) _)
  have i2 : Integrable (fun y => φ y • H y (unitVector j)) volume :=
    (locHc hs j).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
  have key : ∀ i, (∫ y, fderiv ℝ φ y (unitVector j) • G y) (unitVector i) =
      (-∫ y, φ y • H y (unitVector j)) (unitVector i) := by
    intro i
    rw [neg_apply, ContinuousLinearMap.integral_apply i1, ContinuousLinearMap.integral_apply i2]
    simpa using hs.weak_second φ hφ i j
  refine ContinuousLinearMap.ext fun u => ?_
  rw [vec_expand u]
  simp only [map_sum, map_smul, key]

theorem scale {A B c d : ℝ × ℝ → ℂ} (k : ℂ) (h : ∫ p, c p * A p = -∫ p, d p * B p) :
    ∫ p, c p * (k * A p) = -∫ p, d p * (k * B p) := by
  have e1 : (fun p => c p * (k * A p)) = fun p => k * (c p * A p) := funext fun p => by ring
  have e2 : (fun p => d p * (k * B p)) = fun p => k * (d p * B p) := funext fun p => by ring
  rw [e1, e2, integral_const_mul, integral_const_mul, h, mul_neg]

theorem weak_radial {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (a b : Fin 3)
    (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hpos : ∀ p ∈ tsupport φ, 0 < p.1) :
    ∫ p, ((fderiv ℝ φ p (1, 0) : ℝ) : ℂ) * gradMode m n G a b p = -∫ p, (φ p : ℂ) * modeThird m n H a b 0 p := by
  have hgm : ∀ p : ℝ × ℝ, gradMode m n G a b p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (entryQ a b (Real.cos θ, Real.sin θ) (G (cylPoint p.1 θ p.2)) : ℂ) := by
    intro p
    simp only [gradMode, modeMat, entryQ_apply]
    rfl
  have hth : ∀ p : ℝ × ℝ, modeThird m n H a b 0 p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (entryQ a b (Real.cos θ, Real.sin θ) (H (cylPoint p.1 θ p.2) (radialUnit θ)) : ℂ) := by
    intro p
    simp only [modeThird, entryQ_apply]
    rfl
  simp only [hth, hgm]
  exact scale _ (cylModeWeak (Space →L[ℝ] Space) G H (locG hs) (locHc hs) (weakG hs) (entryQ a b)
    (entryQ_smooth a b) m n φ hφ hc hpos).1

open LowEntry.Internal in
theorem third_eq (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b : Fin 3) (p : ℝ × ℝ) :
    modeThird m n H a b 0 p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in Set.Ioo (-Real.pi) Real.pi, gradKernel m n a b θ (H (cylPoint p.1 θ p.2) (radialUnit θ)) := by
  unfold modeThird
  rw [per_interval]
  · rfl
  · intro θ
    simp only [phase_per, cylPoint_per, frameThird, frameUnit, radialUnit, angularUnit,
      Real.cos_add_two_pi, Real.sin_add_two_pi]

open LowEntry.Internal in
theorem third_int (K : CellBox) (hK : IsCellBox K) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (a b : Fin 3) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * modeThird m n H a b 0 p) K.rect := by
  have hc : Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) => gradKernel m n a b q.1 (q.2 (radialUnit q.1))) :=
    (gradKernel_cont m n a b).comp (continuous_fst.prodMk (continuous_snd.clm_apply (radialUnit_cont.comp continuous_fst)))
  have hb : ∀ θ (M : Space →L[ℝ] Space →L[ℝ] Space), ‖gradKernel m n a b θ (M (radialUnit θ))‖ ≤ ‖M‖ := by
    intro θ M
    refine (gradKernel_bound m n a b θ _).trans ((M.le_opNorm _).trans ?_)
    simpa using mul_le_mul_of_nonneg_left (unit_norm θ 0) (norm_nonneg M)
  have h := mode_int K hK (locH hs) (fun θ M => gradKernel m n a b θ (M (radialUnit θ))) hc hb
  have e : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * modeThird m n H a b 0 p) = fun p => (1 / (2 * Real.pi) : ℂ) *
      ((K.lineWeight p.1 : ℂ) * ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        gradKernel m n a b θ (H (cylPoint p.1 θ p.2) (radialUnit θ))) := by
    funext p; rw [third_eq]; ring
  rw [e]
  exact h.const_mul _

open LowEntry.Internal in
theorem grad_int (K : CellBox) (hK : IsCellBox K) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (a b : Fin 3) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * gradMode m n G a b p) K.rect :=
  gradMode_int K hK m n hs.measurable_gradient hs.gradient_two a b

end Breakdown.CellCert.CellAnalysis.ModeRadialPartsA.Internal

namespace Breakdown.CellCert.CellAnalysis.ModeRadialPartsA.Internal

open SteadyCert Set Filter Topology

theorem st_deriv_zero {x : ℝ} (hx : x < 0 ∨ 1 < x) : deriv Real.smoothTransition x = 0 := by
  rcases hx with hx | hx
  · have e : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      (eventually_lt_nhds hx).mono fun y hy => Real.smoothTransition.zero_of_nonpos hy.le
    rw [e.deriv_eq]; simp
  · have e : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
      (eventually_gt_nhds hx).mono fun y hy => Real.smoothTransition.one_of_one_le hy.le
    rw [e.deriv_eq]; simp

theorem st_bound : ∃ S, 0 ≤ S ∧ ∀ x, |deriv Real.smoothTransition x| ≤ S := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc.continuousOn (s := Icc (0 : ℝ) 1))
  refine ⟨max S 0, le_max_right _ _, fun x => ?_⟩
  by_cases h : x ∈ Icc (0 : ℝ) 1
  · exact le_trans (show |deriv Real.smoothTransition x| ≤ S by simpa [Real.norm_eq_abs] using hS x h) (le_max_left _ _)
  · have hx : x < 0 ∨ 1 < x := by
      by_contra hc'
      push Not at hc'
      exact h ⟨hc'.1, hc'.2⟩
    rw [st_deriv_zero hx, abs_zero]
    exact le_max_right _ _

def cutR (a b δ r : ℝ) : ℝ := Real.smoothTransition ((r - a - δ) / δ) * Real.smoothTransition ((b - δ - r) / δ)

theorem cutR_nonneg (a b δ r : ℝ) : 0 ≤ cutR a b δ r :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem cutR_le_one (a b δ r : ℝ) : cutR a b δ r ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)

theorem cutR_contDiff (a b δ : ℝ) : ContDiff ℝ 1 (cutR a b δ) := by
  unfold cutR
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem cutR_zero {a b δ r : ℝ} (hδ : 0 < δ) (h : r ≤ a + δ ∨ b - δ ≤ r) : cutR a b δ r = 0 := by
  unfold cutR
  rcases h with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (x := (r - a - δ) / δ) (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le), zero_mul]
  · rw [Real.smoothTransition.zero_of_nonpos (x := (b - δ - r) / δ) (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le), mul_zero]

theorem cutR_one {a b δ r : ℝ} (hδ : 0 < δ) (h1 : a + 2 * δ ≤ r) (h2 : r ≤ b - 2 * δ) : cutR a b δ r = 1 := by
  unfold cutR
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, mul_one]
  · rw [le_div_iff₀ hδ]; linarith
  · rw [le_div_iff₀ hδ]; linarith

theorem cutR_eventually {a b r : ℝ} (h1 : a < r) (h2 : r < b) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), cutR a b δ r = 1 ∧ deriv (cutR a b δ) r = 0 := by
  have hc : 0 < min (r - a) (b - r) / 3 := by
    have := lt_min (sub_pos.2 h1) (sub_pos.2 h2)
    linarith
  filter_upwards [Ioo_mem_nhdsGT hc] with δ hδ
  have hm1 : min (r - a) (b - r) ≤ r - a := min_le_left _ _
  have hm2 : min (r - a) (b - r) ≤ b - r := min_le_right _ _
  have e : cutR a b δ =ᶠ[𝓝 r] fun _ => (1 : ℝ) := by
    have o : Ioo (a + 2 * δ) (b - 2 * δ) ∈ 𝓝 r := Ioo_mem_nhds (by linarith [hδ.2]) (by linarith [hδ.2])
    filter_upwards [o] with r' hr'
    exact cutR_one hδ.1 hr'.1.le hr'.2.le
  refine ⟨e.eq_of_nhds, ?_⟩
  rw [e.deriv_eq]; simp

theorem cutR_hasDeriv (a b δ r : ℝ) :
    HasDerivAt (cutR a b δ)
      (deriv Real.smoothTransition ((r - a - δ) / δ) * (1 / δ) * Real.smoothTransition ((b - δ - r) / δ) +
        Real.smoothTransition ((r - a - δ) / δ) * (deriv Real.smoothTransition ((b - δ - r) / δ) * ((0 - 1) / δ))) r := by
  have hs : ∀ x, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x := fun x =>
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) x).hasDerivAt
  have d1 : HasDerivAt (fun r : ℝ => (r - a - δ) / δ) (1 / δ) r :=
    (((hasDerivAt_id' r).sub_const a).sub_const δ).div_const δ
  have d2 : HasDerivAt (fun r : ℝ => (b - δ - r) / δ) ((0 - 1) / δ) r :=
    ((hasDerivAt_const r (b - δ)).sub (hasDerivAt_id' r)).div_const δ
  exact ((hs _).comp r d1).mul ((hs _).comp r d2)

theorem cutR_term {a b δ r M S v : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hS : ∀ x, |deriv Real.smoothTransition x| ≤ S)
    (h1 : |v| ≤ M * (r - a)) (h2 : |v| ≤ M * (b - r)) :
    |deriv (cutR a b δ) r * v| ≤ 4 * S * M := by
  rw [(cutR_hasDeriv a b δ r).deriv]
  set x1 := (r - a - δ) / δ
  set x2 := (b - δ - r) / δ
  have S0 : 0 ≤ S := (abs_nonneg _).trans (hS 0)
  have t1 : |deriv Real.smoothTransition x1 * (1 / δ) * Real.smoothTransition x2 * v| ≤ 2 * S * M := by
    by_cases hx : x1 < 0 ∨ 1 < x1
    · rw [st_deriv_zero hx]; simp; positivity
    · push Not at hx
      have hx1 : r - a ≤ 2 * δ := by
        have := hx.2
        rw [div_le_one hδ] at this
        linarith
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (one_div_pos.2 hδ),
        abs_of_nonneg (Real.smoothTransition.nonneg _)]
      have hv : |v| ≤ M * (2 * δ) := h1.trans (mul_le_mul_of_nonneg_left hx1 hM)
      calc |deriv Real.smoothTransition x1| * (1 / δ) * Real.smoothTransition x2 * |v|
          ≤ S * (1 / δ) * 1 * (M * (2 * δ)) := by
            gcongr
            all_goals first | exact hS _ | exact Real.smoothTransition.le_one _ | exact Real.smoothTransition.nonneg _ | positivity
        _ = 2 * S * M := by field_simp
  have t2 : |Real.smoothTransition x1 * (deriv Real.smoothTransition x2 * ((0 - 1) / δ)) * v| ≤ 2 * S * M := by
    by_cases hx : x2 < 0 ∨ 1 < x2
    · rw [st_deriv_zero hx]; simp; positivity
    · push Not at hx
      have hx1 : b - r ≤ 2 * δ := by
        have := hx.2
        rw [div_le_one hδ] at this
        linarith
      have e : |(0 - 1) / δ| = 1 / δ := by rw [zero_sub, neg_div, abs_neg, abs_of_pos (one_div_pos.2 hδ)]
      rw [abs_mul, abs_mul, abs_mul, e, abs_of_nonneg (Real.smoothTransition.nonneg _)]
      have hv : |v| ≤ M * (2 * δ) := h2.trans (mul_le_mul_of_nonneg_left hx1 hM)
      calc Real.smoothTransition x1 * (|deriv Real.smoothTransition x2| * (1 / δ)) * |v|
          ≤ 1 * (S * (1 / δ)) * (M * (2 * δ)) := by
            gcongr
            all_goals first | exact hS _ | exact Real.smoothTransition.le_one _ | exact Real.smoothTransition.nonneg _ | positivity
        _ = 2 * S * M := by field_simp
  rw [add_mul]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 2 * S * M + 2 * S * M := add_le_add t1 t2
    _ = 4 * S * M := by ring


theorem lw_hasDeriv (K : CellBox) (r : ℝ) : HasDerivAt K.lineWeight (if K.r₁ = 0 then 1 else 0) r := by
  unfold CellBox.lineWeight
  split_ifs
  · exact hasDerivAt_id' r
  · exact hasDerivAt_const r (1 : ℝ)

theorem lw_contDiff (K : CellBox) : ContDiff ℝ 1 K.lineWeight := by
  unfold CellBox.lineWeight
  split_ifs
  · exact contDiff_id
  · exact contDiff_const

theorem lw_nonneg (K : CellBox) (hK : IsCellBox K) {r : ℝ} (hr : K.r₁ ≤ r) : 0 ≤ K.lineWeight r := by
  unfold CellBox.lineWeight
  split_ifs
  · linarith [hK.r_order.1]
  · exact zero_le_one

theorem line_hasDeriv {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (r z : ℝ) :
    HasDerivAt (fun r => ψ (r, z)) (fderiv ℝ ψ (r, z) (1, 0)) r :=
  ((hψ.differentiable (by norm_num)) (r, z)).hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_id' r).prodMk (hasDerivAt_const r z))

theorem extend_c1 (K : CellBox) (hK : IsCellBox K) (F T : ℝ × ℝ → ℂ)
    (mF : AEStronglyMeasurable F (volume.restrict K.rect)) (mT : AEStronglyMeasurable T (volume.restrict K.rect))
    (hF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect)
    (hT : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * T p) K.rect)
    (hW : ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ioo K.r₁ K.r₂ ×ˢ Ioo K.z₁ K.z₂ →
      ∫ p, ((fderiv ℝ φ p (1, 0) : ℝ) : ℂ) * F p = -∫ p, (φ p : ℂ) * T p)
    (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ) (h1 : ∀ z, ψ (K.r₁, z) = 0) (h2 : ∀ z, ψ (K.r₂, z) = 0) :
    IntegrableOn (fun p => F p * ((deriv (fun r => K.lineWeight r * ψ (r, p.2)) p.1 : ℝ) : ℂ)) K.rect ∧
    ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * T p * (ψ p : ℂ)
      = -∫ p in K.rect, F p * ((deriv (fun r => K.lineWeight r * ψ (r, p.2)) p.1 : ℝ) : ℂ) := by
  set U : Set (ℝ × ℝ) := Ioo K.r₁ K.r₂ ×ˢ Ioo K.z₁ K.z₂ with hUdef
  have hUm : MeasurableSet U := measurableSet_Ioo.prod measurableSet_Ioo
  have hRm : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hUr : U ⊆ K.rect := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hU : U =ᵐ[volume] K.rect := Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc
  have eU : ∀ f : ℝ × ℝ → ℂ, ∫ p in K.rect, f p = ∫ p in U, f p := fun f => (setIntegral_congr_set hU).symm
  have hcpt : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  set dψ : ℝ × ℝ → ℝ := fun p => fderiv ℝ ψ p (1, 0) with hdψ
  have cdψ : Continuous dψ := (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  obtain ⟨M0, hM0⟩ := hcpt.exists_bound_of_continuousOn cdψ.continuousOn
  set M := max M0 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  have hMb : ∀ p ∈ K.rect, |dψ p| ≤ M := fun p hp =>
    (show |dψ p| ≤ M0 by simpa [Real.norm_eq_abs] using hM0 p hp).trans (le_max_left _ _)
  obtain ⟨S, hS0, hS⟩ := st_bound
  have vl : ∀ p ∈ K.rect, |ψ p| ≤ M * (p.1 - K.r₁) := by
    rintro ⟨r, z⟩ ⟨⟨hr1, hr2⟩, hz⟩
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t => ψ (t, z)) (f' := fun t => dψ (t, z))
      (C := M) (a := K.r₁) (b := K.r₂) (fun t _ => (line_hasDeriv hψ t z).hasDerivWithinAt)
      (fun t ht => by simpa [Real.norm_eq_abs] using hMb (t, z) ⟨⟨ht.1, ht.2.le⟩, hz⟩) r ⟨hr1, hr2⟩
    simpa [h1, Real.norm_eq_abs] using this
  have vr : ∀ p ∈ K.rect, |ψ p| ≤ M * (K.r₂ - p.1) := by
    rintro ⟨r, z⟩ ⟨⟨hr1, hr2⟩, hz⟩
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t => ψ (t, z)) (f' := fun t => dψ (t, z))
      (C := M) (a := r) (b := K.r₂) (fun t _ => (line_hasDeriv hψ t z).hasDerivWithinAt)
      (fun t ht => by simpa [Real.norm_eq_abs] using hMb (t, z) ⟨⟨hr1.trans ht.1, ht.2.le⟩, hz⟩) K.r₂ ⟨hr2, le_rfl⟩
    rw [h2, zero_sub, norm_neg, Real.norm_eq_abs] at this
    exact this
  set cw : ℝ := if K.r₁ = 0 then 1 else 0 with hcw
  set du : ℝ × ℝ → ℝ := fun p => cw * ψ p + K.lineWeight p.1 * dψ p with hdu
  have cdu : Continuous du :=
    (continuous_const.mul hψ.continuous).add (((lw_contDiff K).continuous.comp continuous_fst).mul cdψ)
  have edu : ∀ p : ℝ × ℝ, deriv (fun r => K.lineWeight r * ψ (r, p.2)) p.1 = du p := fun p =>
    ((lw_hasDeriv K p.1).mul (line_hasDeriv hψ p.1 p.2)).deriv
  have bdu : ∀ p ∈ K.rect, |du p| ≤ 2 * M * K.lineWeight p.1 := by
    intro p hp
    have hb := hMb p hp
    have hl := vl p hp
    simp only [hdu, hcw, CellBox.lineWeight]
    split_ifs with h
    · rw [h, sub_zero] at hl
      have hr : 0 ≤ p.1 := hp.1.1.trans' (le_of_eq h.symm)
      calc |1 * ψ p + p.1 * dψ p| ≤ |ψ p| + p.1 * |dψ p| := by
            rw [one_mul]; refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_of_nonneg hr]
        _ ≤ M * p.1 + p.1 * M := add_le_add hl (mul_le_mul_of_nonneg_left hb hr)
        _ = 2 * M * p.1 := by ring
    · rw [zero_mul, zero_add, one_mul]
      linarith
  set φ : ℝ → ℝ × ℝ → ℝ := fun δ p => cutR K.r₁ K.r₂ δ p.1 * cutR K.z₁ K.z₂ δ p.2 * (K.lineWeight p.1 * ψ p)
    with hφdef
  have φC : ∀ δ, ContDiff ℝ 1 (φ δ) := fun δ =>
    (((cutR_contDiff _ _ _).comp contDiff_fst).mul ((cutR_contDiff _ _ _).comp contDiff_snd)).mul
      (((lw_contDiff K).comp contDiff_fst).mul hψ)
  have φsupp : ∀ δ, 0 < δ → ∀ p, φ δ p ≠ 0 → p ∈ Icc (K.r₁ + δ) (K.r₂ - δ) ×ˢ Icc (K.z₁ + δ) (K.z₂ - δ) := by
    intro δ hδ p hp
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> by_contra hc <;> push Not at hc <;> apply hp <;> simp only [hφdef]
    · rw [cutR_zero hδ (Or.inl hc.le)]; ring
    · rw [cutR_zero hδ (Or.inr hc.le)]; ring
    · rw [cutR_zero (a := K.z₁) hδ (Or.inl hc.le)]; ring
    · rw [cutR_zero (a := K.z₁) hδ (Or.inr hc.le)]; ring
  have φts : ∀ δ, 0 < δ → tsupport (φ δ) ⊆ U := by
    intro δ hδ
    refine (closure_minimal (fun p hp => φsupp δ hδ p hp) ((isClosed_Icc).prod isClosed_Icc)).trans ?_
    rintro p ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have φcs : ∀ δ, 0 < δ → HasCompactSupport (φ δ) := fun δ hδ =>
    HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc) fun p hp => by
      by_contra hc; exact hp (φsupp δ hδ p hc)
  have φd : ∀ δ (p : ℝ × ℝ), fderiv ℝ (φ δ) p (1, 0) =
      deriv (cutR K.r₁ K.r₂ δ) p.1 * cutR K.z₁ K.z₂ δ p.2 * (K.lineWeight p.1 * ψ p)
        + cutR K.r₁ K.r₂ δ p.1 * cutR K.z₁ K.z₂ δ p.2 * du p := by
    intro δ p
    have hc : HasDerivAt (cutR K.r₁ K.r₂ δ) (deriv (cutR K.r₁ K.r₂ δ) p.1) p.1 :=
      ((cutR_contDiff _ _ _).differentiable (by norm_num) p.1).hasDerivAt
    have A := ((hc.mul_const (cutR K.z₁ K.z₂ δ p.2)).mul ((lw_hasDeriv K p.1).mul (line_hasDeriv hψ p.1 p.2)))
    have B := line_hasDeriv (φC δ) p.1 p.2
    rw [B.unique A]
    simp only [hdu, hdψ, hcw, Pi.mul_apply, Prod.mk.eta]
  have iW : ∀ δ, 0 < δ → ∫ p in U, ((fderiv ℝ (φ δ) p (1, 0) : ℝ) : ℂ) * F p = -∫ p in U, ((φ δ p : ℝ) : ℂ) * T p := by
    intro δ hδ
    have e1 : ∫ p in U, ((fderiv ℝ (φ δ) p (1, 0) : ℝ) : ℂ) * F p = ∫ p, ((fderiv ℝ (φ δ) p (1, 0) : ℝ) : ℂ) * F p :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => by
        rw [fderiv_of_notMem_tsupport ℝ (fun h => hp (φts δ hδ h))]; simp
    have e2 : ∫ p in U, ((φ δ p : ℝ) : ℂ) * T p = ∫ p, ((φ δ p : ℝ) : ℂ) * T p :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hp (φts δ hδ h))]; simp
    rw [e1, e2]
    exact hW (φ δ) (φC δ) (φcs δ hδ) (φts δ hδ)
  have mFU : AEStronglyMeasurable F (volume.restrict U) := mF.mono_measure (Measure.restrict_mono hUr le_rfl)
  have mTU : AEStronglyMeasurable T (volume.restrict U) := mT.mono_measure (Measure.restrict_mono hUr le_rfl)
  have hFU : Integrable (fun p => (K.lineWeight p.1 : ℂ) * F p) (volume.restrict U) := hF.mono_set hUr
  have hTU : Integrable (fun p => (K.lineWeight p.1 : ℂ) * T p) (volume.restrict U) := hT.mono_set hUr
  have nlw : ∀ p ∈ K.rect, ∀ X : ℂ, ‖(K.lineWeight p.1 : ℂ) * X‖ = K.lineWeight p.1 * ‖X‖ := fun p hp X => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (lw_nonneg K hK hp.1.1)]
  have lA : Tendsto (fun δ => ∫ p in U, ((fderiv ℝ (φ δ) p (1, 0) : ℝ) : ℂ) * F p) (𝓝[>] 0)
      (𝓝 (∫ p in U, ((du p : ℝ) : ℂ) * F p)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun p => (4 * S * M + 2 * M) * ‖(K.lineWeight p.1 : ℂ) * F p‖) ?_ ?_ (hFU.norm.const_mul _) ?_
    · refine Eventually.of_forall fun δ => ?_
      have hc : Continuous (fun p : ℝ × ℝ => fderiv ℝ (φ δ) p (1, 0)) :=
        ((φC δ).continuous_fderiv (by norm_num)).clm_apply continuous_const
      exact (Complex.continuous_ofReal.comp hc).aestronglyMeasurable.mul mFU
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      refine ae_restrict_of_forall_mem hUm fun p hp => ?_
      have hpR := hUr hp
      have hl0 := lw_nonneg K hK hpR.1.1
      have z0 := cutR_nonneg K.z₁ K.z₂ δ p.2
      have z1 := cutR_le_one K.z₁ K.z₂ δ p.2
      have r0 := cutR_nonneg K.r₁ K.r₂ δ p.1
      have r1 := cutR_le_one K.r₁ K.r₂ δ p.1
      have t1 := cutR_term (a := K.r₁) (b := K.r₂) (δ := δ) (r := p.1) hδ hM hS (vl p hpR) (vr p hpR)
      have t2 := bdu p hpR
      have key : |deriv (cutR K.r₁ K.r₂ δ) p.1 * cutR K.z₁ K.z₂ δ p.2 * (K.lineWeight p.1 * ψ p)
          + cutR K.r₁ K.r₂ δ p.1 * cutR K.z₁ K.z₂ δ p.2 * du p| ≤ (4 * S * M + 2 * M) * K.lineWeight p.1 := by
        calc _ ≤ |deriv (cutR K.r₁ K.r₂ δ) p.1 * cutR K.z₁ K.z₂ δ p.2 * (K.lineWeight p.1 * ψ p)|
              + |cutR K.r₁ K.r₂ δ p.1 * cutR K.z₁ K.z₂ δ p.2 * du p| := abs_add_le _ _
          _ = cutR K.z₁ K.z₂ δ p.2 * K.lineWeight p.1 * |deriv (cutR K.r₁ K.r₂ δ) p.1 * ψ p|
              + cutR K.r₁ K.r₂ δ p.1 * cutR K.z₁ K.z₂ δ p.2 * |du p| := by
            rw [show deriv (cutR K.r₁ K.r₂ δ) p.1 * cutR K.z₁ K.z₂ δ p.2 * (K.lineWeight p.1 * ψ p) =
              cutR K.z₁ K.z₂ δ p.2 * K.lineWeight p.1 * (deriv (cutR K.r₁ K.r₂ δ) p.1 * ψ p) by ring,
              abs_mul (cutR K.z₁ K.z₂ δ p.2 * K.lineWeight p.1) (deriv (cutR K.r₁ K.r₂ δ) p.1 * ψ p),
              abs_mul (cutR K.z₁ K.z₂ δ p.2) (K.lineWeight p.1),
              abs_mul (cutR K.r₁ K.r₂ δ p.1 * cutR K.z₁ K.z₂ δ p.2) (du p),
              abs_mul (cutR K.r₁ K.r₂ δ p.1) (cutR K.z₁ K.z₂ δ p.2), abs_of_nonneg z0, abs_of_nonneg hl0,
              abs_of_nonneg r0]
          _ ≤ 1 * K.lineWeight p.1 * (4 * S * M) + 1 * 1 * (2 * M * K.lineWeight p.1) := by
            gcongr
          _ = (4 * S * M + 2 * M) * K.lineWeight p.1 := by ring
      rw [φd, norm_mul, Complex.norm_real, Real.norm_eq_abs, nlw p hpR]
      calc _ ≤ (4 * S * M + 2 * M) * K.lineWeight p.1 * ‖F p‖ := mul_le_mul_of_nonneg_right key (norm_nonneg _)
        _ = _ := by ring
    · refine ae_restrict_of_forall_mem hUm fun p hp => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [(cutR_eventually hp.1.1 hp.1.2).and (cutR_eventually hp.2.1 hp.2.2)] with δ hδ
      rw [φd, hδ.1.1, hδ.1.2, hδ.2.1]
      simp
  have lB : Tendsto (fun δ => ∫ p in U, ((φ δ p : ℝ) : ℂ) * T p) (𝓝[>] 0)
      (𝓝 (∫ p in U, ((K.lineWeight p.1 * ψ p : ℝ) : ℂ) * T p)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun p => (M * (K.r₂ - K.r₁)) * ‖(K.lineWeight p.1 : ℂ) * T p‖) ?_ ?_ (hTU.norm.const_mul _) ?_
    · exact Eventually.of_forall fun δ =>
        (Complex.continuous_ofReal.comp (φC δ).continuous).aestronglyMeasurable.mul mTU
    · refine Eventually.of_forall fun δ => ae_restrict_of_forall_mem hUm fun p hp => ?_
      have hpR := hUr hp
      have hl0 := lw_nonneg K hK hpR.1.1
      have z0 := cutR_nonneg K.z₁ K.z₂ δ p.2
      have z1 := cutR_le_one K.z₁ K.z₂ δ p.2
      have r0 := cutR_nonneg K.r₁ K.r₂ δ p.1
      have r1 := cutR_le_one K.r₁ K.r₂ δ p.1
      have hψb : |ψ p| ≤ M * (K.r₂ - K.r₁) :=
        (vl p hpR).trans (mul_le_mul_of_nonneg_left (by linarith [hpR.1.2]) hM)
      have key : |φ δ p| ≤ M * (K.r₂ - K.r₁) * K.lineWeight p.1 := by
        simp only [hφdef]
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg z0, abs_of_nonneg hl0, abs_of_nonneg r0]
        calc _ ≤ 1 * 1 * (K.lineWeight p.1 * (M * (K.r₂ - K.r₁))) := by gcongr
          _ = _ := by ring
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, nlw p hpR]
      calc _ ≤ M * (K.r₂ - K.r₁) * K.lineWeight p.1 * ‖T p‖ := mul_le_mul_of_nonneg_right key (norm_nonneg _)
        _ = _ := by ring
    · refine ae_restrict_of_forall_mem hUm fun p hp => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [(cutR_eventually hp.1.1 hp.1.2).and (cutR_eventually hp.2.1 hp.2.2)] with δ hδ
      simp only [hφdef]
      rw [hδ.1.1, hδ.2.1]
      simp
  have lim_eq : ∫ p in U, ((du p : ℝ) : ℂ) * F p = -∫ p in U, ((K.lineWeight p.1 * ψ p : ℝ) : ℂ) * T p :=
    tendsto_nhds_unique lA (lB.neg.congr' (by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact (iW δ hδ).symm))
  have eR : (fun p : ℝ × ℝ => F p * ((deriv (fun r => K.lineWeight r * ψ (r, p.2)) p.1 : ℝ) : ℂ)) =
      fun p => F p * ((du p : ℝ) : ℂ) := funext fun p => by rw [edu]
  refine ⟨?_, ?_⟩
  · rw [eR]
    refine Integrable.mono' (hF.norm.const_mul (2 * M))
      (mF.mul (Complex.continuous_ofReal.comp cdu).aestronglyMeasurable) (ae_restrict_of_forall_mem hRm fun p hp => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, nlw p hp]
    calc ‖F p‖ * |du p| ≤ ‖F p‖ * (2 * M * K.lineWeight p.1) := mul_le_mul_of_nonneg_left (bdu p hp) (norm_nonneg _)
      _ = _ := by ring
  · rw [eR, eU, eU]
    have eL : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * T p * (ψ p : ℂ)) =
        fun p => ((K.lineWeight p.1 * ψ p : ℝ) : ℂ) * T p := funext fun p => by push_cast; ring
    have eR2 : (fun p : ℝ × ℝ => F p * ((du p : ℝ) : ℂ)) = fun p => ((du p : ℝ) : ℂ) * F p :=
      funext fun p => by ring
    rw [eL, eR2, lim_eq, neg_neg]


theorem bound_of {f : ℝ × ℝ → ℝ} (hf : Continuous f) (hcf : HasCompactSupport f) :
    ∃ A, 0 ≤ A ∧ ∀ x, |f x| ≤ A := by
  obtain ⟨A, hA⟩ := hcf.isCompact.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max A 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact le_trans (show |f x| ≤ A by simpa [Real.norm_eq_abs] using hA x hx) (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]
    exact le_max_right _ _

theorem conv_bound (ρ : ContDiffBump (0 : ℝ × ℝ)) {g : ℝ × ℝ → ℝ} (hg : Continuous g) {A : ℝ}
    (hA : ∀ x, |g x| ≤ A) (x : ℝ × ℝ) :
    |(ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x| ≤ 3 * A := by
  have h := ρ.dist_normed_convolution_le (μ := volume) (x₀ := x) (ε := 2 * A) hg.aestronglyMeasurable
    (fun y _ => by
      rw [Real.dist_eq]
      calc |g y - g x| ≤ |g y| + |g x| := abs_sub _ _
        _ ≤ A + A := add_le_add (hA y) (hA x)
        _ = 2 * A := by ring)
  rw [Real.dist_eq] at h
  calc _ = |((ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x) + g x| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ 2 * A + A := add_le_add h (hA x)
    _ = 3 * A := by ring

theorem c1_of_smooth (K : CellBox) (hK : IsCellBox K) (F T : ℝ × ℝ → ℂ)
    (hF : ∀ K' : CellBox, IsCellBox K' → IntegrableOn (fun p => (K'.lineWeight p.1 : ℂ) * F p) K'.rect)
    (hT : ∀ K' : CellBox, IsCellBox K' → IntegrableOn (fun p => (K'.lineWeight p.1 : ℂ) * T p) K'.rect)
    (hW : ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ p ∈ tsupport φ, 0 < p.1) →
      ∫ p, ((fderiv ℝ φ p (1, 0) : ℝ) : ℂ) * F p = -∫ p, (φ p : ℂ) * T p)
    (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo K.r₁ K.r₂ ×ˢ Ioo K.z₁ K.z₂) :
    ∫ p, ((fderiv ℝ φ p (1, 0) : ℝ) : ℂ) * F p = -∫ p, (φ p : ℂ) * T p := by
  set f : ℝ × ℝ → ℝ := fun p => min (min (p.1 - K.r₁) (K.r₂ - p.1)) (min (p.2 - K.z₁) (K.z₂ - p.2)) with hfdef
  have fc : Continuous f :=
    ((continuous_fst.sub continuous_const).min (continuous_const.sub continuous_fst)).min
      ((continuous_snd.sub continuous_const).min (continuous_const.sub continuous_snd))
  obtain ⟨m, hm0, hm⟩ : ∃ m > 0, ∀ p ∈ tsupport φ, m ≤ f p := by
    rcases (tsupport φ).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨p₀, hp₀, hmin⟩ := hc.isCompact.exists_isMinOn h fc.continuousOn
      refine ⟨f p₀, ?_, fun p hp => isMinOn_iff.1 hmin p hp⟩
      obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := hs hp₀
      simp only [hfdef, lt_min_iff, sub_pos]
      exact ⟨⟨a1, a2⟩, b1, b2⟩
  set c := min (m / 2) ((K.r₂ - K.r₁) / 4) with hcdef
  have hr := hK.r_order
  have hc0 : 0 < c := lt_min (by linarith) (by linarith)
  have hcm : c ≤ m / 2 := min_le_left _ _
  have hcr : c ≤ (K.r₂ - K.r₁) / 4 := min_le_right _ _
  set B : Set (ℝ × ℝ) := Icc (K.r₁ + c) (K.r₂ - c) ×ˢ Icc (K.z₁ + c) (K.z₂ - c) with hBdef
  have hBc : IsClosed B := isClosed_Icc.prod isClosed_Icc
  have hBm : MeasurableSet B := measurableSet_Icc.prod measurableSet_Icc
  set K' : CellBox := ⟨K.r₁ + c, K.r₂, K.z₁, K.z₂⟩ with hK'def
  have hK' : IsCellBox K' := ⟨⟨by simp only [hK'def]; linarith, by simp only [hK'def]; linarith⟩, hK.z_order⟩
  have lw' : ∀ r, K'.lineWeight r = 1 := by
    intro r
    simp only [CellBox.lineWeight, hK'def]
    rw [if_neg (by linarith)]
  have BK : B ⊆ K'.rect := prod_mono (Icc_subset_Icc le_rfl (by linarith)) (Icc_subset_Icc (by linarith) (by linarith))
  have iF : IntegrableOn F B := by
    have := (hF K' hK').mono_set BK
    simpa [lw'] using this
  have iT : IntegrableOn T B := by
    have := (hT K' hK').mono_set BK
    simpa [lw'] using this
  have Bpos : ∀ p ∈ B, 0 < p.1 := fun p hp => by linarith [hp.1.1]
  have near : ∀ q ∈ tsupport φ, ∀ a : ℝ × ℝ, ‖a‖ < c → a + q ∈ B := by
    intro q hq a ha
    have h := hm q hq
    simp only [hfdef, le_min_iff] at h
    have h1 : |a.1| ≤ ‖a‖ := by simpa [Real.norm_eq_abs] using norm_fst_le a
    have h2 : |a.2| ≤ ‖a‖ := by simpa [Real.norm_eq_abs] using norm_snd_le a
    obtain ⟨a1, a2⟩ := abs_le.1 h1
    obtain ⟨b1, b2⟩ := abs_le.1 h2
    simp only [hBdef, mem_prod, mem_Icc, Prod.fst_add, Prod.snd_add]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith [h.1.1, h.1.2, h.2.1, h.2.2]
  have tsB : tsupport φ ⊆ B := fun q hq => by simpa using near q hq 0 (by simpa using hc0)
  set g : ℝ × ℝ → ℝ := fun y => fderiv ℝ φ y (1, 0) with hgdef
  have gc : Continuous g := (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have gcs : HasCompactSupport g := hc.fderiv_apply (𝕜 := ℝ) (1, 0)
  obtain ⟨Ag, Ag0, hAg⟩ := bound_of gc gcs
  obtain ⟨Aφ, Aφ0, hAφ⟩ := bound_of hφ.continuous hc
  have gB : ∀ p, p ∉ B → g p = 0 := fun p hp => by
    simp only [hgdef]
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hp (tsB h))]
    simp
  have φB : ∀ p, p ∉ B → φ p = 0 := fun p hp => image_eq_zero_of_notMem_tsupport (fun h => hp (tsB h))
  set ε : ℕ → ℝ := fun k => c / ((k : ℝ) + 2) with hεdef
  have ε0 : ∀ k, 0 < ε k := fun k => div_pos hc0 (by positivity)
  have εc : ∀ k, ε k < c := fun k => by
    simp only [hεdef]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  set ρ : ℕ → ContDiffBump (0 : ℝ × ℝ) := fun k => ⟨ε k / 2, ε k, half_pos (ε0 k), half_lt_self (ε0 k)⟩ with hρdef
  have ρt : Tendsto (fun k => (ρ k).rOut) atTop (𝓝 0) := by
    show Tendsto (fun k : ℕ => c / ((k : ℝ) + 2)) atTop (𝓝 0)
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  set φk : ℕ → ℝ × ℝ → ℝ := fun k => (ρ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ with hφkdef
  have supp : ∀ k x, φk k x ≠ 0 → x ∈ B := by
    intro k x hx
    have hx' : x ∈ Function.support ((ρ k).normed volume) + Function.support φ :=
      support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ) hx
    rw [(ρ k).support_normed_eq] at hx'
    obtain ⟨a, ha, q, hq, rfl⟩ := hx'
    refine near q (subset_tsupport _ hq) a ?_
    have : ‖a‖ < ε k := by simpa using ha
    exact this.trans (εc k)
  have ts : ∀ k, tsupport (φk k) ⊆ B := fun k => closure_minimal (fun x hx => supp k x hx) hBc
  have sm : ∀ k, ContDiff ℝ ∞ (φk k) := fun k =>
    (ρ k).hasCompactSupport_normed.contDiff_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
      (ρ k).contDiff_normed hφ.continuous.locallyIntegrable
  have cs : ∀ k, HasCompactSupport (φk k) := fun k =>
    HasCompactSupport.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) (ρ k).hasCompactSupport_normed hc
  have dk : ∀ k x, fderiv ℝ (φk k) x (1, 0) =
      ((ρ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
    intro k x
    have h := hc.hasFDerivAt_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ)
      ((ρ k).integrable_normed (μ := volume)).locallyIntegrable hφ x
    rw [h.fderiv]
    exact convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) ((ρ k).integrable_normed (μ := volume)).locallyIntegrable (hc.fderiv (𝕜 := ℝ))
      (hφ.continuous_fderiv (by norm_num)) x ((1 : ℝ), (0 : ℝ))
  have Wk : ∀ k, ∫ p in B, ((fderiv ℝ (φk k) p (1, 0) : ℝ) : ℂ) * F p = -∫ p in B, ((φk k p : ℝ) : ℂ) * T p := by
    intro k
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
        rw [fderiv_of_notMem_tsupport ℝ (fun h => hp (ts k h))]; simp),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hp (ts k h))]; simp)]
    exact hW (φk k) (sm k) (cs k) (fun p hp => Bpos p (ts k hp))
  have l1 : Tendsto (fun k => ∫ p in B, ((fderiv ℝ (φk k) p (1, 0) : ℝ) : ℂ) * F p) atTop
      (𝓝 (∫ p in B, ((g p : ℝ) : ℂ) * F p)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun p => 3 * Ag * ‖F p‖) ?_ ?_
      (iF.norm.const_mul _) ?_
    · refine Eventually.of_forall fun k => ?_
      have hcont : Continuous (fun p : ℝ × ℝ => fderiv ℝ (φk k) p (1, 0)) :=
        ((sm k).continuous_fderiv (by simp)).clm_apply continuous_const
      exact (Complex.continuous_ofReal.comp hcont).aestronglyMeasurable.mul iF.aestronglyMeasurable
    · refine Eventually.of_forall fun k => Eventually.of_forall fun p => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, dk]
      exact mul_le_mul_of_nonneg_right (conv_bound (ρ k) gc hAg p) (norm_nonneg _)
    · refine Eventually.of_forall fun p => ?_
      simp only [dk]
      exact ((Complex.continuous_ofReal.tendsto _).comp
        (ContDiffBump.convolution_tendsto_right_of_continuous ρt gc p)).mul_const _
  have l2 : Tendsto (fun k => ∫ p in B, ((φk k p : ℝ) : ℂ) * T p) atTop (𝓝 (∫ p in B, ((φ p : ℝ) : ℂ) * T p)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun p => 3 * Aφ * ‖T p‖) ?_ ?_
      (iT.norm.const_mul _) ?_
    · exact Eventually.of_forall fun k =>
        (Complex.continuous_ofReal.comp (sm k).continuous).aestronglyMeasurable.mul iT.aestronglyMeasurable
    · refine Eventually.of_forall fun k => Eventually.of_forall fun p => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (conv_bound (ρ k) hφ.continuous hAφ p) (norm_nonneg _)
    · refine Eventually.of_forall fun p => ?_
      exact ((Complex.continuous_ofReal.tendsto _).comp
        (ContDiffBump.convolution_tendsto_right_of_continuous ρt hφ.continuous p)).mul_const _
  have lim := tendsto_nhds_unique l1 (l2.neg.congr' (Eventually.of_forall fun k => (Wk k).symm))
  have e1 : ∫ p in B, ((g p : ℝ) : ℂ) * F p = ∫ p, ((fderiv ℝ φ p (1, 0) : ℝ) : ℂ) * F p :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by rw [gB p hp]; simp)
  have e2 : ∫ p in B, ((φ p : ℝ) : ℂ) * T p = ∫ p, ((φ p : ℝ) : ℂ) * T p :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by rw [φB p hp]; simp)
  rw [← e1, ← e2]
  exact lim


open LowEntry.Internal in
theorem third_meas (K : CellBox) (hK : IsCellBox K) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (a b : Fin 3) :
    AEStronglyMeasurable (modeThird m n H a b 0) (volume.restrict K.rect) := by
  have hc : Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) => gradKernel m n a b q.1 (q.2 (radialUnit q.1))) :=
    (gradKernel_cont m n a b).comp (continuous_fst.prodMk (continuous_snd.clm_apply (radialUnit_cont.comp continuous_fst)))
  have hF := ModeGradSquare.Internal.meas_gen hs.measurable_second (fun θ M => gradKernel m n a b θ (M (radialUnit θ))) hc
  have e : modeThird m n H a b 0 = fun p => (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in Set.Ioo (-Real.pi) Real.pi, gradKernel m n a b θ (H (cylPoint p.1 θ p.2) (radialUnit θ)) :=
    funext fun p => third_eq m n H a b p
  rw [e]
  exact (hF.mono_measure (ModeGradSquare.Internal.hle K hK)).const_mul _

theorem lw_diff (K : CellBox) : Differentiable ℝ K.lineWeight := fun r => (lw_hasDeriv K r).differentiableAt

theorem split_deriv (K : CellBox) (ψ : ℝ × ℝ → ℂ) (hψ : ContDiff ℝ 1 ψ) (p : ℝ × ℝ) :
    CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p =
      ((deriv (fun r => K.lineWeight r * (ψ (r, p.2)).re) p.1 : ℝ) : ℂ) +
        Complex.I * ((deriv (fun r => K.lineWeight r * (ψ (r, p.2)).im) p.1 : ℝ) : ℂ) := by
  have hd : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have hl : DifferentiableAt ℝ (fun r : ℝ => ψ (r, p.2)) p.1 :=
    (hd _).comp p.1 ((differentiableAt_id).prodMk (differentiableAt_const _))
  have hre : DifferentiableAt ℝ (fun r => K.lineWeight r * (ψ (r, p.2)).re) p.1 :=
    (lw_diff K p.1).mul (Complex.reCLM.differentiableAt.comp p.1 hl)
  have him : DifferentiableAt ℝ (fun r => K.lineWeight r * (ψ (r, p.2)).im) p.1 :=
    (lw_diff K p.1).mul (Complex.imCLM.differentiableAt.comp p.1 hl)
  have e : (fun r : ℝ => (K.lineWeight r : ℂ) * ψ (r, p.2)) = fun r =>
      ((K.lineWeight r * (ψ (r, p.2)).re : ℝ) : ℂ) + Complex.I * ((K.lineWeight r * (ψ (r, p.2)).im : ℝ) : ℂ) := by
    funext r
    apply Complex.ext <;> simp
  show deriv (fun r : ℝ => (K.lineWeight r : ℂ) * ψ (r, p.2)) p.1 = _
  rw [e]
  exact ((hre.hasDerivAt.ofReal_comp).add ((him.hasDerivAt.ofReal_comp).const_mul Complex.I)).deriv

theorem real_parts (K : CellBox) (hK : IsCellBox K) {m : ℕ} {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) (n : ℤ) (a b : Fin 3) (χ : ℝ × ℝ → ℝ) (hχ : ContDiff ℝ 1 χ)
    (e1 : ∀ z, χ (K.r₁, z) = 0) (e2 : ∀ z, χ (K.r₂, z) = 0) :
    IntegrableOn (fun p => gradMode m n G a b p * ((deriv (fun r => K.lineWeight r * χ (r, p.2)) p.1 : ℝ) : ℂ)) K.rect ∧
    ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * modeThird m n H a b 0 p * (χ p : ℂ)
      = -∫ p in K.rect, gradMode m n G a b p * ((deriv (fun r => K.lineWeight r * χ (r, p.2)) p.1 : ℝ) : ℂ) :=
  extend_c1 K hK (gradMode m n G a b) (modeThird m n H a b 0) (modeGradSquare K hK m v G H hs n a b).1
    (third_meas K hK hs n a b) (grad_int K hK hs n a b) (third_int K hK hs n a b)
    (fun φ hφ hcφ hsφ => c1_of_smooth K hK (gradMode m n G a b) (modeThird m n H a b 0)
      (fun K' hK' => grad_int K' hK' hs n a b) (fun K' hK' => third_int K' hK' hs n a b) (weak_radial hs n a b)
      φ hφ hcφ hsφ) χ hχ e1 e2

theorem ab_parts (K : CellBox) (hK : IsCellBox K) {m : ℕ} {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) (n : ℤ) (a b : Fin 3) (ψ : ℝ × ℝ → ℂ) (hψ : ContDiff ℝ 1 ψ)
    (h1 : ∀ z, ψ (K.r₁, z) = 0) (h2 : ∀ z, ψ (K.r₂, z) = 0) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * modeThird m n H a b 0 p * ψ p) K.rect ∧
    IntegrableOn (fun p => gradMode m n G a b p *
      CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p) K.rect ∧
    ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * modeThird m n H a b 0 p * ψ p
      = -∫ p in K.rect, gradMode m n G a b p * CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p := by
  have hT := third_int K hK hs n a b
  have hcpt : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hre : ContDiff ℝ 1 (fun p => (ψ p).re) := Complex.reCLM.contDiff.comp hψ
  have him : ContDiff ℝ 1 (fun p => (ψ p).im) := Complex.imCLM.contDiff.comp hψ
  obtain ⟨iR, eR⟩ := real_parts K hK hs n a b (fun p => (ψ p).re) hre (fun z => by simp [h1]) (fun z => by simp [h2])
  obtain ⟨iI, eI⟩ := real_parts K hK hs n a b (fun p => (ψ p).im) him (fun z => by simp [h1]) (fun z => by simp [h2])
  have cR : ContinuousOn (fun p => (((ψ p).re : ℝ) : ℂ)) K.rect :=
    (Complex.continuous_ofReal.comp hre.continuous).continuousOn
  have cI : ContinuousOn (fun p => (((ψ p).im : ℝ) : ℂ)) K.rect :=
    (Complex.continuous_ofReal.comp him.continuous).continuousOn
  have jR := hT.mul_continuousOn cR hcpt
  have jI := hT.mul_continuousOn cI hcpt
  have eL : (fun p => (K.lineWeight p.1 : ℂ) * modeThird m n H a b 0 p * ψ p) = fun p =>
      (K.lineWeight p.1 : ℂ) * modeThird m n H a b 0 p * (((ψ p).re : ℝ) : ℂ) +
        Complex.I * ((K.lineWeight p.1 : ℂ) * modeThird m n H a b 0 p * (((ψ p).im : ℝ) : ℂ)) := by
    funext p
    conv_lhs => rw [← Complex.re_add_im (ψ p)]
    ring
  have eD : (fun p => gradMode m n G a b p * CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p) =
      fun p => gradMode m n G a b p * ((deriv (fun r => K.lineWeight r * (ψ (r, p.2)).re) p.1 : ℝ) : ℂ) +
        Complex.I * (gradMode m n G a b p * ((deriv (fun r => K.lineWeight r * (ψ (r, p.2)).im) p.1 : ℝ) : ℂ)) := by
    funext p
    rw [split_deriv K ψ hψ p]
    ring
  refine ⟨hT.mul_continuousOn hψ.continuous.continuousOn hcpt, ?_, ?_⟩
  · rw [eD]
    exact iR.add (iI.const_mul _)
  · rw [eL, eD, integral_add jR (jI.const_mul _), integral_add iR (iI.const_mul _), integral_const_mul,
      integral_const_mul, eR, eI]
    ring

end Breakdown.CellCert.CellAnalysis.ModeRadialPartsA.Internal

namespace Breakdown.CellCert.CellAnalysis

open ModeRadialPartsA.Internal in
theorem modeRadialParts : ModeRadialPartsStatement := by
  intro K hK m v G H hs n κ ψ hψ h1 h2
  have P := fun a b => ab_parts K hK hs n a b ψ hψ h1 h2
  have eL : (fun p => (K.lineWeight p.1 : ℂ) * comboThird κ m n H 0 p * ψ p) = fun p =>
      ∑ a : Fin 3, ∑ b : Fin 3, κ a b * ((K.lineWeight p.1 : ℂ) * modeThird m n H a b 0 p * ψ p) := by
    funext p
    simp only [comboThird, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have eR : (fun p => comboGrad κ m n G p * CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p) =
      fun p => ∑ a : Fin 3, ∑ b : Fin 3, κ a b *
        (gradMode m n G a b p * CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p) := by
    funext p
    simp only [comboGrad, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [eL, eR, integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => (P a b).1.const_mul (κ a b)),
    integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => (P a b).2.1.const_mul (κ a b)),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ (fun b _ => (P a b).1.const_mul (κ a b)),
    integral_finsetSum _ (fun b _ => (P a b).2.1.const_mul (κ a b)), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, integral_const_mul, (P a b).2.2, mul_neg]

end Breakdown.CellCert.CellAnalysis
