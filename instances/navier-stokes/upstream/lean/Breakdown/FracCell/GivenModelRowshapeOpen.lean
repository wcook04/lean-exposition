import Breakdown.FracCell.GivenModelDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenModel

open SteadyCert CellAnalysis CellFormula

private theorem sol_frameVec_apply (θ : ℝ) (u : Space) (i : Fin 3) :
    frameVec θ u i = inner ℝ u (frameUnit θ i) := by
  fin_cases i <;> rfl

private theorem sol_frameVec_cart (θ : ℝ) (w : Fin 3 → ℝ) (i : Fin 3) : frameVec θ (cartOfFrame θ w) i = w i := by
  have hs := Real.sin_sq_add_cos_sq θ
  fin_cases i <;>
    simp [frameVec, cartOfFrame, Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit,
      PiLp.inner_apply] <;>
    first | linear_combination (w 0) * hs | linear_combination (w 1) * hs

private theorem sol_cart_frameVec (θ : ℝ) (u : Space) : cartOfFrame θ (fun i => frameVec θ u i) = u := by
  have hs := Real.sin_sq_add_cos_sq θ
  ext j
  fin_cases j <;>
    simp [frameVec, cartOfFrame, Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit,
      PiLp.inner_apply] <;>
    first | linear_combination (u 0) * hs | linear_combination (u 1) * hs

private theorem sol_frameVec_sum {N : ℕ} (θ : ℝ) (μ : Fin N → ℝ) (u : Fin N → Space) (i : Fin 3) :
    frameVec θ (∑ b, μ b • u b) i = ∑ b, μ b * frameVec θ (u b) i := by
  simp only [sol_frameVec_apply, sum_inner, real_inner_smul_left]

private theorem sol_cyl0 (r θ z : ℝ) : cylPoint r θ z 0 = r * Real.cos θ := by simp [cylPoint]

private theorem sol_cyl1 (r θ z : ℝ) : cylPoint r θ z 1 = r * Real.sin θ := by simp [cylPoint]

private theorem sol_cyl2 (r θ z : ℝ) : cylPoint r θ z 2 = z := by simp [cylPoint]

private theorem sol_cyl_radius {r : ℝ} (hr : 0 ≤ r) (θ z : ℝ) : cylRadius (cylPoint r θ z) = r := by
  unfold cylRadius
  rw [sol_cyl0, sol_cyl1]
  have h : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    linear_combination r ^ 2 * Real.sin_sq_add_cos_sq θ
  rw [h, Real.sqrt_sq hr]

private theorem sol_cyl_angle {r : ℝ} (hr : 0 < r) (θ z : ℝ) :
    ∃ j : ℤ, cylAngle (cylPoint r θ z) = θ - j * (2 * Real.pi) := by
  have h : ((cylPoint r θ z 0 : ℝ) : ℂ) + ((cylPoint r θ z 1 : ℝ) : ℂ) * Complex.I =
      (r : ℂ) * (Complex.cos θ + Complex.sin θ * Complex.I) := by
    rw [sol_cyl0, sol_cyl1]
    push_cast
    ring
  unfold cylAngle
  rw [h, Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod hr]
  exact ⟨toIocDiv Real.two_pi_pos (-Real.pi) θ, by rw [← self_sub_toIocDiv_zsmul, zsmul_eq_mul]⟩

private theorem sol_eval_axis {d : ℕ} (P : CellPoly d) (hP : ∀ l, P 0 l = 0) (z : ℝ) : evalPoly P 0 z = 0 := by
  unfold evalPoly
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun l _ => ?_
  by_cases hj : (j : ℕ) = 0
  · have : j = 0 := Fin.ext hj
    subst this
    simp [hP]
  · simp [zero_pow hj]

private theorem sol_exp_period (x : ℝ) (n : ℤ) :
    Complex.exp (((x - n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = Complex.exp ((x : ℂ) * Complex.I) := by
  rw [show (((x - n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = (x : ℂ) * Complex.I - n * (2 * Real.pi * Complex.I) by
    push_cast; ring, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

private theorem sol_angle_trig {y : Space} (hr : 0 < cylRadius y) :
    Real.cos (cylAngle y) = y 0 / cylRadius y ∧ Real.sin (cylAngle y) = y 1 / cylRadius y := by
  have hn : ‖((y 0 : ℂ) + (y 1 : ℂ) * Complex.I)‖ = cylRadius y := by
    rw [Complex.norm_add_mul_I]
    rfl
  have hx : ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    rw [← hn] at hr
    exact lt_irrefl _ hr
  unfold cylAngle
  rw [Complex.cos_arg hx, Complex.sin_arg, hn]
  simp

private theorem sol_term_frame {M : CellMesh} {N : ℕ} (R : RowData M N) (m : ℕ) (b : Fin N)
    (hK : IsCellBox (M.box (R.cell b))) (r z : ℝ)
    (hr : r ∈ Set.Icc (M.box (R.cell b)).r₁ (M.box (R.cell b)).r₂)
    (hz : |z| ∈ Set.Icc (M.box (R.cell b)).z₁ (M.box (R.cell b)).z₂)
    (hax : r = 0 → R.harmonic b = 0 ∧ ∀ l, R.profile b 0 0 l = 0 ∧ R.profile b 1 0 l = 0)
    (θ : ℝ) (i : Fin 3) :
    frameVec θ (R.testField m b (cylPoint r θ z)) i =
      (if z < 0 ∧ i = 2 then -1 else 1) *
        (evalPoly (R.profile b i) r |z| * Complex.exp ((azimuth m (R.harmonic b : ℤ) * θ : ℝ) * Complex.I)).re := by
  obtain ⟨hr1, hr2⟩ := hr
  obtain ⟨hz1, hz2⟩ := hz
  have hr0 : 0 ≤ r := le_trans hK.r_order.1 hr1
  have hR : cylRadius (cylPoint r θ z) = r := sol_cyl_radius hr0 θ z
  have hH : cylHeight (cylPoint r θ z) = z := sol_cyl2 _ _ _
  have hmem : cylPoint r θ z ∈ (M.box (R.cell b)).solid := by
    show _ ∧ _
    rw [hR, hH]
    exact ⟨hr1, hr2, hz1, hz2⟩
  unfold RowData.testField
  rw [Set.indicator_of_mem hmem]
  have hvs : ∀ c, vectorSign (cylPoint r θ z) c = if z < 0 ∧ c = 2 then -1 else 1 := by
    intro c
    simp [vectorSign, hH]
  simp only [hR, hH, hvs]
  rcases eq_or_lt_of_le hr0 with h0 | hpos
  · obtain ⟨hβ, hP⟩ := hax h0.symm
    have hang : cylAngle (cylPoint r θ z) = 0 := by
      simp [cylAngle, sol_cyl0, sol_cyl1, ← h0]
    have hE0 : evalPoly (R.profile b 0) r |z| = 0 := by
      rw [← h0]; exact sol_eval_axis _ (fun l => (hP l).1) _
    have hE1 : evalPoly (R.profile b 1) r |z| = 0 := by
      rw [← h0]; exact sol_eval_axis _ (fun l => (hP l).2) _
    rw [hang, hβ]
    by_cases hz0 : z < 0 <;> fin_cases i <;>
      simp [frameVec, cartOfFrame, Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit,
        PiLp.inner_apply, hE0, hE1, azimuth, hz0]
  · obtain ⟨j, hj⟩ := sol_cyl_angle hpos θ z
    rw [hj]
    have hf : frameUnit (θ - j * (2 * Real.pi)) = frameUnit θ := by
      simp [frameUnit, radialUnit, angularUnit, Real.cos_sub_int_mul_two_pi, Real.sin_sub_int_mul_two_pi]
    have hc : ∀ w, cartOfFrame (θ - j * (2 * Real.pi)) w = cartOfFrame θ w := fun w => by
      unfold cartOfFrame; rw [hf]
    rw [hc]
    rw [show azimuth m (R.harmonic b : ℤ) * (θ - j * (2 * Real.pi)) =
        azimuth m (R.harmonic b : ℤ) * θ - ((R.harmonic b * m * j : ℤ) : ℝ) * (2 * Real.pi) by
      unfold azimuth; push_cast; ring, sol_exp_period]
    exact sol_frameVec_cart θ _ i

private def solA {M : CellMesh} {N : ℕ} (R : RowData M N) (a : Fin N) (i : Fin 3) (r z : ℝ) : ℂ :=
  ∑ b, (R.mix a b : ℂ) * evalPoly (R.profile b i) r z

private def solE (m : ℕ) {M : CellMesh} {N : ℕ} (R : RowData M N) (a : Fin N) (θ : ℝ) : ℂ :=
  Complex.exp ((azimuth m (R.harmonic a : ℤ) * θ : ℝ) * Complex.I)

private theorem sol_row_frame {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (R : RowData M N)
    (hM : IsCellMesh M) (hR : IsRowData R c.order c.rowMax) (hI : IsRowInstance c M R)
    (hS : ∀ a b, R.mix a b ≠ 0 → R.cell a = R.cell b ∧ R.harmonic a = R.harmonic b) (a : Fin N) (r z : ℝ)
    (hr : r ∈ Set.Icc (M.box (R.cell a)).r₁ (M.box (R.cell a)).r₂)
    (hz : |z| ∈ Set.Icc (M.box (R.cell a)).z₁ (M.box (R.cell a)).z₂) (θ : ℝ) (i : Fin 3) :
    frameVec θ (c.row a (cylPoint r θ z)) i =
      (if z < 0 ∧ i = 2 then -1 else 1) * (solA R a i r |z| * solE c.order R a θ).re := by
  rw [hI.row_eq]
  unfold RowData.rowField solA solE
  rw [sol_frameVec_sum, Finset.sum_mul, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : R.mix a b = 0
  · simp [hab]
  · obtain ⟨hc, hh⟩ := hS a b hab
    have hKb := hM.boxes (R.cell b)
    rw [hc] at hr hz
    have hax : r = 0 → R.harmonic b = 0 ∧ ∀ l, R.profile b 0 0 l = 0 ∧ R.profile b 1 0 l = 0 := by
      intro h0
      have hr1 : (M.box (R.cell b)).r₁ = 0 := le_antisymm (h0 ▸ hr.1) hKb.r_order.1
      exact ⟨hR.axis_zeroMode b hr1, hR.axis_regular b hr1⟩
    rw [sol_term_frame R c.order b hKb r z hr hz hax θ i, hh, mul_assoc, Complex.re_ofReal_mul]
    ring

private theorem sol_trace_frame (D : Space →L[ℝ] Space) (θ : ℝ) :
    ∑ i : Fin 3, inner ℝ (D (unitVector i)) (unitVector i) =
      ∑ j : Fin 3, inner ℝ (D (frameUnit θ j)) (frameUnit θ j) := by
  have h0 : frameUnit θ 0 = Real.cos θ • unitVector 0 + Real.sin θ • unitVector 1 := by
    ext i; fin_cases i <;> simp [frameUnit, radialUnit, unitVector]
  have h1 : frameUnit θ 1 = (-Real.sin θ) • unitVector 0 + Real.cos θ • unitVector 1 := by
    ext i; fin_cases i <;> simp [frameUnit, angularUnit, unitVector]
  have h2 : frameUnit θ 2 = unitVector 2 := by
    simp [frameUnit, axialUnit, unitVector]
  rw [Fin.sum_univ_three, Fin.sum_univ_three, h0, h1, h2]
  simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  have hs := Real.sin_sq_add_cos_sq θ
  linear_combination (-(inner ℝ (D (unitVector 0)) (unitVector 0) + inner ℝ (D (unitVector 1)) (unitVector 1))) * hs

private theorem sol_one_sided {g F : ℝ → ℝ} {g' F' : ℝ} (hg : HasDerivAt g g' 0) (hF : HasDerivAt F F' 0)
    {ε : ℝ} (hε : 0 < ε)
    (h : (∀ s ∈ Set.Icc 0 ε, g s = F s) ∨ (∀ s ∈ Set.Icc (-ε) 0, g s = F s)) : g' = F' := by
  rcases h with h | h
  · have hev : g =ᶠ[nhdsWithin 0 (Set.Ici 0)] F :=
      Filter.mem_of_superset (Icc_mem_nhdsGE hε) fun s hs => h s hs
    exact (uniqueDiffWithinAt_Ici 0).eq_deriv _ hg.hasDerivWithinAt
      (hF.hasDerivWithinAt.congr_of_eventuallyEq hev (h 0 ⟨le_rfl, hε.le⟩))
  · have hev : g =ᶠ[nhdsWithin 0 (Set.Iic 0)] F :=
      Filter.mem_of_superset (Icc_mem_nhdsLE (by linarith)) fun s hs => h s hs
    exact (uniqueDiffWithinAt_Iic 0).eq_deriv _ hg.hasDerivWithinAt
      (hF.hasDerivWithinAt.congr_of_eventuallyEq hev (h 0 ⟨by linarith, le_rfl⟩))

private theorem sol_dir {f : Space → Space} {D : Space →L[ℝ] Space} {y : Space} (hf : HasFDerivAt f D y)
    (γ : ℝ → Space) (v : Space) (hγ : HasDerivAt γ v 0) (h0 : γ 0 = y) (w : Space) :
    HasDerivAt (fun s => inner ℝ (f (γ s)) w) (inner ℝ (D v) w) 0 := by
  have h := hf.comp_hasDerivAt_of_eq (0 : ℝ) hγ h0.symm
  have h3 := (innerSL ℝ w).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  refine (h3.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  · rw [innerSL_apply_apply, real_inner_comm]
  · show inner ℝ (f (γ s)) w = innerSL ℝ w ((f ∘ γ) s)
    rw [innerSL_apply_apply, real_inner_comm]
    rfl

private theorem sol_deriv_eval_r {d : ℕ} (P : CellPoly d) (r z : ℝ) :
    HasDerivAt (fun s : ℝ => evalPoly P (r + s) z) (polyDr P r z) 0 := by
  unfold evalPoly polyDr
  refine HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun l _ => ?_
  have h1 := (hasDerivAt_pow (j : ℕ) (r + 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add r)
  rw [add_zero, mul_one] at h1
  have h2 := ((h1.ofReal_comp).const_mul (P j l)).mul_const (((z : ℂ)) ^ (l : ℕ))
  refine (h2.congr_deriv (by push_cast; ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp

private theorem sol_deriv_eval_z {d : ℕ} (P : CellPoly d) (r z : ℝ) :
    HasDerivAt (fun s : ℝ => evalPoly P r (z + s)) (polyDz P r z) 0 := by
  unfold evalPoly polyDz
  refine HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun l _ => ?_
  have h1 := (hasDerivAt_pow (l : ℕ) (z + 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add z)
  rw [add_zero, mul_one] at h1
  have h2 := (h1.ofReal_comp).const_mul (P j l * ((r : ℂ)) ^ (j : ℕ))
  refine (h2.congr_deriv (by push_cast; ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp

private theorem sol_deriv_eval_zneg {d : ℕ} (P : CellPoly d) (r w : ℝ) :
    HasDerivAt (fun s : ℝ => evalPoly P r (w - s)) (-polyDz P r w) 0 := by
  unfold evalPoly polyDz
  rw [← Finset.sum_neg_distrib]
  refine HasDerivAt.fun_sum fun j _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine HasDerivAt.fun_sum fun l _ => ?_
  have h1 := (hasDerivAt_pow (l : ℕ) (w - 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_sub w)
  rw [sub_zero] at h1
  have h2 := (h1.ofReal_comp).const_mul (P j l * ((r : ℂ)) ^ (j : ℕ))
  refine (h2.congr_deriv (by push_cast; ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp

private theorem sol_curve_r (r θ z s : ℝ) : cylPoint (r + s) θ z = cylPoint r θ z + s • radialUnit θ := by
  ext i
  fin_cases i <;> simp [cylPoint, radialUnit] <;> ring

private theorem sol_curve_z (r θ z s : ℝ) : cylPoint r θ (z + s) = cylPoint r θ z + s • axialUnit := by
  ext i
  fin_cases i <;> simp [cylPoint, axialUnit]

private theorem sol_line_deriv (y v : Space) : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y

private theorem sol_cos_deriv (θ : ℝ) : HasDerivAt (fun s : ℝ => Real.cos (θ + s)) (-Real.sin θ) 0 := by
  have h := (Real.hasDerivAt_cos (θ + 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add θ)
  rw [add_zero, mul_one] at h
  exact h

private theorem sol_sin_deriv (θ : ℝ) : HasDerivAt (fun s : ℝ => Real.sin (θ + s)) (Real.cos θ) 0 := by
  have h := (Real.hasDerivAt_sin (θ + 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add θ)
  rw [add_zero, mul_one] at h
  exact h

private theorem sol_curve_t (r θ z : ℝ) : HasDerivAt (fun s => cylPoint r (θ + s) z) (r • angularUnit θ) 0 := by
  have e : (fun s => cylPoint r (θ + s) z) = fun s =>
      (r * Real.cos (θ + s)) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
      (r * Real.sin (θ + s)) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) + EuclideanSpace.single (2 : Fin 3) z := by
    funext s
    ext i
    fin_cases i <;> simp [cylPoint]
  have e2 : r • angularUnit θ = (r * -Real.sin θ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
      (r * Real.cos θ) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) + 0 := by
    ext i
    fin_cases i <;> simp [angularUnit]
  rw [e, e2]
  exact ((((sol_cos_deriv θ).const_mul r).smul_const _).add (((sol_sin_deriv θ).const_mul r).smul_const _)).add
    (hasDerivAt_const _ _)

private theorem sol_re_deriv {f : ℝ → ℂ} {f' : ℂ} (hf : HasDerivAt f f' 0) :
    HasDerivAt (fun s => (f s).re) f'.re 0 := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf

private theorem sol_exp_deriv (k θ : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp ((k * (θ + s) : ℝ) * Complex.I))
      (Complex.exp ((k * θ : ℝ) * Complex.I) * ((k : ℂ) * Complex.I)) 0 := by
  have h1 := (((hasDerivAt_id (0 : ℝ)).const_add θ).const_mul k).ofReal_comp.mul_const Complex.I
  have h2 := h1.cexp
  refine (h2.congr_deriv (by simp)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp

private theorem sol_inner_ang (φ θ : ℝ) (w : Fin 3 → ℝ) :
    inner ℝ (cartOfFrame φ w) (angularUnit θ) =
      w 0 * (Real.sin φ * Real.cos θ - Real.cos φ * Real.sin θ) +
        w 1 * (Real.sin φ * Real.sin θ + Real.cos φ * Real.cos θ) := by
  simp [cartOfFrame, Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit, PiLp.inner_apply]
  ring

private theorem sol_radial {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (R : RowData M N)
    (hM : IsCellMesh M) (hR : IsRowData R c.order c.rowMax) (hI : IsRowInstance c M R)
    (hS : ∀ a b, R.mix a b ≠ 0 → R.cell a = R.cell b ∧ R.harmonic a = R.harmonic b) (a : Fin N) (r z θ : ℝ)
    (hr : r ∈ Set.Icc (M.box (R.cell a)).r₁ (M.box (R.cell a)).r₂)
    (hz : |z| ∈ Set.Icc (M.box (R.cell a)).z₁ (M.box (R.cell a)).z₂)
    {D : Space →L[ℝ] Space} (hD : HasFDerivAt (c.row a) D (cylPoint r θ z)) :
    inner ℝ (D (radialUnit θ)) (radialUnit θ) =
      ((∑ b, (R.mix a b : ℂ) * polyDr (R.profile b 0) r |z|) * solE c.order R a θ).re := by
  have hK := hM.boxes (R.cell a)
  have hg := sol_dir hD (fun s => cylPoint r θ z + s • radialUnit θ) (radialUnit θ) (sol_line_deriv _ _)
    (by simp) (radialUnit θ)
  have hF : HasDerivAt (fun s => (solA R a 0 (r + s) |z| * solE c.order R a θ).re)
      ((∑ b, (R.mix a b : ℂ) * polyDr (R.profile b 0) r |z|) * solE c.order R a θ).re 0 := by
    refine sol_re_deriv (HasDerivAt.mul_const ?_ _)
    unfold solA
    exact HasDerivAt.fun_sum fun b _ => (sol_deriv_eval_r _ _ _).const_mul _
  have key : ∀ s, r + s ∈ Set.Icc (M.box (R.cell a)).r₁ (M.box (R.cell a)).r₂ →
      inner ℝ (c.row a (cylPoint r θ z + s • radialUnit θ)) (radialUnit θ) =
        (solA R a 0 (r + s) |z| * solE c.order R a θ).re := by
    intro s hs
    rw [← sol_curve_r, show radialUnit θ = frameUnit θ 0 from rfl, ← sol_frameVec_apply,
      sol_row_frame c M R hM hR hI hS a (r + s) z hs hz θ 0]
    simp
  rcases lt_or_eq_of_le hr.2 with hlt | heq
  · exact sol_one_sided hg hF (ε := (M.box (R.cell a)).r₂ - r) (by linarith)
      (Or.inl fun s hs => key s ⟨by linarith [hs.1, hr.1], by linarith [hs.2]⟩)
  · exact sol_one_sided hg hF (ε := (M.box (R.cell a)).r₂ - (M.box (R.cell a)).r₁) (by linarith [hK.r_order.2])
      (Or.inr fun s hs => key s ⟨by linarith [hs.1], by linarith [hs.2]⟩)

private theorem sol_axial {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (R : RowData M N)
    (hM : IsCellMesh M) (hR : IsRowData R c.order c.rowMax) (hI : IsRowInstance c M R)
    (hS : ∀ a b, R.mix a b ≠ 0 → R.cell a = R.cell b ∧ R.harmonic a = R.harmonic b) (a : Fin N) (r z θ : ℝ)
    (hr : r ∈ Set.Icc (M.box (R.cell a)).r₁ (M.box (R.cell a)).r₂)
    (hz : |z| ∈ Set.Icc (M.box (R.cell a)).z₁ (M.box (R.cell a)).z₂)
    {D : Space →L[ℝ] Space} (hD : HasFDerivAt (c.row a) D (cylPoint r θ z)) :
    inner ℝ (D axialUnit) axialUnit =
      ((∑ b, (R.mix a b : ℂ) * polyDz (R.profile b 2) r |z|) * solE c.order R a θ).re := by
  have hK := hM.boxes (R.cell a)
  have hg := sol_dir hD (fun s => cylPoint r θ z + s • axialUnit) axialUnit (sol_line_deriv _ _)
    (by simp) axialUnit
  have key : ∀ s, |z + s| ∈ Set.Icc (M.box (R.cell a)).z₁ (M.box (R.cell a)).z₂ →
      inner ℝ (c.row a (cylPoint r θ z + s • axialUnit)) axialUnit =
        (if z + s < 0 then -1 else 1) * (solA R a 2 r |z + s| * solE c.order R a θ).re := by
    intro s hs
    rw [← sol_curve_z, show axialUnit = frameUnit θ 2 from rfl, ← sol_frameVec_apply,
      sol_row_frame c M R hM hR hI hS a r (z + s) hr hs θ 2]
    simp
  have hz1 := hz.1
  have hz2 := hz.2
  have h0 := hK.z_order.1
  have h12 := hK.z_order.2
  rcases le_or_gt 0 z with hzp | hzn
  · rw [abs_of_nonneg hzp] at hz1 hz2 ⊢
    have hF : HasDerivAt (fun s => (solA R a 2 r (z + s) * solE c.order R a θ).re)
        ((∑ b, (R.mix a b : ℂ) * polyDz (R.profile b 2) r z) * solE c.order R a θ).re 0 := by
      refine sol_re_deriv (HasDerivAt.mul_const ?_ _)
      unfold solA
      exact HasDerivAt.fun_sum fun b _ => (sol_deriv_eval_z _ _ _).const_mul _
    have key2 : ∀ s, 0 ≤ z + s → z + s ∈ Set.Icc (M.box (R.cell a)).z₁ (M.box (R.cell a)).z₂ →
        inner ℝ (c.row a (cylPoint r θ z + s • axialUnit)) axialUnit =
          (solA R a 2 r (z + s) * solE c.order R a θ).re := by
      intro s hs0 hs
      rw [key s (by rw [abs_of_nonneg hs0]; exact hs), if_neg (not_lt.2 hs0), abs_of_nonneg hs0, one_mul]
    rcases lt_or_eq_of_le hz2 with hlt | heq
    · exact sol_one_sided hg hF (ε := (M.box (R.cell a)).z₂ - z) (by linarith)
        (Or.inl fun s hs => key2 s (by linarith [hs.1]) ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    · exact sol_one_sided hg hF (ε := (M.box (R.cell a)).z₂ - (M.box (R.cell a)).z₁) (by linarith)
        (Or.inr fun s hs => key2 s (by linarith [hs.1]) ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  · rw [abs_of_neg hzn] at hz1 hz2 ⊢
    have hA : HasDerivAt (fun s => solA R a 2 r (-z - s))
        (∑ b, (R.mix a b : ℂ) * -polyDz (R.profile b 2) r (-z)) 0 := by
      unfold solA
      exact HasDerivAt.fun_sum fun b _ => (sol_deriv_eval_zneg _ _ _).const_mul _
    have hF := (sol_re_deriv (hA.mul_const (solE c.order R a θ))).neg
    have key2 : ∀ s, z + s < 0 → -z - s ∈ Set.Icc (M.box (R.cell a)).z₁ (M.box (R.cell a)).z₂ →
        inner ℝ (c.row a (cylPoint r θ z + s • axialUnit)) axialUnit =
          -(solA R a 2 r (-z - s) * solE c.order R a θ).re := by
      intro s hs0 hs
      have habs : |z + s| = -z - s := by rw [abs_of_neg hs0]; ring
      rw [key s (by rw [habs]; exact hs), if_pos hs0, habs]
      ring
    have hres : -((∑ b, (R.mix a b : ℂ) * -polyDz (R.profile b 2) r (-z)) * solE c.order R a θ).re =
        ((∑ b, (R.mix a b : ℂ) * polyDz (R.profile b 2) r (-z)) * solE c.order R a θ).re := by
      simp only [mul_neg, Finset.sum_neg_distrib, neg_mul, Complex.neg_re, neg_neg]
    rw [← hres]
    rcases lt_or_eq_of_le hz2 with hlt | heq
    · exact sol_one_sided hg hF (ε := (M.box (R.cell a)).z₂ + z) (by linarith)
        (Or.inr fun s hs => key2 s (by linarith [hs.2]) ⟨by linarith [hs.2], by linarith [hs.1]⟩)
    · exact sol_one_sided hg hF (ε := ((M.box (R.cell a)).z₂ - (M.box (R.cell a)).z₁) / 2) (by linarith)
        (Or.inl fun s hs => key2 s (by linarith [hs.2]) ⟨by linarith [hs.2], by linarith [hs.1]⟩)

private theorem sol_angular {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (R : RowData M N)
    (hM : IsCellMesh M) (hR : IsRowData R c.order c.rowMax) (hI : IsRowInstance c M R)
    (hS : ∀ a b, R.mix a b ≠ 0 → R.cell a = R.cell b ∧ R.harmonic a = R.harmonic b) (a : Fin N) (r z θ : ℝ)
    (hr : r ∈ Set.Icc (M.box (R.cell a)).r₁ (M.box (R.cell a)).r₂)
    (hz : |z| ∈ Set.Icc (M.box (R.cell a)).z₁ (M.box (R.cell a)).z₂)
    {D : Space →L[ℝ] Space} (hD : HasFDerivAt (c.row a) D (cylPoint r θ z)) :
    r * inner ℝ (D (angularUnit θ)) (angularUnit θ) =
      (solA R a 0 r |z| * solE c.order R a θ).re +
        (solA R a 1 r |z| * ((azimuth c.order (R.harmonic a : ℤ) : ℂ) * Complex.I) * solE c.order R a θ).re := by
  set κ : ℝ := azimuth c.order (R.harmonic a : ℤ) with hκ
  set A0 := solA R a 0 r |z| with hA0
  set A1 := solA R a 1 r |z| with hA1
  have hg := sol_dir hD (fun s => cylPoint r (θ + s) z) (r • angularUnit θ) (sol_curve_t r θ z) (by simp)
    (angularUnit θ)
  have hfun : (fun s => inner ℝ (c.row a (cylPoint r (θ + s) z)) (angularUnit θ)) = fun s =>
      (A0 * Complex.exp ((κ * (θ + s) : ℝ) * Complex.I)).re *
          (Real.sin (θ + s) * Real.cos θ - Real.cos (θ + s) * Real.sin θ) +
        (A1 * Complex.exp ((κ * (θ + s) : ℝ) * Complex.I)).re *
          (Real.sin (θ + s) * Real.sin θ + Real.cos (θ + s) * Real.cos θ) := by
    funext s
    rw [← sol_cart_frameVec (θ + s) (c.row a (cylPoint r (θ + s) z)), sol_inner_ang,
      sol_row_frame c M R hM hR hI hS a r z hr hz (θ + s) 0, sol_row_frame c M R hM hR hI hS a r z hr hz (θ + s) 1]
    simp [solE, hA0, hA1, hκ]
  rw [hfun] at hg
  have hF := ((sol_re_deriv ((sol_exp_deriv κ θ).const_mul A0)).mul
      (((sol_sin_deriv θ).mul_const (Real.cos θ)).sub ((sol_cos_deriv θ).mul_const (Real.sin θ)))).add
    ((sol_re_deriv ((sol_exp_deriv κ θ).const_mul A1)).mul
      (((sol_sin_deriv θ).mul_const (Real.sin θ)).add ((sol_cos_deriv θ).mul_const (Real.cos θ))))
  have hu := hg.unique hF
  rw [map_smul, real_inner_smul_left] at hu
  rw [hu]
  have hs := Real.sin_sq_add_cos_sq θ
  simp only [Pi.sub_apply, Pi.add_apply, add_zero, solE]
  rw [show A1 * (Complex.exp ((κ * θ : ℝ) * Complex.I) * ((κ : ℂ) * Complex.I)) =
      A1 * ((κ : ℂ) * Complex.I) * Complex.exp ((κ * θ : ℝ) * Complex.I) by ring,
    show A0 * (Complex.exp ((κ * θ : ℝ) * Complex.I) * ((κ : ℂ) * Complex.I)) =
      A0 * ((κ : ℂ) * Complex.I) * Complex.exp ((κ * θ : ℝ) * Complex.I) by ring]
  linear_combination ((A0 * Complex.exp ((κ * θ : ℝ) * Complex.I)).re +
    (A1 * ((κ : ℂ) * Complex.I) * Complex.exp ((κ * θ : ℝ) * Complex.I)).re) * hs

private theorem sol_axis_identity {d : ℕ} (Φ : Fin 3 → CellPoly d) (h : IsSolenoidalProfile 0 Φ) (ζ : ℝ) :
    2 * polyDr (Φ 0) 0 ζ + polyDz (Φ 2) 0 ζ = 0 := by
  have hc : Differentiable ℝ (fun s : ℝ => (s : ℂ)) := Complex.ofRealCLM.differentiable
  have hdr : Differentiable ℝ (fun s : ℝ => polyDr (Φ 0) s ζ) := by
    unfold polyDr
    fun_prop
  have hdz : Differentiable ℝ (fun s : ℝ => polyDz (Φ 2) s ζ) := by
    unfold polyDz
    fun_prop
  have hid : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have h1 := hid.mul (hdr 0).hasDerivAt
  have h2 := hid.mul (hdz 0).hasDerivAt
  have h3 : HasDerivAt (fun s : ℝ => evalPoly (Φ 0) s ζ) (polyDr (Φ 0) 0 ζ) 0 := by
    simpa using sol_deriv_eval_r (Φ 0) 0 ζ
  have hsum := (h1.add h3).add h2
  have hzero : (fun s : ℝ => (s : ℂ) * polyDr (Φ 0) s ζ + evalPoly (Φ 0) s ζ + (s : ℂ) * polyDz (Φ 2) s ζ) =
      fun _ => 0 := by
    funext s
    have := h s ζ
    simpa using this
  have := hsum.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => congrFun hzero s))
  simp at this
  linear_combination this

theorem rowSolenoidal_of_mixSame {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (R : RowData M N)
    (hM : IsCellMesh M) (hR : IsRowData R c.order c.rowMax) (hI : IsRowInstance c M R)
    (hS : ∀ a b, R.mix a b ≠ 0 → R.cell a = R.cell b ∧ R.harmonic a = R.harmonic b) :
    ∀ a, ∀ y ∈ (M.box (R.cell a)).solid,
      ∑ i : Fin 3, inner ℝ (fderiv ℝ (c.row a) y (unitVector i)) (unitVector i) = 0 := by
  intro a y hy
  by_cases hd : DifferentiableAt ℝ (c.row a) y
  swap
  · simp [fderiv_zero_of_not_differentiableAt hd]
  have hK := hM.boxes (R.cell a)
  have hDy : HasFDerivAt (c.row a) (fderiv ℝ (c.row a) y) y := hd.hasFDerivAt
  set D := fderiv ℝ (c.row a) y with hDdef
  obtain ⟨hr1, hr2, hz1, hz2⟩ := hy
  have hr : cylRadius y ∈ Set.Icc (M.box (R.cell a)).r₁ (M.box (R.cell a)).r₂ := ⟨hr1, hr2⟩
  have hz : |cylHeight y| ∈ Set.Icc (M.box (R.cell a)).z₁ (M.box (R.cell a)).z₂ := ⟨hz1, hz2⟩
  have hr0 : 0 ≤ cylRadius y := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hr0 with h0 | hpos
  · have hax : (M.box (R.cell a)).r₁ = 0 := le_antisymm (h0 ▸ hr1) hK.r_order.1
    have hβ := hR.axis_zeroMode a hax
    have hsq : cylRadius y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
    rw [← h0] at hsq
    have hy0 : y 0 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have hy1 : y 1 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have hpt : ∀ θ, cylPoint (cylRadius y) θ (cylHeight y) = y := by
      intro θ
      ext i
      fin_cases i <;> simp [cylPoint, ← h0, hy0, hy1, cylHeight]
    have hD : ∀ θ, HasFDerivAt (c.row a) D (cylPoint (cylRadius y) θ (cylHeight y)) := fun θ => by
      rw [hpt θ]; exact hDy
    rw [sol_trace_frame D 0, Fin.sum_univ_three]
    have e1 : frameUnit 0 1 = radialUnit (Real.pi / 2) := by
      ext i; fin_cases i <;> simp [frameUnit, angularUnit, radialUnit]
    have hA := sol_radial c M R hM hR hI hS a _ _ 0 hr hz (hD 0)
    have hB := sol_radial c M R hM hR hI hS a _ _ (Real.pi / 2) hr hz (hD _)
    have hC := sol_axial c M R hM hR hI hS a _ _ 0 hr hz (hD 0)
    show inner ℝ (D (radialUnit 0)) (radialUnit 0) + inner ℝ (D (frameUnit 0 1)) (frameUnit 0 1) +
      inner ℝ (D axialUnit) axialUnit = 0
    rw [e1, hA, hB, hC]
    have hE : ∀ θ, solE c.order R a θ = 1 := by intro θ; simp [solE, hβ, azimuth]
    simp only [hE, mul_one]
    have key : ∑ b, (R.mix a b : ℂ) * (2 * polyDr (R.profile b 0) (cylRadius y) |cylHeight y| +
        polyDz (R.profile b 2) (cylRadius y) |cylHeight y|) = 0 := by
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hab : R.mix a b = 0
      · simp [hab]
      · obtain ⟨_, hh⟩ := hS a b hab
        have hsol := hR.profile_solenoidal b
        rw [← hh, hβ, show azimuth c.order ((0 : ℕ) : ℤ) = 0 by simp [azimuth]] at hsol
        rw [← h0, sol_axis_identity _ hsol, mul_zero]
    rw [show ∑ b, (R.mix a b : ℂ) * (2 * polyDr (R.profile b 0) (cylRadius y) |cylHeight y| +
        polyDz (R.profile b 2) (cylRadius y) |cylHeight y|) =
        2 * ∑ b, (R.mix a b : ℂ) * polyDr (R.profile b 0) (cylRadius y) |cylHeight y| +
          ∑ b, (R.mix a b : ℂ) * polyDz (R.profile b 2) (cylRadius y) |cylHeight y| by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring] at key
    have h2 : ∀ u v : ℂ, u.re + u.re + v.re = (2 * u + v).re := by
      intro u v
      simp
      ring
    rw [h2, key, Complex.zero_re]
  · set θ := cylAngle y with hθ
    obtain ⟨hc, hs⟩ := sol_angle_trig hpos
    have hpt : cylPoint (cylRadius y) θ (cylHeight y) = y := by
      have hne : cylRadius y ≠ 0 := hpos.ne'
      ext i
      fin_cases i <;> simp [cylPoint, hθ, hc, hs, cylHeight] <;> field_simp
    have hD : HasFDerivAt (c.row a) D (cylPoint (cylRadius y) θ (cylHeight y)) := by
      rw [hpt]; exact hDy
    rw [sol_trace_frame D θ, Fin.sum_univ_three]
    have hA := sol_radial c M R hM hR hI hS a _ _ θ hr hz hD
    have hT := sol_angular c M R hM hR hI hS a _ _ θ hr hz hD
    have hC := sol_axial c M R hM hR hI hS a _ _ θ hr hz hD
    show inner ℝ (D (radialUnit θ)) (radialUnit θ) + inner ℝ (D (angularUnit θ)) (angularUnit θ) +
      inner ℝ (D axialUnit) axialUnit = 0
    set κ : ℝ := azimuth c.order (R.harmonic a : ℤ) with hκ
    set ρ := cylRadius y with hρ
    set ζ := |cylHeight y| with hζ
    have key : (ρ : ℂ) * (∑ b, (R.mix a b : ℂ) * polyDr (R.profile b 0) ρ ζ) +
        (solA R a 0 ρ ζ + solA R a 1 ρ ζ * ((κ : ℂ) * Complex.I)) +
        (ρ : ℂ) * (∑ b, (R.mix a b : ℂ) * polyDz (R.profile b 2) ρ ζ) = 0 := by
      have hterm : ∀ b, (R.mix a b : ℂ) * ((ρ : ℂ) * polyDr (R.profile b 0) ρ ζ + evalPoly (R.profile b 0) ρ ζ +
          Complex.I * (κ : ℂ) * evalPoly (R.profile b 1) ρ ζ + (ρ : ℂ) * polyDz (R.profile b 2) ρ ζ) = 0 := by
        intro b
        by_cases hab : R.mix a b = 0
        · simp [hab]
        · obtain ⟨_, hh⟩ := hS a b hab
          have hsol := hR.profile_solenoidal b
          rw [← hh] at hsol
          rw [hsol ρ ζ, mul_zero]
      rw [← Finset.sum_eq_zero (fun b _ => hterm b)]
      unfold solA
      simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    have hre := congrArg (fun w => (w * solE c.order R a θ).re) key
    simp only [add_mul, Complex.add_re, zero_mul, Complex.zero_re, mul_assoc, Complex.re_ofReal_mul] at hre
    simp only [mul_assoc] at hT
    have hsum : ρ * (inner ℝ (D (radialUnit θ)) (radialUnit θ) + inner ℝ (D (angularUnit θ)) (angularUnit θ) +
        inner ℝ (D axialUnit) axialUnit) = 0 := by
      rw [mul_add, mul_add, hT, hA, hC]
      linarith
    exact (mul_eq_zero.1 hsum).resolve_left hpos.ne'

end GivenModel

end CellCert

end Breakdown
