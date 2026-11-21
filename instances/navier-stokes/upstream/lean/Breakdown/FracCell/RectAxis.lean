import Breakdown.FracCell.FieldWitness
import Breakdown.FracCell.FieldWitnessRect

open MeasureTheory Polynomial Set
open scoped Interval Topology

noncomputable section

namespace Breakdown.CellCert.Spectral

open SteadyCert

namespace Internal.RectAxis

open Internal.FieldWitness

def zres (z0 z1 lam : ℝ) (g : ℝ[X]) (z : ℝ) : ℝ :=
  intervalResolvent (lam * (z1 - z0) ^ 2 / 4) (g.comp (C ((z1 - z0) / 2) * X + C ((z0 + z1) / 2)))
    (2 / (z1 - z0) * z - (z0 + z1) / (z1 - z0))

theorem zres_contDiff {z0 z1 lam : ℝ} (hlam : 0 < lam) (hz : z0 < z1) (g : ℝ[X]) :
    ContDiff ℝ 2 (zres z0 z1 lam g) := by
  have hL : 0 < z1 - z0 := sub_pos.2 hz
  have hμ : 0 < lam * (z1 - z0) ^ 2 / 4 := div_pos (mul_pos hlam (pow_pos hL 2)) (by norm_num)
  have h := (intervalIdentity _ (g.comp (C ((z1 - z0) / 2) * X + C ((z0 + z1) / 2))) hμ).1
  exact h.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem zres_ends {z0 z1 lam : ℝ} (hlam : 0 < lam) (hz : z0 < z1) (g : ℝ[X]) :
    zres z0 z1 lam g z0 = 0 ∧ zres z0 z1 lam g z1 = 0 := by
  have hL : 0 < z1 - z0 := sub_pos.2 hz
  have hLne : z1 - z0 ≠ 0 := hL.ne'
  have hμ : 0 < lam * (z1 - z0) ^ 2 / 4 := div_pos (mul_pos hlam (pow_pos hL 2)) (by norm_num)
  obtain ⟨-, h0, h1, -⟩ := intervalIdentity _ (g.comp (C ((z1 - z0) / 2) * X + C ((z0 + z1) / 2))) hμ
  have e0 : 2 / (z1 - z0) * z0 - (z0 + z1) / (z1 - z0) = -1 := by field_simp; ring
  have e1 : 2 / (z1 - z0) * z1 - (z0 + z1) / (z1 - z0) = 1 := by field_simp; ring
  refine ⟨?_, ?_⟩
  · simp only [zres]; rw [e0]; exact h0
  · simp only [zres]; rw [e1]; exact h1

theorem zres_zero (z0 z1 lam z : ℝ) : zres z0 z1 lam 0 z = 0 := by
  have := resolvent_linear (lam * (z1 - z0) ^ 2 / 4) 0 0 0 0 (2 / (z1 - z0) * z - (z0 + z1) / (z1 - z0))
  simp only [zero_smul, add_zero, zero_mul] at this
  simp only [zres, zero_comp]
  exact this

theorem zres_sum (z0 z1 lam : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℝ[X]) (z : ℝ) :
    zres z0 z1 lam (∑ j ∈ s, a j • g j) z = ∑ j ∈ s, a j * zres z0 z1 lam (g j) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zres_zero]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
    simp only [zres, add_comp, smul_comp]
    have := resolvent_linear (lam * (z1 - z0) ^ 2 / 4) (a j) 1
      ((g j).comp (C ((z1 - z0) / 2) * X + C ((z0 + z1) / 2)))
      ((∑ j ∈ s, a j • g j).comp (C ((z1 - z0) / 2) * X + C ((z0 + z1) / 2)))
      (2 / (z1 - z0) * z - (z0 + z1) / (z1 - z0))
    rw [one_smul, one_mul] at this
    exact this

theorem zres_pair {z0 z1 lam : ℝ} (hlam : 0 < lam) (hz : z0 < z1) (g : ℝ[X]) :
    ∫ z in z0..z1, ((g.eval z - zres z0 z1 lam g z) * zres z0 z1 lam g z
      - lam⁻¹ * deriv (zres z0 z1 lam g) z ^ 2) = 0 := by
  have hL : 0 < z1 - z0 := sub_pos.2 hz
  set L := z1 - z0 with hLdef
  set μ := lam * L ^ 2 / 4 with hμdef
  have hμ : 0 < μ := by positivity
  set c := 2 / L with hcdef
  set d := (z0 + z1) / L with hddef
  have hc0 : c ≠ 0 := by positivity
  set pt := g.comp (C (L / 2) * X + C ((z0 + z1) / 2)) with hptdef
  set R := intervalResolvent μ pt with hRdef
  obtain ⟨hC, -, -, -⟩ := intervalIdentity μ pt hμ
  have hpair := resolvent_pair intervalIdentity μ hμ pt pt
  have hpt : ∀ r, g.eval r = pt.eval (c * r - d) := by
    intro r
    simp only [hptdef, eval_comp, eval_add, eval_mul, eval_C, eval_X]
    congr 1
    rw [hcdef, hddef]
    field_simp
    ring
  have hzr : zres z0 z1 lam g = fun r => R (c * r - d) := rfl
  have hdR : ∀ r, deriv (fun s => R (c * s - d)) r = c * deriv R (c * r - d) := by
    intro r
    have hd : DifferentiableAt ℝ R (c * r - d) := (hC.differentiable (by norm_num)).differentiableAt
    have h2 : HasDerivAt (fun s => c * s - d) c r := by
      simpa using ((hasDerivAt_id r).const_mul c).sub_const d
    have h3 := hd.hasDerivAt.comp r h2
    rw [show (fun s => R (c * s - d)) = R ∘ (fun s => c * s - d) from rfl, h3.deriv]
    ring
  have hcv : ∀ f : ℝ → ℝ, ∫ r in z0..z1, f (c * r - d) = (L / 2) * ∫ x in (-1 : ℝ)..1, f x := by
    intro f
    rw [intervalIntegral.integral_comp_mul_sub (f := f) hc0 d, smul_eq_mul]
    have e0 : c * z0 - d = -1 := by rw [hcdef, hddef]; field_simp; ring
    have e1 : c * z1 - d = 1 := by rw [hcdef, hddef]; field_simp; ring
    rw [e0, e1, hcdef]
    congr 1
    field_simp
  have hcμ : lam⁻¹ * c ^ 2 = μ⁻¹ := by
    rw [hcdef, hμdef]
    field_simp
    norm_num
  have e : (fun z => (g.eval z - zres z0 z1 lam g z) * zres z0 z1 lam g z
      - lam⁻¹ * deriv (zres z0 z1 lam g) z ^ 2)
      = fun z => (fun x => R x * pt.eval x - (R x * R x + μ⁻¹ * (deriv R x * deriv R x))) (c * z - d) := by
    funext z
    rw [hpt z, hzr, hdR z]
    linear_combination (-(deriv R (c * z - d) ^ 2)) * hcμ
  have hcR : Continuous R := hC.continuous
  have hcR' : Continuous (deriv R) := hC.continuous_deriv (by norm_num)
  have hcp : Continuous fun x => pt.eval x := pt.continuous
  have i1 : IntervalIntegrable (fun x => R x * pt.eval x) volume (-1) 1 := (hcR.mul hcp).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x => R x * R x + μ⁻¹ * (deriv R x * deriv R x)) volume (-1) 1 :=
    ((hcR.mul hcR).add (continuous_const.mul (hcR'.mul hcR'))).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun x => R x * R x) volume (-1) 1 := (hcR.mul hcR).intervalIntegrable _ _
  have i4 : IntervalIntegrable (fun x => μ⁻¹ * (deriv R x * deriv R x)) volume (-1) 1 :=
    (continuous_const.mul (hcR'.mul hcR')).intervalIntegrable _ _
  rw [e, hcv (fun x => R x * pt.eval x - (R x * R x + μ⁻¹ * (deriv R x * deriv R x))),
    intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_add i3 i4, intervalIntegral.integral_const_mul]
  have hp2 : ∫ x in (-1 : ℝ)..1, R x * pt.eval x
      = (∫ x in (-1 : ℝ)..1, R x * R x) + μ⁻¹ * ∫ x in (-1 : ℝ)..1, deriv R x * deriv R x := hpair
  rw [hp2]
  ring

theorem zres_cert {q : ℕ} {z0 z1 lam vz : ℝ} (hlam : 0 < lam) (hz : z0 < z1)
    (hc : IntervalCertificate q (lam * (z1 - z0) ^ 2 / 4) vz) (g : ℝ[X]) (hg : g.natDegree ≤ q) :
    (∫ z in z0..z1, (g.eval z - zres z0 z1 lam g z) ^ 2)
      + lam⁻¹ * (∫ z in z0..z1, deriv (zres z0 z1 lam g) z ^ 2)
      ≤ vz * ∫ z in z0..z1, g.eval z ^ 2 :=
  interval_scaled intervalIdentity q z0 z1 lam vz hlam hz hc g hg

theorem int1 {E : ℝ → ℝ → ℝ} (hE : Continuous fun x : ℝ × ℝ => E x.1 x.2) {d : ℝ → ℝ}
    (hd : Measurable d) {K : ℝ} (hK : ∀ r, |d r| ≤ K) {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun r => E (d r) r) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (-K) K ×ˢ Icc a b)).exists_bound_of_continuousOn
    hE.continuousOn
  refine Integrable.of_bound ((hE.measurable.comp (hd.prodMk measurable_id)).aestronglyMeasurable) M ?_
  refine (ae_restrict_mem measurableSet_Ioc).mono fun r hr => ?_
  exact hM (d r, r) ⟨abs_le.1 (hK r), Ioc_subset_Icc_self hr⟩

theorem int2 {E : ℝ → ℝ × ℝ → ℝ} (hE : Continuous fun x : ℝ × (ℝ × ℝ) => E x.1 x.2) {d : ℝ → ℝ}
    (hd : Measurable d) {K : ℝ} (hK : ∀ r, |d r| ≤ K) (a b c e : ℝ) :
    Integrable (fun p : ℝ × ℝ => E (d p.1) p) ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c e))) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc) :
    IsCompact (Icc (-K) K ×ˢ (Icc a b ×ˢ Icc c e))).exists_bound_of_continuousOn hE.continuousOn
  refine Integrable.of_bound
    ((hE.measurable.comp ((hd.comp measurable_fst).prodMk measurable_id)).aestronglyMeasurable) M ?_
  have hmem : ∀ᵐ p ∂((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c e))), p ∈ Ioc a b ×ˢ Ioc c e := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  refine hmem.mono fun p hp => ?_
  exact hM (d p.1, p) ⟨abs_le.1 (hK p.1), Ioc_subset_Icc_self hp.1, Ioc_subset_Icc_self hp.2⟩

theorem int2c {F : ℝ × ℝ → ℝ} (hF : Continuous F) (a b c e : ℝ) :
    Integrable F ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c e))) :=
  int2 (E := fun _ x => F x) (by fun_prop) (d := fun _ => 0) measurable_const (K := 0) (by simp) a b c e

theorem prod_facts {f : ℝ → ℝ → ℝ} {a b c e : ℝ} (hab : a ≤ b) (hce : c ≤ e)
    (hF : Integrable (fun x : ℝ × ℝ => f x.1 x.2) ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c e)))) :
    IntervalIntegrable (fun r => ∫ z in c..e, f r z) volume a b ∧
      IntervalIntegrable (fun z => ∫ r in a..b, f r z) volume c e ∧
      ∫ r in a..b, ∫ z in c..e, f r z = ∫ z in c..e, ∫ r in a..b, f r z := by
  simp only [intervalIntegral.integral_of_le hce, intervalIntegral.integral_of_le hab]
  exact ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hF.integral_prod_left,
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hce).2 hF.integral_prod_right,
    integral_integral_swap (f := f) hF⟩

theorem cut_facts {χ : ℝ → ℝ} (hχ : ∃ K, LipschitzWith K χ) {R : ℝ} :
    Continuous χ ∧ Measurable (deriv fun s => χ (s / R)) ∧
      (∃ K : ℝ, ∀ r, |deriv (fun s => χ (s / R)) r| ≤ K) ∧
      ∀ᵐ r, DifferentiableAt ℝ (fun s => χ (s / R)) r := by
  obtain ⟨K, hK⟩ := hχ
  have h2 : LipschitzWith ‖R⁻¹‖₊ (fun s : ℝ => s / R) := by
    simpa [div_eq_inv_mul, smul_eq_mul] using lipschitzWith_smul (β := ℝ) (R⁻¹ : ℝ)
  have hL : LipschitzWith (K * ‖R⁻¹‖₊) (fun s => χ (s / R)) := hK.comp h2
  refine ⟨hK.continuous, measurable_deriv _, ⟨((K * ‖R⁻¹‖₊ : NNReal) : ℝ), fun r => ?_⟩,
    hL.ae_differentiableAt_real⟩
  rw [← Real.norm_eq_abs]
  exact norm_deriv_le_of_lipschitz hL

theorem iterm {i : ℕ} (hi : i ≤ 1) {F F1 c r : ℝ} (hF : i = 1 → F = r * F1) (hr : r ≠ 0) :
    (i : ℝ) ^ 2 * (c * F) ^ 2 / r ^ 2 = (i : ℝ) ^ 2 * c ^ 2 * F1 ^ 2 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with h | h
  · subst h; simp
  · rw [hF h]; subst h; field_simp

theorem axis_nice {q i : ℕ} {R lam ν va : ℝ} {χ : ℝ → ℝ} (hlam : 0 < lam) (hR : 0 < R) (hi : i ≤ 1)
    (hν : ν ≤ lam * R ^ 2) (hA : AxisCertificate q ν va χ) (f f₁ : ℝ[X]) (hf : f.natDegree ≤ q)
    (hf₁ : i = 1 → f = X * f₁) :
    ∫ r in (0:ℝ)..R, ((1 - χ (r / R)) ^ 2 * f.eval r ^ 2 + lam⁻¹ * ((deriv (fun s => χ (s / R)) r * f.eval r
        + χ (r / R) * (derivative f).eval r) ^ 2 + (i : ℝ) ^ 2 * χ (r / R) ^ 2 * f₁.eval r ^ 2)) * r
      ≤ va * ∫ r in (0:ℝ)..R, f.eval r ^ 2 * r := by
  obtain ⟨hν0, -, hχ, hcert⟩ := hA
  obtain ⟨hχc, hdm, ⟨Kd, hKd⟩, hdiff⟩ := cut_facts hχ (R := R)
  have hRne : R ≠ 0 := hR.ne'
  set ft := f.comp (C R * X) with hft
  have hftdeg : ft.natDegree ≤ q := by
    refine natDegree_comp_le.trans ?_
    have : (C R * X).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans natDegree_X_le
    nlinarith
  have hftX : i = 1 → X ∣ ft := by
    intro h1
    rw [hft, hf₁ h1, mul_comp, X_comp]
    exact dvd_mul_of_dvd_left (dvd_mul_left X (C R)) _
  have key := hcert i hi ft hftdeg hftX
  have hfte : ∀ s, ft.eval s = f.eval (R * s) := by intro s; simp [hft, eval_comp]
  have hχs : ∀ s, χ (R * s / R) = χ s := by intro s; rw [mul_div_cancel_left₀ _ hRne]
  obtain ⟨T, hT⟩ : ∃ T : ℝ → ℝ, T = fun r => ((1 - χ (r / R)) ^ 2 * f.eval r ^ 2 + (ν⁻¹ * R ^ 2)
      * (deriv (fun s => χ (s / R) * f.eval s) r ^ 2
      + (i : ℝ) ^ 2 * (χ (r / R) * f.eval r) ^ 2 / r ^ 2)) * r := ⟨_, rfl⟩
  have hderiv : ∀ s, deriv (fun t => χ t * ft.eval t) s
      = R * deriv (fun r => χ (r / R) * f.eval r) (R * s) := by
    intro s
    have e : (fun t => χ t * ft.eval t) = fun t => (fun r => χ (r / R) * f.eval r) (R * t) := by
      funext t; simp only [hfte, hχs]
    rw [e]
    exact deriv_comp_mul_left R (fun r => χ (r / R) * f.eval r) s
  have hL : axisFunctional i χ ν ft = R⁻¹ * (R⁻¹ * ∫ r in (0:ℝ)..R, T r) := by
    have h1 : axisFunctional i χ ν ft = ∫ s in (0:ℝ)..1, R⁻¹ * T (R * s) := by
      unfold axisFunctional
      congr 1
      funext s
      rw [hderiv s, hfte s, hT]
      simp only [hχs]
      rcases eq_or_ne s 0 with hs | hs
      · subst hs; simp
      · field_simp
        try ring
    rw [h1, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left (fun r => T r) hRne,
      mul_zero, mul_one, smul_eq_mul]
  have hRt : ∫ s in (0:ℝ)..1, ft.eval s ^ 2 * s = R⁻¹ * (R⁻¹ * ∫ r in (0:ℝ)..R, f.eval r ^ 2 * r) := by
    have h1 : ∫ s in (0:ℝ)..1, ft.eval s ^ 2 * s
        = ∫ s in (0:ℝ)..1, R⁻¹ * (fun r => f.eval r ^ 2 * r) (R * s) := by
      congr 1; funext s; rw [hfte s]; field_simp; try ring
    rw [h1, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun r => f.eval r ^ 2 * r) hRne, mul_zero, mul_one, smul_eq_mul]
  rw [hL, hRt] at key
  have hpos : 0 < R⁻¹ * R⁻¹ := by positivity
  have hTle : ∫ r in (0:ℝ)..R, T r ≤ va * ∫ r in (0:ℝ)..R, f.eval r ^ 2 * r := by
    have : (R⁻¹ * R⁻¹) * ∫ r in (0:ℝ)..R, T r ≤ (R⁻¹ * R⁻¹) * (va * ∫ r in (0:ℝ)..R, f.eval r ^ 2 * r) :=
      calc (R⁻¹ * R⁻¹) * ∫ r in (0:ℝ)..R, T r = R⁻¹ * (R⁻¹ * ∫ r in (0:ℝ)..R, T r) := by ring
        _ ≤ va * (R⁻¹ * (R⁻¹ * ∫ r in (0:ℝ)..R, f.eval r ^ 2 * r)) := key
        _ = (R⁻¹ * R⁻¹) * (va * ∫ r in (0:ℝ)..R, f.eval r ^ 2 * r) := by ring
    exact le_of_mul_le_mul_left this hpos
  obtain ⟨N, hN⟩ : ∃ N : ℝ → ℝ → ℝ, N = fun a r => ((1 - χ (r / R)) ^ 2 * f.eval r ^ 2
      + a * ((deriv (fun s => χ (s / R)) r * f.eval r
        + χ (r / R) * (derivative f).eval r) ^ 2 + (i : ℝ) ^ 2 * χ (r / R) ^ 2 * f₁.eval r ^ 2)) * r := ⟨_, rfl⟩
  have hTN : ∫ r in (0:ℝ)..R, T r = ∫ r in (0:ℝ)..R, N (ν⁻¹ * R ^ 2) r := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hdiff] with r hr hrI
    have hr0 : 0 < r := by rw [uIoc_of_le hR.le] at hrI; exact hrI.1
    have hD : deriv (fun s => χ (s / R) * f.eval s) r
        = deriv (fun s => χ (s / R)) r * f.eval r + χ (r / R) * (derivative f).eval r := by
      rw [deriv_fun_mul hr (Polynomial.differentiableAt f), Polynomial.deriv]
    have hI := iterm (c := χ (r / R)) hi (F := f.eval r) (F1 := f₁.eval r)
      (fun h => by rw [hf₁ h]; simp) hr0.ne'
    rw [hT, hN]
    simp only
    rw [hD, hI]
  have hNint : ∀ a, IntervalIntegrable (N a) volume 0 R := by
    intro a
    have hfc := f.continuous
    have hf'c := (derivative f).continuous
    have hf1c := f₁.continuous
    rw [hN]
    exact int1 (E := fun t r => ((1 - χ (r / R)) ^ 2 * f.eval r ^ 2 + a * ((t * f.eval r
        + χ (r / R) * (derivative f).eval r) ^ 2 + (i : ℝ) ^ 2 * χ (r / R) ^ 2 * f₁.eval r ^ 2)) * r)
      (by fun_prop) hdm hKd hR.le
  have hlν : lam⁻¹ ≤ ν⁻¹ * R ^ 2 := by
    rw [inv_mul_eq_div, le_div_iff₀ hν0]
    calc lam⁻¹ * ν ≤ lam⁻¹ * (lam * R ^ 2) := mul_le_mul_of_nonneg_left hν (inv_nonneg.2 hlam.le)
      _ = R ^ 2 := by field_simp
  have hmono : ∫ r in (0:ℝ)..R, N lam⁻¹ r ≤ ∫ r in (0:ℝ)..R, N (ν⁻¹ * R ^ 2) r := by
    refine intervalIntegral.integral_mono_on hR.le (hNint _) (hNint _) fun r hr => ?_
    rw [hN]
    refine mul_le_mul_of_nonneg_right ?_ hr.1
    gcongr
  calc _ = ∫ r in (0:ℝ)..R, N lam⁻¹ r := by rw [hN]
    _ ≤ _ := hmono
    _ = _ := hTN.symm
    _ ≤ _ := hTle

theorem axis_first {q : ℕ} {R lam ν va : ℝ} {χ : ℝ → ℝ} (hlam : 0 < lam) (hR : 0 < R)
    (hν : ν ≤ lam * R ^ 2) (hA : AxisCertificate q ν va χ) (f : ℝ[X]) (hf : f.natDegree ≤ q) :
    ∫ r in (0:ℝ)..R, (1 - χ (r / R)) ^ 2 * f.eval r ^ 2 * r ≤ va * ∫ r in (0:ℝ)..R, f.eval r ^ 2 * r := by
  have h := axis_nice (i := 0) hlam hR zero_le_one hν hA f 0 hf (by simp)
  obtain ⟨-, -, hχ, -⟩ := hA
  obtain ⟨hχc, hdm, ⟨Kd, hKd⟩, -⟩ := cut_facts hχ (R := R)
  have hfc := f.continuous
  have hf'c := (derivative f).continuous
  have hl : 0 ≤ lam⁻¹ := inv_nonneg.2 hlam.le
  refine le_trans (intervalIntegral.integral_mono_on hR.le ?_ ?_ fun r hr => ?_) h
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact int1 (E := fun t r => ((1 - χ (r / R)) ^ 2 * f.eval r ^ 2 + lam⁻¹ * ((t * f.eval r
        + χ (r / R) * (derivative f).eval r) ^ 2 + ((0:ℕ) : ℝ) ^ 2 * χ (r / R) ^ 2 * (0:ℝ[X]).eval r ^ 2)) * r)
      (by fun_prop) hdm hKd hR.le
  · have hr0 : 0 ≤ r := hr.1
    have : 0 ≤ lam⁻¹ * ((deriv (fun s => χ (s / R)) r * f.eval r + χ (r / R) * (derivative f).eval r) ^ 2
        + ((0:ℕ) : ℝ) ^ 2 * χ (r / R) ^ 2 * (0:ℝ[X]).eval r ^ 2) := mul_nonneg hl (by positivity)
    nlinarith [mul_nonneg this hr0]

theorem tve (P : ℝ[X][X]) (q : ℕ) (hP : P.natDegree ≤ q) (r z : ℝ) :
    twoVarEval P r z = ∑ j ∈ Finset.range (q + 1), r ^ j * (P.coeff j).eval z := by
  unfold twoVarEval
  rw [eval_eq_sum_range' (n := q + 1) (lt_of_le_of_lt (natDegree_map_le.trans hP) (Nat.lt_succ_self q))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_map, coe_evalRingHom, mul_comm]

theorem hbase {χ : ℝ → ℝ} {R z0 z1 lam va vz : ℝ} {i : ℕ} (p U Ur Uz V : ℝ × ℝ → ℝ)
    (hR : 0 < R) (hz : z0 < z1) (hlam : 0 < lam) (hi : i ≤ 1) (hva : 0 ≤ va)
    (hχ : ∃ K, LipschitzWith K χ)
    (hpc : Continuous p) (hUc : Continuous U) (hUrc : Continuous Ur) (hUzc : Continuous Uz)
    (hVc : Continuous V)
    (hUr : ∀ r z, HasDerivAt (fun s => U (s, z)) (Ur (r, z)) r)
    (hV : i = 1 → ∀ r z, U (r, z) = r * V (r, z))
    (hZ1 : ∀ r, (∫ z in z0..z1, (p (r, z) - U (r, z)) ^ 2) + lam⁻¹ * (∫ z in z0..z1, Uz (r, z) ^ 2)
      ≤ vz * ∫ z in z0..z1, p (r, z) ^ 2)
    (hZ2 : ∀ r, ∫ z in z0..z1, ((p (r, z) - U (r, z)) * U (r, z) - lam⁻¹ * Uz (r, z) ^ 2) = 0)
    (hA1 : ∀ z, ∫ r in (0:ℝ)..R, ((1 - χ (r / R)) ^ 2 * U (r, z) ^ 2
        + lam⁻¹ * ((deriv (fun s => χ (s / R)) r * U (r, z) + χ (r / R) * Ur (r, z)) ^ 2
          + (i : ℝ) ^ 2 * χ (r / R) ^ 2 * V (r, z) ^ 2)) * r
        ≤ va * ∫ r in (0:ℝ)..R, U (r, z) ^ 2 * r)
    (hA2 : ∀ z, ∫ r in (0:ℝ)..R, (1 - χ (r / R)) ^ 2 * Uz (r, z) ^ 2 * r
        ≤ va * ∫ r in (0:ℝ)..R, Uz (r, z) ^ 2 * r) :
    (∫ r in (0 : ℝ)..R, ∫ z in z0..z1,
        ((p (r, z) - χ (r / R) * U (r, z)) ^ 2
          + lam⁻¹ * (deriv (fun s => χ (s / R) * U (s, z)) r ^ 2
            + (χ (r / R) * Uz (r, z)) ^ 2
            + (i : ℝ) ^ 2 * (χ (r / R) * U (r, z)) ^ 2 / r ^ 2)) * r)
      ≤ (va + vz) * ∫ r in (0 : ℝ)..R, ∫ z in z0..z1, p (r, z) ^ 2 * r := by
  obtain ⟨hχc, hdm, ⟨Kd, hKd⟩, hdiff⟩ := cut_facts hχ (R := R)
  have hzle : z0 ≤ z1 := hz.le
  have hl : 0 ≤ lam⁻¹ := inv_nonneg.2 hlam.le
  obtain ⟨Yf, hYf⟩ : ∃ Yf : ℝ → ℝ → ℝ, Yf = fun r z => r * ((p (r, z) - U (r, z)) ^ 2 + lam⁻¹ * Uz (r, z) ^ 2)
      + 2 * (1 - χ (r / R)) * r * ((p (r, z) - U (r, z)) * U (r, z) - lam⁻¹ * Uz (r, z) ^ 2) := ⟨_, rfl⟩
  obtain ⟨EG, hEG⟩ : ∃ EG : ℝ → ℝ → ℝ → ℝ, EG = fun t r z => ((1 - χ (r / R)) ^ 2 * U (r, z) ^ 2
      + lam⁻¹ * ((t * U (r, z) + χ (r / R) * Ur (r, z)) ^ 2 + (i : ℝ) ^ 2 * χ (r / R) ^ 2 * V (r, z) ^ 2)) * r
      + lam⁻¹ * ((1 - χ (r / R)) ^ 2 * Uz (r, z) ^ 2 * r) := ⟨_, rfl⟩
  have hYc : Continuous fun x : ℝ × ℝ => Yf x.1 x.2 := by simp only [hYf]; fun_prop
  have hEGc : Continuous fun y : ℝ × (ℝ × ℝ) => EG y.1 y.2.1 y.2.2 := by simp only [hEG]; fun_prop
  have hGint : Integrable (fun x : ℝ × ℝ => EG (deriv (fun s => χ (s / R)) x.1) x.1 x.2)
      ((volume.restrict (Ioc 0 R)).prod (volume.restrict (Ioc z0 z1))) :=
    int2 (E := fun t x => EG t x.1 x.2) hEGc hdm hKd 0 R z0 z1
  obtain ⟨hGr, hGz, hGswap⟩ :=
    prod_facts (f := fun r z => EG (deriv (fun s => χ (s / R)) r) r z) hR.le hzle hGint
  obtain ⟨hYr, -, -⟩ := prod_facts (f := Yf) hR.le hzle (int2c hYc 0 R z0 z1)
  have hPint := (prod_facts (f := fun r z => p (r, z) ^ 2 * r) hR.le hzle
    (int2c (F := fun x => p x ^ 2 * x.1) (by fun_prop) 0 R z0 z1)).1
  have hWint := prod_facts (f := fun r z => (U (r, z) ^ 2 + lam⁻¹ * Uz (r, z) ^ 2) * r) hR.le hzle
    (int2c (F := fun x => (U x ^ 2 + lam⁻¹ * Uz x ^ 2) * x.1) (by fun_prop) 0 R z0 z1)
  have hA : (∫ r in (0 : ℝ)..R, ∫ z in z0..z1,
        ((p (r, z) - χ (r / R) * U (r, z)) ^ 2
          + lam⁻¹ * (deriv (fun s => χ (s / R) * U (s, z)) r ^ 2
            + (χ (r / R) * Uz (r, z)) ^ 2
            + (i : ℝ) ^ 2 * (χ (r / R) * U (r, z)) ^ 2 / r ^ 2)) * r)
      = ∫ r in (0 : ℝ)..R, ((∫ z in z0..z1, Yf r z)
        + ∫ z in z0..z1, EG (deriv (fun s => χ (s / R)) r) r z) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hdiff] with r hr hrI
    have hr0 : 0 < r := by rw [uIoc_of_le hR.le] at hrI; exact hrI.1
    have hYz : Continuous fun z => Yf r z := hYc.comp (continuous_const.prodMk continuous_id)
    have hGz' : Continuous fun z => EG (deriv (fun s => χ (s / R)) r) r z :=
      hEGc.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    rw [← intervalIntegral.integral_add (hYz.intervalIntegrable _ _) (hGz'.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun z _ => ?_
    have hD : deriv (fun s => χ (s / R) * U (s, z)) r
        = deriv (fun s => χ (s / R)) r * U (r, z) + χ (r / R) * Ur (r, z) := by
      rw [deriv_fun_mul hr (hUr r z).differentiableAt, (hUr r z).deriv]
    have hI := iterm (c := χ (r / R)) hi (F := U (r, z)) (F1 := V (r, z)) (fun h => hV h r z) hr0.ne'
    simp only [hYf, hEG]
    rw [hD, hI]
    ring
  have hYle : ∫ r in (0:ℝ)..R, ∫ z in z0..z1, Yf r z
      ≤ vz * ∫ r in (0:ℝ)..R, ∫ z in z0..z1, p (r, z) ^ 2 * r := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hR.le hYr (hPint.const_mul vz) fun r hr => ?_
    have e1 : ∫ z in z0..z1, Yf r z = r * ((∫ z in z0..z1, (p (r, z) - U (r, z)) ^ 2)
        + lam⁻¹ * ∫ z in z0..z1, Uz (r, z) ^ 2)
        + 2 * (1 - χ (r / R)) * r
          * ∫ z in z0..z1, ((p (r, z) - U (r, z)) * U (r, z) - lam⁻¹ * Uz (r, z) ^ 2) := by
      simp only [hYf]
      rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_add, intervalIntegral.integral_const_mul]
      all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
    rw [e1, hZ2 r, mul_zero, add_zero, intervalIntegral.integral_mul_const]
    calc r * ((∫ z in z0..z1, (p (r, z) - U (r, z)) ^ 2) + lam⁻¹ * ∫ z in z0..z1, Uz (r, z) ^ 2)
        ≤ r * (vz * ∫ z in z0..z1, p (r, z) ^ 2) := mul_le_mul_of_nonneg_left (hZ1 r) hr.1
      _ = vz * ((∫ z in z0..z1, p (r, z) ^ 2) * r) := by ring
  have hGle : ∫ r in (0:ℝ)..R, ∫ z in z0..z1, EG (deriv (fun s => χ (s / R)) r) r z
      ≤ va * ∫ r in (0:ℝ)..R, ∫ z in z0..z1, p (r, z) ^ 2 * r := by
    rw [hGswap]
    have step1 : ∫ z in z0..z1, ∫ r in (0:ℝ)..R, EG (deriv (fun s => χ (s / R)) r) r z
        ≤ ∫ z in z0..z1, va * ∫ r in (0:ℝ)..R, (U (r, z) ^ 2 + lam⁻¹ * Uz (r, z) ^ 2) * r := by
      refine intervalIntegral.integral_mono_on hzle hGz (hWint.2.1.const_mul va) fun z _ => ?_
      have i1 : IntervalIntegrable (fun r => ((1 - χ (r / R)) ^ 2 * U (r, z) ^ 2
          + lam⁻¹ * ((deriv (fun s => χ (s / R)) r * U (r, z) + χ (r / R) * Ur (r, z)) ^ 2
            + (i : ℝ) ^ 2 * χ (r / R) ^ 2 * V (r, z) ^ 2)) * r) volume 0 R :=
        int1 (E := fun t r => ((1 - χ (r / R)) ^ 2 * U (r, z) ^ 2
          + lam⁻¹ * ((t * U (r, z) + χ (r / R) * Ur (r, z)) ^ 2
            + (i : ℝ) ^ 2 * χ (r / R) ^ 2 * V (r, z) ^ 2)) * r) (by fun_prop) hdm hKd hR.le
      have i2 : IntervalIntegrable (fun r => (1 - χ (r / R)) ^ 2 * Uz (r, z) ^ 2 * r) volume 0 R :=
        Continuous.intervalIntegrable (by fun_prop) _ _
      have i3 : IntervalIntegrable (fun r => U (r, z) ^ 2 * r) volume 0 R :=
        Continuous.intervalIntegrable (by fun_prop) _ _
      have i4 : IntervalIntegrable (fun r => Uz (r, z) ^ 2 * r) volume 0 R :=
        Continuous.intervalIntegrable (by fun_prop) _ _
      have e : ∫ r in (0:ℝ)..R, EG (deriv (fun s => χ (s / R)) r) r z
          = (∫ r in (0:ℝ)..R, ((1 - χ (r / R)) ^ 2 * U (r, z) ^ 2
          + lam⁻¹ * ((deriv (fun s => χ (s / R)) r * U (r, z) + χ (r / R) * Ur (r, z)) ^ 2
            + (i : ℝ) ^ 2 * χ (r / R) ^ 2 * V (r, z) ^ 2)) * r)
          + lam⁻¹ * ∫ r in (0:ℝ)..R, (1 - χ (r / R)) ^ 2 * Uz (r, z) ^ 2 * r := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add i1 (i2.const_mul _), hEG]
      have e2 : ∫ r in (0:ℝ)..R, (U (r, z) ^ 2 + lam⁻¹ * Uz (r, z) ^ 2) * r
          = (∫ r in (0:ℝ)..R, U (r, z) ^ 2 * r) + lam⁻¹ * ∫ r in (0:ℝ)..R, Uz (r, z) ^ 2 * r := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add i3 (i4.const_mul _)]
        congr 1; funext r; ring
      rw [e, e2]
      have h1 := hA1 z
      have h2 := mul_le_mul_of_nonneg_left (hA2 z) hl
      nlinarith
    refine step1.trans ?_
    rw [intervalIntegral.integral_const_mul, ← hWint.2.2]
    refine mul_le_mul_of_nonneg_left ?_ hva
    refine intervalIntegral.integral_mono_on hR.le hWint.1 hPint fun r hr => ?_
    have hpt : ∀ z, (U (r, z) ^ 2 + lam⁻¹ * Uz (r, z) ^ 2) * r = p (r, z) ^ 2 * r
        - (r * (p (r, z) - U (r, z)) ^ 2 + lam⁻¹ * r * Uz (r, z) ^ 2)
        - 2 * r * ((p (r, z) - U (r, z)) * U (r, z) - lam⁻¹ * Uz (r, z) ^ 2) := fun z => by ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul, hZ2 r,
      intervalIntegral.integral_add, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    · have n1 : 0 ≤ ∫ z in z0..z1, (p (r, z) - U (r, z)) ^ 2 :=
        intervalIntegral.integral_nonneg hzle fun z _ => sq_nonneg _
      have n2 : 0 ≤ ∫ z in z0..z1, Uz (r, z) ^ 2 := intervalIntegral.integral_nonneg hzle fun z _ => sq_nonneg _
      nlinarith [mul_nonneg hr.1 n1, mul_nonneg (mul_nonneg hl hr.1) n2]
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [hA, intervalIntegral.integral_add hYr hGr]
  calc _ ≤ vz * (∫ r in (0:ℝ)..R, ∫ z in z0..z1, p (r, z) ^ 2 * r)
        + va * ∫ r in (0:ℝ)..R, ∫ z in z0..z1, p (r, z) ^ 2 * r := add_le_add hYle hGle
    _ = _ := by ring

end Internal.RectAxis

open Internal.RectAxis in
theorem rectAxis_holds : RectAxisStatement := by
  intro q i R z0 z1 lam ν va vz χ hlam hR hz hi hν hA hI P hPdeg hPcoef hPX
  have hAx := hA
  obtain ⟨hν0, -, hχ, hcert⟩ := hA
  have hva : 0 ≤ va := by
    have h := hcert 0 zero_le_one 1 (by simp) (by simp)
    have h0 : 0 ≤ axisFunctional 0 χ ν 1 := by
      unfold axisFunctional
      refine intervalIntegral.integral_nonneg zero_le_one fun r hr => ?_
      exact mul_nonneg (add_nonneg (by positivity) (mul_nonneg (inv_nonneg.2 hν0.le) (by positivity))) hr.1
    have h2 : ∫ r in (0:ℝ)..1, (1 : ℝ[X]).eval r ^ 2 * r = 1 / 2 := by simp [integral_id]
    rw [h2] at h
    linarith
  have hC2 : ∀ j, ContDiff ℝ 2 (zres z0 z1 lam (P.coeff j)) := fun j => zres_contDiff hlam hz _
  have h0 : i = 1 → P.coeff 0 = 0 := by
    intro h1
    obtain ⟨Q, hQ⟩ := hPX h1
    simp [hQ]
  refine ⟨fun j => zres z0 z1 lam (P.coeff j), fun j => (hC2 j).of_le (by norm_num),
    fun j => zres_ends hlam hz _, fun h1 => ?_, ?_⟩
  · funext z
    simp [h0 h1, zres_zero]
  obtain ⟨pr, hpr⟩ : ∃ pr : ℝ → ℝ[X], pr = fun r => ∑ j ∈ Finset.range (q + 1), r ^ j • P.coeff j :=
    ⟨_, rfl⟩
  have hpr_deg : ∀ r, (pr r).natDegree ≤ q := fun r => by
    rw [hpr]
    exact natDegree_sum_le_of_forall_le _ _ fun j _ => (natDegree_smul_le _ _).trans (hPcoef j)
  have hpr_eval : ∀ r z, (pr r).eval z = twoVarEval P r z := by
    intro r z
    rw [tve P q hPdeg r z, hpr]
    simp [eval_finsetSum]
  have hpr_zres : ∀ r z, zres z0 z1 lam (pr r) z
      = ∑ j ∈ Finset.range (q + 1), r ^ j * zres z0 z1 lam (P.coeff j) z := by
    intro r z
    rw [hpr]
    exact zres_sum z0 z1 lam _ (fun j => r ^ j) (fun j => P.coeff j) z
  have hsum_deriv : ∀ r z, HasDerivAt (fun t => ∑ j ∈ Finset.range (q + 1), r ^ j * zres z0 z1 lam (P.coeff j) t)
      (∑ j ∈ Finset.range (q + 1), r ^ j * deriv (zres z0 z1 lam (P.coeff j)) z) z := by
    intro r z
    exact HasDerivAt.fun_sum fun j _ => (((hC2 j).differentiable (by norm_num) z).hasDerivAt).const_mul (r ^ j)
  have hpr_deriv : ∀ r z, deriv (zres z0 z1 lam (pr r)) z
      = ∑ j ∈ Finset.range (q + 1), r ^ j * deriv (zres z0 z1 lam (P.coeff j)) z := by
    intro r z
    rw [show zres z0 z1 lam (pr r) = fun t => ∑ j ∈ Finset.range (q + 1), r ^ j * zres z0 z1 lam (P.coeff j) t
      from funext (hpr_zres r)]
    exact (hsum_deriv r z).deriv
  refine hbase (χ := χ) (R := R) (z0 := z0) (z1 := z1) (lam := lam) (va := va) (vz := vz) (i := i)
    (fun x => twoVarEval P x.1 x.2)
    (fun x => ∑ j ∈ Finset.range (q + 1), x.1 ^ j * zres z0 z1 lam (P.coeff j) x.2)
    (fun x => ∑ j ∈ Finset.range (q + 1), ((j : ℝ) * x.1 ^ (j - 1)) * zres z0 z1 lam (P.coeff j) x.2)
    (fun x => ∑ j ∈ Finset.range (q + 1), x.1 ^ j * deriv (zres z0 z1 lam (P.coeff j)) x.2)
    (fun x => ∑ j ∈ Finset.range q, x.1 ^ j * zres z0 z1 lam (P.coeff (j + 1)) x.2)
    hR hz hlam hi hva hχ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have e : (fun x : ℝ × ℝ => twoVarEval P x.1 x.2)
        = fun x => ∑ j ∈ Finset.range (q + 1), x.1 ^ j * (P.coeff j).eval x.2 :=
      funext fun x => tve P q hPdeg x.1 x.2
    rw [e]
    exact continuous_finsetSum _ fun j _ => (continuous_fst.pow j).mul ((P.coeff j).continuous.comp continuous_snd)
  · exact continuous_finsetSum _ fun j _ => (continuous_fst.pow j).mul ((hC2 j).continuous.comp continuous_snd)
  · exact continuous_finsetSum _ fun j _ =>
      (continuous_const.mul (continuous_fst.pow (j - 1))).mul ((hC2 j).continuous.comp continuous_snd)
  · exact continuous_finsetSum _ fun j _ =>
      (continuous_fst.pow j).mul (((hC2 j).continuous_deriv (by norm_num)).comp continuous_snd)
  · exact continuous_finsetSum _ fun j _ => (continuous_fst.pow j).mul ((hC2 (j + 1)).continuous.comp continuous_snd)
  · intro r z
    dsimp only
    exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_pow j r).mul_const _
  · intro h1 r z
    dsimp only
    rw [Finset.sum_range_succ', h0 h1, zres_zero, mul_zero, add_zero, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  · intro r
    dsimp only
    have h := zres_cert hlam hz hI (pr r) (hpr_deg r)
    simp only [hpr_deriv, hpr_zres, hpr_eval] at h
    exact h
  · intro r
    dsimp only
    have h := zres_pair hlam hz (pr r)
    simp only [hpr_deriv, hpr_zres, hpr_eval] at h
    exact h
  · intro z
    dsimp only
    obtain ⟨f, hf⟩ : ∃ f : ℝ[X], f = ∑ j ∈ Finset.range (q + 1), C (zres z0 z1 lam (P.coeff j) z) * X ^ j :=
      ⟨_, rfl⟩
    obtain ⟨f₁, hf₁⟩ : ∃ f₁ : ℝ[X],
        f₁ = ∑ j ∈ Finset.range q, C (zres z0 z1 lam (P.coeff (j + 1)) z) * X ^ j := ⟨_, rfl⟩
    have hfdeg : f.natDegree ≤ q := by
      rw [hf]
      exact natDegree_sum_le_of_forall_le _ _ fun j hj =>
        (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
    have hfX : i = 1 → f = X * f₁ := by
      intro h1
      rw [hf, hf₁, Finset.sum_range_succ', h0 h1, zres_zero, map_zero, zero_mul, add_zero, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hfe : ∀ r, f.eval r = ∑ j ∈ Finset.range (q + 1), r ^ j * zres z0 z1 lam (P.coeff j) z := by
      intro r
      rw [hf]
      simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hf'e : ∀ r, (derivative f).eval r
        = ∑ j ∈ Finset.range (q + 1), ((j : ℝ) * r ^ (j - 1)) * zres z0 z1 lam (P.coeff j) z := by
      intro r
      rw [hf]
      simp only [derivative_sum, derivative_C_mul_X_pow, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hf1e : ∀ r, f₁.eval r = ∑ j ∈ Finset.range q, r ^ j * zres z0 z1 lam (P.coeff (j + 1)) z := by
      intro r
      rw [hf₁]
      simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h := axis_nice hlam hR hi hν hAx f f₁ hfdeg hfX
    simp only [hfe, hf'e, hf1e] at h
    exact h
  · intro z
    dsimp only
    obtain ⟨g, hg⟩ : ∃ g : ℝ[X],
        g = ∑ j ∈ Finset.range (q + 1), C (deriv (zres z0 z1 lam (P.coeff j)) z) * X ^ j := ⟨_, rfl⟩
    have hgdeg : g.natDegree ≤ q := by
      rw [hg]
      exact natDegree_sum_le_of_forall_le _ _ fun j hj =>
        (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
    have hge : ∀ r, g.eval r = ∑ j ∈ Finset.range (q + 1), r ^ j * deriv (zres z0 z1 lam (P.coeff j)) z := by
      intro r
      rw [hg]
      simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h := axis_first hlam hR hν hAx g hgdeg
    simp only [hge] at h
    exact h

end Breakdown.CellCert.Spectral
