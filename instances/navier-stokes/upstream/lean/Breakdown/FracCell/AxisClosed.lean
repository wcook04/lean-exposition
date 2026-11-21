import Breakdown.FracCell.StSpectral
import Mathlib

open MeasureTheory Polynomial
open scoped Interval

noncomputable section

namespace Breakdown.FracInternal.AxisClosedParts

def bumpPoly (m : ℕ) : ℝ[X] := X ^ m * (1 - X) ^ m

def orthPoly (m : ℕ) : ℝ[X] := (shiftedLegendre m).map (algebraMap ℤ ℝ)

lemma factorial_mul_orthPoly (m : ℕ) :
    (m.factorial : ℝ[X]) * orthPoly m = derivative^[m] (bumpPoly m) := by
  have h := congrArg (Polynomial.map (algebraMap ℤ ℝ)) (factorial_mul_shiftedLegendre_eq m)
  rw [Polynomial.map_mul, ← iterate_derivative_map] at h
  simpa [orthPoly, bumpPoly] using h

lemma iter_factor (m : ℕ) : ∀ k, k ≤ m →
    ∃ h : ℝ[X], derivative^[k] (bumpPoly m) = (X * (1 - X)) ^ (m - k) * h := by
  intro k
  induction k with
  | zero => intro _; exact ⟨1, by simp [bumpPoly, mul_pow]⟩
  | succ k ih =>
    intro hk
    obtain ⟨h, hh⟩ := ih (by omega)
    obtain ⟨b, hb⟩ : ∃ b, m - k = b + 1 := ⟨m - k - 1, by omega⟩
    have hb' : m - (k + 1) = b := by omega
    refine ⟨C ((b : ℝ) + 1) * derivative (X * (1 - X) : ℝ[X]) * h + X * (1 - X) * derivative h, ?_⟩
    rw [Function.iterate_succ_apply', hh, hb, hb', derivative_mul, derivative_pow_succ]
    ring

lemma iter_eval_zero (m k : ℕ) (hk : k < m) :
    (derivative^[k] (bumpPoly m)).eval 0 = 0 ∧ (derivative^[k] (bumpPoly m)).eval 1 = 0 := by
  obtain ⟨h, hh⟩ := iter_factor m k hk.le
  obtain ⟨b, hb⟩ : ∃ b, m - k = b + 1 := ⟨m - k - 1, by omega⟩
  rw [hh, hb]
  simp [pow_succ]

lemma parts_gen (a b : ℝ[X]) :
    ∫ x in (0 : ℝ)..1, b.eval x * (derivative a).eval x
      = b.eval 1 * a.eval 1 - b.eval 0 * a.eval 0
        - ∫ x in (0 : ℝ)..1, (derivative b).eval x * a.eval x :=
  intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun x _ => b.hasDerivAt x)
    (fun x _ => a.hasDerivAt x) ((derivative b).continuous.intervalIntegrable _ _)
    ((derivative a).continuous.intervalIntegrable _ _)

lemma parts_zero (a b : ℝ[X]) (h0 : a.eval 0 = 0) (h1 : a.eval 1 = 0) :
    ∫ x in (0 : ℝ)..1, (derivative a).eval x * b.eval x
      = -∫ x in (0 : ℝ)..1, a.eval x * (derivative b).eval x := by
  have h := parts_gen a b
  rw [h0, h1, mul_zero, mul_zero, sub_zero, zero_sub] at h
  have e1 : (fun x => (derivative a).eval x * b.eval x) = fun x => b.eval x * (derivative a).eval x := by
    funext x; ring
  have e2 : (fun x => a.eval x * (derivative b).eval x) = fun x => (derivative b).eval x * a.eval x := by
    funext x; ring
  rw [e1, e2, h]

lemma iter_parts (m : ℕ) : ∀ k, k ≤ m → ∀ g : ℝ[X],
    ∫ x in (0 : ℝ)..1, (derivative^[k] (bumpPoly m)).eval x * g.eval x
      = (-1) ^ k * ∫ x in (0 : ℝ)..1, (bumpPoly m).eval x * (derivative^[k] g).eval x := by
  intro k
  induction k with
  | zero => intro _ g; simp
  | succ k ih =>
    intro hk g
    obtain ⟨h0, h1⟩ := iter_eval_zero m k (by omega)
    rw [Function.iterate_succ_apply', parts_zero _ _ h0 h1, ih (by omega), Function.iterate_succ_apply]
    ring

lemma orth (m : ℕ) (h : ℝ[X]) (hh : h.natDegree < m) :
    ∫ x in (0 : ℝ)..1, h.eval x * (orthPoly m).eval x = 0 := by
  have hf : (m.factorial : ℝ) ≠ 0 := by positivity
  have key : ∀ x, h.eval x * (orthPoly m).eval x
      = (m.factorial : ℝ)⁻¹ * ((derivative^[m] (bumpPoly m)).eval x * h.eval x) := by
    intro x
    rw [← factorial_mul_orthPoly, eval_mul, eval_natCast]
    field_simp
  simp_rw [key]
  rw [intervalIntegral.integral_const_mul, iter_parts m m le_rfl, iterate_derivative_eq_zero hh]
  simp

lemma comp_symm (m : ℕ) : (-1) ^ m * (orthPoly m).comp (1 - X) = orthPoly m := by
  have h := congrArg (Polynomial.map (algebraMap ℤ ℝ))
    (neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq m)
  simpa [orthPoly, Polynomial.map_comp] using h

lemma l_zero (m : ℕ) : (orthPoly m).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, orthPoly, coeff_map, coeff_shiftedLegendre]
  simp

lemma dl_zero (m : ℕ) : (derivative (orthPoly m)).eval 0 = -((m : ℝ) * (m + 1)) := by
  rw [← coeff_zero_eq_eval_zero, coeff_derivative, orthPoly, coeff_map, coeff_shiftedLegendre]
  simp [Nat.choose_succ_self_right]

lemma l_one (m : ℕ) : (orthPoly m).eval 1 = (-1) ^ m := by
  have h := congrArg (eval 0) (comp_symm m)
  simp only [eval_mul, eval_pow, eval_neg, eval_one, eval_comp, eval_sub, eval_X, sub_zero,
    l_zero] at h
  have hs : ((-1 : ℝ) ^ m) * ((-1) ^ m) = 1 := by rw [← mul_pow]; simp
  linear_combination ((-1 : ℝ) ^ m) * h - (orthPoly m).eval 1 * hs

lemma dl_one (m : ℕ) : (derivative (orthPoly m)).eval 1 = (-1) ^ m * ((m : ℝ) * (m + 1)) := by
  have h := congrArg (fun P => (derivative P).eval 0) (comp_symm m)
  simp only [derivative_mul, derivative_comp, derivative_sub, derivative_one, derivative_X,
    derivative_pow, derivative_neg, eval_mul, eval_pow, eval_neg, eval_one,
    eval_comp, eval_sub, eval_X, sub_zero, zero_sub, dl_zero, mul_zero, zero_mul,
    neg_zero, zero_add] at h
  have hs : ((-1 : ℝ) ^ m) * ((-1) ^ m) = 1 := by rw [← mul_pow]; simp
  linear_combination (-((-1 : ℝ) ^ m)) * h + (-((derivative (orthPoly m)).eval 1)) * hs

lemma reproduce (q : ℕ) (g : ℝ[X]) (hg : g.natDegree ≤ q) :
    ∫ r in (0 : ℝ)..1, (derivative (orthPoly (q + 1))).eval r * g.eval r * r
      = (-1) ^ (q + 1) * g.eval 1 := by
  have hG : (derivative (g * X)).natDegree < q + 1 := by
    have h1 := natDegree_derivative_le (g * X)
    have h2 : (g * X).natDegree ≤ q + 1 :=
      (natDegree_mul_le).trans (by simp only [natDegree_X]; omega)
    omega
  have h := parts_gen (orthPoly (q + 1)) (g * X)
  rw [orth (q + 1) _ hG, l_one] at h
  have e : (fun r => (derivative (orthPoly (q + 1))).eval r * g.eval r * r)
      = fun r => (g * X).eval r * (derivative (orthPoly (q + 1))).eval r := by
    funext r; simp only [eval_mul, eval_X]; ring
  rw [e, h]
  simp [mul_comm]

lemma pair_le (u v : ℝ[X]) :
    (∫ r in (0 : ℝ)..1, u.eval r * v.eval r * r) ^ 2
      ≤ (∫ r in (0 : ℝ)..1, u.eval r ^ 2 * r) * ∫ r in (0 : ℝ)..1, v.eval r ^ 2 * r := by
  set A := ∫ r in (0 : ℝ)..1, u.eval r ^ 2 * r
  set B := ∫ r in (0 : ℝ)..1, u.eval r * v.eval r * r
  set D := ∫ r in (0 : ℝ)..1, v.eval r ^ 2 * r
  have key : ∀ t : ℝ, 0 ≤ A * (t * t) + (-2 * B) * t + D := by
    intro t
    have hnn : 0 ≤ ∫ r in (0 : ℝ)..1, (t * u.eval r - v.eval r) ^ 2 * r :=
      intervalIntegral.integral_nonneg zero_le_one (fun r hr => mul_nonneg (sq_nonneg _) hr.1)
    have e : (fun r => (t * u.eval r - v.eval r) ^ 2 * r) = fun r =>
        (t * t) * (u.eval r ^ 2 * r) + (-2 * t) * (u.eval r * v.eval r * r) + v.eval r ^ 2 * r := by
      funext r; ring
    have c1 : Continuous fun r => u.eval r ^ 2 * r := by fun_prop
    have c2 : Continuous fun r => u.eval r * v.eval r * r := by fun_prop
    have c3 : Continuous fun r => v.eval r ^ 2 * r := by fun_prop
    rw [e, intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hnn
    · linarith
    · exact (c1.const_smul (t * t)).intervalIntegrable _ _
    · exact (c2.const_smul (-2 * t)).intervalIntegrable _ _
    · exact ((c1.const_smul (t * t)).add (c2.const_smul (-2 * t))).intervalIntegrable _ _
    · exact c3.intervalIntegrable _ _
  have h := discrim_le_zero key
  unfold discrim at h
  nlinarith

lemma endpoint (q : ℕ) (u : ℝ[X]) (hu : u.natDegree ≤ q) :
    u.eval 1 ^ 2 ≤ ((q : ℝ) + 1) * ((q : ℝ) + 2) * ∫ r in (0 : ℝ)..1, u.eval r ^ 2 * r := by
  have hLdeg : (derivative (orthPoly (q + 1))).natDegree ≤ q := by
    have h1 := natDegree_derivative_le (orthPoly (q + 1))
    have h2 : (orthPoly (q + 1)).natDegree ≤ q + 1 := by
      unfold orthPoly; exact natDegree_map_le.trans (by simp)
    omega
  set L := derivative (orthPoly (q + 1))
  have hA := reproduce q L hLdeg
  have hB := reproduce q u hu
  have hcs := pair_le L u
  have hsq : ((-1 : ℝ) ^ (q + 1)) * ((-1) ^ (q + 1)) = 1 := by rw [← mul_pow]; simp
  have hA' : ∫ r in (0 : ℝ)..1, L.eval r ^ 2 * r = ((q : ℝ) + 1) * ((q : ℝ) + 2) := by
    have e : (fun r => L.eval r ^ 2 * r) = fun r => L.eval r * L.eval r * r := by funext r; ring
    rw [e, hA, dl_one]
    push_cast
    linear_combination (((q : ℝ) + 1) * ((q : ℝ) + 1 + 1)) * hsq
  rw [hB, hA'] at hcs
  have e2 : ((-1 : ℝ) ^ (q + 1) * u.eval 1) ^ 2 = u.eval 1 ^ 2 := by
    linear_combination (u.eval 1 ^ 2) * hsq
  rw [e2] at hcs
  exact hcs

end Breakdown.FracInternal.AxisClosedParts

namespace Breakdown.FracInternal.AxisClosedParts

lemma sup_bound (q : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ q) (x : ℝ) (hx1 : 1 / 2 ≤ x)
    (hx2 : x ≤ 1) :
    p.eval x ^ 2 * x ≤ 4 * ((q : ℝ) + 1) ^ 2 * ∫ r in (0 : ℝ)..1, p.eval r ^ 2 * r := by
  have hx0 : 0 < x := by linarith
  set u := p.comp (C x * X) with hu_def
  have hu : u.natDegree ≤ q := by
    refine natDegree_comp_le.trans ?_
    have h1 : (C x * X).natDegree ≤ 1 := (natDegree_C_mul_le x X).trans natDegree_X_le
    calc p.natDegree * (C x * X).natDegree ≤ q * 1 := Nat.mul_le_mul hp h1
      _ = q := mul_one q
  have h1 := endpoint q u hu
  have hu1 : u.eval 1 = p.eval x := by simp [u]
  set I := ∫ r in (0 : ℝ)..x, p.eval r ^ 2 * r
  set S := ∫ r in (0 : ℝ)..1, p.eval r ^ 2 * r
  have hint : ∫ r in (0 : ℝ)..1, u.eval r ^ 2 * r = x⁻¹ * (x⁻¹ * I) := by
    have e : (fun r => u.eval r ^ 2 * r) = fun r => x⁻¹ * ((fun s => p.eval s ^ 2 * s) (x * r)) := by
      funext r
      simp only [u, eval_comp, eval_mul, eval_C, eval_X]
      field_simp
    rw [e, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun s => p.eval s ^ 2 * s) hx0.ne']
    simp [I]
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hx0.le (fun r hr => mul_nonneg (sq_nonneg _) hr.1)
  have hIS : I ≤ S := by
    refine intervalIntegral.integral_mono_interval le_rfl hx0.le hx2 ?_ ?_
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun r hr => mul_nonneg (sq_nonneg _) hr.1.le)
    · exact (by fun_prop : Continuous fun r => p.eval r ^ 2 * r).intervalIntegrable _ _
  rw [hu1, hint] at h1
  have hK : 0 ≤ ((q : ℝ) + 1) * ((q : ℝ) + 2) := by positivity
  have h2 : p.eval x ^ 2 * x ≤ ((q : ℝ) + 1) * ((q : ℝ) + 2) * (x⁻¹ * I) := by
    have := mul_le_mul_of_nonneg_right h1 hx0.le
    calc p.eval x ^ 2 * x ≤ ((q : ℝ) + 1) * ((q : ℝ) + 2) * (x⁻¹ * (x⁻¹ * I)) * x := this
      _ = ((q : ℝ) + 1) * ((q : ℝ) + 2) * (x⁻¹ * I) := by field_simp
  have hxi : x⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hx0 (by norm_num)]; linarith
  have h3 : x⁻¹ * I ≤ 2 * S := mul_le_mul hxi hIS hI0 (by norm_num)
  have hS0 : 0 ≤ S := hI0.trans hIS
  calc p.eval x ^ 2 * x ≤ ((q : ℝ) + 1) * ((q : ℝ) + 2) * (x⁻¹ * I) := h2
    _ ≤ ((q : ℝ) + 1) * ((q : ℝ) + 2) * (2 * S) := mul_le_mul_of_nonneg_left h3 hK
    _ ≤ 4 * ((q : ℝ) + 1) ^ 2 * S := by
      have : ((q : ℝ) + 2) ≤ 2 * ((q : ℝ) + 1) := by
        have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
        linarith
      have hq1 : (0 : ℝ) ≤ (q : ℝ) + 1 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hq1)
        (by positivity : (0 : ℝ) ≤ 2 * S)]

lemma grad_cont (i : ℕ) (hi : i ≤ 1) (p : ℝ[X]) (hdiv : i = 1 → X ∣ p) :
    Continuous fun r : ℝ => ((derivative p).eval r ^ 2 + (i : ℝ) ^ 2 * p.eval r ^ 2 / r ^ 2) * r := by
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      zero_div, add_zero]
    fun_prop
  · obtain ⟨s, rfl⟩ := hdiv rfl
    have e : (fun r : ℝ => ((derivative (X * s)).eval r ^ 2 + ((1 : ℕ) : ℝ) ^ 2 * (X * s).eval r ^ 2 / r ^ 2) * r)
        = fun r => (derivative (X * s)).eval r ^ 2 * r + s.eval r ^ 2 * r := by
      funext r
      by_cases hr : r = 0
      · subst hr; simp
      · simp only [eval_mul, eval_X, Nat.cast_one, one_pow, one_mul]
        field_simp
    rw [e]
    fun_prop

lemma pt_upper (c x Dv T r m Pv δ : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hT : 0 ≤ T) (hr : 0 ≤ r)
    (hm : 0 ≤ m) (hx : x = Pv / δ) :
    ((1 - c) ^ 2 * Pv ^ 2 + m * ((-(1 / δ) * Pv + c * Dv) ^ 2 + c ^ 2 * T)) * r
      ≤ 2 * m * ((Dv ^ 2 + T) * r) + ((1 - c) ^ 2 + 2 * m / δ ^ 2) * (Pv ^ 2 * r) := by
  have hx2 : Pv ^ 2 / δ ^ 2 = x ^ 2 := by rw [hx, div_pow]
  have e1 : -(1 / δ) * Pv = -x := by rw [hx]; ring
  rw [e1]
  have hc2 : c ^ 2 ≤ 1 := by nlinarith
  have h1 : (-x + c * Dv) ^ 2 ≤ 2 * x ^ 2 + 2 * Dv ^ 2 := by
    nlinarith [sq_nonneg (x + c * Dv), mul_le_mul_of_nonneg_right hc2 (sq_nonneg Dv)]
  have h2 : c ^ 2 * T ≤ T := by nlinarith
  have h3 : m * ((-x + c * Dv) ^ 2 + c ^ 2 * T) ≤ 2 * m * (Dv ^ 2 + T) + 2 * m / δ ^ 2 * Pv ^ 2 := by
    have : 2 * m / δ ^ 2 * Pv ^ 2 = 2 * m * x ^ 2 := by rw [← hx2]; ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left h1 hm, mul_le_mul_of_nonneg_left h2 hm]
  nlinarith [mul_le_mul_of_nonneg_right h3 hr]

end Breakdown.FracInternal.AxisClosedParts

section

open Set
open scoped Topology

namespace Breakdown.CellCert.Spectral

open Breakdown.FracInternal.AxisClosedParts

theorem axisClosed_holds : AxisClosedStatement := by
  intro q M μ hM hμ i hi p hp hdiv
  have hμ0 : 0 < μ := by linarith
  set e : ℝ := μ ^ (-(1 / 2 : ℝ)) with he
  have he0 : 0 < e := Real.rpow_pos_of_pos hμ0 _
  have he2 : e ^ 2 = μ⁻¹ := by
    rw [he, ← Real.rpow_natCast, ← Real.rpow_mul hμ0.le]
    norm_num
    exact Real.rpow_neg_one μ
  have hs6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  set δ : ℝ := Real.sqrt 6 * e with hδ
  have hδ0 : 0 < δ := by positivity
  have hδne : δ ≠ 0 := hδ0.ne'
  have hm0 : 0 ≤ μ⁻¹ := inv_nonneg.2 hμ0.le
  have hδ2 : δ ^ 2 = 6 * μ⁻¹ := by rw [hδ, mul_pow, hs6, he2]
  have hδhalf : δ ≤ 1 / 2 := by
    have hinv : μ⁻¹ ≤ 1 / 24 := by
      rw [inv_le_comm₀ hμ0 (by norm_num)]; norm_num; linarith
    nlinarith
  set a : ℝ := 1 - δ with ha
  have ha_half : 1 / 2 ≤ a := by linarith
  have ha1 : a < 1 := by linarith
  set S := ∫ r in (0 : ℝ)..1, p.eval r ^ 2 * r with hS
  set χ : ℝ → ℝ := fun r => min 1 ((1 - r) / δ) with hχ
  refine ⟨χ, ?_, ?_, ?_⟩
  · simp [hχ]
  · refine ⟨Real.toNNReal δ⁻¹, ?_⟩
    refine LipschitzWith.const_min ?_ 1
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (inv_nonneg.2 hδ0.le),
      show (1 - x) / δ - (1 - y) / δ = δ⁻¹ * (y - x) by field_simp; ring, abs_mul,
      abs_of_pos (inv_pos.2 hδ0), abs_sub_comm]
  · set G : ℝ → ℝ := fun r => ((derivative p).eval r ^ 2 + (i : ℝ) ^ 2 * p.eval r ^ 2 / r ^ 2) * r
      with hG
    set Hc : ℝ → ℝ := fun r => (((r - a) / δ) ^ 2 + 2 * μ⁻¹ / δ ^ 2) * (p.eval r ^ 2 * r) with hHc
    set g : ℝ → ℝ := fun r => 2 * μ⁻¹ * G r + (Ioi a).indicator Hc r with hg
    have hGc : Continuous G := grad_cont i hi p hdiv
    have hHcc : Continuous Hc := by rw [hHc]; fun_prop
    have hGint : IntegrableOn G (Ioc 0 1) := (hGc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hHint : IntegrableOn Hc (Ioc 0 1) := (hHcc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hgint : Integrable g (volume.restrict (Ioc 0 1)) :=
      (hGint.const_mul (2 * μ⁻¹)).add (hHint.indicator measurableSet_Ioi)
    have hpt : ∀ r, r ∈ Ioc (0 : ℝ) 1 → r ≠ a →
        ((1 - χ r) ^ 2 * p.eval r ^ 2 + μ⁻¹ * (deriv (fun s => χ s * p.eval s) r ^ 2
          + (i : ℝ) ^ 2 * χ r ^ 2 * p.eval r ^ 2 / r ^ 2)) * r ≤ g r := by
      intro r hr hra
      rcases lt_or_gt_of_ne hra with hlt | hgt
      · have hev : (fun s => χ s * p.eval s) =ᶠ[𝓝 r] fun s => p.eval s := by
          filter_upwards [Iio_mem_nhds hlt] with s hs
          have : 1 ≤ (1 - s) / δ := by
            rw [le_div_iff₀ hδ0]; simp only [mem_Iio] at hs; linarith
          simp [hχ, min_eq_left this]
        have hχr : χ r = 1 := min_eq_left (by rw [le_div_iff₀ hδ0]; linarith)
        rw [hev.deriv_eq, Polynomial.deriv, hχr]
        have hnot : r ∉ Ioi a := fun h => absurd (mem_Ioi.1 h) (not_lt.2 hlt.le)
        simp only [hg, indicator_of_notMem hnot, add_zero, hG]
        have hT : 0 ≤ ((derivative p).eval r ^ 2 + (i : ℝ) ^ 2 * p.eval r ^ 2 / r ^ 2) * r :=
          mul_nonneg (by positivity) hr.1.le
        have e1 : (i : ℝ) ^ 2 * 1 ^ 2 * p.eval r ^ 2 / r ^ 2 = (i : ℝ) ^ 2 * p.eval r ^ 2 / r ^ 2 := by
          ring
        rw [e1]
        nlinarith [mul_nonneg hm0 hT]
      · have hev : (fun s => χ s * p.eval s) =ᶠ[𝓝 r] fun s => (1 - s) / δ * p.eval s := by
          filter_upwards [Ioi_mem_nhds hgt] with s hs
          have : (1 - s) / δ ≤ 1 := by
            rw [div_le_one hδ0]; simp only [mem_Ioi] at hs; linarith
          simp [hχ, min_eq_right this]
        have hd : HasDerivAt (fun s => (1 - s) / δ * p.eval s)
            (-(1 / δ) * p.eval r + (1 - r) / δ * (derivative p).eval r) r := by
          have h1 : HasDerivAt (fun s : ℝ => (1 - s) / δ) (-(1 / δ)) r := by
            have := ((hasDerivAt_id' r).const_sub 1).div_const δ
            exact this.congr_deriv (by ring)
          exact h1.mul (p.hasDerivAt r)
        have hc1 : (1 - r) / δ ≤ 1 := by rw [div_le_one hδ0]; linarith
        have hc0 : 0 ≤ (1 - r) / δ := div_nonneg (by linarith [hr.2]) hδ0.le
        have hχr : χ r = (1 - r) / δ := min_eq_right hc1
        have hin : r ∈ Ioi a := hgt
        rw [hev.deriv_eq, hd.deriv, hχr]
        simp only [hg, indicator_of_mem hin, hHc, hG]
        have h1c : (r - a) / δ = 1 - (1 - r) / δ := by rw [ha]; field_simp; ring
        rw [h1c]
        have key := pt_upper ((1 - r) / δ) (p.eval r / δ) ((derivative p).eval r)
          ((i : ℝ) ^ 2 * p.eval r ^ 2 / r ^ 2) r μ⁻¹ (p.eval r) δ hc0 hc1 (by positivity)
          hr.1.le hm0 rfl
        have e1 : (i : ℝ) ^ 2 * ((1 - r) / δ) ^ 2 * p.eval r ^ 2 / r ^ 2
            = ((1 - r) / δ) ^ 2 * ((i : ℝ) ^ 2 * p.eval r ^ 2 / r ^ 2) := by ring
        rw [e1]
        linarith [key]
    have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ a := by
      have := compl_mem_ae_iff.mpr (show (volume : Measure ℝ) {a} = 0 from measure_singleton a)
      filter_upwards [this] with r hr
      simpa using hr
    have hmain : axisFunctional i χ μ p ≤ ∫ r in Ioc (0 : ℝ) 1, g r := by
      unfold axisFunctional
      rw [intervalIntegral.integral_of_le zero_le_one]
      refine integral_mono_of_nonneg ?_ hgint ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        exact mul_nonneg (add_nonneg (by positivity) (mul_nonneg hm0 (by positivity))) hr.1.le
      · filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hne] with r hr hra
        exact hpt r hr hra
    have hset : Ioc (0 : ℝ) 1 ∩ Ioi a = Ioc a 1 := by
      rw [Ioc_inter_Ioi, sup_eq_right.2 (by linarith : (0 : ℝ) ≤ a)]
    have hgval : ∫ r in Ioc (0 : ℝ) 1, g r
        = 2 * μ⁻¹ * (∫ r in (0 : ℝ)..1, G r) + ∫ r in Ioc a 1, Hc r := by
      simp only [hg]
      rw [integral_add (hGint.const_mul _) (hHint.indicator measurableSet_Ioi), integral_const_mul,
        setIntegral_indicator measurableSet_Ioi, hset, intervalIntegral.integral_of_le zero_le_one]
    have hw : ∫ r in a..1, (((r - a) / δ) ^ 2 + 2 * μ⁻¹ / δ ^ 2) = δ / 3 + 2 * μ⁻¹ / δ := by
      have hF : ∀ x ∈ [[a, 1]], HasDerivAt (fun r => (r - a) ^ 3 / (3 * δ ^ 2) + 2 * μ⁻¹ / δ ^ 2 * r)
          (((x - a) / δ) ^ 2 + 2 * μ⁻¹ / δ ^ 2) x := by
        intro x _
        have := ((((hasDerivAt_id' x).sub_const a).pow 3).div_const (3 * δ ^ 2)).add
          ((hasDerivAt_id' x).const_mul (2 * μ⁻¹ / δ ^ 2))
        refine this.congr_deriv ?_
        simp only [Nat.reduceSub, Nat.cast_ofNat, mul_one, div_pow]
        field_simp
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
        (by apply Continuous.intervalIntegrable; fun_prop), ha]
      field_simp
      ring
    have hHb : ∫ r in Ioc a 1, Hc r ≤ (δ / 3 + 2 * μ⁻¹ / δ) * (4 * ((q : ℝ) + 1) ^ 2 * S) := by
      have hB := fun r (hr : r ∈ Ioc a 1) => sup_bound q p hp r (by linarith [hr.1]) hr.2
      calc ∫ r in Ioc a 1, Hc r
          ≤ ∫ r in Ioc a 1, (((r - a) / δ) ^ 2 + 2 * μ⁻¹ / δ ^ 2) * (4 * ((q : ℝ) + 1) ^ 2 * S) := by
            refine setIntegral_mono_on (hHcc.integrableOn_Icc.mono_set Ioc_subset_Icc_self) ?_
              measurableSet_Ioc ?_
            · exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioc_subset_Icc_self
            · intro r hr
              simp only [hHc]
              exact mul_le_mul_of_nonneg_left (hB r hr)
                (add_nonneg (sq_nonneg _) (div_nonneg (mul_nonneg zero_le_two hm0) (sq_nonneg _)))
        _ = (δ / 3 + 2 * μ⁻¹ / δ) * (4 * ((q : ℝ) + 1) ^ 2 * S) := by
            rw [integral_mul_const, ← intervalIntegral.integral_of_le ha1.le, hw]
    have hGb : ∫ r in (0 : ℝ)..1, G r ≤ M * S := hM i hi p hp hdiv
    have h6 : 2 * e ^ 2 / (Real.sqrt 6 * e) = Real.sqrt 6 * e / 3 := by
      rw [div_eq_iff (by positivity)]
      linear_combination (-(e ^ 2) / 3) * hs6
    have hkey : δ / 3 + 2 * μ⁻¹ / δ = 2 * Real.sqrt 6 * e / 3 := by
      rw [← he2, hδ, h6]; ring
    unfold axisClosed
    rw [← he]
    calc axisFunctional i χ μ p ≤ ∫ r in Ioc (0 : ℝ) 1, g r := hmain
      _ = 2 * μ⁻¹ * (∫ r in (0 : ℝ)..1, G r) + ∫ r in Ioc a 1, Hc r := hgval
      _ ≤ 2 * μ⁻¹ * (M * S) + (δ / 3 + 2 * μ⁻¹ / δ) * (4 * ((q : ℝ) + 1) ^ 2 * S) :=
          add_le_add (mul_le_mul_of_nonneg_left hGb (mul_nonneg zero_le_two hm0)) hHb
      _ = (8 * Real.sqrt 6 / 3 * ((q : ℝ) + 1) ^ 2 * e + 2 * M * μ⁻¹) * S := by
          rw [hkey]; ring

end Breakdown.CellCert.Spectral

end
