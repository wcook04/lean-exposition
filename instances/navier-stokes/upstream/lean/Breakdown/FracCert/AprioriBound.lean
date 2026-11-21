import Breakdown.FracCert.StHeldParts
import Breakdown.FracCert.StGradientAdd

open scoped ContDiff ENNReal
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace Breakdown

namespace SteadyCert

private lemma int_inner_two {A B : Space → Space} (hA : MemLp A 2 volume) (hB : MemLp B 2 volume) :
    Integrable (fun y => inner ℝ (A y) (B y)) volume := by
  have hA2 := (memLp_two_iff_integrable_sq_norm hA.1).1 hA
  have hB2 := (memLp_two_iff_integrable_sq_norm hB.1).1 hB
  refine Integrable.mono' ((hA2.add hB2).div_const 2) (hA.1.inner hB.1) ?_
  refine Eventually.of_forall (fun y => ?_)
  rw [Real.norm_eq_abs]
  have h1 := abs_real_inner_le_norm (A y) (B y)
  have h2 := two_mul_le_add_sq ‖A y‖ ‖B y‖
  simp only [Pi.add_apply]
  linarith

private lemma pair_le {A B : Space → Space} (hA : MemLp A 2 volume) (hB : MemLp B 2 volume) :
    l2Pair A B ≤ l2Norm A * l2Norm B := by
  have hA2 := (memLp_two_iff_integrable_sq_norm hA.1).1 hA
  have hB2 := (memLp_two_iff_integrable_sq_norm hB.1).1 hB
  have hprod : Integrable (fun y => ‖A y‖ * ‖B y‖) volume := by
    refine Integrable.mono' ((hA2.add hB2).div_const 2) (hA.1.norm.mul hB.1.norm) ?_
    refine Eventually.of_forall (fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h2 := two_mul_le_add_sq ‖A y‖ ‖B y‖
    simp only [Pi.add_apply]
    linarith
  have h1 : l2Pair A B ≤ ∫ y, ‖A y‖ * ‖B y‖ :=
    integral_mono (int_inner_two hA hB) hprod (fun y => real_inner_le_norm _ _)
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) Real.HolderConjugate.two_two
    (f := fun y => ‖A y‖) (g := fun y => ‖B y‖) (Eventually.of_forall fun y => norm_nonneg _)
    (Eventually.of_forall fun y => norm_nonneg _) (by simpa using hA.norm) (by simpa using hB.norm)
  simp only [Real.rpow_two] at hH
  unfold l2Norm
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  linarith

private lemma int_inner_loc {X e : Space → Space} (hX : AEStronglyMeasurable X volume)
    (hXl : IsLocalSquareIntegrable (fun y => ‖X y‖ ^ 2)) (he : MemLp e 2 volume)
    (hs : ∃ R : ℝ, ∀ y, R < ‖y‖ → e y = 0) :
    Integrable (fun y => inner ℝ (X y) (e y)) volume := by
  obtain ⟨R, hR⟩ := hs
  have he2 := (memLp_two_iff_integrable_sq_norm he.1).1 he
  have hK : Integrable ((Metric.closedBall (0 : Space) R).indicator (fun y => ‖X y‖ ^ 2)) volume :=
    (hXl _ (isCompact_closedBall 0 R)).integrable_indicator measurableSet_closedBall
  refine Integrable.mono' ((hK.add he2).div_const 2) (hX.inner he.1) ?_
  refine Eventually.of_forall (fun y => ?_)
  rw [Real.norm_eq_abs]
  by_cases hy : ‖y‖ ≤ R
  · have hm : y ∈ Metric.closedBall (0 : Space) R := by simpa using hy
    have h1 := abs_real_inner_le_norm (X y) (e y)
    have h2 := two_mul_le_add_sq ‖X y‖ ‖e y‖
    simp only [Pi.add_apply, Set.indicator_of_mem hm]
    linarith
  · have h0 : e y = 0 := hR y (lt_of_not_ge hy)
    have hnn : 0 ≤ (Metric.closedBall (0 : Space) R).indicator (fun y => ‖X y‖ ^ 2) y :=
      Set.indicator_nonneg (fun _ _ => by positivity) y
    rw [show inner ℝ (X y) (e y) = 0 by rw [h0, inner_zero_right], abs_zero]
    simp only [Pi.add_apply]
    have : 0 ≤ ‖e y‖ ^ 2 := by positivity
    linarith

private lemma pair_add {A B e : Space → Space} (hA : Integrable (fun y => inner ℝ (A y) (e y)) volume)
    (hB : Integrable (fun y => inner ℝ (B y) (e y)) volume) :
    l2Pair (fun y => A y + B y) e = l2Pair A e + l2Pair B e := by
  unfold l2Pair
  simp_rw [inner_add_left]
  exact integral_add hA hB

private lemma pair_sub {A B e : Space → Space} (hA : Integrable (fun y => inner ℝ (A y) (e y)) volume)
    (hB : Integrable (fun y => inner ℝ (B y) (e y)) volume) :
    l2Pair (fun y => A y - B y) e = l2Pair A e - l2Pair B e := by
  unfold l2Pair
  simp_rw [inner_sub_left]
  exact integral_sub hA hB

private lemma int_add {A B e : Space → Space} (hA : Integrable (fun y => inner ℝ (A y) (e y)) volume)
    (hB : Integrable (fun y => inner ℝ (B y) (e y)) volume) :
    Integrable (fun y => inner ℝ (A y + B y) (e y)) volume := by
  refine (hA.add hB).congr (Eventually.of_forall fun y => ?_)
  simp [inner_add_left]

private lemma int_sub {A B e : Space → Space} (hA : Integrable (fun y => inner ℝ (A y) (e y)) volume)
    (hB : Integrable (fun y => inner ℝ (B y) (e y)) volume) :
    Integrable (fun y => inner ℝ (A y - B y) (e y)) volume := by
  refine (hA.sub hB).congr (Eventually.of_forall fun y => ?_)
  simp [inner_sub_left]

private lemma wsum_tri {ι : Type*} [Fintype ι] (τ u v : ι → ℝ) (hτ : ∀ i, 0 ≤ τ i) :
    Real.sqrt (∑ i, τ i * (u i + v i) ^ 2) ≤
      Real.sqrt (∑ i, τ i * u i ^ 2) + Real.sqrt (∑ i, τ i * v i ^ 2) := by
  have hu : 0 ≤ ∑ i, τ i * u i ^ 2 := Finset.sum_nonneg (fun i _ => mul_nonneg (hτ i) (sq_nonneg _))
  have hv : 0 ≤ ∑ i, τ i * v i ^ 2 := Finset.sum_nonneg (fun i _ => mul_nonneg (hτ i) (sq_nonneg _))
  have hcs : (∑ i, τ i * u i * v i) ^ 2 ≤ (∑ i, τ i * u i ^ 2) * (∑ i, τ i * v i ^ 2) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (τ i) * u i)
      (fun i => Real.sqrt (τ i) * v i)
    have e1 : ∀ i, Real.sqrt (τ i) * u i * (Real.sqrt (τ i) * v i) = τ i * u i * v i := by
      intro i
      have := Real.mul_self_sqrt (hτ i)
      linear_combination (u i * v i) * this
    have e2 : ∀ (w : ι → ℝ) i, (Real.sqrt (τ i) * w i) ^ 2 = τ i * w i ^ 2 := by
      intro w i
      rw [mul_pow, Real.sq_sqrt (hτ i)]
    simp only [e1, e2] at this
    exact this
  have hc : ∑ i, τ i * u i * v i ≤ Real.sqrt (∑ i, τ i * u i ^ 2) * Real.sqrt (∑ i, τ i * v i ^ 2) := by
    rw [← Real.sqrt_mul hu]
    exact le_trans (le_abs_self _) (Real.abs_le_sqrt hcs)
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hexp : ∑ i, τ i * (u i + v i) ^ 2 =
      ∑ i, τ i * u i ^ 2 + 2 * ∑ i, τ i * u i * v i + ∑ i, τ i * v i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hexp, add_sq, Real.sq_sqrt hu, Real.sq_sqrt hv]
  linarith

private lemma wsum_neg {ι : Type*} [Fintype ι] (τ u : ι → ℝ) :
    Real.sqrt (∑ i, τ i * (-u i) ^ 2) = Real.sqrt (∑ i, τ i * u i ^ 2) := by
  simp only [neg_sq]

private lemma plane_tri (r s a b Y : ℝ) (hY : 0 ≤ Y) :
    (r + a * Y) ^ 2 + (s + b * Y) ^ 2 ≤ (Real.sqrt (r ^ 2 + s ^ 2) + Real.sqrt (a ^ 2 + b ^ 2) * Y) ^ 2 := by
  have h1 : (r * a + s * b) ^ 2 ≤ (r ^ 2 + s ^ 2) * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (r * b - s * a)]
  have h2 : r * a + s * b ≤ Real.sqrt (r ^ 2 + s ^ 2) * Real.sqrt (a ^ 2 + b ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact le_trans (le_abs_self _) (Real.abs_le_sqrt h1)
  have h3 := Real.sq_sqrt (show 0 ≤ r ^ 2 + s ^ 2 by positivity)
  have h4 := Real.sq_sqrt (show 0 ≤ a ^ 2 + b ^ 2 by positivity)
  have h5 : Y * (r * a + s * b) ≤ Y * (Real.sqrt (r ^ 2 + s ^ 2) * Real.sqrt (a ^ 2 + b ^ 2)) :=
    mul_le_mul_of_nonneg_left h2 hY
  have h6 : Real.sqrt (a ^ 2 + b ^ 2) ^ 2 * Y ^ 2 = (a ^ 2 + b ^ 2) * Y ^ 2 := by rw [h4]
  nlinarith [h3, h6, h5]

private lemma quad_solve (sc X W θ Y : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (h : Y ^ 2 ≤ sc * X * Y + (W + θ * Y) ^ 2) :
    Y ≤ (1 / 2) * ((sc * X + 2 * θ * W) / (1 - θ ^ 2)) +
      Real.sqrt ((1 / 4) * ((sc * X + 2 * θ * W) / (1 - θ ^ 2)) ^ 2 + W ^ 2 / (1 - θ ^ 2)) := by
  have hd : 0 < 1 - θ ^ 2 := by nlinarith
  set A := (sc * X + 2 * θ * W) / (1 - θ ^ 2) with hA
  have hA' : A * (1 - θ ^ 2) = sc * X + 2 * θ * W := by rw [hA]; field_simp
  have hB : W ^ 2 / (1 - θ ^ 2) * (1 - θ ^ 2) = W ^ 2 := by field_simp
  have key : (Y - (1 / 2) * A) ^ 2 ≤ (1 / 4) * A ^ 2 + W ^ 2 / (1 - θ ^ 2) := by
    have h' : (1 - θ ^ 2) * (Y ^ 2 - A * Y - W ^ 2 / (1 - θ ^ 2)) ≤ 0 := by
      have : (1 - θ ^ 2) * (Y ^ 2 - A * Y - W ^ 2 / (1 - θ ^ 2)) =
          Y ^ 2 - (sc * X * Y + (W + θ * Y) ^ 2) := by
        have e1 : (1 - θ ^ 2) * (A * Y) = (sc * X + 2 * θ * W) * Y := by rw [← hA']; ring
        have e2 : (1 - θ ^ 2) * (W ^ 2 / (1 - θ ^ 2)) = W ^ 2 := by rw [mul_comm]; exact hB
        linear_combination (-1 : ℝ) * e1 - e2
      rw [this]; linarith
    have : Y ^ 2 - A * Y - W ^ 2 / (1 - θ ^ 2) ≤ 0 := by
      by_contra hc
      push Not at hc
      have := mul_pos hd hc
      linarith
    nlinarith
  have := Real.abs_le_sqrt key
  linarith [le_abs_self (Y - (1 / 2) * A)]

private lemma sq_mul_le (u w : ℝ) (hu : 0 ≤ u) (hw : 0 ≤ w) : u ^ 2 * w ^ 2 ≤ u ^ 3 + w ^ 6 := by
  rcases le_total (w ^ 2) u with h | h
  · have : u ^ 2 * w ^ 2 ≤ u ^ 2 * u := mul_le_mul_of_nonneg_left h (by positivity)
    nlinarith [pow_nonneg hw 6]
  · have h2 : u ^ 2 ≤ (w ^ 2) ^ 2 := pow_le_pow_left₀ hu h 2
    have : u ^ 2 * w ^ 2 ≤ (w ^ 2) ^ 2 * w ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)
    nlinarith [pow_nonneg hu 3]

private lemma op_entry (L : Space →L[ℝ] Space) (x : Space) : ‖L x‖ ^ 2 ≤ entrySq L * ‖x‖ ^ 2 := by
  have hx : x = x 0 • unitVector 0 + x 1 • unitVector 1 + x 2 • unitVector 2 := by
    ext i
    fin_cases i <;> simp [unitVector]
  have hL : L x = x 0 • L (unitVector 0) + x 1 • L (unitVector 1) + x 2 • L (unitVector 2) := by
    conv_lhs => rw [hx]
    simp only [map_add, map_smul]
  have hn : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [Real.norm_eq_abs, sq_abs]
  have hb : ‖L x‖ ≤ |x 0| * ‖L (unitVector 0)‖ + |x 1| * ‖L (unitVector 1)‖ + |x 2| * ‖L (unitVector 2)‖ := by
    rw [hL]
    refine (norm_add₃_le).trans ?_
    simp only [norm_smul, Real.norm_eq_abs, le_refl]
  unfold entrySq
  rw [Fin.sum_univ_three, hn]
  have h0 : 0 ≤ ‖L x‖ := norm_nonneg _
  have hsq := pow_le_pow_left₀ h0 hb 2
  set a := |x 0|
  set b := |x 1|
  set c := |x 2|
  have ha : x 0 ^ 2 = a ^ 2 := (sq_abs _).symm
  have hb' : x 1 ^ 2 = b ^ 2 := (sq_abs _).symm
  have hc : x 2 ^ 2 = c ^ 2 := (sq_abs _).symm
  rw [ha, hb', hc]
  nlinarith [sq_nonneg (a * ‖L (unitVector 1)‖ - b * ‖L (unitVector 0)‖),
    sq_nonneg (a * ‖L (unitVector 2)‖ - c * ‖L (unitVector 0)‖),
    sq_nonneg (b * ‖L (unitVector 2)‖ - c * ‖L (unitVector 1)‖)]


private lemma trace_cont : Continuous (fun L : Space →L[ℝ] Space →L[ℝ] Space => secondTrace L) := by
  unfold secondTrace
  exact continuous_finsetSum _
    (fun j _ => (continuous_id.clm_apply continuous_const).clm_apply continuous_const)

private lemma trace_two {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : IsSecondOrderField m v G H) :
    MemLp (fun y => secondTrace (H y)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => secondTrace (H y)) volume :=
    trace_cont.comp_aestronglyMeasurable h.measurable_second
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  refine Integrable.mono' (h.second_two.const_mul 3) (hm.norm.pow 2) ?_
  refine Eventually.of_forall (fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  unfold secondTrace
  simp only [Fin.sum_univ_three]
  have t := norm_add₃_le (a := H y (unitVector 0) (unitVector 0)) (b := H y (unitVector 1) (unitVector 1))
    (c := H y (unitVector 2) (unitVector 2))
  have t2 := pow_le_pow_left₀ (norm_nonneg _) t 2
  nlinarith [sq_nonneg (‖H y (unitVector 0) (unitVector 0)‖ - ‖H y (unitVector 1) (unitVector 1)‖),
    sq_nonneg (‖H y (unitVector 0) (unitVector 0)‖ - ‖H y (unitVector 2) (unitVector 2)‖),
    sq_nonneg (‖H y (unitVector 1) (unitVector 1)‖ - ‖H y (unitVector 2) (unitVector 2)‖),
    sq_nonneg ‖H y (unitVector 0) (unitVector 1)‖, sq_nonneg ‖H y (unitVector 0) (unitVector 2)‖,
    sq_nonneg ‖H y (unitVector 1) (unitVector 0)‖, sq_nonneg ‖H y (unitVector 1) (unitVector 2)‖,
    sq_nonneg ‖H y (unitVector 2) (unitVector 0)‖, sq_nonneg ‖H y (unitVector 2) (unitVector 1)‖]

private lemma sym_two {k N : ℕ} {α : ℝ} {d : FracCertData k N} (hd : IsFracCert α d) {p : Fin k → ℝ}
    (hp : p ∈ box d.radius) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : IsSecondOrderField m v G H) :
    MemLp (symProduct (d.profile p) (d.gradProfile p) v G) 2 volume := by
  obtain ⟨C, hC⟩ := hd.profile_bounds
  have hC0 : 0 ≤ C := by
    have := (hC p hp 0).1
    simp only [norm_zero, add_zero, Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  have hW : Continuous (d.profile p) := (hd.profile_smooth p hp).continuous
  have hDW : Continuous (d.gradProfile p) := (hd.profile_smooth p hp).continuous_fderiv (by norm_num)
  have happ : Continuous (fun q : (Space →L[ℝ] Space) × Space => q.1 q.2) :=
    continuous_fst.clm_apply continuous_snd
  have m1 : AEStronglyMeasurable (fun y => G y (d.profile p y)) volume :=
    happ.comp_aestronglyMeasurable (h.measurable_gradient.prodMk hW.aestronglyMeasurable)
  have m2 : AEStronglyMeasurable (fun y => d.gradProfile p y (v y)) volume :=
    happ.comp_aestronglyMeasurable (hDW.aestronglyMeasurable.prodMk h.measurable_velocity)
  have i1 : MemLp (fun y => G y (d.profile p y)) 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm m1).2 ?_
    refine Integrable.mono' (h.gradient_two.const_mul (C ^ 2)) (m1.norm.pow 2) ?_
    refine Eventually.of_forall (fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hWy : ‖d.profile p y‖ ≤ C := by
      have h1 := (hC p hp y).1
      have h2 : (1 + ‖y‖) ^ (-(1 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by norm_num)
      have h3 : 0 ≤ (1 + ‖y‖) ^ (-(1 : ℝ)) := Real.rpow_nonneg (by positivity) _
      nlinarith
    have e1 := op_entry (G y) (d.profile p y)
    have e0 : 0 ≤ entrySq (G y) := Finset.sum_nonneg (fun i _ => by positivity)
    have e2 := pow_le_pow_left₀ (norm_nonneg _) hWy 2
    have e3 := mul_le_mul_of_nonneg_left e2 e0
    nlinarith
  have i2 : MemLp (fun y => d.gradProfile p y (v y)) 2 volume := by
    have hv6 : Integrable (fun y => ‖v y‖ ^ 6) volume := by
      have : MemLp v ((6 : ℕ) : ℝ≥0∞) volume := by exact_mod_cast h.velocity_six
      exact this.integrable_norm_pow (by norm_num)
    have hw6 : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(6 : ℝ))) volume := by
      apply integrable_one_add_norm
      norm_num [finrank_euclideanSpace]
    refine (memLp_two_iff_integrable_sq_norm m2).2 ?_
    refine Integrable.mono' ((hw6.add hv6).const_mul (C ^ 2)) (m2.norm.pow 2) ?_
    refine Eventually.of_forall (fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hu0 : 0 ≤ (1 + ‖y‖) ^ (-(2 : ℝ)) := Real.rpow_nonneg (by positivity) _
    have hu3 : (1 + ‖y‖) ^ (-(6 : ℝ)) = ((1 + ‖y‖) ^ (-(2 : ℝ))) ^ 3 := by
      rw [← Real.rpow_mul_natCast (by positivity)]
      norm_num
    have hb : ‖d.gradProfile p y (v y)‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) * ‖v y‖ :=
      ((d.gradProfile p y).le_opNorm (v y)).trans
        (mul_le_mul_of_nonneg_right (hC p hp y).2.1 (norm_nonneg _))
    have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hsm := sq_mul_le ((1 + ‖y‖) ^ (-(2 : ℝ))) ‖v y‖ hu0 (norm_nonneg _)
    simp only [Pi.add_apply]
    rw [hu3]
    have e1 : (C * (1 + ‖y‖) ^ (-(2 : ℝ)) * ‖v y‖) ^ 2 =
        C ^ 2 * (((1 + ‖y‖) ^ (-(2 : ℝ))) ^ 2 * ‖v y‖ ^ 2) := by ring
    rw [e1] at hb2
    have e2 := mul_le_mul_of_nonneg_left hsm (sq_nonneg C)
    linarith
  have e : symProduct (d.profile p) (d.gradProfile p) v G =
      fun y => (1 / 2 : ℝ) • (G y (d.profile p y) + d.gradProfile p y (v y)) := rfl
  rw [e]
  exact (i1.add i2).const_smul (1 / 2 : ℝ)

private lemma local_two {k N : ℕ} {α : ℝ} {d : FracCertData k N} (hd : IsFracCert α d) {p : Fin k → ℝ}
    (hp : p ∈ box d.radius) {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {P : Space → Space}
    (hs : d.IsLinearState α p v G H P) (κ : Fin k → ℝ) :
    MemLp (d.localField α p v G H κ) 2 volume := by
  have hT := trace_two hs.second
  have hS := sym_two hd hp hs.second
  have hA : MemLp (fun y => ∑ i, κ i • d.actuator i y) 2 volume :=
    memLp_finsetSum Finset.univ (fun i _ => (hd.actuator_two i).const_smul (κ i))
  exact ((hs.drift.sub (hT.const_smul d.splitVisc)).add (hS.const_smul (2 : ℝ))).add hA


private lemma rows_tri {k N : ℕ} (d : FracCertData k N) (hτ : ∀ a, 0 ≤ d.rowWeight a)
    {X A B C : Space → Space} (hX : X = fun y => A y - B y - C y)
    (hA : ∀ a, Integrable (fun y => inner ℝ (A y) (d.row a y)) volume)
    (hB : ∀ a, Integrable (fun y => inner ℝ (B y) (d.row a y)) volume)
    (hC : ∀ a, Integrable (fun y => inner ℝ (C y) (d.row a y)) volume) :
    d.rows X ≤ d.rows A + d.rows B + d.rows C := by
  have hp : ∀ a, l2Pair X (d.row a) =
      l2Pair A (d.row a) + (-l2Pair B (d.row a)) + (-l2Pair C (d.row a)) := by
    intro a
    subst hX
    unfold l2Pair
    simp_rw [inner_sub_left]
    rw [integral_sub, integral_sub]
    · ring
    · exact hA a
    · exact hB a
    · exact (hA a).sub (hB a)
    · exact hC a
  unfold FracCertData.rows rowSize
  simp only [hp]
  have t1 := wsum_tri d.rowWeight (fun a => l2Pair A (d.row a) + -l2Pair B (d.row a))
    (fun a => -l2Pair C (d.row a)) hτ
  have t2 := wsum_tri d.rowWeight (fun a => l2Pair A (d.row a)) (fun a => -l2Pair B (d.row a)) hτ
  rw [wsum_neg] at t1 t2
  linarith

private lemma vec_tri {k : ℕ} (u w : Fin k → ℝ) :
    vecNorm (fun i => u i + w i) ≤ vecNorm u + vecNorm w := by
  have := wsum_tri (fun _ => (1 : ℝ)) u w (fun _ => zero_le_one)
  simpa [vecNorm] using this

private lemma grad_zero : IsGradientField (fun _ => (0 : Space)) := by
  refine ⟨fun _ => 0, fun K _ => by simp, fun K _ => by simp, aestronglyMeasurable_const, ?_⟩
  intro φ _ j
  simp

private lemma grad_neg {Q : Space → Space} (hQ : IsGradientField Q) : IsGradientField (fun y => -Q y) := by
  obtain ⟨q, hq, hQ2, hm, hw⟩ := hQ
  refine ⟨fun y => -q y, by simpa using hq, by simpa using hQ2, hm.neg, ?_⟩
  intro φ hφ j
  simp only [mul_neg, inner_neg_left, integral_neg, hw φ hφ j]

private lemma grad_parts {Q : Space → Space} (hQ : IsGradientField Q) :
    AEStronglyMeasurable Q volume ∧ IsLocalSquareIntegrable (fun y => ‖Q y‖ ^ 2) := by
  obtain ⟨q, _, hQ2, hm, _⟩ := hQ
  exact ⟨hm, hQ2⟩

private lemma chain (Z S β cr lowL g sc T coer potL mForm locPair fPair r1 r2 Rw Pn z t rowL sb pinL : ℝ)
    (hgdef : g = cr - lowL) (hSZ : S ≤ Z ^ 2) (hcr : 0 < cr) (hlow : 0 ≤ lowL)
    (hg : 0 < g) (hβ1 : -lowL * S ≤ β) (hβ2 : 0 ≤ β + cr * S)
    (hT : Real.sqrt T ≤ sc * Real.sqrt (β + cr * S)) (hsc : 0 ≤ sc) (hcoer : cr ≤ coer - potL)
    (hlower : coer * Z ^ 2 ≤ mForm + Rw ^ 2 + t * Pn ^ 2) (hform : mForm - potL * Z ^ 2 ≤ locPair)
    (hsplit : fPair = locPair + β) (hpair : fPair ≤ r1 * Real.sqrt T) (hr1 : 0 ≤ r1)
    (hRw : Rw ≤ r2 + rowL * Z + sb * Real.sqrt (β + cr * S)) (hRw0 : 0 ≤ Rw)
    (hrowL : 0 ≤ rowL) (hsb : 0 ≤ sb) (hPn : Pn ≤ z + pinL * Z) (hPn0 : 0 ≤ Pn)
    (hpinL : 0 ≤ pinL) (ht : 0 < t) :
    Real.sqrt g * Z ≤ Real.sqrt (cr * Z ^ 2 + β) ∧
    Real.sqrt (cr * Z ^ 2 + β) ^ 2 ≤ sc * r1 * Real.sqrt (cr * Z ^ 2 + β) +
      (Real.sqrt (r2 ^ 2 + t * z ^ 2) + Real.sqrt ((sb + rowL / Real.sqrt g) ^ 2
        + t * pinL ^ 2 / g) * Real.sqrt (cr * Z ^ 2 + β)) ^ 2 := by
  subst hgdef
  have hYa : 0 ≤ cr * Z ^ 2 + β := by nlinarith
  have hsg0 : 0 < Real.sqrt (cr - lowL) := Real.sqrt_pos.2 hg
  have hsg2 : Real.sqrt (cr - lowL) ^ 2 = cr - lowL := Real.sq_sqrt hg.le
  have hZY : Real.sqrt (cr - lowL) * Z ≤ Real.sqrt (cr * Z ^ 2 + β) := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, hsg2]
    nlinarith
  refine ⟨hZY, ?_⟩
  have hY0 : 0 ≤ Real.sqrt (cr * Z ^ 2 + β) := Real.sqrt_nonneg _
  have hYsq : Real.sqrt (cr * Z ^ 2 + β) ^ 2 = cr * Z ^ 2 + β := Real.sq_sqrt hYa
  have hY0Y : Real.sqrt (β + cr * S) ≤ Real.sqrt (cr * Z ^ 2 + β) := Real.sqrt_le_sqrt (by nlinarith)
  generalize Real.sqrt (cr * Z ^ 2 + β) = Y at hZY hY0 hYsq hY0Y ⊢
  generalize Real.sqrt (β + cr * S) = Y0 at hT hRw hY0Y
  have hZ' : Z ≤ Y / Real.sqrt (cr - lowL) := by rw [le_div_iff₀ hsg0]; linarith
  have hs2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hb1 : (Real.sqrt t * pinL / Real.sqrt (cr - lowL)) ^ 2 = t * pinL ^ 2 / (cr - lowL) := by
    rw [div_pow, mul_pow, hs2, hsg2]
  have hR1 : Rw ≤ r2 + (sb + rowL / Real.sqrt (cr - lowL)) * Y := by
    have e1 : rowL * Z ≤ rowL / Real.sqrt (cr - lowL) * Y := by
      calc rowL * Z ≤ rowL * (Y / Real.sqrt (cr - lowL)) := mul_le_mul_of_nonneg_left hZ' hrowL
        _ = rowL / Real.sqrt (cr - lowL) * Y := by ring
    have e2 : sb * Y0 ≤ sb * Y := mul_le_mul_of_nonneg_left hY0Y hsb
    have e3 : (sb + rowL / Real.sqrt (cr - lowL)) * Y = sb * Y + rowL / Real.sqrt (cr - lowL) * Y := by ring
    rw [e3]
    linarith
  have hP1 : t * Pn ^ 2 ≤ (Real.sqrt t * z + Real.sqrt t * pinL / Real.sqrt (cr - lowL) * Y) ^ 2 := by
    have e1 : pinL * Z ≤ pinL / Real.sqrt (cr - lowL) * Y := by
      calc pinL * Z ≤ pinL * (Y / Real.sqrt (cr - lowL)) := mul_le_mul_of_nonneg_left hZ' hpinL
        _ = pinL / Real.sqrt (cr - lowL) * Y := by ring
    have e2 : Pn ≤ z + pinL / Real.sqrt (cr - lowL) * Y := by linarith
    have e3 := pow_le_pow_left₀ hPn0 e2 2
    have e4 : (Real.sqrt t * z + Real.sqrt t * pinL / Real.sqrt (cr - lowL) * Y) ^ 2 =
        t * (z + pinL / Real.sqrt (cr - lowL) * Y) ^ 2 := by
      have e5 : (Real.sqrt t * z + Real.sqrt t * pinL / Real.sqrt (cr - lowL) * Y) ^ 2 =
          Real.sqrt t ^ 2 * (z + pinL / Real.sqrt (cr - lowL) * Y) ^ 2 := by ring
      rw [e5, hs2]
    rw [e4]; exact mul_le_mul_of_nonneg_left e3 ht.le
  have hR2 := pow_le_pow_left₀ hRw0 hR1 2
  have hF : fPair ≤ sc * r1 * Y := by
    have e1 : Real.sqrt T ≤ sc * Y := hT.trans (mul_le_mul_of_nonneg_left hY0Y hsc)
    have e2 := mul_le_mul_of_nonneg_left e1 hr1
    have e3 : r1 * (sc * Y) = sc * r1 * Y := by ring
    linarith [hpair, e2, e3]
  have hmain : Y ^ 2 ≤ sc * r1 * Y + (r2 + (sb + rowL / Real.sqrt (cr - lowL)) * Y) ^ 2 +
      (Real.sqrt t * z + Real.sqrt t * pinL / Real.sqrt (cr - lowL) * Y) ^ 2 := by
    have e1 : cr * Z ^ 2 ≤ coer * Z ^ 2 - potL * Z ^ 2 := by
      rw [← sub_mul]; exact mul_le_mul_of_nonneg_right hcoer (sq_nonneg Z)
    linarith [hYsq, e1, hlower, hform, hsplit, hF, hR2, hP1]
  have hm := plane_tri r2 (Real.sqrt t * z) (sb + rowL / Real.sqrt (cr - lowL))
    (Real.sqrt t * pinL / Real.sqrt (cr - lowL)) Y hY0
  have e5 : (Real.sqrt t * z) ^ 2 = t * z ^ 2 := by rw [mul_pow, hs2]
  rw [e5, hb1] at hm
  linarith


theorem aprioriBound (_h1 : DriftEnergyStatement) (h2 : SplitFormBoundsStatement)
    (h3 : GradientOrthogonalStatement) (h4 : SecondTraceSolenoidalStatement)
    (hG : GradientAddStatement) : AprioriBoundStatement := by
  intro α hα1 hα2 k N d hd p hp v G H P hs κ
  have hsec := hs.second
  have hpow := hs.power
  have hT2 := trace_two hsec
  have hloc := local_two hd hp hs κ
  have hspl : MemLp (d.splitField P H) 2 volume := hpow.1.add (hT2.const_smul d.splitVisc)
  have hfull : MemLp (d.fullField α p v G H P κ) 2 volume := hloc.add hspl
  obtain ⟨hsol, -⟩ := h4 d.order v G H hsec
  have hAv : MemLp (negSecondTrace H) 2 volume := hsol.1
  have hent0 : ∀ y, 0 ≤ entrySq (G y) := fun y => Finset.sum_nonneg (fun i _ => by positivity)
  have hwint : Integrable (fun y => d.weight y * entrySq (G y)) volume := by
    refine hsec.gradient_two.bdd_mul (c := d.weightMax) hd.weight_measurable.aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hd.weightMin_pos (hd.weight_lower y))]
    exact hd.weight_upper y
  have hT0 : 0 ≤ ∫ y, ‖secondTrace (H y)‖ ^ 2 := integral_nonneg (fun y => by positivity)
  have hEnt0 : 0 ≤ ∫ y, entrySq (G y) := integral_nonneg hent0
  have hwE : d.weightMin * ∫ y, entrySq (G y) ≤ ∫ y, d.weight y * entrySq (G y) := by
    rw [← integral_const_mul]
    exact integral_mono (hsec.gradient_two.const_mul _) hwint
      (fun y => mul_le_mul_of_nonneg_right (hd.weight_lower y) (hent0 y))
  have hS0 : 0 ≤ (∫ y, ‖secondTrace (H y)‖ ^ 2) + d.weightMin * ∫ y, entrySq (G y) :=
    add_nonneg hT0 (mul_nonneg hd.weightMin_pos.le hEnt0)
  have hEn : (∫ y, ‖secondTrace (H y)‖ ^ 2) + d.weightMin * ∫ y, entrySq (G y) ≤ d.energy G H := by
    show _ ≤ (∫ y, ‖secondTrace (H y)‖ ^ 2) + ∫ y, d.weight y * entrySq (G y)
    linarith
  have hκ0 : 0 ≤ d.multiplierScale ^ 2 * ∑ i, κ i ^ 2 := by positivity
  have hZsq : d.size G H κ ^ 2 = d.energy G H + d.multiplierScale ^ 2 * ∑ i, κ i ^ 2 :=
    Real.sq_sqrt (add_nonneg (hS0.trans hEn) hκ0)
  have hSZ : (∫ y, ‖secondTrace (H y)‖ ^ 2) + d.weightMin * ∫ y, entrySq (G y) ≤ d.size G H κ ^ 2 := by
    rw [hZsq]; linarith
  have hZ0 : 0 ≤ d.size G H κ := Real.sqrt_nonneg _
  have hlow : 0 ≤ d.lowLoss := by
    have hb := hd.lowLoss_bound 1 one_pos
    have h0 : 0 ≤ max (d.splitVisc - (1 : ℝ) ^ (2 * (α - 1))) 0 := le_max_right _ _
    have hw := hd.weightMin_pos
    by_contra hc
    push Not at hc
    have : d.lowLoss * (1 + d.weightMin / 1 ^ 2) < 0 := mul_neg_of_neg_of_pos hc (by positivity)
    linarith
  obtain ⟨hβ1, hβ2, hTb⟩ := h2 α hα1 hα2 d hd v G H P hsec hpow
  obtain ⟨_, hl2, hl3⟩ := hd.losses_nonneg
  have hsplit : l2Pair (d.fullField α p v G H P κ) (negSecondTrace H) =
      l2Pair (d.localField α p v G H κ) (negSecondTrace H) + l2Pair (d.splitField P H) (negSecondTrace H) :=
    pair_add (int_inner_two hloc hAv) (int_inner_two hspl hAv)
  have hAvn : l2Norm (negSecondTrace H) = Real.sqrt (∫ y, ‖secondTrace (H y)‖ ^ 2) := by
    simp [l2Norm, negSecondTrace, norm_neg]
  have hpairQ : ∀ Q, IsGradientField Q → MemLp (fun y => d.fullField α p v G H P κ y + Q y) 2 volume →
      l2Pair (d.fullField α p v G H P κ) (negSecondTrace H) ≤
        l2Norm (fun y => d.fullField α p v G H P κ y + Q y) * Real.sqrt (∫ y, ‖secondTrace (H y)‖ ^ 2) := by
    intro Q hQ hfQ
    have hQ2 : MemLp Q 2 volume := by
      have e : Q = (fun y => d.fullField α p v G H P κ y + Q y) - d.fullField α p v G H P κ := by
        funext y
        simp
      rw [e]
      exact hfQ.sub hfull
    have h0 := h3 Q (negSecondTrace H) hQ hQ2 hsol
    have e : l2Pair (fun y => (d.fullField α p v G H P κ y + Q y) - Q y) (negSecondTrace H) =
        l2Pair (fun y => d.fullField α p v G H P κ y + Q y) (negSecondTrace H) - l2Pair Q (negSecondTrace H) :=
      pair_sub (int_inner_two hfQ hAv) (int_inner_two hQ2 hAv)
    simp only [add_sub_cancel_right] at e
    have e2 : l2Pair Q (negSecondTrace H) = 0 := h0
    rw [← hAvn]
    have := pair_le hfQ hAv
    linarith
  have hrowInt : ∀ X : Space → Space, AEStronglyMeasurable X volume →
      IsLocalSquareIntegrable (fun y => ‖X y‖ ^ 2) →
      ∀ a, Integrable (fun y => inner ℝ (X y) (d.row a y)) volume :=
    fun X hX hXl a => int_inner_loc hX hXl (hd.row_two a) (hd.row_support a)
  have hrowL2 : ∀ X : Space → Space, MemLp X 2 volume →
      ∀ a, Integrable (fun y => inner ℝ (X y) (d.row a y)) volume :=
    fun X hX a => int_inner_two hX (hd.row_two a)
  obtain ⟨Q', hQ'g, hQ'⟩ := hd.model_field p hp v G H hsec P hpow hs.drift κ
  obtain ⟨hmF1, hmF2⟩ := hd.model_regular p hp v G H hsec κ
  have hrowsQ : ∀ R, IsGradientField R →
      d.rows (fun y => d.modelField p v κ y + (R y + -Q' y)) ≤
        d.rows (fun y => d.fullField α p v G H P κ y + R y) + d.rowLoss * d.size G H κ +
          d.splitBound * d.splitEnergy P G H := by
    intro R hR
    obtain ⟨hRm, hRl⟩ := grad_parts hR
    obtain ⟨hQm, hQl⟩ := grad_parts hQ'g
    have t := rows_tri d (fun a => (hd.rowWeight_pos a).le)
      (X := fun y => d.modelField p v κ y + (R y + -Q' y))
      (A := fun y => d.fullField α p v G H P κ y + R y)
      (B := fun y => d.localField α p v G H κ y - d.modelField p v κ y + Q' y)
      (C := d.splitField P H)
      (by funext y; simp only [FracCertData.fullField]; abel)
      (fun a => int_add (hrowL2 _ hfull a) (hrowInt R hRm hRl a))
      (fun a => int_add (int_sub (hrowL2 _ hloc a) (hrowInt _ hmF1 hmF2 a)) (hrowInt Q' hQm hQl a))
      (fun a => hrowL2 _ hspl a)
    have := hd.split_rows v G H hsec P hpow
    linarith
  have hPn : vecNorm (d.modelPin p v) ≤ vecNorm (d.pins G) + d.pinLoss * d.size G H κ := by
    have e : d.modelPin p v = fun i => d.pins G i + (d.modelPin p v i - d.pins G i) := by
      funext i; ring
    rw [e]
    exact (vec_tri _ _).trans (by linarith [hd.model_pin p hp v G H hsec P hpow hs.drift κ])
  have hPsq : vecNorm (d.modelPin p v) ^ 2 = ∑ i, d.modelPin p v i ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hbase : ∀ Q1 R, IsGradientField Q1 → MemLp (fun y => d.fullField α p v G H P κ y + Q1 y) 2 volume →
      IsGradientField R →
      Real.sqrt d.reducedGap * d.size G H κ ≤ (Real.sqrt (d.reducedCoercivity * d.size G H κ ^ 2 + l2Pair (d.splitField P H) (negSecondTrace H))) ∧
      (Real.sqrt (d.reducedCoercivity * d.size G H κ ^ 2 + l2Pair (d.splitField P H) (negSecondTrace H))) ^ 2 ≤ d.formScale * l2Norm (fun y => d.fullField α p v G H P κ y + Q1 y) * (Real.sqrt (d.reducedCoercivity * d.size G H κ ^ 2 + l2Pair (d.splitField P H) (negSecondTrace H))) +
        (Real.sqrt (d.rows (fun y => d.fullField α p v G H P κ y + R y) ^ 2 + d.pinWeight * vecNorm (d.pins G) ^ 2) +
          d.contraction * (Real.sqrt (d.reducedCoercivity * d.size G H κ ^ 2 + l2Pair (d.splitField P H) (negSecondTrace H)))) ^ 2 := by
    intro Q1 R hQ1 hfQ1 hR
    have hQc : IsGradientField (fun y => R y + -Q' y) := hG R (fun y => -Q' y) hR (grad_neg hQ'g)
    have hlow' := hd.model_lower p hp v G H hsec κ _ hQc
    rw [← hPsq] at hlow'
    exact chain (d.size G H κ) _ (l2Pair (d.splitField P H) (negSecondTrace H)) d.reducedCoercivity
      d.lowLoss d.reducedGap d.formScale (∫ y, ‖secondTrace (H y)‖ ^ 2) d.coercivity d.potLoss
      (d.modelForm p v κ) (l2Pair (d.localField α p v G H κ) (negSecondTrace H))
      (l2Pair (d.fullField α p v G H P κ) (negSecondTrace H)) (l2Norm (fun y => d.fullField α p v G H P κ y + Q1 y))
      (d.rows (fun y => d.fullField α p v G H P κ y + R y)) (d.rows (fun y => d.modelField p v κ y + (R y + -Q' y)))
      (vecNorm (d.modelPin p v)) (vecNorm (d.pins G)) d.pinWeight d.rowLoss d.splitBound d.pinLoss
      rfl hSZ hd.reduced_pos hlow hd.reducedGap_pos hβ1 hβ2 hTb hd.formScale_nonneg hd.reduced_le
      hlow' (hd.model_form p hp v G H hsec P hpow hs.drift κ) hsplit (hpairQ Q1 hQ1 hfQ1)
      (Real.sqrt_nonneg _) (hrowsQ R hR) (Real.sqrt_nonneg _) hl2 hd.splitBound_nonneg hPn
      (Real.sqrt_nonneg _) hl3 hd.pinWeight_pos
  have hfull0 : MemLp (fun y => d.fullField α p v G H P κ y + (fun _ => (0 : Space)) y) 2 volume := by simpa using hfull
  have hne1 : {r | ∃ Q, IsGradientField Q ∧ MemLp (fun y => d.fullField α p v G H P κ y + Q y) 2 volume ∧
      r = l2Norm (fun y => d.fullField α p v G H P κ y + Q y)}.Nonempty := ⟨_, fun _ => 0, grad_zero, hfull0, rfl⟩
  have hbd1 : BddBelow {r | ∃ Q, IsGradientField Q ∧ MemLp (fun y => d.fullField α p v G H P κ y + Q y) 2 volume ∧
      r = l2Norm (fun y => d.fullField α p v G H P κ y + Q y)} := by
    refine ⟨0, fun r hr => ?_⟩
    obtain ⟨Q, _, _, e⟩ := hr
    rw [e]
    exact Real.sqrt_nonneg _
  have hne2 : {r | ∃ Q, IsGradientField Q ∧ r = rowSize d.row d.rowWeight (fun y => d.fullField α p v G H P κ y + Q y)}.Nonempty :=
    ⟨_, fun _ => 0, grad_zero, rfl⟩
  have hbd2 : BddBelow {r | ∃ Q, IsGradientField Q ∧ r = rowSize d.row d.rowWeight (fun y => d.fullField α p v G H P κ y + Q y)} := by
    refine ⟨0, fun r hr => ?_⟩
    obtain ⟨Q, _, e⟩ := hr
    rw [e]
    exact Real.sqrt_nonneg _
  obtain ⟨u1, -, hu1, hm1⟩ := exists_seq_tendsto_sInf hne1 hbd1
  obtain ⟨u2, -, hu2, hm2⟩ := exists_seq_tendsto_sInf hne2 hbd2
  have hu1' : Tendsto u1 atTop (𝓝 (projectedNorm (d.fullField α p v G H P κ))) := hu1
  have hu2' : Tendsto u2 atTop (𝓝 (d.rowsModGrad (d.fullField α p v G H P κ))) := hu2
  have hZY := (hbase _ _ grad_zero hfull0 grad_zero).1
  have hineq : ∀ n, (Real.sqrt (d.reducedCoercivity * d.size G H κ ^ 2 + l2Pair (d.splitField P H) (negSecondTrace H))) ^ 2 ≤ d.formScale * u1 n * (Real.sqrt (d.reducedCoercivity * d.size G H κ ^ 2 + l2Pair (d.splitField P H) (negSecondTrace H))) +
      (Real.sqrt (u2 n ^ 2 + d.pinWeight * vecNorm (d.pins G) ^ 2) + d.contraction * (Real.sqrt (d.reducedCoercivity * d.size G H κ ^ 2 + l2Pair (d.splitField P H) (negSecondTrace H)))) ^ 2 := by
    intro n
    obtain ⟨Q1, hQ1, hfQ1, e1⟩ := hm1 n
    obtain ⟨R, hR, e2⟩ := hm2 n
    rw [e1, e2]
    exact (hbase Q1 R hQ1 hfQ1 hR).2
  have hlim : Tendsto (fun n => d.formScale * u1 n * (Real.sqrt (d.reducedCoercivity * d.size G H κ ^ 2 + l2Pair (d.splitField P H) (negSecondTrace H))) +
      (Real.sqrt (u2 n ^ 2 + d.pinWeight * vecNorm (d.pins G) ^ 2) + d.contraction * (Real.sqrt (d.reducedCoercivity * d.size G H κ ^ 2 + l2Pair (d.splitField P H) (negSecondTrace H)))) ^ 2) atTop
      (𝓝 (d.formScale * projectedNorm (d.fullField α p v G H P κ) * (Real.sqrt (d.reducedCoercivity * d.size G H κ ^ 2 + l2Pair (d.splitField P H) (negSecondTrace H))) +
        (Real.sqrt (d.rowsModGrad (d.fullField α p v G H P κ) ^ 2 + d.pinWeight * vecNorm (d.pins G) ^ 2) +
          d.contraction * (Real.sqrt (d.reducedCoercivity * d.size G H κ ^ 2 + l2Pair (d.splitField P H) (negSecondTrace H)))) ^ 2)) :=
    ((hu1'.const_mul _).mul_const _).add
      ((((hu2'.pow 2).add_const _).sqrt.add_const _).pow 2)
  have hfin := ge_of_tendsto' hlim hineq
  have hq := quad_solve d.formScale (projectedNorm (d.fullField α p v G H P κ))
    (Real.sqrt (d.rowsModGrad (d.fullField α p v G H P κ) ^ 2 + d.pinWeight * vecNorm (d.pins G) ^ 2)) d.contraction (Real.sqrt (d.reducedCoercivity * d.size G H κ ^ 2 + l2Pair (d.splitField P H) (negSecondTrace H)))
    (Real.sqrt_nonneg _) hd.contraction_lt hfin
  have hgpos := hd.reducedGap_pos
  have hsg : 0 < Real.sqrt d.reducedGap := Real.sqrt_pos.2 hgpos
  unfold FracCertData.boundFn boundConst
  rw [Real.rpow_neg hgpos.le, ← Real.sqrt_eq_rpow]
  have e0 : Real.sqrt (d.rowsModGrad (d.fullField α p v G H P κ) ^ 2 + d.pinWeight * vecNorm (d.pins G) ^ 2) ^ 2 +
      d.pinWeight * (0 : ℝ) ^ 2 =
      Real.sqrt (d.rowsModGrad (d.fullField α p v G H P κ) ^ 2 + d.pinWeight * vecNorm (d.pins G) ^ 2) ^ 2 := by ring
  rw [e0, inv_mul_eq_div, le_div_iff₀ hsg]
  linarith [hZY, hq, mul_comm (d.size G H κ) (Real.sqrt d.reducedGap)]

end SteadyCert

end Breakdown
