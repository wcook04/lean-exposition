import Breakdown.Frac.StTorusCoef
import Breakdown.Torus.CoefCalculus

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Periodic

namespace TorusSymmetry.Internal

theorem periodic_int_smul {E : Type*} {f : Space → E} (hp : IsPeriodic f) (i : Fin 3) (m : ℤ)
    (x : Space) : f (x + (m : ℝ) • unitVector i) = f x := by
  induction m using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    calc f (x + ((n + 1 : ℤ) : ℝ) • unitVector i)
          = f ((x + ((n : ℤ) : ℝ) • unitVector i) + unitVector i) := by
          congr 1
          push_cast
          rw [add_smul, one_smul, add_assoc]
      _ = f x := by rw [hp i, ih]
  | pred n ih =>
    rw [← hp i]
    convert ih x using 2
    push_cast
    rw [sub_smul, one_smul]
    abel

theorem periodic_freq {E : Type*} {f : Space → E} (hp : IsPeriodic f) (n : Lattice) (x : Space) :
    f (x + freq n) = f x := by
  rw [freq, Fin.sum_univ_three, ← add_assoc, ← add_assoc, periodic_int_smul hp 2,
    periodic_int_smul hp 1, periodic_int_smul hp 0]

theorem exists_bound_of_periodic {E : Type*} [NormedAddCommGroup E] {h : Space → E}
    (hc : Continuous h) (hp : IsPeriodic h) : ∃ C, ∀ x, ‖h x‖ ≤ C := by
  obtain ⟨C, hC⟩ := CoefCalculus.Internal.isCompact_cell.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun x => ?_⟩
  set n : Lattice := fun i => ⌊x i⌋ with hn
  have hmem : x - freq n ∈ cell := by
    intro i
    rw [PiLp.sub_apply, CoefCalculus.Internal.freq_apply]
    have a1 := Int.floor_le (x i)
    have a2 := Int.lt_floor_add_one (x i)
    simp only [hn]
    constructor <;> linarith
  have he := periodic_freq hp n (x - freq n)
  rw [sub_add_cancel] at he
  rw [he]
  exact hC _ hmem

theorem isPeriodic_iteratedFDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} (hp : IsPeriodic f) (n : ℕ) : IsPeriodic (iteratedFDeriv ℝ n f) := by
  intro i x
  have h : (fun y => f (y + unitVector i)) = f := funext (hp i)
  rw [← iteratedFDeriv_comp_add_right n (unitVector i) x, h]

theorem isPeriodic_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} (hp : IsPeriodic f) : IsPeriodic (fderiv ℝ f) := by
  intro i x
  have h : (fun y => f (y + unitVector i)) = f := funext (hp i)
  rw [← fderiv_comp_add_right (unitVector i), h]

theorem isPeriodic_fderiv_apply {f : Space → Space} (hp : IsPeriodic f) (z : Space) :
    IsPeriodic (fun y => fderiv ℝ f y z) := by
  intro i x
  simp only [isPeriodic_fderiv hp i x]

theorem integrableOn_cell {E : Type*} [NormedAddCommGroup E] {h : Space → E} (hc : Continuous h) :
    IntegrableOn h cell :=
  hc.continuousOn.integrableOn_compact CoefCalculus.Internal.isCompact_cell

theorem sum_unitVector (z : Space) : ∑ i, z i • unitVector i = z := by
  ext j
  simp [unitVector, Pi.single_apply]

theorem integral_cell_fderiv_eq_zero (H : Space → ℝ) (hH : ContDiff ℝ 1 H) (hp : IsPeriodic H)
    (z : Space) : ∫ x in cell, fderiv ℝ H x z = 0 := by
  have hd : ∀ x, HasFDerivAt H (fderiv ℝ H x) x := fun x => (hH.differentiable (by simp) x).hasFDerivAt
  have hc : Continuous (fderiv ℝ H) := hH.continuous_fderiv (by simp)
  have e : ∀ x, fderiv ℝ H x z = ∑ i, z i * fderiv ℝ H x (unitVector i) := by
    intro x
    conv_lhs => rw [← sum_unitVector z]
    simp [map_sum, map_smul]
  simp_rw [e]
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_const_mul, CoefCalculus.Internal.integral_cell_eq_zero i H (fderiv ℝ H) hd
      (hc.clm_apply continuous_const) (hp i), mul_zero]
  · intro i _
    exact integrableOn_cell (continuous_const.mul (hc.clm_apply continuous_const))

theorem integral_cell_inner_fderiv (a b : Space → Space) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : IsPeriodic a) (hpb : IsPeriodic b) (z : Space) :
    ∫ x in cell, inner ℝ (fderiv ℝ a x z) (b x) = -∫ x in cell, inner ℝ (a x) (fderiv ℝ b x z) := by
  have hH : ContDiff ℝ 1 (fun x => inner ℝ (a x) (b x)) := (ha.inner ℝ hb).of_le (by simp)
  have hp : IsPeriodic (fun x => inner ℝ (a x) (b x)) := fun i x => by simp only [hpa i x, hpb i x]
  have hZ := integral_cell_fderiv_eq_zero _ hH hp z
  have hder : ∀ x, fderiv ℝ (fun x => inner ℝ (a x) (b x)) x z =
      inner ℝ (fderiv ℝ a x z) (b x) + inner ℝ (a x) (fderiv ℝ b x z) := by
    intro x
    rw [fderiv_inner_apply ℝ (ha.differentiable (by simp) x) (hb.differentiable (by simp) x), add_comm]
  have ca : Continuous (fun x => fderiv ℝ a x z) := (ha.continuous_fderiv (by simp)).clm_apply continuous_const
  have cb : Continuous (fun x => fderiv ℝ b x z) := (hb.continuous_fderiv (by simp)).clm_apply continuous_const
  simp_rw [hder] at hZ
  rw [integral_add (integrableOn_cell (ca.inner hb.continuous)) (integrableOn_cell (ha.continuous.inner cb))] at hZ
  linarith

theorem integral_cell_add (H : Space → ℝ) (hH : ContDiff ℝ ∞ H) (hp : IsPeriodic H) (z : Space) :
    ∫ x in cell, H (x + z) = ∫ x in cell, H x := by
  have hc : Continuous (fderiv ℝ H) := hH.continuous_fderiv (by simp)
  have hd : ∀ y, HasFDerivAt H (fderiv ℝ H y) y := fun y => (hH.differentiable (by simp) y).hasFDerivAt
  have hF : Continuous (fun q : Space × ℝ => fderiv ℝ H (q.1 + q.2 • z) z) :=
    (hc.comp (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply continuous_const
  have hftc : ∀ x, H (x + z) - H x = ∫ t in (0 : ℝ)..1, fderiv ℝ H (x + t • z) z := by
    intro x
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
      (f := fun t : ℝ => H (x + t • z)) (f' := fun t => fderiv ℝ H (x + t • z) z) ?_ ?_
    · simpa using this.symm
    · intro t _
      have h1 : HasDerivAt (fun t : ℝ => x + t • z) z t := by
        simpa using ((hasDerivAt_id t).smul_const z).const_add x
      exact (hd _).comp_hasDerivAt t h1
    · exact (hF.comp (Continuous.prodMk continuous_const continuous_id)).intervalIntegrable _ _
  have hslice : ∀ t : ℝ, ∫ x in cell, fderiv ℝ H (x + t • z) z = 0 := by
    intro t
    have hH' : ContDiff ℝ 1 (fun y => H (y + t • z)) :=
      (hH.comp (contDiff_id.add contDiff_const)).of_le (by simp)
    have hp' : IsPeriodic (fun y => H (y + t • z)) := fun i y => by
      simp only
      rw [add_right_comm, hp i]
    have := integral_cell_fderiv_eq_zero _ hH' hp' z
    simpa [fderiv_comp_add_right] using this
  have hint : IntegrableOn (fun x => H (x + z)) cell :=
    integrableOn_cell (hH.continuous.comp (continuous_add_const z))
  have hint2 : IntegrableOn H cell := integrableOn_cell hH.continuous
  have hprod : Integrable (Function.uncurry fun (x : Space) (t : ℝ) => fderiv ℝ H (x + t • z) z)
      ((volume.restrict cell).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    have hK : IsCompact (cell ×ˢ Icc (0 : ℝ) 1) :=
      CoefCalculus.Internal.isCompact_cell.prod isCompact_Icc
    exact (hF.continuousOn.integrableOn_compact hK).mono_set
      (prod_mono subset_rfl Ioc_subset_Icc_self)
  have hswap : ∫ x in cell, (∫ t in (0 : ℝ)..1, fderiv ℝ H (x + t • z) z) =
      ∫ t in (0 : ℝ)..1, ∫ x in cell, fderiv ℝ H (x + t • z) z := by
    simp_rw [intervalIntegral.integral_of_le zero_le_one]
    exact integral_integral_swap hprod
  have h0 : ∫ x in cell, (H (x + z) - H x) = 0 := by
    simp_rw [hftc]
    rw [hswap]
    simp [hslice]
  rw [integral_sub hint hint2] at h0
  linarith

theorem iteratedFDeriv_two_eq_fderiv_apply (f : Space → Space) (hf : ContDiff ℝ ∞ f)
    (x z : Space) :
    iteratedFDeriv ℝ 2 f x ![z, z] = fderiv ℝ (fun y => fderiv ℝ f y z) x z := by
  obtain ⟨_, hf1⟩ := contDiff_infty_iff_fderiv.1 hf
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (contDiff_infty_iff_fderiv.1 hf1).1 x
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const z)]
  simp [fderiv_fun_const]

theorem integral_cell_inner_remainder (v φ : Space → Space) (hv : ContDiff ℝ ∞ v)
    (hφ : ContDiff ℝ ∞ φ) (hpv : IsPeriodic v) (hpφ : IsPeriodic φ) (z : Space) :
    ∫ x in cell, inner ℝ (secondOrderRemainder v x z) (φ x) =
      ∫ x in cell, inner ℝ (v x) (secondOrderRemainder φ x (-z)) := by
  obtain ⟨_, hv1⟩ := contDiff_infty_iff_fderiv.1 hv
  obtain ⟨_, hφ1⟩ := contDiff_infty_iff_fderiv.1 hφ
  have hw : ContDiff ℝ ∞ (fun y => fderiv ℝ v y z) := hv1.clm_apply contDiff_const
  have hψ : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y z) := hφ1.clm_apply contDiff_const
  have hψ2 : ContDiff ℝ ∞ (fun y => fderiv ℝ (fun u => fderiv ℝ φ u z) y z) :=
    (contDiff_infty_iff_fderiv.1 hψ).2.clm_apply contDiff_const
  have hw2 : ContDiff ℝ ∞ (fun y => fderiv ℝ (fun u => fderiv ℝ v u z) y z) :=
    (contDiff_infty_iff_fderiv.1 hw).2.clm_apply contDiff_const
  have hpw := isPeriodic_fderiv_apply hpv z
  have hpψ := isPeriodic_fderiv_apply hpφ z
  have T0 : ∫ x in cell, inner ℝ (v (x + z)) (φ x) = ∫ x in cell, inner ℝ (v x) (φ (x - z)) := by
    have hH : ContDiff ℝ ∞ (fun x => inner ℝ (v x) (φ (x - z))) :=
      hv.inner ℝ (hφ.comp (contDiff_id.sub contDiff_const))
    have hpH : IsPeriodic (fun x => inner ℝ (v x) (φ (x - z))) := fun i x => by
      simp only
      rw [hpv i, add_sub_right_comm, hpφ i]
    have := integral_cell_add _ hH hpH z
    simpa using this
  have T2 := integral_cell_inner_fderiv v φ hv hφ hpv hpφ z
  have T3a := integral_cell_inner_fderiv (fun y => fderiv ℝ v y z) φ hw hφ hpw hpφ z
  have T3b := integral_cell_inner_fderiv v (fun y => fderiv ℝ φ y z) hv hψ hpv hpψ z
  have i0 : IntegrableOn (fun x => inner ℝ (v (x + z)) (φ x)) cell :=
    integrableOn_cell ((hv.continuous.comp (continuous_add_const z)).inner hφ.continuous)
  have i1 : IntegrableOn (fun x => inner ℝ (v x) (φ x)) cell :=
    integrableOn_cell (hv.continuous.inner hφ.continuous)
  have i2 : IntegrableOn (fun x => inner ℝ (fderiv ℝ v x z) (φ x)) cell :=
    integrableOn_cell (hw.continuous.inner hφ.continuous)
  have i3 : IntegrableOn (fun x => inner ℝ (fderiv ℝ (fun u => fderiv ℝ v u z) x z) (φ x)) cell :=
    integrableOn_cell (hw2.continuous.inner hφ.continuous)
  have j0 : IntegrableOn (fun x => inner ℝ (v x) (φ (x - z))) cell :=
    integrableOn_cell (hv.continuous.inner (hφ.continuous.comp (continuous_sub_right z)))
  have j2 : IntegrableOn (fun x => inner ℝ (v x) (fderiv ℝ φ x z)) cell :=
    integrableOn_cell (hv.continuous.inner hψ.continuous)
  have j3 : IntegrableOn (fun x => inner ℝ (v x) (fderiv ℝ (fun u => fderiv ℝ φ u z) x z)) cell :=
    integrableOn_cell (hv.continuous.inner hψ2.continuous)
  have hL : ∀ x, inner ℝ (secondOrderRemainder v x z) (φ x) =
      inner ℝ (v (x + z)) (φ x) - inner ℝ (v x) (φ x) - inner ℝ (fderiv ℝ v x z) (φ x)
        - (1 / 2 : ℝ) * inner ℝ (fderiv ℝ (fun u => fderiv ℝ v u z) x z) (φ x) := by
    intro x
    simp only [secondOrderRemainder, iteratedFDeriv_two_eq_fderiv_apply v hv x z, inner_sub_left,
      real_inner_smul_left]
  have hR : ∀ x, inner ℝ (v x) (secondOrderRemainder φ x (-z)) =
      inner ℝ (v x) (φ (x - z)) - inner ℝ (v x) (φ x) + inner ℝ (v x) (fderiv ℝ φ x z)
        - (1 / 2 : ℝ) * inner ℝ (v x) (fderiv ℝ (fun u => fderiv ℝ φ u z) x z) := by
    intro x
    have e : iteratedFDeriv ℝ 2 φ x ![-z, -z] = iteratedFDeriv ℝ 2 φ x ![z, z] := by
      rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
      simp
    simp only [secondOrderRemainder, e, iteratedFDeriv_two_eq_fderiv_apply φ hφ x z,
      inner_sub_right, real_inner_smul_right, map_neg, inner_neg_right, ← sub_eq_add_neg]
    ring
  simp_rw [hL, hR]
  rw [integral_sub, integral_sub, integral_sub, integral_const_mul, integral_sub, integral_add,
    integral_sub, integral_const_mul]
  · rw [T0, T2, T3a, T3b]
    ring
  all_goals first
    | exact i0 | exact i1 | exact i2 | exact j0 | exact j2 | exact i0.sub i1 | exact j0.sub i1
    | exact (i0.sub i1).sub i2 | exact (j0.sub i1).add j2 | exact i3.const_mul _
    | exact j3.const_mul _

theorem norm_remainder_le_far (f : Space → Space) (x z : Space) (hz : 1 ≤ ‖z‖) :
    ‖secondOrderRemainder f x z‖ ≤
      ‖f (x + z)‖ + (‖f x‖ + ‖fderiv ℝ f x‖ + ‖iteratedFDeriv ℝ 2 f x‖) * ‖z‖ ^ 2 := by
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have h1 : ‖z‖ ≤ ‖z‖ ^ 2 := by nlinarith
  have h2 : (1 : ℝ) ≤ ‖z‖ ^ 2 := by nlinarith
  have hD : ‖fderiv ℝ f x z‖ ≤ ‖fderiv ℝ f x‖ * ‖z‖ := (fderiv ℝ f x).le_opNorm z
  have hD2 : ‖iteratedFDeriv ℝ 2 f x ![z, z]‖ ≤ ‖iteratedFDeriv ℝ 2 f x‖ * ‖z‖ ^ 2 := by
    have := (iteratedFDeriv ℝ 2 f x).le_opNorm ![z, z]
    simpa [Fin.prod_univ_two, sq] using this
  have hs : ‖(1 / 2 : ℝ) • iteratedFDeriv ℝ 2 f x ![z, z]‖ ≤ ‖iteratedFDeriv ℝ 2 f x ![z, z]‖ := by
    rw [norm_smul]
    have := norm_nonneg (iteratedFDeriv ℝ 2 f x ![z, z])
    norm_num
    nlinarith
  unfold secondOrderRemainder
  have n1 := norm_sub_le (f (x + z) - f x - fderiv ℝ f x z) ((1 / 2 : ℝ) • iteratedFDeriv ℝ 2 f x ![z, z])
  have n2 := norm_sub_le (f (x + z) - f x) (fderiv ℝ f x z)
  have n3 := norm_sub_le (f (x + z)) (f x)
  have p1 : ‖f x‖ ≤ ‖f x‖ * ‖z‖ ^ 2 := le_mul_of_one_le_right (norm_nonneg _) h2
  have p2 : ‖fderiv ℝ f x‖ * ‖z‖ ≤ ‖fderiv ℝ f x‖ * ‖z‖ ^ 2 :=
    mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  nlinarith

theorem integrable_of_near_far {f : Space → ℝ} (hf : AEStronglyMeasurable f volume) {a b C : ℝ}
    (ha : a < 3) (hb : 3 < b) (hnear : ∀ z : Space, ‖z‖ ≤ 1 → ‖f z‖ ≤ C * ‖z‖ ^ (-a))
    (hfar : ∀ z : Space, 1 ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ (-b)) : Integrable f := by
  have hfin : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
  have hC : 0 ≤ C := by
    have hn : ‖(EuclideanSpace.single 0 1 : Space)‖ = 1 := by simp
    have := hfar (EuclideanSpace.single 0 1) hn.ge
    rw [hn, Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  have hball : IntegrableOn f (Metric.ball 0 1) volume := by
    refine integrableOn_ball_of_norm_le_rpow (C := C) (by rw [hfin]; norm_num)
      (by rw [hfin]; exact_mod_cast ha) ?_ hf
    refine (ae_restrict_mem measurableSet_ball).mono fun z hz => hnear z ?_
    have : ‖z‖ < 1 := by simpa using hz
    exact this.le
  have hcomp : IntegrableOn f (Metric.ball (0 : Space) 1)ᶜ volume := by
    have hint : Integrable (fun z : Space => (1 + ‖z‖) ^ (-b)) :=
      integrable_one_add_norm (by rw [hfin]; exact_mod_cast hb)
    refine Integrable.mono' ((hint.const_mul (C * 2 ^ b)).integrableOn) hf.restrict ?_
    refine (ae_restrict_mem measurableSet_ball.compl).mono fun z hz => ?_
    have hz1 : 1 ≤ ‖z‖ := by simpa using hz
    have hzpos : 0 < ‖z‖ := by linarith
    have key : ‖z‖ ^ (-b) ≤ 2 ^ b * (1 + ‖z‖) ^ (-b) := by
      rw [Real.rpow_neg hzpos.le, Real.rpow_neg (by positivity), ← div_eq_mul_inv]
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      rw [div_mul_eq_mul_div, one_le_div (by positivity), ← Real.mul_rpow (by norm_num) hzpos.le]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    calc ‖f z‖ ≤ C * ‖z‖ ^ (-b) := hfar z hz1
      _ ≤ C * (2 ^ b * (1 + ‖z‖) ^ (-b)) := mul_le_mul_of_nonneg_left key hC
      _ = C * 2 ^ b * (1 + ‖z‖) ^ (-b) := by ring
  have := hball.union hcomp
  rwa [Set.union_compl_self, integrableOn_univ] at this

theorem rpow_mul_pow_eq (t r : ℝ) (ht : 0 ≤ t) (n : ℕ) (hr : r ≠ 0) (hrn : r + n ≠ 0) :
    t ^ r * t ^ n = t ^ (r + n) := by
  rcases ht.eq_or_lt with h | h
  · rw [← h, Real.zero_rpow hr, Real.zero_rpow hrn, zero_mul]
  · rw [← Real.rpow_natCast, ← Real.rpow_add h]

theorem continuous_remainder_pair (φ : Space → Space) (hφ : ContDiff ℝ ∞ φ) :
    Continuous (fun p : Space × Space => secondOrderRemainder φ p.1 p.2) := by
  have h1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have h2 : Continuous (iteratedFDeriv ℝ 2 φ) := hφ.continuous_iteratedFDeriv (by norm_cast)
  have hm : Continuous (fun p : Space × Space => (![p.2, p.2] : Fin 2 → Space)) := by
    refine continuous_pi (fun i => ?_)
    fin_cases i <;> simpa using continuous_snd
  have hc := hφ.continuous
  have h3 : Continuous (fun p : Space × Space => iteratedFDeriv ℝ 2 φ p.1 ![p.2, p.2]) :=
    continuous_eval.comp ((h2.comp continuous_fst).prodMk hm)
  have h4 : Continuous (fun p : Space × Space => fderiv ℝ φ p.1 p.2) :=
    (h1.comp continuous_fst).clm_apply continuous_snd
  have h5 : Continuous (fun p : Space × Space =>
      (1 / 2 : ℝ) • iteratedFDeriv ℝ 2 φ p.1 ![p.2, p.2]) := h3.const_smul (1 / 2 : ℝ)
  have h6 : Continuous (fun p : Space × Space => φ (p.1 + p.2)) :=
    hc.comp (continuous_fst.add continuous_snd)
  have h7 : Continuous (fun p : Space × Space => φ p.1) := hc.comp continuous_fst
  exact ((h6.sub h7).sub h4).sub h5

theorem exists_dominating (hR : RemainderBoundStatement) (α : ℝ) (h1 : 1 < α) (h2 : α < 3 / 2)
    (v : Space → Space) (hv : ContDiff ℝ ∞ v) (hp : IsPeriodic v) :
    ∃ G : Space → ℝ, Integrable G ∧
      ∀ x z : Space, ‖‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder v x z‖ ≤ G z := by
  obtain ⟨B0, hB0⟩ := exists_bound_of_periodic hv.continuous hp
  obtain ⟨B1, hB1⟩ := exists_bound_of_periodic (hv.continuous_fderiv (by simp)) (isPeriodic_fderiv hp)
  obtain ⟨B2, hB2⟩ := exists_bound_of_periodic
    (hv.continuous_iteratedFDeriv (m := 2) (by norm_cast)) (isPeriodic_iteratedFDeriv hp 2)
  obtain ⟨C3, hC3⟩ := exists_bound_of_periodic
    (hv.continuous_iteratedFDeriv (m := 3) (by norm_cast)) (isPeriodic_iteratedFDeriv hp 3)
  have e0 : 0 ≤ B0 := (norm_nonneg _).trans (hB0 0)
  have e1 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  have e2 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  have e3 : 0 ≤ C3 := (norm_nonneg _).trans (hC3 0)
  set D := 2 * B0 + B1 + B2 with hD
  have eD : 0 ≤ D := by positivity
  have hv3 : ContDiff ℝ 3 v := hv.of_le (by norm_cast)
  refine ⟨fun z => if ‖z‖ ≤ 1 then C3 * ‖z‖ ^ (-(2 * α)) else D * ‖z‖ ^ (-(1 + 2 * α)), ?_, ?_⟩
  · have hm : Measurable (fun z : Space =>
        if ‖z‖ ≤ 1 then C3 * ‖z‖ ^ (-(2 * α)) else D * ‖z‖ ^ (-(1 + 2 * α))) :=
      Measurable.ite (measurableSet_le measurable_norm measurable_const)
        (measurable_const.mul (measurable_norm.pow_const _))
        (measurable_const.mul (measurable_norm.pow_const _))
    refine integrable_of_near_far hm.aestronglyMeasurable (a := 2 * α) (b := 1 + 2 * α)
      (C := C3 + D) (by linarith) (by linarith) ?_ ?_
    · intro z hz
      have hk : 0 ≤ ‖z‖ ^ (-(2 * α)) := Real.rpow_nonneg (norm_nonneg _) _
      rw [if_pos hz, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (by linarith) hk
    · intro z hz
      by_cases h : ‖z‖ ≤ 1
      · have h' : ‖z‖ = 1 := le_antisymm h hz
        rw [if_pos h, h', Real.one_rpow, Real.one_rpow, mul_one, mul_one, Real.norm_of_nonneg e3]
        linarith
      · have hk : 0 ≤ ‖z‖ ^ (-(1 + 2 * α)) := Real.rpow_nonneg (norm_nonneg _) _
        rw [if_neg h, Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right (by linarith) hk
  · intro x z
    dsimp only
    have hK0 : 0 ≤ ‖z‖ ^ (-(3 + 2 * α)) := Real.rpow_nonneg (norm_nonneg _) _
    rw [norm_smul, Real.norm_of_nonneg hK0]
    by_cases h : ‖z‖ ≤ 1
    · rw [if_pos h]
      have hb := hR v hv3 x z C3 (fun y _ => hC3 y)
      calc ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder v x z‖
          ≤ ‖z‖ ^ (-(3 + 2 * α)) * (C3 * ‖z‖ ^ 3) := mul_le_mul_of_nonneg_left hb hK0
        _ = C3 * ‖z‖ ^ (-(2 * α)) := by
          have := rpow_mul_pow_eq ‖z‖ (-(3 + 2 * α)) (norm_nonneg _) 3 (by linarith)
            (by push_cast; linarith)
          have he : -(3 + 2 * α) + ((3 : ℕ) : ℝ) = -(2 * α) := by push_cast; ring
          rw [he] at this
          rw [← this]
          ring
    · rw [if_neg h]
      have hz : 1 ≤ ‖z‖ := (not_le.1 h).le
      have hz2 : 1 ≤ ‖z‖ ^ 2 := one_le_pow₀ hz
      have hb : ‖secondOrderRemainder v x z‖ ≤ D * ‖z‖ ^ 2 := by
        refine (norm_remainder_le_far v x z hz).trans ?_
        have a0 := hB0 (x + z)
        have a1 := hB0 x
        have a2 := hB1 x
        have a3 := hB2 x
        have : (‖v x‖ + ‖fderiv ℝ v x‖ + ‖iteratedFDeriv ℝ 2 v x‖) * ‖z‖ ^ 2 ≤
            (B0 + B1 + B2) * ‖z‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        rw [hD]
        nlinarith
      calc ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder v x z‖
          ≤ ‖z‖ ^ (-(3 + 2 * α)) * (D * ‖z‖ ^ 2) := mul_le_mul_of_nonneg_left hb hK0
        _ = D * ‖z‖ ^ (-(1 + 2 * α)) := by
          have := rpow_mul_pow_eq ‖z‖ (-(3 + 2 * α)) (norm_nonneg _) 2 (by linarith)
            (by push_cast; linarith)
          have he : -(3 + 2 * α) + ((2 : ℕ) : ℝ) = -(1 + 2 * α) := by push_cast; ring
          rw [he] at this
          rw [← this]
          ring


theorem continuous_remainder_section (φ : Space → Space) (hφ : ContDiff ℝ ∞ φ) (z : Space) :
    Continuous (fun x : Space => secondOrderRemainder φ x z) := by
  have h1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have h2 : Continuous (iteratedFDeriv ℝ 2 φ) := hφ.continuous_iteratedFDeriv (by norm_cast)
  have hc := hφ.continuous
  have h3 : Continuous (fun x : Space => iteratedFDeriv ℝ 2 φ x ![z, z]) :=
    continuous_eval.comp (h2.prodMk continuous_const)
  have h4 : Continuous (fun x : Space => fderiv ℝ φ x z) := h1.clm_apply continuous_const
  have h5 : Continuous (fun x : Space => (1 / 2 : ℝ) • iteratedFDeriv ℝ 2 φ x ![z, z]) :=
    h3.const_smul (1 / 2 : ℝ)
  have h6 : Continuous (fun x : Space => φ (x + z)) := hc.comp (continuous_add_const z)
  exact ((h6.sub hc).sub h4).sub h5

theorem continuous_remainder_increment (φ : Space → Space) (hφ : ContDiff ℝ ∞ φ) (x : Space) :
    Continuous (fun z : Space => secondOrderRemainder φ x z) := by
  have hc := hφ.continuous
  have hm : Continuous (fun z : Space => (![z, z] : Fin 2 → Space)) := by
    refine continuous_pi (fun i => ?_)
    fin_cases i <;> simpa using continuous_id'
  have h3 : Continuous (fun z : Space => iteratedFDeriv ℝ 2 φ x ![z, z]) :=
    continuous_eval.comp (continuous_const.prodMk hm)
  have h4 : Continuous (fun z : Space => fderiv ℝ φ x z) := (fderiv ℝ φ x).continuous
  have h5 : Continuous (fun z : Space => (1 / 2 : ℝ) • iteratedFDeriv ℝ 2 φ x ![z, z]) :=
    h3.const_smul (1 / 2 : ℝ)
  have h6 : Continuous (fun z : Space => φ (x + z)) := hc.comp (continuous_const_add x)
  exact ((h6.sub continuous_const).sub h4).sub h5

theorem integrable_remainder_section (hR : RemainderBoundStatement) (α : ℝ) (h1 : 1 < α)
    (h2 : α < 3 / 2) (v : Space → Space) (hv : ContDiff ℝ ∞ v) (hp : IsPeriodic v) (x : Space) :
    Integrable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder v x z) := by
  obtain ⟨G, hG, hdom⟩ := exists_dominating hR α h1 h2 v hv hp
  have hc : Continuous (fun z : Space => secondOrderRemainder v x z) :=
    continuous_remainder_increment v hv x
  have hK : Measurable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α))) := measurable_norm.pow_const _
  exact hG.mono' (hK.aestronglyMeasurable.smul hc.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => hdom x z)

theorem continuous_fractionalPowerAt (hR : RemainderBoundStatement) (α : ℝ) (h1 : 1 < α)
    (h2 : α < 3 / 2) (v : Space → Space) (hv : ContDiff ℝ ∞ v) (hp : IsPeriodic v) :
    Continuous (fractionalPowerAt α v) := by
  obtain ⟨G, hG, hdom⟩ := exists_dominating hR α h1 h2 v hv hp
  have hK : Measurable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α))) := measurable_norm.pow_const _
  have hI : Continuous (fun x : Space => ∫ z : Space, ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder v x z) := by
    refine continuous_of_dominated (μ := (volume : Measure Space)) (bound := G)
      (F := fun x z : Space => ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder v x z) ?_ ?_ hG ?_
    · intro x
      have hcx : Continuous (fun z : Space => secondOrderRemainder v x z) :=
        continuous_remainder_increment v hv x
      exact hK.aestronglyMeasurable.smul hcx.aestronglyMeasurable
    · exact fun x => Filter.Eventually.of_forall fun z => hdom x z
    · refine Filter.Eventually.of_forall fun z => ?_
      exact Continuous.const_smul (continuous_remainder_section v hv z) (‖z‖ ^ (-(3 + 2 * α)))
  unfold fractionalPowerAt
  exact Continuous.const_smul hI (fractionalNormalizer α)⁻¹

theorem integrable_prod_cell (hR : RemainderBoundStatement) (α : ℝ) (h1 : 1 < α) (h2 : α < 3 / 2)
    (v φ : Space → Space) (hv : ContDiff ℝ ∞ v) (hφ : ContDiff ℝ ∞ φ) (hpv : IsPeriodic v)
    (hpφ : IsPeriodic φ) :
    Integrable (fun p : Space × Space =>
      ‖p.2‖ ^ (-(3 + 2 * α)) * inner ℝ (secondOrderRemainder v p.1 p.2) (φ p.1))
      ((volume.restrict cell).prod volume) := by
  obtain ⟨G, hG, hdom⟩ := exists_dominating hR α h1 h2 v hv hpv
  obtain ⟨B, hB⟩ := exists_bound_of_periodic hφ.continuous hpφ
  have : IsFiniteMeasure (volume.restrict cell) :=
    isFiniteMeasure_restrict.2 CoefCalculus.Internal.isCompact_cell.measure_lt_top.ne
  have hin : Continuous (fun p : Space × Space => inner ℝ (secondOrderRemainder v p.1 p.2) (φ p.1)) :=
    (continuous_remainder_pair v hv).inner (hφ.continuous.comp continuous_fst)
  have hm : Measurable (fun p : Space × Space =>
      ‖p.2‖ ^ (-(3 + 2 * α)) * inner ℝ (secondOrderRemainder v p.1 p.2) (φ p.1)) :=
    ((measurable_snd.norm).pow_const _).mul hin.measurable
  refine ((hG.comp_snd (volume.restrict cell)).mul_const B).mono' hm.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun p => ?_
  rw [← real_inner_smul_left, Real.norm_eq_abs]
  refine (abs_real_inner_le_norm _ _).trans ?_
  exact mul_le_mul (hdom p.1 p.2) (hB p.1) (norm_nonneg _) ((norm_nonneg _).trans (hdom p.1 p.2))

end TorusSymmetry.Internal

open TorusSymmetry.Internal in
theorem periodicSymmetry_of (α : ℝ) (h1 : 1 < α) (h2 : α < 3 / 2) (hR : RemainderBoundStatement) :
    PeriodicSymmetry α := by
  intro f g hf hg hpf hpg
  refine ⟨integrableOn_cell (continuous_fractionalPowerAt hR α h1 h2 f hf hpf), ?_⟩
  have hPL := integrable_prod_cell hR α h1 h2 f g hf hg hpf hpg
  have hPR : Integrable (fun p : Space × Space =>
      ‖p.2‖ ^ (-(3 + 2 * α)) * inner ℝ (f p.1) (secondOrderRemainder g p.1 p.2))
      ((volume.restrict cell).prod volume) := by
    refine (integrable_prod_cell hR α h1 h2 g f hg hf hpg hpf).congr
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [real_inner_comm]
  have hLx : ∀ x, inner ℝ (fractionalPowerAt α f x) (g x) = (fractionalNormalizer α)⁻¹ *
      ∫ z, ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (secondOrderRemainder f x z) (g x) := by
    intro x
    unfold fractionalPowerAt
    rw [real_inner_smul_left, real_inner_comm,
      ← integral_inner (integrable_remainder_section hR α h1 h2 f hf hpf x)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [real_inner_smul_right, real_inner_comm]
  have hRx : ∀ x, inner ℝ (f x) (fractionalPowerAt α g x) = (fractionalNormalizer α)⁻¹ *
      ∫ z, ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (f x) (secondOrderRemainder g x z) := by
    intro x
    unfold fractionalPowerAt
    rw [real_inner_smul_right, ← integral_inner (integrable_remainder_section hR α h1 h2 g hg hpg x)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [real_inner_smul_right]
  simp_rw [hLx, hRx]
  rw [integral_const_mul, integral_const_mul]
  congr 1
  have sL := integral_integral_swap (μ := volume.restrict cell) (ν := volume) (f := fun x z : Space =>
    ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (secondOrderRemainder f x z) (g x)) hPL
  have sR := integral_integral_swap (μ := volume.restrict cell) (ν := volume) (f := fun x z : Space =>
    ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (f x) (secondOrderRemainder g x z)) hPR
  rw [sL, sR]
  have e1 : ∀ z : Space,
      ∫ x in cell, ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (secondOrderRemainder f x z) (g x) =
        (fun w : Space => ‖w‖ ^ (-(3 + 2 * α)) *
          ∫ x in cell, inner ℝ (f x) (secondOrderRemainder g x w)) (-z) := by
    intro z
    rw [integral_const_mul, integral_cell_inner_remainder f g hf hg hpf hpg z]
    simp only [norm_neg]
  refine (integral_congr_ae (Filter.Eventually.of_forall e1)).trans ?_
  refine (integral_neg_eq_self (fun w : Space => ‖w‖ ^ (-(3 + 2 * α)) *
    ∫ x in cell, inner ℝ (f x) (secondOrderRemainder g x w)) (volume : Measure Space)).trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  rw [integral_const_mul]

end Breakdown.Periodic
