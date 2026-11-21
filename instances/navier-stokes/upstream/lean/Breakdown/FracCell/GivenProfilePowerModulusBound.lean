import Breakdown.FracCert.Defs
import Breakdown.Frac.OpExports

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracInternal

namespace ProfilePower

open SteadyCert

private theorem sqrt_sq_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Space → E}
    (hf : MemLp f 2 volume) : Real.sqrt (∫ y, ‖f y‖ ^ 2) = ‖hf.toLp f‖ := by
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.sqrt_eq_rpow, one_div]

private theorem abs_pair {X Y : Space → Space} (hX : MemLp X 2 volume) (hY : MemLp Y 2 volume) :
    |∫ y, inner ℝ (X y) (Y y)| ≤ Real.sqrt (∫ y, ‖X y‖ ^ 2) * Real.sqrt (∫ y, ‖Y y‖ ^ 2) := by
  have e : ∫ y, inner ℝ (X y) (Y y) = inner ℝ (hX.toLp X) (hY.toLp Y) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with y a b
    rw [a, b]
  rw [e, sqrt_sq_integral hX, sqrt_sq_integral hY]
  exact abs_real_inner_le_norm _ _

private theorem shift_memLp {E : Type*} [NormedAddCommGroup E] {f : Space → E}
    (hf : MemLp f 2 volume) (c : Space) : MemLp (fun y => f (y - c)) 2 volume :=
  hf.comp_measurePreserving (measurePreserving_sub_right volume c)

private theorem diff_le_two {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hH2 : MemLp H 2 volume)
    (c : Space) :
    Real.sqrt (∫ y, ‖H (y - c) - H y‖ ^ 2) ≤ 2 * Real.sqrt (∫ y, ‖H y‖ ^ 2) := by
  have h1 := shift_memLp hH2 c
  have e : Real.sqrt (∫ y, ‖H (y - c) - H y‖ ^ 2) = ‖h1.toLp _ - hH2.toLp H‖ := by
    rw [← MemLp.toLp_sub]
    exact sqrt_sq_integral (h1.sub hH2)
  rw [e]
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  rw [← sqrt_sq_integral h1, ← sqrt_sq_integral hH2,
    integral_sub_right_eq_self (fun y => ‖H y‖ ^ 2) c]
  ring

private theorem diff_le_mod {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (C : ℝ)
    (hC : ∀ h : Space, ‖h‖ ≤ 1 → ∫ y, ‖H (y + h) - H y‖ ^ 2 ≤ C * ‖h‖) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) {z : Space} (hz : ‖z‖ ≤ 1) :
    ∫ y, ‖H (y - s • z) - H y‖ ^ 2 ≤ |C| * ‖z‖ := by
  have e : ∫ y, ‖H (y - s • z) - H y‖ ^ 2 = ∫ y, ‖H (y + s • z) - H y‖ ^ 2 := by
    rw [← integral_sub_right_eq_self (fun y => ‖H (y + s • z) - H y‖ ^ 2) (s • z)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [sub_add_cancel]
    rw [norm_sub_rev]
  have hn : ‖s • z‖ ≤ ‖z‖ := by
    rw [norm_smul, Real.norm_of_nonneg hs0]
    exact mul_le_of_le_one_left (norm_nonneg z) hs1
  rw [e]
  refine (hC (s • z) (hn.trans hz)).trans ?_
  calc C * ‖s • z‖ ≤ |C| * ‖s • z‖ := mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)
    _ ≤ |C| * ‖z‖ := mul_le_mul_of_nonneg_left hn (abs_nonneg C)

private theorem pair_step {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hH2 : MemLp H 2 volume)
    {φ : Space → Space} (hφ2 : MemLp φ 2 volume) (s : ℝ) (z : Space) :
    |∫ y, inner ℝ ((H (y - s • z) - H y) z z) (φ y)| ≤
      ‖z‖ ^ 2 * Real.sqrt (∫ y, ‖H (y - s • z) - H y‖ ^ 2) * Real.sqrt (∫ y, ‖φ y‖ ^ 2) := by
  have hD : MemLp (fun y => H (y - s • z) - H y) 2 volume := (shift_memLp hH2 (s • z)).sub hH2
  let ev : (Space →L[ℝ] Space →L[ℝ] Space) →L[ℝ] Space :=
    (ContinuousLinearMap.apply ℝ Space z).comp (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) z)
  have hX : MemLp (fun y => (H (y - s • z) - H y) z z) 2 volume := ev.comp_memLp' hD
  refine (abs_pair hX hφ2).trans ?_
  gcongr
  have hle : ∫ y, ‖(H (y - s • z) - H y) z z‖ ^ 2 ≤
      ∫ y, (‖z‖ ^ 2) ^ 2 * ‖H (y - s • z) - H y‖ ^ 2 := by
    refine integral_mono ((memLp_two_iff_integrable_sq_norm hX.1).1 hX)
      (((memLp_two_iff_integrable_sq_norm hD.1).1 hD).const_mul _) (fun y => ?_)
    have h := (H (y - s • z) - H y).le_opNorm₂ z z
    calc ‖(H (y - s • z) - H y) z z‖ ^ 2 ≤ (‖H (y - s • z) - H y‖ * ‖z‖ * ‖z‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = (‖z‖ ^ 2) ^ 2 * ‖H (y - s • z) - H y‖ ^ 2 := by ring
  rw [integral_const_mul] at hle
  calc Real.sqrt (∫ y, ‖(H (y - s • z) - H y) z z‖ ^ 2)
      ≤ Real.sqrt ((‖z‖ ^ 2) ^ 2 * ∫ y, ‖H (y - s • z) - H y‖ ^ 2) := Real.sqrt_le_sqrt hle
    _ = ‖z‖ ^ 2 * Real.sqrt (∫ y, ‖H (y - s • z) - H y‖ ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

private theorem pairProd_integrable {X Y : Space → Space} (hX : Continuous X) (hY : Continuous Y)
    (hYs : HasCompactSupport Y) : Integrable fun y => inner ℝ (X y) (Y y) := by
  refine (Continuous.inner (𝕜 := ℝ) hX hY).integrable_of_hasCompactSupport (hYs.mono ?_)
  intro y hy h0
  exact hy (by simp [h0])

private theorem sum_unit' (x : Space) : x = ∑ j : Fin 3, x j • unitVector j := by
  ext i
  simp [unitVector, Pi.single_apply]

private theorem expand_two {F : Type*} [AddCommGroup F] [Module ℝ F] (B : Space → Space → F)
    (hB1 : ∀ a a' b, B (a + a') b = B a b + B a' b) (hB2 : ∀ (c : ℝ) a b, B (c • a) b = c • B a b)
    (hB3 : ∀ a b b', B a (b + b') = B a b + B a b') (hB4 : ∀ (c : ℝ) a b, B a (c • b) = c • B a b)
    (a b : Space) :
    B a b = ∑ j : Fin 3, ∑ i : Fin 3, (a j * b i) • B (unitVector j) (unitVector i) := by
  let L1 : Space →ₗ[ℝ] F := ⟨⟨fun x => B x b, fun x y => hB1 x y b⟩, fun c x => hB2 c x b⟩
  have hL : ∀ j, B (unitVector j) b = ∑ i : Fin 3, b i • B (unitVector j) (unitVector i) := by
    intro j
    let L2 : Space →ₗ[ℝ] F := ⟨⟨fun x => B (unitVector j) x, fun x y => hB3 _ x y⟩, fun c x => hB4 c _ x⟩
    conv_lhs => rw [sum_unit' b]
    exact map_sum L2 _ _ |>.trans (Finset.sum_congr rfl fun i _ => map_smul L2 _ _)
  have h1 : B a b = ∑ j : Fin 3, a j • B (unitVector j) b := by
    conv_lhs => rw [sum_unit' a]
    exact map_sum L1 _ _ |>.trans (Finset.sum_congr rfl fun j _ => map_smul L1 _ _)
  rw [h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hL j, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]

private theorem weak_dir {v : Space → Space} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hv : ContDiff ℝ 1 v) (hH : IsWeakSecondDerivOf (fun y => fderiv ℝ v y) H) (hH2 : MemLp H 2 volume)
    {θ : Space → ℝ} (hθ : IsTestScalar θ) (a b : Space) :
    (Integrable fun y => fderiv ℝ θ y a • fderiv ℝ v y b) ∧ (Integrable fun y => θ y • H y a b) ∧
      ∫ y, fderiv ℝ θ y a • fderiv ℝ v y b = -∫ y, θ y • H y a b := by
  have hG : Continuous fun y => fderiv ℝ v y := hv.continuous_fderiv (by norm_num)
  have hθ1 : Continuous fun y => fderiv ℝ θ y := hθ.1.continuous_fderiv (by norm_cast)
  have hθs : HasCompactSupport fun y => fderiv ℝ θ y := hθ.2.fderiv (𝕜 := ℝ)
  have i1 : ∀ a b : Space, Integrable fun y => fderiv ℝ θ y a • fderiv ℝ v y b := by
    intro a b
    exact ((hG.clm_apply continuous_const).locallyIntegrable).integrable_smul_left_of_hasCompactSupport
      (hθ1.clm_apply continuous_const) (hθs.comp_left (g := fun L : Space →L[ℝ] ℝ => L a) (by simp))
  have i2 : ∀ a b : Space, Integrable fun y => θ y • H y a b := by
    intro a b
    have hm : MemLp (fun y => H y a b) 2 volume :=
      ((ContinuousLinearMap.apply ℝ Space b).comp
        (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) a)).comp_memLp' hH2
    exact (hm.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hθ.1.continuous hθ.2
  refine ⟨i1 a b, i2 a b, ?_⟩
  have e1 := expand_two (fun a b => ∫ y, fderiv ℝ θ y a • fderiv ℝ v y b)
    (fun a a' b => by simp only [map_add, add_smul]; exact integral_add (i1 a b) (i1 a' b))
    (fun c a b => by simp only [map_smul, smul_eq_mul, mul_smul]; exact integral_smul c _)
    (fun a b b' => by simp only [map_add, smul_add]; exact integral_add (i1 a b) (i1 a b'))
    (fun c a b => by simp only [map_smul, smul_comm _ c]; exact integral_smul c _) a b
  have e2 := expand_two (fun a b => ∫ y, θ y • H y a b)
    (fun a a' b => by simp only [map_add, ContinuousLinearMap.add_apply, smul_add]; exact integral_add (i2 a b) (i2 a' b))
    (fun c a b => by simp only [map_smul, ContinuousLinearMap.smul_apply, smul_comm _ c]; exact integral_smul c _)
    (fun a b b' => by simp only [map_add, smul_add]; exact integral_add (i2 a b) (i2 a b'))
    (fun c a b => by simp only [map_smul, smul_comm _ c]; exact integral_smul c _) a b
  simp only at e1 e2
  rw [e1, e2, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_neg]
  congr 1
  exact hH θ hθ i j

theorem second_pairing_by_parts {v : Space → Space}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hv : ContDiff ℝ 1 v)
    (hH : IsWeakSecondDerivOf (fun y => fderiv ℝ v y) H) (hH2 : MemLp H 2 volume)
    {ψ : Space → Space} (hψ : IsTestVectorField ψ) (w : Space) :
    ∫ y, inner ℝ (v y) (iteratedFDeriv ℝ 2 ψ y ![w, w]) = ∫ y, inner ℝ (H y w w) (ψ y) := by
  have hG : Continuous fun y => fderiv ℝ v y := hv.continuous_fderiv (by norm_num)
  have hd1 : ContDiff ℝ 2 (fderiv ℝ ψ) := hψ.1.fderiv_right (by norm_cast)
  have hd2 : Differentiable ℝ (fderiv ℝ ψ) := hd1.differentiable (by norm_num)
  have hψd : Differentiable ℝ ψ := hψ.1.differentiable (by norm_cast)
  have hχc : ContDiff ℝ 2 (fun x => fderiv ℝ ψ x w) := hd1.clm_apply contDiff_const
  have hχs : HasCompactSupport (fun x => fderiv ℝ ψ x w) :=
    (hψ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] Space => L w) (by simp)
  have hχd : ∀ x, fderiv ℝ (fun x => fderiv ℝ ψ x w) x w = iteratedFDeriv ℝ 2 ψ x ![w, w] := by
    intro x
    rw [iteratedFDeriv_two_apply]
    have h := (hd2 x).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
    rw [h.fderiv]
    simp
  have hχ1 : Continuous fun x => fderiv ℝ (fun x => fderiv ℝ ψ x w) x w :=
    (hχc.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hχ1s : HasCompactSupport fun x => fderiv ℝ (fun x => fderiv ℝ ψ x w) x w :=
    (hχs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] Space => L w) (by simp)
  have ibp : ∫ x, inner ℝ (v x) (fderiv ℝ (fun x => fderiv ℝ ψ x w) x w) =
      -∫ x, inner ℝ (fderiv ℝ v x w) (fderiv ℝ ψ x w) :=
    integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := volume)
      (B := innerSL ℝ) (f := v) (g := fun x => fderiv ℝ ψ x w) (v := w)
      (pairProd_integrable (hG.clm_apply continuous_const) hχc.continuous hχs)
      (pairProd_integrable hv.continuous hχ1 hχ1s)
      (pairProd_integrable hv.continuous hχc.continuous hχs)
      (fun x _ => hv.differentiable (by norm_num) x) (fun x _ => (hχc.differentiable (by norm_num)) x)
  simp only [hχd] at ibp
  rw [ibp]
  have hcomp : ∀ (k : Fin 3) x, fderiv ℝ (fun y => ψ y k) x w = fderiv ℝ ψ x w k := by
    intro k x
    have h := ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).hasFDerivAt.comp x (hψd x).hasFDerivAt)
    rw [show (fun y => ψ y k) = (EuclideanSpace.proj k : Space →L[ℝ] ℝ) ∘ ψ from rfl, h.fderiv]
    rfl
  have htest : ∀ k : Fin 3, IsTestScalar (fun y => ψ y k) := fun k =>
    ⟨(EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp hψ.1,
      hψ.2.comp_left (g := fun x : Space => x k) (by simp)⟩
  have hk : ∀ k : Fin 3, ∫ y, fderiv ℝ (fun y => ψ y k) y w * fderiv ℝ v y w k =
      -∫ y, ψ y k * H y w w k := by
    intro k
    obtain ⟨i1, i2, e⟩ := weak_dir hv hH hH2 (htest k) w w
    have a1 := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integral_comp_comm i1
    have a2 := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integral_comp_comm i2
    simp only [map_smul, smul_eq_mul] at a1 a2
    rw [show (∫ y, fderiv ℝ (fun y => ψ y k) y w * fderiv ℝ v y w k) =
        (EuclideanSpace.proj k : Space →L[ℝ] ℝ) (∫ y, fderiv ℝ (fun y => ψ y k) y w • fderiv ℝ v y w) from a1,
      show (∫ y, ψ y k * H y w w k) =
        (EuclideanSpace.proj k : Space →L[ℝ] ℝ) (∫ y, ψ y k • H y w w) from a2, e, map_neg]
  have hsum1 : ∀ y, inner ℝ (fderiv ℝ v y w) (fderiv ℝ ψ y w) =
      ∑ k : Fin 3, fderiv ℝ (fun y => ψ y k) y w * fderiv ℝ v y w k := by
    intro y
    simp only [hcomp, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  have hsum2 : ∀ y, inner ℝ (H y w w) (ψ y) = ∑ k : Fin 3, ψ y k * H y w w k := by
    intro y
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  have int1 : ∀ k : Fin 3, Integrable (fun y =>
      fderiv ℝ (fun y => ψ y k) y w * fderiv ℝ v y w k) (volume : Measure Space) := fun k => by
    have h := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integrable_comp
      (weak_dir hv hH hH2 (htest k) w w).1
    simp only [map_smul, smul_eq_mul] at h
    exact h
  have int2 : ∀ k : Fin 3, Integrable (fun y => ψ y k * H y w w k) (volume : Measure Space) :=
    fun k => by
    have h := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integrable_comp
      (weak_dir hv hH hH2 (htest k) w w).2.1
    simp only [map_smul, smul_eq_mul] at h
    exact h
  simp only [hsum1, hsum2]
  rw [integral_finsetSum _ (fun k _ => int1 k), integral_finsetSum _ (fun k _ => int2 k)]
  simp only [hk, Finset.sum_neg_distrib, neg_neg]

theorem remainder_integral_form {φ : Space → Space} (hφ : ContDiff ℝ 2 φ) (y z : Space) :
    secondOrderRemainder φ y z = ∫ s in (0 : ℝ)..1,
      (1 - s) • (iteratedFDeriv ℝ 2 φ (y + s • z) ![z, z] - iteratedFDeriv ℝ 2 φ y ![z, z]) := by
  set c := iteratedFDeriv ℝ 2 φ y ![z, z]
  have hd1 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hline : ∀ s : ℝ, HasDerivAt (fun t : ℝ => y + t • z) z s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const z).const_add y
  have hg : ∀ s : ℝ, HasDerivAt (fun t : ℝ => φ (y + t • z)) (fderiv ℝ φ (y + s • z) z) s :=
    fun s => (hd1 (y + s • z)).hasFDerivAt.comp_hasDerivAt s (hline s)
  have hg1 : ∀ s : ℝ, HasDerivAt (fun t : ℝ => fderiv ℝ φ (y + t • z) z)
      (fderiv ℝ (fderiv ℝ φ) (y + s • z) z z) s := fun s => by
    have h := (hd2 (y + s • z)).hasFDerivAt.comp_hasDerivAt s (hline s)
    simpa using h.clm_apply (hasDerivAt_const s z)
  have hF : ∀ s : ℝ, HasDerivAt
      (fun t : ℝ => (1 - t) • fderiv ℝ φ (y + t • z) z + φ (y + t • z) + ((1 - t) ^ 2 / 2) • c)
      ((1 - s) • (iteratedFDeriv ℝ 2 φ (y + s • z) ![z, z] - c)) s := by
    intro s
    have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub 1
    have h2 : HasDerivAt (fun t : ℝ => (1 - t) ^ 2 / 2) (-(1 - s)) s := by
      have := (h1.pow 2).div_const 2
      refine this.congr_deriv ?_
      push_cast
      ring
    have h := ((h1.smul (hg1 s)).add (hg s)).add (h2.smul_const c)
    refine h.congr_deriv ?_
    rw [iteratedFDeriv_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [smul_sub]
    module
  have hcont : Continuous fun s : ℝ => (1 - s) • (iteratedFDeriv ℝ 2 φ (y + s • z) ![z, z] - c) := by
    have hD : Continuous fun x => iteratedFDeriv ℝ 2 φ x := hφ.continuous_iteratedFDeriv le_rfl
    have hc : Continuous fun s : ℝ => iteratedFDeriv ℝ 2 φ (y + s • z) ![z, z] :=
      (continuous_eval_const (![z, z] : Fin 2 → Space) :
        Continuous fun f : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space) Space => f ![z, z]).comp
        (hD.comp (continuous_const.add (continuous_id.smul continuous_const)))
    exact (continuous_const.sub continuous_id).smul (hc.sub continuous_const)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hF s) (hcont.intervalIntegrable 0 1)]
  simp only [secondOrderRemainder, c]
  simp
  module

theorem pairing_swap {v : Space → Space} (hv : Continuous v) {φ : Space → Space}
    (hφ : IsTestVectorField φ) (z : Space) :
    ∫ y, inner ℝ (v y) (∫ s in (0 : ℝ)..1,
      (1 - s) • (iteratedFDeriv ℝ 2 φ (y + s • z) ![z, z] - iteratedFDeriv ℝ 2 φ y ![z, z])) =
      ∫ s in (0 : ℝ)..1, (1 - s) * ∫ y, inner ℝ (v y)
        (iteratedFDeriv ℝ 2 φ (y + s • z) ![z, z] - iteratedFDeriv ℝ 2 φ y ![z, z]) := by
  have hD2 : Continuous fun x => iteratedFDeriv ℝ 2 φ x :=
    hφ.1.continuous_iteratedFDeriv (by norm_cast)
  have hev : Continuous fun f : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space) Space => f ![z, z] :=
    continuous_eval_const (![z, z] : Fin 2 → Space)
  have hDc : Continuous fun p : Space × ℝ =>
      iteratedFDeriv ℝ 2 φ (p.1 + p.2 • z) ![z, z] - iteratedFDeriv ℝ 2 φ p.1 ![z, z] :=
    (hev.comp (hD2.comp (continuous_fst.add (continuous_snd.smul continuous_const)))).sub
      (hev.comp (hD2.comp continuous_fst))
  have ha : ∀ y, inner ℝ (v y) (∫ s in (0 : ℝ)..1, (1 - s) •
      (iteratedFDeriv ℝ 2 φ (y + s • z) ![z, z] - iteratedFDeriv ℝ 2 φ y ![z, z])) =
      ∫ s in (0 : ℝ)..1, (1 - s) * inner ℝ (v y)
        (iteratedFDeriv ℝ 2 φ (y + s • z) ![z, z] - iteratedFDeriv ℝ 2 φ y ![z, z]) := by
    intro y
    have hi : IntervalIntegrable (fun s : ℝ => (1 - s) •
        (iteratedFDeriv ℝ 2 φ (y + s • z) ![z, z] - iteratedFDeriv ℝ 2 φ y ![z, z])) volume 0 1 :=
      ((continuous_const.sub continuous_id).smul
        (hDc.comp (continuous_const.prodMk continuous_id))).intervalIntegrable 0 1
    rw [← innerSL_apply_apply (𝕜 := ℝ), ← (innerSL ℝ (v y)).intervalIntegral_comp_comm hi]
    simp only [innerSL_apply_apply, inner_smul_right]
  simp only [ha]
  set χ : ℝ → ℝ := fun s => max 0 (min (1 - s) (s + 1)) with hχ
  have hχc : Continuous χ :=
    continuous_const.max ((continuous_const.sub continuous_id).min (continuous_id.add continuous_const))
  have hχe : ∀ s ∈ Set.Icc (0 : ℝ) 1, χ s = 1 - s := by
    intro s hs
    simp only [hχ]
    rw [min_eq_left (by linarith [hs.1]), max_eq_right (by linarith [hs.2])]
  set G : Space → ℝ → ℝ := fun y s => χ s * inner ℝ (v y)
    (iteratedFDeriv ℝ 2 φ (y + s • z) ![z, z] - iteratedFDeriv ℝ 2 φ y ![z, z]) with hG
  have hGc : Continuous (Function.uncurry G) :=
    (hχc.comp continuous_snd).mul (Continuous.inner (𝕜 := ℝ) (hv.comp continuous_fst) hDc)
  have hK : IsCompact (tsupport φ) := hφ.2
  have hGs : HasCompactSupport (Function.uncurry G) := by
    refine HasCompactSupport.intro (K := ((fun p : Space × ℝ => (p.1 - p.2 • z, p.2)) ''
      (tsupport φ ×ˢ Set.Icc (-1) 1)) ∪ (tsupport φ ×ˢ Set.Icc (-1) 1)) ?_ ?_
    · exact ((hK.prod isCompact_Icc).image (by fun_prop)).union (hK.prod isCompact_Icc)
    · rintro ⟨y, s⟩ hp
      simp only [Function.uncurry_apply_pair, hG]
      by_cases hs : s ∈ Set.Icc (-1 : ℝ) 1
      · have hy : y ∉ tsupport φ := fun hy => hp (Or.inr ⟨hy, hs⟩)
        have hy' : y + s • z ∉ tsupport φ := fun hy' =>
          hp (Or.inl ⟨(y + s • z, s), ⟨hy', hs⟩, by simp⟩)
        have h0 : ∀ x ∉ tsupport φ, iteratedFDeriv ℝ 2 φ x = 0 := fun x hx =>
          Function.notMem_support.mp fun h => hx (support_iteratedFDeriv_subset 2 h)
        rw [h0 _ hy, h0 _ hy']
        simp
      · have hχ0 : χ s = 0 := by
          simp only [Set.mem_Icc, not_and_or, not_le] at hs
          simp only [hχ]
          rcases hs with h | h
          · exact max_eq_left (by linarith [min_le_right (1 - s) (s + 1)])
          · exact max_eq_left (by linarith [min_le_left (1 - s) (s + 1)])
        rw [hχ0, zero_mul]
  have hGi : Integrable (Function.uncurry G) ((volume : Measure Space).prod (volume : Measure ℝ)) :=
    hGc.integrable_of_hasCompactSupport hGs
  have hGr : Integrable (Function.uncurry G)
      ((volume : Measure Space).prod ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))) := by
    have h := hGi.restrict (s := Set.univ ×ˢ Set.Ioc (0 : ℝ) 1)
    rwa [← Measure.prod_restrict, Measure.restrict_univ] at h
  have e1 : ∀ y, ∫ s in (0 : ℝ)..1, (1 - s) * inner ℝ (v y)
      (iteratedFDeriv ℝ 2 φ (y + s • z) ![z, z] - iteratedFDeriv ℝ 2 φ y ![z, z]) =
      ∫ s in Set.Ioc (0 : ℝ) 1, G y s := by
    intro y
    rw [intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    simp only [hG, hχe s ⟨hs.1.le, hs.2⟩]
  have e2 : ∫ s in (0 : ℝ)..1, (1 - s) * ∫ y, inner ℝ (v y)
      (iteratedFDeriv ℝ 2 φ (y + s • z) ![z, z] - iteratedFDeriv ℝ 2 φ y ![z, z]) =
      ∫ s in Set.Ioc (0 : ℝ) 1, ∫ y, G y s := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    simp only [hG, hχe s ⟨hs.1.le, hs.2⟩]
    rw [integral_const_mul]
  simp only [e1]
  rw [e2]
  exact integral_integral_swap hGr

private theorem test_shift {φ : Space → Space} (hφ : IsTestVectorField φ) (c : Space) :
    IsTestVectorField (fun y => φ (y + c)) :=
  ⟨hφ.1.comp (contDiff_id.add contDiff_const), hφ.2.comp_homeomorph (Homeomorph.addRight c)⟩

private theorem second_integrable {v : Space → Space} (hv : Continuous v) {ψ : Space → Space}
    (hψ : IsTestVectorField ψ) (w : Space) :
    Integrable (fun y => inner ℝ (v y) (iteratedFDeriv ℝ 2 ψ y ![w, w])) := by
  have hd : Continuous fun y => iteratedFDeriv ℝ 2 ψ y :=
    hψ.1.continuous_iteratedFDeriv (by norm_cast)
  have hc : Continuous fun y => iteratedFDeriv ℝ 2 ψ y ![w, w] :=
    (continuous_eval_const (![w, w] : Fin 2 → Space) :
      Continuous fun f : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space) Space => f ![w, w]).comp hd
  refine (Continuous.inner (𝕜 := ℝ) hv hc).integrable_of_hasCompactSupport ?_
  refine (hψ.2.iteratedFDeriv (𝕜 := ℝ) 2).mono ?_
  intro y hy
  rw [Function.mem_support] at hy ⊢
  intro h0
  apply hy
  rw [h0]
  simp

private theorem eval_memLp {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hH2 : MemLp H 2 volume)
    (w : Space) : MemLp (fun y => H y w w) 2 volume :=
  ((ContinuousLinearMap.apply ℝ Space w).comp
    (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) w)).comp_memLp' hH2

private theorem inner_integrable2 {X Y : Space → Space} (hX : MemLp X 2 volume)
    (hY : MemLp Y 2 volume) : Integrable (fun y => inner ℝ (X y) (Y y)) := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hX.toLp X) (hY.toLp Y)).congr ?_
  filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with y a b
  rw [a, b]

theorem remainder_pairing_eq {v : Space → Space}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hv : ContDiff ℝ 1 v) (hv6 : MemLp v 6 volume)
    (hH : IsWeakSecondDerivOf (fun y => fderiv ℝ v y) H) (hH2 : MemLp H 2 volume)
    {φ : Space → Space} (hφ : IsTestVectorField φ) (z : Space) :
    ∫ y, inner ℝ (v y) (secondOrderRemainder φ y z) =
      ∫ s in (0 : ℝ)..1, (1 - s) * ∫ y, inner ℝ ((H (y - s • z) - H y) z z) (φ y) := by
  have hφ2 : MemLp φ 2 volume := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2
  have e1 : ∫ y, inner ℝ (v y) (secondOrderRemainder φ y z) =
      ∫ y, inner ℝ (v y) (∫ s in (0 : ℝ)..1,
        (1 - s) • (iteratedFDeriv ℝ 2 φ (y + s • z) ![z, z] - iteratedFDeriv ℝ 2 φ y ![z, z])) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    try dsimp only
    rw [remainder_integral_form (hφ.1.of_le (by norm_cast)) y z]
  rw [e1, pairing_swap hv.continuous hφ z]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  try dsimp only
  congr 1
  have hsh : ∀ y, iteratedFDeriv ℝ 2 φ (y + s • z) ![z, z] =
      iteratedFDeriv ℝ 2 (fun x => φ (x + s • z)) y ![z, z] := fun y => by
    rw [iteratedFDeriv_comp_add_right]
  simp only [hsh, inner_sub_right]
  rw [integral_sub (second_integrable hv.continuous (test_shift hφ (s • z)) z)
      (second_integrable hv.continuous hφ z),
    second_pairing_by_parts hv hH hH2 (test_shift hφ (s • z)) z,
    second_pairing_by_parts hv hH hH2 hφ z]
  have e2 : ∫ y, inner ℝ (H y z z) (φ (y + s • z)) = ∫ y, inner ℝ (H (y - s • z) z z) (φ y) := by
    rw [← integral_sub_right_eq_self (fun y => inner ℝ (H y z z) (φ (y + s • z))) (s • z)]
    simp only [sub_add_cancel]
  rw [e2, ← integral_sub (inner_integrable2 (eval_memLp (shift_memLp hH2 (s • z)) z) hφ2)
    (inner_integrable2 (eval_memLp hH2 z) hφ2)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show inner ℝ (H (y - s • z) z z) (φ y) - inner ℝ (H y z z) (φ y) =
    inner ℝ ((H (y - s • z) - H y) z z) (φ y)
  rw [← inner_sub_left]
  rfl

theorem remainder_pairing_bound {v : Space → Space}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hv : ContDiff ℝ 1 v) (hv6 : MemLp v 6 volume)
    (hH : IsWeakSecondDerivOf (fun y => fderiv ℝ v y) H) (hH2 : MemLp H 2 volume)
    (hmod : ∃ C : ℝ, ∀ h : Space, ‖h‖ ≤ 1 → ∫ y, ‖H (y + h) - H y‖ ^ 2 ≤ C * ‖h‖) :
    ∃ A : ℝ, ∀ φ : Space → Space, IsTestVectorField φ → ∀ z : Space,
      |∫ y, inner ℝ (v y) (secondOrderRemainder φ y z)| ≤
        A * (if ‖z‖ < 1 then ‖z‖ ^ (5 / 2 : ℝ) else ‖z‖ ^ 2) * Real.sqrt (∫ y, ‖φ y‖ ^ 2) := by
  obtain ⟨C, hC⟩ := hmod
  refine ⟨max (Real.sqrt |C|) (2 * Real.sqrt (∫ y, ‖H y‖ ^ 2)), fun φ hφ z => ?_⟩
  have hφ2 : MemLp φ 2 volume := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2
  have hS : 0 ≤ Real.sqrt (∫ y, ‖φ y‖ ^ 2) := Real.sqrt_nonneg _
  rw [remainder_pairing_eq hv hv6 hH hH2 hφ z]
  have key : ∀ B : ℝ, (∀ s ∈ Set.Icc (0 : ℝ) 1, Real.sqrt (∫ y, ‖H (y - s • z) - H y‖ ^ 2) ≤ B) →
      |∫ s in (0 : ℝ)..1, (1 - s) * ∫ y, inner ℝ ((H (y - s • z) - H y) z z) (φ y)| ≤
        ‖z‖ ^ 2 * B * Real.sqrt (∫ y, ‖φ y‖ ^ 2) := by
    intro B hB
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := ‖z‖ ^ 2 * B * Real.sqrt (∫ y, ‖φ y‖ ^ 2))
      (f := fun s => (1 - s) * ∫ y, inner ℝ ((H (y - s • z) - H y) z z) (φ y)) (fun s hs => by
        rw [Set.uIoc_of_le zero_le_one] at hs
        have hs0 : 0 ≤ 1 - s := by linarith [hs.2]
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hs0]
        refine (mul_le_of_le_one_left (abs_nonneg _) (by linarith [hs.1])).trans ?_
        refine (pair_step hH2 hφ2 s z).trans ?_
        have hb := hB s ⟨hs.1.le, hs.2⟩
        gcongr)
    rw [Real.norm_eq_abs] at h
    simpa using h
  by_cases hz : ‖z‖ < 1
  · rw [if_pos hz]
    refine (key _ fun s hs => Real.sqrt_le_sqrt (diff_le_mod C hC hs.1 hs.2 hz.le)).trans ?_
    rw [Real.sqrt_mul (abs_nonneg C)]
    have e : ‖z‖ ^ 2 * (Real.sqrt |C| * Real.sqrt ‖z‖) = Real.sqrt |C| * ‖z‖ ^ (5 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow ‖z‖, ← Real.rpow_natCast ‖z‖ 2, mul_left_comm,
        ← Real.rpow_add' (norm_nonneg z) (show ((2 : ℕ) : ℝ) + 1 / 2 ≠ 0 by norm_num)]
      norm_num
    rw [e]
    gcongr
    exact le_max_left _ _
  · rw [if_neg hz]
    refine (key _ fun s _ => diff_le_two hH2 (s • z)).trans ?_
    have e : ‖z‖ ^ 2 * (2 * Real.sqrt (∫ y, ‖H y‖ ^ 2)) * Real.sqrt (∫ y, ‖φ y‖ ^ 2) =
        (2 * Real.sqrt (∫ y, ‖H y‖ ^ 2)) * ‖z‖ ^ 2 * Real.sqrt (∫ y, ‖φ y‖ ^ 2) := by ring
    rw [e]
    gcongr
    exact le_max_right _ _

private theorem rem_far_le (f : Space → Space) (x z : Space) (hz : 1 ≤ ‖z‖) :
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

private theorem near_far_integrable {f : Space → ℝ} (hf : AEStronglyMeasurable f volume) {a b C : ℝ}
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

private theorem translate_bound6 {v φ : Space → Space} (hv : Continuous v) (hv6 : MemLp v 6 volume)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ∃ A : ℝ, ∀ w : Space, Integrable (fun x => ‖v x‖ * ‖φ (x + w)‖) ∧
      ∫ x, ‖v x‖ * ‖φ (x + w)‖ ≤ A := by
  have hint : ∀ w : Space, Integrable (fun x => ‖v x‖ * ‖φ (x + w)‖) := by
    intro w
    have hc : HasCompactSupport (fun x => φ (x + w)) := hφc.comp_homeomorph (Homeomorph.addRight w)
    refine (hv.norm.mul (hφ.comp (continuous_add_const w)).norm).integrable_of_hasCompactSupport ?_
    exact hc.norm.mul_left
  have hL6 : MemLp v ((6 : ℕ) : ENNReal) volume := by exact_mod_cast hv6
  have hv6i : Integrable (fun x => ‖v x‖ ^ 6) := hL6.integrable_norm_pow (by norm_num)
  have hφr : Continuous fun x => ‖φ x‖ ^ (6 / 5 : ℝ) :=
    hφ.norm.rpow_const fun _ => Or.inr (by norm_num)
  have hφri : Integrable fun x => ‖φ x‖ ^ (6 / 5 : ℝ) :=
    hφr.integrable_of_hasCompactSupport
      (hφc.norm.comp_left (g := fun t : ℝ => t ^ (6 / 5 : ℝ)) (by norm_num))
  have hY : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a * b ≤ a ^ 6 + b ^ (6 / 5 : ℝ) := by
    intro a b ha hb
    have h := Real.young_inequality_of_nonneg ha hb
      (show (6 : ℝ).HolderConjugate (6 / 5) from Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    have h6 : 0 ≤ a ^ 6 := by positivity
    have h65 : 0 ≤ b ^ (6 / 5 : ℝ) := Real.rpow_nonneg hb _
    push_cast at h
    linarith
  refine ⟨(∫ x, ‖v x‖ ^ 6) + ∫ x, ‖φ x‖ ^ (6 / 5 : ℝ), fun w => ⟨hint w, ?_⟩⟩
  have hs : Integrable (fun x => ‖φ (x + w)‖ ^ (6 / 5 : ℝ)) := hφri.comp_add_right w
  calc ∫ x, ‖v x‖ * ‖φ (x + w)‖ ≤ ∫ x, (‖v x‖ ^ 6 + ‖φ (x + w)‖ ^ (6 / 5 : ℝ)) :=
        integral_mono (hint w) (hv6i.add hs) fun x => hY _ _ (norm_nonneg _) (norm_nonneg _)
    _ = (∫ x, ‖v x‖ ^ 6) + ∫ x, ‖φ x‖ ^ (6 / 5 : ℝ) := by
        rw [integral_add hv6i hs, integral_add_right_eq_self (fun x => ‖φ x‖ ^ (6 / 5 : ℝ)) w]

private theorem rpow_pow_eq (t r : ℝ) (ht : 0 ≤ t) (n : ℕ) (hr : r ≠ 0) (hrn : r + n ≠ 0) :
    t ^ r * t ^ n = t ^ (r + n) := by
  rcases ht.eq_or_lt with h | h
  · rw [← h, Real.zero_rpow hr, Real.zero_rpow hrn, zero_mul]
  · rw [← Real.rpow_natCast, ← Real.rpow_add h]

private theorem rem_continuous_pair {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) :
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
  exact (((hc.comp (continuous_fst.add continuous_snd)).sub (hc.comp continuous_fst)).sub h4).sub
    (h3.const_smul (1 / 2 : ℝ))

private theorem rem_continuous_section {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (z : Space) :
    Continuous (fun x : Space => secondOrderRemainder φ x z) := by
  have h1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have h2 : Continuous (iteratedFDeriv ℝ 2 φ) := hφ.continuous_iteratedFDeriv (by norm_cast)
  have hc := hφ.continuous
  have h3 : Continuous (fun x : Space => iteratedFDeriv ℝ 2 φ x ![z, z]) :=
    continuous_eval.comp (h2.prodMk continuous_const)
  have h4 : Continuous (fun x : Space => fderiv ℝ φ x z) := h1.clm_apply continuous_const
  exact (((hc.comp (continuous_add_const z)).sub hc).sub h4).sub (h3.const_smul (1 / 2 : ℝ))

private theorem rem_zero_far (φ : Space → Space) (x z : Space) {r : ℝ} (hz : ‖z‖ ≤ r)
    (hx : x ∉ Metric.cthickening r (tsupport φ)) : secondOrderRemainder φ x z = 0 := by
  have hx0 : x ∉ tsupport φ := fun h => hx (Metric.self_subset_cthickening _ h)
  have e1 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx0
  have e2 : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ hx0
  have e3 : iteratedFDeriv ℝ 2 φ x = 0 := by
    by_contra h
    exact hx0 (support_iteratedFDeriv_subset 2 (Function.mem_support.mpr h))
  have e4 : φ (x + z) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    apply hx
    apply Metric.mem_cthickening_of_dist_le x (x + z) r _ h
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left]
    exact hz
  simp [secondOrderRemainder, e1, e2, e3, e4]

private theorem prod_integrable6 {α : ℝ} (hα1 : 1 < α) (hα2 : α < 3 / 2) {v φ : Space → Space}
    (hvc : Continuous v) (hv6 : MemLp v 6 volume) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Integrable (fun p : Space × Space =>
      ‖p.2‖ ^ (-(3 + 2 * α)) * inner ℝ (v p.1) (secondOrderRemainder φ p.1 p.2))
      ((volume : Measure Space).prod (volume : Measure Space)) := by
  have hφ0 : Continuous φ := hφ.continuous
  have hRj := rem_continuous_pair hφ
  have hRc : ∀ z, Continuous (fun x => secondOrderRemainder φ x z) := rem_continuous_section hφ
  have hjoint : Continuous (fun p : Space × Space => inner ℝ (v p.1) (secondOrderRemainder φ p.1 p.2)) :=
    Continuous.inner (𝕜 := ℝ) (hvc.comp continuous_fst) hRj
  have hFm : Measurable (fun p : Space × Space =>
      ‖p.2‖ ^ (-(3 + 2 * α)) * inner ℝ (v p.1) (secondOrderRemainder φ p.1 p.2)) :=
    ((measurable_snd.norm).pow_const _).mul hjoint.measurable
  have hSc : IsCompact (tsupport φ) := hφc
  have hsec : ∀ z : Space, Integrable (fun x =>
      ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder φ x z)) := by
    intro z
    refine (continuous_const.mul (Continuous.inner (𝕜 := ℝ) hvc (hRc z))).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (hSc.cthickening (r := ‖z‖)) (fun x hx => ?_)
    simp [rem_zero_far φ x z le_rfl hx]
  rw [integrable_prod_iff' hFm.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall hsec, ?_⟩
  have hT : IsCompact (Metric.cthickening 1 (tsupport φ)) := hSc.cthickening
  obtain ⟨C3, hC3⟩ := (hφ.continuous_iteratedFDeriv (m := 3) (by norm_cast)).bounded_above_of_compact_support
    (hφc.iteratedFDeriv 3)
  obtain ⟨A, hA⟩ := translate_bound6 hvc hv6 hφ0 hφc
  have hA0 : 0 ≤ A := le_trans (integral_nonneg (fun x => by positivity)) (hA 0).2
  have hφ3 : ContDiff ℝ 3 φ := hφ.of_le (by norm_cast)
  have hvT : Integrable ((Metric.cthickening 1 (tsupport φ)).indicator (fun x => ‖v x‖)) :=
    (hvc.norm.continuousOn.integrableOn_compact hT).integrable_indicator hT.measurableSet
  have hzero : ∀ x, x ∉ tsupport φ →
      ‖φ x‖ + ‖fderiv ℝ φ x‖ + ‖iteratedFDeriv ℝ 2 φ x‖ = 0 := by
    intro x hx0
    have e1 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx0
    have e2 : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ hx0
    have e3 : iteratedFDeriv ℝ 2 φ x = 0 := by
      by_contra h
      exact hx0 (support_iteratedFDeriv_subset 2 (Function.mem_support.mpr h))
    simp [e1, e2, e3]
  have hPc : Continuous (fun x => ‖v x‖ * (‖φ x‖ + ‖fderiv ℝ φ x‖ + ‖iteratedFDeriv ℝ 2 φ x‖)) :=
    hvc.norm.mul ((hφ0.norm.add (hφ.continuous_fderiv (by simp)).norm).add
      (hφ.continuous_iteratedFDeriv (m := 2) (by norm_cast)).norm)
  have hPi : Integrable (fun x => ‖v x‖ * (‖φ x‖ + ‖fderiv ℝ φ x‖ + ‖iteratedFDeriv ℝ 2 φ x‖)) := by
    refine hPc.integrable_of_hasCompactSupport (HasCompactSupport.intro hSc (fun x hx => ?_))
    rw [hzero x hx, mul_zero]
  set cP := ∫ x, ‖v x‖ * (‖φ x‖ + ‖fderiv ℝ φ x‖ + ‖iteratedFDeriv ℝ 2 φ x‖) with hcP
  set I1 := ∫ x, (Metric.cthickening 1 (tsupport φ)).indicator (fun x => ‖v x‖) x with hI1
  have hcP0 : 0 ≤ cP := integral_nonneg (fun x => by positivity)
  have hI10 : 0 ≤ I1 := integral_nonneg (fun x => Set.indicator_nonneg (fun y _ => norm_nonneg (v y)) x)
  set C3' := max C3 0 with hC3'
  have hC3'0 : 0 ≤ C3' := le_max_right _ _
  apply near_far_integrable (a := 2 * α) (b := 1 + 2 * α) (C := C3' * I1 + (A + cP))
  · exact (hFm.norm.stronglyMeasurable.integral_prod_left' (μ := volume)).aestronglyMeasurable
  · linarith
  · linarith
  · intro z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have hK0 : 0 ≤ ‖z‖ ^ (-(3 + 2 * α)) := Real.rpow_nonneg (norm_nonneg _) _
    have hpt : ∀ x, ‖‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder φ x z)‖ ≤
        (‖z‖ ^ (-(3 + 2 * α)) * C3' * ‖z‖ ^ 3) *
          (Metric.cthickening 1 (tsupport φ)).indicator (fun x => ‖v x‖) x := by
      intro x
      rw [norm_mul, Real.norm_of_nonneg hK0, Real.norm_eq_abs, mul_assoc, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hK0
      by_cases hx : x ∈ Metric.cthickening 1 (tsupport φ)
      · rw [Set.indicator_of_mem hx]
        calc |inner ℝ (v x) (secondOrderRemainder φ x z)| ≤ ‖v x‖ * ‖secondOrderRemainder φ x z‖ :=
              abs_real_inner_le_norm _ _
          _ ≤ ‖v x‖ * (C3' * ‖z‖ ^ 3) :=
              mul_le_mul_of_nonneg_left
                (remainderBound φ hφ3 x z C3' (fun y _ => (hC3 y).trans (le_max_left _ _))) (norm_nonneg _)
          _ = C3' * (‖z‖ ^ 3 * ‖v x‖) := by ring
      · rw [Set.indicator_of_notMem hx, rem_zero_far φ x z hz hx]
        simp
    calc ∫ x, ‖‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder φ x z)‖
        ≤ ∫ x, (‖z‖ ^ (-(3 + 2 * α)) * C3' * ‖z‖ ^ 3) *
          (Metric.cthickening 1 (tsupport φ)).indicator (fun x => ‖v x‖) x :=
          integral_mono (hsec z).norm (hvT.const_mul _) hpt
      _ = (C3' * I1) * ‖z‖ ^ (-(2 * α)) := by
          rw [integral_const_mul]
          have := rpow_pow_eq ‖z‖ (-(3 + 2 * α)) (norm_nonneg _) 3 (by linarith) (by push_cast; linarith)
          have he : -(3 + 2 * α) + ((3 : ℕ) : ℝ) = -(2 * α) := by push_cast; ring
          rw [he] at this
          rw [← this]
          ring
      _ ≤ (C3' * I1 + (A + cP)) * ‖z‖ ^ (-(2 * α)) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)
  · intro z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have hK0 : 0 ≤ ‖z‖ ^ (-(3 + 2 * α)) := Real.rpow_nonneg (norm_nonneg _) _
    have hg : Integrable (fun x => ‖v x‖ * ‖φ (x + z)‖) := (hA z).1
    have hgA : ∫ x, ‖v x‖ * ‖φ (x + z)‖ ≤ A := (hA z).2
    have hpt : ∀ x, ‖‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder φ x z)‖ ≤
        ‖z‖ ^ (-(3 + 2 * α)) * (‖v x‖ * ‖φ (x + z)‖ +
          ‖v x‖ * (‖φ x‖ + ‖fderiv ℝ φ x‖ + ‖iteratedFDeriv ℝ 2 φ x‖) * ‖z‖ ^ 2) := by
      intro x
      rw [norm_mul, Real.norm_of_nonneg hK0, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ hK0
      refine le_trans (abs_real_inner_le_norm _ _) ?_
      have := mul_le_mul_of_nonneg_left (rem_far_le φ x z hz) (norm_nonneg (v x))
      refine le_trans this (le_of_eq ?_)
      ring
    have hz2 : 1 ≤ ‖z‖ ^ 2 := one_le_pow₀ hz
    calc ∫ x, ‖‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder φ x z)‖
        ≤ ∫ x, ‖z‖ ^ (-(3 + 2 * α)) * (‖v x‖ * ‖φ (x + z)‖ +
          ‖v x‖ * (‖φ x‖ + ‖fderiv ℝ φ x‖ + ‖iteratedFDeriv ℝ 2 φ x‖) * ‖z‖ ^ 2) :=
          integral_mono (hsec z).norm ((hg.add (hPi.mul_const _)).const_mul _) hpt
      _ = ‖z‖ ^ (-(3 + 2 * α)) * ((∫ x, ‖v x‖ * ‖φ (x + z)‖) + cP * ‖z‖ ^ 2) := by
          rw [integral_const_mul, integral_add hg (hPi.mul_const _), integral_mul_const]
      _ ≤ ‖z‖ ^ (-(3 + 2 * α)) * ((A + cP) * ‖z‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hK0
          nlinarith
      _ = (A + cP) * ‖z‖ ^ (-(1 + 2 * α)) := by
          have := rpow_pow_eq ‖z‖ (-(3 + 2 * α)) (norm_nonneg _) 2 (by linarith) (by push_cast; linarith)
          have he : -(3 + 2 * α) + ((2 : ℕ) : ℝ) = -(1 + 2 * α) := by push_cast; ring
          rw [he] at this
          rw [← this]
          ring
      _ ≤ (C3' * I1 + (A + cP)) * ‖z‖ ^ (-(1 + 2 * α)) :=
          mul_le_mul_of_nonneg_right (by nlinarith) (Real.rpow_nonneg (norm_nonneg _) _)

theorem pairing_eq_iterated {α : ℝ} (h1 : 1 < α) (h2 : α < 5 / 4) {v : Space → Space}
    (hv : Continuous v) (hv6 : MemLp v 6 volume) {φ : Space → Space} (hφ : IsTestVectorField φ) :
    ∫ y, inner ℝ (v y) (fractionalPowerAt α φ y) =
      (fractionalNormalizer α)⁻¹ *
        ∫ z : Space, ‖z‖ ^ (-(3 + 2 * α)) * ∫ y, inner ℝ (v y) (secondOrderRemainder φ y z) := by
  have h3 : α < 3 / 2 := by linarith
  have hPR := prod_integrable6 h1 h3 hv hv6 hφ.1 hφ.2
  obtain ⟨Cφ, hCφ⟩ := hφ.1.continuous.bounded_above_of_compact_support hφ.2
  have hRx : ∀ x, inner ℝ (v x) (fractionalPowerAt α φ x) = (fractionalNormalizer α)⁻¹ *
      ∫ z, ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder φ x z) := by
    intro x
    unfold fractionalPowerAt
    rw [real_inner_smul_right, ← integral_inner (remainderIntegrable α h1 h3 φ hφ.1 (Or.inr ⟨Cφ, hCφ⟩) x)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [real_inner_smul_right]
  simp only [hRx]
  rw [integral_const_mul]
  congr 1
  rw [integral_integral_swap (f := fun x z : Space =>
    ‖z‖ ^ (-(3 + 2 * α)) * inner ℝ (v x) (secondOrderRemainder φ x z)) hPR]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  rw [integral_const_mul]

private theorem weight_integrable {α : ℝ} (h1 : 1 < α) (h2 : α < 5 / 4) :
    Integrable (fun z : Space =>
      ‖z‖ ^ (-(3 + 2 * α)) * (if ‖z‖ < 1 then ‖z‖ ^ (5 / 2 : ℝ) else ‖z‖ ^ 2)) := by
  refine (integrable_fun_norm_addHaar (volume : Measure Space)
    (f := fun r : ℝ => r ^ (-(3 + 2 * α)) * (if r < 1 then r ^ (5 / 2 : ℝ) else r ^ 2))).mpr ?_
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  rw [← Set.Ioo_union_Ici_eq_Ioi zero_lt_one]
  refine IntegrableOn.union ?_ ?_
  · have h3 : IntegrableOn (fun y : ℝ => y ^ (3 / 2 - 2 * α)) (Set.Ioo 0 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)
    refine h3.congr_fun (fun y hy => ?_) measurableSet_Ioo
    simp only [if_pos hy.2]
    rw [← Real.rpow_natCast y 2, ← Real.rpow_add hy.1, ← Real.rpow_add hy.1]
    congr 1
    push_cast
    ring
  · have h3 : IntegrableOn (fun y : ℝ => y ^ (1 - 2 * α)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine h3.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy1 : (1 : ℝ) < y := hy
    have hy0 : (0 : ℝ) < y := by linarith
    simp only [if_neg (not_lt.mpr hy1.le)]
    rw [← Real.rpow_natCast y 2, ← Real.rpow_add hy0, ← Real.rpow_add hy0]
    congr 1
    push_cast
    ring

theorem pairing_bound_of_secondModulus {α : ℝ} (h1 : 1 < α) (h2 : α < 5 / 4) {v : Space → Space}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hv : ContDiff ℝ 1 v) (hv6 : MemLp v 6 volume)
    (hH : IsWeakSecondDerivOf (fun y => fderiv ℝ v y) H) (hH2 : MemLp H 2 volume)
    (hmod : ∃ C : ℝ, ∀ h : Space, ‖h‖ ≤ 1 → ∫ y, ‖H (y + h) - H y‖ ^ 2 ≤ C * ‖h‖) :
    ∃ K : ℝ, ∀ φ : Space → Space, IsTestVectorField φ →
      |∫ y, inner ℝ (v y) (fractionalPowerAt α φ y)| ≤ K * Real.sqrt (∫ y, ‖φ y‖ ^ 2) := by
  obtain ⟨A, hA⟩ := remainder_pairing_bound hv hv6 hH hH2 hmod
  refine ⟨|(fractionalNormalizer α)⁻¹| * (A * ∫ z : Space,
      ‖z‖ ^ (-(3 + 2 * α)) * (if ‖z‖ < 1 then ‖z‖ ^ (5 / 2 : ℝ) else ‖z‖ ^ 2)), fun φ hφ => ?_⟩
  have hpt : ∀ z : Space,
      ‖‖z‖ ^ (-(3 + 2 * α)) * ∫ y, inner ℝ (v y) (secondOrderRemainder φ y z)‖ ≤
        A * Real.sqrt (∫ y, ‖φ y‖ ^ 2) *
          (‖z‖ ^ (-(3 + 2 * α)) * (if ‖z‖ < 1 then ‖z‖ ^ (5 / 2 : ℝ) else ‖z‖ ^ 2)) := by
    intro z
    have hk : 0 ≤ ‖z‖ ^ (-(3 + 2 * α)) := Real.rpow_nonneg (norm_nonneg z) _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
    refine (mul_le_mul_of_nonneg_left (hA φ hφ z) hk).trans (le_of_eq ?_)
    ring
  have hb := norm_integral_le_of_norm_le ((weight_integrable h1 h2).const_mul
    (A * Real.sqrt (∫ y, ‖φ y‖ ^ 2))) (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul] at hb
  rw [pairing_eq_iterated h1 h2 hv.continuous hv6 hφ, abs_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [← Real.norm_eq_abs]
  refine hb.trans (le_of_eq ?_)
  ring

end ProfilePower

end FracInternal

end Breakdown
