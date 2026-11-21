/-
Copyright 2026 Anthropic, PBC
SPDX-License-Identifier: Apache-2.0

The within-interval norm derivative, coordinate cross-product derivative and frame
decomposition adapt the argument in
`sources/ccpoint-lean/CCPoint/Lib/R02/FrameMotionAux.lean`.
-/
import TorusEuler.CurlProjection
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

open scoped InnerProductSpace
open NormedSpace (normalize norm_smul_normalize norm_normalize)

namespace TorusEuler

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

private theorem normDerivOfScaled {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v : ℝ → E} {w : E} {s : Set ℝ} {t : ℝ}
    (hv : HasDerivWithinAt v (‖v t‖ • w) s t) (hzero : v t ≠ 0) :
    HasDerivWithinAt (fun u => ‖v u‖)
      (‖v t‖ * ⟪normalize (v t), w⟫_ℝ) s t := by
  have hn : 0 < ‖v t‖ := norm_pos_iff.mpr hzero
  have hsqrt := hv.norm_sq.sqrt (by positivity)
  have hfun : (fun u => Real.sqrt (‖v u‖ ^ 2)) = fun u => ‖v u‖ := by
    funext u
    exact Real.sqrt_sq (norm_nonneg _)
  rw [hfun, Real.sqrt_sq (norm_nonneg _)] at hsqrt
  refine hsqrt.congr_deriv ?_
  rw [real_inner_smul_right, NormedSpace.normalize, real_inner_smul_left]
  field_simp

private theorem normalizeDerivOfScaled {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v : ℝ → E} {w : E} {s : Set ℝ} {t : ℝ}
    (hv : HasDerivWithinAt v (‖v t‖ • w) s t) (hzero : v t ≠ 0) :
    HasDerivWithinAt (fun u => normalize (v u))
      (w - ⟪normalize (v t), w⟫_ℝ • normalize (v t)) s t := by
  have hn : ‖v t‖ ≠ 0 := norm_ne_zero_iff.mpr hzero
  refine (((normDerivOfScaled hv hzero).inv hn).smul hv).congr_deriv ?_
  change ‖v t‖⁻¹ • (‖v t‖ • w) +
      (-(‖v t‖ * ⟪normalize (v t), w⟫_ℝ) / ‖v t‖ ^ 2) • v t = _
  rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
  have hsmul : ⟪normalize (v t), w⟫_ℝ • normalize (v t) =
      (⟪normalize (v t), w⟫_ℝ * ‖v t‖⁻¹) • v t :=
    smul_smul _ _ _
  rw [hsmul]
  have hcoeff : -(‖v t‖ * ⟪normalize (v t), w⟫_ℝ) / ‖v t‖ ^ 2 =
      -(⟪normalize (v t), w⟫_ℝ * ‖v t‖⁻¹) := by
    field_simp
  rw [hcoeff, neg_smul, sub_eq_add_neg]

private theorem logNormDerivOfScaled {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v : ℝ → E} {w : E} {s : Set ℝ} {t : ℝ}
    (hv : HasDerivWithinAt v (‖v t‖ • w) s t) (hzero : v t ≠ 0) :
    HasDerivWithinAt (fun u => Real.log ‖v u‖) ⟪normalize (v t), w⟫_ℝ s t := by
  have hn := norm_ne_zero_iff.mpr hzero
  exact ((normDerivOfScaled hv hzero).log hn).congr_deriv (mul_div_cancel_left₀ _ hn)

theorem hasDerivWithinAt_cross3 {u v : ℝ → ℝ³} {u' v' : ℝ³} {s : Set ℝ} {t : ℝ}
    (hu : HasDerivWithinAt u u' s t) (hv : HasDerivWithinAt v v' s t) :
    HasDerivWithinAt (fun r => cross3 (u r) (v r)) (cross3 u' (v t) + cross3 (u t) v') s t := by
  have hu' := fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivWithinAt t hu
  have hv' := fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivWithinAt t hv
  have d₀ := (((hu' 1).mul (hv' 2)).sub ((hu' 2).mul (hv' 1))).smul_const
    (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
  have d₁ := (((hu' 2).mul (hv' 0)).sub ((hu' 0).mul (hv' 2))).smul_const
    (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
  have d₂ := (((hu' 0).mul (hv' 1)).sub ((hu' 1).mul (hv' 0))).smul_const
    (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
  have h := (d₀.add d₁).add d₂
  refine (h.congr_deriv ?_).congr (fun r _ => ?_) ?_ <;>
    ext i <;> fin_cases i <;> simp [cross3, cross_apply, Function.comp_apply] <;> ring

private theorem inner_eq_dot (u v : ℝ³) : ⟪u, v⟫_ℝ = u.ofLp ⬝ᵥ v.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

private theorem inner_cross3_right (u v : ℝ³) : ⟪v, cross3 u v⟫_ℝ = 0 := by
  rw [inner_eq_dot, cross3, WithLp.ofLp_toLp]
  exact dot_cross_self u.ofLp v.ofLp

private theorem orthonormal_cross3 {u v : ℝ³} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : ⟪u, v⟫_ℝ = 0) : Orthonormal ℝ ![u, v, cross3 u v] := by
  have huu : ⟪u, u⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hvv : ⟪v, v⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have hww : ⟪cross3 u v, cross3 u v⟫_ℝ = 1 := by
    simp only [inner_eq_dot] at huu hvv huv
    rw [inner_eq_dot, cross3, WithLp.ofLp_toLp, cross_dot_cross, huu, hvv, huv]
    ring
  have hvu : ⟪v, u⟫_ℝ = 0 := (real_inner_comm u v).trans huv
  have hwu : ⟪cross3 u v, u⟫_ℝ = 0 := (real_inner_comm _ _).trans (inner_cross3_left u v)
  have hwv : ⟪cross3 u v, v⟫_ℝ = 0 := (real_inner_comm _ _).trans (inner_cross3_right u v)
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Fin.isValue,
      Fin.reduceFinMk, ite_true, ite_false, Fin.reduceEq, Matrix.head_cons, Matrix.tail_cons,
      huu, hvv, hww, huv, hvu, hwu, hwv,
      inner_cross3_left, inner_cross3_right]

/-- The wave vector and the transverse amplitude determine the oriented orthonormal frame
of Lemma 2.2. -/
theorem orthonormal_movingFrame {k a : ℝ³} (hk : k ≠ 0) (ha : a ≠ 0)
    (hperp : ⟪k, a⟫_ℝ = 0) :
    Orthonormal ℝ ![normalize k, normalize a, cross3 (normalize k) (normalize a)] := by
  refine orthonormal_cross3 (norm_normalize hk) (norm_normalize ha) ?_
  simp [NormedSpace.normalize, real_inner_smul_left, real_inner_smul_right, hperp]

private theorem frameExpansion {e : Fin 3 → ℝ³} (he : Orthonormal ℝ e) (v : ℝ³) :
    v = ⟪e 0, v⟫_ℝ • e 0 + ⟪e 1, v⟫_ℝ • e 1 + ⟪e 2, v⟫_ℝ • e 2 := by
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ ℝ³ := by simp
  have hspan := (he.linearIndependent.span_eq_top_of_card_eq_finrank hcard).ge
  have h := (OrthonormalBasis.mk he hspan).sum_repr' v
  simpa only [OrthonormalBasis.coe_mk, Fin.sum_univ_three] using h.symm

private theorem trace_frame {e : Fin 3 → ℝ³} (he : Orthonormal ℝ e) (B : ℝ³ →L[ℝ] ℝ³) :
    LinearMap.trace ℝ ℝ³ B.toLinearMap =
      ⟪e 0, B (e 0)⟫_ℝ + ⟪e 1, B (e 1)⟫_ℝ + ⟪e 2, B (e 2)⟫_ℝ := by
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ ℝ³ := by simp
  have hspan := (he.linearIndependent.span_eq_top_of_card_eq_finrank hcard).ge
  simpa only [Fin.sum_univ_three, OrthonormalBasis.coe_mk, ContinuousLinearMap.coe_coe] using
    LinearMap.trace_eq_sum_inner B.toLinearMap (OrthonormalBasis.mk he hspan)

private theorem cross3_frameDerivative {u v : ℝ³} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : ⟪u, v⟫_ℝ = 0) (ν γ η : ℝ) :
    cross3 ((-ν) • v - γ • cross3 u v) v + cross3 u (ν • u - η • cross3 u v) =
      γ • u + η • v := by
  have huu : u.ofLp ⬝ᵥ u.ofLp = 1 := by
    rw [← inner_eq_dot, real_inner_self_eq_norm_sq, hu, one_pow]
  have hvv : v.ofLp ⬝ᵥ v.ofLp = 1 := by
    rw [← inner_eq_dot, real_inner_self_eq_norm_sq, hv, one_pow]
  have huv' : u.ofLp ⬝ᵥ v.ofLp = 0 := (inner_eq_dot u v).symm.trans huv
  apply WithLp.ofLp_injective
  simp only [cross3, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul,
    map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, cross_self, smul_zero, zero_sub,
    cross_cross_eq_smul_sub_smul, cross_cross_eq_smul_sub_smul', huv', huu, hvv, zero_smul,
    one_smul, zero_sub, smul_neg, neg_neg]

/-- The three frame axes and logarithmic strength satisfy (2.2) of Lemma 2.2.
Taking derivatives within `s` allows one-sided derivatives at interval endpoints. -/
theorem hasDerivWithinAt_movingFrame {k a : ℝ → ℝ³} {s : Set ℝ} {t : ℝ} (ht : t ∈ s)
    (B : ℝ³ →L[ℝ] ℝ³) (htrace : LinearMap.trace ℝ ℝ³ B.toLinearMap = 0)
    (hk₀ : k t ≠ 0) (ha₀ : a t ≠ 0) (hperp : ⟪k t, a t⟫_ℝ = 0)
    (hk : HasDerivWithinAt k (-(B.adjoint (k t))) s t)
    (ha : HasDerivWithinAt a
      (-(B (a t)) + (2 * ⟪k t, B (a t)⟫_ℝ / ‖k t‖ ^ 2) • k t) s t) :
    let E₁ := fun u => normalize (k u)
    let E₂ := fun u => normalize (a u)
    let E₃ := fun u => cross3 (E₁ u) (E₂ u)
    let ν := ⟪E₁ t, B (E₂ t)⟫_ℝ
    let γ := ⟪E₁ t, B (E₃ t)⟫_ℝ
    let η := ⟪E₃ t, B (E₂ t)⟫_ℝ
    HasDerivWithinAt E₁ ((-ν) • E₂ t - γ • E₃ t) s t ∧
    HasDerivWithinAt E₂ (ν • E₁ t - η • E₃ t) s t ∧
    HasDerivWithinAt E₃ (γ • E₁ t + η • E₂ t) s t ∧
    HasDerivWithinAt (fun u => Real.log (‖k u‖ * ‖a u‖)) ⟪E₃ t, B (E₃ t)⟫_ℝ s t := by
  dsimp only
  set x := normalize (k t)
  set y := normalize (a t)
  set z := cross3 x y
  set ν := ⟪x, B y⟫_ℝ
  set γ := ⟪x, B z⟫_ℝ
  set η := ⟪z, B y⟫_ℝ
  have he := orthonormal_movingFrame hk₀ ha₀ hperp
  have hx : ‖x‖ = 1 := he.norm_eq_one 0
  have hy : ‖y‖ = 1 := he.norm_eq_one 1
  have hxy : ⟪x, y⟫_ℝ = 0 := he.inner_eq_zero (i := 0) (j := 1) (by decide)
  have hyx : ⟪y, x⟫_ℝ = 0 := (real_inner_comm _ _).trans hxy
  have hBAdjoint : B.adjoint x = ⟪x, B x⟫_ℝ • x + ν • y + γ • z := by
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, ContinuousLinearMap.adjoint_inner_right,
      real_inner_comm x] using frameExpansion he (B.adjoint x)
  have hBy : B y = ν • x + ⟪y, B y⟫_ℝ • y + η • z := by
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] using
      frameExpansion he (B y)
  have hk' : HasDerivWithinAt k (‖k t‖ • (-(B.adjoint x))) s t := by
    apply hk.congr_deriv
    rw [smul_neg, ← map_smul, norm_smul_normalize]
  set w := -(B y) + (2 * ν) • x with hw
  have ha' : HasDerivWithinAt a (‖a t‖ • w) s t := by
    apply ha.congr_deriv
    have hcoef : 2 * ⟪k t, B (a t)⟫_ℝ / ‖k t‖ ^ 2 * ‖k t‖ = ‖a t‖ * (2 * ν) := by
      have hnk := norm_ne_zero_iff.mpr hk₀
      have hinner : ⟪k t, B (a t)⟫_ℝ = ‖k t‖ * (‖a t‖ * ν) := by
        rw [← real_inner_smul_right, ← map_smul, norm_smul_normalize, ← real_inner_smul_left,
          norm_smul_normalize]
      rw [hinner]
      field_simp
    have hB : ‖a t‖ • B y = B (a t) := by rw [← map_smul, norm_smul_normalize]
    rw [hw, smul_add, smul_neg, hB, smul_smul, ← hcoef, ← smul_smul, norm_smul_normalize]
  have hinner₁ : ⟪x, -(B.adjoint x)⟫_ℝ = -⟪x, B x⟫_ℝ := by
    rw [inner_neg_right, ContinuousLinearMap.adjoint_inner_right, real_inner_comm x (B x)]
  have hinner₂ : ⟪y, w⟫_ℝ = -⟪y, B y⟫_ℝ := by
    rw [hw, inner_add_right, inner_neg_right, real_inner_smul_right, hyx, mul_zero, add_zero]
  have hE₁ : HasDerivWithinAt (fun u => normalize (k u)) ((-ν) • y - γ • z) s t := by
    refine (normalizeDerivOfScaled hk' hk₀).congr_deriv ?_
    change -(B.adjoint x) - ⟪x, -(B.adjoint x)⟫_ℝ • x = _
    rw [hinner₁, hBAdjoint]
    module
  have hE₂ : HasDerivWithinAt (fun u => normalize (a u)) (ν • x - η • z) s t := by
    refine (normalizeDerivOfScaled ha' ha₀).congr_deriv ?_
    change w - ⟪y, w⟫_ℝ • y = _
    rw [hinner₂, hw]
    nth_rw 1 [hBy]
    module
  refine ⟨hE₁, hE₂, (hasDerivWithinAt_cross3 hE₁ hE₂).congr_deriv
    (cross3_frameDerivative hx hy hxy ν γ η), ?_⟩
  have htr := trace_frame he B
  rw [htrace] at htr
  change 0 = ⟪x, B x⟫_ℝ + ⟪y, B y⟫_ℝ + ⟪z, B z⟫_ℝ at htr
  have hlog := (logNormDerivOfScaled hk' hk₀).add (logNormDerivOfScaled ha' ha₀)
  change HasDerivWithinAt _ (⟪x, -(B.adjoint x)⟫_ℝ + ⟪y, w⟫_ℝ) s t at hlog
  rw [hinner₁, hinner₂] at hlog
  have hne := Filter.inter_mem (hk.continuousWithinAt.eventually_ne hk₀)
    (ha.continuousWithinAt.eventually_ne ha₀)
  have hEq : (fun u => Real.log (‖k u‖ * ‖a u‖)) =ᶠ[nhdsWithin t s]
      fun u => Real.log ‖k u‖ + Real.log ‖a u‖ := by
    filter_upwards [hne] with u hu
    exact Real.log_mul (norm_ne_zero_iff.mpr hu.1) (norm_ne_zero_iff.mpr hu.2)
  exact (hlog.congr_of_eventuallyEq_of_mem hEq ht).congr_deriv (by linarith)

end TorusEuler
