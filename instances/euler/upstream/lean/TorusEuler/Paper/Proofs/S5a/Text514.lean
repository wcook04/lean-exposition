import TorusEuler.Paper.S5.TextStatements
import TorusEuler.Paper.S34A.Statements
import TorusEuler.Paper.SBD.Statements
import TorusEuler.Paper.Proofs.S5a.Library.KOmegaPower
import TorusEuler.Paper.Proofs.S5a.Library.TowerMain
import TorusEuler.Paper.Proofs.S5a.Library.MeanUnique
import TorusEuler.Paper.Proofs.S5a.Library.MeanSetting

/-!
# Proof of the display (5.14) (Hölder bound for the velocity of (4.9))

`sections/06d_mean_estimates.tex:30-58` (latest numbering (5.14)).
-/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper

noncomputable section

open AppendixD HierarchyTwistedProfile Lib.S5a Lib.S5a.Tower

local notation "C½" => HalfHolder (UnitAddTorus (Fin 3)) Vec3
local notation "K½" => HalfHolder (UnitAddTorus (Fin 3)) (Vec3 →L[ℝ] Vec3)
local notation "S" => endpointHalfHolderSolenoidal

local instance text514SolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance text514SolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

namespace Lib.S5a

/-- The constant `A` of (4.10) is at most `D^{C_A}` (`06d_mean_estimates.tex:34-38`): the data of Theorem 4.2 are
bounded by `D`, `K₀ = |K|_0`, `K₁ = |K|_1`, `Ω₀`, `Ω₁` (D.6). -/
theorem exists_A_bound (C42 : ℝ) (p : ℕ) (CK CO : ℕ → ℝ) (aK aO : ℕ) :
    ∃ CA : ℕ, ∀ {D : ℝ}, 2 ≤ D → ∀ K₀ K₁ Ω₀ Ω₁ : ℝ, 0 ≤ K₀ → 0 ≤ K₁ → 0 ≤ Ω₀ → 0 ≤ Ω₁ →
      K₀ ≤ 3 ^ 0 * CK 0 * D ^ (aK * (0 + 1)) → K₁ ≤ 3 ^ 1 * CK 1 * D ^ (aK * (1 + 1)) →
      Ω₀ ≤ 3 ^ 0 * CO 0 * D ^ (aO * (0 + 1)) → Ω₁ ≤ 3 ^ 1 * CO 1 * D ^ (aO * (1 + 1)) →
      C42 * (D + D + K₀ + K₁ + Ω₀ + Ω₁) ^ p ≤ D ^ CA := by
  let E : ℕ := 1 + 2 * aK + 2 * aO
  let σ : ℝ := 2 + max (3 ^ 0 * CK 0) 0 + max (3 ^ 1 * CK 1) 0 + max (3 ^ 0 * CO 0) 0 +
    max (3 ^ 1 * CO 1) 0
  let c : ℝ := max C42 0 * σ ^ p
  refine ⟨⌈c⌉₊ + E * p, fun {D} hD K₀ K₁ Ω₀ Ω₁ h0 h1 h2 h3 hK0 hK1 hO0 hO1 => ?_⟩
  have hD1 : 1 ≤ D := by linarith
  have hDp : 0 < D := by linarith
  have hpow (e : ℕ) (he : e ≤ E) : D ^ e ≤ D ^ E := pow_le_pow_right₀ hD1 he
  have key (r : ℝ) (e : ℕ) (he : e ≤ E) : r * D ^ e ≤ max r 0 * D ^ E :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hDp.le _)).trans
      (mul_le_mul_of_nonneg_left (hpow e he) (le_max_right _ _))
  have b0 : D ≤ D ^ E := by
    have := hpow 1 (by omega)
    simpa using this
  have bK0 := hK0.trans (key _ (aK * (0 + 1)) (by omega))
  have bK1 := hK1.trans (key _ (aK * (1 + 1)) (by omega))
  have bO0 := hO0.trans (key _ (aO * (0 + 1)) (by omega))
  have bO1 := hO1.trans (key _ (aO * (1 + 1)) (by omega))
  have hσ : D + D + K₀ + K₁ + Ω₀ + Ω₁ ≤ σ * D ^ E := by
    have hσe : σ * D ^ E = 2 * D ^ E + max (3 ^ 0 * CK 0) 0 * D ^ E + max (3 ^ 1 * CK 1) 0 * D ^ E +
        max (3 ^ 0 * CO 0) 0 * D ^ E + max (3 ^ 1 * CO 1) 0 * D ^ E := by
      simp only [σ]; ring
    rw [hσe]
    linarith
  have hS0 : 0 ≤ D + D + K₀ + K₁ + Ω₀ + Ω₁ := by linarith
  have hSp : (D + D + K₀ + K₁ + Ω₀ + Ω₁) ^ p ≤ σ ^ p * D ^ (E * p) := by
    refine (pow_le_pow_left₀ hS0 hσ p).trans ?_
    rw [mul_pow, ← pow_mul]
  have hc : c ≤ D ^ ⌈c⌉₊ := by
    refine (Nat.le_ceil c).trans ?_
    have h2n : ((⌈c⌉₊ : ℕ) : ℝ) ≤ 2 ^ ⌈c⌉₊ := by exact_mod_cast (Nat.lt_two_pow_self).le
    exact h2n.trans (pow_le_pow_left₀ (by norm_num) hD _)
  calc C42 * (D + D + K₀ + K₁ + Ω₀ + Ω₁) ^ p
      ≤ max C42 0 * (D + D + K₀ + K₁ + Ω₀ + Ω₁) ^ p :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hS0 _)
    _ ≤ max C42 0 * (σ ^ p * D ^ (E * p)) := mul_le_mul_of_nonneg_left hSp (le_max_right _ _)
    _ = c * D ^ (E * p) := by simp only [c]; ring
    _ ≤ D ^ ⌈c⌉₊ * D ^ (E * p) := mul_le_mul_of_nonneg_right hc (pow_nonneg hDp.le _)
    _ = _ := by rw [pow_add]

end Lib.S5a

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Proof of the display **(5.14)** (`cc:uf:mean:holder-bound`), following
`sections/06d_mean_estimates.tex:30-58`: `‖v‖_{[n],1/2} ≤ C_n 𝖣^C ‖g‖_{[n],1/2}` for the velocity `v = z_t` of the
solution of (4.9) with `L = -∫ g`.

Where the hypotheses enter.
* `h4_2` (Theorem 4.2): the constant `A` of (4.10) (TeX 34-38) and the bound `‖v‖ ≤ A ‖L‖` in `C_t C^{0,1/2}`
  (TeX 48-49), through `Lib.S5a.Tower.zero_order` (first item: existence, uniqueness and the bound; the solution
  of (4.9) with the projected source `L = -(P(Kv)(t) - P(Kv)(0) - P ∫_0^t Ωv)`).
* `h5_1` and `hD_2`: (D.6) for `D_aX`, `M`, then Lemma D.2(a) for `K`, `Ω` (TeX 30-33, `exists_KOmega_power`); with
  `(D.6)` for the first label derivatives this gives `A ≤ 𝖣^{C_A}` (TeX 34-38, `exists_A_bound`; `𝖣 ≥ 2`).
* `hText_eq_5_13`: the thresholds (5.13) `ℓ_*^m(|K|_{m,1/2} + |Ω|_{m,1/2}) ≤ C_m / A` at `A = 𝖣^{C_A}`, which give
  the hypothesis (D.7) of Lemma D.3 with `C_low = D^{C_A}` (TeX 52-53, display 42-45; the Hölder norms of the words of `K`, `Ω`
  are compared with the closed-time norms by `mul_endpointClosedTimeNorm_le_of_hierarchyLabelWord`, constant `√2`).
* `hD_3` (Lemma D.3): applied in the spaces of derivative towers (`Library/Tower*.lean`, TeX 50-58), with the equation
  `K v - ∫ Ω v ≡ ∫ g` modulo the time constant solenoidal part and gradients written with the Leray projection;
  the time integration `‖∫_0^t g‖ ≤ T ‖g‖` with `T ≤ 1` (TeX 50-51, source 54-55) is the last step.
* TeX 46-48 (label derivatives preserve the constraints, tower construction): the velocity tower in `Esp` by
  `exists_velocityTower`; the forcing tower is identified with `-P ∫ g` by `Tk_der`/`eq_of_der` from the projected
  equation (base identity `hmom`).
The velocity `v` of the statement is the velocity of the smooth mean solution (invertibility of `D_aX`). -/
theorem Proof.Text.eq_5_14_of (h4_2 : Statement.theorem_4_2) (h5_1 : Statement.proposition_5_1)
    (hD_2 : Statement.lemma_D_2) (hD_3 : Statement.lemma_D_3)
    (hText_eq_5_13 : Statement.Text.eq_5_13) : Statement.Text.eq_5_14 := by
  obtain ⟨C42, p, hC42, h42⟩ := h4_2
  obtain ⟨CK, CO, aK, aO, hCK, hCO, hKO⟩ := Lib.S5a.exists_KOmega_power h5_1 hD_2
  obtain ⟨CA, hCA⟩ := Lib.S5a.exists_A_bound C42 p CK CO aK aO
  obtain ⟨a₀, H513⟩ := hText_eq_5_13 CA
  refine ⟨a₀, fun a ha => ?_⟩
  obtain ⟨C5, Cm5, H5⟩ := H513 a ha
  refine ⟨CA, fun n => Cn_of hD_3 n (fun m => 4 * Real.sqrt 2 * ‖pjL‖ * Cm5 m) * ‖pjL‖ *
    Real.sqrt 2, ?_⟩
  intro T hT U X pU k D lam d hP f B q hs v hv hvper hB ℓ g n hgfin
  have h0 : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hD2 : 2 ≤ D := hP.scale_ge_two
  have hD1 : 1 ≤ D := by linarith
  have hD0 : 0 < D := by linarith
  have hℓdef : ℓ = (D ^ a)⁻¹ := rfl
  have hℓ0 : 0 < ℓ := by rw [hℓdef]; positivity
  -- the parent of Theorem 4.2 and the smooth mean solution
  obtain ⟨Lip, hLip⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT
    (hP.velocity_smooth.of_le (by simp)) hP.velocity_periodic
  have hLeul : ∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (U t) x‖ ≤ D := by
    intro t ht x
    have h : ‖meanGradient U X t (X t 0 x)‖ ≤ D := hP.gradient_le t ht _
    rwa [meanGradient, (hP.flow.inverse hLip h0 ht).2 x] at h
  obtain ⟨par, hpar⟩ := exists_paperMeanParent_of_flow hT hP.flow hP.velocity_smooth
    hP.velocity_periodic (fun t ht a => hP.inverse_deformation_le t ht a) hLeul
    (meanHsharp_le_of_parent hT hP)
  have hpar' : ∀ t ∈ Icc 0 T, ∀ (a : Vec3),
      par.F (t, toUnitTorus a) = fderiv ℝ (X 0 t) a ∧
        par.G (t, toUnitTorus a) = fderiv ℝ (X t 0) (X 0 t a) ∧
          par.M (t, toUnitTorus a) = fderiv ℝ (U t) (X 0 t a) :=
    fun t ht a => ⟨(hpar t ht a).1, (hpar t ht a).2.1, (hpar t ht a).2.2.1⟩
  obtain ⟨s, hB₁, -⟩ := exists_smoothMeanSolution d par hpar' hs
  -- the given velocity is the velocity of the smooth mean solution
  have hU2 : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hP.velocity_smooth.of_le (by simp)
  have hinv : ∀ t ∈ Icc 0 T, ∀ a,
      (fderiv ℝ (X t 0) (X 0 t a)).comp (fderiv ℝ (X 0 t) a) = .id ℝ Vec3 :=
    fun t ht a => (hP.flow.labelDerivative_inverse hT hU2 hP.velocity_periodic h0 ht a).1
  have hvv : ∀ t ∈ Icc 0 T, ∀ a, v t a = s.velocity t a := by
    intro t ht a
    have e3 : fderiv ℝ (X 0 t) a (v t a) = fderiv ℝ (X 0 t) a (s.velocity t a) :=
      (hB t ht a 0).symm.trans (hB₁ t ht a 0)
    have k1 : (fderiv ℝ (X t 0) (X 0 t a)) (fderiv ℝ (X 0 t) a (v t a)) = v t a := by
      rw [← ContinuousLinearMap.comp_apply, hinv t ht a]; rfl
    have k2 : (fderiv ℝ (X t 0) (X 0 t a)) (fderiv ℝ (X 0 t) a (s.velocity t a)) =
        s.velocity t a := by
      rw [← ContinuousLinearMap.comp_apply, hinv t ht a]; rfl
    rw [← k1, e3, k2]
  have hvfun : (fun t : Icc (0 : ℝ) T => v t.val) = fun t => s.velocity t.val :=
    funext fun t => funext fun x => hvv t.val t.property x
  rw [hvfun]
  -- the coefficient data of Theorem 4.2: (D.6) for `K`, `Ω`
  obtain ⟨hPK, hPO⟩ := hKO hT hP
  have hone {F : ℝ → Vec3 → (Vec3 →L[ℝ] Vec3)} (t : ℝ) (b : Vec3) :
      ‖fderiv ℝ (F t) b‖ = ‖iteratedFDeriv ℝ 1 (F t) b‖ := by
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero]
  let K₀ : ℝ := 3 ^ 0 * CK 0 * D ^ (aK * (0 + 1))
  let K₁ : ℝ := 3 ^ 1 * CK 1 * D ^ (aK * (1 + 1))
  let Ω₀ : ℝ := 3 ^ 0 * CO 0 * D ^ (aO * (0 + 1))
  let Ω₁ : ℝ := 3 ^ 1 * CO 1 * D ^ (aO * (1 + 1))
  have hK₀ : ∀ t ∈ Icc 0 T, ∀ b, ‖meanKinetic X t b‖ ≤ K₀ := fun t ht b => by
    simpa only [norm_iteratedFDeriv_zero] using
      norm_iteratedFDeriv_le_of_coefficientPower hPK 0 ⟨t, ht⟩ b
  have hK₁ : ∀ t ∈ Icc 0 T, ∀ b, ‖fderiv ℝ (meanKinetic X t) b‖ ≤ K₁ := fun t ht b => by
    rw [hone (F := meanKinetic X) t b]
    exact norm_iteratedFDeriv_le_of_coefficientPower hPK 1 ⟨t, ht⟩ b
  have hΩ₀ : ∀ t ∈ Icc 0 T, ∀ b, ‖meanVorticity U X t b‖ ≤ Ω₀ := fun t ht b => by
    simpa only [norm_iteratedFDeriv_zero] using
      norm_iteratedFDeriv_le_of_coefficientPower hPO 0 ⟨t, ht⟩ b
  have hΩ₁ : ∀ t ∈ Icc 0 T, ∀ b, ‖fderiv ℝ (meanVorticity U X t) b‖ ≤ Ω₁ := fun t ht b => by
    rw [hone (F := meanVorticity U X) t b]
    exact norm_iteratedFDeriv_le_of_coefficientPower hPO 1 ⟨t, ht⟩ b
  have hAbd : C42 * (D + D + K₀ + K₁ + Ω₀ + Ω₁) ^ p ≤ D ^ CA :=
    hCA hD2 K₀ K₁ Ω₀ Ω₁ (mul_nonneg (mul_nonneg (by positivity) (hCK 0)) (by positivity))
      (mul_nonneg (mul_nonneg (by positivity) (hCK 1)) (by positivity))
      (mul_nonneg (mul_nonneg (by positivity) (hCO 0)) (by positivity))
      (mul_nonneg (mul_nonneg (by positivity) (hCO 1)) (by positivity)) le_rfl le_rfl le_rfl le_rfl
  -- towers of the coefficients, the velocity, the source and its primitive
  obtain ⟨hKper, hΩper, -⟩ := exists_meanCoefficient_bounds hT hP
  obtain ⟨Kt⟩ := exists_symTower hT (Function.uncurry (meanKinetic X)) (meanKinetic_smooth hT hP)
    (fun t ht => hKper t ht)
  obtain ⟨Ωt⟩ := exists_symTower hT (Function.uncurry (meanVorticity U X))
    (meanVorticity_smooth hT hP) (fun t ht => hΩper t ht)
  obtain ⟨Vt⟩ := exists_symTower hT (Function.uncurry s.velocity) s.velocity_smooth
    (fun t ht => (s.periodic t ht).1)
  have hforce : ContDiffOn ℝ ∞ (Function.uncurry fun t a => f.val.val.val (t, a, 0))
      (Icc 0 T ×ˢ (univ : Set Vec3)) := slice0_contDiff f
  have hfper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (fun a => f.val.val.val (t, a, 0)) := by
    intro t ht n a
    change f.val.val.val (t, a + latticeVector n, 0) = f.val.val.val (t, a, 0)
    have h1 : f.val.val.val (t, a + latticeVector n, 0) =
        f.val.val.val (t, a + latticeVector n, 0 + ⟪k, latticeVector n⟫_ℝ) :=
      ((momentum_eval d hs ht _ _).trans (momentum_eval d hs ht _ 0).symm).symm
    exact h1.trans (twistedSlice f t a 0 n)
  have hFsm := hP.flow.contDiffOn_forwardLabelDerivative hT hP.velocity_smooth hP.velocity_periodic
  let w : ℝ → Vec3 → Vec3 := fun r x => (fderiv ℝ (X 0 r) x).adjoint (f.val.val.val (r, x, 0))
  have hw : ContDiffOn ℝ ∞ (Function.uncurry w) (Icc 0 T ×ˢ (univ : Set Vec3)) := by
    have adj : ContDiff ℝ ∞ (fun F : Vec3 →L[ℝ] Vec3 => F.adjoint) :=
      (ContinuousLinearMap.adjoint : (Vec3 →L[ℝ] Vec3) ≃ₗᵢ⋆[ℝ] (Vec3 →L[ℝ] Vec3)).contDiff
    exact (adj.comp_contDiffOn hFsm).clm_apply hforce
  have hwper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (w t) := by
    intro t ht n x
    change (fderiv ℝ (X 0 t) (x + latticeVector n)).adjoint
        (f.val.val.val (t, x + latticeVector n, 0)) =
      (fderiv ℝ (X 0 t) x).adjoint (f.val.val.val (t, x, 0))
    have h1 : fderiv ℝ (X 0 t) (x + latticeVector n) = fderiv ℝ (X 0 t) x :=
      parent_deformation_periodic hT hP ht n x
    have h2 : f.val.val.val (t, x + latticeVector n, 0) = f.val.val.val (t, x, 0) :=
      hfper t ht n x
    rw [h1, h2]
  obtain ⟨gt⟩ := exists_symTower hT (Function.uncurry w) hw hwper
  obtain ⟨srcT⟩ := exists_symTower hT
    (fun p : ℝ × Vec3 => -endpointPrimitive (fun r => w r p.2) p.1)
    (contDiffOn_endpointPhysicalJointPrimitive hT hw).neg
    (fun t ht n x => by
      change -endpointPrimitive (fun r => w r (x + latticeVector n)) t =
        -endpointPrimitive (fun r => w r x) t
      unfold endpointPrimitive
      refine congrArg Neg.neg (intervalIntegral.integral_congr fun r hr => ?_)
      rw [uIcc_of_le ht.1] at hr
      exact hwper r ⟨hr.1, hr.2.trans ht.2⟩ n x)
  have hΩv : ContDiffOn ℝ ∞ (Function.uncurry fun r x =>
      Function.uncurry (meanVorticity U X) (r, x) (s.velocity r x))
      (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    (meanVorticity_smooth hT hP).clm_apply s.velocity_smooth
  obtain ⟨Θt⟩ := exists_symTower hT
    (fun p : ℝ × Vec3 => -endpointPrimitive
      (fun r => Function.uncurry (meanVorticity U X) (r, p.2) (s.velocity r p.2)) p.1)
    (contDiffOn_endpointPhysicalJointPrimitive hT hΩv).neg
    (fun t ht n x => by
      change -endpointPrimitive (fun r => meanVorticity U X r (x + latticeVector n)
          (s.velocity r (x + latticeVector n))) t =
        -endpointPrimitive (fun r => meanVorticity U X r x (s.velocity r x)) t
      unfold endpointPrimitive
      refine congrArg Neg.neg (intervalIntegral.integral_congr fun r hr => ?_)
      rw [uIcc_of_le ht.1] at hr
      have hr' : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
      have e1 : meanVorticity U X r (x + latticeVector n) = meanVorticity U X r x := hΩper r hr' n x
      have e2 : s.velocity r (x + latticeVector n) = s.velocity r x := (s.periodic r hr').1 n x
      rw [e1, e2])
  -- Theorem 4.2, first item
  have H := h42 T U X (meanParentFlow_of_parent hT hP) (meanHsharp_le_of_parent hT hP) D D K₀ K₁
    Ω₀ Ω₁ hD1 (fun t ht b => hP.inverse_deformation_le t ht b)
    (fun t ht b => hP.gradient_le t ht _) hK₀ hK₁ hΩ₀ hΩ₁ (Kt.Y []) (Ωt.Y [])
    (fun t ht b => Kt.lift [] t ht b) (fun t ht b => Ωt.lift [] t ht b)
  dsimp only at H
  obtain ⟨H1, -, -⟩ := H
  -- the base identity (4.9) in projected form
  have hKp : ∀ t ∈ Icc 0 T, ∀ x, HalfHolder.eval (toUnitTorus x) (Kt.Y [] t) = par.kinetic t x := by
    intro t ht x
    refine (Kt.lift [] t ht x).trans ?_
    change meanKinetic X t x = par.kinetic t x
    simp only [PaperMeanParent.kinetic, meanKinetic, meanDeformation, (hpar t ht x).1]
  have hΩp : ∀ t ∈ Icc 0 T, ∀ x,
      HalfHolder.eval (toUnitTorus x) (Ωt.Y [] t) = par.vorticity t x := by
    intro t ht x
    refine (Ωt.lift [] t ht x).trans ?_
    change meanVorticity U X t x = par.vorticity t x
    simp only [PaperMeanParent.vorticity, meanVorticity, meanDeformation, meanGradient,
      (hpar t ht x).1, (hpar t ht x).2.2.1]
  have hSource : ∀ t ∈ Icc 0 T, ∀ x, HalfHolder.eval (toUnitTorus x) (srcT.Y [] t) =
      endpointPhysicalForcePrimitive par.F (fun t a => f.val.val.val (t, a, 0)) (t, x) := by
    intro t ht x
    refine (srcT.lift [] t ht x).trans ?_
    change -endpointPrimitive (fun r => w r x) t = -endpointPrimitive
      (fun r => (par.F (r, toUnitTorus x)).adjoint (f.val.val.val (r, x, 0))) t
    unfold endpointPrimitive
    refine congrArg Neg.neg (intervalIntegral.integral_congr fun r hr => ?_)
    rw [uIcc_of_le ht.1] at hr
    have hr' : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
    change (fderiv ℝ (X 0 r) x).adjoint (f.val.val.val (r, x, 0)) =
      (par.F (r, toUnitTorus x)).adjoint (f.val.val.val (r, x, 0))
    rw [(hpar r hr' x).1]
  let : CompleteSpace S := isClosed_endpointHalfHolderSolenoidal.completeSpace_coe
  obtain ⟨u, hu⟩ := integratedSolution_of_smooth hT s (Kt.Y []) (Ωt.Y []) (Kt.smooth [])
    (Ωt.smooth []) hKp hΩp hforce (srcT.Y []) (srcT.smooth []) hSource
  have hVeq : ∀ t ∈ Icc 0 T, ((u.velocity t : S) : C½) = Vt.Y [] t := by
    intro t ht
    apply HalfHolder.ext
    intro a
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    refine (hu t ht x).trans ?_
    exact (Vt.lift [] t ht x).symm
  have hsrcBase : EqOn (srcT.Y []) (fun t => -endpointPrimitive (gt.Y []) t) (Icc 0 T) :=
    endpointSourceCurve_eq_negPrimitive_of_lift (srcT.Y []) (gt.Y []) (fun r x => w r x)
      (gt.smooth []).continuousOn (fun t ht x => gt.lift [] t ht x)
      (fun t ht x => srcT.lift [] t ht x)
  have hmom : ∀ t ∈ Icc 0 T,
      pjL ((Kt.Y [] t).coefficientMul (Vt.Y [] t)) -
        pjL ((Kt.Y [] 0).coefficientMul (Vt.Y [] 0)) -
          pjL (endpointPrimitive (fun r => (Ωt.Y [] r).coefficientMul (Vt.Y [] r)) t) =
            pjL (endpointPrimitive (gt.Y []) t) := by
    intro t ht
    have hMt : ∀ t' ∈ Icc 0 T, pjL (paperMeanIntegratedMomentum (Kt.Y []) (Ωt.Y []) (srcT.Y [])
        u.velocity t') = (u.constant : C½) := fun t' ht' => congrArg Subtype.val (u.projected t' ht')
    have eM (t' : ℝ) (ht' : t' ∈ Icc 0 T) :
        paperMeanIntegratedMomentum (Kt.Y []) (Ωt.Y []) (srcT.Y []) u.velocity t' =
          (Kt.Y [] t').coefficientMul (Vt.Y [] t') -
            endpointPrimitive (fun r => (Ωt.Y [] r).coefficientMul (Vt.Y [] r)) t' +
              srcT.Y [] t' := by
      have hp : endpointPrimitive (fun r => (Ωt.Y [] r).coefficientMul ((u.velocity r : S) : C½)) t' =
          endpointPrimitive (fun r => (Ωt.Y [] r).coefficientMul (Vt.Y [] r)) t' := by
        unfold endpointPrimitive
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le ht'.1]
        intro r hr
        simp only [hVeq r ⟨hr.1, hr.2.trans ht'.2⟩]
      simp only [paperMeanIntegratedMomentum, hVeq t' ht', hp]
    have e1 := hMt t ht
    have e0 := hMt 0 h0
    rw [eM t ht, hsrcBase ht] at e1
    have hs0 : srcT.Y [] 0 = 0 := by
      rw [hsrcBase h0]; simp [endpointPrimitive]
    rw [eM 0 h0, hs0, endpointPrimitive_zero, sub_zero, add_zero] at e0
    rw [map_add, map_sub, map_neg, ← e0] at e1
    rw [← e1]
    abel
  -- (D.7) from the display (5.13) with `A = D^{C_A}`
  have hClow0 : 0 < D ^ CA := by positivity
  have hnorm0 : 0 ≤ ‖pjL‖ := norm_nonneg pjL
  have hD7 : ∀ m, 1 ≤ m → m ≤ n →
      D ^ CA * (4 * ‖pjL‖ * ∑ w' ∈ (hierarchyAdmissibleWords (Fin 3) m).filter
            (fun w' => w'.length = m), ℓ ^ m * endpointClosedTimeNorm T (Kt.Y w') +
          2 * ‖pjL‖ * T * ∑ w' ∈ (hierarchyAdmissibleWords (Fin 3) m).filter
            (fun w' => w'.length = m), ℓ ^ m * endpointClosedTimeNorm T (Ωt.Y w')) ≤
        4 * Real.sqrt 2 * ‖pjL‖ * Cm5 m := by
    intro m hm1 _
    obtain ⟨hbdd, h51, h52⟩ := H5 hT hP (D ^ CA) hClow0 le_rfl m hm1
    have hKsum : ∑ w' ∈ (hierarchyAdmissibleWords (Fin 3) m).filter (fun w' => w'.length = m),
        ℓ ^ m * endpointClosedTimeNorm T (Kt.Y w') ≤
          Real.sqrt 2 * (ℓ ^ m * holderOrderNorm m
            (fun (t : Icc (0 : ℝ) T) (b : Vec3) => meanKinetic X t b)) := by
      unfold holderOrderNorm
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun w' hw' => ?_
      have hlen := (Finset.mem_filter.mp hw').2
      have h := mul_endpointClosedTimeNorm_le_of_hierarchyLabelWord hT.le one_pos w' (Kt.Y w')
        (fun t ht => hPK.1 ⟨t, ht⟩) (hbdd w' hw').1 (fun t ht x => Kt.lift w' t ht x)
      rw [hlen, one_pow, one_mul] at h
      calc ℓ ^ m * endpointClosedTimeNorm T (Kt.Y w') ≤ ℓ ^ m * (Real.sqrt 2 * _) :=
            mul_le_mul_of_nonneg_left h (pow_nonneg hℓ0.le _)
        _ = _ := by ring
    have hΩsum : ∑ w' ∈ (hierarchyAdmissibleWords (Fin 3) m).filter (fun w' => w'.length = m),
        ℓ ^ m * endpointClosedTimeNorm T (Ωt.Y w') ≤
          Real.sqrt 2 * (ℓ ^ m * holderOrderNorm m
            (fun (t : Icc (0 : ℝ) T) (b : Vec3) => meanVorticity U X t b)) := by
      unfold holderOrderNorm
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun w' hw' => ?_
      have hlen := (Finset.mem_filter.mp hw').2
      have h := mul_endpointClosedTimeNorm_le_of_hierarchyLabelWord hT.le one_pos w' (Ωt.Y w')
        (fun t ht => hPO.1 ⟨t, ht⟩) (hbdd w' hw').2 (fun t ht x => Ωt.lift w' t ht x)
      rw [hlen, one_pow, one_mul] at h
      calc ℓ ^ m * endpointClosedTimeNorm T (Ωt.Y w') ≤ ℓ ^ m * (Real.sqrt 2 * _) :=
            mul_le_mul_of_nonneg_left h (pow_nonneg hℓ0.le _)
        _ = _ := by ring
    have hSK0 : 0 ≤ ∑ w' ∈ (hierarchyAdmissibleWords (Fin 3) m).filter
        (fun w' => w'.length = m), ℓ ^ m * endpointClosedTimeNorm T (Kt.Y w') :=
      Finset.sum_nonneg fun w' _ => mul_nonneg (pow_nonneg hℓ0.le _)
        (endpointClosedTimeNorm_nonneg hT.le _)
    have hSO0 : 0 ≤ ∑ w' ∈ (hierarchyAdmissibleWords (Fin 3) m).filter
        (fun w' => w'.length = m), ℓ ^ m * endpointClosedTimeNorm T (Ωt.Y w') :=
      Finset.sum_nonneg fun w' _ => mul_nonneg (pow_nonneg hℓ0.le _)
        (endpointClosedTimeNorm_nonneg hT.le _)
    have hT1 : T ≤ 1 := hP.time_le_one
    have hbT : 2 * ‖pjL‖ * T * ∑ w' ∈ (hierarchyAdmissibleWords (Fin 3) m).filter
        (fun w' => w'.length = m), ℓ ^ m * endpointClosedTimeNorm T (Ωt.Y w') ≤
        4 * ‖pjL‖ * ∑ w' ∈ (hierarchyAdmissibleWords (Fin 3) m).filter
        (fun w' => w'.length = m), ℓ ^ m * endpointClosedTimeNorm T (Ωt.Y w') := by
      have := mul_nonneg hnorm0 hSO0
      nlinarith
    have hkey := h51.trans h52
    have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    calc D ^ CA * (4 * ‖pjL‖ * _ + 2 * ‖pjL‖ * T * _)
        ≤ D ^ CA * (4 * ‖pjL‖ * (Real.sqrt 2 * (ℓ ^ m * (holderOrderNorm m
            (fun (t : Icc (0 : ℝ) T) (b : Vec3) => meanKinetic X t b) + holderOrderNorm m
            (fun (t : Icc (0 : ℝ) T) (b : Vec3) => meanVorticity U X t b))))) := by
          refine mul_le_mul_of_nonneg_left ?_ hClow0.le
          have := mul_le_mul_of_nonneg_left (add_le_add hKsum hΩsum) (mul_nonneg (by norm_num) hnorm0 :
            (0 : ℝ) ≤ 4 * ‖pjL‖)
          nlinarith
      _ ≤ D ^ CA * (4 * ‖pjL‖ * (Real.sqrt 2 * (Cm5 m / D ^ CA))) := by
          refine mul_le_mul_of_nonneg_left ?_ hClow0.le
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkey hs2)
            (mul_nonneg (by norm_num) hnorm0)
      _ = _ := by field_simp
  have hMain := (main_tower_bound hD_3 hT Kt Ωt H1 s.velocity_smooth s.displacement_smooth
    (fun t ht => (s.periodic t ht).2.1) s.initial s.terminal s.displacement_derivative
    s.divergence_eq Vt gt srcT Θt (gt.smooth []).continuousOn hmom n
    (fun m => 4 * Real.sqrt 2 * ‖pjL‖ * Cm5 m)).2 ℓ (D ^ CA) hℓ0.le hClow0.le hAbd hD7
  -- the norms
  have hgdef : g = fun t : Icc (0 : ℝ) T => w t.val := rfl
  have hgfin' : HolderFieldNormFinite ℓ n (fun t : Icc (0 : ℝ) T => w t.val) := by
    rw [← hgdef]; exact hgfin
  clear_value g
  subst hgdef
  have hvs : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (s.velocity t) :=
    fun t ht => meanInt_slice_spatial s.velocity_smooth ht
  have hvw (w' : Wd) :
      BddAbove (hierarchyJetValues True (hierarchyLabelDirection ℓ) w'
        (fun t : Icc (0 : ℝ) T => s.velocity t)) ∧
      sSup (hierarchyJetValues True (hierarchyLabelDirection ℓ) w'
        (fun t : Icc (0 : ℝ) T => s.velocity t)) ≤ ℓ ^ w'.length * endpointClosedTimeNorm T (Vt.Y w') :=
    hierarchyJetValues_le_of_recovered_halfHolder hT.le hℓ0.le w' hvs (Vt.smooth w').continuousOn
      (fun t ht x => Vt.lift w' t ht x)
  have hgs : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (w t) := fun t ht => meanInt_slice_spatial hw ht
  have hgsum : ∑ w' ∈ hierarchyAdmissibleWords (Fin 3) n,
      ℓ ^ w'.length * endpointClosedTimeNorm T (gt.Y w') ≤ Real.sqrt 2 * holderFieldNorm ℓ n (fun t : Icc (0 : ℝ) T => w t.val) := by
    unfold holderFieldNorm hierarchyFiniteWordNorm
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun w' hw' => mul_endpointClosedTimeNorm_le_of_hierarchyLabelWord hT.le
      hℓ0 w' (gt.Y w') hgs (hgfin'.2 w' hw') (fun t ht x => gt.lift w' t ht x)
  have hg0 : 0 ≤ holderFieldNorm ℓ n (fun t : Icc (0 : ℝ) T => w t.val) :=
    Finset.sum_nonneg fun w' hw' => le_csSup (hgfin'.2 w' hw') (Or.inl rfl)
  have hvsum : holderFieldNorm ℓ n (fun t : Icc (0 : ℝ) T => s.velocity t.val) ≤
      ∑ w' ∈ hierarchyAdmissibleWords (Fin 3) n, ℓ ^ w'.length * endpointClosedTimeNorm T (Vt.Y w') := by
    unfold holderFieldNorm hierarchyFiniteWordNorm
    exact Finset.sum_le_sum fun w' _ => (hvw w').2
  refine ⟨⟨fun t => hvs t.val t.property, fun w' _ => (hvw w').1⟩, ?_⟩
  have hCn0 : 0 ≤ Cn_of hD_3 n (fun m => 4 * Real.sqrt 2 * ‖pjL‖ * Cm5 m) :=
    (main_tower_bound hD_3 hT Kt Ωt H1 s.velocity_smooth s.displacement_smooth
    (fun t ht => (s.periodic t ht).2.1) s.initial s.terminal s.displacement_derivative
    s.divergence_eq Vt gt srcT Θt (gt.smooth []).continuousOn hmom n
    (fun m => 4 * Real.sqrt 2 * ‖pjL‖ * Cm5 m)).1
  have hT1 : T ≤ 1 := hP.time_le_one
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hCD : 0 ≤ Cn_of hD_3 n (fun m => 4 * Real.sqrt 2 * ‖pjL‖ * Cm5 m) * D ^ CA :=
    mul_nonneg hCn0 hClow0.le
  calc holderFieldNorm ℓ n (fun t : Icc (0 : ℝ) T => s.velocity t.val)
      ≤ _ := hvsum
    _ ≤ _ := hMain
    _ ≤ Cn_of hD_3 n (fun m => 4 * Real.sqrt 2 * ‖pjL‖ * Cm5 m) * D ^ CA * (‖pjL‖ * T) *
        (Real.sqrt 2 * holderFieldNorm ℓ n (fun t : Icc (0 : ℝ) T => w t.val)) :=
      mul_le_mul_of_nonneg_left hgsum (mul_nonneg hCD (mul_nonneg hnorm0 hT.le))
    _ ≤ Cn_of hD_3 n (fun m => 4 * Real.sqrt 2 * ‖pjL‖ * Cm5 m) * D ^ CA * (‖pjL‖ * 1) *
        (Real.sqrt 2 * holderFieldNorm ℓ n (fun t : Icc (0 : ℝ) T => w t.val)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT1 hnorm0) hCD)
        (mul_nonneg hs2 hg0)
    _ = _ := by ring

end

end TorusEuler.Paper
