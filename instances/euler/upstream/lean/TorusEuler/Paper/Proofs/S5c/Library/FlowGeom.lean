import TorusEuler.Paper.Proofs.S5c.Library.HessCalc
import TorusEuler.Paper.Proofs.S5c.Library.Center

/-!
# Glue for Lemma 5.9: the inverse flow `Y = X(t,·)⁻¹` and the transported phase

Facts about the inverse label flow `Y = X t 0` of a parent of §5.1 used in the Hessian
identity (5.51) (`sections/08_exact_wave.tex:172-204`):

* `inverseFlow_right`: `X(t, Y(x)) = x`;
* `norm_fderiv_inverseFlow_le`: `|D_xY| ≤ 𝖣` (the bound (5.1) for `(D_aX)⁻¹`);
* `fderiv_inverseFlow_eq`, `norm_fderiv2_inverseFlow_le`: `D_xY = G∘Y` with
  `G = (D_aX)⁻¹`, hence `|D_x²Y| ≤ 𝖣 sup|D_aG|`;
* `inner_carrier_fderiv_inverseFlow`: `k_*·D_xY v = κ(t,Y(x))·v` (the phase gradient is
  the transported wave vector);
* `norm_carrier_le`, `norm_waveVector_le`: `|k_*| ≤ 𝖣λ`, `|κ| ≤ 𝖣²λ` ((5.3) and (5.1)).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5c

open HierarchyTwistedProfile InnerProductSpace

noncomputable section

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3} {D lam : ℝ}

/-- `X(t, Y(x)) = x` for the inverse flow `Y = X t 0`. -/
theorem inverseFlow_right (hT : 0 < T) (hP : S5.Parent T U X pU D lam) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x : Vec3) : X 0 t (X t 0 x) = x := by
  obtain ⟨K, hK⟩ := Bridge.Parent.exists_lipschitz hT hP
  exact (hP.flow.inverse hK ⟨le_rfl, hT.le⟩ ht).2 x

/-- `|D_xY| ≤ 𝖣`, the bound (5.1) for `(D_aX)⁻¹`. -/
theorem norm_fderiv_inverseFlow_le (hT : 0 < T) (hP : S5.Parent T U X pU D lam) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x : Vec3) : ‖fderiv ℝ (X t 0) x‖ ≤ D := by
  have h := hP.inverse_deformation_le t ht (X t 0 x)
  rwa [inverseFlow_right hT hP ht] at h

/-- `D_xY = G ∘ Y` with `G(t,a) = (D_aX(t,a))⁻¹ = D_xY(X(t,a))`. -/
theorem fderiv_inverseFlow_eq (hT : 0 < T) (hP : S5.Parent T U X pU D lam) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    fderiv ℝ (X t 0) = fun x => fderiv ℝ (X t 0) (X 0 t (X t 0 x)) := by
  funext x
  rw [inverseFlow_right hT hP ht]

/-- The inverse deformation `G(t,·) = (D_aX(t,·))⁻¹` is smooth in the label. -/
theorem inverseDeformation_smooth (hT : 0 < T) (hP : S5.Parent T U X pU D lam) {t : ℝ}
    (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (fun a => fderiv ℝ (X t 0) (X 0 t a)) := by
  have h := hP.flow.contDiffOn_inverseLabelDerivative hT hP.velocity_smooth hP.velocity_periodic
  have h' : ContDiffOn ℝ ∞ (Function.uncurry fun (r : ℝ) (a : Vec3) => fderiv ℝ (X r 0) (X 0 r a))
      (Icc 0 T ×ˢ (univ : Set Vec3)) := h
  exact contDiff_slice h' ht

/-- `|D_x²Y| ≤ 𝖣 B` when the label derivative of `G = (D_aX)⁻¹` is bounded by `B`. -/
theorem norm_fderiv2_inverseFlow_le (hT : 0 < T) (hP : S5.Parent T U X pU D lam) {t : ℝ}
    (ht : t ∈ Icc 0 T) {B : ℝ}
    (hB : ∀ a, ‖iteratedFDeriv ℝ 1 (fun a => fderiv ℝ (X t 0) (X 0 t a)) a‖ ≤ B) (x : Vec3) :
    ‖fderiv ℝ (fderiv ℝ (X t 0)) x‖ ≤ B * D := by
  let G : Vec3 → Vec3 →L[ℝ] Vec3 := fun a => fderiv ℝ (X t 0) (X 0 t a)
  have hG : ContDiff ℝ ∞ G := inverseDeformation_smooth hT hP ht
  have hY : ContDiff ℝ ∞ (X t 0) := contDiff_slice (inverseFlow_smooth hT hP) ht
  have hEq : fderiv ℝ (X t 0) = G ∘ X t 0 := fderiv_inverseFlow_eq hT hP ht
  have hd : HasFDerivAt (G ∘ X t 0) ((fderiv ℝ G (X t 0 x)).comp (fderiv ℝ (X t 0) x)) x :=
    ((hG.differentiable (by simp)) _).hasFDerivAt.comp x
      ((hY.differentiable (by simp)) x).hasFDerivAt
  rw [hEq, hd.fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 : ‖fderiv ℝ G (X t 0 x)‖ ≤ B := by
    have := hB (X t 0 x)
    rw [norm_iteratedFDeriv_one] at this
    exact this
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  exact mul_le_mul h1 (norm_fderiv_inverseFlow_le hT hP ht x) (norm_nonneg _) hB0

/-- The phase gradient is the transported wave vector: `k_*·D_xY v = κ(t, Y(x))·v`. -/
theorem inner_carrier_fderiv_inverseFlow (hT : 0 < T) (hP : S5.Parent T U X pU D lam) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x v : Vec3) :
    ⟪k, fderiv ℝ (X t 0) x v⟫_ℝ = ⟪S5.waveVector X k t (X t 0 x), v⟫_ℝ := by
  simp only [S5.waveVector, labelWaveVector, inverseFlow_right hT hP ht,
    ContinuousLinearMap.adjoint_inner_left]

/-- `|k_*| ≤ 𝖣λ`: `k_* = D_aX(t₀,0)ᵀ κ(t₀,0)` with `|κ(t₀,0)| = λ` and (5.1). -/
theorem norm_carrier_le (hP : S5.Parent T U X pU D lam) {t₀ : ℝ} (hL : S5.Launch T X k lam t₀) :
    ‖k‖ ≤ D * lam := by
  have hc := Bridge.Launch.carrier_eq hP hL
  have ht₀ : t₀ ∈ Icc 0 T := Bridge.Launch.start_mem hL
  rw [← hc, ← hL.frequency]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact mul_le_mul_of_nonneg_right (hP.deformation_le t₀ ht₀ 0) (norm_nonneg _)

/-- `|κ(t,a)| ≤ 𝖣²λ`, (5.3) with (5.1). -/
theorem norm_waveVector_le (hP : S5.Parent T U X pU D lam) {t₀ : ℝ} (hL : S5.Launch T X k lam t₀)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) : ‖S5.waveVector X k t a‖ ≤ D ^ 2 * lam := by
  have hD : 0 ≤ D := zero_le_one.trans (Bridge.Parent.scale_ge_one hP)
  simp only [S5.waveVector, labelWaveVector]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  rw [ContinuousLinearMap.adjoint.norm_map]
  calc ‖fderiv ℝ (X t 0) (X 0 t a)‖ * ‖k‖ ≤ D * (D * lam) :=
        mul_le_mul (hP.inverse_deformation_le t ht a) (norm_carrier_le hP hL) (norm_nonneg _) hD
    _ = D ^ 2 * lam := by ring

end

end TorusEuler.Paper.Lib.S5c
