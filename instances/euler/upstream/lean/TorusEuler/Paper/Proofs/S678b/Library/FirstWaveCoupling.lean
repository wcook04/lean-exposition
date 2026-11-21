import TorusEuler.FirstWaveInitialization
import TorusEuler.Paper.S2.Statements

/-! # Lemma 6.1: the sign of the first coupling, with the frame equations (2.2) from Lemma 2.2

Copy (package S678b, Lemma 6.1's own content) of the library lemma
`FirstWaveOrigin.first_coupling_lower` (FirstWaveInitialization.lean:431). The library derives
the frame equations itself from `hasDerivWithinAt_movingFrame` (the content of Lemma 2.2); the
copy takes them, and the orthonormality of the frame, from a hypothesis
`h2_2 : Statement.lemma_2_2`, as the TeX proof does (sections/03a_exact_base.tex:60-61, "the
frame equations (2.2) give `|∂_tE_1|, |∂_tE_2| ≤ |B_ρ|`"). The private helpers
`norm_signed_two_axes_le` and `trace_stationaryShearGradient` are copied unchanged. -/

open Set
open scoped InnerProductSpace

namespace TorusEuler.Paper.Lib.S678b

open MovingWaveVector

/-- Copy of the library's private `norm_signed_two_axes_le`: a vector with components of the
absolute values of two coordinates of `z` along two orthonormal axes has norm at most `‖z‖`. -/
theorem norm_signed_two_axes_le {x y z : Vec3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : ⟪x, y⟫_ℝ = 0) {a b : ℝ}
    (ha : a ^ 2 = ⟪x, z⟫_ℝ ^ 2) (hb : b ^ 2 = ⟪y, z⟫_ℝ ^ 2) :
    ‖a • x + b • y‖ ≤ ‖z‖ := by
  have hyx : ⟪y, x⟫_ℝ = 0 := (real_inner_comm x y).trans hxy
  have hnorm (p q : ℝ) : ‖p • x + q • y‖ ^ 2 = p ^ 2 + q ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hxy, hyx, norm_smul, hx, hy, mul_one, Real.norm_eq_abs, sq_abs]
    ring
  let Z := ⟪x, z⟫_ℝ • x + ⟪y, z⟫_ℝ • y
  have hself : ‖Z‖ ^ 2 = ⟪Z, z⟫_ℝ := by
    unfold Z
    rw [hnorm, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring
  have hZ : ‖Z‖ ≤ ‖z‖ := by
    by_cases hh : ‖Z‖ = 0
    · rw [hh]
      exact norm_nonneg _
    have hpos : 0 < ‖Z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hh)
    have hineq := (le_abs_self _).trans (abs_real_inner_le_norm Z z)
    rw [← hself] at hineq
    exact (mul_le_mul_iff_right₀ hpos).mp (by simpa only [pow_two, mul_comm] using hineq)
  have heq : ‖a • x + b • y‖ ^ 2 = ‖Z‖ ^ 2 := by
    unfold Z
    rw [hnorm, hnorm, ha, hb]
  exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp heq).trans_le hZ

/-- Copy of the library's private `trace_stationaryShearGradient`: `B_ρ` is trace free. -/
theorem trace_stationaryShearGradient (s : ℝ) :
    LinearMap.trace ℝ Vec3 (stationaryShearGradient s).toLinearMap = 0 := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, stationaryShearGradient,
    Fin.sum_univ_three]

/-- The first coupling of the first wave stays at least `π` on `[0,T]`
(sections/03a_exact_base.tex:60-66), copy of `FirstWaveOrigin.first_coupling_lower` with the
frame equations (2.2) and the orthonormality of the frame taken from `h2_2` (Lemma 2.2 applied
to the pair `(κ(·,0), 𝐚(·,0))` over the constant trace-free gradient `B_ρ` on `J = [0,T]`).
They give `|∂_tE_1|, |∂_tE_2| ≤ |B_ρ|`, so `ν(t,0) = E_1·B_ρE_2` changes by at most
`2t|B_ρ|^2 ≤ |B_ρ|/4 ≤ π` from its value `2π` of (6.4). -/
theorem first_coupling_lower (h2_2 : Statement.lemma_2_2) {s T freq : ℝ}
    (w : FirstWaveOrigin s T freq)
    (hf : 0 < freq) (hs : |s| ≤ 1) (hsmall : T * ‖stationaryShearGradient s‖ ≤ 1 / 8)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Real.pi ≤ entry (frame w.covector w.amplitude t) (stationaryShearGradient s) 0 1 := by
  let B := stationaryShearGradient s
  let e := frame w.covector w.amplitude
  let ν (u : ℝ) := entry (e u) B 0 1
  let η (u : ℝ) := entry (e u) B 2 1
  let χ (u : ℝ) := entry (e u) B 0 2
  let d₁ (u : ℝ) := (-ν u) • e u 1 - χ u • e u 2
  let d₂ (u : ℝ) := ν u • e u 0 - η u • e u 2
  -- Lemma 2.2 for the pair at the origin over the constant gradient `B_ρ` on `[0,T]`.
  have hWave : WaveOn (Icc 0 T) (fun _ => B) w.covector w.amplitude :=
    ⟨w.covector_equation, fun u hu => by
      simpa only [affineWaveAmplitudeOperator_apply, affineWavePressureCoeff] using
        w.amplitude_equation u hu⟩
  have hFrameEq (u : ℝ) (hu : u ∈ Icc 0 T) :=
    h2_2 (J := Icc 0 T) (B := fun _ => B) (k := w.covector) (a := w.amplitude)
      (fun _ _ => trace_stationaryShearGradient s) hWave w.transverse u hu
  have hFrame (u : ℝ) (hu : u ∈ Icc 0 T) : Orthonormal ℝ (e u) := (hFrameEq u hu).1
  have hDeriv (u : ℝ) (hu : u ∈ Icc 0 T) :
      HasDerivWithinAt (fun x => e x 0) (d₁ u) (Icc 0 T) u ∧
      HasDerivWithinAt (fun x => e x 1) (d₂ u) (Icc 0 T) u :=
    ⟨(hFrameEq u hu).2.1, (hFrameEq u hu).2.2.1⟩
  have hDerivNorm (u : ℝ) (hu : u ∈ Icc 0 T) : ‖d₁ u‖ ≤ ‖B‖ ∧ ‖d₂ u‖ ≤ ‖B‖ := by
    have he := hFrame u hu
    have hν : ⟪e u 1, B.adjoint (e u 0)⟫_ℝ = ν u :=
      (B.adjoint_inner_right _ _).trans (real_inner_comm _ _)
    have hχ : ⟪e u 2, B.adjoint (e u 0)⟫_ℝ = χ u :=
      (B.adjoint_inner_right _ _).trans (real_inner_comm _ _)
    constructor
    · calc
        ‖d₁ u‖ ≤ ‖B.adjoint (e u 0)‖ := by
          unfold d₁
          rw [sub_eq_add_neg, ← neg_smul]
          exact norm_signed_two_axes_le (he.norm_eq_one 1) (he.norm_eq_one 2)
            (he.inner_eq_zero (by decide : (1 : Fin 3) ≠ 2))
            (by rw [hν]; ring) (by rw [hχ]; ring)
        _ ≤ ‖B‖ := by
          simpa only [LinearIsometryEquiv.norm_map, he.norm_eq_one 0, mul_one] using
            B.adjoint.le_opNorm (e u 0)
    · calc
        ‖d₂ u‖ ≤ ‖B (e u 1)‖ := by
          unfold d₂
          rw [sub_eq_add_neg, ← neg_smul]
          exact norm_signed_two_axes_le (he.norm_eq_one 0) (he.norm_eq_one 2)
            (he.inner_eq_zero (by decide : (0 : Fin 3) ≠ 2))
            rfl (by change (-η u) ^ 2 = (η u) ^ 2; ring)
        _ ≤ ‖B‖ := by simpa only [he.norm_eq_one 1, mul_one] using B.le_opNorm (e u 1)
  let dν (u : ℝ) := ⟪e u 0, B (d₂ u)⟫_ℝ + ⟪d₁ u, B (e u 1)⟫_ℝ
  have hDν (u : ℝ) (hu : u ∈ Icc 0 T) : HasDerivWithinAt ν (dν u) (Icc 0 T) u :=
    ((hDeriv u hu).1).inner ℝ (B.hasFDerivAt.comp_hasDerivWithinAt u (hDeriv u hu).2)
  have hDνle (u : ℝ) (hu : u ∈ Icc 0 T) : ‖dν u‖ ≤ 2 * ‖B‖ ^ 2 := by
    have he := hFrame u hu
    have h₁ : |⟪e u 0, B (d₂ u)⟫_ℝ| ≤ ‖B‖ ^ 2 := by
      have h := abs_real_inner_le_norm (e u 0) (B (d₂ u))
      rw [he.norm_eq_one 0, one_mul] at h
      rw [pow_two]
      exact h.trans ((B.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hDerivNorm u hu).2 (norm_nonneg _)))
    have h₂ : |⟪d₁ u, B (e u 1)⟫_ℝ| ≤ ‖B‖ ^ 2 := by
      have h := abs_real_inner_le_norm (d₁ u) (B (e u 1))
      have hB : ‖B (e u 1)‖ ≤ ‖B‖ := by
        simpa only [he.norm_eq_one 1, mul_one] using B.le_opNorm (e u 1)
      rw [pow_two]
      exact h.trans (mul_le_mul (hDerivNorm u hu).1 hB (norm_nonneg _) (norm_nonneg _))
    rw [Real.norm_eq_abs]
    exact (abs_add_le _ _).trans (by linarith only [h₁, h₂])
  have hdiff := norm_image_sub_le_of_norm_deriv_le_segment' hDν
    (fun u hu => hDνle u (Ico_subset_Icc_self hu)) t ht
  rw [Real.norm_eq_abs, sub_zero] at hdiff
  have hsmall' : 2 * ‖B‖ ^ 2 * t ≤ ‖B‖ / 4 := by
    have h := mul_le_mul_of_nonneg_right ht.2 (show 0 ≤ 2 * ‖B‖ ^ 2 by positivity)
    have hb := mul_le_mul_of_nonneg_right hsmall (norm_nonneg B)
    change T * ‖B‖ * ‖B‖ ≤ 1 / 8 * ‖B‖ at hb
    nlinarith only [h, hb]
  have hmax : ‖B‖ / 4 ≤ Real.pi := by linarith [norm_stationaryShearGradient_le hs]
  have hinit : ν 0 = 2 * Real.pi := (w.initial_couplings hf).1
  change Real.pi ≤ ν t
  linarith only [(abs_le.mp (hdiff.trans (hsmall'.trans hmax))).1, hinit]

end TorusEuler.Paper.Lib.S678b
