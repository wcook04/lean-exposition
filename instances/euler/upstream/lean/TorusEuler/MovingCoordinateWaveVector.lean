import TorusEuler.MovingFrame
import TorusEuler.ReferenceRiccati

open Set
open scoped InnerProductSpace

namespace TorusEuler.MovingWaveVector

noncomputable section

abbrev Space := EuclideanSpace ℝ (Fin 3)

def frame (kp ap : ℝ → Space) (t : ℝ) : Fin 3 → Space :=
  ![NormedSpace.normalize (kp t), NormedSpace.normalize (ap t),
    cross3 (NormedSpace.normalize (kp t)) (NormedSpace.normalize (ap t))]

def entry (e : Fin 3 → Space) (A : Space →L[ℝ] Space) (i j : Fin 3) : ℝ :=
  ⟪e i, A (e j)⟫_ℝ

def strain (e : Fin 3 → Space) (B E : Space →L[ℝ] Space) (S σratio : ℝ) :
    Space →L[ℝ] Space :=
  B + (S * σratio) • InnerProductSpace.rankOne ℝ (e 1) (e 0) + E

def X (e : ℝ → Fin 3 → Space) (k : ℝ → Space) (scale t : ℝ) : ℝ :=
  ⟪e t 0, k t⟫_ℝ / scale

def Q (e : ℝ → Fin 3 → Space) (k : ℝ → Space) (scale S t : ℝ) : ℝ :=
  S * ⟪e t 1, k t⟫_ℝ / scale

def Z (e : ℝ → Fin 3 → Space) (k : ℝ → Space) (scale t : ℝ) : ℝ :=
  ⟪e t 2, k t⟫_ℝ / scale

private theorem frameExpansion {e : Fin 3 → Space} (he : Orthonormal ℝ e) (v : Space) :
    v = ⟪e 0, v⟫_ℝ • e 0 + ⟪e 1, v⟫_ℝ • e 1 + ⟪e 2, v⟫_ℝ • e 2 := by
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ Space := by simp
  have hspan := (he.linearIndependent.span_eq_top_of_card_eq_finrank hcard).ge
  simpa only [OrthonormalBasis.coe_mk, Fin.sum_univ_three] using
    ((OrthonormalBasis.mk he hspan).sum_repr' v).symm

private theorem pairing_coordinate {e : ℝ → Fin 3 → Space} {k : ℝ → Space}
    {scale S t : ℝ} (hscale : scale ≠ 0) (hS : S ≠ 0) (i : Fin 3) :
    ⟪e t i, k t⟫_ℝ = scale * (![X e k scale t, Q e k scale S t / S, Z e k scale t] : Fin 3 → ℝ) i := by
  fin_cases i <;> simp [X, Q, Z] <;> field_simp

/-- The normalized coordinates give the first formula in (2.3). -/
theorem scaled_waveVector_decomposition {e : ℝ → Fin 3 → Space} {k : ℝ → Space}
    {scale S t : ℝ} (he : Orthonormal ℝ (e t)) (hscale : scale ≠ 0) (hS : S ≠ 0) :
    k t = scale • (X e k scale t • e t 0 + (Q e k scale S t / S) • e t 1 + Z e k scale t • e t 2) := by
  nth_rw 1 [frameExpansion he (k t)]
  rw [pairing_coordinate hscale hS 0, pairing_coordinate hscale hS 1, pairing_coordinate hscale hS 2]
  simp [smul_add, smul_smul]

/-- In an orthonormal frame the added shear has just its `(1, 0)` entry. -/
theorem entry_strain {e : Fin 3 → Space} (he : Orthonormal ℝ e)
    (B E : Space →L[ℝ] Space) (S σratio : ℝ) (i j : Fin 3) :
    entry e (strain e B E S σratio) i j =
      entry e B i j + (if i = 1 ∧ j = 0 then S * σratio else 0) + entry e E i j := by
  have hp := orthonormal_iff_ite.mp he
  simp only [entry, strain, add_apply, smul_apply,
    InnerProductSpace.rankOne_apply, inner_add_right, real_inner_smul_right, hp]
  fin_cases i <;> fin_cases j <;> simp

private theorem column_pairing {e : ℝ → Fin 3 → Space} {k : ℝ → Space}
    {scale S t : ℝ} (he : Orthonormal ℝ (e t)) (hscale : scale ≠ 0) (hS : S ≠ 0)
    (A : Space →L[ℝ] Space) (j : Fin 3) :
    ⟪e t j, A.adjoint (k t)⟫_ℝ =
      scale * (entry (e t) A 0 j * X e k scale t +
        entry (e t) A 1 j * (Q e k scale S t / S) + entry (e t) A 2 j * Z e k scale t) := by
  rw [ContinuousLinearMap.adjoint_inner_right, scaled_waveVector_decomposition (k := k) he hscale hS]
  simp only [entry, real_inner_smul_right, inner_add_right, real_inner_comm (A (e t j))]
  ring

/-- The coordinate ODE in Lemma 2.3, with the perturbation matrix's three
rows written in the scaled moving coordinates. -/
theorem normalized_waveVector_derivatives {e : ℝ → Fin 3 → Space} {k : ℝ → Space}
    {J : Set ℝ} {scale S σratio t : ℝ} {B E : Space →L[ℝ] Space}
    (he : Orthonormal ℝ (e t)) (hscale : scale ≠ 0) (hS : S ≠ 0)
    (hE₁ : HasDerivWithinAt (fun u => e u 0)
      ((-entry (e t) B 0 1) • e t 1 - entry (e t) B 0 2 • e t 2) J t)
    (hE₂ : HasDerivWithinAt (fun u => e u 1)
      (entry (e t) B 0 1 • e t 0 - entry (e t) B 2 1 • e t 2) J t)
    (hE₃ : HasDerivWithinAt (fun u => e u 2)
      (entry (e t) B 0 2 • e t 0 + entry (e t) B 2 1 • e t 1) J t)
    (hk : HasDerivWithinAt k (-((strain (e t) B E S σratio).adjoint (k t))) J t) :
    let b := entry (e t) B
    let d := entry (e t) E
    let x := X e k scale t
    let q := Q e k scale S t
    let z := Z e k scale t
    HasDerivWithinAt (X e k scale)
      (-b 0 0 * x - (σratio + b 1 0 / S + b 0 1 / S) * q - (b 2 0 + b 0 2) * z
        - (d 0 0 * x + d 1 0 * q / S + d 2 0 * z)) J t ∧
    HasDerivWithinAt (Q e k scale S)
      (-b 1 1 * q - 2 * S * b 2 1 * z - (S * d 0 1 * x + d 1 1 * q + S * d 2 1 * z)) J t ∧
    HasDerivWithinAt (Z e k scale)
      (-b 2 2 * z - (b 1 2 - b 2 1) * q / S
        - (d 0 2 * x + d 1 2 * q / S + d 2 2 * z)) J t := by
  dsimp only
  have hcolumn := column_pairing (k := k) he hscale hS (strain (e t) B E S σratio)
  have hpair := pairing_coordinate (e := e) (k := k) (t := t) hscale hS
  have hEntry := entry_strain he B E S σratio
  refine ⟨((hE₁.inner ℝ hk).div_const scale).congr_deriv ?_,
    (((hE₂.inner ℝ hk).const_mul S).div_const scale).congr_deriv ?_,
    ((hE₃.inner ℝ hk).div_const scale).congr_deriv ?_⟩ <;>
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left, inner_neg_right,
      hpair, hcolumn, hEntry, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, and_true,
      and_false, ite_true, ite_false, add_zero] <;>
    field_simp <;> ring

/-- Applying the normalized system to the frame of the preceding wave gives
the exact wave-vector equations of Lemma 2.3. All operators use normalized time. -/
theorem moving_waveVector_derivatives {kp ap k : ℝ → Space} {J : Set ℝ}
    {scale S σratio t : ℝ} {B E : Space →L[ℝ] Space} (ht : t ∈ J)
    (hscale : scale ≠ 0) (hS : S ≠ 0)
    (htrace : LinearMap.trace ℝ Space B.toLinearMap = 0)
    (hkp₀ : kp t ≠ 0) (hap₀ : ap t ≠ 0) (hperp : ⟪kp t, ap t⟫_ℝ = 0)
    (hkp : HasDerivWithinAt kp (-(B.adjoint (kp t))) J t)
    (hap : HasDerivWithinAt ap
      (-(B (ap t)) + (2 * ⟪kp t, B (ap t)⟫_ℝ / ‖kp t‖ ^ 2) • kp t) J t)
    (hk : HasDerivWithinAt k (-((strain (frame kp ap t) B E S σratio).adjoint (k t))) J t) :
    let e := frame kp ap
    let b := entry (e t) B
    let d := entry (e t) E
    let x := X e k scale t
    let q := Q e k scale S t
    let z := Z e k scale t
    HasDerivWithinAt (X e k scale)
      (-b 0 0 * x - (σratio + b 1 0 / S + b 0 1 / S) * q - (b 2 0 + b 0 2) * z
        - (d 0 0 * x + d 1 0 * q / S + d 2 0 * z)) J t ∧
    HasDerivWithinAt (Q e k scale S)
      (-b 1 1 * q - 2 * S * b 2 1 * z - (S * d 0 1 * x + d 1 1 * q + S * d 2 1 * z)) J t ∧
    HasDerivWithinAt (Z e k scale)
      (-b 2 2 * z - (b 1 2 - b 2 1) * q / S
        - (d 0 2 * x + d 1 2 * q / S + d 2 2 * z)) J t := by
  obtain ⟨hE₁, hE₂, hE₃, _⟩ :=
    hasDerivWithinAt_movingFrame ht B htrace hkp₀ hap₀ hperp hkp hap
  have he : Orthonormal ℝ (frame kp ap t) := orthonormal_movingFrame hkp₀ hap₀ hperp
  exact normalized_waveVector_derivatives he hscale hS hE₁ hE₂ hE₃ hk

theorem coordinate_initial_values {e : ℝ → Fin 3 → Space} {k : ℝ → Space}
    {scale S t₀ : ℝ} (he : Orthonormal ℝ (e t₀)) (hscale : scale ≠ 0)
    (hk₀ : k t₀ = scale • e t₀ 2) :
    X e k scale t₀ = 0 ∧ Q e k scale S t₀ = 0 ∧ Z e k scale t₀ = 1 := by
  have hi := orthonormal_iff_ite.mp he
  simp [X, Q, Z, hk₀, real_inner_smul_right, hi, hscale, he.norm_eq_one 2]

private theorem abs_le_of_deriv_abs_le {f f' : ℝ → ℝ} {T M τ : ℝ}
    (ht : τ ∈ Icc 0 T) (h₀ : f 0 = 0)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (f' t) (Icc 0 T) t)
    (hb : ∀ t ∈ Icc 0 T, |f' t| ≤ M) : |f τ| ≤ M * T := by
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb 0 h0T)
  have h := (convex_Icc (0 : ℝ) T).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd (fun t ht => by simpa only [Real.norm_eq_abs] using hb t ht) h0T ht
  rw [h₀, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht.1] at h
  exact h.trans (mul_le_mul_of_nonneg_left ht.2 hM)

/-- A triangular residual estimate for the scaled wave vector on the whole
normalized window, with an explicit polynomial loss. -/
theorem polynomial_waveVector_error {ε T D : ℝ} {X Q Z rX rQ rZ : ℝ → ℝ}
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (hT : 2 ≤ T) (hD : 0 ≤ D)
    (hsmall : 12 * D * T ^ 3 ≤ 1) (hX₀ : X 0 = 0) (hQ₀ : Q 0 = 0) (hZ₀ : Z 0 = 1)
    (hX : ∀ t ∈ Icc 0 T, HasDerivWithinAt X (-Q t + rX t) (Icc 0 T) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Q (-ε * Z t + rQ t) (Icc 0 T) t)
    (hZ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Z (rZ t) (Icc 0 T) t)
    (hres : ∀ t ∈ Icc 0 T, let L := D * (|X t| + |Q t| + |Z t|)
      |rX t| ≤ L ∧ |rQ t| ≤ L ∧ |rZ t| ≤ L) :
    ∀ τ ∈ Icc 0 T,
      |X τ - ReferenceRiccati.x ε τ| + |Q τ + ε * τ| + |Z τ - 1| ≤ 24 * D * T ^ 5 := by
  let u (t : ℝ) := X t - ReferenceRiccati.x ε t
  let v (t : ℝ) := Q t + ε * t
  let w (t : ℝ) := Z t - 1
  have hu₀ : u 0 = 0 := by simp [u, ReferenceRiccati.x, hX₀]
  have hv₀ : v 0 = 0 := by simp [v, hQ₀]
  have hw₀ : w 0 = 0 := by simp [w, hZ₀]
  have hu : ∀ t ∈ Icc 0 T, HasDerivWithinAt u (-v t + rX t) (Icc 0 T) t := by
    intro t ht
    exact ((hX t ht).sub (ReferenceRiccati.hasDerivAt_x ε t).hasDerivWithinAt).congr_deriv
      (by dsimp [v]; ring)
  have hv : ∀ t ∈ Icc 0 T, HasDerivWithinAt v (-ε * w t + rQ t) (Icc 0 T) t := by
    intro t ht
    exact ((hQ t ht).add ((hasDerivAt_id t).const_mul ε).hasDerivWithinAt).congr_deriv
      (by dsimp [w]; ring)
  have hw : ∀ t ∈ Icc 0 T, HasDerivWithinAt w (rZ t) (Icc 0 T) t :=
    fun t ht => (hZ t ht).sub_const 1
  have hT₀ : 0 ≤ T := by linarith
  have hT₁ : 1 ≤ T := by linarith
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT₀⟩
  let f (t : ℝ) := |u t| + |v t| + |w t|
  have hfc : ContinuousOn f (Icc 0 T) :=
    ((HasDerivWithinAt.continuousOn hu).abs.add (HasDerivWithinAt.continuousOn hv).abs).add
      (HasDerivWithinAt.continuousOn hw).abs
  obtain ⟨tmax, htmax, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, h0T⟩ hfc
  let M := f tmax
  have hM : 0 ≤ M := by dsimp [M, f]; positivity
  have hfmax : ∀ t ∈ Icc 0 T, f t ≤ M := fun _ ht => hmax ht
  have hTsq_ge : T ≤ T ^ 2 := by nlinarith [mul_nonneg hT₀ (sub_nonneg.mpr hT₁)]
  have hTcube_ge : T ^ 2 ≤ T ^ 3 := by nlinarith [mul_nonneg (sq_nonneg T) (sub_nonneg.mpr hT₁)]
  have hstate (t : ℝ) (ht : t ∈ Icc 0 T) : |X t| + |Q t| + |Z t| ≤ 2 * T ^ 2 + M := by
    have hXsum : X t = u t + ReferenceRiccati.x ε t := by dsimp [u]; ring
    have hQsum : Q t = v t + -(ε * t) := by dsimp [v]; ring
    have hZsum : Z t = w t + 1 := by dsimp [w]; ring
    have hxx : ReferenceRiccati.x ε t ≤ T ^ 2 / 2 := by
      have htSq := pow_le_pow_left₀ ht.1 ht.2 2
      have hεtSq := mul_le_mul_of_nonneg_right hε₁ (sq_nonneg t)
      unfold ReferenceRiccati.x
      linarith
    have hεt : ε * t ≤ T := (mul_le_of_le_one_left ht.1 hε₁).trans ht.2
    have hxAbs := (abs_add_le (u t) (ReferenceRiccati.x ε t))
    rw [← hXsum, abs_of_nonneg (ReferenceRiccati.x_nonneg hε₀ t)] at hxAbs
    have hqAbs := abs_add_le (v t) (-(ε * t))
    rw [← hQsum, abs_neg, abs_of_nonneg (mul_nonneg hε₀ ht.1)] at hqAbs
    have hzAbs := abs_add_le (w t) (1 : ℝ)
    rw [← hZsum, abs_one] at hzAbs
    have hlocal := hfmax t ht
    dsimp [f] at hlocal
    nlinarith
  let R := D * (2 * T ^ 2 + M)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hrs (t : ℝ) (ht : t ∈ Icc 0 T) : |rX t| ≤ R ∧ |rQ t| ≤ R ∧ |rZ t| ≤ R := by
    obtain ⟨h₁, h₂, h₃⟩ := hres t ht
    have h := mul_le_mul_of_nonneg_left (hstate t ht) hD
    exact ⟨h₁.trans h, h₂.trans h, h₃.trans h⟩
  have hwbound (t : ℝ) (ht : t ∈ Icc 0 T) : |w t| ≤ R * T :=
    abs_le_of_deriv_abs_le ht hw₀ hw fun t ht => (hrs t ht).2.2
  have hvbound (t : ℝ) (ht : t ∈ Icc 0 T) : |v t| ≤ 2 * R * T ^ 2 := by
    have hb (t : ℝ) (ht : t ∈ Icc 0 T) : |-ε * w t + rQ t| ≤ 2 * R * T := by
      calc
        _ ≤ ε * |w t| + |rQ t| := by
          simpa only [abs_mul, abs_neg, abs_of_nonneg hε₀] using abs_add_le (-ε * w t) (rQ t)
        _ ≤ R * T + R := add_le_add
          ((mul_le_of_le_one_left (abs_nonneg _) hε₁).trans (hwbound t ht)) (hrs t ht).2.1
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hT₁ hR]
    have h := abs_le_of_deriv_abs_le ht hv₀ hv hb
    nlinarith
  have hubound (t : ℝ) (ht : t ∈ Icc 0 T) : |u t| ≤ 3 * R * T ^ 3 := by
    have hb (t : ℝ) (ht : t ∈ Icc 0 T) : |-v t + rX t| ≤ 3 * R * T ^ 2 := by
      calc
        _ ≤ |v t| + |rX t| := by simpa only [abs_neg] using abs_add_le (-v t) (rX t)
        _ ≤ 2 * R * T ^ 2 + R := add_le_add (hvbound t ht) (hrs t ht).1
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left (hT₁.trans hTsq_ge) hR]
    have h := abs_le_of_deriv_abs_le ht hu₀ hu hb
    nlinarith
  have hsum : M ≤ 6 * R * T ^ 3 := by
    have hT2T3 := mul_le_mul_of_nonneg_left hTcube_ge hR
    have hTT3 := mul_le_mul_of_nonneg_left (hTsq_ge.trans hTcube_ge) hR
    dsimp [M, f]
    nlinarith [hubound tmax htmax, hvbound tmax htmax, hwbound tmax htmax]
  have hMbound : M ≤ 24 * D * T ^ 5 := by
    dsimp [R] at hsum
    nlinarith [mul_le_mul_of_nonneg_right hsmall hM]
  intro τ hτ
  exact (hfmax τ hτ).trans hMbound

private def residualX (b d : Fin 3 → Fin 3 → ℝ) (S σratio x q z : ℝ) : ℝ :=
  (-b 0 0 - d 0 0) * x + (1 - σratio - (b 1 0 + b 0 1 + d 1 0) / S) * q +
    (-(b 2 0 + b 0 2 + d 2 0)) * z

private def residualQ (b d : Fin 3 → Fin 3 → ℝ) (ε S x q z : ℝ) : ℝ :=
  (-(S * d 0 1)) * x + (-b 1 1 - d 1 1) * q + (ε - 2 * S * b 2 1 - S * d 2 1) * z

private def residualZ (b d : Fin 3 → Fin 3 → ℝ) (S x q z : ℝ) : ℝ :=
  (-d 0 2) * x + (-(b 1 2 - b 2 1 + d 1 2) / S) * q + (-b 2 2 - d 2 2) * z

/-- The norm of a strain controls each of its orthonormal-frame entries. -/
theorem coefficient_abs_le_norm {e : Fin 3 → Space} (he : Orthonormal ℝ e)
    (A : Space →L[ℝ] Space) (i j : Fin 3) : |entry e A i j| ≤ ‖A‖ := by
  calc
    _ ≤ ‖e i‖ * ‖A (e j)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖A‖ := by
      simpa only [he.norm_eq_one i, he.norm_eq_one j, one_mul, mul_one] using A.le_opNorm (e j)

private theorem abs_threeProducts_bound {a b c x q z M : ℝ}
    (ha : |a| ≤ M) (hb : |b| ≤ M) (hc : |c| ≤ M) :
    |a * x + b * q + c * z| ≤ M * (|x| + |q| + |z|) := by
  calc
    _ ≤ |a * x + b * q| + |c * z| := abs_add_le _ _
    _ ≤ |a * x| + |b * q| + |c * z| := add_le_add (abs_add_le _ _) le_rfl
    _ = |a| * |x| + |b| * |q| + |c| * |z| := by simp only [abs_mul]
    _ ≤ M * |x| + M * |q| + M * |z| := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hb (abs_nonneg _)))
      (mul_le_mul_of_nonneg_right hc (abs_nonneg _))
    _ = _ := by ring

private theorem abs_div_le_self_of_one_le {a S : ℝ} (hS : 1 ≤ S) : |a / S| ≤ |a| := by
  rw [abs_div, abs_of_nonneg (zero_le_one.trans hS)]
  exact div_le_self (abs_nonneg _) hS

private theorem residual_bounds {b d : Fin 3 → Fin 3 → ℝ}
    {ε T δ S σratio x q z : ℝ} (hδ : 0 ≤ δ) (hT : 1 ≤ T) (hS : 1 ≤ S)
    (hb : ∀ i j, |b i j| ≤ δ) (hd : ∀ i j, |d i j| ≤ δ)
    (hdS : ∀ i j, |S * d i j| ≤ δ) (hσ : |σratio - 1| ≤ 2 * T * δ)
    (hε : |2 * S * b 2 1 - ε| ≤ δ) :
    let L := (5 * T * δ) * (|x| + |q| + |z|)
    |residualX b d S σratio x q z| ≤ L ∧
    |residualQ b d ε S x q z| ≤ L ∧
    |residualZ b d S x q z| ≤ L := by
  dsimp only
  have hTδ : δ ≤ T * δ := by simpa using mul_le_mul_of_nonneg_right hT hδ
  have hbbd (i j i' j' m n : Fin 3) : |b i j + b i' j' + d m n| ≤ 3 * δ := by
    have h := (abs_add_le (b i j + b i' j') (d m n)).trans
      (add_le_add ((abs_add_le (b i j) (b i' j')).trans (add_le_add (hb i j) (hb i' j'))) (hd m n))
    linarith
  have hbndNeg (i j : Fin 3) : |-b i j - d i j| ≤ 5 * T * δ := by
    have h := (abs_sub (-b i j) (d i j)).trans (add_le_add (by simpa using hb i j) (hd i j))
    linarith
  constructor
  · apply abs_threeProducts_bound (hbndNeg 0 0)
    · have hdiff : |1 - σratio| ≤ 2 * T * δ := by simpa only [abs_sub_comm] using hσ
      have hdiv := (abs_div_le_self_of_one_le (a := b 1 0 + b 0 1 + d 1 0) hS).trans
        (hbbd 1 0 0 1 1 0)
      have hc := (abs_sub (1 - σratio) ((b 1 0 + b 0 1 + d 1 0) / S)).trans
        (add_le_add hdiff hdiv)
      linarith
    · rw [abs_neg]
      linarith [hbbd 2 0 0 2 2 0]
  constructor
  · refine abs_threeProducts_bound ?_ (hbndNeg 1 1) ?_
    · rw [abs_neg]
      linarith [hdS 0 1]
    · have heps : |ε - 2 * S * b 2 1| ≤ δ := by simpa only [abs_sub_comm] using hε
      have hc := (abs_sub (ε - 2 * S * b 2 1) (S * d 2 1)).trans
        (add_le_add heps (hdS 2 1))
      linarith
  · refine abs_threeProducts_bound ?_ ?_ (hbndNeg 2 2)
    · rw [abs_neg]
      linarith [hd 0 2]
    · have h₀ := (abs_add_le (b 1 2 - b 2 1) (d 1 2)).trans
        (add_le_add ((abs_sub (b 1 2) (b 2 1)).trans (add_le_add (hb 1 2) (hb 2 1))) (hd 1 2))
      have h := (abs_div_le_self_of_one_le (a := -(b 1 2 - b 2 1 + d 1 2)) hS).trans
        (by simpa only [abs_neg] using h₀)
      linarith

/-- The preceding wave strength normalized by its value at activation. -/
def strengthRatio (kp ap : ℝ → Space) (t : ℝ) : ℝ :=
  (‖kp t‖ * ‖ap t‖) / (‖kp 0‖ * ‖ap 0‖)

/-- The strength variation supplies the coefficient estimate in Lemma 2.3. -/
theorem strengthRatio_bound {kp ap : ℝ → Space} {B : ℝ → Space →L[ℝ] Space}
    {T δ : ℝ} (hsmall : T * δ ≤ 1)
    (htrace : ∀ t ∈ Icc 0 T, LinearMap.trace ℝ Space (B t).toLinearMap = 0)
    (hp : ∀ t ∈ Icc 0 T, kp t ≠ 0 ∧ ap t ≠ 0 ∧ ⟪kp t, ap t⟫_ℝ = 0)
    (hkp : ∀ t ∈ Icc 0 T, HasDerivWithinAt kp (-((B t).adjoint (kp t))) (Icc 0 T) t)
    (hap : ∀ t ∈ Icc 0 T, HasDerivWithinAt ap
      (-(B t (ap t)) + (2 * ⟪kp t, B t (ap t)⟫_ℝ / ‖kp t‖ ^ 2) • kp t) (Icc 0 T) t)
    (hB : ∀ t ∈ Icc 0 T, ‖B t‖ ≤ δ) :
    ∀ t ∈ Icc 0 T, |strengthRatio kp ap t - 1| ≤ 2 * T * δ := by
  let F (t : ℝ) := Real.log (‖kp t‖ * ‖ap t‖) - Real.log (‖kp 0‖ * ‖ap 0‖)
  have hF (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt F (entry (frame kp ap t) (B t) 2 2) (Icc 0 T) t := by
    have h := (hasDerivWithinAt_movingFrame ht (B t) (htrace t ht)
      (hp t ht).1 (hp t ht).2.1 (hp t ht).2.2 (hkp t ht) (hap t ht)).2.2.2
    exact h.sub_const _
  intro t ht
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hF₀ : F 0 = 0 := sub_self _
  have hbound := abs_le_of_deriv_abs_le ht hF₀ hF (fun u hu =>
    (coefficient_abs_le_norm
      (orthonormal_movingFrame (hp u hu).1 (hp u hu).2.1 (hp u hu).2.2) (B u) 2 2).trans
      (hB u hu))
  have hId : Real.exp (F t) = strengthRatio kp ap t := by
    dsimp [F, strengthRatio]
    rw [Real.exp_sub, Real.exp_log (mul_pos (norm_pos_iff.mpr (hp t ht).1)
      (norm_pos_iff.mpr (hp t ht).2.1)), Real.exp_log (mul_pos
      (norm_pos_iff.mpr (hp 0 h0T).1) (norm_pos_iff.mpr (hp 0 h0T).2.1))]
  rw [← hId]
  exact (Real.abs_exp_sub_one_le (hbound.trans (by linarith))).trans (by linarith)

/-- The exact moving-coordinate system and normalized coefficient bounds imply
the wave-vector comparison of Lemma 2.3, with an explicit polynomial constant. -/
theorem moving_waveVector_polynomial_error {kp ap k : ℝ → Space}
    {B E : ℝ → Space →L[ℝ] Space} {ε T δ scale S : ℝ}
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (hT : 2 ≤ T) (hδ : 0 ≤ δ)
    (hscale : scale ≠ 0) (hS : 1 ≤ S) (hsmall : 240 * δ * T ^ 6 ≤ 1)
    (htrace : ∀ t ∈ Icc 0 T, LinearMap.trace ℝ Space (B t).toLinearMap = 0)
    (hp : ∀ t ∈ Icc 0 T, kp t ≠ 0 ∧ ap t ≠ 0 ∧ ⟪kp t, ap t⟫_ℝ = 0)
    (hkp : ∀ t ∈ Icc 0 T, HasDerivWithinAt kp (-((B t).adjoint (kp t))) (Icc 0 T) t)
    (hap : ∀ t ∈ Icc 0 T, HasDerivWithinAt ap
      (-(B t (ap t)) + (2 * ⟪kp t, B t (ap t)⟫_ℝ / ‖kp t‖ ^ 2) • kp t) (Icc 0 T) t)
    (hk : ∀ t ∈ Icc 0 T, HasDerivWithinAt k
      (-((strain (frame kp ap t) (B t) (E t) S (strengthRatio kp ap t)).adjoint (k t))) (Icc 0 T) t)
    (hk₀ : k 0 = scale • frame kp ap 0 2)
    (hB : ∀ t ∈ Icc 0 T, ‖B t‖ ≤ δ)
    (hE : ∀ t ∈ Icc 0 T, ‖E t‖ ≤ δ / S)
    (hCoupling : ∀ t ∈ Icc 0 T,
      |2 * S * entry (frame kp ap t) (B t) 2 1 - ε| ≤ δ) :
    ∀ t ∈ Icc 0 T,
      let e := frame kp ap
      |X e k scale t - ReferenceRiccati.x ε t| + |Q e k scale S t + ε * t| +
        |Z e k scale t - 1| ≤ 120 * δ * T ^ 6 ∧ 120 * δ * T ^ 6 ≤ 1 / 2 := by
  let e := frame kp ap
  let x := X e k scale
  let q := Q e k scale S
  let z := Z e k scale
  let b (t : ℝ) := entry (e t) (B t)
  let d (t : ℝ) := entry (e t) (E t)
  let rX (t : ℝ) := residualX (b t) (d t) S (strengthRatio kp ap t) (x t) (q t) (z t)
  let rQ (t : ℝ) := residualQ (b t) (d t) ε S (x t) (q t) (z t)
  let rZ (t : ℝ) := residualZ (b t) (d t) S (x t) (q t) (z t)
  have hT₀ : 0 ≤ T := by linarith
  have hT₁ : 1 ≤ T := by linarith
  have hS₀ : 0 < S := zero_lt_one.trans_le hS
  have hTδ : T * δ ≤ 1 := by
    have hp : T ^ 1 ≤ T ^ 6 := pow_le_pow_right₀ hT₁ (by decide)
    rw [pow_one] at hp
    nlinarith [mul_le_mul_of_nonneg_right hp hδ]
  have hσ := strengthRatio_bound hTδ htrace hp hkp hap hB
  have he (t : ℝ) (ht : t ∈ Icc 0 T) : Orthonormal ℝ (e t) :=
    orthonormal_movingFrame (hp t ht).1 (hp t ht).2.1 (hp t ht).2.2
  obtain ⟨hx₀, hq₀, hz₀⟩ := coordinate_initial_values (he 0 ⟨le_rfl, hT₀⟩) hscale hk₀
  have hDerivative (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt x (-q t + rX t) (Icc 0 T) t ∧
      HasDerivWithinAt q (-ε * z t + rQ t) (Icc 0 T) t ∧
      HasDerivWithinAt z (rZ t) (Icc 0 T) t := by
    obtain ⟨h₁, h₂, h₃⟩ := moving_waveVector_derivatives ht hscale hS₀.ne'
      (htrace t ht) (hp t ht).1 (hp t ht).2.1 (hp t ht).2.2 (hkp t ht) (hap t ht) (hk t ht)
    refine ⟨h₁.congr_deriv ?_, h₂.congr_deriv ?_, h₃.congr_deriv ?_⟩ <;>
      dsimp [rX, rQ, rZ, residualX, residualQ, residualZ, b, d, x, q, z, e] <;> ring
  have hResidual (t : ℝ) (ht : t ∈ Icc 0 T) :
      let L := (5 * T * δ) * (|x t| + |q t| + |z t|)
      |rX t| ≤ L ∧ |rQ t| ≤ L ∧ |rZ t| ≤ L := by
    have hb₀ (i j : Fin 3) : |b t i j| ≤ δ :=
      (coefficient_abs_le_norm (he t ht) (B t) i j).trans (hB t ht)
    have hd₀ (i j : Fin 3) : |d t i j| ≤ δ / S :=
      (coefficient_abs_le_norm (he t ht) (E t) i j).trans (hE t ht)
    have hdS (i j : Fin 3) : |S * d t i j| ≤ δ := by
      rw [abs_mul, abs_of_nonneg hS₀.le]
      calc
        _ ≤ S * (δ / S) := mul_le_mul_of_nonneg_left (hd₀ i j) hS₀.le
        _ = δ := by field_simp
    exact residual_bounds hδ hT₁ hS hb₀
      (fun i j => (hd₀ i j).trans (div_le_self hδ hS)) hdS (hσ t ht) (hCoupling t ht)
  have hDsmall : 12 * (5 * T * δ) * T ^ 3 ≤ 1 := by
    have hp : T ^ 4 ≤ T ^ 6 := pow_le_pow_right₀ hT₁ (by decide)
    nlinarith [mul_le_mul_of_nonneg_left hp hδ]
  have hpoly := polynomial_waveVector_error hε₀ hε₁ hT (by positivity) hDsmall hx₀ hq₀ hz₀
    (fun t ht => (hDerivative t ht).1) (fun t ht => (hDerivative t ht).2.1)
    (fun t ht => (hDerivative t ht).2.2) hResidual
  intro t ht
  exact ⟨(hpoly t ht).trans_eq (by ring), by linarith⟩

/-- Rescaling the rank-one shear by the physical growth rate gives the exact
rank-one term used in the normalized strain. -/
theorem normalized_rankOne_strain {kp ap : ℝ → Space} {r t : ℝ} (hr : r ≠ 0)
    (hkp₀ : kp 0 ≠ 0) (hap₀ : ap 0 ≠ 0) (hkp : kp t ≠ 0) (hap : ap t ≠ 0) :
    (((‖kp 0‖ * ‖ap 0‖) / r) * strengthRatio kp ap t) •
      InnerProductSpace.rankOne ℝ (frame kp ap t 1) (frame kp ap t 0) =
        (1 / r) • InnerProductSpace.rankOne ℝ (ap t) (kp t) := by
  have hnp₀ := norm_ne_zero_iff.mpr hkp₀
  have hna₀ := norm_ne_zero_iff.mpr hap₀
  have hnp := norm_ne_zero_iff.mpr hkp
  have hna := norm_ne_zero_iff.mpr hap
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply, InnerProductSpace.rankOne_apply, frame, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.isValue, NormedSpace.normalize, real_inner_smul_left, smul_smul,
    strengthRatio]
  congr 1
  field_simp

/-- The normalization in time divides the full older-plus-wave-plus-error gradient by the rate. -/
theorem normalized_strain_eq {kp ap : ℝ → Space} {B E : Space →L[ℝ] Space}
    {r t : ℝ} (hr : r ≠ 0) (hkp₀ : kp 0 ≠ 0) (hap₀ : ap 0 ≠ 0)
    (hkp : kp t ≠ 0) (hap : ap t ≠ 0) :
    strain (frame kp ap t) ((1 / r) • B) ((1 / r) • E)
      ((‖kp 0‖ * ‖ap 0‖) / r) (strengthRatio kp ap t) =
      (1 / r) • (B + InnerProductSpace.rankOne ℝ (ap t) (kp t) + E) := by
  rw [strain, normalized_rankOne_strain hr hkp₀ hap₀ hkp hap, smul_add, smul_add]

/-- The affine change from physical time to time in units of the growth rate. -/
theorem hasDerivWithinAt_normalized_time {f : ℝ → Space} {df : Space} {J I : Set ℝ}
    {r t₀ τ : ℝ} (hmap : MapsTo (fun t => t₀ + t / r) J I)
    (hf : HasDerivWithinAt f df I (t₀ + τ / r)) :
    HasDerivWithinAt (fun t => f (t₀ + t / r)) ((1 / r) • df) J τ := by
  have hchange : HasDerivAt (fun t => t₀ + t / r) (1 / r) τ :=
    ((hasDerivAt_id τ).div_const r).const_add t₀
  exact hf.scomp τ hchange.hasDerivWithinAt hmap

/-- The componentwise estimate gives the Euclidean estimate used in Lemma 2.3. -/
theorem euclidean_error_le_sum (a b c : ℝ) :
    Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) ≤ |a| + |b| + |c| := by
  apply (Real.sqrt_le_left (by positivity)).mpr
  nlinarith [sq_abs a, sq_abs b, sq_abs c,
    mul_nonneg (abs_nonneg a) (abs_nonneg b),
    mul_nonneg (abs_nonneg a) (abs_nonneg c),
    mul_nonneg (abs_nonneg b) (abs_nonneg c)]

/-- The scaled wave vector stays in the region where the amplitude coordinates
and their pressure denominator are well defined. -/
theorem waveVector_coordinate_bounds {ε T t S X Q Z : ℝ}
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1 / 2) (hT : 2 ≤ T) (ht : t ∈ Icc 0 T)
    (herr : |X - ReferenceRiccati.x ε t| + |Q + ε * t| + |Z - 1| ≤ 1 / 2) :
    1 / 2 ≤ Z ∧ Z ≤ 3 / 2 ∧ |X| ≤ T ^ 2 ∧ |Q| ≤ T ∧
      1 / 4 ≤ X ^ 2 + Q ^ 2 / S ^ 2 + Z ^ 2 := by
  have hTsq : 1 ≤ T ^ 2 := by
    have h : 1 ≤ T := by linarith
    simpa using pow_le_pow_left₀ zero_le_one h 2
  have hXnonneg := abs_nonneg (X - ReferenceRiccati.x ε t)
  have hQnonneg := abs_nonneg (Q + ε * t)
  have hZnonneg := abs_nonneg (Z - 1)
  have hZ : |Z - 1| ≤ 1 / 2 := by linarith
  have hZlo : 1 / 2 ≤ Z := by linarith [(abs_le.mp hZ).1]
  refine ⟨hZlo, by linarith [(abs_le.mp hZ).2], ?_, ?_, ?_⟩
  · have hbound : ReferenceRiccati.x ε t ≤ T ^ 2 / 2 := by
      have h := pow_le_pow_left₀ ht.1 ht.2 2
      have heps := mul_le_mul_of_nonneg_right (show ε ≤ 1 by linarith) (sq_nonneg t)
      unfold ReferenceRiccati.x
      linarith
    have hX : |X - ReferenceRiccati.x ε t| ≤ 1 / 2 := by linarith
    have h := abs_add_le (X - ReferenceRiccati.x ε t) (ReferenceRiccati.x ε t)
    rw [sub_add_cancel, abs_of_nonneg (ReferenceRiccati.x_nonneg hε₀ t)] at h
    linarith
  · have heps : ε * t ≤ T / 2 := by
      have h := mul_le_mul_of_nonneg_right hε₁ ht.1
      linarith [ht.2]
    have hQ : |Q + ε * t| ≤ 1 / 2 := by linarith
    have h := abs_sub (Q + ε * t) (ε * t)
    rw [add_sub_cancel_right, abs_of_nonneg (mul_nonneg hε₀ ht.1)] at h
    linarith
  · have hZsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hZlo 2
    have hQsq : 0 ≤ Q ^ 2 / S ^ 2 := div_nonneg (sq_nonneg Q) (sq_nonneg S)
    nlinarith [sq_nonneg X]

end

end TorusEuler.MovingWaveVector
