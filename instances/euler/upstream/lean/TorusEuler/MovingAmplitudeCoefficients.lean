import TorusEuler.MovingCoordinateWaveVector
import TorusEuler.ReferenceAmplitude
import Mathlib.Analysis.Normed.Operator.Prod

/-! The amplitude equation in the scaled coordinates of (2.3). -/

open Set
open scoped InnerProductSpace

namespace TorusEuler.MovingAmplitude

open MovingWaveVector

noncomputable section

abbrev Entries := Fin 3 → Fin 3 → ℝ

def U (e : ℝ → Fin 3 → Space) (a : ℝ → Space) (S t : ℝ) : ℝ :=
  -S * ⟪e t 0, a t⟫_ℝ

def V (e : ℝ → Fin 3 → Space) (a : ℝ → Space) (t : ℝ) : ℝ := ⟪e t 1, a t⟫_ℝ

/-- The growing polarization of Lemma 2.5 has both raw components equal to one. -/
theorem growing_components {e : ℝ → Fin 3 → Space} {a : ℝ → Space} {S t : ℝ}
    (he : Orthonormal ℝ (e t)) (hS : S ≠ 0)
    (ha : a t = (-S⁻¹) • e t 0 + e t 1) :
    U e a S t = 1 ∧ V e a t = 1 := by
  have hinner := orthonormal_iff_ite.mp he
  simp [U, V, ha, inner_add_right, real_inner_smul_right, hinner, he.norm_eq_one, hS]

def normFactor (X Q Z S : ℝ) : ℝ := X ^ 2 + Q ^ 2 / S ^ 2 + Z ^ 2

def pressureU (A : Entries) (X Q Z S : ℝ) : ℝ :=
  X * (-A 0 0 + A 0 2 * X / Z) +
    Q * (-A 1 0 / S + (A 1 2 / S) * X / Z) +
    Z * (-A 2 0 + A 2 2 * X / Z)

def pressureV (A : Entries) (X Q Z S : ℝ) : ℝ :=
  X * (S * A 0 1 - A 0 2 * Q / Z) +
    Q * (A 1 1 - (A 1 2 / S) * Q / Z) +
    Z * (S * A 2 1 - A 2 2 * Q / Z)

/-- The two amplitude rows. The entries of the full normalized strain are
A, and the frame derivatives use only b, the entries of the older gradient. -/
def rawMatrix (b A : Entries) (X Q Z S : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let m := normFactor X Q Z S
  let fu := pressureU A X Q Z S
  let fv := pressureV A X Q Z S
  !![-A 0 0 + (A 0 2 + b 0 2) * X / Z - 2 * X * fu / m,
     S * (A 0 1 + b 0 1) - (A 0 2 + b 0 2) * Q / Z - 2 * X * fv / m;
     (A 1 0 - b 0 1) / S - (A 1 2 + b 2 1) * X / (S * Z) + 2 * Q * fu / (S ^ 2 * m),
     -A 1 1 + (A 1 2 + b 2 1) * Q / (S * Z) + 2 * Q * fv / (S ^ 2 * m)]

def pairOperator (N : Matrix (Fin 2) (Fin 2) ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (N 0 0 • ContinuousLinearMap.fst ℝ ℝ ℝ + N 0 1 • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (N 1 0 • ContinuousLinearMap.fst ℝ ℝ ℝ + N 1 1 • ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem pairOperator_apply (N : Matrix (Fin 2) (Fin 2) ℝ) (u v : ℝ) :
    pairOperator N (u, v) = (N 0 0 * u + N 0 1 * v, N 1 0 * u + N 1 1 * v) := by
  simp [pairOperator]

/-- A uniform entry bound controls the operator norm in the reference comparison. -/
theorem norm_pairOperator_le {N : Matrix (Fin 2) (Fin 2) ℝ} {d : ℝ} (hd : 0 ≤ d)
    (hN : ∀ i j, |N i j| ≤ d) : ‖pairOperator N‖ ≤ 2 * d := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  rintro ⟨u, v⟩
  have hrow (i : Fin 2) : ‖N i 0 * u + N i 1 * v‖ ≤ (2 * d) * ‖(u, v)‖ := by
    calc
      ‖N i 0 * u + N i 1 * v‖ ≤ |N i 0| * ‖u‖ + |N i 1| * ‖v‖ := by
        simpa only [norm_mul, Real.norm_eq_abs] using norm_add_le (N i 0 * u) (N i 1 * v)
      _ ≤ d * ‖(u, v)‖ + d * ‖(u, v)‖ :=
        add_le_add
          (mul_le_mul (hN i 0) (norm_fst_le (u, v)) (norm_nonneg _) hd)
          (mul_le_mul (hN i 1) (norm_snd_le (u, v)) (norm_nonneg _) hd)
      _ = _ := by ring
  rw [pairOperator_apply, Prod.norm_def, max_le_iff]
  exact ⟨hrow 0, hrow 1⟩

private theorem continuousOn_pairOperator {J : Set ℝ} {N : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hN : ∀ i j, ContinuousOn (fun t => N t i j) J) :
    ContinuousOn (fun t => pairOperator (N t)) J := by
  have hrow (i : Fin 2) : ContinuousOn (fun t =>
      N t i 0 • ContinuousLinearMap.fst ℝ ℝ ℝ +
      N t i 1 • ContinuousLinearMap.snd ℝ ℝ ℝ) J :=
    ((hN i 0).smul continuousOn_const).add ((hN i 1).smul continuousOn_const)
  exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp_continuousOn
    ((hrow 0).prodMk (hrow 1))

def referenceMatrix (ε τ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-ReferenceRiccati.damping ε τ, ReferenceRiccati.driving ε τ; 1, 0]

/-- The raw error operator, in the same pair norm as the reference comparison. -/
def errorOperator (ε τ : ℝ) (b A : Entries) (X Q Z S : ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  pairOperator (rawMatrix b A X Q Z S - referenceMatrix ε τ)

private theorem normFactor_pos {X Q Z S : ℝ} (hZ : Z ≠ 0) : 0 < normFactor X Q Z S := by
  unfold normFactor
  have := sq_pos_of_ne_zero hZ
  positivity

/-- The coefficient error is continuous on each interval where the moving coordinates
are defined. Its entries depend on the strain and wave vector alone. -/
theorem continuousOn_errorOperator {ε S : ℝ} {J : Set ℝ} {b A : ℝ → Entries}
    {x q z : ℝ → ℝ} (hS : S ≠ 0) (hz₀ : ∀ t ∈ J, z t ≠ 0)
    (hb : ∀ i j, ContinuousOn (fun t => b t i j) J)
    (hA : ∀ i j, ContinuousOn (fun t => A t i j) J)
    (hx : ContinuousOn x J) (hq : ContinuousOn q J) (hz : ContinuousOn z J) :
    ContinuousOn (fun t => errorOperator ε t (b t) (A t) (x t) (q t) (z t) S) J := by
  have hm : ContinuousOn (fun t => normFactor (x t) (q t) (z t) S) J := by
    unfold normFactor
    fun_prop (disch := positivity)
  have hm₀ (t : ℝ) (ht : t ∈ J) : normFactor (x t) (q t) (z t) S ≠ 0 :=
    (normFactor_pos (hz₀ t ht)).ne'
  have hSz (t : ℝ) (ht : t ∈ J) : S * z t ≠ 0 := mul_ne_zero hS (hz₀ t ht)
  have hSm (t : ℝ) (ht : t ∈ J) : S ^ 2 * normFactor (x t) (q t) (z t) S ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hS) (hm₀ t ht)
  have hfu : ContinuousOn (fun t => pressureU (A t) (x t) (q t) (z t) S) J := by
    unfold pressureU
    fun_prop (disch := first | solve_by_elim | positivity)
  have hfv : ContinuousOn (fun t => pressureV (A t) (x t) (q t) (z t) S) J := by
    unfold pressureV
    fun_prop (disch := first | solve_by_elim | positivity)
  have hs : Continuous (ReferenceRiccati.s ε) := continuous_iff_continuousAt.mpr
    (fun t => (ReferenceRiccati.hasDerivAt_s ε t).continuousAt)
  have hxr : Continuous (ReferenceRiccati.x ε) := by
    unfold ReferenceRiccati.x
    fun_prop
  have hd : ContinuousOn (ReferenceRiccati.damping ε) J :=
    (((continuous_const.mul continuous_id).mul hxr).mul (hs.pow 2)).continuousOn
  have hf : ContinuousOn (ReferenceRiccati.driving ε) J :=
    ((hs.pow 2).mul (continuous_const.sub (continuous_const.mul hxr))).continuousOn
  apply continuousOn_pairOperator
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sub_apply, rawMatrix, referenceMatrix, Matrix.of_apply, Fin.zero_eta,
      Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    fun_prop (disch := solve_by_elim)

private def frameBasis {E : Fin 3 → Space} (hE : Orthonormal ℝ E) :
    OrthonormalBasis (Fin 3) ℝ Space :=
  OrthonormalBasis.mk hE (hE.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge

private theorem frameExpansion {E : Fin 3 → Space} (hE : Orthonormal ℝ E) (v : Space) :
    v = ⟪E 0, v⟫_ℝ • E 0 + ⟪E 1, v⟫_ℝ • E 1 + ⟪E 2, v⟫_ℝ • E 2 := by
  simpa only [frameBasis, OrthonormalBasis.coe_mk, Fin.sum_univ_three] using
    ((frameBasis hE).sum_repr' v).symm

private theorem wavePairings {e : ℝ → Fin 3 → Space} {k : ℝ → Space}
    {scale S t : ℝ} (hscale : scale ≠ 0) (hS : S ≠ 0) :
    ⟪e t 0, k t⟫_ℝ = scale * X e k scale t ∧
      ⟪e t 1, k t⟫_ℝ = scale * (Q e k scale S t / S) ∧
      ⟪e t 2, k t⟫_ℝ = scale * Z e k scale t := by
  unfold X Q Z
  constructor
  · field_simp
  constructor <;> field_simp

/-- The denominator of the pressure coefficient is the normalized wave-vector norm. -/
theorem wave_norm_sq_eq {e : ℝ → Fin 3 → Space} {k : ℝ → Space} {scale S t : ℝ}
    (he : Orthonormal ℝ (e t)) (hscale : scale ≠ 0) (hS : S ≠ 0) :
    ‖k t‖ ^ 2 = scale ^ 2 * normFactor (X e k scale t) (Q e k scale S t) (Z e k scale t) S := by
  let basis := frameBasis he
  have hpair (i : Fin 3) : basis.repr (k t) i = ⟪e t i, k t⟫_ℝ := by
    simp only [OrthonormalBasis.repr_apply_apply, basis, frameBasis, OrthonormalBasis.coe_mk]
  obtain ⟨h₁, h₂, h₃⟩ := wavePairings (e := e) (k := k) (t := t) hscale hS
  rw [← basis.repr.norm_map (k t), EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
    hpair 0, hpair 1, hpair 2, h₁, h₂, h₃, normFactor]
  ring

/-- Transversality determines the third moving component of the amplitude. -/
theorem amplitude_pairings {e : ℝ → Fin 3 → Space} {k a : ℝ → Space} {scale S t : ℝ}
    (he : Orthonormal ℝ (e t)) (hscale : scale ≠ 0) (hS : S ≠ 0)
    (hZ : Z e k scale t ≠ 0) (hperp : ⟪k t, a t⟫_ℝ = 0) :
    ⟪e t 0, a t⟫_ℝ = -(U e a S t) / S ∧
    ⟪e t 1, a t⟫_ℝ = V e a t ∧
    ⟪e t 2, a t⟫_ℝ =
      (X e k scale t * U e a S t - Q e k scale S t * V e a t) / (S * Z e k scale t) := by
  have h₀ : ⟪e t 0, a t⟫_ℝ = -(U e a S t) / S := by
    unfold U
    field_simp
  have h₁ : ⟪e t 1, a t⟫_ℝ = V e a t := rfl
  refine ⟨h₀, h₁, ?_⟩
  rw [scaled_waveVector_decomposition (k := k) he hscale hS] at hperp
  simp only [real_inner_smul_left, inner_add_left, h₀, h₁] at hperp
  have h := (mul_eq_zero.mp hperp).resolve_left hscale
  apply (eq_div_iff (mul_ne_zero hS hZ)).mpr
  field_simp at h
  linear_combination h

theorem amplitude_decomposition {e : ℝ → Fin 3 → Space} {k a : ℝ → Space} {scale S t : ℝ}
    (he : Orthonormal ℝ (e t)) (hscale : scale ≠ 0) (hS : S ≠ 0)
    (hZ : Z e k scale t ≠ 0) (hperp : ⟪k t, a t⟫_ℝ = 0) :
    a t = (-(U e a S t) / S) • e t 0 + (V e a t) • e t 1 +
      ((X e k scale t * U e a S t - Q e k scale S t * V e a t) / (S * Z e k scale t)) • e t 2 := by
  obtain ⟨h₀, h₁, h₂⟩ := amplitude_pairings he hscale hS hZ hperp
  calc
    a t = ⟪e t 0, a t⟫_ℝ • e t 0 + ⟪e t 1, a t⟫_ℝ • e t 1 + ⟪e t 2, a t⟫_ℝ • e t 2 :=
      frameExpansion he _
    _ = _ := by rw [h₂, h₀, h₁]

private theorem strain_amplitude_pairing {e : ℝ → Fin 3 → Space} {k a : ℝ → Space}
    {scale S t : ℝ} (he : Orthonormal ℝ (e t)) (hscale : scale ≠ 0) (hS : S ≠ 0)
    (hZ : Z e k scale t ≠ 0) (hperp : ⟪k t, a t⟫_ℝ = 0) (M : Space →L[ℝ] Space) (i : Fin 3) :
    ⟪e t i, M (a t)⟫_ℝ =
      (-(U e a S t) / S) * entry (e t) M i 0 + V e a t * entry (e t) M i 1 +
      ((X e k scale t * U e a S t - Q e k scale S t * V e a t) / (S * Z e k scale t)) *
        entry (e t) M i 2 := by
  rw [amplitude_decomposition he hscale hS hZ hperp]
  simp only [entry, map_add, map_smul, inner_add_right, real_inner_smul_right]

private theorem pressure_pairing {e : ℝ → Fin 3 → Space} {k a : ℝ → Space}
    {scale S t : ℝ} (he : Orthonormal ℝ (e t)) (hscale : scale ≠ 0) (hS : S ≠ 0)
    (hZ : Z e k scale t ≠ 0) (hperp : ⟪k t, a t⟫_ℝ = 0) (M : Space →L[ℝ] Space) :
    let A := entry (e t) M
    let x := X e k scale t
    let q := Q e k scale S t
    let z := Z e k scale t
    ⟪k t, M (a t)⟫_ℝ =
      scale * (pressureU A x q z S * U e a S t + pressureV A x q z S * V e a t) / S := by
  dsimp only
  rw [scaled_waveVector_decomposition (k := k) he hscale hS]
  simp only [real_inner_smul_left, inner_add_left,
    strain_amplitude_pairing he hscale hS hZ hperp M]
  unfold pressureU pressureV
  field_simp
  ring

/-- Projecting the transverse amplitude equation onto the moving frame yields
the full two-row coefficient operator, including the continuous strain error. -/
theorem normalized_amplitude_derivatives {e : ℝ → Fin 3 → Space} {k a : ℝ → Space}
    {J : Set ℝ} {scale S t : ℝ} {B M : Space →L[ℝ] Space}
    (he : Orthonormal ℝ (e t)) (hscale : scale ≠ 0) (hS : S ≠ 0)
    (hZ : Z e k scale t ≠ 0) (hperp : ⟪k t, a t⟫_ℝ = 0)
    (he₁ : HasDerivWithinAt (fun u => e u 0)
      ((-entry (e t) B 0 1) • e t 1 - entry (e t) B 0 2 • e t 2) J t)
    (he₂ : HasDerivWithinAt (fun u => e u 1)
      (entry (e t) B 0 1 • e t 0 - entry (e t) B 2 1 • e t 2) J t)
    (ha : HasDerivWithinAt a
      (-(M (a t)) + (2 * ⟪k t, M (a t)⟫_ℝ / ‖k t‖ ^ 2) • k t) J t) :
    let N := rawMatrix (entry (e t) B) (entry (e t) M)
      (X e k scale t) (Q e k scale S t) (Z e k scale t) S
    let dUV := pairOperator N (U e a S t, V e a t)
    HasDerivWithinAt (U e a S) dUV.1 J t ∧ HasDerivWithinAt (V e a) dUV.2 J t := by
  obtain ⟨hk₀, hk₁, _⟩ := wavePairings (e := e) (k := k) (t := t) hscale hS
  obtain ⟨ha₀, ha₁, ha₂⟩ := amplitude_pairings he hscale hS hZ hperp
  have hm₀ : 0 < normFactor (X e k scale t) (Q e k scale S t) (Z e k scale t) S :=
    normFactor_pos hZ
  have hp := pressure_pairing he hscale hS hZ hperp M
  dsimp only at hp ⊢
  refine ⟨((he₁.inner ℝ ha).const_mul (-S)).congr_deriv ?_, (he₂.inner ℝ ha).congr_deriv ?_⟩ <;>
    simp only [inner_sub_left, real_inner_smul_left, inner_add_right,
      inner_neg_right, real_inner_smul_right, hk₀, hk₁, ha₀, ha₁, ha₂,
      strain_amplitude_pairing he hscale hS hZ hperp M, hp, wave_norm_sq_eq he hscale hS,
      pairOperator_apply, rawMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.isValue] <;>
    field_simp [hm₀.ne'] <;> ring

/-- The growing-model coefficient and the raw error add to the exact physical rows. -/
theorem normalized_amplitude_perturbed {e : ℝ → Fin 3 → Space} {k a : ℝ → Space}
    {J : Set ℝ} {ε scale S t : ℝ} {B M : Space →L[ℝ] Space}
    (he : Orthonormal ℝ (e t)) (hscale : scale ≠ 0) (hS : S ≠ 0)
    (hZ : Z e k scale t ≠ 0) (hperp : ⟪k t, a t⟫_ℝ = 0)
    (he₁ : HasDerivWithinAt (fun u => e u 0)
      ((-entry (e t) B 0 1) • e t 1 - entry (e t) B 0 2 • e t 2) J t)
    (he₂ : HasDerivWithinAt (fun u => e u 1)
      (entry (e t) B 0 1 • e t 0 - entry (e t) B 2 1 • e t 2) J t)
    (ha : HasDerivWithinAt a
      (-(M (a t)) + (2 * ⟪k t, M (a t)⟫_ℝ / ‖k t‖ ^ 2) • k t) J t) :
    let u := U e a S t
    let v := V e a t
    let R := errorOperator ε t (entry (e t) B) (entry (e t) M)
      (X e k scale t) (Q e k scale S t) (Z e k scale t) S
    HasDerivWithinAt (U e a S) (-ReferenceRiccati.damping ε t * u +
      ReferenceRiccati.driving ε t * v + (R (u, v)).1) J t ∧
    HasDerivWithinAt (V e a) (u + (R (u, v)).2) J t := by
  obtain ⟨hu, hv⟩ := normalized_amplitude_derivatives he hscale hS hZ hperp he₁ he₂ ha
  refine ⟨hu.congr_deriv ?_, hv.congr_deriv ?_⟩ <;>
    simp [errorOperator, referenceMatrix, pairOperator_apply] <;> ring

/-- Exact amplitude rows in the frame of the preceding wave. Time is the
normalized time from Lemma 2.3. The rates `B` and `E` are expressed in those
time units and `σratio` is the current shear divided by the initial shear. -/
theorem moving_amplitude_perturbed {kp ap k a : ℝ → Space} {J : Set ℝ}
    {ε scale S t σratio : ℝ} {B E : Space →L[ℝ] Space} (ht : t ∈ J)
    (hscale : scale ≠ 0) (hS : S ≠ 0)
    (htrace : LinearMap.trace ℝ Space B.toLinearMap = 0)
    (hkp₀ : kp t ≠ 0) (hap₀ : ap t ≠ 0) (hpp : ⟪kp t, ap t⟫_ℝ = 0)
    (hkp : HasDerivWithinAt kp (-(B.adjoint (kp t))) J t)
    (hap : HasDerivWithinAt ap
      (-(B (ap t)) + (2 * ⟪kp t, B (ap t)⟫_ℝ / ‖kp t‖ ^ 2) • kp t) J t)
    (hZ : Z (frame kp ap) k scale t ≠ 0) (hperp : ⟪k t, a t⟫_ℝ = 0)
    (ha : let M := strain (frame kp ap t) B E S σratio
      HasDerivWithinAt a (-(M (a t)) + (2 * ⟪k t, M (a t)⟫_ℝ / ‖k t‖ ^ 2) • k t) J t) :
    let e := frame kp ap
    let u := U e a S t
    let v := V e a t
    let R := errorOperator ε t (entry (e t) B) (entry (e t) (strain (e t) B E S σratio))
      (X e k scale t) (Q e k scale S t) (Z e k scale t) S
    HasDerivWithinAt (U e a S) (-ReferenceRiccati.damping ε t * u +
      ReferenceRiccati.driving ε t * v + (R (u, v)).1) J t ∧
    HasDerivWithinAt (V e a) (u + (R (u, v)).2) J t := by
  obtain ⟨he₁, he₂, _, _⟩ := hasDerivWithinAt_movingFrame ht B htrace hkp₀ hap₀ hpp hkp hap
  exact normalized_amplitude_perturbed
    (orthonormal_movingFrame hkp₀ hap₀ hpp) hscale hS hZ hperp he₁ he₂ ha

end

end TorusEuler.MovingAmplitude
