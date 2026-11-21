import TorusEuler.MovingAmplitudeCoefficients
import TorusEuler.ReferenceComparison

/-! The perturbed transverse propagator of Lemma 2.5 on an arbitrary subinterval. -/

open Set MeasureTheory
open scoped InnerProductSpace

namespace TorusEuler.ReferenceComparison

open ReferenceRiccati ReferencePropagator

private theorem riccati_perturbation_norm_le_from {ε T a t : ℝ} {Y ρ : ℝ → ℝ}
    {R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)} {z : ℝ → ℝ × ℝ}
    (hε : 0 < ε) (hY₀ : Y 0 = 1)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (ha : a ∈ Icc 0 T) (ht : t ∈ Icc a T)
    (hR : ContinuousOn R (Icc a T)) (hρ : ContinuousOn ρ (Icc a T))
    (hRρ : ∀ r ∈ Icc a T, ‖R r‖ ≤ ρ r)
    (hz : ∀ r ∈ Icc a T, HasDerivWithinAt z
      (triangularGenerator (s ε) (deviation ε Y) r (z r) + R r (z r)) (Icc a T) r) :
    ‖z t‖ ≤ 2 * ‖z a‖ * Real.exp (2 * (∫ r in a..t, ρ r)) := by
  have hsub : Icc a T ⊆ Icc 0 T := Icc_subset_Icc_left ha.1
  have hs : Continuous (s ε) := continuous_iff_continuousAt.2
    (fun r => (hasDerivAt_s ε r).continuousAt)
  have he : ContinuousOn (deviation ε Y) (Icc a T) :=
    (HasDerivWithinAt.continuousOn (fun r hr => hasDerivWithinAt_deviation (hY r hr))).mono hsub
  have hzero (r : ℝ) (_ : r ∈ Icc a T) :
      HasDerivWithinAt (fun _ => (0 : ℝ × ℝ))
        (triangularGenerator (s ε) (deviation ε Y) r 0) (Icc a T) r := by
    simpa only [map_zero] using hasDerivWithinAt_const r (Icc a T) (0 : ℝ × ℝ)
  exact (triangular_perturbation_bounds hs.continuousOn he (fun r _ => (s_pos ε r).le)
    (fun r hr => (riccati_deviation_bounds hε hY₀ hY r (hsub hr)).1) hR hρ hRρ hz hzero ht).1

/-- Growth of any raw amplitude path in the normalized coordinates of (2.8).
The perturbation integral starts at the freely chosen initial time `a`. -/
theorem normalizedState_norm_le_of_raw_matrix_from {ε T a t : ℝ} {Y U V η : ℝ → ℝ}
    {R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (hε : 0 < ε) (hY₀ : Y 0 = 1)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (ha : a ∈ Icc 0 T) (ht : t ∈ Icc a T)
    (hR : ContinuousOn R (Icc a T)) (hη : ContinuousOn η (Icc a T))
    (hRη : ∀ r ∈ Icc a T, ‖R r‖ ≤ η r)
    (hU : ∀ r ∈ Icc 0 T, HasDerivWithinAt U
      (-damping ε r * U r + driving ε r * V r + (R r (U r, V r)).1) (Icc 0 T) r)
    (hV : ∀ r ∈ Icc 0 T, HasDerivWithinAt V (U r + (R r (U r, V r)).2) (Icc 0 T) r) :
    let z := normalizedState ε Y U V
    let D := ∫ r in a..t, ((1 + |Y r|) ^ 2 / s ε r) * η r
    ‖z t‖ ≤ 2 * ‖z a‖ * Real.exp (2 * D) := by
  have hsub : Icc a T ⊆ Icc 0 T := Icc_subset_Icc_left ha.1
  have hYC := (HasDerivWithinAt.continuousOn hY).mono hsub
  have hs : Continuous (s ε) := continuous_iff_continuousAt.2
    (fun r => (hasDerivAt_s ε r).continuousAt)
  let ρ (r : ℝ) := ((1 + |Y r|) ^ 2 / s ε r) * η r
  have hρ : ContinuousOn ρ (Icc a T) :=
    ((((continuousOn_const.add hYC.abs).pow 2).div hs.continuousOn
      (fun r _ => (s_pos ε r).ne')).mul hη)
  have hRρ (r : ℝ) (hr : r ∈ Icc a T) : ‖normalizedMatrixError ε Y R r‖ ≤ ρ r :=
    (norm_normalizedMatrixError_le ε Y R r).trans
      (mul_le_mul_of_nonneg_left (hRη r hr) (div_nonneg (sq_nonneg _) (s_pos ε r).le))
  exact riccati_perturbation_norm_le_from hε hY₀ hY ha ht
    (continuousOn_normalizedMatrixError hYC hR) hρ hRρ
    (fun r hr => (hasDerivWithinAt_normalized_perturbed hY (hsub hr)
      (hU r (hsub hr)) (hV r (hsub hr))).mono hsub)

/-- The normalized perturbed system has a fundamental solution and inverse with
initial time anywhere in the reference interval. Its forward operator bound uses
the maximum norm and the integrated size of the normalized perturbation. -/
theorem exists_normalizedPropagator_from {ε T a : ℝ} {Y ρ : ℝ → ℝ}
    {R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (hε : 0 < ε) (hY₀ : Y 0 = 1)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (ha : a ∈ Icc 0 T)
    (hR : ContinuousOn R (Icc a T)) (hρ : ContinuousOn ρ (Icc a T))
    (hRρ : ∀ r ∈ Icc a T, ‖R r‖ ≤ ρ r) :
    let A (r : ℝ) := triangularGenerator (s ε) (deviation ε Y) r + R r
    ∃ Φ Ψ : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ),
      Φ a = ContinuousLinearMap.id ℝ (ℝ × ℝ) ∧
      (∀ t ∈ Icc a T, HasDerivWithinAt Φ ((A t).comp (Φ t)) (Icc a T) t) ∧
      ∀ t ∈ Icc a T, (Ψ t).comp (Φ t) = ContinuousLinearMap.id ℝ (ℝ × ℝ) ∧
        (Φ t).comp (Ψ t) = ContinuousLinearMap.id ℝ (ℝ × ℝ) ∧
        ‖Φ t‖ ≤ 2 * Real.exp (2 * (∫ r in a..t, ρ r)) := by
  let E := ℝ × ℝ
  let A (r : ℝ) := triangularGenerator (s ε) (deviation ε Y) r + R r
  have hsub : Icc a T ⊆ Icc 0 T := Icc_subset_Icc_left ha.1
  have hs : Continuous (s ε) := continuous_iff_continuousAt.2
    (fun r => (hasDerivAt_s ε r).continuousAt)
  have he : ContinuousOn (deviation ε Y) (Icc a T) :=
    (HasDerivWithinAt.continuousOn (fun r hr => hasDerivWithinAt_deviation (hY r hr))).mono hsub
  have hA : ContinuousOn A (Icc a T) := (continuousOn_triangularGenerator hs.continuousOn he).add hR
  obtain ⟨Φ, hΦ₀, hΦ⟩ := linearODE_exists_Icc (E := E →L[ℝ] E)
    (A := fun r => ContinuousLinearMap.compL ℝ E E E (A r)) ha.2
    ((ContinuousLinearMap.compL ℝ E E E).continuous.comp_continuousOn hA)
    (ContinuousLinearMap.id ℝ E)
  obtain ⟨Ψ, hΨ₀, hΨ⟩ := linearODE_exists_Icc (E := E →L[ℝ] E)
    (A := fun r => -(ContinuousLinearMap.compL ℝ E E E).flip (A r)) ha.2
    (((ContinuousLinearMap.compL ℝ E E E).flip.continuous.comp_continuousOn hA).neg)
    (ContinuousLinearMap.id ℝ E)
  have hΦ' (r : ℝ) (hr : r ∈ Icc a T) :
      HasDerivWithinAt Φ ((A r).comp (Φ r)) (Icc a T) r := by
    simpa only [ContinuousLinearMap.compL_apply] using hΦ r hr
  have hΨ' (r : ℝ) (hr : r ∈ Icc a T) :
      HasDerivWithinAt Ψ (-((Ψ r).comp (A r))) (Icc a T) r := by
    simpa only [ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
      neg_apply] using hΨ r hr
  have ha' : a ∈ Icc a T := left_mem_Icc.2 ha.2
  refine ⟨Φ, Ψ, hΦ₀, hΦ', fun t ht => ⟨
    linearODE_inv_comp_fundamental ordConnected_Icc ha' hΦ' hΨ' hΦ₀ hΨ₀ t ht,
    linearODE_fundamental_comp_inv ordConnected_Icc ha' hA hΦ' hΨ' hΦ₀ hΨ₀ t ht, ?_⟩⟩
  apply (Φ t).opNorm_le_bound (by positivity)
  intro v
  have hPath (r : ℝ) (hr : r ∈ Icc a T) : HasDerivWithinAt (fun u => Φ u v)
      (triangularGenerator (s ε) (deviation ε Y) r (Φ r v) + R r (Φ r v)) (Icc a T) r := by
    simpa [A] using (hΦ' r hr).clm_apply (hasDerivWithinAt_const r (Icc a T) v)
  have hBound := riccati_perturbation_norm_le_from hε hY₀ hY ha ht hR hρ hRρ hPath
  rw [hΦ₀, ContinuousLinearMap.id_apply] at hBound
  convert hBound using 1
  ring

/-- The comparison between the Euclidean amplitude and the maximum norm on the
normalized transverse coordinates, under the coordinate bounds of Lemma 2.3. -/
theorem norm_normalizedAmplitude_bounds {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (e : OrthonormalBasis (Fin 3) ℝ E)
    (v : E) {ε t S X Q Z Y h l : ℝ} (hS : 1 ≤ S)
    (hX : |X| ≤ S) (hQ : |Q| ≤ S) (hZ₀ : 1 / 2 ≤ Z) (hZ₁ : Z ≤ 3 / 2)
    (hY : |Y| ≤ 1) (hx : |X - x ε t| ≤ 1 / 2)
    (h₀ : e.repr v 0 = -(Y * h + s ε t * l) / S)
    (h₁ : e.repr v 1 = h)
    (h₂ : e.repr v 2 = (X * (Y * h + s ε t * l) - Q * h) / (S * Z)) :
    ‖v‖ ≤ 9 * ‖(h, l)‖ ∧ ‖(h, l)‖ ≤ 7 * S * ‖v‖ := by
  have hS₀ : 0 < S := by linarith
  have hZ : 0 < Z := by linarith
  let u := Y * h + s ε t * l
  let N := ‖(h, l)‖
  have hN : 0 ≤ N := norm_nonneg _
  have hhN : |h| ≤ N := by rw [← Real.norm_eq_abs]; exact norm_fst_le (h, l)
  have hlN : |l| ≤ N := by rw [← Real.norm_eq_abs]; exact norm_snd_le (h, l)
  have huN : |u| ≤ 2 * N := by
    calc
      |u| ≤ |Y| * |h| + s ε t * |l| := by
        simpa [u, abs_mul, abs_of_pos (s_pos ε t)] using abs_add_le (Y * h) (s ε t * l)
      _ ≤ 1 * N + 1 * N := add_le_add
        (mul_le_mul hY hhN (abs_nonneg _) zero_le_one)
        (mul_le_mul (s_le_one ε t) hlN (abs_nonneg _) zero_le_one)
      _ = 2 * N := by ring
  have hupper₀ : |e.repr v 0| ≤ 2 * N := by
    rw [h₀, abs_div, abs_neg, abs_of_pos hS₀]
    exact ((div_le_iff₀ hS₀).2 (by
      exact huN.trans (le_mul_of_one_le_right (by positivity) hS)))
  have hupper₂ : |e.repr v 2| ≤ 6 * N := by
    rw [h₂, abs_div, abs_of_pos (mul_pos hS₀ hZ)]
    apply (div_le_iff₀ (mul_pos hS₀ hZ)).2
    calc
      |X * u - Q * h| ≤ |X| * |u| + |Q| * |h| := by
        simpa [abs_mul, sub_eq_add_neg] using abs_add_le (X * u) (-(Q * h))
      _ ≤ S * (2 * N) + S * N := add_le_add
        (mul_le_mul hX huN (abs_nonneg _) hS₀.le)
        (mul_le_mul hQ hhN (abs_nonneg _) hS₀.le)
      _ = (6 * N * S) * (1 / 2) := by ring
      _ ≤ (6 * N * S) * Z := mul_le_mul_of_nonneg_left hZ₀ (by positivity)
      _ = 6 * N * (S * Z) := by ring
  constructor
  · have hv : v = e.repr v 0 • e 0 + e.repr v 1 • e 1 + e.repr v 2 • e 2 := by
      simpa only [Fin.sum_univ_three] using (e.sum_repr v).symm
    calc
      ‖v‖ ≤ |e.repr v 0| + |e.repr v 1| + |e.repr v 2| := by
        nth_rw 1 [hv]
        let u₀ : E := e.repr v 0 • e 0
        let u₁ : E := e.repr v 1 • e 1
        let u₂ : E := e.repr v 2 • e 2
        have hsum := (norm_add_le (u₀ + u₁) u₂).trans (add_le_add (norm_add_le u₀ u₁) le_rfl)
        simpa only [u₀, u₁, u₂, norm_smul, Real.norm_eq_abs, e.orthonormal.norm_eq_one,
          mul_one] using hsum
      _ ≤ 2 * N + N + 6 * N := add_le_add (add_le_add hupper₀ (by simpa only [h₁] using hhN)) hupper₂
      _ = 9 * N := by ring
  · have hpair (i : Fin 3) : |e.repr v i| ≤ ‖v‖ := by
      rw [OrthonormalBasis.repr_apply_apply]
      simpa only [e.orthonormal.norm_eq_one, one_mul] using abs_real_inner_le_norm (e i) v
    have hh : |h| ≤ ‖v‖ := by simpa only [h₁] using hpair 1
    have hu : |u| ≤ S * ‖v‖ := by
      have hp := hpair 0
      rw [h₀, abs_div, abs_neg, abs_of_pos hS₀, div_le_iff₀ hS₀, mul_comm ‖v‖ S] at hp
      exact hp
    have hXu : |X| * |u| ≤ (5 / 2) * S * ‖v‖ := by
      have hp := hpair 2
      rw [h₂, abs_div, abs_of_pos (mul_pos hS₀ hZ), div_le_iff₀ (mul_pos hS₀ hZ)] at hp
      calc
        |X| * |u| = |(X * u - Q * h) + Q * h| := by rw [sub_add_cancel, abs_mul]
        _ ≤ |X * u - Q * h| + |Q| * |h| := by
          simpa only [abs_mul] using abs_add_le (X * u - Q * h) (Q * h)
        _ ≤ ‖v‖ * (S * Z) + S * ‖v‖ :=
          add_le_add hp (mul_le_mul hQ hh (abs_nonneg _) hS₀.le)
        _ = (Z + 1) * (S * ‖v‖) := by ring
        _ ≤ (5 / 2) * (S * ‖v‖) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by ring
    have hsinv : (s ε t)⁻¹ ≤ 3 / 2 + |X| := by
      rw [s, inv_inv]
      calc
        Real.sqrt (1 + x ε t ^ 2) ≤ 1 + |x ε t| := by
          exact Real.sqrt_le_iff.2 ⟨by positivity,
            by nlinarith [sq_abs (x ε t), abs_nonneg (x ε t)]⟩
        _ ≤ 3 / 2 + |X| := by
          have hdiff : |x ε t| ≤ |X - x ε t| + |X| := by
            calc
              |x ε t| = |-(X - x ε t) + X| := by ring_nf
              _ ≤ |X - x ε t| + |X| := by simpa only [abs_neg] using abs_add_le (-(X - x ε t)) X
          linarith
    have hls : |l| ≤ 7 * S * ‖v‖ := by
      have hle : s ε t * |l| ≤ |u| + |h| := calc
        s ε t * |l| = |u - Y * h| := by rw [show u - Y * h = s ε t * l by dsimp [u]; ring,
          abs_mul, abs_of_pos (s_pos ε t)]
        _ ≤ |u| + |Y| * |h| := by
          simpa [abs_mul, sub_eq_add_neg] using abs_add_le u (-(Y * h))
        _ ≤ |u| + |h| := add_le_add le_rfl (mul_le_of_le_one_left (abs_nonneg _) hY)
      calc
        |l| ≤ (s ε t)⁻¹ * (|u| + |h|) := by
          rw [← div_eq_inv_mul, le_div_iff₀ (s_pos ε t), mul_comm]
          exact hle
        _ ≤ (3 / 2 + |X|) * (|u| + |h|) :=
          mul_le_mul_of_nonneg_right hsinv (by positivity)
        _ = (3 / 2) * |u| + |X| * |u| + (3 / 2 + |X|) * |h| := by ring
        _ ≤ (3 / 2) * (S * ‖v‖) + (5 / 2) * S * ‖v‖ + (3 / 2 + S) * ‖v‖ :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left hu (by norm_num)) hXu)
            (mul_le_mul (add_le_add le_rfl hX) hh (abs_nonneg _) (by positivity))
        _ ≤ 7 * S * ‖v‖ := by
          have hSn : ‖v‖ ≤ S * ‖v‖ := le_mul_of_one_le_left (norm_nonneg _) hS
          nlinarith [norm_nonneg v]
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff]
    exact ⟨hh.trans (le_mul_of_one_le_left (norm_nonneg _) (by linarith)), hls⟩

open MovingWaveVector (Space X Q Z)
open MovingAmplitude (U V amplitude_pairings)

/-- The norm comparison applies to the actual moving-frame amplitude of (2.3). -/
theorem norm_movingAmplitude_bounds {e : ℝ → Fin 3 → Space} {k b : ℝ → Space}
    {Y : ℝ → ℝ} {ε scale S t : ℝ} (he : Orthonormal ℝ (e t))
    (hscale : scale ≠ 0) (hS : 1 ≤ S) (hperp : ⟪k t, b t⟫_ℝ = 0)
    (hX : |X e k scale t| ≤ S) (hQ : |Q e k scale S t| ≤ S)
    (hZ₀ : 1 / 2 ≤ Z e k scale t) (hZ₁ : Z e k scale t ≤ 3 / 2)
    (hY : |Y t| ≤ 1) (hx : |X e k scale t - x ε t| ≤ 1 / 2) :
    let z := normalizedState ε Y (U e b S) (V e b)
    ‖b t‖ ≤ 9 * growingFactor Y t * ‖z t‖ ∧
      ‖z t‖ ≤ 7 * S * (‖b t‖ / growingFactor Y t) := by
  have hS₀ : S ≠ 0 := by linarith
  have hZ : Z e k scale t ≠ 0 := by linarith
  obtain ⟨h₀, h₁, h₂⟩ := amplitude_pairings he hscale hS₀ hZ hperp
  let B : OrthonormalBasis (Fin 3) ℝ Space :=
    OrthonormalBasis.mk he (he.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge
  let G := growingFactor Y t
  let h := normalizedH Y (V e b) t
  let l := normalizedL ε Y (U e b S) (V e b) t
  let w := G⁻¹ • b t
  have hG : 0 < G := growingFactor_pos Y t
  have hs := (s_pos ε t).ne'
  have hcoord (i : Fin 3) : B.repr w i = G⁻¹ * ⟪e t i, b t⟫_ℝ := by
    simp only [B, w, OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_mk,
      real_inner_smul_right]
  have hu : Y t * h + s ε t * l = U e b S t / G := by
    dsimp [h, l, normalizedH, normalizedL, G]
    field_simp [hG.ne', hs]
    ring
  have hB₀ : B.repr w 0 = -(Y t * h + s ε t * l) / S := by
    rw [hcoord, h₀, hu]
    ring
  have hB₁ : B.repr w 1 = h := by rw [hcoord, h₁]; exact (div_eq_inv_mul _ _).symm
  have hB₂ : B.repr w 2 =
      (X e k scale t * (Y t * h + s ε t * l) - Q e k scale S t * h) / (S * Z e k scale t) := by
    rw [hcoord, h₂, hu]
    dsimp [h, normalizedH, G]
    ring
  have hw : ‖w‖ = ‖b t‖ / G := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hG), div_eq_inv_mul]
  obtain ⟨hUpper, hLower⟩ :=
    norm_normalizedAmplitude_bounds B w hS hX hQ hZ₀ hZ₁ hY hx hB₀ hB₁ hB₂
  rw [hw] at hUpper hLower
  refine ⟨((div_le_iff₀ hG).mp hUpper).trans_eq ?_, hLower⟩
  change 9 * ‖(h, l)‖ * G = 9 * G * ‖(h, l)‖
  ring

/-- The arbitrary-start physical amplitude estimate of Lemma 2.5 with the
integrated matrix error retained in the exponent. -/
theorem norm_movingAmplitude_le_from {e : ℝ → Fin 3 → Space} {k b : ℝ → Space}
    {ε T a t scale S : ℝ} {Y η : ℝ → ℝ} {R : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (hε : 0 < ε) (hY₀ : Y 0 = 1)
    (hY : ∀ r ∈ Icc 0 T, HasDerivWithinAt Y (rhs ε r (Y r)) (Icc 0 T) r)
    (ha : a ∈ Icc 0 T) (ht : t ∈ Icc a T)
    (hscale : scale ≠ 0) (hS : 1 ≤ S)
    (hGeom : ∀ r ∈ Icc a t, Orthonormal ℝ (e r) ∧ ⟪k r, b r⟫_ℝ = 0 ∧
      |X e k scale r| ≤ S ∧ |Q e k scale S r| ≤ S ∧
      1 / 2 ≤ Z e k scale r ∧ Z e k scale r ≤ 3 / 2 ∧
      |Y r| ≤ 1 ∧ |X e k scale r - x ε r| ≤ 1 / 2)
    (hR : ContinuousOn R (Icc a T)) (hη : ContinuousOn η (Icc a T))
    (hRη : ∀ r ∈ Icc a T, ‖R r‖ ≤ η r)
    (hU : ∀ r ∈ Icc 0 T, HasDerivWithinAt (U e b S)
      (-damping ε r * U e b S r + driving ε r * V e b r + (R r (U e b S r, V e b r)).1)
      (Icc 0 T) r)
    (hV : ∀ r ∈ Icc 0 T, HasDerivWithinAt (V e b)
      (U e b S r + (R r (U e b S r, V e b r)).2) (Icc 0 T) r) :
    let D := ∫ r in a..t, ((1 + |Y r|) ^ 2 / s ε r) * η r
    ‖b t‖ ≤ 126 * S * Real.exp (2 * D) * (growingFactor Y t / growingFactor Y a) * ‖b a‖ := by
  let z := normalizedState ε Y (U e b S) (V e b)
  let D := ∫ r in a..t, ((1 + |Y r|) ^ 2 / s ε r) * η r
  have hB (r : ℝ) (hr : r ∈ Icc a t) :
      ‖b r‖ ≤ 9 * growingFactor Y r * ‖z r‖ ∧
      ‖z r‖ ≤ 7 * S * (‖b r‖ / growingFactor Y r) := by
    obtain ⟨hOrth, hperp, hX, hQ, hZ₀, hZ₁, hYabs, hx⟩ := hGeom r hr
    exact norm_movingAmplitude_bounds hOrth hscale hS hperp hX hQ hZ₀ hZ₁ hYabs hx
  have hStart := (hB a (left_mem_Icc.2 ht.1)).2
  have hEnd := (hB t (right_mem_Icc.2 ht.1)).1
  have hGrowth : ‖z t‖ ≤ 2 * ‖z a‖ * Real.exp (2 * D) :=
    normalizedState_norm_le_of_raw_matrix_from hε hY₀ hY ha ht hR hη hRη hU hV
  have hGa := growingFactor_pos Y a
  have hGt := growingFactor_pos Y t
  calc
    ‖b t‖ ≤ 9 * growingFactor Y t * ‖z t‖ := hEnd
    _ ≤ 9 * growingFactor Y t * (2 * ‖z a‖ * Real.exp (2 * D)) :=
      mul_le_mul_of_nonneg_left hGrowth (by positivity)
    _ ≤ 9 * growingFactor Y t * (2 * (7 * S * (‖b a‖ / growingFactor Y a)) * Real.exp (2 * D)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hStart (by norm_num)) (by positivity))
        (by positivity)
    _ = _ := by ring

end TorusEuler.ReferenceComparison
