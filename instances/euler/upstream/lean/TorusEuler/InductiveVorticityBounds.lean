import TorusEuler.InductiveLimitAssembly
import TorusEuler.MovingAmplitudeCoefficients
import TorusEuler.TerminalVorticityTransfer
import Mathlib.Analysis.Calculus.MeanValue

/-! The central curl estimate of Proposition 8.2, (8.1)–(8.2). -/

open Filter Set
open scoped ContDiff InnerProductSpace Topology
open NormedSpace (normalize)

namespace TorusEuler

/-- The curl difference on the whole activation interval is controlled by
the remaining order-one correction increments in (7.4). This version
starts the summation at the current grade, even when the interval varies with it. -/
theorem norm_center_fderiv_sub_le_of_inductive_tail
    {j : ℕ} (hj : 1 ≤ j) {T : ℝ} {slab freq activation : ℕ → ℝ} {U O : ℕ → Velocity}
    {w : Velocity} {t : ℝ} (ht : t ∈ Icc (activation j) (activation (j + 1)))
    (hactivation : Monotone activation) (ha₀ : 0 ≤ activation j)
    (haT : activation (j + 1) < T) (hslab : ∀ n, T ≤ slab n)
    (hinit : 2 ≤ freq 0) (hfreq : ∀ n, freq n ^ 2 ≤ freq (n + 1))
    (hU : ∀ n s, s ∈ Icc 0 (slab n) → DifferentiableAt ℝ (U n s) 0)
    (hO : ∀ n ≥ 2, ∀ s ∈ Icc 0 (activation n), O n s = 0)
    (hB : ∀ n ≥ j, ∀ s ∈ Icc 0 (slab (n + 1)),
      ‖iteratedFDeriv ℝ 1 (U (n + 1) s - U n s - O (n + 1) s) 0‖ ≤ (freq (n + 1))⁻¹)
    (hprefix : ∀ S < T, TendstoUniformlyOn
      (fun n (z : ℝ × Vec3) => fderiv ℝ (U n z.1) z.2)
      (fun z : ℝ × Vec3 => fderiv ℝ (w z.1) z.2) atTop (Icc 0 S ×ˢ (univ : Set Vec3))) :
    ‖fderiv ℝ (w t) 0 - fderiv ℝ (U j t) 0‖ ≤ 2 * (freq (j + 1))⁻¹ := by
  let F (n : ℕ) := fderiv ℝ (U n t) (0 : Vec3)
  have ht₀ : 0 ≤ t := ha₀.trans ht.1
  have hStage (n : ℕ) : t ∈ Icc 0 (slab n) :=
    ⟨ht₀, ht.2.trans (haT.le.trans (hslab n))⟩
  have hstep (n : ℕ) (hn : j ≤ n) : dist (F n) (F (n + 1)) ≤ (freq (n + 1))⁻¹ := by
    have hcut : O (n + 1) t = 0 :=
      hO (n + 1) (Nat.succ_le_succ (hj.trans hn)) t
        ⟨ht₀, ht.2.trans (hactivation (Nat.succ_le_succ hn))⟩
    have h := hB n hn t (hStage (n + 1))
    rw [hcut, sub_zero, norm_iteratedFDeriv_one,
      fderiv_sub (hU (n + 1) t (hStage (n + 1))) (hU n t (hStage n))] at h
    rw [dist_comm, dist_eq_norm]
    exact h
  have hlim : Tendsto F atTop (𝓝 (fderiv ℝ (w t) (0 : Vec3))) :=
    (hprefix (activation (j + 1)) haT).tendsto_at
      (show (t, (0 : Vec3)) ∈ Icc 0 (activation (j + 1)) ×ˢ (univ : Set Vec3) from
        ⟨⟨ht₀, ht.2⟩, mem_univ _⟩)
  obtain ⟨hs, htail⟩ := reciprocal_inductive_frequency_tail hinit hfreq (j + 1)
  have hshift : Tendsto (fun k : ℕ => j + k) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat j
  have hdist :=
    dist_le_tsum_of_dist_le_of_tendsto₀ (fun k => (freq (j + 1 + k))⁻¹)
      (f := fun k => F (j + k)) (fun k => by
        change dist (F (j + k)) (F (j + k + 1)) ≤ (freq (j + 1 + k))⁻¹
        rw [show j + 1 + k = j + k + 1 by omega]
        exact hstep (j + k) (Nat.le_add_right _ _))
      hs (hlim.comp hshift)
  rw [← dist_eq_norm, dist_comm]
  simpa only [Nat.add_zero] using hdist.trans htail

private theorem cross3_smul_smul (r s : ℝ) (x y : Vec3) :
    cross3 (r • x) (s • y) = (r * s) • cross3 x y := by
  apply WithLp.ofLp_injective
  simp [cross3, smul_smul, mul_comm]

open MovingAmplitude (normFactor wave_norm_sq_eq)
open MovingWaveVector (frame X Q Z)

/-- The projection onto the newest wave direction sees the signed preceding
curl. The longitudinal third coordinate of (2.3) gives the lower bound. -/
theorem preceding_curl_projection_of_scaled_coordinates
    {k a k' : ℝ → Vec3} {t scale lengthBound : ℝ}
    (hk' : k' t ≠ 0) (hscale : 0 < scale)
    (hZ : 1 / 2 ≤ Z (frame k a) k' scale t)
    (hlen : ‖scale⁻¹ • k' t‖ ≤ lengthBound) :
    (‖k t‖ * ‖a t‖) * ((1 / 2) / lengthBound) ≤
      ⟪normalize (k' t), cross3 (k t) (a t)⟫_ℝ := by
  have haxis : 1 / 2 ≤ ⟪scale⁻¹ • k' t, frame k a t 2⟫_ℝ := by
    rw [real_inner_smul_left, real_inner_comm (frame k a t 2) (k' t), ← div_eq_inv_mul]
    exact hZ
  have hframe : cross3 (k t) (a t) = (‖k t‖ * ‖a t‖) • frame k a t 2 := by
    change _ = (‖k t‖ * ‖a t‖) • cross3 (normalize (k t)) (normalize (a t))
    rw [← cross3_smul_smul, NormedSpace.norm_smul_normalize, NormedSpace.norm_smul_normalize]
  exact inner_normalize_cross3_ge_of_frame hk' hframe (by positivity) hscale
    (by norm_num) haxis hlen

/-- The clock-window estimates in Lemma 2.3 control the scaled wave length
in (8.1). The bound includes the late regime needed in §8.2. -/
theorem norm_scaled_waveVector_le_of_window
    {e : ℝ → Fin 3 → Vec3} {k : ℝ → Vec3} {t scale S window : ℝ}
    (he : Orthonormal ℝ (e t)) (hscale : 0 < scale) (hS : 1 ≤ S) (hwindow : 1 ≤ window)
    (hX : |X e k scale t| ≤ window ^ 2) (hQ : |Q e k scale S t| ≤ window)
    (hZ : |Z e k scale t - 1| ≤ 1 / 2) :
    ‖scale⁻¹ • k t‖ ≤ 3 * window ^ 2 := by
  have hSpos : 0 < S := zero_lt_one.trans_le hS
  let X₁ := X e k scale t
  let Q₁ := Q e k scale S t
  let Z₁ := Z e k scale t
  have hwin : 1 ≤ window ^ 2 := one_le_pow₀ hwindow
  have hwin' : window ≤ window ^ 2 := by nlinarith
  have hZ₁ : |Z₁| ≤ 3 / 2 := by
    change |Z₁ - 1| ≤ 1 / 2 at hZ
    obtain ⟨hlo, hhi⟩ := abs_le.mp hZ
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hQdiv : |Q₁ / S| ≤ window ^ 2 := by
    rw [abs_div, abs_of_pos hSpos]
    exact (div_le_self (abs_nonneg _) hS).trans (hQ.trans hwin')
  have hXsq : X₁ ^ 2 ≤ (window ^ 2) ^ 2 :=
    sq_le_sq.mpr (by simpa only [abs_of_nonneg (sq_nonneg window)] using hX)
  have hQsq : (Q₁ / S) ^ 2 ≤ (window ^ 2) ^ 2 :=
    sq_le_sq.mpr (by simpa only [abs_of_nonneg (sq_nonneg window)] using hQdiv)
  have hZsq : Z₁ ^ 2 ≤ ((3 / 2 : ℝ) * window ^ 2) ^ 2 :=
    sq_le_sq.mpr (by
      rw [abs_of_nonneg (by positivity : 0 ≤ (3 / 2 : ℝ) * window ^ 2)]
      exact hZ₁.trans (by linarith))
  have hsquare : ‖scale⁻¹ • k t‖ ^ 2 = X₁ ^ 2 + (Q₁ / S) ^ 2 + Z₁ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hscale.le), mul_pow,
      wave_norm_sq_eq he hscale.ne' hSpos.ne', ← mul_assoc,
      ← mul_pow, inv_mul_cancel₀ hscale.ne', one_pow, one_mul, normFactor, div_pow]
  exact le_of_sq_le_sq (by nlinarith) (by positivity)

/-- Applying curl to the consecutive central gradient splittings in (T4)
gives (8.2), with the newest wave removed by the signed projection (8.1). -/
theorem norm_curlOfDerivative_ge_of_two_stage_splits
    {Dold Dmid Dnew Eprev Enew : Vec3 →L[ℝ] Vec3} {kp ap k a : Vec3}
    {cutoff signedLower oldBound prevError newError : ℝ}
    (hk : k ≠ 0)
    (hprev : Dmid = Dold + (innerSL ℝ kp).smulRight ap + Eprev)
    (hnew : Dnew = Dmid + cutoff • (innerSL ℝ k).smulRight a + Enew)
    (hold : ‖Dold‖ ≤ oldBound) (hEp : ‖Eprev‖ ≤ prevError) (hEn : ‖Enew‖ ≤ newError)
    (hsigned : signedLower ≤ ⟪normalize k, cross3 kp ap⟫_ℝ) :
    signedLower - ‖curlOfDerivativeCLM‖ * (oldBound + prevError + newError) ≤
      ‖curlOfDerivative Dnew‖ := by
  let lower := curlOfDerivativeCLM (Dold + Eprev + Enew)
  have hlower : ‖lower‖ ≤ ‖curlOfDerivativeCLM‖ * (oldBound + prevError + newError) := by
    apply (curlOfDerivativeCLM.le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc
      _ ≤ ‖Dold + Eprev‖ + ‖Enew‖ := norm_add_le _ _
      _ ≤ ‖Dold‖ + ‖Eprev‖ + ‖Enew‖ := add_le_add (norm_add_le _ _) le_rfl
      _ ≤ _ := add_le_add (add_le_add hold hEp) hEn
  have hcurl : curlOfDerivative Dnew = lower + cross3 kp ap + cutoff • cross3 k a := by
    have hrank (v w : Vec3) :
        curlOfDerivativeCLM ((innerSL ℝ w).smulRight v) = cross3 w v :=
      coordinateCurl_rankOne v w
    change curlOfDerivativeCLM Dnew = _
    rw [hnew, hprev]
    simp only [lower, map_add, map_smul, hrank]
    abel
  rw [hcurl]
  exact norm_twoLayerCurl_ge_of_projection cutoff hk hlower hsigned

/-- Lemma 2.2's logarithmic strength equation retains at least an
`exp (-1)` fraction of the preceding launch strength on the activation interval. -/
theorem preceding_strength_retained_on_short_interval
    {k a : ℝ → Vec3} {B : ℝ → Vec3 →L[ℝ] Vec3} {l r μ : ℝ}
    (hμ : 1 ≤ μ) (hshort : r - l ≤ μ ^ (-1 / 16 : ℝ))
    (hframe : ∀ t ∈ Icc l r, k t ≠ 0 ∧ a t ≠ 0 ∧ ⟪k t, a t⟫_ℝ = 0)
    (htrace : ∀ t ∈ Icc l r, LinearMap.trace ℝ Vec3 (B t).toLinearMap = 0)
    (hk : ∀ t ∈ Icc l r, HasDerivWithinAt k (-((B t).adjoint (k t))) (Icc l r) t)
    (ha : ∀ t ∈ Icc l r, HasDerivWithinAt a
      (-((B t) (a t)) + (2 * ⟪k t, B t (a t)⟫_ℝ / ‖k t‖ ^ 2) • k t) (Icc l r) t)
    (hB : ∀ t ∈ Icc l r, ‖B t‖ ≤ μ ^ (1 / 32 : ℝ))
    {t : ℝ} (ht : t ∈ Icc l r) :
    Real.exp (-1) * (‖k l‖ * ‖a l‖) ≤ ‖k t‖ * ‖a t‖ := by
  let σ (s : ℝ) := ‖k s‖ * ‖a s‖
  let E (s : ℝ) := frame k a s 2
  have hlog (s : ℝ) (hs : s ∈ Icc l r) :
      HasDerivWithinAt (fun u => Real.log (σ u)) ⟪E s, B s (E s)⟫_ℝ (Icc l r) s := by
    obtain ⟨hK, hA, hperp⟩ := hframe s hs
    exact (hasDerivWithinAt_movingFrame hs (B s) (htrace s hs) hK hA hperp
      (hk s hs) (ha s hs)).2.2.2
  have hderivBound (s : ℝ) (hs : s ∈ Ico l r) :
      ‖⟪E s, B s (E s)⟫_ℝ‖ ≤ μ ^ (1 / 32 : ℝ) := by
    have hs' := Ico_subset_Icc_self hs
    obtain ⟨hK, hA, hperp⟩ := hframe s hs'
    have hunit : ‖E s‖ = 1 := (orthonormal_movingFrame hK hA hperp).norm_eq_one 2
    have hinner := abs_real_inner_le_norm (E s) (B s (E s))
    have hop := (B s).le_opNorm (E s)
    rw [hunit, one_mul] at hinner
    rw [hunit, mul_one] at hop
    simpa only [Real.norm_eq_abs] using (hinner.trans hop).trans (hB s hs')
  have hμ₀ := zero_lt_one.trans_le hμ
  have hsmall : μ ^ (1 / 32 : ℝ) * μ ^ (-1 / 16 : ℝ) ≤ 1 := by
    rw [← Real.rpow_add hμ₀]
    exact Real.rpow_le_one_of_one_le_of_nonpos hμ (by norm_num)
  have habs : |Real.log (σ t) - Real.log (σ l)| ≤ 1 := by
    have hh := norm_image_sub_le_of_norm_deriv_le_segment' hlog hderivBound t ht
    rw [Real.norm_eq_abs] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 l)
      (Real.rpow_nonneg hμ₀.le _)).trans
        ((mul_le_mul_of_nonneg_left hshort (Real.rpow_nonneg hμ₀.le _)).trans hsmall))
  have hσ (s : ℝ) (hs : s ∈ Icc l r) : 0 < σ s :=
    mul_pos (norm_pos_iff.mpr (hframe s hs).1) (norm_pos_iff.mpr (hframe s hs).2.1)
  have hleft : l ∈ Icc l r := ⟨le_rfl, ht.1.trans ht.2⟩
  calc
    Real.exp (-1) * σ l = Real.exp (-1 + Real.log (σ l)) := by
      rw [Real.exp_add, Real.exp_log (hσ l hleft)]
    _ ≤ Real.exp (Real.log (σ t)) := Real.exp_le_exp.mpr (by linarith [(abs_le.mp habs).1])
    _ = σ t := Real.exp_log (hσ t ht)

/-- At current grade `j + 2`, the projection scale is `L_{j+3}`
and the preceding frequency is `λ_{j+1}`. The three-step logarithmic
bound from Lemma 1.3 absorbs the eighth power of this scale. -/
theorem eventually_inductive_projection_log_bound {freq : ℕ → ℝ}
    (hfreq : Tendsto freq atTop atTop)
    (hlog : ∀ i, 4 * Real.log (freq (i + 3)) ≤ Real.log (freq i) ^ 2) :
    ∀ᶠ j : ℕ in atTop, 0 < 4 * Real.log (freq (j + 4)) ∧
      (4 * Real.log (freq (j + 4))) ^ 8 ≤ freq (j + 1) ^ (1 / 8 : ℝ) := by
  have hshift (s : ℕ) : Tendsto (fun n : ℕ => n + s) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n s) tendsto_id
  have hasympt : ∀ᶠ x : ℝ in atTop, (Real.log x) ^ (16 : ℕ) ≤ x ^ (1 / 8 : ℝ) := by
    filter_upwards
      [(isLittleO_log_rpow_rpow_atTop 16 (show (0 : ℝ) < 1 / 8 by norm_num)).eventuallyLE,
        eventually_ge_atTop (1 : ℝ)] with x hx hx₁
    rw [show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hx
    rwa [Real.norm_of_nonneg (pow_nonneg (Real.log_nonneg hx₁) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx₁) _)] at hx
  filter_upwards [(hfreq.comp (hshift 1)).eventually hasympt,
    (hfreq.comp (hshift 4)).eventually_gt_atTop (1 : ℝ)] with j hj hjpos
  have hLpos : 0 < 4 * Real.log (freq (j + 4)) := mul_pos (by norm_num) (Real.log_pos hjpos)
  refine ⟨hLpos, ?_⟩
  calc
    _ ≤ (Real.log (freq (j + 1)) ^ 2) ^ 8 :=
      pow_le_pow_left₀ hLpos.le (hlog (j + 1)) 8
    _ ≤ _ := by rw [← pow_mul]; exact hj

/-- Combining the window and strength scales makes the signed projection
in (8.1) at least a constant times the preceding frequency to power (1/8). -/
theorem preceding_curl_projection_of_stage_scales
    {kp ap k : ℝ → Vec3} {t scale S window L C c μ : ℝ}
    (hKp : kp t ≠ 0) (hAp : ap t ≠ 0) (hperp : ⟪kp t, ap t⟫_ℝ = 0)
    (hk : k t ≠ 0) (hscale : 0 < scale) (hS : 1 ≤ S)
    (hwindow₁ : 1 ≤ window) (hC : 0 < C) (hμ : 0 < μ) (hwin : window ≤ C * L ^ 4)
    (hX : |X (frame kp ap) k scale t| ≤ window ^ 2)
    (hQ : |Q (frame kp ap) k scale S t| ≤ window)
    (hZ : |Z (frame kp ap) k scale t - 1| ≤ 1 / 2)
    (hL : L ^ 8 ≤ μ ^ (1 / 8 : ℝ))
    (hstrength : c * μ ^ (1 / 4 : ℝ) ≤ ‖kp t‖ * ‖ap t‖) :
    (c / (6 * C ^ 2)) * μ ^ (1 / 8 : ℝ) ≤ ⟪normalize (k t), cross3 (kp t) (ap t)⟫_ℝ := by
  have he : Orthonormal ℝ (frame kp ap t) := orthonormal_movingFrame hKp hAp hperp
  have hlen := norm_scaled_waveVector_le_of_window he hscale hS hwindow₁ hX hQ hZ
  have hlength : ‖scale⁻¹ • k t‖ ≤ 3 * C ^ 2 * μ ^ (1 / 8 : ℝ) := by
    calc
      _ ≤ 3 * window ^ 2 := hlen
      _ ≤ 3 * (C * L ^ 4) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hwindow₁) hwin 2)
          (by norm_num)
      _ = 3 * C ^ 2 * L ^ 8 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hL (by positivity)
  have hZ₀ : 1 / 2 ≤ Z (frame kp ap) k scale t := by linarith [(abs_le.mp hZ).1]
  have hproj := preceding_curl_projection_of_scaled_coordinates hk hscale hZ₀ hlength
  have hsquare : μ ^ (1 / 8 : ℝ) * μ ^ (1 / 8 : ℝ) = μ ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hμ]
    norm_num
  calc
    _ = (c * μ ^ (1 / 4 : ℝ)) * ((1 / 2) / (3 * C ^ 2 * μ ^ (1 / 8 : ℝ))) := by
      rw [← hsquare]
      field_simp [hC.ne', (Real.rpow_pos_of_pos hμ _).ne']
      ring
    _ ≤ (‖kp t‖ * ‖ap t‖) * ((1 / 2) / (3 * C ^ 2 * μ ^ (1 / 8 : ℝ))) :=
      mul_le_mul_of_nonneg_right hstrength (by positivity)
    _ ≤ _ := hproj

/-- The smaller, older gradient scale in (8.2) follows from the frequency
gap between the two preceding stages. -/
theorem older_gradient_scale_le_of_frequency_gap {older μ : ℝ} (hOlder : 0 ≤ older)
    (hgap : older ^ (288 : ℕ) ≤ μ) : older ^ 9 ≤ μ ^ (1 / 32 : ℝ) := by
  have h := Real.rpow_le_rpow (pow_nonneg hOlder 288) hgap (by norm_num : 0 ≤ (1 / 32 : ℝ))
  rw [← Real.rpow_natCast, ← Real.rpow_mul hOlder] at h
  have heq : ((288 : ℕ) : ℝ) * (1 / 32) = ((9 : ℕ) : ℝ) := by norm_num
  rwa [heq, Real.rpow_natCast] at h

/-- The signed two-wave lower bound survives the derivative tail. In
particular, this is the limiting bound used by
`theorem11_of_quantitative_activation_bounds`. -/
theorem norm_limit_curl_ge_of_stage_gradient_bounds
    {Dold Dmid Dnew Dlimit Eprev Enew : Vec3 →L[ℝ] Vec3} {kp ap k a : Vec3}
    {cutoff μ c : ℝ} (hμ : 1 ≤ μ) (hk : k ≠ 0)
    (hprev : Dmid = Dold + (innerSL ℝ kp).smulRight ap + Eprev)
    (hnew : Dnew = Dmid + cutoff • (innerSL ℝ k).smulRight a + Enew)
    (hold : ‖Dold‖ ≤ μ ^ (1 / 32 : ℝ))
    (hEp : ‖Eprev‖ ≤ μ ^ (-1 / 4 : ℝ)) (hEn : ‖Enew‖ ≤ μ ^ (-1 / 4 : ℝ))
    (hTail : ‖Dlimit - Dnew‖ ≤ 1)
    (hsigned : c * μ ^ (1 / 8 : ℝ) ≤ ⟪normalize k, cross3 kp ap⟫_ℝ) :
    c * μ ^ (1 / 8 : ℝ) - (3 * ‖curlOfDerivativeCLM‖) * μ ^ (1 / 32 : ℝ) -
      3 * ‖curlOfDerivativeCLM‖ ≤ ‖curlOfDerivative Dlimit‖ := by
  have herr : μ ^ (-1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hμ (by norm_num)
  have hstage := norm_curlOfDerivative_ge_of_two_stage_splits hk hprev hnew hold
    (hEp.trans herr) (hEn.trans herr) hsigned
  have htailCurl : ‖curlOfDerivative Dlimit - curlOfDerivative Dnew‖ ≤ ‖curlOfDerivativeCLM‖ := by
    calc
      _ = ‖curlOfDerivativeCLM (Dlimit - Dnew)‖ := by rw [map_sub]; rfl
      _ ≤ ‖curlOfDerivativeCLM‖ * ‖Dlimit - Dnew‖ := curlOfDerivativeCLM.le_opNorm _
      _ ≤ _ := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hTail (norm_nonneg curlOfDerivativeCLM)
  have htri := norm_sub_norm_le (curlOfDerivative Dnew) (curlOfDerivative Dlimit)
  rw [norm_sub_rev] at htri
  have hmargin : 0 ≤ ‖curlOfDerivativeCLM‖ * μ ^ (1 / 32 : ℝ) := by positivity
  linarith only [hstage, htailCurl, htri, hmargin]

/-- At current grade `j + 2`, the local data from (T4), the normalized
wave comparison, and the order-one tail yield the limiting lower bound
on the closed activation interval. The retained preceding strength is
the output of `preceding_strength_retained_on_short_interval`. -/
theorem norm_limit_center_curl_ge_of_inductive_stage
    {freq : ℕ → ℝ} {j : ℕ} {U : ℕ → Velocity} {w : Velocity}
    {kp ap k a : ℝ → Vec3} {Eprev Enew : Vec3 →L[ℝ] Vec3}
    {t cutoff S window C c : ℝ}
    (hμ : 1 ≤ freq (j + 1)) (hOldNonneg : 0 ≤ freq j) (hnext : freq (j + 1) ≤ freq (j + 2))
    (hfreqTail : 2 ≤ freq (j + 3)) (hgap : freq j ^ 288 ≤ freq (j + 1))
    (hkP : kp t ≠ 0) (haP : ap t ≠ 0) (hperp : ⟪kp t, ap t⟫_ℝ = 0)
    (hk : k t ≠ 0) (hS : 1 ≤ S) (hwindow : 1 ≤ window) (hC : 0 < C)
    (hwin : window ≤ C * (4 * Real.log (freq (j + 4))) ^ 4)
    (hX : |X (frame kp ap) k (freq (j + 2)) t| ≤ window ^ 2)
    (hQ : |Q (frame kp ap) k (freq (j + 2)) S t| ≤ window)
    (hZ : |Z (frame kp ap) k (freq (j + 2)) t - 1| ≤ 1 / 2)
    (hL : (4 * Real.log (freq (j + 4))) ^ 8 ≤ freq (j + 1) ^ (1 / 8 : ℝ))
    (hstrength : (Real.exp (-1) * c) * freq (j + 1) ^ (1 / 4 : ℝ) ≤ ‖kp t‖ * ‖ap t‖)
    (hprev : fderiv ℝ (U (j + 1) t) 0 =
      fderiv ℝ (U j t) 0 + (innerSL ℝ (kp t)).smulRight (ap t) + Eprev)
    (hnew : fderiv ℝ (U (j + 2) t) 0 =
      fderiv ℝ (U (j + 1) t) 0 + cutoff • (innerSL ℝ (k t)).smulRight (a t) + Enew)
    (hold : ‖fderiv ℝ (U j t) 0‖ ≤ freq j ^ 9)
    (hEp : ‖Eprev‖ ≤ freq (j + 1) ^ (-1 / 4 : ℝ))
    (hEn : ‖Enew‖ ≤ freq (j + 2) ^ (-1 / 4 : ℝ))
    (htail : ‖fderiv ℝ (w t) 0 - fderiv ℝ (U (j + 2) t) 0‖ ≤ 2 * (freq (j + 3))⁻¹) :
    (Real.exp (-1) * c / (6 * C ^ 2)) * freq (j + 1) ^ (1 / 8 : ℝ) -
      (3 * ‖curlOfDerivativeCLM‖) * freq (j + 1) ^ (1 / 32 : ℝ) -
      3 * ‖curlOfDerivativeCLM‖ ≤ ‖curl (w t) 0‖ := by
  have hμ₀ := zero_lt_one.trans_le hμ
  have hscale := hμ₀.trans_le hnext
  have hsigned := preceding_curl_projection_of_stage_scales hkP haP hperp hk hscale hS
    hwindow hC hμ₀ hwin hX hQ hZ hL hstrength
  have htail₁ : 2 * (freq (j + 3))⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by linarith)]
    exact hfreqTail
  exact norm_limit_curl_ge_of_stage_gradient_bounds hμ hk hprev hnew
    (hold.trans (older_gradient_scale_le_of_frequency_gap hOldNonneg hgap)) hEp
    (hEn.trans (Real.rpow_le_rpow_of_nonpos hμ₀ hnext (by norm_num)))
    (htail.trans htail₁) hsigned

end TorusEuler
