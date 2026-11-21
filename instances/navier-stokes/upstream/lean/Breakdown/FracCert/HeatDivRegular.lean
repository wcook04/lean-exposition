import Breakdown.FracCert.DecayFarField
import Breakdown.FracCert.KernelScaling
import Breakdown.FracCert.KernelDecay
import Breakdown.FracCert.KernelRingCutoff
import Breakdown.FracCert.KernelPiece
import Breakdown.FracCert.KernelDyadicSum

open MeasureTheory Set Real Filter Metric
open scoped ContDiff

noncomputable section

namespace Breakdown.FracInternal.HeatDivRegular

open Breakdown.FracCert

section Interp

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem deriv_increment {g : V → E} {m : ℕ} (hg : ContDiff ℝ (m + 1 : ℕ) g) {A : ℝ}
    (hA : ∀ y, ‖iteratedFDeriv ℝ (m + 1) g y‖ ≤ A) (x y : V) :
    ‖iteratedFDeriv ℝ m g y - iteratedFDeriv ℝ m g x‖ ≤ A * ‖y - x‖ := by
  refine convex_univ.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (fun z _ => ?_) (fun z _ => ?_)
    (mem_univ x) (mem_univ y)
  · exact hg.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self m) z
  · rw [norm_fderiv_iteratedFDeriv]; exact hA z

theorem step_bound (n : ℕ) : ∀ (g : V → E) (B A : ℝ), ContDiff ℝ (n + 1 : ℕ) g →
    (∀ y, ‖g y‖ ≤ B) → (∀ y, ‖iteratedFDeriv ℝ (n + 1) g y‖ ≤ A) →
    ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ 2 ^ n * B + n * A := by
  induction n with
  | zero =>
    intro g B A _ hB _ x
    simpa [norm_iteratedFDeriv_zero] using hB x
  | succ n ih =>
    intro g B A hg hB hA x
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA x)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x)
    rw [← norm_fderiv_iteratedFDeriv]
    refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) fun v hv => ?_
    have hgt : ContDiff ℝ (n + 1 + 1 : ℕ) (fun y => g (y + v)) :=
      hg.comp (contDiff_id.add contDiff_const)
    set h : V → E := (fun y => g (y + v)) - g with hh
    have hhc : ContDiff ℝ (n + 1 : ℕ) h :=
      (hgt.sub hg).of_le (by exact_mod_cast Nat.le_succ (n + 1))
    have hDh : ∀ m : ℕ, m ≤ n + 1 + 1 → ∀ y, iteratedFDeriv ℝ m h y =
        iteratedFDeriv ℝ m g (y + v) - iteratedFDeriv ℝ m g y := by
      intro m hm y
      have hm' : ((m : ℕ) : WithTop ℕ∞) ≤ ((n + 1 + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hm
      rw [hh, iteratedFDeriv_sub_apply (hgt.contDiffAt.of_le hm') (hg.contDiffAt.of_le hm'),
        iteratedFDeriv_comp_add_right]
    have h1 : ∀ y, ‖h y‖ ≤ 2 * B := by
      intro y
      simp only [hh, Pi.sub_apply]
      exact (norm_sub_le _ _).trans (by linarith [hB (y + v), hB y])
    have h2 : ∀ y, ‖iteratedFDeriv ℝ (n + 1) h y‖ ≤ A := by
      intro y
      rw [hDh (n + 1) (Nat.le_succ _) y]
      have := deriv_increment hg hA y (y + v)
      rwa [add_sub_cancel_left, hv, mul_one] at this
    have h3 := ih h (2 * B) A hhc h1 h2 x
    rw [hDh n (by omega) x] at h3
    have h4 : ‖iteratedFDeriv ℝ n g (x + v) - iteratedFDeriv ℝ n g x -
        fderiv ℝ (iteratedFDeriv ℝ n g) x ((x + v) - x)‖ ≤ A * ‖(x + v) - x‖ := by
      refine (convex_closedBall x 1).norm_image_sub_le_of_norm_fderiv_le' (fun z _ => ?_)
        (fun z hz => ?_) (mem_closedBall_self zero_le_one) ?_
      · exact hg.differentiable_iteratedFDeriv (by exact_mod_cast (by omega : n < n + 1 + 1)) z
      · rw [fderiv_iteratedFDeriv, Function.comp_apply, Function.comp_apply, ← map_sub,
          LinearIsometryEquiv.norm_map]
        have hz' : ‖z - x‖ ≤ 1 := by rwa [mem_closedBall, dist_eq_norm] at hz
        calc _ ≤ A * ‖z - x‖ := deriv_increment hg hA x z
          _ ≤ A * 1 := mul_le_mul_of_nonneg_left hz' hA0
          _ = A := mul_one A
      · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hv]
    rw [add_sub_cancel_left, hv, mul_one] at h4
    have h5 : ‖fderiv ℝ (iteratedFDeriv ℝ n g) x v‖ ≤
        ‖iteratedFDeriv ℝ n g (x + v) - iteratedFDeriv ℝ n g x‖ +
        ‖iteratedFDeriv ℝ n g (x + v) - iteratedFDeriv ℝ n g x -
          fderiv ℝ (iteratedFDeriv ℝ n g) x v‖ := by
      refine le_trans (le_of_eq ?_) (norm_sub_le _ _)
      congr 1; abel
    have h6 : (2 : ℝ) ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
    push_cast
    rw [h6]
    linarith

theorem interp (j : ℕ) (g : V → E) (A B : ℝ) (hg : ContDiff ℝ j g) (hB : ∀ y, ‖g y‖ ≤ B)
    (hA : ∀ y, ‖iteratedFDeriv ℝ j g y‖ ≤ A) :
    ∀ n ≤ j, ∀ y, ‖iteratedFDeriv ℝ n g y‖ ≤ ((2 : ℝ) ^ j + j) ^ j * (A + B) := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set K : ℝ := (2 : ℝ) ^ j + j with hK
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  have hAB : 0 ≤ A + B := by linarith
  have key : ∀ m ≤ j, ∀ y, ‖iteratedFDeriv ℝ (j - m) g y‖ ≤ K ^ m * (A + B) := by
    intro m
    induction m with
    | zero => intro _ y; simp only [Nat.sub_zero, pow_zero, one_mul]; linarith [hA y]
    | succ m ih =>
      intro hm y
      have hKm : 1 ≤ K ^ m := one_le_pow₀ hK1
      have hn1 : j - m = j - (m + 1) + 1 := by omega
      have hgn : ContDiff ℝ (j - (m + 1) + 1 : ℕ) g :=
        hg.of_le (by exact_mod_cast (by omega : j - (m + 1) + 1 ≤ j))
      have hb := step_bound (j - (m + 1)) g B (K ^ m * (A + B)) hgn hB
        (fun z => by have := ih (by omega) z; rwa [hn1] at this) y
      have hnj : ((j - (m + 1) : ℕ) : ℝ) ≤ j := by exact_mod_cast (by omega : j - (m + 1) ≤ j)
      have h2n : (2 : ℝ) ^ (j - (m + 1)) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
      have hX : 0 ≤ K ^ m * (A + B) := mul_nonneg (by linarith) hAB
      have hBle : B ≤ K ^ m * (A + B) := le_trans (by linarith) (le_mul_of_one_le_left hAB hKm)
      calc ‖iteratedFDeriv ℝ (j - (m + 1)) g y‖
          ≤ 2 ^ (j - (m + 1)) * B + ((j - (m + 1) : ℕ) : ℝ) * (K ^ m * (A + B)) := hb
        _ ≤ 2 ^ j * (K ^ m * (A + B)) + j * (K ^ m * (A + B)) :=
          add_le_add (mul_le_mul h2n hBle hB0 (by positivity)) (mul_le_mul_of_nonneg_right hnj hX)
        _ = K ^ (m + 1) * (A + B) := by rw [hK, pow_succ]; ring
  intro n hn y
  have := key (j - n) (Nat.sub_le j n) y
  rw [Nat.sub_sub_self hn] at this
  exact this.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK1 (Nat.sub_le j n)) hAB)

end Interp

section Param

variable {W : Type*} [MeasurableSpace W] {μ : Measure W}
  {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem param_contDiff {Φ : W → V → E} {w : W → ℝ} (j : ℕ)
    (hΦ : ∀ z, ContDiff ℝ j (Φ z))
    (hm : ∀ k ≤ j, ∀ y, AEStronglyMeasurable (fun z => iteratedFDeriv ℝ k (Φ z) y) μ)
    (hb : ∀ k ≤ j, ∀ z y, ‖iteratedFDeriv ℝ k (Φ z) y‖ ≤ w z)
    (hw : Integrable w μ) :
    ContDiff ℝ j (fun y => ∫ z, Φ z y ∂μ) ∧
      ∀ k ≤ j, iteratedFDeriv ℝ k (fun y => ∫ z, Φ z y ∂μ) =
        fun y => ∫ z, iteratedFDeriv ℝ k (Φ z) y ∂μ := by
  have hint : ∀ k ≤ j, ∀ y, Integrable (fun z => iteratedFDeriv ℝ k (Φ z) y) μ :=
    fun k hk y => Integrable.mono' hw (hm k hk y) (Eventually.of_forall fun z => hb k hk z y)
  have hdiff : ∀ k < j, ∀ y, HasFDerivAt (fun y => ∫ z, iteratedFDeriv ℝ k (Φ z) y ∂μ)
      (∫ z, fderiv ℝ (iteratedFDeriv ℝ k (Φ z)) y ∂μ) y := by
    intro k hk y
    have hk1 : k + 1 ≤ j := hk
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := univ)
      (F' := fun x z => fderiv ℝ (iteratedFDeriv ℝ k (Φ z)) x) (bound := w) Filter.univ_mem
      (Eventually.of_forall fun y => hm k hk.le y) (hint k hk.le y) ?_ ?_ hw ?_
    · have : (fun z => fderiv ℝ (iteratedFDeriv ℝ k (Φ z)) y) = fun z =>
          continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => V) E
            (iteratedFDeriv ℝ (k + 1) (Φ z) y) := by
        funext z; rw [fderiv_iteratedFDeriv]; rfl
      rw [this]
      exact (LinearIsometryEquiv.continuous _).comp_aestronglyMeasurable (hm (k + 1) hk1 y)
    · refine Eventually.of_forall fun z x _ => ?_
      rw [fderiv_iteratedFDeriv, Function.comp_apply, LinearIsometryEquiv.norm_map]
      exact hb (k + 1) hk1 z x
    · refine Eventually.of_forall fun z x _ => ?_
      exact ((hΦ z).differentiable_iteratedFDeriv (by exact_mod_cast hk) x).hasFDerivAt
  have heq : ∀ k ≤ j, iteratedFDeriv ℝ k (fun y => ∫ z, Φ z y ∂μ) =
      fun y => ∫ z, iteratedFDeriv ℝ k (Φ z) y ∂μ := by
    intro k
    induction k with
    | zero =>
      intro _
      funext y
      rw [iteratedFDeriv_zero_eq_comp]
      simp only [Function.comp_apply, iteratedFDeriv_zero_eq_comp]
      have hc := LinearIsometry.integral_comp_comm (μ := μ)
        (continuousMultilinearCurryFin0 ℝ V E).symm.toLinearIsometry (fun z => Φ z y)
      simp only [LinearIsometryEquiv.coe_toLinearIsometry] at hc
      exact hc.symm
    | succ k ih =>
      intro hk
      have hk' : k < j := hk
      funext y
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih hk'.le, (hdiff k hk' y).fderiv]
      have : (fun z => fderiv ℝ (iteratedFDeriv ℝ k (Φ z)) y) = fun z =>
          continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => V) E
            (iteratedFDeriv ℝ (k + 1) (Φ z) y) := by
        funext z; rw [fderiv_iteratedFDeriv]; rfl
      have hc := LinearIsometry.integral_comp_comm (μ := μ)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => V) E).toLinearIsometry
        (fun z => iteratedFDeriv ℝ (k + 1) (Φ z) y)
      simp only [LinearIsometryEquiv.coe_toLinearIsometry] at hc
      rw [this, hc, LinearIsometryEquiv.symm_apply_apply]
  have hcont : ∀ k ≤ j, Continuous (fun y => ∫ z, iteratedFDeriv ℝ k (Φ z) y ∂μ) := by
    intro k hk
    refine continuous_of_dominated (fun y => hm k hk y)
      (fun y => Eventually.of_forall fun z => hb k hk z y) hw ?_
    exact Eventually.of_forall fun z => (hΦ z).continuous_iteratedFDeriv (by exact_mod_cast hk)
  refine ⟨?_, heq⟩
  refine contDiff_iff_continuous_differentiable.2 ⟨fun m hm' => ?_, fun m hm' => ?_⟩
  · have hmj : m ≤ j := by exact_mod_cast hm'
    rw [heq m hmj]; exact hcont m hmj
  · have hmj : m < j := by exact_mod_cast hm'
    rw [heq m hmj.le]; exact fun y => (hdiff m hmj y).differentiableAt

end Param

section Conv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem conv_contDiff {f : Space → E} {κ : Space → ℝ} (j : ℕ) (hκ : Integrable κ)
    (hf : ContDiff ℝ j f) {M : ℝ} (hM : ∀ k ≤ j, ∀ y, ‖iteratedFDeriv ℝ k f y‖ ≤ M) (s : ℝ) :
    ContDiff ℝ j (fun x => ∫ w, κ w • f (x - s • w)) ∧
    ∀ k ≤ j, iteratedFDeriv ℝ k (fun x => ∫ w, κ w • f (x - s • w)) =
      fun x => ∫ w, κ w • iteratedFDeriv ℝ k f (x - s • w) := by
  have hfc : ∀ k ≤ j, Continuous (iteratedFDeriv ℝ k f) := fun k hk =>
    hf.continuous_iteratedFDeriv (by exact_mod_cast hk)
  have hsh : ∀ w, ContDiff ℝ j (fun x => f (x - s • w)) := fun w =>
    hf.comp (contDiff_id.sub contDiff_const)
  have hD : ∀ k ≤ j, ∀ w x, iteratedFDeriv ℝ k (fun x => κ w • f (x - s • w)) x =
      κ w • iteratedFDeriv ℝ k f (x - s • w) := by
    intro k hk w x
    rw [iteratedFDeriv_const_smul_apply' ((hsh w).contDiffAt.of_le (by exact_mod_cast hk)),
      iteratedFDeriv_comp_sub]
  obtain ⟨h1, h2⟩ := param_contDiff (μ := volume) (Φ := fun w x => κ w • f (x - s • w))
    (w := fun w => ‖κ w‖ * M) j (fun w => (hsh w).const_smul (κ w))
    (fun k hk y => by
      simp_rw [hD k hk]
      exact hκ.aestronglyMeasurable.smul
        ((hfc k hk).comp (continuous_const.sub (continuous_id.const_smul s))).aestronglyMeasurable)
    (fun k hk w y => by
      rw [hD k hk, norm_smul]
      exact mul_le_mul_of_nonneg_left (hM k hk _) (norm_nonneg _))
    (hκ.norm.mul_const M)
  refine ⟨h1, fun k hk => ?_⟩
  rw [h2 k hk]
  funext x
  exact integral_congr_ae (Eventually.of_forall fun w => hD k hk w x)

theorem conv_norm_le {G : Space → E} {κ : Space → ℝ} (hκ : Integrable κ) {M : ℝ}
    (hM : ∀ y, ‖G y‖ ≤ M) (s : ℝ) (x : Space) :
    ‖∫ w, κ w • G (x - s • w)‖ ≤ (∫ w, ‖κ w‖) * M := by
  rw [← integral_mul_const]
  exact norm_integral_le_of_norm_le (hκ.norm.mul_const M) (Eventually.of_forall fun w => by
    rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _))

theorem conv_continuous {G : Space → E} {κ : Space → ℝ} (hκ : Integrable κ) (hG : Continuous G)
    {M : ℝ} (hM : ∀ y, ‖G y‖ ≤ M) :
    Continuous (fun p : ℝ × Space => ∫ w, κ w • G (p.2 - p.1 • w)) := by
  refine continuous_of_dominated (bound := fun w => ‖κ w‖ * M) (fun p => ?_)
    (fun p => Eventually.of_forall fun w => ?_) (hκ.norm.mul_const M)
    (Eventually.of_forall fun w => ?_)
  · exact hκ.aestronglyMeasurable.smul
      (hG.comp (continuous_const.sub (continuous_id.const_smul p.1))).aestronglyMeasurable
  · rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
  · exact continuous_const.smul (hG.comp (continuous_snd.sub (continuous_fst.smul continuous_const)))

end Conv

theorem scale_integral {s : ℝ} (hs : 0 < s) (κ q : Space → ℝ) (x : Space) :
    ∫ z, ((s ^ 4)⁻¹ * κ (s⁻¹ • (x - z))) * q z = s⁻¹ * ∫ w, κ w * q (x - s • w) := by
  have e1 : ∫ z, ((s ^ 4)⁻¹ * κ (s⁻¹ • (x - z))) * q z =
      ∫ u, ((s ^ 4)⁻¹ * κ (s⁻¹ • u)) * q (x - u) := by
    have := integral_sub_left_eq_self (fun u => ((s ^ 4)⁻¹ * κ (s⁻¹ • u)) * q (x - u))
      (volume : Measure Space) x
    simp only [sub_sub_cancel] at this
    exact this
  have e3 : ∫ u, κ (s⁻¹ • u) * q (x - u) = s ^ 3 * ∫ w, κ w * q (x - s • w) := by
    have h := MeasureTheory.Measure.integral_comp_smul (volume : Measure Space)
      (fun w => κ w * q (x - s • w)) s⁻¹
    simp only [smul_smul, mul_inv_cancel₀ hs.ne', one_smul, finrank_euclideanSpace_fin,
      inv_pow, inv_inv, smul_eq_mul] at h
    rw [h, abs_of_pos (pow_pos hs 3)]
  have e2 : ∫ u, ((s ^ 4)⁻¹ * κ (s⁻¹ • u)) * q (x - u) =
      (s ^ 4)⁻¹ * ∫ u, κ (s⁻¹ • u) * q (x - u) := by
    rw [← integral_const_mul]
    congr 1; funext u; ring
  rw [e1, e2, e3]
  field_simp

theorem kernel_re (hk : KernelDecayStatement) {α t : ℝ} (hα : 0 < α) (ht : 0 < t)
    (a b c : Fin 3) (y : Space) :
    (projDivKernel α t a b c y).re = ((t ^ (1 / (2 * α))) ^ 4)⁻¹ *
      (projDivKernel α 1 a b c ((t ^ (1 / (2 * α)))⁻¹ • y)).re := by
  rw [((kernelScaling_of hk) α hα a b c t ht).1 y, Complex.re_ofReal_mul]
  congr 1
  · rw [Real.rpow_neg ht.le]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    push_cast
    field_simp
    ring
  · rw [Real.rpow_neg ht.le]

theorem basis_expand (v : Space) :
    v = ∑ a : Fin 3, v a • EuclideanSpace.single a (1 : ℝ) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v]
  simp [EuclideanSpace.basisFun_apply]

theorem cont_scaled {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {G : Space → E} {κ : Space → ℝ} (hκ : Integrable κ) (hG : Continuous G)
    {M : ℝ} (hM : ∀ y, ‖G y‖ ≤ M) (g : ℝ) :
    ContinuousOn (fun q : ℝ × Space => ∫ w, κ w • G (q.2 - q.1 ^ g • w)) (Ioi 0 ×ˢ univ) := by
  have hr : ContinuousOn (fun q : ℝ × Space => q.1 ^ g) (Ioi 0 ×ˢ univ) :=
    continuousOn_fst.rpow_const fun q hq => Or.inl (hq.1 : (0 : ℝ) < q.1).ne'
  exact (conv_continuous hκ hG hM).comp_continuousOn (hr.prodMk continuousOn_snd)

end Breakdown.FracInternal.HeatDivRegular

namespace Breakdown.FracCert

open Breakdown.FracInternal.HeatDivRegular

theorem heatDivRegular_of (hk : KernelDecayStatement) : HeatDivRegularStatement := by
  intro α hα1 hα2 β j hβ0 hβ3
  have hα : 0 < α := by linarith
  let κ : Fin 3 × Fin 3 × Fin 3 → Space → ℝ := fun p w => (projDivKernel α 1 p.1 p.2.1 p.2.2 w).re
  have hκ : ∀ p, Integrable (κ p) := fun p =>
    ((kernelScaling_of hk) α hα p.1 p.2.1 p.2.2 1 one_pos).2.2.1.re
  let L : ℝ := ∑ p : Fin 3 × Fin 3 × Fin 3, ∫ w, ‖κ p w‖
  refine ⟨L * ((2 : ℝ) ^ j + j) ^ j, ?_⟩
  intro F A B hF hA hB
  have hB' : ∀ y, ‖F y‖ ≤ B := by
    intro y
    have h1y : (1 : ℝ) ≤ (1 + ‖y‖) ^ β := Real.one_le_rpow (by linarith [norm_nonneg y]) hβ0
    exact le_trans (le_mul_of_one_le_left (norm_nonneg _) h1y) (hB y)
  have hM := interp j F A B hF hB' hA
  set M : ℝ := ((2 : ℝ) ^ j + j) ^ j * (A + B) with hMdef
  let e : Fin 3 → Space := fun a => EuclideanSpace.single a (1 : ℝ)
  let P : Fin 3 × Fin 3 × Fin 3 → (Fin 3 → Fin 3 → ℝ) →L[ℝ] Space := fun p =>
    ((ContinuousLinearMap.proj p.2.2 : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj p.2.1 : (Fin 3 → Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))).smulRight (e p.1)
  have hPapp : ∀ p m, P p m = m p.2.1 p.2.2 • e p.1 := fun p m => rfl
  have hPn : ∀ p, ‖P p‖ ≤ 1 := by
    intro p
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun m => ?_
    rw [hPapp, norm_smul, one_mul]
    have he : ‖e p.1‖ = 1 := by simp [e]
    rw [he, mul_one]
    exact (norm_le_pi_norm (m p.2.1) p.2.2).trans (norm_le_pi_norm m p.2.1)
  let f : Fin 3 × Fin 3 × Fin 3 → Space → Space := fun p => P p ∘ F
  have hfc : ∀ p, ContDiff ℝ j (f p) := fun p => (P p).contDiff.comp hF
  have hfM : ∀ p, ∀ n ≤ j, ∀ y, ‖iteratedFDeriv ℝ n (f p) y‖ ≤ M := by
    intro p n hn y
    rw [ContinuousLinearMap.iteratedFDeriv_comp_left (P p) hF.contDiffAt (by exact_mod_cast hn)]
    refine ((P p).norm_compContinuousMultilinearMap_le _).trans ?_
    calc ‖P p‖ * ‖iteratedFDeriv ℝ n F y‖ ≤ 1 * M :=
          mul_le_mul (hPn p) (hM n hn y) (norm_nonneg _) zero_le_one
      _ = M := one_mul M
  let Φ : ℝ → Space → Space := fun s x => ∑ p, ∫ w, κ p w • f p (x - s • w)
  have hconv := fun p s => conv_contDiff j (hκ p) (hfc p) (hfM p) s
  have hΦc : ∀ s, ContDiff ℝ j (Φ s) := fun s =>
    ContDiff.sum fun p _ => (hconv p s).1
  have hΦD : ∀ s, ∀ n ≤ j, ∀ x, iteratedFDeriv ℝ n (Φ s) x =
      ∑ p, ∫ w, κ p w • iteratedFDeriv ℝ n (f p) (x - s • w) := by
    intro s n hn x
    have : Φ s = ∑ p, fun x => ∫ w, κ p w • f p (x - s • w) := by
      funext x; simp [Φ, Finset.sum_apply]
    rw [this, iteratedFDeriv_sum_apply
      (fun p _ => ((hconv p s).1.of_le (by exact_mod_cast hn)).contDiffAt)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [(hconv p s).2 n hn]
  have hs_pos : ∀ t : ℝ, 0 < t → 0 < t ^ (1 / (2 * α)) := fun t ht => Real.rpow_pos_of_pos ht _
  have hrep : ∀ t : ℝ, 0 < t → heatDivConv α t F =
      fun x => (t ^ (1 / (2 * α)))⁻¹ • Φ (t ^ (1 / (2 * α))) x := by
    intro t ht
    funext x
    set s := t ^ (1 / (2 * α)) with hs
    have hs0 : 0 < s := hs_pos t ht
    have hterm : ∀ a b c : Fin 3, (∫ z, (projDivKernel α t a b c (x - z)).re * F z b c) • e a =
        s⁻¹ • ∫ w, κ (a, b, c) w • f (a, b, c) (x - s • w) := by
      intro a b c
      have h1 : ∫ z, (projDivKernel α t a b c (x - z)).re * F z b c =
          ∫ z, ((s ^ 4)⁻¹ * κ (a, b, c) (s⁻¹ • (x - z))) * F z b c := by
        congr 1; funext z; rw [kernel_re hk hα ht]
      have h2 : (fun w => κ (a, b, c) w • f (a, b, c) (x - s • w)) =
          fun w => (κ (a, b, c) w * F (x - s • w) b c) • e a := by
        funext w
        simp only [f, Function.comp_apply, hPapp, smul_smul]
      rw [h1, scale_integral hs0 (κ (a, b, c)) (fun z => F z b c) x, h2, integral_smul_const,
        smul_smul]
    rw [basis_expand (heatDivConv α t F x)]
    simp only [Φ, Finset.smul_sum]
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show heatDivConv α t F x a = ∑ b : Fin 3, ∑ c : Fin 3,
      ∫ z, (projDivKernel α t a b c (x - z)).re * F z b c from rfl]
    simp only [Finset.sum_smul]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => hterm a b c
  have hD : ∀ n ≤ j, ∀ t : ℝ, 0 < t → ∀ x, iteratedFDeriv ℝ n (heatDivConv α t F) x =
      (t ^ (1 / (2 * α)))⁻¹ • ∑ p, ∫ w, κ p w •
        iteratedFDeriv ℝ n (f p) (x - t ^ (1 / (2 * α)) • w) := by
    intro n hn t ht x
    rw [hrep t ht, iteratedFDeriv_const_smul_apply'
      ((hΦc _).contDiffAt.of_le (by exact_mod_cast hn)), hΦD _ n hn x]
  refine ⟨fun t ht => ?_, fun n hn => ?_, fun n hn t ht _ x => ?_⟩
  · rw [hrep t ht]; exact (hΦc _).const_smul _
  · have hr : ContinuousOn (fun q : ℝ × Space => q.1 ^ (1 / (2 * α))) (Ioi 0 ×ˢ univ) :=
      continuousOn_fst.rpow_const fun q hq => Or.inl (hq.1 : (0 : ℝ) < q.1).ne'
    have hc : ContinuousOn (fun q : ℝ × Space => (q.1 ^ (1 / (2 * α)))⁻¹ •
        ∑ p, ∫ w, κ p w • iteratedFDeriv ℝ n (f p) (q.2 - q.1 ^ (1 / (2 * α)) • w))
        (Ioi 0 ×ˢ univ) := by
      refine (hr.inv₀ fun q hq => (hs_pos q.1 hq.1).ne').smul ?_
      exact continuousOn_finsetSum _ fun p _ => cont_scaled (hκ p)
        ((hfc p).continuous_iteratedFDeriv (by exact_mod_cast hn)) (hfM p n hn) _
    refine hc.congr ?_
    intro q hq
    exact hD n hn q.1 (show (0 : ℝ) < q.1 from hq.1) q.2
  · rw [hD n hn t ht x, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hs_pos t ht)),
      ← Real.rpow_neg ht.le]
    have hsum : ‖∑ p, ∫ w, κ p w • iteratedFDeriv ℝ n (f p) (x - t ^ (1 / (2 * α)) • w)‖ ≤
        L * M := by
      refine (norm_sum_le _ _).trans ?_
      simp only [L, Finset.sum_mul]
      exact Finset.sum_le_sum fun p _ => conv_norm_le (hκ p) (hfM p n hn) _ x
    calc t ^ (-(1 / (2 * α))) * ‖∑ p, ∫ w, κ p w •
          iteratedFDeriv ℝ n (f p) (x - t ^ (1 / (2 * α)) • w)‖
        ≤ t ^ (-(1 / (2 * α))) * (L * M) :=
          mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg ht.le _)
      _ = L * ((2 : ℝ) ^ j + j) ^ j * t ^ (-(1 / (2 * α))) * (A + B) := by rw [hMdef]; ring

theorem heatDivRegular : HeatDivRegularStatement :=
  heatDivRegular_of (kernelDecay_of ringCutoff pieceKernel dyadicSum)

end Breakdown.FracCert
