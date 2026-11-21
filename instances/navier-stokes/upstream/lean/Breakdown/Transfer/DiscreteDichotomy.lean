import Breakdown.Transfer.StatementsAbstract

open scoped ENNReal

noncomputable section

namespace Breakdown

namespace DiscreteDichotomyInternal

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem idem_apply {Pu : E →L[ℝ] E} (hP : Pu * Pu = Pu) (x : E) : Pu (Pu x) = Pu x := by
  have h := congrArg (fun T : E →L[ℝ] E => T x) hP
  simpa [mul_apply_eq_comp] using h

theorem comm_apply {Pu M : E →L[ℝ] E} (hC : Pu * M = M * Pu) (x : E) : Pu (M x) = M (Pu x) := by
  have h := congrArg (fun T : E →L[ℝ] E => T x) hC
  simpa [mul_apply_eq_comp] using h

theorem comm_pow_apply {Pu M : E →L[ℝ] E} (hC : Pu * M = M * Pu) (n : ℕ) (x : E) :
    Pu ((M ^ n) x) = (M ^ n) (Pu x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, ih, comm_apply hC]

theorem eq_of_range {Pu M : E →L[ℝ] E} {K r₂ : ℝ}
    (hg : ∀ (n : ℕ) (x : E), ‖Pu x‖ ≤ K * r₂⁻¹ ^ n * ‖(M ^ n) (Pu x)‖)
    {w w' : E} (hw : Pu w = w) (hw' : Pu w' = w') (h : M w = M w') : w = w' := by
  have h1 := hg 1 (w - w')
  simp only [map_sub, hw, hw', pow_one, h, sub_self, norm_zero, mul_zero] at h1
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h1)

theorem exists_pre {Pu M : E →L[ℝ] E} (hP : Pu * Pu = Pu)
    (hs : ∀ y ∈ LinearMap.range (Pu : E →ₗ[ℝ] E), ∃ x ∈ LinearMap.range (Pu : E →ₗ[ℝ] E), M x = y)
    (z : E) : ∃ w, Pu w = w ∧ M w = Pu z := by
  obtain ⟨x, hx, hMx⟩ := hs (Pu z) (LinearMap.mem_range.mpr ⟨z, rfl⟩)
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hx
  refine ⟨x, ?_, hMx⟩
  rw [← hv]
  exact idem_apply hP v

theorem exists_inverse {Pu M : E →L[ℝ] E} {K r₂ : ℝ} (hP : Pu * Pu = Pu)
    (hg : ∀ (n : ℕ) (x : E), ‖Pu x‖ ≤ K * r₂⁻¹ ^ n * ‖(M ^ n) (Pu x)‖)
    (hs : ∀ y ∈ LinearMap.range (Pu : E →ₗ[ℝ] E), ∃ x ∈ LinearMap.range (Pu : E →ₗ[ℝ] E), M x = y)
    (hK : 0 ≤ K) (hr₂ : 0 < r₂) :
    ∃ N : E →L[ℝ] E, (∀ z, Pu (N z) = N z) ∧ ∀ z, M (N z) = Pu z := by
  choose f hf using exists_pre hP hs
  let L : E →ₗ[ℝ] E :=
    { toFun := f
      map_add' := fun a b => by
        refine eq_of_range hg (hf (a + b)).1 ?_ ?_
        · rw [map_add, (hf a).1, (hf b).1]
        · rw [(hf (a + b)).2, map_add, map_add, (hf a).2, (hf b).2]
      map_smul' := fun t a => by
        refine eq_of_range hg (hf (t • a)).1 ?_ ?_
        · rw [RingHom.id_apply, map_smul, (hf a).1]
        · rw [(hf (t • a)).2, RingHom.id_apply, map_smul, map_smul, (hf a).2] }
  refine ⟨L.mkContinuous (K * r₂⁻¹ * ‖Pu‖) fun z => ?_, fun z => (hf z).1, fun z => (hf z).2⟩
  show ‖f z‖ ≤ K * r₂⁻¹ * ‖Pu‖ * ‖z‖
  have h1 := hg 1 (f z)
  rw [(hf z).1, pow_one, pow_one, (hf z).2] at h1
  calc ‖f z‖ ≤ K * r₂⁻¹ * ‖Pu z‖ := h1
    _ ≤ K * r₂⁻¹ * (‖Pu‖ * ‖z‖) :=
        mul_le_mul_of_nonneg_left (Pu.le_opNorm z) (mul_nonneg hK (inv_nonneg.mpr hr₂.le))
    _ = K * r₂⁻¹ * ‖Pu‖ * ‖z‖ := by ring

section Inverse

variable {Pu M N : E →L[ℝ] E} (hP : Pu * Pu = Pu) (hC : Pu * M = M * Pu)
  (hNP : ∀ z, Pu (N z) = N z) (hMN : ∀ z, M (N z) = Pu z)
include hNP in
theorem range_pow (j : ℕ) (z : E) : Pu ((N ^ (j + 1)) z) = (N ^ (j + 1)) z := by
  rw [pow_succ', mul_apply_eq_comp, hNP]

include hP hC hMN in
theorem left_inverse_pow (j : ℕ) (z : E) : Pu ((M ^ j) ((N ^ j) z)) = Pu z := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ M, pow_succ' N, mul_apply_eq_comp, mul_apply_eq_comp,
      hMN, comm_pow_apply hC j, idem_apply hP, ← comm_pow_apply hC j, ih]

include hP hC hNP hMN in
theorem norm_pow_le {K r₂ : ℝ} (hg : ∀ (n : ℕ) (x : E), ‖Pu x‖ ≤ K * r₂⁻¹ ^ n * ‖(M ^ n) (Pu x)‖)
    (j : ℕ) (z : E) : ‖(N ^ (j + 1)) z‖ ≤ K * r₂⁻¹ ^ (j + 1) * ‖Pu z‖ := by
  have h1 := hg (j + 1) ((N ^ (j + 1)) z)
  rw [← comm_pow_apply hC, left_inverse_pow hP hC hMN, range_pow hNP] at h1
  exact h1

include hNP hMN in
theorem shift_term (Θ : ℝ) (j : ℕ) (v : E) :
    M (Θ ^ (j + 1) • (N ^ (j + 1 + 1)) v) = Θ • (Θ ^ j • (N ^ (j + 1)) v) := by
  rw [map_smul, pow_succ' N (j + 1), mul_apply_eq_comp, hMN, range_pow hNP, smul_smul,
    pow_succ, mul_comm]

end Inverse

def tailSum (N : E →L[ℝ] E) (Θ : ℝ) (f : ℕ → E) : E := -∑' j, Θ ^ j • (N ^ (j + 1)) (f j)

section Series

variable {N : E →L[ℝ] E} {Θ r₂ A : ℝ} (hΘ : 0 < Θ) (hr₂ : 0 < r₂) (hA : 0 ≤ A)
  (hB : ∀ (j : ℕ) (z : E), ‖(N ^ (j + 1)) z‖ ≤ A * r₂⁻¹ ^ (j + 1) * ‖z‖)

include hΘ hr₂ hA hB in
theorem term_le {f : ℕ → E} {R : ℝ} (hf : ∀ j, ‖f j‖ ≤ R) (j : ℕ) :
    ‖Θ ^ j • (N ^ (j + 1)) (f j)‖ ≤ A * r₂⁻¹ * R * (Θ / r₂) ^ j := by
  rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos hΘ]
  calc Θ ^ j * ‖(N ^ (j + 1)) (f j)‖ ≤ Θ ^ j * (A * r₂⁻¹ ^ (j + 1) * R) :=
        mul_le_mul_of_nonneg_left ((hB j (f j)).trans (mul_le_mul_of_nonneg_left (hf j)
          (mul_nonneg hA (pow_nonneg (inv_nonneg.mpr hr₂.le) _)))) (pow_nonneg hΘ.le _)
    _ = A * r₂⁻¹ * R * (Θ / r₂) ^ j := by rw [div_eq_mul_inv, mul_pow, pow_succ]; ring

variable (hΘr : Θ < r₂)

include hΘ hr₂ hA hB hΘr in
theorem summable_terms {f : ℕ → E} {R : ℝ} (hf : ∀ j, ‖f j‖ ≤ R) :
    Summable fun j => Θ ^ j • (N ^ (j + 1)) (f j) :=
  Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (div_nonneg hΘ.le hr₂.le) ((div_lt_one hr₂).mpr hΘr)).mul_left
      (A * r₂⁻¹ * R)) (term_le hΘ hr₂ hA hB hf)

include hΘ hr₂ hA hB hΘr in
theorem norm_tailSum_le {f : ℕ → E} {R : ℝ} (hf : ∀ j, ‖f j‖ ≤ R) :
    ‖tailSum N Θ f‖ ≤ A * r₂⁻¹ * R * (1 - Θ / r₂)⁻¹ := by
  rw [tailSum, norm_neg]
  exact tsum_of_norm_bounded
    ((hasSum_geometric_of_lt_one (div_nonneg hΘ.le hr₂.le) ((div_lt_one hr₂).mpr hΘr)).mul_left
      (A * r₂⁻¹ * R)) (term_le hΘ hr₂ hA hB hf)

include hΘ hr₂ hA hB hΘr in
theorem tailSum_add {f g : ℕ → E} {R S : ℝ} (hf : ∀ j, ‖f j‖ ≤ R) (hg : ∀ j, ‖g j‖ ≤ S) :
    tailSum N Θ (fun j => f j + g j) = tailSum N Θ f + tailSum N Θ g := by
  simp only [tailSum, map_add, smul_add]
  rw [(summable_terms hΘ hr₂ hA hB hΘr hf).tsum_add (summable_terms hΘ hr₂ hA hB hΘr hg), neg_add]

theorem tailSum_smul (t : ℝ) (f : ℕ → E) :
    tailSum N Θ (fun j => t • f j) = t • tailSum N Θ f := by
  simp only [tailSum, map_smul]
  simp only [smul_comm (Θ ^ _) t]
  rw [tsum_const_smul'', smul_neg]

variable {Pu M : E →L[ℝ] E} (hNP : ∀ z, Pu (N z) = N z) (hMN : ∀ z, M (N z) = Pu z)

include hΘ hr₂ hA hB hΘr hNP in
theorem range_tailSum {f : ℕ → E} {R : ℝ} (hf : ∀ j, ‖f j‖ ≤ R) :
    Pu (tailSum N Θ f) = tailSum N Θ f := by
  rw [tailSum, map_neg, ContinuousLinearMap.map_tsum Pu (summable_terms hΘ hr₂ hA hB hΘr hf)]
  simp only [map_smul, range_pow hNP]

include hΘ hr₂ hA hB hΘr hNP hMN in
theorem step_tailSum {f : ℕ → E} {R : ℝ} (hf : ∀ j, ‖f j‖ ≤ R) :
    Θ⁻¹ • (M (tailSum N Θ f) + Pu (f 0)) = tailSum N Θ (fun j => f (j + 1)) := by
  have hs := summable_terms hΘ hr₂ hA hB hΘr hf
  have hM : M (tailSum N Θ f) = -∑' j, M (Θ ^ j • (N ^ (j + 1)) (f j)) := by
    rw [tailSum, map_neg, ContinuousLinearMap.map_tsum M hs]
  rw [(hs.mapL M).tsum_eq_zero_add] at hM
  simp only [shift_term hNP hMN, pow_zero, one_smul, zero_add, pow_one, hMN] at hM
  rw [tsum_const_smul''] at hM
  rw [hM]
  simp only [tailSum]
  set S := ∑' j, Θ ^ j • (N ^ (j + 1)) (f (j + 1))
  have h1 : -(Pu (f 0) + Θ • S) + Pu (f 0) = -(Θ • S) := by abel
  rw [h1, smul_neg, smul_smul, inv_mul_cancel₀ hΘ.ne', one_smul]

end Series

theorem rec_formula (B : E →L[ℝ] E) (w d : ℕ → E) (h : ∀ n, w (n + 1) = B (w n) + d n) (n : ℕ) :
    w n = (B ^ n) (w 0) + ∑ m ∈ Finset.range n, (B ^ (n - 1 - m)) (d m) := by
  have e1 : ∀ (k : ℕ) (v : E), B ((B ^ k) v) = (B ^ (k + 1)) v := fun k v => by
    rw [pow_succ', mul_apply_eq_comp]
  induction n with
  | zero => simp
  | succ n ih =>
    have hsum : ∑ m ∈ Finset.range n, B ((B ^ (n - 1 - m)) (d m)) =
        ∑ m ∈ Finset.range n, (B ^ (n + 1 - 1 - m)) (d m) :=
      Finset.sum_congr rfl fun m hm => by
        rw [e1, show n - 1 - m + 1 = n + 1 - 1 - m by have := Finset.mem_range.mp hm; omega]
    rw [h n, ih, map_add, map_sum, hsum, e1, Finset.sum_range_succ,
      show n + 1 - 1 - n = 0 by omega, pow_zero, one_apply_eq_self, add_assoc]

theorem norm_pow_quot_le {Pu M : E →L[ℝ] E} {K r₁ Θ : ℝ} (hΘ : 0 < Θ)
    (hdec : ∀ n : ℕ, ‖M ^ n * (1 - Pu)‖ ≤ K * r₁ ^ n) (k : ℕ) (v : E) :
    ‖((Θ⁻¹ • M) ^ k) (v - Pu v)‖ ≤ K * (r₁ / Θ) ^ k * ‖v‖ := by
  have e : (M ^ k) (v - Pu v) = (M ^ k * (1 - Pu)) v := by
    rw [mul_apply_eq_comp, sub_apply, one_apply_eq_self]
  rw [smul_pow, smul_apply, norm_smul, e,
    Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hΘ.le) _)]
  calc Θ⁻¹ ^ k * ‖(M ^ k * (1 - Pu)) v‖ ≤ Θ⁻¹ ^ k * (K * r₁ ^ k * ‖v‖) :=
        mul_le_mul_of_nonneg_left ((M ^ k * (1 - Pu)).le_of_opNorm_le (hdec k) v)
          (pow_nonneg (inv_nonneg.mpr hΘ.le) _)
    _ = K * (r₁ / Θ) ^ k * ‖v‖ := by rw [div_eq_mul_inv, mul_pow]; ring

end DiscreteDichotomyInternal

open DiscreteDichotomyInternal in
theorem discreteDichotomy : DiscreteDichotomyStatement := by
  intro E _ _ _ M Pu K r₁ r₂ Θ hP hC hr₁ hr₁Θ hΘr hdec hg hs
  have hΘ : 0 < Θ := lt_of_le_of_lt hr₁ hr₁Θ
  have hr₂ : 0 < r₂ := hΘ.trans hΘr
  have hK : 0 ≤ K := by simpa using (norm_nonneg _).trans (hdec 0)
  have hρ0 : 0 ≤ r₁ / Θ := div_nonneg hr₁ hΘ.le
  have hρ1 : r₁ / Θ < 1 := (div_lt_one hΘ).mpr hr₁Θ
  have hσ1 : Θ / r₂ < 1 := (div_lt_one hr₂).mpr hΘr
  obtain ⟨N, hNP, hMN⟩ := exists_inverse hP hg hs hK hr₂
  have hA : 0 ≤ K * ‖Pu‖ := mul_nonneg hK (norm_nonneg _)
  have hB : ∀ (j : ℕ) (z : E), ‖(N ^ (j + 1)) z‖ ≤ K * ‖Pu‖ * r₂⁻¹ ^ (j + 1) * ‖z‖ := fun j z => by
    calc ‖(N ^ (j + 1)) z‖ ≤ K * r₂⁻¹ ^ (j + 1) * ‖Pu z‖ := norm_pow_le hP hC hNP hMN hg j z
      _ ≤ K * r₂⁻¹ ^ (j + 1) * (‖Pu‖ * ‖z‖) := mul_le_mul_of_nonneg_left (Pu.le_opNorm z)
          (mul_nonneg hK (pow_nonneg (inv_nonneg.mpr hr₂.le) _))
      _ = K * ‖Pu‖ * r₂⁻¹ ^ (j + 1) * ‖z‖ := by ring
  have hc0 : ∀ (c : lp (fun _ : ℕ => E) ∞) (j : ℕ), ‖c j‖ ≤ ‖c‖ :=
    fun c j => lp.norm_apply_le_norm ENNReal.top_ne_zero c j
  have hc : ∀ (c : lp (fun _ : ℕ => E) ∞) (n j : ℕ), ‖c (n + j)‖ ≤ ‖c‖ := fun c n j => hc0 c (n + j)
  let L : lp (fun _ : ℕ => E) ∞ →ₗ[ℝ] E :=
    { toFun := fun c => tailSum N Θ (fun j => c j)
      map_add' := fun c d => by
        simp only [lp.coeFn_add, Pi.add_apply]
        exact tailSum_add hΘ hr₂ hA hB hΘr (hc0 c) (hc0 d)
      map_smul' := fun t c => by
        simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
        exact tailSum_smul t _ }
  let U := L.mkContinuous (K * ‖Pu‖ * r₂⁻¹ * (1 - Θ / r₂)⁻¹) fun c => by
    show ‖tailSum N Θ (fun j => c j)‖ ≤ K * ‖Pu‖ * r₂⁻¹ * (1 - Θ / r₂)⁻¹ * ‖c‖
    calc _ ≤ _ := norm_tailSum_le hΘ hr₂ hA hB hΘr (hc0 c)
      _ = K * ‖Pu‖ * r₂⁻¹ * (1 - Θ / r₂)⁻¹ * ‖c‖ := by ring
  have hU : ∀ c, U c = tailSum N Θ (fun j => c j) := fun c => rfl
  refine ⟨U, K * ‖Pu‖ * r₂⁻¹ * (1 - Θ / r₂)⁻¹ + K + Θ⁻¹ * K * (1 - r₁ / Θ)⁻¹,
    fun c => ?_, fun c x₀ hx₀ n => ?_⟩
  · rw [hU]
    exact range_tailSum hΘ hr₂ hA hB hΘr hNP (hc0 c)
  obtain ⟨y, hy⟩ : ∃ y, y = orbitSeq M Θ (fun m => c m) x₀ := ⟨_, rfl⟩
  have h0 : y 0 = x₀ := by rw [hy]; rfl
  have hrec : ∀ k, y (k + 1) = Θ⁻¹ • (M (y k) + c k) := fun k => by rw [hy]; rfl
  rw [← hy]
  have hPy : ∀ k, Pu (y k) = tailSum N Θ (fun j => c (k + j)) := by
    intro k
    induction k with
    | zero =>
      rw [h0, hx₀, hU]
      simp only [zero_add]
    | succ k ih =>
      have key := step_tailSum hΘ hr₂ hA hB hΘr hNP hMN (f := fun j => c (k + j)) (hc c k)
      simp only [add_zero] at key
      rw [hrec, map_smul, map_add, comm_apply hC, ih, key]
      exact congrArg (tailSum N Θ) (funext fun j => congrArg (⇑c) (by omega))
  have hw := rec_formula (Θ⁻¹ • M) (fun k => y k - Pu (y k)) (fun k => Θ⁻¹ • (c k - Pu (c k)))
    (fun k => by
      simp only [hrec, map_smul, map_add, smul_apply, map_sub, comm_apply hC,
        smul_sub, smul_add]
      abel) n
  simp only [h0] at hw
  have hsum_le : ∑ m ∈ Finset.range n, (r₁ / Θ) ^ (n - 1 - m) ≤ (1 - r₁ / Θ)⁻¹ := by
    have e := Finset.sum_range_reflect (fun i => (r₁ / Θ) ^ i) n
    rw [e]
    have g := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hρ0 hρ1
    simpa using g
  have hwn : ‖y n - Pu (y n)‖ ≤ K * ‖x₀‖ + Θ⁻¹ * K * (1 - r₁ / Θ)⁻¹ * ‖c‖ := by
    rw [hw]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · calc _ ≤ K * (r₁ / Θ) ^ n * ‖x₀‖ := norm_pow_quot_le hΘ hdec n x₀
        _ ≤ K * 1 * ‖x₀‖ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_one₀ hρ0 hρ1.le) hK) (norm_nonneg _)
        _ = K * ‖x₀‖ := by ring
    · calc _ ≤ ∑ m ∈ Finset.range n, Θ⁻¹ * K * ‖c‖ * (r₁ / Θ) ^ (n - 1 - m) := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
            rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hΘ.le)]
            calc Θ⁻¹ * ‖((Θ⁻¹ • M) ^ (n - 1 - m)) (c m - Pu (c m))‖
                ≤ Θ⁻¹ * (K * (r₁ / Θ) ^ (n - 1 - m) * ‖c m‖) :=
                  mul_le_mul_of_nonneg_left (norm_pow_quot_le hΘ hdec _ _) (inv_nonneg.mpr hΘ.le)
              _ ≤ Θ⁻¹ * (K * (r₁ / Θ) ^ (n - 1 - m) * ‖c‖) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hc0 c m)
                    (mul_nonneg hK (pow_nonneg hρ0 _))) (inv_nonneg.mpr hΘ.le)
              _ = Θ⁻¹ * K * ‖c‖ * (r₁ / Θ) ^ (n - 1 - m) := by ring
        _ = Θ⁻¹ * K * ‖c‖ * ∑ m ∈ Finset.range n, (r₁ / Θ) ^ (n - 1 - m) := by rw [Finset.mul_sum]
        _ ≤ Θ⁻¹ * K * ‖c‖ * (1 - r₁ / Θ)⁻¹ := mul_le_mul_of_nonneg_left hsum_le
            (mul_nonneg (mul_nonneg (inv_nonneg.mpr hΘ.le) hK) (norm_nonneg _))
        _ = Θ⁻¹ * K * (1 - r₁ / Θ)⁻¹ * ‖c‖ := by ring
  have hPn : ‖Pu (y n)‖ ≤ K * ‖Pu‖ * r₂⁻¹ * (1 - Θ / r₂)⁻¹ * ‖c‖ := by
    rw [hPy n]
    calc _ ≤ _ := norm_tailSum_le hΘ hr₂ hA hB hΘr (hc c n)
      _ = K * ‖Pu‖ * r₂⁻¹ * (1 - Θ / r₂)⁻¹ * ‖c‖ := by ring
  have hCU : 0 ≤ K * ‖Pu‖ * r₂⁻¹ * (1 - Θ / r₂)⁻¹ :=
    mul_nonneg (mul_nonneg hA (inv_nonneg.mpr hr₂.le)) (inv_nonneg.mpr (sub_pos.mpr hσ1).le)
  have hK2 : 0 ≤ Θ⁻¹ * K * (1 - r₁ / Θ)⁻¹ :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr hΘ.le) hK) (inv_nonneg.mpr (sub_pos.mpr hρ1).le)
  calc ‖y n‖ = ‖Pu (y n) + (y n - Pu (y n))‖ := by congr 1; abel
    _ ≤ ‖Pu (y n)‖ + ‖y n - Pu (y n)‖ := norm_add_le _ _
    _ ≤ K * ‖Pu‖ * r₂⁻¹ * (1 - Θ / r₂)⁻¹ * ‖c‖ +
        (K * ‖x₀‖ + Θ⁻¹ * K * (1 - r₁ / Θ)⁻¹ * ‖c‖) := add_le_add hPn hwn
    _ ≤ (K * ‖Pu‖ * r₂⁻¹ * (1 - Θ / r₂)⁻¹ + K + Θ⁻¹ * K * (1 - r₁ / Θ)⁻¹) * (‖x₀‖ + ‖c‖) := by
        nlinarith [mul_nonneg hCU (norm_nonneg x₀), mul_nonneg hK (norm_nonneg c),
          mul_nonneg hK2 (norm_nonneg x₀)]

end Breakdown
