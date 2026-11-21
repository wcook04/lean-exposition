import Breakdown.Torus.Lattice

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown.Periodic

namespace Internal

theorem heat_apply (t : ℝ) (x : V) (k : Lattice) :
    ((heat t x : V) : Seq) k = heatFactor t k • (x : Seq) k := rfl

theorem kernel_apply (τ : ℝ) (u v : V) (k : Lattice) :
    ((kernel τ u v : V) : Seq) k = kernelSeq τ u v k := rfl

theorem weight_pos (k : Lattice) : 0 < weight k := by
  unfold weight; positivity

theorem sqrt_weight_pos (k : Lattice) : 0 < Real.sqrt (weight k) :=
  Real.sqrt_pos.mpr (weight_pos k)

theorem heatFactor_nonneg (t : ℝ) (k : Lattice) : 0 ≤ heatFactor t k :=
  (Real.exp_pos _).le

theorem heatFactor_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (k : Lattice) :
    heatFactor (s + t) k = heatFactor s k * heatFactor t k := by
  unfold heatFactor
  rw [max_eq_left (add_nonneg hs ht), max_eq_left hs, max_eq_left ht, ← Real.exp_add]
  ring_nf

theorem heatFactor_anti {s t : ℝ} (h : s ≤ t) (k : Lattice) : heatFactor t k ≤ heatFactor s k := by
  unfold heatFactor
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  exact mul_le_mul_of_nonneg_left (max_le_max h le_rfl) (by positivity)

theorem continuous_heatFactor (k : Lattice) : Continuous fun t => heatFactor t k := by
  unfold heatFactor
  exact Real.continuous_exp.comp ((continuous_const.mul (continuous_id.max continuous_const)).neg)

theorem two_toReal_pos : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num

theorem norm_sq_seq (a : Seq) : ‖a‖ ^ 2 = ∑' k, ‖a k‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum two_toReal_pos a
  simpa [Real.rpow_two] using this

theorem summable_sq (a : Seq) : Summable fun k => ‖a k‖ ^ 2 := by
  have := (lp.memℓp a).summable two_toReal_pos
  simpa [Real.rpow_two] using this

theorem norm_le_of_le {a b : Seq} (h : ∀ k, ‖a k‖ ≤ ‖b k‖) : ‖a‖ ≤ ‖b‖ := by
  apply lp.norm_le_of_tsum_le two_toReal_pos (norm_nonneg _)
  rw [lp.norm_rpow_eq_tsum two_toReal_pos]
  exact Summable.tsum_le_tsum (fun k => Real.rpow_le_rpow (norm_nonneg _) (h k) two_toReal_pos.le)
    ((lp.memℓp a).summable two_toReal_pos) ((lp.memℓp b).summable two_toReal_pos)

theorem tendsto_seq {α : Type*} {l : Filter α} {F : α → Seq} {G : Seq} {b : Lattice → ℝ}
    (hb : Summable fun k => b k ^ 2)
    (hF : ∀ k, Tendsto (fun t => F t k) l (𝓝 (G k)))
    (hbound : ∀ᶠ t in l, ∀ k, ‖F t k‖ ≤ b k) : Tendsto F l (𝓝 G) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  have hG : ∀ k, ‖G k‖ ≤ b k := fun k =>
    le_of_tendsto ((hF k).norm) (hbound.mono fun t h => h k)
  have key : Tendsto (fun t => ‖F t - G‖ ^ 2) l (𝓝 0) := by
    simp_rw [norm_sq_seq]
    have h0 : (0 : ℝ) = ∑' k : Lattice, ‖(0 : Coef)‖ ^ 2 := by simp
    rw [h0]
    apply tendsto_tsum_of_dominated_convergence (bound := fun k => 4 * b k ^ 2) (hb.mul_left 4)
    · intro k
      have := (((hF k).sub (tendsto_const_nhds (x := G k))).norm).pow 2
      simpa [lp.coeFn_sub] using this
    · filter_upwards [hbound] with t ht k
      rw [lp.coeFn_sub, Pi.sub_apply, norm_pow, norm_norm]
      have h1 : ‖F t k - G k‖ ≤ 2 * b k := by
        linarith [norm_sub_le (F t k) (G k), ht k, hG k]
      calc ‖F t k - G k‖ ^ 2 ≤ (2 * b k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = 4 * b k ^ 2 := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have := key.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

theorem freq_apply (k : Lattice) (i : Fin 3) : (freq k) i = (k i : ℝ) := by
  simp [freq, unitVector, Pi.single_apply]

theorem norm_freq_sq (k : Lattice) : ‖freq k‖ ^ 2 = ∑ i, ((k i : ℝ)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [freq_apply]

theorem norm_latVec_sq (k : Lattice) : ‖latVec k‖ ^ 2 = ∑ i, ((k i : ℝ)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [latVec, Complex.norm_intCast, sq_abs]

theorem norm_latVec (k : Lattice) : ‖latVec k‖ = ‖freq k‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (latVec k)), ← Real.sqrt_sq (norm_nonneg (freq k)), norm_latVec_sq,
    norm_freq_sq]

theorem divPairing_eq_inner (k : Lattice) (c : Coef) : divPairing k c = inner ℂ (latVec k) c := by
  simp only [divPairing, latVec, PiLp.inner_apply]
  simp [mul_comm]

theorem norm_divPairing_le (k : Lattice) (c : Coef) : ‖divPairing k c‖ ≤ ‖freq k‖ * ‖c‖ := by
  rw [divPairing_eq_inner, ← norm_latVec]
  exact norm_inner_le_norm _ _

theorem norm_proj_le (k : Lattice) (c : Coef) :
    ‖(divPairing k c / ((‖freq k‖ ^ 2 : ℝ) : ℂ)) • latVec k‖ ≤ ‖c‖ := by
  rw [norm_smul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_latVec]
  rcases eq_or_lt_of_le (norm_nonneg (freq k)) with h | h
  · rw [← h]; simp
  · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    calc ‖divPairing k c‖ * ‖freq k‖ ≤ ‖freq k‖ * ‖c‖ * ‖freq k‖ := by
          gcongr; exact norm_divPairing_le k c
      _ = ‖c‖ * ‖freq k‖ ^ 2 := by ring

theorem norm_divFree_le (k : Lattice) (c : Coef) : ‖divFree k c‖ ≤ 2 * ‖c‖ := by
  unfold divFree
  split_ifs with hk
  · linarith [norm_nonneg c]
  · calc ‖c - (divPairing k c / ((‖freq k‖ ^ 2 : ℝ) : ℂ)) • latVec k‖
        ≤ ‖c‖ + ‖(divPairing k c / ((‖freq k‖ ^ 2 : ℝ) : ℂ)) • latVec k‖ := norm_sub_le _ _
      _ ≤ ‖c‖ + ‖c‖ := by gcongr; exact norm_proj_le k c
      _ = 2 * ‖c‖ := by ring

theorem norm_eq_sqrt_weight_mul (u : V) (k : Lattice) :
    ‖(u : Seq) k‖ = Real.sqrt (weight k) * ‖coeff u k‖ := by
  unfold coeff
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (sqrt_weight_pos k), ← mul_assoc,
    mul_inv_cancel₀ (sqrt_weight_pos k).ne', one_mul]

theorem norm_coeff_le (u : V) (k : Lattice) : ‖coeff u k‖ ≤ ‖(u : Seq) k‖ := by
  rw [norm_eq_sqrt_weight_mul]
  have : 1 ≤ Real.sqrt (weight k) := by
    rw [Real.one_le_sqrt]; unfold weight; nlinarith [sq_nonneg ‖freq k‖, sq_nonneg π]
  nlinarith [norm_nonneg (coeff u k)]

theorem freq_mul_coeff_le (u : V) (k : Lattice) :
    2 * π * ‖freq k‖ * ‖coeff u k‖ ≤ ‖(u : Seq) k‖ := by
  rw [norm_eq_sqrt_weight_mul]
  have h : 2 * π * ‖freq k‖ ≤ Real.sqrt (weight k) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * π * ‖freq k‖)]
    apply Real.sqrt_le_sqrt
    unfold weight; nlinarith
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

def advBound (u v : V) : ℝ := (∑' j, ‖(u : Seq) j‖ ^ 2 + ∑' j, ‖(v : Seq) j‖ ^ 2) / 2

theorem advBound_comm (u v : V) : advBound v u = advBound u v := by
  unfold advBound; ring

theorem advBound_nonneg (u v : V) : 0 ≤ advBound u v := by
  unfold advBound
  have h1 : (0 : ℝ) ≤ ∑' j, ‖(u : Seq) j‖ ^ 2 := tsum_nonneg fun j => sq_nonneg _
  have h2 : (0 : ℝ) ≤ ∑' j, ‖(v : Seq) j‖ ^ 2 := tsum_nonneg fun j => sq_nonneg _
  linarith

theorem norm_advCoef_le (u v : V) (k : Lattice) : ‖advCoef u v k‖ ≤ advBound u v := by
  unfold advCoef advBound
  have hu : HasSum (fun j => ‖(u : Seq) (k - j)‖ ^ 2) (∑' j, ‖(u : Seq) j‖ ^ 2) :=
    (Equiv.subLeft k).hasSum_iff.mpr (summable_sq (u : Seq)).hasSum
  have hv := (summable_sq (v : Seq)).hasSum
  refine tsum_of_norm_bounded ((hu.add hv).div_const 2) fun j => ?_
  have e1 : ‖(((2 * π : ℝ) : ℂ) * Complex.I * divPairing j (coeff u (k - j))) • coeff v j‖ =
      2 * π * ‖divPairing j (coeff u (k - j))‖ * ‖coeff v j‖ := by
    rw [norm_smul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    ring
  rw [e1]
  calc 2 * π * ‖divPairing j (coeff u (k - j))‖ * ‖coeff v j‖
      ≤ 2 * π * (‖freq j‖ * ‖coeff u (k - j)‖) * ‖coeff v j‖ := by
        gcongr; exact norm_divPairing_le _ _
    _ = ‖coeff u (k - j)‖ * (2 * π * ‖freq j‖ * ‖coeff v j‖) := by ring
    _ ≤ ‖(u : Seq) (k - j)‖ * ‖(v : Seq) j‖ :=
        mul_le_mul (norm_coeff_le u _) (freq_mul_coeff_le v j) (by positivity) (norm_nonneg _)
    _ ≤ (‖(u : Seq) (k - j)‖ ^ 2 + ‖(v : Seq) j‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖(u : Seq) (k - j)‖ - ‖(v : Seq) j‖)]

theorem summable_expSq {c : ℝ} (hc : 0 < c) : Summable fun n : ℤ => Real.exp (-(c * (n : ℝ) ^ 2)) := by
  have hgeo : Summable fun n : ℕ => Real.exp (-c) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hc))
  have hle : ∀ n : ℕ, Real.exp (-(c * (n : ℝ) ^ 2)) ≤ Real.exp (-c) ^ n := fun n => by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h1 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero n
    nlinarith
  refine summable_int_iff_summable_nat_and_neg.mpr ⟨?_, ?_⟩
  · exact Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => by simpa using hle n) hgeo
  · exact Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => by simpa using hle n) hgeo

theorem summable_prod_fin {g : ℤ → ℝ} (hg : Summable g) (hg0 : 0 ≤ g) :
    ∀ n : ℕ, Summable fun k : Fin n → ℤ => ∏ i, g (k i)
  | 0 => Summable.of_finite
  | n + 1 => by
    have h := hg.mul_of_nonneg (summable_prod_fin hg hg0 n) hg0
      (fun k => Finset.prod_nonneg fun i _ => hg0 _)
    rw [← (Fin.consEquiv fun _ => ℤ).summable_iff]
    exact h.congr fun p => by simp [Fin.consEquiv, Fin.prod_univ_succ]

theorem summable_exp_freq {c : ℝ} (hc : 0 < c) :
    Summable fun k : Lattice => Real.exp (-(c * ‖freq k‖ ^ 2)) := by
  refine (summable_prod_fin (summable_expSq hc) (fun n => (Real.exp_pos _).le) 3).congr fun k => ?_
  rw [norm_freq_sq, Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]

theorem weight_heat_le {τ : ℝ} (hτ : 0 < τ) (k : Lattice) :
    weight k * heatFactor τ k ^ 2 ≤ (1 + 1 / τ) * Real.exp (-((4 * π ^ 2 * τ) * ‖freq k‖ ^ 2)) := by
  have hX : 0 ≤ 4 * π ^ 2 * ‖freq k‖ ^ 2 := by positivity
  have e2 : (4 * π ^ 2 * τ) * ‖freq k‖ ^ 2 = 4 * π ^ 2 * ‖freq k‖ ^ 2 * τ := by ring
  unfold weight heatFactor
  rw [max_eq_left hτ.le, e2]
  set X := 4 * π ^ 2 * ‖freq k‖ ^ 2
  have e1 : Real.exp (X * τ) * Real.exp (-(X * τ)) = 1 := by rw [← Real.exp_add]; simp
  have hE := Real.add_one_le_exp (X * τ)
  have h3 : 1 / τ * (X * τ) = X := by field_simp
  have h2 : (1 + 1 / τ) * (X * τ + 1) ≤ (1 + 1 / τ) * Real.exp (X * τ) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  have key : (1 + 1 / τ) * (X * τ + 1) = X * τ + 1 + 1 / τ * (X * τ) + 1 / τ := by ring
  rw [key, h3] at h2
  have h1 : 1 + X ≤ (1 + 1 / τ) * Real.exp (X * τ) := by
    linarith [mul_nonneg hX hτ.le, (one_div_pos.mpr hτ).le]
  calc (1 + X) * Real.exp (-(X * τ)) ^ 2 = ((1 + X) * Real.exp (-(X * τ))) * Real.exp (-(X * τ)) := by
        ring
    _ ≤ ((1 + 1 / τ) * Real.exp (X * τ) * Real.exp (-(X * τ))) * Real.exp (-(X * τ)) := by
        gcongr
    _ = (1 + 1 / τ) * Real.exp (-(X * τ)) := by rw [mul_assoc (1 + 1 / τ), e1, mul_one]

theorem summable_weight_heat {τ : ℝ} (hτ : 0 < τ) :
    Summable fun k => weight k * heatFactor τ k ^ 2 :=
  Summable.of_nonneg_of_le (fun k => mul_nonneg (weight_pos k).le (sq_nonneg _))
    (weight_heat_le hτ) ((summable_exp_freq (by positivity)).mul_left _)

theorem norm_kernelSeq_le (u v : V) {τ₁ τ : ℝ} (h₁ : 0 < τ₁) (h : τ₁ ≤ τ) (k : Lattice) :
    ‖kernelSeq τ u v k‖ ≤ 2 * advBound u v * (Real.sqrt (weight k) * heatFactor τ₁ k) := by
  unfold kernelSeq
  rw [if_pos (h₁.trans_le h), norm_smul, Real.norm_eq_abs]
  have ha : |(-(1 / 2) * Real.sqrt (weight k) * heatFactor τ k)| =
      1 / 2 * (Real.sqrt (weight k) * heatFactor τ k) := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (heatFactor_nonneg _ _)]
    ring
  have hL : ‖divFree k (advCoef u v k + advCoef v u k)‖ ≤ 4 * advBound u v := by
    calc ‖divFree k (advCoef u v k + advCoef v u k)‖ ≤ 2 * ‖advCoef u v k + advCoef v u k‖ :=
          norm_divFree_le _ _
      _ ≤ 2 * (‖advCoef u v k‖ + ‖advCoef v u k‖) := by gcongr; exact norm_add_le _ _
      _ ≤ 2 * (advBound u v + advBound u v) := by
          gcongr
          · exact norm_advCoef_le u v k
          · rw [← advBound_comm]; exact norm_advCoef_le v u k
      _ = 4 * advBound u v := by ring
  rw [ha]
  have hB := advBound_nonneg u v
  calc 1 / 2 * (Real.sqrt (weight k) * heatFactor τ k) * ‖divFree k (advCoef u v k + advCoef v u k)‖
      ≤ 1 / 2 * (Real.sqrt (weight k) * heatFactor τ₁ k) * (4 * advBound u v) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (heatFactor_anti h k)
          (Real.sqrt_nonneg _)) (by norm_num)) hL (norm_nonneg _) ?_
        exact mul_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg _) (heatFactor_nonneg _ _))
    _ = 2 * advBound u v * (Real.sqrt (weight k) * heatFactor τ₁ k) := by ring

end Internal

theorem heat_zero : heat 0 = ContinuousLinearMap.id ℝ V := by
  ext1 x
  apply Subtype.ext
  apply lp.ext
  funext k
  rw [Internal.heat_apply]
  simp [heatFactor]

theorem heat_add (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) : heat (s + t) = (heat s).comp (heat t) := by
  ext1 x
  apply Subtype.ext
  apply lp.ext
  funext k
  rw [ContinuousLinearMap.comp_apply, Internal.heat_apply, Internal.heat_apply, Internal.heat_apply,
    smul_smul, Internal.heatFactor_add hs ht]

theorem norm_heat_le (t : ℝ) : ‖heat t‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  show ‖((heat t x : V) : Seq)‖ ≤ ‖(x : Seq)‖
  apply Internal.norm_le_of_le
  intro k
  rw [Internal.heat_apply, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) (by simpa using abs_heatFactor_le t k)

theorem heat_continuousOn (x : V) : ContinuousOn (fun t => heat t x) (Ici 0) := by
  refine Continuous.continuousOn ?_
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, tendsto_subtype_rng]
  apply Internal.tendsto_seq (b := fun k => ‖(x : Seq) k‖) (Internal.summable_sq _)
  · intro k
    simp only [Internal.heat_apply]
    exact ((Internal.continuous_heatFactor k).tendsto t₀).smul_const _
  · refine Eventually.of_forall fun t k => ?_
    rw [Internal.heat_apply, norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by simpa using abs_heatFactor_le t k)

theorem kernel_symm (τ : ℝ) (u v : V) : kernel τ u v = kernel τ v u := by
  apply Subtype.ext
  apply lp.ext
  funext k
  rw [Internal.kernel_apply, Internal.kernel_apply]
  unfold kernelSeq
  rw [add_comm (advCoef u v k)]

theorem kernel_continuousOn (u v : V) : ContinuousOn (fun τ => kernel τ u v) (Ioi 0) := by
  intro τ₀ hτ₀
  have hτ₀' : (0 : ℝ) < τ₀ := hτ₀
  rw [ContinuousWithinAt, tendsto_subtype_rng]
  have hev : ∀ᶠ τ in 𝓝[Ioi 0] τ₀, τ₀ / 2 ≤ τ :=
    nhdsWithin_le_nhds (Ici_mem_nhds (half_lt_self hτ₀'))
  apply Internal.tendsto_seq
    (b := fun k => 2 * Internal.advBound u v * (Real.sqrt (weight k) * heatFactor (τ₀ / 2) k))
  · refine ((Internal.summable_weight_heat (half_pos hτ₀')).mul_left
      ((2 * Internal.advBound u v) ^ 2)).congr fun k => ?_
    simp only [mul_pow, Real.sq_sqrt (Internal.weight_pos k).le]
  · intro k
    simp only [Internal.kernel_apply]
    have e : kernelSeq τ₀ u v k =
        (-(1 / 2) * Real.sqrt (weight k) * heatFactor τ₀ k) • divFree k (advCoef u v k + advCoef v u k) := by
      simp only [kernelSeq, if_pos hτ₀']
    rw [e]
    have hc : Tendsto (fun τ => (-(1 / 2) * Real.sqrt (weight k) * heatFactor τ k) •
        divFree k (advCoef u v k + advCoef v u k)) (𝓝[Ioi 0] τ₀)
        (𝓝 ((-(1 / 2) * Real.sqrt (weight k) * heatFactor τ₀ k) •
          divFree k (advCoef u v k + advCoef v u k))) :=
      (((continuous_const.mul (Internal.continuous_heatFactor k)).smul continuous_const).tendsto
        τ₀).mono_left nhdsWithin_le_nhds
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτ' : (0 : ℝ) < τ := hτ
    simp only [kernelSeq, if_pos hτ']
  · filter_upwards [hev] with τ hτ k
    rw [Internal.kernel_apply]
    exact Internal.norm_kernelSeq_le u v (half_pos hτ₀') hτ k

theorem heat_kernel (s τ : ℝ) (hs : 0 ≤ s) (hτ : 0 < τ) (u v : V) :
    heat s (kernel τ u v) = kernel (s + τ) u v := by
  apply Subtype.ext
  apply lp.ext
  funext k
  rw [Internal.heat_apply, Internal.kernel_apply, Internal.kernel_apply]
  unfold kernelSeq
  rw [if_pos hτ, if_pos (add_pos_of_nonneg_of_pos hs hτ), smul_smul, Internal.heatFactor_add hs hτ.le]
  congr 1
  ring

theorem coeff_heat (t : ℝ) (u : V) (k : Lattice) : coeff (heat t u) k = heatFactor t k • coeff u k := by
  unfold coeff
  rw [Internal.heat_apply, smul_comm]

theorem coeff_kernel (τ : ℝ) (hτ : 0 < τ) (u v : V) (k : Lattice) :
    coeff (kernel τ u v) k = (-(1 / 2) * heatFactor τ k) • divFree k (advCoef u v k + advCoef v u k) := by
  unfold coeff
  rw [Internal.kernel_apply]
  unfold kernelSeq
  rw [if_pos hτ, smul_smul]
  congr 1
  have := (Internal.sqrt_weight_pos k).ne'
  field_simp

theorem norm_sq_eq_tsum (u : V) : ‖u‖ ^ 2 = ∑' k, weight k * ‖coeff u k‖ ^ 2 := by
  show ‖(u : Seq)‖ ^ 2 = _
  rw [Internal.norm_sq_seq]
  congr 1
  funext k
  unfold coeff
  rw [norm_smul, mul_pow, norm_inv, Real.norm_eq_abs, abs_of_pos (Internal.sqrt_weight_pos k), inv_pow,
    Real.sq_sqrt (Internal.weight_pos k).le, ← mul_assoc, mul_inv_cancel₀ (Internal.weight_pos k).ne',
    one_mul]

theorem coeff_injective {u v : V} (h : ∀ k, coeff u k = coeff v k) : u = v := by
  apply Subtype.ext
  apply lp.ext
  funext k
  have := congrArg (fun c => Real.sqrt (weight k) • c) (h k)
  simpa [coeff, smul_smul, mul_inv_cancel₀ (Internal.sqrt_weight_pos k).ne'] using this

end Breakdown.Periodic
