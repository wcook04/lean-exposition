import Breakdown.FracCert.StKernel

open scoped ContDiff
open MeasureTheory Real

noncomputable section

namespace Breakdown.FracCert

namespace KernelDecayInternal

section

open scoped Nat Topology
open Set Filter

lemma poly_exp_bound (M : ℕ) (c0 : ℝ) (hc0 : 0 < c0) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ s : ℝ, 0 ≤ s → (1 + s) ^ M * Real.exp (-(s * c0)) ≤ R := by
  refine ⟨(1 + 1 / c0) ^ M * (2 ^ M * (1 + M !)), by positivity, fun s hs => ?_⟩
  set y := s * c0 with hy
  have hy0 : 0 ≤ y := by positivity
  have h1 : (1 + y) ^ M ≤ 2 ^ M * (1 + y ^ M) := by
    rcases le_total y 1 with h | h
    · calc (1 + y) ^ M ≤ 2 ^ M := pow_le_pow_left₀ (by positivity) (by linarith) M
        _ ≤ 2 ^ M * (1 + y ^ M) :=
          le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg hy0 M])
    · calc (1 + y) ^ M ≤ (2 * y) ^ M := pow_le_pow_left₀ (by positivity) (by linarith) M
        _ = 2 ^ M * y ^ M := mul_pow _ _ _
        _ ≤ 2 ^ M * (1 + y ^ M) := by gcongr; linarith
  have h2 : y ^ M ≤ M ! * Real.exp y := by
    have := Real.pow_div_factorial_le_exp (x := y) hy0 M
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hs1 : 1 + s ≤ (1 + 1 / c0) * (1 + y) := by
    rw [hy]
    have : (1 + 1 / c0) * (1 + s * c0) = 1 + s * c0 + 1 / c0 + s := by field_simp; ring
    rw [this]
    have : 0 ≤ s * c0 := by positivity
    have : 0 ≤ 1 / c0 := by positivity
    linarith
  have he : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hey : y ^ M * Real.exp (-y) ≤ M ! := by
    calc y ^ M * Real.exp (-y) ≤ (M ! * Real.exp y) * Real.exp (-y) := by gcongr
      _ = M ! := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  calc (1 + s) ^ M * Real.exp (-y) ≤ ((1 + 1 / c0) * (1 + y)) ^ M * Real.exp (-y) := by
        gcongr
    _ = (1 + 1 / c0) ^ M * ((1 + y) ^ M * Real.exp (-y)) := by rw [mul_pow, mul_assoc]
    _ ≤ (1 + 1 / c0) ^ M * ((2 ^ M * (1 + y ^ M)) * Real.exp (-y)) := by gcongr
    _ = (1 + 1 / c0) ^ M * (2 ^ M * (Real.exp (-y) + y ^ M * Real.exp (-y))) := by ring
    _ ≤ (1 + 1 / c0) ^ M * (2 ^ M * (1 + M !)) := by gcongr

lemma uniform_bound_on {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Space → E)
    (U K : Set Space) (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (M : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i ≤ M, ∀ x ∈ K, ‖iteratedFDerivWithin ℝ i f U x‖ ≤ B := by
  have h : ∀ i : ℕ, ∃ B : ℝ, ∀ x ∈ K, ‖iteratedFDerivWithin ℝ i f U x‖ ≤ B := fun i =>
    hK.exists_bound_of_continuousOn
      ((hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hU.uniqueDiffOn).mono hKU)
  choose B hB using h
  refine ⟨∑ i ∈ Finset.range (M + 1), |B i|, Finset.sum_nonneg (fun _ _ => abs_nonneg _),
    fun i hi x hx => (hB i x hx).trans ((le_abs_self _).trans ?_)⟩
  exact Finset.single_le_sum (f := fun i => |B i|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.mpr (by omega))

lemma norm_iteratedFDeriv_exp_mul (s : ℝ) (i : ℕ) (u : ℝ) :
    ‖iteratedFDeriv ℝ i (fun u : ℝ => Real.exp (-s * u)) u‖ = |s| ^ i * Real.exp (-s * u) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul, norm_mul, norm_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_of_pos (Real.exp_pos _)]

lemma piece_symbol_bound (α : ℝ) (hα : 0 < α) (θ : Space → ℝ) (hθ : IsRingCutoff θ)
    (i j k : Fin 3) (M : ℕ) :
    ∃ A : ℝ, ∀ s : ℝ, 0 < s →
      ContDiff ℝ ∞ (fun ξ => (θ ξ : ℂ) * projDivSymbol α s i j k ξ) ∧
      ∀ q ≤ M, ∀ ξ, ‖iteratedFDeriv ℝ q (fun ξ => (θ ξ : ℂ) * projDivSymbol α s i j k ξ) ξ‖ ≤ A := by
  set U : Set Space := {ξ | 1 / 4 < ‖ξ‖} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_norm
  set K : Set Space := {ξ | 1 / 2 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2} with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall (0 : Space) 2).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)) (fun ξ h => ?_)
    simpa using h.2
  have hKU : K ⊆ U := fun ξ h => by
    show 1 / 4 < ‖ξ‖
    linarith [h.1]
  set P : Space → ℂ := fun ξ => (θ ξ : ℂ) * (((2 * π * ξ k : ℝ) : ℂ) * Complex.I *
    (((if i = j then (1 : ℝ) else 0) - ξ i * ξ j / ‖ξ‖ ^ 2 : ℝ) : ℂ)) with hP
  set ph : Space → ℝ := fun ξ => (2 * π * ‖ξ‖) ^ (2 * α) with hph
  have hm : ∀ s : ℝ, (fun ξ => (θ ξ : ℂ) * projDivSymbol α s i j k ξ) =
      fun ξ => P ξ * (((Real.exp (-s * ph ξ)) : ℝ) : ℂ) := by
    intro s
    funext ξ
    simp only [P, ph, projDivSymbol, neg_mul]
    ring
  have hnorm : ∀ x ∈ U, ContDiffAt ℝ ∞ (fun ξ : Space => ‖ξ‖) x := by
    intro x hx
    have : x ≠ 0 := by
      intro h0
      have : (1 : ℝ) / 4 < ‖x‖ := hx
      rw [h0, norm_zero] at this
      linarith
    exact contDiffAt_norm ℝ this
  have hphU : ContDiffOn ℝ ∞ ph U := by
    intro x hx
    refine ContDiffAt.contDiffWithinAt ?_
    refine ContDiffAt.rpow_const_of_ne (contDiffAt_const.mul (hnorm x hx)) ?_
    have : (1 : ℝ) / 4 < ‖x‖ := hx
    have : 0 < 2 * π * ‖x‖ := by positivity
    exact this.ne'
  have hPU : ContDiffOn ℝ ∞ P U := by
    intro x hx
    refine ContDiffAt.contDiffWithinAt ?_
    have hx0 : ‖x‖ ^ 2 ≠ 0 := by
      have : (1 : ℝ) / 4 < ‖x‖ := hx
      positivity
    have hco : ∀ a : Fin 3, ContDiff ℝ ∞ (fun ξ : Space => ξ a) := fun a =>
      (EuclideanSpace.proj a : Space →L[ℝ] ℝ).contDiff
    have hq : ContDiffAt ℝ ∞ (fun ξ : Space => ξ i * ξ j / ‖ξ‖ ^ 2) x :=
      (((hco i).mul (hco j)).contDiffAt).div ((contDiff_norm_sq ℝ).contDiffAt) hx0
    have hr : ContDiffAt ℝ ∞ (fun ξ : Space => ((2 * π * ξ k : ℝ)) *
        ((if i = j then (1 : ℝ) else 0) - ξ i * ξ j / ‖ξ‖ ^ 2)) x :=
      (contDiffAt_const.mul (hco k).contDiffAt).mul (contDiffAt_const.sub hq)
    have hθc : ContDiff ℝ ∞ (fun ξ => (θ ξ : ℂ)) := Complex.ofRealCLM.contDiff.comp hθ.1
    have hrc : ContDiffAt ℝ ∞ (fun ξ : Space => ((((2 * π * ξ k : ℝ)) *
        ((if i = j then (1 : ℝ) else 0) - ξ i * ξ j / ‖ξ‖ ^ 2) : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hr
    have := hθc.contDiffAt.mul (hrc.mul (contDiffAt_const (c := Complex.I)))
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun ξ => ?_))
    simp only [P]
    push_cast
    ring
  have hEU : ∀ s : ℝ, ContDiffOn ℝ ∞ (fun ξ => (((Real.exp (-s * ph ξ)) : ℝ) : ℂ)) U := by
    intro s
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn
      (Real.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul hphU))
  have hmU : ∀ s : ℝ, ContDiffOn ℝ ∞ (fun ξ => (θ ξ : ℂ) * projDivSymbol α s i j k ξ) U := by
    intro s
    rw [hm s]
    exact hPU.mul (hEU s)
  have hzero : ∀ s : ℝ, ∀ x : Space, x ∉ K →
      (fun ξ => (θ ξ : ℂ) * projDivSymbol α s i j k ξ) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
    intro s x hx
    have hθ0 : ∀ ξ : Space, (‖ξ‖ < 1 / 2 ∨ 2 < ‖ξ‖) → θ ξ = 0 := by
      intro ξ hξ
      by_contra h
      have := hθ.2.2.1 ξ h
      rcases hξ with h1 | h1 <;> linarith [this.1, this.2]
    have hx' : ‖x‖ < 1 / 2 ∨ 2 < ‖x‖ := by
      by_contra h
      push Not at h
      exact hx ⟨h.1, h.2⟩
    have hopen : IsOpen {ξ : Space | ‖ξ‖ < 1 / 2 ∨ 2 < ‖ξ‖} :=
      (isOpen_lt continuous_norm continuous_const).union (isOpen_lt continuous_const continuous_norm)
    filter_upwards [hopen.mem_nhds hx'] with ξ hξ
    simp [hθ0 ξ hξ]
  have hsmooth : ∀ s : ℝ, ContDiff ℝ ∞ (fun ξ => (θ ξ : ℂ) * projDivSymbol α s i j k ξ) := by
    intro s
    refine contDiff_iff_contDiffAt.2 (fun x => ?_)
    by_cases hx : x ∈ U
    · exact (hmU s).contDiffAt (hUo.mem_nhds hx)
    · have hxK : x ∉ K := fun h => hx (hKU h)
      exact contDiffAt_const.congr_of_eventuallyEq (hzero s x hxK)
  obtain ⟨BP, hBP0, hBP⟩ := uniform_bound_on P U K hPU hUo hKc hKU M
  obtain ⟨Φ, hΦ0, hΦ⟩ := uniform_bound_on ph U K hphU hUo hKc hKU M
  set c0 : ℝ := π ^ (2 * α) with hc0
  have hc0p : 0 < c0 := by positivity
  obtain ⟨R, hR0, hR⟩ := poly_exp_bound M c0 hc0p
  have hphK : ∀ x ∈ K, c0 ≤ ph x := by
    intro x hx
    simp only [ph, c0]
    exact Real.rpow_le_rpow (by positivity) (by nlinarith [hx.1, Real.pi_pos]) (by positivity)
  have hEb : ∀ s : ℝ, 0 < s → ∀ q ≤ M, ∀ x ∈ K,
      ‖iteratedFDerivWithin ℝ q (fun ξ => (((Real.exp (-s * ph ξ)) : ℝ) : ℂ)) U x‖ ≤
        M ! * R * (1 + Φ) ^ M := by
    intro s hs q hq x hx
    have hxU := hKU hx
    have hcomp : (fun ξ => (((Real.exp (-s * ph ξ)) : ℝ) : ℂ)) =
        (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ ((fun u : ℝ => Real.exp (-s * u)) ∘ ph) := rfl
    have hg' : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-s * u)) :=
      Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
    have hg : ContDiffOn ℝ ∞ (fun u : ℝ => Real.exp (-s * u)) univ := hg'.contDiffOn
    have hinner : ContDiffOn ℝ ∞ ((fun u : ℝ => Real.exp (-s * u)) ∘ ph) U :=
      hg'.comp_contDiffOn hphU
    rw [hcomp, LinearIsometry.norm_iteratedFDerivWithin_comp_left (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ)
      (hinner x hxU) hUo.uniqueDiffOn hxU (by exact_mod_cast le_top)]
    have hC : ∀ i' ≤ q, ‖iteratedFDerivWithin ℝ i' (fun u : ℝ => Real.exp (-s * u)) univ (ph x)‖ ≤ R := by
      intro i' hi'
      rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_exp_mul, abs_of_pos hs]
      have h1 : s ^ i' ≤ (1 + s) ^ M := by
        calc s ^ i' ≤ (1 + s) ^ i' := pow_le_pow_left₀ hs.le (by linarith) i'
          _ ≤ (1 + s) ^ M := pow_le_pow_right₀ (by linarith) (by omega)
      have h2 : Real.exp (-s * ph x) ≤ Real.exp (-(s * c0)) := by
        apply Real.exp_le_exp.mpr
        have := hphK x hx
        nlinarith
      calc s ^ i' * Real.exp (-s * ph x) ≤ (1 + s) ^ M * Real.exp (-(s * c0)) := by gcongr
        _ ≤ R := hR s hs.le
    have hD : ∀ i', 1 ≤ i' → i' ≤ q → ‖iteratedFDerivWithin ℝ i' ph U x‖ ≤ (1 + Φ) ^ i' := by
      intro i' h1 h2
      calc ‖iteratedFDerivWithin ℝ i' ph U x‖ ≤ Φ := hΦ i' (by omega) x hx
        _ ≤ 1 + Φ := by linarith
        _ = (1 + Φ) ^ 1 := (pow_one _).symm
        _ ≤ (1 + Φ) ^ i' := pow_le_pow_right₀ (by linarith) h1
    have := norm_iteratedFDerivWithin_comp_le hg hphU (by exact_mod_cast le_top) uniqueDiffOn_univ
      hUo.uniqueDiffOn (mapsTo_univ _ _) hxU hC hD
    calc ‖iteratedFDerivWithin ℝ q ((fun u : ℝ => Real.exp (-s * u)) ∘ ph) U x‖
        ≤ q ! * R * (1 + Φ) ^ q := this
      _ ≤ M ! * R * (1 + Φ) ^ M := by
          gcongr
          all_goals first | exact_mod_cast Nat.factorial_le hq | linarith
  refine ⟨2 ^ M * (BP * (M ! * R * (1 + Φ) ^ M)), fun s hs => ⟨hsmooth s, fun q hq x => ?_⟩⟩
  have hA0 : 0 ≤ 2 ^ M * (BP * (M ! * R * (1 + Φ) ^ M)) := by positivity
  by_cases hx : x ∈ K
  · have hxU := hKU hx
    rw [← iteratedFDerivWithin_of_isOpen q hUo hxU, hm s]
    refine (norm_iteratedFDerivWithin_mul_le hPU (hEU s) hUo.uniqueDiffOn hxU
      (by exact_mod_cast le_top)).trans ?_
    calc ∑ i' ∈ Finset.range (q + 1), (q.choose i' : ℝ) * ‖iteratedFDerivWithin ℝ i' P U x‖ *
          ‖iteratedFDerivWithin ℝ (q - i') (fun ξ => (((Real.exp (-s * ph ξ)) : ℝ) : ℂ)) U x‖
        ≤ ∑ i' ∈ Finset.range (q + 1), (q.choose i' : ℝ) * (BP * (M ! * R * (1 + Φ) ^ M)) := by
          refine Finset.sum_le_sum (fun i' hi' => ?_)
          have hi'' : i' ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')
          rw [mul_assoc]
          gcongr
          · exact hBP i' (by omega) x hx
          · exact hEb s hs (q - i') (by omega) x hx
      _ = 2 ^ q * (BP * (M ! * R * (1 + Φ) ^ M)) := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose q
      _ ≤ 2 ^ M * (BP * (M ! * R * (1 + Φ) ^ M)) := by
          gcongr
          · norm_num
  · rw [((hzero s x hx).iteratedFDeriv ℝ q).eq_of_nhds]
    simpa using hA0

end


lemma symbol_smul (α t : ℝ) (hα : 0 < α) (ht : 0 < t) (i j k : Fin 3) (η : Space) :
    projDivSymbol α t i j k ((t ^ (-(1 / (2 * α)))) • η) =
      ((t ^ (-(1 / (2 * α))) : ℝ) : ℂ) * projDivSymbol α 1 i j k η := by
  set c := t ^ (-(1 / (2 * α))) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos ht _
  have hexp : t * c ^ (2 * α) = 1 := by
    rw [hc, ← Real.rpow_mul ht.le]
    have : -(1 / (2 * α)) * (2 * α) = -1 := by field_simp
    rw [this, Real.rpow_neg_one, mul_inv_cancel₀ ht.ne']
  have hnorm : ‖c • η‖ = c * ‖η‖ := by rw [norm_smul, Real.norm_of_nonneg hc0.le]
  have hpow : (2 * π * (c * ‖η‖)) ^ (2 * α) = c ^ (2 * α) * (2 * π * ‖η‖) ^ (2 * α) := by
    rw [show 2 * π * (c * ‖η‖) = c * (2 * π * ‖η‖) by ring]
    exact Real.mul_rpow hc0.le (by positivity)
  have hfrac : (c * η i) * (c * η j) / (c * ‖η‖) ^ 2 = η i * η j / ‖η‖ ^ 2 := by
    rw [show (c * η i) * (c * η j) = c ^ 2 * (η i * η j) by ring, mul_pow]
    exact mul_div_mul_left _ _ (by positivity)
  have hE : t * (2 * π * (c * ‖η‖)) ^ (2 * α) = 1 * (2 * π * ‖η‖) ^ (2 * α) := by
    rw [hpow, ← mul_assoc, hexp]
  unfold projDivSymbol
  simp only [PiLp.smul_apply, smul_eq_mul, hnorm, hfrac, hE]
  push_cast
  ring

lemma kernel_smul (α t : ℝ) (hα : 0 < α) (ht : 0 < t) (i j k : Fin 3) (x : Space) :
    projDivKernel α t i j k x =
      (((t ^ (-(1 / (2 * α)))) ^ 4 : ℝ) : ℂ) *
        projDivKernel α 1 i j k ((t ^ (-(1 / (2 * α)))) • x) := by
  set c := t ^ (-(1 / (2 * α))) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos ht _
  unfold projDivKernel
  rw [Real.fourierInv_eq', Real.fourierInv_eq']
  have h := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure Space))
    (fun η : Space => Complex.exp ((↑(2 * π * inner ℝ η x) * Complex.I)) •
      projDivSymbol α t i j k η) c
  simp only [finrank_euclideanSpace_fin] at h
  have h2 : ∫ η : Space, Complex.exp ((↑(2 * π * inner ℝ η x) * Complex.I)) •
      projDivSymbol α t i j k η = (c ^ 3 : ℝ) • ∫ η : Space,
        Complex.exp ((↑(2 * π * inner ℝ (c • η) x) * Complex.I)) •
          projDivSymbol α t i j k (c • η) := by
    rw [h, smul_smul, abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), one_smul]
  have hsym : ∀ η : Space, projDivSymbol α t i j k (c • η) =
      (c : ℂ) * projDivSymbol α 1 i j k η := symbol_smul α t hα ht i j k
  rw [h2]
  simp only [hsym, real_inner_smul_left, ← real_inner_smul_right]
  rw [← integral_const_mul, ← integral_smul]
  congr 1
  ext η
  simp only [smul_eq_mul, Complex.real_smul]
  push_cast
  ring

lemma scale_factor (α t : ℝ) (ht : 0 < t) (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (t ^ (-(1 / (2 * α)))) ^ 4 * ((t ^ (-(1 / (2 * α)))) ^ n *
      (1 + t ^ (-(1 / (2 * α))) * r) ^ (-(4 + n : ℝ))) =
      (t ^ (1 / (2 * α)) + r) ^ (-(4 + n : ℝ)) := by
  set g := 1 / (2 * α)
  have hc0 : 0 < t ^ (-g) := Real.rpow_pos_of_pos ht _
  have hg0 : 0 < t ^ g := Real.rpow_pos_of_pos ht _
  have hone : t ^ g * t ^ (-g) = 1 := by
    rw [← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero]
  have hsplit : t ^ g + r = t ^ g * (1 + t ^ (-g) * r) := by
    rw [mul_add, mul_one, ← mul_assoc, hone, one_mul]
  rw [hsplit, Real.mul_rpow hg0.le (by positivity), ← mul_assoc]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hc0, ← Real.rpow_mul ht.le,
    ← Real.rpow_mul ht.le]
  congr 1
  push_cast
  ring

lemma decay_of_unit (α : ℝ) (hα : 0 < α) (i j k : Fin 3)
    (H1 : ContDiff ℝ ∞ (projDivKernel α 1 i j k))
    (H2 : ∀ n : ℕ, ∃ C : ℝ, ∀ x : Space,
      ‖iteratedFDeriv ℝ n (projDivKernel α 1 i j k) x‖ ≤ C * (1 + ‖x‖) ^ (-(4 + n : ℝ))) :
    (∀ t : ℝ, 0 < t → ContDiff ℝ ∞ (projDivKernel α t i j k)) ∧
    ∀ n : ℕ, ∃ C : ℝ, ∀ t : ℝ, 0 < t → ∀ x : Space,
      ‖iteratedFDeriv ℝ n (projDivKernel α t i j k) x‖ ≤
        C * (t ^ (1 / (2 * α)) + ‖x‖) ^ (-(4 + n : ℝ)) := by
  have hfun : ∀ t : ℝ, 0 < t → projDivKernel α t i j k =
      fun x => (((t ^ (-(1 / (2 * α)))) ^ 4 : ℝ) : ℂ) •
        (projDivKernel α 1 i j k ∘ ((t ^ (-(1 / (2 * α)))) • ContinuousLinearMap.id ℝ Space)) x := by
    intro t ht
    funext x
    rw [kernel_smul α t hα ht]
    rfl
  refine ⟨fun t ht => ?_, fun n => ?_⟩
  · rw [hfun t ht]
    exact (H1.comp (ContinuousLinearMap.contDiff _)).const_smul _
  · obtain ⟨C, hC⟩ := H2 n
    refine ⟨C, fun t ht x => ?_⟩
    set c := t ^ (-(1 / (2 * α))) with hc
    have hc0 : 0 < c := Real.rpow_pos_of_pos ht _
    set L : Space →L[ℝ] Space := c • ContinuousLinearMap.id ℝ Space
    have hL : ‖L‖ ≤ c := by
      calc ‖L‖ ≤ ‖c‖ * ‖ContinuousLinearMap.id ℝ Space‖ := norm_smul_le _ _
        _ ≤ ‖c‖ * 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
        _ = c := by rw [mul_one, Real.norm_of_nonneg hc0.le]
    have hcomp : ContDiff ℝ ∞ (projDivKernel α 1 i j k ∘ L) :=
      H1.comp (ContinuousLinearMap.contDiff _)
    have hK : projDivKernel α t i j k = (((c ^ 4 : ℝ)) : ℂ) • (projDivKernel α 1 i j k ∘ L) := by
      funext y
      rw [kernel_smul α t hα ht]
      rfl
    rw [hK, iteratedFDeriv_const_smul_apply (hcomp.contDiffAt.of_le (by exact_mod_cast le_top)),
      L.iteratedFDeriv_comp_right H1 x (by exact_mod_cast le_top), norm_smul]
    have h1 : ‖(iteratedFDeriv ℝ n (projDivKernel α 1 i j k) (L x)).compContinuousLinearMap
        (fun _ => L)‖ ≤ ‖iteratedFDeriv ℝ n (projDivKernel α 1 i j k) (L x)‖ * c ^ n := by
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      gcongr
      calc ∏ _i : Fin n, ‖L‖ ≤ ∏ _i : Fin n, c :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hL)
        _ = c ^ n := by simp
    have hLx : ‖L x‖ = c * ‖x‖ := by
      simp only [L, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply, norm_smul,
        Real.norm_of_nonneg hc0.le]
    have h2 := hC (L x)
    rw [hLx] at h2
    have hnc : ‖(((c ^ 4 : ℝ)) : ℂ)‖ = c ^ 4 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hnc, ← scale_factor α t ht n ‖x‖ (norm_nonneg _)]
    calc c ^ 4 * ‖(iteratedFDeriv ℝ n (projDivKernel α 1 i j k) (L x)).compContinuousLinearMap
          (fun _ => L)‖ ≤ c ^ 4 * (‖iteratedFDeriv ℝ n (projDivKernel α 1 i j k) (L x)‖ * c ^ n) := by
          gcongr
      _ ≤ c ^ 4 * ((C * (1 + c * ‖x‖) ^ (-(4 + n : ℝ))) * c ^ n) := by gcongr
      _ = C * (c ^ 4 * (c ^ n * (1 + c * ‖x‖) ^ (-(4 + n : ℝ)))) := by ring

lemma symbol_smul_gen (α t c : ℝ) (hc0 : 0 < c) (i j k : Fin 3) (η : Space) :
    projDivSymbol α t i j k (c • η) =
      (c : ℂ) * projDivSymbol α (t * c ^ (2 * α)) i j k η := by
  have hnorm : ‖c • η‖ = c * ‖η‖ := by rw [norm_smul, Real.norm_of_nonneg hc0.le]
  have hpow : (2 * π * (c * ‖η‖)) ^ (2 * α) = c ^ (2 * α) * (2 * π * ‖η‖) ^ (2 * α) := by
    rw [show 2 * π * (c * ‖η‖) = c * (2 * π * ‖η‖) by ring]
    exact Real.mul_rpow hc0.le (by positivity)
  have hfrac : (c * η i) * (c * η j) / (c * ‖η‖) ^ 2 = η i * η j / ‖η‖ ^ 2 := by
    rw [show (c * η i) * (c * η j) = c ^ 2 * (η i * η j) by ring, mul_pow]
    exact mul_div_mul_left _ _ (by positivity)
  have hE : t * (2 * π * (c * ‖η‖)) ^ (2 * α) = (t * c ^ (2 * α)) * (2 * π * ‖η‖) ^ (2 * α) := by
    rw [hpow, ← mul_assoc]
  unfold projDivSymbol
  simp only [PiLp.smul_apply, smul_eq_mul, hnorm, hfrac, hE]
  push_cast
  ring

lemma invTransform_smul_gen (f : Space → ℂ) (c : ℝ) (hc0 : 0 < c) (x : Space) :
    FourierTransform.fourierInv f x =
      ((c ^ 3 : ℝ) : ℂ) * FourierTransform.fourierInv (fun η => f (c • η)) (c • x) := by
  rw [Real.fourierInv_eq', Real.fourierInv_eq']
  have h := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure Space))
    (fun η : Space => Complex.exp ((↑(2 * π * inner ℝ η x) * Complex.I)) • f η) c
  simp only [finrank_euclideanSpace_fin] at h
  have h2 : ∫ η : Space, Complex.exp ((↑(2 * π * inner ℝ η x) * Complex.I)) • f η =
      (c ^ 3 : ℝ) • ∫ η : Space,
        Complex.exp ((↑(2 * π * inner ℝ (c • η) x) * Complex.I)) • f (c • η) := by
    rw [h, smul_smul, abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), one_smul]
  rw [h2]
  simp only [real_inner_smul_left, ← real_inner_smul_right, Complex.real_smul]

lemma norm_iteratedFDeriv_scale_le (k : Space → ℂ) (hk : ContDiff ℝ ∞ k) (a c : ℝ)
    (hc0 : 0 < c) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (fun y => (a : ℂ) * k (c • y)) x‖ ≤
      |a| * (c ^ n * ‖iteratedFDeriv ℝ n k (c • x)‖) := by
  set L : Space →L[ℝ] Space := c • ContinuousLinearMap.id ℝ Space
  have hL : ‖L‖ ≤ c := by
    calc ‖L‖ ≤ ‖c‖ * ‖ContinuousLinearMap.id ℝ Space‖ := norm_smul_le _ _
      _ ≤ ‖c‖ * 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
      _ = c := by rw [mul_one, Real.norm_of_nonneg hc0.le]
  have hcomp : ContDiff ℝ ∞ (k ∘ L) := hk.comp (ContinuousLinearMap.contDiff _)
  have hK : (fun y => (a : ℂ) * k (c • y)) = (a : ℂ) • (k ∘ L) := by
    funext y
    rfl
  rw [hK, iteratedFDeriv_const_smul_apply (hcomp.contDiffAt.of_le (by exact_mod_cast le_top)),
    L.iteratedFDeriv_comp_right hk x (by exact_mod_cast le_top), norm_smul, Complex.norm_real,
    Real.norm_eq_abs]
  gcongr
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [mul_comm]
  gcongr
  · calc ∏ _i : Fin n, ‖L‖ ≤ ∏ _i : Fin n, c :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hL)
      _ = c ^ n := by simp
  · exact le_rfl

def pieceSymbol (θ : Space → ℝ) (α s : ℝ) (i j k : Fin 3) (ξ : Space) : ℂ :=
  (θ ξ : ℂ) * projDivSymbol α s i j k ξ

lemma piece_kernel_eq (θ : Space → ℝ) (α : ℝ) (i j k : Fin 3) (l : ℤ) (x : Space) :
    FourierTransform.fourierInv
        (fun ξ => (θ (((2 : ℝ) ^ (-(l : ℝ))) • ξ) : ℂ) * projDivSymbol α 1 i j k ξ) x =
      ((((2 : ℝ) ^ (l : ℝ)) ^ 4 : ℝ) : ℂ) *
        FourierTransform.fourierInv (pieceSymbol θ α (((2 : ℝ) ^ (l : ℝ)) ^ (2 * α)) i j k)
          (((2 : ℝ) ^ (l : ℝ)) • x) := by
  set c := (2 : ℝ) ^ (l : ℝ) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hinv : (2 : ℝ) ^ (-(l : ℝ)) * c = 1 := by
    rw [hc, ← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero]
  rw [invTransform_smul_gen _ c hc0 x]
  have hf : (fun η : Space => (θ (((2 : ℝ) ^ (-(l : ℝ))) • c • η) : ℂ) *
      projDivSymbol α 1 i j k (c • η)) =
      fun η => (c : ℂ) * pieceSymbol θ α (c ^ (2 * α)) i j k η := by
    funext η
    rw [smul_smul, hinv, one_smul, symbol_smul_gen α 1 c hc0, one_mul, pieceSymbol]
    ring
  rw [hf, Real.fourierInv_eq', Real.fourierInv_eq']
  have hpt : ∀ η : Space, Complex.exp (↑(2 * π * inner ℝ η (c • x)) * Complex.I) •
      ((c : ℂ) * pieceSymbol θ α (c ^ (2 * α)) i j k η) = (c : ℂ) *
      (Complex.exp (↑(2 * π * inner ℝ η (c • x)) * Complex.I) •
        pieceSymbol θ α (c ^ (2 * α)) i j k η) := by
    intro η
    simp only [smul_eq_mul]
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  push_cast
  ring

lemma radial_integrable (α t : ℝ) (hα : 0 < α) (ht : 0 < t) (m : ℕ) :
    Integrable (fun ξ : Space => ‖ξ‖ ^ m * Real.exp (-(t * (2 * π * ‖ξ‖) ^ (2 * α)))) := by
  refine (integrable_fun_norm_addHaar (volume : Measure Space)
    (f := fun y : ℝ => y ^ m * Real.exp (-(t * (2 * π * y) ^ (2 * α))))).mpr ?_
  refine (integrableOn_rpow_mul_exp_neg_mul_rpow (s := ((m + 2 : ℕ) : ℝ)) (p := 2 * α)
    (b := t * (2 * π) ^ (2 * α)) (by have := (Nat.cast_nonneg (m + 2) : (0 : ℝ) ≤ _); linarith)
    (by positivity) (by positivity)).congr_fun
    (fun y hy => ?_) measurableSet_Ioi
  have hy0 : 0 < y := hy
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]
  rw [Real.rpow_natCast, Real.mul_rpow (by positivity) hy0.le]
  have he : -(t * (2 * π) ^ (2 * α)) * y ^ (2 * α) = -(t * ((2 * π) ^ (2 * α) * y ^ (2 * α))) := by
    ring
  rw [he, show (3 : ℕ) - 1 = 2 from rfl]
  ring

lemma symbol_norm_le (α t : ℝ) (i j k : Fin 3) (ξ : Space) :
    ‖projDivSymbol α t i j k ξ‖ ≤ 4 * π * (‖ξ‖ * Real.exp (-(t * (2 * π * ‖ξ‖) ^ (2 * α)))) := by
  unfold projDivSymbol
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Complex.norm_I, mul_one, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hk : |ξ k| ≤ ‖ξ‖ := by
    have := PiLp.norm_apply_le ξ k
    rwa [Real.norm_eq_abs] at this
  have hi : |ξ i| ≤ ‖ξ‖ := by
    have := PiLp.norm_apply_le ξ i
    rwa [Real.norm_eq_abs] at this
  have hj : |ξ j| ≤ ‖ξ‖ := by
    have := PiLp.norm_apply_le ξ j
    rwa [Real.norm_eq_abs] at this
  have hq : |ξ i * ξ j / ‖ξ‖ ^ 2| ≤ 1 := by
    rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖ξ‖ ^ 2)]
    refine div_le_one_of_le₀ ?_ (by positivity)
    rw [sq]
    exact mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)
  have hd : |(if i = j then (1 : ℝ) else 0) - ξ i * ξ j / ‖ξ‖ ^ 2| ≤ 2 := by
    refine (abs_sub _ _).trans ?_
    have : |(if i = j then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    linarith
  have h2 : |2 * π * ξ k| ≤ 2 * π * ‖ξ‖ := by
    rw [abs_mul, abs_of_pos (by positivity)]
    gcongr
  have hE := (Real.exp_pos (-(t * (2 * π * ‖ξ‖) ^ (2 * α)))).le
  calc |2 * π * ξ k| * |(if i = j then (1 : ℝ) else 0) - ξ i * ξ j / ‖ξ‖ ^ 2| *
        Real.exp (-(t * (2 * π * ‖ξ‖) ^ (2 * α)))
      ≤ (2 * π * ‖ξ‖) * 2 * Real.exp (-(t * (2 * π * ‖ξ‖) ^ (2 * α))) := by
        gcongr
    _ = 4 * π * (‖ξ‖ * Real.exp (-(t * (2 * π * ‖ξ‖) ^ (2 * α)))) := by ring

lemma symbol_measurable (α t : ℝ) (i j k : Fin 3) : Measurable (projDivSymbol α t i j k) := by
  unfold projDivSymbol
  fun_prop

lemma symbol_moment (α t : ℝ) (hα : 0 < α) (ht : 0 < t) (i j k : Fin 3) (n : ℕ) :
    Integrable (fun v : Space => ‖v‖ ^ n * ‖projDivSymbol α t i j k v‖) := by
  refine ((radial_integrable α t hα ht (n + 1)).const_mul (4 * π)).mono' ?_ ?_
  · exact ((continuous_norm.pow n).measurable.mul
      (symbol_measurable α t i j k).norm).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun v => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    calc ‖v‖ ^ n * ‖projDivSymbol α t i j k v‖ ≤
        ‖v‖ ^ n * (4 * π * (‖v‖ * Real.exp (-(t * (2 * π * ‖v‖) ^ (2 * α))))) := by
          gcongr
          exact symbol_norm_le α t i j k v
      _ = 4 * π * (‖v‖ ^ (n + 1) * Real.exp (-(t * (2 * π * ‖v‖) ^ (2 * α)))) := by ring

lemma kernel_contDiff (α t : ℝ) (hα : 0 < α) (ht : 0 < t) (i j k : Fin 3) :
    ContDiff ℝ ∞ (projDivKernel α t i j k) := by
  unfold projDivKernel
  rw [Real.fourierInv_eq_fourier_comp_neg]
  refine Real.contDiff_fourier (N := ⊤) (fun n _ => ?_)
  have h := symbol_moment α t hα ht i j k n
  have := h.comp_neg
  simpa only [norm_neg] using this

lemma cutoff_partial_le (θ : Space → ℝ) (hθ : IsRingCutoff θ) (v : Space) (s : Finset ℤ) :
    ∑ l ∈ s, θ (((2 : ℝ) ^ (-(l : ℝ))) • v) ≤ 1 := by
  by_cases hv : v = 0
  · subst hv
    have h0 : θ 0 = 0 := by
      by_contra h
      have := (hθ.2.2.1 0 h).1
      simp at this
      linarith
    simp [h0]
  · exact sum_le_hasSum s (fun l _ => (hθ.2.1 _).1) (hθ.2.2.2 v hv)

lemma hasSum_integral_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (θ : Space → ℝ) (hθ : IsRingCutoff θ) (H : Space → E) (hH : Integrable H) (hH0 : H 0 = 0) :
    HasSum (fun l : ℤ => ∫ v, θ (((2 : ℝ) ^ (-(l : ℝ))) • (-v)) • H v) (∫ v, H v) := by
  have hcont : Continuous θ := hθ.1.continuous
  have hint : ∀ l : ℤ, Integrable (fun v => θ (((2 : ℝ) ^ (-(l : ℝ))) • (-v)) • H v) := by
    intro l
    refine hH.norm.mono' ((hcont.comp (by fun_prop)).aestronglyMeasurable.smul
      hH.aestronglyMeasurable) (Filter.Eventually.of_forall (fun v => ?_))
    rw [norm_smul, Real.norm_of_nonneg (hθ.2.1 _).1]
    have := (hθ.2.1 (((2 : ℝ) ^ (-(l : ℝ))) • (-v))).2
    calc θ (((2 : ℝ) ^ (-(l : ℝ))) • (-v)) * ‖H v‖ ≤ 1 * ‖H v‖ := by gcongr
      _ = ‖H v‖ := one_mul _
  have hsum : Summable (fun l : ℤ => ∫ v, ‖θ (((2 : ℝ) ^ (-(l : ℝ))) • (-v)) • H v‖) := by
    refine summable_of_sum_le (c := ∫ v, ‖H v‖) (fun l => integral_nonneg (fun v => norm_nonneg _))
      (fun s => ?_)
    rw [← integral_finsetSum s (fun l _ => (hint l).norm)]
    refine integral_mono (integrable_finsetSum s (fun l _ => (hint l).norm)) hH.norm (fun v => ?_)
    simp only
    simp_rw [norm_smul, fun l => Real.norm_of_nonneg (hθ.2.1 (((2 : ℝ) ^ (-(l : ℝ))) • (-v))).1]
    rw [← Finset.sum_mul]
    calc (∑ l ∈ s, θ (((2 : ℝ) ^ (-(l : ℝ))) • (-v))) * ‖H v‖ ≤ 1 * ‖H v‖ := by
          gcongr
          exact cutoff_partial_le θ hθ (-v) s
      _ = ‖H v‖ := one_mul _
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  convert h using 1
  congr 1
  funext v
  by_cases hv : v = 0
  · subst hv
    simp [hH0]
  · have hs := (hθ.2.2.2 (-v) (neg_ne_zero.mpr hv)).smul_const (H v)
    rw [one_smul] at hs
    exact hs.tsum_eq.symm

lemma powSMulRight_smul (a : Space → ℝ) (g : Space → ℂ) (v : Space) (n : ℕ) :
    VectorFourier.fourierPowSMulRight (innerSL ℝ) (fun w => (a w : ℂ) * g w) v n =
      a v • VectorFourier.fourierPowSMulRight (innerSL ℝ) g v n := by
  ext m
  simp only [VectorFourier.fourierPowSMulRight_apply, ContinuousMultilinearMap.smul_apply,
    Complex.real_smul, smul_eq_mul]
  ring

lemma symbol_zero (α t : ℝ) (i j k : Fin 3) : projDivSymbol α t i j k 0 = 0 := by
  simp [projDivSymbol]

lemma kernel_hasSum (α : ℝ) (hα : 0 < α) (θ : Space → ℝ) (hθ : IsRingCutoff θ) (i j k : Fin 3)
    (n : ℕ) (x : Space) :
    HasSum (fun l : ℤ => iteratedFDeriv ℝ n (FourierTransform.fourierInv
        (fun ξ => (θ (((2 : ℝ) ^ (-(l : ℝ))) • ξ) : ℂ) * projDivSymbol α 1 i j k ξ)) x)
      (iteratedFDeriv ℝ n (projDivKernel α 1 i j k) x) := by
  have hcont : Continuous θ := hθ.1.continuous
  set g : Space → ℂ := fun v => projDivSymbol α 1 i j k (-v) with hg
  have hgm : Measurable g := (symbol_measurable α 1 i j k).comp measurable_neg
  have hgmom : ∀ m : ℕ, Integrable (fun v => ‖v‖ ^ m * ‖g v‖) := by
    intro m
    have := (symbol_moment α 1 hα one_pos i j k m).comp_neg
    simpa only [norm_neg] using this
  set G : Space → _ := fun v => VectorFourier.fourierPowSMulRight (innerSL ℝ) g v n with hG
  have hGi : Integrable G :=
    VectorFourier.integrable_fourierPowSMulRight (innerSL ℝ) (hgmom n) hgm.aestronglyMeasurable
  set H : Space → _ := fun v => Real.fourierChar (-(inner ℝ v x)) • G v with hH
  have hHi : Integrable H := by
    refine hGi.norm.mono' ((Real.continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable.smul
      hGi.aestronglyMeasurable) (Filter.Eventually.of_forall (fun v => ?_))
    simp only [hH, Circle.norm_smul, le_refl]
  have hH0 : H 0 = 0 := by
    simp [hH, hG, hg, VectorFourier.fourierPowSMulRight, symbol_zero]
    ext m
    simp
  have hmain : iteratedFDeriv ℝ n (projDivKernel α 1 i j k) x = ∫ v, H v := by
    unfold projDivKernel
    rw [Real.fourierInv_eq_fourier_comp_neg, Real.iteratedFDeriv_fourier (N := ⊤)
      (fun m _ => hgmom m) hgm.aestronglyMeasurable (by exact_mod_cast le_top), Real.fourier_eq]
  have hpiece : ∀ l : ℤ, iteratedFDeriv ℝ n (FourierTransform.fourierInv
      (fun ξ => (θ (((2 : ℝ) ^ (-(l : ℝ))) • ξ) : ℂ) * projDivSymbol α 1 i j k ξ)) x =
      ∫ v, θ (((2 : ℝ) ^ (-(l : ℝ))) • (-v)) • H v := by
    intro l
    set a : Space → ℝ := fun v => θ (((2 : ℝ) ^ (-(l : ℝ))) • (-v)) with ha
    have ham : Measurable (fun v => (a v : ℂ) * g v) :=
      (Complex.measurable_ofReal.comp (hcont.comp (by fun_prop)).measurable).mul hgm
    have hmom : ∀ m : ℕ, Integrable (fun v => ‖v‖ ^ m * ‖(a v : ℂ) * g v‖) := by
      intro m
      refine (hgmom m).mono' (by fun_prop) (Filter.Eventually.of_forall (fun v => ?_))
      rw [Real.norm_of_nonneg (by positivity), norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (hθ.2.1 _).1]
      have := (hθ.2.1 (((2 : ℝ) ^ (-(l : ℝ))) • (-v))).2
      calc ‖v‖ ^ m * (a v * ‖g v‖) ≤ ‖v‖ ^ m * (1 * ‖g v‖) := by gcongr
        _ = ‖v‖ ^ m * ‖g v‖ := by rw [one_mul]
    rw [Real.fourierInv_eq_fourier_comp_neg]
    change iteratedFDeriv ℝ n (FourierTransform.fourier (fun v => (a v : ℂ) * g v)) x = _
    rw [Real.iteratedFDeriv_fourier (N := ⊤) (fun m _ => hmom m) ham.aestronglyMeasurable
      (by exact_mod_cast le_top), Real.fourier_eq]
    congr 1
    funext v
    rw [powSMulRight_smul a g v n, smul_comm]
  rw [hmain]
  have hs := hasSum_integral_cutoff θ hθ H hHi hH0
  simp_rw [← hpiece] at hs
  exact hs

lemma unit_bound (α : ℝ) (hα : 0 < α) (θ : Space → ℝ) (hθ : IsRingCutoff θ) (i j k : Fin 3)
    (hP : ∀ M : ℕ, ∃ A : ℝ, ∀ s : ℝ, 0 < s → ContDiff ℝ ∞ (pieceSymbol θ α s i j k) ∧
      ∀ q ≤ M, ∀ ξ, ‖iteratedFDeriv ℝ q (pieceSymbol θ α s i j k) ξ‖ ≤ A)
    (h2 : PieceKernelStatement) (h3 : DyadicSumStatement) (n : ℕ) :
    ∃ C : ℝ, ∀ x : Space,
      ‖iteratedFDeriv ℝ n (projDivKernel α 1 i j k) x‖ ≤ C * (1 + ‖x‖) ^ (-(4 + n : ℝ)) := by
  set a : ℝ := 4 + n with ha
  have ha0 : 0 < a := by positivity
  obtain ⟨C2, hC2⟩ := h2 (n + 5) n
  obtain ⟨A, hA⟩ := hP (n + 5 + n + 4)
  obtain ⟨C3, hC3⟩ := h3 a ((n + 5 : ℕ) : ℝ) ha0 (by rw [ha]; push_cast; linarith)
  have hK1 : ContDiff ℝ ∞ (projDivKernel α 1 i j k) := kernel_contDiff α 1 hα one_pos i j k
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0 : Space) 1).exists_bound_of_continuousOn
    ((hK1.continuous_iteratedFDeriv (by exact_mod_cast le_top)).continuousOn)
  have hM0nn : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0 (Metric.mem_closedBall_self zero_le_one))
  have hpiece : ∀ (l : ℤ) (x : Space), ‖iteratedFDeriv ℝ n (FourierTransform.fourierInv
      (fun ξ => (θ (((2 : ℝ) ^ (-(l : ℝ))) • ξ) : ℂ) * projDivSymbol α 1 i j k ξ)) x‖ ≤
      (C2 * A) * ((2 : ℝ) ^ (a * l) * (1 + (2 : ℝ) ^ (l : ℝ) * ‖x‖) ^ (-((n + 5 : ℕ) : ℝ))) := by
    intro l x
    set c : ℝ := (2 : ℝ) ^ (l : ℝ) with hc
    have hc0 : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
    have hs0 : 0 < c ^ (2 * α) := Real.rpow_pos_of_pos hc0 _
    obtain ⟨hsm, hsb⟩ := hA (c ^ (2 * α)) hs0
    have hsupp : ∀ ξ, pieceSymbol θ α (c ^ (2 * α)) i j k ξ ≠ 0 → 1 / 4 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 4 := by
      intro ξ hξ
      have hθξ : θ ξ ≠ 0 := by
        intro h0
        apply hξ
        simp [pieceSymbol, h0]
      have := hθ.2.2.1 ξ hθξ
      constructor <;> linarith [this.1, this.2]
    obtain ⟨hkc, hkb⟩ := hC2 (pieceSymbol θ α (c ^ (2 * α)) i j k) A hsm hsupp
      (fun q hq ξ => hsb q hq ξ)
    have hfun : FourierTransform.fourierInv
        (fun ξ => (θ (((2 : ℝ) ^ (-(l : ℝ))) • ξ) : ℂ) * projDivSymbol α 1 i j k ξ) =
        fun y => ((c ^ 4 : ℝ) : ℂ) *
          FourierTransform.fourierInv (pieceSymbol θ α (c ^ (2 * α)) i j k) (c • y) := by
      funext y
      exact piece_kernel_eq θ α i j k l y
    rw [hfun]
    refine (norm_iteratedFDeriv_scale_le _ hkc (c ^ 4) c hc0 n x).trans ?_
    have hb := hkb (c • x)
    have hcx : ‖c • x‖ = c * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg hc0.le]
    rw [hcx] at hb
    have hpos : 0 < (1 + c * ‖x‖) ^ (n + 5) := by positivity
    have hD : ‖iteratedFDeriv ℝ n (FourierTransform.fourierInv
        (pieceSymbol θ α (c ^ (2 * α)) i j k)) (c • x)‖ ≤
        (C2 * A) * (1 + c * ‖x‖) ^ (-((n + 5 : ℕ) : ℝ)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos,
        mul_comm]
      exact hb
    have hcpow : |c ^ 4| * c ^ n = (2 : ℝ) ^ (a * l) := by
      rw [abs_of_pos (by positivity), ← pow_add, hc, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      rw [ha]
      push_cast
      ring
    calc |c ^ 4| * (c ^ n * ‖iteratedFDeriv ℝ n (FourierTransform.fourierInv
          (pieceSymbol θ α (c ^ (2 * α)) i j k)) (c • x)‖)
        ≤ |c ^ 4| * (c ^ n * ((C2 * A) * (1 + c * ‖x‖) ^ (-((n + 5 : ℕ) : ℝ)))) := by
          gcongr
      _ = (C2 * A) * ((|c ^ 4| * c ^ n) * (1 + c * ‖x‖) ^ (-((n + 5 : ℕ) : ℝ))) := by ring
      _ = (C2 * A) * ((2 : ℝ) ^ (a * l) * (1 + c * ‖x‖) ^ (-((n + 5 : ℕ) : ℝ))) := by rw [hcpow]
  have hCA : 0 ≤ C2 * A := by
    have hs1 := (hA 1 one_pos)
    have := (hC2 (pieceSymbol θ α 1 i j k) A hs1.1 (by
      intro ξ hξ
      have hθξ : θ ξ ≠ 0 := by
        intro h0
        apply hξ
        simp [pieceSymbol, h0]
      have := hθ.2.2.1 ξ hθξ
      constructor <;> linarith [this.1, this.2]) (fun q hq ξ => hs1.2 q hq ξ)).2 0
    exact (by positivity : (0 : ℝ) ≤ (1 + ‖(0 : Space)‖) ^ (n + 5) * _).trans this
  have h2a : (0 : ℝ) < 2 ^ a := by positivity
  refine ⟨max (M0 * 2 ^ a) (C2 * A * C3 * 2 ^ a), fun x => ?_⟩
  have hw : 0 ≤ (1 + ‖x‖) ^ (-a) := by positivity
  by_cases hx : ‖x‖ ≤ 1
  · have hlow : 1 ≤ 2 ^ a * (1 + ‖x‖) ^ (-a) := by
      have : (2 : ℝ) ^ (-a) ≤ (1 + ‖x‖) ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      rw [Real.rpow_neg (by norm_num)] at this
      calc (1 : ℝ) = 2 ^ a * (2 ^ a)⁻¹ := by field_simp
        _ ≤ 2 ^ a * (1 + ‖x‖) ^ (-a) := by gcongr
    calc ‖iteratedFDeriv ℝ n (projDivKernel α 1 i j k) x‖ ≤ M0 :=
          hM0 x (by simpa using hx)
      _ ≤ M0 * (2 ^ a * (1 + ‖x‖) ^ (-a)) := le_mul_of_one_le_right hM0nn hlow
      _ = (M0 * 2 ^ a) * (1 + ‖x‖) ^ (-a) := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · push Not at hx
    have hr : 0 < ‖x‖ := by linarith
    obtain ⟨hsum, hle⟩ := hC3 ‖x‖ hr
    have hbound := tsum_of_norm_bounded ((hsum.hasSum).mul_left (C2 * A)) (hpiece · x)
    rw [(kernel_hasSum α hα θ hθ i j k n x).tsum_eq] at hbound
    have hfar : ‖x‖ ^ (-a) ≤ 2 ^ a * (1 + ‖x‖) ^ (-a) := by
      have h1 : (2 * ‖x‖) ^ (-a) ≤ (1 + ‖x‖) ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      rw [Real.mul_rpow (by norm_num) hr.le, Real.rpow_neg (by norm_num)] at h1
      calc ‖x‖ ^ (-a) = 2 ^ a * ((2 ^ a)⁻¹ * ‖x‖ ^ (-a)) := by field_simp
        _ ≤ 2 ^ a * (1 + ‖x‖) ^ (-a) := by gcongr
    calc ‖iteratedFDeriv ℝ n (projDivKernel α 1 i j k) x‖
        ≤ C2 * A * ∑' l : ℤ, (2 : ℝ) ^ (a * l) * (1 + (2 : ℝ) ^ (l : ℝ) * ‖x‖) ^ (-((n + 5 : ℕ) : ℝ)) :=
          hbound
      _ ≤ C2 * A * (C3 * ‖x‖ ^ (-a)) := by gcongr
      _ ≤ C2 * A * (C3 * (2 ^ a * (1 + ‖x‖) ^ (-a))) := by
          have h0 : 0 ≤ C3 * ‖x‖ ^ (-a) :=
            (tsum_nonneg (fun l => by positivity)).trans hle
          have hC3nn : 0 ≤ C3 := by
            by_contra hneg
            have := mul_neg_of_neg_of_pos (lt_of_not_ge hneg)
              (Real.rpow_pos_of_pos hr (-a))
            linarith
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfar hC3nn) hCA
      _ = (C2 * A * C3 * 2 ^ a) * (1 + ‖x‖) ^ (-a) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

end KernelDecayInternal

theorem kernelDecay_of (h1 : RingCutoffStatement) (h2 : PieceKernelStatement)
    (h3 : DyadicSumStatement) : KernelDecayStatement := by
  intro α hα i j k
  obtain ⟨θ, hθ⟩ := h1
  exact KernelDecayInternal.decay_of_unit α hα i j k
    (KernelDecayInternal.kernel_contDiff α 1 hα one_pos i j k)
    (KernelDecayInternal.unit_bound α hα θ hθ i j k
      (KernelDecayInternal.piece_symbol_bound α hα θ hθ i j k) h2 h3)

end Breakdown.FracCert
