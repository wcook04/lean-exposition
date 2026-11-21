import Breakdown.Torus.StatementsCoeff

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Periodic

namespace TrigHs.Internal

def box (a b : ℝ) : Set Space := {x | ∀ i, x i ∈ Icc a b}

def trig (s : Finset Lattice) (c : Lattice → Coef) (x : Space) : Coef :=
  ∑ k ∈ s, character (-k) x • c k

theorem freq_apply (k : Lattice) (i : Fin 3) : freq k i = k i := by
  simp [freq, unitVector, Pi.single_apply]

theorem inner_freq (k : Lattice) (x : Space) : inner ℝ (freq k) x = ∑ i, (k i : ℝ) * x i := by
  simp [freq, unitVector, sum_inner, real_inner_smul_left, EuclideanSpace.inner_single_left]

theorem character_neg (k : Lattice) (x : Space) :
    character (-k) x = Complex.exp (2 * π * Complex.I * ((inner ℝ (freq k) x : ℝ) : ℂ)) := by
  have h : freq (-k) = -freq k := by simp [freq, neg_smul, Finset.sum_neg_distrib]
  simp [character, h, inner_neg_left]

theorem character_neg_eq_prod (k : Lattice) (x : Space) :
    character (-k) x = ∏ i, Complex.exp (2 * π * Complex.I * (((k i : ℝ) * x i : ℝ) : ℂ)) := by
  rw [character_neg, inner_freq, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

theorem continuous_character_neg (k : Lattice) : Continuous (character (-k)) := by
  have h : character (-k) = fun x => Complex.exp (2 * π * Complex.I * ((inner ℝ (freq k) x : ℝ) : ℂ)) :=
    funext (character_neg k)
  rw [h]
  fun_prop

theorem box_eq (a b : ℝ) :
    box a b = (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm ⁻¹' (Set.univ.pi fun _ => Icc a b) := by
  ext x
  simp only [box, mem_ofPred_eq, mem_preimage, mem_univ_pi]
  rfl

theorem isCompact_box (a b : ℝ) : IsCompact (box a b) := by
  have h : box a b = WithLp.toLp 2 '' (Set.univ.pi fun _ : Fin 3 => Icc a b) := by
    ext x
    constructor
    · intro hx
      exact ⟨WithLp.ofLp x, fun i _ => hx i, rfl⟩
    · rintro ⟨y, hy, rfl⟩ i
      exact hy i (Set.mem_univ i)
  rw [h]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)

theorem setIntegral_box_prod (a b : ℝ) (φ : Fin 3 → ℝ → ℂ) :
    ∫ x in box a b, ∏ i, φ i (x i) = ∏ i, ∫ t in Icc a b, φ i t := by
  rw [box_eq]
  refine ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding (fun y => ∏ i, φ i (y i)) _).trans ?_
  rw [volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]

theorem integral_exp_Icc (a : ℝ) (L : ℕ) (m : ℤ) :
    ∫ t in Icc a (a + L), Complex.exp (2 * π * Complex.I * (((m : ℝ) * t : ℝ) : ℂ)) =
      if m = 0 then (L : ℂ) else 0 := by
  have hL : a ≤ a + L := by linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL]
  split_ifs with hm
  · subst hm
    simp
  · have hc : (2 * π * Complex.I * m) ≠ 0 := by simp [hm, pi_ne_zero]
    have h : ∀ t : ℝ, Complex.exp (2 * π * Complex.I * (((m : ℝ) * t : ℝ) : ℂ)) =
        Complex.exp ((2 * π * Complex.I * m) * t) := by
      intro t
      push_cast
      ring_nf
    simp_rw [h]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * π * Complex.I * m * ((a + L : ℝ) : ℂ)) =
        Complex.exp (2 * π * Complex.I * m * a) := by
      have h2 : 2 * π * Complex.I * m * ((a + L : ℝ) : ℂ) =
          2 * π * Complex.I * m * a + ((m * L : ℤ) : ℂ) * (2 * π * Complex.I) := by
        push_cast
        ring
      rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [h1, sub_self, zero_div]

theorem setIntegral_box_character (a : ℝ) (L : ℕ) (n : Lattice) :
    ∫ x in box a (a + L), character (-n) x = if n = 0 then (L : ℂ) ^ 3 else 0 := by
  simp_rw [character_neg_eq_prod]
  rw [setIntegral_box_prod a (a + L) (fun i t => Complex.exp (2 * π * Complex.I * (((n i : ℝ) * t : ℝ) : ℂ)))]
  simp_rw [integral_exp_Icc]
  split_ifs with hn
  · subst hn
    simp
  · obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra h
      push Not at h
      exact hn (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem conj_character_mul (j k : Lattice) (x : Space) :
    (starRingEnd ℂ) (character (-j) x) * character (-k) x = character (-(k - j)) x := by
  rw [character_neg, character_neg, character_neg, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  have h : freq (k - j) = freq k - freq j := by
    simp [freq, sub_smul, Finset.sum_sub_distrib]
  rw [h, inner_sub_left]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

theorem inner_self_coef (v : Coef) : inner ℂ v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_pow]
  exact inner_self_eq_norm_sq_to_K v

theorem integrableOn_character (a b : ℝ) (n : Lattice) : IntegrableOn (character (-n)) (box a b) :=
  (continuous_character_neg n).continuousOn.integrableOn_compact (isCompact_box a b)

theorem integral_norm_sq_trig (a : ℝ) (L : ℕ) (s : Finset Lattice) (c : Lattice → Coef) :
    ∫ x in box a (a + L), ‖trig s c x‖ ^ 2 = (L : ℝ) ^ 3 * ∑ k ∈ s, ‖c k‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have h : ∀ x, ((‖trig s c x‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ s, ∑ k ∈ s, inner ℂ (c k) (c j) * character (-(j - k)) x := by
    intro x
    rw [← inner_self_coef]
    simp only [trig, sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [← conj_character_mul]
    ring
  simp_rw [h]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
    (integrableOn_character _ _ _).const_mul _]
  simp_rw [integral_finsetSum _ fun k _ => (integrableOn_character _ _ _).const_mul _]
  simp_rw [integral_const_mul, setIntegral_box_character, sub_eq_zero, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, inner_self_coef]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp [hk]
  ring


theorem inner_freq_unitVector (k : Lattice) (i : Fin 3) : inner ℝ (freq k) (unitVector i) = k i := by
  rw [inner_freq]
  simp [unitVector]

theorem norm_freq_sq (k : Lattice) : ‖freq k‖ ^ 2 = ∑ i, ((k i : ℝ)) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_freq]
  simp [freq_apply, sq]

theorem hasFDerivAt_character_neg (k : Lattice) (x : Space) :
    HasFDerivAt (character (-k))
      (Complex.exp (2 * π * Complex.I * ((inner ℝ (freq k) x : ℝ) : ℂ)) •
        ((2 * π * Complex.I) • (Complex.ofRealCLM.comp (innerSL ℝ (freq k))))) x := by
  have h1 : HasFDerivAt (fun y : Space => ((inner ℝ (freq k) y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (innerSL ℝ (freq k))) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (innerSL ℝ (freq k)).hasFDerivAt
  have h : character (-k) =
      fun y => Complex.exp (2 * π * Complex.I * ((inner ℝ (freq k) y : ℝ) : ℂ)) :=
    funext (character_neg k)
  rw [h]
  exact (h1.const_mul (2 * π * Complex.I)).cexp

theorem trig_eq (s : Finset Lattice) (c : Lattice → Coef) :
    trig s c = fun x => ∑ k ∈ s, Complex.exp (2 * π * Complex.I * ((inner ℝ (freq k) x : ℝ) : ℂ)) • c k := by
  funext x
  simp only [trig, character_neg]

theorem contDiff_trig (s : Finset Lattice) (c : Lattice → Coef) : ContDiff ℝ 1 (trig s c) := by
  rw [trig_eq]
  refine ContDiff.sum fun k _ => ?_
  have h1 : ContDiff ℝ 1 (fun y : Space => ((inner ℝ (freq k) y : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (innerSL ℝ (freq k)).contDiff
  have h2 := Complex.contDiff_exp.comp ((contDiff_const (c := 2 * π * Complex.I)).mul h1)
  exact (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℂ) (c k)).contDiff.comp h2

theorem fderiv_trig_apply (s : Finset Lattice) (c : Lattice → Coef) (x : Space) (i : Fin 3) :
    fderiv ℝ (trig s c) x (unitVector i) =
      trig s (fun k => (2 * π * Complex.I * (k i : ℂ)) • c k) x := by
  have h := HasFDerivAt.sum (u := s) fun k _ => (hasFDerivAt_character_neg k x).smul_const (c k)
  have e : trig s c = ∑ k ∈ s, fun y => character (-k) y • c k := by
    funext y
    simp [trig, Finset.sum_apply]
  rw [e, h.fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    Complex.ofRealCLM_apply, inner_freq_unitVector, trig, character_neg]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul, smul_smul]
  congr 1
  push_cast
  ring

theorem eq_sum_unitVector (v : Space) : v = ∑ i, v i • unitVector i := by
  ext j
  simp [unitVector, Pi.single_apply]

theorem norm_unitVector (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem opNorm_le_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : Space →L[ℝ] E) :
    ‖T‖ ≤ ∑ i, ‖T (unitVector i)‖ := by
  refine T.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  calc ‖T v‖ = ‖∑ i, v i • T (unitVector i)‖ := by
        conv_lhs => rw [eq_sum_unitVector v]
        simp [map_sum, map_smul]
    _ ≤ ∑ i, ‖v i • T (unitVector i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖v‖ * ‖T (unitVector i)‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v i) (norm_nonneg _)
    _ = (∑ i, ‖T (unitVector i)‖) * ‖v‖ := by rw [← Finset.mul_sum, mul_comm]

theorem norm_le_of_mem_cell {x : Space} (hx : x ∈ cell) : ‖x‖ ≤ 3 := by
  calc ‖x‖ = ‖∑ i, x i • unitVector i‖ := by rw [← eq_sum_unitVector x]
    _ ≤ ∑ i, ‖x i • unitVector i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        rw [norm_smul, norm_unitVector, mul_one, Real.norm_eq_abs, abs_le]
        have h := hx i
        constructor <;> linarith [h.1, h.2]
    _ = 3 := by simp

theorem mem_box_of_norm_le {x : Space} (hx : ‖x‖ ≤ 4) : x ∈ box (-4) (-4 + (8 : ℕ)) := by
  intro i
  have h := PiLp.norm_apply_le x i
  rw [Real.norm_eq_abs] at h
  have h2 := abs_le.1 (h.trans hx)
  constructor <;> push_cast <;> linarith [h2.1, h2.2]

def cutoff : ContDiffBump (0 : Space) := ⟨3, 4, by norm_num, by norm_num⟩

theorem norm_fderiv_cutoff_sq_le {M : ℝ} (hM : ∀ x, ‖fderiv ℝ cutoff x‖ ≤ M)
    (s : Finset Lattice) (c : Lattice → Coef) (x : Space) :
    ‖fderiv ℝ (fun y => cutoff y • trig s c y) x‖ ^ 2 ≤
      (6 + 18 * M ^ 2) * (‖trig s c x‖ ^ 2 +
        ∑ i, ‖trig s (fun k => (2 * π * Complex.I * (k i : ℂ)) • c k) x‖ ^ 2) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x)
  have hd : ∀ i, ‖fderiv ℝ (fun y => cutoff y • trig s c y) x (unitVector i)‖ ≤
      ‖trig s (fun k => (2 * π * Complex.I * (k i : ℂ)) • c k) x‖ + M * ‖trig s c x‖ := by
    intro i
    rw [fderiv_fun_smul ((cutoff.contDiff (n := 1)).differentiable one_ne_zero x)
      ((contDiff_trig s c).differentiable one_ne_zero x)]
    rw [_root_.add_apply, _root_.smul_apply,
      ContinuousLinearMap.smulRight_apply, fderiv_trig_apply]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg cutoff.nonneg]
      exact mul_le_of_le_one_left (norm_nonneg _) cutoff.le_one
    · rw [norm_smul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      calc ‖fderiv ℝ cutoff x (unitVector i)‖ ≤ ‖fderiv ℝ cutoff x‖ * ‖unitVector i‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ M := by rw [norm_unitVector, mul_one]; exact hM x
  have h1 := opNorm_le_sum (fderiv ℝ (fun y => cutoff y • trig s c y) x)
  rw [Fin.sum_univ_three] at h1 ⊢
  have h0 := hd 0
  have h1' := hd 1
  have h2 := hd 2
  set D := ‖fderiv ℝ (fun y => cutoff y • trig s c y) x‖
  set a0 := ‖trig s (fun k => (2 * π * Complex.I * (k 0 : ℂ)) • c k) x‖
  set a1 := ‖trig s (fun k => (2 * π * Complex.I * (k 1 : ℂ)) • c k) x‖
  set a2 := ‖trig s (fun k => (2 * π * Complex.I * (k 2 : ℂ)) • c k) x‖
  set B := ‖trig s c x‖
  have hD : 0 ≤ D := norm_nonneg _
  have ha0 : 0 ≤ a0 := norm_nonneg _
  have ha1 : 0 ≤ a1 := norm_nonneg _
  have ha2 : 0 ≤ a2 := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  have hS : D ≤ a0 + a1 + a2 + 3 * M * B := by linarith
  have hS2 : D ^ 2 ≤ (a0 + a1 + a2 + 3 * M * B) ^ 2 := pow_le_pow_left₀ hD hS 2
  have hS3 : (a0 + a1 + a2 + 3 * M * B) ^ 2 ≤ 6 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2) + 18 * M ^ 2 * B ^ 2 := by
    nlinarith [sq_nonneg (a0 - a1), sq_nonneg (a1 - a2), sq_nonneg (a0 - a2),
      sq_nonneg (a0 + a1 + a2 - 3 * M * B)]
  have hS4 : 6 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2) + 18 * M ^ 2 * B ^ 2 ≤
      (6 + 18 * M ^ 2) * (B ^ 2 + (a0 ^ 2 + a1 ^ 2 + a2 ^ 2)) := by
    nlinarith [sq_nonneg B, mul_nonneg (sq_nonneg M) (add_nonneg (add_nonneg (sq_nonneg a0) (sq_nonneg a1)) (sq_nonneg a2))]
  linarith

theorem integral_fderiv_cutoff_sq_le {M : ℝ} (hM : ∀ x, ‖fderiv ℝ cutoff x‖ ≤ M)
    (s : Finset Lattice) (c : Lattice → Coef) :
    ∫ x, ‖fderiv ℝ (fun y => cutoff y • trig s c y) x‖ ^ 2 ≤
      (6 + 18 * M ^ 2) * 8 ^ 3 * ∑ k ∈ s, weight k * ‖c k‖ ^ 2 := by
  set cd : Fin 3 → Lattice → Coef := fun i k => (2 * π * Complex.I * (k i : ℂ)) • c k with hcd
  have hgc : ContDiff ℝ 1 (fun y => cutoff y • trig s c y) := cutoff.contDiff.smul (contDiff_trig s c)
  have hzero : ∀ x, x ∉ box (-4) (-4 + (8 : ℕ)) →
      ‖fderiv ℝ (fun y => cutoff y • trig s c y) x‖ ^ 2 = 0 := by
    intro x hx
    have hxs : x ∉ tsupport (fun y => cutoff y • trig s c y) := by
      intro h
      have h' := tsupport_smul_subset_left (fun y => cutoff y) (trig s c) h
      rw [cutoff.tsupport_eq] at h'
      exact hx (mem_box_of_norm_le (mem_closedBall_zero_iff.1 h'))
    rw [fderiv_of_notMem_tsupport ℝ hxs]
    simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hK := isCompact_box (-4) (-4 + (8 : ℕ))
  have hI1 : IntegrableOn (fun x => ‖fderiv ℝ (fun y => cutoff y • trig s c y) x‖ ^ 2)
      (box (-4) (-4 + (8 : ℕ))) :=
    ((hgc.continuous_fderiv one_ne_zero).norm.pow 2).continuousOn.integrableOn_compact hK
  have hc1 : ∀ (d : Lattice → Coef), IntegrableOn (fun x => ‖trig s d x‖ ^ 2) (box (-4) (-4 + (8 : ℕ))) :=
    fun d => ((contDiff_trig s d).continuous.norm.pow 2).continuousOn.integrableOn_compact hK
  have hI2 : IntegrableOn (fun x => (6 + 18 * M ^ 2) * (‖trig s c x‖ ^ 2 +
      ∑ i, ‖trig s (cd i) x‖ ^ 2)) (box (-4) (-4 + (8 : ℕ))) :=
    ((hc1 c).add (integrable_finsetSum _ fun i _ => hc1 (cd i))).const_mul _
  refine (integral_mono hI1 hI2 fun x => norm_fderiv_cutoff_sq_le hM s c x).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_add (hc1 c) (integrable_finsetSum _ fun i _ => hc1 (cd i)),
    integral_finsetSum _ fun i _ => hc1 (cd i)]
  simp_rw [integral_norm_sq_trig]
  have hw : ∀ k, weight k * ‖c k‖ ^ 2 = ‖c k‖ ^ 2 + ∑ i, ‖cd i k‖ ^ 2 := by
    intro k
    simp only [weight, hcd, norm_smul, norm_freq_sq]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, Complex.norm_intCast,
      Real.norm_eq_abs, abs_of_pos pi_pos, mul_pow, sq_abs]
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    ring
  simp_rw [hw, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, Finset.sum_comm]
  push_cast
  ring

theorem setIntegral_cell_eq (s : Finset Lattice) (c : Lattice → Coef) :
    ∫ x in cell, ‖∑ k ∈ s, character (-k) x • c k‖ ^ (6 : ℝ) =
      ∫ x in cell, ‖cutoff x • trig s c x‖ ^ (6 : ℝ) := by
  refine setIntegral_congr_fun (isCompact_box 0 1).measurableSet fun x hx => ?_
  have hx' : x ∈ Metric.closedBall (0 : Space) cutoff.rIn :=
    mem_closedBall_zero_iff.2 (norm_le_of_mem_cell hx)
  simp only [cutoff.one_of_mem_closedBall hx', one_smul, trig]

end TrigHs.Internal

open TrigHs.Internal in
theorem trigHs : TrigHs := by
  obtain ⟨M, hM⟩ := ((cutoff.contDiff (n := 1)).continuous_fderiv (by simp)).bounded_above_of_compact_support
    (cutoff.hasCompactSupport.fderiv (𝕜 := ℝ))
  set CG : NNReal := SNormLESNormFDerivOfEqConst Coef (volume : Measure Space) ((2 : NNReal) : ℝ)
  set K : ℝ := (6 + 18 * M ^ 2) * 8 ^ 3
  have hK : 0 < K := by positivity
  refine ⟨((CG : ℝ) + 1) * K ^ (1 / 2 : ℝ), by positivity, fun s c => ?_⟩
  set g : Space → Coef := fun y => cutoff y • trig s c y
  have hgc : ContDiff ℝ 1 g := cutoff.contDiff.smul (contDiff_trig s c)
  have hgs : HasCompactSupport g := cutoff.hasCompactSupport.smul_right
  have hG := eLpNorm_le_eLpNorm_fderiv_of_eq (volume : Measure Space) hgc hgs
    (p := 2) (p' := 6) (by norm_num) (by simp) (by simp; norm_num)
  have hm6 : MemLp g ((6 : NNReal) : ENNReal) volume := hgc.continuous.memLp_of_hasCompactSupport hgs
  have hm2 : MemLp (fderiv ℝ g) ((2 : NNReal) : ENNReal) volume :=
    (hgc.continuous_fderiv one_ne_zero).memLp_of_hasCompactSupport (hgs.fderiv (𝕜 := ℝ))
  rw [hm6.eLpNorm_eq_integral_rpow_norm (by simp) (by simp),
    hm2.eLpNorm_eq_integral_rpow_norm (by simp) (by simp)] at hG
  rw [show ((6 : NNReal) : ENNReal).toReal = 6 by simp,
    show ((2 : NNReal) : ENNReal).toReal = 2 by simp] at hG
  simp_rw [Real.rpow_two] at hG
  have hInt2 : 0 ≤ ∫ x, ‖fderiv ℝ g x‖ ^ 2 := integral_nonneg fun x => by positivity
  have hA : (∫ x, ‖g x‖ ^ (6 : ℝ)) ^ (6 : ℝ)⁻¹ ≤ (CG : ℝ) * (∫ x, ‖fderiv ℝ g x‖ ^ 2) ^ (2 : ℝ)⁻¹ := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)] at hG
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (NNReal.coe_nonneg _) (Real.rpow_nonneg hInt2 _))).1 hG
  have hi : Integrable (fun x => ‖g x‖ ^ (6 : ℝ)) := by
    have h := hm6.integrable_norm_rpow (by simp) (by simp)
    rwa [show ((6 : NNReal) : ENNReal).toReal = 6 by simp] at h
  set S := ∑ k ∈ s, weight k * ‖c k‖ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => mul_nonneg (by unfold weight; positivity) (sq_nonneg _)
  have hI : ∫ x, ‖fderiv ℝ g x‖ ^ 2 ≤ K * S := integral_fderiv_cutoff_sq_le hM s c
  calc (∫ x in cell, ‖∑ k ∈ s, character (-k) x • c k‖ ^ (6 : ℝ)) ^ (1 / 6 : ℝ)
      = (∫ x in cell, ‖g x‖ ^ (6 : ℝ)) ^ (1 / 6 : ℝ) := by rw [setIntegral_cell_eq]
    _ ≤ (∫ x, ‖g x‖ ^ (6 : ℝ)) ^ (1 / 6 : ℝ) :=
        Real.rpow_le_rpow (integral_nonneg fun x => by positivity)
          (setIntegral_le_integral hi (ae_of_all _ fun x => by positivity)) (by norm_num)
    _ ≤ (CG : ℝ) * (∫ x, ‖fderiv ℝ g x‖ ^ 2) ^ (1 / 2 : ℝ) := by
        rw [one_div, one_div]
        exact hA
    _ ≤ (CG : ℝ) * (K * S) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hInt2 hI (by norm_num)) (NNReal.coe_nonneg _)
    _ = (CG : ℝ) * K ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow hK.le hS]
        ring
    _ ≤ ((CG : ℝ) + 1) * K ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ) := by
        have h1 : 0 ≤ K ^ (1 / 2 : ℝ) := Real.rpow_nonneg hK.le _
        have h2 : 0 ≤ S ^ (1 / 2 : ℝ) := Real.rpow_nonneg hS _
        have h3 : 0 ≤ K ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ) := mul_nonneg h1 h2
        nlinarith

end Breakdown.Periodic
