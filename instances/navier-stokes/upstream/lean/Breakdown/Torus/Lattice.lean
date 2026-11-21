import Breakdown.Defs

open MeasureTheory Real

noncomputable section

namespace Breakdown.Periodic

abbrev Lattice := Fin 3 → ℤ

abbrev Coef := EuclideanSpace ℂ (Fin 3)

abbrev Seq := lp (fun _ : Lattice => Coef) 2

def freq (k : Lattice) : Space := ∑ i, (k i : ℝ) • unitVector i

def latVec (k : Lattice) : Coef := WithLp.toLp 2 (fun i => ((k i : ℤ) : ℂ))

def weight (k : Lattice) : ℝ := 1 + 4 * π ^ 2 * ‖freq k‖ ^ 2

def heatFactor (t : ℝ) (k : Lattice) : ℝ := Real.exp (-(4 * π ^ 2 * ‖freq k‖ ^ 2 * max t 0))

def divPairing (k : Lattice) (c : Coef) : ℂ := ∑ i, (k i : ℂ) * c i

def divFree (k : Lattice) (c : Coef) : Coef :=
  if k = 0 then c else c - (divPairing k c / ((‖freq k‖ ^ 2 : ℝ) : ℂ)) • latVec k

private lemma divPairing_add (k : Lattice) (c d : Coef) :
    divPairing k (c + d) = divPairing k c + divPairing k d := by
  simp [divPairing, mul_add, Finset.sum_add_distrib]

private lemma divPairing_sub (k : Lattice) (c d : Coef) :
    divPairing k (c - d) = divPairing k c - divPairing k d := by
  simp [divPairing, mul_sub, Finset.sum_sub_distrib]

private lemma divPairing_csmul (k : Lattice) (z : ℂ) (c : Coef) :
    divPairing k (z • c) = z * divPairing k c := by
  simp only [divPairing, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private lemma divPairing_smul (k : Lattice) (r : ℝ) (c : Coef) :
    divPairing k (r • c) = (r : ℂ) * divPairing k c := by
  rw [← divPairing_csmul, Complex.coe_smul]

private lemma divPairing_zero (k : Lattice) : divPairing k 0 = 0 := by
  simp [divPairing]

private lemma divPairing_neg (k : Lattice) (c : Coef) : divPairing (-k) c = -divPairing k c := by
  simp [divPairing, Finset.sum_neg_distrib]

private lemma divPairing_of_conj {c d : Coef} (h : ∀ i, c i = starRingEnd ℂ (d i)) (k : Lattice) :
    divPairing k c = starRingEnd ℂ (divPairing k d) := by
  simp [divPairing, h, map_sum]

def fieldSpace : Submodule ℝ Seq where
  carrier := {a | (∀ k i, (a (-k)) i = starRingEnd ℂ ((a k) i)) ∧ ∀ k, divPairing k (a k) = 0}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun k i => ?_, fun k => ?_⟩
    · simp [ha k i, hb k i]
    · rw [lp.coeFn_add, Pi.add_apply, divPairing_add, ha' k, hb' k, add_zero]
  zero_mem' := ⟨fun k i => by simp, fun k => by simp [divPairing]⟩
  smul_mem' := by
    rintro r a ⟨ha, ha'⟩
    refine ⟨fun k i => ?_, fun k => ?_⟩
    · simp [ha k i, Complex.real_smul]
    · rw [lp.coeFn_smul, Pi.smul_apply, divPairing_smul, ha' k, mul_zero]

private lemma mem_fieldSpace {a : Seq} :
    a ∈ fieldSpace ↔ (∀ k i, (a (-k)) i = starRingEnd ℂ ((a k) i)) ∧ ∀ k, divPairing k (a k) = 0 :=
  Iff.rfl

private lemma continuous_eval (k : Lattice) : Continuous fun a : Seq => a k :=
  (continuous_apply k).comp (lp.uniformContinuous_coe (E := fun _ : Lattice => Coef) (p := 2)).continuous

private lemma continuous_divPairing (k : Lattice) : Continuous (divPairing k) := by
  unfold divPairing
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (PiLp.continuous_apply 2 _ i)

theorem isClosed_fieldSpace : IsClosed (fieldSpace : Set Seq) := by
  have h : (fieldSpace : Set Seq) = (⋂ k, ⋂ i, {a : Seq | (a (-k)) i = starRingEnd ℂ ((a k) i)}) ∩
      ⋂ k, {a : Seq | divPairing k (a k) = 0} := by
    ext a
    simp only [SetLike.mem_coe, mem_fieldSpace, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [h]
  refine (isClosed_iInter fun k => isClosed_iInter fun i => isClosed_eq ?_ ?_).inter
    (isClosed_iInter fun k => isClosed_eq ((continuous_divPairing k).comp (continuous_eval k)) continuous_const)
  · exact (PiLp.continuous_apply 2 _ i).comp (continuous_eval (-k))
  · exact Complex.continuous_conj.comp ((PiLp.continuous_apply 2 _ i).comp (continuous_eval k))

abbrev V := fieldSpace

instance : CompleteSpace V := isClosed_fieldSpace.completeSpace_coe

def coeff (u : V) (k : Lattice) : Coef := (Real.sqrt (weight k))⁻¹ • (u : Seq) k

private lemma two_toReal : (2 : ENNReal).toReal = 2 := by norm_num

private lemma norm_le_of_pointwise {F : Lattice → Type*} [∀ k, NormedAddCommGroup (F k)]
    {f : Seq} {g : lp F 2} {C : ℝ} (hC : 0 ≤ C) (h : ∀ k, ‖f k‖ ≤ C * ‖g k‖) : ‖f‖ ≤ C * ‖g‖ := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  refine lp.norm_le_of_forall_sum_le hp (mul_nonneg hC (norm_nonneg g)) fun s => ?_
  calc ∑ i ∈ s, ‖f i‖ ^ (2 : ENNReal).toReal ≤ ∑ i ∈ s, (C * ‖g i‖) ^ (2 : ENNReal).toReal :=
        Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (norm_nonneg _) (h i) hp.le
    _ = C ^ (2 : ENNReal).toReal * ∑ i ∈ s, ‖g i‖ ^ (2 : ENNReal).toReal := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Real.mul_rpow hC (norm_nonneg _)
    _ ≤ C ^ (2 : ENNReal).toReal * ‖g‖ ^ (2 : ENNReal).toReal :=
        mul_le_mul_of_nonneg_left (lp.sum_rpow_le_norm_rpow hp g s) (Real.rpow_nonneg hC _)
    _ = (C * ‖g‖) ^ (2 : ENNReal).toReal := (Real.mul_rpow hC (norm_nonneg _)).symm

theorem memℓp_mul (m : Lattice → ℝ) {C : ℝ} (hm : ∀ k, |m k| ≤ C) (a : Seq) :
    Memℓp (fun k => m k • a k) 2 := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hm 0)
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  refine memℓp_gen (Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (((lp.memℓp a).summable hp).mul_left (C ^ (2 : ENNReal).toReal)))
  rw [norm_smul, Real.norm_eq_abs, Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (abs_nonneg _) (hm k) hp.le) (by positivity)

def mulSeq (m : Lattice → ℝ) {C : ℝ} (hC : 0 ≤ C) (hm : ∀ k, |m k| ≤ C) : Seq →L[ℝ] Seq :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟨fun k => m k • a k, memℓp_mul m hm a⟩
      map_add' := fun a b => lp.ext <| funext fun k => by
        show m k • (a + b) k = m k • a k + m k • b k
        rw [lp.coeFn_add, Pi.add_apply, smul_add]
      map_smul' := fun r a => lp.ext <| funext fun k => by
        show m k • (r • a) k = r • (m k • a k)
        rw [lp.coeFn_smul, Pi.smul_apply, smul_comm] } C
    (fun a => norm_le_of_pointwise hC fun k => by
      show ‖m k • a k‖ ≤ C * ‖a k‖
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hm k) (norm_nonneg _))

private lemma mulSeq_apply (m : Lattice → ℝ) {C : ℝ} (hC : 0 ≤ C) (hm : ∀ k, |m k| ≤ C) (a : Seq)
    (k : Lattice) : mulSeq m hC hm a k = m k • a k := rfl

theorem abs_heatFactor_le (t : ℝ) (k : Lattice) : |heatFactor t k| ≤ 1 := by
  rw [heatFactor, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
  have := le_max_right t 0
  positivity

private lemma freq_neg (k : Lattice) : freq (-k) = -freq k := by
  simp [freq, Finset.sum_neg_distrib]

private lemma weight_neg (k : Lattice) : weight (-k) = weight k := by
  rw [weight, weight, freq_neg, norm_neg]

private lemma heatFactor_neg (t : ℝ) (k : Lattice) : heatFactor t (-k) = heatFactor t k := by
  rw [heatFactor, heatFactor, freq_neg, norm_neg]

theorem heat_mem (t : ℝ) (a : V) :
    mulSeq (heatFactor t) zero_le_one (abs_heatFactor_le t) (a : Seq) ∈ fieldSpace := by
  obtain ⟨ha, ha'⟩ := mem_fieldSpace.mp a.2
  refine mem_fieldSpace.mpr ⟨fun k i => ?_, fun k => ?_⟩
  · rw [mulSeq_apply, mulSeq_apply, heatFactor_neg, PiLp.smul_apply, PiLp.smul_apply, ha k i]
    simp [Complex.real_smul]
  · rw [mulSeq_apply, divPairing_smul, ha' k, mul_zero]

def heat (t : ℝ) : V →L[ℝ] V :=
  ((mulSeq (heatFactor t) zero_le_one (abs_heatFactor_le t)).comp fieldSpace.subtypeL).codRestrict
    fieldSpace (heat_mem t)

def advCoef (u v : V) (k : Lattice) : Coef :=
  ∑' j, ((2 * π : ℝ) * Complex.I * divPairing j (coeff u (k - j))) • coeff v j

def kernelSeq (τ : ℝ) (u v : V) (k : Lattice) : Coef :=
  if 0 < τ then
    (-(1 / 2) * Real.sqrt (weight k) * heatFactor τ k) • divFree k (advCoef u v k + advCoef v u k)
  else 0

namespace Internal

private lemma freq_apply (k : Lattice) (i : Fin 3) : freq k i = k i := by
  simp [freq, unitVector, Pi.single_apply]

private lemma norm_freq_sq (k : Lattice) : ‖freq k‖ ^ 2 = ∑ i, ((k i : ℝ)) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [freq_apply, sq_abs]

private lemma latVec_apply (k : Lattice) (i : Fin 3) : latVec k i = (k i : ℂ) := rfl

private lemma norm_latVec (k : Lattice) : ‖latVec k‖ = ‖freq k‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp [freq_apply, latVec_apply, Complex.norm_intCast]

private lemma divPairing_eq_inner (k : Lattice) (c : Coef) : divPairing k c = inner ℂ (latVec k) c := by
  simp [divPairing, latVec_apply, PiLp.inner_apply, mul_comm]

private lemma norm_divPairing_le (k : Lattice) (c : Coef) : ‖divPairing k c‖ ≤ ‖freq k‖ * ‖c‖ := by
  rw [divPairing_eq_inner, ← norm_latVec]
  exact norm_inner_le_norm _ _

private lemma weight_pos (k : Lattice) : 0 < weight k := by
  unfold weight
  positivity

private lemma two_pi_le_sqrt (k : Lattice) : 2 * π * ‖freq k‖ ≤ Real.sqrt (weight k) := by
  apply Real.le_sqrt_of_sq_le
  have e : (2 * π * ‖freq k‖) ^ 2 = 4 * π ^ 2 * ‖freq k‖ ^ 2 := by ring
  rw [e, weight]
  linarith

private lemma norm_coeff (u : V) (k : Lattice) :
    ‖coeff u k‖ = (Real.sqrt (weight k))⁻¹ * ‖(u : Seq) k‖ := by
  rw [coeff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

private lemma norm_coeff_le (u : V) (k : Lattice) : ‖coeff u k‖ ≤ ‖(u : Seq) k‖ := by
  have h1 : 1 ≤ Real.sqrt (weight k) := by
    apply Real.le_sqrt_of_sq_le
    have : 0 ≤ 4 * π ^ 2 * ‖freq k‖ ^ 2 := by positivity
    rw [weight]
    linarith
  rw [norm_coeff]
  exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ h1)

private def advTerm (u v : V) (k j : Lattice) : Coef :=
  ((2 * π : ℝ) * Complex.I * divPairing j (coeff u (k - j))) • coeff v j

private lemma advCoef_eq (u v : V) (k : Lattice) : advCoef u v k = ∑' j, advTerm u v k j := rfl

private lemma norm_advTerm_le (u v : V) (k j : Lattice) :
    ‖advTerm u v k j‖ ≤ ‖(u : Seq) (k - j)‖ * ‖(v : Seq) j‖ := by
  have hs : 0 < Real.sqrt (weight j) := Real.sqrt_pos.mpr (weight_pos j)
  have key : 2 * π * ‖divPairing j (coeff u (k - j))‖ ≤ Real.sqrt (weight j) * ‖(u : Seq) (k - j)‖ :=
    calc 2 * π * ‖divPairing j (coeff u (k - j))‖ ≤ 2 * π * (‖freq j‖ * ‖coeff u (k - j)‖) :=
          mul_le_mul_of_nonneg_left (norm_divPairing_le _ _) (by positivity)
      _ = (2 * π * ‖freq j‖) * ‖coeff u (k - j)‖ := by ring
      _ ≤ Real.sqrt (weight j) * ‖(u : Seq) (k - j)‖ :=
          mul_le_mul (two_pi_le_sqrt j) (norm_coeff_le u _) (norm_nonneg _) hs.le
  rw [advTerm, norm_smul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), norm_coeff]
  calc 2 * π * ‖divPairing j (coeff u (k - j))‖ * ((Real.sqrt (weight j))⁻¹ * ‖(v : Seq) j‖)
      = (2 * π * ‖divPairing j (coeff u (k - j))‖) * (Real.sqrt (weight j))⁻¹ * ‖(v : Seq) j‖ := by
        ring
    _ ≤ (Real.sqrt (weight j) * ‖(u : Seq) (k - j)‖) * (Real.sqrt (weight j))⁻¹ * ‖(v : Seq) j‖ := by
        gcongr
    _ = ‖(u : Seq) (k - j)‖ * ‖(v : Seq) j‖ := by field_simp

private lemma summable_sq (a : Seq) : Summable fun j => ‖a j‖ ^ (2 : ℝ) := by
  have h := (lp.memℓp a).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  rwa [two_toReal] at h

private lemma summable_sq_shift (a : Seq) (k : Lattice) : Summable fun j => ‖a (k - j)‖ ^ (2 : ℝ) :=
  (Equiv.subLeft k).summable_iff.mpr (summable_sq a)

private lemma tsum_sq (a : Seq) : ∑' j, ‖a j‖ ^ (2 : ℝ) = ‖a‖ ^ (2 : ℝ) := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) a
  rw [two_toReal] at h
  exact h.symm

private lemma lpProd (a b : Seq) (k : Lattice) :
    Summable (fun j => ‖a (k - j)‖ * ‖b j‖) ∧ ∑' j, ‖a (k - j)‖ * ‖b j‖ ≤ ‖a‖ * ‖b‖ := by
  obtain ⟨h1, h2⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (fun j => norm_nonneg (a (k - j))) (fun j => norm_nonneg (b j)) (summable_sq_shift a k)
    (summable_sq b)
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  have e : ∑' j, ‖a (k - j)‖ ^ (2 : ℝ) = ‖a‖ ^ (2 : ℝ) := by
    rw [← tsum_sq a]
    exact (Equiv.subLeft k).tsum_eq (fun i => ‖a i‖ ^ (2 : ℝ))
  rw [e, tsum_sq, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_mul (norm_nonneg _)]
  norm_num

private lemma summable_norm_advTerm (u v : V) (k : Lattice) : Summable fun j => ‖advTerm u v k j‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_advTerm_le u v k) (lpProd (u : Seq) (v : Seq) k).1

private lemma summable_advTerm (u v : V) (k : Lattice) : Summable (advTerm u v k) :=
  Summable.of_norm (summable_norm_advTerm u v k)

private lemma norm_advCoef_le (u v : V) (k : Lattice) : ‖advCoef u v k‖ ≤ ‖u‖ * ‖v‖ := by
  have hs := lpProd (u : Seq) (v : Seq) k
  calc ‖advCoef u v k‖ ≤ ∑' j, ‖advTerm u v k j‖ := norm_tsum_le_tsum_norm (summable_norm_advTerm u v k)
    _ ≤ ∑' j, ‖(u : Seq) (k - j)‖ * ‖(v : Seq) j‖ :=
        Summable.tsum_le_tsum (norm_advTerm_le u v k) (summable_norm_advTerm u v k) hs.1
    _ ≤ ‖(u : Seq)‖ * ‖(v : Seq)‖ := hs.2
    _ = ‖u‖ * ‖v‖ := rfl

private lemma coeff_add (u u' : V) (k : Lattice) : coeff (u + u') k = coeff u k + coeff u' k := by
  simp [coeff, smul_add]

private lemma coeff_smul (r : ℝ) (u : V) (k : Lattice) : coeff (r • u) k = r • coeff u k := by
  rw [coeff, coeff, Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, smul_comm]

private lemma advCoef_add_left (u u' v : V) (k : Lattice) :
    advCoef (u + u') v k = advCoef u v k + advCoef u' v k := by
  have e : advTerm (u + u') v k = fun j => advTerm u v k j + advTerm u' v k j := funext fun j => by
    simp only [advTerm, coeff_add, divPairing_add, mul_add, add_smul]
  rw [advCoef_eq, advCoef_eq, advCoef_eq, e]
  exact (summable_advTerm u v k).tsum_add (summable_advTerm u' v k)

private lemma advCoef_add_right (u v v' : V) (k : Lattice) :
    advCoef u (v + v') k = advCoef u v k + advCoef u v' k := by
  have e : advTerm u (v + v') k = fun j => advTerm u v k j + advTerm u v' k j := funext fun j => by
    simp only [advTerm, coeff_add, smul_add]
  rw [advCoef_eq, advCoef_eq, advCoef_eq, e]
  exact (summable_advTerm u v k).tsum_add (summable_advTerm u v' k)

private lemma advCoef_smul_left (r : ℝ) (u v : V) (k : Lattice) :
    advCoef (r • u) v k = r • advCoef u v k := by
  have e : advTerm (r • u) v k = fun j => r • advTerm u v k j := funext fun j => by
    simp only [advTerm, coeff_smul, divPairing_smul]
    rw [← Complex.coe_smul, smul_smul]
    congr 1
    ring
  rw [advCoef_eq, advCoef_eq, e]
  exact (summable_advTerm u v k).tsum_const_smul r

private lemma advCoef_smul_right (r : ℝ) (u v : V) (k : Lattice) :
    advCoef u (r • v) k = r • advCoef u v k := by
  have e : advTerm u (r • v) k = fun j => r • advTerm u v k j := funext fun j => by
    simp only [advTerm, coeff_smul]
    exact smul_comm _ _ _
  rw [advCoef_eq, advCoef_eq, e]
  exact (summable_advTerm u v k).tsum_const_smul r

private lemma divFree_add (k : Lattice) (c d : Coef) : divFree k (c + d) = divFree k c + divFree k d := by
  unfold divFree
  split_ifs
  · rfl
  · rw [divPairing_add, add_div, add_smul]
    abel

private lemma divFree_smul (k : Lattice) (r : ℝ) (c : Coef) : divFree k (r • c) = r • divFree k c := by
  unfold divFree
  split_ifs
  · rfl
  · rw [divPairing_smul, smul_sub, mul_div_assoc, mul_smul, Complex.coe_smul]

private lemma kernelSeq_add_left (τ : ℝ) (u u' v : V) (k : Lattice) :
    kernelSeq τ (u + u') v k = kernelSeq τ u v k + kernelSeq τ u' v k := by
  unfold kernelSeq
  split_ifs
  · rw [advCoef_add_left, advCoef_add_right, add_add_add_comm, divFree_add, smul_add]
  · simp

private lemma kernelSeq_add_right (τ : ℝ) (u v v' : V) (k : Lattice) :
    kernelSeq τ u (v + v') k = kernelSeq τ u v k + kernelSeq τ u v' k := by
  unfold kernelSeq
  split_ifs
  · rw [advCoef_add_left, advCoef_add_right, add_add_add_comm, divFree_add, smul_add]
  · simp

private lemma kernelSeq_smul_left (τ r : ℝ) (u v : V) (k : Lattice) :
    kernelSeq τ (r • u) v k = r • kernelSeq τ u v k := by
  unfold kernelSeq
  split_ifs
  · rw [advCoef_smul_left, advCoef_smul_right, ← smul_add, divFree_smul]
    exact smul_comm _ _ _
  · simp

private lemma kernelSeq_smul_right (τ r : ℝ) (u v : V) (k : Lattice) :
    kernelSeq τ u (r • v) k = r • kernelSeq τ u v k := by
  unfold kernelSeq
  split_ifs
  · rw [advCoef_smul_left, advCoef_smul_right, ← smul_add, divFree_smul]
    exact smul_comm _ _ _
  · simp

private lemma apply_tsum {f : Lattice → Coef} (hf : Summable f) (i : Fin 3) :
    (∑' j, f j) i = ∑' j, f j i :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => ℂ) i).map_tsum hf

private lemma coeff_neg (u : V) (m : Lattice) (i : Fin 3) :
    coeff u (-m) i = starRingEnd ℂ (coeff u m i) := by
  obtain ⟨hu, -⟩ := mem_fieldSpace.mp u.2
  simp only [coeff, PiLp.smul_apply, weight_neg, hu m i]
  simp [Complex.real_smul]

private lemma advCoef_neg (u v : V) (k : Lattice) (i : Fin 3) :
    advCoef u v (-k) i = starRingEnd ℂ (advCoef u v k i) := by
  rw [advCoef_eq, advCoef_eq, apply_tsum (summable_advTerm u v (-k)),
    apply_tsum (summable_advTerm u v k), RCLike.conj_tsum,
    ← (Equiv.neg Lattice).tsum_eq (fun j => advTerm u v (-k) j i)]
  congr 1
  funext j
  simp only [Equiv.neg_apply, advTerm, PiLp.smul_apply, smul_eq_mul]
  rw [show -k - -j = -(k - j) by abel, divPairing_neg, divPairing_of_conj (coeff_neg u (k - j)),
    coeff_neg v j i]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

private lemma divFree_neg_conj {c d : Coef} (h : ∀ i, c i = starRingEnd ℂ (d i)) (k : Lattice) (i : Fin 3) :
    divFree (-k) c i = starRingEnd ℂ (divFree k d i) := by
  by_cases hk : k = 0
  · subst hk
    simp [divFree, h]
  · have hk' : -k ≠ 0 := neg_ne_zero.mpr hk
    simp only [divFree, hk, hk', if_false, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, divPairing_neg,
      divPairing_of_conj h, freq_neg, norm_neg, latVec_apply, h i]
    simp [map_sub, map_mul, map_div₀]
    ring

private lemma freq_ne_zero {k : Lattice} (hk : k ≠ 0) : ‖freq k‖ ^ 2 ≠ 0 := by
  rw [norm_freq_sq]
  intro h
  apply hk
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ((k i : ℝ)))).mp h i
    (Finset.mem_univ _)
  show k i = 0
  simpa using this

private lemma divPairing_latVec (k : Lattice) : divPairing k (latVec k) = ((‖freq k‖ ^ 2 : ℝ) : ℂ) := by
  rw [norm_freq_sq]
  push_cast
  simp [divPairing, latVec_apply, sq]

private lemma divPairing_divFree (k : Lattice) (c : Coef) : divPairing k (divFree k c) = 0 := by
  unfold divFree
  split_ifs with hk
  · subst hk
    simp [divPairing]
  · rw [divPairing_sub, divPairing_csmul, divPairing_latVec, div_mul_cancel₀, sub_self]
    exact Complex.ofReal_ne_zero.mpr (freq_ne_zero hk)

private lemma norm_divFree_le (k : Lattice) (c : Coef) : ‖divFree k c‖ ≤ 2 * ‖c‖ := by
  unfold divFree
  split_ifs with hk
  · linarith [norm_nonneg c]
  · have hf : 0 < ‖freq k‖ :=
      (norm_nonneg _).lt_of_ne (fun h => freq_ne_zero hk (by rw [← h]; ring))
    calc ‖c - (divPairing k c / ((‖freq k‖ ^ 2 : ℝ) : ℂ)) • latVec k‖
        ≤ ‖c‖ + ‖divPairing k c / ((‖freq k‖ ^ 2 : ℝ) : ℂ)‖ * ‖latVec k‖ :=
          (norm_sub_le _ _).trans (le_of_eq (by rw [norm_smul]))
      _ = ‖c‖ + ‖divPairing k c‖ / ‖freq k‖ ^ 2 * ‖freq k‖ := by
          rw [norm_div, Complex.norm_real, norm_latVec, Real.norm_of_nonneg (sq_nonneg _)]
      _ ≤ ‖c‖ + (‖freq k‖ * ‖c‖) / ‖freq k‖ ^ 2 * ‖freq k‖ := by
          gcongr
          exact norm_divPairing_le k c
      _ = 2 * ‖c‖ := by
          field_simp
          ring

private lemma norm_kernelSeq_sq {τ : ℝ} (hτ : 0 < τ) (u v : V) (k : Lattice) :
    ‖kernelSeq τ u v k‖ ^ 2 ≤ 4 * (‖u‖ * ‖v‖) ^ 2 * (weight k * heatFactor τ k ^ 2) := by
  have hX : ‖advCoef u v k + advCoef v u k‖ ≤ 2 * (‖u‖ * ‖v‖) :=
    (norm_add_le _ _).trans (by linarith [norm_advCoef_le u v k, norm_advCoef_le v u k, mul_comm ‖u‖ ‖v‖])
  have hs0 : 0 ≤ Real.sqrt (weight k) * heatFactor τ k :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  have hb : ‖kernelSeq τ u v k‖ ≤ Real.sqrt (weight k) * heatFactor τ k * (2 * (‖u‖ * ‖v‖)) := by
    rw [kernelSeq, if_pos hτ, norm_smul, Real.norm_eq_abs]
    have e : |-(1 / 2) * Real.sqrt (weight k) * heatFactor τ k| =
        1 / 2 * (Real.sqrt (weight k) * heatFactor τ k) := by
      rw [show -(1 / 2) * Real.sqrt (weight k) * heatFactor τ k =
        -(1 / 2 * (Real.sqrt (weight k) * heatFactor τ k)) by ring, abs_neg,
        abs_of_nonneg (mul_nonneg (by norm_num) hs0)]
    rw [e]
    calc 1 / 2 * (Real.sqrt (weight k) * heatFactor τ k) * ‖divFree k (advCoef u v k + advCoef v u k)‖
        ≤ 1 / 2 * (Real.sqrt (weight k) * heatFactor τ k) * (2 * (2 * (‖u‖ * ‖v‖))) :=
          mul_le_mul_of_nonneg_left ((norm_divFree_le _ _).trans (by linarith))
            (mul_nonneg (by norm_num) hs0)
      _ = Real.sqrt (weight k) * heatFactor τ k * (2 * (‖u‖ * ‖v‖)) := by ring
  calc ‖kernelSeq τ u v k‖ ^ 2 ≤ (Real.sqrt (weight k) * heatFactor τ k * (2 * (‖u‖ * ‖v‖))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = 4 * (‖u‖ * ‖v‖) ^ 2 * (weight k * heatFactor τ k ^ 2) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (weight_pos k).le]
        ring

private lemma real_bound {τ x : ℝ} (hτ : 0 < τ) (hx : 0 ≤ x) :
    (1 + 4 * π ^ 2 * x) * Real.exp (-(4 * π ^ 2 * x * τ)) ^ 2 ≤
      (1 + 1 / τ) * Real.exp (-(4 * π ^ 2 * x * τ)) := by
  have hy : 0 ≤ 4 * π ^ 2 * x * τ := by positivity
  have h1 : 1 + 4 * π ^ 2 * x ≤ (1 + 1 / τ) * (1 + 4 * π ^ 2 * x * τ) := by
    have e : (1 + 1 / τ) * (1 + 4 * π ^ 2 * x * τ) = 1 + 4 * π ^ 2 * x * τ + 1 / τ + 4 * π ^ 2 * x := by
      field_simp
      ring
    rw [e]
    have : 0 < 1 / τ := by positivity
    linarith
  have h2 := Real.add_one_le_exp (4 * π ^ 2 * x * τ)
  have h3 : Real.exp (4 * π ^ 2 * x * τ) * Real.exp (-(4 * π ^ 2 * x * τ)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hE := Real.exp_pos (-(4 * π ^ 2 * x * τ))
  calc (1 + 4 * π ^ 2 * x) * Real.exp (-(4 * π ^ 2 * x * τ)) ^ 2
      ≤ ((1 + 1 / τ) * Real.exp (4 * π ^ 2 * x * τ)) * Real.exp (-(4 * π ^ 2 * x * τ)) ^ 2 :=
        mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity)))
          (by positivity)
    _ = (1 + 1 / τ) * (Real.exp (4 * π ^ 2 * x * τ) * Real.exp (-(4 * π ^ 2 * x * τ))) *
          Real.exp (-(4 * π ^ 2 * x * τ)) := by ring
    _ = (1 + 1 / τ) * Real.exp (-(4 * π ^ 2 * x * τ)) := by rw [h3, mul_one]

private lemma weight_heat_le {τ : ℝ} (hτ : 0 < τ) (k : Lattice) :
    weight k * heatFactor τ k ^ 2 ≤ (1 + 1 / τ) * heatFactor τ k := by
  have := real_bound (x := ‖freq k‖ ^ 2) hτ (sq_nonneg _)
  rw [weight, heatFactor, max_eq_left hτ.le]
  exact this

private lemma summable_expSq_int {c : ℝ} (hc : 0 < c) : Summable fun n : ℤ => Real.exp (-(c * (n : ℝ) ^ 2)) := by
  have hr : Summable fun n : ℕ => Real.exp (-c) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le ((Real.exp_lt_exp.mpr (neg_neg_of_pos hc)).trans_eq Real.exp_zero)
  have hb : ∀ n : ℕ, Real.exp (-(c * (((n : ℤ) : ℝ)) ^ 2)) ≤ Real.exp (-c) ^ n := fun n => by
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    push_cast
    have : (n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero n
    nlinarith
  refine Summable.of_nat_of_neg ?_ ?_
  · exact Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) hb hr
  · refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hr
    simpa using hb n

private lemma summable_prod_fin (g : ℤ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (hg : Summable g) :
    ∀ n : ℕ, Summable fun k : Fin n → ℤ => ∏ i, g (k i)
  | 0 => Summable.of_finite
  | n + 1 => by
    have h := hg.mul_of_nonneg (summable_prod_fin g hg0 hg n) (fun m => hg0 m)
      (fun k => Finset.prod_nonneg fun i _ => hg0 _)
    exact (Fin.consEquiv fun _ => ℤ).summable_iff.mp
      (h.congr fun x => by simp [Fin.consEquiv, Fin.prod_univ_succ])

private lemma summable_heat {τ : ℝ} (hτ : 0 < τ) : Summable (heatFactor τ) := by
  have c0 : 0 < 4 * π ^ 2 * τ := by positivity
  refine (summable_prod_fin _ (fun n => (Real.exp_pos _).le) (summable_expSq_int c0) 3).congr
    fun k => ?_
  rw [heatFactor, max_eq_left hτ.le, norm_freq_sq, ← Real.exp_sum, Finset.sum_neg_distrib,
    ← Finset.mul_sum]
  congr 1
  ring

private lemma summable_weight_heat {τ : ℝ} (hτ : 0 < τ) : Summable fun k => weight k * heatFactor τ k ^ 2 :=
  Summable.of_nonneg_of_le (fun k => mul_nonneg (weight_pos k).le (sq_nonneg _)) (weight_heat_le hτ)
    ((summable_heat hτ).mul_left _)

private lemma memℓp_of_sq_bound {c : Lattice → Coef} {M : ℝ} {g : Lattice → ℝ} (hg : Summable g)
    (h : ∀ k, ‖c k‖ ^ 2 ≤ M * g k) : Memℓp c 2 := by
  refine memℓp_gen (Summable.of_nonneg_of_le (fun k => Real.rpow_nonneg (norm_nonneg _) _)
    (fun k => ?_) (hg.mul_left M))
  rw [two_toReal, Real.rpow_two]
  exact h k

private lemma norm_le_of_sq_bound {c : Seq} {M : ℝ} (hM : 0 ≤ M) {g : Lattice → ℝ} (hg0 : ∀ k, 0 ≤ g k)
    (hg : Summable g) (h : ∀ k, ‖c k‖ ^ 2 ≤ M * g k) : ‖c‖ ≤ Real.sqrt (M * ∑' k, g k) := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  refine lp.norm_le_of_tsum_le hp (Real.sqrt_nonneg _) ?_
  rw [two_toReal, Real.rpow_two, Real.sq_sqrt (mul_nonneg hM (tsum_nonneg hg0)), ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k => ?_) (summable_sq c) (hg.mul_left M)
  rw [Real.rpow_two]
  exact h k

end Internal

open Internal

theorem memℓp_kernelSeq (τ : ℝ) (u v : V) : Memℓp (kernelSeq τ u v) 2 := by
  by_cases hτ : 0 < τ
  · exact memℓp_of_sq_bound (summable_weight_heat hτ) (norm_kernelSeq_sq hτ u v)
  · have e : kernelSeq τ u v = 0 := funext fun k => by simp [kernelSeq, hτ]
    rw [e]
    exact zero_memℓp

theorem kernelSeq_mem (τ : ℝ) (u v : V) :
    (⟨kernelSeq τ u v, memℓp_kernelSeq τ u v⟩ : Seq) ∈ fieldSpace := by
  refine mem_fieldSpace.mpr ⟨fun k i => ?_, fun k => ?_⟩
  · show kernelSeq τ u v (-k) i = starRingEnd ℂ (kernelSeq τ u v k i)
    unfold kernelSeq
    split_ifs
    · have hX : ∀ i, (advCoef u v (-k) + advCoef v u (-k)) i =
          starRingEnd ℂ ((advCoef u v k + advCoef v u k) i) := fun i => by
        rw [PiLp.add_apply, PiLp.add_apply, advCoef_neg, advCoef_neg, map_add]
      rw [PiLp.smul_apply, PiLp.smul_apply, weight_neg, heatFactor_neg, divFree_neg_conj hX k i,
        Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal]
    · simp
  · show divPairing k (kernelSeq τ u v k) = 0
    unfold kernelSeq
    split_ifs
    · rw [divPairing_smul, divPairing_divFree, mul_zero]
    · exact divPairing_zero k

def kernelV (τ : ℝ) (u v : V) : V := ⟨⟨kernelSeq τ u v, memℓp_kernelSeq τ u v⟩, kernelSeq_mem τ u v⟩

theorem kernelV_crude (τ : ℝ) : ∃ C : ℝ, ∀ u v : V, ‖kernelV τ u v‖ ≤ C * ‖u‖ * ‖v‖ := by
  by_cases hτ : 0 < τ
  · refine ⟨2 * Real.sqrt (∑' k, weight k * heatFactor τ k ^ 2), fun u v => ?_⟩
    have hle := norm_le_of_sq_bound (c := (kernelV τ u v : Seq)) (M := 4 * (‖u‖ * ‖v‖) ^ 2)
      (by positivity) (fun k => mul_nonneg (weight_pos k).le (sq_nonneg _)) (summable_weight_heat hτ)
      (fun k => norm_kernelSeq_sq hτ u v k)
    calc ‖kernelV τ u v‖ = ‖(kernelV τ u v : Seq)‖ := rfl
      _ ≤ Real.sqrt (4 * (‖u‖ * ‖v‖) ^ 2 * ∑' k, weight k * heatFactor τ k ^ 2) := hle
      _ = 2 * Real.sqrt (∑' k, weight k * heatFactor τ k ^ 2) * ‖u‖ * ‖v‖ := by
        rw [Real.sqrt_mul (by positivity), show (4 : ℝ) * (‖u‖ * ‖v‖) ^ 2 = (2 * (‖u‖ * ‖v‖)) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
        ring
  · refine ⟨0, fun u v => ?_⟩
    have e : kernelV τ u v = 0 := Subtype.ext (lp.ext (funext fun k => by
      show kernelSeq τ u v k = 0
      simp [kernelSeq, hτ]))
    rw [e]
    exact (le_of_eq norm_zero).trans (le_of_eq (by ring))

namespace Internal

private lemma kernelV_ext {x y : V} (h : ∀ k, (x : Seq) k = (y : Seq) k) : x = y :=
  Subtype.ext (lp.ext (funext h))

private lemma kernelV_add_left (τ : ℝ) (u u' v : V) : kernelV τ (u + u') v = kernelV τ u v + kernelV τ u' v :=
  kernelV_ext fun k => kernelSeq_add_left τ u u' v k

private lemma kernelV_smul_left (τ r : ℝ) (u v : V) : kernelV τ (r • u) v = r • kernelV τ u v :=
  kernelV_ext fun k => kernelSeq_smul_left τ r u v k

private lemma kernelV_add_right (τ : ℝ) (u v v' : V) : kernelV τ u (v + v') = kernelV τ u v + kernelV τ u v' :=
  kernelV_ext fun k => kernelSeq_add_right τ u v v' k

private lemma kernelV_smul_right (τ r : ℝ) (u v : V) : kernelV τ u (r • v) = r • kernelV τ u v :=
  kernelV_ext fun k => kernelSeq_smul_right τ r u v k

end Internal

def kernel (τ : ℝ) : V →L[ℝ] V →L[ℝ] V :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (kernelV τ) (kernelV_add_left τ) (kernelV_smul_left τ) (kernelV_add_right τ)
      (kernelV_smul_right τ))
    (kernelV_crude τ).choose (kernelV_crude τ).choose_spec

end Breakdown.Periodic
