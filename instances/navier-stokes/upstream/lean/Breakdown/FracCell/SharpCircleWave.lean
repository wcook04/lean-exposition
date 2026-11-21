import Breakdown.FracCell.CircleProduct
import Breakdown.FracCell.SliceMeasurable
import Breakdown.FracCell.SharpCircleStrain
import Breakdown.FracCell.GaugeFluxParts

open MeasureTheory ComplexConjugate

noncomputable section

namespace Breakdown.FracInternal.SharpCircleWave

open CellCert CellAnalysis SteadyCert Assembly CellAnalysis.CircleProduct

def realCoupling (M : Fin 3 → Fin 3 → ℝ) (a : Fin 3 → ℝ) (i l : Fin 3) : ℝ :=
  -(∑ j, permSign i l j * ∑ b, M j b * a b) + (1 / 2) * ∑ q, (∑ j, permSign i q j * a j) * M l q

theorem realCoupling_sq (M : Fin 3 → Fin 3 → ℝ) (a : Fin 3 → ℝ) (htr : M 0 0 + M 1 1 + M 2 2 = 0) :
    ∑ i, ∑ l, realCoupling M a i l ^ 2 = 7 / 4 * ∑ i, (∑ b, M i b * a b) ^ 2
      + 1 / 4 * (∑ i, ∑ j, M i j ^ 2) * ∑ b, a b ^ 2 + ∑ i, (∑ b, M i b * a b) * (∑ b, M b i * a b) := by
  have h22 : M 2 2 = -M 0 0 - M 1 1 := by linarith
  simp only [realCoupling, Fin.sum_univ_three, permSign, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two,
    Prod.mk.injEq]
  norm_num
  rw [h22]
  ring

private theorem sum_mul_sq_le_three (f g : Fin 3 → ℝ) : (∑ i, f i * g i) ^ 2 ≤ (∑ i, f i ^ 2) * ∑ i, g i ^ 2 :=
  Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem realCoupling_le (M : Fin 3 → Fin 3 → ℝ) (a : Fin 3 → ℝ) (htr : M 0 0 + M 1 1 + M 2 2 = 0)
    (δ : ℝ) (hδ : 0 ≤ δ) (hop : ∀ u : Fin 3 → ℝ, ∑ i, (∑ b, M i b * u b) ^ 2 ≤ δ ^ 2 * ∑ b, u b ^ 2) :
    ∑ i, ∑ l, realCoupling M a i l ^ 2 ≤ 7 / 2 * δ ^ 2 * ∑ b, a b ^ 2 := by
  rw [realCoupling_sq M a htr]
  have hF : ∑ i, ∑ j, M i j ^ 2 ≤ 3 * δ ^ 2 := by
    have h0 := hop ![1, 0, 0]
    have h1 := hop ![0, 1, 0]
    have h2 := hop ![0, 0, 1]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_fin_one] at h0 h1 h2 ⊢
    norm_num at h0 h1 h2
    nlinarith
  set A := ∑ b, a b ^ 2 with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun b _ => sq_nonneg _
  set w : Fin 3 → ℝ := fun i => ∑ b, M b i * a b with hw
  set X := ∑ i, w i ^ 2 with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun b _ => sq_nonneg _
  have hMw := hop w
  have hid : X = ∑ b, a b * ∑ i, M b i * w i := by
    simp only [hX, hw, Fin.sum_univ_three]
    ring
  have hcs := sum_mul_sq_le_three a (fun b => ∑ i, M b i * w i)
  have hXle : X ≤ δ ^ 2 * A := by
    rw [← hid] at hcs
    have : X ^ 2 ≤ A * (δ ^ 2 * X) := le_trans hcs (mul_le_mul_of_nonneg_left hMw hA0)
    rcases eq_or_lt_of_le hX0 with h | h
    · rw [← h]; positivity
    · nlinarith
  have hMa := hop a
  set Y := ∑ i, (∑ b, M i b * a b) ^ 2 with hY
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun b _ => sq_nonneg _
  have hcross := sum_mul_sq_le_three (fun i => ∑ b, M i b * a b) w
  set Z := ∑ i, (∑ b, M i b * a b) * w i with hZ
  have hZle : Z ≤ δ ^ 2 * A := by
    have : Z ^ 2 ≤ (δ ^ 2 * A) ^ 2 := by
      calc Z ^ 2 ≤ Y * X := hcross
        _ ≤ (δ ^ 2 * A) * (δ ^ 2 * A) := mul_le_mul hMa hXle hX0 (by positivity)
        _ = (δ ^ 2 * A) ^ 2 := by ring
    by_contra hc
    push Not at hc
    have hp : 0 ≤ δ ^ 2 * A := by positivity
    nlinarith
  nlinarith

theorem couplingMap_ofReal (Wr : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → ℂ) (i l : Fin 3) :
    couplingMap (fun a b => (Wr a b : ℂ)) v i l
      = (realCoupling Wr (fun b => (v b).re) i l : ℂ) + (realCoupling Wr (fun b => (v b).im) i l : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp [couplingMap, bracketMat, realCoupling, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im] <;> ring

theorem opBound_real (Wr : Fin 3 → Fin 3 → ℝ) (δ : ℝ) (hop : OpBound (fun a b => (Wr a b : ℂ)) δ) (u : Fin 3 → ℝ) :
    ∑ i, (∑ b, Wr i b * u b) ^ 2 ≤ δ ^ 2 * ∑ b, u b ^ 2 := by
  have h := hop (fun b => (u b : ℂ))
  have e1 : vecSq (matVec (fun a b => (Wr a b : ℂ)) (fun b => (u b : ℂ))) = ∑ i, (∑ b, Wr i b * u b) ^ 2 := by
    unfold vecSq matVec
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (∑ b, (Wr i b : ℂ) * (u b : ℂ)) = ((∑ b, Wr i b * u b : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have e2 : vecSq (fun b => (u b : ℂ)) = ∑ b, u b ^ 2 := by
    unfold vecSq
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [e1, e2] at h
  exact h

theorem sumSq_couplingMap_le (Wr : Fin 3 → Fin 3 → ℝ) (htr : Wr 0 0 + Wr 1 1 + Wr 2 2 = 0) (δ : ℝ)
    (hδ : 0 ≤ δ) (hop : OpBound (fun a b => (Wr a b : ℂ)) δ) (v : Fin 3 → ℂ) :
    sumSq (couplingMap (fun a b => (Wr a b : ℂ)) v) ≤ 7 / 2 * δ ^ 2 * vecSq v := by
  have hr := realCoupling_le Wr (fun b => (v b).re) htr δ hδ (opBound_real Wr δ hop)
  have hi := realCoupling_le Wr (fun b => (v b).im) htr δ hδ (opBound_real Wr δ hop)
  have e1 : sumSq (couplingMap (fun a b => (Wr a b : ℂ)) v)
      = ∑ i, ∑ l, realCoupling Wr (fun b => (v b).re) i l ^ 2 + ∑ i, ∑ l, realCoupling Wr (fun b => (v b).im) i l ^ 2 := by
    unfold sumSq
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [couplingMap_ofReal, Complex.sq_norm, Complex.normSq_add_mul_I]
  have e2 : vecSq v = ∑ b, (v b).re ^ 2 + ∑ b, (v b).im ^ 2 := by
    unfold vecSq
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [e1, e2]
  nlinarith

theorem entryPairing_norm_le (A s : Fin 3 → Fin 3 → ℂ) :
    ‖entryPairing A s‖ ≤ Real.sqrt (sumSq A) * Real.sqrt (sumSq s) := by
  have h1 : ‖entryPairing A s‖ ≤ ∑ a, ∑ b, ‖A a b‖ * ‖s a b‖ := by
    unfold entryPairing
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun b _ => ?_))
    rw [norm_mul, Complex.norm_conj]
  have h2 : (∑ a, ∑ b, ‖A a b‖ * ‖s a b‖) ^ 2 ≤ sumSq A * sumSq s := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3 × Fin 3))
      (fun q => ‖A q.1 q.2‖) (fun q => ‖s q.1 q.2‖)
    simp only [Fintype.sum_prod_type] at this
    unfold sumSq
    exact this
  have h3 : ∑ a, ∑ b, ‖A a b‖ * ‖s a b‖ ≤ Real.sqrt (sumSq A * sumSq s) :=
    (le_abs_self _).trans (Real.abs_le_sqrt h2)
  rw [Real.sqrt_mul (by unfold sumSq; positivity)] at h3
  exact h1.trans h3

theorem entryPairing_swap (s t : Fin 3 → Fin 3 → ℂ) : entryPairing s t = (starRingEnd ℂ) (entryPairing t s) := by
  unfold entryPairing
  simp only [map_sum, map_mul, Complex.conj_conj]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem pairing_le (Wr : Fin 3 → Fin 3 → ℝ) (htr : Wr 0 0 + Wr 1 1 + Wr 2 2 = 0) (δ : ℝ)
    (hδ : 0 ≤ δ) (hop : OpBound (fun a b => (Wr a b : ℂ)) δ) (v : Fin 3 → ℂ) (s : Fin 3 → Fin 3 → ℂ) :
    ‖entryPairing (couplingMap (fun a b => (Wr a b : ℂ)) v) s‖
      ≤ Exterior.traceFreeConst * δ * (Real.sqrt (vecSq v) * Real.sqrt (sumSq s)) := by
  refine (entryPairing_norm_le _ s).trans ?_
  have h1 : Real.sqrt (sumSq (couplingMap (fun a b => (Wr a b : ℂ)) v))
      ≤ Exterior.traceFreeConst * δ * Real.sqrt (vecSq v) := by
    refine (Real.sqrt_le_sqrt (sumSq_couplingMap_le Wr htr δ hδ hop v)).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq hδ]
    unfold Exterior.traceFreeConst
    ring
  calc Real.sqrt (sumSq (couplingMap (fun a b => (Wr a b : ℂ)) v)) * Real.sqrt (sumSq s)
      ≤ Exterior.traceFreeConst * δ * Real.sqrt (vecSq v) * Real.sqrt (sumSq s) :=
        mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
    _ = _ := by ring

def couplingCoef (i l x y z : Fin 3) : ℂ :=
  ((-(if y = z then permSign i l x else 0) + (1 / 2) * (if x = l then permSign i y z else 0) : ℝ) : ℂ)

theorem couplingMap_eq (G : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (i l : Fin 3) :
    couplingMap G v i l = ∑ x, ∑ y, ∑ z, couplingCoef i l x y z * (G x y * v z) := by
  fin_cases i <;> fin_cases l <;>
    simp [couplingMap, bracketMat, couplingCoef, Fin.sum_univ_three] <;> ring

theorem pairing_expand (G : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (s : Fin 3 → Fin 3 → ℂ) :
    entryPairing (couplingMap G v) s
      = ∑ i, ∑ l, ∑ x, ∑ y, ∑ z, couplingCoef i l x y z * (conj (s i l) * (G x y * v z)) := by
  unfold entryPairing
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [couplingMap_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  ring

theorem pairing_expand_swap (G : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (s : Fin 3 → Fin 3 → ℂ) :
    conj (entryPairing (couplingMap G v) s)
      = ∑ i, ∑ l, ∑ x, ∑ y, ∑ z, couplingCoef i l x y z * (conj (v z) * (conj (G x y) * s i l)) := by
  rw [pairing_expand]
  simp only [map_sum, map_mul, Complex.conj_conj]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  have : conj (couplingCoef i l x y z) = couplingCoef i l x y z := by
    unfold couplingCoef
    exact Complex.conj_ofReal _
  rw [this]
  ring

theorem hasSum_sum5 {f : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℤ → ℂ} {a : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ}
    (h : ∀ i l x y z, HasSum (f i l x y z) (a i l x y z)) :
    HasSum (fun n => ∑ i, ∑ l, ∑ x, ∑ y, ∑ z, f i l x y z n) (∑ i, ∑ l, ∑ x, ∑ y, ∑ z, a i l x y z) :=
  hasSum_sum fun i _ => hasSum_sum fun l _ => hasSum_sum fun x _ => hasSum_sum fun y _ =>
    hasSum_sum fun z _ => h i l x y z

section Circle

variable {T : ℝ} [hT : Fact (0 < T)]

theorem integral_sum5 {f : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → AddCircle T → ℂ}
    (h : ∀ i l x y z, Integrable (f i l x y z) AddCircle.haarAddCircle) :
    ∫ t, ∑ i, ∑ l, ∑ x, ∑ y, ∑ z, f i l x y z t ∂AddCircle.haarAddCircle
      = ∑ i, ∑ l, ∑ x, ∑ y, ∑ z, ∫ t, f i l x y z t ∂AddCircle.haarAddCircle := by
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun l _ => integrable_finset_sum _ fun x _ =>
    integrable_finset_sum _ fun y _ => integrable_finset_sum _ fun z _ => h i l x y z]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun l _ => integrable_finset_sum _ fun x _ =>
    integrable_finset_sum _ fun y _ => integrable_finset_sum _ fun z _ => h i l x y z]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_finset_sum _ fun x _ => integrable_finset_sum _ fun y _ => integrable_finset_sum _ fun z _ => h i l x y z]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_finset_sum _ fun y _ => integrable_finset_sum _ fun z _ => h i l x y z]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [integral_finset_sum _ fun z _ => h i l x y z]

theorem conj_mul_integrable (X : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) (Z : AddCircle T → ℂ)
    (hZ : MemLp Z 2 AddCircle.haarAddCircle) :
    Integrable (fun t => conj (X t) * Z t) AddCircle.haarAddCircle := by
  have h := L2.integrable_inner (𝕜 := ℂ) X (hZ.toLp Z)
  refine h.congr ?_
  filter_upwards [hZ.coeFn_toLp] with t ht
  rw [ht]
  simp [mul_comm]

end Circle

section Form

variable {T : ℝ} [hT : Fact (0 < T)] {m : ℕ} (hm : 1 ≤ m)
  (w : Fin 3 → Fin 3 → AddCircle T → ℂ) (hwm : ∀ x y, AEStronglyMeasurable (w x y) AddCircle.haarAddCircle)
  (δ : ℝ) (hwb : ∀ x y t, ‖w x y t‖ ≤ δ)
  (s : ℤ → Fin 3 → Fin 3 → ℂ) (hs : ∀ i l, Summable (fun n => ‖s n i l‖ ^ 2))
  (v : ℤ → Fin 3 → ℂ) (hv : ∀ z, Summable (fun n => ‖v n z‖ ^ 2))

include hwm hwb in
theorem form_first_inner (n : ℤ) :
    HasSum (fun n' => entryPairing (couplingMap (fun x y => fourierCoeff (w x y) ((n - n') * m)) (v n')) (s n))
      (∑ i, ∑ l, ∑ x, ∑ y, ∑ z, couplingCoef i l x y z * (conj (s n i l) *
        fourierCoeff (fun t => w x y t * lift (T := T) hm (fun n => v n z) (hv z) t) (n * m))) := by
  simp_rw [pairing_expand]
  exact hasSum_sum5 fun i l x y z =>
    ((inner_hasSum hm (w x y) (hwm x y) δ (hwb x y) _ (hv z) n).mul_left (conj (s n i l))).mul_left _

include hwm hwb in
theorem form_first :
    HasSum (fun n => ∑' n', entryPairing (couplingMap (fun x y => fourierCoeff (w x y) ((n - n') * m)) (v n')) (s n))
      (∫ t, ∑ i, ∑ l, ∑ x, ∑ y, ∑ z, couplingCoef i l x y z *
        (conj (lift (T := T) hm (fun n => s n i l) (hs i l) t) * (w x y t * lift (T := T) hm (fun n => v n z) (hv z) t))
        ∂AddCircle.haarAddCircle) := by
  simp_rw [(form_first_inner hm w hwm δ hwb s v hv _).tsum_eq]
  rw [integral_sum5]
  · simp_rw [integral_const_mul]
    exact hasSum_sum5 fun i l x y z => (outer_hasSum hm _ (hs i l) _
      (mul_memLp (w x y) (hwm x y) δ (hwb x y) _)).mul_left _
  · intro i l x y z
    exact (conj_mul_integrable _ _ (mul_memLp (w x y) (hwm x y) δ (hwb x y) _)).const_mul _

include hwm hwb in
theorem form_second_inner (hw : ∀ x y t, conj (w x y t) = w x y t) (n : ℤ) :
    HasSum (fun n' => entryPairing (s n') (couplingMap (fun x y => fourierCoeff (w x y) ((n' - n) * m)) (v n)))
      (∑ i, ∑ l, ∑ x, ∑ y, ∑ z, couplingCoef i l x y z * (conj (v n z) *
        fourierCoeff (fun t => w x y t * lift (T := T) hm (fun n => s n i l) (hs i l) t) (n * m))) := by
  have hc : ∀ x y k, conj (fourierCoeff (w x y) k) = fourierCoeff (w x y) (-k) := by
    intro x y k
    simp only [fourierCoeff, neg_neg]
    rw [← integral_conj]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp [fourier_neg, hw]
  have e : ∀ n' : ℤ, entryPairing (s n') (couplingMap (fun x y => fourierCoeff (w x y) ((n' - n) * m)) (v n))
      = ∑ i, ∑ l, ∑ x, ∑ y, ∑ z, couplingCoef i l x y z * (conj (v n z) *
        (fourierCoeff (w x y) ((n - n') * m) * s n' i l)) := by
    intro n'
    rw [entryPairing_swap, pairing_expand_swap]
    simp only [hc]
    rw [show -((n' - n) * (m : ℤ)) = (n - n') * m by ring]
  rw [funext e]
  exact hasSum_sum5 fun i l x y z =>
    ((inner_hasSum hm (w x y) (hwm x y) δ (hwb x y) _ (hs i l) n).mul_left (conj (v n z))).mul_left _

end Form

section Form2

variable {T : ℝ} [hT : Fact (0 < T)] {m : ℕ} (hm : 1 ≤ m)
  (w : Fin 3 → Fin 3 → AddCircle T → ℂ) (hwm : ∀ x y, AEStronglyMeasurable (w x y) AddCircle.haarAddCircle)
  (δ : ℝ) (hwb : ∀ x y t, ‖w x y t‖ ≤ δ)
  (s : ℤ → Fin 3 → Fin 3 → ℂ) (hs : ∀ i l, Summable (fun n => ‖s n i l‖ ^ 2))
  (v : ℤ → Fin 3 → ℂ) (hv : ∀ z, Summable (fun n => ‖v n z‖ ^ 2))

include hwm hwb in
theorem form_second (hw : ∀ x y t, conj (w x y t) = w x y t) :
    HasSum (fun n => ∑' n', entryPairing (s n') (couplingMap (fun x y => fourierCoeff (w x y) ((n' - n) * m)) (v n)))
      (∫ t, ∑ i, ∑ l, ∑ x, ∑ y, ∑ z, couplingCoef i l x y z *
        (conj (lift (T := T) hm (fun n => v n z) (hv z) t) * (w x y t * lift (T := T) hm (fun n => s n i l) (hs i l) t))
        ∂AddCircle.haarAddCircle) := by
  simp_rw [(form_second_inner hm w hwm δ hwb s hs v hw _).tsum_eq]
  rw [integral_sum5]
  · simp_rw [integral_const_mul]
    exact hasSum_sum5 fun i l x y z => (outer_hasSum hm _ (hv z) _
      (mul_memLp (w x y) (hwm x y) δ (hwb x y) _)).mul_left _
  · intro i l x y z
    exact (conj_mul_integrable _ _ (mul_memLp (w x y) (hwm x y) δ (hwb x y) _)).const_mul _

theorem sqrt_mul_le_avg (a b ℓ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hℓ : 0 < ℓ) :
    Real.sqrt a * Real.sqrt b ≤ (ℓ * b + a / ℓ) / 2 := by
  have hx := Real.sq_sqrt ha
  have hy := Real.sq_sqrt hb
  set x := Real.sqrt a
  set y := Real.sqrt b
  have h : 0 ≤ (ℓ * y - x) ^ 2 / ℓ := div_nonneg (sq_nonneg _) hℓ.le
  have e : (ℓ * y - x) ^ 2 / ℓ = ℓ * y ^ 2 - 2 * (x * y) + x ^ 2 / ℓ := by
    field_simp
    ring
  rw [← hx, ← hy]
  linarith

theorem lift_sumSq_integral :
    ∫ t, sumSq (fun i l => lift (T := T) hm (fun n => s n i l) (hs i l) t) ∂AddCircle.haarAddCircle
      = ∑' n, sumSq (s n) := by
  unfold sumSq
  have hI : ∀ i l, Integrable (fun t => ‖lift (T := T) hm (fun n => s n i l) (hs i l) t‖ ^ 2) AddCircle.haarAddCircle :=
    fun i l => (memLp_two_iff_integrable_sq_norm (Lp.memLp _).1).1 (Lp.memLp _)
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun l _ => hI i l]
  simp_rw [integral_finset_sum _ fun l _ => hI _ l, lift_sq]
  rw [Summable.tsum_finsetSum fun i _ => summable_sum fun l _ => hs i l]
  exact Finset.sum_congr rfl fun i _ => (Summable.tsum_finsetSum fun l _ => hs i l).symm

theorem lift_vecSq_integral :
    ∫ t, vecSq (fun z => lift (T := T) hm (fun n => v n z) (hv z) t) ∂AddCircle.haarAddCircle
      = ∑' n, vecSq (v n) := by
  unfold vecSq
  have hI : ∀ z, Integrable (fun t => ‖lift (T := T) hm (fun n => v n z) (hv z) t‖ ^ 2) AddCircle.haarAddCircle :=
    fun z => (memLp_two_iff_integrable_sq_norm (Lp.memLp _).1).1 (Lp.memLp _)
  rw [integral_finset_sum _ fun z _ => hI z]
  simp_rw [lift_sq]
  exact (Summable.tsum_finsetSum fun z _ => hv z).symm

theorem form_bound (C ℓ : ℝ) (hC : 0 ≤ C) (hℓ : 0 < ℓ) (E : AddCircle T → ℂ)
    (hE : ∀ t, ‖E t‖ ≤ C * (Real.sqrt (vecSq (fun z => lift (T := T) hm (fun n => v n z) (hv z) t))
      * Real.sqrt (sumSq (fun i l => lift (T := T) hm (fun n => s n i l) (hs i l) t)))) :
    ‖∫ t, E t ∂AddCircle.haarAddCircle‖ ≤ C * ((ℓ * ∑' n, sumSq (s n) + (∑' n, vecSq (v n)) / ℓ) / 2) := by
  set Sq := fun t => sumSq (fun i l => lift (T := T) hm (fun n => s n i l) (hs i l) t)
  set Vq := fun t => vecSq (fun z => lift (T := T) hm (fun n => v n z) (hv z) t)
  have hSi : Integrable Sq AddCircle.haarAddCircle := by
    refine integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun l _ => ?_
    exact (memLp_two_iff_integrable_sq_norm (Lp.memLp _).1).1 (Lp.memLp _)
  have hVi : Integrable Vq AddCircle.haarAddCircle := by
    refine integrable_finset_sum _ fun z _ => ?_
    exact (memLp_two_iff_integrable_sq_norm (Lp.memLp _).1).1 (Lp.memLp _)
  have hg : Integrable (fun t => C * ((ℓ * Sq t + Vq t / ℓ) / 2)) AddCircle.haarAddCircle :=
    (((hSi.const_mul ℓ).add (hVi.div_const ℓ)).div_const 2).const_mul C
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _) hg (ae_of_all _ fun t => ?_)).trans (le_of_eq ?_)
  · refine (hE t).trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact sqrt_mul_le_avg _ _ ℓ (by unfold vecSq; positivity) (by unfold sumSq; positivity) hℓ
  · rw [integral_const_mul, integral_div, integral_add (hSi.const_mul ℓ) (hVi.div_const ℓ), integral_const_mul,
      integral_div]
    simp only [Sq, Vq]
    rw [lift_sumSq_integral hm s hs, lift_vecSq_integral hm v hv]

end Form2

section Pointwise

theorem opBound_entry (M : Fin 3 → Fin 3 → ℂ) (δ : ℝ) (hδ : 0 ≤ δ) (h : OpBound M δ) (a b : Fin 3) :
    ‖M a b‖ ≤ δ := by
  have h1 := h (Pi.single b 1)
  have e1 : vecSq (Pi.single b (1 : ℂ)) = 1 := by
    unfold vecSq
    rw [Finset.sum_eq_single b (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
    simp
  have e2 : ‖M a b‖ ^ 2 ≤ vecSq (matVec M (Pi.single b 1)) := by
    unfold vecSq
    have : matVec M (Pi.single b 1) a = M a b := by
      unfold matVec
      rw [Finset.sum_eq_single b (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
      simp
    rw [← this]
    exact Finset.single_le_sum (f := fun i => ‖matVec M (Pi.single b 1) i‖ ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ a)
  rw [e1, mul_one] at h1
  have h2 := e2.trans h1
  by_contra hc
  push Not at hc
  nlinarith [norm_nonneg (M a b)]

theorem sq_entry_le (s : Fin 3 → Fin 3 → ℂ) (i l : Fin 3) : ‖s i l‖ ^ 2 ≤ sumSq s := by
  unfold sumSq
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ b : Fin 3, ‖s i b‖ ^ 2)
    (fun i _ => Finset.sum_nonneg fun b _ => sq_nonneg _) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun b => ‖s i b‖ ^ 2) (fun b _ => sq_nonneg _) (Finset.mem_univ l)

theorem sq_vec_le (v : Fin 3 → ℂ) (z : Fin 3) : ‖v z‖ ^ 2 ≤ vecSq v := by
  unfold vecSq
  exact Finset.single_le_sum (f := fun b => ‖v b‖ ^ 2) (fun b _ => sq_nonneg _) (Finset.mem_univ z)

theorem couplingMap_zero (v : Fin 3 → ℂ) : couplingMap 0 v = 0 := by
  funext i l
  simp [couplingMap, bracketMat]

theorem entryPairing_zero_left (s : Fin 3 → Fin 3 → ℂ) : entryPairing 0 s = 0 := by
  simp [entryPairing]

theorem entryPairing_zero_right (s : Fin 3 → Fin 3 → ℂ) : entryPairing s 0 = 0 := by
  simp [entryPairing]

end Pointwise

section Circle2

variable {T : ℝ} [hT : Fact (0 < T)]

theorem integral_circleMode_eq (n : ℤ) :
    ∫ t, fourier (-n) t ∂(AddCircle.haarAddCircle (T := T)) = if n = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (orthonormal_fourier (T := T))) n 0
  rw [inner_eq] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_fourierLp (T := T) 2 n, coeFn_fourierLp (T := T) 2 0] with t h1 h2
  rw [h1, h2, fourier_zero, mul_one, fourier_neg]

theorem coeff_sub_const (f : AddCircle T → ℂ) (hf : Integrable f AddCircle.haarAddCircle) (c : ℂ) (n : ℤ) :
    fourierCoeff (fun t => f t - c) n = fourierCoeff f n - (if n = 0 then c else 0) := by
  have hi1 : Integrable (fun t => fourier (-n) t • f t) AddCircle.haarAddCircle := by
    refine hf.norm.mono' ((fourier (T := T) (-n)).continuous.aestronglyMeasurable.smul hf.1) (ae_of_all _ fun t => ?_)
    simp [norm_smul, Circle.norm_coe]
  have hi2 : Integrable (fun t : AddCircle T => fourier (-n) t • c) AddCircle.haarAddCircle := by
    refine Integrable.of_bound ((fourier (T := T) (-n)).continuous.aestronglyMeasurable.smul aestronglyMeasurable_const)
      ‖c‖ (ae_of_all _ fun t => ?_)
    simp [norm_smul, Circle.norm_coe]
  unfold fourierCoeff
  simp_rw [smul_sub]
  rw [integral_sub hi1 hi2, integral_smul_const, integral_circleMode_eq]
  split_ifs <;> simp

end Circle2

theorem half_re (z1 z2 : ℂ) (X : ℝ) (h1 : ‖z1‖ ≤ X) (h2 : ‖z2‖ ≤ X) :
    -X ≤ ((1 / 2 : ℂ) * z1 + (1 / 2 : ℂ) * z2).re := by
  have a1 := Complex.abs_re_le_norm z1
  have a2 := Complex.abs_re_le_norm z2
  have e : ((1 / 2 : ℂ) * z1 + (1 / 2 : ℂ) * z2).re = z1.re / 2 + z2.re / 2 := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  rw [e]
  linarith [neg_abs_le z1.re, neg_abs_le z2.re]

section Total

variable {T : ℝ} [hT : Fact (0 < T)] {m : ℕ} (hm : 1 ≤ m)
  (w : Fin 3 → Fin 3 → AddCircle T → ℂ) (hwm : ∀ x y, AEStronglyMeasurable (w x y) AddCircle.haarAddCircle)
  (δ : ℝ) (hwb : ∀ x y t, ‖w x y t‖ ≤ δ)
  (s : ℤ → Fin 3 → Fin 3 → ℂ) (hs : ∀ i l, Summable (fun n => ‖s n i l‖ ^ 2))
  (v : ℤ → Fin 3 → ℂ) (hv : ∀ z, Summable (fun n => ‖v n z‖ ^ 2))

include hm hwm hwb hs hv in
theorem form_total (hw : ∀ x y t, conj (w x y t) = w x y t)
    (Wr : AddCircle T → Fin 3 → Fin 3 → ℝ) (hWr : ∀ a b t, w a b t = (Wr t a b : ℂ))
    (htr : ∀ t, Wr t 0 0 + Wr t 1 1 + Wr t 2 2 = 0) (hδ : 0 ≤ δ)
    (hopR : ∀ t, OpBound (fun a b => (Wr t a b : ℂ)) δ) (ℓ : ℝ) (hℓ : 0 < ℓ) (Q : ℤ → ℤ → ℂ)
    (hQ : ∀ n n', Q n n' = (1 / 2 : ℂ) * entryPairing (couplingMap (fun x y => fourierCoeff (w x y) ((n - n') * m))
        (v n')) (s n)
      + (1 / 2 : ℂ) * entryPairing (s n') (couplingMap (fun x y => fourierCoeff (w x y) ((n' - n) * m)) (v n))) :
    (∀ n, Summable (Q n)) ∧ Summable (fun n => ∑' n', Q n n') ∧
      -(Exterior.traceFreeConst * δ * ((ℓ * ∑' n, sumSq (s n) + (∑' n, vecSq (v n)) / ℓ) / 2))
        ≤ (∑' n, ∑' n', Q n n').re := by
  have HI1 := form_first_inner hm w hwm δ hwb s v hv
  have HI2 := form_second_inner hm w hwm δ hwb s hs v hw
  have HT1 := form_first hm w hwm δ hwb s hs v hv
  have HT2 := form_second hm w hwm δ hwb s hs v hv hw
  have HQ : ∀ n, HasSum (Q n) _ := fun n => by
    rw [show Q n = _ from funext (hQ n)]
    exact ((HI1 n).mul_left (1 / 2 : ℂ)).add ((HI2 n).mul_left (1 / 2 : ℂ))
  refine ⟨fun n => (HQ n).summable, ?_⟩
  have hrow : (fun n => ∑' n', Q n n') = fun n =>
      (1 / 2 : ℂ) * (∑' n', entryPairing (couplingMap (fun x y => fourierCoeff (w x y) ((n - n') * m)) (v n')) (s n))
      + (1 / 2 : ℂ) * (∑' n', entryPairing (s n') (couplingMap (fun x y => fourierCoeff (w x y) ((n' - n) * m)) (v n))) := by
    funext n
    rw [(HQ n).tsum_eq, (HI1 n).tsum_eq, (HI2 n).tsum_eq]
  have HT := (HT1.mul_left (1 / 2 : ℂ)).add (HT2.mul_left (1 / 2 : ℂ))
  rw [← hrow] at HT
  refine ⟨HT.summable, ?_⟩
  rw [HT.tsum_eq]
  have hC : 0 ≤ Exterior.traceFreeConst * δ := mul_nonneg (Real.sqrt_nonneg _) hδ
  have hpt : ∀ t, ‖entryPairing (couplingMap (fun x y => w x y t) (fun z => lift (T := T) hm (fun n => v n z) (hv z) t))
      (fun i l => lift (T := T) hm (fun n => s n i l) (hs i l) t)‖
      ≤ Exterior.traceFreeConst * δ * (Real.sqrt (vecSq (fun z => lift (T := T) hm (fun n => v n z) (hv z) t))
        * Real.sqrt (sumSq (fun i l => lift (T := T) hm (fun n => s n i l) (hs i l) t))) := by
    intro t
    have e : (fun x y => w x y t) = fun a b => (Wr t a b : ℂ) := funext fun a => funext fun b => hWr a b t
    rw [e]
    exact pairing_le (Wr t) (htr t) δ hδ (hopR t) _ _
  refine half_re _ _ _ ?_ ?_
  · refine form_bound hm s hs v hv _ ℓ hC hℓ _ (fun t => ?_)
    have h := hpt t
    rw [pairing_expand] at h
    exact h
  · refine form_bound hm s hs v hv _ ℓ hC hℓ _ (fun t => ?_)
    have h := hpt t
    rw [← Complex.norm_conj, pairing_expand_swap] at h
    simp only [hw] at h
    exact h

end Total

end Breakdown.FracInternal.SharpCircleWave

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly SharpParts SharpSupremumParts SharpCircleBoundParts CircleProduct
open Breakdown.FracInternal.SharpCircleWave
open Real

attribute [local instance] CircleProduct.pi_fact

theorem sharpCircleWave_holds : SharpCircleWaveStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hwt x hx
  have hK := hd.box
  have hm : 1 ≤ c.order := le_trans (by norm_num) hc.base.order_ge
  have hm0 : (c.order : ℤ) ≠ 0 := by exact_mod_cast (show c.order ≠ 0 by omega)
  filter_upwards [SliceMeasurable.slice_aesm K hK hc.model_measurable.2.2.2,
    SharpCircleStrainParts.interior_ae K, SharpCircleStrainParts.fst_ne_ae K] with p hsl hpI hp0 hq hv
  have hδ : 0 ≤ S.waveGradBound p := (hd.scalars.grad_bounds_nonneg p).2
  have hℓ : 0 < S.splitLength := hd.scalars.splitLength_pos
  set δ := S.waveGradBound p with hδdef
  set ℓ := S.splitLength with hℓdef
  set f : Fin 3 → Fin 3 → ℝ → ℂ := fun a b θ => (frameMat θ (c.modelCurlGrad (cylPoint p.1 θ p.2)) a b : ℂ)
    with hf
  set F : Fin 3 → Fin 3 → AddCircle (π - -π) → ℂ := fun a b => AddCircle.liftIoc (π - -π) (-π) (f a b) with hF
  set g0 : Fin 3 → Fin 3 → ℂ := fun a b => modeMat c.order 0 c.modelCurlGrad p.1 p.2 a b with hg0
  set w : Fin 3 → Fin 3 → AddCircle (π - -π) → ℂ := fun a b t => F a b t - g0 a b with hwdef
  have hθ : ∀ t : AddCircle (π - -π), ∃ θ : ℝ, ∀ a b, F a b t = f a b θ := fun t =>
    ⟨((AddCircle.equivIoc (π - -π) (-π) t : Set.Ioc (-π) (-π + (π - -π))) : ℝ), fun _ _ => rfl⟩
  have hwave : ∀ θ, OpBound (fun a b => f a b θ - g0 a b) δ := fun θ => hd.wave_le p hpI hp0 θ
  have hop : ∀ t, OpBound (fun a b => w a b t) δ := by
    intro t
    obtain ⟨θ, hθt⟩ := hθ t
    have e : (fun a b => w a b t) = fun a b => f a b θ - g0 a b := by
      funext a b
      simp only [hwdef, hθt]
    rw [e]
    exact hwave θ
  have hwb : ∀ a b t, ‖w a b t‖ ≤ δ := fun a b t => opBound_entry _ δ hδ (hop t) a b
  have hfb : ∀ a b θ, ‖f a b θ‖ ≤ δ + ‖g0 a b‖ := by
    intro a b θ
    have h := opBound_entry _ δ hδ (hwave θ) a b
    calc ‖f a b θ‖ = ‖(f a b θ - g0 a b) + g0 a b‖ := by rw [sub_add_cancel]
      _ ≤ ‖f a b θ - g0 a b‖ + ‖g0 a b‖ := norm_add_le _ _
      _ ≤ δ + ‖g0 a b‖ := by linarith
  have hFm : ∀ a b, AEStronglyMeasurable (F a b) AddCircle.haarAddCircle := by
    intro a b
    have hset : Set.Ioc (-π) (-π + (π - -π)) = Set.Ioc (-π) π := by ring_nf
    have hL : MemLp (f a b) 2 (volume.restrict (Set.Ioc (-π) (-π + (π - -π)))) := by
      rw [hset]
      exact MemLp.of_bound (hsl a b) (δ + ‖g0 a b‖) (ae_of_all _ fun θ => hfb a b θ)
    exact hL.memLp_liftIoc.haarAddCircle.1
  have hFb : ∀ a b t, ‖F a b t‖ ≤ δ + ‖g0 a b‖ := by
    intro a b t
    obtain ⟨θ, h⟩ := hθ t
    rw [h]
    exact hfb a b θ
  have hFi : ∀ a b, Integrable (F a b) AddCircle.haarAddCircle := fun a b =>
    Integrable.of_bound (hFm a b) (δ + ‖g0 a b‖) (ae_of_all _ fun t => hFb a b t)
  have hwm : ∀ a b, AEStronglyMeasurable (w a b) AddCircle.haarAddCircle := fun a b =>
    (hFm a b).sub aestronglyMeasurable_const
  have hmode : ∀ β a b, modeMat c.order β c.modelCurlGrad p.1 p.2 a b = fourierCoeff (F a b) (β * c.order) :=
    fun β a b => mode_coeff c.order β c.modelCurlGrad a b p
  have hcoef : ∀ β a b, fourierCoeff (w a b) (β * c.order)
      = if β = 0 then 0 else CellScalars.curlGradMode c β p a b := by
    intro β a b
    have e : fourierCoeff (w a b) (β * c.order) = fourierCoeff (fun t => F a b t - g0 a b) (β * c.order) := rfl
    rw [e, coeff_sub_const (F a b) (hFi a b) (g0 a b), ← hmode]
    by_cases hβ : β = 0
    · subst hβ
      simp [hg0]
    · have hβm : β * (c.order : ℤ) ≠ 0 := mul_ne_zero hβ hm0
      simp [hβ, hβm, CellScalars.curlGradMode]
  have hFr : ∀ a b t, (F a b t).im = 0 := by
    intro a b t
    obtain ⟨θ, h⟩ := hθ t
    rw [h]
    simp only [hf, Complex.ofReal_im]
  have hg0r : ∀ a b, (g0 a b).im = 0 := by
    intro a b
    simp only [hg0]
    rw [CellFormula.Internal.GaugeFluxParts.modeMat_zero]
    exact Complex.ofReal_im _
  set Wr : AddCircle (π - -π) → Fin 3 → Fin 3 → ℝ := fun t a b => (w a b t).re with hWrdef
  have hWr : ∀ a b t, w a b t = (Wr t a b : ℂ) := by
    intro a b t
    apply Complex.ext
    · simp [hWrdef]
    · simp only [hWrdef, Complex.ofReal_im, hwdef, Complex.sub_im, hFr, hg0r, sub_self]
  have hwc : ∀ a b t, conj (w a b t) = w a b t := by
    intro a b t
    rw [hWr]
    exact Complex.conj_ofReal _
  have hFsum : ∀ t, F 0 0 t + F 1 1 t + F 2 2 t = 0 := by
    intro t
    obtain ⟨θ, h⟩ := hθ t
    rw [h, h, h]
    simp only [hf]
    have e1 := CellFormula.Internal.GaugeFluxParts.frame_trace θ (c.modelCurlGrad (cylPoint p.1 θ p.2))
    have e2 := hd.curlGrad_traceFree p ⟨⟨hpI.1.1.le, hpI.1.2.le⟩, ⟨hpI.2.1.le, hpI.2.2.le⟩⟩ hp0 θ
    have e3 : ∑ i : Fin 3, inner ℝ (c.modelCurlGrad (cylPoint p.1 θ p.2) (unitVector i)) (unitVector i)
        = ∑ i : Fin 3, entry (c.modelCurlGrad (cylPoint p.1 θ p.2)) i i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [entry, unitVector, EuclideanSpace.inner_single_right]
    have e4 := e1.trans (e3.trans e2)
    exact_mod_cast e4
  have hg0sum : g0 0 0 + g0 1 1 + g0 2 2 = 0 := by
    have e : ∀ a, g0 a a = fourierCoeff (F a a) 0 := by
      intro a
      simp only [hg0]
      rw [hmode]
      simp
    have a1 := congrFun (fourierCoeff.add (hFi 0 0) (hFi 1 1)) 0
    have a2 := congrFun (fourierCoeff.add ((hFi 0 0).add (hFi 1 1)) (hFi 2 2)) 0
    simp only [Pi.add_apply] at a1 a2
    have : (F 0 0 + F 1 1 + F 2 2) = 0 := by
      funext t
      exact hFsum t
    rw [e, e, e, ← a1, ← a2, this]
    simp [fourierCoeff]
  have htr : ∀ t, Wr t 0 0 + Wr t 1 1 + Wr t 2 2 = 0 := by
    intro t
    simp only [hWrdef, hwdef, Complex.sub_re]
    have h1 := congrArg Complex.re (hFsum t)
    have h2 := congrArg Complex.re hg0sum
    simp only [Complex.add_re, Complex.zero_re] at h1 h2
    linarith
  have hopR : ∀ t, OpBound (fun a b => (Wr t a b : ℂ)) δ := by
    intro t
    have e : (fun a b => (Wr t a b : ℂ)) = fun a b => w a b t := by
      funext a b
      rw [hWr]
    rw [e]
    exact hop t
  have hs : ∀ i l, Summable (fun n => ‖sharpGrad c K S x n p i l‖ ^ 2) := fun i l =>
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => sq_entry_le _ i l) hq
  have hvv : ∀ z, Summable (fun n => ‖sharpVel c K S x n p z‖ ^ 2) := fun z =>
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => sq_vec_le _ z) hv
  have hoff : ∀ n n', offWave c K S x n n' p
      = (1 / 2 : ℂ) * entryPairing (couplingMap (fun a b => fourierCoeff (w a b) ((n - n') * c.order))
          (sharpVel c K S x n' p)) (sharpGrad c K S x n p)
        + (1 / 2 : ℂ) * entryPairing (sharpGrad c K S x n' p)
          (couplingMap (fun a b => fourierCoeff (w a b) ((n' - n) * c.order)) (sharpVel c K S x n p)) := by
    intro n n'
    simp only [hcoef]
    unfold offWave couplingWave
    by_cases h : n' = n
    · subst h
      simp [couplingMap, bracketMat, entryPairing]
    · have h1 : n - n' ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
      have h2 : n' - n ≠ 0 := sub_ne_zero.mpr h
      simp only [h, h1, h2, if_false]
  obtain ⟨A1, A2, A3⟩ := form_total hm w hwm δ hwb (fun n => sharpGrad c K S x n p) hs
    (fun n => sharpVel c K S x n p) hvv hwc Wr hWr htr hδ hopR ℓ hℓ (fun n n' => offWave c K S x n n' p) hoff
  refine ⟨A1, A2, le_trans (le_of_eq ?_) A3⟩
  have hwl : ∑' n, waveLoss c K S x n p = Exterior.traceFreeConst * δ
      * ((ℓ * ∑' n, sumSq (sharpGrad c K S x n p) + (∑' n, vecSq (sharpVel c K S x n p)) / ℓ) / 2) := by
    unfold waveLoss
    rw [tsum_mul_left, Summable.tsum_add (hq.mul_left _) (hv.div_const _), tsum_mul_left, tsum_div_const]
    ring
  rw [hwl]

end Breakdown.CellCert.CellAnalysis
