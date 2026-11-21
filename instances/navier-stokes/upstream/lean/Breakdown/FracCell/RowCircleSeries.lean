import Breakdown.FracCell.RowModeUnfolded
import Breakdown.FracCell.CircleSliceCoupling
import Breakdown.FracCell.CircleSliceRegular
import Breakdown.FracCell.FieldModeSquare

open MeasureTheory Real ComplexConjugate

noncomputable section

namespace Breakdown.FracInternal.RowCircleSeries

open CellCert CellAnalysis SteadyCert Assembly DensitySlice CircleSliceCoupling

def crossR (u w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![u 1 * w 2 - u 2 * w 1, u 2 * w 0 - u 0 * w 2, u 0 * w 1 - u 1 * w 0]

def adjR (u : Fin 3 → ℝ) (l j : Fin 3) : ℝ := ∑ i : Fin 3, permSign i j l * u i

theorem ii_of {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * π)))) :
    IntervalIntegrable f volume 0 (2 * π) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le circle_len_pos.le]
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  exact hf.integrable (by norm_num)

theorem memLp_mul_b {w g : ℝ → ℝ} (hw : AEStronglyMeasurable w (volume.restrict (Set.Ioc 0 (2 * π))))
    {C : ℝ} (hC : ∀ θ, |w θ| ≤ C) (hg : MemLp g 2 (volume.restrict (Set.Ioc 0 (2 * π)))) :
    MemLp (fun θ => g θ * w θ) 2 (volume.restrict (Set.Ioc 0 (2 * π))) := by
  have e : (fun θ => g θ * w θ) = fun θ => w θ * g θ := funext fun θ => mul_comm _ _
  rw [e]
  exact bounded_memLp hw hC hg

theorem cf_sub (m : ℕ) (n : ℤ) {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 (2 * π))
    (hg : IntervalIntegrable g volume 0 (2 * π)) :
    cf m n (fun θ => f θ - g θ) = cf m n f - cf m n g := by
  unfold cf circleCoeff
  have e : ∀ θ : ℝ, Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * ((f θ - g θ : ℝ) : ℂ) =
      Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * (f θ : ℂ)
        - Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * (g θ : ℂ) := fun θ => by push_cast; ring
  have hc : Continuous fun θ : ℝ => Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) := by fun_prop
  have i1 : IntervalIntegrable (fun θ => Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * (f θ : ℂ))
      volume 0 (2 * π) :=
    (show IntervalIntegrable (fun θ => (f θ : ℂ)) volume 0 (2 * π) from ⟨hf.1.ofReal, hf.2.ofReal⟩).continuousOn_mul
      hc.continuousOn
  have i2 : IntervalIntegrable (fun θ => Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * (g θ : ℂ))
      volume 0 (2 * π) :=
    (show IntervalIntegrable (fun θ => (g θ : ℂ)) volume 0 (2 * π) from ⟨hg.1.ofReal, hg.2.ofReal⟩).continuousOn_mul
      hc.continuousOn
  simp only [e]
  rw [intervalIntegral.integral_sub i1 i2, mul_sub]

theorem conv_fin {m : ℕ} (hm : 0 < m) {w g : ℝ → ℝ} (hw : MemLp w 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (hg : IsCircleSliceRegular m g) (hgp : ∀ θ, g (θ + 2 * π) = g θ) (s : Finset ℤ)
    (hs : ∀ n ∉ s, cf m n g = 0) (n : ℤ) :
    cf m n (fun θ => w θ * g θ) = ∑ n' ∈ s, conj (cf m (n' - n) w) * cf m n' g := by
  have H := atom_inner hm hw hg hgp n
  have H2 : HasSum (fun n' : ℤ => cf m (n - n') w * cf m n' g) (∑ n' ∈ s, cf m (n - n') w * cf m n' g) :=
    hasSum_sum_of_ne_finset_zero fun n' hn' => by rw [hs n' hn', mul_zero]
  rw [H.unique H2]
  exact Finset.sum_congr rfl fun n' _ => by rw [cf_conj]

theorem conv_fin' {m : ℕ} (hm : 0 < m) {w g : ℝ → ℝ} (hw : MemLp w 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (hg : IsCircleSliceRegular m g) (hgp : ∀ θ, g (θ + 2 * π) = g θ) (s : Finset ℤ)
    (hs : ∀ n ∉ s, cf m n g = 0) (n : ℤ) :
    cf m n (fun θ => g θ * w θ) = ∑ n' ∈ s, conj (cf m (n' - n) w) * cf m n' g := by
  have e : (fun θ => g θ * w θ) = fun θ => w θ * g θ := funext fun θ => mul_comm _ _
  rw [e]
  exact conv_fin hm hw hg hgp s hs n

theorem conj_cf (m : ℕ) (n : ℤ) (h : ℝ → ℝ) :
    conj (cf m n h) = ((2 * π)⁻¹ : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * π), Complex.exp ((azimuth m n * θ : ℝ) * Complex.I) * (h θ : ℂ) := by
  have hp : (0 : ℝ) ≤ 2 * π := circle_len_pos.le
  unfold cf circleCoeff
  rw [map_mul, intervalIntegral.integral_of_le hp, intervalIntegral.integral_of_le hp, ← integral_conj]
  congr 1
  · rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring, Complex.conj_ofReal]
    push_cast
    ring
  · refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, Complex.conj_I]
    congr 2
    ring

theorem self_conj (m : ℕ) (res : Finset ℤ) (hres : ∀ n, n ∈ res ↔ -n ∈ res) (ℓ : ℤ → ℂ)
    (hℓ : ∀ n, ℓ (-n) = conj (ℓ n)) (θ : ℝ) :
    (((∑ n ∈ res, ℓ n * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)).re : ℝ) : ℂ)
      = ∑ n ∈ res, ℓ n * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I) := by
  refine Complex.conj_eq_iff_re.1 ?_
  rw [map_sum]
  refine Finset.sum_nbij' (fun n => -n) (fun n => -n) (fun n hn => (hres n).1 hn) (fun n hn => (hres n).1 hn)
    (fun n _ => neg_neg n) (fun n _ => neg_neg n) (fun n _ => ?_)
  rw [hℓ, map_mul, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, azimuth]
  congr 2
  push_cast
  ring

theorem cst_low (m : ℕ) (res : Finset ℤ) (hres : ∀ n, n ∈ res ↔ -n ∈ res) (ℓ : ℤ → ℂ)
    (hℓ : ∀ n, ℓ (-n) = conj (ℓ n)) {h : ℝ → ℝ} (hh : IntervalIntegrable h volume 0 (2 * π)) :
    Cst (fun n => if n ∈ res then ℓ n * conj (cf m n h) else 0)
      (fun θ => (∑ n ∈ res, ℓ n * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)).re * h θ) := by
  have hcont : Continuous fun θ : ℝ => (∑ n ∈ res, ℓ n * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)).re :=
    Complex.continuous_re.comp (continuous_finsetSum _ fun n _ => by fun_prop)
  refine ⟨hh.continuousOn_mul hcont.continuousOn, ?_⟩
  have H : HasSum (fun n => if n ∈ res then ℓ n * conj (cf m n h) else 0)
      (∑ n ∈ res, if n ∈ res then ℓ n * conj (cf m n h) else 0) :=
    hasSum_sum_of_ne_finset_zero fun n hn => if_neg hn
  convert H using 1
  rw [Finset.sum_congr rfl fun n hn => if_pos hn]
  have hI : IntervalIntegrable (fun θ => (h θ : ℂ)) volume 0 (2 * π) := ⟨hh.1.ofReal, hh.2.ofReal⟩
  have hi : ∀ n ∈ res, IntervalIntegrable
      (fun θ => ℓ n * (Complex.exp ((azimuth m n * θ : ℝ) * Complex.I) * (h θ : ℂ))) volume 0 (2 * π) :=
    fun n _ => (hI.continuousOn_mul (by fun_prop : Continuous fun θ : ℝ =>
      Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)).continuousOn).const_mul _
  have e1 : (((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
      (∑ n ∈ res, ℓ n * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)).re * h θ : ℝ) : ℂ)
      = ((2 * π)⁻¹ : ℂ) * ∫ θ in (0 : ℝ)..(2 * π),
        ∑ n ∈ res, ℓ n * (Complex.exp ((azimuth m n * θ : ℝ) * Complex.I) * (h θ : ℂ)) := by
    rw [Complex.ofReal_mul, ← intervalIntegral.integral_ofReal]
    congr 1
    · rw [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat]
    · refine intervalIntegral.integral_congr fun θ _ => ?_
      rw [Complex.ofReal_mul, self_conj m res hres ℓ hℓ θ, Finset.sum_mul]
      exact Finset.sum_congr rfl fun n _ => mul_assoc _ _ _
  rw [e1, intervalIntegral.integral_finsetSum hi, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [conj_cf, intervalIntegral.integral_const_mul]
  ring

theorem cst_pair {m : ℕ} (hm : 0 < m) {f h : ℝ → ℝ} (hf : IsCircleSliceRegular m f)
    (hfp : ∀ θ, f (θ + 2 * π) = f θ) (hh : MemLp h 2 (volume.restrict (Set.Ioc 0 (2 * π)))) :
    Cst (fun n => cf m n f * conj (cf m n h)) (fun θ => f θ * h θ) :=
  ⟨product_integrable hf.1 hh, entry_modes hm hf hh hfp⟩

theorem cross_coef {m : ℕ} (hm : 0 < m) {V P : Fin 3 → ℝ → ℝ}
    (hV : ∀ b, MemLp (V b) 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (hP : ∀ c, IsCircleSliceRegular m (P c)) (hPp : ∀ c θ, P c (θ + 2 * π) = P c θ) (s : Finset ℤ)
    (hs : ∀ c, ∀ n ∉ s, cf m n (P c) = 0) (n : ℤ) (i : Fin 3) :
    cf m n (fun θ => crossR (fun b => V b θ) (fun c => P c θ) i) =
      ∑ n' ∈ s, crossC (conjVec3 (fun b => cf m (n' - n) (V b))) (fun c => cf m n' (P c)) i := by
  have hI : ∀ b c, IntervalIntegrable (fun θ => V b θ * P c θ) volume 0 (2 * π) :=
    fun b c => product_integrable (hV b) (hP c).1
  fin_cases i <;>
  · simp only [crossR, crossC, conjVec3, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [cf_sub m n (hI _ _) (hI _ _), conv_fin hm (hV _) (hP _) (hPp _) s (hs _),
      conv_fin hm (hV _) (hP _) (hPp _) s (hs _), ← Finset.sum_sub_distrib]

theorem cross_coef' {m : ℕ} (hm : 0 < m) {W P : Fin 3 → ℝ → ℝ}
    (hW : ∀ b, MemLp (W b) 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (hP : ∀ c, IsCircleSliceRegular m (P c)) (hPp : ∀ c θ, P c (θ + 2 * π) = P c θ) (s : Finset ℤ)
    (hs : ∀ c, ∀ n ∉ s, cf m n (P c) = 0) (n : ℤ) (i : Fin 3) :
    cf m n (fun θ => crossR (fun c => P c θ) (fun b => W b θ) i) =
      ∑ n' ∈ s, crossC (fun c => cf m n' (P c)) (conjVec3 (fun b => cf m (n' - n) (W b))) i := by
  have hI : ∀ b c, IntervalIntegrable (fun θ => P c θ * W b θ) volume 0 (2 * π) :=
    fun b c => product_integrable (hP c).1 (hW b)
  fin_cases i <;>
  · simp only [crossR, crossC, conjVec3, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [cf_sub m n (hI _ _) (hI _ _), conv_fin' hm (hW _) (hP _) (hPp _) s (hs _),
      conv_fin' hm (hW _) (hP _) (hPp _) s (hs _), ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem adj_coef {m : ℕ} (hm : 0 < m) {V P : Fin 3 → ℝ → ℝ}
    (hV : ∀ b, MemLp (V b) 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (hP : ∀ c, IsCircleSliceRegular m (P c)) (hPp : ∀ c θ, P c (θ + 2 * π) = P c θ) (s : Finset ℤ)
    (hs : ∀ c, ∀ n ∉ s, cf m n (P c) = 0)
    (hX : ∀ i, IntervalIntegrable (fun θ => crossR (fun b => V b θ) (fun c => P c θ) i) volume 0 (2 * π))
    (n : ℤ) (l j : Fin 3) :
    (∑ n' ∈ s, curlAdj (crossC (conjVec3 (fun b => cf m (n' - n) (V b))) (fun c => cf m n' (P c))) l j) =
      cf m n (fun θ => adjR (crossR (fun b => V b θ) (fun c => P c θ)) l j) := by
  have e := circleCoeff_sum (azimuth m n) (Finset.univ : Finset (Fin 3))
    (fun i θ => permSign i j l * crossR (fun b => V b θ) (fun c => P c θ) i) (fun i _ => (hX i).const_mul _)
  simp only [circleCoeff_const] at e
  have e2 : cf m n (fun θ => adjR (crossR (fun b => V b θ) (fun c => P c θ)) l j) =
      ∑ i : Fin 3, (permSign i j l : ℂ) * cf m n (fun θ => crossR (fun b => V b θ) (fun c => P c θ) i) := e
  rw [e2]
  simp only [curlAdj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, cross_coef hm hV hP hPp s hs n i]

theorem hbase {m : ℕ} (hm : 0 < m) (Gf : Fin 3 → Fin 3 → ℝ → ℝ) (vf V W P : Fin 3 → ℝ → ℝ)
    (hG : ∀ l j, IsCircleSliceRegular m (Gf l j)) (hGp : ∀ l j θ, Gf l j (θ + 2 * π) = Gf l j θ)
    (hv : ∀ i, IsCircleSliceRegular m (vf i)) (hvp : ∀ i θ, vf i (θ + 2 * π) = vf i θ)
    (hP : ∀ c, IsCircleSliceRegular m (P c)) (hPp : ∀ c θ, P c (θ + 2 * π) = P c θ)
    (hVm : ∀ b, AEStronglyMeasurable (V b) (volume.restrict (Set.Ioc 0 (2 * π))))
    (hWm : ∀ b, AEStronglyMeasurable (W b) (volume.restrict (Set.Ioc 0 (2 * π))))
    (C : ℝ) (hVC : ∀ b θ, |V b θ| ≤ C) (hWC : ∀ b θ, |W b θ| ≤ C)
    (s : Finset ℤ) (hs : ∀ c, ∀ n ∉ s, cf m n (P c) = 0)
    (res : Finset ℤ) (hres : ∀ n, n ∈ res ↔ -n ∈ res)
    (ℓ : ℤ → Fin 3 → Fin 3 → ℂ) (hℓ : ∀ n l j, ℓ (-n) l j = conj (ℓ n l j))
    (lv : ℤ → Fin 3 → ℂ) (hlv : ∀ n i, lv (-n) i = conj (lv n i)) :
    Cst (fun n => entryPairing (fun l j => cf m n (Gf l j) - if n ∈ res then ℓ n l j else 0)
          (fun l j => ∑ n' ∈ s, curlAdj (crossC (conjVec3 (fun b => cf m (n' - n) (V b)))
            (fun c => cf m n' (P c))) l j)
        + CellScalars.vecPair (fun i => cf m n (vf i) - if n ∈ res then lv n i else 0)
          (fun i => ∑ n' ∈ s, crossC (fun c => cf m n' (P c)) (conjVec3 (fun b => cf m (n' - n) (W b))) i))
      (fun θ => ∑ l : Fin 3, ∑ j : Fin 3,
          (Gf l j θ - (∑ n ∈ res, ℓ n l j * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)).re) *
            adjR (crossR (fun b => V b θ) (fun c => P c θ)) l j
        + ∑ i : Fin 3, (vf i θ - (∑ n ∈ res, lv n i * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)).re) *
            crossR (fun c => P c θ) (fun b => W b θ) i) := by
  have mV : ∀ b, MemLp (V b) 2 (volume.restrict (Set.Ioc 0 (2 * π))) := fun b =>
    bounded_memLp_self (hVm b) (hVC b)
  have mW : ∀ b, MemLp (W b) 2 (volume.restrict (Set.Ioc 0 (2 * π))) := fun b =>
    bounded_memLp_self (hWm b) (hWC b)
  have mX : ∀ i, MemLp (fun θ => crossR (fun b => V b θ) (fun c => P c θ) i) 2
      (volume.restrict (Set.Ioc 0 (2 * π))) := by
    intro i
    fin_cases i <;>
    · simp only [crossR, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      exact (bounded_memLp (hVm _) (hVC _) (hP _).1).sub (bounded_memLp (hVm _) (hVC _) (hP _).1)
  have mY : ∀ i, MemLp (fun θ => crossR (fun c => P c θ) (fun b => W b θ) i) 2
      (volume.restrict (Set.Ioc 0 (2 * π))) := by
    intro i
    fin_cases i <;>
    · simp only [crossR, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      exact (memLp_mul_b (hWm _) (hWC _) (hP _).1).sub (memLp_mul_b (hWm _) (hWC _) (hP _).1)
  have mA : ∀ l j, MemLp (fun θ => adjR (crossR (fun b => V b θ) (fun c => P c θ)) l j) 2
      (volume.restrict (Set.Ioc 0 (2 * π))) := fun l j =>
    memLp_finsetSum _ fun i _ => (mX i).const_mul _
  have hA := adj_coef hm mV hP hPp s hs (fun i => ii_of (mX i))
  have hB := cross_coef' hm mW hP hPp s hs
  have cs1 : ∀ l j, Cst (fun n => cf m n (Gf l j) * conj (cf m n (fun θ => adjR (crossR (fun b => V b θ)
        (fun c => P c θ)) l j)) + -(if n ∈ res then ℓ n l j * conj (cf m n (fun θ => adjR (crossR (fun b => V b θ)
        (fun c => P c θ)) l j)) else 0))
      (fun θ => Gf l j θ * adjR (crossR (fun b => V b θ) (fun c => P c θ)) l j +
        -((∑ n ∈ res, ℓ n l j * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)).re *
          adjR (crossR (fun b => V b θ) (fun c => P c θ)) l j)) := fun l j =>
    cst_add (cst_pair hm (hG l j) (hGp l j) (mA l j))
      (cst_neg (cst_low m res hres (fun n => ℓ n l j) (fun n => hℓ n l j) (ii_of (mA l j))))
  have cs2 : ∀ i, Cst (fun n => cf m n (vf i) * conj (cf m n (fun θ => crossR (fun c => P c θ) (fun b => W b θ) i))
        + -(if n ∈ res then lv n i * conj (cf m n (fun θ => crossR (fun c => P c θ) (fun b => W b θ) i)) else 0))
      (fun θ => vf i θ * crossR (fun c => P c θ) (fun b => W b θ) i +
        -((∑ n ∈ res, lv n i * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)).re *
          crossR (fun c => P c θ) (fun b => W b θ) i)) := fun i =>
    cst_add (cst_pair hm (hv i) (hvp i) (mY i))
      (cst_neg (cst_low m res hres (fun n => lv n i) (fun n => hlv n i) (ii_of (mY i))))
  have H := cst_add (cst3 fun l => cst3 fun j => cs1 l j) (cst3 fun i => cs2 i)
  refine cst_congr H (fun n => ?_) (fun θ => ?_)
  · simp only [entryPairing, CellScalars.vecPair, hA n, ← hB n]
    by_cases hn : n ∈ res
    · simp only [hn, ↓reduceIte]
      simp only [Fin.sum_univ_three]
      ring
    · simp only [hn, ↓reduceIte]
      simp only [Fin.sum_univ_three]
      ring
  · simp only [Fin.sum_univ_three]
    ring

theorem frameVec_add (θ : ℝ) (u w : Space) (a : Fin 3) :
    frameVec θ (u + w) a = frameVec θ u a + frameVec θ w a := by
  fin_cases a <;> simp [frameVec, inner_add_left]

theorem frameVec_sub (θ : ℝ) (u w : Space) (a : Fin 3) :
    frameVec θ (u - w) a = frameVec θ u a - frameVec θ w a := by
  fin_cases a <;> simp [frameVec, inner_sub_left]

theorem frameMat_sub (θ : ℝ) (A B : Space →L[ℝ] Space) (a b : Fin 3) :
    frameMat θ (A - B) a b = frameMat θ A a b - frameMat θ B a b := by
  simp only [frameMat, ContinuousLinearMap.sub_apply, inner_sub_left]

theorem frameVec_cross (θ : ℝ) (u w : Space) (i : Fin 3) :
    frameVec θ (crossVec u w) i = crossR (frameVec θ u) (frameVec θ w) i := by
  have hs := Real.sin_sq_add_cos_sq θ
  fin_cases i <;>
    simp [frameVec, crossR, crossVec, radialUnit, angularUnit, axialUnit, PiLp.inner_apply, Fin.sum_univ_three] <;>
    first
      | ring1
      | linear_combination (u 0 * w 1 - u 1 * w 0) * hs
      | linear_combination (-(u 0 * w 1 - u 1 * w 0)) * hs

theorem inner_frame (θ : ℝ) (u w : Space) : inner ℝ u w = ∑ a : Fin 3, frameVec θ u a * frameVec θ w a := by
  have hs := Real.sin_sq_add_cos_sq θ
  simp [frameVec, radialUnit, angularUnit, axialUnit, PiLp.inner_apply, Fin.sum_univ_three]
  first
    | ring1
    | linear_combination (u 0 * w 0 + u 1 * w 1) * hs
    | linear_combination (-(u 0 * w 0 + u 1 * w 1)) * hs

theorem pt_id {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (ψ : Space → Space) {r z : ℝ} (hr : 0 < r) (hz : 0 ≤ z) (θ : ℝ) :
    inner ℝ (CellScalars.highCouplingField c K S v G (cylPoint r θ z)) (ψ (cylPoint r θ z)) =
      ∑ l : Fin 3, ∑ j : Fin 3, (frameMat θ (G (cylPoint r θ z)) l j -
          (∑ n ∈ S.resolved, K.lowStrain c.order n S.degHigh G l j (r, z) *
            Complex.exp ((azimuth c.order n * θ : ℝ) * Complex.I)).re) *
          adjR (crossR (fun b => frameVec θ (c.modelVelocity (cylPoint r θ z)) b)
            (fun b => frameVec θ (ψ (cylPoint r θ z)) b)) l j
      + ∑ i : Fin 3, (frameVec θ (v (cylPoint r θ z)) i -
          (∑ n ∈ S.resolved, K.lowVelocity c.order n S.degHigh v i (r, z) *
            Complex.exp ((azimuth c.order n * θ : ℝ) * Complex.I)).re) *
          crossR (fun b => frameVec θ (ψ (cylPoint r θ z)) b)
            (fun b => frameVec θ (c.modelCurl (cylPoint r θ z)) b) i := by
  rw [inner_frame θ]
  unfold CellScalars.highCouplingField
  simp only [frameVec_add, frameVec_cross]
  simp [crossR, adjR, Fin.sum_univ_three]
  simp only [LayoutRowVolume.frameVec_curl, frameMat_sub, frameVec_sub,
    LayoutRowVolume.lowGrad_frame c K S G hr hz, LayoutRowVolume.lowVel_frame c K S v hr hz]
  simp [Fin.sum_univ_three, permSign]
  ring

theorem ep_smul (s X : Fin 3 → Fin 3 → ℂ) (t : ℝ) :
    entryPairing s (fun a b => (t : ℂ) * X a b) = (t : ℂ) * entryPairing s X := by
  simp only [entryPairing, map_mul, Complex.conj_ofReal, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem vp_smul (x y : Fin 3 → ℂ) (t : ℝ) :
    CellScalars.vecPair x (fun a => (t : ℂ) * y a) = (t : ℂ) * CellScalars.vecPair x y := by
  simp only [CellScalars.vecPair, map_mul, Complex.conj_ofReal, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem lw_hat (K : CellBox) {p : ℝ × ℝ} (hr : 0 < p.1) : K.lineWeight p.1 * CellScalars.rHat K p = p.1 := by
  unfold CellScalars.rHat CellBox.lineWeight
  split_ifs
  · field_simp
  · field_simp

end Breakdown.FracInternal.RowCircleSeries

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly FracInternal.DensitySlice FracInternal.CircleSliceCoupling FracInternal.CircleSliceRegular
  FracInternal.RowCircleSeries

theorem rowCircleSeries_holds : RowCircleSeriesStatement := by
  intro α ha1 ha2 k N c hc K S B Cl slots R hd hw x hx a ha
  have hK := hd.box
  have hm : 0 < c.order := by have := hc.base.order_ge; omega
  have hs := hx.1
  have hsq := fieldModeSquare_holds K hK c.order x.1 x.2.1 x.2.2.1 hs
  have hturn := gradientTurn c.order x.1 x.2.1 x.2.2.1 hs
  obtain ⟨C, hC⟩ := hc.model_bounded
  have hsub := hd.solid_in_region
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Space) (2 * K.r₂ + K.z₂))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  have hv2 : MemLp x.1 2 (volume.restrict (Metric.closedBall (0 : Space) (2 * K.r₂ + K.z₂))) :=
    (hs.velocity_six.restrict _).mono_exponent (by norm_num)
  have hG2 := (clm_memLp hs.measurable_gradient hs.gradient_two).restrict
    (Metric.closedBall (0 : Space) (2 * K.r₂ + K.z₂))
  have hr2 : MemLp (c.row a) 2 (volume.restrict (Metric.closedBall (0 : Space) (2 * K.r₂ + K.z₂))) :=
    (hc.base.row_two a).restrict _
  have fb : ∀ θ (u : Space) (b : Fin 3), |frameVec θ u b| ≤ ‖u‖ := fun θ u b => by
    rw [LowEntry.Internal.frameVec_eq]; exact LowEntry.Internal.inner_unit_bound θ u b
  have hvL : ∀ b, ∀ᵐ p ∂(volume.restrict K.rect),
      MemLp (fun θ => frameVec θ (x.1 (cylPoint p.1 θ p.2)) b) 2 (volume.restrict (Set.Ioc 0 (2 * π))) :=
    fun b => slice_gen hK hs.measurable_velocity hv2 (fun θ u => frameVec θ u b)
      (LowEntry.Internal.frameVec_cont b) (fun θ u => fb θ u b) (fun θ u => LowEntry.Internal.frameVec_per θ u b)
  have hPL : ∀ b, ∀ᵐ p ∂(volume.restrict K.rect),
      MemLp (fun θ => frameVec θ (c.row a (cylPoint p.1 θ p.2)) b) 2 (volume.restrict (Set.Ioc 0 (2 * π))) :=
    fun b => slice_gen hK (hc.base.row_two a).1 hr2 (fun θ u => frameVec θ u b)
      (LowEntry.Internal.frameVec_cont b) (fun θ u => fb θ u b) (fun θ u => LowEntry.Internal.frameVec_per θ u b)
  have hGL : ∀ l j, ∀ᵐ p ∂(volume.restrict K.rect),
      MemLp (fun θ => frameMat θ (x.2.1 (cylPoint p.1 θ p.2)) l j) 2 (volume.restrict (Set.Ioc 0 (2 * π))) :=
    fun l j => slice_gen hK hs.measurable_gradient hG2 (fun θ M => frameMat θ M l j)
      (LowEntry.Internal.frameMat_cont l j) (fun θ M => LowEntry.Internal.frameMat_bound θ M l j)
      (fun θ M => LowEntry.Internal.frameMat_per θ M l j)
  have hvP : ∀ᵐ p ∂(volume.restrict K.rect), ∀ b, ∀ᵐ θ ∂volume,
      frameVec (θ + 2 * π / c.order) (x.1 (cylPoint p.1 (θ + 2 * π / c.order) p.2)) b =
        frameVec θ (x.1 (cylPoint p.1 θ p.2)) b := by
    filter_upwards [slice_ae (P := fun y => x.1 (turnStep c.order y) = turnStep c.order (x.1 y))
      hs.symmetric.1 hK] with p hp b
    refine per_ae (f := fun θ => frameVec θ (x.1 (cylPoint p.1 θ p.2)) b) (fun θ => ?_) _ ?_
    · show frameVec (θ + 2 * π) (x.1 (cylPoint p.1 (θ + 2 * π) p.2)) b = _
      rw [LowEntry.Internal.cylPoint_per, LowEntry.Internal.frameVec_per]
    · filter_upwards [hp] with θ hθ
      show frameVec (θ + 2 * π / c.order) (x.1 (cylPoint p.1 (θ + 2 * π / c.order) p.2)) b = _
      rw [← turn_cyl, hθ]
      exact frameVec_turn c.order θ rfl b
  have hPP : ∀ᵐ p ∂(volume.restrict K.rect), ∀ b, ∀ᵐ θ ∂volume,
      frameVec (θ + 2 * π / c.order) (c.row a (cylPoint p.1 (θ + 2 * π / c.order) p.2)) b =
        frameVec θ (c.row a (cylPoint p.1 θ p.2)) b := by
    filter_upwards [slice_ae (P := fun y => c.row a (turnStep c.order y) = turnStep c.order (c.row a y))
      (hc.base.row_class a).1 hK] with p hp b
    refine per_ae (f := fun θ => frameVec θ (c.row a (cylPoint p.1 θ p.2)) b) (fun θ => ?_) _ ?_
    · show frameVec (θ + 2 * π) (c.row a (cylPoint p.1 (θ + 2 * π) p.2)) b = _
      rw [LowEntry.Internal.cylPoint_per, LowEntry.Internal.frameVec_per]
    · filter_upwards [hp] with θ hθ
      show frameVec (θ + 2 * π / c.order) (c.row a (cylPoint p.1 (θ + 2 * π / c.order) p.2)) b = _
      rw [← turn_cyl, hθ]
      exact frameVec_turn c.order θ rfl b
  have hGP : ∀ᵐ p ∂(volume.restrict K.rect), ∀ l j, ∀ᵐ θ ∂volume,
      frameMat (θ + 2 * π / c.order) (x.2.1 (cylPoint p.1 (θ + 2 * π / c.order) p.2)) l j =
        frameMat θ (x.2.1 (cylPoint p.1 θ p.2)) l j := by
    filter_upwards [slice_ae (P := fun y => ∀ u, x.2.1 (turnStep c.order y) (turnStep c.order u) =
      turnStep c.order (x.2.1 y u)) (hturn.mono fun y h => h.1) hK] with p hp l j
    refine per_ae (f := fun θ => frameMat θ (x.2.1 (cylPoint p.1 θ p.2)) l j) (fun θ => ?_) _ ?_
    · show frameMat (θ + 2 * π) (x.2.1 (cylPoint p.1 (θ + 2 * π) p.2)) l j = _
      rw [LowEntry.Internal.cylPoint_per, LowEntry.Internal.frameMat_per]
    · filter_upwards [hp] with θ hθ
      show frameMat (θ + 2 * π / c.order) (x.2.1 (cylPoint p.1 (θ + 2 * π / c.order) p.2)) l j = _
      rw [← turn_cyl]
      exact frameMat_turn c.order θ hθ l j
  have hVM : ∀ b, ∀ᵐ p ∂(volume.restrict K.rect), AEStronglyMeasurable
      (fun θ => frameVec θ (c.modelVelocity (cylPoint p.1 θ p.2)) b) (volume.restrict (Set.Ioc 0 (2 * π))) :=
    fun b => slice_bdd hK hc.model_measurable.1 (fun θ u => frameVec θ u b) (LowEntry.Internal.frameVec_cont b)
      (fun θ u => LowEntry.Internal.frameVec_per θ u b) C
      (fun p hp θ => (fb _ _ b).trans (hC _ (hsub (cyl_solid hK hp θ))).1)
  have hWM : ∀ b, ∀ᵐ p ∂(volume.restrict K.rect), AEStronglyMeasurable
      (fun θ => frameVec θ (c.modelCurl (cylPoint p.1 θ p.2)) b) (volume.restrict (Set.Ioc 0 (2 * π))) :=
    fun b => slice_bdd hK hc.model_measurable.2.1 (fun θ u => frameVec θ u b) (LowEntry.Internal.frameVec_cont b)
      (fun θ u => LowEntry.Internal.frameVec_per θ u b) C
      (fun p hp θ => (fb _ _ b).trans (hC _ (hsub (cyl_solid hK hp θ))).2.1)
  filter_upwards [ae_restrict_mem (LowEntry.Internal.rect_meas K), ae_restrict_of_ae ae_fst_ne,
    ae_all_iff.2 hvL, ae_all_iff.2 hPL, ae_all_iff.2 fun l => ae_all_iff.2 (hGL l), hvP, hPP, hGP,
    ae_all_iff.2 hVM, ae_all_iff.2 hWM] with p hp hp0 mv mP mG tv tP tG mV mW
  have hr : 0 < p.1 := lt_of_le_of_ne (hK.r_order.1.trans hp.1.1) (Ne.symm hp0)
  have hz : 0 ≤ p.2 := hK.z_order.1.trans hp.2.1
  have key := hbase hm (fun l j θ => frameMat θ (x.2.1 (cylPoint p.1 θ p.2)) l j)
    (fun i θ => frameVec θ (x.1 (cylPoint p.1 θ p.2)) i)
    (fun b θ => frameVec θ (c.modelVelocity (cylPoint p.1 θ p.2)) b)
    (fun b θ => frameVec θ (c.modelCurl (cylPoint p.1 θ p.2)) b)
    (fun b θ => frameVec θ (c.row a (cylPoint p.1 θ p.2)) b)
    (fun l j => ⟨mG l j, tG l j⟩)
    (fun l j θ => by simp only [LowEntry.Internal.cylPoint_per, LowEntry.Internal.frameMat_per])
    (fun i => ⟨mv i, tv i⟩)
    (fun i θ => by simp only [LowEntry.Internal.cylPoint_per, LowEntry.Internal.frameVec_per])
    (fun b => ⟨mP b, tP b⟩)
    (fun b θ => by simp only [LowEntry.Internal.cylPoint_per, LowEntry.Internal.frameVec_per])
    mV mW C
    (fun b θ => (fb _ _ b).trans (hC _ (hsub (cyl_solid hK hp θ))).1)
    (fun b θ => (fb _ _ b).trans (hC _ (hsub (cyl_solid hK hp θ))).2.1)
    R.rowModes (fun b n hn => congrFun (hd.row_modes a ha n hn p hp) b)
    S.resolved hd.scalars.resolved_symm
    (fun n l j => K.lowStrain c.order n S.degHigh x.2.1 l j p)
    (fun n l j => RowModeUnfolded.Internal.lowStrain_neg K B hK hd.bases c.order n S.degHigh x.2.1 l j
      ((hsq n).1 l j) p)
    (fun n i => K.lowVelocity c.order n S.degHigh x.1 i p)
    (fun n i => RowModeUnfolded.Internal.lowVelocity_neg K B hK hd.bases c.order n S.degHigh x.1 i
      ((hsq n).2 i) p)
  have H := (Complex.hasSum_re key.2).mul_left p.1
  convert H using 1
  all_goals try rfl
  · funext n
    unfold CellScalars.rowModeDensity CellScalars.rowCouplingStrain CellScalars.rowCouplingVelocity
    rw [ep_smul, vp_smul, ← mul_add, ← mul_assoc, ← Complex.ofReal_mul, lw_hat K hr, Complex.re_ofReal_mul]
    rfl
  · rw [Complex.ofReal_re]
    unfold CellScalars.circleRowPair
    rw [intervalIntegral.integral_congr fun θ _ => pt_id c K S x.1 x.2.1 (c.row a) hr hz θ, one_div]

end Breakdown.CellCert.CellAnalysis
