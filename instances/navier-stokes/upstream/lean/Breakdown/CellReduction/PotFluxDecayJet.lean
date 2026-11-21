import Breakdown.CellReduction.PotentialShape
import Breakdown.FracCell.GivenAuxDualParts
import Breakdown.FracCell.GivenAuxAtomAxis
import Breakdown.FracCell.GivenProfilePowerFieldJumpsPieces
import Breakdown.CertCell.ShapeSplineDeriv

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape
open CellCert.GivenFields (Spline cellCount cellIndex)

namespace FluxDecay.Internal

theorem one_sub_pow_dvd_jetUnit (n p : ℕ) : (1 - Polynomial.X : Polynomial ℂ) ^ n ∣ jetUnit n p := by
  unfold jetUnit
  exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

theorem X_pow_dvd_jetUnit (n p : ℕ) : (Polynomial.X : Polynomial ℂ) ^ p ∣ jetUnit n p := by
  unfold jetUnit
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _

theorem comp_dvd_comp {p q : Polynomial ℂ} (h : p ∣ q) (r : Polynomial ℂ) : p.comp r ∣ q.comp r := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k.comp r, Polynomial.mul_comp _ _ _⟩

theorem nodalLeft_dvd (n p : ℕ) {a : ℝ} (ha : a ≠ 1) :
    (Polynomial.X - 1 : Polynomial ℂ) ^ n ∣ nodalLeft n p a 1 := by
  unfold nodalLeft
  refine dvd_mul_of_dvd_right ?_ _
  set c : ℂ := (((1 - a)⁻¹ : ℝ) : ℂ) with hcdef
  have hc : c * (1 - (a : ℂ)) = 1 := by
    rw [hcdef, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
      inv_mul_cancel₀ (sub_ne_zero.2 (Ne.symm ha))]
  refine dvd_trans ?_ (comp_dvd_comp (one_sub_pow_dvd_jetUnit n p) _)
  have e : (1 - Polynomial.X : Polynomial ℂ).comp (Polynomial.C c * (Polynomial.X - Polynomial.C (a : ℂ))) =
      Polynomial.C (-c) * (Polynomial.X - 1) := by
    simp only [Polynomial.sub_comp, Polynomial.one_comp, Polynomial.X_comp]
    calc (1 : Polynomial ℂ) - Polynomial.C c * (Polynomial.X - Polynomial.C (a : ℂ)) =
        Polynomial.C (c * (1 - (a : ℂ))) - Polynomial.C c * (Polynomial.X - Polynomial.C (a : ℂ)) := by
          rw [hc, map_one]
      _ = Polynomial.C (-c) * (Polynomial.X - 1) := by
          simp only [map_mul, map_sub, map_one, map_neg]
          ring
  rw [Polynomial.pow_comp, e, mul_pow]
  exact dvd_mul_left _ _

theorem nodalRight_dvd (n p : ℕ) (a : ℝ) :
    (Polynomial.X - 1 : Polynomial ℂ) ^ p ∣ nodalRight n p a 1 := by
  unfold nodalRight
  refine dvd_mul_of_dvd_right ?_ _
  refine dvd_trans ?_ (comp_dvd_comp (X_pow_dvd_jetUnit n p) _)
  rw [Polynomial.pow_comp, Polynomial.X_comp]
  have e : Polynomial.C ((((1 : ℝ) - a)⁻¹ : ℝ) : ℂ) * (Polynomial.C (((1 : ℝ) : ℝ) : ℂ) - Polynomial.X) =
      Polynomial.C (-((((1 : ℝ) - a)⁻¹ : ℝ) : ℂ)) * (Polynomial.X - 1) := by
    simp only [Complex.ofReal_one, map_one, map_neg]
    ring
  rw [e, mul_pow]
  exact dvd_mul_left _ _

theorem bubblePoly_dvd (n s : ℕ) (a : ℝ) :
    (Polynomial.X - 1 : Polynomial ℂ) ^ n ∣ bubblePoly n s a 1 := by
  unfold bubblePoly
  refine dvd_mul_of_dvd_left ?_ _
  have e : ((Polynomial.X - Polynomial.C (a : ℂ)) * (Polynomial.C (((1 : ℝ) : ℝ) : ℂ) - Polynomial.X)) ^ n =
      (-(Polynomial.X - Polynomial.C (a : ℂ))) ^ n * (Polynomial.X - 1 : Polynomial ℂ) ^ n := by
    simp only [Complex.ofReal_one, map_one]
    rw [← mul_pow]
    congr 1
    ring
  rw [e]
  exact dvd_mul_left _ _

theorem getD_last_eq {l : List ℝ} (h1 : l.getLast? = some 1) : l.getD (l.length - 1) 0 = 1 := by
  rw [List.getLast?_eq_getElem?] at h1
  rw [List.getD_eq_getElem?_getD, h1]
  rfl

theorem getD_before_last_lt {l : List ℝ} (hs : l.Pairwise (· < ·)) (h1 : l.getLast? = some 1)
    (h2 : 2 ≤ l.length) : l.getD (l.length - 2) 0 < 1 := by
  have hlt := List.pairwise_iff_getElem.1 hs (l.length - 2) (l.length - 1) (by omega) (by omega) (by omega)
  have e := getD_last_eq h1
  rw [List.getD_eq_getElem _ _ (by omega)] at e
  rw [List.getD_eq_getElem _ _ (by omega), ← e]
  exact hlt

theorem lastPiece_dvd (H : JetSpline) (z : ℕ) (hz : z ≤ H.tAxis.depth)
    (hs : H.tAxis.breaks.Pairwise (· < ·)) (h0 : H.tAxis.breaks.head? = some 0)
    (h1 : H.tAxis.breaks.getLast? = some 1) (hv : EndVanishOrder H z) (j : ℕ) :
    (MvPolynomial.X 0 - 1 : MvPolynomial (Fin 2) ℂ) ^ z ∣ H.toSpline.piece (cellCount H.tAxis.breaks - 1) j := by
  have h2 := CellCert.GivenFields.DualPartsInternal.two_le_length h0 h1
  have hb : H.tAxis.breaks.getD (cellCount H.tAxis.breaks - 1 + 1) 0 = 1 := by
    rw [show cellCount H.tAxis.breaks - 1 + 1 = H.tAxis.breaks.length - 1 by unfold cellCount; omega]
    exact getD_last_eq h1
  have ha : H.tAxis.breaks.getD (cellCount H.tAxis.breaks - 1) 0 ≠ 1 := by
    rw [show cellCount H.tAxis.breaks - 1 = H.tAxis.breaks.length - 2 by unfold cellCount; omega]
    exact (getD_before_last_lt hs h1 h2).ne
  have hterm : ∀ d, (∀ p, d = JetDof.node (cellCount H.tAxis.breaks) p → z ≤ p) →
      (Polynomial.X - 1 : Polynomial ℂ) ^ z ∣ H.tAxis.dofPoly (cellCount H.tAxis.breaks - 1) d := by
    intro d hd
    cases d with
    | node k p =>
      simp only [JetAxis.dofPoly]
      split_ifs with hp hk hk'
      · rw [hb]
        exact (pow_dvd_pow _ hz).trans (nodalLeft_dvd _ _ ha)
      · rw [hb]
        have hzp : z ≤ p := hd p (by
          rw [hk', show cellCount H.tAxis.breaks - 1 + 1 = cellCount H.tAxis.breaks by unfold cellCount; omega])
        exact (pow_dvd_pow _ hzp).trans (nodalRight_dvd _ _ _)
      · exact dvd_zero _
      · exact dvd_zero _
    | bubble i s =>
      simp only [JetAxis.dofPoly]
      split_ifs with hi
      · rw [hb]
        exact (pow_dvd_pow _ hz).trans (bubblePoly_dvd _ _ _)
      · exact dvd_zero _
  show _ ∣ ∑ d ∈ H.tAxis.dofs, ∑ e ∈ H.xAxis.dofs, MvPolynomial.C (H.coef d e) *
    embedFirst (H.tAxis.dofPoly (cellCount H.tAxis.breaks - 1) d) *
      embedSecond (H.xAxis.dofPoly j e)
  refine Finset.dvd_sum fun d _ => Finset.dvd_sum fun e _ => ?_
  by_cases hc : H.coef d e = 0
  · simp [hc]
  · have hd : ∀ p, d = JetDof.node (cellCount H.tAxis.breaks) p → z ≤ p := by
      intro p hp
      by_contra hlt
      exact hc (by rw [hp]; exact hv p (by omega) e)
    have h := map_dvd (Polynomial.aeval (R := ℂ) (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ)) (hterm d hd)
    simp only [map_pow, map_sub, Polynomial.aeval_X, map_one] at h
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _


theorem exists_upper_lt_one (I : List ℝ) (h : ∀ b ∈ I, b < 1) :
    ∃ T : ℝ, 0 ≤ T ∧ T < 1 ∧ ∀ b ∈ I, b ≤ T := by
  induction I with
  | nil => exact ⟨0, le_rfl, one_pos, by simp⟩
  | cons b I ih =>
    obtain ⟨T, hT0, hT1, hT⟩ := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    refine ⟨max b T, le_max_of_le_right hT0, max_lt (h b (by simp)) hT1, ?_⟩
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact le_max_left _ _
    · exact (hT c hc).trans (le_max_right _ _)

theorem le_double_sum (f : ℕ → ℕ → ℝ) (hf : ∀ i j, 0 ≤ f i j) {m n i j : ℕ} (hi : i < m) (hj : j < n) :
    f i j ≤ ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, f i j := by
  calc f i j ≤ ∑ j ∈ Finset.range n, f i j :=
        Finset.single_le_sum (fun k _ => hf i k) (Finset.mem_range.2 hj)
    _ ≤ _ := Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range n, f i j)
        (fun k _ => Finset.sum_nonneg fun _ _ => hf k _) (Finset.mem_range.2 hi)

theorem cellIndex_le_length (l : List ℝ) (u : ℝ) : cellIndex l u ≤ l.length := by
  unfold cellIndex
  refine (List.length_filter_le _ _).trans ?_
  simp only [List.length_dropLast, List.length_drop]
  omega

theorem norm_sub_one_pow (t : ℝ) (ht : t ≤ 1) (z : ℕ) : ‖((t : ℂ) - 1) ^ z‖ = (1 - t) ^ z := by
  rw [norm_pow, show (t : ℂ) - 1 = ((t - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith)]

theorem mul_pow_pred_eq (u : ℝ) (z : ℕ) : u * ((z : ℝ) * u ^ (z - 1)) = z * u ^ z := by
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · simp
  · rw [mul_left_comm, ← pow_succ', Nat.sub_add_cancel hz]

theorem jetEnd_bound (H : JetSpline) (z : ℕ) (hz : z ≤ H.tAxis.depth)
    (hs : H.tAxis.breaks.Pairwise (· < ·)) (h0 : H.tAxis.breaks.head? = some 0)
    (h1 : H.tAxis.breaks.getLast? = some 1) (hv : EndVanishOrder H z) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t x : ℝ, 0 ≤ t → t ≤ 1 → |x| ≤ 1 →
      ‖H.toSpline.evalHalf t x‖ ≤ B * (1 - t) ^ z ∧
      (t ∉ (H.tAxis.breaks.drop 1).dropLast → ∃ g : ℂ,
        HasDerivAt (fun s => H.toSpline.evalHalf s x) g t ∧ (1 - t) * ‖g‖ ≤ B * (1 - t) ^ z) ∧
      (x ∉ (H.xAxis.breaks.drop 1).dropLast → ∃ g : ℂ,
        HasDerivAt (fun s => H.toSpline.evalHalf t s) g x ∧ ‖g‖ ≤ B * (1 - t) ^ z) := by
  obtain ⟨T, hT0, hT1, hT⟩ :=
    exists_upper_lt_one _ (CellCert.GivenFields.DualPartsInternal.interior_lt_one hs h1)
  choose Bf hBf0 hBf using CellCert.GivenFields.DualPartsInternal.poly_bound
  choose R hR using fun j => lastPiece_dvd H z hz hs h0 h1 hv j
  set Q := H.toSpline.piece with hQ
  set K : ℕ → ℕ → ℝ := fun i j => Bf (Q i j) + Bf (MvPolynomial.pderiv 0 (Q i j)) +
    Bf (MvPolynomial.pderiv 1 (Q i j)) with hKdef
  set KL : ℕ → ℝ := fun j => Bf (R j) + Bf (MvPolynomial.pderiv 0 (R j)) +
    Bf (MvPolynomial.pderiv 1 (R j)) with hKLdef
  have hK0 : ∀ i j, 0 ≤ K i j := fun i j => add_nonneg (add_nonneg (hBf0 _) (hBf0 _)) (hBf0 _)
  have hKL0 : ∀ j, 0 ≤ KL j := fun j => add_nonneg (add_nonneg (hBf0 _) (hBf0 _)) (hBf0 _)
  have hTp : 0 < (1 - T) ^ z := pow_pos (by linarith) z
  set SK := ∑ i ∈ Finset.range (H.tAxis.breaks.length + 1), ∑ j ∈ Finset.range (H.xAxis.breaks.length + 1), K i j with hSKdef
  set SL := ∑ j ∈ Finset.range (H.xAxis.breaks.length + 1), KL j with hSLdef
  have hSK : 0 ≤ SK := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hK0 i j
  have hSL : 0 ≤ SL := Finset.sum_nonneg fun j _ => hKL0 j
  have hev : ∀ s u : ℝ, H.toSpline.evalHalf s u =
      MvPolynomial.eval ![(s : ℂ), (u : ℂ)] (Q (cellIndex H.tAxis.breaks s) (cellIndex H.xAxis.breaks u)) :=
    fun s u => rfl
  clear_value SK SL KL K Q
  refine ⟨SK / (1 - T) ^ z + (z + 1) * SL, by positivity, fun t x ht0 ht1 hx => ?_⟩
  have htabs : |t| ≤ 1 := abs_le.2 ⟨by linarith, ht1⟩
  have hu : 0 ≤ 1 - t := by linarith
  have hupow : 0 ≤ (1 - t) ^ z := pow_nonneg hu z
  have hj : cellIndex H.xAxis.breaks x < H.xAxis.breaks.length + 1 :=
    Nat.lt_succ_of_le (cellIndex_le_length _ _)
  have hi : cellIndex H.tAxis.breaks t < H.tAxis.breaks.length + 1 :=
    Nat.lt_succ_of_le (cellIndex_le_length _ _)
  by_cases htT : T ≤ t
  · have hi' : cellIndex H.tAxis.breaks t = cellCount H.tAxis.breaks - 1 :=
      CellCert.GivenFields.AtomAxisInternal.cellIndex_top _ t (fun b hb => (hT b hb).trans htT)
    have hQR : ∀ (j : ℕ) (s u : ℝ), MvPolynomial.eval ![(s : ℂ), (u : ℂ)] (Q (cellCount H.tAxis.breaks - 1) j) =
        ((s : ℂ) - 1) ^ z * MvPolynomial.eval ![(s : ℂ), (u : ℂ)] (R j) := by
      intro j s u
      rw [hR j]
      simp [map_mul, map_pow, map_sub, MvPolynomial.eval_X]
    set j := cellIndex H.xAxis.breaks x
    have hKLB : KL j ≤ SL := by
      rw [hSLdef]
      exact Finset.single_le_sum (fun k _ => hKL0 k) (Finset.mem_range.2 hj)
    have hfin : ∀ c : ℝ, 0 ≤ c → c ≤ KL j → c * (1 - t) ^ z ≤ (SK / (1 - T) ^ z + (z + 1) * SL) * (1 - t) ^ z := by
      intro c hc0 hc
      gcongr
      have : (0 : ℝ) ≤ SK / (1 - T) ^ z := by positivity
      have : (0 : ℝ) ≤ (z + 1) * (SL - KL j) := mul_nonneg (by positivity) (by linarith)
      nlinarith
    refine ⟨?_, ?_, ?_⟩
    · rw [hev, hi', hQR, norm_mul, norm_sub_one_pow t ht1, mul_comm]
      exact hfin _ (norm_nonneg _) ((hBf (R j) t x htabs hx).trans (by rw [hKLdef]; linarith [hBf0 (MvPolynomial.pderiv 0 (R j)), hBf0 (MvPolynomial.pderiv 1 (R j))]))
    · intro htn
      have hloc : (fun s => H.toSpline.evalHalf s x) =ᶠ[nhds t]
          fun s => ((s : ℂ) - 1) ^ z * MvPolynomial.eval ![(s : ℂ), (x : ℂ)] (R j) := by
        filter_upwards [FracInternal.ProfilePowerJumpsPieces.cellIndex_eventuallyEq _ htn] with s hs'
        rw [hev, hs', hi', hQR]
      have hd1 : HasDerivAt (fun s : ℝ => ((s : ℂ) - 1) ^ z) ((z : ℂ) * ((t : ℂ) - 1) ^ (z - 1) * ((1 : ℝ) : ℂ)) t :=
        ((hasDerivAt_id' t).ofReal_comp.sub_const 1).pow z
      have hd2 := CertCell.GivenShape.Internal.hasDerivAt_eval_first (R j) (x : ℂ) t
      refine ⟨_, (hd1.mul hd2).congr_of_eventuallyEq hloc, ?_⟩
      have hn1 : ‖((t : ℂ) - 1) ^ (z - 1)‖ = (1 - t) ^ (z - 1) := norm_sub_one_pow t ht1 _
      have hn2 : ‖((t : ℂ) - 1) ^ z‖ = (1 - t) ^ z := norm_sub_one_pow t ht1 _
      have hb1 := hBf (R j) t x htabs hx
      have hb2 := hBf (MvPolynomial.pderiv 0 (R j)) t x htabs hx
      have hpow1 : 0 ≤ (1 - t) ^ (z - 1) := pow_nonneg hu _
      have hle : (1 - t) * (1 - t) ^ z ≤ (1 - t) ^ z := by
        nlinarith
      calc (1 - t) * ‖(z : ℂ) * ((t : ℂ) - 1) ^ (z - 1) * ((1 : ℝ) : ℂ) *
            MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (R j) +
            ((t : ℂ) - 1) ^ z * MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 0 (R j))‖
          ≤ (1 - t) * ((z * (1 - t) ^ (z - 1)) * Bf (R j) + (1 - t) ^ z * Bf (MvPolynomial.pderiv 0 (R j))) := by
            gcongr
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul, norm_mul, norm_mul, hn1, hn2, Complex.norm_natCast, Complex.ofReal_one, norm_one,
              mul_one]
            gcongr
        _ = ((1 - t) * (z * (1 - t) ^ (z - 1))) * Bf (R j) +
            ((1 - t) * (1 - t) ^ z) * Bf (MvPolynomial.pderiv 0 (R j)) := by ring
        _ ≤ (z * (1 - t) ^ z) * Bf (R j) + (1 - t) ^ z * Bf (MvPolynomial.pderiv 0 (R j)) := by
            rw [mul_pow_pred_eq]
            gcongr
            exact hBf0 _
        _ = ((z : ℝ) * Bf (R j) + Bf (MvPolynomial.pderiv 0 (R j))) * (1 - t) ^ z := by ring
        _ ≤ _ := by
            have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg z
            have hc : (z : ℝ) * Bf (R j) + Bf (MvPolynomial.pderiv 0 (R j)) ≤ (z + 1) * KL j := by
              rw [hKLdef]
              have := mul_nonneg hz0 (hBf0 (MvPolynomial.pderiv 0 (R j)))
              have := mul_nonneg hz0 (hBf0 (MvPolynomial.pderiv 1 (R j)))
              have := hBf0 (R j)
              have := hBf0 (MvPolynomial.pderiv 1 (R j))
              nlinarith
            have hc' : (z + 1) * KL j ≤ SK / (1 - T) ^ z + (z + 1) * SL := by
              have : (0 : ℝ) ≤ SK / (1 - T) ^ z := by positivity
              have : (0 : ℝ) ≤ (z + 1) * (SL - KL j) := mul_nonneg (by positivity) (by linarith)
              nlinarith
            exact mul_le_mul_of_nonneg_right (hc.trans hc') hupow
    · intro hxn
      have hloc : (fun s => H.toSpline.evalHalf t s) =ᶠ[nhds x]
          fun s => ((t : ℂ) - 1) ^ z * MvPolynomial.eval ![(t : ℂ), (s : ℂ)] (R j) := by
        filter_upwards [FracInternal.ProfilePowerJumpsPieces.cellIndex_eventuallyEq _ hxn] with s hs'
        rw [hev, hs', hi', hQR]
      have hd2 := (CertCell.GivenShape.Internal.hasDerivAt_eval_second (R j) (t : ℂ) x).const_mul (((t : ℂ) - 1) ^ z)
      refine ⟨_, hd2.congr_of_eventuallyEq hloc, ?_⟩
      rw [norm_mul, norm_sub_one_pow t ht1, mul_comm]
      exact hfin _ (norm_nonneg _) ((hBf _ t x htabs hx).trans (by rw [hKLdef]; linarith [hBf0 (R j), hBf0 (MvPolynomial.pderiv 0 (R j))]))
  · replace htT : t < T := not_le.1 htT
    set i := cellIndex H.tAxis.breaks t
    set j := cellIndex H.xAxis.breaks x
    have hsmall : (1 - T) ^ z ≤ (1 - t) ^ z := pow_le_pow_left₀ (by linarith) (by linarith) z
    have hKB : K i j ≤ SK := by
      rw [hSKdef]
      exact le_double_sum K hK0 hi hj
    have hfin : ∀ c : ℝ, c ≤ K i j → c ≤ (SK / (1 - T) ^ z + (z + 1) * SL) * (1 - t) ^ z := by
      intro c hc
      have h1' : SK / (1 - T) ^ z * (1 - T) ^ z = SK := div_mul_cancel₀ _ hTp.ne'
      have h2' : SK / (1 - T) ^ z * (1 - T) ^ z ≤ SK / (1 - T) ^ z * (1 - t) ^ z := by gcongr
      have h3' : 0 ≤ (z + 1) * SL * (1 - t) ^ z := by positivity
      nlinarith
    have hKi : ∀ c : ℝ, c ≤ Bf (Q i j) ∨ c ≤ Bf (MvPolynomial.pderiv 0 (Q i j)) ∨ c ≤ Bf (MvPolynomial.pderiv 1 (Q i j)) →
        c ≤ K i j := by
      intro c hc
      have := hBf0 (Q i j)
      have := hBf0 (MvPolynomial.pderiv 0 (Q i j))
      have := hBf0 (MvPolynomial.pderiv 1 (Q i j))
      rw [hKdef]
      rcases hc with hc | hc | hc <;> linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [hev]
      exact hfin _ (hKi _ (Or.inl (hBf _ t x htabs hx)))
    · intro htn
      have hloc : (fun s => H.toSpline.evalHalf s x) =ᶠ[nhds t]
          fun s => MvPolynomial.eval ![(s : ℂ), (x : ℂ)] (Q i j) := by
        filter_upwards [FracInternal.ProfilePowerJumpsPieces.cellIndex_eventuallyEq _ htn] with s hs'
        rw [hev, hs']
      refine ⟨_, (CertCell.GivenShape.Internal.hasDerivAt_eval_first (Q i j) (x : ℂ) t).congr_of_eventuallyEq hloc, ?_⟩
      have hb := hBf (MvPolynomial.pderiv 0 (Q i j)) t x htabs hx
      have hn := norm_nonneg (MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 0 (Q i j)))
      refine hfin _ (hKi _ (Or.inr (Or.inl ?_)))
      nlinarith
    · intro hxn
      have hloc : (fun s => H.toSpline.evalHalf t s) =ᶠ[nhds x]
          fun s => MvPolynomial.eval ![(t : ℂ), (s : ℂ)] (Q i j) := by
        filter_upwards [FracInternal.ProfilePowerJumpsPieces.cellIndex_eventuallyEq _ hxn] with s hs'
        rw [hev, hs']
      refine ⟨_, (CertCell.GivenShape.Internal.hasDerivAt_eval_second (Q i j) (t : ℂ) x).congr_of_eventuallyEq hloc, ?_⟩
      exact hfin _ (hKi _ (Or.inr (Or.inr (hBf _ t x htabs hx))))

end FluxDecay.Internal

end PotentialShape

end Breakdown
