import TorusEuler.EndpointPhysicalMeanEstimate
import TorusEuler.TerminalMeanTimeCalculus
import TorusEuler.TerminalHalfHolderTimeProduct
import TorusEuler.TerminalMeanSpatialInverse
import TorusEuler.TerminalMeanSpatialTimeCommutation
import TorusEuler.TerminalMeanSpatialWordProduct
import Mathlib.Data.Nat.Choose.Sum

/-! Quantitative closed-slab time regularity of the recovered label velocity. -/

open Set
open MeasureTheory
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)
local notation "W" => HalfHolder Labels Vec3
local notation "S" => endpointHalfHolderSolenoidal
local notation "Coeff" => HalfHolder Labels (Vec3 →L[ℝ] Vec3)
local notation "P" => endpointStrongSpatialProjection
local notation "Leray" => endpointStrongSpatialLeray
local notation "Time(" T ")" => Icc (0 : ℝ) T
local notation "Path(" T ")" => Lp Vec3 2 (volume.restrict (Ioc (0 : ℝ) T))
local notation "MixedFixed(" T ")" => freezingFixedSpace (endpointStrongMixedLeray T)

local instance terminalMeanBoundsSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance terminalMeanBoundsSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

private theorem terminalMeanWordDeriv_sum {I : Type*} {u : Vec3} (V : Finset I)
    (k : I → ℕ) (f g : I → W)
    (h : ∀ i ∈ V, endpointTorusHasSpatialDerivative u (f i) (g i)) :
    endpointTorusHasSpatialDerivative u
      (∑ i ∈ V, k i • f i) (∑ i ∈ V, k i • g i) :=
  endpointTorusHasSpatialDerivative.finset_sum V _ _ (fun i hi => (h i hi).nsmul (k i))

private theorem terminalMeanWordDeriv_add_sub {u : Vec3} {a a' b b' c c' : W}
    (ha : endpointTorusHasSpatialDerivative u a a')
    (hb : endpointTorusHasSpatialDerivative u b b')
    (hc : endpointTorusHasSpatialDerivative u c c') :
    endpointTorusHasSpatialDerivative u (a + b - c) (a' + b' - c') :=
  (ha.add hb).sub hc

private theorem terminalMeanWeightedSum_norm_le {I : Type*} (s : Finset I) (k : I → ℕ) (f : I → W)
    {a B : ℝ} (ha : 0 ≤ a) (h : ∀ i ∈ s, a * ‖f i‖ ≤ B) :
    a * ‖∑ i ∈ s, k i • f i‖ ≤ (∑ i ∈ s, (k i : ℝ)) * B := by
  calc
    _ ≤ a * ∑ i ∈ s, ‖k i • f i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) ha
    _ = ∑ i ∈ s, (k i : ℝ) * (a * ‖f i‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [RCLike.norm_nsmul (K := ℝ), nsmul_eq_mul]
      ring
    _ ≤ ∑ i ∈ s, (k i : ℝ) * B :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (h i hi) (Nat.cast_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

private theorem terminalMeanChooseSum (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
  exact_mod_cast Nat.sum_range_choose n

private theorem terminalMeanChoosePositiveSum (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), ((n + 1).choose (i + 1) : ℝ)) ≤ (2 : ℝ) ^ (n + 1) := by
  have h := terminalMeanChooseSum (n + 1)
  rw [Finset.sum_range_succ'] at h
  exact (le_add_of_nonneg_right (Nat.cast_nonneg ((n + 1).choose 0))).trans_eq h

set_option maxHeartbeats 2200000 in
/-- The differentiated physical product has the exact time–space Leibniz
words and a finite-order constant with no loss of spatial orders. -/
theorem terminalMeanProductWords_timeJet_bound {I : Type*} {T : ℝ} (hT : 0 < T)
    (u : I → Vec3) (N q : ℕ)
    (K : List I → ℝ → Coeff) (f g : List I → ℝ → W)
    (hK : ∀ w, w.length ≤ N → ContDiffOn ℝ ∞ (K w) Time(T))
    (hf : ∀ w, w.length ≤ N → ContDiffOn ℝ ∞ (f w) Time(T))
    (hg : ∀ w, w.length ≤ N → ContDiffOn ℝ ∞ (g w) Time(T))
    (hKd : ∀ j w, w.length < N → ∀ t ∈ Time(T),
      endpointTorusHasSpatialDerivative (u j) (K w t) (K (j :: w) t))
    (hfd : ∀ j w, w.length < N → ∀ t ∈ Time(T),
      endpointTorusHasSpatialDerivative (u j) (f w t) (f (j :: w) t))
    (hgd : ∀ j w, w.length < N → ∀ t ∈ Time(T),
      endpointTorusHasSpatialDerivative (u j) (g w t) (g (j :: w) t))
    (hEq : EqOn (g []) (fun t => (K [] t).coefficientMul (f [] t)) Time(T))
    {ℓ A B : ℝ} (hℓ : 0 ≤ ℓ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hKcap : ∀ i ≤ q, ∀ w, w.length ≤ N → ∀ t ∈ Time(T),
      ℓ ^ w.length * ‖terminalTimeJet T i (K w) t‖ ≤ A)
    (hFcap : ∀ i ≤ q, ∀ w, w.length ≤ N → ∀ t ∈ Time(T),
      ℓ ^ w.length * ‖terminalTimeJet T i (f w) t‖ ≤ B) :
    ∀ i ≤ q, ∀ w, w.length ≤ N → ∀ t ∈ Time(T),
      ℓ ^ w.length * ‖terminalTimeJet T i (g w) t‖ ≤ (2 : ℝ) ^ (N + 1 + q) * A * B := by
  intro i hi w hw t ht
  let K' (j : ℕ) (r : List I) := terminalTimeJet T j (K r) t
  let f' (j : ℕ) (r : List I) := terminalTimeJet T j (f r) t
  let g' (j : ℕ) (r : List I) := terminalTimeJet T j (g r) t
  let X (r : List I) := ∑ j ∈ Finset.range (i + 1), i.choose j •
    terminalMeanWordProduct (K' j) (f' (i - j)) r
  have hSp {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (y : List I → ℝ → HalfHolder Labels E)
      (hy : ∀ r, r.length ≤ N → ContDiffOn ℝ ∞ (y r) Time(T))
      (hyd : ∀ j r, r.length < N → ∀ s ∈ Time(T),
        endpointTorusHasSpatialDerivative (u j) (y r s) (y (j :: r) s))
      (n : ℕ) (j : I) (r : List I) (hr : r.length < N) :
      endpointTorusHasSpatialDerivative (u j) (terminalTimeJet T n (y r) t)
        (terminalTimeJet T n (y (j :: r)) t) :=
    terminalSpatialDerivative_iteratedDerivWithin hT (u j)
      ((hy r hr.le).of_le (by simp : (n : ℕ∞ω) ≤ ∞))
      ((hy (j :: r) (by simpa only [List.length_cons] using Nat.succ_le_of_lt hr)).of_le
        (by simp : (n : ℕ∞ω) ≤ ∞)) (hyd j r hr) n le_rfl t ht
  have hXd (j : I) (r : List I) (hr : r.length < N) :
      endpointTorusHasSpatialDerivative (u j) (X r) (X (j :: r)) :=
    terminalMeanWordDeriv_sum _ _ _ _ (fun k _ =>
      terminalMeanWordProduct_spatialDerivative u (K' k) (f' (i - k))
        (hSp K hK hKd k) (hSp f hf hfd (i - k)) j r hr)
  have hBase : g' i [] = X [] := by
    have hEqTime := iteratedDerivWithin_congr (n := i) hEq ht
    have hh := terminalTimeJet_coefficientMul hT (hK [] (by simp)) (hf [] (by simp)) i t ht
    simpa only [g', X, K', f', terminalMeanWordProduct_nil] using hEqTime.trans hh
  have hWord (r : List I) (hr : r.length ≤ N) : g' i r = X r := by
    induction r with
    | nil => exact hBase
    | cons j r ih =>
        have hl : r.length < N := Nat.lt_of_succ_le hr
        have hh := hSp g hg hgd i j r hl
        change endpointTorusHasSpatialDerivative (u j) (g' i r) (g' i (j :: r)) at hh
        rw [ih hl.le] at hh
        apply HalfHolder.ext
        intro a
        simpa only [zero_smul, toUnitTorus_zero, add_zero] using
          (hh a 0).unique (hXd j r hl a 0)
  change ℓ ^ w.length * ‖g' i w‖ ≤ _
  rw [hWord w hw]
  have hProd (j : ℕ) (hj : j ∈ Finset.range (i + 1)) :
      ℓ ^ w.length * ‖terminalMeanWordProduct (K' j) (f' (i - j)) w‖ ≤
        (2 : ℝ) ^ (N + 1) * A * B := by
    have hs := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    refine (terminalMeanWordProduct_norm_le (K' j) (f' (i - j)) w hℓ hA hB
      (fun r hr => hKcap j (hs.trans hi) r (hr.trans hw) t ht)
      (fun r hr => hFcap (i - j) ((Nat.sub_le _ _).trans hi) r (hr.trans hw) t ht)).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ one_le_two (Nat.succ_le_succ hw)) hA) hB
  refine (terminalMeanWeightedSum_norm_le _ _ _ (pow_nonneg hℓ _) hProd).trans ?_
  rw [terminalMeanChooseSum]
  calc
    _ ≤ (2 : ℝ) ^ q * ((2 : ℝ) ^ (N + 1) * A * B) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hi) (by positivity)
    _ = _ := by rw [pow_add (2 : ℝ) (N + 1) q]; ring

set_option maxHeartbeats 3200000 in
/-- Once the fixed-time inverse and the spatial commutators are controlled,
the higher time derivatives of the same label velocity cost no further
spatial derivatives of the source. -/
theorem terminalMeanWords_timeJet_bound {I : Type*} {T : ℝ} (hT : 0 < T)
    (u : I → Vec3) (N q : ℕ)
    (K Ω : List I → ℝ → Coeff) (g : List I → ℝ → W) (v : List I → ℝ → S)
    (hK : ∀ w, w.length ≤ N → ContDiffOn ℝ ∞ (K w) Time(T))
    (hΩ : ∀ w, w.length ≤ N → ContDiffOn ℝ ∞ (Ω w) Time(T))
    (hg : ∀ w, w.length ≤ N → ContDiffOn ℝ ∞ (g w) Time(T))
    (hv : ∀ w, w.length ≤ N → ContDiffOn ℝ ∞ (v w) Time(T))
    (hKd : ∀ j w, w.length < N → ∀ t ∈ Time(T),
      endpointTorusHasSpatialDerivative (u j) (K w t) (K (j :: w) t))
    (hΩd : ∀ j w, w.length < N → ∀ t ∈ Time(T),
      endpointTorusHasSpatialDerivative (u j) (Ω w t) (Ω (j :: w) t))
    (hgd : ∀ j w, w.length < N → ∀ t ∈ Time(T),
      endpointTorusHasSpatialDerivative (u j) (g w t) (g (j :: w) t))
    (hvd : ∀ j w, w.length < N → ∀ t ∈ Time(T),
      endpointTorusHasSpatialDerivative (u j) (v w t).val (v (j :: w) t).val)
    (hEq : ∀ n < q, ∀ t ∈ Time(T),
      P ((K [] t).coefficientMul (terminalTimeJet T (n + 1) (v []) t).val) = P
        ((∑ i ∈ Finset.range (n + 1), n.choose i • (terminalTimeJet T i (Ω []) t).coefficientMul
          (terminalTimeJet T (n - i) (v []) t).val) + terminalTimeJet T n (g []) t -
          ∑ i ∈ Finset.range (n + 1), (n + 1).choose (i + 1) •
            (terminalTimeJet T (i + 1) (K []) t).coefficientMul (terminalTimeJet T (n - i) (v []) t).val))
    (e : ℝ → S ≃L[ℝ] S)
    (he : ∀ t ∈ Time(T), ∀ z : S, e t z = P ((K [] t).coefficientMul z.val))
    {μ : ℝ} (hμ : 0 < μ)
    (hPos : ∀ t ∈ Time(T), ∀ a z, μ * ‖z‖ ^ 2 ≤ ⟪HalfHolder.eval a (K [] t) z, z⟫_ℝ)
    {ℓ Ainv Kcost Ccoef G A₀ : ℝ} (hℓ : 0 ≤ ℓ)
    (hInv : ∀ t ∈ Time(T), ‖((e t).symm : S →L[ℝ] S)‖ ≤ Ainv)
    (hKcost : 0 ≤ Kcost) (hCoe : 0 ≤ Ccoef) (hG : 0 ≤ G) (hInit : 0 ≤ A₀)
    (hK0 : ∀ w, 1 ≤ w.length → w.length ≤ N → ∀ t ∈ Time(T),
      Ainv * (ℓ ^ w.length * (2 * ‖Leray‖ * ‖K w t‖)) ≤ Kcost)
    (hCoeff : ∀ i ≤ q, ∀ w, w.length ≤ N → ∀ t ∈ Time(T),
      ℓ ^ w.length * ‖terminalTimeJet T i (K w) t‖ ≤ Ccoef ∧
        ℓ ^ w.length * ‖terminalTimeJet T i (Ω w) t‖ ≤ Ccoef)
    (hGcap : ∀ i < q, ∀ w, w.length ≤ N → ∀ t ∈ Time(T),
      ℓ ^ w.length * ‖terminalTimeJet T i (g w) t‖ ≤ G)
    (hV0 : ∀ w, w.length ≤ N → ∀ t ∈ Time(T), ℓ ^ w.length * ‖v w t‖ ≤ A₀ * G) :
    let A := max A₀ (Ainv * ‖Leray‖ * (1 + (2 : ℝ) ^ N * Kcost) ^ N)
    let B := (2 : ℝ) ^ (N + 1) * ((2 : ℝ) ^ q + (2 : ℝ) ^ q) * Ccoef
    ∀ i ≤ q, ∀ w, w.length ≤ N → ∀ t ∈ Time(T),
      ℓ ^ w.length * ‖terminalTimeJet T i (v w) t‖ ≤ (1 + A * (1 + B)) ^ (i + 1) * G := by
  intro A B
  have hAinv : 0 ≤ Ainv := (norm_nonneg _).trans (hInv 0 ⟨le_rfl, hT.le⟩)
  have hA : 0 ≤ A := hInit.trans (le_max_left _ _)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let V (i : ℕ) (C : ℝ) : Prop := ∀ w : List I, w.length ≤ N → ∀ t ∈ Time(T),
    ℓ ^ w.length * ‖terminalTimeJet T i (v w) t‖ ≤ C
  apply terminalMeanTimeBound (V := V) hA hB hG
  · intro i C C' hcc hh w hw t ht
    exact (hh w hw t ht).trans hcc
  · intro w hw t ht
    simpa only [terminalTimeJet, iteratedDerivWithin_zero] using
      (hV0 w hw t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hG)
  intro n hn C hC hLower w hw t ht
  let U (i : ℕ) (w : List I) : S := terminalTimeJet T i (v w) t
  let U' (i : ℕ) (w : List I) : W := (U i w).val
  let K' (i : ℕ) (w : List I) : Coeff := terminalTimeJet T i (K w) t
  let Ω' (i : ℕ) (w : List I) : Coeff := terminalTimeJet T i (Ω w) t
  let G' (w : List I) : W := terminalTimeJet T n (g w) t
  let R₀ (i : ℕ) (w : List I) : W := terminalMeanWordProduct (Ω' i) (U' (n - i)) w
  let R₁ (i : ℕ) (w : List I) : W := terminalMeanWordProduct (K' (i + 1)) (U' (n - i)) w
  let F (w : List I) : W :=
    (∑ i ∈ Finset.range (n + 1), n.choose i • R₀ i w) + G' w -
      ∑ i ∈ Finset.range (n + 1), (n + 1).choose (i + 1) • R₁ i w
  have hUf (i : ℕ) (w : List I) (hw : w.length ≤ N) :
      U' i w = terminalTimeJet T i (fun r => (v w r).val) t :=
    (terminalIteratedDerivWithin_clm (uniqueDiffOn_Icc hT) endpointHalfHolderSolenoidal.subtypeL
      (hv w hw) i ht).symm
  have hSp {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (f : List I → ℝ → HalfHolder Labels E)
      (hf : ∀ w, w.length ≤ N → ContDiffOn ℝ ∞ (f w) Time(T))
      (hfd : ∀ j w, w.length < N → ∀ r ∈ Time(T),
        endpointTorusHasSpatialDerivative (u j) (f w r) (f (j :: w) r))
      (i : ℕ) (j : I) (w : List I) (hw : w.length < N) :
      endpointTorusHasSpatialDerivative (u j) (terminalTimeJet T i (f w) t)
        (terminalTimeJet T i (f (j :: w)) t) :=
    terminalSpatialDerivative_iteratedDerivWithin hT (u j)
      ((hf w hw.le).of_le (by simp : (i : ℕ∞ω) ≤ ∞))
      ((hf (j :: w) (by simpa only [List.length_cons] using Nat.succ_le_of_lt hw)).of_le
        (by simp : (i : ℕ∞ω) ≤ ∞)) (hfd j w hw) i le_rfl t ht
  have hUd (i : ℕ) (j : I) (w : List I) (hw : w.length < N) :
      endpointTorusHasSpatialDerivative (u j) (U' i w) (U' i (j :: w)) := by
    rw [hUf i w hw.le, hUf i (j :: w) (by simpa only [List.length_cons] using Nat.succ_le_of_lt hw)]
    exact hSp (fun w r => (v w r).val)
      (fun z hz => endpointHalfHolderSolenoidal.subtypeL.contDiff.comp_contDiffOn (hv z hz)) hvd i j w hw
  have hFd (j : I) (w : List I) (hw : w.length < N) :
      endpointTorusHasSpatialDerivative (u j) (F w) (F (j :: w)) := by
    apply terminalMeanWordDeriv_add_sub
    · exact terminalMeanWordDeriv_sum _ _ _ _ (fun i _ =>
        terminalMeanWordProduct_spatialDerivative u (Ω' i) (U' (n - i))
          (hSp Ω hΩ hΩd i) (hUd (n - i)) j w hw)
    · exact hSp g hg hgd n j w hw
    · exact terminalMeanWordDeriv_sum _ _ _ _ (fun i _ =>
        terminalMeanWordProduct_spatialDerivative u (K' (i + 1)) (U' (n - i))
          (hSp K hK hKd (i + 1)) (hUd (n - i)) j w hw)
  have hBudget (r : List I) (hr : r.length ≤ N) :
      ℓ ^ r.length * ‖F r‖ ≤ G + B * C := by
    let a := ℓ ^ r.length
    let d := (2 : ℝ) ^ (N + 1) * Ccoef * C
    let R := Finset.range (n + 1)
    let A₁ := ∑ i ∈ R, n.choose i • R₀ i r
    let A₂ := ∑ i ∈ R, (n + 1).choose (i + 1) • R₁ i r
    have ha : 0 ≤ a := pow_nonneg hℓ _
    have hd : 0 ≤ d := by dsimp only [d]; positivity
    have hCap (Kword : List I → Coeff) (i : ℕ)
        (hW : ∀ s, s.length ≤ r.length → ℓ ^ s.length * ‖Kword s‖ ≤ Ccoef) :
        a * ‖terminalMeanWordProduct Kword (U' (n - i)) r‖ ≤ d := by
      refine (terminalMeanWordProduct_norm_le Kword (U' (n - i)) r hℓ hCoe hC hW
        (fun s hs => hLower _ (Nat.sub_le _ _) s (hs.trans hr) t ht)).trans ?_
      dsimp only [d]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ one_le_two (Nat.succ_le_succ hr)) hCoe) hC
    have h₀ : a * ‖A₁‖ ≤ (2 : ℝ) ^ q * d := by
      refine (terminalMeanWeightedSum_norm_le R (fun i => n.choose i) (fun i => R₀ i r) (B := d) ha ?_).trans ?_
      · intro i hi
        have hiN : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact hCap (Ω' i) i (fun s hs => (hCoeff i (hiN.trans hn.le) s (hs.trans hr) t ht).2)
      change (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) * d ≤ _
      rw [terminalMeanChooseSum]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hn.le) hd
    have h₁ : a * ‖A₂‖ ≤ (2 : ℝ) ^ q * d := by
      refine (terminalMeanWeightedSum_norm_le R (fun i => (n + 1).choose (i + 1)) (fun i => R₁ i r)
        (B := d) ha ?_).trans ?_
      · intro i hi
        have hiN : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hiQ : i + 1 ≤ q := (Nat.succ_le_succ hiN).trans (Nat.succ_le_of_lt hn)
        exact hCap (K' (i + 1)) i (fun s hs => (hCoeff (i + 1) hiQ s (hs.trans hr) t ht).1)
      exact mul_le_mul_of_nonneg_right ((terminalMeanChoosePositiveSum n).trans
        (pow_le_pow_right₀ one_le_two (Nat.succ_le_of_lt hn))) hd
    change a * ‖A₁ + G' r - A₂‖ ≤ _
    calc
      _ ≤ a * (‖A₁‖ + ‖G' r‖ + ‖A₂‖) :=
        mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) ha
      _ ≤ (2 : ℝ) ^ q * d + G + (2 : ℝ) ^ q * d := by
        simp only [mul_add]
        exact add_le_add (add_le_add h₀ (hGcap n hn r hr t ht)) h₁
      _ = _ := by dsimp only [B, d]; ring
  have hEqF : P ((K [] t).coefficientMul (U (n + 1) []).val) = P (F []) := by
    simpa only [U, U', F, R₀, R₁, K', Ω', G', terminalMeanWordProduct_nil] using hEq n hn t ht
  have hEqLeray : Leray ((K [] t).coefficientMul (U (n + 1) []).val) = Leray (F []) :=
    congrArg (fun z : S => z.val) hEqF
  have hh := terminalMeanSpatialInverse_wordBounds N u (fun r => K r t) F (U (n + 1))
    (e t) (he t ht) hμ (hPos t ht) hEqLeray (fun i r hr => hKd i r hr t ht) hFd (hUd (n + 1))
    hℓ (add_nonneg hG (mul_nonneg hB hC)) hKcost (hInv t ht) hBudget
    (fun r hpos hr => hK0 r hpos hr t ht) w hw
  refine hh.trans ?_
  calc
    _ ≤ Ainv * (‖Leray‖ * (G + B * C)) * (1 + (2 : ℝ) ^ N * Kcost) ^ N :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) hw) (by positivity)
    _ = (Ainv * ‖Leray‖ * (1 + (2 : ℝ) ^ N * Kcost) ^ N) * (G + B * C) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (add_nonneg hG (mul_nonneg hB hC))

set_option maxHeartbeats 2600000 in
/-- The integrated negative primitive supplies the order-zero bound of
the same spatial words used in the higher time estimate. -/
theorem EndpointPhysicalMeanRecovery.terminalInitialWordBounds {T D L : ℝ} {hT : 0 < T}
    {F M : ℝ × Labels → Vec3 →L[ℝ] Vec3} {force v : Velocity}
    (rec : EndpointPhysicalMeanRecovery hT D L F M force v) (hT₁ : T ≤ 1) (N : ℕ)
    (words : EndpointMeanRecoveredWords hT rec.jets.kineticMixed rec.jets.vorticityMixed
      rec.jets.sourceMixed rec.curve N)
    (g : List (Fin 3) → ℝ → W) (hg : ∀ w, ContinuousOn (g w) Time(T))
    (hgEq : ∀ w, EqOn (rec.jets.source.curve w) (fun r => -endpointPrimitive (g w) r) Time(T))
    {μ LK CK As Am Cap ℓ Kcost G : ℝ} (hμ : 0 < μ) (hLK : 0 ≤ LK)
    (hLip : ∀ t ∈ Time(T), ∀ a b,
      ‖HalfHolder.eval a (rec.jets.kinetic.curve [] t) -
        HalfHolder.eval b (rec.jets.kinetic.curve [] t)‖ ≤ LK * dist a b)
    (hPos : ∀ t ∈ Time(T), ∀ a z,
      μ * ‖z‖ ^ 2 ≤ ⟪HalfHolder.eval a (rec.jets.kinetic.curve [] t) z, z⟫_ℝ)
    (hSup : ∀ t ∈ Time(T), ‖(rec.jets.kinetic.curve [] t).val.1‖ ≤ CK)
    (eS : ℝ → S ≃L[ℝ] S)
    (heS : ∀ t ∈ Time(T), ∀ z : S,
      eS t z = P ((rec.jets.kinetic.curve [] t).coefficientMul z.val))
    (hAs : ∀ t ∈ Time(T), ‖((eS t).symm : S →L[ℝ] S)‖ ≤ As)
    (eM : MixedFixed(T) ≃L[ℝ] MixedFixed(T))
    (heM : (eM : MixedFixed(T) →L[ℝ] MixedFixed(T)) = freezingCompression (endpointStrongMixedLeray T)
      (endpointMixedPathCoefficient hT.le (rec.jets.kineticMixed []) (rec.jets.vorticityMixed [])).coefficientMul
        (endpointStrongMixedLeray_idempotent hT))
    (hAm : ‖(eM.symm : MixedFixed(T) →L[ℝ] MixedFixed(T))‖ ≤ Am)
    (hCap : endpointPhysicalInverseBudget hT.le (rec.jets.kineticMixed []) (rec.jets.vorticityMixed []) As Am ≤ Cap)
    (hℓ : 0 < ℓ) (hKcost : 0 ≤ Kcost) (hG : 0 ≤ G)
    (hCoefficient : ∀ w, 1 ≤ w.length → w.length ≤ N →
      Cap * (ℓ ^ w.length * endpointPhysicalCoefficientWordNorm T rec.jets.kinetic.curve rec.jets.vorticity.curve w) ≤ Kcost)
    (hForce : ∀ w, w.length ≤ N → ∀ t ∈ Time(T), ℓ ^ w.length * ‖g w t‖ ≤ G) :
    ∀ w, w.length ≤ N → ∀ t ∈ Time(T),
      ℓ ^ w.length * ‖words.curve w t‖ ≤ Cap * (1 + (2 : ℝ) ^ N * Kcost) ^ N * G := by
  let K := rec.jets.kinetic.curve
  let Ω := rec.jets.vorticity.curve
  let src := rec.jets.source.curve
  let g₀ := words.curve
  let ΩK (w : List (Fin 3)) := endpointPhysicalCoefficientWordNorm T K Ω w
  have hK (w : List (Fin 3)) : ContinuousOn (K w) Time(T) := (rec.jets.kinetic.smooth w).continuousOn
  have hΩ (w : List (Fin 3)) : ContinuousOn (Ω w) Time(T) := (rec.jets.vorticity.smooth w).continuousOn
  have hs (w : List (Fin 3)) : ContinuousOn (src w) Time(T) := (rec.jets.source.smooth w).continuousOn
  have hv (w : List (Fin 3)) (hw : w.length ≤ N) : ContinuousOn (g₀ w) Time(T) :=
    (words.smooth w hw).continuousOn
  have hAs₀ : 0 ≤ As := (norm_nonneg ((eS 0).symm : S →L[ℝ] S)).trans (hAs 0 ⟨le_rfl, hT.le⟩)
  have hAm₀ : 0 ≤ Am := (norm_nonneg (eM.symm : MixedFixed(T) →L[ℝ] MixedFixed(T))).trans hAm
  have hCap₀ := (endpointPhysicalInverseBudget_nonneg hT.le (rec.jets.kineticMixed [])
    (rec.jets.vorticityMixed []) hAs₀ hAm₀).trans hCap
  have hRec := endpointPhysicalJetNormRecurrence hT rec.jets.kineticMixed rec.jets.vorticityMixed words.mixed
    rec.jets.sourceMixed K Ω src g₀ (fun w _ => hK w) (fun w _ => hΩ w) (fun w _ => hs w) hv
    (fun w _ => ae_of_all _ (rec.jets.source_action w)) words.represents
    (fun w _ => ae_of_all _ (rec.jets.kinetic_action w))
    (fun w _ => ae_of_all _ (rec.jets.vorticity_action w))
    words.fixed words.projected_equation hμ hLK hLip hPos hSup eS heS hAs eM heM hAm
  have hRecCap (w : List (Fin 3)) (hw : w.length ≤ N) : endpointClosedTimeNorm T (g₀ w) ≤ Cap *
      (endpointClosedTimeNorm T (src w) + ((endpointMixedCorrectionPairs w).map fun p =>
        ΩK p.1 * endpointClosedTimeNorm T (g₀ p.2)).sum) := by
    apply (hRec w hw).trans
    apply mul_le_mul_of_nonneg_right hCap
    apply add_nonneg (endpointClosedTimeNorm_nonneg hT.le _)
    apply List.sum_nonneg
    intro x hx
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    have hCoeff : 0 ≤ ΩK p.1 := by
      unfold ΩK endpointPhysicalCoefficientWordNorm
      exact mul_nonneg zero_le_two (add_nonneg (endpointClosedTimeNorm_nonneg hT.le _)
        (mul_nonneg hT.le (endpointClosedTimeNorm_nonneg hT.le _)))
    exact mul_nonneg hCoeff (endpointClosedTimeNorm_nonneg hT.le _)
  have hSource (w : List (Fin 3)) (hw : w.length ≤ N) :
      ℓ ^ w.length * endpointClosedTimeNorm T (src w) ≤ G := by
    have hW : 0 < ℓ ^ w.length := pow_pos hℓ _
    have hForce0 : endpointClosedTimeNorm T (g w) ≤ G / ℓ ^ w.length := by
      apply endpointClosedTimeNorm_le hT.le
      intro t ht
      exact (le_div_iff₀ hW).mpr (by simpa only [mul_comm] using hForce w hw t ht)
    have hSmall (t : ℝ) (ht : t ∈ Time(T)) : ‖src w t‖ ≤ G / ℓ ^ w.length := by
      change ‖rec.jets.source.curve w t‖ ≤ _
      rw [hgEq w ht, norm_neg]
      refine (norm_le_endpointClosedTimeNorm (contDiffOn_endpointPrimitive_succ hT
        (contDiffOn_zero.mpr (hg w))).continuousOn ht).trans ?_
      exact (endpointClosedTimeNorm_endpointPrimitive_le hT.le (hg w)).trans
        ((mul_le_mul_of_nonneg_right hT₁ (endpointClosedTimeNorm_nonneg hT.le _)).trans
          (by simpa only [one_mul] using hForce0))
    rw [mul_comm, ← le_div_iff₀ hW]
    exact endpointClosedTimeNorm_le hT.le hSmall
  have hBound := endpointWeightedPhysicalMeanEstimate hT.le hℓ.le hCap₀ hG hKcost K Ω src g₀
    hSource hCoefficient hRecCap
  intro w hw t ht
  have hbase : 1 ≤ 1 + (2 : ℝ) ^ N * Kcost := le_add_of_nonneg_right (by positivity)
  calc
    _ ≤ ℓ ^ w.length * endpointClosedTimeNorm T (g₀ w) :=
      mul_le_mul_of_nonneg_left (norm_le_endpointClosedTimeNorm (hv w hw) ht) (pow_nonneg hℓ.le _)
    _ ≤ Cap * G * (1 + (2 : ℝ) ^ N * Kcost) ^ w.length := hBound w hw
    _ ≤ Cap * G * (1 + (2 : ℝ) ^ N * Kcost) ^ N :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase hw) (mul_nonneg hCap₀ hG)
    _ = _ := by ring

end

end TorusEuler
