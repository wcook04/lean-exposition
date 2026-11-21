import Breakdown.FracCell.FormulaDataDefs
import Breakdown.FracCell.CylIntegral
import Breakdown.FracCert.EmbedWeak
import Mathlib

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellAnalysis.LowEntry.Internal

open SteadyCert Assembly

theorem lineWeight_cont (K : CellBox) : Continuous K.lineWeight := by
  by_cases h : K.r₁ = 0
  · have e : K.lineWeight = fun r => r := funext fun r => by simp [CellBox.lineWeight, h]
    rw [e]; exact continuous_id
  · have e : K.lineWeight = fun _ => 1 := funext fun r => by simp [CellBox.lineWeight, h]
    rw [e]; exact continuous_const

theorem rect_compact (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

theorem rect_meas (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

theorem radialPoly_cont (B : CellBases) (j : ℕ) : Continuous (B.radialPoly j) := by
  unfold CellBases.radialPoly
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_pow i)

theorem heightPoly_cont (B : CellBases) (j : ℕ) : Continuous (B.heightPoly j) := by
  unfold CellBases.heightPoly
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_pow i)

def bas (B : CellBases) (j l : ℕ) (p : ℝ × ℝ) : ℂ := ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)

theorem bas_cont (B : CellBases) (j l : ℕ) : Continuous (bas B j l) :=
  Complex.continuous_ofReal.comp
    (((radialPoly_cont B j).comp continuous_fst).mul ((heightPoly_cont B l).comp continuous_snd))

theorem poly_zero {d d' : ℕ} : (fun _ : ℝ × ℝ => (0 : ℂ)) ∈ polyFn d d' := ⟨0, fun p => by simp⟩

theorem poly_add {d d' : ℕ} {P Q : ℝ × ℝ → ℂ} (hP : P ∈ polyFn d d') (hQ : Q ∈ polyFn d d') :
    (fun p => P p + Q p) ∈ polyFn d d' := by
  obtain ⟨c, hc⟩ := hP
  obtain ⟨c', hc'⟩ := hQ
  refine ⟨c + c', fun p => ?_⟩
  show P p + Q p = _
  rw [hc, hc', ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Pi.add_apply]; ring

theorem poly_smul {d d' : ℕ} (a : ℂ) {P : ℝ × ℝ → ℂ} (hP : P ∈ polyFn d d') :
    (fun p => a * P p) ∈ polyFn d d' := by
  obtain ⟨c, hc⟩ := hP
  refine ⟨fun j l => a * c j l, fun p => ?_⟩
  show a * P p = _
  rw [hc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem poly_mono {d d' i m : ℕ} (hi : i ≤ d) (hm : m ≤ d') :
    (fun p : ℝ × ℝ => (p.1 : ℂ) ^ i * (p.2 : ℂ) ^ m) ∈ polyFn d d' := by
  refine ⟨fun j l => if (j : ℕ) = i ∧ (l : ℕ) = m then 1 else 0, fun p => ?_⟩
  rw [Finset.sum_eq_single (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (d + 1))]
  · rw [Finset.sum_eq_single (⟨m, Nat.lt_succ_of_le hm⟩ : Fin (d' + 1))]
    · simp
    · intro b _ hb
      have : (b : ℕ) ≠ m := fun h => hb (Fin.ext h)
      simp [this]
    · simp
  · intro b _ hb
    have : (b : ℕ) ≠ i := fun h => hb (Fin.ext h)
    simp [this]
  · simp

theorem poly_sum {d d' : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℝ × ℝ → ℂ)
    (h : ∀ i ∈ s, f i ∈ polyFn d d') : (fun p => ∑ i ∈ s, f i p) ∈ polyFn d d' := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _; simpa using (poly_zero (d := d) (d' := d'))
  · intro a s ha ih h
    simp only [Finset.sum_insert ha]
    exact poly_add (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem poly_cont {d d' : ℕ} {P : ℝ × ℝ → ℂ} (hP : P ∈ polyFn d d') : Continuous P := by
  obtain ⟨c, hc⟩ := hP
  rw [show P = _ from funext hc]
  exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun l _ =>
    (continuous_const.mul ((Complex.continuous_ofReal.comp continuous_fst).pow _)).mul
      ((Complex.continuous_ofReal.comp continuous_snd).pow _)

theorem bas_mem (B : CellBases) {d d' j l : ℕ} (hj : j ≤ d) (hl : l ≤ d') : bas B j l ∈ polyFn d d' := by
  have e : bas B j l = fun p => ∑ i ∈ Finset.range (j + 1), ∑ m ∈ Finset.range (l + 1),
      ((B.radialCoef j i * B.heightCoef l m : ℝ) : ℂ) * ((p.1 : ℂ) ^ i * (p.2 : ℂ) ^ m) := by
    funext p
    simp only [bas, CellBases.radialPoly, CellBases.heightPoly, Finset.sum_mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring
  rw [e]
  refine poly_sum _ _ fun i hi => poly_sum _ _ fun m hm => poly_smul _ (poly_mono ?_ ?_)
  · have := Finset.mem_range.1 hi; omega
  · have := Finset.mem_range.1 hm; omega

theorem ortho (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (j l j' l' : ℕ) :
    ∫ p in K.rect, K.lineWeight p.1 * (B.radialPoly j p.1 * B.heightPoly l p.2) *
      (B.radialPoly j' p.1 * B.heightPoly l' p.2) = if j = j' ∧ l = l' then 1 else 0 := by
  have e : (fun p : ℝ × ℝ => K.lineWeight p.1 * (B.radialPoly j p.1 * B.heightPoly l p.2) *
      (B.radialPoly j' p.1 * B.heightPoly l' p.2)) = fun p =>
      (K.lineWeight p.1 * B.radialPoly j p.1 * B.radialPoly j' p.1) * (B.heightPoly l p.2 * B.heightPoly l' p.2) := by
    funext p; ring
  rw [e, CellBox.rect, Measure.volume_eq_prod, setIntegral_prod_mul (fun r => K.lineWeight r * B.radialPoly j r * B.radialPoly j' r)
    (fun z => B.heightPoly l z * B.heightPoly l' z), hB.radial_orthonormal, hB.height_orthonormal]
  by_cases h1 : j = j' <;> by_cases h2 : l = l' <;> simp [h1, h2]

theorem span_zero (c : ℕ → ℕ → ℝ) (hc : ∀ j, c j j ≠ 0) (ψ : (ℝ → ℝ) → ℂ)
    (hadd : ∀ f g : ℝ → ℝ, Continuous f → Continuous g → ψ (fun r => f r + g r) = ψ f + ψ g)
    (hsmul : ∀ (a : ℝ) (f : ℝ → ℝ), Continuous f → ψ (fun r => a * f r) = a * ψ f)
    (d : ℕ) (h0 : ∀ i ≤ d, ψ (fun r => ∑ t ∈ Finset.range (i + 1), c i t * r ^ t) = 0) :
    ∀ j ≤ d, ψ (fun r => r ^ j) = 0 := by
  have hzero : ψ (fun _ => 0) = 0 := by
    have := hsmul 0 (fun _ => 0) continuous_const
    simpa using this
  have hsum : ∀ (s : Finset ℕ) (f : ℕ → ℝ → ℝ), (∀ t ∈ s, Continuous (f t)) →
      ψ (fun r => ∑ t ∈ s, f t r) = ∑ t ∈ s, ψ (f t) := by
    intro s f
    classical
    refine Finset.induction_on s ?_ ?_
    · intro _; simpa using hzero
    · intro a s ha ih h
      simp only [Finset.sum_insert ha]
      rw [hadd (f a) (fun r => ∑ t ∈ s, f t r) (h a (Finset.mem_insert_self _ _))
        (continuous_finsetSum _ fun t ht => h t (Finset.mem_insert_of_mem ht)),
        ih fun t ht => h t (Finset.mem_insert_of_mem ht)]
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have e : (fun r : ℝ => ∑ t ∈ Finset.range (j + 1), c j t * r ^ t) =
        fun r => (∑ t ∈ Finset.range j, c j t * r ^ t) + c j j * r ^ j := by
      funext r; rw [Finset.sum_range_succ]
    have h1 := h0 j hj
    rw [e, hadd (fun r => ∑ t ∈ Finset.range j, c j t * r ^ t) (fun r => c j j * r ^ j)
      (continuous_finsetSum _ fun t _ => continuous_const.mul (continuous_pow t))
      (continuous_const.mul (continuous_pow j)), hsum (Finset.range j) (fun t r => c j t * r ^ t)
      (fun t _ => continuous_const.mul (continuous_pow t))] at h1
    have h2 := hsmul (c j j) (fun r => r ^ j) (continuous_pow j)
    have hz : ∑ t ∈ Finset.range j, ψ (fun r => c j t * r ^ t) = 0 := by
      refine Finset.sum_eq_zero fun t ht => ?_
      have h3 := hsmul (c j t) (fun r => r ^ t) (continuous_pow t)
      rw [h3, ih t (Finset.mem_range.1 ht) (by have := Finset.mem_range.1 ht; omega), mul_zero]
    rw [hz, zero_add, h2] at h1
    exact (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hc j)

def psi (K : CellBox) (G : ℝ × ℝ → ℂ) (u : ℝ × ℝ → ℝ) : ℂ := ∫ p in K.rect, G p * (u p : ℂ)

theorem psi_int (K : CellBox) {G : ℝ × ℝ → ℂ} (hG : IntegrableOn G K.rect) {u : ℝ × ℝ → ℝ} (hu : Continuous u) :
    IntegrableOn (fun p => G p * (u p : ℂ)) K.rect :=
  hG.mul_continuousOn (Complex.continuous_ofReal.comp hu).continuousOn (rect_compact K)

theorem psi_add (K : CellBox) {G : ℝ × ℝ → ℂ} (hG : IntegrableOn G K.rect) {u v : ℝ × ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) : psi K G (fun p => u p + v p) = psi K G u + psi K G v := by
  unfold psi
  rw [← integral_add (psi_int K hG hu) (psi_int K hG hv)]
  congr 1; funext p; push_cast; ring

theorem psi_smul (K : CellBox) (G : ℝ × ℝ → ℂ) (a : ℝ) (u : ℝ × ℝ → ℝ) :
    psi K G (fun p => a * u p) = a * psi K G u := by
  unfold psi
  rw [← integral_const_mul]
  congr 1; funext p; push_cast; ring

theorem weight_cont (K : CellBox) : Continuous (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ)) :=
  Complex.continuous_ofReal.comp ((lineWeight_cont K).comp continuous_fst)

theorem coef_eq_of_orth (K : CellBox) (B : CellBases) {d d' : ℕ} {F P : ℝ × ℝ → ℂ}
    (hF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect) (hP : P ∈ polyFn d d')
    (ho : ∀ T ∈ polyFn d d', K.pairOn K.lineWeightFn (fun p => F p - P p) T = 0) {j l : ℕ}
    (hj : j ≤ d) (hl : l ≤ d') : B.coef K P j l = B.coef K F j l := by
  have h := ho (bas B j l) (bas_mem B hj hl)
  have i1 : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p * bas B j l p) K.rect :=
    hF.mul_continuousOn (bas_cont B j l).continuousOn (rect_compact K)
  have i2 : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * P p * bas B j l p) K.rect :=
    (((weight_cont K).mul (poly_cont hP)).mul (bas_cont B j l)).continuousOn.integrableOn_compact (rect_compact K)
  have e : K.pairOn K.lineWeightFn (fun p => F p - P p) (bas B j l) = B.coef K F j l - B.coef K P j l := by
    rw [show B.coef K F j l - B.coef K P j l = ∫ p in K.rect, ((K.lineWeight p.1 : ℂ) * F p * bas B j l p -
      (K.lineWeight p.1 : ℂ) * P p * bas B j l p) from (integral_sub i1 i2).symm]
    unfold CellBox.pairOn
    congr 1; funext p
    simp only [CellBox.lineWeightFn, bas, Complex.conj_ofReal]
    ring
  rw [e, sub_eq_zero] at h
  exact h.symm

theorem coef_proj (K : CellBox) (B : CellBases) (hB : IsCellBases K B) {F : ℝ × ℝ → ℂ}
    (hF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect) {d d' j l : ℕ} (hj : j ≤ d)
    (hl : l ≤ d') : B.coef K (K.proj d d' F) j l = B.coef K F j l := by
  set P : ℝ × ℝ → ℂ := fun p => ∑ i ∈ Finset.range (d + 1), ∑ m ∈ Finset.range (d' + 1),
    B.coef K F i m * bas B i m p with hPdef
  have hPpoly : P ∈ polyFn d d' := poly_sum _ _ fun i hi => poly_sum _ _ fun m hm =>
    poly_smul _ (bas_mem B (by have := Finset.mem_range.1 hi; omega) (by have := Finset.mem_range.1 hm; omega))
  set G : ℝ × ℝ → ℂ := fun p => (K.lineWeight p.1 : ℂ) * (F p - P p) with hGdef
  have hG : IntegrableOn G K.rect := by
    have e : G = fun p => (K.lineWeight p.1 : ℂ) * F p - (K.lineWeight p.1 : ℂ) * P p := by
      funext p; simp only [hGdef]; ring
    rw [e]
    exact hF.sub (((weight_cont K).mul (poly_cont hPpoly)).continuousOn.integrableOn_compact (rect_compact K))
  have s0 : ∀ i ≤ d, ∀ m ≤ d', psi K G (fun p => B.radialPoly i p.1 * B.heightPoly m p.2) = 0 := by
    intro i hi m hm
    have iF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p * bas B i m p) K.rect :=
      hF.mul_continuousOn (bas_cont B i m).continuousOn (rect_compact K)
    have iP : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * P p * bas B i m p) K.rect :=
      (((weight_cont K).mul (poly_cont hPpoly)).mul (bas_cont B i m)).continuousOn.integrableOn_compact
        (rect_compact K)
    have hcont : ∀ j l, Continuous (fun p : ℝ × ℝ => K.lineWeight p.1 * (B.radialPoly j p.1 * B.heightPoly l p.2) *
        (B.radialPoly i p.1 * B.heightPoly m p.2)) := fun j l =>
      (((lineWeight_cont K).comp continuous_fst).mul (((radialPoly_cont B j).comp continuous_fst).mul
        ((heightPoly_cont B l).comp continuous_snd))).mul (((radialPoly_cont B i).comp continuous_fst).mul
        ((heightPoly_cont B m).comp continuous_snd))
    have eP : ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * P p * bas B i m p = B.coef K F i m := by
      calc ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * P p * bas B i m p
          = ∫ p in K.rect, ∑ j ∈ Finset.range (d + 1), ∑ l ∈ Finset.range (d' + 1), B.coef K F j l *
              ((K.lineWeight p.1 * (B.radialPoly j p.1 * B.heightPoly l p.2) *
                (B.radialPoly i p.1 * B.heightPoly m p.2) : ℝ) : ℂ) := by
            congr 1; funext p
            simp only [hPdef, bas, Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
            push_cast; ring
        _ = ∑ j ∈ Finset.range (d + 1), ∑ l ∈ Finset.range (d' + 1), B.coef K F j l *
              ((∫ p in K.rect, K.lineWeight p.1 * (B.radialPoly j p.1 * B.heightPoly l p.2) *
                (B.radialPoly i p.1 * B.heightPoly m p.2) : ℝ) : ℂ) := by
            rw [integral_finsetSum]
            · refine Finset.sum_congr rfl fun j _ => ?_
              rw [integral_finsetSum]
              · refine Finset.sum_congr rfl fun l _ => ?_
                rw [integral_const_mul, integral_complex_ofReal]
              · intro l _
                exact ((Complex.continuous_ofReal.comp (hcont j l)).continuousOn.integrableOn_compact
                  (rect_compact K)).const_mul _
            · intro j _
              exact integrable_finsetSum _ fun l _ =>
                ((Complex.continuous_ofReal.comp (hcont j l)).continuousOn.integrableOn_compact
                  (rect_compact K)).const_mul _
        _ = B.coef K F i m := by
            simp_rw [ortho K B hB]
            rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.2 (by omega))
              (fun j _ hj => Finset.sum_eq_zero fun l _ => by simp [hj])]
            rw [Finset.sum_eq_single_of_mem m (Finset.mem_range.2 (by omega)) (fun l _ hl => by simp [hl])]
            simp
    unfold psi
    rw [show (∫ p in K.rect, G p * ((B.radialPoly i p.1 * B.heightPoly m p.2 : ℝ) : ℂ)) =
        ∫ p in K.rect, ((K.lineWeight p.1 : ℂ) * F p * bas B i m p - (K.lineWeight p.1 : ℂ) * P p * bas B i m p) by
          congr 1; funext p; simp only [hGdef, bas]; ring,
      integral_sub iF iP, eP]
    exact sub_eq_zero.2 rfl
  have s1 : ∀ m ≤ d', ∀ j ≤ d, psi K G (fun p => p.1 ^ j * B.heightPoly m p.2) = 0 := by
    intro m hm
    refine span_zero B.radialCoef (fun j => (hB.radial_leading j).ne')
      (fun g => psi K G (fun p => g p.1 * B.heightPoly m p.2)) ?_ ?_ d (fun i hi => s0 i hi m hm)
    · intro f g hf hg
      have e : (fun p : ℝ × ℝ => (f p.1 + g p.1) * B.heightPoly m p.2) =
          fun p => f p.1 * B.heightPoly m p.2 + g p.1 * B.heightPoly m p.2 := by funext p; ring
      show psi K G (fun p => (f p.1 + g p.1) * B.heightPoly m p.2) = _
      rw [e, psi_add K hG (u := fun p => f p.1 * B.heightPoly m p.2) (v := fun p => g p.1 * B.heightPoly m p.2)
        ((hf.comp continuous_fst).mul ((heightPoly_cont B m).comp continuous_snd))
        ((hg.comp continuous_fst).mul ((heightPoly_cont B m).comp continuous_snd))]
    · intro a f _
      have e : (fun p : ℝ × ℝ => (a * f p.1) * B.heightPoly m p.2) =
          fun p => a * (f p.1 * B.heightPoly m p.2) := by funext p; ring
      show psi K G (fun p => (a * f p.1) * B.heightPoly m p.2) = _
      rw [e, psi_smul]
  have s2 : ∀ j ≤ d, ∀ l ≤ d', psi K G (fun p => p.1 ^ j * p.2 ^ l) = 0 := by
    intro j hj
    refine span_zero B.heightCoef (fun j => (hB.height_leading j).ne')
      (fun g => psi K G (fun p => p.1 ^ j * g p.2)) ?_ ?_ d' (fun m hm => s1 m hm j hj)
    · intro f g hf hg
      have e : (fun p : ℝ × ℝ => p.1 ^ j * (f p.2 + g p.2)) =
          fun p => p.1 ^ j * f p.2 + p.1 ^ j * g p.2 := by funext p; ring
      show psi K G (fun p => p.1 ^ j * (f p.2 + g p.2)) = _
      rw [e, psi_add K hG (u := fun p => p.1 ^ j * f p.2) (v := fun p => p.1 ^ j * g p.2)
        ((continuous_fst.pow j).mul (hf.comp continuous_snd))
        ((continuous_fst.pow j).mul (hg.comp continuous_snd))]
    · intro a f _
      have e : (fun p : ℝ × ℝ => p.1 ^ j * (a * f p.2)) =
          fun p => a * (p.1 ^ j * f p.2) := by funext p; ring
      show psi K G (fun p => p.1 ^ j * (a * f p.2)) = _
      rw [e, psi_smul]
  have horth : ∀ T ∈ polyFn d d', K.pairOn K.lineWeightFn (fun p => F p - P p) T = 0 := by
    intro T hT
    obtain ⟨c, hc⟩ := hT
    have hmc : ∀ (j l : ℕ), Continuous (fun p : ℝ × ℝ => p.1 ^ j * p.2 ^ l) := fun j l =>
      (continuous_fst.pow j).mul (continuous_snd.pow l)
    unfold CellBox.pairOn
    calc ∫ p in K.rect, (K.lineWeightFn p : ℂ) * (fun p => F p - P p) p * (starRingEnd ℂ) (T p)
        = ∫ p in K.rect, ∑ j : Fin (d + 1), ∑ l : Fin (d' + 1),
            (starRingEnd ℂ) (c j l) * (G p * ((p.1 ^ (j : ℕ) * p.2 ^ (l : ℕ) : ℝ) : ℂ)) := by
          congr 1; funext p
          rw [hc p]
          simp only [map_sum, map_mul, map_pow, Complex.conj_ofReal, Finset.mul_sum, hGdef, CellBox.lineWeightFn]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
          push_cast; ring
      _ = ∑ j : Fin (d + 1), ∑ l : Fin (d' + 1),
            (starRingEnd ℂ) (c j l) * psi K G (fun p => p.1 ^ (j : ℕ) * p.2 ^ (l : ℕ)) := by
          rw [integral_finsetSum]
          · refine Finset.sum_congr rfl fun j _ => ?_
            rw [integral_finsetSum]
            · refine Finset.sum_congr rfl fun l _ => ?_
              rw [integral_const_mul]; rfl
            · intro l _; exact (psi_int K hG (hmc j l)).const_mul _
          · intro j _; exact integrable_finsetSum _ fun l _ => (psi_int K hG (hmc j l)).const_mul _
      _ = 0 := Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun l _ => by
          rw [s2 j (Nat.lt_succ_iff.1 j.2) l (Nat.lt_succ_iff.1 l.2), mul_zero]
  have hex : ∃ P ∈ polyFn d d', ∀ T ∈ polyFn d d', K.pairOn K.lineWeightFn (fun p => F p - P p) T = 0 :=
    ⟨P, hPpoly, horth⟩
  unfold CellBox.proj
  rw [dif_pos hex]
  exact coef_eq_of_orth K B hF hex.choose_spec.1 hex.choose_spec.2 hj hl

section CylPart

open Set Real
open Breakdown.CellCert.Spectral.Internal.CylIntegral

def cylArg (q : (ℝ × ℝ) × ℝ) : Space := cylPoint q.1.1 q.2 q.1.2

def muU : Measure ((ℝ × ℝ) × ℝ) :=
  (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod (volume.restrict (Ioo (-π) π))

theorem muU_def : muU = (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod (volume.restrict (Ioo (-π) π)) := rfl

theorem muU_eq : muU = volume.restrict ((Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioo (-π) π) :=
  Measure.prod_restrict _ _

theorem cylArg_meas : Measurable cylArg := by
  have e : cylArg = fun q : (ℝ × ℝ) × ℝ => toSpace ((q.1.1 * Real.cos q.2, q.1.1 * Real.sin q.2), q.1.2) :=
    funext fun q => (toSpace_apply _ _ _).symm
  rw [e]
  exact toSpace.measurable.comp (Continuous.measurable (by fun_prop))

theorem key (g : Space → ENNReal) : ∫⁻ q, ENNReal.ofReal q.1.1 * g (cylArg q) ∂muU = ∫⁻ y, g y := by
  rw [muU_eq, ← swapEquiv_preimage]
  calc ∫⁻ q in swapEquiv ⁻¹' cylMap.target, ENNReal.ofReal q.1.1 * g (cylArg q)
      = ∫⁻ q in swapEquiv ⁻¹' cylMap.target,
          (fun x => ENNReal.ofReal x.1.1 * g (toSpace (cylMap.symm x))) (swapEquiv q) := by
        congr 1; funext q
        obtain ⟨⟨r, z⟩, θ⟩ := q
        show ENNReal.ofReal r * g (cylPoint r θ z) = _
        rw [show cylPoint r θ z = toSpace ((r * Real.cos θ, r * Real.sin θ), z) from (toSpace_apply r θ z).symm]
        rfl
    _ = ∫⁻ x in cylMap.target, ENNReal.ofReal x.1.1 * g (toSpace (cylMap.symm x)) :=
        swapEquiv_mp.setLIntegral_comp_preimage_emb swapEquiv.measurableEmbedding
          (fun x => ENNReal.ofReal x.1.1 * g (toSpace (cylMap.symm x))) cylMap.target
    _ = ∫⁻ x in cylMap.target, ENNReal.ofReal |(cylDeriv x).det| * g (toSpace (cylMap.symm x)) :=
        setLIntegral_congr_fun cylMap.open_target.measurableSet (fun x hx => by simp only [abs_det_eq hx])
    _ = ∫⁻ w in cylMap.symm '' cylMap.target, g (toSpace w) :=
        (lintegral_image_eq_lintegral_abs_det_fderiv_mul volume cylMap.open_target.measurableSet
          (fun x _ => (hasDeriv x).hasFDerivWithinAt) cylMap.symm.injOn (fun w => g (toSpace w))).symm
    _ = ∫⁻ w, g (toSpace w) := by rw [setLIntegral_congr image_ae, setLIntegral_univ]
    _ = ∫⁻ y, g y := toSpace_mp.lintegral_comp_emb toSpace.measurableEmbedding g

theorem qmp : Measure.QuasiMeasurePreserving cylArg muU volume := by
  refine ⟨cylArg_meas, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply cylArg_meas hs]
  have h1 := key (s.indicator 1)
  rw [lintegral_indicator_one hs, h0] at h1
  have h2 : ∀ᵐ q ∂muU, ENNReal.ofReal q.1.1 * s.indicator 1 (cylArg q) = 0 :=
    (lintegral_eq_zero_iff' ((ENNReal.measurable_ofReal.comp measurable_fst.fst).mul
      ((measurable_one.indicator hs).comp cylArg_meas)).aemeasurable).1 h1
  have h3 : ∀ᵐ q ∂muU, q ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioo (-π) π := by
    rw [muU_eq]
    exact ae_restrict_mem ((measurableSet_Ioi.prod MeasurableSet.univ).prod measurableSet_Ioo)
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [h2, h3] with q hq hq'
  intro hmem
  have hr : 0 < q.1.1 := hq'.1.1
  rw [Set.indicator_of_mem (show cylArg q ∈ s from hmem)] at hq
  simp at hq
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cylPoint_norm (r θ z : ℝ) : ‖cylPoint r θ z‖ ≤ 2 * |r| + |z| := by
  unfold cylPoint
  refine (norm_add₃_le).trans ?_
  rw [PiLp.norm_single, PiLp.norm_single, PiLp.norm_single, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_mul, abs_mul]
  have h1 := Real.abs_cos_le_one θ
  have h2 := Real.abs_sin_le_one θ
  have h3 := abs_nonneg r
  nlinarith

theorem mode_int (K : CellBox) (hK : IsCellBox K) {X : Space → E} (hX : LocallyIntegrable X volume)
    (φ : ℝ → E → ℂ) (hφc : Continuous (fun q : ℝ × E => φ q.1 q.2)) (hφb : ∀ θ e, ‖φ θ e‖ ≤ ‖e‖) :
    IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) *
      ∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2))) K.rect := by
  have hXm := hX.aestronglyMeasurable
  have hf : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => φ q.2 (X (cylArg q))) muU :=
    hφc.comp_aestronglyMeasurable (measurable_snd.aestronglyMeasurable.prodMk
      (hXm.comp_quasiMeasurePreserving qmp))
  rw [muU_def] at hf
  have hF : AEStronglyMeasurable (fun p : ℝ × ℝ => ∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2)))
      (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := hf.integral_prod_right'
  have hle : volume.restrict K.rect ≤ volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
    refine Measure.restrict_mono_ae ?_
    have hsub : K.rect ⊆ Ici (0 : ℝ) ×ˢ (univ : Set ℝ) := fun p hp => ⟨le_trans hK.r_order.1 hp.1.1, trivial⟩
    refine hsub.eventuallyLE.trans ?_
    have : (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ)) =ᵐ[volume] Ici (0 : ℝ) ×ˢ (univ : Set ℝ) :=
      Measure.set_prod_ae_eq Ioi_ae_eq_Ici (ae_eq_refl _)
    exact this.symm.le
  set R : ℝ := 2 * K.r₂ + K.z₂ with hR
  set g : Space → ENNReal := (Metric.closedBall (0 : Space) R).indicator (fun y => ‖X y‖ₑ) with hg_def
  set C : ℝ := if K.r₁ = 0 then 1 else K.r₁⁻¹ with hC
  have hC0 : 0 ≤ C := by
    rw [hC]; split_ifs
    · norm_num
    · exact inv_nonneg.2 hK.r_order.1
  have hw : ∀ p ∈ K.rect, 0 ≤ K.lineWeight p.1 ∧ K.lineWeight p.1 ≤ C * p.1 := by
    intro p hp
    have h1 : K.r₁ ≤ p.1 := hp.1.1
    by_cases h : K.r₁ = 0
    · simp only [CellBox.lineWeight, hC, h, if_true]
      constructor <;> linarith
    · have hr : 0 < K.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h)
      simp only [CellBox.lineWeight, hC, h, if_false]
      refine ⟨zero_le_one, ?_⟩
      rw [inv_mul_eq_div, le_div_iff₀ hr]
      linarith
  have hball : ∀ p ∈ K.rect, ∀ θ, cylPoint p.1 θ p.2 ∈ Metric.closedBall (0 : Space) R := by
    intro p hp θ
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (cylPoint_norm _ _ _).trans ?_
    have h1 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
    have h2 : 0 ≤ p.2 := le_trans hK.z_order.1 hp.2.1
    rw [abs_of_nonneg h1, abs_of_nonneg h2, hR]
    linarith [hp.1.2, hp.2.2]
  have hpt : ∀ p ∈ K.rect, ‖(K.lineWeight p.1 : ℂ) * ∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2))‖ₑ ≤
      ENNReal.ofReal C * (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) := by
    intro p hp
    obtain ⟨hw0, hw1⟩ := hw p hp
    have hi : ‖∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2))‖ₑ ≤
        ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := by
      refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun θ => ?_)
      rw [hg_def, Set.indicator_of_mem (hball p hp θ), ← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hφb θ _)
    have hw' : ‖((K.lineWeight p.1 : ℝ) : ℂ)‖ₑ ≤ ENNReal.ofReal C * ENNReal.ofReal p.1 := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0, ← ENNReal.ofReal_mul hC0]
      exact ENNReal.ofReal_le_ofReal hw1
    rw [enorm_mul, ← mul_assoc]
    exact mul_le_mul' hw' hi
  have hgm : AEMeasurable g volume := hXm.enorm.indicator measurableSet_closedBall
  have hfin : ∫⁻ y, g y < ⊤ := by
    rw [hg_def, lintegral_indicator measurableSet_closedBall]
    exact (hX.integrableOn_isCompact (isCompact_closedBall 0 R)).2
  have hint : ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal p.1 *
      ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) = ∫⁻ y, g y := by
    rw [← key g, muU_def, lintegral_prod]
    · congr 1; funext p
      dsimp only
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    · exact (ENNReal.measurable_ofReal.comp measurable_fst.fst).aemeasurable.mul
        (hgm.comp_quasiMeasurePreserving (muU_def ▸ qmp))
  refine ⟨((weight_cont K).aestronglyMeasurable).mul (hF.mono_measure hle), ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (b := ENNReal.ofReal C * ∫⁻ y, g y) ?_ (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  calc ∫⁻ p in K.rect, ‖(K.lineWeight p.1 : ℂ) * ∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2))‖ₑ
      ≤ ∫⁻ p in K.rect, ENNReal.ofReal C * (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) :=
        setLIntegral_mono' (rect_meas K) hpt
    _ ≤ ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal C *
          (ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) := lintegral_mono' hle le_rfl
    _ = ENNReal.ofReal C * ∫⁻ y, g y := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hint]

end CylPart

section ModePart

open Set Real

theorem single_smul (i : Fin 3) (a : ℝ) :
    EuclideanSpace.single i a = a • EuclideanSpace.single i (1 : ℝ) := by
  ext j; by_cases h : j = i <;> simp [h]

theorem radialUnit_cont : Continuous radialUnit := by
  have e : radialUnit = fun θ => Real.cos θ • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
      Real.sin θ • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) := by
    funext θ; simp only [radialUnit]; rw [single_smul 0, single_smul 1]
  rw [e]; fun_prop

theorem angularUnit_cont : Continuous angularUnit := by
  have e : angularUnit = fun θ => (-Real.sin θ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
      Real.cos θ • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) := by
    funext θ; simp only [angularUnit]; rw [single_smul 0, single_smul 1]
  rw [e]; fun_prop

theorem unit_cont (b : Fin 3) : Continuous (fun θ => ![radialUnit θ, angularUnit θ, axialUnit] b) := by
  fin_cases b
  · simpa using radialUnit_cont
  · simpa using angularUnit_cont
  · simpa using (continuous_const : Continuous fun _ : ℝ => axialUnit)

theorem unit_norm (θ : ℝ) (b : Fin 3) : ‖![radialUnit θ, angularUnit θ, axialUnit] b‖ ≤ 1 := by
  fin_cases b <;> simp [radialUnit, angularUnit, axialUnit, EuclideanSpace.norm_eq, Fin.sum_univ_three]

theorem inner_unit_bound (θ : ℝ) (u : Space) (a : Fin 3) :
    |inner ℝ u (![radialUnit θ, angularUnit θ, axialUnit] a)| ≤ ‖u‖ := by
  refine (abs_real_inner_le_norm _ _).trans ?_
  simpa using mul_le_mul_of_nonneg_left (unit_norm θ a) (norm_nonneg u)

theorem frameMat_bound (θ : ℝ) (M : Space →L[ℝ] Space) (a b : Fin 3) : |frameMat θ M a b| ≤ ‖M‖ := by
  unfold frameMat
  refine (inner_unit_bound θ _ a).trans ?_
  refine (M.le_opNorm _).trans ?_
  simpa using mul_le_mul_of_nonneg_left (unit_norm θ b) (norm_nonneg M)

theorem frameVec_eq (θ : ℝ) (u : Space) (a : Fin 3) :
    frameVec θ u a = inner ℝ u (![radialUnit θ, angularUnit θ, axialUnit] a) := by
  fin_cases a <;> rfl

theorem frameMat_cont (a b : Fin 3) :
    Continuous (fun q : ℝ × (Space →L[ℝ] Space) => frameMat q.1 q.2 a b) := by
  unfold frameMat
  exact (continuous_snd.clm_apply ((unit_cont b).comp continuous_fst)).inner ((unit_cont a).comp continuous_fst)

theorem frameVec_cont (a : Fin 3) : Continuous (fun q : ℝ × Space => frameVec q.1 q.2 a) := by
  simp only [frameVec_eq]
  exact continuous_snd.inner ((unit_cont a).comp continuous_fst)

theorem phase_cont (m : ℕ) (n : ℤ) {β : Type*} [TopologicalSpace β] :
    Continuous (fun q : ℝ × β => Complex.exp (-((azimuth m n * q.1 : ℝ) : ℂ) * Complex.I)) :=
  Complex.continuous_exp.comp (((Complex.continuous_ofReal.comp (continuous_const.mul continuous_fst)).neg).mul
    continuous_const)

theorem phase_norm (m : ℕ) (n : ℤ) (θ : ℝ) : ‖Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I)‖ = 1 := by
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]

theorem phase_per (m : ℕ) (n : ℤ) (θ : ℝ) :
    Complex.exp (-((azimuth m n * (θ + 2 * π) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) := by
  have e : -((azimuth m n * (θ + 2 * π) : ℝ) : ℂ) * Complex.I =
      -((azimuth m n * θ : ℝ) : ℂ) * Complex.I + ((-(n * (m : ℤ)) : ℤ) : ℂ) * (2 * π * Complex.I) := by
    simp only [azimuth]; push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem cylPoint_per (r θ z : ℝ) : cylPoint r (θ + 2 * π) z = cylPoint r θ z := by
  simp only [cylPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem frameMat_per (θ : ℝ) (M : Space →L[ℝ] Space) (a b : Fin 3) :
    frameMat (θ + 2 * π) M a b = frameMat θ M a b := by
  simp only [frameMat, radialUnit, angularUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem frameVec_per (θ : ℝ) (u : Space) (a : Fin 3) : frameVec (θ + 2 * π) u a = frameVec θ u a := by
  simp only [frameVec, radialUnit, angularUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem per_interval (f : ℝ → ℂ) (hf : Function.Periodic f (2 * π)) :
    ∫ θ in (0 : ℝ)..(2 * π), f θ = ∫ θ in Ioo (-π) π, f θ := by
  have h := hf.intervalIntegral_add_eq 0 (-π)
  rw [zero_add, show -π + 2 * π = π by ring] at h
  rw [h, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]

def gradKernel (m : ℕ) (n : ℤ) (a b : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space) : ℂ :=
  Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * (frameMat θ M a b : ℂ)

def velKernel (m : ℕ) (n : ℤ) (a : Fin 3) (θ : ℝ) (u : Space) : ℂ :=
  Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * (frameVec θ u a : ℂ)

theorem gradKernel_cont (m : ℕ) (n : ℤ) (a b : Fin 3) :
    Continuous (fun q : ℝ × (Space →L[ℝ] Space) => gradKernel m n a b q.1 q.2) :=
  (phase_cont m n).mul (Complex.continuous_ofReal.comp (frameMat_cont a b))

theorem velKernel_cont (m : ℕ) (n : ℤ) (a : Fin 3) :
    Continuous (fun q : ℝ × Space => velKernel m n a q.1 q.2) :=
  (phase_cont m n).mul (Complex.continuous_ofReal.comp (frameVec_cont a))

theorem gradKernel_bound (m : ℕ) (n : ℤ) (a b : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space) :
    ‖gradKernel m n a b θ M‖ ≤ ‖M‖ := by
  rw [gradKernel, norm_mul, phase_norm, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact frameMat_bound θ M a b

theorem velKernel_bound (m : ℕ) (n : ℤ) (a : Fin 3) (θ : ℝ) (u : Space) :
    ‖velKernel m n a θ u‖ ≤ ‖u‖ := by
  rw [velKernel, norm_mul, phase_norm, one_mul, Complex.norm_real, Real.norm_eq_abs, frameVec_eq]
  exact inner_unit_bound θ u a

theorem gradMode_eq (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (a b : Fin 3) (p : ℝ × ℝ) :
    gradMode m n G a b p = (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, gradKernel m n a b θ (G (cylPoint p.1 θ p.2)) := by
  unfold gradMode modeMat
  rw [per_interval]
  · rfl
  · intro θ
    simp only [phase_per, cylPoint_per, frameMat_per]

theorem modeVec_eq (m : ℕ) (n : ℤ) (v : Space → Space) (a : Fin 3) (p : ℝ × ℝ) :
    modeVec m n v p.1 p.2 a = (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, velKernel m n a θ (v (cylPoint p.1 θ p.2)) := by
  unfold modeVec
  rw [per_interval]
  · rfl
  · intro θ
    simp only [phase_per, cylPoint_per, frameVec_per]

theorem gradMode_int (K : CellBox) (hK : IsCellBox K) (m : ℕ) (n : ℤ) {G : Space → (Space →L[ℝ] Space)}
    (hG1 : AEStronglyMeasurable G volume) (hG2 : Integrable (fun y => entrySq (G y))) (a b : Fin 3) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * gradMode m n G a b p) K.rect := by
  have h2 : MemLp G 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hG1).2 ((hG2.const_mul 3).mono'
      ((hG1.norm.aemeasurable.pow_const 2).aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact EmbedWeak.Internal.norm_sq_le (G y)
  have h := mode_int K hK (h2.locallyIntegrable (by norm_num)) (gradKernel m n a b) (gradKernel_cont m n a b)
    (gradKernel_bound m n a b)
  have e : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * gradMode m n G a b p) = fun p => (1 / (2 * π) : ℂ) *
      ((K.lineWeight p.1 : ℂ) * ∫ θ in Ioo (-π) π, gradKernel m n a b θ (G (cylPoint p.1 θ p.2))) := by
    funext p; rw [gradMode_eq]; ring
  rw [e]
  exact h.const_mul _

theorem modeVec_int (K : CellBox) (hK : IsCellBox K) (m : ℕ) (n : ℤ) {v : Space → Space}
    (hv : MemLp v 6 volume) (a : Fin 3) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a) K.rect := by
  have h := mode_int K hK (hv.locallyIntegrable (by norm_num)) (velKernel m n a) (velKernel_cont m n a)
    (velKernel_bound m n a)
  have e : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a) = fun p => (1 / (2 * π) : ℂ) *
      ((K.lineWeight p.1 : ℂ) * ∫ θ in Ioo (-π) π, velKernel m n a θ (v (cylPoint p.1 θ p.2))) := by
    funext p; rw [modeVec_eq]; ring
  rw [e]
  exact h.const_mul _

end ModePart

end Breakdown.CellCert.CellAnalysis.LowEntry.Internal

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis LowEntry.Internal

theorem lowEntry_holds : LowEntryStatement := by
  intro k N c K S B L hL x hx i d hd
  have hsec := hx.1
  by_cases hn : i.1 ∈ L.modes
  · by_cases hb : i.2.2.1.val < 3
    · by_cases h : i.2.2.2.1 < L.degCoef + 1 ∧ i.2.2.2.2 < L.degCoef + 1
      · rw [CellLayout.lowEntry, dif_pos hn, dif_pos hb, dif_pos h] at hd
        obtain rfl := Option.some.inj hd
        simp only [CellLayout.trueData, CellDatum.lowStrain, Sum.elim_inl, CellLayout.gradModeOf]
        rw [CellScalars.lowCoef, dif_pos hb, hL.box_eq, hL.bases_eq, hL.order_eq]
        simp only [CellBox.lowStrainAt, CellBox.lowStrain]
        have h1 := h.1
        have h2 := h.2
        rw [hL.degCoef_eq] at h1 h2
        exact (coef_proj K B hL.bases_valid
          (gradMode_int K hL.box_valid c.order i.1 hsec.measurable_gradient hsec.gradient_two _ _)
          (by omega) (by omega)).symm
      · rw [CellLayout.lowEntry, dif_pos hn, dif_pos hb, dif_neg h] at hd
        exact absurd hd (by simp)
    · by_cases h : i.2.2.2.1 < L.degCoef ∧ i.2.2.2.2 < L.degCoef
      · rw [CellLayout.lowEntry, dif_pos hn, dif_neg hb, dif_pos h] at hd
        obtain rfl := Option.some.inj hd
        simp only [CellLayout.trueData, CellDatum.lowVelocity, Sum.elim_inl, Sum.elim_inr]
        rw [CellScalars.lowCoef, dif_neg hb, hL.box_eq, hL.bases_eq]
        unfold CellLayout.velMode
        rw [hL.order_eq]
        simp only [CellBox.lowVelocityAt, CellBox.lowVelocity]
        have h1 := h.1
        have h2 := h.2
        rw [hL.degCoef_eq] at h1 h2
        exact (coef_proj K B hL.bases_valid
          (modeVec_int K hL.box_valid c.order i.1 hsec.velocity_six _)
          (by omega) (by omega)).symm
      · rw [CellLayout.lowEntry, dif_pos hn, dif_neg hb, dif_neg h] at hd
        exact absurd hd (by simp)
  · rw [CellLayout.lowEntry, dif_neg hn] at hd
    exact absurd hd (by simp)

end Breakdown.CellCert.CellFormula
