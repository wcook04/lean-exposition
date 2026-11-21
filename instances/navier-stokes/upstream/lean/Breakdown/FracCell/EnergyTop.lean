import Breakdown.FracCell.StEnergyProof
import Breakdown.FracCell.StAngularMode

open MeasureTheory Matrix Finset

noncomputable section

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis CellFormula

namespace TopFormInternal

variable (K : CellBox)

theorem rect_compact : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

theorem lw_cont : Continuous fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) := by
  unfold CellBox.lineWeight
  split_ifs
  · fun_prop
  · fun_prop

theorem good_of_cont {X : ℝ × ℝ → ℂ} (hX : Continuous X) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * X p) K.rect :=
  ((lw_cont K).mul hX).continuousOn.integrableOn_compact (rect_compact K)

theorem int_mul {X T : ℝ × ℝ → ℂ} (hX : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * X p) K.rect)
    (hT : Continuous T) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * X p * (starRingEnd ℂ) (T p)) K.rect :=
  hX.mul_continuousOn (Complex.continuous_conj.comp hT).continuousOn (rect_compact K)

theorem pair_def (X T : ℝ × ℝ → ℂ) : K.pairOn K.lineWeightFn X T =
    ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * X p * (starRingEnd ℂ) (T p) := rfl

theorem pair_sub_left {X Y T : ℝ × ℝ → ℂ} (hX : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * X p) K.rect)
    (hY : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * Y p) K.rect) (hT : Continuous T) :
    K.pairOn K.lineWeightFn (fun p => X p - Y p) T = K.pairOn K.lineWeightFn X T - K.pairOn K.lineWeightFn Y T := by
  rw [pair_def, pair_def, pair_def, ← integral_sub (int_mul K hX hT) (int_mul K hY hT)]
  congr 1
  funext p
  ring

theorem pair_sum_right {ι : Type} (s : Finset ι) {X : ℝ × ℝ → ℂ} {g : ι → ℝ × ℝ → ℂ}
    (hX : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * X p) K.rect) (hg : ∀ i ∈ s, Continuous (g i)) :
    K.pairOn K.lineWeightFn X (fun p => ∑ i ∈ s, g i p) = ∑ i ∈ s, K.pairOn K.lineWeightFn X (g i) := by
  simp only [pair_def, map_sum, Finset.mul_sum]
  exact integral_finsetSum s fun i hi => int_mul K hX (hg i hi)

theorem pair_smul_right (X g : ℝ × ℝ → ℂ) (c : ℂ) :
    K.pairOn K.lineWeightFn X (fun p => c * g p) = (starRingEnd ℂ) c * K.pairOn K.lineWeightFn X g := by
  simp only [pair_def, map_mul]
  rw [← integral_const_mul]
  congr 1
  funext p
  ring

theorem pair_sum_left {ι : Type} (s : Finset ι) {f : ι → ℝ × ℝ → ℂ} {T : ℝ × ℝ → ℂ}
    (hf : ∀ i ∈ s, Continuous (f i)) (hT : Continuous T) :
    K.pairOn K.lineWeightFn (fun p => ∑ i ∈ s, f i p) T = ∑ i ∈ s, K.pairOn K.lineWeightFn (f i) T := by
  simp only [pair_def, Finset.mul_sum, Finset.sum_mul]
  exact integral_finsetSum s fun i hi => int_mul K (good_of_cont K (hf i hi)) hT

theorem pair_smul_left (f T : ℝ × ℝ → ℂ) (c : ℂ) :
    K.pairOn K.lineWeightFn (fun p => c * f p) T = c * K.pairOn K.lineWeightFn f T := by
  simp only [pair_def]
  rw [← integral_const_mul]
  congr 1
  funext p
  ring

theorem pair_conj (X Y : ℝ × ℝ → ℂ) :
    (starRingEnd ℂ) (K.pairOn K.lineWeightFn X Y) = K.pairOn K.lineWeightFn Y X := by
  simp only [pair_def]
  rw [← integral_conj]
  congr 1
  funext p
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

theorem normSq_eq (X : ℝ × ℝ → ℂ) : K.normSqOn K.lineWeightFn X = (K.pairOn K.lineWeightFn X X).re := by
  rw [pair_def]
  have e : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * X p * (starRingEnd ℂ) (X p)
      = ((K.lineWeight p.1 * ‖X p‖ ^ 2 : ℝ) : ℂ) := by
    intro p
    rw [mul_assoc, Complex.mul_conj']
    push_cast
    ring
  simp_rw [e]
  rw [integral_complex_ofReal, Complex.ofReal_re]
  rfl

def basisC (B : CellBases) (j l : ℕ) (p : ℝ × ℝ) : ℂ := ((basisFn B j l p : ℝ) : ℂ)

theorem basisC_cont (B : CellBases) (j l : ℕ) : Continuous (basisC B j l) := by
  unfold basisC basisFn CellBases.radialPoly CellBases.heightPoly
  fun_prop

theorem pairingMat {B : CellBases} (hB : IsCellBases K B) (j l j' l' : ℕ) :
    K.pairOn K.lineWeightFn (basisC B j l) (basisC B j' l') = if j = j' ∧ l = l' then 1 else 0 := by
  rw [pair_def]
  have e : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * basisC B j l p * (starRingEnd ℂ) (basisC B j' l' p)
      = (((K.lineWeight p.1 * B.radialPoly j p.1 * B.radialPoly j' p.1)
          * (B.heightPoly l p.2 * B.heightPoly l' p.2) : ℝ) : ℂ) := by
    intro p
    simp only [basisC, basisFn, Complex.conj_ofReal]
    push_cast
    ring
  simp_rw [e]
  rw [integral_complex_ofReal, CellBox.rect, Measure.volume_eq_prod,
    setIntegral_prod_mul (fun r => K.lineWeight r * B.radialPoly j r * B.radialPoly j' r)
      (fun z => B.heightPoly l z * B.heightPoly l' z),
    hB.radial_orthonormal, hB.height_orthonormal]
  split_ifs <;> simp_all

theorem pair_comb_left (B : CellBases) (s : Finset ℕ) (w : ℕ → ℂ) (j : ℕ) {T : ℝ × ℝ → ℂ} (hT : Continuous T) :
    K.pairOn K.lineWeightFn (fun p => ∑ l ∈ s, w l * basisC B j l p) T
      = ∑ l ∈ s, w l * K.pairOn K.lineWeightFn (basisC B j l) T := by
  rw [pair_sum_left K s (f := fun l p => w l * basisC B j l p)
    (fun l _ => continuous_const.mul (basisC_cont B j l)) hT]
  exact Finset.sum_congr rfl fun l _ => pair_smul_left K _ _ _

theorem pair_comb_right (B : CellBases) (s : Finset ℕ) (w : ℕ → ℂ) (i : ℕ) {X : ℝ × ℝ → ℂ}
    (hX : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * X p) K.rect) :
    K.pairOn K.lineWeightFn X (fun p => ∑ k ∈ s, w k * basisC B i k p)
      = ∑ k ∈ s, (starRingEnd ℂ) (w k) * K.pairOn K.lineWeightFn X (basisC B i k) := by
  rw [pair_sum_right K s (g := fun k p => w k * basisC B i k p) hX
    (fun k _ => continuous_const.mul (basisC_cont B i k))]
  exact Finset.sum_congr rfl fun k _ => pair_smul_right K _ _ _

theorem pow_span (C : ℕ → ℕ → ℝ) (hC : ∀ j, 0 < C j j) (d : ℕ) :
    ∀ j ≤ d, ∃ a : ℕ → ℝ, ∀ r : ℝ, r ^ j = ∑ i ∈ range (d + 1), a i * ∑ t ∈ range (i + 1), C i t * r ^ t := by
  let P : Fin (d + 1) → ℝ → ℝ := fun i r => ∑ t ∈ range ((i : ℕ) + 1), C i t * r ^ t
  have key : ∀ j, j ≤ d → (fun r : ℝ => r ^ j) ∈ Submodule.span ℝ (Set.range P) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      have hPj : P ⟨j, by omega⟩ ∈ Submodule.span ℝ (Set.range P) := Submodule.subset_span ⟨_, rfl⟩
      have heq : (fun r : ℝ => r ^ j)
          = (C j j)⁻¹ • (P ⟨j, by omega⟩ - ∑ t ∈ range j, C j t • (fun r : ℝ => r ^ t)) := by
        funext r
        have hne := (hC j).ne'
        simp only [P, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul, Finset.sum_range_succ]
        field_simp
        ring
      rw [heq]
      refine Submodule.smul_mem _ _ (Submodule.sub_mem _ hPj (Submodule.sum_mem _ fun t ht =>
        Submodule.smul_mem _ _ (ih t (Finset.mem_range.1 ht) ?_)))
      have := Finset.mem_range.1 ht
      omega
  intro j hj
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (key j hj)
  refine ⟨fun i => if h : i < d + 1 then c ⟨i, h⟩ else 0, fun r => ?_⟩
  have h1 := congrFun hc r
  rw [← h1, Finset.sum_apply, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [P, i.isLt]

theorem mono_expand {B : CellBases} (hB : IsCellBases K B) {d d' j l : ℕ} (hj : j ≤ d) (hl : l ≤ d') :
    ∃ w : ℕ → ℕ → ℂ, ∀ p : ℝ × ℝ, (p.1 : ℂ) ^ j * (p.2 : ℂ) ^ l
      = ∑ i ∈ range (d + 1), ∑ k ∈ range (d' + 1), w i k * basisC B i k p := by
  obtain ⟨a, ha⟩ := pow_span B.radialCoef hB.radial_leading d j hj
  obtain ⟨b, hb⟩ := pow_span B.heightCoef hB.height_leading d' l hl
  refine ⟨fun i k => ((a i * b k : ℝ) : ℂ), fun p => ?_⟩
  have e : (p.1 : ℂ) ^ j * (p.2 : ℂ) ^ l = ((p.1 ^ j * p.2 ^ l : ℝ) : ℂ) := by push_cast; ring
  rw [e, ha p.1, hb p.2, Finset.sum_mul_sum]
  simp only [basisC, basisFn, CellBases.radialPoly, CellBases.heightPoly]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem poly_sum {d d' : ℕ} {ι : Type} (s : Finset ι) {f : ι → ℝ × ℝ → ℂ} (h : ∀ i ∈ s, f i ∈ polyFn d d') :
    (fun p => ∑ i ∈ s, f i p) ∈ polyFn d d' := by
  classical
  simp only [polyFn, Set.mem_ofPred_eq] at h ⊢
  choose! c hc using h
  refine ⟨fun j l => ∑ i ∈ s, c i j l, fun p => ?_⟩
  rw [Finset.sum_congr rfl fun i hi => hc i hi p]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

theorem poly_smul {d d' : ℕ} {f : ℝ × ℝ → ℂ} (c : ℂ) (h : f ∈ polyFn d d') :
    (fun p => c * f p) ∈ polyFn d d' := by
  obtain ⟨c0, hc0⟩ := h
  refine ⟨fun j l => c * c0 j l, fun p => ?_⟩
  beta_reduce
  simp only [hc0 p, Finset.mul_sum, mul_assoc]

theorem poly_mono {d d' i k : ℕ} (hi : i ≤ d) (hk : k ≤ d') :
    (fun p : ℝ × ℝ => (p.1 : ℂ) ^ i * (p.2 : ℂ) ^ k) ∈ polyFn d d' := by
  refine ⟨fun j l => if j = ⟨i, by omega⟩ ∧ l = ⟨k, by omega⟩ then 1 else 0, fun p => ?_⟩
  simp [ite_and, ite_mul, Finset.sum_ite_eq']

theorem poly_basis (B : CellBases) {d d' j l : ℕ} (hj : j ≤ d) (hl : l ≤ d') : basisC B j l ∈ polyFn d d' := by
  have e : basisC B j l = fun p => ∑ t ∈ range (j + 1), ∑ s ∈ range (l + 1),
      ((B.radialCoef j t * B.heightCoef l s : ℝ) : ℂ) * ((p.1 : ℂ) ^ t * (p.2 : ℂ) ^ s) := by
    funext p
    simp only [basisC, basisFn, CellBases.radialPoly, CellBases.heightPoly]
    rw [Finset.sum_mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  rw [e]
  refine poly_sum _ fun t ht => poly_sum _ fun s hs => poly_smul _ (poly_mono ?_ ?_)
  · have := Finset.mem_range.1 ht; omega
  · have := Finset.mem_range.1 hs; omega

theorem poly_cont {d d' : ℕ} {P : ℝ × ℝ → ℂ} (h : P ∈ polyFn d d') : Continuous P := by
  obtain ⟨c, hc⟩ := h
  rw [show P = fun p => ∑ j, ∑ l, c j l * ((p.1 : ℂ) ^ (j : ℕ)) * ((p.2 : ℂ) ^ (l : ℕ)) from funext hc]
  fun_prop

theorem coef_eq (B : CellBases) (F : ℝ × ℝ → ℂ) (j l : ℕ) :
    K.pairOn K.lineWeightFn F (basisC B j l) = B.coef K F j l := by
  rw [pair_def]
  simp only [basisC, basisFn, Complex.conj_ofReal]
  rfl

theorem normSq_proj {B : CellBases} (hB : IsCellBases K B) {F : ℝ × ℝ → ℂ}
    (hF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect) (d d' : ℕ) :
    K.normSqOn K.lineWeightFn (K.proj d d' F)
      = ∑ j ∈ range (d + 1), ∑ l ∈ range (d' + 1), ‖B.coef K F j l‖ ^ 2 := by
  obtain ⟨P₀, hP₀def⟩ : ∃ P₀ : ℝ × ℝ → ℂ,
      P₀ = fun p => ∑ j ∈ range (d + 1), ∑ l ∈ range (d' + 1), B.coef K F j l * basisC B j l p := ⟨_, rfl⟩
  have hrow : ∀ j, Continuous fun p => ∑ l ∈ range (d' + 1), B.coef K F j l * basisC B j l p :=
    fun j => continuous_finsetSum _ fun l _ => continuous_const.mul (basisC_cont B j l)
  have hP₀c : Continuous P₀ := by
    rw [hP₀def]
    exact continuous_finsetSum _ fun j _ => hrow j
  have hP₀poly : P₀ ∈ polyFn d d' := by
    rw [hP₀def]
    refine poly_sum _ fun j hj => poly_sum _ fun l hl => poly_smul _ (poly_basis B ?_ ?_)
    · have := Finset.mem_range.1 hj; omega
    · have := Finset.mem_range.1 hl; omega
  have hP₀b : ∀ j l, j ≤ d → l ≤ d' → K.pairOn K.lineWeightFn P₀ (basisC B j l) = B.coef K F j l := by
    intro j l hj hl
    rw [hP₀def, pair_sum_left K _ (fun j _ => hrow j) (basisC_cont B j l)]
    simp_rw [pair_comb_left K B _ _ _ (basisC_cont B j l), pairingMat K hB]
    rw [Finset.sum_eq_single j, Finset.sum_eq_single l]
    · simp
    · intro l' _ hl'
      simp [hl']
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
    · intro j' _ hj'
      exact Finset.sum_eq_zero fun l' _ => by simp [hj']
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  have hX : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * (F p - P₀ p)) K.rect := by
    have := hF.sub (good_of_cont K hP₀c)
    refine this.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
    simp only [Pi.sub_apply]
    ring
  have horthb : ∀ j l, j ≤ d → l ≤ d' →
      K.pairOn K.lineWeightFn (fun p => F p - P₀ p) (basisC B j l) = 0 := by
    intro j l hj hl
    rw [pair_sub_left K hF (good_of_cont K hP₀c) (basisC_cont B j l), coef_eq, hP₀b j l hj hl, sub_self]
  have horthm : ∀ j l, j ≤ d → l ≤ d' →
      K.pairOn K.lineWeightFn (fun p => F p - P₀ p) (fun p => (p.1 : ℂ) ^ j * (p.2 : ℂ) ^ l) = 0 := by
    intro j l hj hl
    obtain ⟨w, hw⟩ := mono_expand K hB hj hl
    rw [show (fun p : ℝ × ℝ => (p.1 : ℂ) ^ j * (p.2 : ℂ) ^ l) = fun p =>
        ∑ i ∈ range (d + 1), ∑ k ∈ range (d' + 1), w i k * basisC B i k p from funext hw]
    rw [pair_sum_right K (g := fun i p => ∑ k ∈ range (d' + 1), w i k * basisC B i k p) _ hX
      (fun i _ => continuous_finsetSum _ fun k _ => continuous_const.mul (basisC_cont B i k))]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [pair_comb_right K B _ _ _ hX]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [horthb i k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)), mul_zero]
  have hP₀orth : ∀ T ∈ polyFn d d', K.pairOn K.lineWeightFn (fun p => F p - P₀ p) T = 0 := by
    intro T hT
    obtain ⟨c, hc⟩ := hT
    have hT' : T = fun p => ∑ j, ∑ l, c j l * ((p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ)) :=
      funext fun p => by rw [hc p]; simp only [mul_assoc]
    rw [hT', pair_sum_right K (g := fun j p => ∑ l, c j l * ((p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ))) _ hX
      (fun j _ => by fun_prop)]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [pair_sum_right K (g := fun l p => c j l * ((p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ))) _ hX
      (fun l _ => by fun_prop)]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [pair_smul_right, horthm j l (Nat.lt_succ_iff.1 j.isLt) (Nat.lt_succ_iff.1 l.isLt), mul_zero]
  have hex : ∃ P ∈ polyFn d d', ∀ T ∈ polyFn d d', K.pairOn K.lineWeightFn (fun p => F p - P p) T = 0 :=
    ⟨P₀, hP₀poly, hP₀orth⟩
  have hproj : K.proj d d' F = hex.choose := by rw [CellBox.proj, dif_pos hex]
  obtain ⟨hPpoly, hPorth⟩ := hex.choose_spec
  have hPc := poly_cont hPpoly
  have e1 : ∀ T ∈ polyFn d d', K.pairOn K.lineWeightFn hex.choose T = K.pairOn K.lineWeightFn P₀ T := by
    intro T hT
    have a := hPorth T hT
    have b := hP₀orth T hT
    rw [pair_sub_left K hF (good_of_cont K hPc) (poly_cont hT)] at a
    rw [pair_sub_left K hF (good_of_cont K hP₀c) (poly_cont hT)] at b
    linear_combination b - a
  have hnP : K.normSqOn K.lineWeightFn hex.choose = K.normSqOn K.lineWeightFn P₀ := by
    rw [normSq_eq, normSq_eq, e1 _ hPpoly, ← pair_conj K hex.choose P₀, e1 _ hP₀poly, Complex.conj_re]
  have hFP : K.pairOn K.lineWeightFn P₀ P₀ = K.pairOn K.lineWeightFn F P₀ := by
    have b := hP₀orth P₀ hP₀poly
    rw [pair_sub_left K hF (good_of_cont K hP₀c) hP₀c] at b
    linear_combination -b
  rw [hproj, hnP, normSq_eq, hFP]
  conv_lhs => rw [hP₀def]
  rw [pair_sum_right K _ hF (fun j _ => hrow j)]
  simp_rw [pair_comb_right K B _ _ _ hF, coef_eq, Complex.conj_mul']
  simp only [Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re]

theorem qfv_add {D : Type} [Fintype D] (A B : Matrix D D ℂ) (u : D → ℂ) :
    quadFormValue (A + B) u = quadFormValue A u + quadFormValue B u := by
  unfold quadFormValue
  rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]

theorem qfv_sum {D : Type} [Fintype D] {ι : Type} (s : Finset ι) (M : ι → Matrix D D ℂ) (u : D → ℂ) :
    quadFormValue (∑ i ∈ s, M i) u = ∑ i ∈ s, quadFormValue (M i) u := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [quadFormValue]
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, qfv_add, ih]

theorem quad_diag {D : Type} [Fintype D] [DecidableEq D] {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι → D) (W : Matrix ι ι ℂ) (w : ι → ℝ) (hW : ∀ i i', W i i' = if i = i' then (w i : ℂ) else 0)
    (u : D → ℂ) :
    quadFormValue (formOfRows (fun i d => if d = s i then (1 : ℂ) else 0) W) u = ∑ i, w i * ‖u (s i)‖ ^ 2 := by
  have inner : ∀ d, ∑ d', formOfRows (fun i d => if d = s i then (1 : ℂ) else 0) W d d' * u d'
      = ∑ i, (if d = s i then (1 : ℂ) else 0) * ((w i : ℂ) * u (s i)) := by
    intro d
    simp only [formOfRows, hW, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    simp [mul_ite, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq]
  have h2 : ∑ d, (starRingEnd ℂ) (u d) * ∑ i, (if d = s i then (1 : ℂ) else 0) * ((w i : ℂ) * u (s i))
      = ∑ i, ((w i * ‖u (s i)‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [mul_left_comm, Complex.conj_mul']
    push_cast
    ring
  unfold quadFormValue
  simp only [dotProduct, mulVec, Pi.star_apply, Complex.star_def, inner]
  rw [h2, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => Complex.ofReal_re _

theorem rows_eq {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q)
    (n : modes) (a b : Fin 3) :
    (fun jl : Fin (Q + 1) × Fin (Q + 1) => lowRow I n (unitArray a b) jl.1 jl.2)
      = fun jl d => if d = I.strainSlot n a b jl.1 jl.2 then (1 : ℂ) else 0 := by
  funext jl d
  simp only [lowRow, unitArray]
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro b' _ hb'
    simp [hb']
  · simp
  · intro a' _ ha'
    simp [ha']
  · simp

theorem prod_to_range (n n' : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ jl : Fin n × Fin n', F jl.1 jl.2 = ∑ j ∈ range n, ∑ l ∈ range n', F j l := by
  rw [Fintype.sum_prod_type, Finset.sum_range (fun j => ∑ l ∈ range n', F j l)]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (Finset.sum_range (F j)).symm

theorem ind_sum (M N : ℕ) (h : M ≤ N) (X : ℕ → ℝ) :
    ∑ j ∈ range N, (if M ≤ j then (1 : ℝ) else 0) * X j = ∑ j ∈ range N, X j - ∑ j ∈ range M, X j := by
  induction N with
  | zero =>
    have : M = 0 := by omega
    subst this
    simp
  | succ N ih =>
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · subst h'
      rw [sub_self]
      exact Finset.sum_eq_zero fun j hj => by
        rw [if_neg (by have := Finset.mem_range.1 hj; omega), zero_mul]
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, ih (by omega), if_pos (by omega)]
      ring

theorem low_sum (M N : ℕ) (h : M ≤ N) (Y : ℕ → ℝ) :
    ∑ j ∈ range N, (if j < M then (1 : ℝ) else 0) * Y j = ∑ j ∈ range M, Y j := by
  have e : ∀ j, (if j < M then (1 : ℝ) else 0) * Y j = Y j - (if M ≤ j then (1 : ℝ) else 0) * Y j := by
    intro j
    by_cases h1 : j < M
    · rw [if_pos h1, if_neg (by omega)]; ring
    · rw [if_neg h1, if_pos (by omega)]; ring
  simp_rw [e]
  rw [Finset.sum_sub_distrib, ind_sum M N h]
  ring

theorem top_arith (Q : ℕ) (hQ : 2 ≤ Q) (f g : ℕ → ℕ → ℝ) :
    (∑ jl : Fin (Q + 1) × Fin (Q + 1), (if Q - 1 ≤ (jl.1 : ℕ) then (1 : ℝ) else 0) * f jl.1 jl.2)
      + (∑ jl : Fin (Q + 1) × Fin (Q + 1),
          (if (jl.1 : ℕ) ≤ Q - 1 ∧ Q - 1 ≤ (jl.2 : ℕ) then (1 : ℝ) else 0) * g jl.1 jl.2)
    = (∑ j ∈ range (Q + 1), ∑ l ∈ range (Q + 1), f j l - ∑ j ∈ range (Q - 2 + 1), ∑ l ∈ range (Q + 1), f j l)
      + (∑ j ∈ range (Q - 1 + 1), ∑ l ∈ range (Q + 1), g j l
          - ∑ j ∈ range (Q - 1 + 1), ∑ l ∈ range (Q - 2 + 1), g j l) := by
  have e1 : Q - 2 + 1 = Q - 1 := by omega
  have e2 : Q - 1 + 1 = Q := by omega
  rw [e1, e2, prod_to_range (Q + 1) (Q + 1) (fun j l => (if Q - 1 ≤ j then (1 : ℝ) else 0) * f j l),
    prod_to_range (Q + 1) (Q + 1) (fun j l => (if j ≤ Q - 1 ∧ Q - 1 ≤ l then (1 : ℝ) else 0) * g j l)]
  have e3 : ∀ j l, (if j ≤ Q - 1 ∧ Q - 1 ≤ l then (1 : ℝ) else 0) * g j l
      = (if j < Q then (1 : ℝ) else 0) * ((if Q - 1 ≤ l then (1 : ℝ) else 0) * g j l) := by
    intro j l
    by_cases h1 : j < Q <;> by_cases h2 : Q - 1 ≤ l
    · rw [if_pos ⟨by omega, h2⟩, if_pos h1, if_pos h2]; ring
    · rw [if_neg (fun h => h2 h.2), if_pos h1, if_neg h2]; ring
    · rw [if_neg (fun h => h1 (by omega)), if_neg h1]; ring
    · rw [if_neg (fun h => h1 (by omega)), if_neg h1]; ring
  simp_rw [e3]
  simp_rw [← Finset.mul_sum]
  simp_rw [ind_sum (Q - 1) (Q + 1) (by omega)]
  rw [low_sum Q (Q + 1) (by omega), Finset.sum_sub_distrib]

end TopFormInternal

open TopFormInternal

theorem topForm_holds (hmode : ModeIntegrableStatement) : TopFormStatement := by
  intro α D _ _ k N c K B S modes Q q I v G H u hE n
  have hQ : 2 ≤ Q := by
    have := hE.scalars.degrees
    rw [hE.degHigh_eq]
    omega
  have hint : ∀ a b, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * gradMode c.order n G a b p) K.rect :=
    fun a b => (hmode c.order v G H hE.field K hE.box n a).2 b
  unfold topForm
  rw [qfv_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [qfv_add, rows_eq I n a 0, rows_eq I n a 2,
    quad_diag (fun jl : Fin (Q + 1) × Fin (Q + 1) => I.strainSlot n a 0 jl.1 jl.2)
      (fun jl jl' => if jl = jl' ∧ Q - 1 ≤ (jl.1 : ℕ) then (1 : ℂ) else 0)
      (fun jl => if Q - 1 ≤ (jl.1 : ℕ) then 1 else 0) (by
      intro i i'
      by_cases h : i = i'
      · subst h
        by_cases h' : Q - 1 ≤ (i.1 : ℕ) <;> simp [h']
      · simp [h]),
    quad_diag (fun jl : Fin (Q + 1) × Fin (Q + 1) => I.strainSlot n a 2 jl.1 jl.2)
      (fun jl jl' => if jl = jl' ∧ (jl.1 : ℕ) ≤ Q - 1 ∧ Q - 1 ≤ (jl.2 : ℕ) then (1 : ℂ) else 0)
      (fun jl => if (jl.1 : ℕ) ≤ Q - 1 ∧ Q - 1 ≤ (jl.2 : ℕ) then 1 else 0) (by
      intro i i'
      by_cases h : i = i'
      · subst h
        by_cases h' : (i.1 : ℕ) ≤ Q - 1 ∧ Q - 1 ≤ (i.2 : ℕ)
        · rw [if_pos ⟨rfl, h'⟩, if_pos rfl, if_pos h', Complex.ofReal_one]
        · rw [if_neg (fun hh => h' hh.2), if_pos rfl, if_neg h', Complex.ofReal_zero]
      · simp [h])]
  simp only [hE.represents.strain]
  rw [CellBox.topPart, normSq_proj K hE.bases (hint a 0) Q Q, normSq_proj K hE.bases (hint a 0) (Q - 2) Q,
    normSq_proj K hE.bases (hint a 2) (Q - 1) Q, normSq_proj K hE.bases (hint a 2) (Q - 1) (Q - 2)]
  exact top_arith Q hQ (fun j l => ‖B.coef K (gradMode c.order n G a 0) j l‖ ^ 2)
    (fun j l => ‖B.coef K (gradMode c.order n G a 2) j l‖ ^ 2)

end Breakdown.CellCert.CellEnergy
