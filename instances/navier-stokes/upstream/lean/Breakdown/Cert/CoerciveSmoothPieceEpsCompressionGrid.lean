import Breakdown.Cert.CoerciveSmoothPieceEpsCompressionSymbolDefs

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceEpsCompression

open Internal.SmoothPieceEpsCore

private theorem exp_ne_one_of_lt {k : ℤ} {N : ℕ} (hN : 0 < N) (hk : k ≠ 0) (hkN : |k| < N) :
    Complex.exp (2 * Real.pi * Complex.I * k / N) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have e1 : (k : ℂ) = n * N := by
    field_simp at hn
    linear_combination hn
  have e2 : k = n * N := by exact_mod_cast e1
  have hn0 : n ≠ 0 := by rintro rfl; simp at e2; exact hk e2
  have : (N : ℤ) ≤ |k| := by
    rw [e2, abs_mul]
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    have hN0 : (0 : ℤ) ≤ |(N : ℤ)| := abs_nonneg _
    rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ N)]
    nlinarith
  linarith

theorem geom_phase_sum (k : ℤ) (N : ℕ) (hN : 0 < N) (hkN : |k| < N) :
    ∑ a ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * a / N) = if k = 0 then (N : ℂ) else 0 := by
  split_ifs with hk
  · subst hk
    simp
  · have hζ := exp_ne_one_of_lt hN hk hkN
    have e : ∀ a : ℕ, Complex.exp (2 * Real.pi * Complex.I * k * a / N)
        = Complex.exp (2 * Real.pi * Complex.I * k / N) ^ a := by
      intro a
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
    simp only [e]
    rw [geom_sum_eq hζ, ← Complex.exp_nat_mul]
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have : (N : ℂ) * (2 * Real.pi * Complex.I * k / N) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
      field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I, sub_self, zero_div]

def gridPhase (N : ℕ) (k : ℤ × ℤ) (ab : ℕ × ℕ) : ℂ :=
  torusPhase k ((ab.1 : ℝ) / N) (2 * Real.pi * (ab.2 : ℝ) / N)

theorem gridPhase_eq (N : ℕ) (k : ℤ × ℤ) (ab : ℕ × ℕ) :
    gridPhase N k ab = Complex.exp (2 * Real.pi * Complex.I * k.1 * ab.1 / N)
      * Complex.exp (2 * Real.pi * Complex.I * k.2 * ab.2 / N) := by
  unfold gridPhase torusPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem gridPhase_add (N : ℕ) (k k' : ℤ × ℤ) (ab : ℕ × ℕ) :
    gridPhase N (k + k') ab = gridPhase N k ab * gridPhase N k' ab := by
  unfold gridPhase torusPhase
  rw [← Complex.exp_add]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
  push_cast
  ring

theorem gridPhase_conj (N : ℕ) (k : ℤ × ℤ) (ab : ℕ × ℕ) :
    (starRingEnd ℂ) (gridPhase N k ab) = gridPhase N (-k) ab := by
  unfold gridPhase torusPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  push_cast
  ring

theorem gridPhase_sum (N : ℕ) (hN : 0 < N) (k : ℤ × ℤ) (h1 : |k.1| < N) (h2 : |k.2| < N) :
    ∑ ab ∈ Finset.range N ×ˢ Finset.range N, gridPhase N k ab = if k = 0 then ((N : ℂ) * N) else 0 := by
  rw [Finset.sum_product]
  simp only [gridPhase_eq, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [geom_phase_sum k.2 N hN h2]
  simp only [Finset.sum_mul]
  rw [← Finset.sum_mul, geom_phase_sum k.1 N hN h1]
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg hk]
    by_cases hk1 : k.1 = 0
    · have hk2 : k.2 ≠ 0 := fun h => hk (Prod.ext hk1 h)
      simp [hk1, hk2]
    · simp [hk1]

def dotq {q : Type} [Fintype q] (x z : q → ℂ) : ℂ := ∑ j, x j * (starRingEnd ℂ) (z j)

theorem dotq_self {q : Type} [Fintype q] (x : q → ℂ) : dotq x x = ((cnormSq x : ℝ) : ℂ) := by
  unfold dotq cnormSq
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem norm_dotq_le {q : Type} [Fintype q] (x z : q → ℂ) :
    ‖dotq x z‖ ≤ Real.sqrt (cnormSq x) * Real.sqrt (cnormSq z) := by
  unfold dotq cnormSq
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ j ∈ (Finset.univ : Finset q), ‖x j * (starRingEnd ℂ) (z j)‖ = ‖x j‖ * ‖z j‖ :=
    fun j _ => by rw [norm_mul, Complex.norm_conj]
  rw [Finset.sum_congr rfl h]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

def combG {σ q : Type} [Fintype q] (N : ℕ) (s : Finset σ) (p : σ → ℤ × ℤ) (v : σ → q → ℂ) (ab : ℕ × ℕ) :
    q → ℂ :=
  fun j => ∑ t ∈ s, gridPhase N (p t) ab * v t j

theorem dot_combG {σ σ' q : Type} [Fintype q] (N : ℕ) (s : Finset σ) (s' : Finset σ') (p : σ → ℤ × ℤ)
    (p' : σ' → ℤ × ℤ) (v : σ → q → ℂ) (v' : σ' → q → ℂ) (ab : ℕ × ℕ) :
    dotq (combG N s p v ab) (combG N s' p' v' ab)
      = ∑ t ∈ s, ∑ t' ∈ s', gridPhase N (p t - p' t') ab * dotq (v t) (v' t') := by
  unfold dotq combG
  simp only [map_sum, map_mul, gridPhase_conj, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t' _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sub_eq_add_neg, gridPhase_add]
  ring

theorem grid_dot {σ σ' q : Type} [Fintype q] [DecidableEq (ℤ × ℤ)] (N : ℕ) (hN : 0 < N) (s : Finset σ)
    (s' : Finset σ') (p : σ → ℤ × ℤ) (p' : σ' → ℤ × ℤ) (v : σ → q → ℂ) (v' : σ' → q → ℂ)
    (hsmall : ∀ t ∈ s, ∀ t' ∈ s', |(p t - p' t').1| < N ∧ |(p t - p' t').2| < N) :
    ∑ ab ∈ Finset.range N ×ˢ Finset.range N, dotq (combG N s p v ab) (combG N s' p' v' ab)
      = (N : ℂ) * N * ∑ t ∈ s, ∑ t' ∈ s', if p t = p' t' then dotq (v t) (v' t') else 0 := by
  simp only [dot_combG]
  conv_lhs => rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  conv_lhs => rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t' ht' => ?_
  rw [← Finset.sum_mul, gridPhase_sum N hN _ (hsmall t ht t' ht').1 (hsmall t ht t' ht').2]
  by_cases he : p t = p' t'
  · rw [if_pos (sub_eq_zero.mpr he), if_pos he]
  · rw [if_neg (fun h => he (sub_eq_zero.mp h)), if_neg he]
    ring

theorem symbol_apply_comb {q : Type} [Fintype q] (N : ℕ) (H : Finset (ℤ × ℤ)) (A : ℤ × ℤ → Fin 3 → q → ℂ)
    (K : Finset (ℤ × ℤ)) (g : ℤ × ℤ → q → ℂ) (ab : ℕ × ℕ) :
    applyMat (symbolMat H A ((ab.1 : ℝ) / N) (2 * Real.pi * (ab.2 : ℝ) / N)) (combG N K id g ab)
      = combG N (H ×ˢ K) (fun t => t.1 + t.2) (fun t => applyMat (A t.1) (g t.2)) ab := by
  funext i
  unfold applyMat symbolMat combG
  rw [Finset.sum_product]
  simp only [gridPhase_add, Finset.mul_sum, Finset.sum_mul, id]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun κ _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold gridPhase
  ring

theorem grid_norm {p : Type} [Fintype p] (N : ℕ) (hN : 0 < N) (F : Finset (ℤ × ℤ)) (x : ℤ × ℤ → p → ℂ)
    (hsmall : ∀ ι ∈ F, ∀ ι' ∈ F, |(ι - ι').1| < N ∧ |(ι - ι').2| < N) :
    ∑ ab ∈ Finset.range N ×ˢ Finset.range N, cnormSq (combG N F id x ab)
      = (N : ℝ) * N * ∑ ι ∈ F, cnormSq (x ι) := by
  classical
  have h := grid_dot N hN F F id id x x hsmall
  simp only [id, Finset.sum_ite_eq, dotq_self] at h
  have h2 : ((∑ ab ∈ Finset.range N ×ˢ Finset.range N, cnormSq (combG N F id x ab) : ℝ) : ℂ)
      = (((N : ℝ) * N * ∑ ι ∈ F, cnormSq (x ι) : ℝ) : ℂ) := by
    have h' : (∑ i ∈ F, if i ∈ F then ((cnormSq (x i) : ℝ) : ℂ) else 0) = ∑ i ∈ F, ((cnormSq (x i) : ℝ) : ℂ) :=
      Finset.sum_congr rfl fun i hi => if_pos hi
    push_cast
    rw [h, h']
  exact_mod_cast h2

private theorem abs_lt_of3 {a b c B N : ℤ} (ha : |a| ≤ B) (hb : |b| ≤ B) (hc : |c| ≤ B) (hN : 3 * B < N) :
    |a - (b + c)| < N := by
  rw [abs_le] at ha hb hc
  rw [abs_lt]
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]

private theorem abs_lt_of2 {a b B N : ℤ} (ha : |a| ≤ B) (hb : |b| ≤ B) (hN : 3 * B < N) : |a - b| < N := by
  rw [abs_le] at ha hb
  rw [abs_lt]
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

theorem grid_size (F H K : Finset (ℤ × ℤ)) : ∃ N : ℕ, 0 < N ∧
    (∀ ι ∈ F, ∀ t ∈ H ×ˢ K, |(ι - (t.1 + t.2)).1| < N ∧ |(ι - (t.1 + t.2)).2| < N) ∧
    (∀ ι ∈ F, ∀ ι' ∈ F, |(ι - ι').1| < N ∧ |(ι - ι').2| < N) ∧
    (∀ ι ∈ K, ∀ ι' ∈ K, |(ι - ι').1| < N ∧ |(ι - ι').2| < N) := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : ℤ, ∀ ι ∈ F ∪ H ∪ K, |ι.1| ≤ B ∧ |ι.2| ≤ B := by
    refine ⟨∑ ι ∈ F ∪ H ∪ K, (|ι.1| + |ι.2|), fun ι hι => ?_⟩
    have h := Finset.single_le_sum (f := fun ι : ℤ × ℤ => |ι.1| + |ι.2|)
      (fun i _ => add_nonneg (abs_nonneg i.1) (abs_nonneg i.2)) hι
    exact ⟨by linarith [abs_nonneg ι.2], by linarith [abs_nonneg ι.1]⟩
  have hN : 3 * B < ((((3 * B).toNat + 1 : ℕ)) : ℤ) := by
    push_cast
    linarith [Int.self_le_toNat (3 * B)]
  have mF : ∀ ι ∈ F, ι ∈ F ∪ H ∪ K := fun ι h => Finset.mem_union_left _ (Finset.mem_union_left _ h)
  have mH : ∀ ι ∈ H, ι ∈ F ∪ H ∪ K := fun ι h => Finset.mem_union_left _ (Finset.mem_union_right _ h)
  have mK : ∀ ι ∈ K, ι ∈ F ∪ H ∪ K := fun ι h => Finset.mem_union_right _ h
  refine ⟨(3 * B).toNat + 1, Nat.succ_pos _, ?_, ?_, ?_⟩
  · intro ι hι t ht
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp ht
    obtain ⟨a1, a2⟩ := hB ι (mF ι hι)
    obtain ⟨b1, b2⟩ := hB t.1 (mH _ h1)
    obtain ⟨c1, c2⟩ := hB t.2 (mK _ h2)
    exact ⟨abs_lt_of3 a1 b1 c1 hN, abs_lt_of3 a2 b2 c2 hN⟩
  · intro ι hι ι' hι'
    obtain ⟨a1, a2⟩ := hB ι (mF ι hι)
    obtain ⟨b1, b2⟩ := hB ι' (mF ι' hι')
    exact ⟨abs_lt_of2 a1 b1 hN, abs_lt_of2 a2 b2 hN⟩
  · intro ι hι ι' hι'
    obtain ⟨a1, a2⟩ := hB ι (mK ι hι)
    obtain ⟨b1, b2⟩ := hB ι' (mK ι' hι')
    exact ⟨abs_lt_of2 a1 b1 hN, abs_lt_of2 a2 b2 hN⟩

theorem finite_symbol_pairing_bound {q : Type} [Fintype q] (H : Finset (ℤ × ℤ)) (A : ℤ × ℤ → Fin 3 → q → ℂ) (S : ℝ)
    (hS0 : 0 ≤ S) (hsym : ∀ τ φ u, cnormSq (applyMat (symbolMat H A τ φ) u) ≤ S ^ 2 * cnormSq u)
    (F K : Finset (ℤ × ℤ)) (x : ℤ × ℤ → Fin 3 → ℂ) (g : ℤ × ℤ → q → ℂ) :
    ‖∑ ι ∈ F, ∑ t ∈ H ×ˢ K, if ι = t.1 + t.2 then dotq (x ι) (applyMat (A t.1) (g t.2)) else 0‖
      ≤ S * Real.sqrt (∑ ι ∈ F, cnormSq (x ι)) * Real.sqrt (∑ κ ∈ K, cnormSq (g κ)) := by
  classical
  obtain ⟨N, hN, sm1, smF, smK⟩ := grid_size F H K
  set R := Finset.range N ×ˢ Finset.range N
  set X : ℕ × ℕ → Fin 3 → ℂ := fun ab => combG N F id x ab
  set G : ℕ × ℕ → q → ℂ := fun ab => combG N K id g ab
  set M : ℕ × ℕ → Fin 3 → q → ℂ := fun ab => symbolMat H A ((ab.1 : ℝ) / N) (2 * Real.pi * (ab.2 : ℝ) / N)
  have I1 : ∑ ab ∈ R, dotq (X ab) (applyMat (M ab) (G ab))
      = (N : ℂ) * N * ∑ ι ∈ F, ∑ t ∈ H ×ˢ K,
          if ι = t.1 + t.2 then dotq (x ι) (applyMat (A t.1) (g t.2)) else 0 := by
    simp only [X, G, M, symbol_apply_comb]
    exact grid_dot N hN F (H ×ˢ K) id (fun t => t.1 + t.2) x (fun t => applyMat (A t.1) (g t.2)) sm1
  have Ix := grid_norm N hN F x smF
  have Ig := grid_norm N hN K g smK
  have I2 : ‖∑ ab ∈ R, dotq (X ab) (applyMat (M ab) (G ab))‖
      ≤ S * (Real.sqrt (∑ ab ∈ R, cnormSq (X ab)) * Real.sqrt (∑ ab ∈ R, cnormSq (G ab))) := by
    refine (norm_sum_le _ _).trans ?_
    have hpt : ∀ ab ∈ R, ‖dotq (X ab) (applyMat (M ab) (G ab))‖
        ≤ S * (Real.sqrt (cnormSq (X ab)) * Real.sqrt (cnormSq (G ab))) := by
      intro ab _
      refine (norm_dotq_le _ _).trans ?_
      have hm : Real.sqrt (cnormSq (applyMat (M ab) (G ab))) ≤ S * Real.sqrt (cnormSq (G ab)) := by
        rw [← Real.sqrt_sq hS0, ← Real.sqrt_mul (sq_nonneg S)]
        exact Real.sqrt_le_sqrt (hsym _ _ _)
      nlinarith [Real.sqrt_nonneg (cnormSq (X ab)), Real.sqrt_nonneg (cnormSq (G ab)),
        mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg (cnormSq (X ab)))]
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hS0
    have cs := Real.sum_mul_le_sqrt_mul_sqrt R (fun ab => Real.sqrt (cnormSq (X ab)))
      (fun ab => Real.sqrt (cnormSq (G ab)))
    simp only [Real.sq_sqrt (Internal.FieldModes.cnormSq_nonneg _)] at cs
    exact cs
  rw [I1, Ix, Ig, norm_mul] at I2
  have hNN : (0 : ℝ) < N * N := by positivity
  have hnorm : ‖(N : ℂ) * N‖ = (N : ℝ) * N := by
    rw [norm_mul, Complex.norm_natCast]
  rw [hnorm, Real.sqrt_mul hNN.le, Real.sqrt_mul hNN.le] at I2
  have hs : Real.sqrt ((N : ℝ) * N) = N := Real.sqrt_mul_self (Nat.cast_nonneg N)
  rw [hs] at I2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have key : (N : ℝ) * N * ‖∑ ι ∈ F, ∑ t ∈ H ×ˢ K,
      if ι = t.1 + t.2 then dotq (x ι) (applyMat (A t.1) (g t.2)) else 0‖
      ≤ (N : ℝ) * N * (S * Real.sqrt (∑ ι ∈ F, cnormSq (x ι)) * Real.sqrt (∑ κ ∈ K, cnormSq (g κ))) := by
    calc _ ≤ S * (N * Real.sqrt (∑ ι ∈ F, cnormSq (x ι)) * (N * Real.sqrt (∑ κ ∈ K, cnormSq (g κ)))) := I2
      _ = _ := by ring
  exact le_of_mul_le_mul_left key hNN

end Internal.SmoothPieceEpsCompression

end Coercive

end Breakdown
