module

public import QuarticQuery.Forrelation.Arithmetic
public import QuarticQuery.Forrelation.Promise

/-!
# The exact circuit of Lemma 2.1(iii)

`wht` is the butterfly recursion, `layers` the right-to-left walk: `k - 1` transforms
with sign changes. `forrCore` adds the final sum and the three signs `2^(5k) N - M`,
`M - 2^(5k+1) N`, `M + 2^(5k+1) N`, each read from the top wire of a residue. The width
is `5k + 3 + t (k + 1)`, enough for the only magnitude bound used, `|N| ≤ M`, which is
unitarity. Size is `O_k (m (log m)²)`.
-/

@[expose] public section

namespace QuarticQuery.Forrelation

open Finset

variable {ι : Type}

/-- Ledger: claim-butterfly. The unnormalised transform of `f 0, …, f (2^n - 1)`. -/
def wht : ℕ → (ℕ → List (Wire ι)) → Prog ι → (ℕ → List (Wire ι)) × Prog ι
  | 0, f, p => (f, p)
  | n + 1, f, p =>
    let L := wht n f p
    let R := wht n (fun j => f (2 ^ n + j)) L.2
    let S := forN (fun i => addV (L.1 i) (R.1 i)) (2 ^ n) R.2
    let D := forN (fun i => subV (L.1 i) (R.1 i)) (2 ^ n) S.2
    (fun i => if i < 2 ^ n then S.1 i else D.1 (i - 2 ^ n), D.2)

/-- Gates of `wht` at width `w`. -/
def whtCost (w : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => whtCost w n + whtCost w n + 2 ^ n * (6 * w) + 2 ^ n * (6 * w + 1)

/-- Ledger: claim-butterfly. `wht` computes the Walsh transform of its inputs. -/
theorem wht_spec (w n : ℕ) (f : ℕ → List (Wire ι)) (F : ℕ → BitInput ι → ℤ) (p : Prog ι)
    (hf : ∀ j < 2 ^ n, Enc w p (f j) (F j)) :
    ∃ g p', wht n f p = (g, p') ∧ Ext p p' (whtCost w n) ∧
      ∀ i < 2 ^ n, Enc w p' (g i) fun x => ∑ j ∈ range (2 ^ n), walshN n i j * F j x := by
  induction n generalizing f F p with
  | zero => exact ⟨f, p, rfl, Ext.refl p, fun i hi => (hf i hi).congr fun x => by
      obtain rfl : i = 0 := by simpa using hi
      simp [walshN_zero]⟩
  | succ n ih =>
    have hp : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
    obtain ⟨L, p1, e1, x1, h1⟩ := ih f F p fun j hj => hf j (by omega)
    obtain ⟨R, p2, e2, x2, h2⟩ := ih (fun j => f (2 ^ n + j)) (fun j => F (2 ^ n + j)) p1
      fun j hj => (hf _ (by omega)).mono x1
    obtain ⟨S, p3, e3, x3, h3⟩ := forN_spec (w := w) (c := 6 * w)
      (fun i => addV (L i) (R i)) (2 ^ n) p2
      (fun i x => (∑ j ∈ range (2 ^ n), walshN n i j * F j x) +
        ∑ j ∈ range (2 ^ n), walshN n i j * F (2 ^ n + j) x)
      fun i hi q d hq => addV_spec (((h1 i hi).mono x2).mono hq) ((h2 i hi).mono hq)
    obtain ⟨D, p4, e4, x4, h4⟩ := forN_spec (w := w) (c := 6 * w + 1)
      (fun i => subV (L i) (R i)) (2 ^ n) p3
      (fun i x => (∑ j ∈ range (2 ^ n), walshN n i j * F j x) -
        ∑ j ∈ range (2 ^ n), walshN n i j * F (2 ^ n + j) x)
      fun i hi q d hq => subV_spec (((h1 i hi).mono (x2.trans x3)).mono hq)
        (((h2 i hi).mono x3).mono hq)
    refine ⟨fun i => if i < 2 ^ n then S i else D (i - 2 ^ n), p4,
      by simp only [wht, e1, e2, e3, e4], ?_, fun i hi => ?_⟩
    · exact ((x1.trans x2).trans x3).trans x4
    · by_cases hin : i < 2 ^ n
      · simp only [hin, ↓reduceIte]
        refine ((h3 i hin).mono x4).congr fun x => ?_
        rw [sum_walshN_succ, Nat.testBit_lt_two_pow hin]
        simp [bitSign]
      · simp only [hin, ↓reduceIte]
        obtain ⟨i0, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hin)
        rw [Nat.add_sub_cancel_left]
        have hi0 : i0 < 2 ^ n := by omega
        refine (h4 i0 hi0).congr fun x => ?_
        rw [sum_walshN_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hi0]
        have hc (j : ℕ) : walshN n (2 ^ n + i0) j = walshN n i0 j :=
          walshN_congr_left (fun b hb => testBit_two_pow_add_low hb) j
        simp only [hc, bitSign, Bool.not_false, ↓reduceIte]
        ring

theorem whtCost_le (w n : ℕ) : whtCost w n ≤ n * 2 ^ n * (6 * w + 1) := by
  induction n with
  | zero => simp [whtCost]
  | succ n ih =>
    simp only [whtCost, pow_succ]
    generalize 2 ^ n = P at *
    nlinarith

/-- Ledger: claim-N-phi. The walk at width `w + 1`, with input-sign wires `Z`. -/
def layers (n w : ℕ) : ℕ → (ℕ → ℕ → Wire ι) → Prog ι → (ℕ → List (Wire ι)) × Prog ι
  | 0, Z, p =>
    let t := trueGate p
    forN (fun i => signMul (Z 0 i) (w + 1) (oneV w t.1)) (2 ^ n) t.2
  | l + 1, Z, p =>
    let v := layers n w l (fun h => Z (h + 1)) p
    let h := wht n v.1 v.2
    forN (fun i => signMul (Z 0 i) (w + 1) (h.1 i)) (2 ^ n) h.2

/-- Gates of `layers`, with `W` the full width. -/
def layerCost (n W : ℕ) : ℕ → ℕ
  | 0 => 1 + 2 ^ n * (6 * W)
  | l + 1 => layerCost n W l + whtCost W n + 2 ^ n * (6 * W)

theorem layerCost_le (n W l : ℕ) :
    layerCost n W l ≤ 1 + (l + 1) * (whtCost W n + 2 ^ n * (6 * W)) := by
  induction l with
  | zero => simp only [layerCost]; omega
  | succ l ih =>
    simp only [layerCost]
    nlinarith

theorem layers_spec (n w l : ℕ) (Z : ℕ → ℕ → Wire ι) (σ : BitInput ι → ℕ → ℕ → ℤ)
    (hv : ∀ h i (q : Prog ι), (Z h i).Valid q.length)
    (hσ : ∀ x (q : Prog ι) h i, bitSign (val x q (Z h i)) = σ x h i) (p : Prog ι) :
    ∃ g p', layers n w l Z p = (g, p') ∧ Ext p p' (layerCost n (w + 1) l) ∧
      ∀ i < 2 ^ n, Enc (w + 1) p' (g i) fun x => walkN n l (σ x) i := by
  induction l generalizing Z σ p with
  | zero =>
    obtain ⟨t, p1, e1, x1, r1⟩ := trueGate_spec p
    obtain ⟨g, p2, e2, x2, h2⟩ := forN_spec (w := w + 1) (c := 6 * (w + 1))
      (fun i => signMul (Z 0 i) (w + 1) (oneV w t)) (2 ^ n) p1
      (fun i x => walkN n 0 (σ x) i)
      fun i hi q d hq => by
        obtain ⟨out, q', e, x, h⟩ := signMul_spec (hv 0 i q) (enc_oneV (w := w) (r1.mono hq))
        exact ⟨out, q', e, x, h.congr fun y => by simp [hσ, walkN]⟩
    exact ⟨g, p2, by simp only [layers, e1, e2], x1.trans x2, h2⟩
  | succ l ih =>
    obtain ⟨v, p1, e1, x1, h1⟩ := ih (fun h => Z (h + 1)) (fun x h => σ x (h + 1))
      (fun h i q => hv _ i q) (fun x q h i => hσ x q _ i) p
    obtain ⟨h, p2, e2, x2, h2⟩ := wht_spec (w + 1) n v _ p1 h1
    obtain ⟨g, p3, e3, x3, h3⟩ := forN_spec (w := w + 1) (c := 6 * (w + 1))
      (fun i => signMul (Z 0 i) (w + 1) (h i)) (2 ^ n) p2
      (fun i x => walkN n (l + 1) (σ x) i)
      fun i hi q d hq => by
        obtain ⟨out, q', e, x, r⟩ := signMul_spec (hv 0 i q) ((h2 i hi).mono hq)
        exact ⟨out, q', e, x, r.congr fun y => by simp only [hσ, walkN]⟩
    exact ⟨g, p3, by simp only [layers, e1, e2, e3], (x1.trans x2).trans x3, h3⟩

theorem AllValid.getD {p : Prog ι} {v : List (Wire ι)} (h : AllValid p v) (i : ℕ) :
    (v.getD i none).Valid p.length := by
  by_cases hi : i < v.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    trivial

theorem sign_rep {w : ℕ} {p : Prog ι} {v : List (Wire ι)} {T : BitInput ι → ℤ}
    (h : Enc (w + 1) p v T) (hb : ∀ x, -2 ^ w ≤ T x ∧ T x < 2 ^ w) :
    Rep p (v.getD w none) fun x => decide (T x < 0) :=
  ⟨h.2.1.getD w, fun x => sign_wire h x (hb x).1 (hb x).2⟩

/-! ## The whole circuit -/

/-- The input wire of `z_h(i)`. Out of range reads constant false, sign `+1`. -/
def inputZ (l t h i : ℕ) : Wire (ForrelationCoord (l + 1) t) :=
  if hh : h < l + 1 ∧ i < mValue t then some (.inl (⟨h, hh.1⟩, ⟨i, hh.2⟩)) else none

theorem inputZ_valid (l t h i n : ℕ) : (inputZ l t h i).Valid n := by
  unfold inputZ
  split <;> trivial

theorem bitSign_val_inputZ (l t : ℕ) (x : BitInput (ForrelationCoord (l + 1) t))
    (q : Prog (ForrelationCoord (l + 1) t)) (h i : ℕ) :
    bitSign (val x q (inputZ l t h i)) = layerSign x h i := by
  unfold inputZ layerSign
  split <;> rfl

/-- The top wire index; the width is one more. -/
def widthTop (l t : ℕ) : ℕ := 5 * (l + 1) + 2 + t * (l + 2)

/-- Everything before the three output gates. -/
def forrCore (l t : ℕ) :
    Prog (ForrelationCoord (l + 1) t) × Wire (ForrelationCoord (l + 1) t) ×
      Wire (ForrelationCoord (l + 1) t) × Wire (ForrelationCoord (l + 1) t) :=
  let w := widthTop l t
  let r1 := layers (2 * t) w l (inputZ l t) []
  let r2 := sumV (w + 1) r1.1 (2 ^ (2 * t)) r1.2
  let r3 := dblN (5 * (l + 1)) r2.1 r2.2
  let r4 := addV r3.1 r3.1 r3.2
  let t5 := trueGate r4.2
  let r6 := dblN (t * (l + 2)) (oneV w t5.1) t5.2
  let r7 := subV r3.1 r6.1 r6.2
  let r8 := subV r6.1 r4.1 r7.2
  let r9 := addV r6.1 r4.1 r8.2
  (r9.2, r7.1.getD w none, r8.1.getD w none, r9.1.getD w none)

/-- Gates of `forrCore`. -/
def coreSize (l t : ℕ) : ℕ :=
  let W := widthTop l t + 1
  layerCost (2 * t) W l + 2 ^ (2 * t) * (6 * W) + 5 * (l + 1) * (6 * W) + 6 * W + 1 +
    t * (l + 2) * (6 * W) + (6 * W + 1) + (6 * W + 1) + 6 * W

theorem denominator_eq (l t : ℕ) :
    forrelationDenominator (l + 1) t = 2 ^ (t * (l + 2)) := by
  unfold forrelationDenominator
  rw [Nat.add_sub_cancel, ← pow_mul, ← pow_add]
  congr 1
  ring

/-- Ledger: claim-circuit-size. `|N| ≤ M`, the only magnitude bound the circuit uses. -/
theorem abs_numerator_le (l t : ℕ) (x : BitInput (ForrelationCoord (l + 1) t)) :
    |forrelationNumerator (l + 1) t x| ≤ forrelationDenominator (l + 1) t := by
  have hM : (0 : ℝ) < forrelationDenominator (l + 1) t := by
    exact_mod_cast forrelationDenominator_pos (l + 1) t
  have h := abs_Phi_le_one (l + 1) t (by omega) x
  rw [Phi, abs_div, abs_of_pos hM, div_le_one hM] at h
  exact_mod_cast h

/-- Bounds for the three tested values at width `5k + 3 + t (k + 1)`. -/
theorem test_bounds (s e : ℕ) (N M : ℤ) (hM : M = 2 ^ e) (hN : |N| ≤ M) :
    (-2 ^ (s + 2 + e) ≤ 2 ^ s * N - M ∧ 2 ^ s * N - M < 2 ^ (s + 2 + e)) ∧
    (-2 ^ (s + 2 + e) ≤ M - 2 * (2 ^ s * N) ∧ M - 2 * (2 ^ s * N) < 2 ^ (s + 2 + e)) ∧
    (-2 ^ (s + 2 + e) ≤ M + 2 * (2 ^ s * N) ∧ M + 2 * (2 ^ s * N) < 2 ^ (s + 2 + e)) := by
  have ha : (1 : ℤ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
  have hMp : (0 : ℤ) < M := by rw [hM]; positivity
  have hbig : (2 : ℤ) ^ (s + 2 + e) = 4 * (2 ^ s * M) := by
    rw [hM]
    ring
  have hup : 2 ^ s * N ≤ 2 ^ s * M :=
    mul_le_mul_of_nonneg_left (le_trans (le_abs_self N) hN) (by positivity)
  have hlo : 2 ^ s * (-M) ≤ 2 ^ s * N :=
    mul_le_mul_of_nonneg_left (by linarith [neg_abs_le N]) (by positivity)
  have hM1 : M ≤ 2 ^ s * M := by nlinarith
  rw [hbig]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith

theorem decide_tests (c1 c2 c3 : Prop) [Decidable c1] [Decidable c2] [Decidable c3] :
    (((!decide c1 || (!decide c2 && !decide c3)) = true) ↔
      ∃ b, (if ¬ c1 then some true else if ¬ c2 ∧ ¬ c3 then some false else none) = some b) ∧
    ((!decide c1 || (!decide c2 && !decide c3)) = true →
      (if ¬ c1 then some true else if ¬ c2 ∧ ¬ c3 then some false else none) =
        some (!decide c1)) := by
  by_cases h1 : c1 <;> by_cases h2 : c2 <;> by_cases h3 : c3 <;> simp [h1, h2, h3]

/-- Ledger: claim-integer-tests. `P` in terms of the three signs. -/
theorem P_tests (l t : ℕ) (x : BitInput (ForrelationCoord (l + 1) t)) :
    P (l + 1) t x =
      if ¬ ((2 : ℤ) ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x -
        forrelationDenominator (l + 1) t < 0) then some true
      else if ¬ ((forrelationDenominator (l + 1) t : ℤ) -
          2 * (2 ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x) < 0) ∧
        ¬ ((forrelationDenominator (l + 1) t : ℤ) +
          2 * (2 ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x) < 0) then some false
      else none := by
  have h1 : (2 : ℤ) ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x ≥
      forrelationDenominator (l + 1) t ↔
      ¬ ((2 : ℤ) ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x -
        forrelationDenominator (l + 1) t < 0) := by
    constructor <;> intro h <;> omega
  have h2 : (2 : ℤ) ^ (5 * (l + 1) + 1) * |forrelationNumerator (l + 1) t x| ≤
      forrelationDenominator (l + 1) t ↔
      ¬ ((forrelationDenominator (l + 1) t : ℤ) -
          2 * (2 ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x) < 0) ∧
        ¬ ((forrelationDenominator (l + 1) t : ℤ) +
          2 * (2 ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x) < 0) := by
    have e : (2 : ℤ) ^ (5 * (l + 1) + 1) * |forrelationNumerator (l + 1) t x| =
        |2 * (2 ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x)| := by
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ (5 * (l + 1))),
        abs_of_pos (by norm_num : (0 : ℤ) < 2), pow_succ]
      ring
    rw [e, abs_le]
    constructor
    · rintro ⟨u, v⟩
      constructor <;> omega
    · rintro ⟨u, v⟩
      constructor <;> omega
  simp only [P]
  rw [if_congr h1 rfl (if_congr h2 rfl rfl)]

/-- Ledger: claim-integer-tests. The core computes the three signs. -/
theorem forrCore_spec (l t : ℕ) :
    ∃ q a b c, forrCore l t = (q, a, b, c) ∧ q.length = coreSize l t ∧
      Rep q a (fun x => decide ((2 : ℤ) ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x -
        forrelationDenominator (l + 1) t < 0)) ∧
      Rep q b (fun x => decide ((forrelationDenominator (l + 1) t : ℤ) -
        2 * (2 ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x) < 0)) ∧
      Rep q c (fun x => decide ((forrelationDenominator (l + 1) t : ℤ) +
        2 * (2 ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x) < 0)) := by
  set w := widthTop l t with hw
  obtain ⟨g, p1, e1, x1, h1⟩ := layers_spec (2 * t) w l (inputZ l t) (fun x => layerSign x)
    (fun h i q => inputZ_valid l t h i _) (fun x q h i => bitSign_val_inputZ l t x q h i) []
  obtain ⟨o2, p2, e2, x2, h2⟩ := sumV_spec g (2 ^ (2 * t)) p1 _ h1
  have hN : Enc (w + 1) p2 o2 fun x => forrelationNumerator (l + 1) t x :=
    h2.congr fun x => (numerator_eq_walk l t x).symm
  obtain ⟨o3, p3, e3, x3, h3⟩ := dblN_spec (5 * (l + 1)) hN
  obtain ⟨o4, p4, e4, x4, h4⟩ := addV_spec h3 h3
  obtain ⟨tt, p5, e5, x5, r5⟩ := trueGate_spec p4
  obtain ⟨o6, p6, e6, x6, h6⟩ := dblN_spec (t * (l + 2)) (enc_oneV (w := w) r5)
  have hM : ∀ x : BitInput (ForrelationCoord (l + 1) t),
      (2 : ℤ) ^ (t * (l + 2)) * 1 = forrelationDenominator (l + 1) t := fun _ => by
    rw [denominator_eq, mul_one]
  have h6' := h6.congr hM
  have x46 := x5.trans x6
  have h3' := (h3.mono x4).mono x46
  have h4' := h4.mono x46
  obtain ⟨o7, p7, e7, x7, h7⟩ := subV_spec h3' h6'
  obtain ⟨o8, p8, e8, x8, h8⟩ := subV_spec (h6'.mono x7) (h4'.mono x7)
  obtain ⟨o9, p9, e9, x9, h9⟩ := addV_spec ((h6'.mono x7).mono x8) ((h4'.mono x7).mono x8)
  have hbd (x : BitInput (ForrelationCoord (l + 1) t)) := test_bounds (5 * (l + 1)) (t * (l + 2))
    (forrelationNumerator (l + 1) t x) (forrelationDenominator (l + 1) t)
    (denominator_eq l t) (abs_numerator_le l t x)
  have htop : w = 5 * (l + 1) + 2 + t * (l + 2) := rfl
  refine ⟨p9, o7.getD w none, o8.getD w none, o9.getD w none,
    by simp only [forrCore, ← hw, e1, e2, e3, e4, e5, e6, e7, e8, e9], ?_,
    sign_rep (h7.mono (x8.trans x9)) fun x => ?_,
    sign_rep ((h8.congr fun y => ?_).mono x9) fun x => ?_,
    sign_rep (h9.congr fun y => ?_) fun x => ?_⟩
  · have := (((((((x1.trans x2).trans x3).trans x4).trans x46).trans x7).trans x8).trans x9).length_eq
    rw [this]
    simp only [coreSize, ← hw, List.length_nil, zero_add]
    omega
  · rw [htop]
    exact (hbd x).1
  · ring
  · rw [htop]
    exact (hbd x).2.1
  · ring
  · rw [htop]
    exact (hbd x).2.2

/-- The three output gates: `b = ¬ s₁`, then `d = b ∨ (¬ s₂ ∧ ¬ s₃)`. -/
def finish {ι : Type} (c : Prog ι × Wire ι × Wire ι × Wire ι) : Prog ι :=
  let g1 := gate c.2.1 none (fun a _ => !a) c.1
  let g2 := gate c.2.2.1 c.2.2.2 (fun a b => !a && !b) g1.2
  (gate g1.1 g2.1 or g2.2).2

/-- The gate list of the exact circuit, for `k = l + 1`. -/
def forrProg (l t : ℕ) : Prog (ForrelationCoord (l + 1) t) := finish (forrCore l t)

theorem forrProg_length (l t : ℕ) : (forrProg l t).length = coreSize l t + 3 := by
  obtain ⟨q, a, b, c, e, hq, -⟩ := forrCore_spec l t
  simp [forrProg, finish, e, gate, hq]

/-- Ledger: lem-2.1.iii. The exact circuit, for `k = l + 1`. -/
def forrCircuit (l t : ℕ) : Circuit (ForrelationCoord (l + 1) t) :=
  (forrProg l t).toCircuit ⟨coreSize l t + 2, by rw [forrProg_length]; omega⟩
    ⟨coreSize l t, by rw [forrProg_length]; omega⟩

/-- Ledger: lem-2.1.iii. The circuit computes `d` and `b` exactly on every input:
`d = 1` iff `P` is defined, and then `b` is its value. -/
theorem forrCircuit_realises (l t : ℕ) : CircuitRealises (forrCircuit l t) (P (l + 1) t) := by
  obtain ⟨q, a, b, c, e, hq, ra, rb, rc⟩ := forrCore_spec l t
  obtain ⟨w1, p1, e1, x1, r1⟩ := gate_spec ra (rep_none q) (fun a _ => !a)
  obtain ⟨w2, p2, e2, x2, r2⟩ := gate_spec (rb.mono x1) (rc.mono x1) (fun a b => !a && !b)
  obtain ⟨w3, p3, e3, x3, r3⟩ := gate_spec (r1.mono x2) r2 or
  have hp : forrProg l t = p3 := by
    simp only [forrProg, finish, e, e1, e2, e3]
  have hw1 : w1 = some (.inr (coreSize l t)) := by
    rw [← hq]
    exact (Prod.mk.inj e1).1.symm
  have hp1 : p1.length = coreSize l t + 1 := by rw [x1.length_eq, hq]
  have hp2 : p2.length = coreSize l t + 2 := by rw [x2.length_eq, hp1]
  have hw3 : w3 = some (.inr (coreSize l t + 2)) := by
    rw [← hp2]
    exact (Prod.mk.inj e3).1.symm
  have vd (x) : (run x (forrProg l t)).getD (coreSize l t + 2) false =
      ((!decide ((2 : ℤ) ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x -
        forrelationDenominator (l + 1) t < 0)) ||
       ((!decide ((forrelationDenominator (l + 1) t : ℤ) -
        2 * (2 ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x) < 0)) &&
        (!decide ((forrelationDenominator (l + 1) t : ℤ) +
        2 * (2 ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x) < 0)))) := by
    rw [hp]
    have := r3.2 x
    rw [hw3] at this
    exact this
  have vb (x) : (run x (forrProg l t)).getD (coreSize l t) false =
      (!decide ((2 : ℤ) ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x -
        forrelationDenominator (l + 1) t < 0)) := by
    rw [hp]
    have := ((r1.mono x2).mono x3).2 x
    rw [hw1] at this
    exact this
  have hP (x : BitInput (ForrelationCoord (l + 1) t)) := P_tests l t x
  refine realises_of_run (forrProg l t) _ _ _ (fun x => ?_) (fun x => ?_)
  · change (run x (forrProg l t)).getD (coreSize l t + 2) false = true ↔ _
    rw [vd, promised, hP]
    exact (decide_tests _ _ _).1
  · change (run x (forrProg l t)).getD (coreSize l t + 2) false = true →
      _ = some ((run x (forrProg l t)).getD (coreSize l t) false)
    rw [vd, vb, hP]
    exact (decide_tests _ _ _).2

/-! ## Size -/

/-- Ledger: lem-2.1.iii. The constant `c_k`. -/
def forrConstant (k : ℕ) : ℕ := 200 * (k + 1) ^ 2

theorem coreSize_le (l t : ℕ) (ht : 1 ≤ t) :
    coreSize l t + 3 ≤ forrConstant (l + 1) * mValue t * (2 * t) ^ 2 := by
  set a := l + 2 with ha
  set W := widthTop l t + 1 with hWdef
  set m := 2 ^ (2 * t) with hm
  have hm1 : 1 ≤ m := Nat.one_le_two_pow
  set X := m * t ^ 2 with hX
  have ht2 : t ≤ t ^ 2 := by nlinarith
  have hX1 : 1 ≤ X := by nlinarith
  set Z := a * X with hZ
  set Y := a * Z with hY
  have hXZ : X ≤ Z := by nlinarith
  have hZY : 2 * Z ≤ Y := by
    rw [hY]
    exact Nat.mul_le_mul_right Z (by omega)
  have hat : a ≤ a * t := by nlinarith
  have hW : W ≤ 6 * (a * t) := by
    have : t * (l + 2) = a * t := by rw [ha]; ring
    simp only [hWdef, widthTop, this]
    omega
  have hW1 : 1 ≤ W := by omega
  have hQ : t * m * W ≤ 6 * Z := by
    calc t * m * W ≤ t * m * (6 * (a * t)) := Nat.mul_le_mul_left _ hW
      _ = 6 * Z := by rw [hZ, hX]; ring
  have hR : m * W ≤ 6 * Z := by
    calc m * W ≤ m * (6 * (a * t)) := Nat.mul_le_mul_left _ hW
      _ ≤ m * (6 * (a * t ^ 2)) := by gcongr
      _ = 6 * Z := by rw [hZ, hX]; ring
  have hWm : W ≤ m * W := Nat.le_mul_of_pos_left _ hm1
  have htW : t * W ≤ t * m * W := by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ hWm
  have hwc : whtCost W (2 * t) ≤ 84 * Z := by
    have h := whtCost_le W (2 * t)
    rw [← hm] at h
    have : 2 * t * m * (6 * W + 1) ≤ 14 * (t * m * W) := by
      have : 6 * W + 1 ≤ 7 * W := by omega
      calc 2 * t * m * (6 * W + 1) ≤ 2 * t * m * (7 * W) := Nat.mul_le_mul_left _ this
        _ = 14 * (t * m * W) := by ring
    omega
  have hlay : layerCost (2 * t) W l ≤ 1 + 120 * Y := by
    refine (layerCost_le _ _ _).trans ?_
    rw [← hm]
    have hin : whtCost W (2 * t) + m * (6 * W) ≤ 120 * Z := by
      have : m * (6 * W) = 6 * (m * W) := by ring
      omega
    have : (l + 1) * (whtCost W (2 * t) + m * (6 * W)) ≤ a * (120 * Z) :=
      Nat.mul_le_mul (by omega) hin
    have e : a * (120 * Z) = 120 * Y := by rw [hY]; ring
    omega
  have h5 : 5 * (l + 1) * (6 * W) ≤ 180 * Y := by
    have hle : W ≤ 6 * Z := hWm.trans hR
    calc 5 * (l + 1) * (6 * W) ≤ 5 * a * (6 * (6 * Z)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.mul_le_mul_left _ hle)
      _ = 180 * Y := by rw [hY]; ring
  have h6 : t * (l + 2) * (6 * W) ≤ 36 * Y := by
    calc t * (l + 2) * (6 * W) = 6 * a * (t * W) := by rw [ha]; ring
      _ ≤ 6 * a * (6 * Z) := Nat.mul_le_mul_left _ (htW.trans hQ)
      _ = 36 * Y := by rw [hY]; ring
  have htarget : forrConstant (l + 1) * mValue t * (2 * t) ^ 2 = 800 * Y := by
    have : mValue t = m := rfl
    rw [this, forrConstant, hY, hZ, hX, show l + 1 + 1 = a from rfl]
    ring
  rw [htarget]
  have hc : coreSize l t = layerCost (2 * t) W l + m * (6 * W) + 5 * (l + 1) * (6 * W) +
      6 * W + 1 + t * (l + 2) * (6 * W) + (6 * W + 1) + (6 * W + 1) + 6 * W := rfl
  rw [hc]
  have hmW : m * (6 * W) = 6 * (m * W) := by ring
  have hle : W ≤ 6 * Z := hWm.trans hR
  omega

theorem forrCircuit_size_eq (l t : ℕ) : (forrCircuit l t).size = coreSize l t + 3 :=
  forrProg_length l t

/-- Ledger: lem-2.1.iii. `S ≤ c_k m (log₂ m)²`, with `log₂ m = 2 t`. -/
theorem forrCircuit_size_le (l t : ℕ) (ht : 1 ≤ t) :
    (forrCircuit l t).size ≤ forrConstant (l + 1) * mValue t * (2 * t) ^ 2 := by
  rw [forrCircuit_size_eq]
  exact coreSize_le l t ht

theorem logb_mValue (t : ℕ) : Real.logb 2 (mValue t : ℝ) = 2 * t := by
  have : (mValue t : ℝ) = (2 : ℝ) ^ (2 * t) := by simp [mValue]
  rw [this, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  push_cast
  ring

/-- Ledger: lem-2.1.iii. Lemma 2.1(iii) for every `k ≥ 1` and `m = 4 ^ t ≥ 4`. The
circuit exists for `t = 0` too, but then `log m = 0`. -/
theorem exists_circuit (k t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    ∃ C : Circuit (ForrelationCoord k t), CircuitRealises C (P k t) ∧
      (C.size : ℝ) ≤ (forrConstant k : ℝ) * (mValue t : ℝ) *
        Real.logb 2 (mValue t : ℝ) ^ 2 := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
  refine ⟨forrCircuit l t, forrCircuit_realises l t, ?_⟩
  rw [logb_mValue]
  exact_mod_cast forrCircuit_size_le l t ht

end QuarticQuery.Forrelation
