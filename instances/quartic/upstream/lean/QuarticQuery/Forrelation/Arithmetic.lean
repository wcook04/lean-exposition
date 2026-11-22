module

public import QuarticQuery.Forrelation.Builder
public import QuarticQuery.Forrelation.Walsh

/-!
# Fixed-width arithmetic on wires

Integers are held as residues modulo `2 ^ w`, so additions and subtractions need no
range argument: `Enc w p v F` says the wires `v` hold `F x` modulo `2 ^ w`. Only the
final comparisons use a magnitude bound. One combinator does everything: `addsub s a b`
computes `a + (-1)^s b` with `6 w` gates.
-/

@[expose] public section

namespace QuarticQuery.Forrelation

open Finset

variable {ι : Type}

/-- The little-endian value of a bit list. -/
def bv : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * bv l

theorem bv_lt (l : List Bool) : bv l < 2 ^ l.length := by
  induction l with
  | nil => simp [bv]
  | cons b l ih =>
    have : b.toNat ≤ 1 := Bool.toNat_le b
    simp only [bv, List.length_cons, pow_succ]
    omega

theorem testBit_bv (l : List Bool) (i : ℕ) : (bv l).testBit i = l.getD i false := by
  induction l generalizing i with
  | nil => simp [bv]
  | cons b l ih =>
    rcases i with _ | i
    · cases b <;> simp [bv]
    · have e : (bv (b :: l)) / 2 = bv l := by
        have : b.toNat ≤ 1 := Bool.toNat_le b
        simp only [bv]
        omega
      rw [Nat.testBit_succ, e, ih]
      simp

/-- The values of a list of wires. -/
def vals (x : BitInput ι) (p : Prog ι) (v : List (Wire ι)) : List Bool := v.map (val x p)

def AllValid (p : Prog ι) (v : List (Wire ι)) : Prop := ∀ w ∈ v, Wire.Valid p.length w

theorem AllValid.mono {p p' : Prog ι} {c : ℕ} {v : List (Wire ι)} (h : AllValid p v)
    (e : Ext p p' c) : AllValid p' v := fun w hw => e.valid (h w hw)

theorem Ext.vals_eq {p p' : Prog ι} {c : ℕ} {v : List (Wire ι)} (e : Ext p p' c)
    (h : AllValid p v) (x : BitInput ι) : vals x p' v = vals x p v :=
  List.map_congr_left fun w hw => e.val_eq (h w hw) x

/-- One full adder. -/
def fullAdd (a b c : Wire ι) (p : Prog ι) : (Wire ι × Wire ι) × Prog ι :=
  let r1 := gate a b xor p
  let r2 := gate r1.1 c xor r1.2
  let r3 := gate a b and r2.2
  let r4 := gate r1.1 c and r3.2
  let r5 := gate r3.1 r4.1 or r4.2
  ((r2.1, r5.1), r5.2)

theorem fullAdd_spec {p : Prog ι} {a b c : Wire ι} (ha : a.Valid p.length)
    (hb : b.Valid p.length) (hc : c.Valid p.length) :
    ∃ s co p', fullAdd a b c p = ((s, co), p') ∧ Ext p p' 5 ∧
      s.Valid p'.length ∧ co.Valid p'.length ∧ ∀ x,
        (val x p' s).toNat + 2 * (val x p' co).toNat =
          (val x p a).toNat + (val x p b).toNat + (val x p c).toNat := by
  have ra : Rep p a fun x => val x p a := ⟨ha, fun _ => rfl⟩
  have rb : Rep p b fun x => val x p b := ⟨hb, fun _ => rfl⟩
  have rc : Rep p c fun x => val x p c := ⟨hc, fun _ => rfl⟩
  obtain ⟨w1, p1, e1, x1, r1⟩ := gate_spec ra rb xor
  obtain ⟨w2, p2, e2, x2, r2⟩ := gate_spec r1 (rc.mono x1) xor
  obtain ⟨w3, p3, e3, x3, r3⟩ := gate_spec ((ra.mono x1).mono x2) ((rb.mono x1).mono x2) and
  obtain ⟨w4, p4, e4, x4, r4⟩ := gate_spec ((r1.mono x2).mono x3)
    (((rc.mono x1).mono x2).mono x3) and
  obtain ⟨w5, p5, e5, x5, r5⟩ := gate_spec (r3.mono x4) r4 or
  have rs := ((r2.mono x3).mono x4).mono x5
  refine ⟨w2, w5, p5, by simp only [fullAdd, e1, e2, e3, e4, e5],
    (((x1.trans x2).trans x3).trans x4).trans x5, rs.1, r5.1, fun x => ?_⟩
  rw [rs.2 x, r5.2 x]
  dsimp only
  generalize val x p a = A
  generalize val x p b = B
  generalize val x p c = C
  cases A <;> cases B <;> cases C <;> rfl

/-- The ripple-carry adder with carry-in `c`. -/
def ripple : Wire ι → List (Wire ι) → List (Wire ι) → Prog ι →
    (List (Wire ι) × Wire ι) × Prog ι
  | c, a :: as, b :: bs, p =>
    let r := fullAdd a b c p
    let s := ripple r.1.2 as bs r.2
    ((r.1.1 :: s.1.1, s.1.2), s.2)
  | c, _, _, p => (([], c), p)

theorem ripple_spec (as bs : List (Wire ι)) (hl : as.length = bs.length) (c : Wire ι)
    (p : Prog ι) (ha : AllValid p as) (hb : AllValid p bs) (hc : c.Valid p.length) :
    ∃ out co p', ripple c as bs p = ((out, co), p') ∧ Ext p p' (5 * as.length) ∧
      out.length = as.length ∧ AllValid p' out ∧ ∀ x,
        bv (vals x p' out) + 2 ^ as.length * (val x p' co).toNat =
          bv (vals x p as) + bv (vals x p bs) + (val x p c).toNat := by
  induction as generalizing c bs p with
  | nil =>
    obtain rfl : bs = [] := List.length_eq_zero_iff.1 hl.symm
    refine ⟨[], c, p, ?_, Ext.refl p, rfl, fun _ h => by simp at h, fun x => ?_⟩
    · simp [ripple]
    · simp [vals, bv]
  | cons a as ih =>
    obtain ⟨b, bs, rfl⟩ : ∃ b bs', bs = b :: bs' := by
      cases bs with
      | nil => simp at hl
      | cons b bs => exact ⟨b, bs, rfl⟩
    have ha' := ha a (by simp)
    have hb' := hb b (by simp)
    have has : AllValid p as := fun w hw => ha w (by simp [hw])
    have hbs : AllValid p bs := fun w hw => hb w (by simp [hw])
    obtain ⟨s, co, p1, e1, x1, vs, vco, h1⟩ := fullAdd_spec ha' hb' hc
    obtain ⟨out, cc, p2, e2, x2, lo, vo, h2⟩ := ih bs (by simpa using hl) co p1
      (has.mono x1) (hbs.mono x1) vco
    refine ⟨s :: out, cc, p2, by simp only [ripple, e1, e2], ?_, by simp [lo], ?_, fun x => ?_⟩
    · have := x1.trans x2
      rwa [show 5 + 5 * as.length = 5 * (a :: as).length by simp; ring] at this
    · intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact x2.valid vs
      · exact vo w hw
    · have e := h2 x
      have e' := h1 x
      rw [x1.vals_eq has, x1.vals_eq hbs] at e
      have hsv : val x p2 s = val x p1 s := x2.val_eq vs x
      simp only [vals, List.map_cons, bv, List.length_cons] at *
      rw [hsv]
      have hp : 2 ^ (as.length + 1) * (val x p2 cc).toNat =
          2 * (2 ^ as.length * (val x p2 cc).toNat) := by ring
      omega

/-- `b` with every bit xored with `s`. -/
def xorV (s : Wire ι) : List (Wire ι) → Prog ι → List (Wire ι) × Prog ι
  | [], p => ([], p)
  | b :: bs, p =>
    let r := gate b s xor p
    let t := xorV s bs r.2
    (r.1 :: t.1, t.2)

theorem xorV_spec (s : Wire ι) (bs : List (Wire ι)) (p : Prog ι) (hs : s.Valid p.length)
    (hb : AllValid p bs) :
    ∃ out p', xorV s bs p = (out, p') ∧ Ext p p' bs.length ∧ out.length = bs.length ∧
      AllValid p' out ∧ ∀ x, vals x p' out = (vals x p bs).map fun y => xor y (val x p s) := by
  induction bs generalizing p with
  | nil => exact ⟨[], p, rfl, Ext.refl p, rfl, fun _ h => by simp at h, fun x => rfl⟩
  | cons b bs ih =>
    have rb : Rep p b fun x => val x p b := ⟨hb b (by simp), fun _ => rfl⟩
    have rs : Rep p s fun x => val x p s := ⟨hs, fun _ => rfl⟩
    have hbs : AllValid p bs := fun w hw => hb w (by simp [hw])
    obtain ⟨w1, p1, e1, x1, r1⟩ := gate_spec rb rs xor
    obtain ⟨out, p2, e2, x2, lo, vo, h2⟩ := ih p1 (x1.valid hs) (hbs.mono x1)
    refine ⟨w1 :: out, p2, by simp only [xorV, e1, e2], ?_, by simp [lo], ?_, fun x => ?_⟩
    · have := x1.trans x2
      rwa [show 1 + bs.length = (b :: bs).length by simp; omega] at this
    · intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact x2.valid r1.1
      · exact vo w hw
    · have e := h2 x
      rw [x1.vals_eq hbs, x1.val_eq hs] at e
      simp only [vals, List.map_cons] at *
      rw [e, x2.val_eq r1.1, r1.2 x]

theorem bv_map_xor_false (l : List Bool) : bv (l.map fun y => xor y false) = bv l := by
  have : (fun y : Bool => xor y false) = id := by
    funext y
    simp
  rw [this, List.map_id]

theorem bv_map_xor_true (l : List Bool) :
    bv (l.map fun y => xor y true) + bv l + 1 = 2 ^ l.length := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.map_cons, bv, List.length_cons, pow_succ]
    cases b <;> simp only [Bool.false_xor, Bool.true_xor, Bool.not_true,
      Bool.toNat_true, Bool.toNat_false] <;> omega

/-- `F x` modulo `2 ^ w` is held on the `w` wires `v` after `p`. -/
def Enc (w : ℕ) (p : Prog ι) (v : List (Wire ι)) (F : BitInput ι → ℤ) : Prop :=
  v.length = w ∧ AllValid p v ∧ ∀ x, (bv (vals x p v) : ℤ) ≡ F x [ZMOD (2 : ℤ) ^ w]

theorem Enc.mono {w c : ℕ} {p p' : Prog ι} {v : List (Wire ι)} {F : BitInput ι → ℤ}
    (h : Enc w p v F) (e : Ext p p' c) : Enc w p' v F :=
  ⟨h.1, h.2.1.mono e, fun x => by rw [e.vals_eq h.2.1]; exact h.2.2 x⟩

theorem Enc.congr {w : ℕ} {p : Prog ι} {v : List (Wire ι)} {F G : BitInput ι → ℤ}
    (h : Enc w p v F) (e : ∀ x, F x = G x) : Enc w p v G :=
  ⟨h.1, h.2.1, fun x => e x ▸ h.2.2 x⟩

theorem modEq_of_eq_add_mul {a b m c : ℤ} (h : a = b + m * c) : a ≡ b [ZMOD m] := by
  rw [h, Int.ModEq, Int.add_mul_emod_self_left]

/-- `a + (-1)^s b`, in `6 w` gates. -/
def addsub (s : Wire ι) (a b : List (Wire ι)) (p : Prog ι) : List (Wire ι) × Prog ι :=
  let r := xorV s b p
  let t := ripple s a r.1 r.2
  (t.1.1, t.2)

theorem addsub_spec {w : ℕ} {p : Prog ι} {s : Wire ι} {a b : List (Wire ι)}
    {A B : BitInput ι → ℤ} (hs : s.Valid p.length) (ha : Enc w p a A) (hb : Enc w p b B) :
    ∃ out p', addsub s a b p = (out, p') ∧ Ext p p' (6 * w) ∧
      Enc w p' out fun x => A x + bitSign (val x p s) * B x := by
  obtain ⟨la, va, ma⟩ := ha
  obtain ⟨lb, vb, mb⟩ := hb
  obtain ⟨o1, p1, e1, x1, l1, v1, h1⟩ := xorV_spec s b p hs vb
  obtain ⟨out, co, p2, e2, x2, lo, vo, h2⟩ := ripple_spec a o1 (by omega) s p1
    (va.mono x1) v1 (x1.valid hs)
  refine ⟨out, p2, by simp only [addsub, e1, e2], ?_, by omega, vo, fun x => ?_⟩
  · have := x1.trans x2
    rwa [show b.length + 5 * a.length = 6 * w by omega] at this
  · have e := h2 x
    rw [h1 x, x1.vals_eq va, x1.val_eq hs, la] at e
    have hlen : (vals x p b).length = w := by simp [vals, lb]
    have hm := (ma x)
    have hn := (mb x)
    have key : (bv (vals x p2 out) : ℤ) ≡
        (bv (vals x p a) : ℤ) + bitSign (val x p s) * (bv (vals x p b) : ℤ)
          [ZMOD (2 : ℤ) ^ w] := by
      cases hv : val x p s with
      | false =>
        rw [hv, bv_map_xor_false] at e
        refine modEq_of_eq_add_mul (c := -((val x p2 co).toNat : ℤ)) ?_
        simp only [Bool.toNat_false] at e
        simp only [bitSign]
        push_cast
        have e' : (bv (vals x p2 out) : ℤ) + 2 ^ w * ((val x p2 co).toNat : ℤ) =
            bv (vals x p a) + bv (vals x p b) := by exact_mod_cast e
        linarith
      | true =>
        rw [hv] at e
        have f := bv_map_xor_true (vals x p b)
        rw [hlen] at f
        refine modEq_of_eq_add_mul (c := 1 - ((val x p2 co).toNat : ℤ)) ?_
        simp only [Bool.toNat_true] at e
        simp only [bitSign]
        have e' : (bv (vals x p2 out) : ℤ) + 2 ^ w * ((val x p2 co).toNat : ℤ) =
            bv (vals x p a) +
              (bv ((vals x p b).map fun y => xor y true) : ℤ) + 1 := by exact_mod_cast e
        have f' : (bv ((vals x p b).map fun y => xor y true) : ℤ) + bv (vals x p b) + 1 =
            2 ^ w := by exact_mod_cast f
        simp only [ite_true]
        linarith
    exact key.trans (hm.add (hn.mul_left _))

/-- The value `1`, once a true wire is available. -/
def trueGate (p : Prog ι) : Wire ι × Prog ι := gate none none (fun _ _ => true) p

theorem trueGate_spec (p : Prog ι) :
    ∃ t p', trueGate p = (t, p') ∧ Ext p p' 1 ∧ Rep p' t fun _ => true :=
  gate_spec (rep_none p) (rep_none p) _

/-- `a + b`. -/
def addV (a b : List (Wire ι)) (p : Prog ι) : List (Wire ι) × Prog ι := addsub none a b p

theorem addV_spec {w : ℕ} {p : Prog ι} {a b : List (Wire ι)} {A B : BitInput ι → ℤ}
    (ha : Enc w p a A) (hb : Enc w p b B) :
    ∃ out p', addV a b p = (out, p') ∧ Ext p p' (6 * w) ∧
      Enc w p' out fun x => A x + B x := by
  obtain ⟨out, p', e, x, h⟩ := addsub_spec (s := none) trivial ha hb
  exact ⟨out, p', e, x, h.congr fun y => by simp [bitSign, val, wireVal]⟩

/-- `a - b`. -/
def subV (a b : List (Wire ι)) (p : Prog ι) : List (Wire ι) × Prog ι :=
  let r := trueGate p
  addsub r.1 a b r.2

theorem subV_spec {w : ℕ} {p : Prog ι} {a b : List (Wire ι)} {A B : BitInput ι → ℤ}
    (ha : Enc w p a A) (hb : Enc w p b B) :
    ∃ out p', subV a b p = (out, p') ∧ Ext p p' (6 * w + 1) ∧
      Enc w p' out fun x => A x - B x := by
  obtain ⟨t, p1, e1, x1, r1⟩ := trueGate_spec p
  obtain ⟨out, p2, e2, x2, h⟩ := addsub_spec r1.1 (ha.mono x1) (hb.mono x1)
  refine ⟨out, p2, by simp only [subV, e1, e2], ?_, h.congr fun y => ?_⟩
  · have := x1.trans x2
    rwa [show 1 + 6 * w = 6 * w + 1 by omega] at this
  · simp only [r1.2 y, bitSign, ite_true]
    ring

/-- The all-false vector. -/
def zeros (w : ℕ) : List (Wire ι) := List.replicate w none

theorem bv_replicate_false (w : ℕ) : bv (List.replicate w false) = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => simp [List.replicate_succ, bv, ih]

theorem enc_zeros (w : ℕ) (p : Prog ι) : Enc w p (zeros w) fun _ => 0 := by
  refine ⟨by simp [zeros], fun u hu => ?_, fun x => ?_⟩
  · rw [zeros, List.mem_replicate] at hu
    rw [hu.2]
    trivial
  · have : vals x p (zeros w) = List.replicate w false := by
      simp [vals, zeros, List.map_replicate, val, wireVal]
    rw [this, bv_replicate_false]
    rfl

/-- `1` on `w + 1` wires, given a true wire. -/
def oneV (w : ℕ) (t : Wire ι) : List (Wire ι) := t :: zeros w

theorem enc_oneV {w : ℕ} {p : Prog ι} {t : Wire ι} (h : Rep p t fun _ => true) :
    Enc (w + 1) p (oneV w t) fun _ => 1 := by
  obtain ⟨-, vz, mz⟩ := enc_zeros (ι := ι) w p
  refine ⟨by simp [oneV, zeros], fun u hu => ?_, fun x => ?_⟩
  · rcases List.mem_cons.1 hu with rfl | hu
    · exact h.1
    · exact vz u hu
  · have hv : vals x p (zeros w) = List.replicate w false := by
      simp [vals, zeros, List.map_replicate, val, wireVal]
    simp only [oneV, vals, List.map_cons, bv]
    rw [show (zeros w).map (val x p) = vals x p (zeros w) from rfl, hv, bv_replicate_false, h.2 x]
    rfl

/-- `(-1)^s b`. -/
def signMul (s : Wire ι) (w : ℕ) (b : List (Wire ι)) (p : Prog ι) : List (Wire ι) × Prog ι :=
  addsub s (zeros w) b p

theorem signMul_spec {w : ℕ} {p : Prog ι} {s : Wire ι} {b : List (Wire ι)}
    {B : BitInput ι → ℤ} (hs : s.Valid p.length) (hb : Enc w p b B) :
    ∃ out p', signMul s w b p = (out, p') ∧ Ext p p' (6 * w) ∧
      Enc w p' out fun x => bitSign (val x p s) * B x := by
  obtain ⟨out, p', e, x, h⟩ := addsub_spec hs (enc_zeros w p) hb
  exact ⟨out, p', e, x, h.congr fun y => by ring⟩

/-- Doubling `e` times. -/
def dblN : ℕ → List (Wire ι) → Prog ι → List (Wire ι) × Prog ι
  | 0, a, p => (a, p)
  | e + 1, a, p =>
    let r := dblN e a p
    addV r.1 r.1 r.2

theorem dblN_spec {w : ℕ} (e : ℕ) {p : Prog ι} {a : List (Wire ι)} {A : BitInput ι → ℤ}
    (ha : Enc w p a A) :
    ∃ out p', dblN e a p = (out, p') ∧ Ext p p' (e * (6 * w)) ∧
      Enc w p' out fun x => 2 ^ e * A x := by
  induction e with
  | zero => exact ⟨a, p, rfl, by simpa using Ext.refl p, ha.congr fun y => by simp⟩
  | succ e ih =>
    obtain ⟨o1, p1, e1, x1, h1⟩ := ih
    obtain ⟨o2, p2, e2, x2, h2⟩ := addV_spec h1 h1
    refine ⟨o2, p2, by simp only [dblN, e1, e2], ?_, h2.congr fun y => by ring⟩
    have := x1.trans x2
    rwa [show e * (6 * w) + 6 * w = (e + 1) * (6 * w) by ring] at this

/-- Run `act` at `0, …, N - 1` and record the outputs by index. -/
def forN (act : ℕ → Prog ι → List (Wire ι) × Prog ι) :
    ℕ → Prog ι → (ℕ → List (Wire ι)) × Prog ι
  | 0, p => (fun _ => [], p)
  | N + 1, p =>
    let r := forN act N p
    let s := act N r.2
    (fun i => if i = N then s.1 else r.1 i, s.2)

theorem forN_spec {w c : ℕ} (act : ℕ → Prog ι → List (Wire ι) × Prog ι) (N : ℕ) (p : Prog ι)
    (R : ℕ → BitInput ι → ℤ)
    (hact : ∀ i < N, ∀ q d, Ext p q d → ∃ v q', act i q = (v, q') ∧ Ext q q' c ∧
      Enc w q' v (R i)) :
    ∃ g p', forN act N p = (g, p') ∧ Ext p p' (N * c) ∧ ∀ i < N, Enc w p' (g i) (R i) := by
  induction N with
  | zero => exact ⟨fun _ => [], p, rfl, by simpa using Ext.refl p, fun i hi => by simp at hi⟩
  | succ N ih =>
    obtain ⟨g, p1, e1, x1, h1⟩ := ih fun i hi => hact i (by omega)
    obtain ⟨v, p2, e2, x2, h2⟩ := hact N (by omega) p1 _ x1
    refine ⟨fun i => if i = N then v else g i, p2, by simp only [forN, e1, e2], ?_,
      fun i hi => ?_⟩
    · have := x1.trans x2
      rwa [show N * c + c = (N + 1) * c by ring] at this
    · by_cases hN : i = N
      · simpa [hN] using h2
      · simpa [hN] using (h1 i (by omega)).mono x2

/-- `v 0 + ⋯ + v (N - 1)`, from zero. -/
def sumV (w : ℕ) (v : ℕ → List (Wire ι)) : ℕ → Prog ι → List (Wire ι) × Prog ι
  | 0, p => (zeros w, p)
  | N + 1, p =>
    let r := sumV w v N p
    addV r.1 (v N) r.2

theorem sumV_spec {w : ℕ} (v : ℕ → List (Wire ι)) (N : ℕ) (p : Prog ι)
    (F : ℕ → BitInput ι → ℤ) (hv : ∀ i < N, Enc w p (v i) (F i)) :
    ∃ out p', sumV w v N p = (out, p') ∧ Ext p p' (N * (6 * w)) ∧
      Enc w p' out fun x => ∑ i ∈ range N, F i x := by
  induction N with
  | zero =>
    exact ⟨_, p, rfl, by simpa using Ext.refl p, (enc_zeros w p).congr fun y => by simp⟩
  | succ N ih =>
    obtain ⟨o1, p1, e1, x1, h1⟩ := ih fun i hi => hv i (by omega)
    obtain ⟨o2, p2, e2, x2, h2⟩ := addV_spec h1 ((hv N (by omega)).mono x1)
    refine ⟨o2, p2, by simp only [sumV, e1, e2], ?_, h2.congr fun y => ?_⟩
    · have := x1.trans x2
      rwa [show N * (6 * w) + 6 * w = (N + 1) * (6 * w) by ring] at this
    · rw [sum_range_succ]

/-- The bit `w` of a residue on `w + 1` wires is the sign of a value in
`[-2^w, 2^w)`. -/
theorem sign_wire {w : ℕ} {p : Prog ι} {v : List (Wire ι)} {T : BitInput ι → ℤ}
    (h : Enc (w + 1) p v T) (x : BitInput ι) (lo : -2 ^ w ≤ T x) (hi : T x < 2 ^ w) :
    val x p (v.getD w none) = decide (T x < 0) := by
  obtain ⟨hl, -, hm⟩ := h
  have hb : (val x p (v.getD w none)) = (bv (vals x p v)).testBit w := by
    rw [testBit_bv, vals, List.getD_eq_getElem _ _ (by simp [hl]),
      List.getD_eq_getElem _ _ (by simp [hl]), List.getElem_map]
  rw [hb]
  have hlt : bv (vals x p v) < 2 ^ (w + 1) := by
    have := bv_lt (vals x p v)
    simpa [vals, hl] using this
  have hmod := hm x
  have hpow : (2 : ℤ) ^ (w + 1) = 2 * 2 ^ w := by ring
  obtain ⟨c, hc⟩ := (Int.modEq_iff_dvd.1 hmod)
  have hlt' : (bv (vals x p v) : ℤ) < 2 ^ (w + 1) := by exact_mod_cast hlt
  have hnn : (0 : ℤ) ≤ bv (vals x p v) := Int.natCast_nonneg _
  have hw : (0 : ℤ) < 2 ^ w := by positivity
  by_cases hneg : T x < 0
  · have hc1 : c = -1 := by
      have h1 : T x - bv (vals x p v) = (2 * 2 ^ w) * c := by rw [hc, hpow]
      have u : c < 0 := by
        by_contra hu
        have : (2 * 2 ^ w) * c ≥ 0 := mul_nonneg (by positivity) (by omega)
        linarith
      have l : -2 < c := by
        by_contra hu
        have : (2 * 2 ^ w) * c ≤ (2 * 2 ^ w) * (-2) := by
          apply mul_le_mul_of_nonneg_left (by omega) (by positivity)
        rw [hpow] at hlt'
        linarith
      omega
    have hv : (bv (vals x p v) : ℤ) = T x + 2 * 2 ^ w := by
      have h1 : T x - bv (vals x p v) = (2 * 2 ^ w) * c := by rw [hc, hpow]
      rw [hc1] at h1
      linarith
    have hge : 2 ^ w ≤ bv (vals x p v) := by
      have : (2 : ℤ) ^ w ≤ bv (vals x p v) := by linarith
      exact_mod_cast this
    obtain ⟨y, hy⟩ := Nat.exists_eq_add_of_le hge
    have hy' : y < 2 ^ w := by
      rw [pow_succ] at hlt
      omega
    rw [hy, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hy']
    simp [hneg]
  · have hc0 : c = 0 := by
      have h1 : T x - bv (vals x p v) = (2 * 2 ^ w) * c := by rw [hc, hpow]
      have u : c < 1 := by
        by_contra hu
        have : (2 * 2 ^ w) * c ≥ (2 * 2 ^ w) * 1 := by
          apply mul_le_mul_of_nonneg_left (by omega) (by positivity)
        linarith
      have l : -1 < c := by
        by_contra hu
        have : (2 * 2 ^ w) * c ≤ (2 * 2 ^ w) * (-1) := by
          apply mul_le_mul_of_nonneg_left (by omega) (by positivity)
        rw [hpow] at hlt'
        linarith
      omega
    have hv : (bv (vals x p v) : ℤ) = T x := by
      have h1 : T x - bv (vals x p v) = (2 * 2 ^ w) * c := by rw [hc, hpow]
      rw [hc0] at h1
      linarith
    have hlt2 : bv (vals x p v) < 2 ^ w := by
      have : (bv (vals x p v) : ℤ) < 2 ^ w := by linarith
      exact_mod_cast this
    rw [Nat.testBit_lt_two_pow hlt2]
    simp [hneg]

end QuarticQuery.Forrelation
