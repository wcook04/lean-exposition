import PCP.Complexity.Machine
import Mathlib.Data.Nat.Digits.Lemmas

/-! # Binary encoding of natural numbers and finite lists -/

namespace PCP.Machine

open PCP

/-! ## Naturals and lists of naturals -/

/-- A natural in binary, least significant bit first: `Nat.digits 2`, as bits. -/
def binDigits (x : ℕ) : List Bool := (Nat.digits 2 x).map (· == 1)

theorem binDigits_injective : Function.Injective binDigits := by
  intro x y h
  have hd : ∀ z, ∀ c ∈ Nat.digits 2 z, c = 0 ∨ c = 1 := by
    intro z c hc
    have := Nat.digits_lt_base (by norm_num) hc
    omega
  have hinj : ∀ l l' : List ℕ, (∀ c ∈ l, c = 0 ∨ c = 1) → (∀ c ∈ l', c = 0 ∨ c = 1) →
      l.map (· == 1) = l'.map (· == 1) → l = l' := by
    intro l
    induction l with
    | nil => intro l' _ _ h; simpa using h.symm
    | cons a t ih =>
      intro l' ha hl' h
      cases l' with
      | nil => simp at h
      | cons b t' =>
        simp only [List.map_cons, List.cons.injEq] at h
        have hab : a = b := by
          rcases ha a (by simp) with h1 | h1 <;> rcases hl' b (by simp) with h2 | h2 <;>
            simp_all
        rw [hab, ih t' (fun c hc => ha c (by simp [hc])) (fun c hc => hl' c (by simp [hc])) h.2]
  exact Nat.digits_inj_iff.1 (hinj _ _ (hd x) (hd y) h)

/-- A list of naturals: each in binary, each followed by a separator. -/
def encodeNats (l : List ℕ) : List Sym := l.flatMap fun x => ofBits (binDigits x) ++ [.sep]

theorem sep_notMem_ofBits (b : List Bool) : Sym.sep ∉ ofBits b := by
  simp [ofBits]

/-- Two chunks ending at their only separator agree if the encodings do. -/
theorem chunk_eq {a b : List Bool} {xs ys : List Sym}
    (h : ofBits a ++ .sep :: xs = ofBits b ++ .sep :: ys) : a = b ∧ xs = ys := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simpa [ofBits] using h
    | cons c b => simp [ofBits] at h
  | cons c a ih =>
    cases b with
    | nil => simp [ofBits] at h
    | cons e b =>
      simp only [ofBits, List.map_cons, List.cons_append, List.cons.injEq, Sym.bit.injEq] at h
      obtain ⟨hce, hrest⟩ := h
      have := ih (b := b) hrest
      exact ⟨by rw [hce, this.1], this.2⟩

theorem encodeNats_injective : Function.Injective encodeNats := by
  intro l
  induction l with
  | nil =>
    intro l' h
    cases l' with
    | nil => rfl
    | cons y t => simp [encodeNats] at h
  | cons x t ih =>
    intro l' h
    cases l' with
    | nil => simp [encodeNats] at h
    | cons y t' =>
      simp only [encodeNats, List.flatMap_cons, List.append_assoc, List.singleton_append] at h
      obtain ⟨hxy, hrest⟩ := chunk_eq h
      rw [binDigits_injective hxy, ih hrest]

/-! ## Encoded size -/

theorem length_binDigits_le (x : ℕ) : (binDigits x).length ≤ x := by
  simp only [binDigits, List.length_map]
  exact (Nat.digits_length_le_iff (by norm_num) x).2 Nat.lt_two_pow_self

theorem length_encodeNats (l : List ℕ) :
    (encodeNats l).length = (l.map fun x => (binDigits x).length + 1).sum := by
  induction l with
  | nil => simp [encodeNats]
  | cons x t ih =>
    simp only [encodeNats, List.flatMap_cons, List.length_append, List.map_cons,
      List.sum_cons] at ih ⊢
    rw [ih]; simp [ofBits]

/-- Every chunk has at least its separator. -/
theorem length_le_length_encodeNats (l : List ℕ) : l.length ≤ (encodeNats l).length := by
  rw [length_encodeNats]
  induction l with
  | nil => simp
  | cons x t ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega

/-- With every entry at most `B`, each chunk has at most `B + 1` symbols. -/
theorem length_encodeNats_le (l : List ℕ) {B : ℕ} (hB : ∀ x ∈ l, x ≤ B) :
    (encodeNats l).length ≤ l.length * (B + 1) := by
  rw [length_encodeNats]
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have hx := le_trans (length_binDigits_le x) (hB x (by simp))
    have := ih fun y hy => hB y (by simp [hy])
    nlinarith

end PCP.Machine
