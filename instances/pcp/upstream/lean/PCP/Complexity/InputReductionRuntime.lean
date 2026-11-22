import PCP.Complexity.LangRunOnFirstCost
import PCP.Complexity.LangSymbolBridge

/-!
# Concrete polynomial-time preprocessing of verifier inputs

The reduction is run on the input word of the actual triple encoding. The random
word and answer history are copied unchanged, including malformed-length words.
The result composes with the target verifier's genuine machine certificate.
-/

namespace PCP.Machine.InputReductionRuntime

open Lang LangSymbolBridge

theorem code_ofBits (x : List Bool) : code (ofBits x) = x.map Bool.toNat := by
  simp only [code, ofBits, List.map_map]
  congr 1
  funext b
  cases b <;> rfl

theorem code_triple (t : List Bool × List Bool × List Bool) :
    code (encodeTriple t) =
      t.1.map Bool.toNat ++ 2 :: (t.2.1.map Bool.toNat ++ 2 :: t.2.2.map Bool.toNat) := by
  simp only [encodeTriple, code, List.map_append, List.map_cons]
  change code (ofBits t.1) ++ 2 :: code (ofBits t.2.1) ++ 2 :: code (ofBits t.2.2) = _
  simp only [code_ofBits, List.append_assoc, List.cons_append]

theorem code_bounded (xs : List Sym) : ∀ v ∈ code xs, v ≤ 2 := by
  intro v hv
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hv
  cases s with
  | sep => rfl
  | bit b => cases b <;> decide

theorem code_size (xs : List Sym) : listSize (code xs) ≤ 3 * xs.length := by
  induction xs with
  | nil => simp [code, listSize]
  | cons s xs ih =>
    have hs : Nat.size (symbolCode s) ≤ 2 := (size_le_self _).trans
      (by cases s with | sep => rfl | bit b => cases b <;> decide)
    simp only [code, List.map_cons, listSize, List.sum_cons, List.length_cons] at ih ⊢
    omega

theorem bit_ne_separator (x : List Bool) : ∀ v ∈ x.map Bool.toNat, v ≠ 2 := by
  intro v hv
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hv
  cases b <;> decide

/-- The public triple-to-triple preprocessing is realized by a fixed finite machine. -/
theorem polyTimeMap (f : List Bool → List Bool) (P : Prog)
    (hrun : ∀ x : List Bool, P.run (x.map Bool.toNat) = (f x).map Bool.toNat)
    {C d : ℕ} (hcost : ∀ x : List Bool, P.cost (x.map Bool.toNat) ≤ C * (x.length + 1) ^ d) :
    PolyTimeMap encodeTriple encodeTriple
      (fun t : List Bool × List Bool × List Bool => (f t.1, t.2)) := by
  apply LangSymbolBridge.polyTimeMap_of_program encodeTriple encodeTriple _
    (RunOnFirst.program P) (Lang.compile _)
    (c₁ := 1170 + 3 * C) (k₁ := d + 2)
  · intro t
    simp only [code_triple]
    rw [RunOnFirst.program_run P _ _ (bit_ne_separator t.1), hrun]
  · intro t
    have hb := code_bounded (encodeTriple t)
    rw [code_triple] at hb
    have hp := RunOnFirst.program_cost P _ _ (bit_ne_separator t.1) hb
    rw [← code_triple] at hp
    have hs := code_size (encodeTriple t)
    let N := (encodeTriple t).length + 1
    have hn : 0 < N := by omega
    have hx : t.1.length + 1 ≤ N := by simp only [N, length_encodeTriple]; omega
    have hpow : (t.1.length + 1) ^ d ≤ N ^ (d + 2) :=
      (Nat.pow_le_pow_left hx d).trans (Nat.pow_le_pow_right hn (by omega))
    have hred := (hcost t.1).trans (Nat.mul_le_mul_left C hpow)
    have hquad : (listSize (code (encodeTriple t)) + 1) ^ 2 ≤ 9 * N ^ 2 := by
      dsimp only [N]
      nlinarith
    have hpow2 : N ^ 2 ≤ N ^ (d + 2) := Nat.pow_le_pow_right hn (by omega)
    change _ ≤ (1170 + 3 * C) * N ^ (d + 2)
    nlinarith

/-- Machine-time certificates compose with the actual triple preprocessing. -/
theorem polyTimeAlg (alg : VerifierAlg) (hAlg : PolyTimeAlg alg)
    (f : List Bool → List Bool) (P : Prog)
    (hrun : ∀ x : List Bool, P.run (x.map Bool.toNat) = (f x).map Bool.toNat)
    {C d : ℕ} (hcost : ∀ x : List Bool, P.cost (x.map Bool.toNat) ≤ C * (x.length + 1) ^ d) :
    PolyTimeAlg (fun x bits answers => alg (f x) bits answers) :=
  (polyTimeMap f P hrun hcost).comp hAlg

end PCP.Machine.InputReductionRuntime
