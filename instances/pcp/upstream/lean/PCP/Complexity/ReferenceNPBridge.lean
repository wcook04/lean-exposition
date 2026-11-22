import PCP.Complexity.ReferenceNP
import PCP.Complexity.ReferenceNTMWitness
import PCP.Complexity.ReferenceNTMPairedBounds
import PCP.Complexity.LangSymbolBridge
import PCP.Theorem

/-!
# From the pinned reference NP class to the concrete PCP theorem

The witness is a finite sequence of nondeterministic choices. The actual paired
stream program simulates those choices, and the proved compiler supplies its
finite multitape machine and polynomial runtime. The source time polynomial is
used only as the witness-length bound, never as an assumed runtime certificate.
-/

namespace PCP.ReferenceNP

open ReferenceNTM

@[simp] theorem symbolCode_bit (b : Bool) :
    Machine.LangSymbolBridge.symbolCode (.bit b) = b.toNat := by cases b <;> rfl

@[simp] theorem code_encodeBool (b : Bool) :
    Machine.LangSymbolBridge.code (Machine.encodeBool b) = [b.toNat] := by
  cases b <;> rfl

@[simp] theorem code_encodePair (x w : List Bool) :
    Machine.LangSymbolBridge.code (Machine.encodePair (x, w)) = PairedStream.pair x w := by
  simp [Machine.LangSymbolBridge.code, Machine.encodePair, Machine.ofBits,
    PairedStream.pair, List.map_map, Function.comp_def,
    show Machine.LangSymbolBridge.symbolCode .sep = 2 from rfl]

variable {k q : ℕ} (tm : Complexity.NTM k) (eQ : tm.Q ≃ Fin q)

/-- The full reference path checker has polynomial charged cost on the public pair encoding. -/
theorem checker_cost (x w : List Bool) :
    (PairedStream.program tm eQ).cost
      (Machine.LangSymbolBridge.code (Machine.encodePair (x, w))) ≤
      (Lang.ArithmeticStream.programConstant (PairedStream.initial tm eQ)
        (PairedStream.terms tm eQ) (PairedStream.verdict tm eQ) * (Nat.size q + 4) ^ 2) *
      ((Machine.encodePair (x, w)).length + 1) ^ 2 := by
  rw [code_encodePair]
  have hc := PairedStream.program_cost tm eQ x w
  have hw : PairedStream.storageBound q x.length w.length + 1 ≤
      (Nat.size q + 4) * ((Machine.encodePair (x, w)).length + 1) := by
    simp only [PairedStream.storageBound, Machine.length_encodePair]
    nlinarith
  apply hc.trans
  calc
    _ ≤ Lang.ArithmeticStream.programConstant (PairedStream.initial tm eQ)
        (PairedStream.terms tm eQ) (PairedStream.verdict tm eQ) *
        ((Nat.size q + 4) * ((Machine.encodePair (x, w)).length + 1)) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw 2)
    _ = _ := by rw [Nat.mul_pow, Nat.mul_assoc]

include eQ in
/-- A concrete `FinTM2` machine checks any supplied reference-machine path. -/
theorem checker_polyTime : Machine.PolyTimeRel (Cfg.accepts tm) := by
  apply Machine.LangSymbolBridge.polyTimeMap_of_program Machine.encodePair Machine.encodeBool
    (fun p => Cfg.accepts tm p.1 p.2) (PairedStream.program tm eQ)
    (Lang.compile (PairedStream.program tm eQ))
  · rintro ⟨x, w⟩
    rw [code_encodePair, code_encodeBool, PairedStream.program_run]
  · rintro ⟨x, w⟩
    exact checker_cost tm eQ x w

/-- Every language in the exact pinned reference NP class has a concrete
polynomial-time witness checker in this development's machine model. -/
theorem to_inNP {L : Complexity.Language} (hL : L ∈ Complexity.NP) :
    PCP.InNP Machine.PolyTimeRel L := by
  obtain ⟨k, tm, p, htm⟩ := mem_iff_polynomial.mp hL
  refine ⟨{
    witnessBound := p
    check := Cfg.accepts tm
    check_polyTime := checker_polyTime tm (Fintype.equivFin tm.Q)
    spec := fun x => Cfg.decides_iff_witness tm L p.eval htm x }⟩

/-- The PCP theorem for the upstream nondeterministic-machine definition of NP. -/
theorem np_subset_pcp (L : Complexity.Language) (hL : L ∈ Complexity.NP) :
    ∃ (V : PCP.Verifier) (alg : PCP.VerifierAlg) (a b q : ℕ) (p : Polynomial ℕ),
      Machine.PolyTimeAlg alg ∧
      V.ImplementedBy alg ∧
      V.queries = q ∧
      V.CanonicalRandomness a b ∧
      (∀ x : List Bool, V.ReadsBelow x (p.eval x.length)) ∧
      (∀ x : List Bool, x ∈ L → V.CompleteAt x) ∧
      (∀ x : List Bool, x ∉ L → V.SoundAt x (1 / 2)) :=
  PCP.np_subset_pcp L (to_inNP hL)

end PCP.ReferenceNP
