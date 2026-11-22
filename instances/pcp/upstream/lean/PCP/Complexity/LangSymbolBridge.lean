import PCP.Complexity.BlockTransducer
import PCP.Complexity.LangCompile

/-!
# Concrete encoding bridges for compiled language programs

Public tape symbols are represented by naturals zero, one, and two. Finite
transducers convert both ways between the public tape and separator-delimited
natural lists. The bridge uses an explicitly supplied compiler certificate;
callers can now obtain it from the proved `Lang.compile` theorem.
-/

namespace PCP.Machine.LangSymbolBridge

open Turing

def symbolCode : Sym → ℕ
  | .bit false => 0
  | .bit true => 1
  | .sep => 2

def code (xs : List Sym) : List ℕ := xs.map symbolCode

theorem encode_cons (c : Sym) (xs : List Sym) :
    encodeNats (code (c :: xs)) = encodeNats [symbolCode c] ++ encodeNats (code xs) := by
  simp [code, encodeNats]

def encodingSpec : BlockTransducer.Spec where
  State := Unit
  init := ()
  next _ _ := ()
  emit _ c := encodeNats [symbolCode c]

theorem encoding_output (xs : List Sym) :
    encodingSpec.output () xs = encodeNats (code xs) := by
  induction xs with
  | nil => rfl
  | cons c xs ih =>
    change encodeNats [symbolCode c] ++ encodingSpec.output () xs = _
    rw [ih, encode_cons]

def decodingSpec : TransducerSpec where
  State := Fin 5
  init := 0
  next s c := match c with
    | .sep => 0
    | .bit b => if s = 0 then (if b then 2 else 1) else if s = 1 ∧ b = true then 3 else 4
  emit s c := match c with
    | .bit _ => none
    | .sep => some (if s = 2 then .bit true else if s = 3 then .sep else .bit false)

theorem decoding_word (c : Sym) (xs : List Sym) :
    decodingSpec.output (0 : Fin 5) (encodeNats [symbolCode c] ++ xs) =
      c :: decodingSpec.output (0 : Fin 5) xs := by
  cases c with
  | bit b => cases b <;> rfl
  | sep => rfl

theorem decoding_output (xs : List Sym) :
    decodingSpec.output (0 : Fin 5) (encodeNats (code xs)) = xs := by
  induction xs with
  | nil => rfl
  | cons c xs ih =>
    rw [encode_cons, decoding_word, ih]

theorem encoded_length_ge (xs : List Sym) : xs.length ≤ (encodeNats (code xs)).length := by
  induction xs with
  | nil => simp [code, encodeNats]
  | cons c xs ih =>
    rw [encode_cons, List.length_cons]
    have hc : 1 ≤ (encodeNats [symbolCode c]).length := by simp [encodeNats]
    rw [List.length_append]
    omega

/-- Symbol-to-natural conversion is performed by an actual linear-time machine. -/
noncomputable def encodingWitness {α : Type} (ea : α → List Sym) :
    TM2ComputableInPolyTime ea (fun a => encodeNats (code (ea a))) id :=
  BlockTransducer.computable encodingSpec Empty (fun _ => Sym) _ _ _
    (fun a => (encoding_output (ea a)).symm)

/-- The inverse conversion is also performed by an actual linear-time machine. -/
noncomputable def decodingWitness {β : Type} (eb : β → List Sym) :
    TM2ComputableInPolyTime (fun b => encodeNats (code (eb b))) eb id :=
  transducerComputable decodingSpec Empty (fun _ => Sym) _ _ _
    (fun b => (decoding_output (eb b)).symm)

/-- Specialize the supplied compiler certificate to the actual symbol-coded domain. -/
theorem compiled_witness {α β : Type} (ea : α → List Sym) (eb : β → List Sym) (f : α → β)
    (P : Lang.Prog) (hP : Lang.CompilesInPolyTime P)
    (hrun : ∀ a, P.run (code (ea a)) = code (eb (f a))) {c₁ k₁ : ℕ}
    (hcost : ∀ a, P.cost (code (ea a)) ≤ c₁ * ((ea a).length + 1) ^ k₁) :
    Nonempty (TM2ComputableInPolyTime (fun a => encodeNats (code (ea a)))
      (fun b => encodeNats (code (eb b))) f) := by
  obtain ⟨tm, ein, eout, c, k, hc⟩ := hP
  refine ⟨⟨⟨tm, ein, eout⟩, Lang.bridgeTime c k c₁ k₁, fun a => ?_⟩⟩
  have out := Classical.choice (hc (code (ea a)))
  rw [hrun a] at out
  refine ⟨out.toEvalsTo, out.steps_le_m.trans ?_⟩
  apply Lang.bridgeTime_bound
  exact (hcost a).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.add_le_add_right (encoded_length_ge (ea a)) 1) _))

/-- The resulting certificate uses the unchanged public encodings. -/
theorem polyTimeMap_of_program {α β : Type} (ea : α → List Sym) (eb : β → List Sym)
    (f : α → β) (P : Lang.Prog) (hP : Lang.CompilesInPolyTime P)
    (hrun : ∀ a, P.run (code (ea a)) = code (eb (f a))) {c₁ k₁ : ℕ}
    (hcost : ∀ a, P.cost (code (ea a)) ≤ c₁ * ((ea a).length + 1) ^ k₁) :
    PolyTimeMap ea eb f := by
  obtain ⟨compiled⟩ := compiled_witness ea eb f P hP hrun hcost
  have first := composeWitness (f := id) (g := f) (encodingWitness ea) compiled
  have full := composeWitness (f := f ∘ id) (g := id) first (decodingWitness eb)
  exact ⟨full⟩

/-- The answer-history encoding is exactly the one required by the final PCP theorem. -/
theorem polyTimeAlg_of_program (alg : PCP.VerifierAlg) (P : Lang.Prog)
    (hP : Lang.CompilesInPolyTime P)
    (hrun : ∀ t : List Bool × List Bool × List Bool,
      P.run (code (encodeTriple t)) = code (encodeAnswer (alg t.1 t.2.1 t.2.2)))
    {c₁ k₁ : ℕ} (hcost : ∀ t : List Bool × List Bool × List Bool,
      P.cost (code (encodeTriple t)) ≤ c₁ * ((encodeTriple t).length + 1) ^ k₁) :
    PolyTimeAlg alg :=
  polyTimeMap_of_program encodeTriple encodeAnswer (fun t => alg t.1 t.2.1 t.2.2) P hP hrun hcost

end PCP.Machine.LangSymbolBridge
