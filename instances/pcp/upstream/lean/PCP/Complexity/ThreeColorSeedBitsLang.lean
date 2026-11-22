import PCP.Complexity.ThreeColorRawSeedCost

/-!
# Decoding the actual public random-bit list into all seven branch seeds

The complete program consumes stored zero/one cells, constructs every structural
radix from the verifier dimensions, and returns the exact numeric branch codes.
-/

set_option maxRecDepth 4096

namespace PCP.Lang.SeedBits

open PCP.Algebraic ThreeColorSeedIndex ThreeColorSeedSize SeedArithmetic

def word : Stmt 21 4 := WordCodec.decode.rename (Fin.natAdd 16) (fun _ => 2)

def liftRaw (p : Stmt 16 4) : Stmt 21 4 := p.rename (Fin.castAdd 5) id

def raw : Stmt 21 4 := liftRaw RawSeed.program

def program : Stmt 21 4 := .seq word (.seq (.assign 15 (.var 17)) raw)

def Context (n m c t : ℕ) (bits : List Bool) (st : State 21 4) : Prop :=
  (∀ i : Fin 4, st.regs (i.castAdd 17) = ![n, m, c, t] i) ∧
  st.lists 2 = bits.map Bool.toNat ∧ st.lists 3 = []

theorem word_result (st : State 21 4) :
    ((word.run st).1.restrict (Fin.natAdd 16) (fun _ => 2), (word.run st).2) =
      WordCodec.decode.run (st.restrict (Fin.natAdd 16) (fun _ => 2)) := by
  unfold word
  exact WordCodec.decode.run_rename (Fin.natAdd 16) (fun _ => 2)
    (Fin.natAdd_injective 5 16) (Function.injective_of_subsingleton _) st

private theorem liftRaw_result (p : Stmt 16 4) (st : State 21 4) :
    (((liftRaw p).run st).1.restrict (Fin.castAdd 5) id, ((liftRaw p).run st).2) =
      p.run (st.restrict (Fin.castAdd 5) id) := by
  exact p.run_rename (Fin.castAdd 5) id (Fin.castAdd_injective 16 5)
    Function.injective_id st

theorem raw_result (st : State 21 4) :
    ((raw.run st).1.restrict (Fin.castAdd 5) id, (raw.run st).2) =
      RawSeed.program.run (st.restrict (Fin.castAdd 5) id) := liftRaw_result _ st

theorem word_run (bits : List Bool) (st : State 21 4)
    (hb : st.lists 2 = bits.map Bool.toNat) :
    (word.run st).1.regs 17 = Machine.bitsValue bits := by
  have h := (WordCodec.decode_run (st.restrict (Fin.natAdd 16) (fun _ => 2))).1
  rw [← word_result st] at h
  change (word.run st).1.regs 17 = WordCodec.value (st.lists 2) at h
  simpa only [hb, WordCodec.value_map_bool] using h

theorem word_reg (i : Fin 21) (hi : i.val < 16) (st : State 21 4) :
    (word.run st).1.regs i = st.regs i := by
  unfold word
  apply Stmt.run_rename_reg_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [Fin.val_natAdd] at this
  omega

theorem word_empty (st : State 21 4) : (word.run st).1.lists 3 = st.lists 3 := by
  unfold word
  apply Stmt.run_rename_list_outside
  decide

theorem raw_context (n m c t : ℕ) (bits : List Bool) (st : State 21 4)
    (hc : Context n m c t bits st) :
    RawSeed.Context n m c t (Machine.bitsValue bits)
      ((setReg (word.run st).1 15 ((word.run st).1.regs 17)).restrict (Fin.castAdd 5) id) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hi : i.castAdd 17 ≠ (15 : Fin 21) := by
      intro hh; have := congrArg Fin.val hh
      simp only [Fin.val_castAdd] at this
      norm_num at this
      omega
    change (setReg (word.run st).1 15 ((word.run st).1.regs 17)).regs (i.castAdd 17) = _
    rw [setReg_regs, Function.update_of_ne hi, word_reg _ (by simp; omega)]
    exact hc.1 i
  · change (setReg (word.run st).1 15 ((word.run st).1.regs 17)).regs 15 = _
    rw [setReg_regs, Function.update_self]
    exact word_run bits st hc.2.1
  · exact (word_empty st).trans hc.2.2

/-- Exact production decoding for every supplied bit list, including short and long lists. -/
theorem program_bits {F : Type*} [Field F] [Algebra (ZMod 2) F] {t : ℕ}
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (n m c : ℕ) (bits : List Bool)
    (st : State 21 4) (hc : Context n m c t bits st) :
    (program.run st).1.lists 1 = List.ofFn (fun i => ((branchCodec ρ n m c i).equiv
      (((ThreeColorSeedIndex.equiv ρ n m c).symm
        (SeedBitCompatibility.seedOfBits (rawBits n m c t) bits)) i)).val) := by
  let s := setReg (word.run st).1 15 ((word.run st).1.regs 17)
  have h := RawSeed.program_bits ρ n m c bits (s.restrict (Fin.castAdd 5) id)
    (raw_context n m c t bits st hc)
  rw [← raw_result s] at h
  simp only [State.restrict_lists, id_eq] at h
  simp only [program, run_seq_fst, run_assign_fst, Expr.eval]
  exact h

end PCP.Lang.SeedBits
