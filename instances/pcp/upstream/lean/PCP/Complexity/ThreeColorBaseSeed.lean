import PCP.Complexity.ThreeColorBaseSetup

/-! Materializing all seven actual sampler codes into permanent base-verifier registers. -/

set_option maxRecDepth 1024

namespace PCP.Lang.ThreeColorBaseSeed

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters ThreeColorSeedIndex
  ThreeColorBaseSetup

def sample (N : ℕ) (bits : List Bool) :=
  (ThreeColorSeedIndex.equiv (coordinates (exponent N)) (size (exponent N))
    (size (exponent N)) 4).symm
    (SeedBitCompatibility.seedOfBits (ThreeColorBinaryVerifier.randomBits N) bits)

def codes (N : ℕ) (bits : List Bool) (i : Fin 7) : ℕ :=
  ((branchCodec (coordinates (exponent N)) (size (exponent N))
    (size (exponent N)) 4 i).equiv (sample N bits i)).val

def port (i : Fin 7) : Fin 400 := ⟨350+i.val, by omega⟩

def Seeds (N : ℕ) (bits : List Bool) (st : State 400 128) : Prop :=
  ∀ i, st.regs (port i) = codes N bits i

def load : Stmt 400 128 := .seq (.assign 0 (.var 322)) (.seq (.assign 1 (.var 322))
  (.seq (.assign 2 (.const 4)) (.seq (.assign 3 (.var 324))
    (.seq (.copy 101 2) (.copy 122 3)))))

def decoder : Stmt 400 128 := call (by decide) (by decide) SeedBits.program

def parse : Stmt 400 128 := .seq (.copy 1 99)
  (.seq (.pop 99 350 319) (.seq (.pop 99 351 319) (.seq (.pop 99 352 319)
    (.seq (.pop 99 353 319) (.seq (.pop 99 354 319) (.seq (.pop 99 355 319)
      (.pop 99 356 319)))))))

def program : Stmt 400 128 := .seq load (.seq decoder parse)

attribute [local irreducible] decoder SeedBits.program

theorem load_context (N : ℕ) (bits : List Bool) (st : State 400 128)
    (hd : Data N st) (hb : st.lists 101 = bits.map Bool.toNat) :
    SeedBits.Context (size (exponent N)) (size (exponent N)) 4
      (binaryDimension (exponent N)) bits
      ((load.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [load, Stmt.run, Expr.eval, Function.update, State.restrict,
      hd.dimension, hd.width]
  · simpa [load, Stmt.run, Expr.eval, Function.update, State.restrict] using hb
  · simpa [load, Stmt.run, Expr.eval, Function.update, State.restrict] using hd.empty

theorem parse_run (f : Fin 7 → ℕ) (st : State 400 128)
    (h : st.lists 1 = List.ofFn f) (i : Fin 7) :
    (parse.run st).1.regs (port i) = f i := by
  fin_cases i <;> simp [parse, Stmt.run, Function.update, h, List.ofFn_succ, port]

theorem program_run (N : ℕ) (bits : List Bool) (st : State 400 128)
    (hd : Data N st) (hb : st.lists 101 = bits.map Bool.toNat) :
    Seeds N bits (program.run st).1 := by
  have h := SeedBits.program_bits (coordinates (exponent N))
    (size (exponent N)) (size (exponent N)) 4 bits _ (load_context N bits st hd hb)
  rw [← call_result (by decide) (by decide) SeedBits.program (load.run st).1] at h
  have h' : (decoder.run (load.run st).1).1.lists 1 = List.ofFn (codes N bits) := by
    unfold ThreeColorBaseSeed.codes ThreeColorBaseSeed.sample
    unfold decoder
    exact h
  simp only [program, run_seq_fst]
  exact parse_run (codes N bits) _ h'

theorem program_frame (st : State 400 128) : ThreeColorBaseSetup.Frame st (program.run st).1 := by
  have hl := frame_of_writes load (by simp [load, Stmt.regWrites])
    (by simp [load, Stmt.listWrites]) st
  have hd := call_frame (by decide) (by decide) SeedBits.program (load.run st).1
  have hp := frame_of_writes parse (by simp [parse, Stmt.regWrites])
    (by simp [parse, Stmt.listWrites]) (decoder.run (load.run st).1).1
  apply hl.trans
  apply (show ThreeColorBaseSetup.Frame (load.run st).1 (decoder.run (load.run st).1).1 from by
    simpa only [decoder] using hd).trans
  exact hp

end PCP.Lang.ThreeColorBaseSeed
