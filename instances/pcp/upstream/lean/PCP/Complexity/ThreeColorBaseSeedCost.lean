import PCP.Complexity.ThreeColorBaseSeed

/-! # Input-polynomial charged cost of all seven actual sampler codes -/

namespace PCP.Lang.ThreeColorBaseSeed

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters ThreeColorSeedIndex
  ThreeColorBaseSetup CanonicalResourceBounds

theorem code_size (N : ℕ) (bits : List Bool) (i : Fin 7) :
    Nat.size (codes N bits i) ≤ 32000000*(N+1) := by
  have hi := ((branchCodec (coordinates (exponent N)) (size (exponent N))
    (size (exponent N)) 4 i).equiv (sample N bits i)).isLt
  change codes N bits i < _ at hi
  rw [SeedArithmetic.branchCodec_size] at hi
  exact (Nat.size_le.mpr hi).trans (branch_bits N i)

theorem codes_listSize (N : ℕ) (bits : List Bool) :
    listSize (List.ofFn (codes N bits)) ≤ 7*(32000000*(N+1)+1) := by
  unfold listSize
  rw [List.map_ofFn, List.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin 7, (32000000*(N+1)+1) :=
      Finset.sum_le_sum (fun i _ => Nat.add_le_add_right (code_size N bits i) 1)
    _ = 7*(32000000*(N+1)+1) := by simp

def loadConstant : ℕ := load.C*(load.width+load.csize+1)

theorem load_cost (N : ℕ) (bits : List Bool) (st : State 400 128)
    (hd : Data N st) (hb : st.lists 101 = bits.map Bool.toNat) :
    (load.run st).2 ≤ loadConstant*(coreBound N+2*bits.length+5) := by
  obtain ⟨_, ht, hn, _⟩ := core_bounds N
  apply loopFree_cost_le load (by decide) st (coreBound N+2*bits.length+4)
  · intro i hi
    have he : i = 322 ∨ i = 324 := by
      simpa [load, Stmt.uses, Stmt.mustW, Expr.uses] using hi
    rcases he with rfl | rfl
    · rw [hd.dimension]; exact (size_le_self _).trans (hn.trans (by omega))
    · rw [hd.width]; exact (size_le_self _).trans (ht.trans (by omega))
  · intro L hL
    have he : L = 101 ∨ L = 122 := by simpa [load, Stmt.lUses] using hL
    rcases he with rfl | rfl
    · rw [hb]; exact (ThreeColorContext.bitList_size bits).trans (by omega)
    · rw [hd.empty]; exact Nat.zero_le _

theorem parse_cost (f : Fin 7 → ℕ) (st : State 400 128)
    (h : st.lists 1 = List.ofFn f) :
    (parse.run st).2 = 2*listSize (List.ofFn f)+8 := by
  simp [parse, Stmt.run, Function.update, h, List.ofFn_succ, listSize]
  ring

attribute [local irreducible] decoder SeedBits.program coreConstant loadConstant

def costConstant : ℕ := loadConstant*(coreConstant+7)+
  SeedBits.programConstant*(coreConstant+32000006)^2+448000025

theorem program_cost (N : ℕ) (bits : List Bool) (st : State 400 128)
    (hd : Data N st) (hb : st.lists 101 = bits.map Bool.toNat) :
    (program.run st).2 ≤ costConstant*(N+bits.length+1)^24 := by
  obtain ⟨hcore, ht, hn, _⟩ := core_bounds N
  change binaryDimension (exponent N) ≤ coreBound N at ht
  change size (exponent N) ≤ coreBound N at hn
  let A := N+bits.length+1
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hlin : A ≤ A^12 := Nat.le_pow (by decide)
  have hbA : bits.length ≤ A^12 := (by dsimp [A]; omega : bits.length ≤ A).trans hlin
  have hnA : N+1 ≤ A^12 := (by dsimp [A]; omega : N+1 ≤ A).trans hlin
  have h12 : A^12 ≤ A^24 := Nat.pow_le_pow_right hA (by decide)
  have h1 : 1 ≤ A^12 := Nat.one_le_pow _ _ hA
  have h24 : 1 ≤ A^24 := Nat.one_le_pow _ _ hA
  have hcoreA : coreBound N ≤ coreConstant*A^12 := by
    unfold coreBound
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [A]; omega) 12)
  have hload := load_cost N bits st hd hb
  have hloadArg : coreBound N+2*bits.length+5 ≤ (coreConstant+7)*A^12 := by
    nlinarith only [hcoreA,hbA,hnA,h1]
  have hload' := hload.trans ((Nat.mul_le_mul_left _ hloadArg).trans
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h12)))
  have hparam : ∀ i : Fin 4, Nat.size (![size (exponent N),size (exponent N),4,
      binaryDimension (exponent N)] i) ≤ coreBound N+bits.length+4 := by
    intro i
    fin_cases i <;> apply (size_le_self _).trans <;> dsimp <;> omega
  have hdecode := SeedBits.program_cost (size (exponent N)) (size (exponent N)) 4
    (binaryDimension (exponent N)) (32000000*(N+1)) (coreBound N+bits.length+4)
    bits _ (load_context N bits st hd hb) hparam (branch_bits N) (by omega)
  rw [← call_result (by decide) (by decide) SeedBits.program] at hdecode
  rw [show call (by decide) (by decide) SeedBits.program = decoder by
    unfold decoder; rfl] at hdecode
  have harg : 32000000*(N+1)+(coreBound N+bits.length+4)+1 ≤
      (coreConstant+32000006)*A^12 := by
    nlinarith only [hcoreA,hbA,hnA,h1]
  have hdecode' := hdecode.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 2))
  have hout := SeedBits.program_bits (coordinates (exponent N))
    (size (exponent N)) (size (exponent N)) 4 bits _ (load_context N bits st hd hb)
  rw [← call_result (by decide) (by decide) SeedBits.program] at hout
  have hout' : (decoder.run (load.run st).1).1.lists 1 = List.ofFn (codes N bits) := by
    unfold codes sample decoder
    exact hout
  have hparse := parse_cost (codes N bits) _ hout'
  have hls := codes_listSize N bits
  have hparse' : (parse.run (decoder.run (load.run st).1).1).2 ≤ 448000022*A^24 := by
    rw [hparse]
    have hl : N+1 ≤ A^24 := (by dsimp [A]; omega : N+1 ≤ A).trans
      (Nat.le_pow (by decide))
    nlinarith only [hls,hl,h24]
  simp only [program, run_seq_snd]
  change _ ≤ costConstant*A^24
  unfold costConstant
  nlinarith only [hload',hdecode',hparse',h24]

theorem program_input_cost (x bits : List Bool) (st : State 400 128)
    (hd : Data (ThreeColorEncoding.vertexCount x) st)
    (hb : st.lists 101 = bits.map Bool.toNat) :
    (program.run st).2 ≤ costConstant*(x.length+bits.length+1)^24 :=
  (program_cost _ bits st hd hb).trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (by have := ThreeColorEncoding.size_le_length x; omega) 24))

end PCP.Lang.ThreeColorBaseSeed
