import PCP.Complexity.ThreeColorSeedGuardDerivedCost
import PCP.Complexity.ThreeColorBaseSeedCost

/-! Polynomial charged cost of the four-zero guard on the actual canonical seed. -/

set_option maxRecDepth 1024

namespace PCP.Lang.ThreeColorSeedGuard

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling ThreeColorBaseSetup
  ThreeColorParameterChoice ThreeColorParameters CanonicalResourceBounds

variable {t n : ℕ} [NeZero t]

local notation "F" => BinaryMaterializedField.Element t
local notation "ρ" => BinaryMaterializedField.coordinates t

def finishConstant : ℕ := finish.C * (finish.width + finish.csize + 1)

def guardConstant : ℕ :=
  readDerivedConstant 1 354 + readDerivedConstant 2 355 + 2 * finishConstant + 2

attribute [local irreducible] readDerived parameters finishConstant program

theorem parameters_cost (s : RawSample F n n 4 t) (st : State 400 128) (W : ℕ)
    (hn : st.regs 322 = n) (ht : st.regs 324 = t) (he : st.lists 122 = [])
    (hs : SeedSources s st)
    (h4 : t + 2 * n + n + 2 ^ t + Nat.size ((derivedCodec ρ n n 4 3).equiv (s 4)).val + 5 ≤ W)
    (h5 : t + 2 * (n + n) + n + 2 ^ t +
      Nat.size ((derivedCodec ρ (n + n) n 4 3).equiv (s 5)).val + 5 ≤ W) :
    (parameters.run st).2 ≤ (readDerivedConstant 1 354 + readDerivedConstant 2 355 + 1) * W^4 := by
  have hv := readDerived_cost_dim (n := n) ρ 1 n (one_mul n) (s 4) 354 360 361 st W
    hn ht he (by decide) (by decide) (by decide) (by decide) hs.1 h4
  have hun := (readDerived_reg 1 354 360 361 322 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) st).trans hn
  have hut := (readDerived_reg 1 354 360 361 324 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) st).trans ht
  have hue := (readDerived_list 1 354 360 361 122 (by decide) st).trans he
  have hus := (readDerived_reg 1 354 360 361 355 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) st).trans hs.2
  generalize hU : ((readDerived 1 354 360 361).run st).1 = u at *
  have hp := readDerived_cost_dim (n := n) ρ 2 (n + n) (two_mul n) (s 5) 355 362 363 u W
    hun hut hue (by decide) (by decide) (by decide) (by decide) hus h5
  have hq := Nat.two_pow_pos t
  have hW : 1 ≤ W^4 := Nat.one_le_pow _ _ (by omega)
  simp only [parameters,run_seq_snd,hU]
  nlinarith only [hv,hp,hW]

omit [NeZero t] in
theorem finish_cost (st : State 400 128) (W : ℕ)
    (h : ∀ i : Fin 400, 360 ≤ i.val → i.val < 364 → Nat.size (st.regs i) ≤ W) :
    (finish.run st).2 ≤ finishConstant * (W + 1) := by
  unfold finishConstant
  apply loopFree_cost_le finish (by decide) st W
  · intro i hi
    have hi' : i = 360 ∨ i = 361 ∨ i = 362 ∨ i = 363 := by
      simpa [finish, Stmt.uses, Stmt.mustW, Expr.uses] using hi
    rcases hi' with rfl | rfl | rfl | rfl <;> exact h _ (by decide) (by decide)
  · simp [finish, Stmt.lUses]

theorem generic_cost (s : RawSample F n n 4 t) (st : State 400 128) (W : ℕ)
    (hn : st.regs 322 = n) (ht : st.regs 324 = t) (he : st.lists 122 = [])
    (hs : SeedSources s st)
    (h4 : t + 2 * n + n + 2 ^ t + Nat.size ((derivedCodec ρ n n 4 3).equiv (s 4)).val + 5 ≤ W)
    (h5 : t + 2 * (n + n) + n + 2 ^ t +
      Nat.size ((derivedCodec ρ (n + n) n 4 3).equiv (s 5)).val + 5 ≤ W) :
    (program.run st).2 ≤ guardConstant * W^4 := by
  have hc := parameters_cost s st W hn ht he hs h4 h5
  have hp := parameters_run s st hn ht he hs
  have hf := finish_cost (parameters.run st).1 t (by
    intro i hi hj
    have hx : i = 360 ∨ i = 361 ∨ i = 362 ∨ i = 363 := by omega
    rcases hx with rfl | rfl | rfl | rfl
    · rw [hp.1]; exact Nat.size_le.mpr (BinaryFieldCode.fieldEquiv t _).isLt
    · rw [hp.2.1]; exact Nat.size_le.mpr (BinaryFieldCode.fieldEquiv t _).isLt
    · rw [hp.2.2.1]; exact Nat.size_le.mpr (BinaryFieldCode.fieldEquiv t _).isLt
    · rw [hp.2.2.2]; exact Nat.size_le.mpr (BinaryFieldCode.fieldEquiv t _).isLt)
  have hq := Nat.two_pow_pos t
  have hW : 1 ≤ W := by omega
  have htW : t + 1 ≤ 2 * W^4 := by
    have : W ≤ W^4 := Nat.le_pow (by decide)
    omega
  have hf' := hf.trans (Nat.mul_le_mul_left _ htW)
  have hpow : 1 ≤ W^4 := Nat.one_le_pow _ _ hW
  simp only [program,run_seq_snd]
  unfold guardConstant
  nlinarith only [hc,hf',hpow]

def budgetConstant : ℕ := 7 * coreConstant + 32000005

def costConstant : ℕ := guardConstant * budgetConstant^4

theorem program_cost (N : ℕ) (bits : List Bool) (st : State 400 128)
    (hd : Data N st) (hs : ThreeColorBaseSeed.Seeds N bits st) :
    (program.run st).2 ≤ costConstant * (N + 1)^48 := by
  let W := budgetConstant * (N + 1)^12
  obtain ⟨_, ht, hn, hq⟩ := core_bounds N
  change binaryDimension (exponent N) ≤ coreBound N at ht
  change size (exponent N) ≤ coreBound N at hn
  change 2^(binaryDimension (exponent N)) ≤ coreBound N at hq
  have h1 : 1 ≤ (N + 1)^12 := Nat.one_le_pow _ _ (by omega)
  have hlin : N + 1 ≤ (N + 1)^12 := Nat.le_pow (by decide)
  have h4 := ThreeColorBaseSeed.code_size N bits 4
  have h5 := ThreeColorBaseSeed.code_size N bits 5
  change Nat.size ((derivedCodec (coordinates (exponent N))
    (size (exponent N)) (size (exponent N)) 4 3).equiv
      (ThreeColorBaseSeed.sample N bits 4)).val ≤ _ at h4
  change Nat.size ((derivedCodec (coordinates (exponent N))
    (size (exponent N) + size (exponent N)) (size (exponent N)) 4 3).equiv
      (ThreeColorBaseSeed.sample N bits 5)).val ≤ _ at h5
  have h := generic_cost (ThreeColorBaseSeed.sample N bits) st W
    hd.dimension hd.width hd.empty ⟨hs 4,hs 5⟩ (by
      change binaryDimension (exponent N) + 2 * size (exponent N) + size (exponent N) +
        2 ^ binaryDimension (exponent N) + Nat.size ((derivedCodec (coordinates (exponent N))
          (size (exponent N)) (size (exponent N)) 4 3).equiv
            (ThreeColorBaseSeed.sample N bits 4)).val + 5 ≤ W
      dsimp only [W,budgetConstant]
      unfold coreBound at ht hn hq
      nlinarith only [ht,hn,hq,h4,h1,hlin]) (by
      change binaryDimension (exponent N) + 2 * (size (exponent N) + size (exponent N)) +
        size (exponent N) + 2 ^ binaryDimension (exponent N) +
          Nat.size ((derivedCodec (coordinates (exponent N))
            (size (exponent N) + size (exponent N)) (size (exponent N)) 4 3).equiv
              (ThreeColorBaseSeed.sample N bits 5)).val + 5 ≤ W
      dsimp only [W,budgetConstant]
      unfold coreBound at ht hn hq
      nlinarith only [ht,hn,hq,h5,h1,hlin])
  have heq : guardConstant * W^4 = costConstant * (N+1)^48 := by
    dsimp only [W, costConstant]
    rw [mul_pow, ← pow_mul, ← Nat.mul_assoc]
  rw [heq] at h
  exact h

theorem program_input_cost (x bits : List Bool) (st : State 400 128)
    (hd : Data (ThreeColorEncoding.vertexCount x) st)
    (hs : ThreeColorBaseSeed.Seeds (ThreeColorEncoding.vertexCount x) bits st) :
    (program.run st).2 ≤ costConstant * (x.length + 1)^48 :=
  (program_cost _ bits st hd hs).trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (by have := ThreeColorEncoding.size_le_length x; omega) 48))

end PCP.Lang.ThreeColorSeedGuard
