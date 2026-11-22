import PCP.Complexity.ThreeColorBaseSetup

/-! # Charged input-polynomial cost of the public base-verifier setup -/

namespace PCP.Lang.ThreeColorBaseSetup

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters

def saveConstant : ℕ := save.C*(save.width+save.csize+1)

theorem save_cost (N : ℕ) (st : State 400 128)
    (hc : ThreeColorContext.Prepared N
      (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))) :
    (save.run st).2 ≤ saveConstant*(40*(N+1)+10*(2^binaryDimension (exponent N)+1)+1) := by
  rcases hc with ⟨⟨hN, ha, hn, hv, ht⟩, ⟨⟨_, _, hmod, _⟩, hq, hc, hf⟩, hnodes⟩
  change st.regs 42 = N at hN
  change st.regs 43 = _ at ha
  change st.regs 44 = _ at hn
  change st.regs 45 = _ at hv
  change st.regs 46 = _ at ht
  change st.regs 47 = _ at hq
  change st.regs 48 = _ at hc
  change st.regs 49 = _ at hf
  change st.lists 3 = _ at hmod
  change st.lists 14 = _ at hnodes
  let t := binaryDimension (exponent N)
  let q := 2^t
  let W := 40*(N+1)+10*(q+1)
  have hmeta := ThreeColorParameter.candidate_bound N (exponent N) (exponent_ge_two N) le_rfl
  have htw : t ≤ q := Nat.lt_two_pow_self.le
  have hcore : N ≤ W ∧ 32*(N+1) ≤ W ∧ q ≤ W ∧ 2*t ≤ W ∧ 5*(t+1) ≤ W := by
    dsimp only [W]
    omega
  have hbits : listSize (BinaryField.encode (BinaryWordMaterialization.modulus t)) ≤ 2*t := by
    simpa only [BinaryField.encode_length] using
      BinaryField.listSize_bits (BinaryField.encode_bits (BinaryWordMaterialization.modulus t))
  have hnodesSize : listSize (List.ofFn (fun i : Fin 5 =>
      (fieldCode (exponent N) (ThreeColorParameters.nodes (exponent N) i)).val)) ≤ 5*(t+1) := by
    unfold listSize
    rw [List.map_ofFn, List.sum_ofFn]
    calc
      _ ≤ ∑ _i : Fin 5, (t+1) := Finset.sum_le_sum (fun i _ => by
        have hh := Nat.size_le.mpr (fieldCode (exponent N)
          (ThreeColorParameters.nodes (exponent N) i)).isLt
        exact Nat.add_le_add_right hh 1)
      _ = 5*(t+1) := by simp
  apply loopFree_cost_le save (by decide) st W
  · intro i hi
    have he : i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 := by
      simpa [save, Stmt.uses, Stmt.mustW, Expr.uses] using hi
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hN]; exact (size_le_self _).trans hcore.1
    · rw [ha]; exact (size_le_self _).trans (hmeta.1.trans hcore.2.1)
    · rw [hn]; exact (size_le_self _).trans (hmeta.2.1.trans hcore.2.1)
    · rw [hv]; exact (size_le_self _).trans (hmeta.2.2.trans hcore.2.1)
    · rw [ht]; exact (size_le_self _).trans (htw.trans hcore.2.2.1)
    · rw [hq]; exact (size_le_self _).trans hcore.2.2.1
    · rw [hc]; exact (size_le_self _).trans ((Fin.isLt _).le.trans hcore.2.2.1)
    · rw [hf]; exact (size_le_self _).trans ((Fin.isLt _).le.trans hcore.2.2.1)
  · intro L hL
    have he : L = 3 ∨ L = 14 := by
      simpa [save, Stmt.lUses] using hL
    rcases he with rfl | rfl
    · rw [hmod]; exact hbits.trans hcore.2.2.2.1
    · rw [hnodes]; exact hnodesSize.trans hcore.2.2.2.2

def costConstant : ℕ := ThreeColorContext.setupCostConstant+
  saveConstant*(10*ThreeColorContext.fieldConstant+51)+7

attribute [local irreducible] fieldCall ThreeColorContext.setup ThreeColorContext.fieldConstant
  ThreeColorContext.setupCostConstant saveConstant

theorem field_cost (x : List Bool) (st : State 400 128)
    (hx : st.lists 100 = x.map Bool.toNat) (he : st.lists 122 = []) :
    (field.run st).2 ≤ costConstant*(x.length+1)^84 := by
  have hload : (load.run st).2 ≤ 2*x.length+3 := by
    have hh := ThreeColorContext.bitList_size x
    simp [load, Stmt.run, hx, he, listSize]
    simpa only [listSize, List.map_map] using hh
  have hl : (load.run st).1.lists 11 = x.map Bool.toNat ∧ (load.run st).1.lists 7 = [] := by
    simp [load, Stmt.run, Function.update, hx, he]
  have hsetup := ThreeColorContext.setup_cost x
    ((load.run st).1.restrict (Fin.castLE (by decide : 50 ≤ 400))
      (Fin.castLE (by decide : 15 ≤ 128)))
    (by change (load.run st).1.lists 11 = _; exact hl.1)
    (by change (load.run st).1.lists 7 = _; exact hl.2)
  rw [← call_result (by decide) (by decide) ThreeColorContext.setup] at hsetup
  rw [show call (by decide) (by decide) ThreeColorContext.setup = fieldCall by
    unfold fieldCall; rfl] at hsetup
  have hsave := save_cost (ThreeColorEncoding.vertexCount x) _
    (fieldCall_run x _ hl.1 hl.2)
  have hq := ThreeColorContext.field_cardinality_bound (ThreeColorEncoding.vertexCount x)
  have hN := ThreeColorEncoding.size_le_length x
  have hpow12 := Nat.pow_le_pow_left (Nat.add_le_add_right hN 1) 12
  have hq' := hq.trans (Nat.mul_le_mul_left _ hpow12)
  have hpow : (x.length+1)^12 ≤ (x.length+1)^84 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hlin : x.length+1 ≤ (x.length+1)^84 := Nat.le_pow (by decide)
  have h1 : 1 ≤ (x.length+1)^84 := Nat.one_le_pow _ _ (by omega)
  have hq'' := hq'.trans (Nat.mul_le_mul_left _ hpow)
  have harg : 40*(ThreeColorEncoding.vertexCount x+1)+
      10*(2^binaryDimension (exponent (ThreeColorEncoding.vertexCount x))+1)+1 ≤
      (10*ThreeColorContext.fieldConstant+51)*(x.length+1)^84 := by
    nlinarith only [hN,hq'',hlin,h1]
  have hsave' := hsave.trans (Nat.mul_le_mul_left _ harg)
  simp only [field, run_seq_snd]
  unfold costConstant
  nlinarith only [hload,hsetup,hsave',hlin,h1]

end PCP.Lang.ThreeColorBaseSetup
