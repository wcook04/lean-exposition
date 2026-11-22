import PCP.Complexity.ThreeColorSetupLang
import PCP.Complexity.ThreeColorContextCost
import PCP.Complexity.ThreeColorFieldSetupCost
import PCP.Complexity.ThreeColorNodeSetupCost

/-!
# Input-length polynomial time for complete production field setup

The modulus and roots are constructed by actual searches. Their cardinality
cost is polynomial in input length because the chosen field has size bounded
by a constant times the twelfth power of the public graph size plus one.
-/

namespace PCP.Lang.ThreeColorContext

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters

def fieldConstant : ℕ := 2 ^ 32 * 32 ^ 12

theorem field_cardinality_bound (N : ℕ) :
    2 ^ binaryDimension (exponent N) ≤ fieldConstant * (N + 1) ^ 12 := by
  have hn := (ThreeColorParameter.candidate_bound N (exponent N)
    (exponent_ge_two N) le_rfl).2.1
  have hq : 2 ^ binaryDimension (exponent N) = 2 ^ 32 * (size (exponent N)) ^ 12 := by
    rw [← card_field, card_field_pow_two, binaryDimension_eq]
  rw [hq]
  calc
    _ ≤ 2 ^ 32 * (32 * (N + 1)) ^ 12 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 12)
    _ = fieldConstant * (N + 1) ^ 12 := by rw [mul_pow, fieldConstant, Nat.mul_assoc]

def preparationConstant : ℕ := metadataConstant + 1300000002

theorem prepare_cost (N : ℕ) (st : State 50 15) (hN : st.regs 42 = N)
    (he : st.lists 7 = []) :
    (prepare.run st).2 ≤ preparationConstant * (N + 2 ^ binaryDimension (exponent N) + 4) ^ 7 := by
  have hm := metadata_run N st hN
  have hmc := metadata_cost N st hN
  have h7 := (metadata_lists st 7).trans he
  generalize hu : (metadata.run st).1 = u at *
  have hr := roots_run (exponent N) u hm.2 h7
  have hrc := roots_cost (exponent N) u hm.2 h7
  generalize hv : (roots.run u).1 = v at *
  have hnc := storeNodes_cost (exponent N) v hr
  let B := N + 2 ^ binaryDimension (exponent N) + 4
  have hB : 1 ≤ B := (by decide : 1 ≤ 4).trans (Nat.le_add_left _ _)
  have hNB : N + 1 ≤ B := Nat.add_le_add (Nat.le_add_right _ _) (by decide : 1 ≤ 4)
  have hqB : 2 ^ binaryDimension (exponent N) + 4 ≤ B :=
    Nat.add_le_add_right (Nat.le_add_left _ _) 4
  have hm2 : (N + 1) ^ 2 ≤ B ^ 7 :=
    (Nat.pow_le_pow_left hNB 2).trans
      (Nat.pow_le_pow_right hB (by decide))
  have hr7 : (2 ^ binaryDimension (exponent N) + 4) ^ 7 ≤ B ^ 7 :=
    Nat.pow_le_pow_left hqB 7
  have hn4 : (2 ^ binaryDimension (exponent N) + 4) ^ 4 ≤ B ^ 7 :=
    (Nat.pow_le_pow_left hqB 4).trans
      (Nat.pow_le_pow_right hB (by decide))
  have hmc' := hmc.trans (Nat.mul_le_mul_left _ hm2)
  have hrc' := hrc.trans (Nat.mul_le_mul_left _ hr7)
  have hnc' := hnc.trans (Nat.mul_le_mul_left _ hn4)
  have hone : 1 ≤ B ^ 7 := one_le_pow₀ hB
  simp only [prepare, run_seq_snd, hu, hv]
  change _ ≤ preparationConstant * B ^ 7
  dsimp only [preparationConstant]
  nlinarith

def preparedCostConstant : ℕ := preparationConstant * (fieldConstant + 5) ^ 7

theorem prepare_polynomial_cost (N : ℕ) (st : State 50 15) (hN : st.regs 42 = N)
    (he : st.lists 7 = []) :
    (prepare.run st).2 ≤ preparedCostConstant * (N + 1) ^ 84 := by
  have hp := prepare_cost N st hN he
  have hq := field_cardinality_bound N
  have hn : N + 1 ≤ (N + 1) ^ 12 := le_self_pow₀ (by omega) (by decide)
  have hsum : N + 2 ^ binaryDimension (exponent N) + 4 ≤
      (fieldConstant + 5) * (N + 1) ^ 12 := by nlinarith
  apply hp.trans
  calc
    _ ≤ preparationConstant * ((fieldConstant + 5) * (N + 1) ^ 12) ^ 7 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 7)
    _ = preparedCostConstant * (N + 1) ^ 84 := by
      rw [mul_pow, ← pow_mul, preparedCostConstant, Nat.mul_assoc]

theorem bitList_size (x : List Bool) : listSize (x.map Bool.toNat) ≤ 2 * x.length := by
  induction x with
  | nil => simp [listSize]
  | cons b x ih =>
    cases b <;> simp only [List.map_cons, Bool.toNat_false, Bool.toNat_true,
      listSize, List.sum_cons, Nat.size_zero, Nat.size_one, List.length_cons] at ih ⊢ <;> omega

theorem header_cost (x : List Bool) (st : State 50 15)
    (hx : st.lists 11 = x.map Bool.toNat) :
    (header.run st).2 ≤ 400 * (x.length + 1) ^ 2 := by
  have hb : ∀ v ∈ (st.restrict headerRegs headerLists).lists 0, v ≤ 1 := by
    change ∀ v ∈ st.lists 11, v ≤ 1
    rw [hx]
    intro v hv
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hv
    cases b <;> decide
  have hc := GraphHeader.program_cost (st.restrict headerRegs headerLists) hb
  have ht := GraphHeader.program.run_rename_cost headerRegs headerLists
    (Fin.castAdd_injective _ _) headerLists_injective st
  change (header.run st).2 = _ at ht
  rw [← ht] at hc
  change (header.run st).2 ≤ 100 * (listSize (st.lists 11) + 1) ^ 2 at hc
  rw [hx] at hc
  have hs := bitList_size x
  nlinarith

def setupCostConstant : ℕ := preparedCostConstant + 410

/-- Header decoding, dimensions, modulus, roots, and nodes all run in input-polynomial time. -/
theorem setup_cost (x : List Bool) (st : State 50 15)
    (hx : st.lists 11 = x.map Bool.toNat) (he : st.lists 7 = []) :
    (setup.run st).2 ≤ setupCostConstant * (x.length + 1) ^ 84 := by
  have hn := header_run x st hx
  have hhc := header_cost x st hx
  have h7 := (header_lists st 7 (by decide)).trans he
  generalize hu : (header.run st).1 = u at *
  have hpc := prepare_polynomial_cost (ThreeColorEncoding.vertexCount x)
    (setReg u 42 (u.regs 1)) (by simpa using hn) h7
  have hlen := ThreeColorEncoding.size_le_length x
  have hpc' := hpc.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) 84))
  have hs : Nat.size (u.regs 1) ≤ x.length := by
    rw [hn]
    exact (size_le_self _).trans hlen
  have hpow2 : (x.length + 1) ^ 2 ≤ (x.length + 1) ^ 84 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hhc' := hhc.trans (Nat.mul_le_mul_left _ hpow2)
  have hlin : x.length + 1 ≤ (x.length + 1) ^ 84 := le_self_pow₀ (by omega) (by decide)
  simp only [setup, run_seq_snd, run_assign_fst, Expr.eval, hu]
  change (header.run st).2 + ((Expr.var 1).cost u.regs +
    (prepare.run (setReg u 42 (u.regs 1))).2 + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval]
  dsimp only [setupCostConstant]
  nlinarith

end PCP.Lang.ThreeColorContext
