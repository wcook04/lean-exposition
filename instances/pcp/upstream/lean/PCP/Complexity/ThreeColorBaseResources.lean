import PCP.Complexity.ThreeColorBaseSeedCost
import PCP.Complexity.ThreeColorBaseCardinalCost

/-! # Uniform size bounds for permanent base-verifier metadata and sampler codes -/

namespace PCP.Lang.ThreeColorBaseResources

open PCP.Algebraic ThreeColorParameterChoice ThreeColorParameters CanonicalResourceBounds
  ThreeColorBaseSetup ThreeColorBaseCardinal

def metadataWidth (N : ℕ) : ℕ := 100000000*(coreBound N+N+1)^2

def metadataConstant : ℕ := 100000000*(coreConstant+1)^2

theorem metadataWidth_bound (N : ℕ) :
    metadataWidth N ≤ metadataConstant*(N+1)^24 := by
  have hlin : N+1 ≤ (N+1)^12 := Nat.le_pow (by decide)
  have hsum : coreBound N+N+1 ≤ (coreConstant+1)*(N+1)^12 := by
    unfold coreBound
    nlinarith only [hlin]
  exact (Nat.mul_le_mul_left 100000000 (Nat.pow_le_pow_left hsum 2)).trans_eq (by
    rw [mul_pow, ← pow_mul]
    unfold metadataConstant
    ring)

theorem metadataWidth_input (x : List Bool) :
    metadataWidth (ThreeColorEncoding.vertexCount x) ≤ metadataConstant*(x.length+1)^24 :=
  (metadataWidth_bound _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.add_le_add_right (ThreeColorEncoding.size_le_length x) 1) 24))

theorem metadata_basic (N : ℕ) :
    32*(N+1) ≤ metadataWidth N ∧ 4*dimension N+4 ≤ metadataWidth N ∧
    10*(fieldWidth N+1) ≤ metadataWidth N ∧ 2^fieldWidth N+1 ≤ metadataWidth N ∧
    4*fieldWidth N*dimension N+1 ≤ metadataWidth N ∧
    32000000*(N+1) ≤ metadataWidth N := by
  obtain ⟨hB, ht, hn, hq⟩ := core_bounds N
  let H := coreBound N+N+1
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hN : N+1 ≤ H := by dsimp [H]; omega
  have htH : fieldWidth N ≤ H := ht.trans (by dsimp [H]; omega)
  have hnH : dimension N ≤ H := hn.trans (by dsimp [H]; omega)
  have hqH : 2^fieldWidth N ≤ H := hq.trans (by dsimp [H]; omega)
  have hlin : H ≤ H^2 := Nat.le_pow (by decide)
  have h1 : 1 ≤ H^2 := Nat.one_le_pow _ _ hH
  have hmul := Nat.mul_le_mul htH hnH
  change _ ≤ 100000000*H^2 ∧ _ ≤ 100000000*H^2 ∧ _ ≤ 100000000*H^2 ∧
    _ ≤ 100000000*H^2 ∧ _ ≤ 100000000*H^2 ∧ _ ≤ 100000000*H^2
  constructor
  · nlinarith only [hN,hlin]
  constructor
  · nlinarith only [hnH,hlin,h1]
  constructor
  · nlinarith only [htH,hlin,h1]
  constructor
  · nlinarith only [hqH,hlin,h1]
  constructor
  · nlinarith only [hmul,h1]
  · nlinarith only [hN,hlin]

theorem data_regs (N : ℕ) (st : State 400 128) (hd : Data N st)
    (i : Fin 400) (hi : 320 ≤ i.val) (hj : i.val < 328) :
    Nat.size (st.regs i) ≤ metadataWidth N := by
  have hb := metadata_basic N
  change 32*(N+1) ≤ metadataWidth N ∧ 4*size (exponent N)+4 ≤ metadataWidth N ∧
    10*(binaryDimension (exponent N)+1) ≤ metadataWidth N ∧
    2^binaryDimension (exponent N)+1 ≤ metadataWidth N ∧
    4*binaryDimension (exponent N)*size (exponent N)+1 ≤ metadataWidth N ∧
    32000000*(N+1) ≤ metadataWidth N at hb
  have hc := ThreeColorParameter.candidate_bound N (exponent N) (exponent_ge_two N) le_rfl
  have he : i = 320 ∨ i = 321 ∨ i = 322 ∨ i = 323 ∨ i = 324 ∨ i = 325 ∨
      i = 326 ∨ i = 327 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hd.order]; exact (size_le_self _).trans (by omega)
  · rw [hd.exponent]; exact (size_le_self _).trans (hc.1.trans hb.1)
  · rw [hd.dimension]; exact (size_le_self _).trans (hc.2.1.trans hb.1)
  · rw [hd.volume]; exact (size_le_self _).trans (hc.2.2.trans hb.1)
  · rw [hd.width]; exact (size_le_self _).trans (by have := hb.2.2.1; omega)
  · rw [hd.card, Nat.size_pow]; exact (by have := hb.2.2.1; omega)
  · rw [hd.cube]
    exact (Nat.size_le.mpr (fieldCode (exponent N) (cubeRoot (exponent N))).isLt).trans
      (by have := hb.2.2.1; omega)
  · rw [hd.generatorCode]
    exact (Nat.size_le.mpr (fieldCode (exponent N) (generator (exponent N))).isLt).trans
      (by have := hb.2.2.1; omega)

theorem cardinal_regs (N : ℕ) (st : State 400 128)
    (hc : Cardinal (fieldWidth N) (dimension N) st)
    (i : Fin 400) (hi : 328 ≤ i.val) (hj : i.val < 334) :
    Nat.size (st.regs i) ≤ metadataWidth N := by
  have hb := metadata_basic N
  have hpow (d : ℕ) (hd : d ≤ 4*dimension N) :
      Nat.size ((2^fieldWidth N)^d) ≤ metadataWidth N := by
    rw [← pow_mul, Nat.size_pow]
    have hh := Nat.mul_le_mul_left (fieldWidth N) hd
    nlinarith only [hh,hb.2.2.2.2.1]
  have hl (r : ℕ) : Nat.size (2^BooleanCoefficientIndex.dimension (fieldWidth N) r) ≤
      metadataWidth N := (HadamardSeed.cardinal_size _ _).trans hb.2.2.2.1
  have he : i = 328 ∨ i = 329 ∨ i = 330 ∨ i = 331 ∨ i = 332 ∨ i = 333 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hc.vertices]; exact hpow _ (by omega)
  · rw [hc.pairs]; exact hpow _ (by omega)
  · rw [hc.proper]; exact hpow _ (by omega)
  · rw [hc.inner]; exact hpow _ (by omega)
  · rw [hc.affine]; exact hl _
  · rw [hc.cubic]; exact hl _

theorem seed_regs (N : ℕ) (bits : List Bool) (st : State 400 128)
    (hs : ThreeColorBaseSeed.Seeds N bits st)
    (i : Fin 400) (hi : 350 ≤ i.val) (hj : i.val < 357) :
    Nat.size (st.regs i) ≤ metadataWidth N := by
  let j : Fin 7 := ⟨i.val-350, by omega⟩
  have he : ThreeColorBaseSeed.port j = i := by
    apply Fin.ext; simp only [ThreeColorBaseSeed.port,j]; omega
  rw [← he, hs j]
  exact (ThreeColorBaseSeed.code_size N bits j).trans (metadata_basic N).2.2.2.2.2

theorem fieldCodes_size {α : Type*} {t : ℕ} (e : α ≃ Fin (2 ^ t)) (a : Fin 5 → α) :
    listSize (List.ofFn (fun i => (e (a i)).val)) ≤ 5*(t+1) := by
  unfold listSize
  rw [List.map_ofFn, List.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin 5, (t+1) := Finset.sum_le_sum (fun i _ =>
      Nat.add_le_add_right (Nat.size_le.mpr (e (a i)).isLt) 1)
    _ = _ := by simp

theorem data_lists (N : ℕ) (st : State 400 128) (hd : Data N st)
    (L : Fin 128) (hi : 120 ≤ L.val) (hj : L.val < 123) :
    listSize (st.lists L) ≤ metadataWidth N := by
  have hb := (metadata_basic N).2.2.1
  have he : L = 120 ∨ L = 121 ∨ L = 122 := by omega
  rcases he with rfl | rfl | rfl
  · rw [hd.modulus]
    have hh := BinaryField.listSize_bits
      (BinaryField.encode_bits (BinaryWordMaterialization.modulus (fieldWidth N)))
    rw [BinaryField.encode_length] at hh
    exact hh.trans (by omega)
  · rw [hd.nodes]
    exact (fieldCodes_size (fieldCode (exponent N)) (nodes (exponent N))).trans
      (by change 5*(fieldWidth N+1) ≤ _; omega)
  · rw [hd.empty]; exact Nat.zero_le _

end PCP.Lang.ThreeColorBaseResources
