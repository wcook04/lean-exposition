import PCP.Complexity.DerivedSeedResources
import PCP.Complexity.DerivedSeedLang
import PCP.Complexity.DerivedCallResources

/-! Actual stored-source bounds after the complete derived-seed materializer. -/

namespace PCP.Lang.DerivedSeed

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection DerivedGrid BinaryPolynomialSpace

variable {t n m : ℕ} [NeZero t]

/-- Polynomial in the input width, the dimensions, and the field cardinality. -/
def outputWidth (t n m W : ℕ) : ℕ :=
  W + 4*(t+1)*(n+m) + 10*t + 4*2 ^ t + 30

theorem context_bound (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (a b : k.Point t n) (w : Fin t → ZMod 2)
    (mask : Coefficients t 3) (weight : OuterBranch.Field t)
    (loc : HadamardRow.Location (OuterBranch.Field t) n m 4 3)
    (first second : k.Seed t n m) (qs : List ℕ) (bs : List Bool)
    (st : State 300 112) (W : ℕ)
    (hc : DerivedCall.Context k nodes ζ a b w mask weight loc first second qs bs st)
    (hfirst : Nat.size ((callCodec (BinaryMaterializedField.coordinates t)
      (CorrectionContext.coordinateCodec k n) m 4).equiv (padCall first)).val ≤ W)
    (hsecond : Nat.size ((callCodec (BinaryMaterializedField.coordinates t)
      (CorrectionContext.coordinateCodec k n) m 4).equiv (padCall second)).val ≤ W)
    (hqs : listSize qs ≤ W) (hbs : listSize (bs.map Bool.toNat) ≤ W) :
    DerivedCall.SourceBound (outputWidth t n m W) st := by
  let B := outputWidth t n m W
  have hd : k.outer.dimension n ≤ 4*n := by
    cases k <;> simp [Certificate.outer, OuterBranch.Kind.dimension] <;> omega
  have hbasic : t+1 ≤ B ∧ m ≤ B ∧ 4*n ≤ B ∧ 2*2 ^ t+2 ≤ B ∧
      2*t ≤ B ∧ 5*(t+1) ≤ B ∧ W ≤ B := by
    dsimp [B,outputWidth]
    have hmul : n+m ≤ (t+1)*(n+m) := Nat.le_mul_of_pos_left _ (by omega)
    simp only [Nat.mul_assoc]
    omega
  have hprod (d : ℕ) (hh : d ≤ 4*(n+m)) : d*(t+1) ≤ B := by
    have hh' := Nat.mul_le_mul_right (t+1) hh
    dsimp [B,outputWidth]
    nlinarith only [hh', Nat.zero_le (2 ^ t), Nat.zero_le W, Nat.zero_le t]
  have hp (d : ℕ) (hh : d ≤ 4*(n+m)) : Nat.size ((2 ^ t)^d) ≤ B := by
    rw [← pow_mul, Nat.size_pow]
    have hh' := Nat.mul_le_mul_left t hh
    dsimp [B,outputWidth]
    nlinarith only [hh', Nat.zero_le (2 ^ t), Nat.zero_le W,
      Nat.zero_le t, Nat.zero_le n, Nat.zero_le m]
  have hl (r : ℕ) : Nat.size (2^BooleanCoefficientIndex.dimension t r) ≤ B := by
    have h := BooleanCoefficientTransform.masks_length_le t r
    rw [BooleanMask.masks_length] at h
    rw [Nat.size_pow]
    omega
  have hf (x : OuterBranch.Field t) : Nat.size (fieldEquiv t x).val ≤ B :=
    (Nat.size_le.mpr (fieldEquiv t x).isLt).trans (by omega)
  have hpoint (x : k.Point t n) : Nat.size (k.outer.pointCode (fieldEquiv t) x) ≤ B :=
    (k.outer.pointCode_size x).trans ((Nat.mul_le_mul_left t hd).trans (by
      have hh := hprod (4*n) (by omega)
      nlinarith only [hh, Nat.zero_le n]))
  have hcodes {d : ℕ} (x : Fin d → OuterBranch.Field t) (hh : d ≤ 4*(n+m)) :
      listSize (List.ofFn (fun i => (fieldEquiv t (x i)).val)) ≤ B :=
    (StandardCorrection.fieldCodes_size x).trans (hprod d hh)
  have hbits (v : Fin t → ZMod 2) : listSize (List.ofFn (fun i => (v i).val)) ≤ B :=
    (InterpolationBranch.coordinateBits_size v).trans (by omega)
  have hlabel {r : ℕ} (p : Coefficients t r) :
      listSize (BooleanCoefficientList.encode p) ≤ B :=
    (HadamardLabel.encode_size p).trans (by omega)
  have hinput : QueryAddress.inputWidth t n m 4 ≤ B := by
    dsimp [QueryAddress.inputWidth,B,outputWidth]
    nlinarith only [Nat.zero_le W,Nat.zero_le t,Nat.zero_le n,Nat.zero_le m,Nat.zero_le (2 ^ t)]
  constructor
  · intro i hi
    by_cases hip : 260 ≤ i.val
    · have hj : i.val < 270 := by omega
      let j : Fin 10 := ⟨i.val-260,by omega⟩
      have he : DerivedCall.payloadPort j = i := by
        apply Fin.ext
        simp only [DerivedCall.payloadPort,j]
        omega
      rw [← he,hc.payload]
      exact (QueryAddress.inputs_size (fieldEquiv t) (loc.query 0) j.castSucc).trans hinput
    have he : i = 240 ∨ i = 241 ∨ i = 242 ∨ i = 243 ∨ i = 244 ∨ i = 245 ∨
        i = 246 ∨ i = 247 ∨ i = 248 ∨ i = 249 ∨ i = 250 ∨ i = 251 ∨ i = 252 ∨
        i = 253 ∨ i = 254 ∨ i = 255 := by omega
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hc.width]; exact (size_le_self t).trans (by omega)
    · rw [hc.base]; exact (size_le_self m).trans (by omega)
    · rw [hc.dimension]; exact (size_le_self _).trans (hd.trans (by omega))
    · rw [hc.card,Nat.size_pow]; exact hbasic.1
    · rw [hc.root]; exact hf _
    · rw [hc.weight]; exact hf _
    · rw [hc.firstCode]; exact hpoint _
    · rw [hc.secondCode]; exact hpoint _
    · rw [hc.firstSeed]; exact hfirst.trans (by omega)
    · rw [hc.secondSeed]; exact hsecond.trans (by omega)
    · rw [hc.vertices]; exact hp _ (by omega)
    · rw [hc.pairs]; exact hp _ (by omega)
    · rw [hc.proper]; exact hp _ (by omega)
    · rw [hc.inner]; exact hp _ (by omega)
    · rw [hc.affineLabels]; exact hl _
    · rw [hc.cubicLabels]; exact hl _
  · intro L hL hu
    have he : L = 100 ∨ L = 101 ∨ L = 102 ∨ L = 103 ∨ L = 104 ∨ L = 105 ∨
        L = 106 ∨ L = 107 ∨ L = 108 := by omega
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hc.empty]; exact Nat.zero_le _
    · rw [hc.modulus]; exact hbits _
    · rw [hc.nodes]; exact (StandardCorrection.fieldCodes_size _).trans (by omega)
    · rw [hc.firstPoint]; exact hcodes _ (by omega)
    · rw [hc.secondPoint]; exact hcodes _ (by omega)
    · rw [hc.label]; exact hbits _
    · rw [hc.mask]; exact hlabel _
    · rw [hc.history]; exact hqs.trans (by omega)
    · rw [hc.answers]; exact hbs.trans (by omega)

theorem outputWidth_le (t n m W B : ℕ) (ht : t ≤ B) (hn : n ≤ B) (hm : m ≤ B)
    (hq : 2 ^ t ≤ B) (hW : W ≤ B) : outputWidth t n m W ≤ 100*(B+1)^2 := by
  have hp := Nat.mul_le_mul (by omega : t+1 ≤ B+1) (by omega : n+m ≤ 2*B)
  unfold outputWidth
  nlinarith only [hp,ht,hq,hW,Nat.zero_le B]

attribute [local irreducible] program

theorem program_output_bound (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t)
    (ζ : OuterBranch.Field t) (h : ℕ) (hh : h ≤ 2 ^ t) (x : List Bool)
    (s : DerivedGrid.Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 300 112)
    (W : ℕ) (hi : Input k (padDerived s) st)
    (hp : Public (n := n) (m := m) nodes ζ h x qs bs st) (hb : SourceBound W st) :
    DerivedCall.SourceBound (outputWidth t n m W) ((program k).run st).1 := by
  have hc := program_run k nodes ζ h hh x s qs bs st hi hp
  have hcode : Nat.size ((derivedCodec (BinaryMaterializedField.coordinates t)
      (baseDimension k n) m 4 3).equiv (padDerived s)).val ≤ W := by
    rw [← hi.seed]
    exact hb.input 3
  apply context_bound k nodes ζ _ _ _ _ _ _ _ _ qs bs _ W hc
  · rw [← firstSeed_code k s]
    exact (component_size k (padDerived s) 2).trans hcode
  · rw [← secondSeed_code k s]
    exact (component_size k (padDerived s) 1).trans hcode
  · rw [← hp.history]
    exact hb.lists 107 (by decide)
  · rw [← hp.answers]
    exact hb.lists 108 (by decide)

end PCP.Lang.DerivedSeed
