/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.NumericDerivedCost
import PCP.Complexity.AmplifiedRoundCost

/-! # A uniform polynomial envelope for the complete numeric derived branch -/

namespace PCP.Lang.NumericDerived

open PCP.Algebraic LocalCorrection DerivedGrid

/-- Every variable-size magnitude charged by the concrete implementation. -/
structure Magnitudes where
  B : ℕ
  t : ℕ
  n : ℕ
  m : ℕ
  h : ℕ
  W : ℕ
  k : Certificate
  x : List Bool
  qs : List ℕ
  bs : List Bool
  ht : t ≤ B
  hn : n ≤ B
  hm : m ≤ B
  hh : h ≤ B
  hW : W ≤ B
  hq : 2^t ≤ B
  hqs : listSize qs ≤ B
  hbs : bs.length ≤ B
  hx : x.length ≤ B
  hedge : GridEdge.budget t h n x ≤ B

/-- The degree and coefficient are uniform in all stored inputs. -/
def Poly (f : Magnitudes → ℕ) : Prop :=
  ∃ C d : ℕ, ∀ a, f a ≤ C*(a.B+1)^d

theorem poly_const (c : ℕ) : Poly (fun _ => c) := by
  refine ⟨c,0,?_⟩
  intro a
  simp

theorem poly_le {f g : Magnitudes → ℕ} (hg : Poly g) (h : ∀ a, f a ≤ g a) : Poly f := by
  obtain ⟨C,d,hg⟩ := hg
  exact ⟨C,d,fun a => (h a).trans (hg a)⟩

theorem poly_basic {f : Magnitudes → ℕ} (h : ∀ a, f a ≤ a.B) : Poly f :=
  ⟨1,1,fun a => by simpa using (h a).trans (Nat.le_add_right a.B 1)⟩

theorem poly_add {f g : Magnitudes → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun a => f a+g a) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨D,e,hg⟩ := hg
  refine ⟨C+D,d+e,?_⟩
  intro a
  have h1 := Nat.pow_le_pow_right (by omega : 1 ≤ a.B+1) (Nat.le_add_right d e)
  have h2 := Nat.pow_le_pow_right (by omega : 1 ≤ a.B+1) (Nat.le_add_left e d)
  have h := Nat.add_le_add ((hf a).trans (Nat.mul_le_mul_left C h1))
    ((hg a).trans (Nat.mul_le_mul_left D h2))
  simpa only [Nat.add_mul] using h

theorem poly_mul {f g : Magnitudes → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun a => f a*g a) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨D,e,hg⟩ := hg
  refine ⟨C*D,d+e,?_⟩
  intro a
  calc
    _ ≤ (C*(a.B+1)^d)*(D*(a.B+1)^e) := Nat.mul_le_mul (hf a) (hg a)
    _ = _ := by rw [Nat.pow_add]; ring

theorem poly_pow {f : Magnitudes → ℕ} (hf : Poly f) (d : ℕ) :
    Poly (fun a => f a^d) := by
  obtain ⟨C,e,hf⟩ := hf
  refine ⟨C^d,e*d,?_⟩
  intro a
  simpa only [Nat.mul_pow,← Nat.pow_mul] using Nat.pow_le_pow_left (hf a) d

theorem poly_certificate (f : Certificate → ℕ) : Poly (fun a => f a.k) := by
  apply poly_le (poly_const (f .valid+f .proper))
  intro a
  cases a.k <;> omega

syntax "derive_poly" : tactic
open Lean Meta Elab Tactic in
elab_rules : tactic
| `(tactic| derive_poly) => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let tag ← lambdaTelescope target.appArg! fun _ body => do
    let b := (← instantiateMVars body).consumeMData
    if b.isAppOf ``HAdd.hAdd || b.isAppOf ``Add.add || b.isAppOf ``Nat.add then return 1
    if b.isAppOf ``HMul.hMul || b.isAppOf ``Mul.mul || b.isAppOf ``Nat.mul then return 2
    if (b.isAppOf ``HPow.hPow || b.isAppOf ``Pow.pow || b.isAppOf ``Nat.pow) &&
        b.appArg!.isAppOf ``OfNat.ofNat then return 3
    return 0
  match tag with
  | 1 => evalTactic (← `(tactic| apply poly_add <;> derive_poly))
  | 2 => evalTactic (← `(tactic| apply poly_mul <;> derive_poly))
  | 3 => evalTactic (← `(tactic| apply poly_pow <;> derive_poly))
  | _ => evalTactic (← `(tactic| first | assumption | exact poly_const _))

attribute [local irreducible] Poly

attribute [local irreducible] DerivedSeed.splitConstant DerivedSeed.vectorConstant
  DerivedSeed.fixedConstant RadixCodec.passConstant CorrectionSeed.costConstant
  CorrectionContext.fixedConstant InnerSeed.costConstant LocalCorrection.costConstant
  DerivedPrimary.programConstant DerivedCall.fixedConstant QueryAddress.widthConstant
  QueryAddress.width OuterBranch.storedWidth CorrectionSeed.radixBound DerivedSeed.radixBound
  DerivedSeed.outputWidth ThreeColorSeedSize.innerBits

-- Structural closure traverses the fixed, finite cost expression.
set_option maxRecDepth 1024 in
/-- The finite arithmetic cost expression has one degree for both derived branches. -/
theorem programCost_poly (C : ℕ) :
    Poly (fun a => programCost C a.k a.t a.n a.m a.h a.W a.x a.qs a.bs) := by
  have ht := poly_basic Magnitudes.ht
  have hn := poly_basic Magnitudes.hn
  have hm := poly_basic Magnitudes.hm
  have hh := poly_basic Magnitudes.hh
  have hW := poly_basic Magnitudes.hW
  have hq := poly_basic Magnitudes.hq
  have hqs := poly_basic Magnitudes.hqs
  have hbs := poly_basic Magnitudes.hbs
  have hedge := poly_basic Magnitudes.hedge
  have hx := poly_basic Magnitudes.hx
  have hxbit : Poly (fun a => listSize (a.x.map Bool.toNat)) :=
    poly_le (poly_mul (poly_const 2) hx) (fun a => AmplifiedStream.boolList_size a.x)
  have hpc := poly_certificate (fun k => DerivedSeed.fixedConstant (DerivedSeed.payload k))
  have hic := poly_certificate (fun k =>
    CorrectionContext.fixedConstant (CorrectionContext.prepareInner k))
  have hfc := poly_certificate (fun k =>
    CorrectionContext.fixedConstant (CorrectionContext.finalize k))
  have hbits : Poly (fun a => listSize (a.bs.map Bool.toNat)) := by
    apply poly_le (poly_mul (poly_const 2) hbs)
    intro a
    exact AmplifiedStream.boolList_size a.bs
  have hd : Poly (fun a => a.k.outer.dimension a.n) := by
    apply poly_le (poly_mul (poly_const 4) hn)
    intro a
    cases a.k <;> simp [Certificate.outer, OuterBranch.Kind.dimension] <;> omega
  have hbase : Poly (fun a => baseDimension a.k a.n) := by
    apply poly_le (poly_mul (poly_const 2) hn)
    intro a
    cases a.k <;> simp [baseDimension] <;> omega
  have hinter : Poly (fun a => ThreeColorSeedSize.innerBits a.m 4 a.t) := by
    simp only [ThreeColorSeedSize.innerBits, ThreeColorSeedSize.hadamardBits_one]
    derive_poly
  have hwidth : Poly (fun a => QueryAddress.width a.t a.n a.m 4) := by
    unfold QueryAddress.width QueryAddress.inputWidth
    derive_poly
  have hstored : Poly (fun a => OuterBranch.storedWidth a.t a.n a.m a.qs a.bs []) := by
    simp only [OuterBranch.storedWidth, show listSize ([] : List ℕ) = 0 from rfl]
    derive_poly
  have hradix : Poly (fun a => CorrectionSeed.radixBound (a.k.outer.dimension a.n) a.m a.t) := by
    unfold CorrectionSeed.radixBound
    derive_poly
  have hderradix : Poly (fun a => DerivedSeed.radixBound (baseDimension a.k a.n) a.m a.t) := by
    unfold DerivedSeed.radixBound
    derive_poly
  have hout : Poly (fun a => DerivedSeed.outputWidth a.t a.n a.m a.W) := by
    unfold DerivedSeed.outputWidth
    derive_poly
  unfold programCost DerivedSeed.programCost DerivedSeed.materializeCost
    DerivedSeed.wordsCost DerivedSeed.maskCost DerivedSeed.pointsCost DerivedSeed.encodeCost
    DerivedSeed.edgeCost DerivedCall.programCost DerivedCall.primaryCost DerivedCall.correctionCost
    NumericCorrection.programCost NumericCorrection.callCost NumericCorrection.outerCallCost
    NumericCorrection.sourceWidth CorrectionContext.programCost CorrectionContext.materializeCost
    CorrectionContext.innerCost CorrectionContext.loadedWidth InnerSeed.budget
  derive_poly

/-- One polynomial controls the full actual branch on every bounded set of stored magnitudes. -/
theorem program_cost_uniform : ∃ C d : ℕ, ∀ (t n m : ℕ) [NeZero t] [NeZero m]
    (k : Certificate) (nodes : Fin 5 → OuterBranch.Field t) (ζ : OuterBranch.Field t)
    (h : ℕ) (_hh : h ≤ 2 ^ t) (x : List Bool) (s : DerivedGrid.Sample k t n m)
    (qs : List ℕ) (bs : List Bool) (W B : ℕ) (st : State 300 112),
    DerivedSeed.Input k (ThreeColorFullFieldSampling.padDerived s) st →
    DerivedSeed.Public (n := n) (m := m) nodes ζ h x qs bs st →
    DerivedSeed.SourceBound W st → t ≤ B → n ≤ B → m ≤ B → h ≤ B → W ≤ B →
    2 ^ t ≤ B → listSize qs ≤ B → bs.length ≤ B → x.length ≤ B →
    GridEdge.budget t h n x ≤ B → ((program k).run st).2 ≤ C*(B+1)^d := by
  obtain ⟨K,hK⟩ := program_cost
  have hpoly := programCost_poly K
  unfold Poly at hpoly
  obtain ⟨C,d,hC⟩ := hpoly
  refine ⟨C,d,?_⟩
  intro t n m _ _ k nodes ζ h hh x s qs bs W B st hi hp hb ht hn hm hh' hW hq hqs hbs hx he
  have hc := hC ⟨B,t,n,m,h,W,k,x,qs,bs,ht,hn,hm,hh',hW,hq,hqs,hbs,hx,he⟩
  exact (hK t n m k nodes ζ h hh x s qs bs W st hi hp hb).trans hc

end PCP.Lang.NumericDerived
