import PCP.Complexity.LangComputedSeedCost
import PCP.Complexity.LangProductSeedLayout
import PCP.Complexity.ThreeColorSeedArithmetic

/-!
# Actual nested verifier-seed decoders

Each fixed decoder constructs its own seven radix cells. Unused slots have
radix one and return zero. Compound leaves retain their actual codec integer
for the dedicated point, label, or inner-test materialization routine.
-/

namespace PCP.Lang.NestedSeed

open ArithmeticExpression PCP.Algebraic ThreeColorSeedIndex ThreeColorSeedSize
open ThreeColorFullFieldSampling

private def mul := Term.bin (n := 4) .mul
private def add := Term.bin (n := 4) .add

def pointBits : Term 4 := mul (.input 3) (.input 0)
def innerPointBits : Term 4 := mul (.input 3) (mul (.input 2) (.input 1))
def callBits : Term 4 := add (add (add (mul (.const 2) pointBits) (.input 3))
  innerPointBits) SeedArithmetic.inner

def outerTerms (cubic : Bool) : Fin 7 → Term 4 :=
  ![SeedArithmetic.inner, SeedArithmetic.hadamard cubic, .input 3, innerPointBits,
    .input 3, pointBits, pointBits]

def innerTerms : Fin 7 → Term 4 :=
  ![.input 3, .input 3, innerPointBits, innerPointBits,
    SeedArithmetic.hadamard false, innerPointBits, .const 1]

def callTerms : Fin 7 → Term 4 :=
  ![SeedArithmetic.inner, innerPointBits, .input 3, pointBits, .const 0, .const 0, .const 0]

def derivedTerms : Fin 7 → Term 4 :=
  ![SeedArithmetic.coefficientThree, callBits, callBits, .input 3, pointBits, .const 0, .const 0]

def differenceTerms : Fin 7 → Term 4 :=
  ![.input 3, pointBits, pointBits, .const 0, .const 0, .const 0, .const 0]

def outer (cubic : Bool) : Stmt 16 4 := ComputedSeed.program (outerTerms cubic)
def inner : Stmt 16 4 := ComputedSeed.program innerTerms
def call : Stmt 16 4 := ComputedSeed.program callTerms
def derived : Stmt 16 4 := ComputedSeed.program derivedTerms
def difference : Stmt 16 4 := ComputedSeed.program differenceTerms

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {t : ℕ}
variable (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))

def outerLayout {σ : Type*} (σc : Codec σ) (m c r : ℕ) :
    SeedLayout (outerCodec ρ σc m c r) :=
  let p := SeedLayout.leaf (σc.function (fieldCodec ρ))
  (p.prod p).prod ((SeedLayout.leaf (fieldCodec ρ)).prod
    (((SeedLayout.leaf (innerPointCodec ρ m c)).prod (SeedLayout.leaf (bitsCodec t))).prod
      ((SeedLayout.leaf (hadamardCodec t r)).prod (SeedLayout.leaf (innerCodec ρ m c)))))

def innerLayout (m c : ℕ) : SeedLayout (innerCodec ρ m c) :=
  let p := SeedLayout.leaf (innerPointCodec ρ m c)
  (SeedLayout.leaf boolCodec).prod
    ((p.prod (SeedLayout.leaf (hadamardCodec t 1))).prod
      (((p.prod p).prod (SeedLayout.leaf (fieldCodec ρ))).prod (SeedLayout.leaf (bitsCodec t))))

def callLayout {σ : Type*} (σc : Codec σ) (m c : ℕ) :
    SeedLayout (callCodec ρ σc m c) :=
  (SeedLayout.leaf (σc.function (fieldCodec ρ))).prod
    ((SeedLayout.leaf (fieldCodec ρ)).prod
      ((SeedLayout.leaf (innerPointCodec ρ m c)).prod (SeedLayout.leaf (innerCodec ρ m c))))

def derivedLayout (n m c : ℕ) : SeedLayout (derivedCodec ρ n m c 3) :=
  let a := SeedLayout.leaf (callCodec ρ ((Codec.fin n).sum (Codec.fin n)) m c)
  (SeedLayout.leaf ((Codec.fin n).function (fieldCodec ρ))).prod
    (((SeedLayout.leaf (bitsCodec t)).prod (a.prod a)).prod
      (SeedLayout.leaf (coefficientCodec t 3)))

def differenceLayout (n : ℕ) :
    SeedLayout ((((Codec.fin n).function (fieldCodec ρ)).prod
      ((Codec.fin n).function (fieldCodec ρ))).prod (bitsCodec t)) :=
  let p := SeedLayout.leaf ((Codec.fin n).function (fieldCodec ρ))
  (p.prod p).prod (SeedLayout.leaf (bitsCodec t))

end PCP.Lang.NestedSeed
