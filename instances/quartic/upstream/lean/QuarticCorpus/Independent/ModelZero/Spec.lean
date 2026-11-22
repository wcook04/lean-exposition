module

public import QuarticQuery.Statement

/-!
An independently stated semantic expectation for zero-query complexity.
`LabelsAgree` mentions only the promise labels. It does not define its expected
answer through DLe, RLe, QLe, or ConstantOnPromise. Empty promises are allowed.
-/

@[expose] public section

set_option autoImplicit false

namespace QuarticQuery.Independent.ModelZero

def LabelsAgree {ι : Type} (f : PartialBool ι) : Prop :=
  ∀ (x y : BitInput ι) (b c : Bool),
    f x = some b → f y = some c → b = c

end QuarticQuery.Independent.ModelZero
