module
prelude
public import Init.Core
public import Init.Data.Nat.Gcd
public import Init.Data.Nat.Bitwise.Basic

public section
namespace Minimal

theorem result (p q : Prop) (h : And p q) : And q p :=
  sorry

end Minimal
