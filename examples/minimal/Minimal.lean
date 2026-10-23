module
prelude
public import Init.Prelude

public section
namespace Minimal

theorem swap (p q : Prop) (h : And p q) : And q p :=
  And.intro (And.right h) (And.left h)

theorem result (p q : Prop) (h : And p q) : And q p :=
  swap p q h

end Minimal
