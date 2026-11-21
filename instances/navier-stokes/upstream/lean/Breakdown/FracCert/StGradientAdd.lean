import Breakdown.FracCert.Defs

namespace Breakdown.SteadyCert

def GradientAddStatement : Prop :=
  ∀ Q R : Space → Space, IsGradientField Q → IsGradientField R → IsGradientField (fun y => Q y + R y)

end Breakdown.SteadyCert
