import Breakdown.Frac.StProfile

namespace Breakdown

theorem profileExistsIff : ProfileExistsIff := by
  intro α
  constructor
  · rintro ⟨U, P, a, ν, h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨U, P, a, ν, ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩⟩
  · rintro ⟨U, P, a, ν, h⟩
    exact ⟨U, P, a, ν, h.pos, h.smooth, h.smooth_pressure, h.smooth_power, h.residual, h.div,
      h.nonzero, h.decay⟩

end Breakdown
