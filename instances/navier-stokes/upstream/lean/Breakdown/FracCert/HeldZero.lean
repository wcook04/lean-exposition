import Breakdown.FracCert.StHeld
import Breakdown.Held.Exports

open Matrix

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace HeldZeroInternal

theorem det_isUnit_of_near {k : ℕ} (U : Matrix (Fin k) (Fin k) ℝ) (δ : ℝ)
    (hU : ∀ z : Fin k → ℝ, |∑ j, (U *ᵥ z) j ^ 2 - ∑ j, z j ^ 2| ≤ δ * ∑ j, z j ^ 2) (hδ : δ < 1) :
    IsUnit U.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hUv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
  have h1 := hU v
  rw [hUv] at h1
  have hs : 0 ≤ ∑ j, v j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have e : ∑ j, ((0 : Fin k → ℝ) j) ^ 2 = 0 := by simp
  rw [e, zero_sub, abs_neg, abs_of_nonneg hs] at h1
  have hS : ∑ j, v j ^ 2 = 0 := by nlinarith
  apply hv
  funext j
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i))).1 hS j (Finset.mem_univ j)
  simpa using hj

end HeldZeroInternal

theorem heldZero (h1 : HeldMultiplierContinuousStatement) (h2 : ActiveEnclosureStatement)
    (h3 : StiffEnclosureStatement) (h4 : TestBoxSubsetStatement) : HeldZeroStatement := by
  intro α hα1 hα2 k N d hd
  obtain ⟨Φ, hΦc, hΦ⟩ := h1 α hα1 hα2 d hd
  have hsub : d.testBox ⊆ box d.radius := h4 α d hd
  have hm : ∀ p, d.heldMultiplier p (fun i => Φ p i - d.multiplier p i) = Φ p := by
    intro p
    funext i
    simp [FracCertData.heldMultiplier]
  obtain ⟨p, hp, hp0⟩ := Held.testSetZero d.activeSet d.radius d.slope d.ellipsoidRadius d.frame Φ
    (fun j _ => hd.radius_nonneg j) hd.ellipsoidRadius_nonneg hd.slope_ne_zero
    (HeldZeroInternal.det_isUnit_of_near d.frame d.frameDefect hd.frame_near hd.frameDefect_lt)
    (hΦc.mono hsub)
    (fun p hp j hj => by
      obtain ⟨u, G, H, P, hs, hsz⟩ := hΦ p (hsub hp)
      have := h2 α hα1 hα2 d hd p hp u G H P _ hs hsz j hj
      rwa [hm] at this)
    (fun p hp => by
      obtain ⟨u, G, H, P, hs, hsz⟩ := hΦ p (hsub hp)
      have := h3 α hα1 hα2 d hd p hp u G H P _ hs hsz
      rwa [hm] at this)
  obtain ⟨u, G, H, P, hs, hsz⟩ := hΦ p (hsub hp)
  exact ⟨p, hsub hp, u, G, H, P, _, hs, hsz, by rw [hm, hp0]⟩

end SteadyCert

end Breakdown
