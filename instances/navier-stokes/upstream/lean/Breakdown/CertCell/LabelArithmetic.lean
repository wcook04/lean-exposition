import Breakdown.CertCell.BridgeStatements

namespace Breakdown

namespace CertCell

namespace Bridge

theorem labelArithmetic : LabelArithmeticHolds := by
  intro m hm
  have hm' : (m : ℤ) ≠ 0 := by
    have : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
    exact ne_of_gt this
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [labelHarmonic, labelTime, labelAzimuth, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hac : a = c := mul_right_cancel₀ hm' h2
    subst hac
    simp only [Prod.mk.injEq, true_and]
    omega
  · rintro ⟨a, b⟩
    simp only [labelHarmonic, labelTime, labelAzimuth, labelFlip, flipLabel, Prod.mk.injEq]
    constructor <;> ring
  · rintro ⟨a, b⟩
    simp only [labelHarmonic, labelTime, labelAzimuth, Prod.neg_mk, Prod.mk.injEq]
    constructor <;> ring
  · rintro ⟨x, y⟩
    simp only [IsLatticeHarmonic]
    constructor
    · rintro ⟨⟨a, b⟩, h⟩
      simp only [labelHarmonic, labelTime, labelAzimuth, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1 h2
      refine ⟨⟨a, by ring⟩, ?_⟩
      rw [Int.mul_ediv_cancel _ hm']
      exact ⟨b, by ring⟩
    · rintro ⟨⟨n, hn⟩, ⟨k, hk⟩⟩
      subst hn
      rw [Int.mul_ediv_cancel_left _ hm'] at hk
      refine ⟨(n, k), ?_⟩
      simp only [labelHarmonic, labelTime, labelAzimuth, Prod.mk.injEq]
      constructor
      · omega
      · ring

end Bridge

end CertCell

end Breakdown
