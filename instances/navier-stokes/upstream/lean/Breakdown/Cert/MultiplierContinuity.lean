import Breakdown.Cert.Nodes

open scoped Topology
open Filter

noncomputable section

namespace Breakdown.Cert

namespace Internal.MultiplierContinuity

open scoped Classical

def heldMultiplier {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) : Fin k → ℝ :=
  if h : ∃ κ, ∃ f, IsHeldSolution d p f κ then h.choose else 0

theorem heldMultiplier_spec {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ)
    (h : ∃ κ, ∃ f, IsHeldSolution d p f κ) : ∃ f, IsHeldSolution d p f (heldMultiplier d p) := by
  unfold heldMultiplier
  rw [dif_pos h]
  exact h.choose_spec

theorem multiplierOf_eq {k : ℕ} (d : CertificateData k) :
    multiplierOf d = fun p => d.multiplier p + heldMultiplier d p := rfl

theorem heldMultiplier_continuousOn (h1 : HeldLimitHolds) (h2 : HeldExistsUniqueHolds)
    {k : ℕ} (d : CertificateData k) (hd : IsCertificate d) :
    ContinuousOn (heldMultiplier d) d.box := by
  have hex : ∀ p ∈ d.box, ∃ f, IsHeldSolution d p f (heldMultiplier d p) := by
    intro p hp
    obtain ⟨f, κ, hf, -⟩ := h2 d hd p hp
    exact heldMultiplier_spec d p ⟨κ, f, hf⟩
  intro q hq
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  rw [tendsto_nhdsWithin_iff] at hns
  obtain ⟨hlim, hev⟩ := hns
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hmem : ∀ n, ns (n + N) ∈ d.box := fun n => hN _ (Nat.le_add_left N n)
  have hlim' : Tendsto (fun n => ns (n + N)) atTop (𝓝 q) := (tendsto_add_atTop_iff_nat N).2 hlim
  choose f hf using fun n => hex _ (hmem n)
  obtain ⟨φ, -, f₀, κ₀, h₀, hκ⟩ := h1 d hd (fun n => ns (n + N)) q hmem hq hlim' f
    (fun n => heldMultiplier d (ns (n + N))) hf
  obtain ⟨fq, hfq⟩ := hex q hq
  obtain ⟨g, μ, -, huniq⟩ := h2 d hd q hq
  have e1 := (huniq _ _ hfq).2
  have e2 := (huniq _ _ h₀).2
  refine ⟨fun n => φ n + N, ?_⟩
  rw [e1, ← e2]
  exact hκ

end Internal.MultiplierContinuity

open Internal.MultiplierContinuity in
theorem multiplierContinuityHolds_of (h1 : HeldLimitHolds) (h2 : HeldExistsUniqueHolds) :
    MultiplierContinuityHolds := by
  intro k d hd
  rw [multiplierOf_eq]
  exact hd.multiplier_continuous.add (heldMultiplier_continuousOn h1 h2 d hd)

end Breakdown.Cert
