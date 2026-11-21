import TorusEuler.Paper.Proofs.S678b.Library.Limit

/-! # Proof of Proposition 8.4 (cites Lemma 1.3; setting 7.1, 8.1) -/

open Filter Set
open scoped Topology

namespace TorusEuler.Paper

open Lib.S678b

/-- Proof of **Proposition 8.4** (`cc:uf:terminal:off-origin`), following
sections/09b_terminal_properties.tex:93-123.

* "For large `j` ... `q_j ≥ m`" (09b:96): `q_j → ∞` is Lemma 1.3, used through `h1_3`
  (`lemma13_schedule h1_3 P`); it enters only the off-origin trace
  `inductiveEuler_terminal_trace_of_stage_limits` (content of 8.4). The closed-slab limit `w`
  of the opening of Section 8 (`closedSlab_velocity_limit`) needs no bound on `q_j`.
* Velocity (09b:94-100): the support of `O_j` lies in the ball of radius `λ_{j-1}^{-1}`
  (`h71.oscillation_support`), so for large `j` (7.4) (`h71.increment`) bounds
  `U_j - U_{j-1}` in `C^m(K)` and `w(t) → w(T_∞)` in `C^m(K)`; `u = w` on `[0,T_∞)`
  (`h81.convergence`, inside `closedSlab_velocity_limit`) transfers this to `u`.
* Time derivative (09b:102-122): with the Euler equation of `u` from Proposition 8.1
  (`h81.euler`), the near and far pressure parts converge
  (`IsEulerSolution.hasOffOriginLimits_timeDerivative_of_velocity_jets`, content of 8.4),
  using the uniform convergence `u(t) → w(T_∞)` on the torus and the local jets. -/
theorem Proof.proposition_8_4_of (h1_3 : Statement.lemma_1_3) : Statement.proposition_8_4 := by
  intro P c C T u p h71 h81
  obtain ⟨hT, _, hSlab⟩ := h71.lifetime
  have hinit := two_le_frequency_zero P
  have hq := (lemma13_schedule h1_3 P).1
  obtain ⟨w, -, hW, hagree⟩ := closedSlab_velocity_limit h71 h81
  have hRadius : Tendsto (fun n => (P.frequency n)⁻¹) atTop (𝓝 0) := by
    have h := (reciprocal_inductive_frequency_tail hinit
      (c.stages.frequency_square_gap hinit) 0).1.tendsto_atTop_zero
    simp only [zero_add] at h
    exact h
  obtain ⟨hwOff, hwTCont, hwTPer, hwTSmooth, hwTGlobal, hwTLocal⟩ :=
    inductiveEuler_terminal_trace_of_stage_limits (U := c.stages.velocity)
      (O := c.stages.oscillation) (freq := P.frequency) (q := P.order) hT
      (fun j => (hSlab j).le) hinit (c.stages.frequency_square_gap hinit) hq
      (fun n => (h71.T1 n).1) (fun n t ht => ((h71.T1 n).2 t ht).1)
      (fun n t ht x => (h71.increment (n + 1) (Nat.succ_pos n) t ht).1 x)
      (increment_jet_bound h71) hW hRadius
      (fun n t ht x hx => h71.oscillation_support (n + 1) (Nat.succ_pos n) t
        (Icc_subset_Icc_right (hSlab (n + 1)).le ht) x hx)
  have hEv : ∀ᶠ t in 𝓝[Ico 0 T] T, w t = u t :=
    eventually_nhdsWithin_of_forall fun t ht => (hagree t ht).symm
  have hvel : HasOffOriginLimits T u := by
    intro K hK hKo m
    obtain ⟨U, g, hU, hKU, hUo, hg, hconv⟩ := hwOff K hK hKo m
    exact ⟨U, g, hU, hKU, hUo, hg, fun j hj => (hconv j hj).congr
      (hEv.mono fun t ht => by rw [ht]; exact fun _ _ => rfl)⟩
  refine ⟨hvel, ?_⟩
  exact h81.euler.hasOffOriginLimits_timeDerivative_of_velocity_jets hwTCont hwTSmooth hwTPer
    (hwTGlobal.tendstoUniformlyOn.congr (hEv.mono fun t ht => by rw [ht]; exact fun _ _ => rfl))
    (fun S hS hSo d =>
      (hwTLocal S hS hSo d).congr (hEv.mono fun t ht => by rw [ht]; exact fun _ _ => rfl))

end TorusEuler.Paper
