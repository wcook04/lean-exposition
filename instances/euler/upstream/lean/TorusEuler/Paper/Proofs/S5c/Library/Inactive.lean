import TorusEuler.Paper.Proofs.S5Bridge.Leading
import TorusEuler.HierarchySupportPropagation
import TorusEuler.HierarchyPhysicalSolvers

/-!
# Supports on the inactive region (package S5c)

Generic glue on the region `{t < t₀} ∪ {a ∉ supp g}` of the slab used by the proof of Lemma 5.9
(`sections/08_exact_wave.tex:226`, `:266-267`): the support `supp g` of the periodized envelope
(`envelopeSupport_add_latticeVector`, `isClosed_envelopeSupport`,
`radialEnvelope_eq_zero_of_not_mem`), the submodule `inactiveVP` of profiles vanishing there,
and the facts that the local operators, the slow advection, the phase average, the completion
`C[·]` and the solution of (5.15) from `V(0) = 0` keep it (the library `inactiveLaws`,
`profileCompletion_eq_zero_on_inactive`, `exists_transverseResult` with
`Bridge.TransverseSolution.unique`). The facts about the profiles of the expansion themselves
are assembled in `Support54.lean` (`inactive_of_prop54`): the vanishing before `t₀` is read from
Proposition 5.4; the supports of the individual `V_p`, `𝗉_p`, which Proposition 5.4 does not
state, follow from the support of the sources by `transverseSolution_mem_inactive`.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5c

open HierarchyTwistedProfile

noncomputable section

/-! ## The envelope support -/

/-- The support `supp g` of the periodized envelope is invariant under lattice translations. -/
theorem envelopeSupport_add_latticeVector (ℓ : ℝ) (n : Fin 3 → ℤ) (x : Vec3) :
    x + latticeVector n ∈ S5.envelopeSupport ℓ ↔ x ∈ S5.envelopeSupport ℓ := by
  unfold S5.envelopeSupport
  let e : Vec3 ≃ₜ Vec3 := Homeomorph.addRight (latticeVector n)
  have hcomp : periodizeCentered (radialEnvelope ℓ) ∘ e = periodizeCentered (radialEnvelope ℓ) :=
    funext fun y => spatiallyPeriodic_periodizeCentered (radialEnvelope ℓ) n y
  have h := tsupport_comp_eq_preimage (periodizeCentered (radialEnvelope ℓ)) e
  rw [hcomp] at h
  constructor
  · intro hx
    rw [h]
    exact hx
  · intro hx
    rw [h] at hx
    exact hx

/-- `supp g` is closed. -/
theorem isClosed_envelopeSupport (ℓ : ℝ) : IsClosed (S5.envelopeSupport ℓ) :=
  isClosed_tsupport _

/-- On the label cell, the envelope vanishes outside `supp g` (`2ℓ_* < 1/2`). -/
theorem radialEnvelope_eq_zero_of_not_mem {ℓ : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2)
    {a : Vec3} (ha : a ∈ centeredCell) (hS : a ∉ S5.envelopeSupport ℓ) :
    radialEnvelope ℓ a = 0 := by
  by_contra hne
  apply hS
  apply subset_tsupport
  have heq := periodizeCentered_eq_on_centeredCell (f := radialEnvelope ℓ) (δ := 1 / 2 - 2 * ℓ)
    (by linarith) (fun x hx => by
      obtain ⟨i, hi⟩ := hx
      apply radialEnvelope_eq_zero hℓ
      have hxi : |x i| ≤ ‖x‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
      linarith) ha
  rw [Function.mem_support, heq]
  exact hne

/-! ## Vanishing on the inactive region from the cell values -/

/-- The inactive region `{t < t₀} ∪ {a ∉ supp g}` of the slab, as a submodule of profiles. -/
abbrev inactiveVP (T : ℝ) (k : Vec3) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t₀ ℓ : ℝ) : Submodule ℝ (HierarchyTwistedProfile T k E) :=
  inactiveSubmodule T k E t₀ (S5.envelopeSupport ℓ)

/-- A twisted profile vanishes on the inactive region as soon as it vanishes at its inactive
points over the label cell (the lattice twist and the periodicity of `supp g`). -/
theorem mem_inactive_of_cell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} {k : Vec3} {t₀ ℓ : ℝ} (f : HierarchyTwistedProfile T k E)
    (hcell : ∀ t ∈ Icc 0 T, ∀ a ∈ centeredCell, ∀ s,
      (t < t₀ ∨ a ∉ S5.envelopeSupport ℓ) → f.val.val.val (t, a, s) = 0) :
    f ∈ inactiveVP T k E t₀ ℓ := by
  intro x hx
  refine Lib.S5Bridge.forall_of_centeredCell (T := T) k
    (Q := fun x => (x.1 < t₀ ∨ x.2.1 ∉ S5.envelopeSupport ℓ) → f.val.val.val x = 0)
    ?_ hcell x hx.1 hx.2
  intro t a s n hq hcond
  rw [twistedSlice f t a s n]
  apply hq
  rcases hcond with h | h
  · exact Or.inl h
  · exact Or.inr fun ha => h ((envelopeSupport_add_latticeVector ℓ n a).mpr ha)

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ

/-- The divergence correction `C[V] = 𝐝 × Q[V]` of a profile vanishing on the inactive
region vanishes there (it centres its input and acts pointwise in time and label). -/
theorem curlCorrection_mem_inactive (d : ParentGeometry hT U X k) {t₀ ℓ : ℝ} {V : VP}
    (hV : V ∈ inactiveVP T k Vec3 t₀ ℓ) : S5.curlCorrection d V ∈ inactiveVP T k Vec3 t₀ ℓ := by
  have hL := inactiveLaws (τ := t₀) hT (isClosed_envelopeSupport ℓ) d.inverse d.strain d.covector
    d.mean.inverse_independent
  have hc : V - (S5.ops d).average V ∈ inactiveVP T k Vec3 t₀ ℓ :=
    Submodule.sub_mem _ hV (hL.average hV)
  intro x hx
  exact HierarchySmoothProfile.profileCompletion_eq_zero_on_inactive hT
    (isClosed_envelopeSupport ℓ) d.inverse.val.val d.covector.val.val
    (V - (S5.ops d).average V).val.val d.oscillation.covector_ne_zero hc hx

/-- A solution of (5.15) from `V(0) = 0` whose source has zero phase mean and vanishes on the
inactive region vanishes there, together with its pressure: it is the library ODE solve
(`exists_transverseResult`), by uniqueness (`Bridge.TransverseSolution.unique`), and that
solve keeps the inactive region (its field `inactive`). -/
theorem transverseSolution_mem_inactive (d : ParentGeometry hT U X k) {t₀ ℓ : ℝ} {f V : VP}
    {q : SP} (h : S5.TransverseSolution d f V q) (hf0 : (S5.ops d).average f = 0)
    (hf : f ∈ inactiveVP T k Vec3 t₀ ℓ) :
    V ∈ inactiveVP T k Vec3 t₀ ℓ ∧ q ∈ inactiveVP T k ℝ t₀ ℓ := by
  obtain ⟨r⟩ := exists_transverseResult hT d.inverse d.strain d.covector d.oscillation f hf0
  have hr : S5.TransverseSolution d f r.output.V r.output.p := by
    refine ⟨r.momentum, fun t ht a s => ?_, r.output.average_V, r.velocity_initial,
      r.pressure_mean⟩
    have h := r.transverse t ht a s
    rw [d.covector_value (t, a, s) ⟨ht, mem_univ _⟩] at h
    exact h
  obtain ⟨hV, hq⟩ := Bridge.TransverseSolution.unique d h hr
  have hz := r.inactive t₀ (S5.envelopeSupport ℓ)
    (fun t ht a s hi => hf (x := (t, a, s)) ⟨⟨ht, mem_univ _⟩, hi⟩)
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [hV]
    exact (hz x.1 hx.1.1 x.2.1 x.2.2 hx.2).1
  · rw [hq]
    exact (hz x.1 hx.1.1 x.2.1 x.2.2 hx.2).2

/-! ## The sources of the expansion -/

/-- The transverse source `f_p + f_p^S` of (5.27), (5.28) has zero phase mean when the means
`B_i`, `2 ≤ i ≤ p`, are phase independent. -/
theorem average_transverseSource (d : ParentGeometry hT U X k)
    (u : HierarchyProfiles VP SP) (cS : VP) {p : ℕ}
    (hB : ∀ i ∈ Finset.Icc 2 p, (S5.ops d).average (u.B i) = u.B i) :
    (S5.ops d).average (S5.oscSource (S5.ops d) u cS p + S5.suppSource (S5.ops d) u p) = 0 := by
  have hosc : (S5.ops d).average (S5.oscSource (S5.ops d) u cS p) = 0 := by
    unfold S5.oscSource
    rw [map_neg, map_sub, Bridge.ops_average_idempotent d, sub_self, neg_zero]
  have hsupp : (S5.ops d).average (S5.suppSource (S5.ops d) u p) = 0 := by
    unfold S5.suppSource
    rw [map_neg, map_sum]
    refine neg_eq_zero.mpr (Finset.sum_eq_zero fun i hi => ?_)
    exact average_meanPhaseAdv hT d.inverse d.strain d.covector (u.B i) _
      d.oscillation.covector_independent (hB i hi)
  rw [map_add, hosc, hsupp, add_zero]

end

end TorusEuler.Paper.Lib.S5c
