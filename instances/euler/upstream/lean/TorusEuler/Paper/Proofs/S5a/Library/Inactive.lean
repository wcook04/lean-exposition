import TorusEuler.Paper.Proofs.S5Bridge.Leading
import TorusEuler.HierarchySupportPropagation
import TorusEuler.HierarchyPhysicalSolvers

/-!
# S5a library: the expansion vanishes before `t₀` and outside `supp g` (Proposition 5.4)

Proposition 5.4 asserts that `W_osc` and the sources `f_p + f_p^S` are supported in `supp g`,
and that `V_p`, `C_p`, `𝗉_p`, `f_p + f_p^S` vanish for `t < t₀`
(`sections/06c_finite_hierarchy.tex:317-321`); its proof (`:376-391`) runs the induction on the
level over the open set `𝒪 = {t < t₀} ∪ {a ∉ supp g}`: `V₁`, `C₂`, `𝗉₁` vanish on `𝒪`; if the
lower levels vanish there, `H_p` reduces to the phase-independent products `(B_i·𝐝)B_j`, so
`f_p = f_p^S = 0` on `𝒪`, and the transverse solution vanishes where its source does
(`06c_finite_hierarchy.tex:24-28`), and so do `C_{p+1}` and `𝗉_p`.

For an expansion of depth `P` in predicate form (`S5.IsExpansion`), the profiles `V_p`, `𝗉_p`
(`1 ≤ p ≤ P`), the corrections `C_p` (`1 ≤ p ≤ P + 1`) and the transverse sources
`f_p + f_p^S` (`2 ≤ p ≤ P`) vanish at every point `(t, a, s)` of the slab with `t < t₀` or
`a ∉ supp g` (`IsExpansion.inactive`).

The argument is the ordered recursion of §5.5 read in predicate form: the leading pair and
the activation term vanish there by their cell values (3.7), (3.8) (`χ̃ = χ̃' = 0` before
`t₀`, `g = 0` outside `supp g`); local operators, the slow advection and the phase average
preserve the vanishing (the library `HierarchyTwistedProfile.inactiveLaws`); the completion
`C[·]` preserves it (`HierarchySmoothProfile.profileCompletion_eq_zero_on_inactive`); and the
solution of (5.15) from `V(0) = 0` with a source vanishing there vanishes there, since it is
the library ODE solve (`exists_transverseResult`, its field `inactive`) by uniqueness
(`Bridge.TransverseSolution.unique`). It uses no content lemma of another ledger row; it is the
argument of the library 5.4 content `physicalConstruct_support_and_tail_on_inactive`, which is
stated for the construction `physicalSolvers` and so is not usable here.

Copy: this file is a copy of the glue file `Proofs/S5c/Library/Inactive.lean` of package S5c
(branch `lean-latest/B-S5c`, commit `e53692d4`), namespace `Lib.S5c` renamed `Lib.S5a`; the
statements and proofs are unchanged.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5a

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

/-- The transverse source `f_p + f_p^S` of level `p ≥ 2` vanishes on the inactive region when
the lower levels do: `Y_j = V_j + C_j` for `1 ≤ j < p`, `C_p`, `𝗉_{p-1}` and (at `p = 2`) the
activation correction `C[χ̃'A₁]` vanish there, and the means `B_j`, `1 ≤ j < p`, are phase
independent (the statement holds for every `p`; it is used for `2 ≤ p ≤ P`). On the inactive region `H_p` reduces to the slow products of means, which the
centring removes, and every term of `f_p^S` has an inactive second factor. -/
theorem transverseSource_mem_inactive (d : ParentGeometry hT U X k) {t₀ ℓ : ℝ}
    (u : HierarchyProfiles VP SP) (cS : VP) {p : ℕ}
    (hY : ∀ j, 1 ≤ j → j < p → S5.Yd u j ∈ inactiveVP T k Vec3 t₀ ℓ)
    (hCp : S5.Cd u p ∈ inactiveVP T k Vec3 t₀ ℓ)
    (hpp : u.p (p - 1) ∈ inactiveVP T k ℝ t₀ ℓ)
    (hcS : cS ∈ inactiveVP T k Vec3 t₀ ℓ)
    (hB : ∀ j, 1 ≤ j → j < p → (S5.ops d).average (u.B j) = u.B j) :
    S5.oscSource (S5.ops d) u cS p + S5.suppSource (S5.ops d) u p ∈ inactiveVP T k Vec3 t₀ ℓ := by
  let A := S5.ops d
  let E₀ := inactiveVP T k Vec3 t₀ ℓ
  have hL : HierarchySupportLaws A E₀ (inactiveVP T k ℝ t₀ ℓ) :=
    inactiveLaws hT (isClosed_envelopeSupport ℓ) d.inverse d.strain d.covector
      d.mean.inverse_independent
  let pairs := (Finset.Icc 1 p ×ˢ Finset.Icc 1 p).filter (fun ij : ℕ × ℕ => ij.1 + ij.2 = p)
  let Dm : VP := ∑ ij ∈ pairs, A.labelAdv (u.B ij.1) (u.B ij.2)
  have hpairs : ∀ ij ∈ pairs, 1 ≤ ij.1 ∧ ij.1 < p ∧ 1 ≤ ij.2 ∧ ij.2 < p := by
    intro ij hij
    simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hij
    omega
  have hDm : A.average Dm = Dm := by
    simp only [Dm, map_sum]
    refine Finset.sum_congr rfl fun ij hij => ?_
    obtain ⟨h1, h2, h3, h4⟩ := hpairs ij hij
    exact hL.labelAdv_mean (hB ij.1 h1 h2) (hB ij.2 h3 h4)
  have hlin : A.material (S5.Cd u p) + A.labelGrad (u.p (p - 1)) - (if p = 2 then cS else 0) ∈ E₀ := by
    refine E₀.sub_mem (E₀.add_mem (hL.material hCp) (hL.labelGrad hpp)) ?_
    by_cases hp2 : p = 2
    · simpa only [hp2, ↓reduceIte] using hcS
    · simpa only [hp2, ↓reduceIte] using E₀.zero_mem
  have hslow : (∑ ij ∈ pairs, A.labelAdv (S5.Zd u ij.1) (S5.Zd u ij.2)) - Dm ∈ E₀ := by
    simp only [Dm]
    rw [← Finset.sum_sub_distrib]
    refine Submodule.sum_mem E₀ fun ij hij => ?_
    obtain ⟨h1, h2, h3, h4⟩ := hpairs ij hij
    have heq : A.labelAdv (S5.Zd u ij.1) (S5.Zd u ij.2) - A.labelAdv (u.B ij.1) (u.B ij.2) =
        A.labelAdv (S5.Yd u ij.1) (S5.Zd u ij.2) + A.labelAdv (u.B ij.1) (S5.Yd u ij.2) := by
      simp only [S5.Zd, map_add, LinearMap.add_apply]
      abel
    rw [heq]
    exact E₀.add_mem (hL.labelAdv_left (hY _ h1 h2) _) (hL.labelAdv_right _ (hY _ h3 h4))
  have hfast : (∑ ij ∈ (Finset.Icc 2 p ×ˢ Finset.Icc 1 p).filter
      (fun ij : ℕ × ℕ => ij.1 + ij.2 = p + 1), A.phaseAdv (S5.Cd u ij.1) (S5.Yd u ij.2)) ∈ E₀ := by
    refine Submodule.sum_mem E₀ fun ij hij => ?_
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hij
    exact hL.phaseAdv_right _ (hY ij.2 (by omega) (by omega))
  have hLD : S5.levelSource A u cS p - Dm ∈ E₀ := by
    have heq : S5.levelSource A u cS p - Dm =
        (A.material (S5.Cd u p) + A.labelGrad (u.p (p - 1)) - (if p = 2 then cS else 0)) +
          ((∑ ij ∈ pairs, A.labelAdv (S5.Zd u ij.1) (S5.Zd u ij.2)) - Dm) +
          (∑ ij ∈ (Finset.Icc 2 p ×ˢ Finset.Icc 1 p).filter
            (fun ij : ℕ × ℕ => ij.1 + ij.2 = p + 1), A.phaseAdv (S5.Cd u ij.1) (S5.Yd u ij.2)) := by
      simp only [S5.levelSource, pairs]
      abel
    rw [heq]
    exact E₀.add_mem (E₀.add_mem hlin hslow) hfast
  have hosc : S5.oscSource A u cS p ∈ E₀ := by
    have heq : S5.oscSource A u cS p =
        -((S5.levelSource A u cS p - Dm) - A.average (S5.levelSource A u cS p - Dm)) := by
      simp only [S5.oscSource, map_sub, hDm]
      abel
    rw [heq]
    exact E₀.neg_mem (E₀.sub_mem hLD (hL.average hLD))
  have hsupp : S5.suppSource A u p ∈ E₀ := by
    unfold S5.suppSource
    refine E₀.neg_mem (Submodule.sum_mem E₀ fun i hi => ?_)
    rw [Finset.mem_Icc] at hi
    exact hL.phaseAdv_right _ (hY _ (by omega) (by omega))
  exact E₀.add_mem hosc hsupp

/-! ## The expansion -/

/-- **Supports of the expansion.** For an expansion of depth `P` (`S5.IsExpansion`) with
`0 < ℓ_*`, `2ℓ_* < 1/2`: `V_p`, `𝗉_p` (`1 ≤ p ≤ P`), `C_p` (`1 ≤ p ≤ P + 1`) and
`f_p + f_p^S` (`2 ≤ p ≤ P`) vanish at every point of the slab with `t < t₀` or `a ∉ supp g`.
These are the support clauses of Proposition 5.4 (`06c_finite_hierarchy.tex:317-321, 376-391`);
see the module docstring for the argument. -/
theorem IsExpansion.inactive (d : ParentGeometry hT U X k) {pU : Pressure} {t₀ : ℝ}
    {χ : PaperWaveCutoff t₀ T} {ℓ h : ℝ} {amp : ℝ → Vec3 → Vec3} {P : ℕ} {R S : VP}
    {u : HierarchyProfiles VP SP} (hu : S5.IsExpansion d pU χ ℓ h amp P R S u)
    (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) :
    (∀ i ∈ Finset.Icc 1 P, u.V i ∈ inactiveVP T k Vec3 t₀ ℓ ∧ u.p i ∈ inactiveVP T k ℝ t₀ ℓ) ∧
    (∀ i ∈ Finset.Icc 1 (P + 1), S5.Cd u i ∈ inactiveVP T k Vec3 t₀ ℓ) ∧
    (∀ i ∈ Finset.Icc 2 P,
      S5.oscSource (S5.ops d) u (S5.curlCorrection d S) i + S5.suppSource (S5.ops d) u i ∈
        inactiveVP T k Vec3 t₀ ℓ) := by
  let E₀ := inactiveVP T k Vec3 t₀ ℓ
  let F₀ := inactiveVP T k ℝ t₀ ℓ
  let cS := S5.curlCorrection d S
  -- the leading cell values vanish on the inactive region
  have hcellZero : ∀ t ∈ Icc 0 T, ∀ a ∈ centeredCell, (t < t₀ ∨ a ∉ S5.envelopeSupport ℓ) →
      (t < t₀ ∧ χ.value t = 0 ∧ χ.derivative t = 0) ∨ radialEnvelope ℓ a = 0 := by
    intro t ht a ha hi
    rcases hi with hi | hi
    · exact Or.inl ⟨hi, χ.zero_before t ht hi, χ.derivative_zero_before hT ht hi⟩
    · exact Or.inr (radialEnvelope_eq_zero_of_not_mem hℓ hfit ha hi)
  have hV1 : u.V 1 ∈ E₀ := by
    refine mem_inactive_of_cell _ fun t ht a ha s hi => ?_
    rw [hu.leading_velocity t ht a ha s]
    rcases hcellZero t ht a ha hi with ⟨_, h0, _⟩ | h0
    · rw [h0, zero_smul]
    · simp only [S5.leading, h0, zero_mul, zero_smul, smul_zero]
  have hp1 : u.p 1 ∈ F₀ := by
    refine mem_inactive_of_cell _ fun t ht a ha s hi => ?_
    rw [hu.leading_pressure t ht a ha s]
    rcases hcellZero t ht a ha hi with ⟨_, h0, _⟩ | h0
    · rw [h0, zero_mul]
    · simp only [S5.leadingPressure, wavePressureCoefficient, h0, mul_zero, zero_mul, zero_div,
        neg_zero]
  have hS : S ∈ E₀ := by
    refine mem_inactive_of_cell _ fun t ht a ha s hi => ?_
    rw [hu.activation t ht a ha s]
    rcases hcellZero t ht a ha hi with ⟨_, _, h0⟩ | h0
    · rw [h0, zero_smul]
    · simp only [S5.leading, h0, zero_mul, zero_smul, smul_zero]
  have hcS : cS ∈ E₀ := curlCorrection_mem_inactive d hS
  have hC1 : S5.Cd u 1 ∈ E₀ := by
    rw [hu.first_correction]
    exact E₀.zero_mem
  have hBavg : ∀ j, 1 ≤ j → j ≤ P → (S5.ops d).average (u.B j) = u.B j := by
    intro j h1 h2
    rcases lt_or_eq_of_le h1 with h | h
    · exact (hu.mean j (Finset.mem_Icc.mpr ⟨h, h2⟩)).1.phase_independent
    · subst j
      rw [hu.first_mean.1, map_zero]
  -- the ordered recursion
  have hlev : ∀ i, 1 ≤ i → i ≤ P → u.V i ∈ E₀ ∧ u.p i ∈ F₀ ∧ S5.Cd u (i + 1) ∈ E₀ := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi1 hiP
      have hVp : u.V i ∈ E₀ ∧ u.p i ∈ F₀ := by
        rcases lt_or_eq_of_le hi1 with hi2 | hi2
        · have hY : ∀ j, 1 ≤ j → j < i → S5.Yd u j ∈ E₀ := by
            intro j hj1 hji
            refine E₀.add_mem (ih j hji hj1 (by omega)).1 ?_
            rcases lt_or_eq_of_le hj1 with hj2 | hj2
            · have h := (ih (j - 1) (by omega) (by omega) (by omega)).2.2
              rwa [show j - 1 + 1 = j by omega] at h
            · rw [← hj2]
              exact hC1
          have hCi : S5.Cd u i ∈ E₀ := by
            have h := (ih (i - 1) (by omega) (by omega) (by omega)).2.2
            rwa [show i - 1 + 1 = i by omega] at h
          have hpi : u.p (i - 1) ∈ F₀ := (ih (i - 1) (by omega) (by omega) (by omega)).2.1
          have hsrc := transverseSource_mem_inactive d u cS hY hCi hpi hcS
            (fun j h1 h2 => hBavg j h1 (by omega))
          have hiP' : i ∈ Finset.Icc 2 P := Finset.mem_Icc.mpr ⟨by omega, hiP⟩
          have havg := average_transverseSource d u cS (p := i)
            (fun j hj => hBavg j (by rw [Finset.mem_Icc] at hj; omega)
              (by rw [Finset.mem_Icc] at hj; omega))
          exact transverseSolution_mem_inactive d (hu.transverse i hiP') havg hsrc
        · subst i
          exact ⟨hV1, hp1⟩
      refine ⟨hVp.1, hVp.2, ?_⟩
      rw [hu.correction i (Finset.mem_Icc.mpr ⟨hi1, hiP⟩)]
      exact curlCorrection_mem_inactive d hVp.1
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [Finset.mem_Icc] at hi
    exact ⟨(hlev i hi.1 hi.2).1, (hlev i hi.1 hi.2).2.1⟩
  · rw [Finset.mem_Icc] at hi
    rcases lt_or_eq_of_le hi.1 with h | h
    · have h' := (hlev (i - 1) (by omega) (by omega)).2.2
      rwa [show i - 1 + 1 = i by omega] at h'
    · rw [← h]
      exact hC1
  · rw [Finset.mem_Icc] at hi
    have hY : ∀ j, 1 ≤ j → j < i → S5.Yd u j ∈ E₀ := by
      intro j hj1 hji
      refine E₀.add_mem (hlev j hj1 (by omega)).1 ?_
      rcases lt_or_eq_of_le hj1 with hj2 | hj2
      · have h := (hlev (j - 1) (by omega) (by omega)).2.2
        rwa [show j - 1 + 1 = j by omega] at h
      · rw [← hj2]
        exact hC1
    have hCi : S5.Cd u i ∈ E₀ := by
      have h := (hlev (i - 1) (by omega) (by omega)).2.2
      rwa [show i - 1 + 1 = i by omega] at h
    exact transverseSource_mem_inactive d u cS hY hCi (hlev (i - 1) (by omega) (by omega)).2.1
      hcS (fun j h1 h2 => hBavg j h1 (by omega))

end

end TorusEuler.Paper.Lib.S5a
