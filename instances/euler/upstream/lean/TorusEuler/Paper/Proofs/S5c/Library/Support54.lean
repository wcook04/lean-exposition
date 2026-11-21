import TorusEuler.Paper.Proofs.S5c.Library.Inactive
import TorusEuler.Paper.S5.Statements

/-!
# Supports and vanishing before `t₀`, from Proposition 5.4

The proof of Lemma 5.9 reads the supports of the profiles and their vanishing before the
activation time from Proposition 5.4 (`sections/08_exact_wave.tex:226`, `:266-267`; the
profiles are those of Proposition 5.4, `:1-7`). Proposition 5.4 (`Statement.proposition_5_4`)
states that the sources `f_p + f_p^S` (`2 ≤ p ≤ P`) are supported in `supp g` and vanish for
`t < t₀`. Here these source facts, taken from `h5_4`, give (by the transverse ODE of (5.15) and
its uniqueness, the generic argument of `Inactive.lean`) the vanishing of `V_p`, `𝗉_p`
(`2 ≤ p ≤ P`) on the inactive region, and the leading cell values and `C[·]` (a local operator)
give the rest. Nothing is derived from the recursion of the sources: the support of the sources
is the input from `h5_4`.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5c

open HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ

/-- **The leading pressure vanishes on the inactive region** (no use of Proposition 5.4): on the
label cell `𝗉₁ = χ̃ · (-c_𝐚) 𝗉_h` (`hu.leading_pressure`), `χ̃ = 0` for `t < t₀` (the cutoff) and
`c_𝐚 = 0` off `supp g` (the radial envelope), as in `08_exact_wave.tex:185-186`. -/
theorem IsExpansion.leadingPressure_mem_inactive (d : ParentGeometry hT U X k) {pU : Pressure}
    {t₀ : ℝ} {χ : PaperWaveCutoff t₀ T} {ℓ h : ℝ} {amp : ℝ → Vec3 → Vec3} {P : ℕ} {R S : VP}
    {u : HierarchyProfiles VP SP} (hu : S5.IsExpansion d pU χ ℓ h amp P R S u)
    (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) : u.p 1 ∈ inactiveVP T k ℝ t₀ ℓ := by
  refine mem_inactive_of_cell _ fun t ht a ha s hi => ?_
  rw [hu.leading_pressure t ht a ha s]
  rcases hi with hi | hi
  · rw [χ.zero_before t ht hi, zero_mul]
  · have h0 : radialEnvelope ℓ a = 0 := radialEnvelope_eq_zero_of_not_mem hℓ hfit ha hi
    simp only [S5.leadingPressure, wavePressureCoefficient, h0, mul_zero, zero_mul, zero_div,
      neg_zero]

/-- **Supports of the expansion, given the support of the sources.** If the sources
`f_p + f_p^S` (`2 ≤ p ≤ P`) lie in the inactive submodule, then so do `V_p`, `𝗉_p`
(`1 ≤ p ≤ P`) and `C_p` (`1 ≤ p ≤ P + 1`). The leading pair and the activation term vanish
there by their cell values (3.7), (3.8); for `p ≥ 2` the transverse equation (5.15) with the
zero initial datum is solved by the library ODE solve, which keeps the inactive region, and
`C_{p+1} = C[V_p]`. -/
theorem IsExpansion.inactive_of_sources (d : ParentGeometry hT U X k) {pU : Pressure} {t₀ : ℝ}
    {χ : PaperWaveCutoff t₀ T} {ℓ h : ℝ} {amp : ℝ → Vec3 → Vec3} {P : ℕ} {R S : VP}
    {u : HierarchyProfiles VP SP} (hu : S5.IsExpansion d pU χ ℓ h amp P R S u)
    (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2)
    (hsrc : ∀ i ∈ Finset.Icc 2 P,
      S5.oscSource (S5.ops d) u (S5.curlCorrection d S) i + S5.suppSource (S5.ops d) u i ∈
        inactiveVP T k Vec3 t₀ ℓ) :
    (∀ i ∈ Finset.Icc 1 P, u.V i ∈ inactiveVP T k Vec3 t₀ ℓ ∧ u.p i ∈ inactiveVP T k ℝ t₀ ℓ) ∧
    (∀ i ∈ Finset.Icc 1 (P + 1), S5.Cd u i ∈ inactiveVP T k Vec3 t₀ ℓ) ∧
    (∀ i ∈ Finset.Icc 2 P,
      S5.oscSource (S5.ops d) u (S5.curlCorrection d S) i + S5.suppSource (S5.ops d) u i ∈
        inactiveVP T k Vec3 t₀ ℓ) := by
  let E₀ := inactiveVP T k Vec3 t₀ ℓ
  let F₀ := inactiveVP T k ℝ t₀ ℓ
  let cS := S5.curlCorrection d S
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
  have hp1 : u.p 1 ∈ F₀ := IsExpansion.leadingPressure_mem_inactive d hu hℓ hfit
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
  have hlev : ∀ i, 1 ≤ i → i ≤ P → u.V i ∈ E₀ ∧ u.p i ∈ F₀ := by
    intro i hi1 hiP
    rcases lt_or_eq_of_le hi1 with hi2 | hi2
    · have hiP' : i ∈ Finset.Icc 2 P := Finset.mem_Icc.mpr ⟨by omega, hiP⟩
      have havg := average_transverseSource d u cS (p := i)
        (fun j hj => hBavg j (by rw [Finset.mem_Icc] at hj; omega)
          (by rw [Finset.mem_Icc] at hj; omega))
      exact transverseSolution_mem_inactive d (hu.transverse i hiP') havg (hsrc i hiP')
    · subst i
      exact ⟨hV1, hp1⟩
  refine ⟨fun i hi => ?_, fun i hi => ?_, hsrc⟩
  · rw [Finset.mem_Icc] at hi
    exact hlev i hi.1 hi.2
  · rw [Finset.mem_Icc] at hi
    rcases lt_or_eq_of_le hi.1 with h | h
    · have h' := (hlev (i - 1) (by omega) (by omega)).1
      have hc := hu.correction (i - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      rw [show i - 1 + 1 = i by omega] at hc
      rw [hc]
      exact curlCorrection_mem_inactive d h'
    · rw [← h]
      exact hC1

/-- **Supports and vanishing before `t₀`, from Proposition 5.4** (`h5_4`). For every expansion
(`S5.IsExpansion`) of depth `P ≥ 2` and `a ≥ a₀(5.4)`: `V_p`, `𝗉_p` (`1 ≤ p ≤ P`), `C_p`
(`1 ≤ p ≤ P + 1`) and `f_p + f_p^S` (`2 ≤ p ≤ P`) vanish where `t < t₀` or `a ∉ supp g`
(`08_exact_wave.tex:226`, `:266-267`). The vanishing for `t < t₀` of `V_p`, `𝗉_p`, `C_p` is read from the
corresponding clause of Proposition 5.4; the support in `supp g` of the individual `V_p`, `𝗉_p`
(`p ≥ 2`), which Proposition 5.4 states only for the sources and for `W_osc`, is derived from the
support of the sources by `IsExpansion.inactive_of_sources` (transverse ODE uniqueness). -/
theorem inactive_of_prop54 (h5_4 : Statement.proposition_5_4) :
    ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a → 3 ≤ a →
    ∀ {T : ℝ} (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
      {D lam t₀ : ℝ} {center : ℝ → Vec3} (d : ParentGeometry hT U X k) (χ : PaperWaveCutoff t₀ T),
      S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ → S5.Origin T U X k D lam t₀ center →
      ∀ amp : ℝ → Vec3 → Vec3, S5.IsSeed U X k t₀ T center amp →
      ∀ P : ℕ, 2 ≤ P →
      ∀ (R S : HierarchyTwistedProfile T k Vec3)
        (u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)),
        S5.IsExpansion d pU χ (S5.radius D a) (S5.width lam) amp P R S u →
        (∀ i ∈ Finset.Icc 1 P, u.V i ∈ inactiveVP T k Vec3 t₀ (S5.radius D a) ∧
          u.p i ∈ inactiveVP T k ℝ t₀ (S5.radius D a)) ∧
        (∀ i ∈ Finset.Icc 1 (P + 1), S5.Cd u i ∈ inactiveVP T k Vec3 t₀ (S5.radius D a)) ∧
        (∀ i ∈ Finset.Icc 2 P,
          S5.oscSource (S5.ops d) u (S5.curlCorrection d S) i + S5.suppSource (S5.ops d) u i ∈
            inactiveVP T k Vec3 t₀ (S5.radius D a)) := by
  obtain ⟨a₀, h⟩ := h5_4
  refine ⟨a₀, fun a ha ha3 T hT U X pU k D lam t₀ center d χ hP hL hO amp hamp P hP2 R S u hu => ?_⟩
  have hℓ : 0 < S5.radius D a := Bridge.radius_pos hP a
  have hfit : 2 * S5.radius D a < 1 / 2 := Bridge.radius_fits hP.scale_ge_two ha3
  obtain ⟨-, h⟩ := h a ha hT d χ hP hL hO
  obtain ⟨-, -, h⟩ := h amp hamp P hP2
  obtain ⟨-, -, -, -, -, hsupp, hvan, -⟩ := h R S u hu
  have hres := IsExpansion.inactive_of_sources d hu hℓ hfit fun i hi x hx => by
    obtain ⟨⟨ht, -⟩, hi'⟩ := hx
    rcases hi' with h0 | h0
    · exact (hvan x.1 ht h0 x.2.1 x.2.2).2.2 i hi
    · exact hsupp i hi x.1 ht x.2.1 h0 x.2.2
  obtain ⟨hVp, hCd, hsrc⟩ := hres
  refine ⟨fun i hi => ⟨fun x hx => ?_, fun x hx => ?_⟩, fun i hi x hx => ?_, hsrc⟩
  · rcases hx.2 with h0 | h0
    · exact (hvan x.1 hx.1.1 h0 x.2.1 x.2.2).1 i hi |>.1
    · exact (hVp i hi).1 hx
  · rcases hx.2 with h0 | h0
    · exact (hvan x.1 hx.1.1 h0 x.2.1 x.2.2).1 i hi |>.2
    · exact (hVp i hi).2 hx
  · rcases hx.2 with h0 | h0
    · exact (hvan x.1 hx.1.1 h0 x.2.1 x.2.2).2.1 i hi
    · exact hCd i hi hx

end

end TorusEuler.Paper.Lib.S5c
