import TorusEuler.PaperAppendixB
import TorusEuler.PaperAppendixBBernsteinReal
import TorusEuler.PaperAppendixBLInfinityReal
import TorusEuler.PaperAppendixDFields
import TorusEuler.PaperAppendixDMultiIndex
import TorusEuler.PaperAppendixDLifting
import TorusEuler.Paper.SBD.Library.Words

/-! # Vocabulary for Appendices B and D of the latest manuscript

Definitions used by the statements of Lemma B.1 and Lemmas D.1, D.2, D.3
(`TorusEuler/Paper/SBD/Statements.lean`). They only name objects fixed in the
text of Appendices B and D: the hypotheses on the cutoff symbol, the field
norms (D.1), the half-Hölder norm `‖·‖_{[n],1/2}`, the phase operators of
(D.5), the coefficient sizes `|c|_m`, `|c|_{m,1/2}` and the power bound (D.6).
None of them chooses an object from the content of another numbered result.

The last section proves the identities that the text uses without comment:
for a phase-independent field `c(t, a)` only the terms with `j = 0` occur in
(D.1) (`fieldNorm_phaseIndependent`, `CoefficientNormFinite.fieldNormFinite`),
and the weighted word norms are the sums `∑_{m≤n} ℓ_*^m |c|_m` and
`∑_{m≤n} ℓ_*^m |c|_{m,1/2}` (`coefficientNorm_eq_labelWordNorm`,
`holderFieldNorm_eq_sum`). They are calculus glue, not the content of a
numbered result.

The vocabulary lives in the namespaces `TorusEuler.Paper.AppendixB` and
`TorusEuler.Paper.AppendixD`. -/

open scoped ContDiff

namespace TorusEuler.Paper

namespace AppendixB

/-- The hypotheses on the symbol `ψ` fixed at the start of Appendix B
(`sections/appB_cutoff.tex:2-3`): `ψ` is smooth, `0 ≤ ψ ≤ 1`, `ψ = 1` on
`|ζ| ≤ 1`, and `ψ = 0` outside `|ζ| ≤ 2` (so `supp ψ ⊆ {|ζ| ≤ 2}` and
`ψ ∈ C_c^∞(ℝ³)`).

Representation: the manuscript assumes `ψ` radial; only its consequence
`ψ(-ζ) = ψ(ζ)` (evenness) is recorded, which makes the statements that take
this structure as hypothesis more general (`CutoffSymbol.of_radial` derives
the structure from the manuscript's hypotheses). -/
structure CutoffSymbol (ψ : Vec3 → ℝ) : Prop where
  /-- `ψ ∈ C^∞(ℝ³)`. -/
  smooth : ContDiff ℝ ∞ ψ
  /-- `0 ≤ ψ`. -/
  nonneg : ∀ ξ, 0 ≤ ψ ξ
  /-- `ψ ≤ 1`. -/
  le_one : ∀ ξ, ψ ξ ≤ 1
  /-- `ψ = 1` on `|ζ| ≤ 1`. -/
  eq_one : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1
  /-- `supp ψ ⊆ {|ζ| ≤ 2}`. -/
  eq_zero : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0
  /-- `ψ` is even (a consequence of radiality). -/
  even : Function.Even ψ

/-- The manuscript's hypotheses on `ψ` (smooth, radial, `0 ≤ ψ ≤ 1`, `ψ = 1`
on `|ζ| ≤ 1`, `ψ = 0` outside `|ζ| ≤ 2`) give `CutoffSymbol ψ`. Radiality is
stated as: `ψ` takes equal values at points of equal norm. -/
theorem CutoffSymbol.of_radial {ψ : Vec3 → ℝ} (hsmooth : ContDiff ℝ ∞ ψ)
    (hradial : ∀ ξ η : Vec3, ‖ξ‖ = ‖η‖ → ψ ξ = ψ η)
    (hnonneg : ∀ ξ, 0 ≤ ψ ξ) (hle : ∀ ξ, ψ ξ ≤ 1)
    (hone : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) (hzero : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) :
    CutoffSymbol ψ :=
  ⟨hsmooth, hnonneg, hle, hone, hzero, fun ξ => hradial (-ξ) ξ (norm_neg ξ)⟩

/-- The fixed smooth cutoff `dyadicMultiplierCutoff` used by the construction
satisfies the hypotheses of Appendix B. -/
theorem cutoffSymbol_dyadicMultiplierCutoff : CutoffSymbol (⇑dyadicMultiplierCutoff) :=
  ⟨dyadicMultiplierCutoff_smooth, fun _ => dyadicMultiplierCutoff.nonneg,
    fun _ => dyadicMultiplierCutoff.le_one, dyadicMultiplierCutoff_unit,
    fun ξ h => dyadicMultiplierCutoff_zero ξ h.le, dyadicMultiplierCutoff.neg⟩

end AppendixB

namespace AppendixD

section Fields

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The label derivative `∂_{a_i} f` of a field `f(t, a, s)`, written
`f t (a, s)`, in the `i`-th coordinate direction of the label `a ∈ ℝ³`. -/
noncomputable def labelPartial (i : Fin 3) (f : I → Vec3 × ℝ → E) : I → Vec3 × ℝ → E :=
  fun t => phaseDirectionalDerivative (fun _ => phaseCoordinateDirection (.inl i)) (f t)

/-- The phase derivative `∂_s f` of a field `f(t, a, s)`, written `f t (a, s)`. -/
noncomputable def phasePartial (f : I → Vec3 × ℝ → E) : I → Vec3 × ℝ → E :=
  fun t => phaseDirectionalDerivative (fun _ => phaseCoordinateDirection (.inr ())) (f t)

/-- The phase average `⟨f⟩(t, a) = ∫₀¹ f(t, a, s) ds`, viewed as a field of
`(t, a, s)` that does not depend on `s`. -/
noncomputable def phaseAverage (f : I → Vec3 × ℝ → E) : I → Vec3 × ℝ → E :=
  fun t x => phaseMean (fun s => f t (x.1, s))

/-- The phase primitive `∂_s^{-1} f`: the primitive `∫₀^s f(t, a, σ) dσ` minus
its phase average. For a field of period one and zero phase average it is
the zero-mean periodic primitive of (D.5). -/
noncomputable def phaseInverse (f : I → Vec3 × ℝ → E) : I → Vec3 × ℝ → E :=
  fun t x => phasePrimitive (fun s => f t (x.1, s)) x.2

/-- The field `f / γ`, with the time weight `γ(t)` of (D.1). -/
noncomputable def weighted (γ : I → ℝ) (f : I → Vec3 × ℝ → E) : I → Vec3 × ℝ → E :=
  fun t x => (γ t)⁻¹ • f t x

/-- The finite norm (D.1) `‖f‖_{[n]} = ∑_{m+j≤n} ℓ_*^m h^j |∂_s^j f|_m`, where
`|g|_m = ∑_{|β|=m} sup |∂_a^β g|` and the supremum runs over all times, labels
and phases. `ℓ` is the envelope radius `ℓ_*` and `h` the profile width.

Representation: the sum runs over the nondecreasing words in the four
weighted directions `ℓ e_1, ℓ e_2, ℓ e_3` (labels) and `h ∂_s` (phase) of
length at most `n` (`hierarchyAdmissibleWords (Fin 4) n`), one word for each
pair `(β, j)` with `|β| + j ≤ n`; the term of a word is the supremum of the
norm of the corresponding weighted derivative, which is
`ℓ^{|β|} h^j sup |∂_a^β ∂_s^j f|`. Labels range over `ℝ³` (the lift of the
torus). The value is a genuine supremum only when the jets are bounded, which
`FieldNormFinite` records. -/
noncomputable def fieldNorm (ℓ h : ℝ) (n : ℕ) (f : I → Vec3 × ℝ → E) : ℝ :=
  hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n f

/-- The weighted finite norm `‖f‖_{[n],γ} = ‖f/γ‖_{[n]}` of (D.1). The time
domain `I` is arbitrary, so the norm can be taken on `[t₀, T]` or on any closed
subinterval. -/
noncomputable def weightedFieldNorm (ℓ h : ℝ) (γ : I → ℝ) (n : ℕ)
    (f : I → Vec3 × ℝ → E) : ℝ :=
  fieldNorm ℓ h n (weighted γ f)

/-- The field `f` is smooth in `(a, s)` at every time and every weighted jet
entering `‖f‖_{[n]}` of (D.1) is bounded, so that `fieldNorm ℓ h n f` is the
finite norm of the manuscript. -/
def FieldNormFinite (ℓ h : ℝ) (n : ℕ) (f : I → Vec3 × ℝ → E) : Prop :=
  (∀ t, ContDiff ℝ ∞ (f t)) ∧
    ∀ w ∈ hierarchyAdmissibleWords (Fin 4) n,
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w f)

/-- The half-Hölder finite norm of a phase-independent field `c(t, a)`
(`sections/appD_finite_norms.tex:25-29`):
`‖c‖_{[n],1/2} = ∑_{m≤n} ℓ_*^m |c|_{m,1/2}`, with
`|c|_{m,1/2} = ∑_{|β|=m} sup_t ‖∂_a^β c(t)‖_{C^{0,1/2}}`.

Representation: one nondecreasing word in the weighted label directions
`ℓ e_i` for each multi-index `β` with `|β| ≤ n`; the term of a word is the
supremum over times of the maximum of the supremum norm and the 1/2-Hölder
seminorm of `ℓ^{|β|} ∂_a^β c(t)` (`hierarchyJetValues True`). The manuscript's
`C^{0,1/2}` norm is the sum of these two quantities, so the two norms differ
at most by a factor 2. -/
noncomputable def holderFieldNorm (ℓ : ℝ) (n : ℕ) (c : I → Vec3 → E) : ℝ :=
  hierarchyFiniteWordNorm True (hierarchyLabelDirection ℓ) n c

/-- The phase-independent field `c` is smooth in `a` at every time and every
quantity entering `‖c‖_{[n],1/2}` is bounded. -/
def HolderFieldNormFinite (ℓ : ℝ) (n : ℕ) (c : I → Vec3 → E) : Prop :=
  (∀ t, ContDiff ℝ ∞ (c t)) ∧
    ∀ w ∈ hierarchyAdmissibleWords (Fin 3) n,
      BddAbove (hierarchyJetValues True (hierarchyLabelDirection ℓ) w c)

end Fields

section Coefficients

variable {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The size `|c|_m = ∑_{|β|=m} sup_{t,a} |∂_a^β c(t, a)|` of the label
derivatives of order `m` of a phase-independent field
(`sections/appD_finite_norms.tex:9`). Matrix-valued fields take values in a
normed space of linear maps, with the operator norm.

Representation: one nondecreasing coordinate word of length `m`
(`appendixCoefficientOrderWords m`) for each multi-index `β` with `|β| = m`. -/
noncomputable def coefficientOrderNorm (m : ℕ) (c : I → Vec3 → X) : ℝ :=
  ∑ w ∈ appendixCoefficientOrderWords m,
    sSup (hierarchyJetValues False (hierarchyLabelDirection 1) w c)

/-- The finite norm (D.1) of a phase-independent coefficient,
`‖c‖_{[n]} = ∑_{m≤n} ℓ_*^m |c|_m` (only the terms with `j = 0` occur,
`sections/appD_finite_norms.tex:22-23`). For `ℓ ≥ 0` and smooth `c` it equals
`fieldNorm ℓ h n` of the field `(t, a, s) ↦ c(t, a)` for every `h`
(`fieldNorm_phaseIndependent`) and the weighted label word norm
(`coefficientNorm_eq_labelWordNorm`). -/
noncomputable def coefficientNorm (ℓ : ℝ) (n : ℕ) (c : I → Vec3 → X) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), ℓ ^ m * coefficientOrderNorm m c

/-- The size `|c|_{m,1/2} = ∑_{|β|=m} sup_t ‖∂_a^β c(t)‖_{C^{0,1/2}}` of a
phase-independent field (`sections/appD_finite_norms.tex:26`).

Representation: one nondecreasing coordinate word of length `m` for each
multi-index `β` with `|β| = m`; the term of a word is the supremum over times
of the maximum of the supremum norm and the 1/2-Hölder seminorm of
`∂_a^β c(t)` (`hierarchyJetValues True`), which differs from the manuscript's
sum of the two by a factor at most 2. For `ℓ ≥ 0` and smooth `c`,
`‖c‖_{[n],1/2} = ∑_{m≤n} ℓ_*^m |c|_{m,1/2}` is `holderFieldNorm_eq_sum`. -/
noncomputable def holderOrderNorm (m : ℕ) (c : I → Vec3 → X) : ℝ :=
  ∑ w ∈ appendixCoefficientOrderWords m,
    sSup (hierarchyJetValues True (hierarchyLabelDirection 1) w c)

/-- The phase-independent field `c` is smooth in `a` at every time and the
suprema `sup_{t,a} |∂_a^β c|` with `|β| ≤ n` entering `‖c‖_{[n]}` are finite.
It gives `FieldNormFinite` for the field `(t, a, s) ↦ c(t, a)`
(`CoefficientNormFinite.fieldNormFinite`). -/
def CoefficientNormFinite (n : ℕ) (c : I → Vec3 → X) : Prop :=
  (∀ t, ContDiff ℝ ∞ (c t)) ∧
    ∀ w ∈ hierarchyAdmissibleWords (Fin 3) n,
      BddAbove (hierarchyJetValues False (hierarchyLabelDirection 1) w c)

/-- The power bound (D.6) `|c|_m ≤ C_m 𝖣^{a(m+1)}` for all `m ≥ 0`, for a
smooth phase-independent coefficient `c`, with fixed-order constants `C` and
absolute exponent `a`. Every supremum entering `|c|_m` is finite.

Representation: the exponent `a` is a natural number, while the manuscript's
absolute exponent `C` of (D.6) is a real constant. Since `𝖣 ≥ 1`, a bound with
a real exponent `C` implies the bound with `a = ⌈C⌉`, so (D.6) with exponent
`C` is `CoefficientPower C_m 𝖣 ⌈C⌉`. -/
def CoefficientPower (C : ℕ → ℝ) (D : ℝ) (a : ℕ) (c : I → Vec3 → X) : Prop :=
  (∀ t, ContDiff ℝ ∞ (c t)) ∧
    (∀ m, ∀ w ∈ appendixCoefficientOrderWords m,
      BddAbove (hierarchyJetValues False (hierarchyLabelDirection 1) w c)) ∧
    ∀ m, coefficientOrderNorm m c ≤ C m * D ^ (a * (m + 1))

end Coefficients

section PhaseIndependent

open scoped Pointwise

variable {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Each weighted label derivative contributes one factor `r`: the quantities
measured on a word in the directions `r e_i` are `|r|^{|β|}` times those in the
unit directions. -/
theorem jetValues_labelDirection (holder : Prop) (r : ℝ) (w : List (Fin 3))
    {c : I → Vec3 → X} (hc : ∀ t, ContDiff ℝ ∞ (c t)) :
    hierarchyJetValues holder (hierarchyLabelDirection r) w c =
      ‖r ^ w.length‖ • hierarchyJetValues holder (hierarchyLabelDirection 1) w c := by
  have hword (s : ℝ) (t : I) (x : Vec3) :
      phaseOperatorWord (hierarchyLabelDirection s) w (c t) x =
        s ^ w.length • phaseOperatorWord (fun i (_ : Vec3) => coordinateDirection i) w (c t) x := by
    have h := phaseOperatorWord_scaled_directions (fun _ : Fin 3 => s)
      (D := fun i (_ : Vec3) => coordinateDirection i) (fun _ => contDiff_const) (hc t) w x
    rw [List.map_const', List.prod_replicate] at h
    exact h
  have hfun (t : I) : phaseOperatorWord (hierarchyLabelDirection r) w (c t) =
      phaseOperatorWord (hierarchyLabelDirection 1) w ((r ^ w.length • c) t) := by
    funext x
    have h := phaseOperatorWord_const_smul (D := hierarchyLabelDirection 1)
      (fun _ => contDiff_const) (hc t) (r ^ w.length) w x
    rw [hword 1 t x, one_pow, one_smul] at h
    rw [hword r t x]
    exact h.symm
  calc hierarchyJetValues holder (hierarchyLabelDirection r) w c
      = hierarchyJetValues holder (hierarchyLabelDirection 1) w (r ^ w.length • c) := by
        simp only [hierarchyJetValues, hfun]
    _ = _ := actualJetValues_smul holder (fun _ => contDiff_const) w hc _

/-- The weighted label word norm of a phase-independent field is the sum over
the orders `m ≤ n` of `ℓ^m` times the sum over the multi-indices of order `m`,
for the supremum norm (`holder = False`) and for the half-Hölder norm
(`holder = True`). -/
theorem labelWordNorm_eq_sum (holder : Prop) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (n : ℕ)
    {c : I → Vec3 → X} (hc : ∀ t, ContDiff ℝ ∞ (c t)) :
    hierarchyFiniteWordNorm holder (hierarchyLabelDirection ℓ) n c =
      ∑ m ∈ Finset.range (n + 1), ℓ ^ m * ∑ w ∈ appendixCoefficientOrderWords m,
        sSup (hierarchyJetValues holder (hierarchyLabelDirection 1) w c) := by
  classical
  have hterm (w : List (Fin 3)) :
      sSup (hierarchyJetValues holder (hierarchyLabelDirection ℓ) w c) =
        ℓ ^ w.length * sSup (hierarchyJetValues holder (hierarchyLabelDirection 1) w c) := by
    rw [jetValues_labelDirection holder ℓ w hc, Real.sSup_smul_of_nonneg (norm_nonneg _),
      smul_eq_mul, Real.norm_of_nonneg (pow_nonneg hℓ _)]
  unfold hierarchyFiniteWordNorm
  simp_rw [hterm]
  rw [← Finset.sum_fiberwise_of_maps_to (s := hierarchyAdmissibleWords (Fin 3) n)
    (t := Finset.range (n + 1)) (g := List.length)
    (fun w hw => Finset.mem_range.mpr (Nat.lt_succ_of_le (mem_hierarchyAdmissibleWords.mp hw).1))]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mul_sum]
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hset : ((hierarchyAdmissibleWords (Fin 3) n).filter fun w => w.length = m) =
      appendixCoefficientOrderWords m := by
    ext w
    simp only [appendixCoefficientOrderWords, Finset.mem_filter, mem_hierarchyAdmissibleWords]
    constructor
    · rintro ⟨⟨_, hs⟩, hl⟩
      exact ⟨⟨hl.le, hs⟩, hl⟩
    · rintro ⟨⟨_, hs⟩, hl⟩
      exact ⟨⟨by omega, hs⟩, hl⟩
  rw [hset]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [(Finset.mem_filter.mp hw).2]

/-- `‖c‖_{[n]} = ∑_{m≤n} ℓ_*^m |c|_m` is the weighted label word norm. -/
theorem coefficientNorm_eq_labelWordNorm {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (n : ℕ)
    {c : I → Vec3 → X} (hc : ∀ t, ContDiff ℝ ∞ (c t)) :
    coefficientNorm ℓ n c = hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) n c :=
  (labelWordNorm_eq_sum False hℓ n hc).symm

/-- `‖c‖_{[n],1/2} = ∑_{m≤n} ℓ_*^m |c|_{m,1/2}`
(`sections/appD_finite_norms.tex:26-28`). -/
theorem holderFieldNorm_eq_sum {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (n : ℕ)
    {c : I → Vec3 → X} (hc : ∀ t, ContDiff ℝ ∞ (c t)) :
    holderFieldNorm ℓ n c = ∑ m ∈ Finset.range (n + 1), ℓ ^ m * holderOrderNorm m c :=
  labelWordNorm_eq_sum True hℓ n hc

/-- For a phase-independent field only the terms with `j = 0` occur in (D.1)
(`sections/appD_finite_norms.tex:22-23`): the norm `‖·‖_{[n]}` of the field
`(t, a, s) ↦ c(t, a)` is `‖c‖_{[n]} = ∑_{m≤n} ℓ_*^m |c|_m`, for every
profile width `h`. -/
theorem fieldNorm_phaseIndependent {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (h : ℝ) (n : ℕ)
    {c : I → Vec3 → X} (hc : ∀ t, ContDiff ℝ ∞ (c t)) :
    fieldNorm ℓ h n (fun t (x : Vec3 × ℝ) => c t x.1) = coefficientNorm ℓ n c := by
  rw [coefficientNorm_eq_labelWordNorm hℓ n hc]
  exact hierarchyFiniteMixedWordNorm_phaseIndependent_eq_label ℓ h n hc

/-- If `‖c‖_{[n]}` is finite, so is the norm (D.1) of the field
`(t, a, s) ↦ c(t, a)`, for all weights `ℓ`, `h`. -/
theorem CoefficientNormFinite.fieldNormFinite {n : ℕ} {c : I → Vec3 → X}
    (hc : CoefficientNormFinite n c) (ℓ h : ℝ) :
    FieldNormFinite ℓ h n (fun t (x : Vec3 × ℝ) => c t x.1) := by
  classical
  refine ⟨fun t => (hc.1 t).comp contDiff_fst, fun w hw => ?_⟩
  let d (i : Fin 4) := hierarchyMixedDirection ℓ h i ((0 : Vec3), (0 : ℝ))
  have hlift (u : List (Fin 4)) (t : I) :
      phaseOperatorWord (hierarchyMixedDirection ℓ h) u (fun x : Vec3 × ℝ => c t x.1) =
        phaseOperatorWord (fun i (_ : Vec3) => (d i).1) u (c t) ∘ Prod.fst :=
    Lib.SBD.word_fst_of_constant d (hc.1 t) u
  by_cases hl : Fin.last 3 ∈ w
  · have hz (t : I) :
        phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun x : Vec3 × ℝ => c t x.1) = 0 := by
      rw [hlift w t, Lib.SBD.word_eq_zero_of_zero_letter (fun i _ => (d i).1) (c t) _ ?_ hl]
      · rfl
      · funext a
        unfold d hierarchyMixedDirection
        rw [Fin.lastCases_last]
        simp [phaseCoordinateDirection]
    refine ⟨0, ?_⟩
    rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hH, _⟩)
    · exact le_rfl
    · simp only [hz, Pi.zero_apply, norm_zero, le_refl]
    · exact hH.elim
  · obtain ⟨v, rfl⟩ := Lib.SBD.list_eq_castSucc_map_of_not_mem_last hl
    have hv : v ∈ hierarchyAdmissibleWords (Fin 3) n := by
      obtain ⟨hlen, hs⟩ := mem_hierarchyAdmissibleWords.mp hw
      refine mem_hierarchyAdmissibleWords.mpr ⟨by simpa only [List.length_map] using hlen, ?_⟩
      simpa only [List.pairwise_map, Fin.castSucc_le_castSucc_iff] using hs
    have hD : (fun (i : Fin 3) (_ : Vec3) => (d i.castSucc).1) = hierarchyLabelDirection ℓ := by
      funext i a
      simp [d, hierarchyMixedDirection, hierarchyLabelDirection, phaseCoordinateDirection]
    have hword (t : I) :
        phaseOperatorWord (hierarchyMixedDirection ℓ h) (v.map Fin.castSucc)
            (fun x : Vec3 × ℝ => c t x.1) =
          phaseOperatorWord (hierarchyLabelDirection ℓ) v (c t) ∘ Prod.fst := by
      rw [hlift, Lib.SBD.word_map_letters, hD]
    have hsub : hierarchyJetValues False (hierarchyMixedDirection ℓ h) (v.map Fin.castSucc)
          (fun t (x : Vec3 × ℝ) => c t x.1) ⊆
        hierarchyJetValues False (hierarchyLabelDirection ℓ) v c := by
      rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hH, _⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨t, x.1, by simp only [hword, Function.comp_apply]⟩)
      · exact hH.elim
    refine BddAbove.mono hsub ?_
    rw [jetValues_labelDirection False ℓ v hc.1]
    exact (hc.2 v hv).smul_of_nonneg (norm_nonneg _)

/-- The power bound (D.6) makes every norm `‖c‖_{[n]}` finite. -/
theorem CoefficientPower.coefficientNormFinite {C : ℕ → ℝ} {D : ℝ} {a : ℕ}
    {c : I → Vec3 → X} (hc : CoefficientPower C D a c) (n : ℕ) : CoefficientNormFinite n c :=
  ⟨hc.1, fun w hw => hc.2.1 w.length w (Finset.mem_filter.mpr
    ⟨mem_hierarchyAdmissibleWords.mpr ⟨le_rfl, (mem_hierarchyAdmissibleWords.mp hw).2⟩, rfl⟩)⟩

end PhaseIndependent

end AppendixD

end TorusEuler.Paper
