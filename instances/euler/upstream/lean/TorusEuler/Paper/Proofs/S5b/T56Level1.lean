import TorusEuler.Paper.Proofs.S5b.T56Twist
import TorusEuler.Paper.Proofs.S5b.Lemma58OddB

/-!
# Theorem 5.6, glue: time multipliers and the level one of the expansion

The fields of level one are `V₁ = χ̃ V`, `𝗉₁ = χ̃ q`, `S = χ̃' V` for the leading pair `(V, q)` of
**Lemma 5.5** (the unswitched oscillation `A₁`, `𝗉[A₁]` extended as twisted profiles): the two
agree on the label cell, hence everywhere by the lattice twist. The operators `C[·]`, `𝐝` act at
fixed time, and `∂_t + M` obeys the product rule, so that the linear term of `H₂` is
`χ̃[(∂_t+M)C[V] + 𝐝q]` (`relay_two_eq`; the terms in `χ̃'` cancel against `C[S]`,
TeX :570-571 "for `p = 2` this is the bound for `A₁`, with `f = 0` and `χ̃ ≤ 1`").
-/

open Set Filter
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.Paper.S5b

open AppendixD HierarchyTwistedProfile

noncomputable section

/-! ## Norms under a time multiplier -/

section Mult

variable {T : ℝ} {k : Vec3} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The norm (D.1) of a field on a time set only depends on the field on that set. -/
theorem fieldNorm_congr_on {ℓ h : ℝ} {A : Set ℝ} {τ : ℝ → ℝ} {n : ℕ} {f g : ℝ → Vec3 × ℝ → E}
    (hfg : ∀ t ∈ A, ∀ x, f t x = g t x) :
    S5.fieldNorm ℓ h A τ n f = S5.fieldNorm ℓ h A τ n g := by
  unfold S5.fieldNorm
  congr 1
  funext t x
  rw [hfg t t.2 x]

/-- **A time multiplier of modulus at most one does not increase the weighted norm**: if
`F = c G` on `[t₀,T]` and `|c| ≤ 1` there, then `‖F‖_{[n],γ} ≤ ‖G‖_{[n],γ}`. -/
theorem wNorm_smul_time_le (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) {ℓ h : ℝ}
    {γ : ℝ → ℝ} (hγc : ContinuousOn γ (Icc t₀ T)) (hγ : ∀ t ∈ Icc t₀ T, 0 < γ t) {c : ℝ → ℝ}
    (hc : ∀ t ∈ Icc t₀ T, |c t| ≤ 1) {F G : HierarchyTwistedProfile T k E}
    (hFG : ∀ t ∈ Icc t₀ T, ∀ x s, F.val.val.val (t, x, s) = c t • G.val.val.val (t, x, s)) (n : ℕ) :
    S5.wNorm ℓ h t₀ γ n F ≤ S5.wNorm ℓ h t₀ γ n G := by
  have hfin := Bridge.fieldNormFinite_weighted hT ℓ h n ht₀ htT hγc hγ G
  unfold S5.wNorm
  rw [fieldNorm_congr_on (g := fun t x => c t • G.val.val.val (t, x)) (fun t ht x => hFG t ht x.1 x.2)]
  exact fieldNorm_smul_time_le (τ := fun t => (γ t)⁻¹) hc n (f := fun t x => G.val.val.val (t, x))
    fun w hw => hfin.2 w hw

end Mult

/-! ## The curl completion and the label gradient act at fixed time -/

section Local

variable {T : ℝ} {k : Vec3}

/-- Copy of the private library lemma `wavePotential_smul_profile`
(`TorusEuler/PaperGenericSwitchCompletion.lean:11`): same statement and proof. -/
theorem wavePotential_smul_profile' (K : Vec3) (c : ℝ) (V : ℝ → Vec3) (s : ℝ) :
    wavePotential K (fun q => c • V q) s = c • wavePotential K V s := by
  have he : (fun q => (-(‖K‖ ^ 2)⁻¹) • cross3 K (c • V q)) =
      fun q => c • ((-(‖K‖ ^ 2)⁻¹) • cross3 K (V q)) := by
    funext q
    change (-(‖K‖ ^ 2)⁻¹) • cross3Left K (c • V q) =
      c • ((-(‖K‖ ^ 2)⁻¹) • cross3Left K (V q))
    rw [map_smul]
    exact smul_comm _ _ _
  unfold wavePotential
  rw [he]
  simp only [phasePrimitive, phaseOscillation, intervalIntegral.integral_smul,
    phaseMean_const_smul, smul_sub]

set_option maxHeartbeats 1000000 in
/-- **`C[·]` acts at fixed time**: if `W(t,·,·) = c V(t,·,·)` at one time `t` (for a constant `c`),
then `C[W](t,·,·) = c C[V](t,·,·)` (the curl completion is linear and uses only the profile at the
time `t`). -/
theorem complete_smul_time_eval (hT : 0 < T)
    (G : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)) (κ₀ V W : HierarchyTwistedProfile T k Vec3)
    (hPhase : HierarchyPeriodicProfile.PhaseIndependent κ₀.val.val)
    (hκ₀ : ∀ t ∈ Icc 0 T, ∀ a, κ₀.val.val.val (t, a, 0) ≠ 0)
    (hV : profilePhaseAverage hT V = 0) (hW : profilePhaseAverage hT W = 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) {c : ℝ}
    (hcW : ∀ b q, W.val.val.val (t, b, q) = c • V.val.val.val (t, b, q)) (a : Vec3) (s : ℝ) :
    (complete hT G κ₀ hPhase hκ₀ W).val.val.val (t, a, s) =
      c • (complete hT G κ₀ hPhase hκ₀ V).val.val.val (t, a, s) := by
  let Q := HierarchySmoothProfile.profileWavePotential hT κ₀.val.val hκ₀ W.val.val
  let Q' := HierarchySmoothProfile.profileWavePotential hT κ₀.val.val hκ₀ V.val.val
  have hQ : (fun b => Q.val (t, b, s)) = c • fun b => Q'.val (t, b, s) := by
    funext b
    rw [HierarchySmoothProfile.profileWavePotential_apply hT κ₀.val.val hκ₀ W.val.val ht,
      Pi.smul_apply, HierarchySmoothProfile.profileWavePotential_apply hT κ₀.val.val hκ₀ V.val.val ht,
      funext (hcW b)]
    exact wavePotential_smul_profile' _ _ _ _
  rw [complete_val_val_of_phaseMean_zero hT G κ₀ hPhase hκ₀ W hW,
    complete_val_val_of_phaseMean_zero hT G κ₀ hPhase hκ₀ V hV]
  change (HierarchySmoothProfile.profileSlowCurl hT G.val.val Q).val (t, a, s) =
    c • (HierarchySmoothProfile.profileSlowCurl hT G.val.val Q').val (t, a, s)
  rw [HierarchySmoothProfile.profileSlowCurl_apply hT G.val.val Q ht,
    HierarchySmoothProfile.profileSlowCurl_apply hT G.val.val Q' ht, hQ,
    fderiv_const_smul_field, Pi.smul_apply, ContinuousLinearMap.smul_comp, curlOfDerivative_smul]

/-- The label gradient on the slab: `(𝐝q)(x) = ∑_i ∂q(x)(0, (D_aX)⁻¹ e_i, 0) e_i`. -/
theorem ops_labelGrad_eval (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity}
    (d : ParentGeometry hT U X k) (q : HierarchyTwistedProfile T k ℝ) {x : HierarchyProfilePoint}
    (hx : x ∈ hierarchyProfileSlab T) :
    ((S5.ops d).labelGrad q).val.val.val x =
      ∑ i : Fin 3, fderivWithin ℝ q.val.val.val (hierarchyProfileSlab T) x
        (0, d.inverse.val.val.val x (EuclideanSpace.single i 1), 0) • EuclideanSpace.single i 1 :=
  HierarchySmoothProfile.labelGradient_apply hT d.inverse.val.val q.val.val hx

/-- **`𝐝` acts at fixed time**: if `q₁(r,·,·) = c(r) q(r,·,·)` on `[0,T]` for a smooth `c`, then
`(𝐝q₁)(t,a,s) = c(t) (𝐝q)(t,a,s)` (the label gradient has no time derivative). -/
theorem labelGrad_time_smul (hT : 0 < T) {U : Velocity} {X : ℝ → Velocity}
    (d : ParentGeometry hT U X k) (q q₁ : HierarchyTwistedProfile T k ℝ) {c : ℝ → ℝ}
    (hcs : ContDiffOn ℝ ∞ c (Icc 0 T))
    (hq₁ : ∀ r ∈ Icc 0 T, ∀ b σ, q₁.val.val.val (r, b, σ) = c r * q.val.val.val (r, b, σ))
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    ((S5.ops d).labelGrad q₁).val.val.val (t, a, s) =
      c t • ((S5.ops d).labelGrad q).val.val.val (t, a, s) := by
  have hx : (t, a, s) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  have e (q' : HierarchyTwistedProfile T k ℝ) := ops_labelGrad_eval hT d q' hx
  rw [e q₁, e q, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set w : HierarchyProfilePoint := (0, d.inverse.val.val.val (t, a, s) (EuclideanSpace.single i 1), 0)
    with hw
  have hU := uniqueDiffOn_hierarchyProfileSlab hT (t, a, s) hx
  have hqd : DifferentiableWithinAt ℝ q.val.val.val (hierarchyProfileSlab T) (t, a, s) :=
    ((HierarchySmoothProfile.smooth q.val.val).differentiableOn (by simp)) _ hx
  have hcd : DifferentiableWithinAt ℝ c (Icc 0 T) t :=
    (hcs.differentiableOn (by simp)) _ ht
  have hC : HasFDerivWithinAt (fun z : HierarchyProfilePoint => c z.1)
      (derivWithin c (Icc 0 T) t • ContinuousLinearMap.fst ℝ ℝ (Vec3 × ℝ))
      (hierarchyProfileSlab T) (t, a, s) :=
    HasDerivWithinAt.comp_hasFDerivWithinAt (t, a, s) (f := Prod.fst) hcd.hasDerivWithinAt
      hasFDerivWithinAt_fst (fun z hz => hz.1)
  have hProd := hC.mul hqd.hasFDerivWithinAt
  have hcongr : fderivWithin ℝ q₁.val.val.val (hierarchyProfileSlab T) (t, a, s) =
      fderivWithin ℝ (fun z : HierarchyProfilePoint => c z.1 * q.val.val.val z)
        (hierarchyProfileSlab T) (t, a, s) := by
    refine fderivWithin_congr (fun z hz => hq₁ z.1 hz.1 z.2.1 z.2.2) (hq₁ t ht a s)
  rw [hcongr, show fderivWithin ℝ (fun z : HierarchyProfilePoint => c z.1 * q.val.val.val z)
    (hierarchyProfileSlab T) (t, a, s) = _ from hProd.fderivWithin hU]
  simp [hw, smul_smul]

/-- Evaluation of a twisted profile at a point as a linear map. -/
def evalLM {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (z : HierarchyProfilePoint) :
    HierarchyTwistedProfile T k E →ₗ[ℝ] E :=
  (LinearMap.proj z).comp (((hierarchySmoothProfileSubmodule T E).subtype.comp
    (hierarchyPeriodicProfileSubmodule T E).subtype).comp (hierarchyTwistedProfileSubmodule T k E).subtype)

/-- Evaluation of a sum of profiles. -/
theorem eval_add {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : HierarchyTwistedProfile T k E) (z : HierarchyProfilePoint) :
    (f + g).val.val.val z = f.val.val.val z + g.val.val.val z := map_add (evalLM z) f g

/-- Evaluation of a difference of profiles. -/
theorem eval_sub {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : HierarchyTwistedProfile T k E) (z : HierarchyProfilePoint) :
    (f - g).val.val.val z = f.val.val.val z - g.val.val.val z := map_sub (evalLM z) f g

end Local

/-! ## Level one of the expansion in terms of the leading pair -/

section One

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
  {D lam t₀ : ℝ} {center : ℝ → Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3

/-- **`V₁ = χ̃ V`**: for a twisted profile `V` equal to `A₁` on `[t₀,T] × cell`, the first velocity
`V₁ = χ̃A₁` (on the cell) is `χ̃ V` on the whole slab (lattice twist; before `t₀` both vanish). -/
theorem V1_eq_smul (d : ParentGeometry hT U X k) {χ : PaperWaveCutoff t₀ T} {ℓ h : ℝ}
    {amp : ℝ → Vec3 → Vec3} {P : ℕ} {R S : VP}
    {u : HierarchyProfiles VP (HierarchyTwistedProfile T k ℝ)}
    (hu : S5.IsExpansion d pU χ ℓ h amp P R S u) (V : VP)
    (hV : ∀ t ∈ Icc t₀ T, ∀ x ∈ centeredCell, ∀ s,
      V.val.val.val (t, x, s) = S5.leading ℓ h amp t x s) :
    ∀ t ∈ Icc 0 T, ∀ x s, (u.V 1).val.val.val (t, x, s) = χ.value t • V.val.val.val (t, x, s) := by
  have hall := Lib.S5Bridge.forall_of_centeredCell (T := T) k
    (Q := fun z : HierarchyProfilePoint =>
      (u.V 1).val.val.val z = χ.value z.1 • V.val.val.val z)
    (fun t a s n hq => by
      change (u.V 1).val.val.val (t, a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ) =
        χ.value t • V.val.val.val (t, a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ)
      rw [HierarchyTwistedProfile.twistedSlice, HierarchyTwistedProfile.twistedSlice]
      exact hq)
    (fun t ht a ha s => by
      change (u.V 1).val.val.val (t, a, s) = χ.value t • V.val.val.val (t, a, s)
      rw [hu.leading_velocity t ht a ha s]
      by_cases hpre : t < t₀
      · rw [χ.zero_before t ht hpre, zero_smul, zero_smul]
      · rw [hV t ⟨not_lt.mp hpre, ht.2⟩ a ha s])
  exact fun t ht x s => hall (t, x, s) ⟨ht, mem_univ _⟩

/-- **`𝗉₁ = χ̃ q`** (the same for the pressure). -/
theorem p1_eq_smul (d : ParentGeometry hT U X k) {χ : PaperWaveCutoff t₀ T} {ℓ h : ℝ}
    {amp : ℝ → Vec3 → Vec3} {P : ℕ} {R S : VP}
    {u : HierarchyProfiles VP (HierarchyTwistedProfile T k ℝ)}
    (hu : S5.IsExpansion d pU χ ℓ h amp P R S u) (q : HierarchyTwistedProfile T k ℝ)
    (hq : ∀ t ∈ Icc t₀ T, ∀ x ∈ centeredCell, ∀ s,
      q.val.val.val (t, x, s) = S5.leadingPressure U X k ℓ h amp t x s) :
    ∀ t ∈ Icc 0 T, ∀ x s, (u.p 1).val.val.val (t, x, s) = χ.value t * q.val.val.val (t, x, s) := by
  have hall := Lib.S5Bridge.forall_of_centeredCell (T := T) k
    (Q := fun z : HierarchyProfilePoint =>
      (u.p 1).val.val.val z = χ.value z.1 * q.val.val.val z)
    (fun t a s n hq' => by
      change (u.p 1).val.val.val (t, a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ) =
        χ.value t * q.val.val.val (t, a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ)
      rw [HierarchyTwistedProfile.twistedSlice, HierarchyTwistedProfile.twistedSlice]
      exact hq')
    (fun t ht a ha s => by
      change (u.p 1).val.val.val (t, a, s) = χ.value t * q.val.val.val (t, a, s)
      rw [hu.leading_pressure t ht a ha s]
      by_cases hpre : t < t₀
      · rw [χ.zero_before t ht hpre, zero_mul, zero_mul]
      · rw [hq t ⟨not_lt.mp hpre, ht.2⟩ a ha s])
  exact fun t ht x s => hall (t, x, s) ⟨ht, mem_univ _⟩

/-- **`S = χ̃' V`** (the activation term, the same for `χ̃'`). -/
theorem S_eq_smul (d : ParentGeometry hT U X k) {χ : PaperWaveCutoff t₀ T} {ℓ h : ℝ}
    {amp : ℝ → Vec3 → Vec3} {P : ℕ} {R S : VP}
    {u : HierarchyProfiles VP (HierarchyTwistedProfile T k ℝ)}
    (hu : S5.IsExpansion d pU χ ℓ h amp P R S u) (V : VP)
    (hV : ∀ t ∈ Icc t₀ T, ∀ x ∈ centeredCell, ∀ s,
      V.val.val.val (t, x, s) = S5.leading ℓ h amp t x s) :
    ∀ t ∈ Icc 0 T, ∀ x s, S.val.val.val (t, x, s) = χ.derivative t • V.val.val.val (t, x, s) := by
  have hall := Lib.S5Bridge.forall_of_centeredCell (T := T) k
    (Q := fun z : HierarchyProfilePoint =>
      S.val.val.val z = χ.derivative z.1 • V.val.val.val z)
    (fun t a s n hq => by
      change S.val.val.val (t, a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ) =
        χ.derivative t • V.val.val.val (t, a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ)
      rw [HierarchyTwistedProfile.twistedSlice, HierarchyTwistedProfile.twistedSlice]
      exact hq)
    (fun t ht a ha s => by
      change S.val.val.val (t, a, s) = χ.derivative t • V.val.val.val (t, a, s)
      rw [hu.activation t ht a ha s]
      by_cases hpre : t < t₀
      · rw [χ.derivative_zero_before hT ht hpre, zero_smul, zero_smul]
      · rw [hV t ⟨not_lt.mp hpre, ht.2⟩ a ha s])
  exact fun t ht x s => hall (t, x, s) ⟨ht, mem_univ _⟩

set_option maxHeartbeats 2000000 in
/-- **The linear term of `H₂`** (TeX :570-571): `(∂_t+M)C₂ + 𝐝𝗉₁ - C[χ̃'A₁] = χ̃ [(∂_t+M)C[V] + 𝐝q]`
(the terms in `χ̃'` cancel). Here `C₂ = C[V₁]`, `V₁ = χ̃V`, `𝗉₁ = χ̃q`, `S = χ̃'V`. -/
theorem relay_two_eq (d : ParentGeometry hT U X k) {χ : PaperWaveCutoff t₀ T} {ℓ h : ℝ}
    {amp : ℝ → Vec3 → Vec3} {P : ℕ} {R S : VP}
    {u : HierarchyProfiles VP (HierarchyTwistedProfile T k ℝ)}
    (hu : S5.IsExpansion d pU χ ℓ h amp P R S u) (V : VP) (q : HierarchyTwistedProfile T k ℝ)
    (hV : ∀ t ∈ Icc t₀ T, ∀ x ∈ centeredCell, ∀ s,
      V.val.val.val (t, x, s) = S5.leading ℓ h amp t x s)
    (hq : ∀ t ∈ Icc t₀ T, ∀ x ∈ centeredCell, ∀ s,
      q.val.val.val (t, x, s) = S5.leadingPressure U X k ℓ h amp t x s)
    (hVavg : (S5.ops d).average V = 0) (hV1avg : (S5.ops d).average (u.V 1) = 0)
    (hSavg : (S5.ops d).average S = 0) (hP1 : 1 ≤ P) :
    ∀ t ∈ Icc 0 T, ∀ a s,
      ((S5.ops d).relayAtLevel u (S5.curlCorrection d S) 2).val.val.val (t, a, s) =
        χ.value t • ((S5.ops d).material (S5.curlCorrection d V) +
          (S5.ops d).labelGrad q).val.val.val (t, a, s) := by
  intro t ht a s
  have hx : (t, a, s) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  have h1 := V1_eq_smul d hu V hV
  have hp1 := p1_eq_smul d hu q hq
  have hS := S_eq_smul d hu V hV
  have hC1 : u.C 1 = S5.curlCorrection d (u.V 1) := hu.correction 1 (Finset.mem_Icc.mpr ⟨le_rfl, hP1⟩)
  -- `C[·]` at each time
  have hCV (r : ℝ) (hr : r ∈ Icc 0 T) (b : Vec3) (σ : ℝ) :
      (u.C 1).val.val.val (r, b, σ) = χ.value r • (S5.curlCorrection d V).val.val.val (r, b, σ) := by
    rw [hC1]
    exact complete_smul_time_eval hT d.inverse d.covector V (u.V 1)
      d.oscillation.covector_independent d.oscillation.covector_ne_zero hVavg hV1avg hr
      (fun b q => h1 r hr b q) b σ
  have hCS : (S5.curlCorrection d S).val.val.val (t, a, s) =
      χ.derivative t • (S5.curlCorrection d V).val.val.val (t, a, s) :=
    complete_smul_time_eval hT d.inverse d.covector V S d.oscillation.covector_independent
      d.oscillation.covector_ne_zero hVavg hSavg ht (fun b q => hS t ht b q) a s
  -- the time derivative of `C₂ = χ̃ C[V]` (product rule)
  have hdiffC : DifferentiableWithinAt ℝ
      (fun r => (S5.curlCorrection d V).val.val.val (r, a, s)) (Icc 0 T) t := by
    have hsm := HierarchySmoothProfile.smooth (S5.curlCorrection d V).val.val
    have hι : ContDiffOn ℝ ∞ (fun r : ℝ => ((r, a, s) : HierarchyProfilePoint)) (Icc 0 T) :=
      (contDiff_id.prodMk contDiff_const).contDiffOn
    exact ((hsm.comp hι (fun r hr => ⟨hr, mem_univ _⟩)).differentiableOn (by simp)) t ht
  have hdiffχ : DifferentiableWithinAt ℝ χ.value (Icc 0 T) t :=
    (χ.smooth.differentiableOn (by simp)) t ht
  have hder : derivWithin (fun r => (u.C 1).val.val.val (r, a, s)) (Icc 0 T) t =
      χ.value t • derivWithin (fun r => (S5.curlCorrection d V).val.val.val (r, a, s)) (Icc 0 T) t +
        χ.derivative t • (S5.curlCorrection d V).val.val.val (t, a, s) := by
    rw [derivWithin_congr (f := fun r => χ.value r • (S5.curlCorrection d V).val.val.val (r, a, s))
      (fun r hr => hCV r hr a s) (hCV t ht a s)]
    exact derivWithin_smul hdiffχ hdiffC
  have hlg := labelGrad_time_smul hT d q (u.p 1) χ.smooth hp1 ht a s
  -- assemble
  change (((S5.ops d).material (u.C 1) + (S5.ops d).labelGrad (u.p 1)) -
      S5.curlCorrection d S).val.val.val (t, a, s) = _
  rw [eval_sub, eval_add, hCS, hlg, Bridge.ops_material_eval d (u.C 1) hx]
  try dsimp only
  rw [hder, hCV t ht a s, eval_add, Bridge.ops_material_eval d (S5.curlCorrection d V) hx]
  try dsimp only
  simp only [map_smul, smul_add]
  abel

end One


end

end TorusEuler.Paper.S5b
