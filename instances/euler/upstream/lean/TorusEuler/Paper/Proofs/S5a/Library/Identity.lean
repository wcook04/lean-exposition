import TorusEuler.Paper.Proofs.S5a.Library.Inactive
import TorusEuler.Paper.Proofs.S5Bridge.Hierarchy
import TorusEuler.HierarchyPhysicalPiola
import TorusEuler.Paper.Proofs.S5a.Library.MeanSolve

/-!
# S5a library: the identities of Proposition 5.4 for every expansion

For an expansion of depth `P ≥ 2` in predicate form (`S5.IsExpansion`) this file proves the
identities of Proposition 5.4 (`sections/06c_finite_hierarchy.tex:304-333`), following its proof
(`:334-391`):

* `W = ∑_{p=1}^P Z_p + C_{P+1}` (`expansion_eq_sum_Zd`), `Y_{P+1} = Z_{P+1} = C_{P+1}`;
* `𝐝̃·W = 0` (`:335-340`): `𝐝̃·(V_p + C[V_p]) = 𝐝̃·(𝐝̃ × Q[V_p]) = 0` by (3.6)
  (library `profileTotalDivergence_completedOutput_eq_zero`), and `𝐝·B_p = 0` by (5.11), i.e.
  `div_a v = 0` and the Piola identity for `B = D_aX v` (`det D_aX = 1`)
  (`totalDivergence_meanSolution`, the argument of the library
  `ParentGeometry.meanResult_divergence_eq_zero` for a `S5.MeanSolution`);
* (5.29) `W_t + MW + (W·𝐝̃)W + 𝐝̃𝖯 + R_U∘X = R_P + R_χ̃` (`:341-367`), given the leading
  switch `V_{1,t} + MV_1 + κ∂_s𝗉_1 = χ̃'A₁` of (3.4), (3.7) as the hypothesis `hsw`
  (`momentum_of_leadingSwitch`): the algebraic cancellation is the 5.4 content
  `HierarchyOperators.momentum_eq_remainder_add_switch`, applied to the expansion with the
  levels outside `1 ≤ p ≤ P` set to zero (`truncProfiles`), which has the same `W`, `𝖯`, `R_P`
  and the same sources at the levels `2 ≤ p ≤ P`;
* `W_osc = W - ⟨W⟩ = ∑_{p=1}^P (V_p + C_{p+1})` (`:317-318`);
* the supports and the vanishing before `t₀` (`:317-321`, `:376-391`, from `IsExpansion.inactive`),
  and the phase independence of `R_P` outside `supp g` (`:388-390`).

The leading switch `(3.4)·χ̃ + χ̃'A₁` is the hypothesis `hsw`, supplied by `Lib.S5a.leadingSwitch`
(`Switch.lean`; (3.4) is glue, decision D6).
-/

open Set Filter
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.Paper.Lib.S5a

noncomputable section

open HierarchyTwistedProfile

/-! ## Truncation of the levels -/

section Trunc

variable {E F : Type*} [AddCommGroup E] [AddCommGroup F]

/-- The profiles of an expansion of depth `P` with the levels outside `1 ≤ p ≤ P` and the
library corrections `u.C q` outside `q ≤ P` (that is, `C_{q+1}` outside `1 ≤ q + 1 ≤ P + 1`) set to
zero. Only these levels enter `W`, `𝖯`, `R_P` and the sources of Proposition 5.4. -/
def truncProfiles (u : HierarchyProfiles E F) (P : ℕ) : HierarchyProfiles E F where
  V i := if 1 ≤ i ∧ i ≤ P then u.V i else 0
  C i := if i ≤ P then u.C i else 0
  B i := if 1 ≤ i ∧ i ≤ P then u.B i else 0
  p i := if 1 ≤ i ∧ i ≤ P then u.p i else 0
  q i := if 1 ≤ i ∧ i ≤ P then u.q i else 0

variable (u : HierarchyProfiles E F) (P : ℕ)

/-- Truncating the profiles at `P` does not change `V i` for `1 ≤ i ≤ P`. -/
theorem trunc_V {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ P) : (truncProfiles u P).V i = u.V i := by
  simp [truncProfiles, h1, h2]

/-- Truncating the profiles at `P` does not change `B i` for `1 ≤ i ≤ P`. -/
theorem trunc_B {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ P) : (truncProfiles u P).B i = u.B i := by
  simp [truncProfiles, h1, h2]

/-- Truncating the profiles at `P` does not change `p i` for `1 ≤ i ≤ P`. -/
theorem trunc_p {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ P) : (truncProfiles u P).p i = u.p i := by
  simp [truncProfiles, h1, h2]

/-- Truncating the profiles at `P` does not change `q i` for `1 ≤ i ≤ P`. -/
theorem trunc_q {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ P) : (truncProfiles u P).q i = u.q i := by
  simp [truncProfiles, h1, h2]

/-- Truncating at `P` does not change `Cd i` for `i ≤ P + 1`. -/
theorem trunc_Cd {i : ℕ} (h2 : i ≤ P + 1) : S5.Cd (truncProfiles u P) i = S5.Cd u i := by
  unfold S5.Cd
  have h : i - 1 ≤ P := by omega
  simp [truncProfiles, h]

/-- The truncated profile `V` vanishes at level `P + 1`. -/
theorem trunc_V_top : (truncProfiles u P).V (P + 1) = 0 := by simp [truncProfiles]

/-- The truncated profile `B` vanishes at level `P + 1`. -/
theorem trunc_B_top : (truncProfiles u P).B (P + 1) = 0 := by simp [truncProfiles]

variable {u P}

/-- Truncating at `P` does not change `Yd i` for `1 ≤ i ≤ P + 1`. -/
theorem trunc_Yd (hV : u.V (P + 1) = 0) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ P + 1) :
    S5.Yd (truncProfiles u P) i = S5.Yd u i := by
  unfold S5.Yd
  rw [trunc_Cd u P h2]
  rcases Nat.lt_or_ge i (P + 1) with h | h
  · rw [trunc_V u P h1 (by omega)]
  · have hi : i = P + 1 := by omega
    subst hi
    rw [trunc_V_top, hV]

/-- Truncating at `P` does not change `Zd i` for `1 ≤ i ≤ P + 1`. -/
theorem trunc_Zd (hV : u.V (P + 1) = 0) (hB : u.B (P + 1) = 0) {i : ℕ} (h1 : 1 ≤ i)
    (h2 : i ≤ P + 1) : S5.Zd (truncProfiles u P) i = S5.Zd u i := by
  unfold S5.Zd
  rw [trunc_Yd hV h1 h2]
  rcases Nat.lt_or_ge i (P + 1) with h | h
  · rw [trunc_B u P h1 (by omega)]
  · have hi : i = P + 1 := by omega
    subst hi
    rw [trunc_B_top, hB]

/-- The expansion to order `P` is unchanged by truncating at `P`. -/
theorem expansion_trunc : S5.expansion (truncProfiles u P) P = S5.expansion u P := by
  unfold S5.expansion
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_Icc] at hi
  rw [trunc_V u P hi.1 hi.2, trunc_Cd u P (by omega), trunc_B u P hi.1 hi.2]

/-- The expansion pressure to order `P` is unchanged by truncating at `P`. -/
theorem expansionPressure_trunc :
    S5.expansionPressure (truncProfiles u P) P = S5.expansionPressure u P := by
  unfold S5.expansionPressure
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_Icc] at hi
  rw [trunc_p u P hi.1 hi.2, trunc_q u P hi.1 hi.2]

end Trunc

section TruncOps

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {u : HierarchyProfiles E F} {P : ℕ}

/-- The remainder is unchanged by truncating at `P` when the top profiles vanish. -/
theorem remainder_trunc (A : HierarchyOperators E F) (hP : 1 ≤ P) (hV : u.V (P + 1) = 0)
    (hB : u.B (P + 1) = 0) : S5.remainder A (truncProfiles u P) P = S5.remainder A u P := by
  unfold S5.remainder
  rw [trunc_Cd u P le_rfl, trunc_p u P hP le_rfl]
  have h1 : (∑ ij ∈ (Finset.Icc 1 (P + 1) ×ˢ Finset.Icc 1 (P + 1)).filter
        (fun ij => P + 1 ≤ ij.1 + ij.2),
        A.labelAdv (S5.Zd (truncProfiles u P) ij.1) (S5.Zd (truncProfiles u P) ij.2)) =
      ∑ ij ∈ (Finset.Icc 1 (P + 1) ×ˢ Finset.Icc 1 (P + 1)).filter
        (fun ij => P + 1 ≤ ij.1 + ij.2), A.labelAdv (S5.Zd u ij.1) (S5.Zd u ij.2) := by
    refine Finset.sum_congr rfl fun ij hij => ?_
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hij
    rw [trunc_Zd hV hB hij.1.1.1 hij.1.1.2, trunc_Zd hV hB hij.1.2.1 hij.1.2.2]
  have h2 : (∑ ij ∈ (Finset.Icc 1 (P + 1) ×ˢ Finset.Icc 1 (P + 1)).filter
        (fun ij => P + 2 ≤ ij.1 + ij.2),
        A.phaseAdv (S5.Zd (truncProfiles u P) ij.1) (S5.Yd (truncProfiles u P) ij.2)) =
      ∑ ij ∈ (Finset.Icc 1 (P + 1) ×ˢ Finset.Icc 1 (P + 1)).filter
        (fun ij => P + 2 ≤ ij.1 + ij.2), A.phaseAdv (S5.Zd u ij.1) (S5.Yd u ij.2) := by
    refine Finset.sum_congr rfl fun ij hij => ?_
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hij
    rw [trunc_Zd hV hB hij.1.1.1 hij.1.1.2, trunc_Yd hV hij.1.2.1 hij.1.2.2]
  rw [h1, h2]

/-- The level source of order `p ≥ 2` is unchanged by truncation. -/
theorem levelSource_trunc (A : HierarchyOperators E F) (cS : E) {p : ℕ} (hp : 2 ≤ p)
    (hpP : p ≤ P) : S5.levelSource A (truncProfiles u P) cS p = S5.levelSource A u cS p :=
  Bridge.levelSource_congr A cS hp (fun i h1 h2 => trunc_V u P h1 (by omega))
    (fun i h1 h2 => trunc_B u P h1 (by omega)) (fun i h1 h2 => trunc_p u P h1 (by omega))
    (fun i _ h2 => trunc_Cd u P (by omega))

/-- The support source of order `p ≤ P` is unchanged by truncation. -/
theorem suppSource_trunc (A : HierarchyOperators E F) {p : ℕ} (hpP : p ≤ P) :
    S5.suppSource A (truncProfiles u P) p = S5.suppSource A u p :=
  Bridge.suppSource_congr A (fun i h1 h2 => trunc_V u P h1 (by omega))
    (fun i h1 h2 => trunc_B u P (by omega) (h2.trans hpP))
    (fun i _ h2 => trunc_Cd u P (by omega))

/-- The two groupings of the remainder agree: `R_P` of (5.30) is the library remainder, when
the transverse levels do not differentiate the phase and `C_1 = B_1 = 0`. -/
theorem remainder_eq_library (A : HierarchyOperators E F) (u : HierarchyProfiles E F) (P : ℕ)
    (hC₀ : u.C 0 = 0) (hB₁ : u.B 1 = 0) (htr : ∀ i v, A.phaseAdv (u.V i) v = 0) :
    S5.remainder A u P = A.remainder u P := by
  have hprod : ∀ (s t : Finset ℕ) (x : ℕ × ℕ), x ∈ s.product t ↔ x.1 ∈ s ∧ x.2 ∈ t :=
    fun _ _ _ => Finset.mem_product
  unfold S5.remainder HierarchyOperators.remainder
  have hC : S5.Cd u (P + 1) = u.C P := by
    unfold S5.Cd
    rw [Nat.add_sub_cancel]
  rw [hC]
  have h1 : (∑ ij ∈ (Finset.Icc 1 (P + 1) ×ˢ Finset.Icc 1 (P + 1)).filter
        (fun ij => P + 1 ≤ ij.1 + ij.2), A.labelAdv (S5.Zd u ij.1) (S5.Zd u ij.2)) =
      ∑ ij ∈ hierarchyTailPairs P 0, A.labelProduct u ij := by
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_product, hierarchyTailPairs, hierarchyAdvectionPairs,
      hprod, Finset.mem_Icc]
    constructor <;> intro h <;> omega
  have h2 : (∑ ij ∈ (Finset.Icc 1 (P + 1) ×ˢ Finset.Icc 1 (P + 1)).filter
        (fun ij => P + 2 ≤ ij.1 + ij.2), A.phaseAdv (S5.Zd u ij.1) (S5.Yd u ij.2)) =
      ∑ ij ∈ hierarchyTailPairs P 1,
        (A.completionPhaseProduct u ij + A.meanPhaseProduct u ij) := by
    have hsplit : ∀ ij : ℕ × ℕ, A.phaseAdv (S5.Zd u ij.1) (S5.Yd u ij.2) =
        A.completionPhaseProduct u ij + A.meanPhaseProduct u ij := by
      intro ij
      simp only [S5.Zd, S5.Yd, S5.Cd, HierarchyOperators.completionPhaseProduct,
        HierarchyOperators.meanPhaseProduct, HierarchyProfiles.Y, map_add, LinearMap.add_apply,
        htr, zero_add]
      abel
    simp only [hsplit]
    symm
    refine Finset.sum_subset (fun ij hij => ?_) (fun ij hij hn => ?_)
    · simp only [Finset.mem_filter, Finset.mem_product, hierarchyTailPairs,
        hierarchyAdvectionPairs, hprod, Finset.mem_Icc] at hij ⊢
      omega
    · simp only [Finset.mem_filter, Finset.mem_product, hierarchyTailPairs,
        hierarchyAdvectionPairs, hprod, Finset.mem_Icc] at hij hn
      have hi : ij.1 = 1 := by omega
      simp only [HierarchyOperators.completionPhaseProduct, HierarchyOperators.meanPhaseProduct,
        hi, Nat.sub_self, hC₀, hB₁, map_zero, LinearMap.zero_apply, add_zero]
  rw [h1, h2]

end TruncOps

/-! ## Divergence -/

section Divergence

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {pU : Pressure}
  {D lam : ℝ}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ

/-- `𝐝·B = 0` for a solution of the mean equation (5.11): `B = D_aX v` with `div_a v = 0` and
`det D_aX = 1` (Piola identity), and `B` is independent of the phase. This is the argument of
the library `ParentGeometry.meanResult_divergence_eq_zero` (unlisted glue) for a
`S5.MeanSolution`. -/
theorem totalDivergence_meanSolution (d : ParentGeometry hT U X k) (hP : S5.Parent T U X pU D lam)
    {f B : VP} {q : SP} (hm : S5.MeanSolution d f B q) : S5.totalDivergence d B = 0 := by
  obtain ⟨v, z, hv, -, -, -, -, -, hdiv, hBv⟩ := hm.endpoint
  have hBind := Bridge.phaseIndependent_of_average_eq d hm.phase_independent
  have h0 : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hU2 : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hP.velocity_smooth.of_le (by simp)
  have hFlow := hP.flow.contDiffOn_forwardLabelFlow hT hP.velocity_smooth hP.velocity_periodic
  unfold S5.totalDivergence
  apply HierarchySmoothProfile.ext
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  have hXt : ContDiff ℝ ∞ (X 0 t) := meanSlice_contDiff hFlow ht
  have hvt : ContDiff ℝ ∞ (v t) := meanSlice_contDiff hv ht
  have hdet : ∀ᶠ b in 𝓝 a, LinearMap.det (fderiv ℝ (X 0 t) b).toLinearMap = 1 :=
    Eventually.of_forall fun b =>
      hP.flow.det_labelDerivative hT hU2 hP.velocity_periodic hP.divergence_free h0 ht b
  have hGF := (hP.flow.labelDerivative_inverse hT hU2 hP.velocity_periodic h0 ht a).1
  have hphase : (fun r => B.val.val.val (t, a, r)) = fun _ => B.val.val.val (t, a, s) :=
    funext fun r => hBind (t, a, s) hx r
  have hfast : deriv (fun r => B.val.val.val (t, a, r)) s = 0 := by
    rw [hphase]
    simp
  have hslow : LinearMap.trace ℝ Vec3
      (((fderiv ℝ (fun b => B.val.val.val (t, b, s)) a).comp
        (fderiv ℝ (X t 0) (X 0 t a))).toLinearMap) = 0 :=
    trace_endpointPhysicalMean_eq_zero_of_volumePreserving (X := X 0 t)
      ((hXt.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt) (fun b => rfl) hGF hdet
      ((hvt.differentiable (by simp)) a) (hdiv t ht a) (fun b => hBv t ht b s)
  change (HierarchySmoothProfile.profileLabelDivergence hT d.inverse.val.val B.val.val).val
      (t, a, s) +
    (HierarchySmoothProfile.profilePhaseDivergence hT d.covector.val.val B.val.val).val (t, a, s) = 0
  rw [HierarchySmoothProfile.profileLabelDivergence_apply hT _ _ ht,
    HierarchySmoothProfile.profilePhaseDivergence_apply hT _ _ ht, d.inverse_value _ hx, hslow,
    hfast, inner_zero_right, add_zero]

/-- `𝐝̃·(V + C[V]) = 𝐝̃·(𝐝̃ × Q[V]) = 0` for a transverse profile `V` of zero phase mean, by (3.6)
(library `profileTotalDivergence_completedOutput_eq_zero`, unlisted glue). -/
theorem totalDivergence_completed (d : ParentGeometry hT U X k) (hP : S5.Parent T U X pU D lam)
    {V : VP} (hav : (S5.ops d).average V = 0)
    (htr : ∀ t ∈ Icc 0 T, ∀ a s, ⟪S5.waveVector X k t a, V.val.val.val (t, a, s)⟫_ℝ = 0) :
    S5.totalDivergence d (V + S5.curlCorrection d V) = 0 := by
  obtain ⟨hSurj, hChart⟩ := d.inverseGraph_values hP.flow hP.velocity_smooth hP.velocity_periodic
  have hinvX := hP.flow.contDiffOn_inverseLabelFlow hT hP.velocity_smooth hP.velocity_periodic
  let o : HierarchyTransverseOutput (S5.ops d) :=
    ⟨V, 0, hav, fun w => Bridge.ops_phaseAdv_of_transverse d htr w⟩
  exact profileTotalDivergence_completedOutput_eq_zero hT d.inverse d.strain d.covector
    d.oscillation.covector_independent d.oscillation.covector_ne_zero o
    (fun t ht => (meanSlice_contDiff (f := fun t x => X t 0 x) hinvX ht).of_le (by simp)) hSurj
    (fun t ht x s => (hChart t ht x s).1) (fun t ht x s => (hChart t ht x s).2)

end Divergence

/-! ## The identities -/

section Identities

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {pU : Pressure}
  {D lam t₀ : ℝ} {center : ℝ → Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ

/-- The leading level of an expansion is the leading velocity profile of the bridge
(`V₁ = χ̃A₁` on the label cell determines the profile). -/
theorem IsExpansion.leading_eq (d : ParentGeometry hT U X k) (hP : S5.Parent T U X pU D lam)
    (hL : S5.Launch T X k lam t₀) {amp : ℝ → Vec3 → Vec3}
    (hamp : S5.IsSeed U X k t₀ T center amp) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2)
    (hh : 0 < h) (hh₁ : h ≤ 1) {χ : PaperWaveCutoff t₀ T} {P : ℕ} {R S : VP}
    {u : HierarchyProfiles VP SP} (hu : S5.IsExpansion d pU χ ℓ h amp P R S u) :
    u.V 1 = (Bridge.leadingOutput d hP hL hamp hℓ hfit hh hh₁ χ).V :=
  Lib.S5Bridge.eq_of_centeredCell fun t ht a ha s =>
    (hu.leading_velocity t ht a ha s).trans
      (Bridge.leadingVelocityProfile_cell_eval hL hamp hℓ hfit hh hh₁ χ.value χ.smooth
        χ.zero_before ht ha s).symm

set_option maxHeartbeats 2000000 in
/-- **The identities of Proposition 5.4** for every expansion of depth `P ≥ 2`, given the
leading switch `(∂_t+M)V₁ + κ∂_s𝗉₁ = χ̃'A₁` (from (3.4) and (3.7),
`06c_finite_hierarchy.tex:355-358`). Each conclusion is a clause of the identities conjunct of
`Statement.proposition_5_4`, in the same order; see the module docstring for the TeX steps. -/
theorem isExpansion_identities (d : ParentGeometry hT U X k) (hP : S5.Parent T U X pU D lam)
    (hL : S5.Launch T X k lam t₀) {amp : ℝ → Vec3 → Vec3}
    (hamp : S5.IsSeed U X k t₀ T center amp) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2)
    (hh : 0 < h) (hh₁ : h ≤ 1) {χ : PaperWaveCutoff t₀ T} {P : ℕ} (hP2 : 2 ≤ P) {R S : VP}
    {u : HierarchyProfiles VP SP} (hu : S5.IsExpansion d pU χ ℓ h amp P R S u)
    (hsw : (S5.ops d).material (u.V 1) + (S5.ops d).phaseGrad (u.p 1) = S) :
    let A := S5.ops d
    let Sg := S5.envelopeSupport ℓ
    let cS := S5.curlCorrection d S
    let W := S5.expansion u P
    let Pr := S5.expansionPressure u P
    let RP := S5.remainder A u P
    W = (∑ i ∈ Finset.Icc 1 P, S5.Zd u i) + S5.Cd u (P + 1) ∧
    S5.totalDivergence d W = 0 ∧
    A.material W + A.labelAdv W W + A.phaseAdv W W + A.labelGrad Pr + A.phaseGrad Pr + R =
      RP + (S + cS) ∧
    W - A.average W = ∑ i ∈ Finset.Icc 1 P, (u.V i + S5.Cd u (i + 1)) ∧
    (∀ t ∈ Icc 0 T, ∀ x ∉ Sg, ∀ s, (W - A.average W).val.val.val (t, x, s) = 0) ∧
    (∀ i ∈ Finset.Icc 2 P, ∀ t ∈ Icc 0 T, ∀ x ∉ Sg, ∀ s,
      (S5.oscSource A u cS i + S5.suppSource A u i).val.val.val (t, x, s) = 0) ∧
    (∀ t ∈ Icc 0 T, t < t₀ → ∀ x s,
      (∀ i ∈ Finset.Icc 1 P,
        (u.V i).val.val.val (t, x, s) = 0 ∧ (u.p i).val.val.val (t, x, s) = 0) ∧
      (∀ i ∈ Finset.Icc 1 (P + 1), (S5.Cd u i).val.val.val (t, x, s) = 0) ∧
      ∀ i ∈ Finset.Icc 2 P,
        (S5.oscSource A u cS i + S5.suppSource A u i).val.val.val (t, x, s) = 0) ∧
    S5.Yd u (P + 1) = S5.Cd u (P + 1) ∧ S5.Zd u (P + 1) = S5.Cd u (P + 1) ∧
    ∀ t ∈ Icc 0 T, ∀ x ∉ Sg, ∀ s, RP.val.val.val (t, x, s) = RP.val.val.val (t, x, 0) := by
  intro A Sg cS W Pr RP
  have hP1 : 1 ≤ P := by omega
  have hmem1 : (1 : ℕ) ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨le_rfl, hP1⟩
  obtain ⟨hVtop, hBtop⟩ := hu.top
  have hC0 : u.C 0 = 0 := hu.first_correction
  obtain ⟨hB1, hq1⟩ := hu.first_mean
  -- the levels: zero phase mean and transversality of `V_i`, phase independence of `B_i`
  have hV1 := IsExpansion.leading_eq d hP hL hamp hℓ hfit hh hh₁ hu
  have hVav : ∀ i ∈ Finset.Icc 1 P, A.average (u.V i) = 0 := by
    intro i hi
    rcases eq_or_lt_of_le (Finset.mem_Icc.mp hi).1 with h1 | h1
    · subst h1
      rw [hV1]
      exact (Bridge.leadingOutput d hP hL hamp hℓ hfit hh hh₁ χ).average_V
    · exact (hu.transverse i (Finset.mem_Icc.mpr ⟨h1, (Finset.mem_Icc.mp hi).2⟩)).mean_zero
  have hVtr : ∀ i ∈ Finset.Icc 1 P, ∀ t ∈ Icc 0 T, ∀ a s,
      ⟪S5.waveVector X k t a, (u.V i).val.val.val (t, a, s)⟫_ℝ = 0 := by
    intro i hi
    rcases eq_or_lt_of_le (Finset.mem_Icc.mp hi).1 with h1 | h1
    · subst h1
      rw [hV1]
      exact Bridge.leadingVelocityProfile_transverse d hL hamp hℓ hfit hh hh₁ χ.value χ.smooth
        χ.zero_before
    · exact (hu.transverse i (Finset.mem_Icc.mpr ⟨h1, (Finset.mem_Icc.mp hi).2⟩)).transverse
  have hBav : ∀ i ∈ Finset.Icc 1 P, A.average (u.B i) = u.B i := by
    intro i hi
    rcases eq_or_lt_of_le (Finset.mem_Icc.mp hi).1 with h1 | h1
    · subst h1
      rw [hB1, map_zero]
    · exact (hu.mean i (Finset.mem_Icc.mpr ⟨h1, (Finset.mem_Icc.mp hi).2⟩)).1.phase_independent
  have hCd : ∀ i ∈ Finset.Icc 1 P, S5.Cd u (i + 1) = S5.curlCorrection d (u.V i) :=
    fun i hi => hu.correction i hi
  -- the truncated profiles
  let v := truncProfiles u P
  have hvC0 : v.C 0 = 0 := by simp [v, truncProfiles, hC0]
  have hvB1 : v.B 1 = 0 := by simp [v, truncProfiles, hB1]
  have hvq1 : v.q 1 = 0 := by simp [v, truncProfiles, hq1]
  have hvtr : ∀ i w, A.phaseAdv (v.V i) w = 0 := by
    intro i w
    by_cases hi : 1 ≤ i ∧ i ≤ P
    · rw [show v.V i = u.V i from trunc_V u P hi.1 hi.2]
      exact Bridge.ops_phaseAdv_of_transverse d (hVtr i (Finset.mem_Icc.mpr hi)) w
    · rw [show v.V i = 0 by simp [v, truncProfiles, hi], map_zero, LinearMap.zero_apply]
  have hvph : ∀ j w, A.phaseAdv w (v.B j) = 0 := by
    intro j w
    by_cases hj : 1 ≤ j ∧ j ≤ P
    · rw [show v.B j = u.B j from trunc_B u P hj.1 hj.2]
      exact Bridge.ops_phaseAdv_of_mean d w (hBav j (Finset.mem_Icc.mpr hj))
    · rw [show v.B j = 0 by simp [v, truncProfiles, hj], map_zero]
  have hvq : ∀ j, A.phaseGrad (v.q j) = 0 := by
    intro j
    by_cases hj : 2 ≤ j ∧ j ≤ P
    · rw [show v.q j = u.q j from trunc_q u P (by omega) hj.2]
      exact (hu.mean j (Finset.mem_Icc.mpr hj)).1.pressure_phase_independent
    · by_cases hj1 : j = 1
      · subst hj1
        rw [hvq1, map_zero]
      · have hc : ¬(1 ≤ j ∧ j ≤ P) := by omega
        rw [show v.q j = 0 by simp [v, truncProfiles, hc], map_zero]
  have hvlead : A.material (v.V 1) + A.phaseGrad (v.p 1) = S := by
    rw [show v.V 1 = u.V 1 from trunc_V u P le_rfl hP1,
      show v.p 1 = u.p 1 from trunc_p u P le_rfl hP1]
    exact hsw
  have hvmean : ∀ p ∈ Finset.Icc 2 P, A.material (v.B p) + A.labelGrad (v.q p) =
      -A.average (A.sourceBeforeMean v P cS p) - (if p = 2 then R else 0) := by
    intro p hp
    obtain ⟨hp2, hpP⟩ := Finset.mem_Icc.mp hp
    rw [show v.B p = u.B p from trunc_B u P (by omega) hpP,
      show v.q p = u.q p from trunc_q u P (by omega) hpP, (hu.mean p hp).1.momentum,
      ← Bridge.meanSource_eq A v cS R hpP]
    unfold S5.meanSource
    rw [levelSource_trunc A cS hp2 hpP]
  have hvosc : ∀ p ∈ Finset.Icc 2 P, A.material (v.V p) + A.phaseGrad (v.p p) =
      -(A.sourceBeforeMean v P cS p - A.average (A.sourceBeforeMean v P cS p)) -
        hierarchyAdvectionAtLevel P 1 p (A.meanPhaseProduct v) := by
    intro p hp
    obtain ⟨hp2, hpP⟩ := Finset.mem_Icc.mp hp
    rw [show v.V p = u.V p from trunc_V u P (by omega) hpP,
      show v.p p = u.p p from trunc_p u P (by omega) hpP, (hu.transverse p hp).momentum,
      ← Bridge.oscSource_add_suppSource_eq A v cS hpP]
    unfold S5.oscSource
    rw [levelSource_trunc A cS hp2 hpP, suppSource_trunc A hpP]
  have hmom := A.momentum_eq_remainder_add_switch v hP2 S cS R hvC0 hvB1 hvq1
    (trunc_V_top u P) (trunc_B_top u P) hvtr hvph hvq hvlead hvmean hvosc
  have hvel : v.velocity P = W := by
    show v.velocity P = S5.expansion u P
    rw [← expansion_trunc (u := u) (P := P)]
    unfold S5.expansion HierarchyProfiles.velocity
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [S5.Cd, Nat.add_sub_cancel]
    rfl
  have hpr : v.pressure P = Pr := expansionPressure_trunc
  have hrem : A.remainder v P = RP := by
    rw [← remainder_eq_library A v P hvC0 hvB1 hvtr]
    exact remainder_trunc A hP1 hVtop hBtop
  rw [hvel, hpr, hrem] at hmom
  -- supports
  obtain ⟨hVin, hCin, hsrcin⟩ := IsExpansion.inactive d hu hℓ hfit
  have hin {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : HierarchyTwistedProfile T k E}
      (hg : g ∈ inactiveVP T k E t₀ ℓ) {t : ℝ} (ht : t ∈ Icc 0 T) {x : Vec3} (s : ℝ)
      (hx : t < t₀ ∨ x ∉ Sg) : g.val.val.val (t, x, s) = 0 :=
    hg ⟨⟨ht, mem_univ _⟩, hx⟩
  have hosc : W - A.average W = ∑ i ∈ Finset.Icc 1 P, (u.V i + S5.Cd u (i + 1)) := by
    unfold W S5.expansion
    rw [map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [map_add, map_add, hVav i hi, hCd i hi, Bridge.ops_average_curlCorrection d, hBav i hi, ← hCd i hi]
    abel
  have hoscin : W - A.average W ∈ inactiveVP T k Vec3 t₀ ℓ := by
    rw [hosc]
    refine Submodule.sum_mem _ fun i hi => Submodule.add_mem _ (hVin i hi).1 (hCin (i + 1) ?_)
    rw [Finset.mem_Icc] at hi ⊢
    omega
  have hYin : ∀ i ∈ Finset.Icc 1 (P + 1), S5.Yd u i ∈ inactiveVP T k Vec3 t₀ ℓ := by
    intro i hi
    refine Submodule.add_mem _ ?_ (hCin i hi)
    rcases Nat.lt_or_ge i (P + 1) with h | h
    · exact (hVin i (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, by omega⟩)).1
    · rw [show i = P + 1 by rw [Finset.mem_Icc] at hi; omega, hVtop]
      exact Submodule.zero_mem _
  have hBav' : ∀ i ∈ Finset.Icc 1 (P + 1), A.average (u.B i) = u.B i := by
    intro i hi
    rcases Nat.lt_or_ge i (P + 1) with h | h
    · exact hBav i (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, by omega⟩)
    · rw [show i = P + 1 by rw [Finset.mem_Icc] at hi; omega, hBtop, map_zero]
  have hLaws := inactiveLaws (τ := t₀) hT (isClosed_envelopeSupport ℓ) d.inverse d.strain
    d.covector d.mean.inverse_independent
  let F0 := (Finset.Icc 1 (P + 1) ×ˢ Finset.Icc 1 (P + 1)).filter
    (fun ij : ℕ × ℕ => P + 1 ≤ ij.1 + ij.2)
  let Dm : VP := ∑ ij ∈ F0, A.labelAdv (u.B ij.1) (u.B ij.2)
  have hF0 : ∀ ij ∈ F0, ij.1 ∈ Finset.Icc 1 (P + 1) ∧ ij.2 ∈ Finset.Icc 1 (P + 1) := by
    intro ij hij
    simp only [F0, Finset.mem_filter, Finset.mem_product] at hij
    exact hij.1
  have hDm : A.average Dm = Dm := by
    simp only [Dm, map_sum]
    refine Finset.sum_congr rfl fun ij hij => ?_
    exact hLaws.labelAdv_mean (hBav' _ (hF0 ij hij).1) (hBav' _ (hF0 ij hij).2)
  have hRD : RP - Dm ∈ inactiveVP T k Vec3 t₀ ℓ := by
    have heq : RP - Dm = A.material (S5.Cd u (P + 1)) + A.labelGrad (u.p P) +
        (∑ ij ∈ F0, (A.labelAdv (S5.Yd u ij.1) (S5.Zd u ij.2) +
          A.labelAdv (u.B ij.1) (S5.Yd u ij.2))) +
        ∑ ij ∈ (Finset.Icc 1 (P + 1) ×ˢ Finset.Icc 1 (P + 1)).filter
          (fun ij : ℕ × ℕ => P + 2 ≤ ij.1 + ij.2), A.phaseAdv (S5.Zd u ij.1) (S5.Yd u ij.2) := by
      have hsplit : ∀ ij : ℕ × ℕ, A.labelAdv (S5.Zd u ij.1) (S5.Zd u ij.2) =
          A.labelAdv (S5.Yd u ij.1) (S5.Zd u ij.2) + A.labelAdv (u.B ij.1) (S5.Yd u ij.2) +
            A.labelAdv (u.B ij.1) (u.B ij.2) := by
        intro ij
        simp only [S5.Zd, map_add, LinearMap.add_apply]
        abel
      simp only [RP, S5.remainder, Dm, F0, hsplit, Finset.sum_add_distrib]
      abel
    rw [heq]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (hLaws.material (hCin (P + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)))
      (hLaws.labelGrad (hVin P (Finset.mem_Icc.mpr ⟨hP1, le_rfl⟩)).2))
      (Submodule.sum_mem _ fun ij hij => Submodule.add_mem _
        (hLaws.labelAdv_left (hYin _ (hF0 ij hij).1) _)
        (hLaws.labelAdv_right _ (hYin _ (hF0 ij hij).2))))
      (Submodule.sum_mem _ fun ij hij => hLaws.phaseAdv_right _ (hYin _ ?_))
    simp only [Finset.mem_filter, Finset.mem_product] at hij
    exact hij.1.2
  have hDind := Bridge.phaseIndependent_of_average_eq d hDm
  refine ⟨?_, ?_, ?_, hosc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `W = ∑ Z_p + C_{P+1}`
    have h := v.velocity_eq_sum_Z_add_completion hP1 hvC0
    rw [hvel] at h
    rw [h]
    have hZ : ∑ i ∈ Finset.Icc 1 P, v.Z i = ∑ i ∈ Finset.Icc 1 P, S5.Zd u i :=
      Finset.sum_congr rfl fun i hi => trunc_Zd hVtop hBtop (Finset.mem_Icc.mp hi).1
        (by have := (Finset.mem_Icc.mp hi).2; omega)
    rw [hZ]
    congr 1
    have h' := trunc_Cd u P (i := P + 1) le_rfl
    unfold S5.Cd at h' ⊢
    simpa only [Nat.add_sub_cancel] using h'
  · -- `𝐝̃·W = 0`
    let forget : VP →ₗ[ℝ] HierarchySmoothProfile T Vec3 :=
      (hierarchyPeriodicProfileSubmodule T Vec3).subtype.comp
        (hierarchyTwistedProfileSubmodule T k Vec3).subtype
    let Dv := (HierarchySmoothProfile.profileTotalDivergence hT d.inverse.val.val
      d.covector.val.val).comp forget
    change Dv W = 0
    unfold W S5.expansion
    rw [map_sum]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [map_add]
    have h1 : Dv (u.V i + S5.Cd u (i + 1)) = 0 := by
      rw [hCd i hi]
      exact totalDivergence_completed d hP (hVav i hi) (hVtr i hi)
    have h2 : Dv (u.B i) = 0 := by
      rcases eq_or_lt_of_le (Finset.mem_Icc.mp hi).1 with h1' | h1'
      · subst h1'
        rw [hB1, map_zero]
      · exact totalDivergence_meanSolution d hP
          (hu.mean i (Finset.mem_Icc.mpr ⟨h1', (Finset.mem_Icc.mp hi).2⟩)).1
    rw [h1, h2, add_zero]
  · -- (5.29)
    exact hmom
  · -- `W_osc` is supported in `supp g`
    intro t ht x hx s
    exact hin hoscin ht s (Or.inr hx)
  · -- the sources `f_p + f_p^S` are supported in `supp g`
    intro i hi t ht x hx s
    exact hin (hsrcin i hi) ht s (Or.inr hx)
  · -- vanishing before activation
    intro t ht hlt x s
    exact ⟨fun i hi => ⟨hin (hVin i hi).1 ht s (Or.inl hlt), hin (hVin i hi).2 ht s (Or.inl hlt)⟩,
      fun i hi => hin (hCin i hi) ht s (Or.inl hlt),
      fun i hi => hin (hsrcin i hi) ht s (Or.inl hlt)⟩
  · -- `Y_{P+1} = C_{P+1}`
    unfold S5.Yd
    rw [hVtop, zero_add]
  · -- `Z_{P+1} = C_{P+1}`
    unfold S5.Zd S5.Yd
    rw [hVtop, hBtop, zero_add, add_zero]
  · -- `R_P` is independent of the phase outside `supp g`
    intro t ht x hx s
    have h1 : (RP - Dm).val.val.val (t, x, s) = 0 := hin hRD ht s (Or.inr hx)
    have h2 : (RP - Dm).val.val.val (t, x, 0) = 0 := hin hRD ht 0 (Or.inr hx)
    have h3 : Dm.val.val.val (t, x, s) = Dm.val.val.val (t, x, 0) :=
      hDind (t, x, 0) ⟨ht, mem_univ _⟩ s
    change RP.val.val.val (t, x, s) - Dm.val.val.val (t, x, s) = 0 at h1
    change RP.val.val.val (t, x, 0) - Dm.val.val.val (t, x, 0) = 0 at h2
    rw [sub_eq_zero] at h1 h2
    rw [h1, h2, h3]

end Identities

end

end TorusEuler.Paper.Lib.S5a
