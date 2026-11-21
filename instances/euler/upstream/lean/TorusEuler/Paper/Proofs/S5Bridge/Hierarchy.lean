import TorusEuler.Paper.Proofs.S5Bridge.Operators
import TorusEuler.Paper.Proofs.S5Bridge.Library.Wrap
import TorusEuler.HierarchyParentGeometry
import TorusEuler.TruncatedChildStage

/-!
# S5 bridge: the finite expansion of §5.5

* `MeanSolvable d` (abstract mean solver data: every phase-independent source has a
  solution of (5.11) whose pressure has zero cell mean) and `MeanUnique d` (such
  solutions are unique). Both quantify over every phase-independent source, so they can
  only come from `Statement.theorem_4_2`, through a bridge from its integrated system
  (`EndpointSystemSolution`) to `S5.MeanSolution` that is not written yet; only rows
  citing 4.2 (5.2, 5.4, 5.9, Aux 1.2, Aux 1.3) can supply them. `Statement.proposition_5_4`
  does not imply them: its clauses concern only expansions, whose mean sources are the
  specific sources of (5.27). Rows citing 5.4 without 4.2 (5.6, 5.8, 7.1) take the
  existence and uniqueness of the expansion from `Statement.proposition_5_4` directly.
  The transverse solves come from the ODE (`transverseSolvable`,
  `TransverseSolution.unique`).
* `solvers d hM hO`: the library `FiniteHierarchySolvers` over the operators `S5.ops d`
  whose solves are chosen from the abstract data and whose completion is `C[·]`
  (`S5.curlCorrection d`).
* The source identities: `S5.levelSource` is the library `sourceBeforeMean`, and the
  sources of (5.27), (5.28) are those of the library recursion.
* `construct_isExpansion`: the library construction over `solvers d hM hO`, started from
  any leading pair with the cell values `χ̃A₁`, `χ̃𝗉[A₁]` of (3.7), satisfies
  `S5.IsExpansion`.
* `IsExpansion.unique`: two expansions agree level by level, given `MeanUnique d`
  (transverse uniqueness from `V_p(0) = 0` and the zero phase mean of `𝗉_p`); hence every
  expansion is the library construction (`IsExpansion.eq_construct`).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Bridge

open HierarchyTwistedProfile Lib.S5Bridge

noncomputable section

/-! ## Algebra of the sources -/

section Algebra

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The terms `H_p` of (5.25)–(5.26) (`S5.levelSource`) are the library preliminary source
`sourceBeforeMean` of the depth-`P` recursion, for `p ≤ P`. -/
theorem levelSource_eq_sourceBeforeMean (A : HierarchyOperators E F)
    (u : HierarchyProfiles E F) (cS : E) {P p : ℕ} (hp : p ≤ P) :
    S5.levelSource A u cS p = A.sourceBeforeMean u P cS p := by
  have hlab : (∑ ij ∈ (Finset.Icc 1 p ×ˢ Finset.Icc 1 p).filter (fun ij => ij.1 + ij.2 = p),
      A.labelAdv (S5.Zd u ij.1) (S5.Zd u ij.2)) = hierarchyAdvectionAtLevel P 0 p (A.labelProduct u) := by
    unfold hierarchyAdvectionAtLevel
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext ⟨i, j⟩
    have hprod : ∀ (s t : Finset ℕ) (x : ℕ × ℕ), x ∈ s.product t ↔ x.1 ∈ s ∧ x.2 ∈ t :=
      fun _ _ _ => Finset.mem_product
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_product, hierarchyAdvectionPairs, hprod, Finset.mem_Icc,
      hierarchyAdvectionLevel]
    constructor <;> intro h <;> omega
  have hph : (∑ ij ∈ (Finset.Icc 2 p ×ˢ Finset.Icc 1 p).filter (fun ij => ij.1 + ij.2 = p + 1),
      A.phaseAdv (S5.Cd u ij.1) (S5.Yd u ij.2)) =
        hierarchyAdvectionAtLevel P 1 p (A.completionPhaseProduct u) := by
    unfold hierarchyAdvectionAtLevel
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext ⟨i, j⟩
    have hprod : ∀ (s t : Finset ℕ) (x : ℕ × ℕ), x ∈ s.product t ↔ x.1 ∈ s ∧ x.2 ∈ t :=
      fun _ _ _ => Finset.mem_product
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_product, hierarchyAdvectionPairs, hprod, Finset.mem_Icc,
      hierarchyAdvectionLevel]
    constructor <;> intro h <;> omega
  unfold S5.levelSource HierarchyOperators.sourceBeforeMean
  rw [hlab, hph]
  rfl

/-- The mean source `f̄_p` of (5.27) in the form used by the library recursion. -/
theorem meanSource_eq (A : HierarchyOperators E F) (u : HierarchyProfiles E F) (cS R : E)
    {P p : ℕ} (hp : p ≤ P) :
    S5.meanSource A u cS R p =
      -A.average (A.sourceBeforeMean u P cS p) - (if p = 2 then R else 0) := by
  unfold S5.meanSource
  rw [levelSource_eq_sourceBeforeMean A u cS hp]

/-- The transverse source `f_p + f_p^S` of (5.27), (5.28) in the form used by the library
recursion. -/
theorem oscSource_add_suppSource_eq (A : HierarchyOperators E F) (u : HierarchyProfiles E F)
    (cS : E) {P p : ℕ} (hp : p ≤ P) :
    S5.oscSource A u cS p + S5.suppSource A u p =
      -(A.sourceBeforeMean u P cS p - A.average (A.sourceBeforeMean u P cS p)) -
        hierarchyAdvectionAtLevel P 1 p (A.meanPhaseProduct u) := by
  unfold S5.oscSource S5.suppSource
  rw [levelSource_eq_sourceBeforeMean A u cS hp, A.meanPhaseAdvectionAtLevel_eq_sum u hp]
  exact (sub_eq_add_neg _ _).symm

/-- `H_p` only depends on the levels below `p` (and on `C_p`). -/
theorem levelSource_congr (A : HierarchyOperators E F) {u v : HierarchyProfiles E F} (cS : E)
    {p : ℕ} (hp : 2 ≤ p)
    (hV : ∀ i, 1 ≤ i → i < p → u.V i = v.V i) (hB : ∀ i, 1 ≤ i → i < p → u.B i = v.B i)
    (hP : ∀ i, 1 ≤ i → i < p → u.p i = v.p i) (hC : ∀ i, 1 ≤ i → i ≤ p → S5.Cd u i = S5.Cd v i) :
    S5.levelSource A u cS p = S5.levelSource A v cS p := by
  have hZ : ∀ i, 1 ≤ i → i < p → S5.Zd u i = S5.Zd v i := fun i h1 h2 => by
    unfold S5.Zd S5.Yd
    rw [hV i h1 h2, hC i h1 h2.le, hB i h1 h2]
  have hY : ∀ i, 1 ≤ i → i < p → S5.Yd u i = S5.Yd v i := fun i h1 h2 => by
    unfold S5.Yd
    rw [hV i h1 h2, hC i h1 h2.le]
  unfold S5.levelSource
  rw [hC p (by omega) le_rfl, hP (p - 1) (by omega) (by omega)]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun ij hij => ?_
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hij
    rw [hZ ij.1 (by omega) (by omega), hZ ij.2 (by omega) (by omega)]
  · refine Finset.sum_congr rfl fun ij hij => ?_
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hij
    rw [hC ij.1 (by omega) (by omega), hY ij.2 (by omega) (by omega)]

/-- `f_p^S` only depends on the means up to level `p` and the levels below `p`. -/
theorem suppSource_congr (A : HierarchyOperators E F) {u v : HierarchyProfiles E F} {p : ℕ}
    (hV : ∀ i, 1 ≤ i → i < p → u.V i = v.V i) (hB : ∀ i, 2 ≤ i → i ≤ p → u.B i = v.B i)
    (hC : ∀ i, 1 ≤ i → i < p → S5.Cd u i = S5.Cd v i) :
    S5.suppSource A u p = S5.suppSource A v p := by
  unfold S5.suppSource
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_Icc] at hi
  unfold S5.Yd
  rw [hB i hi.1 hi.2, hV (p + 1 - i) (by omega) (by omega), hC (p + 1 - i) (by omega) (by omega)]

end Algebra


/-! ## Solvers from abstract data -/

section Solvers

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ

/-- Abstract mean solver data: every phase-independent source `f̄` has a solution
`(B, q̄)` of the mean equation (5.11) whose pressure has zero mean over the label cell
(the normalization of the pressure `𝗊` of Theorem 4.2). Only `Statement.theorem_4_2` can
supply it (through a bridge from `EndpointSystemSolution` to `S5.MeanSolution`, not
written yet), so only rows citing 4.2 can use it. -/
def MeanSolvable (d : ParentGeometry hT U X k) : Prop :=
  ∀ f : VP, (S5.ops d).average f = f →
    ∃ (B : VP) (q : SP), S5.MeanSolution d f B q ∧
      ∀ t ∈ Icc 0 T, (∫ a in centeredCell, q.val.val.val (t, a, 0)) = 0

/-- Uniqueness of the normalized solutions of the mean equation (5.11), for every
phase-independent source. Only `Statement.theorem_4_2` can supply it (through a bridge
from `EndpointSystemSolution` to `S5.MeanSolution`, not written yet), so only rows citing
4.2 can use it; the uniqueness clause of `Statement.proposition_5_4` concerns only
expansions and does not imply it. -/
def MeanUnique (d : ParentGeometry hT U X k) : Prop :=
  ∀ (f B B' : VP) (q q' : SP), S5.MeanSolution d f B q →
    (∀ t ∈ Icc 0 T, (∫ a in centeredCell, q.val.val.val (t, a, 0)) = 0) →
    S5.MeanSolution d f B' q' →
    (∀ t ∈ Icc 0 T, (∫ a in centeredCell, q'.val.val.val (t, a, 0)) = 0) → B = B' ∧ q = q'

/-- The library solvers of the finite expansion over the operators `S5.ops d`: the mean
and transverse solves are chosen from the abstract data `hM`, `hO`, and the completion is
`C[·]`. -/
def solvers (d : ParentGeometry hT U X k) (hM : MeanSolvable d) (hO : TransverseSolvable d) :
    FiniteHierarchySolvers (S5.ops d) where
  average_idempotent := ops_average_idempotent d
  average_meanPhaseAdv := fun B hB Y =>
    average_meanPhaseAdv hT d.inverse d.strain d.covector B Y d.oscillation.covector_independent hB
  solveMean := fun f hf =>
    ⟨⟨(hM f hf).choose, (hM f hf).choose_spec.choose,
      (hM f hf).choose_spec.choose_spec.1.phase_independent,
      fun v => ops_phaseAdv_of_mean d v (hM f hf).choose_spec.choose_spec.1.phase_independent,
      (hM f hf).choose_spec.choose_spec.1.pressure_phase_independent⟩,
     (hM f hf).choose_spec.choose_spec.1.momentum⟩
  solveTransverse := fun f hf =>
    ⟨⟨(hO f hf).choose, (hO f hf).choose_spec.choose,
      (hO f hf).choose_spec.choose_spec.mean_zero,
      fun v => ops_phaseAdv_of_transverse d (hO f hf).choose_spec.choose_spec.transverse v⟩,
     (hO f hf).choose_spec.choose_spec.momentum⟩
  complete := S5.curlCorrection d
  average_complete := fun V _ => ops_average_curlCorrection d V

/-- The mean solve of `solvers` solves (5.11) with a pressure of zero cell mean. -/
theorem solvers_solveMean_spec (d : ParentGeometry hT U X k) (hM : MeanSolvable d)
    (hO : TransverseSolvable d) (f : VP) (hf : (S5.ops d).average f = f) :
    S5.MeanSolution d f ((solvers d hM hO).solveMean f hf).val.B
        ((solvers d hM hO).solveMean f hf).val.q ∧
      ∀ t ∈ Icc 0 T,
        (∫ a in centeredCell, ((solvers d hM hO).solveMean f hf).val.q.val.val.val (t, a, 0)) = 0 :=
  (hM f hf).choose_spec.choose_spec

/-- The transverse solve of `solvers` solves (5.15) from zero. -/
theorem solvers_solveTransverse_spec (d : ParentGeometry hT U X k) (hM : MeanSolvable d)
    (hO : TransverseSolvable d) (f : VP) (hf : (S5.ops d).average f = 0) :
    S5.TransverseSolution d f ((solvers d hM hO).solveTransverse f hf).val.V
      ((solvers d hM hO).solveTransverse f hf).val.p :=
  (hO f hf).choose_spec.choose_spec

/-- The completion of `solvers` is `C[·]`. -/
theorem solvers_complete (d : ParentGeometry hT U X k) (hM : MeanSolvable d)
    (hO : TransverseSolvable d) : (solvers d hM hO).complete = S5.curlCorrection d := rfl

/-! ## The construction is an expansion -/

set_option maxHeartbeats 1000000 in
/-- The library construction over `solvers d hM hO` at depth `P ≥ 1`, with completion
switch `C[S]`, parent residual `R` and leading pair `L`, is an expansion
(`S5.IsExpansion`) as soon as `R = R_U∘X`, `S = χ̃'A₁` and `L = (χ̃A₁, χ̃𝗉[A₁])` on the
label cell. -/
theorem construct_isExpansion (d : ParentGeometry hT U X k) (hM : MeanSolvable d)
    (hO : TransverseSolvable d) {pU : Pressure} {t₀ : ℝ} (χ : PaperWaveCutoff t₀ T) (ℓ h : ℝ)
    (amp : ℝ → Vec3 → Vec3) {P : ℕ} (hP : 1 ≤ P) (L : HierarchyTransverseOutput (S5.ops d))
    (R S : VP) (hRavg : (S5.ops d).average R = R)
    (hR : ∀ z ∈ hierarchyProfileSlab T,
      R.val.val.val z = momentumResidual (Icc 0 T) U pU z.1 (X 0 z.1 z.2.1))
    (hS : ∀ t ∈ Icc 0 T, ∀ a ∈ centeredCell, ∀ s,
      S.val.val.val (t, a, s) = χ.derivative t • S5.leading ℓ h amp t a s)
    (hV : ∀ t ∈ Icc 0 T, ∀ a ∈ centeredCell, ∀ s,
      L.V.val.val.val (t, a, s) = χ.value t • S5.leading ℓ h amp t a s)
    (hp : ∀ t ∈ Icc 0 T, ∀ a ∈ centeredCell, ∀ s,
      L.p.val.val.val (t, a, s) = χ.value t * S5.leadingPressure U X k ℓ h amp t a s) :
    S5.IsExpansion d pU χ ℓ h amp P R S
      ((solvers d hM hO).construct P (S5.curlCorrection d S) R hRavg L) := by
  obtain ⟨hV1, hp1, hB1, hq1⟩ :=
    (solvers d hM hO).construct_leading P (S5.curlCorrection d S) R hRavg L
  refine ⟨hR, hS, fun t ht a ha s => ?_, fun t ht a ha s => ?_, ?_, ⟨hB1, hq1⟩,
    fun p hp' => ?_, fun p hp' => ?_, fun p hp' => ?_, ?_⟩
  · rw [hV1]
    exact hV t ht a ha s
  · rw [hp1]
    exact hp t ht a ha s
  · exact ((solvers d hM hO).construct_eq_zero_of_index hP (Or.inl rfl)
      (S5.curlCorrection d S) R hRavg L).2.1
  · have h := (solvers d hM hO).construct_completion hp' (S5.curlCorrection d S) R hRavg L
    unfold S5.Cd
    rw [Nat.add_sub_cancel]
    exact h
  · obtain ⟨hf, hB, hq⟩ :=
      (solvers d hM hO).construct_mean_selected hp' (S5.curlCorrection d S) R hRavg L
    have hspec := solvers_solveMean_spec d hM hO _ hf
    rw [hB, hq, meanSource_eq (S5.ops d) _ (S5.curlCorrection d S) R (Finset.mem_Icc.mp hp').2]
    exact hspec
  · obtain ⟨hf, hV', hp''⟩ :=
      (solvers d hM hO).construct_transverse_selected hp' (S5.curlCorrection d S) R hRavg L
    have hspec := solvers_solveTransverse_spec d hM hO _ hf
    rw [hV', hp'', oscSource_add_suppSource_eq (S5.ops d) _ (S5.curlCorrection d S)
      (Finset.mem_Icc.mp hp').2]
    convert hspec using 2
  · obtain ⟨h1, -, h3, -, -⟩ := (solvers d hM hO).construct_eq_zero_of_index hP
      (Or.inr (Nat.lt_succ_self P)) (S5.curlCorrection d S) R hRavg L
    exact ⟨h1, h3⟩

/-- The pulled-back parent residual `R_U∘X` is a phase-independent profile. -/
theorem exists_residualProfile (d : ParentGeometry hT U X k) {pU : Pressure} {D lam : ℝ}
    (hPar : S5.Parent T U X pU D lam) :
    ∃ R : VP, (S5.ops d).average R = R ∧
      ∀ z ∈ hierarchyProfileSlab T,
        R.val.val.val z = momentumResidual (Icc 0 T) U pU z.1 (X 0 z.1 z.2.1) := by
  have hRs := contDiffOn_closedSlab_momentumResidual hT hPar.velocity_smooth hPar.pressure_smooth
  have hslice (f : ℝ → Vec3 → ℝ) (hf : ContDiffOn ℝ ∞ (Function.uncurry f)
      (Icc 0 T ×ˢ (univ : Set Vec3))) (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (f t) :=
    contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  have hsliceU (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (U t) :=
    contDiffOn_univ.mp (hPar.velocity_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  have hRp : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (momentumResidual (Icc 0 T) U pU t) :=
    fun t ht => spatiallyPeriodic_closedSlab_momentumResidual ht (hsliceU t ht)
      (hslice pU hPar.pressure_smooth t ht) hPar.velocity_periodic (hPar.pressure_periodic t ht)
  obtain ⟨R, hR, hval, -⟩ := exists_pulledBackParentResidual hT hPar.flow hPar.velocity_smooth
    hPar.velocity_periodic hRs hRp d
  exact ⟨R, hR, hval⟩

/-! ## Uniqueness of the expansion -/

/-- Uniqueness of the expansion: two families satisfying the defining recursions
(`S5.IsExpansion`) for the same parent, cutoff, seed and depth have the same `R`, `S` and
the same levels, given the uniqueness of the normalized mean solves (`MeanUnique`). The
transverse levels are unique by `TransverseSolution.unique` (`V_p(0) = 0`, zero phase mean
of `𝗉_p`), the leading level by its cell values, and the recursion propagates the
agreement level by level. -/
theorem IsExpansion.unique (d : ParentGeometry hT U X k) (hMU : MeanUnique d) {pU : Pressure}
    {t₀ : ℝ} {χ : PaperWaveCutoff t₀ T} {ℓ h : ℝ} {amp : ℝ → Vec3 → Vec3} {P : ℕ}
    {R S R' S' : VP} {u u' : HierarchyProfiles VP SP}
    (hu : S5.IsExpansion d pU χ ℓ h amp P R S u) (hu' : S5.IsExpansion d pU χ ℓ h amp P R' S' u') :
    R = R' ∧ S = S' ∧
      (∀ i ∈ Finset.Icc 1 P, u.V i = u'.V i ∧ u.B i = u'.B i ∧ u.p i = u'.p i ∧ u.q i = u'.q i) ∧
      ∀ i ∈ Finset.Icc 1 (P + 1), S5.Cd u i = S5.Cd u' i := by
  have hR : R = R' := HierarchyTwistedProfile.ext fun z hz =>
    (hu.residual z hz).trans (hu'.residual z hz).symm
  have hS : S = S' := eq_of_centeredCell fun t ht a ha s =>
    (hu.activation t ht a ha s).trans (hu'.activation t ht a ha s).symm
  subst hR hS
  -- agreement of the levels `1 ≤ p ≤ P`, together with `C_{p+1}`
  have hlev : ∀ p, 1 ≤ p → p ≤ P → u.V p = u'.V p ∧ u.B p = u'.B p ∧ u.p p = u'.p p ∧
      u.q p = u'.q p ∧ S5.Cd u (p + 1) = S5.Cd u' (p + 1) := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      intro hp1 hpP
      have hCp : ∀ V V' : VP, V = V' → S5.Cd u (p + 1) = S5.curlCorrection d V →
          S5.Cd u' (p + 1) = S5.curlCorrection d V' → S5.Cd u (p + 1) = S5.Cd u' (p + 1) := by
        intro V V' hVV h1 h2
        rw [h1, h2, hVV]
      have hmem : p ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨hp1, hpP⟩
      rcases Nat.lt_or_ge p 2 with hlt | hge
      · -- the leading level
        have hp : p = 1 := by omega
        subst hp
        have hV1 : u.V 1 = u'.V 1 := eq_of_centeredCell fun t ht a ha s =>
          (hu.leading_velocity t ht a ha s).trans (hu'.leading_velocity t ht a ha s).symm
        have hp1' : u.p 1 = u'.p 1 := eq_of_centeredCell fun t ht a ha s =>
          (hu.leading_pressure t ht a ha s).trans (hu'.leading_pressure t ht a ha s).symm
        refine ⟨hV1, hu.first_mean.1.trans hu'.first_mean.1.symm, hp1',
          hu.first_mean.2.trans hu'.first_mean.2.symm, ?_⟩
        exact hCp _ _ hV1 (hu.correction 1 hmem) (hu'.correction 1 hmem)
      · -- a correction level
        have hmem2 : p ∈ Finset.Icc 2 P := Finset.mem_Icc.mpr ⟨hge, hpP⟩
        have hVb : ∀ i, 1 ≤ i → i < p → u.V i = u'.V i := fun i h1 h2 => (ih i h2 h1 (by omega)).1
        have hBb : ∀ i, 1 ≤ i → i < p → u.B i = u'.B i := fun i h1 h2 => (ih i h2 h1 (by omega)).2.1
        have hPb : ∀ i, 1 ≤ i → i < p → u.p i = u'.p i :=
          fun i h1 h2 => (ih i h2 h1 (by omega)).2.2.1
        have hCb : ∀ i, 1 ≤ i → i ≤ p → S5.Cd u i = S5.Cd u' i := by
          intro i h1 h2
          rcases Nat.lt_or_ge i 2 with hi | hi
          · have hi1 : i = 1 := by omega
            subst hi1
            rw [hu.first_correction, hu'.first_correction]
          · have h := (ih (i - 1) (by omega) (by omega) (by omega)).2.2.2.2
            rwa [Nat.sub_add_cancel (by omega : 1 ≤ i)] at h
        have hH := levelSource_congr (S5.ops d) (S5.curlCorrection d S) hge hVb hBb hPb hCb
        -- the mean level
        obtain ⟨hm, hq0⟩ := hu.mean p hmem2
        obtain ⟨hm', hq0'⟩ := hu'.mean p hmem2
        have hmeanSrc : S5.meanSource (S5.ops d) u (S5.curlCorrection d S) R p =
            S5.meanSource (S5.ops d) u' (S5.curlCorrection d S) R p := by
          unfold S5.meanSource
          rw [hH]
        rw [hmeanSrc] at hm
        obtain ⟨hB, hq⟩ := hMU _ _ _ _ _ hm hq0 hm' hq0'
        -- the transverse level
        have hBle : ∀ i, 2 ≤ i → i ≤ p → u.B i = u'.B i := by
          intro i h1 h2
          rcases Nat.lt_or_ge i p with hi | hi
          · exact hBb i (by omega) hi
          · have hip : i = p := by omega
            subst hip
            exact hB
        have hsrc : S5.oscSource (S5.ops d) u (S5.curlCorrection d S) p + S5.suppSource (S5.ops d) u p =
            S5.oscSource (S5.ops d) u' (S5.curlCorrection d S) p + S5.suppSource (S5.ops d) u' p := by
          unfold S5.oscSource
          rw [hH, suppSource_congr (S5.ops d) hVb hBle (fun i h1 h2 => hCb i h1 h2.le)]
        have ht := hu.transverse p hmem2
        rw [hsrc] at ht
        obtain ⟨hV, hpp⟩ := TransverseSolution.unique d ht (hu'.transverse p hmem2)
        exact ⟨hV, hB, hpp, hq, hCp _ _ hV (hu.correction p hmem) (hu'.correction p hmem)⟩
  refine ⟨rfl, rfl, fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
    obtain ⟨a, b, c, e, -⟩ := hlev i h1 h2
    exact ⟨a, b, c, e⟩
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
    rcases Nat.lt_or_ge i 2 with hi2 | hi2
    · have hi1 : i = 1 := by omega
      subst hi1
      rw [hu.first_correction, hu'.first_correction]
    · have h := (hlev (i - 1) (by omega) (by omega)).2.2.2.2
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ i)] at h

/-- Every expansion is the library construction over `solvers d hM hO` (level by level), for
the parent residual, activation term and leading pair of the expansion, given
`MeanUnique d`. -/
theorem IsExpansion.eq_construct (d : ParentGeometry hT U X k) (hM : MeanSolvable d)
    (hMU : MeanUnique d) {pU : Pressure} {t₀ : ℝ} {χ : PaperWaveCutoff t₀ T} {ℓ h : ℝ}
    {amp : ℝ → Vec3 → Vec3} {P : ℕ} (hP : 1 ≤ P) {R S : VP} {u : HierarchyProfiles VP SP}
    (hu : S5.IsExpansion d pU χ ℓ h amp P R S u) (L : HierarchyTransverseOutput (S5.ops d))
    (hRavg : (S5.ops d).average R = R)
    (hV : ∀ t ∈ Icc 0 T, ∀ a ∈ centeredCell, ∀ s,
      L.V.val.val.val (t, a, s) = χ.value t • S5.leading ℓ h amp t a s)
    (hp : ∀ t ∈ Icc 0 T, ∀ a ∈ centeredCell, ∀ s,
      L.p.val.val.val (t, a, s) = χ.value t * S5.leadingPressure U X k ℓ h amp t a s) :
    let w := (solvers d hM (transverseSolvable d)).construct P (S5.curlCorrection d S) R hRavg L
    (∀ i ∈ Finset.Icc 1 P, u.V i = w.V i ∧ u.B i = w.B i ∧ u.p i = w.p i ∧ u.q i = w.q i) ∧
      ∀ i ∈ Finset.Icc 1 (P + 1), S5.Cd u i = S5.Cd w i :=
  (IsExpansion.unique d hMU hu (construct_isExpansion d hM (transverseSolvable d) χ ℓ h amp hP L R S
    hRavg hu.residual hu.activation hV hp)).2.2

end Solvers

end

end TorusEuler.Paper.Bridge
