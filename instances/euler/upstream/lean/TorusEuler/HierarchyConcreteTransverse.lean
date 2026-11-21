import TorusEuler.FiniteHierarchyConstruction
import TorusEuler.HierarchyConcreteOperators

/-! The actual smooth transverse solve for the ordered profile hierarchy. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

namespace HierarchySmoothProfile

variable {T : ℝ}

local notation "VP" => HierarchySmoothProfile T Vec3
local notation "SP" => HierarchySmoothProfile T ℝ
local notation "VPmap" => HierarchySmoothProfile T (Vec3 →L[ℝ] Vec3)

section Slices

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Restriction to a time line extracts the actual time derivative, including
at the boundary of the closed slab. -/
theorem hasDerivWithinAt_profileTime (f : HierarchySmoothProfile T E)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    HasDerivWithinAt (fun r => f.val (r, a, s))
      (fderivWithin ℝ f.val (hierarchyProfileSlab T) (t, a, s) (1, 0, 0))
      (Icc 0 T) t := by
  have hF := ((smooth f).differentiableOn (by simp) (t, a, s) ⟨ht, mem_univ _⟩).hasFDerivWithinAt
  have hd : HasDerivWithinAt (fun r : ℝ => (r, a, s)) (1, 0, 0) (Icc 0 T) t :=
    (hasDerivWithinAt_id t (Icc 0 T)).prodMk (hasDerivWithinAt_const t (Icc 0 T) (a, s))
  have hMap : MapsTo (fun r : ℝ => (r, a, s)) (Icc 0 T) (hierarchyProfileSlab T) :=
    fun _ hr => ⟨hr, mem_univ _⟩
  exact hF.comp_hasDerivWithinAt t hd hMap

/-- The phase direction ranges over the entire real line at each fixed time and label. -/
theorem hasDerivAt_profilePhase (f : HierarchySmoothProfile T E)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    HasDerivAt (fun r => f.val (t, a, r))
      (fderivWithin ℝ f.val (hierarchyProfileSlab T) (t, a, s) (0, 0, 1)) s := by
  have hF := ((smooth f).differentiableOn (by simp) (t, a, s) ⟨ht, mem_univ _⟩).hasFDerivWithinAt
  have hd : HasDerivAt (fun r : ℝ => (t, a, r)) (0, 0, 1) s :=
    (hasDerivAt_const (c := t) s).prodMk
      ((hasDerivAt_const (c := a) s).prodMk (hasDerivAt_id s))
  have hInside (r : ℝ) : (t, a, r) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  exact hF.comp_hasDerivAt s hd (Filter.Eventually.of_forall hInside)

end Slices

set_option maxHeartbeats 1000000 in
/-- A smooth phase solution realizes the concrete transverse momentum,
with the original velocity and pressure on every slice. -/
theorem exists_hierarchyConcreteTransverseOutput_of_solution
    {m : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {k : ℝ → Vec3 → Vec3}
    (hT : 0 < T) (G M : VPmap) (κ F : VP)
    (hM : ∀ x ∈ hierarchyProfileSlab T, M.val x = m x.1 x.2.1)
    (hκ : ∀ x ∈ hierarchyProfileSlab T, κ.val x = k x.1 x.2.1)
    {v : ℝ → (Vec3 × ℝ) → Vec3} {q : ℝ → (Vec3 × ℝ) → ℝ}
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) (hierarchyProfileSlab T))
    (hq : ContDiffOn ℝ ∞ (Function.uncurry q) (hierarchyProfileSlab T))
    (hmean : ∀ a t, t ∈ Icc 0 T → phaseMean (fun s => v t (a, s)) = 0)
    (htransverse : ∀ t ∈ Icc 0 T, ∀ a s, ⟪k t a, v t (a, s)⟫_ℝ = 0)
    (hmomentum : ∀ t ∈ Icc 0 T, ∀ a s, HasDerivWithinAt (fun u => v u (a, s))
      (F.val (t, a, s) - m t a (v t (a, s)) -
        deriv (fun σ => q t (a, σ)) s • k t a) (Icc 0 T) t) :
    let A := hierarchyConcreteOperators hT G M κ
    ∃ o : HierarchyTransverseOutput A,
      A.material o.V + A.phaseGrad o.p = F ∧
      ∀ t ∈ Icc 0 T, ∀ a s, o.V.val (t, a, s) = v t (a, s) ∧
        o.p.val (t, a, s) = q t (a, s) := by
  intro A
  let vP := ofSmooth (Function.uncurry v) hv
  let qP := ofSmooth (Function.uncurry q) hq
  have hVVal (t : ℝ) (a : Vec3) (s : ℝ) (ht : t ∈ Icc 0 T) :
      vP.val (t, a, s) = v t (a, s) := ofSmooth_apply hv ⟨ht, mem_univ _⟩
  have hPVal (t : ℝ) (a : Vec3) (s : ℝ) (ht : t ∈ Icc 0 T) :
      qP.val (t, a, s) = q t (a, s) := ofSmooth_apply hq ⟨ht, mem_univ _⟩
  have hAverage : A.average vP = 0 := by
    apply ext
    rintro ⟨t, a, s⟩ hx
    change (profilePhaseAverage hT vP).val (t, a, s) = 0
    rw [profilePhaseAverage_apply hT vP hx,
      show (fun σ => vP.val (t, a, σ)) = (fun σ => v t (a, σ)) from
        funext (fun σ => hVVal t a σ hx.1)]
    exact hmean a t hx.1
  have htrans (r : VP) : A.phaseAdv vP r = 0 := by
    apply ext
    rintro ⟨t, a, s⟩ hx
    change (advect hT (phaseDirections κ) vP r).val (t, a, s) = 0
    rw [advect_apply hT _ vP r hx, phaseDirections_apply κ vP hx, hκ _ hx,
      hVVal t a s hx.1, htransverse t hx.1 a s]
    exact map_zero _
  refine ⟨⟨vP, qP, hAverage, htrans⟩, ?_, ?_⟩
  · apply ext
    rintro ⟨t, a, s⟩ hx
    have ht := hx.1
    have hqSlice : (fun σ => qP.val (t, a, σ)) = (fun σ => q t (a, σ)) :=
      funext (fun σ => hPVal t a σ ht)
    have hqd := (hasDerivAt_profilePhase qP ht a s).deriv
    rw [hqSlice] at hqd
    have hvt := hmomentum t ht a s
    have hvtP := hvt.congr (fun r hr => hVVal r a s hr) (hVVal t a s ht)
    have hvd := ((hasDerivWithinAt_profileTime vP ht a s).derivWithin
      (uniqueDiffOn_Icc hT t ht)).symm.trans (hvtP.derivWithin (uniqueDiffOn_Icc hT t ht))
    change (A.material vP).val (t, a, s) + (phaseGradient hT κ qP).val (t, a, s) = F.val (t, a, s)
    rw [hierarchyConcreteOperators_material_apply hT G M κ vP hx, phaseGradient_apply hT κ qP hx,
      hM _ hx, hκ _ hx, hVVal t a s ht, ← hqd, hvd]
    abel
  · exact fun t ht a s => ⟨hVVal t a s ht, hPVal t a s ht⟩

set_option maxHeartbeats 1000000 in
/-- Equation (5.17) with its normalized pressure realizes the transverse
output for the concrete material and phase-gradient maps. -/
theorem exists_hierarchyConcreteTransverseOutput {m : ℝ → Vec3 → Vec3 →L[ℝ] Vec3}
    {k : ℝ → Vec3 → Vec3} (hT : 0 < T) (G M : VPmap) (κ : VP)
    (hm : ContDiffOn ℝ ∞ (Function.uncurry m) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hk : ContDiffOn ℝ ∞ (Function.uncurry k) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hM : ∀ x ∈ hierarchyProfileSlab T, M.val x = m x.1 x.2.1)
    (hκ : ∀ x ∈ hierarchyProfileSlab T, κ.val x = k x.1 x.2.1)
    (hκ₀ : ∀ a, k 0 a ≠ 0)
    (hκt : ∀ a t, t ∈ Icc 0 T →
      HasDerivWithinAt (fun r => k r a) (-((m t a).adjoint (k t a))) (Icc 0 T) t)
    (F : VP) (hFPer : ∀ a t, t ∈ Icc 0 T →
      Function.Periodic (fun s => F.val (t, a, s)) 1)
    (hFMean : profilePhaseAverage hT F = 0) :
    let A := hierarchyConcreteOperators hT G M κ
    ∃ o : HierarchyTransverseOutput A,
      A.material o.V + A.phaseGrad o.p = F ∧
      (∀ a t, t ∈ Icc 0 T →
        Function.Periodic (fun s => o.V.val (t, a, s)) 1 ∧
        Function.Periodic (fun s => o.p.val (t, a, s)) 1) ∧
      ∀ a s, o.V.val (0, a, s) = 0 := by
  intro A
  let f (t : ℝ) (as : Vec3 × ℝ) := F.val (t, as)
  have hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set (Vec3 × ℝ))) := smooth F
  have hfavg (a : Vec3) (t : ℝ) (ht : t ∈ Icc 0 T) : phaseMean (fun s => f t (a, s)) = 0 := by
    have h := congrArg (fun v : VP => v.val (t, a, 0)) hFMean
    rw [profilePhaseAverage_apply hT F ⟨ht, mem_univ _⟩] at h
    exact h
  obtain ⟨v, q, h0, hv, _, hq, hEq⟩ := exists_jointSmooth_oscillatoryPhaseSolve
    (M := m) (κ := k) (f := f) hT hm hk hf hκ₀ hκt hFPer hfavg
  obtain ⟨o, ho, hval⟩ := exists_hierarchyConcreteTransverseOutput_of_solution
    hT G M κ F hM hκ hv hq (fun a t ht => (hEq a t ht).2.1)
    (fun t ht a s => ((hEq a t ht).2.2.2.2 s).1)
    (fun t ht a s => ((hEq a t ht).2.2.2.2 s).2.2.2)
  refine ⟨o, ho, ?_, ?_⟩
  · intro a t ht
    constructor
    · intro s
      simp only [(hval t ht a _).1, (hEq a t ht).1 s]
    · intro s
      simp only [(hval t ht a _).2, (hEq a t ht).2.2.1 s]
  · intro a s
    rw [(hval 0 ⟨le_rfl, hT.le⟩ a s).1, h0]
    rfl

end HierarchySmoothProfile

end

end TorusEuler
