import TorusEuler.HierarchyPeriodicSolves
import TorusEuler.HierarchyTwistedProfiles
import TorusEuler.OscillatorySolveSymmetries

/-! The concrete hierarchy solvers on the lattice-twisted slab. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k₀ : Vec3}

local notation "VP" => HierarchyTwistedProfile T k₀ Vec3
local notation "SP" => HierarchyTwistedProfile T k₀ ℝ
local notation "MP" => HierarchyTwistedProfile T k₀ (Vec3 →L[ℝ] Vec3)

/-- Smooth phase-independent coefficients of the actual affine-wave equation
on the label torus. -/
structure TransverseCoefficients (M : MP) (κ : VP) where
  strain : ℝ → Vec3 → Vec3 →L[ℝ] Vec3
  covector : ℝ → Vec3 → Vec3
  strain_smooth : ContDiffOn ℝ ∞ (Function.uncurry strain) (Icc 0 T ×ˢ (univ : Set Vec3))
  covector_smooth : ContDiffOn ℝ ∞ (Function.uncurry covector) (Icc 0 T ×ˢ (univ : Set Vec3))
  strain_value : ∀ x ∈ hierarchyProfileSlab T, M.val.val.val x = strain x.1 x.2.1
  covector_value : ∀ x ∈ hierarchyProfileSlab T, κ.val.val.val x = covector x.1 x.2.1
  initial_nonzero : ∀ a, covector 0 a ≠ 0
  covector_equation : ∀ a t, t ∈ Icc 0 T →
    HasDerivWithinAt (fun u => covector u a) (-((strain t a).adjoint (covector t a))) (Icc 0 T) t

theorem TransverseCoefficients.strain_periodic {M : MP} {κ : VP}
    (d : TransverseCoefficients M κ) (t : ℝ) (ht : t ∈ Icc 0 T) :
    SpatiallyPeriodic (d.strain t) := by
  intro n a
  have h := twistedSlice M t a 0 n
  rw [d.strain_value _ ⟨ht, mem_univ _⟩, d.strain_value _ ⟨ht, mem_univ _⟩] at h
  exact h

theorem TransverseCoefficients.covector_periodic {M : MP} {κ : VP}
    (d : TransverseCoefficients M κ) (t : ℝ) (ht : t ∈ Icc 0 T) :
    SpatiallyPeriodic (d.covector t) := by
  intro n a
  have h := twistedSlice κ t a 0 n
  rw [d.covector_value _ ⟨ht, mem_univ _⟩, d.covector_value _ ⟨ht, mem_univ _⟩] at h
  exact h

theorem TransverseCoefficients.covector_independent {M : MP} {κ : VP}
    (d : TransverseCoefficients M κ) : HierarchyPeriodicProfile.PhaseIndependent κ.val.val := by
  intro x hx s
  exact (d.covector_value (x.1, x.2.1, s) ⟨hx.1, mem_univ _⟩).trans
    (d.covector_value x hx).symm

/-- The twisted solve retains the actual momentum, transverse constraint,
zero initial velocity, and parity and support laws of the selected profile. -/
structure TransverseResult (hT : 0 < T) (G M : MP) (κ F : VP) where
  output : HierarchyTransverseOutput (twistedHierarchyOperators hT G M κ)
  momentum : (twistedHierarchyOperators hT G M κ).material output.V +
    (twistedHierarchyOperators hT G M κ).phaseGrad output.p = F
  transverse : ∀ t ∈ Icc 0 T, ∀ a s, ⟪κ.val.val.val (t,a,s), output.V.val.val.val (t,a,s)⟫_ℝ = 0
  velocity_initial : ∀ a s, output.V.val.val.val (0,a,s) = 0
  pressure_mean : ∀ t ∈ Icc 0 T, ∀ a, phaseMean (fun s => output.p.val.val.val (t,a,s)) = 0
  pressure_value : ∀ t ∈ Icc 0 T, ∀ a s,
    output.p.val.val.val (t,a,s) = oscillatoryPhasePressure (M.val.val.val (t,a,0))
      (κ.val.val.val (t,a,0)) (fun r => F.val.val.val (t,a,r))
      (fun r => output.V.val.val.val (t,a,r)) s
  velocity_equation : ∀ t ∈ Icc 0 T, ∀ a s,
    HasDerivWithinAt (fun r => output.V.val.val.val (r,a,s))
      (F.val.val.val (t,a,s) - M.val.val.val (t,a,0) (output.V.val.val.val (t,a,s)) -
        deriv (fun r => output.p.val.val.val (t,a,r)) s • κ.val.val.val (t,a,0)) (Icc 0 T) t
  pressure_slope : ∀ t ∈ Icc 0 T, ∀ a s,
    HasDerivAt (fun r => output.p.val.val.val (t,a,r))
      (oscillatoryPressureSlope (M.val.val.val (t,a,0)) (κ.val.val.val (t,a,0))
        (F.val.val.val (t,a,s)) (output.V.val.val.val (t,a,s))) s
  reflection :
    (∀ t ∈ Icc 0 T, ∀ a, M.val.val.val (t,-a,0) = M.val.val.val (t,a,0)) →
    (∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t,-a,0) = κ.val.val.val (t,a,0)) →
    (∀ t ∈ Icc 0 T, ∀ a s, F.val.val.val (t,-a,-s) = -F.val.val.val (t,a,s)) →
    ∀ t ∈ Icc 0 T, ∀ a s,
      output.V.val.val.val (t,-a,-s) = -output.V.val.val.val (t,a,s) ∧
      output.p.val.val.val (t,-a,-s) = output.p.val.val.val (t,a,s)
  inactive : ∀ (τ : ℝ) (S : Set Vec3),
    (∀ t ∈ Icc 0 T, ∀ a s, t < τ ∨ a ∉ S → F.val.val.val (t,a,s) = 0) →
    ∀ t ∈ Icc 0 T, ∀ a s, t < τ ∨ a ∉ S →
      output.V.val.val.val (t,a,s) = 0 ∧ output.p.val.val.val (t,a,s) = 0

set_option maxHeartbeats 2000000 in
/-- Solve the projected oscillatory equation and reconstruct its unique
normalized pressure in the twisted profile space. -/
theorem exists_transverseResult (hT : 0 < T) (G M : MP) (κ : VP)
    (d : TransverseCoefficients M κ) (F : VP)
    (hFMean : (twistedHierarchyOperators hT G M κ).average F = 0) :
    Nonempty (TransverseResult hT G M κ F) := by
  let f (t : ℝ) (as : Vec3 × ℝ) := F.val.val.val (t, as)
  have hf : ContDiffOn ℝ ∞ (Function.uncurry f) (hierarchyProfileSlab T) := (HierarchySmoothProfile.smooth F.val.val)
  have hfmean (a : Vec3) (t : ℝ) (ht : t ∈ Icc 0 T) : phaseMean (fun s => f t (a,s)) = 0 := by
    have h := congrArg (fun u : VP => u.val.val.val (t,a,0)) hFMean
    change (HierarchySmoothProfile.profilePhaseAverage hT F.val.val).val (t,a,0) = 0 at h
    rw [HierarchySmoothProfile.profilePhaseAverage_apply hT F.val.val ⟨ht, mem_univ _⟩] at h
    exact h
  obtain ⟨v, q, h0, hv, hqdef, hq, hspec, htwist, hreflect, hzero⟩ :=
    exists_jointSmooth_oscillatoryPhaseSolve_withConditionalSymmetries
      (M := d.strain) (κ := d.covector) (f := f) (k := k₀) hT d.strain_smooth d.covector_smooth
      hf d.initial_nonzero d.covector_equation (fun a t _ => HierarchyPeriodicProfile.phasePeriodic F.val t a) hfmean
      d.strain_periodic d.covector_periodic (fun t _ a s n => twistedSlice F t a s n)
  obtain ⟨out, hmomentum, hval⟩ :=
    HierarchySmoothProfile.exists_hierarchyConcreteTransverseOutput_of_solution
      hT G.val.val M.val.val κ.val.val F.val.val d.strain_value d.covector_value hv hq
      (fun a t ht => (hspec a t ht).2.1) (fun t ht a s => ((hspec a t ht).2.2.2.2 s).1)
      (fun t ht a s => ((hspec a t ht).2.2.2.2 s).2.2.2)
  let vp := HierarchyPeriodicProfile.ofPeriodicSlices out.V fun t ht a s => by
    change out.V.val (t,a,s+1) = out.V.val (t,a,s)
    rw [(hval t ht a _).1, (hval t ht a _).1]
    exact (hspec a t ht).1 s
  let qp := HierarchyPeriodicProfile.ofPeriodicSlices out.p fun t ht a s => by
    change out.p.val (t,a,s+1) = out.p.val (t,a,s)
    rw [(hval t ht a _).2, (hval t ht a _).2]
    exact (hspec a t ht).2.2.1 s
  let V := ofTwistedSlices vp fun t ht a s n => by
    change out.V.val _ = out.V.val _
    rw [(hval t ht _ _).1, (hval t ht _ _).1]
    exact (htwist t ht a s n).1
  let Q := ofTwistedSlices qp fun t ht a s n => by
    change out.p.val _ = out.p.val _
    rw [(hval t ht _ _).2, (hval t ht _ _).2]
    exact (htwist t ht a s n).2
  let A := twistedHierarchyOperators hT G M κ
  have hmean : A.average V = 0 := Subtype.ext (Subtype.ext out.average_V)
  have hphase (r : VP) : A.phaseAdv V r = 0 := Subtype.ext (Subtype.ext (out.phaseAdv_V r.val.val))
  have hvq (t : ℝ) (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
      V.val.val.val (t,a,s) = v t (a,s) ∧ Q.val.val.val (t,a,s) = q t (a,s) := hval t ht a s
  refine ⟨⟨⟨V,Q,hmean,hphase⟩, Subtype.ext (Subtype.ext hmomentum), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro t ht a s
    change ⟪κ.val.val.val (t,a,s), V.val.val.val (t,a,s)⟫_ℝ = 0
    rw [d.covector_value _ ⟨ht, mem_univ _⟩, (hvq t ht a s).1]
    exact ((hspec a t ht).2.2.2.2 s).1
  · intro a s
    change V.val.val.val (0,a,s) = 0
    rw [(hvq 0 ⟨le_rfl, hT.le⟩ a s).1, h0]
    rfl
  · intro t ht a
    change phaseMean (fun s => Q.val.val.val (t,a,s)) = 0
    rw [show (fun s => Q.val.val.val (t,a,s)) = (fun s => q t (a,s)) from
      funext (fun s => (hvq t ht a s).2)]
    exact (hspec a t ht).2.2.2.1
  · intro t ht a s
    change Q.val.val.val (t,a,s) = _
    rw [(hvq t ht a s).2, d.strain_value (t,a,0) ⟨ht, mem_univ _⟩,
      d.covector_value (t,a,0) ⟨ht, mem_univ _⟩,
      show (fun r => V.val.val.val (t,a,r)) = (fun r => v t (a,r)) from
        funext (fun r => (hvq t ht a r).1), hqdef]
  · intro t ht a s
    change HasDerivWithinAt (fun r => V.val.val.val (r,a,s)) _ (Icc 0 T) t
    have hs := ((hspec a t ht).2.2.2.2 s).2.2.2
    have hqSlice : (fun r => Q.val.val.val (t,a,r)) = (fun r => q t (a,r)) :=
      funext (fun r => (hvq t ht a r).2)
    rw [d.strain_value (t,a,0) ⟨ht, mem_univ _⟩, d.covector_value (t,a,0) ⟨ht, mem_univ _⟩,
      (hvq t ht a s).1, hqSlice]
    exact hs.congr_of_mem (fun r hr => (hvq r hr a s).1) ht
  · intro t ht a s
    change HasDerivAt (fun r => Q.val.val.val (t,a,r)) _ s
    have hqSlice : (fun r => Q.val.val.val (t,a,r)) = (fun r => q t (a,r)) :=
      funext (fun r => (hvq t ht a r).2)
    rw [d.strain_value (t,a,0) ⟨ht, mem_univ _⟩, d.covector_value (t,a,0) ⟨ht, mem_univ _⟩,
      (hvq t ht a s).1, hqSlice]
    exact ((hspec a t ht).2.2.2.2 s).2.2.1
  · intro hm hk hf t ht a s
    have hm' (r : ℝ) (hr : r ∈ Icc 0 T) (b : Vec3) : d.strain r (-b) = d.strain r b := by
      simpa only [d.strain_value (r,-b,0) ⟨hr, mem_univ _⟩,
        d.strain_value (r,b,0) ⟨hr, mem_univ _⟩] using hm r hr b
    have hk' (r : ℝ) (hr : r ∈ Icc 0 T) (b : Vec3) : d.covector r (-b) = d.covector r b := by
      simpa only [d.covector_value (r,-b,0) ⟨hr, mem_univ _⟩,
        d.covector_value (r,b,0) ⟨hr, mem_univ _⟩] using hk r hr b
    change V.val.val.val (t,-a,-s) = -V.val.val.val (t,a,s) ∧
      Q.val.val.val (t,-a,-s) = Q.val.val.val (t,a,s)
    rw [(hvq t ht (-a) (-s)).1, (hvq t ht a s).1, (hvq t ht (-a) (-s)).2, (hvq t ht a s).2]
    exact hreflect hm' hk' hf t ht a s
  · intro τ S hf t ht a s hi
    change V.val.val.val (t,a,s) = 0 ∧ Q.val.val.val (t,a,s) = 0
    rw [(hvq t ht a s).1, (hvq t ht a s).2]
    exact hzero τ S hf t ht a s hi

/-- The selected transverse solve used at each retained correction level. -/
def solveTransverse (hT : 0 < T) (G M : MP) (κ : VP) (d : TransverseCoefficients M κ)
    (F : VP) (hF : (twistedHierarchyOperators hT G M κ).average F = 0) :
    TransverseResult hT G M κ F :=
  Classical.choice (exists_transverseResult hT G M κ d F hF)

/-- A mean solution on the label torus gives a solution of the mean
hierarchy equation without changing its velocity or pressure. -/
theorem exists_meanOutput_of_solution (hT : 0 < T) (G M : MP) (κ F : VP)
    (B : ℝ → Vec3 → Vec3) (q : ℝ → Vec3 → ℝ)
    (hB : ContDiffOn ℝ ∞ (Function.uncurry B) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hq : ContDiffOn ℝ ∞ (Function.uncurry q) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hBper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (B t))
    (hqper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (q t))
    (heq : ∀ (t : ℝ) (a : Vec3) (s : ℝ), t ∈ Icc 0 T →
      derivWithin (fun r => B r a) (Icc 0 T) t + M.val.val.val (t, a, s) (B t a) +
        (G.val.val.val (t, a, s)).adjoint (gradient (q t) a) = F.val.val.val (t, a, s)) :
    let A := twistedHierarchyOperators hT G M κ
    ∃ o : HierarchyMeanOutput A, A.material o.B + A.labelGrad o.q = F ∧
      ∀ t ∈ Icc 0 T, ∀ a s, o.B.val.val.val (t,a,s) = B t a ∧ o.q.val.val.val (t,a,s) = q t a := by
  intro A
  obtain ⟨out, hmomentum, hval⟩ := HierarchyPeriodicProfile.exists_periodicHierarchyMeanOutput
    hT G.val M.val κ.val F.val B q hB hq heq
  let Bp : VP := ofTwistedSlices out.B fun t ht a s n => by
    rw [(hval t (a + latticeVector n) (s + ⟪k₀, latticeVector n⟫_ℝ) ht).1, (hval t a s ht).1]
    exact hBper t ht n a
  let qp : SP := ofTwistedSlices out.q fun t ht a s n => by
    rw [(hval t (a + latticeVector n) (s + ⟪k₀, latticeVector n⟫_ℝ) ht).2, (hval t a s ht).2]
    exact hqper t ht n a
  have hmean : A.average Bp = Bp := Subtype.ext out.average_B
  have hphase (v : VP) : A.phaseAdv v Bp = 0 := Subtype.ext (out.phaseAdv_B v.val)
  have hqgrad : A.phaseGrad qp = 0 := Subtype.ext out.phaseGrad_q
  exact ⟨⟨Bp, qp, hmean, hphase, hqgrad⟩, Subtype.ext hmomentum, fun t ht a s => hval t a s ht⟩

/-- A source fixed by the phase average is an actual phase-independent,
periodic label field. -/
theorem meanSource_properties (hT : 0 < T) (G M : MP) (κ F : VP)
    (hF : (twistedHierarchyOperators hT G M κ).average F = F) :
    let f := fun (t : ℝ) (a : Vec3) => F.val.val.val (t,a,0)
    ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      (∀ t ∈ Icc 0 T, SpatiallyPeriodic (f t)) ∧
      ∀ t ∈ Icc 0 T, ∀ a s, F.val.val.val (t,a,s) = f t a := by
  intro f
  have hmean := average_is_mean hT G M κ F
  rw [hF] at hmean
  refine ⟨?_, hmean.2, ?_⟩
  · have hins : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => (z.1, z.2, (0 : ℝ)))
        (Icc 0 T ×ˢ (univ : Set Vec3)) :=
      contDiffOn_fst.prodMk (contDiffOn_snd.prodMk contDiffOn_const)
    exact (HierarchySmoothProfile.smooth F.val.val).comp hins (fun _ hz => ⟨hz.1, mem_univ _⟩)
  · exact fun t ht a s => hmean.1 (t,a,0) ⟨ht, mem_univ _⟩ s


end

end TorusEuler.HierarchyTwistedProfile
