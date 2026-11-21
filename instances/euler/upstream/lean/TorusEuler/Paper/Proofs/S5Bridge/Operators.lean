import TorusEuler.Paper.Proofs.S5Bridge.Seed
import TorusEuler.FiniteHierarchyConstruction
import TorusEuler.HierarchyTwistedSolves
import TorusEuler.HierarchyTwistedCompletion
import TorusEuler.FirstWaveHierarchyInput
import TorusEuler.HierarchyConcreteTransverse
import TorusEuler.OscillatorySolveSymmetries

/-!
# S5 bridge: the operators of the expansion and the transverse solves

* Pointwise values of the operators `S5.ops d` (`∂_t + M`, `κ∂_s`, `⟨·⟩`) on the slab.
* Vanishing of the phase advections against means and transverse fields.
* The transverse equation (5.15) with `V(0) = 0` and zero phase mean of the pressure:
  existence for every source of zero phase mean (`transverseSolvable`, the library ODE
  solve `exists_transverseResult`) and uniqueness (`TransverseSolution.unique`, by
  linear ODE uniqueness at each label and phase after the pressure slope is eliminated
  with the transversality constraint).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Bridge

open HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ

/-! ## Pointwise values -/

/-- `((∂_t + M) V)(t,a,s) = ∂_t V(t,a,s) + M(t,a) V(t,a,s)` on the slab. -/
theorem ops_material_eval (d : ParentGeometry hT U X k) (V : VP) {p : HierarchyProfilePoint}
    (hp : p ∈ hierarchyProfileSlab T) :
    ((S5.ops d).material V).val.val.val p =
      derivWithin (fun r => V.val.val.val (r, p.2.1, p.2.2)) (Icc 0 T) p.1 +
        S5.strainField U X p.1 p.2.1 (V.val.val.val p) := by
  have h := material_eval hT d.inverse d.strain d.covector V hp
  rw [d.strain_value p hp] at h
  exact h

/-- `(κ∂_s q)(t,a,s) = ∂_s q(t,a,s) κ(t,a)` on the slab. -/
theorem ops_phaseGrad_eval (d : ParentGeometry hT U X k) (q : SP) {p : HierarchyProfilePoint}
    (hp : p ∈ hierarchyProfileSlab T) :
    ((S5.ops d).phaseGrad q).val.val.val p =
      deriv (fun z => q.val.val.val (p.1, p.2.1, z)) p.2.2 • S5.waveVector X k p.1 p.2.1 := by
  have h := phaseGrad_eval hT d.inverse d.strain d.covector q hp
  rw [d.covector_value p hp] at h
  exact h

/-- `⟨V⟩(t,a,s) = ∫₀¹ V(t,a,σ) dσ` on the slab. -/
theorem ops_average_eval (d : ParentGeometry hT U X k) (V : VP) {p : HierarchyProfilePoint}
    (hp : p ∈ hierarchyProfileSlab T) :
    ((S5.ops d).average V).val.val.val p = phaseMean (fun z => V.val.val.val (p.1, p.2.1, z)) :=
  average_eval hT d.inverse d.strain d.covector V hp

/-- A profile fixed by the phase average is independent of the phase. -/
theorem phaseIndependent_of_average_eq (d : ParentGeometry hT U X k) {B : VP}
    (hB : (S5.ops d).average B = B) : HierarchyPeriodicProfile.PhaseIndependent B.val.val := by
  have h : HierarchyPeriodicProfile.PhaseIndependent ((S5.ops d).average B).val.val :=
    (average_is_mean hT d.inverse d.strain d.covector B).1
  rw [hB] at h
  exact h

/-- `(V·κ)∂_s B = 0` when `B` is independent of the phase. -/
theorem ops_phaseAdv_of_mean (d : ParentGeometry hT U X k) (V : VP) {B : VP}
    (hB : (S5.ops d).average B = B) : (S5.ops d).phaseAdv V B = 0 :=
  phaseAdv_eq_zero_of_independent hT d.inverse d.strain d.covector V B
    (phaseIndependent_of_average_eq d hB)

/-- `(V·κ)∂_s Y = 0` when `κ·V = 0` on the slab. -/
theorem ops_phaseAdv_of_transverse (d : ParentGeometry hT U X k) {V : VP}
    (hV : ∀ t ∈ Icc 0 T, ∀ a s, ⟪S5.waveVector X k t a, V.val.val.val (t, a, s)⟫_ℝ = 0)
    (Y : VP) : (S5.ops d).phaseAdv V Y = 0 :=
  phaseAdv_eq_zero_of_transverse hT d.inverse d.strain d.covector V Y fun x hx => by
    rw [d.covector_value x hx]
    exact hV x.1 hx.1 x.2.1 x.2.2

/-- The phase average is idempotent. -/
theorem ops_average_idempotent (d : ParentGeometry hT U X k) (f : VP) :
    (S5.ops d).average ((S5.ops d).average f) = (S5.ops d).average f :=
  average_idempotent hT d.inverse d.strain d.covector f

/-- `⟨C[V]⟩ = 0`. -/
theorem ops_average_curlCorrection (d : ParentGeometry hT U X k) (V : VP) :
    (S5.ops d).average (S5.curlCorrection d V) = 0 :=
  average_complete hT d.inverse d.strain d.covector d.mean.inverse_independent
    d.oscillation.covector_independent d.oscillation.covector_ne_zero V

/-! ## Coefficient values of a parent geometry -/

/-- The covector coefficient of the transverse solve is `κ(t,a)` on `[0,T]`. -/
theorem oscillation_covector_eq (d : ParentGeometry hT U X k) {t : ℝ} (ht : t ∈ Icc 0 T)
    (a : Vec3) : d.oscillation.covector t a = S5.waveVector X k t a :=
  (d.oscillation.covector_value (t, a, 0) ⟨ht, mem_univ _⟩).symm.trans
    (d.covector_value (t, a, 0) ⟨ht, mem_univ _⟩)

/-- The strain coefficient of the transverse solve is `M(t,a)` on `[0,T]`. -/
theorem oscillation_strain_eq (d : ParentGeometry hT U X k) {t : ℝ} (ht : t ∈ Icc 0 T)
    (a : Vec3) : d.oscillation.strain t a = S5.strainField U X t a :=
  (d.oscillation.strain_value (t, a, 0) ⟨ht, mem_univ _⟩).symm.trans
    (d.strain_value (t, a, 0) ⟨ht, mem_univ _⟩)

/-- `κ(t,a) ≠ 0` on `[0,T]` (recorded by the carrier). -/
theorem geometry_waveVector_ne_zero (d : ParentGeometry hT U X k) {t : ℝ} (ht : t ∈ Icc 0 T)
    (a : Vec3) : S5.waveVector X k t a ≠ 0 := fun h =>
  d.oscillation.covector_ne_zero t ht a ((d.covector_value (t, a, 0) ⟨ht, mem_univ _⟩).trans h)

/-- The covector equation `κ_t = -Mᵀκ` on `[0,T]` (recorded by the carrier). -/
theorem geometry_waveVector_hasDerivWithinAt (d : ParentGeometry hT U X k) (a : Vec3) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun u => S5.waveVector X k u a)
      (-((S5.strainField U X t a).adjoint (S5.waveVector X k t a))) (Icc 0 T) t := by
  have h := d.oscillation.covector_equation a t ht
  rw [oscillation_covector_eq d ht a, oscillation_strain_eq d ht a] at h
  exact h.congr (fun u hu => (oscillation_covector_eq d hu a).symm)
    (oscillation_covector_eq d ht a).symm

/-- The seed operator `t ↦ -(Id - 2P_κ)M` at a label is continuous on `[0,T]`. -/
theorem geometry_seedOperator_continuousOn (d : ParentGeometry hT U X k) (a : Vec3) :
    ContinuousOn (fun u => affineWaveAmplitudeOperator (S5.strainField U X u a)
      (S5.waveVector X k u a)) (Icc 0 T) := by
  have hM : ContinuousOn (fun u => d.oscillation.strain u a) (Icc 0 T) :=
    continuousOn_slice (f := d.oscillation.strain) d.oscillation.strain_smooth.continuousOn a
      (fun _ hu => ⟨hu, mem_univ a⟩)
  have hK : ContinuousOn (fun u => d.oscillation.covector u a) (Icc 0 T) :=
    continuousOn_slice (f := d.oscillation.covector) d.oscillation.covector_smooth.continuousOn a
      (fun _ hu => ⟨hu, mem_univ a⟩)
  refine (continuousOn_affineWaveAmplitudeOperator hM hK fun u hu => ?_).congr fun u hu => ?_
  · rw [oscillation_covector_eq d hu a]
    exact geometry_waveVector_ne_zero d hu a
  · simp only [oscillation_covector_eq d hu a, oscillation_strain_eq d hu a]

/-! ## The transverse equation (5.15) -/

/-- A homogeneous solution of (5.15) — `V_t + MV + κ∂_s𝗉 = 0`, `κ·V = 0`, `V(0) = 0`,
and `𝗉` of zero phase mean — vanishes. Transversality eliminates the pressure slope,
`∂_s𝗉 = -2κ·MV/|κ|²`, so that `V_t = -(Id - 2P_κ)MV` at each label and phase, a linear
ODE with zero initial value; then `∂_s𝗉 = 0`, and the zero phase mean gives `𝗉 = 0`. -/
theorem transverse_homogeneous_eq_zero (d : ParentGeometry hT U X k) {W : VP} {r : SP}
    (hmom : (S5.ops d).material W + (S5.ops d).phaseGrad r = 0)
    (htr : ∀ t ∈ Icc 0 T, ∀ a s, ⟪S5.waveVector X k t a, W.val.val.val (t, a, s)⟫_ℝ = 0)
    (hinit : ∀ a s, W.val.val.val (0, a, s) = 0)
    (hmean : ∀ t ∈ Icc 0 T, ∀ a, phaseMean (fun s => r.val.val.val (t, a, s)) = 0) :
    W = 0 ∧ r = 0 := by
  have hpt : ∀ t ∈ Icc 0 T, ∀ a s,
      derivWithin (fun u => W.val.val.val (u, a, s)) (Icc 0 T) t +
        S5.strainField U X t a (W.val.val.val (t, a, s)) +
          deriv (fun z => r.val.val.val (t, a, z)) s • S5.waveVector X k t a = 0 := by
    intro t ht a s
    have hz : (t, a, s) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
    have h := congrArg (fun F : VP => F.val.val.val (t, a, s)) hmom
    change ((S5.ops d).material W).val.val.val (t, a, s) +
      ((S5.ops d).phaseGrad r).val.val.val (t, a, s) = 0 at h
    rw [ops_material_eval d W hz, ops_phaseGrad_eval d r hz] at h
    exact h
  -- the velocity vanishes on the slab
  have hW : ∀ a s, ∀ t ∈ Icc 0 T, W.val.val.val (t, a, s) = 0 := by
    intro a s
    let w : ℝ → Vec3 := fun u => W.val.val.val (u, a, s)
    let A : ℝ → Vec3 →L[ℝ] Vec3 := fun u =>
      affineWaveAmplitudeOperator (S5.strainField U X u a) (S5.waveVector X k u a)
    have hw : ∀ t ∈ Icc 0 T, HasDerivWithinAt w (A t (w t)) (Icc 0 T) t := by
      intro t ht
      have hd : HasDerivWithinAt w (derivWithin w (Icc 0 T) t) (Icc 0 T) t :=
        (HierarchySmoothProfile.hasDerivWithinAt_profileTime W.val.val ht a s).differentiableWithinAt.hasDerivWithinAt
      obtain ⟨c, hc⟩ : ∃ c, deriv (fun z => r.val.val.val (t, a, z)) s = c := ⟨_, rfl⟩
      have hp := hpt t ht a s
      rw [hc, add_assoc, add_eq_zero_iff_eq_neg, neg_add'] at hp
      -- `hp : w' = -(M w) - c • κ`
      have hi := (geometry_waveVector_hasDerivWithinAt d a ht).inner ℝ hd
      have h0 : HasDerivWithinAt (fun u => ⟪S5.waveVector X k u a, w u⟫_ℝ) 0 (Icc 0 T) t :=
        (hasDerivWithinAt_const t (Icc 0 T) (0 : ℝ)).congr (fun u hu => htr u hu a s) (htr t ht a s)
      have heq := (uniqueDiffOn_Icc hT t ht).eq_deriv _ hi h0
      change ⟪S5.waveVector X k t a, derivWithin w (Icc 0 T) t⟫_ℝ +
        ⟪-((S5.strainField U X t a).adjoint (S5.waveVector X k t a)), w t⟫_ℝ = 0 at heq
      have hp' : derivWithin w (Icc 0 T) t =
          -(S5.strainField U X t a (w t)) - c • S5.waveVector X k t a := hp
      rw [hp'] at heq
      simp only [inner_sub_right, inner_neg_right, real_inner_smul_right, inner_neg_left,
        ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq] at heq
      have hn : ‖S5.waveVector X k t a‖ ^ 2 ≠ 0 :=
        pow_ne_zero 2 (norm_ne_zero_iff.mpr (geometry_waveVector_ne_zero d ht a))
      have hcv : c = -(2 * ⟪S5.waveVector X k t a, S5.strainField U X t a (w t)⟫_ℝ /
          ‖S5.waveVector X k t a‖ ^ 2) := by
        have h1 : c * ‖S5.waveVector X k t a‖ ^ 2 =
            -(2 * ⟪S5.waveVector X k t a, S5.strainField U X t a (w t)⟫_ℝ) := by linarith
        rw [neg_div', eq_div_iff hn]
        exact h1
      refine hd.congr_deriv ?_
      rw [hp', hcv]
      change _ = affineWaveAmplitudeOperator (S5.strainField U X t a) (S5.waveVector X k t a) (w t)
      rw [affineWaveAmplitudeOperator_apply, neg_smul, sub_neg_eq_add]
    have hz : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun _ => (0 : Vec3)) (A t 0) (Icc 0 T) t :=
      fun t _ => by
        rw [show A t 0 = 0 from map_zero (A t)]
        exact hasDerivWithinAt_const t (Icc 0 T) (0 : Vec3)
    have hEq := linearODE_unique_of_mem ordConnected_Icc (left_mem_Icc.mpr hT.le)
      (geometry_seedOperator_continuousOn d a) hw hz (hinit a s)
    exact fun t ht => hEq ht
  have hWz : W = 0 := HierarchyTwistedProfile.ext fun x hx => hW x.2.1 x.2.2 x.1 hx.1
  refine ⟨hWz, HierarchyTwistedProfile.ext fun x hx => ?_⟩
  -- the pressure slope vanishes, and the zero phase mean fixes the constant
  have hslope : ∀ s, deriv (fun z => r.val.val.val (x.1, x.2.1, z)) s = 0 := by
    intro s
    have hp := hpt x.1 hx.1 x.2.1 s
    have hd0 : derivWithin (fun u => W.val.val.val (u, x.2.1, s)) (Icc 0 T) x.1 = 0 := by
      have hc : derivWithin (fun u => W.val.val.val (u, x.2.1, s)) (Icc 0 T) x.1 =
          derivWithin (fun _ => (0 : Vec3)) (Icc 0 T) x.1 :=
        derivWithin_congr (fun u hu => hW x.2.1 s u hu) (hW x.2.1 s x.1 hx.1)
      rw [hc]
      exact (hasDerivWithinAt_const x.1 (Icc 0 T) (0 : Vec3)).derivWithin
        (uniqueDiffOn_Icc hT x.1 hx.1)
    rw [hd0, hW x.2.1 s x.1 hx.1, map_zero, zero_add, zero_add, smul_eq_zero] at hp
    exact hp.resolve_right (geometry_waveVector_ne_zero d hx.1 x.2.1)
  have hfun : (fun z => r.val.val.val (x.1, x.2.1, z)) = fun _ => (0 : ℝ) := by
    refine phaseProfile_eq_of_hasDerivAt (f := fun _ => (0 : ℝ)) (fun z => ?_)
      (fun z => hasDerivAt_const z (0 : ℝ)) ?_
    · have h := (HierarchySmoothProfile.hasDerivAt_profilePhase r.val.val hx.1 x.2.1 z).differentiableAt.hasDerivAt
      rw [hslope z] at h
      exact h
    · rw [hmean x.1 hx.1 x.2.1, phaseMean_const]
  have hx2 := congrFun hfun x.2.2
  exact hx2

/-- Uniqueness of the solution of (5.15) from `V(0) = 0` with pressure of zero phase mean:
two solutions with the same source agree. -/
theorem TransverseSolution.unique (d : ParentGeometry hT U X k) {f V V' : VP} {q q' : SP}
    (h : S5.TransverseSolution d f V q) (h' : S5.TransverseSolution d f V' q') :
    V = V' ∧ q = q' := by
  have hmom : (S5.ops d).material (V - V') + (S5.ops d).phaseGrad (q - q') = 0 := by
    rw [map_sub, map_sub, sub_add_sub_comm, h.momentum, h'.momentum, sub_self]
  have htr : ∀ t ∈ Icc 0 T, ∀ a s,
      ⟪S5.waveVector X k t a, (V - V').val.val.val (t, a, s)⟫_ℝ = 0 := by
    intro t ht a s
    change ⟪S5.waveVector X k t a, V.val.val.val (t, a, s) - V'.val.val.val (t, a, s)⟫_ℝ = 0
    rw [inner_sub_right, h.transverse t ht a s, h'.transverse t ht a s, sub_self]
  have hinit : ∀ a s, (V - V').val.val.val (0, a, s) = 0 := by
    intro a s
    change V.val.val.val (0, a, s) - V'.val.val.val (0, a, s) = 0
    rw [h.initial a s, h'.initial a s, sub_self]
  have hmean : ∀ t ∈ Icc 0 T, ∀ a, phaseMean (fun s => (q - q').val.val.val (t, a, s)) = 0 := by
    intro t ht a
    have hc (r : SP) : Continuous (fun s => r.val.val.val (t, a, s)) :=
      (HierarchySmoothProfile.smooth r.val.val).continuousOn.comp_continuous
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
        (fun _ => ⟨ht, mem_univ _⟩)
    change phaseMean (fun s => q.val.val.val (t, a, s) - q'.val.val.val (t, a, s)) = 0
    rw [phaseMean_sub (hc q) (hc q'), h.pressure_mean_zero t ht a, h'.pressure_mean_zero t ht a,
      sub_self]
  obtain ⟨hV, hq⟩ := transverse_homogeneous_eq_zero d hmom htr hinit hmean
  exact ⟨sub_eq_zero.mp hV, sub_eq_zero.mp hq⟩

/-- Every source of zero phase mean has a solution of (5.15) from `V(0) = 0` with pressure
of zero phase mean (the library ODE solve `exists_transverseResult`). -/
def TransverseSolvable (d : ParentGeometry hT U X k) : Prop :=
  ∀ f : VP, (S5.ops d).average f = 0 → ∃ (V : VP) (q : SP), S5.TransverseSolution d f V q

/-- The transverse equation (5.15) is solvable for every source of zero phase mean. -/
theorem transverseSolvable (d : ParentGeometry hT U X k) : TransverseSolvable d := by
  intro f hf
  obtain ⟨r⟩ := exists_transverseResult hT d.inverse d.strain d.covector d.oscillation f hf
  refine ⟨r.output.V, r.output.p, r.momentum, fun t ht a s => ?_, r.output.average_V,
    r.velocity_initial, r.pressure_mean⟩
  have h := r.transverse t ht a s
  rw [d.covector_value (t, a, s) ⟨ht, mem_univ _⟩] at h
  exact h

end

end TorusEuler.Paper.Bridge
