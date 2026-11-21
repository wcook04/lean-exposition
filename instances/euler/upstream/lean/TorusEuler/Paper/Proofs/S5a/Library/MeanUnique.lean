import TorusEuler.Paper.Proofs.S5a.Library.MeanSolve
import TorusEuler.Paper.Proofs.S5a.Library.MeanIntegrate
import TorusEuler.PaperMeanFlowAdapter
import TorusEuler.TorusFourier

/-!
# S5a library: the normalized solution of the mean equation (5.11) is unique (from Theorem 4.2)

The proof of Proposition 5.4 uses that the mean equation (5.11) has a unique solution
(`sections/06c_finite_hierarchy.tex:372`, "by Theorem 4.2"; `sections/06d_mean_estimates.tex:3-14`).
`meanUnique_of_theorem42 h4_2 d hP : Bridge.MeanUnique d` carries this out for the parent of §5.1:

* a solution `(B, q̄)` of (5.11) is a smooth mean solution in label coordinates
  (`exists_smoothMeanSolution`: the phase-0 slices, with `B = D_aX v`, `v = z_t`);
* a smooth mean solution solves the integrated system (4.9) (`integratedSolution_of_smooth`:
  "(4.9) is (4.11) integrated once in time", `sections/06b_mean_inverse.tex:136-139`), for the
  integrated source `src = -∫_0^t (D_aX)^T f̄` and the curves `K`, `Ω` of (4.1);
* the uniqueness clause of the first item of Theorem 4.2 (`h4_2`) then gives the velocity, hence
  `B = D_aX v`; the label gradient of `q̄` follows from (5.11), and the normalization
  `∫_cell q̄(t,·,0) = 0` fixes `q̄`.
-/

open Set MeasureTheory
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5a

noncomputable section

open HierarchyTwistedProfile

local notation "C½" => HalfHolder (UnitAddTorus (Fin 3)) Vec3
local notation "K½" => HalfHolder (UnitAddTorus (Fin 3)) (Vec3 →L[ℝ] Vec3)

/-- Normed group structure on the divergence-free subspace (local shortcut). -/
local instance meanUniqueSolenoidalNormedGroup : NormedAddCommGroup endpointHalfHolderSolenoidal :=
  inferInstance

/-- Real normed space structure on the divergence-free subspace (local shortcut). -/
local instance meanUniqueSolenoidalNormedSpace : NormedSpace ℝ endpointHalfHolderSolenoidal :=
  inferInstance

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {pU : Pressure}
  {D lam : ℝ}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ

/-- A smooth periodic field on the slab is realized by a curve in `C^{0,1/2}` that is smooth in
time (the empty word of the generic slab jets; the smooth variant of `exists_halfHolder_curve`). -/
theorem exists_smooth_halfHolder_curve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (hT : 0 < T) (f : ℝ → Vec3 → E)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (f t)) :
    ∃ c : ℝ → HalfHolder (UnitAddTorus (Fin 3)) E, ContDiffOn ℝ ∞ c (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, ∀ a, HalfHolder.eval (toUnitTorus a) (c t) = f t a := by
  obtain ⟨j⟩ := exists_endpointSlabHalfHolderJets hT (fun i : Fin 3 => EuclideanSpace.single i 1)
    (Function.uncurry f) hf hper
  exact ⟨j.curve [], j.smooth [], fun t ht a => j.eval_lift [] t ht a⟩

/-- The pressure of a solution of (5.11) is independent of the phase: `κ∂_s q̄ = 0` with
`κ ≠ 0`. -/
theorem pressure_phase_const (d : ParentGeometry hT U X k) {q : SP}
    (h : (S5.ops d).phaseGrad q = 0) {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    q.val.val.val (t, a, s) = q.val.val.val (t, a, 0) := by
  have hsm : ContDiffOn ℝ ∞ (fun z : ℝ => q.val.val.val (t, a, z)) univ :=
    (HierarchySmoothProfile.smooth q.val.val).comp
      (contDiffOn_const.prodMk (contDiffOn_const.prodMk contDiffOn_id))
      (fun z _ => ⟨ht, mem_univ _⟩)
  have hdiff : Differentiable ℝ (fun z : ℝ => q.val.val.val (t, a, z)) :=
    (contDiffOn_univ.mp hsm).differentiable (by simp)
  have hder : ∀ z, deriv (fun z : ℝ => q.val.val.val (t, a, z)) z = 0 := by
    intro z
    have h1 : ((S5.ops d).phaseGrad q).val.val.val (t, a, z) = 0 :=
      congrArg (fun P : VP => P.val.val.val (t, a, z)) h
    rw [Bridge.ops_phaseGrad_eval d q (p := (t, a, z)) ⟨ht, mem_univ _⟩] at h1
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 (Bridge.geometry_waveVector_ne_zero d ht a)
  exact is_const_of_deriv_eq_zero hdiff hder s 0

/-- The phase-0 slice of a jointly smooth profile is jointly smooth in `(t, a)`. -/
theorem slice0_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : HierarchyTwistedProfile T k E) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => g.val.val.val (z.1, z.2, 0)) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
  (HierarchySmoothProfile.smooth g.val.val).comp
    (contDiffOn_fst.prodMk (contDiffOn_snd.prodMk contDiffOn_const))
    (fun _ hz => ⟨hz.1, mem_univ _⟩)

/-- (5.11) at a point of the slab, with `B`, `q̄` replaced by their phase-0 values:
`f = ∂_tB + MB + (D_aX)^{-T}∇_a q̄`. Consequently the source is independent of the phase. -/
theorem momentum_eval (d : ParentGeometry hT U X k) {f B : VP} {q : SP}
    (hs : S5.MeanSolution d f B q) {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    f.val.val.val (t, a, s) =
      derivWithin (fun r => B.val.val.val (r, a, 0)) (Icc 0 T) t +
        fderiv ℝ (U t) (X 0 t a) (B.val.val.val (t, a, 0)) +
        (fderiv ℝ (X t 0) (X 0 t a)).adjoint (gradient (fun y => q.val.val.val (t, y, 0)) a) := by
  have hBind := Bridge.phaseIndependent_of_average_eq d hs.phase_independent
  have hx : ((t, a, s) : HierarchyProfilePoint) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  have hm := congrArg (fun P : VP => P.val.val.val (t, a, s)) hs.momentum
  change ((S5.ops d).material B).val.val.val (t, a, s) +
    ((S5.ops d).labelGrad q).val.val.val (t, a, s) = f.val.val.val (t, a, s) at hm
  have hlab : ((S5.ops d).labelGrad q).val.val.val (t, a, s) =
      (fderiv ℝ (X t 0) (X 0 t a)).adjoint (gradient (fun y => q.val.val.val (t, y, 0)) a) := by
    change (HierarchySmoothProfile.labelGradient hT d.inverse.val.val q.val.val).val (t, a, s) = _
    rw [HierarchySmoothProfile.labelGradient_eq_adjoint_gradient hT d.inverse.val.val q.val.val ht
      a s, d.inverse_value (t, a, s) hx]
    have hq' : (fun y => q.val.val.val (t, y, s)) = fun y => q.val.val.val (t, y, 0) :=
      funext fun y => pressure_phase_const d hs.pressure_phase_independent ht y s
    rw [hq']
  have hB' : ∀ r ∈ Icc 0 T, B.val.val.val (r, a, s) = B.val.val.val (r, a, 0) :=
    fun r hr => hBind (r, a, 0) ⟨hr, mem_univ _⟩ s
  have hmat : ((S5.ops d).material B).val.val.val (t, a, s) =
      derivWithin (fun r => B.val.val.val (r, a, 0)) (Icc 0 T) t +
        fderiv ℝ (U t) (X 0 t a) (B.val.val.val (t, a, 0)) := by
    rw [Bridge.ops_material_eval d B hx]
    change derivWithin (fun r => B.val.val.val (r, a, s)) (Icc 0 T) t +
      fderiv ℝ (U t) (X 0 t a) (B.val.val.val (t, a, s)) = _
    rw [hB' t ht, derivWithin_congr (fun r hr => hB' r hr) (hB' t ht)]
  rw [← hm, hmat, hlab]

/-- A solution `(B, q̄)` of (5.11) is a smooth mean solution in label coordinates (the phase-0
slices; `B = D_aX v`, `v = z_t`, `div_a v = 0`, `B_t + MB + (D_aX)^{-T}∇_a q̄ = f̄`), for the
parent `par` of Theorem 4.2 with the coefficients of the flow. -/
theorem exists_smoothMeanSolution (d : ParentGeometry hT U X k)
    {D' : ℝ} (par : PaperMeanParent T D' D')
    (hpar : ∀ t ∈ Icc 0 T, ∀ (a : Vec3),
      par.F (t, toUnitTorus a) = fderiv ℝ (X 0 t) a ∧
        par.G (t, toUnitTorus a) = fderiv ℝ (X t 0) (X 0 t a) ∧
          par.M (t, toUnitTorus a) = fderiv ℝ (U t) (X 0 t a))
    {f B : VP} {q : SP} (hs : S5.MeanSolution d f B q) :
    ∃ s : PaperSmoothMeanSolution par (fun t a => f.val.val.val (t, a, 0)),
      (∀ t ∈ Icc 0 T, ∀ a s', B.val.val.val (t, a, s') = fderiv ℝ (X 0 t) a (s.velocity t a)) ∧
      ∀ t ∈ Icc 0 T, ∀ a, s.pressure t a = q.val.val.val (t, a, 0) := by
  obtain ⟨v, z, hv, hz, hper, h0, hTz, hzd, hdiv, hBv⟩ := hs.endpoint
  have hB := hs.phase_independent
  have hqper : ∀ t ∈ Icc 0 T, ∀ (n : Fin 3 → ℤ) a,
      q.val.val.val (t, a + latticeVector n, 0) = q.val.val.val (t, a, 0) := by
    intro t ht n a
    have h1 := twistedSlice q t a 0 n
    rw [pressure_phase_const d hs.pressure_phase_independent ht (a + latticeVector n) 0,
      ← pressure_phase_const d hs.pressure_phase_independent ht (a + latticeVector n)
        (0 + ⟪k, latticeVector n⟫_ℝ)]
    rw [h1]
  refine ⟨⟨v, z, fun t a => B.val.val.val (t, a, 0), fun t a => q.val.val.val (t, a, 0),
    hv, hz, slice0_contDiff B, slice0_contDiff q, ?_, h0, hTz, ?_, hzd, hdiv, ?_⟩,
    fun t ht a s' => ?_, fun t ht a => rfl⟩
  · intro t ht
    exact ⟨(hper t ht).1, (hper t ht).2, fun n a => meanProfile_periodic d hB ht 0 0 n a,
      fun n a => hqper t ht n a⟩
  · intro t ht x
    rw [(hpar t ht x).1]
    exact hBv t ht x 0
  · intro t ht x
    rw [(hpar t ht x).2.1, (hpar t ht x).2.2]
    change derivWithin (fun r => B.val.val.val (r, x, 0)) (Icc 0 T) t +
      fderiv ℝ (U t) (X 0 t x) (B.val.val.val (t, x, 0)) +
      (fderiv ℝ (X t 0) (X 0 t x)).adjoint (gradient (fun y => q.val.val.val (t, y, 0)) x) =
        f.val.val.val (t, x, 0)
    exact (momentum_eval d hs ht x 0).symm
  · exact hBv t ht a s'

/-- If two smooth solutions of the mean equation (5.11) in label coordinates have the same
velocity, their pressures have the same gradient: `(D_aX)^T (D_aX)^{-T} = Id`. -/
theorem smoothMeanSolution_pressure_eq {D' : ℝ} {par : PaperMeanParent T D' D'}
    {force : Velocity} (s₁ s₂ : PaperSmoothMeanSolution par force)
    (hvel : ∀ t ∈ Icc 0 T, ∀ x, s₁.velocity t x = s₂.velocity t x)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) :
    gradient (s₁.pressure t) x = gradient (s₂.pressure t) x := by
  have hmean : ∀ r ∈ Icc 0 T, ∀ y, s₁.mean r y = s₂.mean r y := fun r hr y => by
    rw [s₁.mean_eq r hr y, s₂.mean_eq r hr y, hvel r hr y]
  have hd : derivWithin (fun r => s₁.mean r x) (Icc 0 T) t =
      derivWithin (fun r => s₂.mean r x) (Icc 0 T) t :=
    derivWithin_congr (fun r hr => hmean r hr x) (hmean t ht x)
  have h1 := s₁.momentum t ht x
  have h2 := s₂.momentum t ht x
  rw [hd, hmean t ht x] at h1
  have h3 : (par.G (t, toUnitTorus x)).adjoint (gradient (s₁.pressure t) x) =
      (par.G (t, toUnitTorus x)).adjoint (gradient (s₂.pressure t) x) := by
    have := h1.trans h2.symm
    exact add_left_cancel this
  have hinv : ∀ y, (par.F (t, toUnitTorus x)).adjoint ((par.G (t, toUnitTorus x)).adjoint y) = y := by
    intro y
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp,
      par.left_inverse (toUnitTorus x) t ht, ContinuousLinearMap.adjoint_id]
    rfl
  have := congrArg (par.F (t, toUnitTorus x)).adjoint h3
  rwa [hinv, hinv] at this

/-- Two smooth periodic functions with the same gradient and the same mean over the label cell
coincide. -/
theorem eq_of_gradient_eq_of_integral_eq {φ ψ : Vec3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ∀ x, gradient φ x = gradient ψ x)
    (hI : (∫ x in centeredCell, φ x) = ∫ x in centeredCell, ψ x) : φ = ψ := by
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hfd : ∀ x, fderiv ℝ (fun y => φ y - ψ y) x = 0 := by
    intro x
    rw [fderiv_fun_sub (hφd x) (hψd x)]
    have h := hg x
    have h' : fderiv ℝ φ x = fderiv ℝ ψ x := by
      have := congrArg (InnerProductSpace.toDual ℝ Vec3) h
      simpa [gradient] using this
    rw [h', sub_self]
  have hconst : ∀ x, φ x - ψ x = φ 0 - ψ 0 :=
    fun x => is_const_of_fderiv_eq_zero (hφd.sub hψd) hfd x 0
  have hvol : (volume : Measure Vec3).real centeredCell = 1 := by
    let : IsProbabilityMeasure unitTorusMeasure :=
      inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin 3 =>
        (AddCircle.haarAddCircle : Measure UnitAddCircle)))
    have h := torusIntegral_eq_centeredCell (fun _ => (1 : ℝ))
    simpa only [integral_const, setIntegral_const, measureReal_def, Measure.restrict_apply_univ,
      measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one] using h.symm
  have hint : (∫ x in centeredCell, (φ x - ψ x)) = 0 := by
    rw [integral_sub (hφ.continuous.continuousOn.integrableOn_compact isCompact_centeredCell)
      (hψ.continuous.continuousOn.integrableOn_compact isCompact_centeredCell), hI, sub_self]
  have hk : φ 0 - ψ 0 = 0 := by
    have : (∫ x in centeredCell, (φ x - ψ x)) = ∫ x in centeredCell, (φ 0 - ψ 0) :=
      setIntegral_congr_fun isCompact_centeredCell.measurableSet (fun x _ => hconst x)
    rw [this, setIntegral_const, hvol] at hint
    simpa using hint
  exact funext fun x => sub_eq_zero.mp ((hconst x).trans hk)

set_option maxHeartbeats 3200000 in
/-- **The normalized solution of the mean equation (5.11) is unique** (`06d_mean_estimates.tex:3-14`),
for the parent of §5.1. `h4_2` enters through the uniqueness clause of its first item: a normalized
solution `(B, q̄)` of (5.11) gives (by `integratedSolution_of_smooth`, "(4.11) integrated once in
time") a solution of the integrated system (4.9) with source `L = -∫_0^t (D_aX)^T f̄`, whose velocity
is unique; this fixes `B = D_aX v`, then `∇_a q̄` by (5.11), and `q̄` by its normalization. -/
theorem meanUnique_of_theorem42 (h4_2 : Statement.theorem_4_2) (d : ParentGeometry hT U X k)
    (hP : S5.Parent T U X pU D lam) : Bridge.MeanUnique d := by
  intro f B B' q q' hs hn hs' hn'
  have h0 : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hD1 : 1 ≤ D := Bridge.Parent.scale_ge_one hP
  obtain ⟨C, p, -, h42⟩ := h4_2
  obtain ⟨hKper, hΩper, K₀, K₁, Ω₀, Ω₁, hK₀, hK₁, hΩ₀, hΩ₁⟩ := exists_meanCoefficient_bounds hT hP
  obtain ⟨Kc, hKs, hKe⟩ :=
    exists_smooth_halfHolder_curve hT (meanKinetic X) (meanKinetic_smooth hT hP) hKper
  obtain ⟨Ωc, hΩs, hΩe⟩ :=
    exists_smooth_halfHolder_curve hT (meanVorticity U X) (meanVorticity_smooth hT hP) hΩper
  have H := h42 T U X (meanParentFlow_of_parent hT hP) (meanHsharp_le_of_parent hT hP) D D K₀ K₁
    Ω₀ Ω₁ hD1 (fun t ht a => hP.inverse_deformation_le t ht a)
    (fun t ht a => hP.gradient_le t ht _) hK₀ hK₁ hΩ₀ hΩ₁ Kc Ωc hKe hΩe
  dsimp only at H
  obtain ⟨H1, -, -⟩ := H
  -- the parent as a `PaperMeanParent`
  obtain ⟨Lip, hLip⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT
    (hP.velocity_smooth.of_le (by simp)) hP.velocity_periodic
  have hLeul : ∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (U t) x‖ ≤ D := by
    intro t ht x
    have h : ‖meanGradient U X t (X t 0 x)‖ ≤ D := hP.gradient_le t ht _
    rwa [meanGradient, (hP.flow.inverse hLip h0 ht).2 x] at h
  obtain ⟨par, hpar⟩ := exists_paperMeanParent_of_flow hT hP.flow hP.velocity_smooth
    hP.velocity_periodic (fun t ht a => hP.inverse_deformation_le t ht a) hLeul
    (meanHsharp_le_of_parent hT hP)
  have hpar' : ∀ t ∈ Icc 0 T, ∀ (a : Vec3),
      par.F (t, toUnitTorus a) = fderiv ℝ (X 0 t) a ∧
        par.G (t, toUnitTorus a) = fderiv ℝ (X t 0) (X 0 t a) ∧
          par.M (t, toUnitTorus a) = fderiv ℝ (U t) (X 0 t a) :=
    fun t ht a => ⟨(hpar t ht a).1, (hpar t ht a).2.1, (hpar t ht a).2.2.1⟩
  -- the source of (5.11) and its integral
  have hforce : ContDiffOn ℝ ∞ (Function.uncurry fun t a => f.val.val.val (t, a, 0))
      (Icc 0 T ×ˢ (univ : Set Vec3)) := slice0_contDiff f
  have hfper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (fun a => f.val.val.val (t, a, 0)) := by
    intro t ht n a
    change f.val.val.val (t, a + latticeVector n, 0) = f.val.val.val (t, a, 0)
    have h1 : f.val.val.val (t, a + latticeVector n, 0) =
        f.val.val.val (t, a + latticeVector n, 0 + ⟪k, latticeVector n⟫_ℝ) :=
      ((momentum_eval d hs ht _ _).trans (momentum_eval d hs ht _ 0).symm).symm
    exact h1.trans (twistedSlice f t a 0 n)
  -- the source `L = -∫_0^t (D_aX)^T f̄` of (4.9) as a smooth curve in `C^{0,1/2}`
  have hFsm := hP.flow.contDiffOn_forwardLabelDerivative hT hP.velocity_smooth hP.velocity_periodic
  let w : ℝ → Vec3 → Vec3 := fun r x => (fderiv ℝ (X 0 r) x).adjoint (f.val.val.val (r, x, 0))
  have hw : ContDiffOn ℝ ∞ (Function.uncurry w) (Icc 0 T ×ˢ (univ : Set Vec3)) := by
    have adj : ContDiff ℝ ∞ (fun F : Vec3 →L[ℝ] Vec3 => F.adjoint) :=
      (ContinuousLinearMap.adjoint : (Vec3 →L[ℝ] Vec3) ≃ₗᵢ⋆[ℝ] (Vec3 →L[ℝ] Vec3)).contDiff
    exact (adj.comp_contDiffOn hFsm).clm_apply hforce
  let g : ℝ → Vec3 → Vec3 := fun t x => -endpointPrimitive (fun r => w r x) t
  have hg : ContDiffOn ℝ ∞ (Function.uncurry g) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    (contDiffOn_endpointPhysicalJointPrimitive hT hw).neg
  have hgper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (g t) := by
    intro t ht n x
    change -endpointPrimitive (fun r => w r (x + latticeVector n)) t =
      -endpointPrimitive (fun r => w r x) t
    unfold endpointPrimitive
    refine congrArg Neg.neg (intervalIntegral.integral_congr fun r hr => ?_)
    rw [uIcc_of_le ht.1] at hr
    have hr' : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
    change (fderiv ℝ (X 0 r) (x + latticeVector n)).adjoint
        (f.val.val.val (r, x + latticeVector n, 0)) =
      (fderiv ℝ (X 0 r) x).adjoint (f.val.val.val (r, x, 0))
    have h1 : fderiv ℝ (X 0 r) (x + latticeVector n) = fderiv ℝ (X 0 r) x :=
      parent_deformation_periodic hT hP hr' n x
    have h2 : f.val.val.val (r, x + latticeVector n, 0) = f.val.val.val (r, x, 0) :=
      hfper r hr' n x
    rw [h1, h2]
  obtain ⟨src, hsrc, hsrcv⟩ := exists_smooth_halfHolder_curve hT g hg hgper
  have hSource : ∀ t ∈ Icc 0 T, ∀ x, HalfHolder.eval (toUnitTorus x) (src t) =
      endpointPhysicalForcePrimitive par.F (fun t a => f.val.val.val (t, a, 0)) (t, x) := by
    intro t ht x
    rw [hsrcv t ht x]
    change -endpointPrimitive (fun r => w r x) t = -endpointPrimitive
      (fun r => (par.F (r, toUnitTorus x)).adjoint (f.val.val.val (r, x, 0))) t
    unfold endpointPrimitive
    refine congrArg Neg.neg (intervalIntegral.integral_congr fun r hr => ?_)
    rw [uIcc_of_le ht.1] at hr
    have hr' : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
    change (fderiv ℝ (X 0 r) x).adjoint (f.val.val.val (r, x, 0)) =
      (par.F (r, toUnitTorus x)).adjoint (f.val.val.val (r, x, 0))
    rw [(hpar r hr' x).1]
  obtain ⟨z0, v0, c0, φ0, G0, -, -, huniq⟩ := H1 src hsrc.continuousOn
  have hKp : ∀ t ∈ Icc 0 T, ∀ x, HalfHolder.eval (toUnitTorus x) (Kc t) = par.kinetic t x := by
    intro t ht x
    rw [hKe t ht x]
    simp only [PaperMeanParent.kinetic, meanKinetic, meanDeformation, (hpar t ht x).1]
  have hΩp : ∀ t ∈ Icc 0 T, ∀ x, HalfHolder.eval (toUnitTorus x) (Ωc t) = par.vorticity t x := by
    intro t ht x
    rw [hΩe t ht x]
    simp only [PaperMeanParent.vorticity, meanVorticity, meanDeformation, meanGradient,
      (hpar t ht x).1, (hpar t ht x).2.2.1]
  let : CompleteSpace endpointHalfHolderSolenoidal :=
    isClosed_endpointHalfHolderSolenoidal.completeSpace_coe
  -- the velocity of every smooth mean solution is the unique velocity of (4.9)
  have key : ∀ s : PaperSmoothMeanSolution par (fun t a => f.val.val.val (t, a, 0)),
      ∀ t ∈ Icc 0 T, ∀ x, s.velocity t x = HalfHolder.eval (toUnitTorus x) (v0 t : C½) := by
    intro s t ht x
    obtain ⟨u, hu⟩ := integratedSolution_of_smooth hT s Kc Ωc hKs hΩs hKp hΩp hforce src hsrc
      hSource
    obtain ⟨φ, Gφ, hGc, hG⟩ := u.exists_potential hKs.continuousOn hΩs.continuousOn
      hsrc.continuousOn
    have hess : EndpointSystemSolution T Kc Ωc src (endpointPrimitive u.velocity) u.velocity
        u.constant φ Gφ :=
      ⟨u.continuous, fun t ht => hasDerivWithinAt_endpointPrimitive_of_continuousOn u.continuous ht,
        by simp only [endpointPrimitive, intervalIntegral.integral_same], u.terminal, hGc,
        fun t ht => ⟨(hG t ht).1, (hG t ht).2.2.1⟩, fun t ht => (hG t ht).2.2.2⟩
    obtain ⟨-, hv, -, -⟩ := huniq _ _ _ _ _ hess
    rw [← hu t ht x, hv ht]
  obtain ⟨s₁, hB₁, hp₁⟩ := exists_smoothMeanSolution d par hpar' hs
  obtain ⟨s₂, hB₂, hp₂⟩ := exists_smoothMeanSolution d par hpar' hs'
  have hvel : ∀ t ∈ Icc 0 T, ∀ x, s₁.velocity t x = s₂.velocity t x :=
    fun t ht x => (key s₁ t ht x).trans (key s₂ t ht x).symm
  refine ⟨HierarchyTwistedProfile.ext fun x hx => ?_, HierarchyTwistedProfile.ext fun x hx => ?_⟩
  · obtain ⟨t, a, s⟩ := x
    rw [hB₁ t hx.1 a s, hB₂ t hx.1 a s, hvel t hx.1 a]
  · obtain ⟨t, a, s⟩ := x
    have ht : t ∈ Icc 0 T := hx.1
    change q.val.val.val (t, a, s) = q'.val.val.val (t, a, s)
    rw [pressure_phase_const d hs.pressure_phase_independent ht a s,
      pressure_phase_const d hs'.pressure_phase_independent ht a s]
    have e₁ : s₁.pressure t = fun y => q.val.val.val (t, y, 0) := funext (hp₁ t ht)
    have e₂ : s₂.pressure t = fun y => q'.val.val.val (t, y, 0) := funext (hp₂ t ht)
    have hfun : s₁.pressure t = s₂.pressure t :=
      eq_of_gradient_eq_of_integral_eq (meanInt_slice_spatial s₁.pressure_smooth ht)
        (meanInt_slice_spatial s₂.pressure_smooth ht)
        (fun y => smoothMeanSolution_pressure_eq s₁ s₂ hvel ht y)
        (by rw [e₁, e₂]; exact (hn t ht).trans (hn' t ht).symm)
    have := congrFun hfun a
    rwa [hp₁ t ht a, hp₂ t ht a] at this

end

end TorusEuler.Paper.Lib.S5a
