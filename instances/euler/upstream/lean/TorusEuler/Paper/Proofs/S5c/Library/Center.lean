import TorusEuler.Paper.S5.Statements
import TorusEuler.Paper.Proofs.S5Bridge.Parent
import TorusEuler.Paper.Proofs.S5c.Library.CutoffBounds
import TorusEuler.SmoothPeriodicHolder

/-!
# Glue for Lemma 5.9: the velocity gradient at the origin

The proof of (5.50) (`sections/08_exact_wave.tex:257-278`):

* `leading_graph_hasFDerivAt_origin`: with `g(0) = 1`, `F_h(0) = 0`, `F_h'(0) = 1`, the
  chain rule (3.1) gives `D_xV_1^♮(t,0) = χ̃(t) 𝐚(t,0) ⊗ κ(t,0)` (`:257-261`), for any profile
  `V_1` with the cell values `χ̃A₁` of (3.7). The profile facts `F_h(0) = 0`, `F_h'(0) = 1`
  are hypotheses (in the proof of Lemma 5.9 they come from Lemma 3.1). The computation is the
  one of the library `hasFDerivAt_inductionPrimaryWave_origin`, whose call of the 3.1 content
  `hasDerivAt_waveProfile_zero` is replaced by the hypothesis.
* `expansion_eq_split`: `W = V_1 + (W_osc - V_1) + W̄` with `W_osc - V_1 = ∑_{p≥2} V_p +
  ∑_{p≥2}^{P+1} C_p` and `W̄ = ∑_{p≥2} B_p` (`:262-264`).
* `centralReturn_eq`: hence `E_c(t) = D_x(W_osc - V_1)^♮(t,0) + D_xW̄^♮(t,0)` (`:252-253`).
* `norm_fderiv_graph_le_words`: the operator norm of `D_x f^♮(t,0)` is at most the sum of the
  suprema of the first coordinate derivatives of `f^♮(t)`, the left side of (5.44) at `m = 1`.
-/

open Set Filter
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.Paper.Lib.S5c

open HierarchyTwistedProfile InnerProductSpace

noncomputable section

/-! ## Derivatives of slices and coordinate words -/

/-- The operator norm of a derivative is at most the sum of its values on the coordinate
vectors. -/
theorem opNorm_le_sum_coordinate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Vec3 →L[ℝ] E) : ‖L‖ ≤ ∑ j : Fin 3, ‖L (EuclideanSpace.single j 1)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : v = ∑ j : Fin 3, v j • EuclideanSpace.single j (1 : ℝ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v]
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  calc ‖L v‖ = ‖∑ j : Fin 3, v j • L (EuclideanSpace.single j 1)‖ := by
        conv_lhs => rw [hv]
        rw [map_sum]
        simp only [map_smul]
    _ ≤ ∑ j : Fin 3, ‖v j • L (EuclideanSpace.single j 1)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, ‖v‖ * ‖L (EuclideanSpace.single j 1)‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v j) (norm_nonneg _)
    _ = (∑ j : Fin 3, ‖L (EuclideanSpace.single j 1)‖) * ‖v‖ := by
        rw [← Finset.mul_sum, mul_comm]

/-- For a field with a bounded first derivative, the operator norm of the
derivative at a point is at most the sum, over the coordinate words of length one, of the
suprema in (5.44) at `m = 1`. -/
theorem norm_fderiv_le_words {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Vec3 → E} {B : ℝ} (hB : ∀ x, ‖iteratedFDeriv ℝ 1 F x‖ ≤ B)
    (x₀ : Vec3) :
    ‖fderiv ℝ F x₀‖ ≤
      ∑ i : Fin 1 → Fin 3, spatialSupNorm (spatialDerivativeWord (List.ofFn i) F) := by
  have hword (j : Fin 3) : spatialDerivativeWord [j] F =
      fun x => fderiv ℝ F x (EuclideanSpace.single j 1) := rfl
  have hbdd (j : Fin 3) :
      BddAbove (range fun x => ‖fderiv ℝ F x (EuclideanSpace.single j 1)‖) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨x, rfl⟩
    calc ‖fderiv ℝ F x (EuclideanSpace.single j 1)‖
        ≤ ‖fderiv ℝ F x‖ * ‖(EuclideanSpace.single j (1 : ℝ) : Vec3)‖ :=
          (fderiv ℝ F x).le_opNorm _
      _ = ‖iteratedFDeriv ℝ 1 F x‖ := by
          rw [show ‖(EuclideanSpace.single j (1 : ℝ) : Vec3)‖ = 1 by simp, mul_one,
            norm_iteratedFDeriv_one]
      _ ≤ B := hB x
  have hsum : (∑ i : Fin 1 → Fin 3, spatialSupNorm (spatialDerivativeWord (List.ofFn i) F)) =
      ∑ j : Fin 3, spatialSupNorm (fun x => fderiv ℝ F x (EuclideanSpace.single j 1)) := by
    refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 3)) _ _ fun i => ?_
    have hi : List.ofFn i = [i 0] := by simp [List.ofFn_succ]
    rw [hi, hword]
    rfl
  rw [hsum]
  refine (opNorm_le_sum_coordinate _).trans (Finset.sum_le_sum fun j _ => ?_)
  exact norm_le_spatialSupNorm (f := fun x => fderiv ℝ F x (EuclideanSpace.single j 1))
    (hbdd j) x₀

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3} {D lam : ℝ}

/-- The inverse label flow `Y(t) = X(t → 0)` of a parent is jointly smooth on the slab. -/
theorem inverseFlow_smooth (hT : 0 < T) (hP : S5.Parent T U X pU D lam) :
    ContDiffOn ℝ ∞ (Function.uncurry fun t => X t 0) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
  hP.flow.contDiffOn_inverseLabelFlow hT hP.velocity_smooth hP.velocity_periodic

/-- The inverse label flow is lattice equivariant. -/
theorem inverseFlow_lattice (hT : 0 < T) (hP : S5.Parent T U X pU D lam) {t : ℝ}
    (ht : t ∈ Icc 0 T) (n : Fin 3 → ℤ) (x : Vec3) :
    X t 0 (x + latticeVector n) = X t 0 x + latticeVector n := by
  obtain ⟨K, hK⟩ := Bridge.Parent.exists_lipschitz hT hP
  exact hP.flow.add_latticeVector hK hP.velocity_periodic ht ⟨le_rfl, hT.le⟩ n x

/-- The inverse label flow fixes the origin. -/
theorem inverseFlow_origin (hT : 0 < T) (hP : S5.Parent T U X pU D lam) {t : ℝ}
    (ht : t ∈ Icc 0 T) : X t 0 0 = 0 := by
  obtain ⟨K, hK⟩ := Bridge.Parent.exists_lipschitz hT hP
  have h := (hP.flow.inverse hK ⟨le_rfl, hT.le⟩ ht).1 (0 : Vec3)
  rw [Bridge.Parent.flow_origin hT hP ht] at h
  exact h

/-- The Eulerian readout `f^♮(t) = graphRead (X(t → 0)) f t` of a twisted profile is smooth on
`ℝ³` at each time of the slab. -/
theorem graphRead_slice_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hT : 0 < T) (hP : S5.Parent T U X pU D lam) (f : HierarchyTwistedProfile T k E) {t : ℝ}
    (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (graphRead (fun t => X t 0) f t) :=
  contDiff_slice (HierarchySmoothProfile.contDiffOn_graphRead k f.val.val
    (inverseFlow_smooth hT hP)) ht

/-- (5.44) at `m = 1`, left side: the operator norm of `D_xf^♮(t,0)` is at most the sum of the
suprema of the first coordinate derivatives of `f^♮(t)`. -/
theorem norm_fderiv_graph_le_words {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hT : 0 < T) (hP : S5.Parent T U X pU D lam) (f : HierarchyTwistedProfile T k E) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x₀ : Vec3) :
    ‖fderiv ℝ (graphRead (fun t => X t 0) f t) x₀‖ ≤
      ∑ i : Fin 1 → Fin 3,
        spatialSupNorm (spatialDerivativeWord (List.ofFn i) (graphRead (fun t => X t 0) f t)) := by
  obtain ⟨B, hB⟩ := exists_bound_spatial_jet_of_contDiffOn_periodic hT
    (HierarchySmoothProfile.contDiffOn_graphRead k f.val.val (inverseFlow_smooth hT hP))
    (fun r hr => spatiallyPeriodic_graphRead _ f r (inverseFlow_lattice hT hP hr)) 1
  exact norm_fderiv_le_words (hB t ht) x₀

/-! ## The leading oscillation at the origin -/

/-- The chain rule (3.1) at the origin for the leading oscillation: if `V_1` has the cell
values `χ̃A₁ = χ̃ g 𝐚 F_h` of (3.7), then, for `t ∈ [t₀,T]`,
`D_xV_1^♮(t,0) = χ̃(t) 𝐚(t,0) ⊗ κ(t,0)` (`08_exact_wave.tex:257-261`). The inputs are
`g(0) = 1` (`0 < ℓ_*`), `F_h(0) = 0` and `F_h'(0) = 1` (Lemma 3.1, here hypotheses), the
fixed origin of the inverse flow, and `κ(t,0) = (D_xX(t → 0)(0))ᵀ k_*`. -/
theorem leading_graph_hasFDerivAt_origin (hT : 0 < T) (hP : S5.Parent T U X pU D lam)
    {t₀ : ℝ} {center : ℝ → Vec3} {amp : ℝ → Vec3 → Vec3}
    (hamp : S5.IsSeed U X k t₀ T center amp) (hst : Icc t₀ T ⊆ Icc 0 T)
    (χ : PaperWaveCutoff t₀ T) {ℓ h : ℝ} (hℓ : 0 < ℓ)
    (hF0 : waveProfile h 0 = 0) (hF' : HasDerivAt (waveProfile h) 1 0)
    (V1 : HierarchyTwistedProfile T k Vec3)
    (hV1 : ∀ t ∈ Icc 0 T, ∀ a ∈ centeredCell, ∀ s,
      V1.val.val.val (t, a, s) = χ.value t • S5.leading ℓ h amp t a s)
    {t : ℝ} (ht : t ∈ Icc t₀ T) :
    HasFDerivAt (graphRead (fun t => X t 0) V1 t)
      (χ.value t • rankOne ℝ (center t) (S5.waveVector X k t 0)) 0 := by
  have htI : t ∈ Icc 0 T := hst ht
  let Y : Vec3 → Vec3 := X t 0
  have hYs : ContDiff ℝ ∞ Y := contDiff_slice (inverseFlow_smooth hT hP) htI
  have hY0 : Y 0 = 0 := inverseFlow_origin hT hP htI
  have hYd : HasFDerivAt Y (fderiv ℝ Y 0) 0 :=
    ((hYs.differentiable (by simp)) 0).hasFDerivAt
  have hκ : (fderiv ℝ Y 0).adjoint k = S5.waveVector X k t 0 := by
    simp only [S5.waveVector, labelWaveVector, Bridge.Parent.flow_origin hT hP htI, Y]
  have has : ContDiff ℝ ∞ (amp t) :=
    contDiffOn_univ.mp (hamp.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  have hamp0 : amp t 0 = center t := hamp.at_origin t ht
  -- the raw leading field along the graph
  let phase : Vec3 → ℝ := fun x => ⟪k, Y x⟫_ℝ
  let Bf : Vec3 → Vec3 := fun x => (χ.value t * radialEnvelope ℓ (Y x)) • amp t (Y x)
  have hphase₀ : phase 0 = 0 := by simp [phase, hY0]
  have hphase : HasFDerivAt phase (innerSL ℝ ((fderiv ℝ Y 0).adjoint k)) 0 :=
    (hasGradientAt_transportedPhase (A := fun _ => Y) (t := t) hYd).hasFDerivAt
  have hFφ : HasFDerivAt (waveProfile h ∘ phase) (innerSL ℝ ((fderiv ℝ Y 0).adjoint k)) 0 := by
    simpa only [one_smul] using hF'.comp_hasFDerivAt_of_eq 0 hphase hphase₀.symm
  have haY : DifferentiableAt ℝ (amp t) (Y 0) := (has.differentiable (by simp)) _
  have hB : DifferentiableAt ℝ Bf 0 := by
    have hc : DifferentiableAt ℝ (fun _ : Vec3 => χ.value t) 0 := differentiableAt_const _
    exact (hc.mul (((contDiff_radialEnvelope hℓ).differentiable (by simp) (Y 0)).comp 0
      hYd.differentiableAt)).smul (haY.comp 0 hYd.differentiableAt)
  have hB₀ : Bf 0 = χ.value t • amp t 0 := by
    simp [Bf, hY0, radialEnvelope_eq_one hℓ (show ‖(0 : Vec3)‖ ≤ ℓ by simpa using hℓ.le)]
  have hd := hFφ.smul hB.hasFDerivAt
  rw [Function.comp_apply, hphase₀, hF0, zero_smul, zero_add, hB₀] at hd
  have hraw : HasFDerivAt (fun x => waveProfile h (phase x) • Bf x)
      (χ.value t • rankOne ℝ (center t) (S5.waveVector X k t 0)) 0 := by
    refine hd.congr_fderiv ?_
    ext v
    simp [rankOne_apply, smul_smul, mul_comm, hκ, hamp0]
  -- near the origin the readout of `V_1` is the raw field
  have hnear : ∀ᶠ x in 𝓝 (0 : Vec3), Y x ∈ centeredCell := by
    have hball : Metric.ball (0 : Vec3) (1 / 2) ⊆ centeredCell := by
      intro x hx i
      have hnorm : ‖x‖ < (1 : ℝ) / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
      exact abs_le.mp ((PiLp.norm_apply_le x i).trans hnorm.le)
    have hc : ContinuousAt Y 0 := hYd.continuousAt
    rw [ContinuousAt, hY0] at hc
    exact hc.eventually (mem_of_superset (Metric.ball_mem_nhds _ (by norm_num)) hball)
  apply hraw.congr_of_eventuallyEq
  filter_upwards [hnear] with x hx
  change V1.val.val.val (t, Y x, ⟪k, Y x⟫_ℝ) = _
  rw [hV1 t htI (Y x) hx]
  simp only [S5.leading, phase, Bf, smul_smul]
  congr 1
  ring

/-! ## The split of the expansion -/

variable {hT : 0 < T}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ

/-- `W = V_1 + (W_osc - V_1) + W̄`, with `W_osc - V_1 = ∑_{p=2}^P V_p + ∑_{p=1}^P C_{p+1}` and
`W̄ = ∑_{p=2}^P B_p`, for profiles with `B_1 = 0` (`08_exact_wave.tex:262-264`). -/
theorem expansion_eq_split (u : HierarchyProfiles VP SP) {P : ℕ} (hP : 1 ≤ P)
    (hB1 : u.B 1 = 0) :
    S5.expansion u P = u.V 1 +
      ((∑ p ∈ Finset.Icc 2 P, u.V p) + ∑ p ∈ Finset.Icc 1 P, S5.Cd u (p + 1)) +
      ∑ p ∈ Finset.Icc 2 P, u.B p := by
  have hsplit (f : ℕ → VP) : ∑ p ∈ Finset.Icc 1 P, f p = f 1 + ∑ p ∈ Finset.Icc 2 P, f p := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_Icc.mpr ⟨le_rfl, hP⟩), add_comm]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [Finset.mem_erase, Finset.mem_Icc]
    omega
  unfold S5.expansion
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsplit u.V, hsplit u.B, hB1, zero_add]
  abel

/-- **The central error** (`08_exact_wave.tex:257-264`). For an expansion of depth `P ≥ 1`
over a parent, `V = U + W^♮` and `t ∈ [t₀,T]`, the difference
`∇V(t,0) - ∇U(t,0) - χ̃(t) 𝐚(t,0) ⊗ κ(t,0)` equals
`D_x(W_osc - V_1)^♮(t,0) + D_xW̄^♮(t,0)`. The profile facts `F_h(0) = 0`, `F_h'(0) = 1`
enter through `leading_graph_hasFDerivAt_origin`. -/
theorem centralReturn_eq (d : ParentGeometry hT U X k) (hP : S5.Parent T U X pU D lam)
    {t₀ : ℝ} {center : ℝ → Vec3} {amp : ℝ → Vec3 → Vec3}
    (hamp : S5.IsSeed U X k t₀ T center amp) (hst : Icc t₀ T ⊆ Icc 0 T)
    {χ : PaperWaveCutoff t₀ T} {ℓ h : ℝ} (hℓ : 0 < ℓ)
    (hF0 : waveProfile h 0 = 0) (hF' : HasDerivAt (waveProfile h) 1 0)
    {P : ℕ} (hP1 : 1 ≤ P) {R S : VP} {u : HierarchyProfiles VP SP}
    (hu : S5.IsExpansion d pU χ ℓ h amp P R S u) {t : ℝ} (ht : t ∈ Icc t₀ T) :
    let Y : Velocity := fun t => X t 0
    let V : Velocity := U + graphRead Y (S5.expansion u P)
    let G : VP := (∑ p ∈ Finset.Icc 2 P, u.V p) + ∑ p ∈ Finset.Icc 1 P, S5.Cd u (p + 1)
    let Bs : VP := ∑ p ∈ Finset.Icc 2 P, u.B p
    fderiv ℝ (V t) 0 - fderiv ℝ (U t) 0 -
        χ.value t • rankOne ℝ (center t) (S5.waveVector X k t 0) =
      fderiv ℝ (graphRead Y G t) 0 + fderiv ℝ (graphRead Y Bs t) 0 := by
  intro Y V G Bs
  have htI : t ∈ Icc 0 T := hst ht
  have hW : S5.expansion u P = u.V 1 + G + Bs := expansion_eq_split u hP1 hu.first_mean.1
  have hread : V t = U t + (graphRead Y (u.V 1) t + graphRead Y G t + graphRead Y Bs t) := by
    funext x
    change U t x + (S5.expansion u P).val.val.val (t, Y t x, ⟪k, Y t x⟫_ℝ) = _
    rw [hW]
    rfl
  have hUd : DifferentiableAt ℝ (U t) 0 :=
    ((contDiff_slice hP.velocity_smooth htI).differentiable (by simp)) 0
  have hd (f : VP) : DifferentiableAt ℝ (graphRead Y f t) 0 :=
    ((graphRead_slice_smooth hT hP f htI).differentiable (by simp)) 0
  have hV1 := leading_graph_hasFDerivAt_origin hT hP hamp hst χ hℓ hF0 hF' (u.V 1)
    hu.leading_velocity ht
  rw [hread, fderiv_add hUd (((hd _).add (hd _)).add (hd _)), fderiv_add ((hd _).add (hd _)) (hd _),
    fderiv_add (hd _) (hd _), hV1.fderiv]
  abel

end

end TorusEuler.Paper.Lib.S5c
