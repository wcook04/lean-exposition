import TorusEuler.Paper.Proofs.S5c.Library.HessCalc
import TorusEuler.Paper.Proofs.S5c.Library.HigherNorms
import TorusEuler.Paper.Proofs.S5c.Library.HigherGrad
import TorusEuler.Paper.Proofs.S5c.Library.FlowGeom

/-!
# The Hessian identity (5.51) of Lemma 5.9 at one point, through Lemma D.1

`sections/08_exact_wave.tex:172-204`.  With `𝗉_1 = q`, `D_x𝗉_1^♮ = (𝐝q + κ∂_sq)^♮`
(`gradient_graphRead_eq`), so `D_x²𝗉_1^♮` is the derivative of the readout of the two vector
profiles `g₁ = 𝐝q` and `g₂ = κ∂_sq`.  The tensors of (5.51) are

* the phase derivative of `g₂`, `κ ∂_s²q`, which gives the first tensor `-c_𝐚F_h'κ⊗κ`
  (`phaseGrad_phase_deriv`, `leading_hess_point`);
* the label and phase derivatives of `g₁` and the label derivative of `g₂`, which are the remaining
  tensors and are bounded by the scaled jets of `g₁`, `g₂` of order one (`leading_hess_point`),
  that is by `‖g₁‖_{[1],γ}`, `‖g₂‖_{[1],γ}` (`scaledJets_of_wNorm`).  These norms are bounded through
  Lemma D.1 (`hD_1`): `wNorm_labelGrad_le` ((D.4) for `G ∂_{a_j}q`, (D.3) for `∂_{a_j}`) and
  `wNorm_phaseGradScalar_le` ((D.4) for `κ ∂_sq`, (D.3) for `∂_s`).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5c

open HierarchyTwistedProfile InnerProductSpace AppendixD ContinuousLinearMap

noncomputable section

/-- The chain rule for the readout `y ↦ G(Y y, k·Y y)` of a vector-valued label-phase field. -/
theorem fderiv_graphField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : Vec3 × ℝ → E}
    (hG : ContDiff ℝ ∞ G) {Y : Vec3 → Vec3} (hY : ContDiff ℝ ∞ Y) (k x v : Vec3) :
    fderiv ℝ (fun y => G (Y y, ⟪k, Y y⟫_ℝ)) x v =
      fderiv ℝ G (Y x, ⟪k, Y x⟫_ℝ) (fderiv ℝ Y x v, ⟪k, fderiv ℝ Y x v⟫_ℝ) := by
  have hYd : HasFDerivAt Y (fderiv ℝ Y x) x := ((hY.differentiable (by simp)) x).hasFDerivAt
  have hΦ : HasFDerivAt (fun y => ((Y y, ⟪k, Y y⟫_ℝ) : Vec3 × ℝ))
      ((fderiv ℝ Y x).prod ((innerSL ℝ k).comp (fderiv ℝ Y x))) x :=
    hYd.prodMk ((innerSL ℝ k).hasFDerivAt.comp x hYd)
  have hFd : HasFDerivAt G (fderiv ℝ G (Y x, ⟪k, Y x⟫_ℝ)) (Y x, ⟪k, Y x⟫_ℝ) :=
    ((hG.differentiable (by simp)) _).hasFDerivAt
  have hc := (hFd.comp x hΦ).fderiv
  rw [show (fun y => G (Y y, ⟪k, Y y⟫_ℝ)) = G ∘ (fun y => ((Y y, ⟪k, Y y⟫_ℝ) : Vec3 × ℝ)) from rfl, hc]
  rfl

/-- **The Hessian (5.51) at one point.** For the vector fields `G₁ = 𝐝q`, `G₂ = κ∂_sq` of the label
and phase gradient, read on the graph `Φ(y) = (Y y, k·Y y)`, the quadratic form of the derivative of
`y ↦ G₁(Φ y) + G₂(Φ y)` is the phase term `c σ²` of `G₂` (`∂_sG₂ = c • κ`, `σ = κ·v = k·D_xY v`: the
first tensor of (5.51)) plus the terms bounded by the scaled jets of order one of `G₁` (all components)
and of `G₂` (label components only): the remaining tensors of (5.51). -/
theorem leading_hess_point {G₁ G₂ : Vec3 × ℝ → Vec3} {Y : Vec3 → Vec3} (hG₁ : ContDiff ℝ ∞ G₁)
    (hG₂ : ContDiff ℝ ∞ G₂) (hY : ContDiff ℝ ∞ Y) (k x v κ : Vec3) {ℓ h A₁ A₂ : ℝ}
    (hℓ : 0 < ℓ) (hh : 0 < h)
    (hJ₁ : PhaseJetBound 1 A₁ (scaledPhaseProfile ℓ h (fun a s => G₁ (a, s))))
    (hJ₂ : PhaseJetBound 1 A₂ (scaledPhaseProfile ℓ h (fun a s => G₂ (a, s))))
    (hκ : ∀ w, ⟪k, fderiv ℝ Y x w⟫_ℝ = ⟪κ, w⟫_ℝ) {c : ℝ}
    (hs₂ : fderiv ℝ G₂ (Y x, ⟪k, Y x⟫_ℝ) ((0 : Vec3), (1 : ℝ)) = c • κ) {DY Kk : ℝ}
    (hDY : ‖fderiv ℝ Y x‖ ≤ DY) (hk : ‖k‖ ≤ Kk) :
    ⟪v, fderiv ℝ (fun y => G₁ (Y y, ⟪k, Y y⟫_ℝ) + G₂ (Y y, ⟪k, Y y⟫_ℝ)) x v⟫_ℝ ≤
      c * ⟪κ, v⟫_ℝ ^ 2 + A₁ * ‖v‖ ^ 2 * (DY / ℓ + Kk * DY / h) + A₂ * ‖v‖ ^ 2 * (DY / ℓ) := by
  have hΦc : ContDiff ℝ ∞ (fun y => ((Y y, ⟪k, Y y⟫_ℝ) : Vec3 × ℝ)) :=
    hY.prodMk (ContDiff.inner ℝ (contDiff_const (c := k)) hY)
  have hd1 : DifferentiableAt ℝ (fun y => G₁ (Y y, ⟪k, Y y⟫_ℝ)) x :=
    (hG₁.comp hΦc).differentiable (by simp) x
  have hd2 : DifferentiableAt ℝ (fun y => G₂ (Y y, ⟪k, Y y⟫_ℝ)) x :=
    (hG₂.comp hΦc).differentiable (by simp) x
  rw [show (fun y => G₁ (Y y, ⟪k, Y y⟫_ℝ) + G₂ (Y y, ⟪k, Y y⟫_ℝ)) =
      (fun y => G₁ (Y y, ⟪k, Y y⟫_ℝ)) + (fun y => G₂ (Y y, ⟪k, Y y⟫_ℝ)) from rfl,
    fderiv_add hd1 hd2, add_apply, fderiv_graphField hG₁ hY k x v, fderiv_graphField hG₂ hY k x v]
  set z : Vec3 × ℝ := (Y x, ⟪k, Y x⟫_ℝ)
  set α : Vec3 := fderiv ℝ Y x v with hα
  set σ : ℝ := ⟪k, α⟫_ℝ with hσ
  have hσκ : σ = ⟪κ, v⟫_ℝ := hκ v
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
  have hDY0 : 0 ≤ DY := (norm_nonneg _).trans hDY
  have hαn : ‖α‖ ≤ DY * ‖v‖ := (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hDY hv0)
  have hσn : ‖σ‖ ≤ Kk * (DY * ‖v‖) := by
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm k α).trans
      (mul_le_mul hk hαn (norm_nonneg _) ((norm_nonneg _).trans hk))
  have hA₁ : 0 ≤ A₁ := (norm_nonneg _).trans (hJ₁ 0 (by norm_num) 0)
  have hA₂ : 0 ≤ A₂ := (norm_nonneg _).trans (hJ₂ 0 (by norm_num) 0)
  -- the first field
  have e1 : ⟪v, fderiv ℝ G₁ z (α, σ)⟫_ℝ ≤ A₁ * ‖v‖ ^ 2 * (DY / ℓ + Kk * DY / h) := by
    refine (real_inner_le_norm _ _).trans ?_
    have hj := jet_one_le hℓ hh hG₁ le_rfl hJ₁ z (α, σ)
    have hsum : ‖(α, σ).1‖ / ℓ + ‖(α, σ).2‖ / h ≤ DY * ‖v‖ / ℓ + Kk * (DY * ‖v‖) / h :=
      add_le_add (div_le_div_of_nonneg_right hαn hℓ.le) (div_le_div_of_nonneg_right hσn hh.le)
    calc ‖v‖ * ‖fderiv ℝ G₁ z (α, σ)‖ ≤ ‖v‖ * (A₁ * (DY * ‖v‖ / ℓ + Kk * (DY * ‖v‖) / h)) :=
          mul_le_mul_of_nonneg_left (hj.trans (mul_le_mul_of_nonneg_left hsum hA₁)) hv0
      _ = A₁ * ‖v‖ ^ 2 * (DY / ℓ + Kk * DY / h) := by field_simp
  -- the second field
  have hsplit : ((α, σ) : Vec3 × ℝ) = ((α, (0 : ℝ)) : Vec3 × ℝ) + σ • ((0 : Vec3), (1 : ℝ)) := by
    ext <;> simp
  have e2 : ⟪v, fderiv ℝ G₂ z (α, σ)⟫_ℝ ≤ c * ⟪κ, v⟫_ℝ ^ 2 + A₂ * ‖v‖ ^ 2 * (DY / ℓ) := by
    rw [hsplit, map_add, map_smul, hs₂, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_comm κ v, ← hσκ]
    have hj := jet_one_le hℓ hh hG₂ le_rfl hJ₂ z (α, 0)
    have hsum : ‖((α, (0 : ℝ)) : Vec3 × ℝ).1‖ / ℓ + ‖((α, (0 : ℝ)) : Vec3 × ℝ).2‖ / h ≤
        DY * ‖v‖ / ℓ := by
      simp only [norm_zero, zero_div, add_zero]
      exact div_le_div_of_nonneg_right hαn hℓ.le
    have hb : ⟪v, fderiv ℝ G₂ z (α, 0)⟫_ℝ ≤ A₂ * ‖v‖ ^ 2 * (DY / ℓ) := by
      refine (real_inner_le_norm _ _).trans ?_
      calc ‖v‖ * ‖fderiv ℝ G₂ z (α, 0)‖ ≤ ‖v‖ * (A₂ * (DY * ‖v‖ / ℓ)) :=
            mul_le_mul_of_nonneg_left (hj.trans (mul_le_mul_of_nonneg_left hsum hA₂)) hv0
        _ = A₂ * ‖v‖ ^ 2 * (DY / ℓ) := by field_simp
    nlinarith [hb]
  rw [inner_add_right]
  linarith [e1, e2]

/-- On a phase line `q(a,s) = c P(s)` with `P' = F`, the phase derivative of the gradient field
`G₂ = κ∂_sq` is `(c F'(s)) κ` (`08_exact_wave.tex:178-184`: the first tensor `c_𝐚F_h'κ⊗κ` of (5.51)). -/
theorem phaseGrad_phase_deriv {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {k : Vec3}
    (d : ParentGeometry hT U X k) {q : HierarchyTwistedProfile T k ℝ} {t : ℝ}
    (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) {c : ℝ} {P F : ℝ → ℝ}
    (hline : ∀ r, q.val.val.val (t, a, r) = c * P r) (hP : ∀ r, HasDerivAt P (F r) r)
    (hF : Differentiable ℝ F) :
    fderiv ℝ (fun z : Vec3 × ℝ => ((S5.ops d).phaseGrad q).val.val.val (t, z.1, z.2)) (a, s)
        ((0 : Vec3), (1 : ℝ)) = (c * deriv F s) • S5.waveVector X k t a := by
  have hG : ContDiff ℝ ∞ (fun z : Vec3 × ℝ => ((S5.ops d).phaseGrad q).val.val.val (t, z.1, z.2)) :=
    HierarchySmoothProfile.contDiff_labelPhase_slice ((S5.ops d).phaseGrad q).val.val ht
  have hFd : HasFDerivAt (fun z : Vec3 × ℝ => ((S5.ops d).phaseGrad q).val.val.val (t, z.1, z.2))
      (fderiv ℝ (fun z : Vec3 × ℝ => ((S5.ops d).phaseGrad q).val.val.val (t, z.1, z.2)) (a, s))
      (a, s) := ((hG.differentiable (by simp)) _).hasFDerivAt
  have hi : HasDerivAt (fun r : ℝ => ((a, r) : Vec3 × ℝ)) ((0 : Vec3), (1 : ℝ)) s :=
    (hasDerivAt_const s a).prodMk (hasDerivAt_id s)
  have h1 := hFd.comp_hasDerivAt s hi
  have hline' : ∀ r, ((S5.ops d).phaseGrad q).val.val.val (t, a, r) =
      (c * F r) • S5.waveVector X k t a := by
    intro r
    rw [Bridge.ops_phaseGrad_eval d q ⟨ht, mem_univ _⟩]
    congr 1
    have : (fun z => q.val.val.val (t, a, z)) = fun z => c * P z := funext hline
    rw [this, deriv_const_mul _ (hP r).differentiableAt, (hP r).deriv]
  have h2 : HasDerivAt (fun r => ((S5.ops d).phaseGrad q).val.val.val (t, a, r))
      ((c * deriv F s) • S5.waveVector X k t a) s := by
    have := (((hF s).hasDerivAt).const_mul c).smul_const (S5.waveVector X k t a)
    exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall hline')
  exact h1.unique h2

/-- **`‖κ∂_sq‖_{[1],γ} ≤ C ‖κ‖_{[1]} h⁻¹ ‖q‖_{[2],γ}`** (`08_exact_wave.tex:197-204`), by (D.4) for
the product of the wave vector `κ` (phase independent) with `∂_sq` and (D.3) for `∂_s`
(both from `hD_1`). -/
theorem wNorm_phaseGradScalar_le (hD1 : Statement.lemma_D_1) {T : ℝ} {hT : 0 < T} {U : Velocity}
    {X : ℝ → Velocity} {k : Vec3} (d : ParentGeometry hT U X k)
    {t₀ ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) {γ : ℝ → ℝ}
    (hγc : ContinuousOn γ (Icc t₀ T)) (hγ : ∀ t ∈ Icc t₀ T, 0 < γ t) {BK : ℝ}
    (hKfin : FieldNormFinite ℓ h 1
      (fun (t : Icc t₀ T) (x : Vec3 × ℝ) => S5.waveVector X k t.1 x.1))
    (hKn : fieldNorm ℓ h 1
      (fun (t : Icc t₀ T) (x : Vec3 × ℝ) => S5.waveVector X k t.1 x.1) ≤ BK)
    (q : HierarchyTwistedProfile T k ℝ) :
    S5.wNorm ℓ h t₀ γ 1 ((S5.ops d).phaseGrad q) ≤
      ((hierarchyAdmissibleWords (Fin 4) 1).card * (2 : ℝ) ^ 1 * 2) * BK *
        (h⁻¹ * S5.wNorm ℓ h t₀ γ 2 q) := by
  have hA : Icc t₀ T ⊆ Icc 0 T := Icc_subset_Icc_zero ht₀
  obtain ⟨hD3, hD4, -, -⟩ := hD1 (Icc t₀ T) ℓ h hℓ hh (Bridge.restrictWeight (Icc t₀ T) γ)
    (fun t => hγ t t.2) 1
  have hqfin := Bridge.fieldNormFinite_weighted hT ℓ h 2 ht₀ htT hγc hγ q
  obtain ⟨-, hpfin, -, hp3⟩ := hD3 ℝ (Bridge.slices (Icc t₀ T) q) hqfin
  have hsmB : ‖((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Vec3 →L[ℝ] Vec3).flip)‖ ≤ 1 := by
    rw [ContinuousLinearMap.opNorm_flip]
    exact ContinuousLinearMap.opNorm_lsmul_le
  have hslice : Bridge.slices (Icc t₀ T) ((S5.ops d).phaseGrad q) =
      fun (t : Icc t₀ T) (x : Vec3 × ℝ) =>
        ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Vec3 →L[ℝ] Vec3).flip)
          (S5.waveVector X k t.1 x.1) (phasePartial (Bridge.slices (Icc t₀ T) q) t x) := by
    funext t x
    have ht : (t : ℝ) ∈ Icc 0 T := hA t.2
    change ((S5.ops d).phaseGrad q).val.val.val ((t : ℝ), x.1, x.2) = _
    rw [Bridge.ops_phaseGrad_eval d q ⟨ht, mem_univ _⟩]
    let F : Vec3 × ℝ → ℝ := fun z => q.val.val.val ((t : ℝ), z.1, z.2)
    have hF : ContDiff ℝ ∞ F := HierarchySmoothProfile.contDiff_labelPhase_slice q.val.val ht
    have hFd : HasFDerivAt F (fderiv ℝ F x) x := ((hF.differentiable (by simp)) x).hasFDerivAt
    have hi : HasDerivAt (fun r : ℝ => ((x.1, r) : Vec3 × ℝ)) ((0 : Vec3), (1 : ℝ)) x.2 :=
      (hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2)
    have hd : deriv (fun z => q.val.val.val ((t : ℝ), x.1, z)) x.2 = fderiv ℝ F x ((0 : Vec3), (1 : ℝ)) :=
      by
      have hFd' : HasFDerivAt F (fderiv ℝ F x) (x.1, x.2) := hFd
      exact (hFd'.comp_hasDerivAt x.2 hi).deriv
    rw [hd]
    rfl
  have hprod := hD4 Vec3 ℝ Vec3
    ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Vec3 →L[ℝ] Vec3).flip)
    (fun (t : Icc t₀ T) (x : Vec3 × ℝ) => S5.waveVector X k t.1 x.1)
    (phasePartial (Bridge.slices (Icc t₀ T) q)) hKfin hpfin
  rw [Bridge.wNorm_eq_weightedFieldNorm, hslice]
  have hK0 := fieldNorm_nonneg hKfin
  have hBK : 0 ≤ BK := hK0.trans hKn
  have hw0 : 0 ≤ weightedFieldNorm ℓ h (Bridge.restrictWeight (Icc t₀ T) γ) 1
      (phasePartial (Bridge.slices (Icc t₀ T) q)) := fieldNorm_nonneg hpfin
  set c0 : ℝ := (hierarchyAdmissibleWords (Fin 4) 1).card * (2 : ℝ) ^ 1 * 2 with hc0
  have hc00 : 0 ≤ c0 := by positivity
  have hcard : 0 ≤ ((hierarchyAdmissibleWords (Fin 4) 1).card : ℝ) * (2 : ℝ) ^ 1 := by positivity
  calc _ ≤ _ := hprod.2
    _ ≤ (c0 * BK) * (h⁻¹ * weightedFieldNorm ℓ h (Bridge.restrictWeight (Icc t₀ T) γ) 2
          (Bridge.slices (Icc t₀ T) q)) := by
        refine mul_le_mul ?_ hp3 hw0 (by positivity)
        calc _ ≤ ((hierarchyAdmissibleWords (Fin 4) 1).card * (2 : ℝ) ^ 1 * (2 * 1)) *
              fieldNorm ℓ h 1 (fun (t : Icc t₀ T) (x : Vec3 × ℝ) => S5.waveVector X k t.1 x.1) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hsmB (by norm_num)) hcard) hK0
          _ ≤ c0 * BK := mul_le_mul (by rw [hc0]; linarith) hKn hK0 hc00
    _ = _ := by rw [Bridge.wNorm_eq_weightedFieldNorm]

end

end TorusEuler.Paper.Lib.S5c
