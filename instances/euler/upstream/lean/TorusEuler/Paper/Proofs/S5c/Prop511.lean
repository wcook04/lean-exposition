import TorusEuler.Paper.S5.Statements
import TorusEuler.Paper.SBD.Statements
import TorusEuler.Paper.Proofs.S5Bridge.Children
import TorusEuler.Paper.Proofs.S5Bridge.Norms
import TorusEuler.Paper.Proofs.S5c.Library.CutoffBounds

/-!
# Proof of Proposition 5.11 (package S5c)

Conditional proof `Paper.Proof.proposition_5_11_of` of the frequency truncation
(`cc:uf:step:thm:step`, `sections/08_exact_wave.tex:379-449`) from Lemma 5.8, Lemma 5.9,
Lemma B.1 and the product inequality (5.59).

**Ledger.** The TeX proof of Proposition 5.11 displays (5.59) at
`08_exact_wave.tex:424-428` and uses it at `:428-431` for the three quadratic tensors of
(5.58); by ledger decision D3, (5.59) is generic glue (`spatialHolderHalf_bilinear`) and 5.11 lists
`eq_5_59` in its `text_cites`. The proof takes (5.59) through the hypothesis `hText_eq_5_59`,
after the cites 5.8, 5.9, B.1.
-/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper

noncomputable section

namespace Lib.S5c

/-- Copy of the private `hessianSub` (`PaperPhysicalCutoff.lean:30`): the Hessian of a
difference of `C²` pressures. -/
theorem hessianSub {p q : Vec3 → ℝ} (hp : ContDiff ℝ 2 p) (hq : ContDiff ℝ 2 q) (x : Vec3) :
    fderiv ℝ (gradient (p - q)) x = fderiv ℝ (gradient p) x - fderiv ℝ (gradient q) x := by
  have hH := fderiv_gradient_add_three_pressures hq (hp.sub hq)
    (contDiff_const : ContDiff ℝ 2 (0 : Vec3 → ℝ)) x
  change fderiv ℝ (gradient (q + (p - q) + (0 : Vec3 → ℝ))) x =
    fderiv ℝ (gradient q) x + fderiv ℝ (gradient (p - q)) x +
      fderiv ℝ (gradient (0 : Vec3 → ℝ)) x at hH
  have hsum : q + (p - q) + (0 : Vec3 → ℝ) = p := by abel
  rw [hsum] at hH
  rw [show gradient (0 : Vec3 → ℝ) = 0 from gradient_fun_const' (0 : ℝ),
    fderiv_zero, Pi.zero_apply, add_zero] at hH
  rw [hH]
  abel

/-- The second spatial derivative of a smooth periodic pressure is in `C^{0,1/2}`. -/
theorem spatialHolderHalf_hessian {q : Vec3 → ℝ} (hq : ContDiff ℝ ∞ q)
    (hper : SpatiallyPeriodic q) : SpatialHolderHalf 0 (fderiv ℝ (gradient q)) := by
  have hGrad : ContDiff ℝ ∞ (gradient q) :=
    (InnerProductSpace.toDual ℝ Vec3).symm.contDiff.comp (hq.fderiv_right (m := ∞) (by simp))
  exact spatialHolderHalf_of_contDiff_periodic (hGrad.fderiv_right (m := ∞) (by simp))
    ((hper.gradient (hq.differentiable (by simp))).fderiv (hGrad.differentiable (by simp))) 0

end Lib.S5c

open Lib.S5c

/-- Proof of **Proposition 5.11** (`cc:uf:step:thm:step`), following
`sections/08_exact_wave.tex:402-449`, for every `u`, `p` with `S5.IsTruncation` (the
truncation `u = S_Λ V` of (5.55) and its zero-mean Poisson pressure).

* *The approximate solution.* `h5_8` (Lemma 5.8) gives that `V` is smooth, periodic, odd
  and divergence free, that `Π` is smooth and periodic, and the equation (5.46)
  `V_t + V·∇V + ∇Π = R_V` on `[0,T]`; (5.46) is the equation to which `S_Λ` and `ℙ` are
  applied (`:407-410`) and whose divergence gives `ΔΠ` (`:437-440`); it also makes `R_V`
  smooth and periodic.
* *The cutoff.* `hB_1` (Lemma B.1, for the symbol `ψ` and the frequency `Λ`) gives the
  parity, divergence and band properties of `S_Λ` ("By Lemma B.1, `u` and `v_Λ` are odd and
  divergence free and `u` is supported on frequencies at most `2Λ`", `:403-405`), its
  commutation with the time and space derivatives (`:407-410`, `:434-436`: `S_Λ` commutes
  with derivatives), and the tail bound (B.2) at the order `P` for the real velocity and
  the real tensor cutoffs (`:420-423`, and `S_Λ` bounded on `C^{m,1/2}`). They enter the
  library copies `Lib.S5c.nonempty_truncatedChildStage` (existence of the child stage) and
  `Lib.S5c.exists_cutoffBounds` (the bounds (5.56)).
* *The product inequality.* `hText_eq_5_59` (the display (5.59)) bounds the three
  quadratic tensors of (5.58) in `C^{2,1/2}` (`:424-431`), inside
  `Lib.S5c.exists_cutoffBounds`.
* *The pressure.* The zero-mean pressure `p` is identified with the pressure of the child
  stage by the uniqueness of zero-mean periodic Poisson solutions
  (`periodicPoissonPressure_unique`, content of this row). Then (5.56) gives
  `‖D²(p-Π)‖_{C^{0,1/2}} ≤ C‖R_V‖ + C_{2,P}ε_Λ`, and `h5_9` (Lemma 5.9, (5.49)
  `D²𝖯^♮ ≤ C_step λ^{-1/4} Id`) with `p - p_U = (p - Π) + 𝖯^♮` gives (5.57) (`:446-448`).

Constants: `a₀`, `b₀`, `Γ₀` are the maxima of those of 5.8 and 5.9; `C` and `K P` are
twice the cutoff constants (the sum in (5.56) is bounded at two times). -/
theorem Proof.proposition_5_11_of (h5_8 : Statement.lemma_5_8) (h5_9 : Statement.lemma_5_9)
    (hB_1 : Statement.lemma_B_1) (hText_eq_5_59 : Statement.Text.eq_5_59) :
    Statement.proposition_5_11 := by
  intro ψ hψ
  -- Lemma B.1 for the symbol `ψ`
  obtain ⟨_Cop, _Cb, Ct, _hCop, _hCb, hCt, hB⟩ := hB_1 ψ (Bridge.cutoffSymbol_appendixB hψ)
  -- the constants of (5.59)
  choose Cm hCm using hText_eq_5_59
  have hprod : Lib.S5c.ProductBound Cm := hCm
  -- the cutoff constants
  obtain ⟨Cc, hCc, hBounds⟩ := Lib.S5c.exists_cutoffBounds (ψ := ψ) hCt hprod
  let Kc : ℕ → ℝ := fun P => if h : 2 ≤ P then (hBounds P h).choose else 0
  obtain ⟨a₈, h8⟩ := h5_8
  obtain ⟨a₉, h9⟩ := h5_9
  refine ⟨max a₈ a₉, fun a ha => ?_⟩
  obtain ⟨b₈, Γ₈, _K₈, h8a⟩ := h8 a (le_of_max_le_left ha)
  obtain ⟨b₉, Γ₉, h9a⟩ := h9 a (le_of_max_le_right ha)
  refine ⟨max b₈ b₉, fun P => max (Γ₈ P) (Γ₉ P), 2 * Cc, fun P => 2 * Kc P, ?_⟩
  intro b hb Γ hΓ T hT U X pU k D lam t₀ center d χ hP hL hO amp hamp P hP2 R S w hw hsmall
    Λ hΛ
  have hΛ₀ : 0 < Λ := zero_lt_one.trans_le hΛ
  -- Lemma 5.8: the approximate solution `V`, `Π` and (5.46)
  obtain ⟨⟨hVs, hVt⟩, ⟨hPs, hPper⟩, hMom, -⟩ :=
    h8a b (le_of_max_le_left hb) Γ (fun P => (le_max_left _ _).trans (hΓ P)) hT d χ hP hL hO
      amp hamp P hP2 R S w hw hsmall
  -- Lemma 5.9: (5.49)
  obtain ⟨hHess, -⟩ :=
    h9a b (le_of_max_le_right hb) Γ (fun P => (le_max_right _ _).trans (hΓ P)) hT d χ hP hL hO
      amp hamp P hP2 R S w hw hsmall
  intro Y V Pres RV ε e
  have hVper (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (V t) := (hVt t ht).1
  have hVodd (t : ℝ) (ht : t ∈ Icc 0 T) : Function.Odd (V t) := (hVt t ht).2.1
  have hVdiv (t : ℝ) (ht : t ∈ Icc 0 T) : ∀ x, divergence (V t) x = 0 := (hVt t ht).2.2
  -- `R_V` is smooth and periodic, by (5.46)
  have hRV : ContDiffOn ℝ ∞ (Function.uncurry RV) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    (contDiffOn_closedSlab_momentumResidual hT hVs hPs).congr fun z hz =>
      (hMom z.1 hz.1 z.2).symm
  have hRVper (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (RV t) := by
    have h := spatiallyPeriodic_closedSlab_momentumResidual ht (Lib.S5c.contDiff_slice hVs ht)
      (Lib.S5c.contDiff_slice hPs ht) hVper (hPper t ht)
    intro n x
    exact (hMom t ht (x + latticeVector n)).symm.trans ((h n x).trans (hMom t ht x))
  -- `Π` as a family of smooth periodic potentials
  let aP : ℝ → EndpointSmoothPotential := fun t =>
    if ht : t ∈ Icc 0 T then ⟨Pres t, Lib.S5c.contDiff_slice hPs ht, hPper t ht⟩
    else ⟨0, contDiff_const, fun _ _ => rfl⟩
  have haP (t : ℝ) (ht : t ∈ Icc 0 T) : (aP t).lift = Pres t := by
    simp only [aP]
    split_ifs
    rfl
  have hMom' : ∀ t ∈ Icc 0 T, ∀ x, derivWithin (fun r => V r x) (Icc 0 T) t +
      fderiv ℝ (V t) x (V t x) + gradient (aP t).lift x = RV t x := by
    intro t ht x
    rw [haP t ht]
    exact hMom t ht x
  -- Lemma B.1 at the frequency `Λ`
  obtain ⟨hCx, hRe, -⟩ := hB Λ hΛ₀
  obtain ⟨-, hspace, htime, hpar, hdivc, hband, -, -, hvt⟩ := hRe
  have htc : Lib.S5c.CutTailComplex (Fin 3 → ComplexEuclideanVec3) ψ Λ Ct :=
    (hCx (Fin 3 → ComplexEuclideanVec3)).2.2.2.2.2.2.2
  -- the child stage and its bounds
  obtain ⟨s⟩ := Lib.S5c.nonempty_truncatedChildStage hpar hdivc hband htime hspace hT aP hVs hRV hVper
    hRVper hVodd hVdiv hMom'
  have hKspec := (hBounds P hP2).choose_spec
  have hKc : Kc P = (hBounds P hP2).choose := by simp [Kc, hP2]
  have hK : 0 ≤ Kc P := hKc ▸ hKspec.1
  have hb : s.CutoffBounds aP P Cc (Kc P) :=
    hKc ▸ hKspec.2 hT hΛ hvt htc s aP hVs hRV (fun t ht => hVdiv t ht) hMom'
  -- the slab norms of `V` and `R_V`
  let M := slabSpatialHolderHalfNorm T P V
  let Rn := slabSpatialHolderHalfNorm T 1 RV
  obtain ⟨MV, hMV⟩ := exists_spatialHolderHalfNorm_bound_of_contDiffOn_periodic hT hVs hVper P
  obtain ⟨MR, hMR⟩ := exists_spatialHolderHalfNorm_bound_of_contDiffOn_periodic hT hRV hRVper 1
  have hVpoint (t : ℝ) (ht : t ∈ Icc 0 T) : spatialHolderHalfNorm P (V t) ≤ M :=
    le_ciSup ⟨MV, forall_mem_range.mpr fun r : Icc (0 : ℝ) T => (hMV r r.property).2⟩
      (⟨t, ht⟩ : Icc (0 : ℝ) T)
  have hRpoint (t : ℝ) (ht : t ∈ Icc 0 T) : spatialHolderHalfNorm 1 (RV t) ≤ Rn :=
    le_ciSup ⟨MR, forall_mem_range.mpr fun r : Icc (0 : ℝ) T => (hMR r r.property).2⟩
      (⟨t, ht⟩ : Icc (0 : ℝ) T)
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hRnonneg : 0 ≤ Rn :=
    (Lib.S5c.spatialHolderHalfNorm_nonneg' (hMR 0 h0T).1).trans (hRpoint 0 h0T)
  have hεnonneg : 0 ≤ ε := by
    have hΛ0 : 0 ≤ Λ := hΛ₀.le
    exact mul_nonneg (zpow_nonneg hΛ0 _) (sq_nonneg _)
  have hεpoint (t : ℝ) (ht : t ∈ Icc 0 T) : s.truncationError P t ≤ ε := by
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ _) (zpow_nonneg hΛ₀.le _)
    · linarith only [Lib.S5c.spatialHolderHalfNorm_nonneg' (hMV t ht).1]
    · exact add_le_add le_rfl (hVpoint t ht)
  have hBound (t : ℝ) (ht : t ∈ Icc 0 T) :
      Cc * spatialHolderHalfNorm 1 (RV t) + Kc P * s.truncationError P t ≤ Cc * Rn + Kc P * ε :=
    add_le_add (mul_le_mul_of_nonneg_left (hRpoint t ht) hCc)
      (mul_le_mul_of_nonneg_left (hεpoint t ht) hK)
  have he : e = 2 * (Cc * Rn + Kc P * ε) := by
    change 2 * Cc * Rn + 2 * Kc P * ε = _
    ring
  have hhalf : Cc * Rn + Kc P * ε ≤ e := by
    rw [he]
    nlinarith only [mul_nonneg hCc hRnonneg, mul_nonneg hK hεnonneg]
  refine ⟨Bridge.exists_isTruncation_of_stage s, ?_⟩
  intro u p hu Ru
  -- identification of the truncation with the child stage
  have hvel : ∀ t ∈ Icc 0 T, u t = s.velocity t := Bridge.IsTruncation.velocity_eq hu s
  have hpres : ∀ t ∈ Icc 0 T, p t = s.pressure t :=
    Bridge.IsTruncation.pressure_eq_stage hu s fun q q' hq hq' hqp hqp' hqm hqm' hEq =>
      periodicPoissonPressure_unique hq hq' hqp hqp' hqm hqm' hEq
  have hRu : ∀ t ∈ Icc 0 T, Ru t = s.residual t := by
    intro t ht
    funext x
    change materialAcceleration (Icc 0 T) u t x + gradient (p t) x =
      materialAcceleration (Icc 0 T) s.velocity t x + gradient (s.pressure t) x
    simp only [materialAcceleration, hvel t ht, hpres t ht]
    rw [derivWithin_congr (fun r hr => congrFun (hvel r hr) x) (congrFun (hvel t ht) x)]
  have hpdiff (t : ℝ) (ht : t ∈ Icc 0 T) :
      (fun x => s.pressure t x - (aP t).lift x) = p t - Pres t := by
    funext x
    rw [haP t ht, hpres t ht]
    rfl
  refine ⟨⟨?_, fun t ht => ⟨?_, ?_, ?_⟩⟩, fun t ht => ⟨?_, ?_, ?_⟩, fun t ht => ⟨?_, ?_⟩,
    fun t ht t' ht' => ⟨?_, ?_, ?_⟩, ?_⟩
  -- `u` smooth, odd, divergence free, frequencies at most `2Λ`
  · exact s.smooth_velocity.congr fun z hz => congrFun (hvel z.1 hz.1) z.2
  · rw [hvel t ht]; exact s.odd_velocity t ht
  · rw [hvel t ht]; exact s.divergence_free t ht
  · exact ⟨s.torusVelocity t, fun x => (congrFun (hvel t ht) x).symm, s.velocity_band t ht⟩
  -- `R_u` odd, divergence free, frequencies at most `4Λ`
  · rw [hRu t ht]; exact s.odd_residual hT hΛ₀.le ht
  · rw [hRu t ht]; exact s.divergence_free_residual hT ht
  · obtain ⟨r, _, hr, hband4, _, _⟩ := s.residual_projectedData hT hΛ₀.le ht
    exact ⟨r, fun x => (hr x).trans (congrFun (hRu t ht) x).symm, hband4⟩
  -- (5.56), the tail
  · rw [hvel t ht]; exact (hb.all_tails 2 hP2 t ht).1
  · rw [hvel t ht]
    refine (hb.tail_two t ht).trans ((mul_le_mul_of_nonneg_left (hεpoint t ht) hK).trans ?_)
    nlinarith only [mul_nonneg hK hεnonneg]
  -- (5.56), the residual and the pressure
  · rw [hRu t ht]; exact (hb.residual t ht).1
  · have hps : ContDiff ℝ ∞ (p t') := hu.pressure_smooth t' ht'
    exact Lib.S5c.spatialHolderHalf_hessian (hps.sub (Lib.S5c.contDiff_slice hPs ht'))
      (fun n x => by
        change p t' (x + latticeVector n) - Pres t' (x + latticeVector n) = p t' x - Pres t' x
        rw [hu.pressure_periodic t' ht' n x]
        exact congrArg (p t' x - ·) (hPper t' ht' n x))
  · rw [hRu t ht, ← hpdiff t' ht']
    have h1 := ((hb.residual t ht).2).trans (hBound t ht)
    have h2 := (hb.pressure t' ht').trans (hBound t' ht')
    rw [he]
    linarith
  -- (5.57), from (5.56) and (5.49)
  · intro t ht x v
    have hp' : ContDiff ℝ ∞ (s.pressure t) := Lib.S5c.contDiff_slice s.smooth_pressure ht
    have hDiff := TruncatedChildStage.pressureHessian_le_of_cutoff hp' (aP t).smooth
      (s.periodic_pressure t ht) (aP t).periodic ((hb.pressure t ht).trans (hBound t ht)) x v
    have hpU : ContDiff ℝ 2 (pU t) := (Lib.S5c.contDiff_slice hP.pressure_smooth ht).of_le (by simp)
    have hPres2 : ContDiff ℝ 2 (Pres t) := (Lib.S5c.contDiff_slice hPs ht).of_le (by simp)
    have hNat : Pres t - pU t = HierarchyTwistedProfile.graphRead Y (S5.expansionPressure w P) t := by
      funext y
      change pU t y + HierarchyTwistedProfile.graphRead Y (S5.expansionPressure w P) t y - pU t y = _
      ring
    have hUpper := hHess t ht x v
    rw [← hNat, Lib.S5c.hessianSub hPres2 hpU, _root_.sub_apply, inner_sub_right] at hUpper
    rw [haP t ht] at hDiff
    rw [hpres t ht, Lib.S5c.hessianSub (hp'.of_le (by simp)) hpU, _root_.sub_apply, inner_sub_right]
    have hv2 : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
    nlinarith only [hDiff, hUpper, mul_le_mul_of_nonneg_right hhalf hv2]

end

end TorusEuler.Paper
