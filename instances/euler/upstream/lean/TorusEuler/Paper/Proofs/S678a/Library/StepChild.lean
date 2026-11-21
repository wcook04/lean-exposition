import TorusEuler.Paper.Proofs.S678a.Library.StepBundle
import TorusEuler.Paper.Proofs.S678a.Library.LocalStep
import TorusEuler.Paper.Proofs.S5Bridge.Parent
import TorusEuler.Paper.Proofs.S5Bridge.Seed

/-! # The child of one step from the Section 5 statements (package S678a)

`exists_child_of_section5`: item 4 of the proof of Theorem 7.1
(sections/08b_induction.tex:376-461). -/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler HierarchyTwistedProfile

noncomputable section

section Child

variable {P : InductiveEulerParameters} {n : ℕ} {activationOld activation : ℝ}

local notation "Tchild" => P.slab (n + 1) activation
local notation "Tparent" => P.slab n activationOld
local notation "μ" => P.frequency n
local notation "lam" => P.frequency (n + 1)
local notation "nxt" => P.frequency (n + 2)
local notation "depth" => 6 * frequencyExponent P.exponentParameter (P.order (n + 2))

set_option maxHeartbeats 4000000 in
/-- The child of a step from the statements 5.8-5.11: for a parent stage, a wave and its expansion, there are a cutoff child, the next stage with the approximate velocity and the clauses of the induction (item 4-6 of the proof of Theorem 7.1). The (T1) facts of the truncation are taken from Proposition 5.11. -/
theorem exists_child_of_section5
    (parent : InductiveEulerStage P n activationOld)
    {ψ : Vec3 → ℝ} {a : ℕ} {Γ : ℕ → ℝ} {K58 : ℕ → ℕ → ℝ} {C11 Cc : ℝ} {K11 : ℕ → ℝ} {Ct : ℕ → ℝ}
    (h58 : Body58 a P.exponentParameter Γ K58) (h59 : Body59 a P.exponentParameter Γ)
    (h510 : Body510 a P.exponentParameter Γ) (h511 : Body511 ψ a P.exponentParameter Γ C11 K11)
    (hTail : TailBounds ψ Ct)
    (hT : 0 < Tchild) {k : Vec3} {center : ℝ → Vec3} {amp : ℝ → Vec3 → Vec3}
    (d : ParentGeometry hT parent.velocity parent.flow k) (χ : PaperWaveCutoff activation Tchild)
    (hpar : S5.Parent Tchild parent.velocity parent.flow parent.pressure (μ ^ 9) lam)
    (hl : S5.Launch Tchild parent.flow k lam activation)
    (ho : S5.Origin Tchild parent.velocity parent.flow k (μ ^ 9) lam activation center)
    (hs : S5.IsSeed parent.velocity parent.flow k activation Tchild center amp)
    {R S : HierarchyTwistedProfile Tchild k Vec3}
    {u : HierarchyProfiles (HierarchyTwistedProfile Tchild k Vec3)
      (HierarchyTwistedProfile Tchild k ℝ)}
    (hu : S5.IsExpansion d parent.pressure χ (S5.radius (μ ^ 9) a) (S5.width lam) amp depth R S u)
    -- the schedule
    (ha : 3 ≤ a) (hInitial : 2 ≤ P.frequency 0) (hSlab : Tchild ≤ Tparent)
    -- numerical hypotheses (cost table)
    (hΓ : Γ depth * ((μ ^ 9) ^ P.exponentParameter) * lam ^ (-1 / 12 : ℝ) ≤ 1)
    (hRVn : Γ depth * ((μ ^ 9) ^ P.exponentParameter) * lam ^ (2 : ℝ) *
      (lam ^ (-2 * (depth : ℝ) / 3) + χ.derivativeSize (S5.weight lam center)) ≤
        nxt ^ (-7 / 2 : ℝ))
    (hCt0 : 0 ≤ Ct depth) (hCtμ : Ct depth ≤ μ) (hC11 : C11 ≤ Cc) (hCc : 0 ≤ Cc) (hK11 : K11 depth ≤ μ)
    (hLarge : max 2 ((2 * Cc) ^ (2 : ℕ)) ≤ nxt)
    {Cparent Cstep Cmean : ℝ}
    (hJets : ∀ t ∈ Icc 0 Tchild, PhaseJetBound (depth + 1)
      (Cparent * μ ^ (5 * (depth + 1) + 1)) (parent.velocity t))
    (hCp : (3 * ((depth : ℝ) + 1)) * Cparent ≤ μ) (hCparent : 0 ≤ Cparent)
    (hCosc : K58 depth depth ≤ μ) (hCstep0 : K58 0 depth * ((μ ^ 9) ^ P.exponentParameter) ≤ Cstep)
    (hCstepΓ : Γ depth * ((μ ^ 9) ^ P.exponentParameter) ≤ Cstep)
    (hCstep32 : Cstep ≤ lam ^ (1 / 32 : ℝ))
    (hKmean : ∀ m ≤ P.order (n + 1), K58 m depth ≤ Cmean) (hMeanμ : Cmean ≤ μ) :
    ∃ (s : CutoffChild Tchild ((μ ^ frequencyExponent P.exponentParameter (P.order (n + 1))) ^ 5) ψ
        (parent.velocity + graphRead (fun t => parent.flow t 0) (S5.expansion u depth)))
      (child : InductiveEulerStage P (n + 1) activation),
      child.velocity = s.velocity ∧ child.pressure = s.pressure ∧
      (∀ t ∈ Icc 0 Tchild, ∀ x, ‖graphRead (fun t => parent.flow t 0)
        (S5.expansion u depth - (S5.ops d).average (S5.expansion u depth)) t x‖ ≤ lam⁻¹) ∧
      (∀ m ≤ P.order (n + 1), ∀ t ∈ Icc 0 Tchild,
        SpatialHolderHalf m (child.velocity t - parent.velocity t - graphRead (fun t => parent.flow t 0)
          (S5.expansion u depth - (S5.ops d).average (S5.expansion u depth)) t) ∧
        spatialHolderHalfNorm m (child.velocity t - parent.velocity t - graphRead (fun t => parent.flow t 0)
          (S5.expansion u depth - (S5.ops d).average (S5.expansion u depth)) t) ≤ lam⁻¹) ∧
      -- the clauses `approximate` and `truncation` of `Theorem71StepData`
      ApproxClause d parent.pressure S u depth ∧
      S5.IsTruncation Tchild ψ (lam ^ 5)
        (parent.velocity + graphRead (fun t => parent.flow t 0) (S5.expansion u depth))
        child.velocity child.pressure ∧
      -- the tails of the cutoff child, (B.2) at the constant `Ct depth`
      (∀ m ≤ depth, ∀ t ∈ Icc 0 Tchild,
        SpatialHolderHalf m (s.velocity t - (parent.velocity + graphRead (fun t => parent.flow t 0)
          (S5.expansion u depth)) t) ∧
        spatialHolderHalfNorm m (s.velocity t - (parent.velocity + graphRead (fun t => parent.flow t 0)
          (S5.expansion u depth)) t) ≤ Ct depth * ((μ ^ frequencyExponent P.exponentParameter
            (P.order (n + 1))) ^ 5) ^ ((m : ℤ) - depth) * spatialHolderHalfNorm depth
          ((parent.velocity + graphRead (fun t => parent.flow t 0) (S5.expansion u depth)) t)) ∧
      (∀ t ∈ Icc 0 Tchild, spatialHolderHalfNorm 2 (s.velocity t - (parent.velocity +
          graphRead (fun t => parent.flow t 0) (S5.expansion u depth)) t) ≤
        Ct depth * truncErr ((μ ^ frequencyExponent P.exponentParameter (P.order (n + 1))) ^ 5)
          (parent.velocity + graphRead (fun t => parent.flow t 0) (S5.expansion u depth)) depth t) ∧
      (∀ t ∈ Icc 0 Tchild,
        Ct depth * truncErr ((μ ^ frequencyExponent P.exponentParameter (P.order (n + 1))) ^ 5)
          (parent.velocity + graphRead (fun t => parent.flow t 0) (S5.expansion u depth)) depth t ≤
        nxt ^ (-5 : ℝ)) ∧
      -- (5.50) at the center
      (∀ t ∈ Icc activation Tchild,
        ‖fderiv ℝ ((parent.velocity + graphRead (fun t => parent.flow t 0) (S5.expansion u depth)) t) 0 -
            fderiv ℝ (parent.velocity t) 0 -
            χ.value t • InnerProductSpace.rankOne ℝ (center t) (S5.waveVector parent.flow k t 0)‖ ≤
          lam ^ (-1 / 3 : ℝ)) := by
  classical
  obtain ⟨hμ, hOrder, hDepth⟩ := physicalWave_schedule (P := P) (n := n) hInitial
  have hdep2 : 2 ≤ depth := (le_max_left _ _).trans hDepth
  have hChildEq : lam = μ ^ frequencyExponent P.exponentParameter (P.order (n + 1)) :=
    P.frequency_step n
  have hNextEq : nxt = (μ ^ frequencyExponent P.exponentParameter (P.order (n + 1))) ^
      frequencyExponent P.exponentParameter (P.order (n + 2)) := physicalWave_next_frequency
  have h8 := h58 hT d χ hpar hl ho amp hs depth hdep2 R S u hu hΓ
  have h9 := h59 hT d χ hpar hl ho amp hs depth hdep2 R S u hu hΓ
  dsimp only at h8 h9
  obtain ⟨⟨hVsm, hVprop⟩, ⟨hPsm, hPper⟩, hRVeq, h547, h548o, h548b, h548R⟩ := h8
  obtain ⟨h549, h550⟩ := h9
  have hb : 1 ≤ P.exponentParameter := P.exponentParameter_ge
  have hD2 : (2 : ℝ) ≤ μ ^ 9 := hμ.trans (le_self_pow₀ (by linarith) (by norm_num))
  have hV1 := average_firstLevel d hl hs (Bridge.radius_pos hpar a) (Bridge.radius_fits hD2 ha)
    (Bridge.width_pos hpar) (Bridge.width_le_one hpar) hu
  have havg := average_expansion d hu hV1
  set Y : Velocity := fun t => parent.flow t 0 with hY
  set W := S5.expansion u depth with hW
  set V : Velocity := parent.velocity + graphRead Y W with hVdef
  set Pres : Pressure := parent.pressure + graphRead Y (S5.expansionPressure u depth) with hPresdef
  set RV : Velocity := graphRead Y (S5.remainder (S5.ops d) u depth + (S + S5.curlCorrection d S))
    with hRVdef
  set osc : Velocity := graphRead Y (W - (S5.ops d).average W) with hoscdef
  set mean : Velocity := graphRead Y (∑ p ∈ Finset.Icc 2 depth, u.B p) with hmeandef
  have hVper : ∀ t ∈ Icc 0 Tchild, SpatiallyPeriodic (V t) := fun t ht => (hVprop t ht).1
  have hVodd : ∀ t ∈ Icc 0 Tchild, Function.Odd (V t) := fun t ht => (hVprop t ht).2.1
  have hVdiv : ∀ t ∈ Icc 0 Tchild, ∀ x, divergence (V t) x = 0 := fun t ht => (hVprop t ht).2.2
  have hSplit : ∀ t ∈ Icc 0 Tchild, V t = parent.velocity t + osc t + mean t := by
    intro t ht
    funext x
    show parent.velocity t x + graphRead Y W t x = parent.velocity t x + graphRead Y (W -
      (S5.ops d).average W) t x + graphRead Y (∑ p ∈ Finset.Icc 2 depth, u.B p) t x
    rw [← havg, graphRead_sub_apply]
    abel
  have hVholder : ∀ t ∈ Icc 0 Tchild, SpatialHolderHalf depth (V t) := by
    intro t ht
    have hUsmooth : ContDiff ℝ ∞ (parent.velocity t) :=
      contDiff_slice' parent.smooth_velocity ⟨ht.1, ht.2.trans hSlab⟩
    obtain ⟨hUreg, -⟩ := spatialHolderHalfNorm_le_of_uniformJets hUsmooth
      (mul_nonneg hCparent (pow_nonneg (by linarith) _)) (hJets t ht)
    rw [hSplit t ht]
    exact (spatialHolderHalf_add_exact (spatialHolderHalf_add_exact hUreg (h548o depth t ht).1).1
      (h548b depth t ht).1).1
  have hRVsize : ∀ t ∈ Icc 0 Tchild, spatialHolderHalfNorm 1 (RV t) ≤ nxt ^ (-7 / 2 : ℝ) :=
    fun t ht => (h548R t ht).2.trans (by push_cast; exact hRVn)
  have hApprox := physicalWaveApproximationBounds_of_5_8 parent (V := V) (RV := RV)
    (osc := osc) (mean := mean)
    (Kosc := fun m => K58 m depth) (Kmean := fun m => K58 m depth) (Kosc0 := K58 0 depth)
    hμ hSlab hJets (by push_cast; exact hCp) hCparent hSplit h548o h547 h548b hCosc hCosc hCstep0 hKmean
    hRVsize
  have hΛ0 : 0 < (μ ^ frequencyExponent P.exponentParameter (P.order (n + 1))) ^ 5 :=
    pow_pos (pow_pos (by linarith) _) _
  have hΛ1 : 1 ≤ (μ ^ frequencyExponent P.exponentParameter (P.order (n + 1))) ^ 5 :=
    one_le_pow₀ (one_le_pow₀ (by linarith))
  have h11 := h511 hT d χ hpar hl ho amp hs depth hdep2 R S u hu hΓ _ hΛ1
  dsimp only at h11
  obtain ⟨hex, h11⟩ := h11
  obtain ⟨s⟩ := exists_cutoffChild hT hVsm hVper hex fun u p h => by
    obtain ⟨h1, -⟩ := h11 u p h
    exact h1
  have hTails := hTail hΛ0 s depth hVholder
  obtain ⟨-, -, hC3, hE, h57⟩ := h11 s.velocity s.pressure (isTruncation_of_cutoffChild s)
  have hNslab : 0 ≤ slabSpatialHolderHalfNorm Tchild 1 RV :=
    Real.iSup_nonneg fun _ => holderNorm_nonneg 1 _
  have hRes57 := scheduled_bounds_of_5_11 hT s hμ hb hK11 hCc
    (G := Γ depth * ((μ ^ 9) ^ P.exponentParameter) * lam ^ (-1 / 4 : ℝ)) (pU := parent.pressure)
    (by rw [← hNextEq]; exact hRVsize)
    (fun t ht => ⟨hVholder t ht, by
      have := hApprox.velocity_size t ht
      rw [hChildEq] at this
      exact this⟩) (fun t ht t' ht' => by
        obtain ⟨e1, e2, e3⟩ := hE t ht t' ht'
        exact ⟨e1, e2, e3.trans (add_le_add_left (mul_le_mul_of_nonneg_right hC11 hNslab) _)⟩)
    (fun t ht => by
      obtain ⟨e1, e2⟩ := hC3 t ht
      exact ⟨e1, e2⟩)
    (fun t ht x v => (h57 t ht x v).trans (mul_le_mul_of_nonneg_right
      (by linarith only [mul_le_mul_of_nonneg_right hC11 hNslab])
      (sq_nonneg _)))
  obtain ⟨hRes, -, hTwoF, hP57⟩ := hRes57
  have hlam0 : 0 ≤ lam ^ (-1 / 4 : ℝ) :=
    Real.rpow_nonneg (by rw [hChildEq]; exact pow_nonneg (by linarith) _) _
  have hG : Γ depth * ((μ ^ 9) ^ P.exponentParameter) * lam ^ (-1 / 4 : ℝ) ≤
      Cstep * lam ^ (-1 / 4 : ℝ) := mul_le_mul_of_nonneg_right hCstepΓ hlam0
  have h510' : ∀ v : Velocity,
      ContDiffOn ℝ ∞ (Function.uncurry v) (Icc 0 Tchild ×ˢ (univ : Set Vec3)) →
      (∀ t ∈ Icc 0 Tchild, SpatiallyPeriodic (v t)) →
      (∀ t ∈ Icc 0 Tchild, ∀ x, divergence (v t) x = 0) →
      (∀ t ∈ Icc 0 Tchild, ∀ j ≤ 2, ∀ x, ‖iteratedFDeriv ℝ j (v t) x‖ ≤ lam ^ (-5 / 2 : ℝ)) →
      ∃ Yf : ℝ → Velocity, ChildFlow.DeformationOn (V + v) Yf Tchild (Cstep * lam ^ (1 / 4 : ℝ)) := by
    intro v hvsm hvper hvdiv hv2
    obtain ⟨⟨Yf, hYf⟩, -⟩ := h510 hT d χ hpar hl ho amp hs depth hdep2 R S u hu hΓ v hvsm hvper
      hvdiv hv2
    exact ⟨Yf, deformationOn_mono hYf (mul_le_mul_of_nonneg_right hCstepΓ
      (Real.rpow_nonneg (by rw [hChildEq]; exact pow_nonneg (by linarith) _) _))⟩
  obtain ⟨child, hv, hp, hosc, hcorr⟩ := exists_inductiveEulerChild_of_physicalCutoff' parent s
    hTails hRes (by simpa only [hNextEq] using hTwoF)
    (fun t ht x v => by
      have h := (hP57 t ht x v).trans (mul_le_mul_of_nonneg_right
        (add_le_add hG le_rfl) (sq_nonneg ‖v‖))
      simpa only [hChildEq, hNextEq] using h)
    hApprox hInitial hSlab hCc hCt0 hCtμ hMeanμ hCstep32 hLarge hVholder hSplit hVsm hVper hVdiv
    h510'
  have hErr (t : ℝ) (ht : t ∈ Icc 0 Tchild) :
      Ct depth * truncErr ((μ ^ frequencyExponent P.exponentParameter (P.order (n + 1))) ^ 5) V depth t ≤
        nxt ^ (-5 : ℝ) := by
    rw [hNextEq]
    exact truncErr_le_next (V := V) hμ hb hCtμ t (hVholder t ht)
      (by simpa only [hChildEq] using hApprox.velocity_size t ht)
  have hTwo := tailTwo_of_tails hCt0 hΛ0 s hdep2 hTails
  refine ⟨s, child, hv, hp, hosc, hcorr, ⟨⟨hVsm, hVprop⟩, ⟨hPsm, hPper⟩, hRVeq⟩, ?_, hTails, hTwo, hErr,
    fun t ht => h550 t ht⟩
  rw [hChildEq, hv, hp]
  exact isTruncation_of_cutoffChild s

end Child

end

end TorusEuler.Paper.Lib.S678a
