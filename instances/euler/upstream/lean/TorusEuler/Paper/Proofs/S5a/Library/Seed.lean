import TorusEuler.Paper.S5.Vocabulary
import TorusEuler.Paper.Proofs.S5Bridge.Parent
import TorusEuler.Paper.Proofs.S5Bridge.Operators
import TorusEuler.Paper.Proofs.S5Bridge.Seed

/-!
# S5a library: existence of the seed of §5.1

The seed `𝐚` of §5.1 is "the solution of (3.2) on `[t₀,T]` with (5.4)"
(`sections/08a_parent_step.tex:62-67`); Proposition 5.4 asserts that the profiles built from
it are well defined, which includes its existence (ledger export of row 5.4). This file
constructs it without any bound: at each label a linear ODE solution
(`linearODE_exists_Icc_of_mem`), joint smoothness of the selected family
(`contDiffOn_selected_linearTrajectory`), the value at the origin by linear uniqueness
against the central seed of (5.5), and transversality by `oscillatory_transverse_of_initial`.
It does not use the near-origin bounds (5.19) (content of Lemma 5.3) or the coefficient
bounds of Proposition 5.1.

Copy: the private `contDiffOn_seed_coefficients` (`TorusEuler/LocalizedSeedRegularity.lean:586`)
is `contDiffOn_seed_coefficients` here (same statement and proof).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5a

noncomputable section

open HierarchyTwistedProfile LocalizedAmplitude

/-- Copy of the private `contDiffOn_seed_coefficients`
(`TorusEuler/LocalizedSeedRegularity.lean:586`): the seed operator `-(Id - 2P_κ)M` and the
projection `Id - P_κ` are jointly smooth where `M`, `κ` are and `κ ≠ 0`. -/
theorem contDiffOn_seed_coefficients
    {M : ℝ × Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ × Vec3 → Vec3} {S : Set (ℝ × Vec3)}
    (hM : ContDiffOn ℝ ∞ M S) (hκ : ContDiffOn ℝ ∞ κ S) (hκ₀ : ∀ p ∈ S, κ p ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => affineWaveAmplitudeOperator (M p) (κ p)) S ∧
      ContDiffOn ℝ ∞ (fun p => oscillatoryTransverseProjection (κ p)) S := by
  let L : Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ := innerSL ℝ
  have hInner := L.contDiff.comp_contDiffOn hκ
  have hRank : ContDiffOn ℝ ∞ (fun p => InnerProductSpace.rankOne ℝ (κ p) (κ p)) S :=
    (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := Vec3) (F := Vec3)).contDiff.comp_contDiffOn
      (hInner.prodMk hκ)
  have hn : ContDiffOn ℝ ∞ (fun p => ‖κ p‖ ^ 2) S := hκ.norm_sq ℝ
  have hn₀ (p : ℝ × Vec3) (hp : p ∈ S) : ‖κ p‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr (hκ₀ p hp))
  have ht := (contDiffOn_const (c := (2 : ℝ))).div hn hn₀
  have hp := hn.inv hn₀
  exact ⟨hM.neg.add (ht.smul (hRank.clm_comp hM)), contDiffOn_const.sub (hp.smul hRank)⟩

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
  {D lam t₀ : ℝ} {center : ℝ → Vec3}

set_option maxHeartbeats 1000000 in
/-- **Existence of the seed of §5.1** (`sections/08a_parent_step.tex:62-67`): over a parent
with launch data and a central seed (5.5), the solution `𝐚` of the seed equation (3.2) on
`[t₀,T]` with the initial value (5.4) `𝐚(t₀,a) = (Id - P_{κ(t₀,a)}) 𝐚(t₀,0)` exists, is jointly
smooth, transverse to `κ`, and equals the central seed at the origin. -/
theorem exists_isSeed (d : ParentGeometry hT U X k) (hP : S5.Parent T U X pU D lam)
    (hL : S5.Launch T X k lam t₀) (hO : S5.Origin T U X k D lam t₀ center) :
    ∃ amp : ℝ → Vec3 → Vec3, S5.IsSeed U X k t₀ T center amp := by
  have hI : Icc t₀ T ⊆ Icc 0 T := Bridge.Launch.active_subset hL
  let J : Set ℝ := Icc t₀ T
  let Sl : Set (ℝ × Vec3) := J ×ˢ univ
  have hsubS : Sl ⊆ Icc 0 T ×ˢ (univ : Set Vec3) := prod_mono hI subset_rfl
  have hMs : ContDiffOn ℝ ∞ (Function.uncurry (S5.strainField U X)) Sl :=
    (Bridge.Parent.strainField_smooth hT hP).mono hsubS
  have hκs : ContDiffOn ℝ ∞ (Function.uncurry (S5.waveVector X k)) Sl :=
    (Bridge.Parent.waveVector_smooth hT hP).mono hsubS
  have hκ₀ (t : ℝ) (ht : t ∈ J) (a : Vec3) : S5.waveVector X k t a ≠ 0 :=
    Bridge.Parent.waveVector_ne_zero hT hP hL.carrier_ne_zero (hI ht) a
  obtain ⟨hA, hProj⟩ := contDiffOn_seed_coefficients (S := Sl)
    (M := fun p => S5.strainField U X p.1 p.2) (κ := fun p => S5.waveVector X k p.1 p.2)
    hMs hκs (fun p hp => hκ₀ p.1 hp.1 p.2)
  let A : ℝ → Vec3 → Vec3 →L[ℝ] Vec3 := fun t a =>
    affineWaveAmplitudeOperator (S5.strainField U X t a) (S5.waveVector X k t a)
  have hAuncurry : ContDiffOn ℝ ∞ (Function.uncurry A) Sl := hA.congr (fun p _ => rfl)
  have ht₀ : t₀ ∈ J := left_mem_Icc.mpr hL.start_lt.le
  have hAc (a : Vec3) : ContinuousOn (fun t => A t a) J :=
    Bridge.continuousOn_slice (f := A) hAuncurry.continuousOn a (fun r hr => ⟨hr, mem_univ a⟩)
  let x₀ (a : Vec3) : Vec3 :=
    oscillatoryTransverseProjection (S5.waveVector X k t₀ a) (center t₀)
  have hexists (a : Vec3) : ∃ z : ℝ → Vec3, z t₀ = x₀ a ∧
      ∀ t ∈ J, HasDerivWithinAt z (A t a (z t)) J t :=
    linearODE_exists_Icc_of_mem ht₀ (hAc a) (x₀ a)
  choose z hz₀ hz using hexists
  let amp : ℝ → Vec3 → Vec3 := fun t a => z a t
  -- smoothness of the initial value and of the selected family
  have hProj₀ : ContDiff ℝ ∞ (fun a => oscillatoryTransverseProjection (S5.waveVector X k t₀ a)) := by
    have hmem : ∀ a : Vec3, ((t₀, a) : ℝ × Vec3) ∈ Sl := fun a => mem_prod.mpr ⟨ht₀, mem_univ a⟩
    have h := hProj.comp_contDiff (f := fun a : Vec3 => ((t₀, a) : ℝ × Vec3))
      (contDiff_const.prodMk contDiff_id) hmem
    exact h
  have hInit : ContDiff ℝ ∞ (amp t₀) := by
    have : amp t₀ = fun a => x₀ a := funext hz₀
    rw [this]
    exact hProj₀.clm_apply contDiff_const
  have hSmooth : ContDiffOn ℝ ∞ (Function.uncurry amp) Sl :=
    contDiffOn_selected_linearTrajectory hL.start_lt hAuncurry hInit
      (fun a t ht => hz a t ht)
  -- the central seed solves the same equation at the origin, from the same value
  have hcenter (t : ℝ) (ht : t ∈ J) : HasDerivWithinAt center (A t 0 (center t)) J t :=
    hO.wave.amplitude t ht
  have hOrigin : EqOn (fun t => amp t 0) center J := by
    apply linearODE_unique_of_mem ordConnected_Icc ht₀ (hAc 0) (hz 0) hcenter
    rw [hz₀ 0]
    show oscillatoryTransverseProjection (S5.waveVector X k t₀ 0) (center t₀) = center t₀
    have h0 : ⟪S5.waveVector X k t₀ 0, center t₀⟫_ℝ = 0 := (hO.wave.nonzero t₀ ht₀).2.2
    rw [oscillatoryTransverseProjection_apply, h0, zero_div, zero_smul, sub_zero]
  -- transversality
  have hTrans (a : Vec3) : ∀ t ∈ J, ⟪S5.waveVector X k t a, amp t a⟫_ℝ = 0 := by
    refine oscillatory_transverse_of_initial (M := fun t => S5.strainField U X t a)
      (κ := fun t => S5.waveVector X k t a) (V := fun t => amp t a) (f := fun _ => 0)
      ordConnected_Icc ht₀ (fun t ht => hκ₀ t ht a)
      (fun t ht => (Bridge.geometry_waveVector_hasDerivWithinAt d a (hI ht)).mono hI)
      (fun t ht => by simpa only [map_zero, add_zero] using hz a t ht) ?_
    change ⟪S5.waveVector X k t₀ a, z a t₀⟫_ℝ = 0
    rw [hz₀ a]
    show ⟪S5.waveVector X k t₀ a,
      oscillatoryTransverseProjection (S5.waveVector X k t₀ a) (center t₀)⟫_ℝ = 0
    exact inner_oscillatoryTransverseProjection _ _ (hκ₀ t₀ ht₀ a)
  exact ⟨amp, ⟨fun t ht => hOrigin ht, fun a => hz₀ a, fun a t ht => hz a t ht,
    fun a t ht => hTrans a t ht, hSmooth⟩⟩

end

end TorusEuler.Paper.Lib.S5a
