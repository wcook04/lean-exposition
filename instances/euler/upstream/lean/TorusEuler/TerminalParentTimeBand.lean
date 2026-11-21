import TorusEuler.TerminalTimeJet
import TorusEuler.InductiveStageConstruction
import TorusEuler.TruncatedChildStage

/-! Fourier support and Bernstein estimates for the Eulerian time jets of a stage. -/

open Set UnitAddTorus
open scoped ContDiff

namespace TorusEuler

local notation "Labels" => UnitAddTorus (Fin 3)

private theorem terminal_contDiff_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set Vec3)))
    {t : ℝ} (ht : t ∈ Icc a b) : ContDiff ℝ ∞ (f t) :=
  contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

/-- Each time jet retains the initial closed-slab Fourier band, at both endpoints
as well as at interior times. -/
theorem exists_slabTimeJet_torusFourierBand {a b R : ℝ} {f : Velocity} (hab : a < b)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc a b, SpatiallyPeriodic (f t))
    (g : ℝ → C(Labels, Vec3))
    (hg : ∀ t ∈ Icc a b, (∀ x, g t (toUnitTorus x) = f t x) ∧ RealTorusFourierBand R (g t))
    (q : ℕ) :
    ∃ gq : ℝ → C(Labels, Vec3),
      ∀ t ∈ Icc a b, (∀ x, gq t (toUnitTorus x) = slabTimeJet a b q f t x) ∧
        RealTorusFourierBand R (gq t) := by
  induction q with
  | zero => exact ⟨g, by simpa only [slabTimeJet, iteratedDerivWithin_zero] using hg⟩
  | succ q ih =>
    classical
    obtain ⟨gq, hgq⟩ := ih
    have hsl (t : ℝ) (ht : t ∈ Icc a b) :=
      (slabTimeJet_periodic hper (q + 1) ht).exists_continuousTorusFunction
        (slabTimeJet_slice_smooth hab hf (q + 1) ht).continuous
    let gq₁ (t : ℝ) : C(Labels, Vec3) := if ht : t ∈ Icc a b then (hsl t ht).choose else 0
    have hRep (t : ℝ) (ht : t ∈ Icc a b) (x : Vec3) :
        gq₁ t (toUnitTorus x) = slabTimeJet a b (q + 1) f t x := by
      simp only [gq₁, dite_eq_left ht]
      exact (hsl t ht).choose_spec x
    refine ⟨gq₁, fun t ht => ⟨hRep t ht, ?_⟩⟩
    intro k hk
    have hq : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => gq z.1 (toUnitTorus z.2))
        (Icc a b ×ˢ (univ : Set Vec3)) :=
      (slabTimeJet_smooth hab hf q).congr (fun z hz => (hgq z.1 hz.1).1 z.2)
    apply mFourierCoeff_timeDerivative_eq_zero_outside_band hab gq hq
      (fun r hr => (hgq r hr).2) ht (gq₁ t) _ k hk
    intro x
    rw [hRep t ht x]
    exact (hasDerivWithinAt_slabTimeJet hab hf q ht x).congr_of_mem
      (fun r hr => (hgq r hr).1 x) ht

namespace InductiveEulerStage

variable {P : InductiveEulerParameters} {n : ℕ} {activation : ℝ}

local notation "S" => P.slab n activation
local notation "μ" => P.frequency n

/-- Higher time derivatives of the actual velocity are supported in its
original stage band. -/
theorem exists_velocity_slabTimeJet_torusFourierBand (s : InductiveEulerStage P n activation)
    (hS : 0 < S) (q : ℕ) :
    ∃ g : ℝ → C(Labels, Vec3), ∀ t ∈ Icc 0 S,
      (∀ x, g t (toUnitTorus x) = slabTimeJet 0 S q s.velocity t x) ∧
        RealTorusFourierBand (2 * μ ^ 5) (g t) :=
  exists_slabTimeJet_torusFourierBand (f := s.velocity) hS s.smooth_velocity (fun t _ => s.periodic_velocity t)
    s.torusVelocity (fun t ht => ⟨fun _ => rfl, s.velocity_band t ht⟩) q

/-- Higher time derivatives of the actual residual retain the doubled stage
band from the projected momentum equation. -/
theorem exists_residual_slabTimeJet_torusFourierBand (s : InductiveEulerStage P n activation)
    (hS : 0 < S) (hμ : 0 ≤ μ) (q : ℕ) :
    ∃ g : ℝ → C(Labels, Vec3), ∀ t ∈ Icc 0 S,
      (∀ x, g t (toUnitTorus x) = slabTimeJet 0 S q s.residual t x) ∧
        RealTorusFourierBand (4 * μ ^ 5) (g t) := by
  classical
  have hSmooth : ContDiffOn ℝ ∞ (Function.uncurry s.residual) (Icc 0 S ×ˢ (univ : Set Vec3)) :=
    contDiffOn_closedSlab_momentumResidual (u := s.velocity) hS s.smooth_velocity s.smooth_pressure
  have hPeriodic (t : ℝ) (ht : t ∈ Icc 0 S) : SpatiallyPeriodic (s.residual t) :=
    spatiallyPeriodic_closedSlab_momentumResidual ht
      (terminal_contDiff_slice (f := s.velocity) s.smooth_velocity ht)
      (terminal_contDiff_slice s.smooth_pressure ht) (fun r _ => s.periodic_velocity r)
      (s.periodic_pressure t ht)
  have hResidual (t : ℝ) (ht : t ∈ Icc 0 S) : ∃ R : C(Labels, Vec3),
      (∀ x, R (toUnitTorus x) = s.residual t x) ∧ RealTorusFourierBand (4 * μ ^ 5) R := by
    obtain ⟨R, _, hRep, hBand, _, _⟩ := exists_closedSlab_momentumResidual_projectedData
      hS (pow_nonneg hμ 5) ht s.torusVelocity s.pressure s.smooth_velocity s.smooth_pressure
      (s.periodic_pressure t ht) s.velocity_band s.divergence_free (s.projected_eq t ht)
    exact ⟨R, hRep, hBand⟩
  let g (t : ℝ) : C(Labels, Vec3) := if ht : t ∈ Icc 0 S then (hResidual t ht).choose else 0
  refine exists_slabTimeJet_torusFourierBand hS hSmooth hPeriodic g (fun t ht => ?_) q
  simp only [g, dite_eq_left ht]
  exact (hResidual t ht).choose_spec

/-- The same spatial Bernstein constants work for every time order and both
actual stage fields. Each spatial derivative costs exactly the stage cutoff
scale `μ ^ 5`. -/
theorem exists_slabTimeJet_bernsteinBounds :
    ∃ K : ℕ → ℝ, (∀ m, 0 ≤ K m) ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {activation : ℝ}
        (s : InductiveEulerStage P n activation), 0 < P.slab n activation → 0 < P.frequency n →
        ∀ (q : ℕ) (A B : ℝ), 0 ≤ A → 0 ≤ B →
        let stageEnd := P.slab n activation
        let D := P.frequency n ^ 5
        ((∀ t ∈ Icc 0 stageEnd, ∀ x, ‖slabTimeJet 0 stageEnd q s.velocity t x‖ ≤ A) →
          ∀ m, ∀ t ∈ Icc 0 stageEnd, ∀ x,
            ‖iteratedFDeriv ℝ m (slabTimeJet 0 stageEnd q s.velocity t) x‖ ≤ K m * A * D ^ m) ∧
        ((∀ t ∈ Icc 0 stageEnd, ∀ x, ‖slabTimeJet 0 stageEnd q s.residual t x‖ ≤ B) →
          ∀ m, ∀ t ∈ Icc 0 stageEnd, ∀ x,
            ‖iteratedFDeriv ℝ m (slabTimeJet 0 stageEnd q s.residual t) x‖ ≤ K m * B * D ^ m) := by
  obtain ⟨K, hK, hBernstein⟩ := exists_bandBernsteinJetBounds
  refine ⟨K, hK, ?_⟩
  intro P n activation s hS hμ q A B hA hB
  let freq := P.frequency n
  have hD : 0 < freq ^ 5 := pow_pos hμ 5
  have hLift (f : Vec3 → Vec3) (g : C(Labels, Vec3)) {C : ℝ}
      (hC : 0 ≤ C) (hEq : ∀ x, g (toUnitTorus x) = f x)
      (hBand : RealTorusFourierBand (4 * freq ^ 5) g) (hSup : ∀ x, ‖f x‖ ≤ C) :
      ∀ m x, ‖iteratedFDeriv ℝ m f x‖ ≤ K m * C * (freq ^ 5) ^ m := by
    have hg : ‖g‖ ≤ C := (ContinuousMap.norm_le g hC).mpr fun z => by
      obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
      rw [hEq x]
      exact hSup x
    simpa only [funext hEq] using (hBernstein g hD hC hg hBand).2
  obtain ⟨U, hU⟩ := s.exists_velocity_slabTimeJet_torusFourierBand hS q
  obtain ⟨R, hR⟩ := s.exists_residual_slabTimeJet_torusFourierBand hS hμ.le q
  refine ⟨fun hV m t ht x => ?_, fun hW m t ht x => ?_⟩
  · have hBand : RealTorusFourierBand (4 * freq ^ 5) (U t) := fun k hk =>
      (hU t ht).2 k ((show 2 * freq ^ 5 ≤ 4 * freq ^ 5 by linarith only [hD]).trans_lt hk)
    exact hLift _ _ hA (hU t ht).1 hBand (hV t ht) m x
  · exact hLift _ _ hB (hR t ht).1 (hR t ht).2 (hW t ht) m x

end InductiveEulerStage

end TorusEuler
