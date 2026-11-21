import TorusEuler.Paper.Proofs.S2b.Library.Glue

/-! # Restriction of the setting of Subsection 2.2.1 to the slab

The statements of Section 2 take the wave equations on a compact window `I` containing
the slab `t₀ ≤ t ≤ t₀ + T/r`. The proof of the bound on `Φ` in Lemma 2.6 needs amplitude
vectors with arbitrary data in the transverse plane, which exist on the slab (a closed
interval) but not necessarily on `I`. This file restricts the setting to the slab: the
data of the preceding wave are unchanged, so `σ, ν, η, r, S, ε`, the frame and the clock
are the same, and the error `δ` of (2.6), a supremum over the smaller set, does not
increase. Glue only (namespace `TorusEuler.Paper.Lib.S2b`).
-/

open Set
open scoped InnerProductSpace

namespace TorusEuler.Paper.Lib.S2b

open MovingWaveVector

noncomputable section

variable {I : Set ℝ} {t₀ : ℝ}

/-- The clock maps `[0, T]` into the slab. -/
theorem clock_mem_slab (w : PhysicalAmplification I t₀) {T τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    w.clock τ ∈ w.activeSlab T :=
  ⟨by simpa only [PhysicalAmplification.clock_zero] using w.strictMono_clock.monotone hτ.1,
    w.strictMono_clock.monotone hτ.2⟩

/-- Every time of the slab is on the clock of `[0, T]`. -/
theorem elapsed_mem_Icc (w : PhysicalAmplification I t₀) {T t : ℝ}
    (ht : t ∈ w.activeSlab T) : w.elapsed t ∈ Icc 0 T := by
  have ha := w.strictMono_elapsed.monotone ht.1
  have hb := w.strictMono_elapsed.monotone ht.2
  have h0 : w.elapsed t₀ = 0 := by
    simpa only [PhysicalAmplification.clock_zero] using w.elapsed_clock 0
  rw [h0] at ha
  rw [PhysicalAmplification.elapsed_clock] at hb
  exact ⟨ha, hb⟩

/-- The slab lies in the window. -/
theorem slab_subset (w : PhysicalAmplification I t₀) {T : ℝ}
    (hclock : MapsTo w.clock (Icc 0 T) I) : w.activeSlab T ⊆ I := by
  intro t ht
  rw [← w.clock_elapsed t]
  exact hclock (elapsed_mem_Icc w ht)

/-- The setting of Subsection 2.2.1 restricted to the slab `[t₀, t₀ + T/r]`. -/
def restrictSlab (w : PhysicalAmplification I t₀) {T : ℝ} (hT : 0 ≤ T)
    (hclock : MapsTo w.clock (Icc 0 T) I) : PhysicalAmplification (w.activeSlab T) t₀ where
  kp := w.kp
  ap := w.ap
  B := w.B
  E := w.E
  compact := isCompact_Icc
  activation := by
    simpa only [PhysicalAmplification.clock_zero] using clock_mem_slab w ⟨le_rfl, hT⟩
  older_continuous := w.older_continuous.mono (slab_subset w hclock)
  error_continuous := w.error_continuous.mono (slab_subset w hclock)
  trace_zero := fun t ht => w.trace_zero t (slab_subset w hclock ht)
  preceding_data := fun t ht => w.preceding_data t (slab_subset w hclock ht)
  preceding_vector := fun t ht =>
    (w.preceding_vector t (slab_subset w hclock ht)).mono (slab_subset w hclock)
  preceding_amplitude := fun t ht =>
    (w.preceding_amplitude t (slab_subset w hclock ht)).mono (slab_subset w hclock)
  first_coupling_positive := w.first_coupling_positive
  third_coupling_positive := w.third_coupling_positive

/-- A supremum of the error (2.6) over a nonempty part of a compact window is at most the
supremum over the window. -/
theorem amplificationPhysicalError_mono {J : Set ℝ} {e : ℝ → Fin 3 → Space}
    {B E : ℝ → Space →L[ℝ] Space} {ν η r : ℝ} (hJI : J ⊆ I) (hJ : J.Nonempty)
    (hI : IsCompact I) (hec : ∀ i, ContinuousOn (fun t => e t i) I)
    (hBc : ContinuousOn B I) (hEc : ContinuousOn E I) (hν : 0 < ν) (hr : 0 < r) :
    amplificationPhysicalError J e B E ν η r ≤ amplificationPhysicalError I e B E ν η r := by
  have hent (i j : Fin 3) : ContinuousOn (fun t => entry (e t) (B t) i j) I :=
    (hec i).inner (hBc.clm_apply (hec j))
  have key {f : ℝ → ℝ} (hf : ContinuousOn f I) : sSup (f '' J) ≤ sSup (f '' I) :=
    csSup_le_csSup (hI.image_of_continuousOn hf).bddAbove (hJ.image f) (image_mono hJI)
  have h1 := key (f := fun t => |entry (e t) (B t) 0 1 / ν - 1|)
    (((hent 0 1).div_const ν).sub continuousOn_const).abs
  have h2 := key (f := fun t => |entry (e t) (B t) 2 1 / η - 1|)
    (((hent 2 1).div_const η).sub continuousOn_const).abs
  have h3 := key (f := fun t => ‖B t‖) hBc.norm
  have h4 := key (f := fun t => ‖E t‖) hEc.norm
  unfold amplificationPhysicalError
  exact add_le_add (add_le_add (add_le_add h1 h2) (div_le_div_of_nonneg_right h3 hr.le))
    (div_le_div_of_nonneg_right h4 hν.le)

/-- The error `δ` of the restricted setting is at most `δ`. -/
theorem errorSize_restrictSlab_le (w : PhysicalAmplification I t₀) {T : ℝ} (hT : 0 ≤ T)
    (hclock : MapsTo w.clock (Icc 0 T) I) :
    (restrictSlab w hT hclock).errorSize ≤ w.errorSize :=
  amplificationPhysicalError_mono (slab_subset w hclock)
    ⟨t₀, (restrictSlab w hT hclock).activation⟩ w.compact (basis_continuousOn w)
    w.older_continuous w.error_continuous w.first_coupling_positive w.rate_pos

/-- (2.7) passes to the restricted setting. -/
theorem finiteSmallness_restrictSlab (w : PhysicalAmplification I t₀) {T : ℝ} {C₀ : ℕ}
    (hT : 0 ≤ T) (hclock : MapsTo w.clock (Icc 0 T) I) (hs : FiniteSmallness w T C₀) :
    FiniteSmallness (restrictSlab w hT hclock) T C₀ :=
  ⟨hs.1, le_trans (mul_le_mul_of_nonneg_left (errorSize_restrictSlab_le w hT hclock)
    (by positivity)) hs.2⟩

/-- The clock of the restricted setting maps `[0, T]` into the slab. -/
theorem mapsTo_restrictSlab (w : PhysicalAmplification I t₀) {T : ℝ} (hT : 0 ≤ T)
    (hclock : MapsTo w.clock (Icc 0 T) I) :
    MapsTo (restrictSlab w hT hclock).clock (Icc 0 T) (w.activeSlab T) :=
  fun _ hτ => clock_mem_slab w hτ

/-- The wave vector of the new wave restricts to the slab. -/
theorem newWaveVector_restrictSlab (w : PhysicalAmplification I t₀) {T lam : ℝ} (hT : 0 ≤ T)
    (hclock : MapsTo w.clock (Icc 0 T) I) {k : ℝ → Space} (hk : NewWaveVector w lam k) :
    NewWaveVector (restrictSlab w hT hclock) lam k :=
  ⟨hk.1, hk.2.1, fun t ht => (hk.2.2 t (slab_subset w hclock ht)).mono (slab_subset w hclock)⟩

/-- Copy of the private `AmplificationWindow.growingFactor_ratio_le`
(`PhysicalGrowthPropagator.lean`): (2.18) at two times bounds the ratio of reference
amplitudes by `e` times the ratio of the norms of the amplitude vector. -/
theorem growingFactor_ratio_le {ε u v : ℝ} {Y : ℝ → ℝ} {A : ℝ → ℝ}
    (hε : 2 * ε ≤ 1) (hu : 0 < A u)
    (hlo : Real.exp (-ε) * ReferencePropagator.growingFactor Y v ≤ A v)
    (hhi : A u ≤ Real.exp ε * ReferencePropagator.growingFactor Y u) :
    ReferencePropagator.growingFactor Y v / ReferencePropagator.growingFactor Y u ≤
      Real.exp 1 * (A v / A u) := by
  have hgv : ReferencePropagator.growingFactor Y v ≤ Real.exp ε * A v := by
    have h := mul_le_mul_of_nonneg_left hlo (Real.exp_pos ε).le
    rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h
  rw [← mul_div_assoc, div_le_div_iff₀ (ReferencePropagator.growingFactor_pos Y u) hu]
  calc
    _ ≤ (Real.exp ε * A v) * (Real.exp ε * ReferencePropagator.growingFactor Y u) :=
      mul_le_mul hgv hhi hu.le
        (mul_nonneg (Real.exp_pos ε).le
          ((mul_pos (Real.exp_pos _) (ReferencePropagator.growingFactor_pos Y v)).le.trans hlo))
    _ = Real.exp (ε + ε) * A v * ReferencePropagator.growingFactor Y u := by
      rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [hε]))
        ((mul_pos (Real.exp_pos _) (ReferencePropagator.growingFactor_pos Y v)).le.trans hlo))
      (ReferencePropagator.growingFactor_pos Y u).le

end

end TorusEuler.Paper.Lib.S2b
