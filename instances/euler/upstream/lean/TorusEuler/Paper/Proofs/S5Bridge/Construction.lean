import TorusEuler.Paper.Proofs.S5Bridge.Seed

/-!
# S5 bridge: the standing hypotheses from the library data of the construction

The converse direction of `Parent.lean`, for the proofs of Theorem 7.1 and of the
auxiliary note, which apply the Section 5 statements to the waves of the construction.
The library describes a wave by its central data `CenterWaveOn (fun t => ∇U(t,0)) κ 𝐚 …`
with a central covector `κ`; the Section 5 statements use the carrier `k_*` with
`κ(t,0) = (D_aX(t,0))^{-T} k_*`.

* `waveVector_origin_eq_of_covector`: the carrier `k_* = (D_aX(t₀,0))^T κ(t₀)` transports
  to `κ` along the origin (`S5.waveVector X k_* t 0 = κ t` on `[t₀,T]`).
* `centerWaveOn_congr_covector`: `CenterWaveOn` only depends on the covector on `[t₀,T]`.
* `origin_of_centerWaveOn`, `launch_of_carrier`: `S5.Origin` and `S5.Launch` from the
  library central data.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Bridge

open LocalizedAmplitude

noncomputable section

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {t₀ : ℝ} {center : ℝ → Vec3}
  {pU : Pressure} {D lam : ℝ}

/-- `CenterWaveOn` only depends on the values of the covector on `[t₀,T]`. -/
theorem centerWaveOn_congr_covector {M : ℝ → Vec3 →L[ℝ] Vec3} {κ κ' : ℝ → Vec3} {D' : ℝ}
    (h : CenterWaveOn M κ center t₀ T D') (hEq : EqOn κ' κ (Icc t₀ T)) :
    CenterWaveOn M κ' center t₀ T D' := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, ?_, fun t ht => ?_⟩
  · rw [hEq ht]
    exact (h.covector t ht).congr (fun u hu => hEq hu) (hEq ht)
  · rw [hEq ht]
    exact h.nonzero t ht
  · rw [hEq ht]
    exact h.amplitude t ht
  · intro z hz hperp u v hu hv huv
    refine h.stability z (fun t ht => ?_) (fun t ht => ?_) hu hv huv
    · rw [← hEq ht]
      exact hz t ht
    · rw [← hEq ht]
      exact hperp t ht
  · rw [hEq ht]
    exact h.coupling t ht

/-- The carrier `k_* = (D_aX(t₀,0))^T κ(t₀)` of a central covector `κ` with
`κ_t = -∇U(t,0)^T κ` transports to `κ` along the origin: `κ(t,0) = κ(t)` on `[t₀,T]`
(and `k_* ≠ 0` when `κ(t₀) ≠ 0`). -/
theorem waveVector_origin_eq_of_covector (hT : 0 < T) (hP : S5.Parent T U X pU D lam)
    (ht₀ : t₀ ∈ Icc 0 T) {κ : ℝ → Vec3}
    (hκ : ∀ t ∈ Icc t₀ T, HasDerivWithinAt κ (-((fderiv ℝ (U t) (0 : Vec3)).adjoint (κ t)))
      (Icc t₀ T) t) :
    ((κ t₀ ≠ 0 → (fderiv ℝ (X 0 t₀) (0 : Vec3)).adjoint (κ t₀) ≠ 0) ∧
      ∀ t ∈ Icc t₀ T,
        S5.waveVector X ((fderiv ℝ (X 0 t₀) (0 : Vec3)).adjoint (κ t₀)) t 0 = κ t) := by
  obtain ⟨hne, heq⟩ := hP.flow.center_coframe_covector_eq hT (hP.velocity_smooth.of_le (by simp))
    hP.velocity_periodic hP.velocity_odd ht₀ hκ
  refine ⟨hne, fun t ht => ?_⟩
  have h := heq t ht
  have h0 : X 0 t 0 = 0 := Parent.flow_origin hT hP (Icc_subset_Icc_left ht₀.1 ht)
  unfold S5.waveVector labelWaveVector
  rw [h0]
  exact h

/-- `S5.Launch` from a nonzero carrier, an activation time in `[0,T)` and `|κ(t₀,0)| = λ`. -/
theorem launch_of_carrier (ht₀ : 0 ≤ t₀) (htT : t₀ < T) (hk : k ≠ 0)
    (hlam : ‖S5.waveVector X k t₀ 0‖ = lam) : S5.Launch T X k lam t₀ :=
  ⟨ht₀, htT, hk, hlam⟩

/-- `S5.Origin` from the library central data at the parent gradient `∇U(t,0)`, for a
central covector equal to `κ(t,0)` on `[t₀,T]`, and the normalization `γ ≤ 1`. -/
theorem origin_of_centerWaveOn (hP : S5.Parent T U X pU D lam) (hL : S5.Launch T X k lam t₀)
    {κ : ℝ → Vec3}
    (hc : CenterWaveOn (fun t => fderiv ℝ (U t) 0) κ center t₀ T D)
    (hκ : ∀ t ∈ Icc t₀ T, S5.waveVector X k t 0 = κ t)
    (hnorm : ∀ t ∈ Icc t₀ T, lam ^ (3 / 4 : ℝ) * ‖center t‖ ≤ 1) :
    S5.Origin T U X k D lam t₀ center :=
  ⟨((centerWaveOn_congr_covector hc fun _ ht => hκ _ ht).congr_gradient fun _ ht =>
    (Parent.strainField_origin (Launch.end_pos hL) hP (Launch.active_subset hL ht)).symm), hnorm⟩

end

end TorusEuler.Paper.Bridge
