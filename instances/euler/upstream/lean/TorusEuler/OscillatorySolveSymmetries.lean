import TorusEuler.OscillatoryJointRegularity

/-! Lattice, reflection, and support preservation for the actual oscillatory solve. -/

open Set
open scoped ContDiff InnerProductSpace Interval

namespace TorusEuler

section PhaseNormalization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem phaseMean_translate_periodic {f : ℝ → E} (hf : Function.Periodic f 1) (b : ℝ) :
    phaseMean (fun s => f (s + b)) = phaseMean f := by
  unfold phaseMean
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm (1 : ℝ) b] using hf.intervalIntegral_add_eq b 0

theorem phaseMean_reflect_periodic {f : ℝ → E} (hf : Function.Periodic f 1) :
    phaseMean (fun s => f (-s)) = phaseMean f := by
  unfold phaseMean
  rw [intervalIntegral.integral_comp_neg, neg_zero]
  have h := hf.intervalIntegral_add_eq 0 (-1)
  rw [zero_add, neg_add_cancel] at h
  exact h.symm

variable [CompleteSpace E]

/-- Phase normalization determines the additive constant of a primitive. -/
theorem phaseProfile_eq_of_hasDerivAt {F G f : ℝ → E}
    (hF : ∀ s, HasDerivAt F (f s) s) (hG : ∀ s, HasDerivAt G (f s) s)
    (hmean : phaseMean F = phaseMean G) : F = G := by
  have hD (s : ℝ) : HasDerivAt (fun u => F u - G u) 0 s := by
    have h := (hF s).sub (hG s)
    change HasDerivAt (fun u => F u - G u) (f s - f s) s at h
    simpa only [sub_self] using h
  have hconst : (fun s => F s - G s) = fun _ => F 0 - G 0 :=
    funext fun s => is_const_of_deriv_eq_zero (fun u => (hD u).differentiableAt)
      (fun u => (hD u).deriv) s 0
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun s => (hF s).continuousAt
  have hGc : Continuous G := continuous_iff_continuousAt.mpr fun s => (hG s).continuousAt
  have hc : phaseMean (fun s => F s - G s) = 0 := by
    rw [phaseMean_sub hFc hGc, hmean, sub_self]
  rw [hconst, phaseMean_const] at hc
  exact funext fun s => sub_eq_zero.mp ((congrFun hconst s).trans hc)

end PhaseNormalization

section Symmetries

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem oscillatoryPressureSlope_neg (M : E →L[ℝ] E) (κ f V : E) :
    oscillatoryPressureSlope M κ (-f) (-V) = -oscillatoryPressureSlope M κ f V := by
  simp only [oscillatoryPressureSlope, map_neg, inner_neg_right, ← neg_div]
  ring

private theorem inhomogeneous_eqOn_Icc
    {A : ℝ → E →L[ℝ] E} {y z F : ℝ → E} {T : ℝ}
    (hT : 0 ≤ T) (hA : ContinuousOn A (Icc 0 T))
    (hy : ∀ t ∈ Icc 0 T, HasDerivWithinAt y (A t (y t) + F t) (Icc 0 T) t)
    (hz : ∀ t ∈ Icc 0 T, HasDerivWithinAt z (A t (z t) + F t) (Icc 0 T) t)
    (hinit : y 0 = z 0) : EqOn y z (Icc 0 T) := by
  let w (t : ℝ) := y t - z t
  have hw (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt w (A t (w t)) (Icc 0 T) t := by
    refine ((hy t ht).sub (hz t ht)).congr_deriv ?_
    change A t (y t) + F t - (A t (z t) + F t) = A t (y t - z t)
    rw [map_sub]
    abel
  have hw0 : w 0 = 0 := sub_eq_zero.mpr hinit
  have h0 (t : ℝ) (_ : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun _ => (0 : E)) (A t 0) (Icc 0 T) t := by
    simpa only [map_zero] using hasDerivWithinAt_const t (Icc 0 T) (0 : E)
  have h := linearODE_unique_of_mem ordConnected_Icc ⟨le_rfl, hT⟩ hA hw h0 hw0
  exact fun t ht => sub_eq_zero.mp (h ht)

set_option maxHeartbeats 900000 in
/-- The pointwise projected equation and the normalized phase pressure
preserve the lattice twist, the simultaneous reflection, and vanishing
before activation or at an inactive label. Time propagation on the closed
slab holds each label and phase fixed. -/
theorem oscillatorySolve_preserves_conditional_symmetries
    {M : ℝ → Vec3 → E →L[ℝ] E} {κ : ℝ → Vec3 → E}
    {f V : ℝ → (Vec3 × ℝ) → E} {Q : ℝ → (Vec3 × ℝ) → ℝ}
    {k : Vec3} {T : ℝ} (hT : 0 ≤ T)
    (hA : ∀ a, ContinuousOn (fun u => affineWaveAmplitudeOperator (M u a) (κ u a)) (Icc 0 T))
    (hV₀ : V 0 = 0)
    (hV : ∀ t ∈ Icc 0 T, ∀ a s,
      HasDerivWithinAt (fun u => V u (a,s))
        (affineWaveAmplitudeOperator (M t a) (κ t a) (V t (a,s)) +
          oscillatoryTransverseProjection (κ t a) (f t (a,s))) (Icc 0 T) t)
    (hQd : ∀ t ∈ Icc 0 T, ∀ a s,
      HasDerivAt (fun σ => Q t (a,σ))
        (oscillatoryPressureSlope (M t a) (κ t a) (f t (a,s)) (V t (a,s))) s)
    (hQper : ∀ t ∈ Icc 0 T, ∀ a, Function.Periodic (fun s => Q t (a,s)) 1)
    (hQmean : ∀ t ∈ Icc 0 T, ∀ a, phaseMean (fun s => Q t (a,s)) = 0)
    (hMper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (M t))
    (hκper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (κ t))
    (hfTwist : ∀ t ∈ Icc 0 T, ∀ a s (n : Fin 3 → ℤ),
      f t (a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ) = f t (a,s))
    : (∀ t ∈ Icc 0 T, ∀ a s (n : Fin 3 → ℤ),
      V t (a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ) = V t (a,s) ∧
      Q t (a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ) = Q t (a,s)) ∧
    ((∀ t ∈ Icc 0 T, ∀ a, M t (-a) = M t a) →
      (∀ t ∈ Icc 0 T, ∀ a, κ t (-a) = κ t a) →
      (∀ t ∈ Icc 0 T, ∀ a s, f t (-a,-s) = -f t (a,s)) →
      ∀ t ∈ Icc 0 T, ∀ a s, V t (-a,-s) = -V t (a,s) ∧ Q t (-a,-s) = Q t (a,s)) ∧
    (∀ (τ : ℝ) (S : Set Vec3),
      (∀ t ∈ Icc 0 T, ∀ a s, t < τ ∨ a ∉ S → f t (a,s) = 0) →
      ∀ t ∈ Icc 0 T, ∀ a s, t < τ ∨ a ∉ S → V t (a,s) = 0 ∧ Q t (a,s) = 0) := by
  let I := Icc (0 : ℝ) T
  let A (u : ℝ) (a : Vec3) := affineWaveAmplitudeOperator (M u a) (κ u a)
  let F (u : ℝ) (a : Vec3) (s : ℝ) := oscillatoryTransverseProjection (κ u a) (f u (a,s))
  let p (t : ℝ) (a : Vec3) (s : ℝ) := oscillatoryPressureSlope (M t a) (κ t a) (f t (a,s)) (V t (a,s))
  have hTwistV (t : ℝ) (ht : t ∈ I) (a : Vec3) (s : ℝ) (n : Fin 3 → ℤ) :
      V t (a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ) = V t (a,s) := by
    let b := a + latticeVector n
    let c := ⟪k, latticeVector n⟫_ℝ
    have hshift (u : ℝ) (hu : u ∈ I) :
        HasDerivWithinAt (fun r => V r (b,s + c))
          (A u a (V u (b,s + c)) + F u a s) I u := by
      have h := hV u hu b (s + c)
      simpa only [b, c, hMper u hu n a, hκper u hu n a, hfTwist u hu a s n, A, F] using h
    exact inhomogeneous_eqOn_Icc hT (hA a) hshift (fun u hu => hV u hu a s)
      (by simp [hV₀]) ht
  refine ⟨?_, ?_, ?_⟩
  · intro t ht a s n
    refine ⟨hTwistV t ht a s n, ?_⟩
    let b := a + latticeVector n
    let c := ⟪k, latticeVector n⟫_ℝ
    have hderive (σ : ℝ) : HasDerivAt (fun u => Q t (b,u + c)) (p t a σ) σ := by
      have h := (hQd t ht b (σ + c)).scomp σ ((hasDerivAt_id σ).add_const c)
      simpa only [Function.comp_def, id_eq, one_smul, b, c, p, hMper t ht n a, hκper t ht n a,
        hfTwist t ht a σ n, hTwistV t ht a σ n] using h
    have hmean : phaseMean (fun u => Q t (b,u + c)) = phaseMean (fun u => Q t (a,u)) :=
      (phaseMean_translate_periodic (hQper t ht b) c).trans
        ((hQmean t ht b).trans (hQmean t ht a).symm)
    exact congrFun (phaseProfile_eq_of_hasDerivAt hderive (hQd t ht a) hmean) s
  · intro hMneg hκneg hfneg
    have hNegV (t : ℝ) (ht : t ∈ I) (a : Vec3) (s : ℝ) :
        V t (-a,-s) = -V t (a,s) := by
      have hshift (u : ℝ) (hu : u ∈ I) :
          HasDerivWithinAt (fun r => V r (-a,-s))
            (A u a (V u (-a,-s)) - F u a s) I u := by
        have h := hV u hu (-a) (-s)
        simpa only [hMneg u hu a, hκneg u hu a, hfneg u hu a s, map_neg, sub_eq_add_neg, A, F] using h
      have hneg (u : ℝ) (hu : u ∈ I) :
          HasDerivWithinAt (fun r => -V r (a,s))
            (A u a (-V u (a,s)) - F u a s) I u := by
        have h := (hV u hu a s).neg
        exact h.congr_deriv (by simp only [A, F, map_neg, sub_eq_add_neg, neg_add])
      have h := inhomogeneous_eqOn_Icc hT (hA a)
        (fun u hu => by simpa only [sub_eq_add_neg] using hshift u hu)
        (fun u hu => by simpa only [sub_eq_add_neg] using hneg u hu)
        (by simp [hV₀])
      exact h ht
    intro t ht a s
    refine ⟨hNegV t ht a s, ?_⟩
    have hderive (σ : ℝ) : HasDerivAt (fun u => Q t (-a,-u)) (p t a σ) σ := by
      have h := (hQd t ht (-a) (-σ)).scomp σ ((hasDerivAt_id σ).neg)
      simpa only [Function.comp_def, id_eq, neg_smul, one_smul, p, hMneg t ht a, hκneg t ht a,
        hfneg t ht a σ, hNegV t ht a σ, oscillatoryPressureSlope_neg, neg_neg] using h
    have hmean : phaseMean (fun u => Q t (-a,-u)) = phaseMean (fun u => Q t (a,u)) :=
      (phaseMean_reflect_periodic (hQper t ht (-a))).trans
        ((hQmean t ht (-a)).trans (hQmean t ht a).symm)
    exact congrFun (phaseProfile_eq_of_hasDerivAt hderive (hQd t ht a) hmean) s
  · intro τ S hfzero
    have hZeroV (t : ℝ) (ht : t ∈ I) (a : Vec3) (s : ℝ) (h : t < τ ∨ a ∉ S) :
        V t (a,s) = 0 := by
      have hsub : Icc 0 t ⊆ I := Icc_subset_Icc_right ht.2
      have hz (u : ℝ) (hu : u ∈ Icc 0 t) :
          HasDerivWithinAt (fun r => V r (a,s)) (A u a (V u (a,s))) (Icc 0 t) u := by
        have hf' := hfzero u (hsub hu) a s (h.imp (hu.2.trans_lt) id)
        simpa only [hf', map_zero, add_zero, A] using (hV u (hsub hu) a s).mono hsub
      have hconst (u : ℝ) (_ : u ∈ Icc 0 t) :
          HasDerivWithinAt (fun _ => (0 : E)) (A u a 0) (Icc 0 t) u := by
        simpa only [map_zero] using hasDerivWithinAt_const u (Icc 0 t) (0 : E)
      exact linearODE_unique_of_mem ordConnected_Icc ⟨le_rfl, ht.1⟩
        ((hA a).mono hsub) hz hconst (by simp [hV₀]) ⟨ht.1, le_rfl⟩
    intro t ht a s h
    refine ⟨hZeroV t ht a s h, ?_⟩
    have hderive (σ : ℝ) : HasDerivAt (fun u => Q t (a,u)) 0 σ := by
      simpa only [hfzero t ht a σ h, hZeroV t ht a σ h, oscillatoryPressureSlope, map_zero,
        inner_zero_right, mul_zero, sub_self, zero_div] using hQd t ht a σ
    have hmean : phaseMean (fun u => Q t (a,u)) = phaseMean (fun _ => (0 : ℝ)) := by
      rw [hQmean t ht a, phaseMean_const]
    exact congrFun (phaseProfile_eq_of_hasDerivAt hderive (fun σ => hasDerivAt_const σ (0 : ℝ)) hmean) s

set_option maxHeartbeats 1100000 in
/-- The smooth zero-start solve with the actual normalized pressure
inherits the symmetry and inactive-region conditions of the hierarchy. -/
theorem exists_jointSmooth_oscillatoryPhaseSolve_withConditionalSymmetries
    [FiniteDimensional ℝ E]
    {M : ℝ → Vec3 → E →L[ℝ] E} {κ : ℝ → Vec3 → E}
    {f : ℝ → (Vec3 × ℝ) → E} {k : Vec3} {T : ℝ} (hT : 0 < T)
    (hM : ContDiffOn ℝ ∞ (Function.uncurry M) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hκ : ContDiffOn ℝ ∞ (Function.uncurry κ) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set (Vec3 × ℝ))))
    (hκ₀ : ∀ a, κ 0 a ≠ 0)
    (hκt : ∀ a t, t ∈ Icc 0 T →
      HasDerivWithinAt (fun u => κ u a) (-((M t a).adjoint (κ t a))) (Icc 0 T) t)
    (hfper : ∀ a t, t ∈ Icc 0 T → Function.Periodic (fun s => f t (a,s)) 1)
    (hfmean : ∀ a t, t ∈ Icc 0 T → phaseMean (fun s => f t (a,s)) = 0)
    (hMper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (M t))
    (hκper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (κ t))
    (hfTwist : ∀ t ∈ Icc 0 T, ∀ a s (n : Fin 3 → ℤ),
      f t (a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ) = f t (a,s))
    :
    ∃ (V : ℝ → (Vec3 × ℝ) → E) (Q : ℝ → (Vec3 × ℝ) → ℝ), V 0 = 0 ∧
      ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set (Vec3 × ℝ))) ∧
      Q = (fun t p => oscillatoryPhasePressure (M t p.1) (κ t p.1)
        (fun s => f t (p.1,s)) (fun s => V t (p.1,s)) p.2) ∧
      ContDiffOn ℝ ∞ (Function.uncurry Q) (Icc 0 T ×ˢ (univ : Set (Vec3 × ℝ))) ∧
      (∀ a t, t ∈ Icc 0 T →
        Function.Periodic (fun s => V t (a,s)) 1 ∧ phaseMean (fun s => V t (a,s)) = 0 ∧
        Function.Periodic (fun s => Q t (a,s)) 1 ∧ phaseMean (fun s => Q t (a,s)) = 0 ∧
        ∀ s, ⟪κ t a, V t (a,s)⟫_ℝ = 0 ∧
          HasDerivWithinAt (fun u => V u (a,s))
            (affineWaveAmplitudeOperator (M t a) (κ t a) (V t (a,s)) +
              oscillatoryTransverseProjection (κ t a) (f t (a,s))) (Icc 0 T) t ∧
          HasDerivAt (fun σ => Q t (a,σ))
            (oscillatoryPressureSlope (M t a) (κ t a) (f t (a,s)) (V t (a,s))) s ∧
          HasDerivWithinAt (fun u => V u (a,s))
            (f t (a,s) - M t a (V t (a,s)) -
              deriv (fun σ => Q t (a,σ)) s • κ t a) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, ∀ a s (n : Fin 3 → ℤ),
        V t (a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ) = V t (a,s) ∧
        Q t (a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ) = Q t (a,s)) ∧
      ((∀ t ∈ Icc 0 T, ∀ a, M t (-a) = M t a) →
        (∀ t ∈ Icc 0 T, ∀ a, κ t (-a) = κ t a) →
        (∀ t ∈ Icc 0 T, ∀ a s, f t (-a,-s) = -f t (a,s)) →
        ∀ t ∈ Icc 0 T, ∀ a s, V t (-a,-s) = -V t (a,s) ∧ Q t (-a,-s) = Q t (a,s)) ∧
      (∀ (τ : ℝ) (S : Set Vec3),
        (∀ t ∈ Icc 0 T, ∀ a s, t < τ ∨ a ∉ S → f t (a,s) = 0) →
        ∀ t ∈ Icc 0 T, ∀ a s, t < τ ∨ a ∉ S → V t (a,s) = 0 ∧ Q t (a,s) = 0) := by
  obtain ⟨V, Q, hV₀, hVs, hQdef, hQs, hspec⟩ :=
    exists_jointSmooth_oscillatoryPhaseSolve (M := M) (κ := κ) (f := f)
      hT hM hκ hf hκ₀ hκt hfper hfmean
  have hA (a : Vec3) :
      ContinuousOn (fun u => affineWaveAmplitudeOperator (M u a) (κ u a)) (Icc 0 T) := by
    have hs : Continuous (fun t : ℝ => (t, a)) := continuous_id.prodMk continuous_const
    have hm : MapsTo (fun t : ℝ => (t, a)) (Icc 0 T) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
      fun _ ht => ⟨ht, mem_univ _⟩
    have hMc : ContinuousOn (fun t => M t a) (Icc 0 T) :=
      hM.continuousOn.comp hs.continuousOn hm
    have hκc : ContinuousOn (fun t => κ t a) (Icc 0 T) :=
      hκ.continuousOn.comp hs.continuousOn hm
    have hAdj : ContinuousOn (fun t => -(M t a).adjoint) (Icc 0 T) :=
      ((ContinuousLinearMap.adjoint (𝕜 := ℝ)).continuous.comp_continuousOn hMc).neg
    have hn : ∀ t ∈ Icc 0 T, κ t a ≠ 0 :=
      linearODE_ne_zero_of_mem ordConnected_Icc ⟨le_rfl, hT.le⟩ hAdj
        (fun t ht => by simpa only [neg_apply] using hκt a t ht) (hκ₀ a)
    exact continuousOn_affineWaveAmplitudeOperator hMc hκc hn
  have hV (t : ℝ) (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
      HasDerivWithinAt (fun u => V u (a,s))
        (affineWaveAmplitudeOperator (M t a) (κ t a) (V t (a,s)) +
          oscillatoryTransverseProjection (κ t a) (f t (a,s))) (Icc 0 T) t :=
    ((hspec a t ht).2.2.2.2 s).2.1
  have hQd (t : ℝ) (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
      HasDerivAt (fun σ => Q t (a,σ))
        (oscillatoryPressureSlope (M t a) (κ t a) (f t (a,s)) (V t (a,s))) s :=
    ((hspec a t ht).2.2.2.2 s).2.2.1
  have hSym := oscillatorySolve_preserves_conditional_symmetries (M := M) (κ := κ) (f := f) (V := V) (Q := Q)
    (k := k) hT.le hA hV₀ hV hQd
    (fun t ht a => (hspec a t ht).2.2.1) (fun t ht a => (hspec a t ht).2.2.2.1)
    hMper hκper hfTwist
  exact ⟨V, Q, hV₀, hVs, hQdef, hQs, hspec, hSym⟩

end Symmetries

end TorusEuler
