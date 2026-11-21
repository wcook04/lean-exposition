import TorusEuler.FourierCutoffBounds

/-! The (C^{s,1/2}) tail estimate (B.2) on the Euclidean lift of the unit torus. -/

open MeasureTheory Set UnitAddTorus
open scoped ContDiff SchwartzMap

namespace TorusEuler

noncomputable section

section HolderNorm

variable {E : Type*} [NormedAddCommGroup E]

/-- The uniform norm of a bounded field on the Euclidean lift. -/
def spatialSupNorm (f : Vec3 → E) : ℝ :=
  ⨆ x : Vec3, ‖f x‖

/-- The quotient defining the spatial (1/2)-Hölder seminorm, using an increment. -/
def spatialHolderHalfQuotient (f : Vec3 → E) (p : Vec3 × Vec3) : ℝ :=
  ‖f (p.1 + p.2) - f p.1‖ / Real.sqrt ‖p.2‖

/-- The (1/2)-Hölder seminorm on the lift. Equal-point increments have quotient zero. -/
def spatialHolderHalfSeminorm (f : Vec3 → E) : ℝ :=
  ⨆ p : Vec3 × Vec3, spatialHolderHalfQuotient f p

theorem norm_le_spatialSupNorm {f : Vec3 → E} (h : BddAbove (range (fun x => ‖f x‖))) (x : Vec3) :
    ‖f x‖ ≤ spatialSupNorm f :=
  le_ciSup h x

theorem norm_increment_le_spatialHolderHalfSeminorm {f : Vec3 → E}
    (h : BddAbove (range (spatialHolderHalfQuotient f))) (x v : Vec3) :
    ‖f (x + v) - f x‖ ≤ spatialHolderHalfSeminorm f * Real.sqrt ‖v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (div_le_iff₀ (Real.sqrt_pos_of_pos (norm_pos_iff.mpr hv))).mp (le_ciSup h (x, v))

private theorem spatialSupNorm_nonneg {f : Vec3 → E}
    (h : BddAbove (range (fun x => ‖f x‖))) : 0 ≤ spatialSupNorm f :=
  (norm_nonneg (f 0)).trans (norm_le_spatialSupNorm h 0)

private theorem spatialHolderHalfSeminorm_nonneg {f : Vec3 → E}
    (h : BddAbove (range (spatialHolderHalfQuotient f))) : 0 ≤ spatialHolderHalfSeminorm f := by
  have heq : spatialHolderHalfQuotient f (0, 0) = 0 := by simp [spatialHolderHalfQuotient]
  have hle := le_ciSup h ((0 : Vec3), (0 : Vec3))
  rw [heq] at hle
  exact hle

private theorem bddAbove_quotient_and_seminorm_le {f : Vec3 → E} {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ x v, ‖f (x + v) - f x‖ ≤ D * Real.sqrt ‖v‖) :
    BddAbove (range (spatialHolderHalfQuotient f)) ∧ spatialHolderHalfSeminorm f ≤ D := by
  have hquot (p : Vec3 × Vec3) : spatialHolderHalfQuotient f p ≤ D := by
    rcases p with ⟨x, v⟩
    by_cases hv : v = 0
    · simpa [spatialHolderHalfQuotient, hv] using hD
    · exact (div_le_iff₀ (Real.sqrt_pos_of_pos (norm_pos_iff.mpr hv))).mpr (h x v)
  exact ⟨⟨D, forall_mem_range.mpr hquot⟩, ciSup_le hquot⟩

variable [NormedSpace ℝ E]

/-- Spatial (C^{m,1/2}) on the lift, with finite uniform and increment bounds
for the iterated derivatives through order (m). -/
def SpatialHolderHalf (m : ℕ) (f : Vec3 → E) : Prop :=
  ContDiff ℝ m f ∧ ∀ j ≤ m,
    BddAbove (range (fun x => ‖iteratedFDeriv ℝ j f x‖)) ∧
    BddAbove (range (spatialHolderHalfQuotient (iteratedFDeriv ℝ j f)))

/-- The spatial (C^{m,1/2}) norm using the operator norms of the iterated
Fréchet derivatives. -/
def spatialHolderHalfNorm (m : ℕ) (f : Vec3 → E) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (spatialSupNorm (iteratedFDeriv ℝ j f) +
    spatialHolderHalfSeminorm (iteratedFDeriv ℝ j f))

private theorem spatialHolderHalfNorm_ge_order {m : ℕ} {f : Vec3 → E}
    (hf : SpatialHolderHalf m f) {j : ℕ} (hj : j ≤ m) :
    spatialSupNorm (iteratedFDeriv ℝ j f) + spatialHolderHalfSeminorm (iteratedFDeriv ℝ j f) ≤
      spatialHolderHalfNorm m f := by
  unfold spatialHolderHalfNorm
  apply Finset.single_le_sum (f := fun j => spatialSupNorm (iteratedFDeriv ℝ j f) +
    spatialHolderHalfSeminorm (iteratedFDeriv ℝ j f)) _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  intro k hk
  obtain ⟨h0, h1⟩ := hf.2 k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  exact add_nonneg (spatialSupNorm_nonneg h0) (spatialHolderHalfSeminorm_nonneg h1)

end HolderNorm

section IteratedDerivatives

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem norm_iteratedFDeriv_iteratedFDeriv (f : Vec3 → E) (n j : ℕ) (x : Vec3) :
    ‖iteratedFDeriv ℝ n (iteratedFDeriv ℝ j f) x‖ = ‖iteratedFDeriv ℝ (j + n) f x‖ := by
  induction j generalizing n with
  | zero =>
      rw [iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, zero_add]
  | succ j ih =>
      rw [iteratedFDeriv_succ_eq_comp_left]
      let e := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Vec3) E).symm
      have h := LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := Vec3)
        (F := Vec3 →L[ℝ] (Vec3 [×j]→L[ℝ] E)) (G := Vec3 [×(j + 1)]→L[ℝ] E)
        e (fderiv ℝ (iteratedFDeriv ℝ j f)) x n
      rw [norm_iteratedFDeriv_fderiv, ih, show j + (n + 1) = j + 1 + n by omega] at h
      exact h

private theorem norm_sub_iteratedFDeriv_iteratedFDeriv {f : Vec3 → E} (n j : ℕ)
    (hf : ContDiff ℝ (j + n : ℕ) f) (x y : Vec3) :
    ‖iteratedFDeriv ℝ n (iteratedFDeriv ℝ j f) x - iteratedFDeriv ℝ n (iteratedFDeriv ℝ j f) y‖ =
      ‖iteratedFDeriv ℝ (j + n) f x - iteratedFDeriv ℝ (j + n) f y‖ := by
  let t := x - y
  have hadd : y + t = x := by dsimp [t]; abel
  have hshift : ContDiff ℝ (j + n : ℕ) (fun z => f (z + t)) := hf.comp (by fun_prop)
  have hj : (j : ℕ∞ω) ≤ (j + n : ℕ) := by exact_mod_cast Nat.le_add_right j n
  have hD : ContDiff ℝ n (iteratedFDeriv ℝ j f) := hf.iteratedFDeriv_right (by norm_cast; omega)
  have hDshift : ContDiff ℝ n (fun z => iteratedFDeriv ℝ j f (z + t)) :=
    hD.comp (by fun_prop)
  have h := norm_iteratedFDeriv_iteratedFDeriv ((fun z => f (z + t)) - f) n j y
  have hinner := iteratedFDeriv_sub (i := j) (hshift.of_le hj) (hf.of_le hj)
  have houter := iteratedFDeriv_sub (i := n) hDshift hD
  have htotal := iteratedFDeriv_sub (i := j + n) hshift hf
  rw [hinner, iteratedFDeriv_comp_add_right', houter, htotal] at h
  simpa only [Pi.sub_apply, iteratedFDeriv_comp_add_right, hadd] using h

end IteratedDerivatives

section CutoffTail

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Absolute moments of the undilated frequency cutoff kernel. -/
def cutoffKernelAbsoluteMoment (K : 𝓢(Vec3, ℂ)) (k : ℕ) : ℝ :=
  ∫ y, ‖y‖ ^ k * ‖K y‖

private theorem cutoffKernelAbsoluteMoment_nonneg (K : 𝓢(Vec3, ℂ)) (k : ℕ) :
    0 ≤ cutoffKernelAbsoluteMoment K k :=
  integral_nonneg fun y => mul_nonneg (pow_nonneg (norm_nonneg y) k) (norm_nonneg _)

/-- At positive order the tail constant is an absolute moment. At order zero it
is one plus the (L^1) operator bound. -/
def cutoffHolderTailConstant (K : 𝓢(Vec3, ℂ)) (k : ℕ) : ℝ :=
  (if k = 0 then 1 else 0) + cutoffKernelAbsoluteMoment K k

private theorem cutoffHolderTailConstant_nonneg (K : 𝓢(Vec3, ℂ)) (k : ℕ) :
    0 ≤ cutoffHolderTailConstant K k := by
  refine add_nonneg ?_ (cutoffKernelAbsoluteMoment_nonneg K k)
  split <;> norm_num

private theorem cutoffHolderTailConstant_le (K : 𝓢(Vec3, ℂ)) {M k : ℕ} (hk : k ≤ M) :
    cutoffHolderTailConstant K k ≤ 1 + ∑ i ∈ Finset.range (M + 1), cutoffKernelAbsoluteMoment K i := by
  apply add_le_add
  · split <;> norm_num
  · exact Finset.single_le_sum (fun i _ => cutoffKernelAbsoluteMoment_nonneg K i)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

private theorem spatialHolderHalf_bounds_liftTail
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) {Λ : ℝ} (hΛ : 0 < Λ)
    {k : ℕ} {g : Vec3 → E} (hg : ContDiff ℝ k g)
    (h0 : BddAbove (range (fun x => ‖g x‖)))
    (ht0 : BddAbove (range (fun x => ‖iteratedFDeriv ℝ k g x‖)))
    (ht1 : BddAbove (range (spatialHolderHalfQuotient (iteratedFDeriv ℝ k g)))) :
    let K := cutoffSchwartzKernel hψ hs
    let R := g - liftConvolution (scaledLiftKernel Λ K) g
    BddAbove (range (fun x => ‖R x‖)) ∧
    BddAbove (range (spatialHolderHalfQuotient R)) ∧
    spatialSupNorm R + spatialHolderHalfSeminorm R ≤
      (Λ⁻¹) ^ k * cutoffHolderTailConstant K k *
      (spatialSupNorm (iteratedFDeriv ℝ k g) + spatialHolderHalfSeminorm (iteratedFDeriv ℝ k g)) := by
  let K := cutoffSchwartzKernel hψ hs
  let KR := scaledLiftKernel Λ K
  let R := g - liftConvolution KR g
  let A := (Λ⁻¹) ^ k * cutoffHolderTailConstant K k
  let B := spatialSupNorm (iteratedFDeriv ℝ k g)
  let H := spatialHolderHalfSeminorm (iteratedFDeriv ℝ k g)
  have hA : 0 ≤ A :=
    mul_nonneg (pow_nonneg (inv_nonneg.mpr hΛ.le) k) (cutoffHolderTailConstant_nonneg K k)
  have hHb : 0 ≤ H := spatialHolderHalfSeminorm_nonneg ht1
  have hpoint : (∀ x, ‖R x‖ ≤ A * B) ∧
      (∀ x v, ‖R (x + v) - R x‖ ≤ A * H * Real.sqrt ‖v‖) := by
    cases k with
    | zero =>
      have hKR : Integrable KR := integrable_scaledLiftKernel hΛ K.integrable
      have hL1 : A = 1 + ∫ y, ‖KR y‖ := by
        rw [integral_norm_scaledLiftKernel hΛ]
        simp [A, cutoffHolderTailConstant, cutoffKernelAbsoluteMoment]
      have hbound (x : Vec3) : ‖g x‖ ≤ B := by
        simpa only [norm_iteratedFDeriv_zero] using norm_le_spatialSupNorm ht0 x
      have hinc (x v : Vec3) : ‖g (x + v) - g x‖ ≤ H * Real.sqrt ‖v‖ := by
        have h := norm_increment_le_spatialHolderHalfSeminorm ht1 x v
        change ‖iteratedFDeriv ℝ 0 g (x + v) - iteratedFDeriv ℝ 0 g x‖ ≤ H * Real.sqrt ‖v‖ at h
        rw [iteratedFDeriv_zero_eq_comp] at h
        simpa only [Function.comp_apply, ← map_sub, LinearIsometryEquiv.norm_map] using h
      refine ⟨fun x => ?_, fun x v => ?_⟩
      · calc
          ‖R x‖ ≤ ‖g x‖ + ‖liftConvolution KR g x‖ := norm_sub_le _ _
          _ ≤ B + (∫ y, ‖KR y‖) * B :=
            add_le_add (hbound x) (norm_liftConvolution_le hKR hbound x)
          _ = A * B := by rw [hL1]; ring
      · have heq : R (x + v) - R x = (g (x + v) - g x) -
            (liftConvolution KR g (x + v) - liftConvolution KR g x) := by
          dsimp only [R, Pi.sub_apply]
          abel
        rw [heq]
        calc
          _ ≤ ‖g (x + v) - g x‖ + ‖liftConvolution KR g (x + v) - liftConvolution KR g x‖ :=
            norm_sub_le _ _
          _ ≤ H * Real.sqrt ‖v‖ + (∫ y, ‖KR y‖) * (H * Real.sqrt ‖v‖) :=
            add_le_add (hinc x v)
              (norm_liftConvolution_increment_le hKR hg.continuous hbound x v (fun z => hinc z v))
          _ = A * H * Real.sqrt ‖v‖ := by rw [hL1]; ring
    | succ n =>
      refine ⟨fun x => ?_, fun x v => ?_⟩
      · have h := norm_sub_liftConvolution_scaledCutoffSchwartzKernel_le hψ hs hunit hΛ hg
          (norm_le_spatialSupNorm h0) (norm_le_spatialSupNorm ht0) x
        simpa [A, B, R, KR, K, cutoffHolderTailConstant, cutoffKernelAbsoluteMoment] using h
      · have h := norm_sub_liftConvolution_scaledCutoffSchwartzKernel_increment_le
          hψ hs hunit hΛ hg (norm_le_spatialSupNorm h0) v
          (fun z => norm_increment_le_spatialHolderHalfSeminorm ht1 z v) x
        simpa [A, H, R, KR, K, cutoffHolderTailConstant, cutoffKernelAbsoluteMoment, mul_assoc] using h
  obtain ⟨hseminormBound, hseminorm⟩ := bddAbove_quotient_and_seminorm_le (mul_nonneg hA hHb)
    hpoint.2
  have hsup : spatialSupNorm R ≤ A * B := ciSup_le hpoint.1
  refine ⟨⟨A * B, forall_mem_range.mpr hpoint.1⟩, hseminormBound, ?_⟩
  rw [mul_add]
  exact add_le_add hsup hseminorm

/-- A uniform constant for all losses of regularity in Appendix B at input order `M`. -/
def cutoffHolderTailUniformConstant (K : 𝓢(Vec3, ℂ)) (M : ℕ) : ℝ :=
  (M + 1 : ℝ) * (1 + ∑ k ∈ Finset.range (M + 1), cutoffKernelAbsoluteMoment K k)

private theorem spatialHolderHalfNorm_cutoffTail_add
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) {Λ : ℝ} (hΛ : 0 < Λ)
    (g : C(UnitAddTorus (Fin 3), E)) (s k : ℕ)
    (hf : SpatialHolderHalf (s + k) (fun x => g (toUnitTorus x))) :
    let f : Vec3 → E := fun x => g (toUnitTorus x)
    let R : Vec3 → E := f - fun x => smoothFourierCutoff ψ Λ g (toUnitTorus x)
    SpatialHolderHalf s R ∧
      spatialHolderHalfNorm s R ≤ cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs)
        (s + k) * (Λ⁻¹) ^ k * spatialHolderHalfNorm (s + k) f := by
  let f : Vec3 → E := fun x => g (toUnitTorus x)
  let Sf : Vec3 → E := fun x => smoothFourierCutoff ψ Λ g (toUnitTorus x)
  let R := f - Sf
  let K := cutoffSchwartzKernel hψ hs
  let KR := scaledLiftKernel Λ K
  let N := spatialHolderHalfNorm (s + k) f
  let A := (Λ⁻¹) ^ k * cutoffHolderTailConstant K k
  have hΛinv : 0 ≤ (Λ⁻¹) ^ k := pow_nonneg (inv_nonneg.mpr hΛ.le) k
  have hA : 0 ≤ A := mul_nonneg hΛinv (cutoffHolderTailConstant_nonneg K k)
  have hN : 0 ≤ N := by
    obtain ⟨h0, h1⟩ := hf.2 0 (Nat.zero_le _)
    exact (add_nonneg (spatialSupNorm_nonneg h0) (spatialHolderHalfSeminorm_nonneg h1)).trans
      (spatialHolderHalfNorm_ge_order hf (Nat.zero_le _))
  have hSf : ContDiff ℝ ∞ Sf := contDiff_lift_smoothFourierCutoff ψ Λ g
  have hKR : Integrable KR := integrable_scaledLiftKernel hΛ K.integrable
  have hconv : liftConvolution KR f = Sf := funext (liftConvolution_cutoffSchwartzKernel hψ hs hΛ g)
  have hlevels (j : ℕ) (hj : j ≤ s) :
      BddAbove (range (fun x => ‖iteratedFDeriv ℝ j R x‖)) ∧
      BddAbove (range (spatialHolderHalfQuotient (iteratedFDeriv ℝ j R))) ∧
      spatialSupNorm (iteratedFDeriv ℝ j R) + spatialHolderHalfSeminorm (iteratedFDeriv ℝ j R)
        ≤ A * N := by
    let df := iteratedFDeriv ℝ j f
    have hjM : j ≤ s + k := by omega
    have hjk : j + k ≤ s + k := by omega
    have hdf : ContDiff ℝ k df := hf.1.iteratedFDeriv_right (by
      norm_cast
      omega)
    have hdf0 := (hf.2 j hjM).1
    have hsup : (fun x => ‖iteratedFDeriv ℝ k df x‖) =
        (fun x => ‖iteratedFDeriv ℝ (j + k) f x‖) :=
      funext (norm_iteratedFDeriv_iteratedFDeriv f k j)
    have hquot : spatialHolderHalfQuotient (iteratedFDeriv ℝ k df) =
        spatialHolderHalfQuotient (iteratedFDeriv ℝ (j + k) f) := by
      funext p
      unfold spatialHolderHalfQuotient
      rw [norm_sub_iteratedFDeriv_iteratedFDeriv k j (hf.1.of_le (by exact_mod_cast hjk))]
    have hnorm : spatialSupNorm (iteratedFDeriv ℝ k df) +
        spatialHolderHalfSeminorm (iteratedFDeriv ℝ k df) ≤ N := by
      unfold spatialSupNorm spatialHolderHalfSeminorm
      rw [hsup, hquot]
      exact spatialHolderHalfNorm_ge_order hf hjk
    have htail := spatialHolderHalf_bounds_liftTail hψ hs hunit hΛ hdf hdf0
      (hsup.symm ▸ (hf.2 _ hjk).1) (hquot.symm ▸ (hf.2 _ hjk).2)
    have hderiv : iteratedFDeriv ℝ j R = df - liftConvolution KR df := by
      change iteratedFDeriv ℝ j (f - Sf) = _
      rw [iteratedFDeriv_sub (hf.1.of_le (by exact_mod_cast hjM)) (hSf.of_le (by simp)), ← hconv]
      rw [iteratedFDeriv_liftConvolution_eq_liftConvolution_iteratedFDeriv hKR
        (hf.1.of_le (by exact_mod_cast hjM)) (fun n => spatialSupNorm (iteratedFDeriv ℝ n f))
        (fun n hn => norm_le_spatialSupNorm (hf.2 n (hn.trans hjM)).1)]
    rw [hderiv]
    exact ⟨htail.1, htail.2.1, htail.2.2.trans (mul_le_mul_of_nonneg_left hnorm hA)⟩
  refine ⟨⟨(hf.1.of_le ?_).sub (hSf.of_le (by simp)), fun j hj => ⟨(hlevels j hj).1,
    (hlevels j hj).2.1⟩⟩, ?_⟩
  · exact_mod_cast Nat.le_add_right s k
  change spatialHolderHalfNorm s R ≤ cutoffHolderTailUniformConstant K (s + k) * (Λ⁻¹) ^ k * N
  have hsum : spatialHolderHalfNorm s R ≤ (s + 1 : ℝ) * (A * N) := by
    unfold spatialHolderHalfNorm
    calc
      _ ≤ ∑ _ ∈ Finset.range (s + 1), A * N :=
        Finset.sum_le_sum fun j hj => (hlevels j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).2.2
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have hC := cutoffHolderTailConstant_le K (M := s + k) (Nat.le_add_left k s)
  have hspan : (s + 1 : ℝ) ≤ (s + k : ℕ) + 1 := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hsum_nonneg : 0 ≤ 1 + ∑ i ∈ Finset.range (s + k + 1), cutoffKernelAbsoluteMoment K i :=
    add_nonneg zero_le_one (Finset.sum_nonneg fun i _ => cutoffKernelAbsoluteMoment_nonneg K i)
  refine hsum.trans ?_
  unfold cutoffHolderTailUniformConstant
  dsimp only [A]
  calc
    _ = ((s + 1 : ℝ) * cutoffHolderTailConstant K k) * (Λ⁻¹) ^ k * N := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul hspan hC (cutoffHolderTailConstant_nonneg K k) (by positivity)) hΛinv) hN

/-- Appendix B.1's tail estimate for (0 \le s \le M), in spatial
(C^{s,1/2}) norms on periodic lifts. The constant depends only on the input
order and the fixed cutoff symbol. -/
theorem spatialHolderHalfNorm_cutoffTail
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) {Λ : ℝ} (hΛ : 0 < Λ)
    (g : C(UnitAddTorus (Fin 3), E)) {M s : ℕ} (hsM : s ≤ M)
    (hf : SpatialHolderHalf M (fun x => g (toUnitTorus x))) :
    let f : Vec3 → E := fun x => g (toUnitTorus x)
    let R : Vec3 → E := f - fun x => smoothFourierCutoff ψ Λ g (toUnitTorus x)
    SpatialHolderHalf s R ∧
      spatialHolderHalfNorm s R ≤ cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) M *
        Λ ^ ((s : ℤ) - M) * spatialHolderHalfNorm M f := by
  let k := M - s
  have hM : s + k = M := by omega
  have hpow : ((s : ℤ) - M) = -(k : ℤ) := by omega
  have h := spatialHolderHalfNorm_cutoffTail_add hψ hs hunit hΛ g s k (hM.symm ▸ hf)
  rw [hpow, zpow_neg, zpow_natCast, ← inv_pow]
  simpa only [hM] using h

end CutoffTail

end

end TorusEuler
