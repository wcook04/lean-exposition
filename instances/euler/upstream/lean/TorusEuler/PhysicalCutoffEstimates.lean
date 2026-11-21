import TorusEuler.FourierHolderTail
import TorusEuler.PeriodicLerayReal
import TorusEuler.PeriodicLift
import TorusEuler.WaveDivergence
import Mathlib.Topology.MetricSpace.Thickening

/-!
The effect of the frequency cutoff from Appendix B.1 on a localized
Eulerian oscillation, including outside its transported support.
-/

open Filter LineDeriv MeasureTheory Set Topology UnitAddTorus
open scoped ContDiff NNReal SchwartzMap Topology

namespace TorusEuler

private theorem isQuotientMap_toUnitTorus : IsQuotientMap toUnitTorus := by
  let c : (Fin 3 → ℝ) → UnitAddTorus (Fin 3) :=
    Pi.map (fun _ : Fin 3 => fun x : ℝ => (x : UnitAddCircle))
  have hc : IsOpenQuotientMap c :=
    IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  let e := PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)
  change IsQuotientMap (c ∘ e)
  exact hc.isQuotientMap.comp e.isQuotientMap

/-- A continuous spatially periodic lift descends to a continuous torus field. -/
theorem SpatiallyPeriodic.exists_continuousTorusFunction {E : Type*} [TopologicalSpace E]
    {f : Vec3 → E} (hper : SpatiallyPeriodic f) (hf : Continuous f) :
    ∃ g : C(UnitAddTorus (Fin 3), E), ∀ x, g (toUnitTorus x) = f x := by
  obtain ⟨g, hg, _⟩ := hper.existsUnique_torusFunction
  have hcomp : g ∘ toUnitTorus = f := funext hg
  refine ⟨⟨g, isQuotientMap_toUnitTorus.continuous_iff.mpr ?_⟩, hg⟩
  rw [hcomp]
  exact hf

section KernelMoments

private theorem iteratedFDeriv_scaledLiftKernel_apply {Λ : ℝ} (K : 𝓢(Vec3, ℂ))
    {m : ℕ} (v : Fin m → Vec3) (y : Vec3) :
    iteratedFDeriv ℝ m (scaledLiftKernel Λ (K : Vec3 → ℂ)) y v =
      Λ ^ m • scaledLiftKernel Λ (fun z => iteratedFDeriv ℝ m (K : Vec3 → ℂ) z v) y := by
  have hc : ContDiff ℝ m (fun z : Vec3 => K (Λ • z)) := (K.smooth m).comp (by fun_prop)
  unfold scaledLiftKernel
  rw [iteratedFDeriv_const_smul_apply' hc.contDiffAt, iteratedFDeriv_comp_const_smul Λ (K.smooth m)]
  simp only [smul_apply, smul_comm (Λ ^ (3 : ℕ))]

/-- Adding a spatial derivative multiplies the kernel moment by the cutoff
scale, while adding a distance power divides it by the same scale. -/
theorem integral_norm_pow_iteratedFDeriv_scaledLiftKernel {Λ : ℝ} (hΛ : 0 < Λ)
    (K : 𝓢(Vec3, ℂ)) {m : ℕ} (v : Fin m → Vec3) (N : ℕ) :
    (∫ y, ‖y‖ ^ N * ‖iteratedFDeriv ℝ m (scaledLiftKernel Λ (K : Vec3 → ℂ)) y v‖) =
      Λ ^ m * (Λ⁻¹) ^ N * ∫ y, ‖y‖ ^ N * ‖iteratedFDeriv ℝ m (K : Vec3 → ℂ) y v‖ := by
  simp_rw [iteratedFDeriv_scaledLiftKernel_apply K v, norm_smul,
    Real.norm_of_nonneg (pow_nonneg hΛ.le m), mul_left_comm (_ ^ N) (Λ ^ m)]
  rw [integral_const_mul, integral_norm_pow_scaledLiftKernel hΛ]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem norm_liftConvolution_of_zero_ball_le
    {K : Vec3 → ℂ} {f : Vec3 → E} {x : Vec3} {d M : ℝ} (hd : 0 < d)
    (hM : ∀ z, ‖f z‖ ≤ M) (hzero : ∀ z, dist x z < d → f z = 0)
    {N : ℕ} (hK : Integrable (fun y => ‖y‖ ^ N * ‖K y‖)) :
    ‖liftConvolution K f x‖ ≤ (d⁻¹) ^ N * (∫ y, ‖y‖ ^ N * ‖K y‖) * M := by
  have hM₀ : 0 ≤ M := (norm_nonneg (f x)).trans (hM x)
  have hpoint (y : Vec3) :
      ‖K y • f (x - y)‖ ≤ (d⁻¹) ^ N * (‖y‖ ^ N * ‖K y‖) * M := by
    by_cases hy : ‖y‖ < d
    · have hdist : dist x (x - y) < d := by
        rwa [dist_eq_norm, sub_sub_cancel]
      rw [hzero (x - y) hdist, smul_zero, norm_zero]
      positivity
    · have hpow : 1 ≤ (d⁻¹) ^ N * ‖y‖ ^ N := by
        rw [← mul_pow]
        apply one_le_pow₀
        rw [mul_comm, ← div_eq_mul_inv, one_le_div hd]
        exact le_of_not_gt hy
      calc
        ‖K y • f (x - y)‖ ≤ ‖K y‖ * M := by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (hM (x - y)) (norm_nonneg _)
        _ ≤ ((d⁻¹) ^ N * ‖y‖ ^ N) * ‖K y‖ * M :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (norm_nonneg _) hpow) hM₀
        _ = _ := by ring
  unfold liftConvolution
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul, ← integral_mul_const]
  exact integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
    ((hK.const_mul _).mul_const _) (Eventually.of_forall hpoint)

end KernelMoments

section PeriodicCutoff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The Bernstein bound for the actual cutoff of a bounded continuous
periodic field, with the undilated kernel constant. -/
theorem norm_iteratedFDeriv_lift_cutoff_le
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    {Λ : ℝ} (hΛ : 0 < Λ) (g : C(UnitAddTorus (Fin 3), E)) {M : ℝ}
    (hM : ∀ z, ‖g (toUnitTorus z)‖ ≤ M) {m : ℕ} (v : Fin m → Vec3) (x : Vec3) :
    ‖iteratedFDeriv ℝ m (fun z => smoothFourierCutoff ψ Λ g (toUnitTorus z)) x v‖ ≤
      Λ ^ m * (∫ y, ‖iteratedFDeriv ℝ m
        (cutoffSchwartzKernel hψ hs : Vec3 → ℂ) y v‖) * M := by
  let K := cutoffSchwartzKernel hψ hs
  let KR := scaledSchwartzKernel Λ hΛ.ne' K
  let DK := ∂^{v} KR
  have heq : (fun y => iteratedFDeriv ℝ m (scaledLiftKernel Λ (K : Vec3 → ℂ)) y v) =
      (DK : Vec3 → ℂ) := by
    funext y
    change iteratedFDeriv ℝ m (KR : Vec3 → ℂ) y v = (∂^{v} KR) y
    exact SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv.symm
  rw [iteratedFDeriv_liftConvolution_cutoffSchwartzKernel hψ hs hΛ]
  change ‖liftConvolution (fun y => iteratedFDeriv ℝ m (scaledLiftKernel Λ (K : Vec3 → ℂ)) y v)
    (fun z => g (toUnitTorus z)) x‖ ≤ _
  have h := norm_liftConvolution_le DK.integrable hM x
  rw [← heq, integral_norm_iteratedFDeriv_scaledLiftKernel hΛ] at h
  exact h

/-- At positive distance from the original support, every fixed derivative
of the frequency cutoff decays by any prescribed power of distance times
cutoff scale. Only the supremum of the original field enters the bound. -/
theorem norm_iteratedFDeriv_lift_cutoff_of_zero_ball_le
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    {Λ : ℝ} (hΛ : 0 < Λ) (g : C(UnitAddTorus (Fin 3), E)) {x : Vec3} {d M : ℝ}
    (hd : 0 < d) (hM : ∀ z, ‖g (toUnitTorus z)‖ ≤ M)
    (hzero : ∀ z, dist x z < d → g (toUnitTorus z) = 0)
    {m : ℕ} (v : Fin m → Vec3) (N : ℕ) :
    ‖iteratedFDeriv ℝ m (fun z => smoothFourierCutoff ψ Λ g (toUnitTorus z)) x v‖ ≤
      Λ ^ m * (Λ⁻¹) ^ N * (d⁻¹) ^ N * (∫ y, ‖y‖ ^ N * ‖iteratedFDeriv ℝ m
        (cutoffSchwartzKernel hψ hs : Vec3 → ℂ) y v‖) * M := by
  let K := cutoffSchwartzKernel hψ hs
  let KR := scaledSchwartzKernel Λ hΛ.ne' K
  let DK := ∂^{v} KR
  have heq : (fun y => iteratedFDeriv ℝ m (scaledLiftKernel Λ (K : Vec3 → ℂ)) y v) =
      (DK : Vec3 → ℂ) := by
    funext y
    change iteratedFDeriv ℝ m (KR : Vec3 → ℂ) y v = (∂^{v} KR) y
    exact SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv.symm
  rw [iteratedFDeriv_liftConvolution_cutoffSchwartzKernel hψ hs hΛ]
  change ‖liftConvolution (fun y => iteratedFDeriv ℝ m (scaledLiftKernel Λ (K : Vec3 → ℂ)) y v)
    (fun z => g (toUnitTorus z)) x‖ ≤ _
  have h := norm_liftConvolution_of_zero_ball_le hd hM hzero (DK.integrable_pow_mul volume N)
  rw [← heq, integral_norm_pow_iteratedFDeriv_scaledLiftKernel hΛ] at h
  convert h using 1
  ring

/-- On a set with a common positive distance from the support, any fixed
spatial derivative of the cut-off field converges uniformly to zero. -/
theorem tendstoUniformlyOn_iteratedFDeriv_lift_cutoff_offSupport
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (g : C(UnitAddTorus (Fin 3), E)) {S : Set Vec3} {d M : ℝ} (hd : 0 < d)
    (hM : ∀ z, ‖g (toUnitTorus z)‖ ≤ M)
    (hzero : ∀ x ∈ S, ∀ z, dist x z < d → g (toUnitTorus z) = 0)
    {m : ℕ} (v : Fin m → Vec3) :
    TendstoUniformlyOn (fun Λ x =>
      iteratedFDeriv ℝ m (fun z => smoothFourierCutoff ψ Λ g (toUnitTorus z)) x v)
      (fun _ => 0) atTop S := by
  let C := (d⁻¹) ^ (m + 1) * (∫ y, ‖y‖ ^ (m + 1) * ‖iteratedFDeriv ℝ m
    (cutoffSchwartzKernel hψ hs : Vec3 → ℂ) y v‖) * M
  have hdecay : Tendsto (fun Λ : ℝ => Λ⁻¹ * C) atTop (𝓝 0) := by
    simpa only [zero_mul] using tendsto_inv_atTop_zero.mul_const C
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  filter_upwards [Metric.tendsto_nhds.1 hdecay ε hε, eventually_gt_atTop (0 : ℝ)] with Λ hsmall hΛ
  intro x hx
  rw [dist_comm, dist_zero_right]
  have hscale : Λ ^ m * (Λ⁻¹) ^ (m + 1) = Λ⁻¹ := by
    rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hΛ.ne', one_pow, one_mul]
  have h := norm_iteratedFDeriv_lift_cutoff_of_zero_ball_le hψ hs hΛ g hd hM (hzero x hx) v (m + 1)
  rw [hscale] at h
  calc
    _ ≤ _ := h
    _ = Λ⁻¹ * C := by dsimp only [C]; ring
    _ ≤ |Λ⁻¹ * C| := le_abs_self _
    _ < ε := by simpa only [Real.dist_eq, sub_zero] using hsmall

end PeriodicCutoff

section LocalizedProfiles

open scoped InnerProductSpace

private theorem centeredLabel_add_floorLattice (a : Vec3) :
    centeredLabel a + latticeVector (fun i => ⌊a i + (1 / 2 : ℝ)⌋) = a := by
  refine PiLp.ext fun i => ?_
  change Int.fract (a i + 1 / 2) - 1 / 2 + (⌊a i + 1 / 2⌋ : ℝ) = a i
  rw [Int.fract]
  ring

/-- A centered label ball of radius `r` is transported inside the union of
lattice translates of the ball of radius `L * r`. The forward flow is
`L`-Lipschitz, fixes the lifted origin, and inverts the label map. This is the
support estimate used in the new velocity step of Theorem 7.1. -/
theorem localizedTransportedProfile_eq_zero_of_lattice_separation
    {F : Type*} [Zero F] {A : Velocity} {k : Vec3} {t : ℝ} {f : ℝ → Vec3 → ℝ → F}
    {X : Vec3 → Vec3} (hInv : Function.LeftInverse X (A t))
    (hXper : ∀ n : Fin 3 → ℤ, ∀ a, X (a + latticeVector n) = X a + latticeVector n)
    (hX₀ : X 0 = 0) {L : ℝ≥0} (hL : LipschitzWith L X) {r : ℝ}
    (hf : ∀ a, r < ‖a‖ → f t a ⟪k, a⟫_ℝ = 0)
    (x : Vec3) (hx : ∀ n : Fin 3 → ℤ, (L : ℝ) * r < dist x (latticeVector n)) :
    localizedTransportedProfile A k f t x = 0 := by
  let a := centeredLabel (A t x)
  let n : Fin 3 → ℤ := fun i => ⌊A t x i + (1 / 2 : ℝ)⌋
  have hlabel : a + latticeVector n = A t x := centeredLabel_add_floorLattice _
  have hpos : X a + latticeVector n = x := by
    rw [← hXper, hlabel, hInv]
  have hdist : dist x (latticeVector n) = ‖X a‖ := by
    rw [← hpos, dist_eq_norm, add_sub_cancel_right]
  have hLip := hL.dist_le_mul a 0
  simp only [hX₀, dist_zero_right] at hLip
  have ha : r < ‖a‖ := by
    by_contra! hb
    exact (not_le_of_gt (hx n)) (hdist.trans_le
      (hLip.trans (mul_le_mul_of_nonneg_left hb L.coe_nonneg)))
  exact hf a ha

/-- The centered-cell construction in §3.1 gives a continuous torus input
for the actual frequency cutoff, for arbitrary real phase vector. -/
theorem exists_continuousTorusFunction_localizedTransportedProfile
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Velocity} {k : Vec3} {t : ℝ} {f : ℝ → Vec3 → ℝ → E}
    (hAper : ∀ n : Fin 3 → ℤ, ∀ x, A t (x + latticeVector n) = A t x + latticeVector n)
    (hA : Continuous (A t)) (hf : Continuous (fun a => f t a ⟪k, a⟫_ℝ))
    {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1 / 2)
    (hsupp : ∀ a, r < ‖a‖ → f t a ⟪k, a⟫_ℝ = 0) :
    ∃ g : C(UnitAddTorus (Fin 3), E), ∀ x,
      g (toUnitTorus x) = localizedTransportedProfile A k f t x := by
  apply (spatiallyPeriodic_localizedTransportedProfile hAper k f).exists_continuousTorusFunction
  let δ := (1 / 2 : ℝ) - r
  have hδ : 0 < δ := sub_pos.mpr hr'
  have hδ' : δ ≤ 1 / 2 := sub_le_self _ hr
  have hcollar (a : Vec3) (ha : ∃ i : Fin 3, 1 / 2 - δ < |a i|) : f t a ⟪k, a⟫_ℝ = 0 := by
    obtain ⟨i, hi⟩ := ha
    have hcoord : |a i| ≤ ‖a‖ := PiLp.norm_apply_le a i
    have heq : (1 / 2 : ℝ) - δ = r := by simp [δ]
    rw [heq] at hi
    exact hsupp a (hi.trans_le hcoord)
  exact (contDiff_localizedTransportedProfile (contDiff_zero.mpr hA) hδ hδ'
    (contDiff_zero.mpr hf) hcollar).continuous

/-- A compact part of the punctured lift is uniformly separated from all
integer translates of the origin. -/
theorem exists_lattice_separation_of_isCompact_offOrigin {S : Set Vec3}
    (hS : IsCompact S) (hSoff : S ⊆ offOrigin) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ S, ∀ n : Fin 3 → ℤ, ρ ≤ dist x (latticeVector n) := by
  obtain ⟨ρ, hρ, hsub⟩ := hS.exists_thickening_subset_open isOpen_offOrigin hSoff
  refine ⟨ρ, hρ, fun x hx n => le_of_not_gt fun hn => ?_⟩
  have hnear : latticeVector n ∈ Metric.thickening ρ S := Metric.mem_thickening_iff.2
    ⟨x, hx, by rwa [dist_comm]⟩
  exact hsub hnear (mem_range_self n)

/-- The localized Eulerian profile in §3.1 has a Fourier cutoff whose spatial
derivatives converge uniformly to zero on every set beyond its transported
support radius, with a positive separation. This is the separation used
before the off-origin convergence argument in Proposition 8.4. -/
theorem tendstoUniformlyOn_iteratedFDeriv_cutoff_localizedTransportedProfile
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {A : Velocity} {k : Vec3} {t : ℝ} {f : ℝ → Vec3 → ℝ → E}
    {X : Vec3 → Vec3} (hInv : Function.LeftInverse X (A t))
    (hXper : ∀ n : Fin 3 → ℤ, ∀ a, X (a + latticeVector n) = X a + latticeVector n)
    (hX₀ : X 0 = 0) {L : ℝ≥0} (hL : LipschitzWith L X) {r : ℝ}
    (hf : ∀ a, r < ‖a‖ → f t a ⟪k, a⟫_ℝ = 0)
    (g : C(UnitAddTorus (Fin 3), E))
    (hg : ∀ x, g (toUnitTorus x) = localizedTransportedProfile A k f t x)
    {S : Set Vec3} {d : ℝ} (hd : 0 < d)
    (hsep : ∀ x ∈ S, ∀ n : Fin 3 → ℤ, (L : ℝ) * r + d ≤ dist x (latticeVector n))
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    {m : ℕ} (v : Fin m → Vec3) :
    TendstoUniformlyOn (fun Λ x =>
      iteratedFDeriv ℝ m (fun z => smoothFourierCutoff ψ Λ g (toUnitTorus z)) x v)
      (fun _ => 0) atTop S := by
  apply tendstoUniformlyOn_iteratedFDeriv_lift_cutoff_offSupport hψ hs g hd
    (fun z => g.norm_coe_le_norm (toUnitTorus z)) _ v
  intro x hx z hz
  rw [hg]
  refine localizedTransportedProfile_eq_zero_of_lattice_separation hInv hXper hX₀ hL hf z fun n => ?_
  have htriangle := dist_triangle x z (latticeVector n)
  linarith [hsep x hx n]

end LocalizedProfiles

section RealCutoff

private theorem norm_cutoff_complexify (x : Vec3) :
    ‖periodicComplexifyVector x‖ = ‖x‖ := by
  simp only [EuclideanSpace.norm_eq, periodicComplexifyVector_apply, Complex.norm_real]

private theorem norm_cutoff_realPart (x : ComplexEuclideanVec3) :
    ‖periodicRealPartVector x‖ ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  rw [periodicRealPartVector_apply]
  exact pow_le_pow_left₀ (norm_nonneg _) (Complex.abs_re_le_norm (x i)) _

private noncomputable def complexifyCutoffInput (g : C(UnitAddTorus (Fin 3), Vec3)) :
    C(UnitAddTorus (Fin 3), ComplexEuclideanVec3) :=
  ⟨fun z => periodicComplexifyVector (g z), periodicComplexifyVector.continuous.comp g.continuous⟩

/-- The Fourier cutoff on real Euclidean vector fields, obtained by complex
Fourier synthesis followed by the coordinatewise real projection. -/
noncomputable def realVectorFourierCutoff (ψ : Vec3 → ℝ) (Λ : ℝ)
    (g : C(UnitAddTorus (Fin 3), Vec3)) (z : UnitAddTorus (Fin 3)) : Vec3 :=
  periodicRealPartVector (smoothFourierCutoff ψ Λ (complexifyCutoffInput g) z)

private theorem iteratedFDeriv_realVectorFourierCutoff (ψ : Vec3 → ℝ) (Λ : ℝ)
    (g : C(UnitAddTorus (Fin 3), Vec3)) (m : ℕ) (v : Fin m → Vec3) (x : Vec3) :
    iteratedFDeriv ℝ m (fun z => realVectorFourierCutoff ψ Λ g (toUnitTorus z)) x v =
      periodicRealPartVector (iteratedFDeriv ℝ m
        (fun z => smoothFourierCutoff ψ Λ (complexifyCutoffInput g) (toUnitTorus z)) x v) := by
  let fc (z : Vec3) := smoothFourierCutoff ψ Λ (complexifyCutoffInput g) (toUnitTorus z)
  have hc : ContDiff ℝ ∞ fc := contDiff_lift_smoothFourierCutoff ψ Λ _
  change iteratedFDeriv ℝ m (periodicRealPartVector ∘ fc) x v = _
  rw [periodicRealPartVector.iteratedFDeriv_comp_left hc.contDiffAt (by simp)]
  rfl

/-- The directional Bernstein estimate for the real truncated velocity. -/
theorem norm_iteratedFDeriv_realVectorFourierCutoff_le
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    {Λ : ℝ} (hΛ : 0 < Λ) (g : C(UnitAddTorus (Fin 3), Vec3)) {M : ℝ}
    (hM : ∀ z, ‖g (toUnitTorus z)‖ ≤ M) {m : ℕ} (v : Fin m → Vec3) (x : Vec3) :
    ‖iteratedFDeriv ℝ m (fun z => realVectorFourierCutoff ψ Λ g (toUnitTorus z)) x v‖ ≤
      Λ ^ m * (∫ y, ‖iteratedFDeriv ℝ m
        (cutoffSchwartzKernel hψ hs : Vec3 → ℂ) y v‖) * M := by
  rw [iteratedFDeriv_realVectorFourierCutoff]
  exact (norm_cutoff_realPart _).trans (norm_iteratedFDeriv_lift_cutoff_le hψ hs hΛ
    (complexifyCutoffInput g) (fun z => by simpa [complexifyCutoffInput, norm_cutoff_complexify] using hM z) v x)

/-- The off-support decay estimate for the real truncated velocity. -/
theorem norm_iteratedFDeriv_realVectorFourierCutoff_of_zero_ball_le
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    {Λ : ℝ} (hΛ : 0 < Λ) (g : C(UnitAddTorus (Fin 3), Vec3)) {x : Vec3} {d M : ℝ}
    (hd : 0 < d) (hM : ∀ z, ‖g (toUnitTorus z)‖ ≤ M)
    (hzero : ∀ z, dist x z < d → g (toUnitTorus z) = 0)
    {m : ℕ} (v : Fin m → Vec3) (N : ℕ) :
    ‖iteratedFDeriv ℝ m (fun z => realVectorFourierCutoff ψ Λ g (toUnitTorus z)) x v‖ ≤
      Λ ^ m * (Λ⁻¹) ^ N * (d⁻¹) ^ N * (∫ y, ‖y‖ ^ N * ‖iteratedFDeriv ℝ m
        (cutoffSchwartzKernel hψ hs : Vec3 → ℂ) y v‖) * M := by
  rw [iteratedFDeriv_realVectorFourierCutoff]
  refine (norm_cutoff_realPart _).trans (norm_iteratedFDeriv_lift_cutoff_of_zero_ball_le hψ hs hΛ
    (complexifyCutoffInput g) hd (fun z => ?_) (fun z hz => ?_) v N)
  · simpa [complexifyCutoffInput, norm_cutoff_complexify] using hM z
  · simp [complexifyCutoffInput, hzero z hz]

private theorem spatialHolderHalf_comp_contraction
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : ∀ a, ‖L a‖ ≤ ‖a‖)
    {f : Vec3 → E} {m : ℕ} (hf : SpatialHolderHalf m f) :
    SpatialHolderHalf m (L ∘ f) ∧
      spatialHolderHalfNorm m (L ∘ f) ≤ spatialHolderHalfNorm m f := by
  have hnorm : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun a => by simpa only [one_mul] using hL a)
  have hjets (j : ℕ) (hj : j ≤ m) (x : Vec3) :
      iteratedFDeriv ℝ j (L ∘ f) x = L.compContinuousMultilinearMap (iteratedFDeriv ℝ j f x) :=
    L.iteratedFDeriv_comp_left hf.1.contDiffAt (by exact_mod_cast hj)
  have hmap (j : ℕ) (q : Vec3 [×j]→L[ℝ] E) :
      ‖L.compContinuousMultilinearMap q‖ ≤ ‖q‖ :=
    (L.norm_compContinuousMultilinearMap_le q).trans
      (mul_le_of_le_one_left (norm_nonneg _) hnorm)
  have hpoint (j : ℕ) (hj : j ≤ m) (x : Vec3) :
      ‖iteratedFDeriv ℝ j (L ∘ f) x‖ ≤ ‖iteratedFDeriv ℝ j f x‖ := by
    rw [hjets j hj]
    exact hmap _ _
  have hinc (j : ℕ) (hj : j ≤ m) (p : Vec3 × Vec3) :
      spatialHolderHalfQuotient (iteratedFDeriv ℝ j (L ∘ f)) p ≤
        spatialHolderHalfQuotient (iteratedFDeriv ℝ j f) p := by
    unfold spatialHolderHalfQuotient
    rw [hjets j hj, hjets j hj]
    let T := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => Vec3) E F L
    change ‖T (iteratedFDeriv ℝ j f (p.1 + p.2)) - T (iteratedFDeriv ℝ j f p.1)‖ /
      Real.sqrt ‖p.2‖ ≤ _
    rw [← map_sub]
    exact div_le_div_of_nonneg_right (hmap _ _) (Real.sqrt_nonneg _)
  have hsup (j : ℕ) (hj : j ≤ m) (x : Vec3) :
      ‖iteratedFDeriv ℝ j (L ∘ f) x‖ ≤ spatialSupNorm (iteratedFDeriv ℝ j f) :=
    (hpoint j hj x).trans (norm_le_spatialSupNorm (hf.2 j hj).1 x)
  have hsemi (j : ℕ) (hj : j ≤ m) (p : Vec3 × Vec3) :
      spatialHolderHalfQuotient (iteratedFDeriv ℝ j (L ∘ f)) p ≤
        spatialHolderHalfSeminorm (iteratedFDeriv ℝ j f) :=
    (hinc j hj p).trans (le_ciSup (hf.2 j hj).2 p)
  constructor
  · exact ⟨L.contDiff.comp hf.1, fun j hj =>
      ⟨⟨_, forall_mem_range.mpr (hsup j hj)⟩, ⟨_, forall_mem_range.mpr (hsemi j hj)⟩⟩⟩
  · unfold spatialHolderHalfNorm
    apply Finset.sum_le_sum
    intro j hj
    have hj' : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    exact add_le_add (ciSup_le (hsup j hj')) (ciSup_le (hsemi j hj'))

/-- The real velocity cutoff error in the first bound of (5.56), with the
Appendix B tail constant. -/
theorem spatialHolderHalfNorm_realVectorCutoffTail
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) {Λ : ℝ} (hΛ : 0 < Λ)
    (g : C(UnitAddTorus (Fin 3), Vec3)) {M s : ℕ} (hsM : s ≤ M)
    (hf : SpatialHolderHalf M (fun x => g (toUnitTorus x))) :
    let f : Vec3 → Vec3 := fun x => g (toUnitTorus x)
    let R : Vec3 → Vec3 := f - fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)
    SpatialHolderHalf s R ∧
      spatialHolderHalfNorm s R ≤ cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) M *
        Λ ^ ((s : ℤ) - M) * spatialHolderHalfNorm M f := by
  let f : Vec3 → Vec3 := fun x => g (toUnitTorus x)
  let gc := complexifyCutoffInput g
  let R : Vec3 → Vec3 := f - fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)
  let Rc : Vec3 → ComplexEuclideanVec3 :=
    (fun x => gc (toUnitTorus x)) - fun x => smoothFourierCutoff ψ Λ gc (toUnitTorus x)
  have hc := spatialHolderHalf_comp_contraction periodicComplexifyVector
    (fun x => (norm_cutoff_complexify x).le) hf
  change SpatialHolderHalf M (fun x => gc (toUnitTorus x)) ∧
    spatialHolderHalfNorm M (fun x => gc (toUnitTorus x)) ≤ spatialHolderHalfNorm M f at hc
  have htail := spatialHolderHalfNorm_cutoffTail hψ hs hunit hΛ gc hsM hc.1
  have hr := spatialHolderHalf_comp_contraction periodicRealPartVector norm_cutoff_realPart htail.1
  have heq : periodicRealPartVector ∘ Rc = R := by
    funext x
    change periodicRealPartVector
      (periodicComplexifyVector (f x) - smoothFourierCutoff ψ Λ gc (toUnitTorus x)) = _
    rw [map_sub]
    congr 1
  change SpatialHolderHalf s (periodicRealPartVector ∘ Rc) ∧ _ at hr
  rw [heq] at hr
  have hC : 0 ≤ cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) M := by
    unfold cutoffHolderTailUniformConstant cutoffKernelAbsoluteMoment
    positivity
  exact ⟨hr.1, hr.2.trans (htail.2.trans
    (mul_le_mul_of_nonneg_left hc.2 (mul_nonneg hC (zpow_nonneg hΛ.le _))))⟩

end RealCutoff

end TorusEuler
