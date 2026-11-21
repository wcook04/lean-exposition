import TorusEuler.EndpointPressureRecovery
import TorusEuler.PeriodicLift
import TorusEuler.PhysicalCutoffEstimates
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
The real frequency truncation in Proposition 5.11 and the next parent
conditions in (T1) of Theorem 7.1.
-/

open Filter MeasureTheory Set UnitAddTorus
open scoped ComplexConjugate ContDiff InnerProductSpace Topology

namespace TorusEuler

noncomputable section

private theorem mFourierCoeff_cutoff_comp_coord {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    (L : E →L[ℂ] ℂ) (g : C(UnitAddTorus (Fin 3), E)) (k : Fin 3 → ℤ) :
    mFourierCoeff (fun z => L (g z)) k = L (mFourierCoeff g k) := by
  have hcont : Continuous (fun z => mFourier (-k) z • g z) :=
    (mFourier (-k)).continuous.smul g.continuous
  have hint : Integrable (fun z => mFourier (-k) z • g z) unitTorusMeasure := by
    simpa only [integrableOn_univ] using
      hcont.continuousOn.integrableOn_compact (μ := unitTorusMeasure) isCompact_univ
  change (∫ z, mFourier (-k) z • L (g z) ∂unitTorusMeasure) =
    L (∫ z, mFourier (-k) z • g z ∂unitTorusMeasure)
  rw [← L.integral_comp_comm hint]
  simp only [map_smul]

private theorem smoothFourierCutoff_comp_coord {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    (L : E →L[ℂ] ℂ) (g : C(UnitAddTorus (Fin 3), E))
    (ψ : Vec3 → ℝ) (Λ : ℝ) (z : UnitAddTorus (Fin 3)) :
    L (smoothFourierCutoff ψ Λ g z) = smoothFourierCutoff ψ Λ (fun a => L (g a)) z := by
  unfold smoothFourierCutoff finiteFourierSum
  simp only [map_sum, map_smul, ContinuousLinearMap.map_smul_of_tower,
    mFourierCoeff_cutoff_comp_coord]

/-- Complexification followed by real projection recovers the original vector. -/
theorem periodicRealPartVector_complexifyVector (v : Vec3) :
    periodicRealPartVector (periodicComplexifyVector v) = v := by
  apply PiLp.ext
  intro i
  rw [periodicRealPartVector_apply, periodicComplexifyVector_apply, Complex.ofReal_re]

/-- For the even symbol of Appendix B.1, complex Fourier synthesis of real
vector data has real coordinates at every point. -/
theorem complexify_realPart_smoothFourierCutoff_of_even
    {ψ : Vec3 → ℝ} (hψ : Function.Even ψ) (Λ : ℝ)
    (g : C(UnitAddTorus (Fin 3), Vec3)) (z : UnitAddTorus (Fin 3)) :
    periodicComplexifyVector
        (periodicRealPartVector (smoothFourierCutoff ψ Λ (endpointComplexifyContinuous g) z)) =
      smoothFourierCutoff ψ Λ (endpointComplexifyContinuous g) z := by
  apply PiLp.ext
  intro i
  rw [periodicComplexifyVector_apply, periodicRealPartVector_apply]
  let L : ComplexEuclideanVec3 →L[ℂ] ℂ := EuclideanSpace.proj i
  change (L (smoothFourierCutoff ψ Λ (endpointComplexifyContinuous g) z)).re =
    L (smoothFourierCutoff ψ Λ (endpointComplexifyContinuous g) z)
  rw [smoothFourierCutoff_comp_coord L]
  apply Complex.conj_eq_iff_re.mp
  apply conj_smoothFourierCutoff_of_real hψ Λ _ z
  intro a
  change conj ((g a i : ℝ) : ℂ) = ((g a i : ℝ) : ℂ)
  exact Complex.conj_ofReal _

private abbrev CTorus := UnitAddTorus (Fin 3)

private theorem toUnitTorus_neg_cutoff (x : Vec3) : toUnitTorus (-x) = -toUnitTorus x := by
  funext i
  change ((-(x i) : ℝ) : UnitAddCircle) = -(x i : UnitAddCircle)
  exact AddCircle.coe_neg (p := (1 : ℝ)) (x := x i)

/-- The truncated field has a smooth spatial lift. -/
theorem contDiff_lift_realVectorFourierCutoff (ψ : Vec3 → ℝ) (Λ : ℝ) (g : C(CTorus, Vec3)) :
    ContDiff ℝ ∞ (fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)) :=
  periodicRealPartVector.contDiff.comp
    (contDiff_lift_smoothFourierCutoff ψ Λ (endpointComplexifyContinuous g))

theorem spatiallyPeriodic_lift_realVectorFourierCutoff
    (ψ : Vec3 → ℝ) (Λ : ℝ) (g : C(CTorus, Vec3)) :
    SpatiallyPeriodic (fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)) := by
  intro n x
  change realVectorFourierCutoff ψ Λ g (toUnitTorus (x + latticeVector n)) =
    realVectorFourierCutoff ψ Λ g (toUnitTorus x)
  rw [(toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩]

/-- An even cutoff symbol preserves oddness of a real lifted field. -/
theorem odd_lift_realVectorFourierCutoff {ψ : Vec3 → ℝ} (hψ : Function.Even ψ)
    (Λ : ℝ) (g : C(CTorus, Vec3))
    (hg : Function.Odd (fun x => g (toUnitTorus x))) :
    Function.Odd (fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)) := by
  have hOdd (z : CTorus) : g (-z) = -g z := by
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
    rw [← toUnitTorus_neg_cutoff]
    exact hg x
  have hc (z : CTorus) :
      endpointComplexifyContinuous g (-z) = (-1 : ℝ) • endpointComplexifyContinuous g z := by
    change periodicComplexifyVector (g (-z)) = (-1 : ℝ) • periodicComplexifyVector (g z)
    rw [hOdd, map_neg, neg_one_smul]
  intro x
  change realVectorFourierCutoff ψ Λ g (toUnitTorus (-x)) =
    -realVectorFourierCutoff ψ Λ g (toUnitTorus x)
  rw [toUnitTorus_neg_cutoff]
  change periodicRealPartVector (smoothFourierCutoff ψ Λ (endpointComplexifyContinuous g)
    (-toUnitTorus x)) = -periodicRealPartVector
      (smoothFourierCutoff ψ Λ (endpointComplexifyContinuous g) (toUnitTorus x))
  rw [smoothFourierCutoff_neg_arg hψ Λ (-1 : ℝ) hc, neg_one_smul, map_neg]

private def bundledRealVectorFourierCutoff (ψ : Vec3 → ℝ) (Λ : ℝ) (g : C(CTorus, Vec3)) :
    C(CTorus, Vec3) := by
  refine ⟨realVectorFourierCutoff ψ Λ g, periodicRealPartVector.continuous.comp ?_⟩
  unfold smoothFourierCutoff finiteFourierSum
  exact continuous_finsetSum _ fun k _ => (mFourier k).continuous.smul continuous_const

/-- Complexifying the real cutoff recovers the exact complex mode synthesis. -/
theorem complexify_realVectorFourierCutoff_of_even
    {ψ : Vec3 → ℝ} (hψ : Function.Even ψ) (Λ : ℝ) (g : C(CTorus, Vec3)) (z : CTorus) :
    periodicComplexifyVector (realVectorFourierCutoff ψ Λ g z) =
      smoothFourierCutoff ψ Λ (endpointComplexifyContinuous g) z :=
  complexify_realPart_smoothFourierCutoff_of_even hψ Λ g z

/-- The next parent has the exact cutoff coefficients on the closed band
of radius `2 * Λ` and zero coefficients outside the band. -/
theorem mFourierCoeff_realVectorFourierCutoff_of_even
    {ψ : Vec3 → ℝ} (hψ : Function.Even ψ) (Λ : ℝ) (g : C(CTorus, Vec3)) (k : Fin 3 → ℤ) :
    mFourierCoeff (fun z => periodicComplexifyVector (realVectorFourierCutoff ψ Λ g z)) k =
      if k ∈ frequencyBand (2 * Λ) then
        ψ (Λ⁻¹ • latticeVector k) • mFourierCoeff (endpointComplexifyContinuous g) k
      else 0 := by
  rw [show (fun z => periodicComplexifyVector (realVectorFourierCutoff ψ Λ g z)) =
    smoothFourierCutoff ψ Λ (endpointComplexifyContinuous g) from
      funext (complexify_realVectorFourierCutoff_of_even hψ Λ g),
    smoothFourierCutoff, mFourierCoeff_finiteFourierSum]

local instance : IsProbabilityMeasure unitTorusMeasure :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin 3 =>
    (AddCircle.haarAddCircle : Measure UnitAddCircle)))

private theorem complexifyCutoff_toLp (g : C(CTorus, Vec3)) :
    (endpointComplexifyContinuous g).toLp 2 unitTorusMeasure ℂ =
      periodicComplexifyL2 (g.toLp 2 unitTorusMeasure ℝ) := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) unitTorusMeasure
    (endpointComplexifyContinuous g),
    periodicComplexifyL2_apply_ae (g.toLp 2 unitTorusMeasure ℝ),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) unitTorusMeasure g] with z h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  rfl

private theorem periodicL2Coefficient_bundled (g : C(CTorus, ComplexEuclideanVec3)) (k : Fin 3 → ℤ) :
    periodicL2Coefficient k (g.toLp 2 unitTorusMeasure ℂ) = mFourierCoeff g k := by
  rw [periodicL2Coefficient_eq_mFourierCoeff]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) unitTorusMeasure g] with z hz
  rw [hz]

private theorem cutoff_toLp_mem_endpointSpatialSolenoidal_iff {g : C(CTorus, Vec3)}
    (hg : ContDiff ℝ ∞ (fun x => g (toUnitTorus x))) :
    g.toLp 2 unitTorusMeasure ℝ ∈ endpointSpatialSolenoidal ↔
      ∀ x, divergence (fun y => g (toUnitTorus y)) x = 0 := by
  rw [mem_endpointSpatialSolenoidal, ← endpointTorusGradientPairing_iff_divergence_free hg
    (fun _ => rfl)]
  apply forall_congr'
  intro p
  have h : (∫ a, ⟪endpointPotentialGradient p a, (g.toLp 2 unitTorusMeasure ℝ) a⟫_ℝ
      ∂unitTorusMeasure) = ∫ a, ⟪endpointPotentialGradient p a, g a⟫_ℝ ∂unitTorusMeasure := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) unitTorusMeasure g] with z hz
    rw [hz]
  rw [h]

/-- The real even cutoff preserves incompressibility on every smooth
periodic spatial slice. -/
theorem divergence_free_lift_realVectorFourierCutoff
    {ψ : Vec3 → ℝ} (hψ : Function.Even ψ) (Λ : ℝ) (g : C(CTorus, Vec3))
    (hg : ContDiff ℝ ∞ (fun x => g (toUnitTorus x)))
    (hdiv : ∀ x, divergence (fun y => g (toUnitTorus y)) x = 0) :
    ∀ x, divergence (fun y => realVectorFourierCutoff ψ Λ g (toUnitTorus y)) x = 0 := by
  have hL2 := (cutoff_toLp_mem_endpointSpatialSolenoidal_iff hg).mpr hdiv
  have hcomplex := periodicComplexifyL2_mem_solenoidal_of_endpointSpatialSolenoidal _ hL2
  rw [← complexifyCutoff_toLp, mem_periodicComplexSolenoidal_iff_coeff] at hcomplex
  let u := bundledRealVectorFourierCutoff ψ Λ g
  have hu : ContDiff ℝ ∞ (fun x => u (toUnitTorus x)) :=
    contDiff_lift_realVectorFourierCutoff ψ Λ g
  suffices huSol : u.toLp 2 unitTorusMeasure ℝ ∈ endpointSpatialSolenoidal from
    (cutoff_toLp_mem_endpointSpatialSolenoidal_iff hu).mp huSol
  rw [← periodicComplexifyL2_mem_solenoidal_iff, ← complexifyCutoff_toLp,
    mem_periodicComplexSolenoidal_iff_coeff]
  intro k
  rw [periodicL2Coefficient_bundled]
  change mFourierCoeff (fun z => periodicComplexifyVector (realVectorFourierCutoff ψ Λ g z)) k ∈
    transverseModeSpace k
  rw [mFourierCoeff_realVectorFourierCutoff_of_even hψ]
  split_ifs
  · rw [← Complex.coe_smul]
    exact (transverseModeSpace k).smul_mem _ (periodicL2Coefficient_bundled _ _ ▸ hcomplex k)
  · exact (transverseModeSpace k).zero_mem

/-- Finite Fourier synthesis with smooth coefficient paths is jointly
smooth on the slab, including its endpoints. -/
theorem contDiffOn_lift_realVectorFourierCutoff_of_coefficients
    {I : Set ℝ} (ψ : Vec3 → ℝ) (Λ : ℝ) (g : ℝ → C(CTorus, Vec3))
    (hCoeff : ∀ k ∈ frequencyBand (2 * Λ),
      ContDiffOn ℝ ∞ (fun t => mFourierCoeff (endpointComplexifyContinuous (g t)) k) I) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 => realVectorFourierCutoff ψ Λ (g p.1)
      (toUnitTorus p.2)) (I ×ˢ univ) := by
  apply periodicRealPartVector.contDiff.comp_contDiffOn
  change ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 =>
    ∑ k ∈ frequencyBand (2 * Λ), fourierMode k p.2 •
      (ψ (Λ⁻¹ • latticeVector k) • mFourierCoeff (endpointComplexifyContinuous (g p.1)) k))
    (I ×ˢ univ)
  apply ContDiffOn.sum
  intro k hk
  have hMode : ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 => fourierMode k p.2) (I ×ˢ univ) :=
    ((contDiff_fourierMode k).comp contDiff_snd).contDiffOn
  have hTerm : ContDiffOn ℝ ∞
      (fun p : ℝ × Vec3 => mFourierCoeff (endpointComplexifyContinuous (g p.1)) k) (I ×ˢ univ) :=
    (hCoeff k hk).comp contDiff_fst.contDiffOn (fun p hp => hp.1)
  exact hMode.smul (hTerm.const_smul (ψ (Λ⁻¹ • latticeVector k)))

/-- The cutoff yields (T1) from smooth coefficient paths and smooth, odd,
divergence-free input slices. -/
theorem realVectorFourierCutoff_T1_of_coefficients
    {I : Set ℝ} {ψ : Vec3 → ℝ} (hψ : Function.Even ψ) (Λ : ℝ)
    (g : ℝ → C(CTorus, Vec3))
    (hCoeff : ∀ k ∈ frequencyBand (2 * Λ),
      ContDiffOn ℝ ∞ (fun t => mFourierCoeff (endpointComplexifyContinuous (g t)) k) I)
    (hg : ∀ t ∈ I, ContDiff ℝ ∞ (fun x => g t (toUnitTorus x)))
    (hodd : ∀ t ∈ I, Function.Odd (fun x => g t (toUnitTorus x)))
    (hdiv : ∀ t ∈ I, ∀ x, divergence (fun y => g t (toUnitTorus y)) x = 0) :
    let u : Velocity := fun t x => realVectorFourierCutoff ψ Λ (g t) (toUnitTorus x)
    ContDiffOn ℝ ∞ (Function.uncurry u) (I ×ˢ univ) ∧
      ∀ t ∈ I, SpatiallyPeriodic (u t) ∧ Function.Odd (u t) ∧
        (∀ x, divergence (u t) x = 0) ∧
        ∀ k ∉ frequencyBand (2 * Λ),
          mFourierCoeff (fun z => periodicComplexifyVector (realVectorFourierCutoff ψ Λ (g t) z)) k = 0 := by
  refine ⟨contDiffOn_lift_realVectorFourierCutoff_of_coefficients ψ Λ g hCoeff, fun t ht => ?_⟩
  refine ⟨spatiallyPeriodic_lift_realVectorFourierCutoff ψ Λ (g t),
    odd_lift_realVectorFourierCutoff hψ Λ (g t) (hodd t ht),
    divergence_free_lift_realVectorFourierCutoff hψ Λ (g t) (hg t ht) (hdiv t ht),
    fun k hk => ?_⟩
  rw [mFourierCoeff_realVectorFourierCutoff_of_even hψ, ite_eq_right hk]

/-- Integration over a compact spatial cell commutes with differentiation of a
jointly continuous family of time derivatives on a closed interval. -/
theorem hasDerivWithinAt_integral_prod_Icc
    {A : Type*} [NormedAddCommGroup A] [MeasureSpace A] [BorelSpace A]
    [IsLocallyFiniteMeasure (volume : Measure A)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F D : ℝ → A → E} {a b t : ℝ} {K : Set A}
    (hK : IsCompact K) (ht : t ∈ Icc a b)
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ K))
    (hD : ContinuousOn (Function.uncurry D) (Icc a b ×ˢ K))
    (hderiv : ∀ s ∈ Icc a b, ∀ x ∈ K,
      HasDerivWithinAt (fun r => F r x) (D s x) (Icc a b) s) :
    HasDerivWithinAt (fun s => ∫ x in K, F s x) (∫ x in K, D t x) (Icc a b) t := by
  have sectionIntegrable {G : ℝ → A → E}
      (hG : ContinuousOn (Function.uncurry G) (Icc a b ×ˢ K)) {s : ℝ}
      (hs : s ∈ Icc a b) : IntegrableOn (G s) K := by
    apply ContinuousOn.integrableOn_compact hK
    exact hG.comp (continuous_const.prodMk continuous_id).continuousOn fun x hx => ⟨hs, hx⟩
  have hμ : (volume : Measure A) K < ⊤ := hK.measure_lt_top
  let m := (volume : Measure A).real K
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  let η := ε / (m + 1)
  have hdenom : 0 < m + 1 := by positivity
  have hη : 0 < η := div_pos hε hdenom
  have hηm : η * m ≤ ε := by
    dsimp [η]
    rw [div_mul_eq_mul_div, div_le_iff₀ hdenom]
    nlinarith
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hD) η hη
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds t hδ)] with s hs hst
  have pointwiseBound (x : A) (hx : x ∈ K) :
      ‖F s x - F t x - (s - t) • D t x‖ ≤ η * ‖s - t‖ := by
    have hr (r : ℝ) (hr : r ∈ Icc a b ∩ Metric.ball t δ) :
        HasDerivWithinAt (fun u => F u x - (u - t) • D t x)
          (D r x - D t x) (Icc a b ∩ Metric.ball t δ) r := by
      have hid : HasDerivWithinAt (fun u : ℝ => u - t) 1 (Icc a b) r :=
        (hasDerivWithinAt_id (s := Icc a b) (x := r)).sub_const t
      change HasDerivWithinAt ((fun u => F u x) - (fun u => (u - t) • D t x))
        (D r x - D t x) (Icc a b ∩ Metric.ball t δ) r
      simpa only [one_smul] using
        ((hderiv r hr.1 x hx).sub (hid.smul_const (D t x))).mono inter_subset_left
    have hrNorm (r : ℝ) (hr : r ∈ Icc a b ∩ Metric.ball t δ) :
        ‖D r x - D t x‖ ≤ η := by
      have hdist : dist (r, x) (t, x) < δ := by
        simpa [Prod.dist_eq, max_eq_left (dist_nonneg (x := r) (y := t))] using hr.2
      exact le_of_lt (by simpa only [Function.uncurry, dist_eq_norm] using
        (hclose (r, x) ⟨hr.1, hx⟩ (t, x) ⟨ht, hx⟩ hdist))
    have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hr hrNorm
      ((convex_Icc a b).inter (convex_ball t δ))
      ⟨ht, Metric.mem_ball_self hδ⟩ ⟨hs, hst⟩
    simpa only [sub_self, zero_smul, sub_zero, sub_right_comm] using hmean
  have hsIntegrable := sectionIntegrable hF hs
  have htIntegrable := sectionIntegrable hF ht
  have hdtIntegrable := sectionIntegrable hD ht
  have hintegral :
      (∫ x in K, F s x) - (∫ x in K, F t x) - (s - t) • (∫ x in K, D t x) =
        ∫ x in K, F s x - F t x - (s - t) • D t x := by
    symm
    calc
      (∫ x in K, F s x - F t x - (s - t) • D t x) =
          (∫ x in K, F s x - F t x) - (∫ x in K, (s - t) • D t x) :=
        integral_sub (hsIntegrable.sub htIntegrable) (hdtIntegrable.smul (s - t))
      _ = (∫ x in K, F s x) - (∫ x in K, F t x) - (s - t) • (∫ x in K, D t x) :=
        congrArg₂ (· - ·) (integral_sub hsIntegrable htIntegrable) (integral_smul (s - t) (D t))
  rw [hintegral]
  calc
    ‖∫ x in K, F s x - F t x - (s - t) • D t x‖ ≤ (η * ‖s - t‖) * m :=
      norm_setIntegral_le_of_norm_le_const hμ pointwiseBound
    _ = (η * m) * ‖s - t‖ := mul_right_comm _ _ _
    _ ≤ ε * ‖s - t‖ := mul_le_mul_of_nonneg_right hηm (norm_nonneg _)

private theorem contDiffOn_Icc_of_timeJets {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ} (hab : a < b)
    (d : ℕ → ℝ → E)
    (hd : ∀ n t, t ∈ Icc a b → HasDerivWithinAt (d n) (d (n + 1) t) (Icc a b) t) :
    ContDiffOn ℝ ∞ (d 0) (Icc a b) := by
  have hdiff (n : ℕ) : DifferentiableOn ℝ (d n) (Icc a b) :=
    fun t ht => (hd n t ht).differentiableWithinAt
  have hn (k : ℕ) : ∀ n, ContDiffOn ℝ k (d n) (Icc a b) := by
    induction k with
    | zero =>
      intro n
      simpa only [Nat.cast_zero, contDiffOn_zero] using (hdiff n).continuousOn
    | succ k ih =>
      intro n
      rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hab)]
      refine ⟨hdiff n, by simp, (ih (n + 1)).congr ?_⟩
      intro t ht
      exact (hd n t ht).derivWithin (uniqueDiffOn_Icc hab t ht)
  exact contDiffOn_infty.mpr fun k => hn k 0

private theorem exists_truncated_parent_integrand_timeJets
    {a b : ℝ} (hab : a < b) {V : ℝ → Vec3 → Vec3}
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc a b ×ˢ (univ : Set Vec3)))
    (k : Fin 3 → ℤ) :
    ∃ J : ℕ → ℝ → Vec3 → ComplexEuclideanVec3,
      (∀ t x, J 0 t x = fourierMode (-k) x • periodicComplexifyVector (V t x)) ∧
      (∀ n, ContinuousOn (Function.uncurry (J n)) (Icc a b ×ˢ centeredCell)) ∧
      (∀ n t, t ∈ Icc a b → ∀ x,
        HasDerivWithinAt (fun r => J n r x) (J (n + 1) t x) (Icc a b) t) := by
  let S : Set (ℝ × Vec3) := Icc a b ×ˢ univ
  let P := ftaylorSeriesWithin ℝ (Function.uncurry V) S
  let v (n : ℕ) : Fin n → ℝ × Vec3 := fun _ => (1, 0)
  let J (n : ℕ) (t : ℝ) (x : Vec3) := P (t,x) n (v n)
  have hT := hV.ftaylorSeriesWithin ((uniqueDiffOn_Icc hab).prod uniqueDiffOn_univ)
  have hJzero (t : ℝ) (x : Vec3) : J 0 t x = V t x := by
    simp only [J, P, ftaylorSeriesWithin, iteratedFDerivWithin_zero_apply, Function.uncurry_apply_pair]
  have hJcont (n : ℕ) : ContinuousOn (Function.uncurry (J n)) S := by
    let ev : ((ℝ × Vec3) [×n]→L[ℝ] Vec3) →L[ℝ] Vec3 :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℝ × Vec3) Vec3 (v n)
    exact ev.continuous.comp_continuousOn (hT.cont n (by simp))
  have hJderiv (n : ℕ) (t : ℝ) (ht : t ∈ Icc a b) (x : Vec3) :
      HasDerivWithinAt (fun r => J n r x) (J (n + 1) t x) (Icc a b) t := by
    let ev : ((ℝ × Vec3) [×n]→L[ℝ] Vec3) →L[ℝ] Vec3 :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℝ × Vec3) Vec3 (v n)
    have hraw : HasFDerivWithinAt (fun y => P y n) (P (t,x) (n + 1)).curryLeft S (t,x) :=
      hT.fderivWithin n (by exact_mod_cast ENat.natCast_lt_top n) (t,x) ⟨ht, mem_univ x⟩
    have hslice := hraw.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x).hasFDerivWithinAt
      (fun r hr => (show (r,x) ∈ S from ⟨hr, mem_univ x⟩))
    have heval := ev.hasFDerivAt.comp_hasFDerivWithinAt t hslice
    have heq : Fin.cons ((1 : ℝ), (0 : Vec3)) (v n) = v (n + 1) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [v]
      · simp [v]
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ev, J,
      ContinuousMultilinearMap.apply_apply, ContinuousLinearMap.inl_apply,
      ContinuousMultilinearMap.curryLeft_apply, heq] using heval.hasDerivWithinAt
  let F (n : ℕ) (t : ℝ) (x : Vec3) := fourierMode (-k) x • periodicComplexifyVector (J n t x)
  refine ⟨F, fun t x => congrArg (fun z => fourierMode (-k) x • periodicComplexifyVector z) (hJzero t x),
    fun n => ?_, fun n t ht x => ?_⟩
  · have hmode : Continuous (fun y : ℝ × Vec3 => fourierMode (-k) y.2) :=
      (contDiff_fourierMode (-k)).continuous.comp continuous_snd
    exact (hmode.continuousOn.smul
      (periodicComplexifyVector.continuous.comp_continuousOn (hJcont n))).mono
      (prod_mono_right (subset_univ centeredCell))
  · have hd := (periodicComplexifyVector.hasFDerivAt.comp_hasDerivWithinAt t
      (hJderiv n t ht x)).const_smul (fourierMode (-k) x)
    change HasDerivWithinAt (fun r => F n r x) (F (n + 1) t x) (Icc a b) t at hd
    exact hd

/-- A centered-cell Fourier coefficient of a smooth lift is smooth in time on the closed slab. -/
theorem contDiffOn_truncatedParent_fourierCoeff
    {a b : ℝ} (hab : a < b) {V : ℝ → Vec3 → Vec3}
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc a b ×ˢ (univ : Set Vec3)))
    (k : Fin 3 → ℤ) :
    ContDiffOn ℝ ∞ (fun t => ∫ x in centeredCell,
      fourierMode (-k) x • periodicComplexifyVector (V t x)) (Icc a b) := by
  obtain ⟨J, hj0, hjc, hjd⟩ := exists_truncated_parent_integrand_timeJets hab hV k
  let d (n : ℕ) (t : ℝ) := ∫ x in centeredCell, J n t x
  have hd (n : ℕ) (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt (d n) (d (n + 1) t) (Icc a b) t :=
    hasDerivWithinAt_integral_prod_Icc isCompact_centeredCell ht (hjc n) (hjc (n + 1))
      (fun r hr x _ => hjd n r hr x)
  exact (contDiffOn_Icc_of_timeJets hab d hd).congr (fun t _ => by
    change (∫ x in centeredCell, fourierMode (-k) x • periodicComplexifyVector (V t x)) =
      ∫ x in centeredCell, J 0 t x
    simp_rw [hj0])

/-- The Fourier coefficients of the descended parent field are smooth throughout the slab. -/
theorem contDiffOn_mFourierCoeff_of_truncatedParentLift
    {a b : ℝ} (hab : a < b) {V : ℝ → Vec3 → Vec3}
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc a b ×ˢ (univ : Set Vec3)))
    (g : ℝ → UnitAddTorus (Fin 3) → Vec3)
    (hrep : ∀ t ∈ Icc a b, ∀ x, g t (toUnitTorus x) = V t x) (k : Fin 3 → ℤ) :
    ContDiffOn ℝ ∞ (fun t => mFourierCoeff (fun z => periodicComplexifyVector (g t z)) k)
      (Icc a b) :=
  (contDiffOn_truncatedParent_fourierCoeff hab hV k).congr (fun t ht => by
    rw [fourierCoeff_eq_centeredCell]
    simp_rw [hrep t ht])

/-- Truncating a smooth periodic input velocity on a nondegenerate closed
time slab supplies (T1) for the next parent. The input is odd and
divergence free, and the symbol is even as in Appendix B.1. -/
theorem exists_truncatedParent_T1
    {a b : ℝ} (hab : a < b) {V : Velocity}
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc a b ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc a b, SpatiallyPeriodic (V t))
    (hodd : ∀ t ∈ Icc a b, Function.Odd (V t))
    (hdiv : ∀ t ∈ Icc a b, ∀ x, divergence (V t) x = 0)
    {ψ : Vec3 → ℝ} (hψ : Function.Even ψ) (Λ : ℝ) :
    ∃ g : ℝ → C(CTorus, Vec3), (∀ t ∈ Icc a b, ∀ x, g t (toUnitTorus x) = V t x) ∧
      let u : Velocity := fun t x => realVectorFourierCutoff ψ Λ (g t) (toUnitTorus x)
      ContDiffOn ℝ ∞ (Function.uncurry u) (Icc a b ×ˢ univ) ∧
        ∀ t ∈ Icc a b, SpatiallyPeriodic (u t) ∧ Function.Odd (u t) ∧
          (∀ x, divergence (u t) x = 0) ∧
          ∀ k ∉ frequencyBand (2 * Λ),
            mFourierCoeff (fun z => periodicComplexifyVector (realVectorFourierCutoff ψ Λ (g t) z)) k
              = 0 := by
  classical
  have hslice (t : ℝ) (ht : t ∈ Icc a b) : ContDiff ℝ ∞ (V t) := by
    have hj : ContDiff ℝ ∞ (fun x : Vec3 => (t, x)) := contDiff_const.prodMk contDiff_id
    exact contDiffOn_univ.1 (hV.comp hj.contDiffOn (fun x _ => ⟨ht, mem_univ x⟩))
  have hExists (t : ℝ) (ht : t ∈ Icc a b) :
      ∃ u : C(CTorus, Vec3), ∀ x, u (toUnitTorus x) = V t x :=
    (hper t ht).exists_continuousTorusFunction (hslice t ht).continuous
  let g (t : ℝ) : C(CTorus, Vec3) := if ht : t ∈ Icc a b then (hExists t ht).choose else 0
  have hg (t : ℝ) (ht : t ∈ Icc a b) (x : Vec3) : g t (toUnitTorus x) = V t x := by
    simp only [g, dite_eq_left ht]
    exact (hExists t ht).choose_spec x
  have hrep (t : ℝ) (ht : t ∈ Icc a b) : (fun x => g t (toUnitTorus x)) = V t :=
    funext (hg t ht)
  refine ⟨g, hg, realVectorFourierCutoff_T1_of_coefficients hψ Λ g
    (fun k _ => contDiffOn_mFourierCoeff_of_truncatedParentLift hab hV
      (fun t z => g t z) hg k) ?_ ?_ ?_⟩
  · intro t ht
    rw [hrep t ht]
    exact hslice t ht
  · intro t ht
    rw [hrep t ht]
    exact hodd t ht
  · intro t ht
    rw [hrep t ht]
    exact hdiv t ht

end

end TorusEuler
