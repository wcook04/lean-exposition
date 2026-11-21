import TorusEuler.HalfHolderFourierMultiplier
import TorusEuler.MultiplierOffSupport
import TorusEuler.OffOriginPressure
import TorusEuler.TorusLerayModes
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Smoothness of periodized dyadic multiplier kernels away from the lattice. -/

open Filter MeasureTheory Set
open scoped ContDiff FourierTransform SchwartzMap Topology

namespace TorusEuler

noncomputable section

section SchwartzDecay

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The symbol moments and derivative integrals needed to estimate a kernel jet. -/
def multiplierJetMass (d p : ℕ) (symbol : Vec3 → F) : ℝ :=
  ∑ k ∈ Finset.range (d + 1) ×ˢ Finset.range (p + 1),
    ∫ ξ, ‖ξ‖ ^ k.1 * ‖iteratedFDeriv ℝ k.2 symbol ξ‖

theorem multiplierJetMass_nonneg (d p : ℕ) (symbol : Vec3 → F) :
    0 ≤ multiplierJetMass d p symbol := by
  exact Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => by positivity

/-- The annular derivative mass with the constants from Fourier integration by parts. -/
def multiplierJetDecayConstant (d p : ℕ) (symbol : Vec3 → F) : ℝ :=
  2 ^ p * ((2 * Real.pi) ^ d * (2 * (d : ℝ) + 2) ^ p *
    multiplierJetMass d p symbol)

theorem multiplierJetDecayConstant_nonneg (d p : ℕ) (symbol : Vec3 → F) :
    0 ≤ multiplierJetDecayConstant d p symbol := by
  unfold multiplierJetDecayConstant
  have := multiplierJetMass_nonneg d p symbol
  positivity

private theorem inverseMultiplierKernel_pow_mul_le_jetMass (symbol : 𝓢(Vec3, F))
    (d n p : ℕ) (hn : n ≤ p) (y : Vec3) :
    ‖y‖ ^ n * ‖iteratedFDeriv ℝ d (𝓕⁻ symbol : 𝓢(Vec3, F)) y‖ ≤
      (2 * Real.pi) ^ d * (2 * (d : ℝ) + 2) ^ p * multiplierJetMass d p symbol := by
  have hFourier := Real.pow_mul_norm_iteratedFDeriv_fourier_le
    (f := (symbol : Vec3 → F)) (K := ⊤) (k := d) (n := n)
    (symbol.smooth ⊤) (fun k n _ _ => symbol.integrable_pow_mul_iteratedFDeriv volume k n)
    le_top le_top (-y)
  have hneg :
      ‖iteratedFDeriv ℝ d (𝓕⁻ symbol : 𝓢(Vec3, F)) y‖ =
        ‖iteratedFDeriv ℝ d (𝓕 (symbol : Vec3 → F)) (-y)‖ := by
    rw [SchwartzMap.fourierInv_coe]
    simp_rw [show (𝓕⁻ (symbol : Vec3 → F)) =
      (𝓕 (symbol : Vec3 → F)) ∘ LinearIsometryEquiv.neg ℝ (E := Vec3) by
        funext x
        exact Real.fourierInv_eq_fourier_neg symbol x]
    exact (LinearIsometryEquiv.neg ℝ (E := Vec3)).norm_iteratedFDeriv_comp_right _ y d
  rw [hneg, ← norm_neg y]
  refine hFourier.trans ?_
  have hpow : (2 * (d : ℝ) + 2) ^ n ≤ (2 * (d : ℝ) + 2) ^ p :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) d]) hn
  have hmass : multiplierJetMass d n symbol ≤ multiplierJetMass d p symbol := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.product_subset_product (fun _ h => h) (Finset.range_mono (by omega))
    · exact fun _ _ _ => integral_nonneg fun _ => by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) hmass
    (multiplierJetMass_nonneg d n symbol) (by positivity)

/-- A Schwartz inverse multiplier kernel has arbitrary polynomial decay,
with an explicit bound from the symbol's weighted derivatives. -/
theorem inverseMultiplierKernel_decay_all (symbol : 𝓢(Vec3, F)) (d p : ℕ) (y : Vec3) :
    (1 + ‖y‖) ^ p * ‖iteratedFDeriv ℝ d (𝓕⁻ symbol : 𝓢(Vec3, F)) y‖ ≤
      multiplierJetDecayConstant d p symbol := by
  unfold multiplierJetDecayConstant
  rcases le_total ‖y‖ 1 with hy | hy
  · have hw : (1 + ‖y‖) ^ p ≤ (2 : ℝ) ^ p :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    refine (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [pow_zero, one_mul] using
      inverseMultiplierKernel_pow_mul_le_jetMass symbol d 0 p (Nat.zero_le _) y
  · have hw : (1 + ‖y‖) ^ p ≤ (2 : ℝ) ^ p * ‖y‖ ^ p := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    refine (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (inverseMultiplierKernel_pow_mul_le_jetMass symbol d p p le_rfl y) (by positivity)

/-- Scaling contributes a factor of three powers for volume and one further
power for each kernel differentiation. -/
theorem scaledMultiplierKernel_decay_all (symbol : 𝓢(Vec3, F))
    {Λ : ℝ} (hΛ : 0 < Λ) (d p : ℕ) (y : Vec3) :
    (1 + Λ * ‖y‖) ^ p *
        ‖iteratedFDeriv ℝ d (scaledMultiplierKernel Λ (𝓕⁻ symbol : 𝓢(Vec3, F))) y‖ ≤
      Λ ^ (3 + d) * multiplierJetDecayConstant d p symbol := by
  let K : 𝓢(Vec3, F) := 𝓕⁻ symbol
  have hcomp : ContDiff ℝ d (fun z : Vec3 => K (Λ • z)) :=
    (K.smooth d).comp (contDiff_id.const_smul Λ)
  change (1 + Λ * ‖y‖) ^ p *
    ‖iteratedFDeriv ℝ d (fun z : Vec3 => Λ ^ 3 • K (Λ • z)) y‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' hcomp.contDiffAt,
    iteratedFDeriv_comp_const_smul Λ (K.smooth d), norm_smul, norm_smul,
    Real.norm_of_nonneg (pow_nonneg hΛ.le _), Real.norm_of_nonneg (pow_nonneg hΛ.le _)]
  have hnorm : ‖Λ • y‖ = Λ * ‖y‖ := by rw [norm_smul, Real.norm_of_nonneg hΛ.le]
  rw [← hnorm]
  calc
    _ = Λ ^ (3 + d) * ((1 + ‖Λ • y‖) ^ p * ‖iteratedFDeriv ℝ d K (Λ • y)‖) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (inverseMultiplierKernel_decay_all symbol d p (Λ • y))
      (pow_nonneg hΛ.le _)

end SchwartzDecay

section SmoothSum

variable {ι X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A locally uniformly summable series of smooth maps is smooth wherever all of
its jets admit uniform summable majorants on an open neighborhood. -/
theorem contDiffOn_tsum_of_jet_majorants {U : Set X} (hU : IsOpen U)
    {f : ι → X → F} (hf : ∀ i, ContDiff ℝ ∞ (f i)) {b : ℕ → ι → ℝ}
    (hb : ∀ d, Summable (b d))
    (hbound : ∀ d i x, x ∈ U → ‖iteratedFDeriv ℝ d (f i) x‖ ≤ b d i) :
    ContDiffOn ℝ ∞ (fun x => ∑' i, f i x) U ∧
      ∀ d, EqOn (iteratedFDeriv ℝ d (fun x => ∑' i, f i x))
        (fun x => ∑' i, iteratedFDeriv ℝ d (f i) x) U := by
  classical
  let J : X → FormalMultilinearSeries ℝ X F := fun x d => ∑' i, iteratedFDeriv ℝ d (f i) x
  have hs (d : ℕ) (x : X) (hx : x ∈ U) :
      Summable (fun i => iteratedFDeriv ℝ d (f i) x) :=
    Summable.of_norm_bounded (hb d) (fun i => hbound d i x hx)
  have hu (d : ℕ) :=
    tendstoUniformlyOn_tsum (hb d) (fun i x hx => hbound d i x hx)
  have hD (d : ℕ) (x : X) (hx : x ∈ U) :
      HasFDerivAt (fun y => J y d) (J x (d + 1)).curryLeft x := by
    let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => X) F
    have hlim : TendstoUniformlyOn
        (fun t : Finset ι => fun y => ∑ i ∈ t, L (iteratedFDeriv ℝ (d + 1) (f i) y))
        (fun y => (J y (d + 1)).curryLeft) atTop U := by
      refine (tendstoUniformlyOn_tsum
        (f := fun i y => L (iteratedFDeriv ℝ (d + 1) (f i) y))
        (hb (d + 1)) (fun i y hy => ?_)).congr_right ?_
      · simpa only [L, LinearIsometryEquiv.norm_map] using hbound (d + 1) i y hy
      · intro y hy
        exact L.toContinuousLinearEquiv.toContinuousLinearMap.map_tsum (hs (d + 1) y hy) |>.symm
    refine hasFDerivAt_of_tendstoUniformlyOn hU hlim (fun t y _ => ?_)
      (fun y hy => (hu d).tendsto_at hy) hx
    apply HasFDerivAt.fun_sum
    intro i _
    have hdi := (hf i).differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top d)
    have hfi := hdi.differentiableAt (x := y) |>.hasFDerivAt
    rw [fderiv_iteratedFDeriv] at hfi
    exact hfi
  have hzero (x : X) (hx : x ∈ U) : (J x 0).curry0 = ∑' i, f i x := by
    let L := continuousMultilinearCurryFin0 ℝ X F
    calc
      _ = ∑' i, L (iteratedFDeriv ℝ 0 (f i) x) :=
        L.toContinuousLinearEquiv.toContinuousLinearMap.map_tsum (hs 0 x hx)
      _ = _ := by simp [L, iteratedFDeriv_zero_apply]
  have hJ (m : ℕ) : HasFTaylorSeriesUpToOn m (fun x => ∑' i, f i x) J U :=
    ⟨hzero, fun d _ x hx => (hD d x hx).hasFDerivWithinAt,
      fun d _ x hx => (hD d x hx).continuousAt.continuousWithinAt⟩
  refine ⟨contDiffOn_infty.mpr fun m => (hJ m).contDiffOn, fun d x hx => ?_⟩
  rw [← iteratedFDerivWithin_of_isOpen d hU hx]
  exact ((hJ d).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hU.uniqueDiffOn hx).symm

end SmoothSum

section Periodization

local notation "Freq" => (Fin 3 → ℤ)

private theorem summable_latticeVector_norm_pow_inv (p : ℕ) (hp : 3 < p) :
    Summable (fun n : Freq => ‖latticeVector n‖⁻¹ ^ p) := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let L := Submodule.span ℤ (Set.range b)
  let : DiscreteTopology L := inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range b)))
  let : IsZLattice ℝ L := inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range b)))
  have hmem (n : Freq) : latticeVector n ∈ L := by
    apply (b.mem_span_iff_repr_mem ℤ _).2
    intro i
    exact ⟨n i, rfl⟩
  let e (n : Freq) : L := ⟨latticeVector n, hmem n⟩
  have he : Function.Injective e := by
    intro n m h
    funext i
    have hi := congrArg (fun v : L => (v : Vec3) i) h
    change (n i : ℝ) = (m i : ℝ) at hi
    exact Int.cast_inj.mp hi
  have hLrank : Module.finrank ℤ L = 3 := by
    rw [ZLattice.rank ℝ]
    exact finrank_euclideanSpace_fin
  have hLp : Module.finrank ℤ L < p := by rw [hLrank]; exact hp
  have hlsum : Summable (fun n : L => ‖n‖⁻¹ ^ p) := ZLattice.summable_norm_pow_inv L p hLp
  have hcomp := hlsum.comp_injective he
  exact hcomp

theorem summable_inv_one_add_latticeVector_norm_pow (p : ℕ) (hp : 3 < p) :
    Summable (fun n : Freq => ((1 + ‖latticeVector n‖) ^ p)⁻¹) := by
  have hlattice := summable_latticeVector_norm_pow_inv p hp
  refine Summable.of_norm_bounded_eventually hlattice ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : Freq)] with n hn
  have hnorm : 0 < ‖latticeVector n‖ := by
    refine norm_pos_iff.2 fun hz => hn ?_
    funext i
    have hi := congrArg (fun v : Vec3 => v i) hz
    change (n i : ℝ) = (0 : ℝ) at hi
    change n i = 0
    exact Int.cast_eq_zero.mp hi
  rw [Real.norm_of_nonneg (by positivity), inv_pow]
  exact inv_anti₀ (pow_pos hnorm p)
    (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left zero_le_one) p)

theorem spatiallyPeriodic_tsum_lattice_translates {F : Type*}
    [NormedAddCommGroup F] (K : ℕ → Vec3 → F) :
    SpatiallyPeriodic (fun x => ∑' i : ℕ × Freq, K i.1 (x + latticeVector i.2)) := by
  intro k x
  let e : ℕ × Freq ≃ ℕ × Freq := Equiv.prodCongr (Equiv.refl ℕ)
    { toFun := fun n => k + n
      invFun := fun n => n - k
      left_inv := fun n => add_sub_cancel_left k n
      right_inv := fun n => by
        change k + (n - k) = n
        rw [add_comm, sub_add_cancel] }
  calc
    _ = ∑' i : ℕ × Freq, K (e i).1 (x + latticeVector (e i).2) := by
      apply tsum_congr
      intro i
      congr 1
      apply PiLp.ext
      intro l
      change (x l + (k l : ℝ)) + (i.2 l : ℝ) = x l + (((k l + i.2 l : ℤ) : ℝ))
      rw [Int.cast_add, add_assoc]
    _ = _ := e.tsum_eq (fun i => K i.1 (x + latticeVector i.2))

theorem exists_summable_bound_lattice_translates {F : Type*} [NormedAddCommGroup F]
    (K : Vec3 → F) (p : ℕ) (C R Λ : ℝ) (hp : 3 < p)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hΛ : 1 ≤ Λ)
    (hdecay : ∀ y, ‖K y‖ ≤ C / (1 + Λ * ‖y‖) ^ p) :
    ∃ u : Freq → ℝ, Summable u ∧
      ∀ (n : Freq) (x : Vec3), ‖x‖ ≤ R → ‖K (x + latticeVector n)‖ ≤ u n := by
  let u (n : Freq) : ℝ := (C * (1 + R) ^ p) * ((1 + ‖latticeVector n‖) ^ p)⁻¹
  refine ⟨u, (summable_inv_one_add_latticeVector_norm_pow p hp).mul_left _, ?_⟩
  intro n x hx
  let y := x + latticeVector n
  have htriangle : ‖latticeVector n‖ ≤ ‖y‖ + ‖x‖ := by
    rw [← norm_neg x]
    calc
      ‖latticeVector n‖ = ‖y + -x‖ := by congr 1; dsimp [y]; abel
      _ ≤ _ := norm_add_le _ _
  have hbase : 1 + ‖latticeVector n‖ ≤ (1 + R) * (1 + Λ * ‖y‖) := by
    calc
      _ ≤ 1 + (‖y‖ + R) := by linarith
      _ ≤ (1 + R) * (1 + ‖y‖) := by nlinarith [mul_nonneg hR (norm_nonneg y)]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add_right (le_mul_of_one_le_left (norm_nonneg y) hΛ) _) (by positivity)
  have hpow := pow_le_pow_left₀ (show 0 ≤ 1 + ‖latticeVector n‖ by positivity) hbase p
  rw [mul_pow] at hpow
  calc
    _ ≤ C / (1 + Λ * ‖y‖) ^ p := hdecay y
    _ ≤ (C * (1 + R) ^ p) / (1 + ‖latticeVector n‖) ^ p := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpow hC
    _ = u n := div_eq_mul_inv _ _

theorem exists_summable_bound_dyadic_lattice_translates {F : Type*}
    [NormedAddCommGroup F] (K : ℕ → Vec3 → F) (m : ℕ) (C R ρ : ℝ)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hρ : 0 < ρ)
    (hdecay : ∀ j y, ‖K j y‖ ≤ C * ((2 : ℝ) ^ j) ^ (3 + m) /
      (1 + (2 : ℝ) ^ j * ‖y‖) ^ (m + 4)) :
    ∃ u : ℕ × Freq → ℝ, Summable u ∧
      ∀ (i : ℕ × Freq) (x : Vec3), ‖x‖ ≤ R →
        (∀ n : Freq, ρ ≤ ‖x + latticeVector n‖) →
        ‖K i.1 (x + latticeVector i.2)‖ ≤ u i := by
  let B : ℝ := 1 + (1 + R) / ρ
  let a (j : ℕ) : ℝ := (1 / 2 : ℝ) ^ j
  let b (n : Freq) : ℝ := ((1 + ‖latticeVector n‖) ^ (m + 4))⁻¹
  have ha : Summable a := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hb : Summable b := summable_inv_one_add_latticeVector_norm_pow _ (by omega)
  have hs : Summable (fun i : ℕ × Freq => a i.1 * b i.2) :=
    summable_mul_of_summable_norm ha.norm hb.norm
  refine ⟨fun i => C * B ^ (m + 4) * (a i.1 * b i.2), hs.mul_left _, ?_⟩
  rintro ⟨j,n⟩ x hx hsep
  let y := x + latticeVector n
  let q : ℝ := 1 + ‖latticeVector n‖
  let L : ℝ := (2 : ℝ) ^ j
  have hL : 0 < L := by positivity
  have hq : 0 < q := by positivity
  have hB : 0 ≤ B := by unfold B; positivity
  have hB' : 0 ≤ (1 + R) / ρ := by positivity
  have htriangle : ‖latticeVector n‖ ≤ ‖y‖ + ‖x‖ := by
    rw [← norm_neg x]
    calc
      ‖latticeVector n‖ = ‖y + -x‖ := by congr 1; dsimp [y]; abel
      _ ≤ _ := norm_add_le _ _
  have hrescale : 1 + R ≤ ((1 + R) / ρ) * ‖y‖ := by
    calc
      1 + R = ((1 + R) / ρ) * ρ := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsep n) hB'
  have hbase : q ≤ B * ‖y‖ := by
    unfold q B
    rw [add_mul, one_mul]
    linarith
  have hbase' : L * q ≤ B * (1 + L * ‖y‖) := by
    calc
      L * q ≤ L * (B * ‖y‖) := mul_le_mul_of_nonneg_left hbase hL.le
      _ ≤ B * (1 + L * ‖y‖) := by nlinarith
  have hp := pow_le_pow_left₀ (show 0 ≤ L * q by positivity) hbase' (m + 4)
  rw [mul_pow B] at hp
  have hpow : L ^ (3 + m) * L = L ^ (m + 4) := by
    rw [← pow_succ]
    congr 1
    omega
  have hapos : a j = L⁻¹ := by
    simp [a, L, ← inv_pow, one_div]
  calc
    _ ≤ C * L ^ (3 + m) / (1 + L * ‖y‖) ^ (m + 4) := hdecay j y
    _ ≤ C * L ^ (3 + m) * B ^ (m + 4) / (L * q) ^ (m + 4) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp
        (show 0 ≤ C * L ^ (3 + m) by positivity)
    _ = C * B ^ (m + 4) * (a j * b n) := by
      rw [hapos, show b n = (q ^ (m + 4))⁻¹ from rfl, mul_pow L, ← hpow]
      field_simp

end Periodization

section FundamentalCell

local notation "Freq" => (Fin 3 → ℤ)

private noncomputable def kernelLatticeBasis : Module.Basis (Fin 3) ℝ Vec3 :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

private abbrev KernelLattice := Submodule.span ℤ (range kernelLatticeBasis)

/-- A half-open fundamental cell for periodizing the Euclidean multiplier kernel. -/
def multiplierKernelCell : Set Vec3 :=
  ZSpan.fundamentalDomain kernelLatticeBasis

/-- The half-open cell has compact closure, allowing a uniform kernel bound on
the bounded differences between a target and cell source points. -/
theorem isCompact_closure_multiplierKernelCell : IsCompact (closure multiplierKernelCell) :=
  kernelLatticeBasis.parallelepiped.isCompact.of_isClosed_subset isClosed_closure
    (closure_minimal (ZSpan.fundamentalDomain_subset_parallelepiped kernelLatticeBasis)
      kernelLatticeBasis.parallelepiped.isCompact.isClosed)

private theorem multiplierKernelCell_measurable : MeasurableSet multiplierKernelCell :=
  ZSpan.fundamentalDomain_measurableSet kernelLatticeBasis

private theorem multiplierKernelCell_measure_lt_top :
    (volume : Measure Vec3) multiplierKernelCell < ⊤ :=
  (measure_mono (ZSpan.fundamentalDomain_subset_parallelepiped kernelLatticeBasis)).trans_lt
    kernelLatticeBasis.parallelepiped.isCompact.measure_lt_top

private noncomputable def kernelLatticeEquiv : Freq ≃ KernelLattice := by
  let e (n : Freq) : KernelLattice :=
    ⟨latticeVector n, (kernelLatticeBasis.mem_span_iff_repr_mem ℤ _).2 fun i => ⟨n i, rfl⟩⟩
  refine Equiv.ofBijective e ⟨?_, ?_⟩
  · intro n m h
    funext i
    have hi := congrArg (fun z : KernelLattice => (z : Vec3) i) h
    change (n i : ℝ) = (m i : ℝ) at hi
    exact Int.cast_inj.mp hi
  · intro z
    have hz (i : Fin 3) : ∃ n : ℤ, (n : ℝ) = (z : Vec3) i :=
      (kernelLatticeBasis.mem_span_iff_repr_mem ℤ _).mp z.property i
    choose n hn using hz
    exact ⟨n, Subtype.ext (PiLp.ext hn)⟩

private theorem kernelLatticeEquiv_apply (n : Freq) :
    (kernelLatticeEquiv n : Vec3) = latticeVector n := rfl

/-- An absolutely periodizable Euclidean kernel gives exactly the corresponding
cell convolution on bounded continuous periodic inputs. -/
theorem operatorLiftConvolution_eq_integral_periodized
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (K : Vec3 → E →L[ℂ] F) (hK : Integrable K) (hKcont : Continuous K)
    (f : Vec3 → E) (hf : Continuous f) (hfper : SpatiallyPeriodic f)
    (x : Vec3) {M : ℝ} (hM : ∀ y, ‖f y‖ ≤ M) {u : Freq → ℝ} (hu : Summable u)
    (hbound : ∀ (n : Freq) (y : Vec3), y ∈ multiplierKernelCell →
      ‖K (x - y + latticeVector n)‖ ≤ u n) :
    operatorLiftConvolution K f x =
      ∫ y in multiplierKernelCell, (∑' n : Freq, K (x - y + latticeVector n)) (f y) := by
  let W (y : Vec3) := K y (f (x - y))
  let W' (y : Vec3) := K (x - y) (f y)
  have hW : Integrable W := integrable_operatorLiftConvolution hK hf hM x
  let e := MeasurableEquiv.subLeft x
  have he : MeasurePreserving e (volume : Measure Vec3) volume := volume.measurePreserving_sub_left x
  have hcomp : W ∘ e = W' := by
    funext y
    change K (x - y) (f (x - (x - y))) = _
    rw [sub_sub_cancel]
  have hW' : Integrable W' := hcomp ▸ (he.integrable_comp_emb e.measurableEmbedding).2 hW
  have hswitch : operatorLiftConvolution K f x = ∫ y, W' y := by
    rw [← hcomp]
    exact (he.integral_comp' W).symm
  let : DiscreteTopology KernelLattice :=
    inferInstanceAs (DiscreteTopology (Submodule.span ℤ (range kernelLatticeBasis)))
  let : VAddInvariantMeasure KernelLattice Vec3 (volume : Measure Vec3) :=
    inferInstanceAs (VAddInvariantMeasure
      (Submodule.span ℤ (range kernelLatticeBasis)).toAddSubgroup Vec3 (volume : Measure Vec3))
  have hcell := ZSpan.isAddFundamentalDomain kernelLatticeBasis (volume : Measure Vec3)
  let V (n : Freq) (y : Vec3) := K (x - y + latticeVector n) (f y)
  have hinter : ∫ y, W' y = ∑' n : Freq, ∫ y in multiplierKernelCell, V n y := by
    calc
      _ = ∑' z : KernelLattice, ∫ y in multiplierKernelCell, W' (-z +ᵥ y) :=
        hcell.integral_eq_tsum' W' hW'
      _ = ∑' n : Freq, ∫ y in multiplierKernelCell, W' (-(kernelLatticeEquiv n) +ᵥ y) :=
        (kernelLatticeEquiv.tsum_eq (fun z => ∫ y in multiplierKernelCell, W' (-z +ᵥ y))).symm
      _ = _ := by
        apply tsum_congr
        intro n
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        change K (x - (-((kernelLatticeEquiv n : KernelLattice) : Vec3) + y))
          (f (-((kernelLatticeEquiv n : KernelLattice) : Vec3) + y)) = V n y
        rw [kernelLatticeEquiv_apply]
        have hn : latticeVector (-n) = -latticeVector n :=
          PiLp.ext (fun i => Int.cast_neg (n i))
        rw [show x - (-latticeVector n + y) = x - y + latticeVector n by abel,
          show -latticeVector n + y = y + latticeVector (-n) by rw [hn, add_comm],
          hfper]
  let μ := (volume : Measure Vec3).restrict multiplierKernelCell
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 multiplierKernelCell_measure_lt_top.ne
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hVbound (n : Freq) (y : Vec3) (hy : y ∈ multiplierKernelCell) : ‖V n y‖ ≤ u n * M :=
    ((K _).le_opNorm_of_le (hM y)).trans (mul_le_mul_of_nonneg_right (hbound n y hy) hM₀)
  have hV (n : Freq) : Integrable (V n) μ := by
    have hcont : Continuous (V n) :=
      (hKcont.comp ((continuous_const.sub continuous_id).add continuous_const)).clm_apply hf
    exact Integrable.of_bound hcont.aestronglyMeasurable (u n * M)
      ((ae_restrict_iff' multiplierKernelCell_measurable).2
        (Eventually.of_forall fun y hy => hVbound n y hy))
  have hnorm (n : Freq) : (∫ y, ‖V n y‖ ∂μ) ≤
      (u n * M) * (volume : Measure Vec3).real multiplierKernelCell := by
    refine (le_abs_self _).trans ?_
    change ‖∫ y in multiplierKernelCell, ‖V n y‖‖ ≤ _
    apply norm_setIntegral_le_of_norm_le_const multiplierKernelCell_measure_lt_top
    intro y hy
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hVbound n y hy
  have hsum : Summable (fun n => ∫ y, ‖V n y‖ ∂μ) :=
    ((hu.mul_right M).mul_right ((volume : Measure Vec3).real multiplierKernelCell)).of_nonneg_of_le
      (fun n => integral_nonneg fun y => norm_nonneg (V n y)) hnorm
  rw [hswitch, hinter, integral_tsum_of_summable_integral_norm hV hsum]
  apply setIntegral_congr_fun multiplierKernelCell_measurable
  intro y hy
  have hsumK : Summable (fun n : Freq => K (x - y + latticeVector n)) :=
    Summable.of_norm_bounded hu (fun n => hbound n y hy)
  exact ((ContinuousLinearMap.apply ℂ F (f y)).map_tsum hsumK).symm

end FundamentalCell

section PeriodicKernel

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
local notation "Freq" => (Fin 3 → ℤ)

/-- One dyadic Euclidean kernel for the compact symbol before periodization. -/
def dyadicEuclideanMultiplierKernel (σ : 𝓢(Vec3, F)) (j : ℕ) : Vec3 → F :=
  scaledMultiplierKernel ((2 : ℝ) ^ j) (𝓕⁻ σ : 𝓢(Vec3, F))

theorem contDiff_dyadicEuclideanMultiplierKernel (σ : 𝓢(Vec3, F)) (j : ℕ) :
    ContDiff ℝ ∞ (dyadicEuclideanMultiplierKernel σ j) := by
  unfold dyadicEuclideanMultiplierKernel scaledMultiplierKernel
  exact ((𝓕⁻ σ : 𝓢(Vec3, F)).smooth ⊤ |>.comp
    (contDiff_id.const_smul ((2 : ℝ) ^ j))).const_smul (((2 : ℝ) ^ j) ^ 3)

/-- The periodic kernel of one dyadic block. -/
def dyadicPeriodicMultiplierBlock (σ : 𝓢(Vec3, F)) (j : ℕ) (x : Vec3) : F :=
  ∑' k : Freq, dyadicEuclideanMultiplierKernel σ j (x + latticeVector k)

/-- The periodic kernel on the complement of the singular lattice is the sum
of the translated Euclidean kernels over dyadic scales and lattice points. -/
def dyadicPeriodicMultiplierKernel (σ : 𝓢(Vec3, F)) (x : Vec3) : F :=
  ∑' i : ℕ × Freq, dyadicEuclideanMultiplierKernel σ i.1 (x + latticeVector i.2)

theorem spatiallyPeriodic_dyadicPeriodicMultiplierKernel (σ : 𝓢(Vec3, F)) :
    SpatiallyPeriodic (dyadicPeriodicMultiplierKernel σ) :=
  spatiallyPeriodic_tsum_lattice_translates (dyadicEuclideanMultiplierKernel σ)

private theorem norm_iteratedFDeriv_dyadicEuclideanMultiplierKernel_le
    (σ : 𝓢(Vec3, F)) (d p j : ℕ) (x : Vec3) :
    ‖iteratedFDeriv ℝ d (dyadicEuclideanMultiplierKernel σ j) x‖ ≤
      multiplierJetDecayConstant d p σ * ((2 : ℝ) ^ j) ^ (3 + d) /
        (1 + (2 : ℝ) ^ j * ‖x‖) ^ p := by
  apply (le_div_iff₀ (by positivity)).2
  simpa only [dyadicEuclideanMultiplierKernel, mul_comm] using
    scaledMultiplierKernel_decay_all σ (Λ := (2 : ℝ) ^ j) (by positivity) d p x

variable [CompleteSpace F]

/-- The kernel jets of a single periodic block are the sums of the translated
Euclidean kernel jets. The block is globally smooth. -/
theorem contDiff_dyadicPeriodicMultiplierBlock (σ : 𝓢(Vec3, F)) (j : ℕ) :
    ContDiff ℝ ∞ (dyadicPeriodicMultiplierBlock σ j) ∧
      ∀ d x, iteratedFDeriv ℝ d (dyadicPeriodicMultiplierBlock σ j) x =
        ∑' k : Freq, iteratedFDeriv ℝ d (dyadicEuclideanMultiplierKernel σ j)
          (x + latticeVector k) := by
  have hlocal (x : Vec3) : ContDiffAt ℝ ∞ (dyadicPeriodicMultiplierBlock σ j) x ∧
      ∀ d, iteratedFDeriv ℝ d (dyadicPeriodicMultiplierBlock σ j) x =
        ∑' k : Freq, iteratedFDeriv ℝ d (dyadicEuclideanMultiplierKernel σ j)
          (x + latticeVector k) := by
    let U := Metric.ball x 1
    let R := ‖x‖ + 1
    let K := dyadicEuclideanMultiplierKernel σ j
    have hU : IsOpen U := Metric.isOpen_ball
    have hx : x ∈ U := Metric.mem_ball_self zero_lt_one
    have hbound (y : Vec3) (hy : y ∈ U) : ‖y‖ ≤ R := by
      have hdist : ‖y - x‖ ≤ 1 := by
        rw [← dist_eq_norm]
        exact (show dist y x < 1 from hy).le
      exact (norm_le_norm_add_norm_sub x y).trans (by
        simpa only [norm_sub_rev] using add_le_add_right hdist ‖x‖)
    have hmaj (d : ℕ) :
        ∃ b : Freq → ℝ, Summable b ∧ ∀ (k : Freq) (y : Vec3), y ∈ U →
          ‖iteratedFDeriv ℝ d (fun z => K (z + latticeVector k)) y‖ ≤ b k := by
      let p := d + 4
      let C := multiplierJetDecayConstant d p σ * ((2 : ℝ) ^ j) ^ (3 + d)
      have hC : 0 ≤ C :=
        mul_nonneg (multiplierJetDecayConstant_nonneg d p σ) (by positivity)
      obtain ⟨b, hb, hh⟩ := exists_summable_bound_lattice_translates
        (iteratedFDeriv ℝ d K) p C R ((2 : ℝ) ^ j) (by omega) hC (by positivity)
        (one_le_pow₀ (by norm_num)) (norm_iteratedFDeriv_dyadicEuclideanMultiplierKernel_le σ d p j)
      refine ⟨b, hb, fun k y hy => ?_⟩
      rw [iteratedFDeriv_comp_add_right]
      exact hh k y (hbound y hy)
    choose b hb hb' using hmaj
    have hcd (k : Freq) : ContDiff ℝ ∞ (fun z => K (z + latticeVector k)) :=
      (contDiff_dyadicEuclideanMultiplierKernel σ j).comp (contDiff_id.add contDiff_const)
    have ht := contDiffOn_tsum_of_jet_majorants hU hcd hb hb'
    refine ⟨ht.1.contDiffAt (hU.mem_nhds hx), fun d => ?_⟩
    change iteratedFDeriv ℝ d (fun z => ∑' k : Freq, K (z + latticeVector k)) x = _
    simpa only [iteratedFDeriv_comp_add_right] using ht.2 d hx
  exact ⟨contDiff_iff_contDiffAt.mpr fun x => (hlocal x).1, fun d x => (hlocal x).2 d⟩

omit [CompleteSpace F] in
/-- On a bounded and periodically separated set, the translated derivatives are
uniformly dominated by a summable sequence over scales and lattice translates. -/
theorem exists_jet_majorant_dyadicPeriodicMultiplierKernel (σ : 𝓢(Vec3, F))
    (d : ℕ) {R ρ : ℝ} (hR : 0 ≤ R) (hρ : 0 < ρ) :
    ∃ b : ℕ × Freq → ℝ, Summable b ∧
      ∀ (i : ℕ × Freq) (x : Vec3), ‖x‖ ≤ R → (∀ k : Freq, ρ ≤ ‖x + latticeVector k‖) →
        ‖iteratedFDeriv ℝ d (dyadicEuclideanMultiplierKernel σ i.1)
          (x + latticeVector i.2)‖ ≤ b i := by
  have h := exists_summable_bound_dyadic_lattice_translates
    (fun j => iteratedFDeriv ℝ d (dyadicEuclideanMultiplierKernel σ j)) d
    (multiplierJetDecayConstant d (d + 4) σ) R ρ
    (multiplierJetDecayConstant_nonneg d (d + 4) σ) hR hρ
    (norm_iteratedFDeriv_dyadicEuclideanMultiplierKernel_le σ d (d + 4))
  exact h

private theorem norm_add_latticeVector_eq_dist_neg (x : Vec3) (k : Freq) :
    ‖x + latticeVector k‖ = dist (latticeVector (-k)) x := by
  have h : latticeVector (-k) = -latticeVector k :=
    PiLp.ext fun i => Int.cast_neg (k i)
  rw [h, dist_comm, dist_eq_norm, sub_neg_eq_add]

/-- Every compact set off the lattice has a bounded open neighborhood with a
single positive separation from all lattice translates of the origin. -/
theorem exists_bounded_separated_offOrigin_neighborhood {S : Set Vec3}
    (hS : IsCompact S) (hSo : S ⊆ offOrigin) :
    ∃ U : Set Vec3, IsOpen U ∧ S ⊆ U ∧ ∃ R ρ : ℝ, 0 ≤ R ∧ 0 < ρ ∧
      ∀ x ∈ U, ‖x‖ ≤ R ∧ ∀ k : Freq, ρ ≤ ‖x + latticeVector k‖ := by
  obtain ⟨r, hr, hcompact, _, _, _, hdist⟩ := exists_offOrigin_compact_neighborhood hS hSo
  let U := Metric.thickening (r / 2) S
  obtain ⟨R, hR⟩ := hcompact.isBounded.exists_norm_le
  refine ⟨U, Metric.isOpen_thickening, Metric.self_subset_thickening (half_pos hr) S,
    max 0 R, r / 2, le_max_left _ _, half_pos hr, fun x hx => ⟨?_, ?_⟩⟩
  · exact (hR x (Metric.thickening_subset_cthickening r S
      (Metric.thickening_mono (by linarith) S hx))).trans (le_max_right _ _)
  · intro k
    obtain ⟨y, hy, hyx⟩ := Metric.mem_thickening_iff.mp hx
    rw [norm_add_latticeVector_eq_dist_neg]
    linarith only [hdist y hy (-k), hyx, dist_triangle (latticeVector (-k)) x y,
      dist_comm x y]

/-- The summed periodic kernel is smooth away from the lattice and can be
differentiated term by term there. -/
theorem contDiffOn_dyadicPeriodicMultiplierKernel (σ : 𝓢(Vec3, F)) :
    ContDiffOn ℝ ∞ (dyadicPeriodicMultiplierKernel σ) offOrigin ∧
      ∀ d, EqOn (iteratedFDeriv ℝ d (dyadicPeriodicMultiplierKernel σ))
        (fun x => ∑' i : ℕ × Freq, iteratedFDeriv ℝ d (dyadicEuclideanMultiplierKernel σ i.1)
          (x + latticeVector i.2)) offOrigin := by
  have hlocal (x : Vec3) (hx : x ∈ offOrigin) :
      ContDiffAt ℝ ∞ (dyadicPeriodicMultiplierKernel σ) x ∧
      ∀ d, iteratedFDeriv ℝ d (dyadicPeriodicMultiplierKernel σ) x =
        ∑' i : ℕ × Freq, iteratedFDeriv ℝ d (dyadicEuclideanMultiplierKernel σ i.1)
          (x + latticeVector i.2) := by
    obtain ⟨U, hU, hxU, R, ρ, hR, hρ, hsep⟩ :=
      exists_bounded_separated_offOrigin_neighborhood (isCompact_singleton (x := x))
        (singleton_subset_iff.mpr hx)
    have hmaj (d : ℕ) :
        ∃ b : ℕ × Freq → ℝ, Summable b ∧ ∀ (i : ℕ × Freq) (y : Vec3), y ∈ U →
          ‖iteratedFDeriv ℝ d
            (fun z => dyadicEuclideanMultiplierKernel σ i.1 (z + latticeVector i.2)) y‖ ≤ b i := by
      obtain ⟨b, hb, hh⟩ := exists_jet_majorant_dyadicPeriodicMultiplierKernel σ d hR hρ
      refine ⟨b, hb, fun i y hy => ?_⟩
      rw [iteratedFDeriv_comp_add_right]
      exact hh i y (hsep y hy).1 (hsep y hy).2
    choose b hb hb' using hmaj
    have hcd (i : ℕ × Freq) :
        ContDiff ℝ ∞ (fun z => dyadicEuclideanMultiplierKernel σ i.1 (z + latticeVector i.2)) :=
      (contDiff_dyadicEuclideanMultiplierKernel σ i.1).comp (contDiff_id.add contDiff_const)
    have ht := contDiffOn_tsum_of_jet_majorants hU hcd hb hb'
    have hx' : x ∈ U := hxU (mem_singleton x)
    refine ⟨ht.1.contDiffAt (hU.mem_nhds hx'), fun d => ?_⟩
    change iteratedFDeriv ℝ d (fun z => ∑' i : ℕ × Freq,
      dyadicEuclideanMultiplierKernel σ i.1 (z + latticeVector i.2)) x = _
    simpa only [iteratedFDeriv_comp_add_right] using ht.2 d hx'
  exact ⟨isOpen_offOrigin.contDiffOn_iff.mpr (fun x hx => (hlocal x hx).1),
    fun d _ hx => (hlocal _ hx).2 d⟩

/-- Every derivative of the finite dyadic periodic kernel converges uniformly
on compact subsets off the lattice. -/
theorem tendstoUniformlyOn_dyadicPeriodicMultiplierKernel_jets (σ : 𝓢(Vec3, F))
    (d : ℕ) {S : Set Vec3} (hS : IsCompact S) (ho : S ⊆ offOrigin) :
    TendstoUniformlyOn (fun N x => ∑ j ∈ Finset.range N,
      iteratedFDeriv ℝ d (dyadicPeriodicMultiplierBlock σ j) x)
      (iteratedFDeriv ℝ d (dyadicPeriodicMultiplierKernel σ)) atTop S := by
  obtain ⟨U, _, hsu, R, ρ, hR, hρ, hsep⟩ := exists_bounded_separated_offOrigin_neighborhood hS ho
  obtain ⟨b, hb, hbound⟩ := exists_jet_majorant_dyadicPeriodicMultiplierKernel σ d hR hρ
  have hmajor (j : ℕ) (x : Vec3) (hx : x ∈ S) :
      ‖iteratedFDeriv ℝ d (dyadicPeriodicMultiplierBlock σ j) x‖ ≤ ∑' n : Freq, b (j, n) := by
    rw [(contDiff_dyadicPeriodicMultiplierBlock σ j).2]
    have h := fun n : Freq => hbound (j, n) x (hsep x (hsu hx)).1 (hsep x (hsu hx)).2
    have hnorm := (hb.prod_factor j).of_nonneg_of_le (fun _ => norm_nonneg _) h
    exact (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum h (hb.prod_factor j))
  refine (tendstoUniformlyOn_tsum_nat hb.prod hmajor).congr_right ?_
  intro x hx
  rw [(contDiffOn_dyadicPeriodicMultiplierKernel σ).2 d (ho hx)]
  simp_rw [(contDiff_dyadicPeriodicMultiplierBlock σ _).2]
  have hh := fun i : ℕ × Freq => hbound i x (hsep x (hsu hx)).1 (hsep x (hsu hx)).2
  have hsum := Summable.of_norm_bounded hb hh
  exact (hsum.tsum_prod' hsum.prod_factor).symm

/-- Use the fixed annular partition of the half-Hölder multiplier to select
its periodic kernel off the diagonal. -/
def homogeneousOffOriginMultiplierKernel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : Vec3 → E →L[ℂ] F} (hA : ContDiffOn ℝ ∞ A ({0}ᶜ : Set Vec3)) : Vec3 → E →L[ℂ] F :=
  dyadicPeriodicMultiplierKernel
    ((annularLocalize_compact dyadicMultiplierCutoff_zero A).toSchwartzMap
      (annularLocalize_smooth dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit hA))

end PeriodicKernel

section FarKernel

variable {G A B : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]

private def kernelJetAction (d : ℕ) (L : G →L[ℝ] A →L[ℝ] B) :
    (Vec3 [×d]→L[ℝ] G) →L[ℝ] A →L[ℝ] (Vec3 [×d]→L[ℝ] B) :=
  ((ContinuousLinearMap.flipMultilinearEquiv ℝ (fun _ : Fin d => Vec3) A B).symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin d => Vec3) G
        (A →L[ℝ] B) L)

@[simp] private theorem kernelJetAction_apply (d : ℕ) (L : G →L[ℝ] A →L[ℝ] B)
    (M : Vec3 [×d]→L[ℝ] G) (a : A) (w : Fin d → Vec3) :
    kernelJetAction d L M a w = L (M w) a :=
  rfl

/-- The separated kernel for a spatial jet, with an optional real linear
action on its output. -/
def periodicFarMultiplierJet (σ : 𝓢(Vec3, G)) (L : G →L[ℝ] A →L[ℝ] B)
    (d : ℕ) (x y : Vec3) : A →L[ℝ] (Vec3 [×d]→L[ℝ] B) :=
  kernelJetAction d L (iteratedFDeriv ℝ d (dyadicPeriodicMultiplierKernel σ) (x - y))

variable [CompleteSpace G]

private theorem continuousOn_iteratedFDeriv_dyadicPeriodicMultiplierKernel
    (σ : 𝓢(Vec3, G)) (d : ℕ) :
    ContinuousOn (iteratedFDeriv ℝ d (dyadicPeriodicMultiplierKernel σ)) offOrigin := by
  intro x hx
  exact (((contDiffOn_dyadicPeriodicMultiplierKernel σ).1.contDiffAt
    (isOpen_offOrigin.mem_nhds hx)).continuousAt_iteratedFDeriv (k := d)
      (mod_cast (le_top : (d : ℕ∞) ≤ ⊤))).continuousWithinAt

private theorem hasFDerivAt_periodicFarMultiplierJet
    (σ : 𝓢(Vec3, G)) (L : G →L[ℝ] A →L[ℝ] B) (d : ℕ)
    {x y : Vec3} (hxy : x - y ∈ offOrigin) (a : A) :
    HasFDerivAt (fun z => periodicFarMultiplierJet σ L d z y a)
      (periodicFarMultiplierJet σ L (d + 1) x y a).curryLeft x := by
  let K := dyadicPeriodicMultiplierKernel σ
  let P : (Vec3 [×d]→L[ℝ] G) →L[ℝ] (Vec3 [×d]→L[ℝ] B) :=
    (ContinuousLinearMap.apply ℝ (Vec3 [×d]→L[ℝ] B) a).comp (kernelJetAction d L)
  have hd := ((contDiffOn_dyadicPeriodicMultiplierKernel σ).1.contDiffAt
    (isOpen_offOrigin.mem_nhds hxy)).differentiableAt_iteratedFDeriv
      (mod_cast ENat.natCast_lt_top d)
  have hbase : HasFDerivAt (iteratedFDeriv ℝ d K)
      (iteratedFDeriv ℝ (d + 1) K (x - y)).curryLeft (x - y) := by
    have h := hd.hasFDerivAt
    rw [fderiv_iteratedFDeriv] at h
    exact h
  have h := P.hasFDerivAt.comp x (hbase.comp x ((hasFDerivAt_id x).sub_const y))
  have hclm : P.comp ((iteratedFDeriv ℝ (d + 1) K (x - y)).curryLeft.comp
      (ContinuousLinearMap.id ℝ Vec3)) = (periodicFarMultiplierJet σ L (d + 1) x y a).curryLeft := by
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousMultilinearMap.ext
    intro w
    rfl
  rw [hclm] at h
  exact h

/-- Actual annular multiplier kernel jets satisfy the hypotheses of the
separated pressure integral on a common open neighborhood of the target. -/
theorem exists_periodicFarMultiplierJet_bounds
    (σ : 𝓢(Vec3, G)) (L : G →L[ℝ] A →L[ℝ] B) {K S : Set Vec3}
    (hK : IsCompact K) (hS : IsCompact S)
    (hsep : ∀ x ∈ K, ∀ y ∈ S, x - y ∈ offOrigin)
    (μ : Measure Vec3) :
    ∃ U : Set Vec3, IsOpen U ∧ K ⊆ U ∧
      (∀ d x, x ∈ U → AEStronglyMeasurable
        (periodicFarMultiplierJet σ L d x) (μ.restrict S)) ∧
      (∀ d, ∃ M : ℝ, ∀ᵐ y ∂(μ.restrict S), ∀ x ∈ U,
        ‖periodicFarMultiplierJet σ L d x y‖ ≤ M) ∧
      (∀ d, ∀ᵐ y ∂(μ.restrict S), ∀ x ∈ U, ∀ a : A,
        HasFDerivAt (fun z => periodicFarMultiplierJet σ L d z y a)
          (periodicFarMultiplierJet σ L (d + 1) x y a).curryLeft x) := by
  obtain ⟨r, hr, hdist⟩ := exists_periodically_separated_neighborhood hK hS hsep
  let U := Metric.thickening r K
  let V := Metric.cthickening r K
  have hUV : U ⊆ V := Metric.thickening_subset_cthickening r K
  have hV : IsCompact V := hK.cthickening
  have hs : ∀ x ∈ V, ∀ y ∈ S, x - y ∈ offOrigin := by
    intro x hx y hy
    rintro ⟨n, h⟩
    have hn := hdist x hx y hy n
    rw [h, dist_self] at hn
    exact hr.not_gt hn
  have hc (d : ℕ) : ContinuousOn
      (fun p : Vec3 × Vec3 => iteratedFDeriv ℝ d (dyadicPeriodicMultiplierKernel σ) (p.1 - p.2))
      (V ×ˢ S) := (continuousOn_iteratedFDeriv_dyadicPeriodicMultiplierKernel σ d).comp
        (continuous_fst.sub continuous_snd).continuousOn (fun _ hp => hs _ hp.1 _ hp.2)
  refine ⟨U, Metric.isOpen_thickening, Metric.self_subset_thickening hr K, ?_, ?_, ?_⟩
  · intro d x hx
    exact (kernelJetAction d L).continuous.comp_aestronglyMeasurable
      (((hc d).comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ hy => ⟨hUV hx, hy⟩)).aestronglyMeasurable_of_isCompact hS hS.isClosed.measurableSet)
  · intro d
    obtain ⟨M, hM⟩ := (hV.prod hS).exists_bound_of_continuousOn (hc d)
    refine ⟨‖L‖ * M, ?_⟩
    filter_upwards [ae_restrict_mem hS.isClosed.measurableSet] with y hy x hx
    let J := iteratedFDeriv ℝ d (dyadicPeriodicMultiplierKernel σ) (x - y)
    have hJ : ‖J‖ ≤ M := hM (x, y) ⟨hUV hx, hy⟩
    have hM₀ := (norm_nonneg J).trans hJ
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro a
    apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
    intro z
    change ‖kernelJetAction d L J a z‖ ≤ _
    rw [kernelJetAction_apply]
    calc
      _ ≤ (‖L‖ * (M * ∏ i, ‖z i‖)) * ‖a‖ :=
        (L (J z)).le_of_opNorm_le (L.le_opNorm_of_le (J.le_of_opNorm_le hJ z)) a
      _ = _ := by ring
  · intro d
    filter_upwards [ae_restrict_mem hS.isClosed.measurableSet] with y hy x hx a
    exact hasFDerivAt_periodicFarMultiplierJet σ L d (hs x (hUV hx) y hy) a

/-- A separated periodic multiplier maps convergence of the velocity on
a compact source set to uniform convergence of each far contribution jet. -/
theorem tendstoUniformlyOn_periodicFarMultiplier_spatial_derivatives
    {ι V : Type*} {l : Filter ι} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace B]
    (σ : 𝓢(Vec3, G)) (L : G →L[ℝ] A →L[ℝ] B)
    (μ : Measure Vec3) [IsLocallyFiniteMeasure μ] {K S : Set Vec3}
    (hK : IsCompact K) (hS : IsCompact S)
    (hsep : ∀ x ∈ K, ∀ y ∈ S, x - y ∈ offOrigin)
    (tensor : V →L[ℝ] V →L[ℝ] A) {v : ι → Vec3 → V} {w : Vec3 → V}
    (hv : TendstoUniformlyOn v w l S) (hvc : ∀ i, ContinuousOn (v i) S)
    (hwc : ContinuousOn w S) (m : ℕ) :
    ∃ U : Set Vec3, IsOpen U ∧ K ⊆ U ∧
      let far (b : Vec3 → V) (x : Vec3) :=
        ∫ y in S, (L (dyadicPeriodicMultiplierKernel σ (x - y))) (tensor (b y) (b y)) ∂μ
      ContDiffOn ℝ m (far w) U ∧ ∀ d ≤ m,
        TendstoUniformlyOn (fun i => iteratedFDeriv ℝ d (far (v i)))
          (iteratedFDeriv ℝ d (far w)) l U := by
  obtain ⟨U, hU, hKU, hMeas, hNorm, hDeriv⟩ :=
    exists_periodicFarMultiplierJet_bounds σ L hK hS hsep μ
  let far (b : Vec3 → V) (x : Vec3) :=
    (farKernelIntegral (μ.restrict S) (periodicFarMultiplierJet σ L 0)
      (fun y => tensor (b y) (b y)) x).curry0
  have hfar (b : Vec3 → V) (x : Vec3) :
      far b x = ∫ y in S, (L (dyadicPeriodicMultiplierKernel σ (x - y))) (tensor (b y) (b y)) ∂μ := by
    let C := continuousMultilinearCurryFin0 ℝ Vec3 B
    change C (∫ y in S, periodicFarMultiplierJet σ L 0 x y (tensor (b y) (b y)) ∂μ) = _
    calc
      _ = ∫ y in S, C (periodicFarMultiplierJet σ L 0 x y (tensor (b y) (b y))) ∂μ :=
        (LinearIsometry.integral_comp_comm (μ := μ.restrict S) C.toLinearIsometry _).symm
      _ = _ := by congr 1
  have h := tendstoUniformlyOn_farKernel_spatial_derivatives_of_uniform_velocity
    hS hU tensor hv hvc hwc hMeas hNorm hDeriv m
  refine ⟨U, hU, hKU, ?_⟩
  change ContDiffOn ℝ m (far w) U ∧ ∀ d ≤ m,
    TendstoUniformlyOn (fun i => iteratedFDeriv ℝ d (far (v i)))
      (iteratedFDeriv ℝ d (far w)) l U at h
  simpa only [show ∀ b, far b = _ from fun b => funext (hfar b)] using h

end FarKernel

section MultiplierAgreement

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] in
private theorem operatorLiftConvolution_dyadic_eq_periodicBlock
    (σ : 𝓢(Vec3, E →L[ℂ] F)) (j : ℕ)
    (f : Vec3 → E) (hf : Continuous f) (hfper : SpatiallyPeriodic f)
    (x : Vec3) (M : ℝ) (hM : ∀ y, ‖f y‖ ≤ M) :
    operatorLiftConvolution (dyadicEuclideanMultiplierKernel σ j) f x =
      ∫ y in multiplierKernelCell, (dyadicPeriodicMultiplierBlock σ j (x - y)) (f y) := by
  let K := dyadicEuclideanMultiplierKernel σ j
  have hK : Integrable K :=
    integrable_scaledMultiplierKernel (by positivity) (𝓕⁻ σ : 𝓢(Vec3, E →L[ℂ] F)).integrable
  have hC : 0 ≤ multiplierJetDecayConstant 0 4 σ * ((2 : ℝ) ^ j) ^ (3 + 0) :=
    mul_nonneg (multiplierJetDecayConstant_nonneg 0 4 σ) (by positivity)
  have hcompact : IsCompact ((fun y : Vec3 => x - y) '' closure multiplierKernelCell) :=
    isCompact_closure_multiplierKernelCell.image (continuous_const.sub continuous_id)
  obtain ⟨R, hR⟩ := hcompact.isBounded.exists_norm_le
  obtain ⟨u, hu, hub⟩ := exists_summable_bound_lattice_translates K 4
    (multiplierJetDecayConstant 0 4 σ * ((2 : ℝ) ^ j) ^ (3 + 0))
    (max 0 R) ((2 : ℝ) ^ j) (by omega) hC (le_max_left _ _) (one_le_pow₀ (by norm_num)) (fun y => by
      simpa only [norm_iteratedFDeriv_zero] using
        norm_iteratedFDeriv_dyadicEuclideanMultiplierKernel_le σ 0 4 j y)
  refine operatorLiftConvolution_eq_integral_periodized K hK
    (contDiff_dyadicEuclideanMultiplierKernel σ j).continuous f hf hfper x hM hu (fun n y hy => ?_)
  exact hub n (x - y) ((hR _ ⟨y, subset_closure hy, rfl⟩).trans (le_max_right _ _))

/-- On separated data the bounded half-Hölder multiplier with zero constant
mode is exactly the integral of its summed periodic dyadic kernel. -/
theorem eval_homogeneousHalfHolderMultiplier_eq_periodicFarIntegral
    {A : Vec3 → E →L[ℂ] F} (hA : ContDiffOn ℝ ∞ A ({0}ᶜ : Set Vec3)) (hA0 : A 0 = 0)
    (f : HalfHolder (UnitAddTorus (Fin 3)) E) (x : Vec3) {S : Set Vec3} (hS : IsCompact S)
    (hsep : ∀ y ∈ S, x - y ∈ offOrigin)
    (hvanish : ∀ y ∈ multiplierKernelCell, y ∉ S → HalfHolder.eval (toUnitTorus y) f = 0) :
    HalfHolder.eval (toUnitTorus x)
      (homogeneousHalfHolderMultiplier dyadicMultiplierCutoff_smooth
        dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero hA f) =
      ∫ y in S ∩ multiplierKernelCell,
        (homogeneousOffOriginMultiplierKernel hA (x - y)) (HalfHolder.eval (toUnitTorus y) f) := by
  let g := fun y => continuousHalfHolder f (toUnitTorus y)
  have hq : Continuous toUnitTorus := continuous_pi fun i =>
    (AddCircle.continuous_mk' (1 : ℝ)).comp (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i)
  have hg : Continuous g := (continuousHalfHolder f).continuous.comp hq
  have hgper : SpatiallyPeriodic g := by
    intro n y
    exact congrArg (continuousHalfHolder f) ((toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩)
  let M := ‖continuousHalfHolder f‖
  have hM : ∀ y, ‖g y‖ ≤ M := fun y => (continuousHalfHolder f).norm_coe_le_norm (toUnitTorus y)
  let hc := annularLocalize_compact dyadicMultiplierCutoff_zero A
  let hs := annularLocalize_smooth dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit hA
  let σ := hc.toSchwartzMap hs
  let T := S ∩ multiplierKernelCell
  let D := (fun y : Vec3 => x - y) '' S
  have hD : IsCompact D := hS.image (continuous_const.sub continuous_id)
  have hDo : D ⊆ offOrigin := by
    rintro z ⟨y, hy, rfl⟩
    exact hsep y hy
  obtain ⟨U, _, hDU, R, ρ, hR, hρ, hloc⟩ := exists_bounded_separated_offOrigin_neighborhood hD hDo
  obtain ⟨b, hb, hb'⟩ := exists_jet_majorant_dyadicPeriodicMultiplierKernel σ 0 hR hρ
  have hbound (y : Vec3) (hy : y ∈ S) (i : ℕ × (Fin 3 → ℤ)) :
      ‖dyadicEuclideanMultiplierKernel σ i.1 (x - y + latticeVector i.2)‖ ≤ b i := by
    have hxy := hloc _ (hDU ⟨y, hy, rfl⟩)
    simpa only [norm_iteratedFDeriv_zero] using hb' i (x - y) hxy.1 hxy.2
  let V := fun j (y : Vec3) => (dyadicPeriodicMultiplierBlock σ j (x - y)) (g y)
  have hVcont (j : ℕ) : Continuous (V j) :=
    (((contDiff_dyadicPeriodicMultiplierBlock σ j).1.continuous).comp
      (continuous_const.sub continuous_id)).clm_apply hg
  have hVi (j : ℕ) : IntegrableOn (V j) T :=
    ((hVcont j).continuousOn.integrableOn_compact hS).mono_set inter_subset_left
  have hTfin : (volume : Measure Vec3) T < ⊤ :=
    (measure_mono inter_subset_left).trans_lt hS.measure_lt_top
  have hVb (j : ℕ) (y : Vec3) (hy : y ∈ S) : ‖V j y‖ ≤ (∑' n, b (j, n)) * M := by
    have hpt := fun n : Fin 3 → ℤ => hbound y hy (j, n)
    have hn := (hb.prod_factor j).of_nonneg_of_le (fun _ => norm_nonneg _) hpt
    refine ((dyadicPeriodicMultiplierBlock σ j (x - y)).le_opNorm_of_le (hM y)).trans ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum hpt (hb.prod_factor j))
  have hNormSum : Summable (fun j => ∫ y in T, ‖V j y‖) := by
    apply ((hb.prod.mul_right M).mul_right (volume.real T)).of_nonneg_of_le
      (fun j => integral_nonneg fun _ => norm_nonneg _)
    intro j
    refine (le_abs_self _).trans ?_
    change ‖∫ y in T, ‖V j y‖‖ ≤ _
    apply norm_setIntegral_le_of_norm_le_const hTfin
    intro y hy
    simpa only [Real.norm_of_nonneg (norm_nonneg (V j y))] using hVb j y hy.1
  have hIntegralSum : Summable (fun j => ∫ y in T, V j y) :=
    Summable.of_norm_bounded hNormSum (fun j => norm_integral_le_integral_norm _)
  have hsum : (∑' j, ∫ y in T, V j y) =
      ∫ y in T, (dyadicPeriodicMultiplierKernel σ (x - y)) (g y) := by
    rw [integral_tsum_of_summable_integral_norm hVi hNormSum]
    apply setIntegral_congr_fun (hS.isClosed.measurableSet.inter multiplierKernelCell_measurable)
    intro y hy
    have hpair := Summable.of_norm_bounded hb (hbound y hy.1)
    let L := ContinuousLinearMap.apply ℂ F (g y)
    calc
      _ = L (∑' j, dyadicPeriodicMultiplierBlock σ j (x - y)) :=
        (L.map_tsum hpair.prod).symm
      _ = _ := congrArg L (hpair.tsum_prod' hpair.prod_factor).symm
  have hcell (j : ℕ) : operatorLiftConvolution (dyadicEuclideanMultiplierKernel σ j) g x =
      ∫ y in T, V j y := by
    rw [operatorLiftConvolution_dyadic_eq_periodicBlock σ j g hg hgper x M hM]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero multiplierKernelCell_measurable inter_subset_right
    intro y hy
    have hzero : g y = 0 := hvanish y hy.1 (fun hyS => hy.2 ⟨hyS, hy.1⟩)
    rw [hzero, map_zero]
  have hVlimit := hIntegralSum.hasSum.tendsto_sum_nat
  rw [hsum] at hVlimit
  have hblocks := tendsto_operatorLiftConvolution_compactSymbolDyadicBlocks
    (fun z hz => dyadicMultiplierCutoff_zero z hz.le) dyadicMultiplierCutoff_smooth
    dyadicMultiplierCutoff_unit hc hs
    (annularLocalize_zero_of_small dyadicMultiplierCutoff_unit A 0 (by norm_num))
    (fun z hz => annularLocalize_zero_of_large dyadicMultiplierCutoff_zero A z (by linarith)) f x
  change Tendsto (fun N => ∑ j ∈ Finset.range N,
    operatorLiftConvolution (dyadicEuclideanMultiplierKernel σ j) g x) atTop
    (𝓝 (HalfHolder.eval (toUnitTorus x)
      ((homogeneousDyadicBlocks dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit
        dyadicMultiplierCutoff_zero hA).toMultiplier f))) at hblocks
  simp_rw [hcell] at hblocks
  have hzero : HalfHolder.eval (toUnitTorus x)
      (homogeneousHalfHolderMultiplier dyadicMultiplierCutoff_smooth
        dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero hA f) =
      HalfHolder.eval (toUnitTorus x)
        ((homogeneousDyadicBlocks dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit
          dyadicMultiplierCutoff_zero hA).toMultiplier f) := by
    simp [homogeneousHalfHolderMultiplier, hA0]
  rw [hzero]
  exact tendsto_nhds_unique hblocks hVlimit

end MultiplierAgreement

section PressureTensor

open ContinuousLinearMap UnitAddTorus

/-- Complex coordinates of a spatial tensor. -/
abbrev ComplexPressureTensor := Fin 3 → Fin 3 → ℂ

/-- Take the real part of the output of an operator on complex tensor coordinates. -/
def pressureTensorRealOutput :
    (ComplexPressureTensor →L[ℂ] ℂ) →L[ℝ] (ComplexPressureTensor →L[ℝ] ℝ) :=
  ((compL ℝ ComplexPressureTensor ℂ ℝ) Complex.reCLM).comp
    (restrictScalarsL ℂ ComplexPressureTensor ℂ ℝ ℝ)

@[simp] theorem pressureTensorRealOutput_apply
    (K : ComplexPressureTensor →L[ℂ] ℂ) (A : ComplexPressureTensor) :
    pressureTensorRealOutput K A = (K A).re := rfl

private def complexPressureTensorEntry (i j : Fin 3) : ComplexPressureTensor →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj j : (Fin 3 → ℂ) →L[ℂ] ℂ).comp
    (ContinuousLinearMap.proj i : ComplexPressureTensor →L[ℂ] (Fin 3 → ℂ))

private def pressureTensorWeight (ξ : Vec3) (i j : Fin 3) : ℝ :=
  (ξ i * ξ j) / ‖ξ‖ ^ 2

private theorem contDiffOn_pressureTensorWeight (i j : Fin 3) :
    ContDiffOn ℝ ∞ (fun ξ => pressureTensorWeight ξ i j) ({0}ᶜ : Set Vec3) := by
  have hcoord (a : Fin 3) : ContDiff ℝ ∞ (fun ξ : Vec3 => ξ a) :=
    (EuclideanSpace.proj (𝕜 := ℝ) a).contDiff
  have hsquared : ContDiff ℝ ∞ (fun ξ : Vec3 => ‖ξ‖ ^ 2) := by
    simp only [EuclideanSpace.real_norm_sq_eq]
    exact ContDiff.sum fun a _ => (hcoord a).pow 2
  refine ((hcoord i).mul (hcoord j)).contDiffOn.div hsquared.contDiffOn ?_
  intro ξ hξ
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr (by simpa using hξ))

private theorem pressureTensorWeight_pos_smul {c : ℝ} (hc : 0 < c) (ξ : Vec3) (i j : Fin 3) :
    pressureTensorWeight (c • ξ) i j = pressureTensorWeight ξ i j := by
  simp only [pressureTensorWeight, PiLp.smul_apply, smul_eq_mul, norm_smul,
    Real.norm_eq_abs, abs_of_pos hc, mul_pow]
  rw [show c * ξ i * (c * ξ j) = c ^ 2 * (ξ i * ξ j) by ring,
    mul_div_mul_left _ _ (pow_ne_zero 2 hc.ne')]

/-- The pressure symbol −Δ⁻¹ div div, with zero value at frequency zero. -/
def pressureTensorSymbol (ξ : Vec3) : ComplexPressureTensor →L[ℂ] ℂ :=
  -∑ i : Fin 3, ∑ j : Fin 3, (pressureTensorWeight ξ i j : ℂ) • complexPressureTensorEntry i j

theorem pressureTensorSymbol_apply (ξ : Vec3) (A : ComplexPressureTensor) :
    pressureTensorSymbol ξ A = -∑ i : Fin 3, ∑ j : Fin 3,
      ((ξ i * ξ j / ‖ξ‖ ^ 2 : ℝ) : ℂ) * A i j := by
  simp [pressureTensorSymbol, pressureTensorWeight, complexPressureTensorEntry, _root_.sum_apply]

@[simp] theorem pressureTensorSymbol_zero : pressureTensorSymbol 0 = 0 := by
  ext A
  simp [pressureTensorSymbol_apply]

@[simp] theorem pressureTensorSymbol_neg (ξ : Vec3) : pressureTensorSymbol (-ξ) = pressureTensorSymbol ξ := by
  ext A
  simp [pressureTensorSymbol_apply]

theorem pressureTensorSymbol_pos_smul (c : ℝ) (hc : 0 < c) (ξ : Vec3) :
    pressureTensorSymbol (c • ξ) = pressureTensorSymbol ξ := by
  simp only [pressureTensorSymbol, pressureTensorWeight_pos_smul hc]

theorem contDiffOn_pressureTensorSymbol :
    ContDiffOn ℝ ∞ pressureTensorSymbol ({0}ᶜ : Set Vec3) := by
  unfold pressureTensorSymbol
  refine (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ?_).neg
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_pressureTensorWeight i j)).smul contDiffOn_const

private theorem pressureTensorWeight_lattice (k : Fin 3 → ℤ) (i j : Fin 3) :
    (pressureTensorWeight (latticeVector k) i j : ℂ) =
      fourierDerivativeSymbol k i * fourierDerivativeSymbol k j * inverseLaplacianMode k := by
  have hnorm : ‖latticeVector k‖ ^ 2 = frequencyNormSq k := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [pressureTensorWeight, hnorm]
  have hcoords (a : Fin 3) : latticeVector k a = (k a : ℝ) := rfl
  simp only [hcoords, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_intCast]
  by_cases hk : k = 0
  · subst k
    simp [fourierDerivativeSymbol]
  · let c : ℂ := 2 * (Real.pi : ℂ)
    have hc : c ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
    have hN : (frequencyNormSq k : ℂ) ≠ 0 := by
      exact_mod_cast (frequencyNormSq_pos hk).ne'
    have hprod : (c * Complex.I * (k i : ℂ)) * (c * Complex.I * (k j : ℂ)) =
        -(c ^ 2) * ((k i : ℂ) * (k j : ℂ)) := by
      calc
        _ = c ^ 2 * Complex.I ^ 2 * ((k i : ℂ) * (k j : ℂ)) := by ring
        _ = _ := by rw [Complex.I_sq, mul_neg_one]
    change _ = ((c * Complex.I * (k i : ℂ)) * (c * Complex.I * (k j : ℂ))) *
        (-(c ^ 2 * (frequencyNormSq k : ℂ)))⁻¹
    rw [hprod]
    field_simp

/-- The lattice action is exactly the negative mean-zero Poisson inverse
of the two tensor divergences. -/
theorem pressureTensorSymbol_lattice_apply (k : Fin 3 → ℤ) (A : ComplexPressureTensor) :
    pressureTensorSymbol (latticeVector k) A =
      -inverseLaplacianMode k * ∑ i : Fin 3, ∑ j : Fin 3,
        fourierDerivativeSymbol k i * fourierDerivativeSymbol k j * A i j := by
  rw [pressureTensorSymbol_apply]
  change (-∑ i : Fin 3, ∑ j : Fin 3,
    (pressureTensorWeight (latticeVector k) i j : ℂ) * A i j) = _
  simp only [pressureTensorWeight_lattice, neg_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The single tensor divergence at one Fourier mode. -/
def tensorDivergenceMode (k : Fin 3 → ℤ) (A : ComplexPressureTensor) : ComplexVec3 :=
  fun i => ∑ j : Fin 3, fourierDerivativeSymbol k j * A i j

theorem pressureTensorSymbol_lattice_eq_neg_pressureCorrectionMode (k : Fin 3 → ℤ)
    (A : ComplexPressureTensor) :
    pressureTensorSymbol (latticeVector k) A = -pressureCorrectionMode k (tensorDivergenceMode k A) := by
  rw [pressureTensorSymbol_lattice_apply, pressureCorrectionMode, divergenceMode, neg_mul]
  congr 1
  unfold tensorDivergenceMode
  simp [Finset.mul_sum, mul_assoc]

/-- The pressure gradient is the nonlocal part of the projected tensor divergence. -/
theorem lerayMode_tensorDivergenceMode (k : Fin 3 → ℤ) (A : ComplexPressureTensor) :
    lerayMode k (tensorDivergenceMode k A) = tensorDivergenceMode k A +
      gradientMode k (pressureTensorSymbol (latticeVector k) A) := by
  rw [lerayMode_eq_sub_gradient, pressureTensorSymbol_lattice_eq_neg_pressureCorrectionMode]
  funext i
  simp [gradientMode, sub_eq_add_neg]

/-- The periodic multiplier maps the velocity tensor to its normalized pressure. -/
def complexPressureTensorMultiplier :
    HalfHolder (UnitAddTorus (Fin 3)) ComplexPressureTensor →L[ℝ]
      HalfHolder (UnitAddTorus (Fin 3)) ℂ :=
  homogeneousHalfHolderMultiplier dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit
    dyadicMultiplierCutoff_zero contDiffOn_pressureTensorSymbol

/-- The real pressure obtained from complex coordinates of a real tensor. -/
def pressureTensorMultiplier :
    HalfHolder (UnitAddTorus (Fin 3)) ComplexPressureTensor →L[ℝ]
      HalfHolder (UnitAddTorus (Fin 3)) ℝ :=
  (HalfHolder.map Complex.reCLM).comp complexPressureTensorMultiplier

theorem mFourierCoeff_complexPressureTensorMultiplier
    (f : HalfHolder (UnitAddTorus (Fin 3)) ComplexPressureTensor) (k : Fin 3 → ℤ) :
    mFourierCoeff (continuousHalfHolder (complexPressureTensorMultiplier f)) k =
      -inverseLaplacianMode k * ∑ i : Fin 3, ∑ j : Fin 3,
        fourierDerivativeSymbol k i * fourierDerivativeSymbol k j *
          mFourierCoeff (continuousHalfHolder f) k i j := by
  rw [← pressureTensorSymbol_lattice_apply]
  exact mFourierCoeff_homogeneousHalfHolderMultiplier dyadicMultiplierCutoff_smooth
    dyadicMultiplierCutoff_unit dyadicMultiplierCutoff_zero contDiffOn_pressureTensorSymbol
    (fun c hc ξ _ => pressureTensorSymbol_pos_smul c hc ξ) f k

/-- A continuous pressure whose coefficients solve the normalized Poisson equation
is the pressure multiplier applied to the tensor. -/
theorem complexPressureTensorMultiplier_eq_of_fourierPoisson
    (f : HalfHolder (UnitAddTorus (Fin 3)) ComplexPressureTensor)
    (p : C(UnitAddTorus (Fin 3), ℂ)) (hmean : mFourierCoeff p 0 = 0)
    (hPoisson : ∀ k : Fin 3 → ℤ, laplacianMode k * mFourierCoeff p k =
      -∑ i : Fin 3, ∑ j : Fin 3, fourierDerivativeSymbol k i * fourierDerivativeSymbol k j *
        mFourierCoeff (continuousHalfHolder f) k i j) :
    continuousHalfHolder (complexPressureTensorMultiplier f) = p := by
  apply eq_of_mFourierCoeff_eq
  intro k
  rw [mFourierCoeff_complexPressureTensorMultiplier]
  by_cases hk : k = 0
  · subst k
    simp [hmean]
  · rw [neg_mul, ← mul_neg, ← hPoisson k, ← mul_assoc, inverseLaplacianMode,
      inv_mul_cancel₀ (laplacianMode_ne_zero hk), one_mul]

/-- The tensor product of real velocities in the complex coordinate space of the symbol. -/
def velocityPressureTensor : Vec3 →L[ℝ] Vec3 →L[ℝ] ComplexPressureTensor := by
  let L : Vec3 →ₗ[ℝ] Vec3 →ₗ[ℝ] ComplexPressureTensor := by
    apply LinearMap.mk₂ ℝ (fun (u v : Vec3) i j => (↑(u i * v j) : ℂ))
    · intro u u' v
      funext i j
      simp [PiLp.add_apply, Pi.add_apply, add_mul]
    · intro c u v
      funext i j
      simp [PiLp.smul_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul, mul_assoc]
    · intro u v v'
      funext i j
      simp [PiLp.add_apply, Pi.add_apply, mul_add]
    · intro c u v
      funext i j
      simp [PiLp.smul_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul, mul_left_comm]
  refine L.mkContinuous₂ 1 fun u v => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i =>
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  change ‖((u i * v j : ℝ) : ℂ)‖ ≤ _
  rw [Complex.norm_real, norm_mul]
  exact mul_le_mul (PiLp.norm_apply_le u i) (PiLp.norm_apply_le v j)
    (norm_nonneg _) (norm_nonneg _)

@[simp] theorem velocityPressureTensor_apply (u v : Vec3) (i j : Fin 3) :
    velocityPressureTensor u v i j = (↑(u i * v j) : ℂ) := rfl


/-- Uniform convergence of a scalar derivative controls the corresponding
derivative of its gradient, with one extra scalar derivative. -/
theorem tendstoUniformlyOn_iteratedFDeriv_gradient
    {ι X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {l : Filter ι} {U : Set X} {f : ι → X → ℝ} {g : X → ℝ} (d : ℕ)
    (h : TendstoUniformlyOn (fun i => iteratedFDeriv ℝ (d + 1) (f i))
      (iteratedFDeriv ℝ (d + 1) g) l U) :
    TendstoUniformlyOn (fun i => iteratedFDeriv ℝ d (gradient (f i)))
      (iteratedFDeriv ℝ d (gradient g)) l U := by
  let R : (X →L[ℝ] ℝ) ≃L[ℝ] X := (InnerProductSpace.toDual ℝ X).symm.toContinuousLinearEquiv
  let C := (continuousMultilinearCurryRightEquiv' ℝ d X ℝ).toContinuousLinearEquiv
  let L := C.trans (R.continuousMultilinearMapCongrRight (fun _ : Fin d => X))
  have hjet (q : X → ℝ) :
      iteratedFDeriv ℝ d (gradient q) = L ∘ iteratedFDeriv ℝ (d + 1) q := by
    funext x
    change iteratedFDeriv ℝ d (R ∘ fderiv ℝ q) x = _
    rw [R.iteratedFDeriv_comp_left]
    have hC : C (iteratedFDeriv ℝ (d + 1) q x) = iteratedFDeriv ℝ d (fderiv ℝ q) x := by
      rw [iteratedFDeriv_succ_eq_comp_right]
      exact C.apply_symm_apply _
    change _ = R.toContinuousLinearMap.compContinuousMultilinearMap
      (C (iteratedFDeriv ℝ (d + 1) q x))
    rw [hC]
  simp only [hjet]
  exact L.toContinuousLinearMap.uniformContinuous.comp_tendstoUniformlyOn h


/-- The annular symbol for the nonlocal pressure part of the projected tensor divergence. -/
def pressureTensorAnnularSymbol : 𝓢(Vec3, ComplexPressureTensor →L[ℂ] ℂ) :=
  (annularLocalize_compact dyadicMultiplierCutoff_zero pressureTensorSymbol).toSchwartzMap
    (annularLocalize_smooth dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit
      contDiffOn_pressureTensorSymbol)

/-- Restrict the actual periodic pressure kernel to the separated source set. -/
def periodicFarPressure (S : Set Vec3) (P : Vec3 → ComplexPressureTensor) (x : Vec3) : ℝ :=
  ∫ y in S ∩ multiplierKernelCell,
    pressureTensorRealOutput (dyadicPeriodicMultiplierKernel pressureTensorAnnularSymbol (x - y)) (P y)

/-- The Fourier-defined real pressure multiplier is the separated far integral
on sources supported away from the target. -/
theorem eval_pressureTensorMultiplier_eq_periodicFarPressure
    (f : HalfHolder (UnitAddTorus (Fin 3)) ComplexPressureTensor) (x : Vec3)
    {S : Set Vec3} (hS : IsCompact S) (hsep : ∀ y ∈ S, x - y ∈ offOrigin)
    (hvanish : ∀ y ∈ multiplierKernelCell, y ∉ S → HalfHolder.eval (toUnitTorus y) f = 0) :
    HalfHolder.eval (toUnitTorus x) (pressureTensorMultiplier f) =
      periodicFarPressure S (fun y => HalfHolder.eval (toUnitTorus y) f) x := by
  let g := fun y => HalfHolder.eval (toUnitTorus y) f
  have hq : Continuous toUnitTorus := continuous_pi fun i =>
    (AddCircle.continuous_mk' (1 : ℝ)).comp (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i)
  have hg : Continuous g := (continuousHalfHolder f).continuous.comp hq
  have hK : ContinuousOn (fun y =>
      dyadicPeriodicMultiplierKernel pressureTensorAnnularSymbol (x - y)) S :=
    ((contDiffOn_dyadicPeriodicMultiplierKernel pressureTensorAnnularSymbol).1.continuousOn).comp
      (continuous_const.sub continuous_id).continuousOn hsep
  have hi : IntegrableOn (fun y => dyadicPeriodicMultiplierKernel pressureTensorAnnularSymbol
      (x - y) (g y)) (S ∩ multiplierKernelCell) :=
    (hK.clm_apply hg.continuousOn |>.integrableOn_compact hS).mono_set inter_subset_left
  unfold pressureTensorMultiplier
  rw [ContinuousLinearMap.comp_apply, HalfHolder.eval_map]
  change Complex.reCLM (HalfHolder.eval (toUnitTorus x)
    (homogeneousHalfHolderMultiplier dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit
      dyadicMultiplierCutoff_zero contDiffOn_pressureTensorSymbol f)) = _
  rw [eval_homogeneousHalfHolderMultiplier_eq_periodicFarIntegral contDiffOn_pressureTensorSymbol
    pressureTensorSymbol_zero f x hS hsep hvanish]
  exact (Complex.reCLM.integral_comp_comm hi).symm

/-- Uniform velocity convergence gives convergence of each spatial jet of
the actual far pressure gradient from the projected tensor divergence. -/
theorem tendstoUniformlyOn_periodicFarPressureGradient_spatial_derivatives
    {ι : Type*} {l : Filter ι} {K S : Set Vec3} (hK : IsCompact K) (hS : IsCompact S)
    (hsep : ∀ x ∈ K, ∀ y ∈ S, x - y ∈ offOrigin)
    {v : ι → Vec3 → Vec3} {w : Vec3 → Vec3}
    (hv : TendstoUniformlyOn v w l S) (hvc : ∀ i, ContinuousOn (v i) S)
    (hwc : ContinuousOn w S) (m : ℕ) :
    ∃ U : Set Vec3, IsOpen U ∧ K ⊆ U ∧
      let farGrad (b : Vec3 → Vec3) :=
        gradient (periodicFarPressure S (fun y => velocityPressureTensor (b y) (b y)))
      ∀ d ≤ m, TendstoUniformlyOn (fun i => iteratedFDeriv ℝ d (farGrad (v i)))
        (iteratedFDeriv ℝ d (farGrad w)) l U := by
  obtain ⟨U, hU, hKU, _, hjet⟩ := tendstoUniformlyOn_periodicFarMultiplier_spatial_derivatives
    pressureTensorAnnularSymbol pressureTensorRealOutput (volume.restrict multiplierKernelCell)
    hK hS hsep velocityPressureTensor hv hvc hwc (m + 1)
  refine ⟨U, hU, hKU, fun d hd => ?_⟩
  apply tendstoUniformlyOn_iteratedFDeriv_gradient d
  unfold periodicFarPressure
  simpa only [Measure.restrict_restrict hS.isClosed.measurableSet] using
    hjet (d + 1) (Nat.add_le_add_right hd 1)

set_option maxHeartbeats 800000 in
/-- Each spatial derivative of the separated pressure kernel is bounded by the
(L^1) tensor difference on the source portion of the fundamental cell. -/
theorem exists_norm_iteratedFDeriv_periodicFarPressure_sub_le
    {K S : Set Vec3} (hK : IsCompact K) (hS : IsCompact S)
    (hsep : ∀ x ∈ K, ∀ y ∈ S, x - y ∈ offOrigin) :
    ∃ U : Set Vec3, IsOpen U ∧ K ⊆ U ∧ ∀ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ P Q : Vec3 → ComplexPressureTensor,
        IntegrableOn P (S ∩ multiplierKernelCell) →
        IntegrableOn Q (S ∩ multiplierKernelCell) →
        ∀ x ∈ U,
          ‖iteratedFDeriv ℝ d (periodicFarPressure S P) x -
            iteratedFDeriv ℝ d (periodicFarPressure S Q) x‖ ≤
          C * ∫ y in S ∩ multiplierKernelCell, ‖P y - Q y‖ := by
  let μ := (volume : Measure Vec3).restrict multiplierKernelCell
  let ν := μ.restrict S
  have hν : ν = (volume : Measure Vec3).restrict (S ∩ multiplierKernelCell) :=
    Measure.restrict_restrict hS.isClosed.measurableSet
  let J := periodicFarMultiplierJet pressureTensorAnnularSymbol pressureTensorRealOutput
  obtain ⟨U, hU, hKU, hMeas, hNorm, hDeriv⟩ :=
    exists_periodicFarMultiplierJet_bounds pressureTensorAnnularSymbol pressureTensorRealOutput
      hK hS hsep μ
  have hfar (P : Vec3 → ComplexPressureTensor) :
      periodicFarPressure S P = (fun x => (farKernelIntegral ν (J 0) P x).curry0) := by
    funext x
    let C := continuousMultilinearCurryFin0 ℝ Vec3 ℝ
    change (∫ y in S ∩ multiplierKernelCell,
      pressureTensorRealOutput (dyadicPeriodicMultiplierKernel pressureTensorAnnularSymbol
        (x - y)) (P y)) = C (∫ y, J 0 x y (P y) ∂ν)
    rw [← hν]
    calc
      _ = ∫ y, C (J 0 x y (P y)) ∂ν := rfl
      _ = _ := LinearIsometry.integral_comp_comm (μ := ν) C.toLinearIsometry _
  have hjet (P : Vec3 → ComplexPressureTensor) (hP : Integrable P ν)
      (d : ℕ) (x : Vec3) (hx : x ∈ U) :
      iteratedFDeriv ℝ d (periodicFarPressure S P) x = farKernelIntegral ν (J d) P x := by
    rw [hfar]
    exact (contDiffOn_farKernelIntegral_of_spatial_jets hU hP hMeas hNorm hDeriv d).2 d le_rfl hx
  have hPm (P : Vec3 → ComplexPressureTensor) (hP : Integrable P ν)
      (d : ℕ) (x : Vec3) (hx : x ∈ U) :
      AEStronglyMeasurable (fun y => J d x y (P y)) ν := by
    have hEval : Continuous (fun z : (ComplexPressureTensor →L[ℝ] (Vec3 [×d]→L[ℝ] ℝ)) ×
        ComplexPressureTensor => z.1 z.2) := continuous_fst.clm_apply continuous_snd
    exact hEval.comp_aestronglyMeasurable ((hMeas d x hx).prodMk hP.aestronglyMeasurable)
  refine ⟨U, hU, hKU, fun d => ?_⟩
  obtain ⟨C, hC⟩ := hNorm d
  refine ⟨max 0 C, le_max_left _ _, fun P Q hP hQ x hx => ?_⟩
  have hPi : Integrable P ν := by rw [hν]; exact hP
  have hQi : Integrable Q ν := by rw [hν]; exact hQ
  rw [hjet P hPi d x hx, hjet Q hQi d x hx, ← hν]
  exact norm_farKernelIntegral_sub_le (hC.mono fun y hy => (hy x hx).trans (le_max_right _ _)) hPi hQi
    (hPm P hPi d x hx) (hPm Q hQi d x hx)

/-- Taking the gradient loses exactly one scalar derivative in the operator
norm of the spatial jets. -/
theorem norm_iteratedFDeriv_gradient_sub_eq
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (d : ℕ) (f g : X → ℝ) (x : X) :
    ‖iteratedFDeriv ℝ d (gradient f) x - iteratedFDeriv ℝ d (gradient g) x‖ =
      ‖iteratedFDeriv ℝ (d + 1) f x - iteratedFDeriv ℝ (d + 1) g x‖ := by
  let R := (InnerProductSpace.toDual ℝ X).symm
  let C := continuousMultilinearCurryRightEquiv' ℝ d X ℝ
  let L := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin d => X)
    (X →L[ℝ] ℝ) X R.toLinearIsometry.toContinuousLinearMap
  have hjet (q : X → ℝ) : iteratedFDeriv ℝ d (gradient q) x =
      L (C (iteratedFDeriv ℝ (d + 1) q x)) := by
    change iteratedFDeriv ℝ d (R.toContinuousLinearEquiv ∘ fderiv ℝ q) x = _
    rw [R.toContinuousLinearEquiv.iteratedFDeriv_comp_left]
    have hC : C (iteratedFDeriv ℝ (d + 1) q x) = iteratedFDeriv ℝ d (fderiv ℝ q) x := by
      rw [iteratedFDeriv_succ_eq_comp_right]
      exact C.apply_symm_apply _
    rw [hC]
    rfl
  rw [hjet f, hjet g]
  let a := iteratedFDeriv ℝ (d + 1) f x
  let b := iteratedFDeriv ℝ (d + 1) g x
  change ‖L (C a) - L (C b)‖ = ‖a - b‖
  have hlinear : L (C (a - b)) = L (C a) - L (C b) := by
    calc
      _ = L (C a - C b) := congrArg (fun z => L z) (C.toLinearEquiv.map_sub a b)
      _ = _ := ContinuousLinearMap.map_sub L (C a) (C b)
  rw [← hlinear]
  exact (R.toLinearIsometry.norm_compContinuousMultilinearMap _).trans (C.norm_map _)

/-- The nonlocal pressure gradient obeys the far-field estimate of
Proposition 8.4 on each spatial derivative. -/
theorem exists_norm_iteratedFDeriv_periodicFarPressureGradient_sub_le
    {K S : Set Vec3} (hK : IsCompact K) (hS : IsCompact S)
    (hsep : ∀ x ∈ K, ∀ y ∈ S, x - y ∈ offOrigin) :
    ∃ U : Set Vec3, IsOpen U ∧ K ⊆ U ∧ ∀ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ P Q : Vec3 → ComplexPressureTensor,
        IntegrableOn P (S ∩ multiplierKernelCell) →
        IntegrableOn Q (S ∩ multiplierKernelCell) →
        ∀ x ∈ U,
          ‖iteratedFDeriv ℝ d (gradient (periodicFarPressure S P)) x -
            iteratedFDeriv ℝ d (gradient (periodicFarPressure S Q)) x‖ ≤
          C * ∫ y in S ∩ multiplierKernelCell, ‖P y - Q y‖ := by
  obtain ⟨U, hU, hKU, hbd⟩ := exists_norm_iteratedFDeriv_periodicFarPressure_sub_le hK hS hsep
  refine ⟨U, hU, hKU, fun d => ?_⟩
  obtain ⟨C, hC₀, hC⟩ := hbd (d + 1)
  refine ⟨C, hC₀, fun P Q hP hQ x hx => ?_⟩
  rw [norm_iteratedFDeriv_gradient_sub_eq]
  exact hC P Q hP hQ x hx

end PressureTensor

end
end TorusEuler
