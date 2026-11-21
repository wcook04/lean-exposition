import TorusEuler.PeriodicLift
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open Filter Set
open scoped ContDiff Topology

namespace TorusEuler

private noncomputable def latticeDetector (x : Vec3) : ℝ :=
  ∑ i : Fin 3, Real.sin (x i * Real.pi) ^ 2

private theorem contDiff_latticeDetector : ContDiff ℝ ∞ latticeDetector := by
  change ContDiff ℝ ∞ (fun x : Vec3 => ∑ i : Fin 3, Real.sin (x i * Real.pi) ^ 2)
  apply ContDiff.sum
  intro i _
  have hi : ContDiff ℝ ∞ (fun x : Vec3 => x i) := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  exact (Real.contDiff_sin.comp (hi.mul contDiff_const)).pow 2

private theorem latticeDetector_nonneg (x : Vec3) : 0 ≤ latticeDetector x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem latticeDetector_eq_zero_iff (x : Vec3) :
    latticeDetector x = 0 ↔ x ∈ range latticeVector := by
  constructor
  · intro hx
    have hsin (i : Fin 3) : Real.sin (x i * Real.pi) = 0 := by
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun (i : Fin 3) _ =>
        sq_nonneg (Real.sin (x i * Real.pi)))).1 hx i (Finset.mem_univ i)
      exact sq_eq_zero_iff.mp hi
    choose n hn using fun i => Real.sin_eq_zero_iff.mp (hsin i)
    refine ⟨n, PiLp.ext fun i => ?_⟩
    exact mul_right_cancel₀ Real.pi_ne_zero (hn i)
  · rintro ⟨n, rfl⟩
    change (∑ i : Fin 3, Real.sin ((n i : ℝ) * Real.pi) ^ 2) = 0
    simp only [Real.sin_int_mul_pi, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]

private theorem spatiallyPeriodic_latticeDetector : SpatiallyPeriodic latticeDetector := by
  intro n x
  unfold latticeDetector
  apply Finset.sum_congr rfl
  intro i _
  change Real.sin ((x i + (n i : ℝ)) * Real.pi) ^ 2 = Real.sin (x i * Real.pi) ^ 2
  have hcos :
      Real.cos (2 * ((x i + (n i : ℝ)) * Real.pi)) = Real.cos (2 * (x i * Real.pi)) := by
    rw [show 2 * ((x i + (n i : ℝ)) * Real.pi) =
      2 * (x i * Real.pi) + (n i : ℝ) * (2 * Real.pi) by ring, Real.cos_add_int_mul_two_pi]
  rw [Real.cos_two_mul_eq_one_sub, Real.cos_two_mul_eq_one_sub] at hcos
  linarith only [hcos]

/-- The cutoff in Proposition 8.4. It equals one on a neighborhood of the
compact target and zero on a neighborhood of the singular lattice. Its
complementary support is disjoint from the target modulo the lattice. -/
theorem exists_periodic_offOrigin_cutoff
    {K : Set Vec3} (hK : IsCompact K) (hKo : K ⊆ offOrigin) :
    ∃ (χ : Vec3 → ℝ) (U V : Set Vec3),
      ContDiff ℝ ∞ χ ∧ SpatiallyPeriodic χ ∧ (∀ x, χ x ∈ Icc 0 1) ∧
      IsOpen U ∧ K ⊆ U ∧ EqOn χ (fun _ => 1) U ∧
      IsOpen V ∧ range latticeVector ⊆ V ∧ EqOn χ (fun _ => 0) V ∧
      tsupport χ ⊆ offOrigin ∧
      ∀ x ∈ K, ∀ y ∈ tsupport (fun z => 1 - χ z), x - y ∈ offOrigin := by
  by_cases hne : K.Nonempty
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne contDiff_latticeDetector.continuous.continuousOn
    let d := latticeDetector x₀
    have hd : 0 < d := lt_of_le_of_ne (latticeDetector_nonneg x₀) fun hz =>
      (hKo hx₀) ((latticeDetector_eq_zero_iff x₀).1 hz.symm)
    let b : ContDiffBump (0 : ℝ) := ⟨d / 4, d / 2, by linarith, by linarith⟩
    let χ := fun x : Vec3 => 1 - b (latticeDetector x)
    let U := {x : Vec3 | d / 2 < latticeDetector x}
    let V := {x : Vec3 | latticeDetector x < d / 4}
    have hU : IsOpen U := isOpen_lt continuous_const contDiff_latticeDetector.continuous
    have hV : IsOpen V := isOpen_lt contDiff_latticeDetector.continuous continuous_const
    have hlatV : range latticeVector ⊆ V := by
      intro x hx
      change latticeDetector x < d / 4
      rw [(latticeDetector_eq_zero_iff x).2 hx]
      linarith
    have hKU : K ⊆ U := by
      intro x hx
      change d / 2 < latticeDetector x
      exact (show d / 2 < d by linarith).trans_le (hmin hx)
    have hχU : EqOn χ (fun _ => 1) U := by
      intro x hx
      have hx' : b.rOut ≤ dist (latticeDetector x) 0 := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (latticeDetector_nonneg x)]
        exact (show d / 2 < latticeDetector x from hx).le
      simp only [χ, b.zero_of_le_dist hx', sub_zero]
    have hχV : EqOn χ (fun _ => 0) V := by
      intro x hx
      have hx' : latticeDetector x ∈ Metric.closedBall 0 b.rIn := by
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg (latticeDetector_nonneg x)]
        exact (show latticeDetector x < d / 4 from hx).le
      simp only [χ, b.one_of_mem_closedBall hx', sub_self]
    have hsupp : tsupport χ ⊆ Vᶜ :=
      closure_minimal (fun _ hx hv => hx (hχV hv)) hV.isClosed_compl
    have hfar : tsupport (fun z => 1 - χ z) ⊆ Uᶜ := by
      apply closure_minimal _ hU.isClosed_compl
      intro x hx hxU
      apply hx
      change 1 - χ x = 0
      rw [hχU hxU, sub_self]
    refine ⟨χ, U, V, contDiff_const.sub (b.contDiff.comp contDiff_latticeDetector),
      fun n x => by simp only [χ, spatiallyPeriodic_latticeDetector n x],
      fun x => ⟨sub_nonneg.mpr b.le_one, sub_le_self _ b.nonneg⟩,
      hU, hKU, hχU, hV, hlatV, hχV, fun _ hx hz => hsupp hx (hlatV hz), ?_⟩
    intro x hx y hy hxy
    obtain ⟨n, hn⟩ := hxy
    have hshift : y + latticeVector n = x := by rw [hn]; abel
    have hρ : latticeDetector x = latticeDetector y := by
      rw [← hshift, spatiallyPeriodic_latticeDetector n y]
    have hyU : y ∈ U := by
      change d / 2 < latticeDetector y
      rw [← hρ]
      exact hKU hx
    exact hfar hy hyU
  · have hKe : K = ∅ := not_nonempty_iff_eq_empty.mp hne
    subst K
    refine ⟨fun _ => 0, ∅, univ, contDiff_const, fun _ _ => rfl, fun _ => ⟨le_rfl, zero_le_one⟩,
      isOpen_empty, empty_subset _, by simp, isOpen_univ, subset_univ _, fun _ _ => rfl, ?_, by simp⟩
    simp [tsupport]

/-- A cutoff supported away from the singular lattice turns a locally smooth
field into an ambient smooth field, even if the original field is arbitrary
on the lattice. -/
theorem contDiff_cutoff_smul_of_contDiffOn_offOrigin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    {χ : Vec3 → ℝ} {f : Vec3 → E} (hχ : ContDiff ℝ m χ)
    (hsupp : tsupport χ ⊆ offOrigin) (hf : ContDiffOn ℝ m f offOrigin) :
    ContDiff ℝ m (fun x => χ x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ offOrigin
  · exact hχ.contDiffAt.smul ((hf x hx).contDiffAt (isOpen_offOrigin.mem_nhds hx))
  · apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
    have hxS : x ∉ tsupport χ := fun h => hx (hsupp h)
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxS] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]

/-- Multiplying by the fixed cutoff transfers convergence of spatial jets
on the compact part of its support to convergence on the entire compact cell. -/
theorem tendstoUniformlyOn_cutoff_smul_spatial_jets
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {l : Filter ι}
    {C : Set Vec3} (hC : IsCompact C) {m : ℕ} {χ : Vec3 → ℝ} {f : ι → Vec3 → E}
    {g : Vec3 → E} (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ offOrigin)
    (hf : ∀ i, ContDiffOn ℝ m (f i) offOrigin) (hg : ContDiffOn ℝ m g offOrigin)
    (hJ : ∀ k ≤ m, TendstoUniformlyOn (fun i => iteratedFDeriv ℝ k (f i))
      (iteratedFDeriv ℝ k g) l (C ∩ tsupport χ)) :
    ∀ k ≤ m, TendstoUniformlyOn
      (fun i => iteratedFDeriv ℝ k (fun x => χ x • f i x))
      (iteratedFDeriv ℝ k (fun x => χ x • g x)) l C := by
  intro k hk
  have hχm : ContDiff ℝ m χ := hχ.of_le (by simp)
  let weight (x : Vec3) := ∑ j ∈ Finset.range (k + 1),
    (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j χ x‖
  have hweight : Continuous weight := by
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul (hχ.continuous_iteratedFDeriv (by simp)).norm
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hweight.continuousOn
  let B := max M 0
  have hB : 0 < B + 1 := add_pos_of_nonneg_of_pos (le_max_right _ _) zero_lt_one
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  let δ := ε / (B + 1)
  have hδ : 0 < δ := div_pos hε hB
  have hsmall : ∀ᶠ i in l, ∀ j ∈ Finset.range (k + 1), ∀ x ∈ C ∩ tsupport χ,
      ‖iteratedFDeriv ℝ (k - j) (f i) x - iteratedFDeriv ℝ (k - j) g x‖ < δ := by
    rw [eventually_all_finset]
    intro j _
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hJ (k - j) ((Nat.sub_le ..).trans hk)) δ hδ]
      with i hi x hx
    rw [← dist_eq_norm, dist_comm]
    exact hi x hx
  filter_upwards [hsmall] with i hi x hx
  by_cases hxS : x ∈ tsupport χ
  · have hxO := hsupp hxS
    have hxOn := isOpen_offOrigin.mem_nhds hxO
    have hfk : ContDiffAt ℝ k (fun y => χ y • f i y) x :=
      (contDiff_cutoff_smul_of_contDiffOn_offOrigin hχm hsupp (hf i)).contDiffAt.of_le (by exact_mod_cast hk)
    have hgk : ContDiffAt ℝ k (fun y => χ y • g y) x :=
      (contDiff_cutoff_smul_of_contDiffOn_offOrigin hχm hsupp hg).contDiffAt.of_le (by exact_mod_cast hk)
    have heq : (fun y => χ y • f i y) - (fun y => χ y • g y) = fun y => χ y • (f i y - g y) := by
      funext y
      exact (smul_sub _ _ _).symm
    rw [dist_comm, dist_eq_norm, ← iteratedFDeriv_sub_apply hfk hgk, heq]
    have hprod := norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ) hχm.contDiffOn
      ((hf i).sub hg) isOpen_offOrigin.uniqueDiffOn hxO (n := k) (by exact_mod_cast hk)
    simp_rw [iteratedFDerivWithin_of_isOpen _ isOpen_offOrigin hxO] at hprod
    refine hprod.trans_lt ?_
    calc
      _ ≤ weight x * δ := by
        dsimp only [weight]
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro j hj
        have hsub (a : Vec3 → E) (ha : ContDiffOn ℝ m a offOrigin) :
            ContDiffAt ℝ (↑(k - j : ℕ)) a x :=
          ((ha x hxO).contDiffAt hxOn).of_le (by exact_mod_cast (Nat.sub_le k j).trans hk)
        rw [← Pi.sub_def, iteratedFDeriv_sub_apply (hsub (f i) (hf i)) (hsub g hg)]
        exact mul_le_mul_of_nonneg_left (hi j hj x ⟨hx, hxS⟩).le
          (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
      _ ≤ B * δ := mul_le_mul_of_nonneg_right
        ((le_abs_self _).trans ((hM x hx).trans (le_max_left _ _))) hδ.le
      _ < (B + 1) * δ := mul_lt_mul_of_pos_right (lt_add_one B) hδ
      _ = ε := by rw [mul_comm, div_mul_cancel₀ _ hB.ne']
  · have heq : (fun y => χ y • g y) =ᶠ[𝓝 x] (fun y => χ y • f i y) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxS] with y hy
      simp only [image_eq_zero_of_notMem_tsupport hy, zero_smul]
    rw [(heq.iteratedFDeriv ℝ k).self_of_nhds, dist_self]
    exact hε

/-- The near part of the projected Euler nonlinearity is continuous in the
spatial norms of Proposition 8.4 once the tensor product, cutoff multiplication,
divergence and zero-order projection are supplied as bounded maps. -/
theorem tendsto_nearPressure_of_bounded_maps
    {ι V A B E : Type*} {l : Filter ι}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (tensor : V →L[ℝ] V →L[ℝ] A) (cutoff : A →L[ℝ] B)
    (divergence : B →L[ℝ] E) (leray : E →L[ℝ] E)
    {v : ι → V} {w : V} (hv : Tendsto v l (𝓝 w)) :
    Tendsto (fun i => -leray (divergence (cutoff (tensor (v i) (v i))))) l
      (𝓝 (-leray (divergence (cutoff (tensor w w))))) := by
  have hTensor : Continuous (fun z => tensor z z) := tensor.continuous.clm_apply continuous_id
  have hNear : Continuous (fun z => -leray (divergence (cutoff (tensor z z)))) :=
    (leray.continuous.comp (divergence.continuous.comp (cutoff.continuous.comp hTensor))).neg
  exact hNear.continuousAt.tendsto.comp hv

end TorusEuler
