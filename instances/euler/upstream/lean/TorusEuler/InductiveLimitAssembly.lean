import TorusEuler.UniformSeries
import TorusEuler.OffOriginLimits
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.SpecificLimits.Basic

/-! The increment estimates of Theorem 7.1 on the common closed slab
supply the velocity and spatial-jet convergence in Propositions 8.1 and 8.4. -/

open Filter Metric Set
open scoped ContDiff Pointwise Topology

namespace TorusEuler

/-- The schedule (1.14) has the reciprocal-frequency tail used in §8.1.
The schedule can grow faster than the quadratic lower bound. -/
theorem reciprocal_inductive_frequency_tail {freq : ℕ → ℝ} (hinit : 2 ≤ freq 0)
    (hstep : ∀ n, freq n ^ 2 ≤ freq (n + 1)) (j : ℕ) :
    Summable (fun k => (freq (j + k))⁻¹) ∧
      (∑' k : ℕ, (freq (j + k))⁻¹) ≤ 2 * (freq j)⁻¹ := by
  have hfreq : ∀ n, 2 ≤ freq n := by
    intro n
    induction n with
    | zero => exact hinit
    | succ n ih => exact (by nlinarith : (2 : ℝ) ≤ freq n ^ 2).trans (hstep n)
  have hdouble (n : ℕ) : 2 * freq n ≤ freq (n + 1) :=
    (by nlinarith [hfreq n] : 2 * freq n ≤ freq n ^ 2).trans (hstep n)
  have hinv (n : ℕ) : (freq (n + 1))⁻¹ ≤ (freq n)⁻¹ * (1 / 2) := by
    have hp : 0 < freq n := by linarith [hfreq n]
    simpa only [mul_inv_rev, div_eq_mul_inv, one_mul, mul_comm] using
      (inv_anti₀ (by positivity : 0 < 2 * freq n) (hdouble n))
  have hmajor (k : ℕ) : (freq (j + k))⁻¹ ≤ (freq j)⁻¹ * (1 / 2 : ℝ) ^ k := by
    induction k with
    | zero => simp
    | succ k hk =>
      calc
        _ ≤ (freq (j + k))⁻¹ * (1 / 2) := hinv (j + k)
        _ ≤ ((freq j)⁻¹ * (1 / 2 : ℝ) ^ k) * (1 / 2) :=
          mul_le_mul_of_nonneg_right hk (by norm_num)
        _ = _ := by rw [pow_succ, mul_assoc]
  have hg := summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hs : Summable (fun k => (freq (j + k))⁻¹) :=
    (hg.mul_left (freq j)⁻¹).of_nonneg_of_le
      (fun k => inv_nonneg.mpr (by linarith [hfreq (j + k)])) hmajor
  refine ⟨hs, (hs.tsum_le_tsum hmajor (hg.mul_left (freq j)⁻¹)).trans_eq ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  ring

/-- On each preterminal prefix, all sufficiently late oscillations vanish
at every spatial point. The increment at grade `n + 1` has parent `n`. -/
theorem inductive_oscillations_eventually_zero_on_prefix {activation : ℕ → ℝ}
    {T S : ℝ} {O : ℕ → Velocity}
    (hactivation : Tendsto activation atTop (𝓝 T)) (hST : S < T)
    (hO : ∀ n ≥ 2, ∀ t ∈ Icc 0 (activation n), O n t = 0) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc 0 S, EqOn (O (n + 1) t) 0 univ := by
  have he : ∀ᶠ n in atTop, S < activation n := hactivation.eventually (Ioi_mem_nhds hST)
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  refine ⟨max N 1, fun n hn t ht x _ => ?_⟩
  have h := hN (n + 1) ((le_max_left N 1).trans (hn.trans (Nat.le_succ n)))
  have hge : 2 ≤ n + 1 := Nat.succ_le_succ ((le_max_right N 1).trans hn)
  exact congrFun (hO (n + 1) hge t ⟨ht.1, ht.2.trans h.le⟩) x

/-- Joint smoothness of a stage on its closed slab gives smooth spatial
slices and continuity of all their spatial derivatives, including at the
two temporal endpoints. -/
theorem stage_spatial_jets_of_joint_smoothness {S : ℝ} {u : Velocity} (hS : 0 < S)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 S ×ˢ (univ : Set Vec3))) :
    (∀ t ∈ Icc 0 S, ContDiff ℝ ∞ (u t)) ∧
    ∀ m : ℕ, ContinuousOn
      (fun z : ℝ × Vec3 => iteratedFDeriv ℝ m (u z.1) z.2) (Icc 0 S ×ˢ (univ : Set Vec3)) := by
  let slab := Icc (0 : ℝ) S ×ˢ (univ : Set Vec3)
  have hUnique : UniqueDiffOn ℝ slab := (uniqueDiffOn_Icc hS).prod uniqueDiffOn_univ
  constructor
  · intro t ht
    have hemb : ContDiff ℝ ∞ (fun x : Vec3 => (t, x)) := contDiff_const.prodMk contDiff_id
    exact contDiffOn_univ.mp (hu.comp hemb.contDiffOn (fun _ _ => ⟨ht, mem_univ _⟩))
  · intro m
    let L := ContinuousLinearMap.inr ℝ ℝ Vec3
    let C := ContinuousMultilinearMap.compContinuousLinearMapL (F := Vec3) (fun _ : Fin m => L)
    refine (C.continuous.comp_continuousOn
      (hu.continuousOn_iteratedFDerivWithin (by simp) hUnique)).congr ?_
    rintro ⟨t, x⟩ ht
    let a : ℝ × Vec3 := (t, 0)
    let D := Icc (-t) (S - t) ×ˢ (univ : Set Vec3)
    have htrans : MapsTo (fun z => a + z) D slab := by
      intro z hz
      exact ⟨⟨by change 0 ≤ t + z.1; linarith [hz.1.1],
        by change t + z.1 ≤ S; linarith [hz.1.2]⟩, mem_univ _⟩
    have hD : a +ᵥ D = slab := by
      change (fun z => a + z) '' D = slab
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact htrans hy
      · intro hz
        refine ⟨(z.1 - t, z.2), ⟨⟨?_, ?_⟩, mem_univ _⟩, ?_⟩
        · linarith [hz.1.1]
        · linarith [hz.1.2]
        · ext <;> simp [a]
    have hf : ContDiffOn ℝ ∞ (fun z => Function.uncurry u (a + z)) D :=
      hu.comp (contDiff_const.add contDiff_id).contDiffOn htrans
    have hDiffD : UniqueDiffOn ℝ D :=
      (uniqueDiffOn_Icc (by linarith : -t < S - t)).prod uniqueDiffOn_univ
    have hpre : (⇑L ⁻¹' D) = univ := by
      apply eq_univ_iff_forall.mpr
      intro y
      exact ⟨⟨neg_nonpos.mpr ht.1.1, sub_nonneg.mpr ht.1.2⟩, mem_univ y⟩
    have hx : L x ∈ D := by rw [← mem_preimage, hpre]; exact mem_univ x
    have hDiffPre : UniqueDiffOn ℝ (⇑L ⁻¹' D) := hpre ▸ uniqueDiffOn_univ
    have hslice : (fun z => Function.uncurry u (a + z)) ∘ ⇑L = u t := by
      funext y
      change u (t + 0) (0 + y) = u t y
      simp
    have hd := L.iteratedFDerivWithin_comp_right hf hDiffD hDiffPre hx (i := m) (by simp)
    rw [hpre, iteratedFDerivWithin_univ, hslice, iteratedFDerivWithin_comp_add_left, hD] at hd
    change iteratedFDeriv ℝ m (u t) x =
      (iteratedFDerivWithin ℝ m (Function.uncurry u) slab (t, x)).compContinuousLinearMap
        (fun _ => L)
    simpa only [a, L, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add] using hd

/-- The increment estimates in Theorem 7.1 give a continuous velocity limit
on the common slab. On every open spatial region and time set where the
oscillations eventually vanish, the actual spatial derivatives converge
uniformly with the reciprocal-frequency tail and are jointly continuous. -/
theorem exists_inductive_velocity_limit_and_spatial_jets
    {T : ℝ} {slab freq : ℕ → ℝ} {q : ℕ → ℕ} {U O : ℕ → Velocity}
    (hT : 0 < T) (hslab : ∀ n, T ≤ slab n) (hinit : 2 ≤ freq 0)
    (hfreq : ∀ n, freq n ^ 2 ≤ freq (n + 1)) (hq : Tendsto q atTop atTop)
    (hUstage : ∀ n, ContDiffOn ℝ ∞ (Function.uncurry (U n))
      (Icc 0 (slab n) ×ˢ (univ : Set Vec3)))
    (hO : ∀ n t, t ∈ Icc 0 (slab (n + 1)) → ∀ x,
      ‖O (n + 1) t x‖ ≤ (freq (n + 1))⁻¹)
    (hB : ∀ n m, m ≤ q (n + 1) → ∀ t ∈ Icc 0 (slab (n + 1)), ∀ x,
      ‖iteratedFDeriv ℝ m (U (n + 1) t - U n t - O (n + 1) t) x‖ ≤ (freq (n + 1))⁻¹) :
    ∃ w : Velocity,
      ContinuousOn (Function.uncurry w) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      TendstoUniformlyOn (fun n => Function.uncurry (U n)) (Function.uncurry w)
        atTop (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      ∀ (I : Set ℝ) (s : Set Vec3), I ⊆ Icc 0 T → IsOpen s →
        (∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ I, EqOn (O (n + 1) t) 0 s) →
        (∀ t ∈ I, ContDiffOn ℝ ∞ (w t) s) ∧
        ∀ m : ℕ,
          TendstoUniformlyOn (fun n (z : ℝ × Vec3) => iteratedFDeriv ℝ m (U n z.1) z.2)
            (fun z : ℝ × Vec3 => iteratedFDeriv ℝ m (w z.1) z.2) atTop (I ×ˢ s) ∧
          ContinuousOn (fun z : ℝ × Vec3 => iteratedFDeriv ℝ m (w z.1) z.2) (I ×ˢ s) ∧
          ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ I, ∀ x ∈ s,
            ‖iteratedFDeriv ℝ m (U n t) x - iteratedFDeriv ℝ m (w t) x‖ ≤
              2 * (freq (n + 1))⁻¹ := by
  have hspatial (n : ℕ) := stage_spatial_jets_of_joint_smoothness
    (hT.trans_le (hslab n)) (hUstage n)
  have hU (n : ℕ) := (hspatial n).1
  have hUjet (n : ℕ) := (hspatial n).2
  let b (n : ℕ) := (freq (n + 1))⁻¹
  have hb : Summable b := by
    simpa only [b, Nat.add_comm] using (reciprocal_inductive_frequency_tail hinit hfreq 1).1
  have hbTail (n : ℕ) : (∑' k, b (n + k)) ≤ 2 * (freq (n + 1))⁻¹ := by
    have heq (k : ℕ) : n + k + 1 = n + 1 + k := by omega
    simp only [b, heq]
    exact (reciprocal_inductive_frequency_tail hinit hfreq (n + 1)).2
  have hStage (n : ℕ) : Icc 0 T ⊆ Icc 0 (slab n) := Icc_subset_Icc_right (hslab n)
  have hVelStep (n : ℕ) (_ : 0 ≤ n) (z : ℝ × Vec3)
      (hz : z ∈ Icc 0 T ×ˢ (univ : Set Vec3)) :
      dist (Function.uncurry (U n) z) (Function.uncurry (U (n + 1)) z) ≤ 2 * b n := by
    have ht := hStage (n + 1) hz.1
    have hB₀ := hB n 0 (Nat.zero_le _) z.1 ht z.2
    rw [norm_iteratedFDeriv_zero] at hB₀
    have hO₀ := hO n z.1 ht z.2
    rw [dist_comm, dist_eq_norm]
    change ‖U (n + 1) z.1 z.2 - U n z.1 z.2‖ ≤ 2 * b n
    calc
      _ = ‖U (n + 1) z.1 z.2 - U n z.1 z.2 - O (n + 1) z.1 z.2 +
          O (n + 1) z.1 z.2‖ := by rw [sub_add_cancel]
      _ ≤ ‖U (n + 1) z.1 z.2 - U n z.1 z.2 - O (n + 1) z.1 z.2‖ +
          ‖O (n + 1) z.1 z.2‖ := norm_add_le _ _
      _ ≤ b n + b n := add_le_add hB₀ hO₀
      _ = 2 * b n := (two_mul _).symm
  have hUcont (n : ℕ) : ContinuousOn (Function.uncurry (U n))
      (Icc 0 T ×ˢ (univ : Set Vec3)) := by
    have h := ((continuousMultilinearCurryFin0 ℝ Vec3 Vec3).continuous.comp_continuousOn
      (hUjet n 0)).mono (prod_mono_left (hStage n))
    refine h.congr fun z _ => ?_
    change U n z.1 z.2 =
      continuousMultilinearCurryFin0 ℝ Vec3 Vec3 (iteratedFDeriv ℝ 0 (U n z.1) z.2)
    rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
  obtain ⟨v, hvcont, hv, _⟩ := exists_continuousOn_uniformLimit_of_summable_increments
    0 (hb.mul_left 2) hVelStep hUcont
  let w (t : ℝ) (x : Vec3) := v (t, x)
  refine ⟨w, hvcont, hv, ?_⟩
  intro I s hI hs
  rintro ⟨N₀, hvanish⟩
  have hprod : I ×ˢ s ⊆ Icc 0 T ×ˢ (univ : Set Vec3) := prod_mono hI (subset_univ s)
  have happrox (n m : ℕ) : ContinuousOn
      (fun z : ℝ × Vec3 => iteratedFDeriv ℝ m (U n z.1) z.2) (I ×ˢ s) :=
    (hUjet n m).mono (prod_mono (hI.trans (hStage n)) (subset_univ s))
  have hjet (m : ℕ) : ∃ p : ℝ × Vec3 → ContinuousMultilinearMap ℝ (fun _ : Fin m => Vec3) Vec3,
      TendstoUniformlyOn (fun n (z : ℝ × Vec3) => iteratedFDeriv ℝ m (U n z.1) z.2) p
        atTop (I ×ˢ s) ∧
      ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ I ×ˢ s,
        ‖iteratedFDeriv ℝ m (U n z.1) z.2 - p z‖ ≤ 2 * (freq (n + 1))⁻¹ := by
    obtain ⟨Nq, hNq⟩ := eventually_atTop.1 (hq.eventually_ge_atTop m)
    let N := max N₀ Nq
    have hstep (n : ℕ) (hn : N ≤ n) (z : ℝ × Vec3) (hz : z ∈ I ×ˢ s) :
        dist (iteratedFDeriv ℝ m (U n z.1) z.2) (iteratedFDeriv ℝ m (U (n + 1) z.1) z.2) ≤
          b n := by
      have ht := hI hz.1
      have hEq : (U (n + 1) z.1 - U n z.1) =ᶠ[𝓝 z.2]
          (U (n + 1) z.1 - U n z.1 - O (n + 1) z.1) := by
        filter_upwards [hs.mem_nhds hz.2] with x hx
        simp only [Pi.sub_apply, hvanish n ((le_max_left _ _).trans hn) z.1 hz.1 hx,
          Pi.zero_apply, sub_zero]
      have hderiv := ((hEq.iteratedFDeriv ℝ m).eq_of_nhds)
      rw [dist_comm, dist_eq_norm, ← iteratedFDeriv_sub_apply
        (((hU (n + 1) z.1 (hStage (n + 1) ht)).of_le (by simp)).contDiffAt)
        (((hU n z.1 (hStage n ht)).of_le (by simp)).contDiffAt), hderiv]
      exact hB n m (hNq (n + 1) ((le_max_right _ _).trans (hn.trans (Nat.le_succ n))))
        z.1 (hStage (n + 1) ht) z.2
    obtain ⟨p, hp, htail⟩ := exists_uniformLimit_of_summable_increments N hb hstep
    exact ⟨p, hp, N, fun n hn z hz => by
      rw [← dist_eq_norm]
      exact (htail n hn z hz).trans (hbTail n)⟩
  choose p hp using hjet
  let P (t : ℝ) (x : Vec3) : FormalMultilinearSeries ℝ Vec3 Vec3 := fun m => p m (t, x)
  have hslice (m : ℕ) (t : ℝ) (ht : t ∈ I) :=
    contDiffOn_slice_of_uniform_spatial_derivatives (u := w) (p := P) hs m
      (fun n r hr => ((hU n r (hStage n (hI hr))).of_le (by simp)).contDiffOn)
      (hv.mono hprod) (fun k _ => (hp k).1) ht
  refine ⟨fun t ht => contDiffOn_infty.mpr (fun m => (hslice m t ht).1), ?_⟩
  intro m
  have hId (z : ℝ × Vec3) (hz : z ∈ I ×ˢ s) :
      p m z = iteratedFDeriv ℝ m (w z.1) z.2 :=
    ((hslice m z.1 hz.1).2 m le_rfl hz.2).symm
  have hm := (hp m).1.congr_right hId
  obtain ⟨N, hN⟩ := (hp m).2
  refine ⟨hm, hm.continuousOn (Frequently.of_forall (fun n => happrox n m)),
    N, fun n hn t ht x hx => ?_⟩
  simpa only [hId (t, x) ⟨ht, hx⟩] using hN n hn (t, x) ⟨ht, hx⟩

/-- The first spatial jet supplies the ordinary Fréchet derivative convergence
used in the prefix momentum limit. -/
theorem tendstoUniformlyOn_spatial_fderiv_of_first_jet
    {P : Set (ℝ × Vec3)} {U : ℕ → Velocity} {w : Velocity}
    (h : TendstoUniformlyOn (fun n (z : ℝ × Vec3) => iteratedFDeriv ℝ 1 (U n z.1) z.2)
      (fun z : ℝ × Vec3 => iteratedFDeriv ℝ 1 (w z.1) z.2) atTop P) :
    TendstoUniformlyOn (fun n (z : ℝ × Vec3) => fderiv ℝ (U n z.1) z.2)
      (fun z : ℝ × Vec3 => fderiv ℝ (w z.1) z.2) atTop P := by
  let C := continuousMultilinearCurryFin1 ℝ Vec3 Vec3
  have hC (f : Vec3 → Vec3) (x : Vec3) : C (iteratedFDeriv ℝ 1 f x) = fderiv ℝ f x := by
    ext y : 1
    change iteratedFDeriv ℝ 1 f x (fun _ => y) = fderiv ℝ f x y
    rw [iteratedFDeriv_one_apply]
  simpa only [Function.comp_def, hC] using C.isometry.uniformContinuous.comp_tendstoUniformlyOn h

/-- Consecutive spatial-jet bounds also control the half-Hölder quotient
on a full slice. The same bound works uniformly over a time prefix. -/
theorem halfHolder_difference_of_consecutive_spatial_jet_bounds {f g : Vec3 → Vec3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {m : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (h0 : ∀ x, ‖iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m g x‖ ≤ R)
    (h1 : ∀ x, ‖iteratedFDeriv ℝ (m + 1) f x - iteratedFDeriv ℝ (m + 1) g x‖ ≤ R)
    (x y : Vec3) :
    ‖(iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m g x) -
      (iteratedFDeriv ℝ m f y - iteratedFDeriv ℝ m g y)‖ ≤ 2 * R * Real.sqrt (dist x y) := by
  let D := iteratedFDeriv ℝ m (f - g)
  have hD (z : Vec3) : D z = iteratedFDeriv ℝ m f z - iteratedFDeriv ℝ m g z :=
    iteratedFDeriv_sub_apply ((hf.of_le (by simp)).contDiffAt) ((hg.of_le (by simp)).contDiffAt)
  have hdif : Differentiable ℝ D :=
    (hf.sub hg).differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top m)
  have hlip : ‖D x - D y‖ ≤ R * dist x y := by
    rw [dist_eq_norm]
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdif z) (fun z _ => by
      rw [show D = iteratedFDeriv ℝ m (f - g) from rfl, norm_fderiv_iteratedFDeriv,
        iteratedFDeriv_sub_apply ((hf.of_le (by simp)).contDiffAt) ((hg.of_le (by simp)).contDiffAt)]
      exact h1 z) (convex_univ : Convex ℝ (univ : Set Vec3)) (mem_univ y) (mem_univ x)
  have hsup : ‖D x - D y‖ ≤ 2 * R := by
    calc
      _ ≤ ‖D x‖ + ‖D y‖ := norm_sub_le _ _
      _ ≤ R + R := by rw [hD, hD]; exact add_le_add (h0 x) (h0 y)
      _ = _ := (two_mul _).symm
  rw [← hD x, ← hD y]
  by_cases hd : dist x y ≤ 1
  · have hs₁ : Real.sqrt (dist x y) ≤ 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hd
    have hd_sqrt : dist x y ≤ Real.sqrt (dist x y) := by
      nlinarith [Real.sq_sqrt (dist_nonneg : 0 ≤ dist x y),
        mul_nonneg (Real.sqrt_nonneg (dist x y)) (sub_nonneg.mpr hs₁)]
    exact hlip.trans <| (mul_le_mul_of_nonneg_left hd_sqrt hR).trans <|
      mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  · have hs₁ : 1 ≤ Real.sqrt (dist x y) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (le_of_lt (lt_of_not_ge hd))
    exact hsup.trans (le_mul_of_one_le_right (by positivity) hs₁)

/-- Shrinking periodic ball supports exclude a whole neighborhood of
each compact subset of the punctured lift. -/
theorem inductive_oscillations_eventually_zero_near_offOrigin_compact
    {K : Set Vec3} (hK : IsCompact K) (hKo : K ⊆ offOrigin)
    {T : ℝ} {radius : ℕ → ℝ} {O : ℕ → Velocity}
    (hradius : Tendsto radius atTop (𝓝 0))
    (hsupport : ∀ n t, t ∈ Icc 0 T → ∀ x, O (n + 1) t x ≠ 0 →
      ∃ z : Fin 3 → ℤ, dist (latticeVector z) x ≤ radius n) :
    ∃ s : Set Vec3, IsOpen s ∧ K ⊆ s ∧ s ⊆ offOrigin ∧
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc 0 T, EqOn (O (n + 1) t) 0 s := by
  obtain ⟨r, hr, _, _, _, hL, hsep⟩ := exists_offOrigin_compact_neighborhood hK hKo
  have hr₂ : 0 < r / 2 := by positivity
  have hsmall : ∀ᶠ n in atTop, radius n < r / 2 := hradius.eventually (Iio_mem_nhds hr₂)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  refine ⟨thickening (r / 2) K, isOpen_thickening, self_subset_thickening hr₂ K,
    (thickening_subset_cthickening_of_le (by linarith) K).trans hL, N, ?_⟩
  intro n hn t ht x hx
  change O (n + 1) t x = 0
  by_contra hne
  obtain ⟨z, hz⟩ := hsupport n t ht x hne
  obtain ⟨y, hy, hdist⟩ := mem_thickening_iff.mp hx
  have htriangle := dist_triangle (latticeVector z) x y
  linarith [hsep y hy z, hN n hn]

/-- The spatial part of Proposition 8.4 follows by combining the jets of
the common-slab velocity limit with the shrinking supports. -/
theorem hasOffOriginLimits_of_inductive_velocity_jets
    {T : ℝ} (hT : 0 ≤ T) {radius : ℕ → ℝ} {O : ℕ → Velocity} {w : Velocity}
    (hradius : Tendsto radius atTop (𝓝 0))
    (hsupport : ∀ n t, t ∈ Icc 0 T → ∀ x, O (n + 1) t x ≠ 0 →
      ∃ z : Fin 3 → ℤ, dist (latticeVector z) x ≤ radius n)
    (hjets : ∀ (s : Set Vec3), IsOpen s →
      (∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc 0 T, EqOn (O (n + 1) t) 0 s) →
      ContDiffOn ℝ ∞ (w T) s ∧
        ∀ m : ℕ, ContinuousOn
          (fun z : ℝ × Vec3 => iteratedFDeriv ℝ m (w z.1) z.2) (Icc 0 T ×ˢ s)) :
    HasOffOriginLimits T w := by
  intro K hK hKo m
  obtain ⟨s, hs, hKs, hso, hcut⟩ :=
    inductive_oscillations_eventually_zero_near_offOrigin_compact hK hKo hradius hsupport
  obtain ⟨hsmooth, hcont⟩ := hjets s hs hcut
  refine ⟨s, w T, hs, hKs, hso, hsmooth.of_le (by simp), fun j _ => ?_⟩
  exact tendstoUniformlyOn_terminal_of_continuousOn hT hK
    (w := fun t x => iteratedFDeriv ℝ j (w t) x)
    ((hcont j).mono (prod_mono_right hKs))

end TorusEuler
