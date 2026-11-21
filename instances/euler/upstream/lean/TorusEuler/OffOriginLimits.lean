import TorusEuler.LimitDerivatives
import TorusEuler.PeriodicLift
import Mathlib.Topology.MetricSpace.Thickening

open Filter Metric Set
open scoped ContDiff Topology

namespace TorusEuler

/-- A compact subset of the punctured lift has a compact neighborhood
uniformly separated from the singular lattice. -/
theorem exists_offOrigin_compact_neighborhood {K : Set Vec3}
    (hK : IsCompact K) (hKo : K ⊆ offOrigin) :
    ∃ r > (0 : ℝ), IsCompact (cthickening r K) ∧
      K ⊆ thickening r K ∧ thickening r K ⊆ cthickening r K ∧
      cthickening r K ⊆ offOrigin ∧
      ∀ x ∈ K, ∀ n : Fin 3 → ℤ, r < dist (latticeVector n) x := by
  obtain ⟨r, hr, hro⟩ := hK.exists_cthickening_subset_open isOpen_offOrigin hKo
  refine ⟨r, hr, hK.cthickening, self_subset_thickening hr K, thickening_subset_cthickening r K,
    hro, fun x hx n => lt_of_not_ge ?_⟩
  intro hn
  exact (hro (mem_cthickening_of_dist_le _ _ r K hx hn)) (mem_range_self n)

/-- A continuous spatial field on a closed slab over a compact set
converges uniformly to its terminal trace. -/
theorem tendstoUniformlyOn_terminal_of_continuousOn
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {T : ℝ} (hT : 0 ≤ T) {K : Set X} (hK : IsCompact K) {w : ℝ → X → Y}
    (hw : ContinuousOn (Function.uncurry w) (Icc 0 T ×ˢ K)) :
    TendstoUniformlyOn w (w T) (𝓝[Ico 0 T] T) K := by
  have hu := (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hw
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.1 hu ε hε
  have htime : ∀ᶠ t in 𝓝[Ico 0 T] T, t ∈ ball T δ :=
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds T hδ)
  filter_upwards [self_mem_nhdsWithin, htime] with t ht hdist x hx
  exact hclose (x := (T, x)) (y := (t, x)) ⟨⟨hT, le_rfl⟩, hx⟩
    ⟨⟨ht.1, ht.2.le⟩, hx⟩ (by simpa only [dist_prod_same_right, dist_comm T t, mem_ball] using hdist)

/-- Local uniform comparison of actual spatial jets yields the compact
terminal limits in Proposition 8.4. The approximants live on the closed
slab. The preterminal field agrees locally with their velocity limit. -/
theorem hasOffOriginLimits_of_uniform_spatial_jets
    {T : ℝ} (hT : 0 ≤ T) {f w : Velocity} {F : ℕ → Velocity}
    (hmatch : ∀ t ∈ Ico 0 T, EqOn (w t) (f t) offOrigin)
    (hF : ∀ j t, t ∈ Icc 0 T → ContDiff ℝ ∞ (F j t))
    (hvel : ∀ L : Set Vec3, IsCompact L → L ⊆ offOrigin →
      TendstoUniformlyOn (fun j => Function.uncurry (F j)) (Function.uncurry w)
        atTop (Icc 0 T ×ˢ L))
    (hjets : ∀ (L : Set Vec3), IsCompact L → L ⊆ offOrigin → ∀ m : ℕ,
      ∃ p : ℝ → Vec3 → FormalMultilinearSeries ℝ Vec3 Vec3, ∀ k ≤ m,
        TendstoUniformlyOn (fun j (tx : ℝ × Vec3) => iteratedFDeriv ℝ k (F j tx.1) tx.2)
          (fun tx : ℝ × Vec3 => p tx.1 tx.2 k) atTop (Icc 0 T ×ˢ L) ∧
        ∀ j, ContinuousOn (fun tx : ℝ × Vec3 => iteratedFDeriv ℝ k (F j tx.1) tx.2)
          (Icc 0 T ×ˢ L)) :
    HasOffOriginLimits T f := by
  intro K hK hKo m
  obtain ⟨r, _, hL, hKU, hUL, hLo, _⟩ := exists_offOrigin_compact_neighborhood hK hKo
  let U := thickening r K
  let L := cthickening r K
  have hU : IsOpen U := isOpen_thickening
  have hUo : U ⊆ offOrigin := hUL.trans hLo
  have hprod : Icc 0 T ×ˢ U ⊆ Icc 0 T ×ˢ L := prod_mono_right hUL
  obtain ⟨p, hp⟩ := hjets L hL hLo m
  have hslice (t : ℝ) (ht : t ∈ Icc 0 T) :=
    contDiffOn_slice_of_uniform_spatial_derivatives hU m
      (fun j t ht => ((hF j t ht).of_le (by simp)).contDiffOn)
      ((hvel L hL hLo).mono hprod) (fun k hk => (hp k hk).1.mono hprod) ht
  have hlast := hslice T ⟨hT, le_rfl⟩
  refine ⟨U, w T, hU, hKU, hUo, hlast.1, fun k hk => ?_⟩
  have hpc : ContinuousOn (fun tx : ℝ × Vec3 => p tx.1 tx.2 k) (Icc 0 T ×ˢ K) :=
    ((hp k hk).1.continuousOn (Frequently.of_forall (hp k hk).2)).mono
      (prod_mono_right (hKU.trans hUL))
  have hlim := tendstoUniformlyOn_terminal_of_continuousOn hT hK (w := fun t x => p t x k) hpc
  apply (hlim.congr_right (fun x hx => (hlast.2 k hk (hKU hx)).symm)).congr
  filter_upwards [self_mem_nhdsWithin] with t ht
  intro x hx
  have hxU := hKU hx
  have huz := (hslice t ⟨ht.1, ht.2.le⟩).2 k hk hxU
  rw [← huz, ← iteratedFDerivWithin_of_isOpen k hU hxU,
    ← iteratedFDerivWithin_of_isOpen k hU hxU]
  exact iteratedFDerivWithin_congr ((hmatch t ht).mono hUo) hxU k

/-- A preterminal time derivative can be identified by within-interval
dynamics. Its spatial limits follow from those of the identified field. -/
theorem hasOffOriginLimits_timeDerivative_of_dynamics
    {T : ℝ} {u g : Velocity}
    (hdynamics : ∀ t ∈ Ico 0 T, ∀ x ∈ offOrigin,
      HasDerivWithinAt (fun s => u s x) (g t x) (Ico 0 T) t)
    (hg : HasOffOriginLimits T g) :
    HasOffOriginLimits T (timeDerivative T u) := by
  intro K hK hKo m
  obtain ⟨U, v, hU, hKU, hUo, hv, hlim⟩ := hg K hK hKo m
  refine ⟨U, v, hU, hKU, hUo, hv, fun k hk => (hlim k hk).congr ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  intro x hx
  have hxU := hKU hx
  have heq : EqOn (g t) (timeDerivative T u t) U := fun y hy =>
    ((hdynamics t ht y (hUo hy)).derivWithin (uniqueDiffOn_Ico _ _ t ht)).symm
  rw [← iteratedFDerivWithin_of_isOpen k hU hxU,
    ← iteratedFDerivWithin_of_isOpen k hU hxU]
  exact iteratedFDerivWithin_congr heq hxU k

/-- The dynamics may be available on each closed slab strictly before the
terminal time, as in the integrated limit passage of Proposition 8.1. -/
theorem hasOffOriginLimits_timeDerivative_of_prefix_dynamics
    {T : ℝ} {u g : Velocity}
    (hdynamics : ∀ S < T, ∀ t ∈ Icc 0 S, ∀ x ∈ offOrigin,
      HasDerivWithinAt (fun s => u s x) (g t x) (Icc 0 S) t)
    (hg : HasOffOriginLimits T g) :
    HasOffOriginLimits T (timeDerivative T u) := by
  apply hasOffOriginLimits_timeDerivative_of_dynamics _ hg
  intro t ht x hx
  obtain ⟨S, htS, hST⟩ := exists_between ht.2
  have hneighborhood : Icc 0 S ∈ 𝓝[Ico 0 T] t := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htS)]
      with r hr hrS
    exact ⟨hr.1, (show r < S from hrS).le⟩
  exact (hdynamics S hST t ⟨ht.1, htS.le⟩ x hx).mono_of_mem_nhdsWithin hneighborhood

end TorusEuler
