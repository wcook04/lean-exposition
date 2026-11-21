import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
Flat activation of the jointly smooth profiles in §3.1, equation (3.7).
The jet-matching and cutoff arguments are adapted from the archived
`ChainPlanar/Kit/Bootstrap.lean` and `CCPoint/Lib/R03/ZeroExtendJoint.lean`.
-/

open Filter Set
open scoped ContDiff Topology

namespace TorusEuler

section Gluing

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem contDiffOn_union_of_matching_jets {f : V → F} {s t : Set V}
    (hs : IsClosed s) (ht : IsClosed t) (hUs : UniqueDiffOn ℝ s) (hUt : UniqueDiffOn ℝ t)
    (hfs : ContDiffOn ℝ ∞ f s) (hft : ContDiffOn ℝ ∞ f t)
    (hmatch : ∀ x ∈ s ∩ t, ∀ k : ℕ,
      iteratedFDerivWithin ℝ k f s x = iteratedFDerivWithin ℝ k f t x) :
    ContDiffOn ℝ ∞ f (s ∪ t) := by
  classical
  let p := s.piecewise (ftaylorSeriesWithin ℝ f s) (ftaylorSeriesWithin ℝ f t)
  have hps : ∀ k : ℕ, EqOn (fun x => p x k) (fun x => ftaylorSeriesWithin ℝ f s x k) s := by
    intro k x hx
    simp [p, hx]
  have hpt : ∀ k : ℕ, EqOn (fun x => p x k) (fun x => ftaylorSeriesWithin ℝ f t x k) t := by
    intro k x hx
    by_cases hxs : x ∈ s
    · simpa [p, hxs, ftaylorSeriesWithin] using
        hmatch x ⟨hxs, hx⟩ k
    · simp [p, hxs]
  have hleft := (hfs.ftaylorSeriesWithin hUs).congr_series (fun k _ => (hps k).symm)
  have hright := (hft.ftaylorSeriesWithin hUt).congr_series (fun k _ => (hpt k).symm)
  refine HasFTaylorSeriesUpToOn.contDiffOn (f' := p) ⟨?_, ?_, ?_⟩
  · intro x hx
    exact hx.elim (hleft.zero_eq x) (hright.zero_eq x)
  · intro k hk x hx
    rcases hx with hxs | hxt
    · by_cases hxt : x ∈ t
      · exact (hleft.fderivWithin k hk x hxs).union (hright.fderivWithin k hk x hxt)
      · refine (hleft.fderivWithin k hk x hxs).mono_of_mem_nhdsWithin ?_
        rw [mem_nhdsWithin]
        exact ⟨tᶜ, ht.isOpen_compl, hxt, fun _ hy => hy.2.resolve_right hy.1⟩
    · by_cases hxs : x ∈ s
      · exact (hleft.fderivWithin k hk x hxs).union (hright.fderivWithin k hk x hxt)
      · refine (hright.fderivWithin k hk x hxt).mono_of_mem_nhdsWithin ?_
        rw [mem_nhdsWithin]
        exact ⟨sᶜ, hs.isOpen_compl, hxs, fun _ hy => hy.2.resolve_left hy.1⟩
  · intro k hk
    exact (hleft.cont k hk).union_of_isClosed (hright.cont k hk) hs ht

private theorem flat_cutoff_jet_at_activation {χ : ℝ → ℝ} {a : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hflat : ∀ t ≤ a, χ t = 0) (x : V) (k : ℕ) :
    iteratedFDeriv ℝ k (fun z : ℝ × V => χ z.1) (a, x) = 0 := by
  let w : ℝ × V → ℝ := χ ∘ Prod.fst
  have hw : ContDiff ℝ ∞ w := hχ.comp contDiff_fst
  have hclosed : IsClosed {z | iteratedFDeriv ℝ k w z = 0} :=
    isClosed_eq (hw.continuous_iteratedFDeriv (by simp)) continuous_const
  have hsub : Iio a ×ˢ (univ : Set V) ⊆ {z | iteratedFDeriv ℝ k w z = 0} := by
    intro z hz
    have hzero : w =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_Iio.prod isOpen_univ).mem_nhds hz] with p hp
      exact hflat p.1 (le_of_lt hp.1)
    change iteratedFDeriv ℝ k w z = 0
    rw [(hzero.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply]
  apply closure_minimal hsub hclosed
  rw [closure_prod_eq, closure_Iio, closure_univ]
  exact ⟨mem_Iic.2 le_rfl, mem_univ x⟩

/-- A time cutoff that vanishes up to activation gives joint smoothness on the
full pre-terminal slab. The unweighted profile only needs to be smooth on the
closed active slab. -/
theorem contDiffOn_flatActivation_smul {a b : ℝ} {χ : ℝ → ℝ} {g : ℝ × V → F}
    (hab : a < b) (hχ : ContDiff ℝ ∞ χ) (hflat : ∀ t ≤ a, χ t = 0)
    (hg : ContDiffOn ℝ ∞ g (Icc a b ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × V => χ z.1 • g z) (Iic b ×ˢ univ) := by
  let w : ℝ × V → ℝ := χ ∘ Prod.fst
  let f : ℝ × V → F := fun z => w z • g z
  let s : Set (ℝ × V) := Iic a ×ˢ univ
  let t : Set (ℝ × V) := Icc a b ×ˢ univ
  have hst : s ∪ t = Iic b ×ˢ univ := by
    change (Iic a ×ˢ (univ : Set V)) ∪ (Icc a b ×ˢ univ) = Iic b ×ˢ univ
    rw [← union_prod, Iic_union_Icc_eq_Iic hab.le]
  have hUs : UniqueDiffOn ℝ s := (uniqueDiffOn_Iic a).prod uniqueDiffOn_univ
  have hUt : UniqueDiffOn ℝ t := (uniqueDiffOn_Icc hab).prod uniqueDiffOn_univ
  have hzero : EqOn f (fun _ => (0 : F)) s := by
    intro z hz
    exact (congrArg (fun c : ℝ => c • g z) (hflat z.1 hz.1)).trans (zero_smul ℝ _)
  have hw : ContDiff ℝ ∞ w := hχ.comp contDiff_fst
  have hfs : ContDiffOn ℝ ∞ f s := contDiffOn_const.congr hzero
  have hft : ContDiffOn ℝ ∞ f t := hw.contDiffOn.smul hg
  rw [← hst]
  refine contDiffOn_union_of_matching_jets (isClosed_Iic.prod isClosed_univ)
    (isClosed_Icc.prod isClosed_univ) hUs hUt hfs hft ?_
  rintro ⟨r, x⟩ hz k
  have hr : r = a := le_antisymm hz.1.1 hz.2.1.1
  subst r
  change iteratedFDerivWithin ℝ k f s (a, x) = iteratedFDerivWithin ℝ k f t (a, x)
  rw [iteratedFDerivWithin_congr hzero hz.1, iteratedFDerivWithin_fun_zero, Pi.zero_apply]
  symm
  apply norm_le_zero_iff.mp
  refine (norm_iteratedFDerivWithin_smul_le hw.contDiffOn hg hUt hz.2
    (n := k) (by simp)).trans (le_of_eq (Finset.sum_eq_zero fun i _ => ?_))
  have hi : iteratedFDeriv ℝ i w (a, x) = 0 := flat_cutoff_jet_at_activation hχ hflat x i
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hUt
    (hw.of_le (by simp : (i : ℕ∞ω) ≤ ∞)).contDiffAt hz.2,
    hi, norm_zero, mul_zero, zero_mul]

end Gluing

end TorusEuler
