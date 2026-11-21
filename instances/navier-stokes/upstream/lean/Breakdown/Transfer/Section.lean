import Breakdown.Transfer.StatementsAbstract

noncomputable section

namespace Breakdown

namespace SectionInternal

theorem exists_preimage_of_dense {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Pu : X →L[ℝ] X) (C' : Submodule ℝ X)
    (hfin : FiniteDimensional ℝ (LinearMap.range (Pu : X →ₗ[ℝ] X))) (hd : Dense (C' : Set X))
    (v : X) (hv : v ∈ LinearMap.range (Pu : X →ₗ[ℝ] X)) : ∃ c ∈ C', Pu c = v := by
  have hle : Submodule.map (Pu : X →ₗ[ℝ] X) C' ≤ LinearMap.range (Pu : X →ₗ[ℝ] X) :=
    LinearMap.map_le_range
  have : FiniteDimensional ℝ (Submodule.map (Pu : X →ₗ[ℝ] X) C') :=
    Submodule.finiteDimensional_of_le hle
  have hcl : IsClosed ((Submodule.map (Pu : X →ₗ[ℝ] X) C' : Submodule ℝ X) : Set X) :=
    Submodule.closed_of_finiteDimensional _
  obtain ⟨x, rfl⟩ := hv
  have himg : (Pu : X → X) '' (C' : Set X) ⊆
      ((Submodule.map (Pu : X →ₗ[ℝ] X) C' : Submodule ℝ X) : Set X) := by
    rintro _ ⟨c, hc, rfl⟩
    exact Submodule.mem_map_of_mem hc
  have hx : Pu x ∈ ((Submodule.map (Pu : X →ₗ[ℝ] X) C' : Submodule ℝ X) : Set X) :=
    hcl.closure_subset_iff.mpr himg (Pu.continuous.range_subset_closure_image_dense hd ⟨x, rfl⟩)
  obtain ⟨c, hc, hcx⟩ := Submodule.mem_map.mp hx
  exact ⟨c, hc, hcx⟩

end SectionInternal

theorem exists_section : SectionStatement := by
  intro X _ _ _ Pu C' _ hfin hd
  set V := LinearMap.range (Pu : X →ₗ[ℝ] X)
  have : FiniteDimensional ℝ V := hfin
  let b := Module.finBasis ℝ V
  have hpre : ∀ i, ∃ c ∈ C', Pu c = (b i : X) := fun i =>
    SectionInternal.exists_preimage_of_dense Pu C' hfin hd (b i) (b i).2
  choose c hcC hcP using hpre
  let J₀ : V →ₗ[ℝ] X := b.constr ℝ c
  have hJ₀ : ∀ v : V, Pu (J₀ v) = v := by
    have h : (Pu : X →ₗ[ℝ] X).comp J₀ = V.subtype := by
      refine b.ext fun i => ?_
      simp [J₀, hcP]
    intro v
    exact LinearMap.congr_fun h v
  have hJ₀C : ∀ v : V, J₀ v ∈ C' := by
    intro v
    have hr : LinearMap.range J₀ ≤ C' := by
      rw [Module.Basis.constr_range]
      exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hcC i)
    exact hr (LinearMap.mem_range_self J₀ v)
  let R : X →L[ℝ] V := Pu.codRestrict V (fun x => LinearMap.mem_range_self (Pu : X →ₗ[ℝ] X) x)
  refine ⟨(LinearMap.toContinuousLinearMap J₀).comp R, ?_, ?_⟩
  · ext x
    change Pu ((LinearMap.toContinuousLinearMap J₀) (R x)) = Pu x
    rw [LinearMap.coe_toContinuousLinearMap', hJ₀]
    rfl
  · intro x
    exact hJ₀C _

end Breakdown
