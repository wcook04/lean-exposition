import Breakdown.FracCell.FiniteDefs

open Matrix

noncomputable section

namespace Breakdown.CellCert.Finite

namespace TreeFinalInternal

theorem quad_add {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadValue (A + B) x = quadValue A x + quadValue B x := by
  simp [quadValue, Matrix.add_mulVec, dotProduct_add]

theorem quad_zero {ι : Type*} [Fintype ι] (x : ι → ℝ) : quadValue (0 : Matrix ι ι ℝ) x = 0 := by
  simp [quadValue]

theorem quad_at_zero {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) : quadValue M 0 = 0 := by
  simp [quadValue]

theorem quad_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (M : κ → Matrix ι ι ℝ) (x : ι → ℝ) :
    quadValue (∑ k ∈ s, M k) x = ∑ k ∈ s, quadValue (M k) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [quad_zero]
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, quad_add, ih]

theorem front_root_le {a b : ℕ} (T : TreeCertificate a b) (hT : IsTreeCertificate T)
    (x : Fin a ⊕ Fin b → ℝ) :
    quadValue (T.front T.root) x ≤ (haveI := T.cellFintype; ∑ c, quadValue (T.cellForm c) x) := by
  classical
  let _ := T.cellFintype
  let _ := T.nodeFintype
  set f : T.Node → ℝ := fun μ => quadValue (T.front μ) x with hf
  set g : T.Cell → ℝ := fun c => quadValue (T.cellForm c) x with hg
  have hsum : ∑ ν, f ν ≤ ∑ ν, quadValue (T.nodeInput ν) x :=
    Finset.sum_le_sum (fun ν _ => hT.node_bound ν x)
  have hin : ∀ ν, quadValue (T.nodeInput ν) x =
      (∑ c, if T.cellNode c = ν then g c else 0) + ∑ μ, if T.parent μ = some ν then f μ else 0 := by
    intro ν
    unfold TreeCertificate.nodeInput
    rw [quad_add, quad_sum, quad_sum, Finset.sum_filter, Finset.sum_filter]
  have hcells : ∑ ν, (∑ c, if T.cellNode c = ν then g c else 0) = ∑ c, g c := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_ite_eq]
    simp
  have hkids : ∑ ν, (∑ μ, if T.parent μ = some ν then f μ else 0) = ∑ μ, f μ - f T.root := by
    rw [Finset.sum_comm]
    have h1 : ∀ μ ∈ (Finset.univ : Finset T.Node),
        (∑ ν, if T.parent μ = some ν then f μ else 0) = f μ - if μ = T.root then f μ else 0 := by
      intro μ _
      by_cases hne : μ = T.root
      · subst hne
        simp [hT.root_parent]
      · obtain ⟨ν0, hν0⟩ : ∃ ν0, T.parent μ = some ν0 := by
          cases h : T.parent μ with
          | none => exact absurd (hT.only_root μ h) hne
          | some ν0 => exact ⟨ν0, rfl⟩
        rw [hν0]
        simp [hne]
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp
  have htot : ∑ ν, quadValue (T.nodeInput ν) x = ∑ c, g c + (∑ μ, f μ - f T.root) := by
    rw [Finset.sum_congr rfl (fun ν _ => hin ν), Finset.sum_add_distrib, hcells, hkids]
  rw [htot] at hsum
  show f T.root ≤ ∑ c, g c
  linarith

end TreeFinalInternal

open TreeFinalInternal in
theorem tree_final (V : Type) [AddCommGroup V] [Module ℝ V] {a b : ℕ} (Q : V → ℝ) (z₀ : V →ₗ[ℝ] Fin a → ℝ)
    (L : Matrix (Fin a) (Fin b) ℝ) (T : TreeCertificate a b) : IsTreeCertificate T →
    Q 0 ≤ 0 →
    IsStateBound Q z₀ L ((haveI := T.cellFintype; ∑ c, T.cellForm c) + T.globalForm) →
    ∀ x, 0 ≤ Q x := by
  intro hT hQ0 hS x
  classical
  let _ := T.cellFintype
  have hΦΨ : ∀ y, quadValue (T.front T.root + T.globalForm) y
      ≤ quadValue ((∑ c, T.cellForm c) + T.globalForm) y := by
    intro y
    rw [quad_add, quad_add, quad_sum]
    have := front_root_le T hT y
    linarith
  obtain ⟨P, -, hcard, hpos⟩ := hT.root_positive
  let N := {i : Fin a // ¬ T.IsEliminatedSomewhere i}
  let r : (Fin a ⊕ Fin b → ℝ) →ₗ[ℝ] (N ⊕ Fin b → ℝ) :=
    LinearMap.funLeft ℝ ℝ (Sum.map Subtype.val id)
  let s : (Fin b → ℝ) →ₗ[ℝ] (Fin a ⊕ Fin b → ℝ) :=
    { toFun := fun u => Sum.elim (L *ᵥ u) u
      map_add' := by
        intro u v
        funext k
        cases k <;> simp [Matrix.mulVec_add]
      map_smul' := by
        intro c u
        funext k
        cases k <;> simp [Matrix.mulVec_smul] }
  let G : (P × (Fin b → ℝ)) →ₗ[ℝ] (N ⊕ Fin b → ℝ) :=
    r ∘ₗ P.subtype ∘ₗ LinearMap.fst ℝ P (Fin b → ℝ) - r ∘ₗ s ∘ₗ LinearMap.snd ℝ P (Fin b → ℝ)
  have hagree : ∀ y w : Fin a ⊕ Fin b → ℝ, r y = r w →
      quadValue (T.front T.root + T.globalForm) y = quadValue (T.front T.root + T.globalForm) w := by
    intro y w h
    apply hT.root_independent
    · intro i hi
      have := congrFun h (Sum.inl ⟨i, hi⟩)
      simpa [r, LinearMap.funLeft_apply] using this
    · intro j
      have := congrFun h (Sum.inr j)
      simpa [r, LinearMap.funLeft_apply] using this
  have hUle : ∀ u, quadValue (T.front T.root + T.globalForm) (s u) ≤ 0 := by
    intro u
    have h1 := hS 0 u
    simp only [map_zero, zero_add] at h1
    exact (hΦΨ _).trans (h1.trans hQ0)
  have hinj : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨p, hp⟩, u⟩ hG
    have hG' : r p - r (s u) = 0 := hG
    have hr : r p = r (s u) := sub_eq_zero.mp hG'
    have hp0 : p = 0 := by
      by_contra hne
      have h1 := hpos p hp hne
      have h2 := hagree _ _ hr
      have h3 := hUle u
      linarith
    subst hp0
    have hu : u = 0 := by
      funext j
      have := congrFun hr (Sum.inr j)
      simpa [r, s, LinearMap.funLeft_apply] using this.symm
    subst hu
    rfl
  have hsurj : Function.Surjective G := by
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    have hge : Module.finrank ℝ (N ⊕ Fin b → ℝ) ≤ Module.finrank ℝ (P × (Fin b → ℝ)) := by
      rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card,
        Fintype.card_sum, Fintype.card_fin]
      rw [Nat.card_eq_fintype_card] at hcard
      have hN : Fintype.card N = Fintype.card {i : Fin a // ¬ T.IsEliminatedSomewhere i} :=
        Fintype.card_congr (Equiv.refl _)
      omega
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm hle hge)).mp hinj
  obtain ⟨⟨⟨p, hp⟩, u⟩, hG⟩ := hsurj (r (Sum.elim (z₀ x) 0))
  have hG' : r p - r (s u) = r (Sum.elim (z₀ x) 0) := hG
  have e : (Sum.elim (z₀ x + L *ᵥ u) u : Fin a ⊕ Fin b → ℝ) = Sum.elim (z₀ x) 0 + s u := by
    funext k
    cases k <;> simp [s]
  have hr : r p = r (Sum.elim (z₀ x + L *ᵥ u) u) := by
    rw [e, map_add, ← hG']
    abel
  have hnn : 0 ≤ quadValue (T.front T.root + T.globalForm) p := by
    by_cases h0 : p = 0
    · rw [h0, quad_at_zero]
    · exact (hpos p hp h0).le
  rw [hagree _ _ hr] at hnn
  exact hnn.trans ((hΦΨ _).trans (hS x u))

end Breakdown.CellCert.Finite
