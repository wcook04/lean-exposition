import Breakdown.FracCell.SpectralBlocksParts

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

def ModeField (g : CellBlock) (F : Space → Space) : Prop :=
  ∃ f : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ, (∀ s c t, Measurable (Function.uncurry (f s c t))) ∧
    ∀ y, F y = ∑ s : Fin 2, Set.indicator (cellSolid g s)
      (fun w => ∑ c : Fin 3, (∑ t : Fin 2, trigMode t (g.mode * angleCoord w)
        * f s c t (radialCoord w) (w 2)) • frameVector c w) y

def ModeGradient (g : CellBlock) (D : Space → (Space →L[ℝ] Space)) : Prop :=
  ∃ f : Fin 2 → Fin 3 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ, (∀ s c d t, Measurable (Function.uncurry (f s c d t))) ∧
    ∀ y, D y = ∑ s : Fin 2, Set.indicator (cellSolid g s)
      (fun w => ∑ c : Fin 3, ∑ d : Fin 3, (∑ t : Fin 2, trigMode t (g.mode * angleCoord w)
        * f s c d t (radialCoord w) (w 2)) • (innerSL ℝ (frameVector d w)).smulRight (frameVector c w)) y

def ModeOrthStatement : Prop :=
  ∀ g g' : CellBlock,
    (volume (⋃ s, cellSolid g s ∩ ⋃ s, cellSolid g' s) = 0 ∨
      (g.innerRadius = g'.innerRadius ∧ g.outerRadius = g'.outerRadius ∧ g.lowerHeight = g'.lowerHeight ∧
        g.upperHeight = g'.upperHeight ∧ g.mode ≠ g'.mode)) →
    (∀ F G : Space → Space, ModeField g F → ModeField g' G → MemLp F 2 volume → MemLp G 2 volume →
      ∫ y, inner ℝ (F y) (G y) = 0) ∧
    (∀ D D' : Space → (Space →L[ℝ] Space), ModeGradient g D → ModeGradient g' D' →
      AEStronglyMeasurable D volume → AEStronglyMeasurable D' volume →
      Integrable (fun y => entrySq (D y)) volume → Integrable (fun y => entrySq (D' y)) volume →
      ∫ y, entryInner (D y) (D' y) = 0)

def BlockWitnessStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (sd : SpectralData), IsSpectralData c sd →
    ∀ lam : ℝ, 0 < lam → ∀ x : Fin N → ℝ, ∀ a : Fin N,
      ∃ (ψ : Space → Space) (Dψ : Space → (Space →L[ℝ] Space)),
        MemLp ψ 2 volume ∧ AEStronglyMeasurable Dψ volume ∧ Integrable (fun y => entrySq (Dψ y)) ∧
        IsWeakGradientOf ψ Dψ ∧ ModeGradient (sd.block (c.blockIndex a)) Dψ ∧
        ModeField (sd.block (c.blockIndex a))
          (fun y => ∑ b, (if c.blockIndex b = c.blockIndex a then x b else 0) • c.row b y - ψ y) ∧
        MemLp (fun y => ∑ b, (if c.blockIndex b = c.blockIndex a then x b else 0) • c.row b y - ψ y) 2 volume ∧
        (∫ y, ‖∑ b, (if c.blockIndex b = c.blockIndex a then x b else 0) • c.row b y - ψ y‖ ^ 2)
            + (1 / lam) * ∫ y, entrySq (Dψ y)
          ≤ sd.blockSpectral (c.blockIndex a) lam * ∑ b, (if c.blockIndex b = c.blockIndex a then x b ^ 2 else 0)

theorem blockFamily_of_parts (hO : ModeOrthStatement) (hW : BlockWitnessStatement) : BlockFamilyStatement := by
  intro k N c sd hsd lam hlam x
  classical
  choose Ψ DΨ hΨ using hW c sd hsd lam hlam x
  obtain ⟨φb, hφb⟩ : ∃ φb : ℕ → Space → Space,
      ∀ β y, φb β y = ∑ b, (if c.blockIndex b = β then x b else 0) • c.row b y := ⟨_, fun _ _ => rfl⟩
  have hzero : ∀ β, (¬ ∃ a, c.blockIndex a = β) → ∀ y, φb β y = 0 := by
    intro β hβ y
    rw [hφb]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg fun h => hβ ⟨b, h⟩, zero_smul]
  refine ⟨fun β => if h : ∃ a, c.blockIndex a = β then Ψ h.choose else fun _ => 0,
    fun β => if h : ∃ a, c.blockIndex a = β then DΨ h.choose else fun _ => 0, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp_rw [← hφb]
  · intro β
    by_cases h : ∃ a, c.blockIndex a = β
    · simp only [dif_pos h]
      obtain ⟨h1, h2, h3, h4, -⟩ := hΨ h.choose
      exact ⟨h1, h2, h3, h4⟩
    · simp only [dif_neg h]
      refine ⟨MemLp.zero, aestronglyMeasurable_const, ?_, ?_⟩
      · simp [entrySq]
      · intro φ _ j
        simp
  · intro β
    by_cases h : ∃ a, c.blockIndex a = β
    · simp only [dif_pos h]
      have e := (hΨ h.choose).2.2.2.2.2.2.1
      rw [h.choose_spec] at e
      simp_rw [← hφb] at e
      exact e
    · simp only [dif_neg h, hzero β h, sub_zero]
      exact MemLp.zero
  · intro β β' hne
    by_cases h : ∃ a, c.blockIndex a = β
    · by_cases h' : ∃ a, c.blockIndex a = β'
      · simp only [dif_pos h, dif_pos h']
        have hap := hsd.blocks_apart h.choose h'.choose (by rw [h.choose_spec, h'.choose_spec]; exact hne)
        have m1 := (hΨ h.choose).2.2.2.2.2.1
        have m2 := (hΨ h'.choose).2.2.2.2.2.1
        have l1 := (hΨ h.choose).2.2.2.2.2.2.1
        have l2 := (hΨ h'.choose).2.2.2.2.2.2.1
        have key := (hO _ _ hap).1 _ _ m1 m2 l1 l2
        rw [h.choose_spec, h'.choose_spec] at key
        simp_rw [← hφb] at key
        exact key
      · simp only [dif_neg h', hzero β' h', sub_zero, inner_zero_right, integral_zero]
    · simp only [dif_neg h, hzero β h, sub_zero, inner_zero_left, integral_zero]
  · intro β β' hne
    by_cases h : ∃ a, c.blockIndex a = β
    · by_cases h' : ∃ a, c.blockIndex a = β'
      · simp only [dif_pos h, dif_pos h']
        have hap := hsd.blocks_apart h.choose h'.choose (by rw [h.choose_spec, h'.choose_spec]; exact hne)
        obtain ⟨-, a1, i1, -, g1, -⟩ := hΨ h.choose
        obtain ⟨-, a2, i2, -, g2, -⟩ := hΨ h'.choose
        exact (hO _ _ hap).2 _ _ g1 g2 a1 a2 i1 i2
      · simp only [dif_neg h']
        simp [entryInner]
    · simp only [dif_neg h]
      simp [entryInner]
  · intro β
    by_cases h : ∃ a, c.blockIndex a = β
    · simp only [dif_pos h]
      have e := (hΨ h.choose).2.2.2.2.2.2.2
      rw [h.choose_spec] at e
      simp_rw [← hφb] at e
      exact e
    · simp only [dif_neg h, hzero β h, sub_zero]
      have hs : ∑ b, (if c.blockIndex b = β then x b ^ 2 else 0) = 0 :=
        Finset.sum_eq_zero fun b _ => if_neg fun hb => h ⟨b, hb⟩
      rw [hs]
      simp [entrySq]

end Spectral

end CellCert

end Breakdown
