import TorusEuler.Paper.Proofs.S5b.T56Facts

/-!
# Theorem 5.6, glue: the mean of the retained source (slaving identity)

The phase average of the retained source at level `p ≤ P` is the sum of the three slow
interactions of the mean source (TeX :593-597: the fast mean `⟨(C_i·κ)∂_sY_j⟩ = ⟨(𝐝·V_{i-1})Y_j⟩`
by integration by parts in `s` (the identity (5.42), which follows from the slaving identity (3.6)), products of one mean and one
oscillation average to zero). This is the library identity
`average_sourceBeforeMean_eq_slowProducts`, applied to the truncation of the profiles to the
levels `1..P` (the library lemma quantifies over all levels).
-/

open Set Filter
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.Paper.S5b

open AppendixD HierarchyTwistedProfile

noncomputable section

section Exact

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
  {D lam t₀ : ℝ} {center : ℝ → Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3

/-- The levels of `u` restricted to `1..P` (`C_i` for `i ≤ P`), zero elsewhere. -/
def truncate (P : ℕ) (u : HierarchyProfiles VP (HierarchyTwistedProfile T k ℝ)) :
    HierarchyProfiles VP (HierarchyTwistedProfile T k ℝ) where
  V i := if i ∈ Finset.Icc 1 P then u.V i else 0
  C i := if i ≤ P then u.C i else 0
  B i := if i ∈ Finset.Icc 1 P then u.B i else 0
  p := u.p
  q := u.q

/-- Index facts of the pairs at level `p`: `shift + 1 ≤ i`, `1 ≤ j`, `i + j = p + shift`
(copy of the private library lemma `hierarchyLevelPairs_spec`). -/
theorem levelPairs_spec {P shift p : ℕ} {ij : ℕ × ℕ} (hij : ij ∈ hierarchyLevelPairs P shift p) :
    shift + 1 ≤ ij.1 ∧ 1 ≤ ij.2 ∧ ij.1 + ij.2 = p + shift := by
  obtain ⟨hbox, hlevel⟩ := Finset.mem_filter.mp hij
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hbox
  rw [Finset.mem_Icc] at hi hj
  unfold hierarchyAdvectionLevel at hlevel
  exact ⟨hi.1, hj.1, by omega⟩

/-- The indices of a pair at level `p` with `shift ≤ 1` are at most `p`. -/
theorem levelPairs_le {P shift p : ℕ} (hs : shift ≤ 1) {ij : ℕ × ℕ}
    (hij : ij ∈ hierarchyLevelPairs P shift p) : ij.1 ≤ p ∧ ij.2 ≤ p := by
  obtain ⟨h1, h2, h3⟩ := levelPairs_spec hij
  omega

set_option maxHeartbeats 2000000 in
/-- **The mean of the retained source** (TeX :593-597, (5.42)): for `p ∈ [2,P]`,
`⟨H_p⟩ = ∑_{i+j=p} (⟨(Y_i·𝐝)Y_j⟩ + ⟨(𝐝·V_i)Y_j⟩ + (B_i·𝐝)B_j)`. -/
theorem average_sourceBeforeMean_eq (hP : S5.Parent T U X pU D lam) (d : ParentGeometry hT U X k)
    {P : ℕ} {u : HierarchyProfiles VP (HierarchyTwistedProfile T k ℝ)} (cS : VP)
    (hcS : (S5.ops d).average cS = 0) (hC0 : u.C 0 = 0)
    (hC : ∀ i ∈ Finset.Icc 1 P, u.C i = S5.curlCorrection d (u.V i))
    (hV : ∀ i ∈ Finset.Icc 1 P, (S5.ops d).average (u.V i) = 0)
    (hB : ∀ i ∈ Finset.Icc 1 P, (S5.ops d).average (u.B i) = u.B i)
    (htr : ∀ i ∈ Finset.Icc 1 P, ∀ t ∈ Icc 0 T, ∀ a s,
      ⟪S5.waveVector X k t a, (u.V i).val.val.val (t, a, s)⟫_ℝ = 0)
    (hpm : ∀ i ∈ Finset.Icc 1 P, ∀ t ∈ Icc 0 T, ∀ a,
      phaseMean (fun r => (u.p i).val.val.val (t, a, r)) = 0) :
    ∀ p ∈ Finset.Icc 2 P, (S5.ops d).average ((S5.ops d).sourceBeforeMean u P cS p) =
      ∑ ij ∈ hierarchyLevelPairs P 0 p,
        ((S5.ops d).average ((S5.ops d).labelAdv (u.Y ij.1) (u.Y ij.2)) +
          (S5.ops d).average (slowLabelDivergenceProduct hT d.inverse (u.V ij.1) (u.Y ij.2)) +
          (S5.ops d).labelAdv (u.B ij.1) (u.B ij.2)) := by
  intro p hp
  obtain ⟨hp2, hpP⟩ := Finset.mem_Icc.mp hp
  let u' := truncate P u
  have hVu' (i : ℕ) (hi : i ∈ Finset.Icc 1 P) : u'.V i = u.V i := by simp only [u', truncate, hi, ↓reduceIte]
  have hBu' (i : ℕ) (hi : i ∈ Finset.Icc 1 P) : u'.B i = u.B i := by simp only [u', truncate, hi, ↓reduceIte]
  have hCu' (i : ℕ) (hi : i ≤ P) : u'.C i = u.C i := by simp only [u', truncate, hi, ↓reduceIte]
  have hYu' (i : ℕ) (hi : i ∈ Finset.Icc 1 P) : u'.Y i = u.Y i := by
    have h1 := Finset.mem_Icc.mp hi
    unfold HierarchyProfiles.Y
    rw [hVu' i hi, hCu' (i - 1) (by omega)]
  -- the source only depends on the levels below `p`
  have hsrc : (S5.ops d).sourceBeforeMean u P cS p = (S5.ops d).sourceBeforeMean u' P cS p := by
    rw [← Bridge.levelSource_eq_sourceBeforeMean (S5.ops d) u cS hpP,
      ← Bridge.levelSource_eq_sourceBeforeMean (S5.ops d) u' cS hpP]
    refine Bridge.levelSource_congr (S5.ops d) cS hp2 (fun i h1 h2 => ?_) (fun i h1 h2 => ?_)
      (fun i h1 h2 => rfl) (fun i h1 h2 => ?_)
    · exact (hVu' i (Finset.mem_Icc.mpr ⟨h1, by omega⟩)).symm
    · exact (hBu' i (Finset.mem_Icc.mpr ⟨h1, by omega⟩)).symm
    · change u.C (i - 1) = u'.C (i - 1)
      rw [hCu' (i - 1) (by omega)]
  -- the library identity for `u'`
  have hX := hP.flow
  have hU := hP.velocity_smooth
  have hper := hP.velocity_periodic
  obtain ⟨hsurj, hgraph⟩ := d.inverseGraph_values hX hU hper
  have hA (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ 2 (X t 0) :=
    (slice_contDiff (g := fun z : ℝ × Vec3 => X z.1 0 z.2)
      (hX.contDiffOn_inverseLabelFlow hT hU hper) ht).of_le (by simp)
  have hVz (i : ℕ) : (S5.ops d).average (u'.V i) = 0 := by
    by_cases hi : i ∈ Finset.Icc 1 P
    · rw [hVu' i hi]; exact hV i hi
    · have h0 : u'.V i = 0 := by simp only [u', truncate, hi, ↓reduceIte]
      rw [h0, map_zero]
  have hBz (i : ℕ) : (S5.ops d).average (u'.B i) = u'.B i := by
    by_cases hi : i ∈ Finset.Icc 1 P
    · rw [hBu' i hi]; exact hB i hi
    · have h0 : u'.B i = 0 := by simp only [u', truncate, hi, ↓reduceIte]
      rw [h0, map_zero]
  have hCz (i : ℕ) : u'.C i = complete hT d.inverse d.covector d.oscillation.covector_independent
      d.oscillation.covector_ne_zero (u'.V i) ∨ u'.V i = 0 ∧ u'.C i = 0 := by
    by_cases hi : i ∈ Finset.Icc 1 P
    · left
      rw [hVu' i hi, hCu' i (Finset.mem_Icc.mp hi).2, hC i hi]
      rfl
    · right
      have hV0 : u'.V i = 0 := by simp only [u', truncate, hi, ↓reduceIte]
      refine ⟨hV0, ?_⟩
      by_cases hi0 : i = 0
      · subst hi0
        rw [hCu' 0 (Nat.zero_le _), hC0]
      · have hPi : ¬ i ≤ P := fun h => hi (Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hi0, h⟩)
        simp only [u', truncate, hPi, ↓reduceIte]
  have htrz (i : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
      ⟪d.covector.val.val.val (t, a, 0), (u'.V i).val.val.val (t, a, s)⟫_ℝ = 0 := by
    have hκ := d.covector_value (t, a, 0) ⟨ht, mem_univ _⟩
    rw [hκ]
    by_cases hi : i ∈ Finset.Icc 1 P
    · rw [hVu' i hi]; exact htr i hi t ht a s
    · have hV0 : u'.V i = 0 := by simp only [u', truncate, hi, ↓reduceIte]
      rw [hV0]
      change ⟪S5.waveVector X k t a, (0 : VP).val.val.val (t, a, s)⟫_ℝ = 0
      have : (0 : VP).val.val.val (t, a, s) = 0 := rfl
      rw [this, inner_zero_right]
  have hid := average_sourceBeforeMean_eq_slowProducts hT d.inverse d.strain d.covector
    d.mean.inverse_independent (PhysicalApproximationData.parentStrain_phaseIndependent (d := d))
    d.oscillation.covector_independent d.oscillation.covector_ne_zero hA hsurj
    (fun t ht x s => (hgraph t ht x s).1) (fun t ht x => (hgraph t ht x 0).2) (p := p) hpP u' cS
    hVz hBz hCz htrz (by
      have hp1 : p - 1 ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      exact hpm (p - 1) hp1) hcS
  rw [hsrc]
  refine hid.trans (Finset.sum_congr rfl fun ij hij => ?_)
  obtain ⟨h1, h2, h3⟩ := levelPairs_spec hij
  obtain ⟨h4, h5⟩ := levelPairs_le (by norm_num) hij
  have hi1 : ij.1 ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hi2 : ij.2 ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  rw [hYu' _ hi1, hYu' _ hi2, hVu' _ hi1, hBu' _ hi1, hBu' _ hi2]

end Exact

end

end TorusEuler.Paper.S5b
