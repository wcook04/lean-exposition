import Breakdown.Cert.FixedPointOdd

namespace Breakdown

theorem exists_fixedPoint_box {k : ℕ} (a b : Fin k → ℝ) (hab : a ≤ b)
    (f : (Fin k → ℝ) → (Fin k → ℝ))
    (hf : ContinuousOn f (Set.Icc a b)) (hmap : Set.MapsTo f (Set.Icc a b) (Set.Icc a b)) :
    ∃ x ∈ Set.Icc a b, f x = x := by
  classical
  by_contra hno
  push Not at hno
  have hK : IsCompact (Set.Icc a b) := isCompact_Icc
  have hKne : (Set.Icc a b).Nonempty := ⟨a, le_refl a, hab⟩
  have hg : ContinuousOn (fun x => f x - x) (Set.Icc a b) := hf.sub continuousOn_id
  obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hKne hg.norm
  have hε : 0 < ‖f x0 - x0‖ := norm_pos_iff.2 (sub_ne_zero.2 (hno x0 hx0))
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hg) _ hε
  obtain ⟨p, hp⟩ := exists_nat_gt ((∑ i, (b i - a i)) / δ)
  have hsum0 : 0 ≤ ∑ i, (b i - a i) := Finset.sum_nonneg fun i _ => sub_nonneg.2 (hab i)
  have hpR : (0 : ℝ) < p := lt_of_le_of_lt (div_nonneg hsum0 hδ.le) hp
  have hp0 : 0 < p := by exact_mod_cast hpR
  have hstep : ∀ i, (b i - a i) / p < δ := by
    intro i
    have h1 : b i - a i ≤ ∑ j, (b j - a j) :=
      Finset.single_le_sum (f := fun j => b j - a j) (fun j _ => sub_nonneg.2 (hab j))
        (Finset.mem_univ i)
    have h2 : (∑ j, (b j - a j)) < p * δ := by
      rw [div_lt_iff₀ hδ] at hp
      linarith
    rw [div_lt_iff₀ hpR]
    linarith
  set pt : (Fin k → ℕ) → (Fin k → ℝ) := fun x i => a i + (b i - a i) * ((x i : ℝ) / p) with hpt_def
  have hpt : ∀ x : Fin k → ℕ, (∀ j, x j ≤ p) → pt x ∈ Set.Icc a b := by
    intro x hx
    constructor
    · intro i
      have h1 : (0 : ℝ) ≤ (x i : ℝ) / p := div_nonneg (Nat.cast_nonneg _) hpR.le
      have h2 := mul_nonneg (sub_nonneg.2 (hab i)) h1
      simp only [hpt_def]
      linarith
    · intro i
      have h1 : (x i : ℝ) / p ≤ 1 := by
        rw [div_le_one hpR]
        exact_mod_cast hx i
      have h2 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 (hab i))
      simp only [hpt_def]
      linarith
  set lab : (Fin k → ℕ) → Fin k → Prop := fun x i => x i ≠ 0 ∧ f (pt x) i ≤ pt x i with hlab
  have h0 : ∀ x : Fin k → ℕ, (∀ j, x j ≤ p) → ∀ i, x i = 0 → ¬ lab x i := by
    intro x _ i hi h
    exact h.1 hi
  have h1 : ∀ x : Fin k → ℕ, (∀ j, x j ≤ p) → ∀ i, x i = p → lab x i := by
    intro x hx i hi
    refine ⟨by omega, ?_⟩
    have hb : pt x i = b i := by
      simp only [hpt_def, hi, div_self hpR.ne']
      ring
    rw [hb]
    exact (hmap (hpt x hx)).2 i
  obtain ⟨v, τ, hv⟩ := GridSimplex.exists_complete_simplex hp0 lab h0 h1
  have hgrid : ∀ s : ℕ, ∀ j, GridSimplex.vertex v τ s j ≤ p := fun s j =>
    GridSimplex.vertex_le v τ s j
  have hclose : ∀ s t : ℕ, dist (pt (GridSimplex.vertex v τ s)) (pt (GridSimplex.vertex v τ t)) < δ := by
    intro s t
    rw [dist_pi_lt_iff hδ]
    intro i
    have hd : |(GridSimplex.vertex v τ s i : ℝ) - (GridSimplex.vertex v τ t i : ℝ)| ≤ 1 := by
      unfold GridSimplex.vertex
      rw [abs_le]
      constructor <;> split_ifs <;> push_cast <;> linarith
    have hba := sub_nonneg.2 (hab i)
    rw [Real.dist_eq]
    have he : pt (GridSimplex.vertex v τ s) i - pt (GridSimplex.vertex v τ t) i =
        (b i - a i) / p * ((GridSimplex.vertex v τ s i : ℝ) - (GridSimplex.vertex v τ t i : ℝ)) := by
      simp only [hpt_def]
      field_simp
      ring
    rw [he, abs_mul, abs_of_nonneg (div_nonneg hba hpR.le)]
    calc (b i - a i) / p * |(GridSimplex.vertex v τ s i : ℝ) - (GridSimplex.vertex v τ t i : ℝ)|
        ≤ (b i - a i) / p * 1 := mul_le_mul_of_nonneg_left hd (div_nonneg hba hpR.le)
      _ < δ := by rw [mul_one]; exact hstep i
  set xs := pt (GridSimplex.vertex v τ 0) with hxs
  have hxsK : xs ∈ Set.Icc a b := hpt _ (hgrid 0)
  have hlt : ‖f xs - xs‖ < ‖f x0 - x0‖ := by
    rw [pi_norm_lt_iff hε]
    intro i
    obtain ⟨⟨j1, hj1⟩, ⟨j2, hj2⟩⟩ := hv i
    set y := pt (GridSimplex.vertex v τ j1) with hy
    set z := pt (GridSimplex.vertex v τ j2) with hz
    have hyK : y ∈ Set.Icc a b := hpt _ (hgrid _)
    have hzK : z ∈ Set.Icc a b := hpt _ (hgrid _)
    have hgy : 0 ≤ f y i - y i := by
      simp only [hlab, not_and_or, not_not, not_le] at hj1
      rcases hj1 with h | h
      · have hya : y i = a i := by
          simp only [hy, hpt_def, h]
          simp
        have := (hmap hyK).1 i
        linarith
      · linarith
    have hgz : f z i - z i ≤ 0 := by
      have := hj2.2
      linarith
    have hdy : dist (f xs - xs) (f y - y) < ‖f x0 - x0‖ := hδε xs hxsK y hyK (hclose 0 j1)
    have hdz : dist (f xs - xs) (f z - z) < ‖f x0 - x0‖ := hδε xs hxsK z hzK (hclose 0 j2)
    have hdy' := lt_of_le_of_lt (dist_le_pi_dist (f xs - xs) (f y - y) i) hdy
    have hdz' := lt_of_le_of_lt (dist_le_pi_dist (f xs - xs) (f z - z) i) hdz
    rw [Real.dist_eq] at hdy' hdz'
    simp only [Pi.sub_apply] at hdy' hdz' ⊢
    rw [Real.norm_eq_abs, abs_lt]
    rw [abs_lt] at hdy' hdz'
    constructor <;> linarith [hdy'.1, hdy'.2, hdz'.1, hdz'.2]
  exact absurd (hmin hxsK) (not_le.2 hlt)

end Breakdown
