import Breakdown.Spectral.SpectrumEigen
import Breakdown.Spectral.Separation

noncomputable section

namespace Breakdown.Spectral

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

private lemma exists_pow_gap {b r : ℝ} (hb : 0 ≤ b) (hbr : b < r) :
    ∃ N : ℕ, 1 ≤ N ∧ 4 * b ^ N < r ^ N := by
  have hr : 0 < r := lt_of_le_of_lt hb hbr
  have h0 : 0 ≤ b / r := div_nonneg hb hr.le
  have h1 : b / r < 1 := (div_lt_one hr).2 hbr
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  have hev := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))).and
    (Filter.eventually_ge_atTop 1)
  obtain ⟨N, hN, hN1⟩ := hev.exists
  refine ⟨N, hN1, ?_⟩
  have hrN : 0 < r ^ N := pow_pos hr N
  rw [div_pow, div_lt_iff₀ hrN] at hN
  linarith

private lemma finite_pow_fiber {N : ℕ} (hN : 0 < N) (w : ℂ) :
    ((fun z : ℂ => z ^ N) ⁻¹' {w}).Finite := by
  refine (Polynomial.nthRootsFinset N w).finite_toSet.subset ?_
  intro z hz
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
  exact (Polynomial.mem_nthRootsFinset hN w).2 hz

theorem finite_spectrum_outside (T₀ C : Y →L[ℂ] Y) {b r : ℝ} (hT₀ : ‖T₀‖ ≤ b) (hbr : b < r)
    (hC : IsCompactOperator C) : {z ∈ spectrum ℂ (T₀ + C) | r ≤ ‖z‖}.Finite := by
  have hb : 0 ≤ b := le_trans (norm_nonneg _) hT₀
  have hr : 0 < r := lt_of_le_of_lt hb hbr
  obtain ⟨N, hN1, hN⟩ := exists_pow_gap hb hbr
  have hNpos : 0 < N := hN1
  by_contra hinf
  set E := {z ∈ spectrum ℂ (T₀ + C) | r ≤ ‖z‖} with hEdef
  have himg : ((fun z : ℂ => z ^ N) '' E).Infinite := by
    intro hfin
    apply hinf
    refine (hfin.preimage' (fun w _ => finite_pow_fiber hNpos w)).subset ?_
    intro z hz
    exact ⟨z, hz, rfl⟩
  let e := himg.natEmbedding
  let μ : ℕ → ℂ := fun k => (e k : ℂ)
  have hμ : Function.Injective μ := fun i j hij => e.injective (Subtype.ext hij)
  have hmem : ∀ k, ∃ z ∈ E, z ^ N = μ k := fun k => (e k).2
  have hE : ∀ k, Module.End.HasEigenvalue (((T₀ + C) ^ N : Y →L[ℂ] Y) : Module.End ℂ Y) (μ k) := by
    intro k
    obtain ⟨z, ⟨hzσ, hzr⟩, hz⟩ := hmem k
    rw [← hz]
    exact hasEigenvalue_pow (hasEigenvalue_of_mem_spectrum T₀ C hT₀ hC hzσ
      (lt_of_lt_of_le hbr hzr)) N
  have hnorm : ∀ k, r ^ N ≤ ‖μ k‖ := by
    intro k
    obtain ⟨z, ⟨_, hzr⟩, hz⟩ := hmem k
    rw [← hz, norm_pow]
    exact pow_le_pow_left₀ hr.le hzr N
  obtain ⟨y, hy, hsep⟩ := exists_separated_of_eigen ((T₀ + C) ^ N) μ hμ hE
  have hA : ‖T₀ ^ N‖ ≤ b ^ N :=
    le_trans (norm_pow_le' T₀ hNpos) (pow_le_pow_left₀ (norm_nonneg _) hT₀ N)
  have hK := isCompactOperator_pow_sub_pow T₀ C hC N
  refine not_separated_of_compact (T₀ ^ N) ((T₀ + C) ^ N - T₀ ^ N) hA hK
    (c := r ^ N / 2) (by linarith) y hy ?_
  intro m n hmn
  rw [add_sub_cancel]
  exact le_trans (by linarith [hnorm n]) (hsep m n hmn)

theorem exists_annulus (T₀ C : Y →L[ℂ] Y) {b α β : ℝ} (hT₀ : ‖T₀‖ ≤ b) (hbα : b ≤ α)
    (hαβ : α < β) (hC : IsCompactOperator C) :
    ∃ ρ₁ ρ₂ : ℝ, α < ρ₁ ∧ ρ₁ < ρ₂ ∧ ρ₂ < β ∧
      ∀ z : ℂ, ρ₁ ≤ ‖z‖ → ‖z‖ ≤ ρ₂ → z ∈ resolventSet ℂ (T₀ + C) := by
  set r := (α + β) / 2 with hrdef
  have hαr : α < r := by rw [hrdef]; linarith
  have hrβ : r < β := by rw [hrdef]; linarith
  have hfin := finite_spectrum_outside T₀ C hT₀ (lt_of_le_of_lt hbα hαr) hC
  set s : Set ℝ := insert β ((fun z : ℂ => ‖z‖) '' {z ∈ spectrum ℂ (T₀ + C) | r ≤ ‖z‖} ∩
    Set.Ioi r) with hsdef
  have hsfin : s.Finite := ((hfin.image _).inter_of_left _).insert β
  obtain ⟨m, hms, hmin⟩ := Set.exists_min_image s id hsfin ⟨β, Set.mem_insert _ _⟩
  have hmβ : m ≤ β := hmin β (Set.mem_insert _ _)
  have hrm : r < m := by
    rcases hms with h | ⟨_, h⟩
    · rw [h]; exact hrβ
    · exact h
  refine ⟨r + (m - r) / 3, r + 2 * (m - r) / 3, by linarith, by linarith, by linarith, ?_⟩
  intro z hz1 hz2
  by_contra hres
  have hzσ : z ∈ spectrum ℂ (T₀ + C) := hres
  have hzs : ‖z‖ ∈ s :=
    Set.mem_insert_of_mem _ ⟨⟨z, ⟨hzσ, by linarith⟩, rfl⟩, show r < ‖z‖ by linarith⟩
  have := hmin _ hzs
  simp only [id] at this
  linarith

end Breakdown.Spectral
