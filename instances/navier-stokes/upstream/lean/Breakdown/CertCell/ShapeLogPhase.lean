import Breakdown.CertCell.ShapeStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

theorem deriv_eq_of_eqOn_open {F G H : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hFG : ∀ t ∈ U, F t = G t) (hG : ∀ t ∈ U, HasDerivAt G (H t) t) :
    ∀ t ∈ U, deriv F t = H t := by
  intro t ht
  have h : F =ᶠ[nhds t] G := Filter.eventually_of_mem (hU.mem_nhds ht) hFG
  rw [h.deriv_eq]
  exact (hG t ht).deriv

theorem shifted_pos {c t : ℝ} (ht : t ∈ Set.Ioi (-c)) : 0 < c + t := by
  simp only [Set.mem_Ioi] at ht
  linarith

theorem logPhase_hasDerivAt (rate c : ℝ) (hc : 0 < c) (t : ℝ) (ht : t ∈ Set.Ioi (-c)) :
    HasDerivAt (fun s => rate / 2 * Real.log (1 + s / c)) (rate / 2 * (c + t)⁻¹) t := by
  have hpos : 0 < c + t := shifted_pos ht
  have hrw : 1 + t / c = (c + t) / c := by field_simp
  have hne : 1 + t / c ≠ 0 := by
    rw [hrw]
    exact (div_pos hpos hc).ne'
  have h1 : HasDerivAt (fun s => 1 + s / c) (1 / c) t :=
    ((hasDerivAt_id' t).div_const c).const_add 1
  refine ((h1.log hne).const_mul (rate / 2)).congr_deriv ?_
  rw [hrw]
  have hne' : c + t ≠ 0 := hpos.ne'
  have hcne : c ≠ 0 := hc.ne'
  field_simp

theorem inv_shift_hasDerivAt (rate c : ℝ) (t : ℝ) (ht : t ∈ Set.Ioi (-c)) :
    HasDerivAt (fun s => rate / 2 * (c + s)⁻¹) (-(rate / 2) * ((c + t) ^ 2)⁻¹) t := by
  have hpos : 0 < c + t := shifted_pos ht
  refine ((((hasDerivAt_id' t).const_add c).inv hpos.ne').const_mul (rate / 2)).congr_deriv ?_
  ring

theorem inv_sq_shift_hasDerivAt (rate c : ℝ) (t : ℝ) (ht : t ∈ Set.Ioi (-c)) :
    HasDerivAt (fun s => -(rate / 2) * ((c + s) ^ 2)⁻¹) (rate * ((c + t) ^ 3)⁻¹) t := by
  have hpos : 0 < c + t := shifted_pos ht
  refine (((((hasDerivAt_id' t).const_add c).pow 2).inv (pow_pos hpos 2).ne').const_mul (-(rate / 2))).congr_deriv ?_
  have hne' : c + t ≠ 0 := hpos.ne'
  simp only [Pi.pow_apply]
  field_simp
  ring

theorem radial_of_pos (rate c : ℝ) (hc : 0 < c) :
    IsRadialPhase (fun s => rate / 2 * Real.log (1 + s / c)) := by
  have hU : IsOpen (Set.Ioi (-c)) := isOpen_Ioi
  have d1 : ∀ t ∈ Set.Ioi (-c), deriv (fun s => rate / 2 * Real.log (1 + s / c)) t =
      rate / 2 * (c + t)⁻¹ := fun t ht => (logPhase_hasDerivAt rate c hc t ht).deriv
  have d2 : ∀ t ∈ Set.Ioi (-c), deriv (deriv (fun s => rate / 2 * Real.log (1 + s / c))) t =
      -(rate / 2) * ((c + t) ^ 2)⁻¹ :=
    deriv_eq_of_eqOn_open hU d1 (fun t ht => inv_shift_hasDerivAt rate c t ht)
  have d3 : ∀ t ∈ Set.Ioi (-c),
      deriv (deriv (deriv (fun s => rate / 2 * Real.log (1 + s / c)))) t = rate * ((c + t) ^ 3)⁻¹ :=
    deriv_eq_of_eqOn_open hU d2 (fun t ht => inv_sq_shift_hasDerivAt rate c t ht)
  refine ⟨⟨c, hc, ?_⟩, ⟨|rate|, fun s hs => ?_⟩⟩
  · refine contDiffOn_const.mul (ContDiffOn.log ?_ ?_)
    · exact contDiffOn_const.add (contDiffOn_id.div_const c)
    · intro x hx
      have hpos : 0 < c + x := shifted_pos hx
      have hrw : 1 + x / c = (c + x) / c := by field_simp
      rw [hrw]
      exact (div_pos hpos hc).ne'
  · have hs' : s ∈ Set.Ioi (-c) := by
      simp only [Set.mem_Ioi]
      linarith
    have hpos : 0 < c + s := shifted_pos hs'
    have hq0 : 0 ≤ s * (c + s)⁻¹ := mul_nonneg hs (inv_nonneg.mpr hpos.le)
    have hq1 : s * (c + s)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hpos]
      linarith
    have hr2 : |rate / 2| = |rate| / 2 := by rw [abs_div, abs_two]
    have hra : 0 ≤ |rate| := abs_nonneg rate
    have i2 : iteratedDeriv 2 (fun s => rate / 2 * Real.log (1 + s / c)) s =
        deriv (deriv (fun s => rate / 2 * Real.log (1 + s / c))) s := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have i3 : iteratedDeriv 3 (fun s => rate / 2 * Real.log (1 + s / c)) s =
        deriv (deriv (deriv (fun s => rate / 2 * Real.log (1 + s / c)))) s := by
      rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
    rw [i2, i3, d1 s hs', d2 s hs', d3 s hs']
    have e1 : s * (rate / 2 * (c + s)⁻¹) = rate / 2 * (s * (c + s)⁻¹) := by ring
    have e2 : s ^ 2 * (-(rate / 2) * ((c + s) ^ 2)⁻¹) = -(rate / 2) * (s * (c + s)⁻¹) ^ 2 := by
      rw [mul_pow, inv_pow]
      ring
    have e3 : s ^ 3 * (rate * ((c + s) ^ 3)⁻¹) = rate * (s * (c + s)⁻¹) ^ 3 := by
      rw [mul_pow, inv_pow]
      ring
    rw [e1, e2, e3]
    have p2 : (s * (c + s)⁻¹) ^ 2 ≤ 1 := pow_le_one₀ hq0 hq1
    have p3 : (s * (c + s)⁻¹) ^ 3 ≤ 1 := pow_le_one₀ hq0 hq1
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_mul, abs_of_nonneg hq0, hr2]
      nlinarith
    · rw [abs_mul, abs_neg, abs_of_nonneg (pow_nonneg hq0 2), hr2]
      nlinarith
    · rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 3)]
      nlinarith

end Internal

theorem logPhaseIsRadial : LogPhaseIsRadial := by
  intro rate hbase hcore
  exact Internal.radial_of_pos rate (hbase ^ 2) (by positivity)

end GivenShape

end CertCell

end Breakdown
