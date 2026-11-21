import Breakdown.CertCell.ShapeStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

private theorem polynomial_eval_contDiff (p : Polynomial ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun t : ℝ => p.eval t) := by
  have h := p.contDiff_aeval (𝕜 := ℝ) n
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using h

private theorem clamp_hasDerivAt (φ φ' : ℝ → ℝ) (a t : ℝ) (h : ∀ s, HasDerivAt φ (φ' s) s)
    (ha : φ' a = 0) : HasDerivAt (fun s => φ (min s a)) (φ' (min t a)) t := by
  rcases lt_trichotomy t a with hta | hta | hta
  · rw [min_eq_left hta.le]
    apply (h t).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hta] with s hs
    simp [min_eq_left (Set.mem_Iio.mp hs).le]
  · subst hta
    rw [min_self]
    have h1 : HasDerivWithinAt (fun s => φ (min s t)) (φ' t) (Set.Iic t) t :=
      (h t).hasDerivWithinAt.congr (fun s hs => by simp [min_eq_left (Set.mem_Iic.mp hs)])
        (by simp)
    have h2 : HasDerivWithinAt (fun s => φ (min s t)) (φ' t) (Set.Ici t) t := by
      rw [ha]
      exact (hasDerivWithinAt_const t (Set.Ici t) (φ t)).congr
        (fun s hs => by simp [min_eq_right (Set.mem_Ici.mp hs)]) (by simp)
    have h3 := h1.union h2
    rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at h3
  · rw [min_eq_right hta.le, ha]
    apply (hasDerivAt_const t (φ a)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hta] with s hs
    simp [min_eq_right (Set.mem_Ioi.mp hs).le]

private theorem join_value (g : OriginProfile) (hg : IsOriginProfile g) (h1 : g.edge < 1) :
    g.poly.eval g.edge = g.tail := by
  simpa using hg.joins h1 0 (by norm_num)

private theorem join_slope (g : OriginProfile) (hg : IsOriginProfile g) (h1 : g.edge < 1) :
    g.poly.derivative.eval g.edge = 0 := by
  simpa using hg.joins h1 1 (by norm_num)

private theorem join_curvature (g : OriginProfile) (hg : IsOriginProfile g) (h1 : g.edge < 1) :
    g.poly.derivative.derivative.eval g.edge = 0 := by
  simpa using hg.joins h1 2 (by norm_num)

private theorem eval_eq_clamp (g : OriginProfile) (hg : IsOriginProfile g) (h1 : g.edge < 1) :
    g.eval = fun t => g.poly.eval (min t g.edge) := by
  funext t
  unfold OriginProfile.eval
  split_ifs with ht
  · rw [min_eq_left ht]
  · rw [min_eq_right (not_le.mp ht).le, join_value g hg h1]

private theorem eval_hasDerivAt (g : OriginProfile) (hg : IsOriginProfile g) (h1 : g.edge < 1) (t : ℝ) :
    HasDerivAt g.eval (g.poly.derivative.eval (min t g.edge)) t := by
  rw [eval_eq_clamp g hg h1]
  exact clamp_hasDerivAt (fun s => g.poly.eval s) (fun s => g.poly.derivative.eval s) g.edge t
    (fun s => g.poly.hasDerivAt s) (join_slope g hg h1)

private theorem deriv_eq_clamp (g : OriginProfile) (hg : IsOriginProfile g) (h1 : g.edge < 1) :
    deriv g.eval = fun t => g.poly.derivative.eval (min t g.edge) :=
  funext fun t => (eval_hasDerivAt g hg h1 t).deriv

private theorem deriv_hasDerivAt (g : OriginProfile) (hg : IsOriginProfile g) (h1 : g.edge < 1) (t : ℝ) :
    HasDerivAt (deriv g.eval) (g.poly.derivative.derivative.eval (min t g.edge)) t := by
  rw [deriv_eq_clamp g hg h1]
  exact clamp_hasDerivAt (fun s => g.poly.derivative.eval s)
    (fun s => g.poly.derivative.derivative.eval s) g.edge t
    (fun s => g.poly.derivative.hasDerivAt s) (join_curvature g hg h1)

private theorem second_deriv_eq_clamp (g : OriginProfile) (hg : IsOriginProfile g) (h1 : g.edge < 1) :
    deriv (deriv g.eval) = fun t => g.poly.derivative.derivative.eval (min t g.edge) :=
  funext fun t => (deriv_hasDerivAt g hg h1 t).deriv

private theorem eval_contDiff (g : OriginProfile) (hg : IsOriginProfile g) (h1 : g.edge < 1) :
    ContDiff ℝ 2 g.eval := by
  have e : (2 : WithTop ℕ∞) = 1 + 1 := rfl
  rw [e, contDiff_succ_iff_deriv]
  refine ⟨fun t => (eval_hasDerivAt g hg h1 t).differentiableAt, by simp, ?_⟩
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (deriv_hasDerivAt g hg h1 t).differentiableAt, ?_⟩
  rw [second_deriv_eq_clamp g hg h1]
  exact (Polynomial.continuous _).comp (continuous_id.min continuous_const)

private theorem second_deriv_slope (g : OriginProfile) (hg : IsOriginProfile g) (h1 : g.edge < 1)
    (R : ℝ) : ∃ L : NNReal, LipschitzOnWith L (deriv (deriv g.eval)) (Set.Icc (-R) R) := by
  obtain ⟨K, hK⟩ :=
    ((polynomial_eval_contDiff g.poly.derivative.derivative 1).contDiffOn
      (s := Set.Icc (-(|R| + 1)) (|R| + 1))).exists_lipschitzOnWith one_ne_zero (convex_Icc _ _)
      isCompact_Icc
  have hmin : LipschitzWith 1 (fun t : ℝ => min t g.edge) := LipschitzWith.id.min_const _
  refine ⟨K * 1, ?_⟩
  rw [second_deriv_eq_clamp g hg h1]
  refine hK.comp hmin.lipschitzOnWith ?_
  intro t ht
  have e0 := hg.edge_pos
  have r0 := le_abs_self R
  have r1 := abs_nonneg R
  constructor
  · exact le_min (by linarith [ht.1]) (by linarith)
  · exact (min_le_left _ _).trans (by linarith [ht.2])

private theorem eval_eq_poly (g : OriginProfile) (he : g.edge = 1) (t : ℝ) (ht : t < 1) :
    g.eval t = g.poly.eval t := by
  unfold OriginProfile.eval
  rw [if_pos (by rw [he]; exact ht.le)]

private theorem second_deriv_eq_poly (g : OriginProfile) (he : g.edge = 1) (t : ℝ) (ht : t < 1) :
    deriv (deriv g.eval) t = g.poly.derivative.derivative.eval t := by
  have hev : g.eval =ᶠ[nhds t] fun s => g.poly.eval s := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact eval_eq_poly g he s hs
  have hd : deriv (fun s => g.poly.eval s) = fun s => g.poly.derivative.eval s :=
    funext fun s => (g.poly.hasDerivAt s).deriv
  rw [hev.deriv.deriv_eq, hd]
  exact (g.poly.derivative.hasDerivAt t).deriv

theorem originProfileSmooth : OriginProfileSmooth := by
  intro g hg
  rcases lt_or_eq_of_le hg.edge_le with h1 | h1
  · exact ⟨(eval_contDiff g hg h1).contDiffOn, fun R _ => second_deriv_slope g hg h1 R⟩
  · refine ⟨(polynomial_eval_contDiff g.poly 2).contDiffOn.congr
      (fun t ht => eval_eq_poly g h1 t ht), fun R hR => ?_⟩
    obtain ⟨K, hK⟩ :=
      ((polynomial_eval_contDiff g.poly.derivative.derivative 1).contDiffOn
        (s := Set.Icc (-R) R)).exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc
    refine ⟨K, ?_⟩
    intro x hx y hy
    rw [second_deriv_eq_poly g h1 x (lt_of_le_of_lt hx.2 hR),
      second_deriv_eq_poly g h1 y (lt_of_le_of_lt hy.2 hR)]
    exact hK hx hy

end GivenShape

end CertCell

end Breakdown
