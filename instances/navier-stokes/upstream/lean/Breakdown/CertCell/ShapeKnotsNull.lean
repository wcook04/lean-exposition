import Breakdown.CertCell.ShapeKnots

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace KnotNull

def flat : Set Space := {y | y 2 = 0}

def sph (r : ℝ) : Set Space := {y | y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 = r ^ 2}

def cone (b : ℝ) : Set Space := {y | y 2 ^ 2 = b ^ 2 * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2)}

theorem norm_sq_eq (y : Space) : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

theorem coord_null (i : Fin 3) : volume {y : Space | y i = 0} = 0 := by
  have hs : ({y : Space | y i = 0} : Set Space) =
      (LinearMap.ker (EuclideanSpace.proj i : Space →L[ℝ] ℝ).toLinearMap : Set Space) := by
    ext y
    simp
  rw [hs]
  apply Measure.addHaar_submodule
  intro htop
  have h : (EuclideanSpace.single i (1 : ℝ) : Space) ∈
      LinearMap.ker (EuclideanSpace.proj i : Space →L[ℝ] ℝ).toLinearMap := by
    rw [htop]
    trivial
  simp at h

theorem flat_null : volume flat = 0 := coord_null 2

theorem sph_null (r : ℝ) : volume (sph r) = 0 := by
  refine measure_mono_null (fun y hy => ?_) (Measure.addHaar_sphere volume (0 : Space) |r|)
  simp only [Metric.mem_sphere, dist_zero_right]
  have h := norm_sq_eq y
  rw [show y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 = r ^ 2 from hy] at h
  rw [← Real.sqrt_sq (norm_nonneg y), h, Real.sqrt_sq_eq_abs]

def lift (c : ℝ) (x : Space) : Space :=
  x 0 • EuclideanSpace.single 0 (1 : ℝ) + x 1 • EuclideanSpace.single 1 (1 : ℝ) +
    (c * Real.sqrt (x 0 ^ 2 + x 1 ^ 2)) • EuclideanSpace.single 2 (1 : ℝ)

theorem lift_differentiableOn (c : ℝ) :
    DifferentiableOn ℝ (lift c) {x : Space | x 2 = 0 ∧ x 0 ^ 2 + x 1 ^ 2 ≠ 0} := by
  intro x hx
  have h0 : DifferentiableAt ℝ (fun x : Space => x 0) x :=
    (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).differentiableAt
  have h1 : DifferentiableAt ℝ (fun x : Space => x 1) x :=
    (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).differentiableAt
  have hq : DifferentiableAt ℝ (fun x : Space => x 0 ^ 2 + x 1 ^ 2) x := (h0.pow 2).add (h1.pow 2)
  have hs : DifferentiableAt ℝ (fun x : Space => c * Real.sqrt (x 0 ^ 2 + x 1 ^ 2)) x :=
    (hq.sqrt hx.2).const_mul c
  exact (((h0.smul_const _).add (h1.smul_const _)).add (hs.smul_const _)).differentiableWithinAt

theorem lift_apply (c : ℝ) (x : Space) :
    lift c x 0 = x 0 ∧ lift c x 1 = x 1 ∧ lift c x 2 = c * Real.sqrt (x 0 ^ 2 + x 1 ^ 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [lift]

theorem cone_null (b : ℝ) : volume (cone b) = 0 := by
  rcases lt_trichotomy (b ^ 2) 1 with hb | hb | hb
  · set β := Real.sqrt (b ^ 2 / (1 - b ^ 2)) with hβ
    set H : Set Space := {x : Space | x 2 = 0 ∧ x 0 ^ 2 + x 1 ^ 2 ≠ 0}
    have hH : volume H = 0 := measure_mono_null (fun x hx => hx.1) flat_null
    have hsub : cone b ⊆ {y : Space | y 0 = 0} ∪ (lift β '' H ∪ lift (-β) '' H) := by
      intro y hy
      have hy' : y 2 ^ 2 = b ^ 2 * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) := hy
      by_cases hρ : y 0 ^ 2 + y 1 ^ 2 = 0
      · left
        show y 0 = 0
        nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
      · right
        have hpos : 0 < 1 - b ^ 2 := by linarith
        have hρ0 : 0 ≤ y 0 ^ 2 + y 1 ^ 2 := by positivity
        have key : y 2 ^ 2 = (β * Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) ^ 2 := by
          rw [mul_pow, hβ, Real.sq_sqrt (div_nonneg (sq_nonneg b) hpos.le), Real.sq_sqrt hρ0]
          field_simp
          nlinarith [hy']
        let x : Space := y 0 • EuclideanSpace.single 0 (1 : ℝ) + y 1 • EuclideanSpace.single 1 (1 : ℝ)
        have hx0 : x 0 = y 0 := by simp [x]
        have hx1 : x 1 = y 1 := by simp [x]
        have hx2 : x 2 = 0 := by simp [x]
        have hxH : x ∈ H := ⟨hx2, by rw [hx0, hx1]; exact hρ⟩
        have hl : ∀ c : ℝ, y 2 = c * Real.sqrt (y 0 ^ 2 + y 1 ^ 2) → lift c x = y := by
          intro c hc
          ext i
          fin_cases i <;> simp [lift, x, hc]
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp key with h | h
        · exact Or.inl ⟨x, hxH, hl β h⟩
        · exact Or.inr ⟨x, hxH, hl (-β) (by rw [h]; ring)⟩
    refine measure_mono_null hsub (measure_union_null (coord_null 0) (measure_union_null ?_ ?_))
    · exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume (lift_differentiableOn β) hH
    · exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume (lift_differentiableOn (-β)) hH
  · refine measure_mono_null (fun y hy => ?_) (coord_null 0)
    have hy' : y 2 ^ 2 = b ^ 2 * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) := hy
    rw [hb, one_mul] at hy'
    show y 0 = 0
    nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
  · refine measure_mono_null (fun y hy => ?_) flat_null
    have hy' : y 2 ^ 2 = b ^ 2 * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) := hy
    show y 2 = 0
    have h2 : y 2 ^ 2 = 0 := by
      nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2), mul_nonneg (sq_nonneg (y 2)) (sub_nonneg.mpr hb.le),
        mul_nonneg (sub_nonneg.mpr hb.le) (add_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1)))]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h2

open GivenShape

open CellCert.GivenFields (Spline)

def splineSet (P : ShapeParams) (S : Spline) : Set Space :=
  (⋃ b ∈ {b | b ∈ S.mesh.tBreaks}, sph (chartRadius P b)) ∪ ⋃ b ∈ {b | b ∈ S.mesh.xBreaks}, cone b

theorem splineSet_null (P : ShapeParams) (S : Spline) : volume (splineSet P S) = 0 :=
  measure_union_null ((measure_biUnion_null_iff (List.finite_toSet _).countable).2 fun b _ => sph_null _)
    ((measure_biUnion_null_iff (List.finite_toSet _).countable).2 fun b _ => cone_null b)

def keySet (P : ShapeParams) (A : KeyAmp) : Set Space :=
  splineSet P A.radial ∪ splineSet P A.polar ∪ splineSet P A.stream ∪ splineSet P A.swirl

theorem keySet_null (P : ShapeParams) (A : KeyAmp) : volume (keySet P A) = 0 :=
  measure_union_null (measure_union_null (measure_union_null (splineSet_null P _) (splineSet_null P _))
    (splineSet_null P _)) (splineSet_null P _)

def bigSet (P : ShapeParams) (D : TimeFieldData) : Set Space :=
  flat ∪ {y | y 0 = 0} ∪ sph (chartRadius P P.origin.edge) ∪ ⋃ κ ∈ (↑D.keys : Set FieldKey), keySet P (D.amp κ)

theorem bigSet_null (P : ShapeParams) (D : TimeFieldData) : volume (bigSet P D) = 0 :=
  measure_union_null (measure_union_null (measure_union_null flat_null (coord_null 0)) (sph_null _))
    ((measure_biUnion_null_iff D.keys.countable_toSet).2 fun κ _ => keySet_null P _)

theorem planeNorm_sq {y : Space} {q : ℝ × ℝ} (h1 : q.1 = Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) (h2 : q.2 ^ 2 = y 2 ^ 2) :
    planeNorm q ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
  rw [planeNorm, Real.sq_sqrt (by positivity), h1, Real.sq_sqrt (by positivity), h2]

theorem mem_bigSet {P : ShapeParams} {D : TimeFieldData} {y : Space} {q : ℝ × ℝ}
    (h1 : q.1 = Real.sqrt (y 0 ^ 2 + y 1 ^ 2)) (h2 : q.2 ^ 2 = y 2 ^ 2) (hq : q ∈ shapeKnots P D) :
    y ∈ bigSet P D := by
  have hn := planeNorm_sq h1 h2
  have hsph : ∀ c, planeNorm q = c → y ∈ sph c := by
    intro c hc
    show y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 = c ^ 2
    rw [← hn, hc]
  have hcone : ∀ b, q.2 = b * planeNorm q → y ∈ cone b := by
    intro b hb
    show y 2 ^ 2 = b ^ 2 * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2)
    rw [← hn, ← h2, hb, mul_pow]
  have hspl : ∀ S : Spline, q ∈ splineKnots P S → y ∈ splineSet P S := by
    intro S hS
    rcases hS with ⟨b, hb, hb'⟩ | ⟨b, hb, hb'⟩
    · exact Or.inl (Set.mem_biUnion hb (hsph _ hb'))
    · exact Or.inr (Set.mem_biUnion hb (hcone _ hb'))
  simp only [shapeKnots, Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion] at hq
  rcases hq with (((h | h) | h) | h) | ⟨κ, hκ, hk⟩
  · left; left; left
    show y 2 = 0
    rw [h] at h2
    exact pow_eq_zero_iff two_ne_zero |>.mp (by rw [← h2]; ring)
  · left; left; right
    show y 0 = 0
    rw [h] at h1
    have h0 : y 0 ^ 2 + y 1 ^ 2 = 0 := (Real.sqrt_eq_zero (by positivity)).mp h1.symm
    nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
  · left; left; left
    show y 2 = 0
    have h0 : q.2 = 0 := by rw [h]; rfl
    rw [h0] at h2
    exact pow_eq_zero_iff two_ne_zero |>.mp (by rw [← h2]; ring)
  · left; right
    obtain ⟨b, hb, hb'⟩ := h
    rw [List.mem_singleton] at hb
    rw [hb] at hb'
    exact hsph _ hb'
  · right
    refine Set.mem_biUnion (show κ ∈ (↑D.keys : Set FieldKey) from hκ) ?_
    rcases hk with ((h | h) | h) | h
    · exact Or.inl (Or.inl (Or.inl (hspl _ h)))
    · exact Or.inl (Or.inl (Or.inr (hspl _ h)))
    · exact Or.inl (Or.inr (hspl _ h))
    · exact Or.inr (hspl _ h)

theorem shapeKnotsNullSpace : ShapeKnotsNullSpace := by
  intro P D _
  refine measure_mono_null (fun y hy => ?_) (bigSet_null P D)
  rcases hy with h | h
  · exact mem_bigSet rfl rfl h
  · exact mem_bigSet (q := ((KnotZero.planeOf y).1, -(KnotZero.planeOf y).2)) rfl (by simp [KnotZero.planeOf]) h

end KnotNull

end CertCell

end Breakdown
