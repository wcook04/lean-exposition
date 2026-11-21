import Breakdown.CertCell.ShapeStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline cellCount cellIndex)

namespace Internal

theorem reflectPoly_C_mul (c : ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    reflectPoly (MvPolynomial.C c * P) = MvPolynomial.C c * reflectPoly P := by
  unfold reflectPoly
  rw [map_mul, MvPolynomial.bind₁_C_right]

theorem reflectPoly_reflectPoly (P : MvPolynomial (Fin 2) ℂ) : reflectPoly (reflectPoly P) = P := by
  unfold reflectPoly
  rw [MvPolynomial.bind₁_bind₁]
  have h : (fun i : Fin 2 => MvPolynomial.bind₁
      (fun k : Fin 2 => if k = 0 then (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) else -MvPolynomial.X 1)
      (if i = 0 then (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) else -MvPolynomial.X 1)) = MvPolynomial.X := by
    funext i
    fin_cases i <;> simp
  rw [h, MvPolynomial.bind₁_X_left]
  rfl

theorem map_reflectPoly (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (reflectPoly P) = reflectPoly (MvPolynomial.map (starRingEnd ℂ) P) := by
  unfold reflectPoly
  rw [MvPolynomial.map_bind₁]
  have h : (fun i : Fin 2 => MvPolynomial.map (starRingEnd ℂ)
      (if i = 0 then (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) else -MvPolynomial.X 1)) =
      fun k : Fin 2 => if k = 0 then (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) else -MvPolynomial.X 1 := by
    funext i
    split_ifs <;> simp
  rw [h]

theorem map_conj_conj (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map (starRingEnd ℂ) P) = P := by
  rw [MvPolynomial.map_map]
  have h : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := RingHom.ext fun z => by simp
  rw [h, MvPolynomial.map_id]

theorem sign_mul_self (odd : Bool) : (if odd then -1 else 1 : ℂ) * (if odd then -1 else 1) = 1 := by
  cases odd <;> norm_num

theorem sign_conj (odd : Bool) : starRingEnd ℂ (if odd then -1 else 1 : ℂ) = (if odd then -1 else 1 : ℂ) := by
  cases odd <;> simp

theorem cellCount_reflect (l : List ℝ) : cellCount ((l.map Neg.neg).reverse) = cellCount l := by
  simp [cellCount]

theorem agrees_refl (S : Spline) : SplineAgrees S S := ⟨rfl, fun _ _ _ _ => rfl⟩

theorem agrees_symm {S T : Spline} (h : SplineAgrees S T) : SplineAgrees T S := by
  refine ⟨h.mesh_eq.symm, fun i hi j hj => ?_⟩
  rw [← h.mesh_eq] at hi hj
  exact (h.piece_eq i hi j hj).symm

theorem agrees_trans {S T U : Spline} (h1 : SplineAgrees S T) (h2 : SplineAgrees T U) :
    SplineAgrees S U := by
  refine ⟨h1.mesh_eq.trans h2.mesh_eq, fun i hi j hj => ?_⟩
  have hi' := hi
  have hj' := hj
  rw [h1.mesh_eq] at hi' hj'
  exact (h1.piece_eq i hi j hj).trans (h2.piece_eq i hi' j hj')

theorem agrees_conj {S T : Spline} (h : SplineAgrees S T) : SplineAgrees S.conj T.conj := by
  refine ⟨h.mesh_eq, fun i hi j hj => ?_⟩
  show MvPolynomial.map (starRingEnd ℂ) (S.piece i j) = MvPolynomial.map (starRingEnd ℂ) (T.piece i j)
  rw [h.piece_eq i hi j hj]

theorem agrees_reflect (odd : Bool) {S T : Spline} (h : SplineAgrees S T) :
    SplineAgrees (reflectSpline odd S) (reflectSpline odd T) := by
  refine ⟨?_, fun i hi j hj => ?_⟩
  · simp only [reflectSpline, h.mesh_eq]
  · have hj' : j < cellCount S.mesh.xBreaks := by
      have hc := cellCount_reflect S.mesh.xBreaks
      dsimp only [reflectSpline] at hj
      omega
    dsimp only [reflectSpline]
    rw [← h.mesh_eq, h.piece_eq i hi _ (by omega)]

theorem agrees_conj_conj (S : Spline) : SplineAgrees S.conj.conj S :=
  ⟨rfl, fun i _ j _ => map_conj_conj (S.piece i j)⟩

theorem agrees_reflect_reflect (odd : Bool) (S : Spline) :
    SplineAgrees (reflectSpline odd (reflectSpline odd S)) S := by
  refine ⟨?_, fun i hi j hj => ?_⟩
  · obtain ⟨⟨tb, xb⟩, p⟩ := S
    simp [reflectSpline]
  · have hc := cellCount_reflect S.mesh.xBreaks
    have hj' : j < cellCount S.mesh.xBreaks := by
      dsimp only [reflectSpline] at hj
      simp only [cellCount_reflect] at hj
      exact hj
    dsimp only [reflectSpline]
    rw [hc, reflectPoly_C_mul, ← mul_assoc, ← map_mul, sign_mul_self, map_one, one_mul,
      reflectPoly_reflectPoly]
    congr 1
    omega

theorem agrees_reflect_conj (odd : Bool) (S : Spline) :
    SplineAgrees (reflectSpline odd S).conj (reflectSpline odd S.conj) := by
  refine ⟨rfl, fun i _ j _ => ?_⟩
  dsimp only [reflectSpline, CellCert.GivenFields.Spline.conj]
  rw [map_mul, MvPolynomial.map_C, map_reflectPoly, sign_conj]

theorem joined_of_agrees {a b : ℕ} {S T : Spline} (h : SplineAgrees S T) (hS : IsJoinedSpline a b S) :
    IsJoinedSpline a b T := by
  obtain ⟨hm, hp⟩ := h
  refine ⟨by rw [← hm]; exact hS.mesh, fun i hi hic j hj o ho => ?_, fun j hj hjc i hi o ho => ?_⟩
  · rw [← hm] at hic hj ⊢
    rw [← hp (i - 1) (by omega) j hj, ← hp i hic j hj]
    exact hS.t_joins i hi hic j hj o ho
  · rw [← hm] at hjc hi ⊢
    rw [← hp i hi (j - 1) (by omega), ← hp i hi j hjc]
    exact hS.x_joins j hj hjc i hi o ho

theorem two_le_length_of_ends {l : List ℝ} {a b : ℝ} (hab : a ≠ b) (h1 : l.head? = some a)
    (h2 : l.getLast? = some b) : 2 ≤ l.length := by
  match l, h1, h2 with
  | [], h1, _ => simp at h1
  | [c], h1, h2 =>
    simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at h1 h2
    exact absurd (h1.symm.trans h2) hab
  | _ :: _ :: _, _, _ =>
    simp only [List.length_cons]
    omega

theorem cellIndex_lt {l : List ℝ} (h : 2 ≤ l.length) (u : ℝ) : cellIndex l u < cellCount l := by
  unfold cellIndex cellCount
  have hf := List.length_filter_le (fun b => decide (b ≤ u)) ((l.drop 1).dropLast)
  simp only [List.length_dropLast, List.length_drop] at hf
  omega

theorem evalHalf_of_agrees {S T : Spline} (h : SplineAgrees S T) (hm : IsFullMesh S.mesh) (t x : ℝ) :
    S.evalHalf t x = T.evalHalf t x := by
  have ht := cellIndex_lt (two_le_length_of_ends (by norm_num) hm.t_first hm.t_last) t
  have hx := cellIndex_lt (two_le_length_of_ends (by norm_num) hm.x_first hm.x_last) x
  unfold CellCert.GivenFields.Spline.evalHalf
  rw [← h.mesh_eq, h.piece_eq _ ht _ hx]

end Internal

open Internal in
theorem splineAgreementRules : SplineAgreementRules := by
  intro a b odd S T U
  exact ⟨agrees_refl S, agrees_symm, agrees_trans, fun h => ⟨agrees_conj h, agrees_reflect odd h⟩,
    agrees_conj_conj S, agrees_reflect_reflect odd S, agrees_reflect_conj odd S, joined_of_agrees,
    fun h hm => evalHalf_of_agrees h hm⟩

end GivenShape

end CertCell

end Breakdown
