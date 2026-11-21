import Breakdown.CertCell.ShapeSplineReflect

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline cellCount weightPoly radialScale heightDeriv heightRatio radialVec polarVecQ
  azimVecQ qOf)

namespace Internal

theorem flipPoint_coords (y : Space) : flipPoint y 0 = y 0 ∧ flipPoint y 1 = -y 1 ∧ flipPoint y 2 = -y 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [flipPoint, unitVector]

theorem norm_of_flipPoint (y : Space) : ‖flipPoint y‖ = ‖y‖ := by
  obtain ⟨h0, h1, h2⟩ := flipPoint_coords y
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_three, Fin.sum_univ_three, h0, h1, h2,
    norm_neg, norm_neg]

theorem heightRatio_of_flipPoint (y : Space) : heightRatio (flipPoint y) = -heightRatio y := by
  unfold CellCert.GivenFields.heightRatio
  rw [norm_of_flipPoint, (flipPoint_coords y).2.2, neg_div]

theorem chartCoord_of_flipPoint (P : ShapeParams) (y : Space) : chartCoord P (flipPoint y) = chartCoord P y := by
  unfold chartCoord
  rw [norm_of_flipPoint]

theorem keyPhase_of_flipKey (P : ShapeParams) (κ : FieldKey) (σ : ℝ) (y : Space) :
    keyPhase P κ.flipKey σ (flipPoint y) = keyPhase P κ σ y := by
  obtain ⟨h0, h1, -⟩ := flipPoint_coords y
  have hθ : pointAngle (flipPoint y) = if pointAngle y = Real.pi then Real.pi else -pointAngle y := by
    unfold pointAngle
    rw [← Complex.arg_conj, h0, h1]
    congr 1
    apply Complex.ext <;> simp
  have ht : labelTime κ.flipKey.label = labelTime κ.label := by
    simp only [FieldKey.flipKey, labelTime, labelFlip]
    ring
  have hk : labelAzimuth P.azimuthOrder κ.flipKey.label = -labelAzimuth P.azimuthOrder κ.label := by
    simp only [FieldKey.flipKey, labelAzimuth, labelFlip]
    ring
  have hj : κ.flipKey.phaseIndex = κ.phaseIndex := rfl
  unfold keyPhase
  rw [norm_of_flipPoint, ht, hk, hj, hθ]
  split_ifs with h
  · rw [h]
    apply Complex.exp_eq_exp_iff_exists_int.2
    refine ⟨-labelAzimuth P.azimuthOrder κ.label, ?_⟩
    push_cast
    ring
  · congr 1
    push_cast
    ring

theorem polarFactor_of_neg (x : ℝ) : polarFactor (-x) = polarFactor x := by
  unfold polarFactor
  rw [neg_sq]

theorem axisFactor_of_neg (x : ℝ) : axisFactor (-x) = axisFactor x := by
  unfold axisFactor
  rw [neg_sq]

theorem shiftedScale_of_reflected (P : ShapeParams) (j : ℤ) (f : ℝ → ℝ → ℂ) (t x : ℝ) :
    shiftedScale P j (fun t' x' => f t' (-x')) t x = shiftedScale P j f t (-x) := rfl

theorem heightDeriv_of_reflected_neg (f : ℝ → ℝ → ℂ) (t x : ℝ) :
    heightDeriv (fun t' x' => -f t' (-x')) t x = heightDeriv f t (-x) := by
  unfold CellCert.GivenFields.heightDeriv
  rw [show (fun x' : ℝ => -f t (-x')) = -(fun x' : ℝ => f t (-x')) from rfl, deriv.neg, deriv_comp_neg, neg_neg]

theorem heightDeriv_of_odd (f : ℝ → ℝ → ℂ) (hf : ∀ t x, f t (-x) = -f t x) (t x : ℝ) :
    heightDeriv f t (-x) = heightDeriv f t x := by
  have e : f = fun t' x' => -f t' (-x') := by
    funext t' x'
    rw [hf, neg_neg]
  conv_rhs => rw [e]
  rw [heightDeriv_of_reflected_neg]

theorem shiftedScale_of_odd (P : ShapeParams) (j : ℤ) (f : ℝ → ℝ → ℂ) (hf : ∀ t x, f t (-x) = -f t x)
    (t x : ℝ) : shiftedScale P j f t (-x) = -shiftedScale P j f t x := by
  unfold shiftedScale CellCert.GivenFields.radialScale
  have e : (fun t' => f t' (-x)) = -(fun t' => f t' x) := by
    funext t'
    rw [hf]
    rfl
  rw [e, deriv.neg, hf]
  ring

def compsOne (P : ShapeParams) (j : ℤ) (k : ℂ) (ur uθ : ℝ → ℝ → ℂ) (t x : ℝ) : Fin 3 → ℂ :=
  ![ur t x, uθ t x, (Complex.I / k) *
    (shiftedScale P j ur t x + 2 * ur t x - heightDeriv (fun t' x' => polarFactor x' * uθ t' x') t x)]

def compsTwo (P : ShapeParams) (j : ℤ) (p : ℝ → ℂ) (Ψ G : ℝ → ℝ → ℂ) (t x : ℝ) : Fin 3 → ℂ :=
  ![-(p t * heightDeriv (fun t' x' => polarFactor x' * Ψ t' x') t x),
    -(shiftedScale P j (fun t' x' => p t' * Ψ t' x') t x + 2 * (p t * Ψ t x)), p t * G t x]

theorem reducedComps_of_typeOne (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (h : κ.label.1 ≠ 0) (t x : ℝ) :
    reducedComps P κ A t x = compsOne P κ.phaseIndex (labelAzimuth P.azimuthOrder κ.label : ℂ)
      (fun t' x' => weightPoly A.lowOrder A.highOrder t' * axisFactor x' * A.radial.evalHalf t' x')
      (fun t' x' => weightPoly A.lowOrder A.highOrder t' * axisFactor x' * A.polar.evalHalf t' x') t x := by
  unfold reducedComps
  rw [if_neg h]
  rfl

theorem reducedComps_of_typeTwo (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (h : κ.label.1 = 0) (t x : ℝ) :
    reducedComps P κ A t x = compsTwo P κ.phaseIndex (fun t' => weightPoly 1 A.highOrder t')
      (fun t' x' => streamValue P A t' x') (fun t' x' => A.swirl.evalHalf t' x') t x := by
  unfold reducedComps
  rw [if_pos h]
  rfl

theorem compsOne_of_reflected (P : ShapeParams) (j : ℤ) (k : ℂ) (ur uθ : ℝ → ℝ → ℂ) (t x : ℝ) :
    compsOne P j (-k) (fun t' x' => ur t' (-x')) (fun t' x' => -uθ t' (-x')) t (-x) 0 = compsOne P j k ur uθ t x 0 ∧
    compsOne P j (-k) (fun t' x' => ur t' (-x')) (fun t' x' => -uθ t' (-x')) t (-x) 1 =
      -compsOne P j k ur uθ t x 1 ∧
    compsOne P j (-k) (fun t' x' => ur t' (-x')) (fun t' x' => -uθ t' (-x')) t (-x) 2 =
      -compsOne P j k ur uθ t x 2 := by
  have e : (fun t' x' => polarFactor x' * -uθ t' (-x')) =
      fun t' x' => -(polarFactor (-x') * uθ t' (-x')) := by
    funext t' x'
    rw [polarFactor_of_neg]
    ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [compsOne, Matrix.cons_val_zero, neg_neg]
  · simp only [compsOne, Matrix.cons_val_one, Matrix.cons_val_zero, neg_neg]
  · simp only [compsOne, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [e, heightDeriv_of_reflected_neg (fun t'' x'' => polarFactor x'' * uθ t'' x''), shiftedScale_of_reflected,
      neg_neg, div_neg, neg_mul]

theorem compsTwo_of_odd (P : ShapeParams) (j : ℤ) (p : ℝ → ℂ) (Ψ G : ℝ → ℝ → ℂ)
    (hΨ : ∀ t x, Ψ t (-x) = -Ψ t x) (hG : ∀ t x, G t (-x) = -G t x) (t x : ℝ) :
    compsTwo P j p Ψ G t (-x) 0 = compsTwo P j p Ψ G t x 0 ∧
    compsTwo P j p Ψ G t (-x) 1 = -compsTwo P j p Ψ G t x 1 ∧
    compsTwo P j p Ψ G t (-x) 2 = -compsTwo P j p Ψ G t x 2 := by
  have h0 : ∀ t x, (fun t' x' => polarFactor x' * Ψ t' x') t (-x) = -(fun t' x' => polarFactor x' * Ψ t' x') t x := by
    intro t x
    simp only [polarFactor_of_neg, hΨ]
    ring
  have h1 : ∀ t x, (fun t' x' => p t' * Ψ t' x') t (-x) = -(fun t' x' => p t' * Ψ t' x') t x := by
    intro t x
    simp only [hΨ]
    ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [compsTwo, Matrix.cons_val_zero]
    rw [heightDeriv_of_odd _ h0]
  · simp only [compsTwo, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [shiftedScale_of_odd P j _ h1, hΨ]
    ring
  · simp only [compsTwo, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [hG]
    ring

theorem keyVector_of_flipped_comps (P : ShapeParams) (κ κ' : FieldKey) (A A' : KeyAmp) (σ : ℝ) (y : Space)
    (hph : keyPhase P κ' σ (flipPoint y) = keyPhase P κ σ y)
    (hc : ∀ t x, reducedComps P κ' A' t (-x) 0 = reducedComps P κ A t x 0 ∧
      reducedComps P κ' A' t (-x) 1 = -reducedComps P κ A t x 1 ∧
      reducedComps P κ' A' t (-x) 2 = -reducedComps P κ A t x 2) :
    keyVector P κ' A' σ (flipPoint y) = flipVec (keyVector P κ A σ y) := by
  obtain ⟨c0, c1, c2⟩ := hc (chartCoord P y) (heightRatio y)
  obtain ⟨e0, e1, e2⟩ := flipPoint_coords y
  have hn := norm_of_flipPoint y
  have hh := heightRatio_of_flipPoint y
  have hc' := chartCoord_of_flipPoint P y
  funext i
  fin_cases i <;>
    simp only [keyVector, flipVec, hph, hc', hh, c0, c1, c2, radialVec, polarVecQ, azimVecQ, qOf, hn, e0, e1, e2,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons] <;>
    push_cast <;> ring

theorem flipKey_of_typeTwo (κ : FieldKey) (h : κ.label.1 = 0) : κ.flipKey = κ := by
  obtain ⟨⟨a, b⟩, j⟩ := κ
  simp only at h
  subst h
  simp [FieldKey.flipKey, labelFlip]

theorem evalHalf_of_agreeing {S T : Spline} (h : SplineAgrees S T) (hm : IsFullMesh S.mesh) (t x : ℝ) :
    S.evalHalf t x = T.evalHalf t x := by
  have ht := cellIndex_lt _ (breaks_two_le_length _ (by norm_num) hm.t_first hm.t_last) t
  have hx := cellIndex_lt _ (breaks_two_le_length _ (by norm_num) hm.x_first hm.x_last) x
  unfold CellCert.GivenFields.Spline.evalHalf
  rw [h.piece_eq _ ht _ hx, h.mesh_eq]

theorem evalHalf_of_reflect_agree {a b : ℕ} (odd : Bool) {S T : Spline} (h : SplineAgrees T (reflectSpline odd S))
    (hT : IsFullMesh T.mesh) (hS : IsJoinedSpline a b S) (t x : ℝ) :
    T.evalHalf t x = (if odd then -1 else 1) * S.evalHalf t (-x) := by
  rw [evalHalf_of_agreeing h hT, evalHalf_reflect a b odd S hS]

end Internal

open Internal in
theorem keyFlip_holds : KeyFlip := by
  intro P D κ σ y hD hκ
  apply keyVector_of_flipped_comps P κ κ.flipKey _ _ σ y (keyPhase_of_flipKey P κ σ y)
  intro t x
  by_cases h : κ.label.1 = 0
  · have hf := flipKey_of_typeTwo κ h
    rw [hf]
    have hs : ∀ t x, (D.amp κ).stream.evalHalf t (-x) = -(D.amp κ).stream.evalHalf t x := by
      intro t x
      rw [evalHalf_of_reflect_agree true (hD.stream_odd κ hκ h) (hD.stream_class κ hκ h).mesh
        (hD.stream_class κ hκ h), neg_neg]
      simp
    have hw : ∀ t x, (D.amp κ).swirl.evalHalf t (-x) = -(D.amp κ).swirl.evalHalf t x := by
      intro t x
      rw [evalHalf_of_reflect_agree true (hD.swirl_odd κ hκ h) (hD.swirl_class κ hκ h).mesh
        (hD.swirl_class κ hκ h), neg_neg]
      simp
    have hΨ : ∀ t x, streamValue P (D.amp κ) t (-x) = -streamValue P (D.amp κ) t x := by
      intro t x
      unfold streamValue
      rw [hs]
      push_cast
      ring
    rw [reducedComps_of_typeTwo P κ _ h, reducedComps_of_typeTwo P κ _ h]
    exact compsTwo_of_odd P _ _ _ _ hΨ hw t x
  · have hκ' : κ.flipKey ∈ D.keys := (hD.keys_flip κ).1 hκ
    have h' : κ.flipKey.label.1 ≠ 0 := by
      simpa [FieldKey.flipKey, labelFlip] using h
    have hr : ∀ t x, (D.amp κ.flipKey).radial.evalHalf t x = (D.amp κ).radial.evalHalf t (-x) := by
      intro t x
      rw [evalHalf_of_reflect_agree false (hD.flip_radial κ hκ h) (hD.radial_class _ hκ' h').mesh
        (hD.radial_class κ hκ h)]
      simp
    have hp : ∀ t x, (D.amp κ.flipKey).polar.evalHalf t x = -(D.amp κ).polar.evalHalf t (-x) := by
      intro t x
      rw [evalHalf_of_reflect_agree true (hD.flip_polar κ hκ h) (hD.polar_class _ hκ' h').mesh
        (hD.polar_class κ hκ h)]
      simp
    obtain ⟨hlo, hhi⟩ := hD.flip_orders κ hκ
    have hk : (labelAzimuth P.azimuthOrder κ.flipKey.label : ℂ) = -(labelAzimuth P.azimuthOrder κ.label : ℂ) := by
      simp only [FieldKey.flipKey, labelAzimuth, labelFlip]
      push_cast
      ring
    have eur : (fun t' x' => weightPoly (D.amp κ.flipKey).lowOrder (D.amp κ.flipKey).highOrder t' * axisFactor x' *
        (D.amp κ.flipKey).radial.evalHalf t' x') = fun t' x' =>
          (fun t'' x'' => weightPoly (D.amp κ).lowOrder (D.amp κ).highOrder t'' * axisFactor x'' *
            (D.amp κ).radial.evalHalf t'' x'') t' (-x') := by
      funext t' x'
      dsimp only
      rw [hlo, hhi, hr, axisFactor_of_neg]
    have euθ : (fun t' x' => weightPoly (D.amp κ.flipKey).lowOrder (D.amp κ.flipKey).highOrder t' * axisFactor x' *
        (D.amp κ.flipKey).polar.evalHalf t' x') = fun t' x' =>
          -(fun t'' x'' => weightPoly (D.amp κ).lowOrder (D.amp κ).highOrder t'' * axisFactor x'' *
            (D.amp κ).polar.evalHalf t'' x'') t' (-x') := by
      funext t' x'
      dsimp only
      rw [hlo, hhi, hp, axisFactor_of_neg]
      ring
    rw [reducedComps_of_typeOne P _ _ h', reducedComps_of_typeOne P κ _ h, hk, eur, euθ]
    exact compsOne_of_reflected P κ.phaseIndex (labelAzimuth P.azimuthOrder κ.label : ℂ)
      (fun t'' x'' => weightPoly (D.amp κ).lowOrder (D.amp κ).highOrder t'' * axisFactor x'' *
        (D.amp κ).radial.evalHalf t'' x'')
      (fun t'' x'' => weightPoly (D.amp κ).lowOrder (D.amp κ).highOrder t'' * axisFactor x'' *
        (D.amp κ).polar.evalHalf t'' x'') t x

end GivenShape

end CertCell

end Breakdown
