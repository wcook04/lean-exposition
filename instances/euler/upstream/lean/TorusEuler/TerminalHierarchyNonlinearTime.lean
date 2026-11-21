import TorusEuler.TerminalHierarchyLinearTime
import TorusEuler.HierarchyTwistedSlowSourceBounds
import TorusEuler.HierarchyPhysicalSourceTerms

/-! Quantitative slow and fast advection in the factorial time-jet norms. -/

open ContinuousLinearMap Finset Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section
set_option maxHeartbeats 2400000

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)
local notation "Q(" n ")" => hierarchyQuadraticConstant (Fin 4) n
local notation "scalarAction" => (lsmul ℝ ℝ : ℝ →L[ℝ] Vec3 →L[ℝ] Vec3)

private def terminalProfileEval (x : HierarchyProfilePoint) : VP →ₗ[ℝ] Vec3 where
  toFun f := f.val.val.val x
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

private theorem sum_coordinateDirection_terminal (v : Vec3) :
    ∑ i : Fin 3, v i • coordinateDirection i = v := by
  apply PiLp.ext
  intro j
  let eval : Vec3 →L[ℝ] ℝ := EuclideanSpace.proj j
  change eval (∑ i, v i • coordinateDirection i) = v j
  rw [map_sum]
  simp [eval, coordinateDirection, EuclideanSpace.single, PiLp.single_apply]

private theorem scaledProfileDerivative_label_apply (hT : 0 < T) (ℓ h : ℝ)
    (i : Fin 3) (g : VP) {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (scaledProfileDerivative hT ℓ h i.castSucc g).val.val.val (t, a, s) =
      ℓ • fderiv ℝ (fun b => g.val.val.val (t, b, s)) a (coordinateDirection i) := by
  rw [scaledProfileDerivative_apply hT ℓ h i.castSucc g ht (a,s), phaseDirectionalDerivative]
  simp only [hierarchyMixedDirection, Fin.lastCases_castSucc, phaseCoordinateDirection, map_smul]
  congr 1
  have hs := (HierarchySmoothProfile.contDiff_labelPhase_slice g.val.val ht).differentiable
    (by simp) (a, s)
  rw [(hasFDerivAt_profile_partials hs).fderiv]
  simp [coprod_apply]

/-- The actual slow advection is the sum of the scaled coframe rows applied
to the advector, each times one scaled label derivative. -/
theorem labelAdv_eq_sum_scaledProducts (hT : 0 < T) (G M : MP) (κ z g : VP)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) :
    (twistedHierarchyOperators hT G M κ).labelAdv z g = ∑ i : Fin 3,
      pointwiseBilinear scalarAction (applyField (scaledCoframeRowProfile ℓ G i) z)
        (scaledProfileDerivative hT ℓ h i.castSucc g) := by
  apply HierarchyTwistedProfile.ext
  rintro ⟨t,a,s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  let v := G.val.val.val (t,a,s) (z.val.val.val (t,a,s))
  let ev := terminalProfileEval (T := T) (k := k) (t,a,s)
  change _ = ev (∑ i : Fin 3, pointwiseBilinear scalarAction
    (applyField (scaledCoframeRowProfile ℓ G i) z) (scaledProfileDerivative hT ℓ h i.castSucc g))
  rw [map_sum, labelAdv_apply_label_fderiv hT G M κ z g ht a s]
  change fderiv ℝ (fun b => g.val.val.val (t,b,s)) a v = _
  conv_lhs => rw [← sum_coordinateDirection_terminal v, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change _ = (pointwiseBilinear scalarAction
    (applyField (scaledCoframeRowProfile ℓ G i) z)
    (scaledProfileDerivative hT ℓ h i.castSucc g)).val.val.val (t,a,s)
  rw [map_smul, pointwiseBilinear_eval _ _ _ hx, applyField_eval _ _ hx,
    scaledCoframeRowProfile_apply _ _ _ hx, scaledProfileDerivative_label_apply hT ℓ h i g ht a s]
  let d := fderiv ℝ (fun b => g.val.val.val (t,b,s)) a (coordinateDirection i)
  change v i • d = (ℓ⁻¹ * v i) • (ℓ • d)
  rw [smul_smul, mul_comm (ℓ⁻¹ * v i), ← mul_assoc, mul_inv_cancel₀ hℓ, one_mul]

/-- The scaled fast covector and derivative recover the actual fast advection. -/
theorem phaseAdv_eq_scaledProduct (hT : 0 < T) (G M : MP) (κ z g : VP)
    (ℓ h : ℝ) (hh : h ≠ 0) :
    (twistedHierarchyOperators hT G M κ).phaseAdv z g =
      pointwiseBilinear scalarAction (applyField (scaledPhaseCoefficientProfile h κ) z)
        (scaledProfileDerivative hT ℓ h (Fin.last 3) g) := by
  apply HierarchyTwistedProfile.ext
  rintro ⟨t,x⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  rw [phaseAdv_apply_slice_fderiv hT G M κ z g ht x, pointwiseBilinear_eval _ _ _ hx,
    applyField_eval _ _ hx, scaledPhaseCoefficientProfile_apply h κ ht x,
    scaledProfileDerivative_apply hT ℓ h (Fin.last 3) g ht x]
  simp only [phaseDirectionalDerivative, hierarchyMixedDirection, Fin.lastCases_last,
    phaseCoordinateDirection, map_smul]
  let d := fderiv ℝ (fun y => g.val.val.val (t,y)) x (0,1)
  change ⟪κ.val.val.val (t,x), z.val.val.val (t,x)⟫_ℝ • d =
    h • ((h⁻¹ * ⟪κ.val.val.val (t,x), z.val.val.val (t,x)⟫_ℝ) • d)
  rw [smul_smul, ← mul_assoc, mul_inv_cancel₀ hh, one_mul]

private theorem scaledLabelDerivative_eq_scaledProfileDerivative (hT : 0 < T) (ℓ h : ℝ)
    (i : Fin 3) (g : VP) :
    scaledLabelDerivativeProfile hT ℓ h i g = scaledProfileDerivative hT ℓ h i.castSucc g := by
  apply HierarchyTwistedProfile.ext
  rintro ⟨t,x⟩ hx
  exact (scaledLabelDerivativeProfile_apply hT ℓ h i g hx.1 x).trans
    (scaledProfileDerivative_apply hT ℓ h i.castSucc g hx.1 x).symm

theorem slowLabelDivergenceProduct_eq_scaledProducts (hT : 0 < T) (G : MP) (V Y : VP)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) :
    slowLabelDivergenceProduct hT G V Y = pointwiseBilinear scalarAction
      (∑ i : Fin 3, applyField (scaledCoframeRowProfile ℓ G i)
        (scaledProfileDerivative hT ℓ h i.castSucc V)) Y := by
  have he : slowLabelDivergenceProduct hT G V Y =
      pointwiseBilinear scalarAction (slowLabelDivergence hT G V) Y := by
    apply HierarchyTwistedProfile.ext
    intro x hx
    rw [slowLabelDivergenceProduct_apply hT G V Y hx, pointwiseBilinear_eval _ _ _ hx]
    rfl
  rw [he, slowLabelDivergence_eq_sum_apply_scaledRows hT ℓ h hℓ]
  simp only [scaledLabelDerivative_eq_scaledProfileDerivative]

private theorem quadratic_nonneg (n : ℕ) : 0 ≤ Q(n) := by
  unfold hierarchyQuadraticConstant
  positivity

private theorem productCost_le {E F G : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {B : E →L[ℝ] F →L[ℝ] G}
    (hB : ‖B‖ ≤ 1) (n : ℕ) : terminalHierarchyProductCost B n ≤ Q(n) := by
  unfold terminalHierarchyProductCost hierarchyQuadraticConstant
  gcongr
  linarith only [hB]

private theorem rowApplication_norm_le :
    ‖(ContinuousLinearMap.apply ℝ ℝ (E := Vec3)).flip‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro L
  rw [one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro z
  exact L.le_opNorm z

private theorem timeJetSeminorm_applyRow_le (hT : 0 < T) (q : ℕ) (ℓ h : ℝ) (n : ℕ)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τ : ℝ → ℝ) {C : ℝ} (hτ : ∀ t ∈ A, ‖τ t‖ ≤ C)
    (R : HierarchyTwistedProfile T k (Vec3 →L[ℝ] ℝ)) (z : VP) :
    timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h n hT hA τ hτ) (applyField R z) ≤
      Q(n) * (timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT) R *
        timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h n hT hA τ hτ) z) :=
  (timeJetSeminorm_applyField_weighted_le hT q False ℓ h n hA τ hτ R z).trans
    (mul_le_mul_of_nonneg_right (productCost_le rowApplication_norm_le n)
      (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))

private theorem timeJetSeminorm_smulProduct_le (hT : 0 < T) (q : ℕ) (ℓ h : ℝ) (n : ℕ)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τZ τY τP : ℝ → ℝ) {CV CY CP : ℝ}
    (hZ : ∀ t ∈ A, ‖τZ t‖ ≤ CV) (hY : ∀ t ∈ A, ‖τY t‖ ≤ CY)
    (hP : ∀ t ∈ A, ‖τP t‖ ≤ CP) (hweight : ∀ t ∈ A, τP t = τZ t * τY t)
    (f : SP) (g : VP) :
    timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h n hT hA τP hP)
      (pointwiseBilinear scalarAction f g) ≤
      Q(n) * (timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h n hT hA τZ hZ) f *
        timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h n hT hA τY hY) g) := by
  refine (timeJetSeminorm_boundedWeight_bilinear_le scalarAction False ℓ h n q hT hA τZ τY τP
    hZ hY hP hweight f g).trans ?_
  have hB : ‖scalarAction‖ ≤ 1 := opNorm_lsmul_le
  exact mul_le_mul_of_nonneg_right (productCost_le hB n)
    (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))

private theorem timeJetSeminorm_scaledAdvectionProduct_le (hT : 0 < T) (q : ℕ) (ℓ h : ℝ)
    (i : Fin 4) (n : ℕ) {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τZ τY τP : ℝ → ℝ) {CV CY CP : ℝ}
    (hZ : ∀ t ∈ A, ‖τZ t‖ ≤ CV) (hY : ∀ t ∈ A, ‖τY t‖ ≤ CY)
    (hP : ∀ t ∈ A, ‖τP t‖ ≤ CP) (hweight : ∀ t ∈ A, τP t = τZ t * τY t)
    (R : HierarchyTwistedProfile T k (Vec3 →L[ℝ] ℝ)) (z y : VP) :
    timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h n hT hA τP hP)
      (pointwiseBilinear scalarAction (applyField R z) (scaledProfileDerivative hT ℓ h i y)) ≤
      Q(n) ^ 2 * timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT) R *
        timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h n hT hA τZ hZ) z *
        timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h (n+1) hT hA τY hY) y := by
  let Z : Seminorm ℝ VP := timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h n hT hA τZ hZ)
  let Y : Seminorm ℝ VP := timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h (n+1) hT hA τY hY)
  let L := timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT) R
  have ha := timeJetSeminorm_applyRow_le hT q ℓ h n hA τZ hZ R z
  have hd := timeJetSeminorm_scaledProfileDerivative_le False hT q ℓ h i n y hA τY hY
  refine (timeJetSeminorm_smulProduct_le hT q ℓ h n hA τZ τY τP hZ hY hP hweight
    (applyField R z) (scaledProfileDerivative hT ℓ h i y)).trans ?_
  calc
    _ ≤ Q(n) * ((Q(n) * (L * Z z)) * Y y) :=
      mul_le_mul_of_nonneg_left (mul_le_mul ha hd (apply_nonneg _ _)
        (mul_nonneg (quadratic_nonneg n) (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))))
        (quadratic_nonneg n)
    _ = _ := by ring

/-- Slow advection in the mixed norm, with the two input weights split
exactly as in the spatial estimate. -/
theorem timeJetSeminorm_labelAdv_split_le (hT : 0 < T) (q : ℕ) (G M : MP) (κ z g : VP)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) {L : ℝ}
    (hG : ∀ i : Fin 3, timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT)
      (scaledCoframeRowProfile ℓ G i) ≤ L)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τZ τY τP : ℝ → ℝ) {CV CY CP : ℝ}
    (hZ : ∀ t ∈ A, ‖τZ t‖ ≤ CV) (hY : ∀ t ∈ A, ‖τY t‖ ≤ CY)
    (hP : ∀ t ∈ A, ‖τP t‖ ≤ CP) (hweight : ∀ t ∈ A, τP t = τZ t * τY t) :
    timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h n hT hA τP hP)
      ((twistedHierarchyOperators hT G M κ).labelAdv z g) ≤
      3 * Q(n)^2 * L *
        timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h n hT hA τZ hZ) z *
        timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h (n+1) hT hA τY hY) g := by
  let S : Seminorm ℝ VP := timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h n hT hA τP hP)
  let Z : Seminorm ℝ VP := timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h n hT hA τZ hZ)
  let Y : Seminorm ℝ VP := timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h (n+1) hT hA τY hY)
  rw [labelAdv_eq_sum_scaledProducts hT G M κ z g ℓ h hℓ]
  refine (Finset.le_sum_of_subadditive S (by simp) (map_add_le_add S) _ _).trans ?_
  calc
    _ ≤ ∑ _ : Fin 3, Q(n) ^ 2 * L * Z z * Y g := by
      refine Finset.sum_le_sum fun i _ => ?_
      exact (timeJetSeminorm_scaledAdvectionProduct_le hT q ℓ h i.castSucc n hA τZ τY τP
        hZ hY hP hweight (scaledCoframeRowProfile ℓ G i) z g).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hG i) (sq_nonneg _)) (apply_nonneg _ _)) (apply_nonneg _ _))
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      change 3 * (Q(n)^2 * L * Z z * Y g) = 3 * Q(n)^2 * L * Z z * Y g
      ring

/-- Fast advection in the mixed norm. The factor (h^{-1}) remains in the
measured covector, so the old frequency power is unchanged. -/
theorem timeJetSeminorm_phaseAdv_split_le (hT : 0 < T) (q : ℕ) (G M : MP) (κ z g : VP)
    (ℓ h : ℝ) (hh : h ≠ 0) (n : ℕ)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τZ τY τP : ℝ → ℝ) {CV CY CP : ℝ}
    (hZ : ∀ t ∈ A, ‖τZ t‖ ≤ CV) (hY : ∀ t ∈ A, ‖τY t‖ ≤ CY)
    (hP : ∀ t ∈ A, ‖τP t‖ ≤ CP) (hweight : ∀ t ∈ A, τP t = τZ t * τY t) :
    timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h n hT hA τP hP)
      ((twistedHierarchyOperators hT G M κ).phaseAdv z g) ≤
      Q(n)^2 * timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT)
        (scaledPhaseCoefficientProfile h κ) *
        timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h n hT hA τZ hZ) z *
        timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h (n+1) hT hA τY hY) g := by
  rw [phaseAdv_eq_scaledProduct hT G M κ z g ℓ h hh]
  exact timeJetSeminorm_scaledAdvectionProduct_le hT q ℓ h (Fin.last 3) n hA τZ τY τP
    hZ hY hP hweight (scaledPhaseCoefficientProfile h κ) z g

/-- The slow divergence spends the extra label order on its first input. -/
theorem timeJetSeminorm_slowLabelDivergenceProduct_split_le (hT : 0 < T) (q : ℕ)
    (G : MP) (V Y : VP) (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) {L : ℝ}
    (hG : ∀ i : Fin 3, timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT)
      (scaledCoframeRowProfile ℓ G i) ≤ L)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (τV τY τP : ℝ → ℝ) {CV CY CP : ℝ}
    (hV : ∀ t ∈ A, ‖τV t‖ ≤ CV) (hY : ∀ t ∈ A, ‖τY t‖ ≤ CY)
    (hP : ∀ t ∈ A, ‖τP t‖ ≤ CP) (hweight : ∀ t ∈ A, τP t = τV t * τY t) :
    timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h n hT hA τP hP)
      (slowLabelDivergenceProduct hT G V Y) ≤
      3 * Q(n)^2 * L *
        timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h (n+1) hT hA τV hV) V *
        timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h n hT hA τY hY) Y := by
  let U : Seminorm ℝ (HierarchyTwistedProfile T k (Vec3 →L[ℝ] ℝ)) :=
    timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT)
  let Vn : Seminorm ℝ VP := timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h n hT hA τV hV)
  let Vn₁ : Seminorm ℝ VP := timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h (n+1) hT hA τV hV)
  let S : Seminorm ℝ SP := timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h n hT hA τV hV)
  let Yn : Seminorm ℝ VP := timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h n hT hA τY hY)
  let R (i : Fin 3) := scaledCoframeRowProfile ℓ G i
  let D (i : Fin 3) := scaledProfileDerivative hT ℓ h i.castSucc V
  have hSum : S (∑ i : Fin 3, applyField (R i) (D i)) ≤ 3 * Q(n) * L * Vn₁ V := by
    refine (Finset.le_sum_of_subadditive S (by simp) (map_add_le_add S) _ _).trans ?_
    calc
      _ ≤ ∑ _ : Fin 3, Q(n) * L * Vn₁ V := by
        refine Finset.sum_le_sum fun i _ => (timeJetSeminorm_applyRow_le hT q ℓ h n hA τV hV
          (R i) (D i)).trans ?_
        have hd : Vn (D i) ≤ Vn₁ V :=
          timeJetSeminorm_scaledProfileDerivative_le False hT q ℓ h i.castSucc n V hA τV hV
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (hG i) hd (apply_nonneg _ _)
          ((apply_nonneg U (R i)).trans (hG i))) (quadratic_nonneg n)
      _ = _ := by simp [mul_assoc]
  rw [slowLabelDivergenceProduct_eq_scaledProducts hT G V Y ℓ h hℓ]
  refine (timeJetSeminorm_smulProduct_le hT q ℓ h n hA τV τY τP hV hY hP hweight
    (∑ i : Fin 3, applyField (R i) (D i)) Y).trans ?_
  calc
    _ ≤ Q(n) * ((3 * Q(n) * L * Vn₁ V) * Yn Y) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hSum (apply_nonneg _ _))
        (quadratic_nonneg n)
    _ = _ := by ring


private theorem timeJetSeminorm_restrict_unweighted_le {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (hT : 0 < T) (q : ℕ) (ℓ h : ℝ) (n : ℕ)
    {A : Set ℝ} (hA : A ⊆ Icc 0 T) (f : HierarchyTwistedProfile T k E) :
    timeJetSeminorm hT q (boundedWeightSeminorm False ℓ h n hT hA (fun _ => 1)
      (B := 1) (by simp)) f ≤ timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT) f :=
  timeJetSeminorm_mono_seminorm hT q (Seminorm.le_def.mpr (fun v =>
    boundedWeightSeminorm_mono_time False ℓ h n hT hA (Subset.rfl : Icc 0 T ⊆ Icc 0 T)
      (fun _ => 1) (C := 1) (by simp) v)) f

private theorem timeJetSeminorm_unweighted_mono_order {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (hT : 0 < T) (q : ℕ) (ℓ h : ℝ)
    {m n : ℕ} (hmn : m ≤ n) (f : HierarchyTwistedProfile T k E) :
    timeJetSeminorm hT q (unweightedSeminorm False ℓ h m hT) f ≤
      timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT) f :=
  timeJetSeminorm_mono_seminorm hT q
    (Seminorm.le_def.mpr (unweightedSeminorm_mono_order False ℓ h hmn hT)) f

/-- Full-slab slow advection in factorial time norms. -/
theorem timeJetSeminorm_unweighted_labelAdv_le (hT : 0 < T) (q : ℕ) (G M : MP) (κ z g : VP)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) {L : ℝ}
    (hG : ∀ i : Fin 3, timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT)
      (scaledCoframeRowProfile ℓ G i) ≤ L) :
    timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT)
      ((twistedHierarchyOperators hT G M κ).labelAdv z g) ≤
      3 * Q(n)^2 * L * timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT) z *
        timeJetSeminorm hT q (unweightedSeminorm False ℓ h (n+1) hT) g :=
  timeJetSeminorm_labelAdv_split_le hT q G M κ z g ℓ h hℓ n hG (Subset.rfl : Icc 0 T ⊆ Icc 0 T)
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (CV := 1) (CY := 1) (CP := 1)
    (by simp) (by simp) (by simp) (by simp)

/-- Full-slab fast advection in factorial time norms. -/
theorem timeJetSeminorm_unweighted_phaseAdv_le (hT : 0 < T) (q : ℕ) (G M : MP) (κ z g : VP)
    (ℓ h : ℝ) (hh : h ≠ 0) (n : ℕ) :
    timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT)
      ((twistedHierarchyOperators hT G M κ).phaseAdv z g) ≤
      Q(n)^2 * timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT)
        (scaledPhaseCoefficientProfile h κ) *
        timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT) z *
        timeJetSeminorm hT q (unweightedSeminorm False ℓ h (n+1) hT) g :=
  timeJetSeminorm_phaseAdv_split_le hT q G M κ z g ℓ h hh n (Subset.rfl : Icc 0 T ⊆ Icc 0 T)
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (CV := 1) (CY := 1) (CP := 1)
    (by simp) (by simp) (by simp) (by simp)

/-- Full-slab slow divergence in factorial time norms. -/
theorem timeJetSeminorm_unweighted_slowLabelDivergenceProduct_le (hT : 0 < T) (q : ℕ)
    (G : MP) (V Y : VP) (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) {L : ℝ}
    (hG : ∀ i : Fin 3, timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT)
      (scaledCoframeRowProfile ℓ G i) ≤ L) :
    timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT)
      (slowLabelDivergenceProduct hT G V Y) ≤
      3 * Q(n)^2 * L *
        timeJetSeminorm hT q (unweightedSeminorm False ℓ h (n+1) hT) V *
        timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT) Y :=
  timeJetSeminorm_slowLabelDivergenceProduct_split_le hT q G V Y ℓ h hℓ n hG
    (Subset.rfl : Icc 0 T ⊆ Icc 0 T) (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (CV := 1) (CY := 1) (CP := 1) (by simp) (by simp) (by simp) (by simp)

section Active

variable {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
  (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)

local notation "Wt(" hT "," q "," ℓ "," h "," n ")" =>
  timeJetSeminorm hT q (amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos)
local notation "Ut(" hT "," q "," ℓ "," h "," n ")" =>
  timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT)

private theorem timeJetSeminorm_amplitude_mono_order (hT : 0 < T) (q : ℕ) (ℓ h : ℝ)
    {m n : ℕ} (hmn : m ≤ n) (f : VP) :
    Wt(hT,q,ℓ,h,m) f ≤ Wt(hT,q,ℓ,h,n) f :=
  timeJetSeminorm_mono_seminorm hT q
    (Seminorm.le_def.mpr (amplitudeSeminorm_mono_order False ℓ h hmn hT ht₀ htT γ hγ hpos)) f

private theorem timeJetSeminorm_amplitude_labelAdv_left_le (hT : 0 < T) (q : ℕ) (G M : MP) (κ z g : VP)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) {L : ℝ}
    (hG : ∀ i : Fin 3, Ut(hT,q,ℓ,h,n) (scaledCoframeRowProfile ℓ G i) ≤ L) :
    Wt(hT,q,ℓ,h,n) ((twistedHierarchyOperators hT G M κ).labelAdv z g) ≤
      3 * Q(n)^2 * L * Wt(hT,q,ℓ,h,n) z * Ut(hT,q,ℓ,h,(n+1)) g := by
  have hτ := (inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hpos).choose_spec
  have hb := timeJetSeminorm_labelAdv_split_le hT q G M κ z g ℓ h hℓ n hG (Icc_subset_Icc_left ht₀)
    (fun t => (γ t)⁻¹) (fun _ => 1) (fun t => (γ t)⁻¹) (CY := 1)
    hτ (by simp) hτ (by simp)
  exact hb.trans (mul_le_mul_of_nonneg_left
    (timeJetSeminorm_restrict_unweighted_le hT q ℓ h (n+1) (Icc_subset_Icc_left ht₀) g)
    (mul_nonneg (mul_nonneg (by positivity)
      ((apply_nonneg _ _).trans (hG 0))) (apply_nonneg _ _)))

private theorem timeJetSeminorm_amplitude_labelAdv_right_le (hT : 0 < T) (q : ℕ) (G M : MP) (κ z g : VP)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) {L : ℝ}
    (hG : ∀ i : Fin 3, Ut(hT,q,ℓ,h,n) (scaledCoframeRowProfile ℓ G i) ≤ L) :
    Wt(hT,q,ℓ,h,n) ((twistedHierarchyOperators hT G M κ).labelAdv z g) ≤
      3 * Q(n)^2 * L * Ut(hT,q,ℓ,h,n) z * Wt(hT,q,ℓ,h,(n+1)) g := by
  have hτ := (inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hpos).choose_spec
  have hb := timeJetSeminorm_labelAdv_split_le hT q G M κ z g ℓ h hℓ n hG (Icc_subset_Icc_left ht₀)
    (fun _ => 1) (fun t => (γ t)⁻¹) (fun t => (γ t)⁻¹) (CV := 1)
    (by simp) hτ hτ (by simp)
  exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (timeJetSeminorm_restrict_unweighted_le hT q ℓ h n (Icc_subset_Icc_left ht₀) z)
    (mul_nonneg (by positivity) ((apply_nonneg _ _).trans (hG 0)))) (apply_nonneg _ _))

/-- The one amplitude weight of the mixed fast source is on the differentiated profile. -/
theorem timeJetSeminorm_amplitude_phaseAdv_le (hT : 0 < T) (q : ℕ) (G M : MP) (κ z g : VP)
    (ℓ h : ℝ) (hh : h ≠ 0) (n : ℕ) :
    Wt(hT,q,ℓ,h,n) ((twistedHierarchyOperators hT G M κ).phaseAdv z g) ≤
      Q(n)^2 * Ut(hT,q,ℓ,h,n) (scaledPhaseCoefficientProfile h κ) *
        Ut(hT,q,ℓ,h,n) z * Wt(hT,q,ℓ,h,(n+1)) g := by
  have hτ := (inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hpos).choose_spec
  have hb := timeJetSeminorm_phaseAdv_split_le hT q G M κ z g ℓ h hh n (Icc_subset_Icc_left ht₀)
    (fun _ => 1) (fun t => (γ t)⁻¹) (fun t => (γ t)⁻¹) (CV := 1)
    (by simp) hτ hτ (by simp)
  exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (timeJetSeminorm_restrict_unweighted_le hT q ℓ h n (Icc_subset_Icc_left ht₀) z)
    (mul_nonneg (sq_nonneg _) (apply_nonneg _ _))) (apply_nonneg _ _))


/-- A phase-centered mixed term is bounded by twice the original term. -/
theorem timeJetSeminorm_amplitude_centered_le (hT : 0 < T) (q : ℕ) (G M : MP) (κ f : VP)
    (ℓ h : ℝ) (n : ℕ) :
    Wt(hT,q,ℓ,h,n) (f - (twistedHierarchyOperators hT G M κ).average f) ≤
      2 * Wt(hT,q,ℓ,h,n) f := by
  let N : Seminorm ℝ VP := Wt(hT,q,ℓ,h,n)
  have hτ := (inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hpos).choose_spec
  have hA : N ((twistedHierarchyOperators hT G M κ).average f) ≤ N f :=
    timeJetSeminorm_average_le hT q ℓ h n G M κ f (Icc_subset_Icc_left ht₀)
      (fun t => (γ t)⁻¹) hτ
  rw [two_mul]
  exact (map_sub_le_add N _ _).trans (add_le_add le_rfl hA)

/-- Split the centered slow source before assigning the amplitude weight.
The mean–mean term cancels, and the two measured factors consume order n+1. -/
theorem timeJetSeminorm_centered_labelProduct_le (hT : 0 < T) (q : ℕ) (G M : MP) (κ : VP)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) {L : ℝ}
    (hG : ∀ i : Fin 3, Ut(hT,q,ℓ,h,n) (scaledCoframeRowProfile ℓ G i) ≤ L)
    (u : HierarchyProfiles VP SP) (i j : ℕ)
    (hγle : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hzero : ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, (u.Y j).val.val.val (t, x) = 0)
    (hmean : let A := twistedHierarchyOperators hT G M κ
      A.average (A.labelAdv (u.B i) (u.B j)) = A.labelAdv (u.B i) (u.B j)) :
    let A := twistedHierarchyOperators hT G M κ
    let F := A.labelProduct u (i,j)
    Wt(hT,q,ℓ,h,n) (F - A.average F) ≤
      (2 * (3 * Q(n)^2 * L)) *
        ((Wt(hT,q,ℓ,h,(n+1)) (u.Y i) + Ut(hT,q,ℓ,h,(n+1)) (u.B i)) *
          (Wt(hT,q,ℓ,h,(n+1)) (u.Y j) + Ut(hT,q,ℓ,h,(n+1)) (u.B j))) := by
  let A := twistedHierarchyOperators hT G M κ
  let U (m : ℕ) : Seminorm ℝ VP := Ut(hT,q,ℓ,h,m)
  let W (m : ℕ) : Seminorm ℝ VP := Wt(hT,q,ℓ,h,m)
  let K := 3 * Q(n)^2 * L
  let YY := A.labelAdv (u.Y i) (u.Y j)
  let YB := A.labelAdv (u.Y i) (u.B j)
  let BY := A.labelAdv (u.B i) (u.Y j)
  let F := YY + YB + BY
  have hL : 0 ≤ L := (apply_nonneg _ _).trans (hG 0)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hy : U (n+1) (u.Y j) ≤ W (n+1) (u.Y j) :=
    timeJetSeminorm_le_amplitude_of_inactive hT q False ℓ h (n+1) ht₀ htT γ hγ hpos hγle _ hzero
  have hWi : W n (u.Y i) ≤ W (n+1) (u.Y i) :=
    timeJetSeminorm_amplitude_mono_order ht₀ htT γ hγ hpos hT q ℓ h (Nat.le_succ n) _
  have hUi : U n (u.B i) ≤ U (n+1) (u.B i) :=
    timeJetSeminorm_unweighted_mono_order hT q ℓ h (Nat.le_succ n) _
  have hYY : W n YY ≤ K * W (n+1) (u.Y i) * W (n+1) (u.Y j) := by
    refine (timeJetSeminorm_amplitude_labelAdv_left_le ht₀ htT γ hγ hpos hT q G M κ
      (u.Y i) (u.Y j) ℓ h hℓ n hG).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hWi hK) hy (apply_nonneg _ _)
      (mul_nonneg hK (apply_nonneg _ _))
  have hYB : W n YB ≤ K * W (n+1) (u.Y i) * U (n+1) (u.B j) :=
    (timeJetSeminorm_amplitude_labelAdv_left_le ht₀ htT γ hγ hpos hT q G M κ
      (u.Y i) (u.B j) ℓ h hℓ n hG).trans <|
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWi hK) (apply_nonneg _ _)
  have hBY : W n BY ≤ K * U (n+1) (u.B i) * W (n+1) (u.Y j) :=
    (timeJetSeminorm_amplitude_labelAdv_right_le ht₀ htT γ hγ hpos hT q G M κ
      (u.B i) (u.Y j) ℓ h hℓ n hG).trans <|
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hUi hK) (apply_nonneg _ _)
  have hcap : W n F ≤ K * ((W (n+1) (u.Y i) + U (n+1) (u.B i)) *
      (W (n+1) (u.Y j) + U (n+1) (u.B j))) := by
    calc
      _ ≤ W n YY + W n YB + W n BY :=
        (map_add_le_add (W n) _ _).trans (add_le_add (map_add_le_add (W n) _ _) le_rfl)
      _ ≤ _ + K * U (n+1) (u.B i) * U (n+1) (u.B j) := by
        exact (add_le_add (add_le_add hYY hYB) hBY).trans
          (le_add_of_nonneg_right (mul_nonneg (mul_nonneg hK (apply_nonneg _ _)) (apply_nonneg _ _)))
      _ = _ := by ring
  change W n (A.labelProduct u (i,j) - A.average (A.labelProduct u (i,j))) ≤ _
  rw [A.centered_labelProduct_eq u i j hmean]
  change W n (F - A.average F) ≤ _
  exact (timeJetSeminorm_amplitude_centered_le ht₀ htT γ hγ hpos hT q G M κ F ℓ h n).trans
    ((mul_le_mul_of_nonneg_left hcap zero_le_two).trans_eq (by ring))

/-- The fast completion is inactive before launch, so both factors may
be measured in the amplitude norm after centering. -/
theorem timeJetSeminorm_amplitude_centered_phaseAdv_le (hT : 0 < T) (q : ℕ) (G M : MP)
    (κ C Y : VP) (ℓ h : ℝ) (hh : h ≠ 0) (n : ℕ)
    (hγle : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hzero : ∀ t ∈ Icc 0 T, t < t₀ → ∀ x : Vec3 × ℝ, C.val.val.val (t,x) = 0) :
    let A := twistedHierarchyOperators hT G M κ
    let F := A.phaseAdv C Y
    Wt(hT,q,ℓ,h,n) (F - A.average F) ≤
      (2 * Q(n)^2) * Ut(hT,q,ℓ,h,n) (scaledPhaseCoefficientProfile h κ) *
        Wt(hT,q,ℓ,h,n) C * Wt(hT,q,ℓ,h,(n+1)) Y := by
  intro A F
  have hC := timeJetSeminorm_le_amplitude_of_inactive hT q False ℓ h n ht₀ htT γ hγ hpos hγle C hzero
  have hF := (timeJetSeminorm_amplitude_phaseAdv_le ht₀ htT γ hγ hpos
    hT q G M κ C Y ℓ h hh n).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC (by positivity)) (apply_nonneg _ _))
  exact (timeJetSeminorm_amplitude_centered_le ht₀ htT γ hγ hpos
    hT q G M κ F ℓ h n).trans ((mul_le_mul_of_nonneg_left hF zero_le_two).trans_eq (by ring))

end Active

end

end TorusEuler.HierarchyTwistedProfile
