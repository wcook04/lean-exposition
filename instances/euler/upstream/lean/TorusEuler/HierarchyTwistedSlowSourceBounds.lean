import TorusEuler.HierarchyTwistedSourceCancellation
import TorusEuler.HierarchyActualNorms
import TorusEuler.HierarchyLinearRelayBounds

/-! The scaled coframe estimates for the actual slow sources in (5.27) and (5.35). -/

open ContinuousLinearMap Filter Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ
local notation "VPmap" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)
local notation "row" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] ℝ)

/-- A row of the inverse coframe scaled by the inverse label width. -/
def scaledCoframeRowProfile (ℓ : ℝ) (G : VPmap) (i : Fin 3) : row :=
  map (ℓ⁻¹ • compL ℝ Vec3 Vec3 ℝ (EuclideanSpace.proj i)) G

/-- The constant label direction with the label width included. -/
def scaledLabelDerivativeProfile (hT : 0 < T) (ℓ h : ℝ) (i : Fin 3) (V : VP) : VP :=
  map (ContinuousLinearMap.apply ℝ Vec3 (hierarchyMixedDirection ℓ h i.castSucc 0))
    (hierarchyTwistedSliceDerivative hT V)

theorem scaledCoframeRowProfile_apply (ℓ : ℝ) (G : VPmap) (i : Fin 3)
    {x : HierarchyProfilePoint} (hx : x ∈ hierarchyProfileSlab T) (v : Vec3) :
    (scaledCoframeRowProfile ℓ G i).val.val.val x v = ℓ⁻¹ * (G.val.val.val x v) i := by
  simp only [scaledCoframeRowProfile, map_val, HierarchyPeriodicProfile.map_val,
    HierarchySmoothProfile.map_apply _ _ hx, smul_apply, compL_apply, comp_apply, smul_eq_mul]
  rfl

/-- The bundled row measures the same coefficient as the raw mixed-word
advection estimate. -/
theorem weightedSlices_one_scaledCoframeRowProfile {A : Set ℝ} (hA : A ⊆ Icc 0 T)
    (ℓ : ℝ) (G : VPmap) (i : Fin 3) :
    weightedSlices A (fun _ => 1) (scaledCoframeRowProfile ℓ G i) =
      hierarchyScaledCoframeRow ℓ (fun (t : A) x => G.val.val.val (t, x)) i := by
  funext t x
  apply ContinuousLinearMap.ext
  intro v
  change (1 : ℝ) * (scaledCoframeRowProfile ℓ G i).val.val.val (t, x) v =
    ℓ⁻¹ * (G.val.val.val (t, x) v) i
  rw [one_mul, scaledCoframeRowProfile_apply ℓ G i ⟨hA t.property, mem_univ x⟩]

theorem scaledLabelDerivativeProfile_apply (hT : 0 < T) (ℓ h : ℝ) (i : Fin 3) (V : VP)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3 × ℝ) :
    (scaledLabelDerivativeProfile hT ℓ h i V).val.val.val (t, x) =
      phaseDirectionalDerivative (hierarchyMixedDirection ℓ h i.castSucc)
        (fun y => V.val.val.val (t, y)) x := by
  have hx : (t, x) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  simp only [scaledLabelDerivativeProfile, map_val, HierarchyPeriodicProfile.map_val,
    HierarchySmoothProfile.map_apply _ _ hx, hierarchyTwistedSliceDerivative_apply _ _ ht,
    apply_apply, phaseDirectionalDerivative]
  rfl

private theorem applyField_eval_onSlab {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : HierarchyTwistedProfile T k (E →L[ℝ] F))
    (f : HierarchyTwistedProfile T k E) {x : HierarchyProfilePoint} (hx : x ∈ hierarchyProfileSlab T) :
    (applyField L f).val.val.val x = L.val.val.val x (f.val.val.val x) := by
  simp only [applyField_val, HierarchyPeriodicProfile.applyField_val,
    HierarchySmoothProfile.applyField_eval _ _ hx]

/-- In each trace contraction the label width cancels against the inverse width
in the corresponding coframe row. -/
theorem slowLabelDivergence_eq_sum_apply_scaledRows (hT : 0 < T) (ℓ h : ℝ) (hℓ : ℓ ≠ 0)
    (G : VPmap) (V : VP) :
    slowLabelDivergence hT G V = ∑ i : Fin 3,
      applyField (scaledCoframeRowProfile ℓ G i) (scaledLabelDerivativeProfile hT ℓ h i V) := by
  apply HierarchyTwistedProfile.ext
  rintro ⟨t, a, s⟩ hx
  let ev : SP →ₗ[ℝ] ℝ :=
    { toFun := fun f => f.val.val.val (t, a, s)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change _ = ev (∑ i : Fin 3,
    applyField (scaledCoframeRowProfile ℓ G i) (scaledLabelDerivativeProfile hT ℓ h i V))
  rw [map_sum, slowLabelDivergence_apply_labelRows hT G V hx.1 a s]
  refine Finset.sum_congr rfl fun i _ => ?_
  change _ = (applyField _ _).val.val.val (t, a, s)
  rw [applyField_eval_onSlab _ _ hx, scaledCoframeRowProfile_apply _ _ _ hx,
    scaledLabelDerivativeProfile_apply _ _ _ _ _ hx.1]
  let f (x : Vec3 × ℝ) := V.val.val.val (t, x)
  have hdf := (hasFDerivAt_profile_partials
    (((HierarchySmoothProfile.contDiff_labelPhase_slice V.val.val hx.1).differentiable (by simp))
      (a, s))).fderiv
  change (G.val.val.val (t, a, s) (fderiv ℝ (fun b => f (b, s)) a
    (EuclideanSpace.single i 1))) i =
    ℓ⁻¹ * (G.val.val.val (t, a, s) (fderiv ℝ f (a, s)
      (hierarchyMixedDirection ℓ h i.castSucc (a, s)))) i
  rw [hdf]
  simp only [hierarchyMixedDirection, Fin.lastCases_castSucc, phaseCoordinateDirection,
    map_smul, coprod_apply, toSpanSingleton_apply, zero_smul, add_zero,
    PiLp.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hℓ, one_mul]
  rfl

variable {A : Set ℝ} (hA : A ⊆ Icc 0 T) {τ : ℝ → ℝ} {C : ℝ}
  (hτ : ∀ t ∈ A, ‖τ t‖ ≤ C)

/-- A time weight does not enter the label differentiation. An extra sorted
mixed order therefore controls one scaled label derivative. -/
theorem boundedWeightSeminorm_scaledLabelDerivativeProfile_le (holder : Prop)
    (hT : 0 < T) (ℓ h : ℝ) (i : Fin 3) (n : ℕ) (V : VP) :
    boundedWeightSeminorm holder ℓ h n hT hA τ hτ (scaledLabelDerivativeProfile hT ℓ h i V) ≤
      boundedWeightSeminorm holder ℓ h (n + 1) hT hA τ hτ V := by
  let d (j : Fin 4) := hierarchyMixedDirection ℓ h j 0
  let F := weightedSlices A τ V
  have hB (w : List (Fin 4)) (_hw : w ∈ hierarchyAdmissibleWords (Fin 4) (n + 1)) :
      BddAbove (hierarchyJetValues holder (fun j (_ : Vec3 × ℝ) => d j) w F) :=
    hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h holder w V hA τ hτ
  have hb := (hierarchyFiniteWordNorm_constDerivative_le holder d
    (weightedSlices_smooth hA τ V) i.castSucc n hB).2
  have heq : weightedSlices A τ (scaledLabelDerivativeProfile hT ℓ h i V) =
      fun t => phaseDirectionalDerivative (fun _ => d i.castSucc) (F t) := by
    funext t x
    change τ t • (scaledLabelDerivativeProfile hT ℓ h i V).val.val.val (t, x) =
      fderiv ℝ (τ t • fun y => V.val.val.val (t, y)) x (d i.castSucc)
    rw [scaledLabelDerivativeProfile_apply _ _ _ _ _ (hA t.property), fderiv_const_smul_field]
    rfl
  simp only [boundedWeightSeminorm_apply, heq]
  exact hb

/-- Each coframe row pairs with one additional scaled label derivative of
the input. The three row norms may be bounded on the full slab. -/
theorem boundedWeightSeminorm_slowLabelDivergence_le (holder : Prop) (hT : 0 < T)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) (G : VPmap) (V : VP) {L : ℝ}
    (hG : ∀ i : Fin 3, unweightedSeminorm holder ℓ h n hT
      (scaledCoframeRowProfile ℓ G i) ≤ L) :
    boundedWeightSeminorm holder ℓ h n hT hA τ hτ (slowLabelDivergence hT G V) ≤
      3 * hierarchyQuadraticConstant (Fin 4) n * L *
        boundedWeightSeminorm holder ℓ h (n + 1) hT hA τ hτ V := by
  let K := hierarchyQuadraticConstant (Fin 4) n
  let N : Seminorm ℝ SP := boundedWeightSeminorm holder ℓ h n hT hA τ hτ
  let R (i : Fin 3) := scaledCoframeRowProfile ℓ G i
  let D (i : Fin 3) := scaledLabelDerivativeProfile hT ℓ h i V
  let vN := boundedWeightSeminorm holder ℓ h (n + 1) hT hA τ hτ V
  let B : (Vec3 →L[ℝ] ℝ) →L[ℝ] Vec3 →L[ℝ] ℝ := (ContinuousLinearMap.apply ℝ ℝ).flip
  have hB : ‖B‖ ≤ 1 := by
    simp only [B, opNorm_flip, ContinuousLinearMap.apply]
    refine opNorm_le_bound _ zero_le_one fun f => ?_
    simp only [ContinuousLinearMap.coe_id', id, one_mul]
    rfl
  have hK : 0 ≤ K := by dsimp [K, hierarchyQuadraticConstant]; positivity
  have hterm (i : Fin 3) : N (applyField (R i) (D i)) ≤ K * L * vN := by
    let rN := boundedWeightSeminorm holder ℓ h n hT hA (fun _ => 1) (B := 1) (by simp) (R i)
    let dN := boundedWeightSeminorm holder ℓ h n hT hA τ hτ (D i)
    have hr : rN ≤ L :=
      (boundedWeightSeminorm_mono_time holder ℓ h n hT hA
        (Subset.rfl : Icc 0 T ⊆ Icc 0 T) (fun _ => 1) (C := 1) (by simp) (R i)).trans (hG i)
    have hd : dN ≤ vN := boundedWeightSeminorm_scaledLabelDerivativeProfile_le hA hτ
      holder hT ℓ h i n V
    have hL : 0 ≤ L := (apply_nonneg _ _ : 0 ≤ rN).trans hr
    have hR : 0 ≤ rN := apply_nonneg _ _
    have hD : 0 ≤ dN := apply_nonneg _ _
    calc
      _ ≤ (hierarchyAdmissibleWords (Fin 4) n).card * (2 : ℝ) ^ n *
          (2 * ‖B‖ * rN * dN) :=
        boundedWeightSeminorm_bilinear_le B holder ℓ h n hT hA (fun _ => 1) τ τ
          (Cf := 1) (by simp) hτ hτ (by simp) (R i) (D i) (applyField (R i) (D i))
          (fun t ht x => applyField_eval_onSlab _ _ ⟨hA ht, mem_univ x⟩)
      _ ≤ (hierarchyAdmissibleWords (Fin 4) n).card * (2 : ℝ) ^ n *
          (2 * 1 * L * vN) := by gcongr
      _ = _ := by simp [K, hierarchyQuadraticConstant, mul_assoc]
  change N (slowLabelDivergence hT G V) ≤ 3 * K * L * vN
  rw [slowLabelDivergence_eq_sum_apply_scaledRows hT ℓ h hℓ]
  calc
    _ ≤ ∑ i : Fin 3, N (applyField (R i) (D i)) :=
      Finset.le_sum_of_subadditive N (by simp) (map_add_le_add N) _ _
    _ ≤ ∑ _ : Fin 3, K * L * vN := Finset.sum_le_sum fun i _ => hterm i
    _ = _ := by simp [mul_assoc]

/-- The actual slow divergence product consumes one extra weighted order
of the differentiated profile. The time multiplier on the product may be
split between the two factors. -/
theorem boundedWeightSeminorm_slowLabelDivergenceProduct_le (holder : Prop) (hT : 0 < T)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) (G : VPmap) (V Y : VP) {L : ℝ}
    (hG : ∀ i : Fin 3, unweightedSeminorm holder ℓ h n hT
      (scaledCoframeRowProfile ℓ G i) ≤ L)
    (τV τY τP : ℝ → ℝ) {CV CY CP : ℝ}
    (hV : ∀ t ∈ A, ‖τV t‖ ≤ CV) (hY : ∀ t ∈ A, ‖τY t‖ ≤ CY)
    (hP : ∀ t ∈ A, ‖τP t‖ ≤ CP) (hweight : ∀ t ∈ A, τP t = τV t * τY t) :
    boundedWeightSeminorm holder ℓ h n hT hA τP hP (slowLabelDivergenceProduct hT G V Y) ≤
      3 * hierarchyQuadraticConstant (Fin 4) n ^ 2 * L *
        boundedWeightSeminorm holder ℓ h (n + 1) hT hA τV hV V *
        boundedWeightSeminorm holder ℓ h n hT hA τY hY Y := by
  let B : ℝ →L[ℝ] Vec3 →L[ℝ] Vec3 := lsmul ℝ ℝ
  have hB : ‖B‖ ≤ 1 := opNorm_lsmul_le
  let D := slowLabelDivergence hT G V
  let dN := boundedWeightSeminorm holder ℓ h n hT hA τV hV D
  let yN := boundedWeightSeminorm holder ℓ h n hT hA τY hY Y
  let vN := boundedWeightSeminorm holder ℓ h (n + 1) hT hA τV hV V
  let K := hierarchyQuadraticConstant (Fin 4) n
  have hd : dN ≤ 3 * K * L * vN :=
    boundedWeightSeminorm_slowLabelDivergence_le hA hV holder hT ℓ h hℓ n G V hG
  have hd₀ : 0 ≤ dN := apply_nonneg _ _
  have hy₀ : 0 ≤ yN := apply_nonneg _ _
  calc
    _ ≤ (hierarchyAdmissibleWords (Fin 4) n).card * (2 : ℝ) ^ n * (2 * ‖B‖ * dN * yN) :=
      boundedWeightSeminorm_bilinear_le B holder ℓ h n hT hA τV τY τP hV hY hP hweight
        D Y (slowLabelDivergenceProduct hT G V Y) (by
          intro t ht x
          rw [slowLabelDivergenceProduct_apply _ _ _ _ ⟨hA ht, mem_univ x⟩]
          rfl)
    _ ≤ (hierarchyAdmissibleWords (Fin 4) n).card * (2 : ℝ) ^ n *
        (2 * 1 * (3 * K * L * vN) * yN) := by gcongr
    _ = 3 * K ^ 2 * L * vN * yN := by dsimp [K, hierarchyQuadraticConstant]; ring
private def slowAdvectionCoordinate (hT : 0 < T) (G : VPmap) (z g : VP) (i : Fin 3) : VP :=
  let g' := map (ContinuousLinearMap.apply ℝ Vec3 (coordinateDirection i, 0))
    (hierarchyTwistedSliceDerivative hT g)
  let coframeRow := map (ContinuousLinearMap.compL ℝ Vec3 Vec3 ℝ (EuclideanSpace.proj i)) G
  applyField (map (smulRightL ℝ ℝ Vec3 (ContinuousLinearMap.id ℝ ℝ)) g') (applyField coframeRow z)

private theorem slowAdvectionCoordinate_apply (hT : 0 < T) (G : VPmap) (z g : VP) (i : Fin 3)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3 × ℝ) :
    (slowAdvectionCoordinate hT G z g i).val.val.val (t, x) =
      (G.val.val.val (t, x) (z.val.val.val (t, x))) i •
        fderiv ℝ (fun y => g.val.val.val (t, y)) x (coordinateDirection i, 0) := by
  have hx : (t, x) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  simp only [slowAdvectionCoordinate, applyField_val, HierarchyPeriodicProfile.applyField_val,
    HierarchySmoothProfile.applyField_eval _ _ hx, map_val, HierarchyPeriodicProfile.map_val,
    HierarchySmoothProfile.map_apply _ _ hx, hierarchyTwistedSliceDerivative_apply hT g ht x,
    ContinuousLinearMap.apply_apply, compL_apply, comp_apply]
  rfl

private theorem slowAdvCoordinateSum (hT : 0 < T) (G M : VPmap) (κ z g : VP) :
    (twistedHierarchyOperators hT G M κ).labelAdv z g =
      ∑ i : Fin 3, slowAdvectionCoordinate hT G z g i := by
  apply ext
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  let g' (x : Vec3 × ℝ) := g.val.val.val (t, x)
  let v := G.val.val.val (t, a, s) (z.val.val.val (t, a, s))
  let I := ContinuousLinearMap.inr ℝ ℝ (Vec3 × ℝ)
  have hI : HasFDerivAt (fun x : Vec3 × ℝ => (t, x)) I (a, s) :=
    hasFDerivAt_prodMk_right (𝕜 := ℝ) t (a, s)
  have hD := ((HierarchySmoothProfile.smooth g.val.val).differentiableOn (by simp) (t, a, s)
    hx).hasFDerivWithinAt
  have hm : ∀ᶠ x : Vec3 × ℝ in 𝓝 (a, s), (t, x) ∈ hierarchyProfileSlab T :=
    Eventually.of_forall fun _ => ⟨ht, mem_univ _⟩
  have hrestrict :
      fderiv ℝ g' (a, s) =
        (fderivWithin ℝ g.val.val.val (hierarchyProfileSlab T) (t, a, s)).comp I :=
    (hD.comp_hasFDerivAt (a, s) hI hm).fderiv
  have hv : ∑ i : Fin 3, v i • (coordinateDirection i, (0 : ℝ)) = (v, 0) := by
    have hvec : ∑ i : Fin 3, v i • coordinateDirection i = v := by
      ext j
      let eval := (EuclideanSpace.proj j : Vec3 →L[ℝ] ℝ)
      change eval (∑ i, v i • EuclideanSpace.single i (1 : ℝ)) = v j
      rw [map_sum]
      simp [eval, EuclideanSpace.single, PiLp.single_apply]
    refine Prod.ext ?_ ?_
    · change ContinuousLinearMap.fst ℝ Vec3 ℝ (∑ i : Fin 3, v i • (coordinateDirection i, 0)) = v
      rw [map_sum]
      exact hvec
    · change ContinuousLinearMap.snd ℝ Vec3 ℝ (∑ i : Fin 3, v i • (coordinateDirection i, 0)) = 0
      rw [map_sum]
      simp
  have heval : ((twistedHierarchyOperators hT G M κ).labelAdv z g).val.val.val (t, a, s) =
      fderiv ℝ g' (a, s) (v, 0) := by
    change (HierarchySmoothProfile.advect hT (HierarchySmoothProfile.labelDirections G.val.val)
      z.val.val g.val.val).val (t, a, s) = _
    rw [HierarchySmoothProfile.advect_apply hT _ _ _ hx,
      HierarchySmoothProfile.labelDirections_apply G.val.val z.val.val hx, hrestrict]
    rfl
  rw [heval]
  simp only [Submodule.coe_sum, Finset.sum_apply, slowAdvectionCoordinate_apply hT G z g _ ht]
  conv_lhs => rw [← hv, map_sum]
  simp only [map_smul]
  rfl

private theorem slowAdvection_slices_component_le (hT : 0 < T) (G : VPmap) (z g : VP)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) (i : Fin 3)
    {S : Set ℝ} (hS : S ⊆ Icc 0 T) (r q : ℝ → ℝ) {R Q : ℝ}
    (hr : ∀ t ∈ S, ‖r t‖ ≤ R) (hq : ∀ t ∈ S, ‖q t‖ ≤ Q) :
    let D := hierarchyMixedDirection ℓ h
    hierarchyFiniteWordNorm False D n
      (weightedSlices S (fun t => r t * q t) (slowAdvectionCoordinate hT G z g i)) ≤
      hierarchyQuadraticConstant (Fin 4) n ^ 2 *
        hierarchyFiniteWordNorm False D n (weightedSlices S (fun _ => 1) (scaledCoframeRowProfile ℓ G i)) *
        hierarchyFiniteWordNorm False D n (weightedSlices S r z) *
        hierarchyFiniteWordNorm False D (n + 1) (weightedSlices S q g) := by
  let A := weightedSlices S (fun _ => 1) G
  have hrow : hierarchyScaledCoframeRow ℓ A i =
      weightedSlices S (fun _ => 1) (scaledCoframeRowProfile ℓ G i) := by
    rw [weightedSlices_one_scaledCoframeRowProfile hS]
    congr 1
    funext t x
    change (1 : ℝ) • G.val.val.val (t, x) = G.val.val.val (t, x)
    exact one_smul ℝ _
  have hrowb (w : List (Fin 4)) (_hw : w ∈ hierarchyAdmissibleWords (Fin 4) n) :
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w
        (hierarchyScaledCoframeRow ℓ A i)) := by
    rw [hrow]
    exact hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h False w (scaledCoframeRowProfile ℓ G i)
      hS (fun _ => 1) (B := 1) (by simp)
  have hcalc :=
    hierarchySlowAdvectionComponent_le ℓ h hℓ i n
      (weightedSlices_smooth hS (fun _ => 1) G) (weightedSlices_smooth hS r z)
      (weightedSlices_smooth hS q g) hrowb
      (fun w _ => hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h False w z hS r hr)
      (fun w _ => hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h False w g hS q hq)
      (le_refl _)
  rw [hrow] at hcalc
  have heq : (fun (t : S) x => (A t x (weightedSlices S r z t x)) i •
      fderiv ℝ (weightedSlices S q g t) x (coordinateDirection i, 0)) =
      weightedSlices S (fun t => r t * q t) (slowAdvectionCoordinate hT G z g i) := by
    have hh :=
      hierarchy_slowAdvection_timeFactors (fun (t : S) => r t) (fun (t : S) => q t) A
        (fun t x => z.val.val.val (t, x)) (fun t x => g.val.val.val (t, x)) i
        (fun t => by
          have hd := (weightedSlices_smooth hS (fun _ => 1) g t).differentiable (by simp)
          simpa [weightedSlices] using hd)
    refine hh.trans ?_
    funext t x
    have heval := slowAdvectionCoordinate_apply hT G z g i (hS t.property) x
    simp only [A, weightedSlices, LinearMap.coe_mk, AddHom.coe_mk, one_smul] at *
    exact congrArg (fun v : Vec3 => (r t * q t) • v) heval.symm
  exact heq ▸ hcalc


set_option maxHeartbeats 1000000 in
/-- Slow advection costs one label derivative. A bounded time weight may be
placed on either factor before the fixed-time derivatives are measured. -/
theorem boundedWeightSeminorm_labelAdv_le (hT : 0 < T) (G M : VPmap) (κ z g : VP)
    (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (n : ℕ) {L : ℝ}
    (hG : ∀ i : Fin 3, unweightedSeminorm False ℓ h n hT (scaledCoframeRowProfile ℓ G i) ≤ L)
    {S : Set ℝ} (hS : S ⊆ Icc 0 T) (r q : ℝ → ℝ) {R Q : ℝ}
    (hr : ∀ t ∈ S, ‖r t‖ ≤ R) (hq : ∀ t ∈ S, ‖q t‖ ≤ Q) :
    let hprod : ∀ t ∈ S, ‖r t * q t‖ ≤ R * Q :=
      fun t ht => (norm_mul _ _).le.trans
        (mul_le_mul (hr t ht) (hq t ht) (norm_nonneg _) ((norm_nonneg _).trans (hr t ht)))
    boundedWeightSeminorm False ℓ h n hT hS (fun t => r t * q t) hprod
      ((twistedHierarchyOperators hT G M κ).labelAdv z g) ≤
    3 * hierarchyQuadraticConstant (Fin 4) n ^ 2 * L *
      boundedWeightSeminorm False ℓ h n hT hS r hr z *
      boundedWeightSeminorm False ℓ h (n + 1) hT hS q hq g := by
  dsimp only
  let N : Seminorm ℝ VP := boundedWeightSeminorm False ℓ h n hT hS (fun t => r t * q t)
    (B := R * Q) (fun t ht => (norm_mul _ _).le.trans
      (mul_le_mul (hr t ht) (hq t ht) (norm_nonneg _) ((norm_nonneg _).trans (hr t ht))))
  let K := hierarchyQuadraticConstant (Fin 4) n
  let zN := boundedWeightSeminorm False ℓ h n hT hS r hr z
  let gN := boundedWeightSeminorm False ℓ h (n + 1) hT hS q hq g
  have hz : 0 ≤ zN := apply_nonneg _ _
  have hg : 0 ≤ gN := apply_nonneg _ _
  have hterm (i : Fin 3) : N (slowAdvectionCoordinate hT G z g i) ≤ K ^ 2 * L * zN * gN := by
    have hrow : boundedWeightSeminorm False ℓ h n hT hS (fun _ => 1)
        (B := 1) (by simp) (scaledCoframeRowProfile ℓ G i) ≤ L :=
      (boundedWeightSeminorm_mono_time False ℓ h n hT hS
        (Subset.rfl : Icc 0 T ⊆ Icc 0 T) (fun _ => 1) (C := 1) (by simp)
        (scaledCoframeRowProfile ℓ G i)).trans (hG i)
    exact (slowAdvection_slices_component_le hT G z g ℓ h hℓ n i hS r q hr hq).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrow (sq_nonneg K)) hz) hg)
  change N ((twistedHierarchyOperators hT G M κ).labelAdv z g) ≤ 3 * K ^ 2 * L * zN * gN
  rw [slowAdvCoordinateSum hT G M κ z g]
  calc
    _ ≤ ∑ i : Fin 3, N (slowAdvectionCoordinate hT G z g i) :=
      Finset.le_sum_of_subadditive N (by simp) (map_add_le_add N) _ _
    _ ≤ ∑ _ : Fin 3, K ^ 2 * L * zN * gN := Finset.sum_le_sum fun i _ => hterm i
    _ = _ := by simp [mul_assoc]

end

set_option maxHeartbeats 650000 in
/-- Width-weighted label jets absorb the order-dependent parent power.
The inverse width from the coframe row remains explicit. -/
theorem unweightedSeminorm_scaledCoframeRowProfile_le_of_parent_power_bound
    {T : ℝ} {k : Vec3} (hT : 0 < T)
    (G : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3))
    (hphase : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    {ℓ h D L : ℝ} {n q p : ℕ} {C : ℕ → ℝ}
    (hℓ : 0 ≤ ℓ) (hD : 0 ≤ D) (hL : 0 ≤ L) (hscale : ℓ * D ^ q ≤ 1)
    (hC : ∀ j ≤ n, 0 ≤ C j)
    (hjets : ∀ t ∈ Icc 0 T, ∀ j ≤ n, ∀ a,
      ‖iteratedFDeriv ℝ j (fun b => G.val.val.val (t, b, 0)) a‖ ≤ C j * L * D ^ (q * j + p))
    (i : Fin 3) :
    unweightedSeminorm False ℓ h n hT (scaledCoframeRowProfile ℓ G i) ≤
      (hierarchyAdmissibleWords (Fin 4) n).card *
        ((∑ j ∈ Finset.range (n + 1), C j) * (‖ℓ⁻¹‖ * L * D ^ p)) := by
  let S := Icc (0 : ℝ) T
  let G₀ (t : S) (a : Vec3) := G.val.val.val (t, a, 0)
  let P : (Vec3 →L[ℝ] Vec3) →L[ℝ] (Vec3 →L[ℝ] ℝ) :=
    ℓ⁻¹ • compL ℝ Vec3 Vec3 ℝ (EuclideanSpace.proj i)
  let c (t : S) := P ∘ G₀ t
  have hG₀ (t : S) : ContDiff ℝ ∞ (G₀ t) :=
    (HierarchySmoothProfile.contDiff_labelPhase_slice G.val.val t.property).comp
      (contDiff_id.prodMk contDiff_const)
  have hP : ‖P‖ ≤ ‖ℓ⁻¹‖ := by
    refine P.opNorm_le_bound (norm_nonneg _) fun F => ?_
    refine (P F).opNorm_le_bound (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun v => ?_
    change ‖ℓ⁻¹ * (F v) i‖ ≤ (‖ℓ⁻¹‖ * ‖F‖) * ‖v‖
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le (F v) i).trans (F.le_opNorm v))
      (norm_nonneg _)
  have hc (t : S) : ContDiff ℝ ∞ (c t) := P.contDiff.comp (hG₀ t)
  have hcjet (t : S) (j : ℕ) (hj : j ≤ n) (a : Vec3) :
      ‖iteratedFDeriv ℝ j (c t) a‖ ≤ C j * (‖ℓ⁻¹‖ * L * D ^ p) * D ^ (q * j) := by
    calc
      _ ≤ ‖P‖ * ‖iteratedFDeriv ℝ j (G₀ t) a‖ :=
        P.norm_iteratedFDeriv_comp_left (hG₀ t).contDiffAt (by simp)
      _ ≤ ‖ℓ⁻¹‖ * (C j * L * D ^ (q * j + p)) :=
        mul_le_mul hP (hjets t t.property j hj a) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by rw [pow_add]; ring
  have hcoef := HierarchyRelayCoefficientJets.of_parent_power_bound
    (h := h) hℓ hD (show 0 ≤ ‖ℓ⁻¹‖ * L * D ^ p by positivity) hscale hc hC hcjet
  have heq : hierarchyScaledCoframeRow ℓ (fun (t : S) x => G.val.val.val (t, x)) i =
      (fun (t : S) x => c t x.1) := by
    funext t x
    change ℓ⁻¹ • (EuclideanSpace.proj i).comp (G.val.val.val (t, x)) =
      ℓ⁻¹ • (EuclideanSpace.proj i).comp (G.val.val.val (t, x.1, 0))
    rw [hphase (t, x.1, 0) ⟨t.property, mem_univ _⟩ x.2]
  change hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n
    (weightedSlices S (fun _ => 1) (scaledCoframeRowProfile ℓ G i)) ≤ _
  rw [weightedSlices_one_scaledCoframeRowProfile (Subset.rfl : S ⊆ Icc 0 T), heq]
  exact hcoef.2.finiteNorm_le


end TorusEuler.HierarchyTwistedProfile
