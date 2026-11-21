import TorusEuler.EndpointKinetic
import TorusEuler.ParentCoframeEstimates
import TorusEuler.ParentResidualEstimates

/-! The kinetic and vorticity coefficient estimates of Appendix D and Section 5.5. -/

open ContinuousLinearMap Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

local notation "Coefficient" => Vec3 →L[ℝ] Vec3

private theorem norm_iteratedFDeriv_adjoint_eq (G : Vec3 → Coefficient) (n : ℕ) (a : Vec3) :
    ‖iteratedFDeriv ℝ n (fun b => (G b).adjoint) a‖ = ‖iteratedFDeriv ℝ n G a‖ := by
  let J := ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)
  exact J.norm_iteratedFDeriv_comp_left G a n

private theorem contDiff_adjoint_field {G : Vec3 → Coefficient} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun b => (G b).adjoint) :=
  (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)).toContinuousLinearEquiv.contDiff.comp hG

private theorem norm_iteratedFDeriv_meanForms_le {F M : Vec3 → Coefficient}
    (hF : ContDiff ℝ ∞ F) (hM : ContDiff ℝ ∞ M) {n : ℕ} (a : Vec3) {C D : ℝ}
    (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hFjet : ∀ i ≤ n, ‖iteratedFDeriv ℝ i F a‖ ≤ C * D ^ (5 * i + 1))
    (hMjet : ∀ i ≤ n, ‖iteratedFDeriv ℝ i M a‖ ≤ C * D ^ (6 * i + 1)) :
    ‖iteratedFDeriv ℝ n (fun b => kineticForm (F b)) a‖ ≤
        (2 : ℝ) ^ n * (C * C) * D ^ (5 * n + 2) ∧
      ‖iteratedFDeriv ℝ n (fun b => vorticityForm (F b) (M b)) a‖ ≤
        (2 : ℝ) ^ n * (C * ((2 : ℝ) ^ n * ((2 * C) * C))) * D ^ (6 * n + 3) := by
  let Fadj (b : Vec3) := (F b).adjoint
  let Madj (b : Vec3) := (M b).adjoint
  let curl (b : Vec3) := Madj b - M b
  let B := compL ℝ Vec3 Vec3 Vec3
  have hB : ‖B‖ ≤ 1 := norm_compL_le ℝ Vec3 Vec3 Vec3
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hFa : ContDiff ℝ ∞ Fadj := contDiff_adjoint_field hF
  have hMa : ContDiff ℝ ∞ Madj := contDiff_adjoint_field hM
  have hcurl : ContDiff ℝ ∞ curl := hMa.sub hM
  have hFadj (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i Fadj a‖ ≤ C * D ^ (5 * i + 1) := by
    exact (norm_iteratedFDeriv_adjoint_eq F i a).trans_le (hFjet i hi)
  have hF6 (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i F a‖ ≤ C * D ^ (6 * i + 1) :=
    (hFjet i hi).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by omega)) hC)
  have hFa6 (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i Fadj a‖ ≤ C * D ^ (6 * i + 1) :=
    (norm_iteratedFDeriv_adjoint_eq F i a).trans_le (hF6 i hi)
  have hcurlJet (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i curl a‖ ≤ (2 * C) * D ^ (6 * i + 1) := by
    have hsub := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := i) (x := a)
      (hMa.of_le (by simp)).contDiffAt (hM.of_le (by simp)).contDiffAt
    change iteratedFDeriv ℝ i curl a = _ at hsub
    rw [hsub]
    calc
      _ ≤ ‖iteratedFDeriv ℝ i Madj a‖ + ‖iteratedFDeriv ℝ i M a‖ := norm_sub_le _ _
      _ ≤ C * D ^ (6 * i + 1) + C * D ^ (6 * i + 1) :=
        add_le_add ((norm_iteratedFDeriv_adjoint_eq M i a).trans_le (hMjet i hi)) (hMjet i hi)
      _ = _ := by ring
  constructor
  · exact norm_iteratedFDeriv_bilinear_scaled_le B hB
      (hFa.of_le (by simp)) (hF.of_le (by simp)) a hFadj hFjet
  · let Q (b : Vec3) := B (curl b) (F b)
    have hQ : ContDiff ℝ ∞ Q := hcurl.clm_comp hF
    have hQjet (i : ℕ) (hi : i ≤ n) :
        ‖iteratedFDeriv ℝ i Q a‖ ≤ ((2 : ℝ) ^ n * ((2 * C) * C)) * D ^ (6 * i + 2) := by
      calc
        _ ≤ (2 : ℝ) ^ i * ((2 * C) * C) * D ^ (6 * i + 1 + 1) :=
          norm_iteratedFDeriv_bilinear_scaled_le B hB (hcurl.of_le (by simp))
            (hF.of_le (by simp)) a (fun j hj => hcurlJet j (hj.trans hi))
            (fun j hj => hF6 j (hj.trans hi))
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) hi) (mul_nonneg (mul_nonneg (by norm_num) hC) hC))
          (pow_nonneg hD₀ _)
    exact norm_iteratedFDeriv_bilinear_scaled_le B hB
      (hFa.of_le (by simp)) (hQ.of_le (by simp)) a hFa6 hQjet

set_option maxHeartbeats 1100000 in
/-- The actual mean coefficients and the transpose deformation satisfy the
spatial bounds used in (D.3), with explicit powers of the parent scale. -/
theorem exists_parentMeanCoefficientJetBounds (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T D : ℝ}, 0 < T → T ≤ 1 → 1 ≤ D →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
        (∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
          ‖iteratedFDeriv ℝ k (U t) x‖ ≤ R n * D ^ k) →
        ∀ t ∈ Icc 0 T,
          let F := fderiv ℝ (X 0 t)
          let Fadj (b : Vec3) := (F b).adjoint
          let M (b : Vec3) := fderiv ℝ (U t) (X 0 t b)
          let K (b : Vec3) := kineticForm (F b)
          let Ω (b : Vec3) := vorticityForm (F b) (M b)
          ContDiff ℝ ∞ F ∧ ContDiff ℝ ∞ Fadj ∧ ContDiff ℝ ∞ K ∧ ContDiff ℝ ∞ Ω ∧
          ∀ n : ℕ, ∀ a : Vec3,
            ‖iteratedFDeriv ℝ n F a‖ ≤ C n * D ^ (5 * n + 1) ∧
            ‖iteratedFDeriv ℝ n Fadj a‖ ≤ C n * D ^ (5 * n + 1) ∧
            ‖iteratedFDeriv ℝ n K a‖ ≤ C n * D ^ (5 * n + 2) ∧
            ‖iteratedFDeriv ℝ n Ω a‖ ≤ C n * D ^ (6 * n + 3) := by
  obtain ⟨P, hP, hparent⟩ := exists_parent_coefficientJetBounds R hR
  let B (n : ℕ) := ∑ i ∈ Finset.range (n + 1), P i
  let BK (n : ℕ) := (2 : ℝ) ^ n * (B n * B n)
  let BΩ (n : ℕ) := (2 : ℝ) ^ n * (B n * ((2 : ℝ) ^ n * ((2 * B n) * B n)))
  let C (n : ℕ) := B n + BK n + BΩ n
  have hB (n : ℕ) : 0 ≤ B n := Finset.sum_nonneg fun i _ => hP i
  have hBK (n : ℕ) : 0 ≤ BK n :=
    mul_nonneg (by positivity) (mul_nonneg (hB n) (hB n))
  have hBΩ (n : ℕ) : 0 ≤ BΩ n :=
    mul_nonneg (by positivity) (mul_nonneg (hB n)
      (mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (by norm_num) (hB n)) (hB n))))
  have hPC {i n : ℕ} (hi : i ≤ n) : P i ≤ B n :=
    Finset.single_le_sum (f := P) (fun j _ => hP j) (Finset.mem_range.mpr (by omega))
  refine ⟨C, fun n => add_nonneg (add_nonneg (hB n) (hBK n)) (hBΩ n), ?_⟩
  intro U X T D hT hT₁ hD hX hU hper hF hInv hUjet t ht F Fadj M K Ω
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  let e := coordinateDirection 0
  have he : ‖labelWaveVector X 0 0 e 0‖ = 1 := by
    have hX₀ : X 0 0 = id := funext fun a => hX.initial 0 h₀ a
    simp [labelWaveVector, hX₀, e, coordinateDirection, ContinuousLinearMap.adjoint_id]
  have hForward : ContDiff ℝ ∞ (X 0 t) :=
    contDiff_iff_forall_nat_le.mpr fun n _ => (hX.labelJets_evolve n hT hU hper).1 t ht
  have hUslice : ContDiff ℝ ∞ (U t) :=
    contDiffOn_univ.mp (hU.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  have hFs : ContDiff ℝ ∞ F := hForward.fderiv_right (by simp)
  have hFas : ContDiff ℝ ∞ Fadj := contDiff_adjoint_field hFs
  have hMs : ContDiff ℝ ∞ M := (hUslice.fderiv_right (by simp)).comp hForward
  have hMads : ContDiff ℝ ∞ (fun b => (M b).adjoint) := contDiff_adjoint_field hMs
  have hKs : ContDiff ℝ ∞ K := hFas.clm_comp hFs
  have hΩs : ContDiff ℝ ∞ Ω := hFas.clm_comp ((hMads.sub hMs).clm_comp hFs)
  have hbase := hparent hT hT₁ hD hX hU hper hF hInv hUjet e zero_lt_one h₀ he
  refine ⟨hFs, hFas, hKs, hΩs, fun n a => ?_⟩
  have hFjet (i : ℕ) (hi : i ≤ n) : ‖iteratedFDeriv ℝ i F a‖ ≤ B n * D ^ (5 * i + 1) :=
    (hbase i t ht a).1.trans (mul_le_mul_of_nonneg_right (hPC hi) (pow_nonneg hD₀ _))
  have hMjet (i : ℕ) (hi : i ≤ n) : ‖iteratedFDeriv ℝ i M a‖ ≤ B n * D ^ (6 * i + 1) :=
    (hbase i t ht a).2.2.2.1.trans (mul_le_mul_of_nonneg_right (hPC hi) (pow_nonneg hD₀ _))
  obtain ⟨hKjet, hΩjet⟩ := norm_iteratedFDeriv_meanForms_le hFs hMs a (hB n) hD hFjet hMjet
  have hB_le : B n ≤ C n := by dsimp only [C]; linarith [hBK n, hBΩ n]
  have hBK_le : BK n ≤ C n := by dsimp only [C]; linarith [hB n, hBΩ n]
  have hBΩ_le : BΩ n ≤ C n := by dsimp only [C]; linarith [hB n, hBK n]
  have hf := (hFjet n le_rfl).trans (mul_le_mul_of_nonneg_right hB_le (pow_nonneg hD₀ _))
  exact ⟨hf, (norm_iteratedFDeriv_adjoint_eq F n a).trans_le hf,
    hKjet.trans (mul_le_mul_of_nonneg_right hBK_le (pow_nonneg hD₀ _)),
    hΩjet.trans (mul_le_mul_of_nonneg_right hBΩ_le (pow_nonneg hD₀ _))⟩


section HalfHolderNorms

variable {I G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The half-Hölder norm of a torus representative of a label derivative is
bounded by the corresponding word norm on the Euclidean lift. -/
theorem norm_halfHolder_le_of_hierarchyLabelWord
    {ℓ : ℝ} {f : I → Vec3 → G} (w : List (Fin 3)) (t : I)
    (hBdd : BddAbove (hierarchyJetValues True (hierarchyLabelDirection ℓ) w f))
    (g : HalfHolder (UnitAddTorus (Fin 3)) G)
    (hLift : ∀ x, HalfHolder.eval (toUnitTorus x) g =
      phaseOperatorWord (hierarchyLabelDirection ℓ) w (f t) x) :
    ‖g‖ ≤ Real.sqrt 2 * sSup (hierarchyJetValues True (hierarchyLabelDirection ℓ) w f) := by
  let D := hierarchyLabelDirection ℓ
  let v := phaseOperatorWord D w (f t)
  let B := sSup (hierarchyJetValues True D w f)
  have hB : 0 ≤ B := le_csSup hBdd (Or.inl rfl)
  have hroot : 1 ≤ Real.sqrt (2 : ℝ) := by
    exact Real.le_sqrt_of_sq_le (by norm_num)
  have hval (x : Vec3) : ‖v x‖ ≤ B :=
    le_csSup hBdd (Or.inr (Or.inl ⟨t, x, rfl⟩))
  have hinc (x y : Vec3) : ‖v x - v y‖ ≤ B * Real.sqrt (dist x y) := by
    by_cases hxy : x = y
    · simp [hxy]
    · exact (div_le_iff₀ (Real.sqrt_pos.2 (dist_pos.2 hxy))).1
        (le_csSup hBdd (Or.inr (Or.inr ⟨trivial, t, x, y, rfl⟩)))
  apply (HalfHolder.norm_le_iff (mul_nonneg (Real.sqrt_nonneg _) hB)).mpr
  constructor
  · intro z
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
    change ‖HalfHolder.eval (toUnitTorus x) g‖ ≤ _
    rw [hLift]
    exact (hval x).trans (le_mul_of_one_le_left hB hroot)
  · intro z w'
    obtain ⟨x, y, hx, hy, hDist⟩ := exists_close_lifts z w'
    change ‖HalfHolder.eval z g - HalfHolder.eval w' g‖ ≤ _
    have hzx : HalfHolder.eval z g = v x := hx ▸ hLift x
    have hwy : HalfHolder.eval w' g = v y := hy ▸ hLift y
    rw [hzx, hwy]
    calc
      _ ≤ B * Real.sqrt (dist x y) := hinc x y
      _ ≤ B * Real.sqrt (2 * dist z w') :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by simpa only [dist_eq_norm] using hDist)) hB
      _ = _ := by rw [Real.sqrt_mul (by norm_num)]; ring

/-- A torus representative of the unweighted word can be used directly
in a weighted half-Hölder coefficient estimate. -/
theorem mul_norm_halfHolder_le_of_hierarchyLabelWord
    {ℓ : ℝ} {f : I → Vec3 → G} (hℓ : 0 ≤ ℓ) (w : List (Fin 3)) (t : I)
    (hf : ContDiff ℝ ∞ (f t))
    (hBdd : BddAbove (hierarchyJetValues True (hierarchyLabelDirection ℓ) w f))
    (g : HalfHolder (UnitAddTorus (Fin 3)) G)
    (hLift : ∀ x, HalfHolder.eval (toUnitTorus x) g = spatialDerivativeWord w (f t) x) :
    ℓ ^ w.length * ‖g‖ ≤
      Real.sqrt 2 * sSup (hierarchyJetValues True (hierarchyLabelDirection ℓ) w f) := by
  have hb := norm_halfHolder_le_of_hierarchyLabelWord w t hBdd (ℓ ^ w.length • g) (by
    intro x
    rw [map_smul, hLift, phaseOperatorWord_hierarchyLabelDirection_eq_smul ℓ hf])
  simpa only [norm_smul, Real.norm_of_nonneg (pow_nonneg hℓ _)] using hb

private theorem hierarchyFiniteWordNorm_holder_le_of_power
    {f : I → Vec3 → G} {D ℓ A : ℝ} {C : ℕ → ℝ} (hD : 1 ≤ D)
    (hℓ : 0 < ℓ) (hscale : ℓ * D ^ 6 ≤ 1) (hA : 0 ≤ A)
    (hC : ∀ m, 0 ≤ C m) (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hjet : ∀ m t a, ‖iteratedFDeriv ℝ m (f t) a‖ ≤ C m * A * D ^ (6 * m)) (n : ℕ) :
    hierarchyFiniteWordNorm True (hierarchyLabelDirection ℓ) n f ≤
      (4 * ∑ w ∈ hierarchyAdmissibleWords (Fin 3) (n + 1), C w.length) * A / Real.sqrt ℓ := by
  have hℓ₁ : ℓ ≤ 1 := (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (one_le_pow₀ hD (n := 6)) hℓ.le :
    ℓ ≤ ℓ * D ^ 6).trans hscale
  obtain ⟨hBdd, hNorm⟩ := hierarchyFiniteWordNorm_false_label_le_of_iteratedFDeriv hℓ.le hscale hA
    hf (n + 1) (fun m _ => hC m) (fun m _ => hjet m)
  calc
    _ ≤ 4 * hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) (n + 1) f / Real.sqrt ℓ :=
      hierarchyFiniteWordNorm_holder_le ℓ hℓ hℓ₁ n hf hBdd
    _ ≤ _ := by
      rw [mul_assoc]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNorm (by norm_num))
        (Real.sqrt_nonneg ℓ)

end HalfHolderNorms

/-- A uniform bound with the square-root label gain gives the slow-coefficient
threshold after multiplication by the low-order inverse bound. -/
theorem mul_le_of_meanCoefficientThreshold {A B C D ℓ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hB : B ≤ C * D ^ 9 * Real.sqrt ℓ) (hsmall : A * D ^ 9 * Real.sqrt ℓ ≤ 1) :
    A * B ≤ C := by
  calc
    _ ≤ A * (C * D ^ 9 * Real.sqrt ℓ) := mul_le_mul_of_nonneg_left hB hA
    _ = (A * D ^ 9 * Real.sqrt ℓ) * C := by ring
    _ ≤ C := mul_le_of_le_one_left hC hsmall


section PositiveWordHolder

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem norm_spatialDerivativeWord_le_iteratedFDeriv {f : Vec3 → G}
    (hf : ContDiff ℝ ∞ f) (w : List (Fin 3)) (x : Vec3) :
    ‖spatialDerivativeWord w f x‖ ≤ ‖iteratedFDeriv ℝ w.length f x‖ := by
  have hcoord (i : Fin 3) : ‖coordinateDirection i‖ = 1 := by simp [coordinateDirection]
  rw [spatialDerivativeWord_eq_iteratedFDeriv hf]
  simpa only [hcoord, Finset.prod_const_one, mul_one] using
    (iteratedFDeriv ℝ w.length f x).le_opNorm (fun i => coordinateDirection (w.get i))

private theorem norm_fderiv_spatialDerivativeWord_le {f : Vec3 → G}
    (hf : ContDiff ℝ ∞ f) (w : List (Fin 3)) (x : Vec3) :
    ‖fderiv ℝ (spatialDerivativeWord w f) x‖ ≤ ‖iteratedFDeriv ℝ (w.length + 1) f x‖ := by
  have hcoord (i : Fin 3) : ‖coordinateDirection i‖ = 1 := by simp [coordinateDirection]
  have hword : spatialDerivativeWord w f = fun y =>
      iteratedFDeriv ℝ w.length f y (fun i => coordinateDirection (w.get i)) :=
    funext (spatialDerivativeWord_eq_iteratedFDeriv hf w)
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ w.length f) x :=
    hf.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top w.length) x
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  rw [hword]
  let directions : Fin (w.length + 1) → Vec3 :=
    Fin.cons v (fun i => coordinateDirection (w.get i))
  have happly :
      iteratedFDeriv ℝ (w.length + 1) f x directions =
        (fderiv ℝ (fun y => iteratedFDeriv ℝ w.length f y
          (fun i => coordinateDirection (w.get i))) x) v := by
    simpa only [directions, Fin.tail_cons, Fin.cons_zero] using
      (hdiff.iteratedFDeriv_succ_apply_left' (m := directions))
  rw [← happly]
  simpa only [directions, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, hcoord,
    Finset.prod_const_one, mul_one] using
    (iteratedFDeriv ℝ (w.length + 1) f x).le_opNorm directions

private theorem norm_weightedLabelWord_le_positiveJet {ell D : ℝ} {p q : ℕ}
    {A : ℝ} {f : Vec3 → G} (hell : 0 ≤ ell) (hD : 1 ≤ D) (hscale : ell * D ^ p ≤ 1)
    (hf : ContDiff ℝ ∞ f) (w : List (Fin 3)) (hw : 0 < w.length) (hA : 0 ≤ A)
    (x : Vec3) (hjet : ‖iteratedFDeriv ℝ w.length f x‖ ≤ A * D ^ (p * w.length + q)) :
    ‖phaseOperatorWord (hierarchyLabelDirection ell) w f x‖ ≤ ell * A * D ^ (p + q) := by
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hbase₀ : 0 ≤ ell * D ^ p := mul_nonneg hell (pow_nonneg hD₀ _)
  have hbasePow : (ell * D ^ p) ^ w.length ≤ ell * D ^ p := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hw)
    rw [hm, pow_succ]
    exact mul_le_of_le_one_left hbase₀ (pow_le_one₀ hbase₀ hscale)
  rw [phaseOperatorWord_hierarchyLabelDirection_eq_smul ell hf w x,
    norm_smul, Real.norm_of_nonneg (pow_nonneg hell _)]
  calc
    _ ≤ ell ^ w.length * ‖iteratedFDeriv ℝ w.length f x‖ :=
      mul_le_mul_of_nonneg_left (norm_spatialDerivativeWord_le_iteratedFDeriv hf w x)
        (pow_nonneg hell _)
    _ ≤ ell ^ w.length * (A * D ^ (p * w.length + q)) :=
      mul_le_mul_of_nonneg_left hjet (pow_nonneg hell _)
    _ = (ell * D ^ p) ^ w.length * (A * D ^ q) := by
      rw [mul_pow, ← pow_mul, pow_add]; ring
    _ ≤ (ell * D ^ p) * (A * D ^ q) :=
      mul_le_mul_of_nonneg_right hbasePow (mul_nonneg hA (pow_nonneg hD₀ _))
    _ = _ := by rw [pow_add]; ring

private theorem norm_sub_le_sqrt_dist_of_differentiable_bounds {f : Vec3 → G}
    (hf : Differentiable ℝ f) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hval : ∀ z, ‖f z‖ ≤ A) (hder : ∀ z, ‖fderiv ℝ f z‖ ≤ B) (x y : Vec3) :
    ‖f x - f y‖ ≤ Real.sqrt (2 * A * B) * Real.sqrt (dist x y) := by
  have hdiff : ‖f x - f y‖ ≤ B * dist x y := by
    simpa only [dist_eq_norm] using
      (convex_univ : Convex ℝ (Set.univ : Set Vec3)).norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => hf z) (fun z _ => hder z) (Set.mem_univ y) (Set.mem_univ x)
  have hsum : ‖f x - f y‖ ≤ 2 * A := by
    rw [two_mul]
    exact (norm_sub_le _ _).trans (add_le_add (hval x) (hval y))
  have hsq : ‖f x - f y‖ ^ 2 ≤ (2 * A * B) * dist x y := by
    rw [sq, mul_assoc]
    exact mul_le_mul hsum hdiff (norm_nonneg _) (by positivity)
  rw [← Real.sqrt_mul (by positivity)]
  exact Real.le_sqrt_of_sq_le hsq

/-- A positive weighted label word gains the square root of the label radius
in the half-Hölder seminorm. The constants use the two adjacent Fréchet jets. -/
theorem norm_sub_weightedLabelWord_le_sqrt_dist_of_iteratedFDeriv
    {ell D : ℝ} {p q : ℕ} {C : ℕ → ℝ} {f : Vec3 → G}
    (hell : 0 ≤ ell) (hD : 1 ≤ D) (hscale : ell * D ^ p ≤ 1)
    (hf : ContDiff ℝ ∞ f) (w : List (Fin 3)) (hw : 0 < w.length)
    (hC : 0 ≤ C w.length) (hC' : 0 ≤ C (w.length + 1))
    (hjet : ∀ x, ‖iteratedFDeriv ℝ w.length f x‖ ≤ C w.length * D ^ (p * w.length + q))
    (hjet' : ∀ x, ‖iteratedFDeriv ℝ (w.length + 1) f x‖ ≤
      C (w.length + 1) * D ^ (p * (w.length + 1) + q)) (x y : Vec3) :
    ‖phaseOperatorWord (hierarchyLabelDirection ell) w f x -
      phaseOperatorWord (hierarchyLabelDirection ell) w f y‖ ≤
      (Real.sqrt (2 * C w.length * C (w.length + 1)) * D ^ (p + q) * Real.sqrt ell) *
        Real.sqrt (dist x y) := by
  let g := phaseOperatorWord (hierarchyLabelDirection ell) w f
  let scale := D ^ (p + q)
  let A := ell * C w.length * scale
  let B := C (w.length + 1) * scale
  have hscale₀ : 0 ≤ scale := pow_nonneg (zero_le_one.trans hD) _
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg hell hC) hscale₀
  have hB : 0 ≤ B := mul_nonneg hC' hscale₀
  have hbase₀ : 0 ≤ ell * D ^ p := mul_nonneg hell (pow_nonneg (zero_le_one.trans hD) _)
  have hword : g = fun z => ell ^ w.length • spatialDerivativeWord w f z :=
    funext (phaseOperatorWord_hierarchyLabelDirection_eq_smul ell hf w)
  have hspatial : Differentiable ℝ (spatialDerivativeWord w f) :=
    (contDiff_phaseOperatorWord (fun _ => contDiff_const) hf w).differentiable (by simp)
  have hg : Differentiable ℝ g := by
    rw [hword]
    exact hspatial.const_smul (ell ^ w.length)
  have hval (z : Vec3) : ‖g z‖ ≤ A :=
    norm_weightedLabelWord_le_positiveJet hell hD hscale hf w hw hC z (hjet z)
  have hder (z : Vec3) : ‖fderiv ℝ g z‖ ≤ B := by
    rw [hword, fderiv_fun_const_smul (hspatial z), norm_smul,
      Real.norm_of_nonneg (pow_nonneg hell _)]
    calc
      _ ≤ ell ^ w.length * ‖iteratedFDeriv ℝ (w.length + 1) f z‖ :=
        mul_le_mul_of_nonneg_left (norm_fderiv_spatialDerivativeWord_le hf w z)
          (pow_nonneg hell _)
      _ ≤ ell ^ w.length * (C (w.length + 1) * D ^ (p * (w.length + 1) + q)) :=
        mul_le_mul_of_nonneg_left (hjet' z) (pow_nonneg hell _)
      _ = (ell * D ^ p) ^ w.length * B := by
        dsimp [B, scale]
        rw [mul_pow, ← pow_mul, Nat.mul_succ, Nat.add_assoc, pow_add]
        ring
      _ ≤ B := mul_le_of_le_one_left hB (pow_le_one₀ hbase₀ hscale)
  change ‖g x - g y‖ ≤ _ * Real.sqrt (dist x y)
  have hsqrt : Real.sqrt (2 * A * B) =
      Real.sqrt (2 * C w.length * C (w.length + 1)) * scale * Real.sqrt ell := by
    have hab : 2 * A * B = (2 * C w.length * C (w.length + 1)) * (scale ^ 2) * ell := by
      dsimp [A, B]
      ring
    rw [hab, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_sq hscale₀]
  rw [← hsqrt]
  exact norm_sub_le_sqrt_dist_of_differentiable_bounds hg hA hB hval hder x y

/-- The corresponding bound for the half-Hölder difference quotient. -/
theorem weightedLabelWord_holderQuotient_le_of_iteratedFDeriv
    {ell D : ℝ} {p q : ℕ} {C : ℕ → ℝ} {f : Vec3 → G}
    (hell : 0 ≤ ell) (hD : 1 ≤ D) (hscale : ell * D ^ p ≤ 1)
    (hf : ContDiff ℝ ∞ f) (w : List (Fin 3)) (hw : 0 < w.length)
    (hC : 0 ≤ C w.length) (hC' : 0 ≤ C (w.length + 1))
    (hjet : ∀ x, ‖iteratedFDeriv ℝ w.length f x‖ ≤ C w.length * D ^ (p * w.length + q))
    (hjet' : ∀ x, ‖iteratedFDeriv ℝ (w.length + 1) f x‖ ≤
      C (w.length + 1) * D ^ (p * (w.length + 1) + q)) {x y : Vec3} (hxy : x ≠ y) :
    ‖phaseOperatorWord (hierarchyLabelDirection ell) w f x -
      phaseOperatorWord (hierarchyLabelDirection ell) w f y‖ / Real.sqrt (dist x y) ≤
      Real.sqrt (2 * C w.length * C (w.length + 1)) * D ^ (p + q) * Real.sqrt ell :=
  (div_le_iff₀ (Real.sqrt_pos.2 (dist_pos.2 hxy))).2
    (norm_sub_weightedLabelWord_le_sqrt_dist_of_iteratedFDeriv hell hD hscale hf w hw hC hC'
      hjet hjet' x y)

/-- Uniform adjacent jet bounds bound the value and half-Hölder quotient
of every weighted label word, including the empty word. -/
theorem hierarchyJetValues_true_label_bddAbove_csSup_le_of_iteratedFDeriv
    {T : Type*} {ell A B : ℝ} {f : T → Vec3 → G}
    (hell : 0 ≤ ell) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ t, ContDiff ℝ ∞ (f t)) (w : List (Fin 3))
    (hjet : ∀ t z, ‖iteratedFDeriv ℝ w.length (f t) z‖ ≤ A)
    (hjet' : ∀ t z, ‖iteratedFDeriv ℝ (w.length + 1) (f t) z‖ ≤ B) :
    BddAbove (hierarchyJetValues True (hierarchyLabelDirection ell) w f) ∧
    sSup (hierarchyJetValues True (hierarchyLabelDirection ell) w f) ≤
      ell ^ w.length * (A + Real.sqrt (2 * A * B)) := by
  let M := ell ^ w.length * (A + Real.sqrt (2 * A * B))
  have hM : 0 ≤ M := mul_nonneg (pow_nonneg hell _) (add_nonneg hA (Real.sqrt_nonneg _))
  have hrange : ∀ r ∈ hierarchyJetValues True (hierarchyLabelDirection ell) w f, r ≤ M := by
    rintro _ (rfl | ⟨t, x, rfl⟩ | ⟨_, t, x, y, rfl⟩)
    · exact hM
    · rw [phaseOperatorWord_hierarchyLabelDirection_eq_smul ell (hf t) w x,
        norm_smul, Real.norm_of_nonneg (pow_nonneg hell _)]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hell _)
      exact (norm_spatialDerivativeWord_le_iteratedFDeriv (hf t) w x).trans
        ((hjet t x).trans (le_add_of_nonneg_right (Real.sqrt_nonneg _)))
    · by_cases hxy : x = y
      · subst y
        simpa only [sub_self, norm_zero, zero_div] using hM
      · rw [phaseOperatorWord_hierarchyLabelDirection_eq_smul ell (hf t) w x,
          phaseOperatorWord_hierarchyLabelDirection_eq_smul ell (hf t) w y,
          ← smul_sub, norm_smul, Real.norm_of_nonneg (pow_nonneg hell _), mul_div_assoc]
        refine mul_le_mul_of_nonneg_left (le_trans ?_ (le_add_of_nonneg_left hA))
          (pow_nonneg hell _)
        apply (div_le_iff₀ (Real.sqrt_pos.2 (dist_pos.2 hxy))).2
        have hd : Differentiable ℝ (spatialDerivativeWord w (f t)) :=
          (contDiff_phaseOperatorWord (fun _ => contDiff_const) (hf t) w).differentiable (by simp)
        exact norm_sub_le_sqrt_dist_of_differentiable_bounds hd hA hB
          (fun z => (norm_spatialDerivativeWord_le_iteratedFDeriv (hf t) w z).trans (hjet t z))
          (fun z => (norm_fderiv_spatialDerivativeWord_le (hf t) w z).trans (hjet' t z)) x y
  exact ⟨⟨M, hrange⟩, csSup_le ⟨0, Or.inl rfl⟩ hrange⟩

/-- The full half-Hölder range of a positive weighted word gains a factor
of the square root of the label radius. -/
theorem hierarchyJetValues_true_label_positive_bddAbove_csSup_le_of_iteratedFDeriv
    {T : Type*} {ell D : ℝ} {p q : ℕ} {C : ℕ → ℝ} {f : T → Vec3 → G}
    (hell : 0 ≤ ell) (hD : 1 ≤ D) (hscale : ell * D ^ p ≤ 1)
    (hf : ∀ t, ContDiff ℝ ∞ (f t)) (w : List (Fin 3)) (hw : 0 < w.length)
    (hC : 0 ≤ C w.length) (hC' : 0 ≤ C (w.length + 1))
    (hjet : ∀ t z, ‖iteratedFDeriv ℝ w.length (f t) z‖ ≤ C w.length * D ^ (p * w.length + q))
    (hjet' : ∀ t z, ‖iteratedFDeriv ℝ (w.length + 1) (f t) z‖ ≤
      C (w.length + 1) * D ^ (p * (w.length + 1) + q)) :
    BddAbove (hierarchyJetValues True (hierarchyLabelDirection ell) w f) ∧
    sSup (hierarchyJetValues True (hierarchyLabelDirection ell) w f) ≤
      (C w.length + Real.sqrt (2 * C w.length * C (w.length + 1))) *
        D ^ (p + q) * Real.sqrt ell := by
  let K := Real.sqrt (2 * C w.length * C (w.length + 1))
  let S := D ^ (p + q)
  let M := (C w.length + K) * S * Real.sqrt ell
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hS : 0 ≤ S := pow_nonneg (zero_le_one.trans hD) _
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg (add_nonneg hC hK) hS) (Real.sqrt_nonneg _)
  have hell₁ : ell ≤ 1 := by
    calc
      ell = ell * 1 := (mul_one ell).symm
      _ ≤ ell * D ^ p := mul_le_mul_of_nonneg_left (one_le_pow₀ hD) hell
      _ ≤ 1 := hscale
  have hsqrt : ell ≤ Real.sqrt ell := by
    have hroot : Real.sqrt ell ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hell₁
    calc
      ell = Real.sqrt ell * Real.sqrt ell := by rw [← sq, Real.sq_sqrt hell]
      _ ≤ Real.sqrt ell * 1 := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _)
      _ = _ := mul_one _
  have hrange : ∀ r ∈ hierarchyJetValues True (hierarchyLabelDirection ell) w f, r ≤ M := by
    rintro _ (rfl | ⟨t, x, rfl⟩ | ⟨_, t, x, y, rfl⟩)
    · exact hM
    · calc
        _ ≤ ell * C w.length * S :=
          norm_weightedLabelWord_le_positiveJet hell hD hscale (hf t) w hw hC x (hjet t x)
        _ ≤ Real.sqrt ell * (C w.length + K) * S :=
          mul_le_mul_of_nonneg_right (mul_le_mul hsqrt (le_add_of_nonneg_right hK)
            hC (Real.sqrt_nonneg _)) hS
        _ = M := by dsimp [M]; ring
    · by_cases hxy : x = y
      · subst y
        simpa only [sub_self, norm_zero, zero_div] using hM
      · refine (weightedLabelWord_holderQuotient_le_of_iteratedFDeriv hell hD hscale
          (hf t) w hw hC hC' (hjet t) (hjet' t) hxy).trans ?_
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) hS) (Real.sqrt_nonneg _)
  exact ⟨⟨M, hrange⟩, csSup_le ⟨0, Or.inl rfl⟩ hrange⟩

end PositiveWordHolder

set_option maxHeartbeats 1200000 in
/-- The positive label derivatives of the kinetic and vorticity coefficients
lose only an order-independent power of the parent scale and gain the square
root of the radius. The deformation and its transpose have the finite
half-Hölder bounds needed to put the forcing and response in label variables. -/
theorem exists_parentMeanWeightedCoefficientBounds (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ C H : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧ (∀ n, 0 ≤ H n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T D ℓ : ℝ},
        0 < T → T ≤ 1 → 1 ≤ D → 0 < ℓ → ℓ * D ^ 6 ≤ 1 →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
        (∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
          ‖iteratedFDeriv ℝ k (U t) x‖ ≤ R n * D ^ k) →
        let F (t : Icc (0 : ℝ) T) := fderiv ℝ (X 0 t.val)
        let Fadj (t : Icc (0 : ℝ) T) (b : Vec3) := (F t b).adjoint
        let M (t : Icc (0 : ℝ) T) (b : Vec3) := fderiv ℝ (U t.val) (X 0 t.val b)
        let K (t : Icc (0 : ℝ) T) (b : Vec3) := kineticForm (F t b)
        let Ω (t : Icc (0 : ℝ) T) (b : Vec3) := vorticityForm (F t b) (M t b)
        let d := hierarchyLabelDirection ℓ
        (∀ w : List (Fin 3), BddAbove (hierarchyJetValues True d w F) ∧
          BddAbove (hierarchyJetValues True d w Fadj) ∧
          BddAbove (hierarchyJetValues True d w K) ∧
          BddAbove (hierarchyJetValues True d w Ω)) ∧
        (∀ n : ℕ,
          hierarchyFiniteWordNorm True d n F ≤ C n * D / Real.sqrt ℓ ∧
          hierarchyFiniteWordNorm True d n Fadj ≤ C n * D / Real.sqrt ℓ) ∧
        ∀ w : List (Fin 3), 0 < w.length →
          sSup (hierarchyJetValues True d w K) + sSup (hierarchyJetValues True d w Ω) ≤
            H w.length * D ^ 9 * Real.sqrt ℓ := by
  obtain ⟨J, hJ, hraw⟩ := exists_parentMeanCoefficientJetBounds R hR
  let C (n : ℕ) := 4 * ∑ w ∈ hierarchyAdmissibleWords (Fin 3) (n + 1), J w.length
  let H₀ (m : ℕ) := J m + Real.sqrt (2 * J m * J (m + 1))
  let H (m : ℕ) := 2 * H₀ m
  refine ⟨C, H, fun n => mul_nonneg (by norm_num) (Finset.sum_nonneg (fun w _ => hJ w.length)),
    fun m => mul_nonneg zero_le_two (add_nonneg (hJ m) (Real.sqrt_nonneg _)), ?_⟩
  intro U X T D ℓ hT hT₁ hD hℓ hscale hX hU hper hF hInv hVel F Fadj M K Ω d
  let I := Icc (0 : ℝ) T
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have h := hraw hT hT₁ hD hX hU hper hF hInv hVel
  have hFs (t : I) : ContDiff ℝ ∞ (F t) := (h t.val t.property).1
  have hFas (t : I) : ContDiff ℝ ∞ (Fadj t) := (h t.val t.property).2.1
  have hKs (t : I) : ContDiff ℝ ∞ (K t) := (h t.val t.property).2.2.1
  have hΩs (t : I) : ContDiff ℝ ∞ (Ω t) := (h t.val t.property).2.2.2.1
  have hFjet (m : ℕ) (t : I) (a : Vec3) :
      ‖iteratedFDeriv ℝ m (F t) a‖ ≤ J m * D ^ (6 * m + 1) :=
    ((h t.val t.property).2.2.2.2 m a).1.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by omega)) (hJ m))
  have hFajet (m : ℕ) (t : I) (a : Vec3) :
      ‖iteratedFDeriv ℝ m (Fadj t) a‖ ≤ J m * D ^ (6 * m + 1) :=
    ((h t.val t.property).2.2.2.2 m a).2.1.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by omega)) (hJ m))
  have hKjet (m : ℕ) (t : I) (a : Vec3) :
      ‖iteratedFDeriv ℝ m (K t) a‖ ≤ J m * D ^ (6 * m + 3) :=
    ((h t.val t.property).2.2.2.2 m a).2.2.1.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by omega)) (hJ m))
  have hΩjet (m : ℕ) (t : I) (a : Vec3) :
      ‖iteratedFDeriv ℝ m (Ω t) a‖ ≤ J m * D ^ (6 * m + 3) :=
    ((h t.val t.property).2.2.2.2 m a).2.2.2
  have hFinite {f : I → Vec3 → Coefficient} (hf : ∀ t, ContDiff ℝ ∞ (f t))
      (hjet : ∀ m t a, ‖iteratedFDeriv ℝ m (f t) a‖ ≤ J m * D ^ (6 * m + 1))
      (n : ℕ) : hierarchyFiniteWordNorm True d n f ≤ C n * D / Real.sqrt ℓ := by
    apply hierarchyFiniteWordNorm_holder_le_of_power hD hℓ hscale hD₀ hJ hf _ n
    intro m t a
    refine (hjet m t a).trans_eq ?_
    rw [pow_succ]
    ring
  have hBdd {f : I → Vec3 → Coefficient} (q : ℕ) (hf : ∀ t, ContDiff ℝ ∞ (f t))
      (hjet : ∀ m t a, ‖iteratedFDeriv ℝ m (f t) a‖ ≤ J m * D ^ (6 * m + q))
      (w : List (Fin 3)) : BddAbove (hierarchyJetValues True d w f) :=
    (hierarchyJetValues_true_label_bddAbove_csSup_le_of_iteratedFDeriv hℓ.le
      (mul_nonneg (hJ _) (pow_nonneg hD₀ _)) (mul_nonneg (hJ _) (pow_nonneg hD₀ _))
      hf w (hjet w.length) (hjet (w.length + 1))).1
  refine ⟨fun w => ⟨hBdd 1 hFs hFjet w, hBdd 1 hFas hFajet w,
    hBdd 3 hKs hKjet w, hBdd 3 hΩs hΩjet w⟩,
    fun n => ⟨hFinite hFs hFjet n, hFinite hFas hFajet n⟩, ?_⟩
  intro w hw
  have hK := (hierarchyJetValues_true_label_positive_bddAbove_csSup_le_of_iteratedFDeriv
    (p := 6) (q := 3) (C := J) hℓ.le hD hscale hKs w hw (hJ _) (hJ _)
    (hKjet w.length) (hKjet (w.length + 1))).2
  have hΩ := (hierarchyJetValues_true_label_positive_bddAbove_csSup_le_of_iteratedFDeriv
    (p := 6) (q := 3) (C := J) hℓ.le hD hscale hΩs w hw (hJ _) (hJ _)
    (hΩjet w.length) (hΩjet (w.length + 1))).2
  calc
    _ ≤ H₀ w.length * D ^ 9 * Real.sqrt ℓ + H₀ w.length * D ^ 9 * Real.sqrt ℓ :=
      add_le_add hK hΩ
    _ = _ := by dsimp only [H]; ring


/-- At unit label radius, the zeroth and first half-Hölder norms are
bounded by the power at order two. This bounds the coefficient input
to the low-order mean inverse. -/
theorem hierarchyFiniteWordNorm_unitLabelOrderOne_le_of_power
    {I G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {p q : ℕ} {D : ℝ} {C : ℕ → ℝ} {f : I → Vec3 → G} (hD : 1 ≤ D)
    (hC : ∀ m ≤ 2, 0 ≤ C m) (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hjet : ∀ m ≤ 2, ∀ t a, ‖iteratedFDeriv ℝ m (f t) a‖ ≤ C m * D ^ (p * m + q)) :
    hierarchyFiniteWordNorm True (hierarchyLabelDirection 1) 1 f ≤
      (4 * ∑ w ∈ hierarchyAdmissibleWords (Fin 3) 2, C w.length) * D ^ (p * 2 + q) := by
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hjet' (m : ℕ) (hm : m ≤ 2) (t : I) (a : Vec3) :
      ‖iteratedFDeriv ℝ m (f t) a‖ ≤ C m * D ^ (p * 2 + q) * (1 : ℝ) ^ (6 * m) := by
    rw [one_pow, mul_one]
    exact (hjet m hm t a).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hD (Nat.add_le_add_right (Nat.mul_le_mul_left p hm) q)) (hC m hm))
  obtain ⟨hbdd, hnorm⟩ := hierarchyFiniteWordNorm_false_label_le_of_iteratedFDeriv
    (D := 1) zero_le_one (by simp) (pow_nonneg hD₀ _) hf 2 hC hjet'
  calc
    _ ≤ 4 * hierarchyFiniteWordNorm False (hierarchyLabelDirection 1) 2 f := by
      simpa only [Real.sqrt_one, div_one] using
        hierarchyFiniteWordNorm_holder_le 1 zero_lt_one le_rfl 1 hf hbdd
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hnorm (by norm_num)

/-- A single polynomial radius restriction suffices both for the weighted
jet bound and for the mean coefficient threshold when the low-order inverse
constant is bounded by `B * D ^ a`. -/
theorem meanCoefficient_radius_conditions {A B D ℓ : ℝ} {a : ℕ}
    (hD : 1 ≤ D) (hB : 1 ≤ B) (hA : A ≤ B * D ^ a)
    (hr : ℓ ≤ ((B * D ^ (a + 9))⁻¹) ^ 2) :
    ℓ * D ^ 6 ≤ 1 ∧ A * D ^ 9 * Real.sqrt ℓ ≤ 1 := by
  let Q := B * D ^ (a + 9)
  have hQ : 1 ≤ Q := one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hD)
  have hQ₀ : 0 < Q := zero_lt_one.trans_le hQ
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hRadius : Real.sqrt ℓ ≤ Q⁻¹ :=
    (Real.sqrt_le_sqrt hr).trans_eq (Real.sqrt_sq (inv_nonneg.mpr hQ₀.le))
  have hscale : D ^ 6 ≤ Q := calc
    _ ≤ D ^ (a + 9) := pow_le_pow_right₀ hD (by omega)
    _ ≤ Q := le_mul_of_one_le_left (pow_nonneg hD₀ _) hB
  have hsq : Q ≤ Q ^ 2 := by
    simpa only [pow_one] using (pow_le_pow_right₀ hQ (show (1 : ℕ) ≤ 2 by decide))
  have hInverse : A * D ^ 9 ≤ Q := by
    calc
      _ ≤ (B * D ^ a) * D ^ 9 := mul_le_mul_of_nonneg_right hA (pow_nonneg hD₀ _)
      _ = Q := by dsimp only [Q]; rw [pow_add]; ring
  constructor
  · calc
      _ ≤ (Q⁻¹) ^ 2 * D ^ 6 := mul_le_mul_of_nonneg_right hr (pow_nonneg hD₀ _)
      _ ≤ (Q⁻¹) ^ 2 * Q ^ 2 := mul_le_mul_of_nonneg_left (hscale.trans hsq) (sq_nonneg _)
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hQ₀.ne', one_pow]
  · calc
      _ ≤ Q * Q⁻¹ :=
        mul_le_mul hInverse hRadius (Real.sqrt_nonneg _) hQ₀.le
      _ = 1 := mul_inv_cancel₀ hQ₀.ne'

end

end TorusEuler
