import TorusEuler.EndpointPhysicalMeanEstimate
import TorusEuler.TerminalTimeJet
import TorusEuler.TerminalMeanSpatialTimeCommutation
import TorusEuler.TerminalMeanTimeCalculus

/-! Read the time jets of the endpoint half-Hölder words on the Euclidean lift. -/

open Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)
local notation "Time(" T ")" => Icc (0 : ℝ) T
local notation "Lift(" T ")" => Set.prod (Time(T)) (univ : Set Vec3)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem scaled_torusWord_le_of_labelNorm {I : Type*} (ℓ : ℝ) (N : ℕ)
    (hℓ : 0 < ℓ) (hℓ₁ : ℓ ≤ 1) {f : I → Vec3 → E}
    (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hb : ∀ w ∈ hierarchyAdmissibleWords (Fin 3) (N + 1),
      BddAbove (hierarchyJetValues False (hierarchyLabelDirection ℓ) w f))
    (w : List (Fin 3)) (hw : w.length ≤ N) (t : I) (u : HalfHolder Labels E)
    (hLift : ∀ x, HalfHolder.eval (toUnitTorus x) u = spatialDerivativeWord w (f t) x) :
    ℓ ^ w.length * ‖u‖ ≤
      4 * hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) (N + 1) f / Real.sqrt ℓ := by
  let d := hierarchyLabelDirection ℓ
  let R := hierarchyFiniteWordNorm False d (N + 1) f
  have hR : 0 ≤ R := Finset.sum_nonneg (fun q hq => le_csSup (hb q hq) (Or.inl rfl))
  have hWord (q : List (Fin 3)) (hq : q.length ≤ N + 1) (x : Vec3) :
      ‖phaseOperatorWord d q (f t) x‖ ≤ R := by
    have hp : q.mergeSort.Perm q := List.mergeSort_perm _ _
    have hs : q.mergeSort ∈ hierarchyAdmissibleWords (Fin 3) (N + 1) :=
      mem_hierarchyAdmissibleWords.mpr ⟨hp.length_eq.trans_le hq, List.pairwise_mergeSort' _ _⟩
    have hEq : phaseOperatorWord d q.mergeSort (f t) = phaseOperatorWord d q (f t) :=
      phaseOperatorWord_constantDirections_perm (fun i => d i 0) (hf t) hp
    rw [← hEq]
    have hVal : ‖phaseOperatorWord d q.mergeSort (f t) x‖ ≤
        sSup (hierarchyJetValues False d q.mergeSort f) :=
      le_csSup (hb _ hs) (Or.inr (Or.inl ⟨t, x, rfl⟩))
    exact hVal.trans (Finset.single_le_sum
      (fun r hr => le_csSup (hb r hr) (Or.inl rfl)) hs)
  let g := phaseOperatorWord d w (f t)
  let G := ℓ ^ w.length • u
  have hG (x : Vec3) : HalfHolder.eval (toUnitTorus x) G = g x := by
    rw [map_smul, hLift]
    exact (phaseOperatorWord_hierarchyLabelDirection_eq_smul ℓ (hf t) w x).symm
  have hD (x : Vec3) (i : Fin 3) : ‖fderiv ℝ g x (coordinateDirection i)‖ ≤ R / ℓ := by
    have hs := hWord (i :: w) (by simp only [List.length_cons]; omega) x
    change ‖fderiv ℝ g x (ℓ • coordinateDirection i)‖ ≤ R at hs
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hℓ] at hs
    exact (le_div_iff₀ hℓ).2 (by simpa only [mul_comm] using hs)
  have hGradient (x : Vec3) : ‖fderiv ℝ g x‖ ≤ 3 * (R / ℓ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro z
    have hRep : ∑ i : Fin 3, (z i) • coordinateDirection i = z := by
      simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, coordinateDirection]
        using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr z
    have hLinear : fderiv ℝ g x z =
        ∑ i : Fin 3, (z i) • fderiv ℝ g x (coordinateDirection i) := by
      nth_rw 1 [← hRep]
      simp only [map_sum, map_smul]
    rw [hLinear]
    calc
      _ ≤ ∑ i : Fin 3, ‖(z i) • fderiv ℝ g x (coordinateDirection i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, ‖z‖ * (R / ℓ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul]
        exact mul_le_mul (PiLp.norm_apply_le z i) (hD x i) (norm_nonneg _) (norm_nonneg _)
      _ = (3 * (R / ℓ)) * ‖z‖ := by simp [mul_left_comm, mul_comm]
  have hg : Differentiable ℝ g :=
    (contDiff_phaseOperatorWord (fun _ => contDiff_const) (hf t) w).differentiable (by simp)
  have hLip (x y : Vec3) : ‖g x - g y‖ ≤ (3 * (R / ℓ)) * ‖x - y‖ :=
    (convex_univ : Convex ℝ (univ : Set Vec3)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hg z) (fun z _ => hGradient z) (mem_univ y) (mem_univ x)
  have hsg : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ
  have hs₁ : Real.sqrt ℓ ≤ 1 := by simpa using Real.sqrt_le_sqrt hℓ₁
  have hGnorm : ‖G‖ ≤ 4 * R / Real.sqrt ℓ := by
    apply (HalfHolder.norm_le_iff (by positivity)).mpr
    constructor
    · intro a
      obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
      change ‖HalfHolder.eval (toUnitTorus x) G‖ ≤ _
      rw [hG]
      apply (hWord w (hw.trans (Nat.le_succ _)) x).trans
      apply (le_div_iff₀ hsg).2
      exact (mul_le_of_le_one_right hR hs₁).trans (by linarith only [hR])
    · intro a b
      obtain ⟨x,y,hx,hy,hdist⟩ := holderBridge_exists_close_lifts a b
      change ‖HalfHolder.eval a G - HalfHolder.eval b G‖ ≤ _
      rw [← hx, ← hy, hG, hG, hx, hy]
      have hTwo : ‖g x - g y‖ ≤ 2 * R := by
        rw [two_mul]
        exact (norm_sub_le _ _).trans (add_le_add (hWord w (hw.trans (Nat.le_succ _)) x)
          (hWord w (hw.trans (Nat.le_succ _)) y))
      have hDist : ‖g x - g y‖ ≤ (6 * (R / ℓ)) * dist a b := by
        refine (hLip x y).trans ((mul_le_mul_of_nonneg_left hdist (by positivity)).trans_eq ?_)
        ring
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      calc
        ‖g x - g y‖ ^ 2 ≤ (2 * R) * ((6 * (R / ℓ)) * dist a b) := by
          rw [sq]
          exact mul_le_mul hTwo hDist (norm_nonneg _) (by positivity)
        _ ≤ (4 * R / Real.sqrt ℓ * Real.sqrt (dist a b)) ^ 2 := by
          rw [mul_pow, div_pow, Real.sq_sqrt hℓ.le, Real.sq_sqrt dist_nonneg]
          have hPow : (2 * R) * (6 * (R / ℓ)) ≤ (4 * R) ^ 2 / ℓ := by
            apply (le_div_iff₀ hℓ).2
            have heq : (2 * R) * (6 * (R / ℓ)) * ℓ = 12 * R ^ 2 := by
              field_simp
              ring
            rw [heq]
            nlinarith [sq_nonneg R]
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right hPow dist_nonneg
  simpa only [G, norm_smul, Real.norm_of_nonneg (pow_nonneg hℓ.le _)] using hGnorm

variable [CompleteSpace E]

/-- The time derivative of a recovered label word is the genuine spatial
word of the time derivative of its lift. -/
theorem EndpointSlabHalfHolderJets.eval_lift_terminalTimeJet {T : ℝ} (hT : 0 < T)
    {f : ℝ → Vec3 → E} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) Lift(T))
    (jet : EndpointSlabHalfHolderJets T coordinateDirection (Function.uncurry f))
    (i : ℕ) (w : List (Fin 3)) (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) :
    HalfHolder.eval (toUnitTorus x) (terminalTimeJet T i (jet.curve w) t) =
      spatialDerivativeWord w (slabTimeJet 0 T i f t) x := by
  apply eval_lift_recoveredSpatialWord (slabTimeJet_slice_smooth hT hf i ht)
    (fun q => terminalTimeJet T i (jet.curve q) t) ?_ ?_ w le_rfl x
  · intro y
    have hEq : EqOn (fun r => HalfHolder.eval (toUnitTorus y) (jet.curve [] r))
        (fun r => f r y) Time(T) := fun r hr => jet.eval_lift [] r hr y
    exact ((terminalIteratedDerivWithin_clm (uniqueDiffOn_Icc hT) (HalfHolder.eval (toUnitTorus y))
      (jet.smooth []) i ht).symm.trans (iteratedDerivWithin_congr hEq ht))
  · intro j q _
    exact terminalSpatialDerivative_iteratedDerivWithin hT (coordinateDirection j)
      ((jet.smooth q).of_le (by simp)) ((jet.smooth (j :: q)).of_le (by simp))
      (fun r hr => jet.spatialDerivative j q r hr) i le_rfl t ht

/-- Each actual half-Hölder time word is bounded by the unweighted label
norm at one higher order. The exponent loss in the radius is one half. -/
theorem EndpointSlabHalfHolderJets.mul_norm_terminalTimeJet_le_labelNorm {T ℓ : ℝ}
    (hT : 0 < T) (hℓ : 0 < ℓ) (hℓ₁ : ℓ ≤ 1) {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) Lift(T)) (hper : ∀ t ∈ Time(T), SpatiallyPeriodic (f t))
    (jet : EndpointSlabHalfHolderJets T coordinateDirection (Function.uncurry f))
    (N i : ℕ) (w : List (Fin 3)) (hw : w.length ≤ N) (t : ℝ) (ht : t ∈ Time(T)) :
    ℓ ^ w.length * ‖terminalTimeJet T i (jet.curve w) t‖ ≤
      4 * hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) (N + 1)
        (fun r : Time(T) => slabTimeJet 0 T i f r) / Real.sqrt ℓ := by
  apply scaled_torusWord_le_of_labelNorm ℓ N hℓ hℓ₁
    (fun r : Time(T) => slabTimeJet_slice_smooth hT hf i r.property) ?_ w hw ⟨t,ht⟩
    (terminalTimeJet T i (jet.curve w) t) (jet.eval_lift_terminalTimeJet hT hf i w t ht)
  intro q _
  exact (bddAbove_endpointLabelWord_of_smooth_periodic hT hℓ.le (slabTimeJet_smooth hT hf i)
    (fun r hr => slabTimeJet_periodic hper i hr) q).1

/-- A fixed slope in the raw spatial jets leaves one absolute parent power
in the weighted half-Hölder norm of each time word. -/
theorem EndpointSlabHalfHolderJets.mul_norm_terminalTimeJet_le_rawJets
    {T ℓ D A : ℝ} (hT : 0 < T) (hℓ : 0 < ℓ) (hD : 1 ≤ D) (hA : 0 ≤ A)
    {f : ℝ → Vec3 → E} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) Lift(T))
    (jet : EndpointSlabHalfHolderJets T coordinateDirection (Function.uncurry f))
    (p i : ℕ) (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n) (hScale : ℓ * D ^ p ≤ 1)
    (hRaw : ∀ n t, t ∈ Time(T) → ∀ x,
      ‖iteratedFDeriv ℝ n (slabTimeJet 0 T i f t) x‖ ≤ C n * A * D ^ (p * n))
    (w : List (Fin 3)) (t : ℝ) (ht : t ∈ Time(T)) :
    ℓ ^ w.length * ‖terminalTimeJet T i (jet.curve w) t‖ ≤
      6 * (C w.length + C (w.length + 1)) * A * D ^ p := by
  let n := w.length
  let M := (C n + C (n + 1)) * A * D ^ (p * (n + 1))
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg (add_nonneg (hC n) (hC (n + 1))) hA) (pow_nonneg hD₀ _)
  let g := fun r : Time(T) => slabTimeJet 0 T i f r
  have hg (r : Time(T)) : ContDiff ℝ ∞ (g r) := slabTimeJet_slice_smooth hT hf i r.property
  have hZero (r : Time(T)) (x : Vec3) : ‖iteratedFDeriv ℝ n (g r) x‖ ≤ M :=
    (hRaw n r r.property x).trans (mul_le_mul
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hC (n + 1))) hA)
      (pow_le_pow_right₀ hD (Nat.mul_le_mul_left p (Nat.le_succ n)))
      (pow_nonneg hD₀ _) (mul_nonneg (add_nonneg (hC n) (hC (n + 1))) hA))
  have hOne (r : Time(T)) (x : Vec3) : ‖iteratedFDeriv ℝ (n + 1) (g r) x‖ ≤ M :=
    (hRaw (n + 1) r r.property x).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hC n)) hA) (pow_nonneg hD₀ _))
  obtain ⟨hbdd, hSup⟩ := hierarchyJetValues_true_label_bddAbove_csSup_le_of_iteratedFDeriv
    hℓ.le hM hM hg w hZero hOne
  have hJet := mul_norm_halfHolder_le_of_hierarchyLabelWord hℓ.le w (⟨t,ht⟩ : Time(T))
    (hg ⟨t,ht⟩) hbdd _ (jet.eval_lift_terminalTimeJet hT hf i w t ht)
  have hSqrtM : Real.sqrt (2 * M * M) ≤ 2 * M := by
    apply (Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩)
    nlinarith only [sq_nonneg M]
  have hSqrt : Real.sqrt (2 : ℝ) ≤ 2 := Real.sqrt_le_iff.mpr (by norm_num)
  have hWeighted : ℓ ^ n * M ≤ (C n + C (n + 1)) * A * D ^ p := by
    calc
      _ = (ℓ * D ^ p) ^ n * ((C n + C (n + 1)) * A * D ^ p) := by
        dsimp only [M]
        rw [Nat.mul_succ, pow_add, mul_pow, ← pow_mul]
        ring
      _ ≤ _ := mul_le_of_le_one_left
        (mul_nonneg (mul_nonneg (add_nonneg (hC n) (hC (n + 1))) hA) (pow_nonneg hD₀ _))
        (pow_le_one₀ (mul_nonneg hℓ.le (pow_nonneg hD₀ _)) hScale)
  calc
    _ ≤ Real.sqrt 2 * (ℓ ^ n * (M + Real.sqrt (2 * M * M))) :=
      hJet.trans (mul_le_mul_of_nonneg_left hSup (Real.sqrt_nonneg _))
    _ ≤ 2 * (ℓ ^ n * (3 * M)) :=
      mul_le_mul hSqrt (mul_le_mul_of_nonneg_left (by linarith only [hSqrtM]) (pow_nonneg hℓ.le _))
        (by positivity) zero_le_two
    _ = 6 * (ℓ ^ n * M) := by ring
    _ ≤ 6 * ((C n + C (n + 1)) * A * D ^ p) :=
      mul_le_mul_of_nonneg_left hWeighted (by norm_num)
    _ = _ := by simp only [n]; ring

/-- The actual half-Hölder time word bounds control the finite unweighted
label norm of the time-differentiated lift. -/
theorem EndpointSlabHalfHolderJets.slabTimeJet_labelNorm_le_of_wordCap
    {T ℓ C : ℝ} (hT : 0 < T) {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) Lift(T))
    (jet : EndpointSlabHalfHolderJets T coordinateDirection (Function.uncurry f))
    (hℓ : 0 ≤ ℓ) (n i : ℕ) (hC : 0 ≤ C)
    (hWords : ∀ w, w.length ≤ n → ∀ t ∈ Time(T),
      ℓ ^ w.length * ‖terminalTimeJet T i (jet.curve w) t‖ ≤ C) :
    hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) n
        (fun r : Time(T) => slabTimeJet 0 T i f r) ≤
      ((hierarchyAdmissibleWords (Fin 3) n).card : ℝ) * C := by
  let g := fun r : Time(T) => slabTimeJet 0 T i f r
  unfold hierarchyFiniteWordNorm
  calc
    _ ≤ ∑ _w ∈ hierarchyAdmissibleWords (Fin 3) n, C := by
      apply Finset.sum_le_sum
      intro w hw
      apply csSup_le (show (hierarchyJetValues False (hierarchyLabelDirection ℓ) w g).Nonempty from
        ⟨0, Or.inl rfl⟩)
      rintro r (rfl | hval | ⟨hFalse, _, _, _, _⟩)
      · exact hC
      · obtain ⟨t, x, rfl⟩ := hval
        have hg : ContDiff ℝ ∞ (g t) := slabTimeJet_slice_smooth hT hf i t.property
        rw [phaseOperatorWord_hierarchyLabelDirection_eq_smul ℓ hg,
          ← jet.eval_lift_terminalTimeJet hT hf i w t t.property x,
          norm_smul, Real.norm_of_nonneg (pow_nonneg hℓ _)]
        let u := terminalTimeJet T i (jet.curve w) t
        have hval : ‖HalfHolder.eval (toUnitTorus x) u‖ ≤ ‖u‖ :=
          ((HalfHolder.norm_le_iff (norm_nonneg u)).mp le_rfl).1 _
        exact (mul_le_mul_of_nonneg_left hval (pow_nonneg hℓ _)).trans
          (hWords w (mem_hierarchyAdmissibleWords.mp hw).1 t t.property)
      · exact hFalse.elim
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

end

end TorusEuler
