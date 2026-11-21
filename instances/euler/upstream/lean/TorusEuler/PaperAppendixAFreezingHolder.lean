import TorusEuler.PaperAppendixAFreezing
import TorusEuler.EndpointJointWordRegularity
import TorusEuler.PeriodicLerayHigherJets
import TorusEuler.PhaseJetBounds

/-! The higher freezing inverse in the usual lifted spatial Hölder spaces. -/

open MeasureTheory Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def holderLift (f : HalfHolder A E) : Vec3 → E :=
  fun x => HalfHolder.eval (toUnitTorus x) f

private theorem periodic_holderLift (f : HalfHolder A E) : SpatiallyPeriodic (holderLift f) := by
  intro k x
  unfold holderLift
  rw [(toUnitTorus_eq_iff _ _).mpr ⟨k, rfl⟩]

private theorem fderiv_is_periodic {f : Vec3 → E} (h : SpatiallyPeriodic f) :
    SpatiallyPeriodic (fderiv ℝ f) := by
  intro k x
  rw [← fderiv_comp_add_right]
  exact congrArg (fun g : Vec3 → E => fderiv ℝ g x) (funext (h k))

private theorem periodic_coordinateWord {f : Vec3 → E} (hf : SpatiallyPeriodic f)
    (l : List (Fin 3)) : SpatiallyPeriodic (spatialDerivativeWord l f) := by
  induction l with
  | nil => exact hf
  | cons i l ih =>
    intro k x
    change (fderiv ℝ (spatialDerivativeWord l f) (x + latticeVector k)) (coordinateDirection i) =
      (fderiv ℝ (spatialDerivativeWord l f) x) (coordinateDirection i)
    rw [fderiv_is_periodic ih k x]

private theorem spatialHolderHalf_coordinateWord {f : Vec3 → E} {n : ℕ}
    (hf : SpatialHolderHalf n f) (l : List (Fin 3)) (hl : l.length ≤ n) :
    SpatialHolderHalf (n - l.length) (spatialDerivativeWord l f) ∧
      spatialHolderHalfNorm (n - l.length) (spatialDerivativeWord l f) ≤ spatialHolderHalfNorm n f := by
  induction l with
  | nil => exact ⟨hf, le_rfl⟩
  | cons i l ih =>
    have hPrev := ih (by simp only [List.length_cons] at hl; omega)
    have horder : n - l.length = (n - (i :: l).length) + 1 := by
      simp only [List.length_cons] at *
      omega
    rw [horder] at hPrev
    let L := ContinuousLinearMap.apply ℝ E (coordinateDirection i)
    have hL : ‖L‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro g
      have hg := g.le_opNorm (coordinateDirection i)
      simpa only [L, ContinuousLinearMap.apply_apply, coordinateDirection, PiLp.norm_single,
        norm_one, mul_one, one_mul] using hg
    have h := spatialHolderHalf_contraction_fderiv L hPrev.1
    have hNorm := nonneg_spatialHolderHalfNorm _ _ hPrev.1
    exact ⟨h.1, h.2.trans ((mul_le_of_le_one_left hNorm hL).trans hPrev.2)⟩

/-- All coordinate words through a given order descend with their half-Hölder
norm bounded by the ordinary Fréchet-derivative norm. -/
theorem exists_halfHolderWords_norm_le {f : HalfHolder A E} {n : ℕ}
    (hf : SpatialHolderHalf n (fun x => HalfHolder.eval (toUnitTorus x) f)) :
    ∃ w : List (Fin 3) → HalfHolder A E, w [] = f ∧
      (∀ (i : Fin 3) l, l.length < n →
        endpointTorusHasSpatialDerivative (coordinateDirection i) (w l) (w (i :: l))) ∧
      ∀ l, l.length ≤ n → ‖w l‖ ≤ Real.sqrt 2 *
        spatialHolderHalfNorm n (fun x => HalfHolder.eval (toUnitTorus x) f) := by
  classical
  have hDesc (w : List (Fin 3)) (hw : w.length ≤ n) :
      ∃ v : HalfHolder A E, holderLift v = spatialDerivativeWord w (holderLift f) ∧
        ‖v‖ ≤ Real.sqrt 2 * spatialHolderHalfNorm n (holderLift f) := by
    have hg := spatialHolderHalf_coordinateWord hf w hw
    have hg0 : SpatialHolderHalf 0 (spatialDerivativeWord w (holderLift f)) :=
      ⟨hg.1.1.of_le (by simp), fun j hj => hg.1.2 j (hj.trans (Nat.zero_le _))⟩
    have hNorm0 : spatialHolderHalfNorm 0 (spatialDerivativeWord w (holderLift f)) ≤
        spatialHolderHalfNorm (n - w.length) (spatialDerivativeWord w (holderLift f)) := by
      generalize n - w.length = m at hg ⊢
      cases m with
      | zero => exact le_rfl
      | succ m =>
        rw [spatialHolderHalfNorm_succ_eq]
        exact le_add_of_nonneg_right (nonneg_spatialHolderHalfNorm _ _
          ((spatialHolderHalf_succ_iff m _).1 hg.1).2.2)
    obtain ⟨v, hEval, hv⟩ := exists_halfHolder_of_spatialHolderHalf_zero
      (periodic_coordinateWord (periodic_holderLift f) w) hg0
    exact ⟨v, funext hEval, hv.trans (mul_le_mul_of_nonneg_left (hNorm0.trans hg.2) (Real.sqrt_nonneg _))⟩
  choose F hF using hDesc
  let F' (w : List (Fin 3)) : HalfHolder A E := if hw : w.length ≤ n then F w hw else 0
  have hEval (w : List (Fin 3)) (hw : w.length ≤ n) :
      holderLift (F' w) = spatialDerivativeWord w (holderLift f) := by
    simpa only [F', dite_eq_left hw] using (hF w hw).1
  refine ⟨F', ?_, ?_, ?_⟩
  · apply HalfHolder.ext
    intro y
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective y
    simpa only [holderLift, spatialDerivativeWord, phaseOperatorWord] using
      congrFun (hEval [] (Nat.zero_le _)) x
  · intro i w hw a s
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    have hwl : w.length ≤ n := hw.le
    have hil : (i :: w).length ≤ n := by simp only [List.length_cons]; omega
    let g := spatialDerivativeWord w (holderLift f)
    have hg := (spatialHolderHalf_coordinateWord hf w hwl).1.1
    have hgDiff : Differentiable ℝ g := hg.differentiable (by
      have hn : n - w.length ≠ 0 := by omega
      exact_mod_cast hn)
    have hline : HasDerivAt (fun r : ℝ => x + r • coordinateDirection i)
        (coordinateDirection i) s := by
      simpa only [Pi.add_def, id_eq, zero_add, one_smul] using
        (hasDerivAt_const s x).add ((hasDerivAt_id s).smul_const (coordinateDirection i))
    have h := (hgDiff (x + s • coordinateDirection i)).hasFDerivAt.comp_hasDerivAt s hline
    have hs (r : ℝ) :
        HalfHolder.eval (toUnitTorus x + toUnitTorus (r • coordinateDirection i)) (F' w) =
          g (x + r • coordinateDirection i) := by
      rw [← toUnitTorus_add]
      exact congrFun (hEval w hwl) _
    rw [show (fun r : ℝ => HalfHolder.eval (toUnitTorus x + toUnitTorus (r • coordinateDirection i))
      (F' w)) = (fun r : ℝ => g (x + r • coordinateDirection i)) from funext hs, ← toUnitTorus_add]
    change HasDerivAt (fun r : ℝ => g (x + r • coordinateDirection i))
      (holderLift (F' (i :: w)) (x + s • coordinateDirection i)) s
    rw [congrFun (hEval (i :: w) hil) (x + s • coordinateDirection i)]
    exact h
  · intro w hw
    change ‖F' w‖ ≤ Real.sqrt 2 * spatialHolderHalfNorm n (holderLift f)
    simpa only [F', dite_eq_left hw] using (hF w hw).2

private theorem spatialHolderHalf_to_words {f : HalfHolder A E} {n : ℕ}
    (hf : SpatialHolderHalf n (holderLift f)) : HasSpatialHolderWords n f := by
  obtain ⟨w, hBase, hD, _⟩ := exists_halfHolderWords_norm_le hf
  exact ⟨w, hBase, hD⟩

private theorem spatialHolderWords_to_holder {f : HalfHolder A E} {n : ℕ}
    (hf : HasSpatialHolderWords n f) : SpatialHolderHalf n (holderLift f) := by
  induction n generalizing f with
  | zero => exact (spatialHolderHalf_zero_of_halfHolder f).1
  | succ n ih =>
    obtain ⟨w, hw₀, hw⟩ := hf
    let d (i : Fin 3) := w [i]
    have hd (i : Fin 3) :
        endpointTorusHasSpatialDerivative (EuclideanSpace.single i (1 : ℝ)) f (d i) := by
      simpa only [coordinateDirection, List.length_nil, hw₀, d] using hw i [] (Nat.zero_lt_succ n)
    have hdwords (i : Fin 3) : HasSpatialHolderWords n (d i) := by
      refine ⟨fun l => w (l ++ [i]), rfl, fun j l hl => ?_⟩
      exact hw j (l ++ [i]) (by simp only [List.length_append, List.length_singleton]; omega)
    let L (i : Fin 3) : E →L[ℝ] (Vec3 →L[ℝ] E) :=
      ContinuousLinearMap.smulRightL ℝ Vec3 E (EuclideanSpace.proj i)
    have hDiff (x : Vec3) :
        HasFDerivAt (holderLift f) (∑ i : Fin 3, L i (holderLift (d i) x)) x :=
      HalfHolder.hasFDerivAt_lift_of_coordinateDerivatives hd x
    have hFDeriv : fderiv ℝ (holderLift f) = fun x => ∑ i : Fin 3, L i (holderLift (d i) x) :=
      funext fun x => (hDiff x).fderiv
    have hL (i : Fin 3) : SpatialHolderHalf n (L i ∘ holderLift (d i)) :=
      (spatialHolderHalf_comp_clm (L i) (ih (hdwords i))).1
    have hSum : SpatialHolderHalf n
        ((L 0 ∘ holderLift (d 0)) + (L 1 ∘ holderLift (d 1)) + (L 2 ∘ holderLift (d 2))) :=
      (spatialHolderHalf_add (spatialHolderHalf_add (hL 0) (hL 1)).1 (hL 2)).1
    refine (spatialHolderHalf_succ_iff n _).mpr
      ⟨fun x => (hDiff x).differentiableAt, (spatialHolderHalf_zero_of_halfHolder f).1, ?_⟩
    rw [hFDeriv]
    simp only [Fin.sum_univ_three]
    exact hSum

/-- Ordinary lifted spatial Hölder regularity is equivalent to the finite
coordinate-word formulation of the higher freezing inverse. -/
theorem hasSpatialHolderWords_iff_spatialHolderHalf (n : ℕ) (f : HalfHolder A E) :
    HasSpatialHolderWords n f ↔ SpatialHolderHalf n (fun x => HalfHolder.eval (toUnitTorus x) f) :=
  ⟨spatialHolderWords_to_holder, spatialHolderHalf_to_words⟩

/-- A common half-Hölder bound for the genuine coordinate derivatives bounds
the lifted Fréchet-derivative norm through the same order. -/
theorem exists_spatialHolderHalfNorm_le_of_word_bounds (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : List (Fin 3) → HalfHolder A E) (K : ℝ), 0 ≤ K →
      (∀ (i : Fin 3) l, l.length < n →
        endpointTorusHasSpatialDerivative (coordinateDirection i) (w l) (w (i :: l))) →
      (∀ l, l.length ≤ n → ‖w l‖ ≤ K) →
      spatialHolderHalfNorm n (fun x => HalfHolder.eval (toUnitTorus x) (w [])) ≤ C * K := by
  induction n with
  | zero =>
    refine ⟨2, by norm_num, fun w K _ _ hW => ?_⟩
    exact (spatialHolderHalf_zero_of_halfHolder (w [])).2.trans
      (mul_le_mul_of_nonneg_left (hW [] (Nat.zero_le _)) (by norm_num))
  | succ n ih =>
    obtain ⟨C, hC, hInd⟩ := ih
    let L (i : Fin 3) : E →L[ℝ] (Vec3 →L[ℝ] E) :=
      ContinuousLinearMap.smulRightL ℝ Vec3 E (EuclideanSpace.proj i)
    let q : ℝ := 2 * (n + 1)
    let H : ℝ := q ^ 2 * (‖L 0‖ + ‖L 1‖ + ‖L 2‖) * C
    have hq : 1 ≤ q := by dsimp [q]; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hq₀ : 0 ≤ q := zero_le_one.trans hq
    refine ⟨2 + H, add_nonneg (by norm_num) (by dsimp [H]; positivity), ?_⟩
    intro w K hK hD hW
    let d (i : Fin 3) := w [i]
    have hd (i : Fin 3) :
        endpointTorusHasSpatialDerivative (EuclideanSpace.single i (1 : ℝ)) (w []) (d i) :=
      hD i [] (Nat.zero_lt_succ n)
    have hWord (i : Fin 3) : HasSpatialHolderWords n (d i) := by
      refine ⟨fun l => w (l ++ [i]), rfl, fun j l hl => ?_⟩
      exact hD j (l ++ [i]) (by simp only [List.length_append, List.length_singleton]; omega)
    have hNorm (i : Fin 3) : spatialHolderHalfNorm n (holderLift (d i)) ≤ C * K := by
      apply hInd (fun l => w (l ++ [i])) K hK
      · intro j l hl
        exact hD j (l ++ [i]) (by simp only [List.length_append, List.length_singleton]; omega)
      · intro l hl
        exact hW (l ++ [i]) (by simp only [List.length_append, List.length_singleton]; omega)
    have hDer : fderiv ℝ (holderLift (w [])) = fun x => ∑ i : Fin 3, L i (holderLift (d i) x) :=
      funext fun x => (HalfHolder.hasFDerivAt_lift_of_coordinateDerivatives hd x).fderiv
    let U (i : Fin 3) := L i ∘ holderLift (d i)
    have hU (i : Fin 3) := spatialHolderHalf_comp_clm (L i) (spatialHolderWords_to_holder (hWord i))
    have hUN (i : Fin 3) : spatialHolderHalfNorm n (U i) ≤ ‖L i‖ * (C * K) :=
      (hU i).2.trans (mul_le_mul_of_nonneg_left (hNorm i) (norm_nonneg _))
    have h01 := spatialHolderHalf_add (hU 0).1 (hU 1).1
    have h012 := spatialHolderHalf_add h01.1 (hU 2).1
    have hDnorm : spatialHolderHalfNorm n (fderiv ℝ (holderLift (w []))) ≤ H * K := by
      rw [hDer, show (fun x => ∑ i : Fin 3, L i (holderLift (d i) x)) = U 0 + U 1 + U 2 from
        funext (fun _ => Fin.sum_univ_three _)]
      calc
        _ ≤ q * (spatialHolderHalfNorm n (U 0 + U 1) + spatialHolderHalfNorm n (U 2)) := h012.2
        _ ≤ q * (q * (‖L 0‖ * (C * K) + ‖L 1‖ * (C * K)) + ‖L 2‖ * (C * K)) := by
          apply mul_le_mul_of_nonneg_left _ hq₀
          refine add_le_add (h01.2.trans ?_) (hUN 2)
          exact mul_le_mul_of_nonneg_left (add_le_add (hUN 0) (hUN 1)) hq₀
        _ ≤ q * (q * (‖L 0‖ * (C * K) + ‖L 1‖ * (C * K)) + q * (‖L 2‖ * (C * K))) := by
          have hLast : ‖L 2‖ * (C * K) ≤ q * (‖L 2‖ * (C * K)) :=
            le_mul_of_one_le_left (by positivity) hq
          exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hLast) hq₀
        _ = H * K := by dsimp [H]; ring
    change spatialHolderHalfNorm (n + 1) (holderLift (w [])) ≤ (2 + H) * K
    rw [spatialHolderHalfNorm_succ_eq, add_mul]
    exact add_le_add ((spatialHolderHalf_zero_of_halfHolder (w [])).2.trans
      (mul_le_mul_of_nonneg_left (hW [] (Nat.zero_le _)) (by norm_num))) hDnorm

/-- The Lipschitz input of the freezing estimate is supplied by the uniform
norm of the first lifted derivative. -/
theorem halfHolder_lipschitz_of_spatialHolderHalf_one (f : HalfHolder A E)
    (hf : SpatialHolderHalf 1 (fun x => HalfHolder.eval (toUnitTorus x) f)) :
    0 ≤ spatialSupNorm (fderiv ℝ (fun x => HalfHolder.eval (toUnitTorus x) f)) ∧
      ∀ a b, ‖HalfHolder.eval a f - HalfHolder.eval b f‖ ≤
        2 * spatialSupNorm (fderiv ℝ (fun x => HalfHolder.eval (toUnitTorus x) f)) * dist a b := by
  let g := holderLift f
  let M := spatialSupNorm (fderiv ℝ g)
  have hD := ((spatialHolderHalf_zero_iff _).1 ((spatialHolderHalf_one_iff g).1 hf).2.2).2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (norm_le_spatialSupNorm hD 0)
  refine ⟨hM, fun a b => ?_⟩
  obtain ⟨x, y, hx, hy, hxy⟩ := holderBridge_exists_close_lifts a b
  rw [← hx, ← hy]
  change ‖g x - g y‖ ≤ 2 * M * dist (toUnitTorus x) (toUnitTorus y)
  have hLip := (convex_univ : Convex ℝ (univ : Set Vec3)).norm_image_sub_le_of_norm_fderiv_le
    (fun u _ => hf.1.differentiable_one u) (fun u _ => norm_le_spatialSupNorm hD u)
    (mem_univ y) (mem_univ x)
  rw [hx, hy]
  exact hLip.trans ((mul_le_mul_of_nonneg_left hxy hM).trans_eq (by ring))

local notation "Paths" => Lp Vec3 2 (volume.restrict (Ioc (0 : ℝ) 1))
local notation "P" => endpointStrongSpatialLeray
local notation "Q" => endpointStrongMixedLeray 1

private theorem freezingScale_of_derivative_bound {C μ S M V : ℝ}
    (hC : 0 ≤ C) (hμ : 0 < μ) (hS : 0 ≤ S) (hM : 0 ≤ M) (hV : 0 ≤ V) :
    C * (2 + μ⁻¹ + S + 2 * M) ^ (145 : ℕ) * V ≤
      (C * 2 ^ (145 : ℕ)) * (2 + μ⁻¹ + (S + M)) ^ (145 : ℕ) * V := by
  have hBase : 2 + μ⁻¹ + S + 2 * M ≤ 2 * (2 + μ⁻¹ + (S + M)) := by
    linarith only [inv_nonneg.mpr hμ.le, hS]
  have hp := pow_le_pow_left₀ (by positivity) hBase 145
  rw [mul_pow] at hp
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) hV

/-- Spatial freezing with the coefficient hypotheses and the `C¹` norm of Lemma A.2. -/
theorem paperLemmaA2_spatial_holder :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : HalfHolder A (Vec3 →L[ℝ] Vec3)) {μ : ℝ},
      0 < μ → SpatialHolderHalf 1 (fun x => HalfHolder.eval (toUnitTorus x) B) →
      (∀ a w, μ * ‖w‖ ^ 2 ≤ ⟪HalfHolder.eval a B w, w⟫_ℝ) →
      ∃ e : freezingFixedSpace P ≃L[ℝ] freezingFixedSpace P,
        (e : freezingFixedSpace P →L[ℝ] freezingFixedSpace P) =
          freezingCompression P B.coefficientMul endpointStrongSpatialLeray_idempotent ∧
        ∀ v : freezingFixedSpace P, ‖v‖ ≤ C * (2 + μ⁻¹ +
          (‖B.val.1‖ + spatialSupNorm (fderiv ℝ (fun x => HalfHolder.eval (toUnitTorus x) B)))) ^
            (145 : ℕ) * ‖e v‖ := by
  obtain ⟨C, hC, hInv⟩ := paperLemmaA2_spatial
  refine ⟨C * 2 ^ (145 : ℕ), by positivity, ?_⟩
  intro B μ hμ hB hCoercive
  obtain ⟨hM, hLip⟩ := halfHolder_lipschitz_of_spatialHolderHalf_one B hB
  obtain ⟨e, he, heBound⟩ := hInv B hμ (mul_nonneg (by norm_num) hM) hLip hCoercive
  exact ⟨e, he, fun v => (heBound v).trans
    (freezingScale_of_derivative_bound hC hμ (norm_nonneg _) hM (norm_nonneg _))⟩

set_option maxHeartbeats 20000000 in
/-- Time-path freezing with the coefficient hypotheses and the `C¹` norm of Lemma A.2. -/
theorem paperLemmaA2_mixed_holder :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : HalfHolder A (Paths →L[ℝ] Paths)) {μ : ℝ},
      0 < μ → SpatialHolderHalf 1 (fun x => HalfHolder.eval (toUnitTorus x) B) →
      (∀ a w, endpointIntegral 1 w = 0 → μ * ‖w‖ ^ 2 ≤ ⟪HalfHolder.eval a B w, w⟫_ℝ) →
      ∃ e : freezingFixedSpace Q ≃L[ℝ] freezingFixedSpace Q,
        (e : freezingFixedSpace Q →L[ℝ] freezingFixedSpace Q) =
          freezingCompression Q B.coefficientMul (endpointStrongMixedLeray_idempotent zero_lt_one) ∧
        ∀ v : freezingFixedSpace Q, ‖v‖ ≤ C * (2 + μ⁻¹ +
          (‖B.val.1‖ + spatialSupNorm (fderiv ℝ (fun x => HalfHolder.eval (toUnitTorus x) B)))) ^
            (145 : ℕ) * ‖e v‖ := by
  obtain ⟨C, hC, hInv⟩ := paperLemmaA2_mixed
  refine ⟨C * 2 ^ (145 : ℕ), by positivity, ?_⟩
  intro B μ hμ hB hCoercive
  obtain ⟨hM, hLip⟩ := halfHolder_lipschitz_of_spatialHolderHalf_one B hB
  let M := spatialSupNorm (fderiv ℝ (fun x => HalfHolder.eval (toUnitTorus x) B))
  obtain ⟨e, he, heBound⟩ := hInv B (L := 2 * M) hμ (mul_nonneg (by norm_num) hM) hLip hCoercive
  refine ⟨e, he, fun v => (heBound v).trans ?_⟩
  exact freezingScale_of_derivative_bound (S := ‖B.val.1‖) (M := M) (V := ‖e v‖)
    hC hμ (norm_nonneg _) hM (norm_nonneg _)

/-- The spatial freezing inverse preserves the ordinary lifted Hölder spaces. -/
theorem paperLemmaA2_spatial_holder_higher {μ L : ℝ} (hμ : 0 < μ) (hL : 0 ≤ L)
    (B : HalfHolder A (Vec3 →L[ℝ] Vec3))
    (hLip : ∀ a b, ‖HalfHolder.eval a B - HalfHolder.eval b B‖ ≤ L * dist a b)
    (hCoercive : ∀ a w, μ * ‖w‖ ^ 2 ≤ ⟪HalfHolder.eval a B w, w⟫_ℝ)
    (n : ℕ) (hB : SpatialHolderHalf n (fun x => HalfHolder.eval (toUnitTorus x) B))
    (f : freezingFixedSpace P) (hf : SpatialHolderHalf n (fun x => HalfHolder.eval (toUnitTorus x) f.val)) :
    ∃! v : freezingFixedSpace P, P (B.coefficientMul v.val) = f.val ∧
      SpatialHolderHalf n (fun x => HalfHolder.eval (toUnitTorus x) v.val) := by
  simpa only [hasSpatialHolderWords_iff_spatialHolderHalf] using
    paperLemmaA2_spatial_higher hμ hL B hLip hCoercive n
      ((hasSpatialHolderWords_iff_spatialHolderHalf n B).mpr hB) f
      ((hasSpatialHolderWords_iff_spatialHolderHalf n f.val).mpr hf)

/-- The time-path freezing inverse preserves the same lifted Hölder spaces. -/
theorem paperLemmaA2_mixed_holder_higher {μ L : ℝ} (hμ : 0 < μ) (hL : 0 ≤ L)
    (B : HalfHolder A (Paths →L[ℝ] Paths))
    (hLip : ∀ a b, ‖HalfHolder.eval a B - HalfHolder.eval b B‖ ≤ L * dist a b)
    (hCoercive : ∀ a w, endpointIntegral 1 w = 0 → μ * ‖w‖ ^ 2 ≤ ⟪HalfHolder.eval a B w, w⟫_ℝ)
    (n : ℕ) (hB : SpatialHolderHalf n (fun x => HalfHolder.eval (toUnitTorus x) B))
    (f : freezingFixedSpace Q) (hf : SpatialHolderHalf n (fun x => HalfHolder.eval (toUnitTorus x) f.val)) :
    ∃! v : freezingFixedSpace Q, Q (B.coefficientMul v.val) = f.val ∧
      SpatialHolderHalf n (fun x => HalfHolder.eval (toUnitTorus x) v.val) := by
  simpa only [hasSpatialHolderWords_iff_spatialHolderHalf] using
    paperLemmaA2_mixed_higher hμ hL B hLip hCoercive n
      ((hasSpatialHolderWords_iff_spatialHolderHalf n B).mpr hB) f
      ((hasSpatialHolderWords_iff_spatialHolderHalf n f.val).mpr hf)

private theorem spatialHolderHalf_compressedCoefficient
    (proj : HalfHolder A E →L[ℝ] HalfHolder A E) (hProj : CommutesTorusLineDerivatives proj)
    (n : ℕ) {B : HalfHolder A (E →L[ℝ] E)} {v : HalfHolder A E}
    (hB : SpatialHolderHalf n (holderLift B)) (hv : SpatialHolderHalf n (holderLift v)) :
    SpatialHolderHalf n (holderLift (proj (B.coefficientMul v))) := by
  have hMul : SpatialHolderHalf n (holderLift (B.coefficientMul v)) := by
    have heq : holderLift (B.coefficientMul v) = fun x => holderLift B x (holderLift v x) := by
      funext x
      exact HalfHolder.eval_coefficientMul B v (toUnitTorus x)
    rw [heq]
    exact (spatialHolderHalf_bilinear (ContinuousLinearMap.apply ℝ E (E := E)).flip hB hv).1
  have hMul0 : SpatialHolderHalf 0 (holderLift (B.coefficientMul v)) :=
    (spatialHolderHalf_zero_of_halfHolder (B.coefficientMul v)).1
  have hp := periodic_holderLift (B.coefficientMul v)
  have h := (spatialHolderHalf_halfHolderProjectionLift n proj hProj hp hMul).1
  rw [halfHolderProjectionLift_eq_of_descent proj hp hMul0 (B.coefficientMul v) (fun _ => rfl)] at h
  exact h

private theorem freezingHolderHalf_one_of_succ {f : HalfHolder A E} {n : ℕ}
    (hf : SpatialHolderHalf (n + 1) (holderLift f)) : SpatialHolderHalf 1 (holderLift f) := by
  refine ⟨hf.1.of_le ?_, fun j hj => hf.2 j (hj.trans (by omega))⟩
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

/-- The compressed spatial map on the order-zero space restricts to a bijection
on every positive-order spatial Hölder class: the same map preserves the class,
and each datum in it has a unique preimage in it. -/
theorem paperLemmaA2_spatial_holder_restriction {μ : ℝ} (hμ : 0 < μ)
    (B : HalfHolder A (Vec3 →L[ℝ] Vec3))
    (hCoercive : ∀ a w, μ * ‖w‖ ^ 2 ≤ ⟪HalfHolder.eval a B w, w⟫_ℝ)
    (n : ℕ) (hB : SpatialHolderHalf (n + 1) (fun x => HalfHolder.eval (toUnitTorus x) B)) :
    (∀ v : freezingFixedSpace P, SpatialHolderHalf (n + 1) (fun x => HalfHolder.eval (toUnitTorus x) v.val) →
      SpatialHolderHalf (n + 1) (fun x => HalfHolder.eval (toUnitTorus x) (P (B.coefficientMul v.val)))) ∧
    ∀ f : freezingFixedSpace P,
      SpatialHolderHalf (n + 1) (fun x => HalfHolder.eval (toUnitTorus x) f.val) →
      ∃! v : freezingFixedSpace P, P (B.coefficientMul v.val) = f.val ∧
        SpatialHolderHalf (n + 1) (fun x => HalfHolder.eval (toUnitTorus x) v.val) := by
  constructor
  · exact fun _ => spatialHolderHalf_compressedCoefficient P
      endpointStrongSpatialLeray_preserves_torusDirectionalDerivative _ hB
  · obtain ⟨hM, hLip⟩ :=
      halfHolder_lipschitz_of_spatialHolderHalf_one B (freezingHolderHalf_one_of_succ hB)
    exact paperLemmaA2_spatial_holder_higher hμ (mul_nonneg (by norm_num) hM) B hLip hCoercive _ hB

/-- The analogous higher Hölder restriction of the compressed time-path map. -/
theorem paperLemmaA2_mixed_holder_restriction {μ : ℝ} (hμ : 0 < μ)
    (B : HalfHolder A (Paths →L[ℝ] Paths))
    (hCoercive : ∀ a w, endpointIntegral 1 w = 0 → μ * ‖w‖ ^ 2 ≤ ⟪HalfHolder.eval a B w, w⟫_ℝ)
    (n : ℕ) (hB : SpatialHolderHalf (n + 1) (fun x => HalfHolder.eval (toUnitTorus x) B)) :
    (∀ v : freezingFixedSpace Q, SpatialHolderHalf (n + 1) (fun x => HalfHolder.eval (toUnitTorus x) v.val) →
      SpatialHolderHalf (n + 1) (fun x => HalfHolder.eval (toUnitTorus x) (Q (B.coefficientMul v.val)))) ∧
    ∀ f : freezingFixedSpace Q,
      SpatialHolderHalf (n + 1) (fun x => HalfHolder.eval (toUnitTorus x) f.val) →
      ∃! v : freezingFixedSpace Q, Q (B.coefficientMul v.val) = f.val ∧
        SpatialHolderHalf (n + 1) (fun x => HalfHolder.eval (toUnitTorus x) v.val) := by
  have hComm : CommutesTorusLineDerivatives Q := by
    intro u f df hf
    exact freezingProjection_preserves_torusDirectionalDerivative_of_haar_bound Q 1 zero_le_one
      (fun z => by simpa only [one_mul] using endpointStrongMixedLeray_haar_norm_le zero_lt_one z)
      u (fun h z => endpointStrongMixedLeray_torusTranslate 1 (toUnitTorus (h • u)) z) f df hf
  constructor
  · exact fun _ => spatialHolderHalf_compressedCoefficient Q hComm _ hB
  · obtain ⟨hM, hLip⟩ :=
      halfHolder_lipschitz_of_spatialHolderHalf_one B (freezingHolderHalf_one_of_succ hB)
    exact paperLemmaA2_mixed_holder_higher hμ (mul_nonneg (by norm_num) hM) B hLip hCoercive _ hB

end

end TorusEuler
