import TorusEuler.CutoffResidual
import TorusEuler.TruncatedParentAdmissibility
import TorusEuler.FrequencyLattice
import TorusEuler.InductionBudget
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! The spatial norm estimates for the projected residual (5.58) in Proposition 5.11. -/

open Set UnitAddTorus
open scoped ContDiff SchwartzMap

namespace TorusEuler

noncomputable section

section HolderCalculus

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem spatialLevel_nonneg {f : Vec3 → E} {m j : ℕ}
    (hf : SpatialHolderHalf m f) (hj : j ≤ m) :
    0 ≤ spatialSupNorm (iteratedFDeriv ℝ j f) +
      spatialHolderHalfSeminorm (iteratedFDeriv ℝ j f) := by
  apply add_nonneg
  · exact (norm_nonneg _).trans (norm_le_spatialSupNorm (hf.2 j hj).1 0)
  · have h := le_ciSup (hf.2 j hj).2 ((0 : Vec3), (0 : Vec3))
    rw [show spatialHolderHalfQuotient (iteratedFDeriv ℝ j f) (0, 0) = 0 by
      simp [spatialHolderHalfQuotient]] at h
    exact h

private theorem spatialHolderHalfNorm_nonneg' {f : Vec3 → E} {m : ℕ}
    (hf : SpatialHolderHalf m f) : 0 ≤ spatialHolderHalfNorm m f :=
  Finset.sum_nonneg fun j hj => spatialLevel_nonneg hf (by simpa using hj)

private theorem spatialLevel_le_norm {f : Vec3 → E} {m j : ℕ}
    (hf : SpatialHolderHalf m f) (hj : j ≤ m) :
    spatialSupNorm (iteratedFDeriv ℝ j f) + spatialHolderHalfSeminorm (iteratedFDeriv ℝ j f) ≤
      spatialHolderHalfNorm m f := by
  unfold spatialHolderHalfNorm
  exact Finset.single_le_sum (s := Finset.range (m + 1))
    (fun k hk => spatialLevel_nonneg hf (by simpa using hk))
    (by simpa using hj)

private theorem spatialJet_le {f : Vec3 → E} {m j : ℕ}
    (hf : SpatialHolderHalf m f) (hj : j ≤ m) (x : Vec3) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ spatialHolderHalfNorm m f := by
  refine (norm_le_spatialSupNorm (hf.2 j hj).1 x).trans ?_
  refine (le_add_of_nonneg_right ?_).trans (spatialLevel_le_norm hf hj)
  have h := le_ciSup (hf.2 j hj).2 ((0 : Vec3), (0 : Vec3))
  rw [show spatialHolderHalfQuotient (iteratedFDeriv ℝ j f) (0, 0) = 0 by
    simp [spatialHolderHalfQuotient]] at h
  exact h

private theorem spatialJet_inc_le {f : Vec3 → E} {m j : ℕ}
    (hf : SpatialHolderHalf m f) (hj : j ≤ m) (x v : Vec3) :
    ‖iteratedFDeriv ℝ j f (x + v) - iteratedFDeriv ℝ j f x‖ ≤
      spatialHolderHalfNorm m f * Real.sqrt ‖v‖ := by
  refine (norm_increment_le_spatialHolderHalfSeminorm (hf.2 j hj).2 x v).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact (le_add_of_nonneg_left ((norm_nonneg _).trans
    (norm_le_spatialSupNorm (hf.2 j hj).1 x))).trans (spatialLevel_le_norm hf hj)

private theorem spatialHolderHalf_of_level_bounds {g : Vec3 → E} {m : ℕ} {A B : ℝ}
    (hg : ContDiff ℝ m g) (hB : 0 ≤ B)
    (hA : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ A)
    (hD : ∀ j ≤ m, ∀ x v, ‖iteratedFDeriv ℝ j g (x + v) - iteratedFDeriv ℝ j g x‖ ≤
      B * Real.sqrt ‖v‖) :
    SpatialHolderHalf m g ∧ spatialHolderHalfNorm m g ≤ (m + 1 : ℝ) * (A + B) := by
  have hQ (j : ℕ) (hj : j ≤ m) (p : Vec3 × Vec3) :
      spatialHolderHalfQuotient (iteratedFDeriv ℝ j g) p ≤ B := by
    rcases p with ⟨x, v⟩
    by_cases hv : v = 0
    · simpa [spatialHolderHalfQuotient, hv] using hB
    · exact (div_le_iff₀ (Real.sqrt_pos_of_pos (norm_pos_iff.mpr hv))).2 (hD j hj x v)
  refine ⟨⟨hg, fun j hj => ⟨⟨A, forall_mem_range.mpr (hA j hj)⟩,
    ⟨B, forall_mem_range.mpr (hQ j hj)⟩⟩⟩, ?_⟩
  unfold spatialHolderHalfNorm
  calc
    _ ≤ ∑ _ ∈ Finset.range (m + 1), (A + B) :=
      Finset.sum_le_sum fun j hj => add_le_add (ciSup_le (hA j (by simpa using hj)))
        (ciSup_le (hQ j (by simpa using hj)))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

private theorem spatialHolderHalf_mono {f : Vec3 → E} {m n : ℕ}
    (h : n ≤ m) (hf : SpatialHolderHalf m f) : SpatialHolderHalf n f ∧
      spatialHolderHalfNorm n f ≤ spatialHolderHalfNorm m f := by
  refine ⟨⟨hf.1.of_le (by exact_mod_cast h), fun j hj => hf.2 j (hj.trans h)⟩, ?_⟩
  unfold spatialHolderHalfNorm
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right h 1))
  exact fun j hj _ => spatialLevel_nonneg hf (by simpa using hj)

/-- A spatial half-Hölder sum estimate for an arbitrary normed target. -/
theorem spatialHolderHalf_add {f g : Vec3 → E} {m : ℕ}
    (hf : SpatialHolderHalf m f) (hg : SpatialHolderHalf m g) :
    SpatialHolderHalf m (f + g) ∧
      spatialHolderHalfNorm m (f + g) ≤ (2 * (m + 1) : ℝ) *
        (spatialHolderHalfNorm m f + spatialHolderHalfNorm m g) := by
  have heq (j : ℕ) (hj : j ≤ m) : iteratedFDeriv ℝ j (f + g) =
      iteratedFDeriv ℝ j f + iteratedFDeriv ℝ j g :=
    iteratedFDeriv_add (hf.1.of_le (by exact_mod_cast hj)) (hg.1.of_le (by exact_mod_cast hj))
  have h := spatialHolderHalf_of_level_bounds
    (show ContDiff ℝ m (f + g) from hf.1.add hg.1)
    (add_nonneg (spatialHolderHalfNorm_nonneg' hf) (spatialHolderHalfNorm_nonneg' hg))
    (fun j hj x => by
      rw [heq j hj, Pi.add_apply]
      exact (norm_add_le _ _).trans (add_le_add (spatialJet_le hf hj x) (spatialJet_le hg hj x)))
    (fun j hj x v => by
      rw [heq j hj, Pi.add_apply, Pi.add_apply]
      rw [show (iteratedFDeriv ℝ j f (x + v) + iteratedFDeriv ℝ j g (x + v)) -
          (iteratedFDeriv ℝ j f x + iteratedFDeriv ℝ j g x) =
          (iteratedFDeriv ℝ j f (x + v) - iteratedFDeriv ℝ j f x) +
          (iteratedFDeriv ℝ j g (x + v) - iteratedFDeriv ℝ j g x) by abel]
      exact (norm_add_le _ _).trans ((add_le_add (spatialJet_inc_le hf hj x v)
        (spatialJet_inc_le hg hj x v)).trans_eq (add_mul _ _ _).symm))
  exact ⟨h.1, h.2.trans_eq (by ring)⟩

private theorem spatialHolderHalf_neg {f : Vec3 → E} {m : ℕ}
    (hf : SpatialHolderHalf m f) : SpatialHolderHalf m (-f) ∧
      spatialHolderHalfNorm m (-f) = spatialHolderHalfNorm m f := by
  have hsup (j : ℕ) : (fun x => ‖iteratedFDeriv ℝ j (-f) x‖) =
      fun x => ‖iteratedFDeriv ℝ j f x‖ := by
    rw [iteratedFDeriv_neg]
    simp only [Pi.neg_apply, norm_neg]
  have hq (j : ℕ) : spatialHolderHalfQuotient (iteratedFDeriv ℝ j (-f)) =
      spatialHolderHalfQuotient (iteratedFDeriv ℝ j f) := by
    rw [iteratedFDeriv_neg]
    funext p
    simp only [spatialHolderHalfQuotient, Pi.neg_apply, neg_sub_neg]
    rw [norm_sub_rev]
  refine ⟨⟨hf.1.neg, fun j hj => ?_⟩, ?_⟩
  · rw [hsup j, hq j]
    exact hf.2 j hj
  · unfold spatialHolderHalfNorm
    apply Finset.sum_congr rfl
    intro j _
    simp only [spatialSupNorm, spatialHolderHalfSeminorm, hsup j, hq j]

private theorem contDiff_bilinear (B : E →L[ℝ] F →L[ℝ] G) {m : ℕ} {f : Vec3 → E}
    {g : Vec3 → F} (hf : ContDiff ℝ m f) (hg : ContDiff ℝ m g) :
    ContDiff ℝ m (fun x => B (f x) (g x)) := (B.contDiff.comp hf).clm_apply hg

private theorem norm_iteratedFDeriv_bilinear_const_le (B : E →L[ℝ] F →L[ℝ] G)
    {f : Vec3 → E} {g : Vec3 → F} {m j : ℕ} (hj : j ≤ m)
    (hf : ContDiff ℝ m f) (hg : ContDiff ℝ m g) (x : Vec3) {A D : ℝ} (hA : 0 ≤ A)
    (hf' : ∀ i ≤ j, ‖iteratedFDeriv ℝ i f x‖ ≤ A)
    (hg' : ∀ i ≤ j, ‖iteratedFDeriv ℝ i g x‖ ≤ D) :
    ‖iteratedFDeriv ℝ j (fun y => B (f y) (g y)) x‖ ≤ ‖B‖ * (2 : ℝ)^m * A * D := by
  have hD : 0 ≤ D := (norm_nonneg _).trans (hg' 0 (Nat.zero_le _))
  have hchoose : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ)^j := by
    exact_mod_cast Nat.sum_range_choose j
  calc
    _ ≤ ‖B‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j - i) g x‖ :=
      B.norm_iteratedFDeriv_le_of_bilinear hf hg x (by exact_mod_cast hj)
    _ ≤ ‖B‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A * D := by
      gcongr with i hi
      · exact hf' i (Finset.mem_range_succ_iff.mp hi)
      · exact hg' (j - i) (Nat.sub_le _ _)
    _ = ‖B‖ * (2 : ℝ)^j * A * D := by rw [← Finset.sum_mul, ← Finset.sum_mul, hchoose]; ring
    _ ≤ _ := by gcongr; norm_num

/-- Leibniz and the product increment formula give (5.59) for any continuous bilinear map. -/
theorem spatialHolderHalf_bilinear (B : E →L[ℝ] F →L[ℝ] G)
    {f : Vec3 → E} {g : Vec3 → F} {m : ℕ}
    (hf : SpatialHolderHalf m f) (hg : SpatialHolderHalf m g) :
    SpatialHolderHalf m (fun x => B (f x) (g x)) ∧
      spatialHolderHalfNorm m (fun x => B (f x) (g x)) ≤
        (3 * (m + 1) * ‖B‖ * (2 : ℝ)^m) * spatialHolderHalfNorm m f * spatialHolderHalfNorm m g := by
  let A := spatialHolderHalfNorm m f
  let D := spatialHolderHalfNorm m g
  let K := ‖B‖ * (2 : ℝ)^m * A * D
  have hA : 0 ≤ A := spatialHolderHalfNorm_nonneg' hf
  have hD : 0 ≤ D := spatialHolderHalfNorm_nonneg' hg
  have hK : 0 ≤ K := by positivity
  have hprod := contDiff_bilinear B hf.1 hg.1
  have hsup (j : ℕ) (hj : j ≤ m) (x : Vec3) :
      ‖iteratedFDeriv ℝ j (fun y => B (f y) (g y)) x‖ ≤ K :=
    norm_iteratedFDeriv_bilinear_const_le B hj hf.1 hg.1 x hA
      (fun i hi => spatialJet_le hf (hi.trans hj) x) (fun i hi => spatialJet_le hg (hi.trans hj) x)
  have hinc (j : ℕ) (hj : j ≤ m) (x v : Vec3) :
      ‖iteratedFDeriv ℝ j (fun y => B (f y) (g y)) (x + v) -
        iteratedFDeriv ℝ j (fun y => B (f y) (g y)) x‖ ≤ (2 * K) * Real.sqrt ‖v‖ := by
    let fs := fun y => f (y + v)
    let gs := fun y => g (y + v)
    have hfs : ContDiff ℝ m fs := hf.1.comp (by fun_prop)
    have hgs : ContDiff ℝ m gs := hg.1.comp (by fun_prop)
    have hfsf : ContDiff ℝ m (fs - f) := hfs.sub hf.1
    have hgsg : ContDiff ℝ m (gs - g) := hgs.sub hg.1
    have h₁ := contDiff_bilinear B hfsf hgs
    have h₂ := contDiff_bilinear B hf.1 hgsg
    have hsplit : ((fun y => B (fs y) (gs y)) - (fun y => B (f y) (g y))) =
        (fun y => B ((fs - f) y) (gs y)) + (fun y => B (f y) ((gs - g) y)) := by
      funext y
      simp only [Pi.add_apply, Pi.sub_apply, map_sub, sub_apply]
      abel
    have heq := congrFun (congrArg (iteratedFDeriv ℝ j) hsplit) x
    rw [iteratedFDeriv_sub ((contDiff_bilinear B hfs hgs).of_le (by exact_mod_cast hj))
      (hprod.of_le (by exact_mod_cast hj)), iteratedFDeriv_add
      (h₁.of_le (by exact_mod_cast hj)) (h₂.of_le (by exact_mod_cast hj)), Pi.sub_apply,
      Pi.add_apply] at heq
    change iteratedFDeriv ℝ j (fun y => (fun z => B (f z) (g z)) (y + v)) x - _ = _ at heq
    rw [iteratedFDeriv_comp_add_right (f := fun z => B (f z) (g z))] at heq
    rw [heq]
    apply (norm_add_le _ _).trans
    have hmul₁ := norm_iteratedFDeriv_bilinear_const_le B hj hfsf hgs x
      (mul_nonneg hA (Real.sqrt_nonneg _)) (D := D) (fun i hi => by
        have hi' := hi.trans hj
        have hN : (i : ℕ∞ω) ≤ m := by exact_mod_cast hi'
        rw [iteratedFDeriv_sub (hfs.of_le hN) (hf.1.of_le hN), Pi.sub_apply]
        change ‖iteratedFDeriv ℝ i (fun y => f (y + v)) x - _‖ ≤ _
        rw [iteratedFDeriv_comp_add_right (f := f)]
        exact spatialJet_inc_le hf hi' x v)
      (fun i hi => by
        change ‖iteratedFDeriv ℝ i (fun y => g (y + v)) x‖ ≤ _
        rw [iteratedFDeriv_comp_add_right (f := g)]
        exact spatialJet_le hg (hi.trans hj) (x + v))
    have hmul₂ := norm_iteratedFDeriv_bilinear_const_le B hj hf.1 hgsg x hA
      (fun i hi => spatialJet_le hf (hi.trans hj) x) (D := D * Real.sqrt ‖v‖) (fun i hi => by
        have hi' := hi.trans hj
        have hN : (i : ℕ∞ω) ≤ m := by exact_mod_cast hi'
        rw [iteratedFDeriv_sub (hgs.of_le hN) (hg.1.of_le hN), Pi.sub_apply]
        change ‖iteratedFDeriv ℝ i (fun y => g (y + v)) x - _‖ ≤ _
        rw [iteratedFDeriv_comp_add_right (f := g)]
        exact spatialJet_inc_le hg hi' x v)
    exact (add_le_add hmul₁ hmul₂).trans_eq (by dsimp [K]; ring)
  have h := spatialHolderHalf_of_level_bounds hprod (mul_nonneg (by norm_num) hK) hsup hinc
  exact ⟨h.1, h.2.trans_eq (by dsimp [K, A, D]; ring)⟩

/-- Continuous linear maps preserve finite spatial half-Hölder regularity. -/
theorem spatialHolderHalf_comp_clm (L : E →L[ℝ] F) {f : Vec3 → E} {m : ℕ}
    (hf : SpatialHolderHalf m f) : SpatialHolderHalf m (L ∘ f) ∧
      spatialHolderHalfNorm m (L ∘ f) ≤ ‖L‖ * spatialHolderHalfNorm m f := by
  have heq (j : ℕ) (hj : j ≤ m) (x : Vec3) : iteratedFDeriv ℝ j (L ∘ f) x =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ j f x) :=
    L.iteratedFDeriv_comp_left hf.1.contDiffAt (by exact_mod_cast hj)
  have hsup (j : ℕ) (hj : j ≤ m) (x : Vec3) : ‖iteratedFDeriv ℝ j (L ∘ f) x‖ ≤
      ‖L‖ * spatialSupNorm (iteratedFDeriv ℝ j f) := by
    rw [heq j hj]
    exact (L.norm_compContinuousMultilinearMap_le _).trans
      (mul_le_mul_of_nonneg_left (norm_le_spatialSupNorm (hf.2 j hj).1 x) (norm_nonneg _))
  have hquot (j : ℕ) (hj : j ≤ m) (p : Vec3 × Vec3) :
      spatialHolderHalfQuotient (iteratedFDeriv ℝ j (L ∘ f)) p ≤
        ‖L‖ * spatialHolderHalfSeminorm (iteratedFDeriv ℝ j f) := by
    unfold spatialHolderHalfQuotient
    rw [heq j hj, heq j hj]
    let L' := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => Vec3) E F L
    change ‖L' (iteratedFDeriv ℝ j f (p.1 + p.2)) - L' (iteratedFDeriv ℝ j f p.1)‖ /
      Real.sqrt ‖p.2‖ ≤ _
    rw [← map_sub]
    calc
      _ ≤ (‖L‖ * ‖iteratedFDeriv ℝ j f (p.1 + p.2) - iteratedFDeriv ℝ j f p.1‖) /
          Real.sqrt ‖p.2‖ :=
        div_le_div_of_nonneg_right (L.norm_compContinuousMultilinearMap_le _) (Real.sqrt_nonneg _)
      _ = ‖L‖ * spatialHolderHalfQuotient (iteratedFDeriv ℝ j f) p := by
        rw [mul_div_assoc]
        rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_ciSup (hf.2 j hj).2 p) (norm_nonneg _)
  refine ⟨⟨L.contDiff.comp hf.1, fun j hj =>
    ⟨⟨_, forall_mem_range.mpr (hsup j hj)⟩, ⟨_, forall_mem_range.mpr (hquot j hj)⟩⟩⟩, ?_⟩
  unfold spatialHolderHalfNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hj' := Finset.mem_range_succ_iff.mp hj
  rw [mul_add]
  exact add_le_add (ciSup_le (hsup j hj')) (ciSup_le (hquot j hj'))

private theorem spatialHolderHalf_fderiv {f : Vec3 → E} {m : ℕ}
    (hf : SpatialHolderHalf (m + 1) f) :
    SpatialHolderHalf m (fderiv ℝ f) ∧
      spatialHolderHalfNorm m (fderiv ℝ f) ≤ spatialHolderHalfNorm (m + 1) f := by
  have heq (j : ℕ) (x : Vec3) : iteratedFDeriv ℝ (j + 1) f x =
      (continuousMultilinearCurryRightEquiv' ℝ j Vec3 E).symm
        (iteratedFDeriv ℝ j (fderiv ℝ f) x) := iteratedFDeriv_succ_eq_comp_right
  have hsup (j : ℕ) : (fun x => ‖iteratedFDeriv ℝ j (fderiv ℝ f) x‖) =
      fun x => ‖iteratedFDeriv ℝ (j + 1) f x‖ :=
    funext fun x => by rw [heq, LinearIsometryEquiv.norm_map]
  have hquo (j : ℕ) : spatialHolderHalfQuotient (iteratedFDeriv ℝ j (fderiv ℝ f)) =
      spatialHolderHalfQuotient (iteratedFDeriv ℝ (j + 1) f) := by
    funext p
    unfold spatialHolderHalfQuotient
    rw [heq j p.1, heq j (p.1 + p.2)]
    let c := (continuousMultilinearCurryRightEquiv' ℝ j Vec3 E).symm
    rw [← c.map_sub, c.norm_map]
  refine ⟨⟨hf.1.fderiv_right (by simp), fun j hj => ?_⟩, ?_⟩
  · rw [hsup, hquo]
    exact hf.2 _ (Nat.succ_le_succ hj)
  · unfold spatialHolderHalfNorm
    have hsum : (∑ j ∈ Finset.range (m + 1), (spatialSupNorm (iteratedFDeriv ℝ j (fderiv ℝ f)) +
        spatialHolderHalfSeminorm (iteratedFDeriv ℝ j (fderiv ℝ f)))) =
        ∑ j ∈ Finset.range (m + 1), (spatialSupNorm (iteratedFDeriv ℝ (j + 1) f) +
          spatialHolderHalfSeminorm (iteratedFDeriv ℝ (j + 1) f)) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [spatialSupNorm, spatialHolderHalfSeminorm, hsup j, hquo j]
    rw [hsum]
    conv_rhs => rw [Finset.sum_range_succ']
    exact le_add_of_nonneg_right (spatialLevel_nonneg hf (Nat.zero_le _))

/-- Contracting a first spatial derivative, as for a tensor divergence, loses one Hölder order. -/
theorem spatialHolderHalf_contraction_fderiv (L : (Vec3 →L[ℝ] E) →L[ℝ] F)
    {f : Vec3 → E} {m : ℕ} (hf : SpatialHolderHalf (m + 1) f) :
    SpatialHolderHalf m (L ∘ fderiv ℝ f) ∧
      spatialHolderHalfNorm m (L ∘ fderiv ℝ f) ≤ ‖L‖ * spatialHolderHalfNorm (m + 1) f := by
  have hD := spatialHolderHalf_fderiv hf
  have hL := spatialHolderHalf_comp_clm L hD.1
  exact ⟨hL.1, hL.2.trans (mul_le_mul_of_nonneg_left hD.2 (norm_nonneg _))⟩

end HolderCalculus


section QuantitativeResidual

variable {Q Qc : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup Qc] [NormedSpace ℂ Qc] [CompleteSpace Qc]

private theorem cutoffHolderTailUniformConstant_nonneg' (K : 𝓢(Vec3, ℂ)) (m : ℕ) :
    0 ≤ cutoffHolderTailUniformConstant K m := by
  unfold cutoffHolderTailUniformConstant cutoffKernelAbsoluteMoment
  positivity

/-- The real Fourier cutoff on a tensor field represented in a complex normed space. -/
def realTensorFourierCutoff (J : Q →L[ℝ] Qc) (R : Qc →L[ℝ] Q) (ψ : Vec3 → ℝ) (Λ : ℝ)
    (g : C(UnitAddTorus (Fin 3), Q)) (z : UnitAddTorus (Fin 3)) : Q :=
  R (smoothFourierCutoff ψ Λ
    (⟨fun a => J (g a), J.continuous.comp g.continuous⟩ : C(UnitAddTorus (Fin 3), Qc)) z)

/-- The tensor cutoff tail follows from the complex cutoff tail by contraction. -/
theorem spatialHolderHalfNorm_realTensorCutoffTail (J : Q →L[ℝ] Qc) (R : Qc →L[ℝ] Q)
    (hRJ : ∀ q, R (J q) = q)
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) {Λ : ℝ} (hΛ : 0 < Λ)
    (g : C(UnitAddTorus (Fin 3), Q)) {M s : ℕ} (hsM : s ≤ M)
    (hg : SpatialHolderHalf M (fun x => g (toUnitTorus x))) :
    let f : Vec3 → Q := fun x => g (toUnitTorus x)
    let r : Vec3 → Q := f - fun x => realTensorFourierCutoff J R ψ Λ g (toUnitTorus x)
    SpatialHolderHalf s r ∧ spatialHolderHalfNorm s r ≤
      (‖R‖ * ‖J‖ * cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) M) *
        Λ ^ ((s : ℤ) - M) * spatialHolderHalfNorm M f := by
  let f := fun x => g (toUnitTorus x)
  let gc : C(UnitAddTorus (Fin 3), Qc) := ⟨fun a => J (g a), J.continuous.comp g.continuous⟩
  let rc := (fun x => gc (toUnitTorus x)) -
    fun x => smoothFourierCutoff ψ Λ gc (toUnitTorus x)
  have hJ := spatialHolderHalf_comp_clm J hg
  change SpatialHolderHalf M (fun x => gc (toUnitTorus x)) ∧
    spatialHolderHalfNorm M (fun x => gc (toUnitTorus x)) ≤ ‖J‖ * spatialHolderHalfNorm M f at hJ
  have ht := spatialHolderHalfNorm_cutoffTail hψ hs hunit hΛ gc hsM hJ.1
  change SpatialHolderHalf s rc ∧ spatialHolderHalfNorm s rc ≤ _ at ht
  have hR := spatialHolderHalf_comp_clm R ht.1
  have heq : R ∘ rc = f - fun x => realTensorFourierCutoff J R ψ Λ g (toUnitTorus x) := by
    funext x
    change R (J (f x) - smoothFourierCutoff ψ Λ gc (toUnitTorus x)) = _
    rw [map_sub, hRJ]
    rfl
  rw [heq] at hR
  refine ⟨hR.1, hR.2.trans ?_⟩
  have hC := cutoffHolderTailUniformConstant_nonneg' (cutoffSchwartzKernel hψ hs) M
  have hp : 0 ≤ Λ ^ ((s : ℤ) - M) := zpow_nonneg hΛ.le _
  let C := cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) M
  calc
    _ ≤ ‖R‖ * (C * Λ ^ ((s : ℤ) - M) * spatialHolderHalfNorm M (fun x => gc (toUnitTorus x))) :=
      mul_le_mul_of_nonneg_left ht.2 (norm_nonneg _)
    _ ≤ ‖R‖ * (C * Λ ^ ((s : ℤ) - M) * (‖J‖ * spatialHolderHalfNorm M f)) := by
      gcongr
      exact hJ.2
    _ = _ := by ring

private theorem spatialHolderHalf_realVectorCutoff {ψ : Vec3 → ℝ}
    (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) {Λ : ℝ} (hΛ : 0 < Λ)
    (g : C(UnitAddTorus (Fin 3), Vec3)) {m : ℕ}
    (hg : SpatialHolderHalf m (fun x => g (toUnitTorus x))) :
    let u := fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)
    SpatialHolderHalf m u ∧ spatialHolderHalfNorm m u ≤
      (2 * (m + 1) * (1 + cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) m)) *
        spatialHolderHalfNorm m (fun x => g (toUnitTorus x)) := by
  let f := fun x => g (toUnitTorus x)
  let u := fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)
  have ht := spatialHolderHalfNorm_realVectorCutoffTail hψ hs hunit hΛ g (le_refl m) hg
  change SpatialHolderHalf m (f - u) ∧ spatialHolderHalfNorm m (f - u) ≤ _ at ht
  have hneg := spatialHolderHalf_neg ht.1
  have h := spatialHolderHalf_add hg hneg.1
  rw [show f + -(f - u) = u by abel, hneg.2] at h
  refine ⟨h.1, h.2.trans ?_⟩
  have htail : spatialHolderHalfNorm m (f - u) ≤
      cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) m * spatialHolderHalfNorm m f := by
    simpa only [sub_self, zpow_zero, mul_one] using ht.2
  calc
    _ ≤ (2 * (m + 1) : ℝ) * (spatialHolderHalfNorm m f +
        cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) m * spatialHolderHalfNorm m f) := by
      gcongr
    _ = _ := by ring


/-- The right-hand side of (5.58), formed using the real velocity and tensor cutoffs. -/
def truncatedParentProjectedResidual
    (J : Q →L[ℝ] Qc) (R : Qc →L[ℝ] Q)
    (B : Vec3 →L[ℝ] Vec3 →L[ℝ] Q) (D : (Vec3 →L[ℝ] Q) →L[ℝ] Vec3)
    (proj : (Vec3 → Vec3) → (Vec3 → Vec3)) (ψ : Vec3 → ℝ) (Λ : ℝ)
    (gV gRV : C(UnitAddTorus (Fin 3), Vec3)) : Vec3 → Vec3 :=
  let V := fun x => gV (toUnitTorus x)
  let u := fun x => realVectorFourierCutoff ψ Λ gV (toUnitTorus x)
  let v := u - V
  let gVV : C(UnitAddTorus (Fin 3), Q) :=
    ⟨fun z => B (gV z) (gV z), (B.continuous.comp gV.continuous).clm_apply gV.continuous⟩
  let tensorTail := (fun x => gVV (toUnitTorus x)) -
    fun x => realTensorFourierCutoff J R ψ Λ gVV (toUnitTorus x)
  proj ((fun x => realVectorFourierCutoff ψ Λ gRV (toUnitTorus x)) +
    D ∘ fderiv ℝ ((fun x => B (v x) (u x)) + (fun x => B (V x) (v x)) + tensorTail))

/-- The estimate for (5.58) is uniform in the cutoff and in the velocity slices.
The periodic Leray estimate is an input. The other bounds are supplied by the
Fourier tail, the bilinear Hölder estimate, and contraction of the tensor derivative. -/
theorem truncatedParentProjectedResidual_holder_bound
    (J : Q →L[ℝ] Qc) (R : Qc →L[ℝ] Q) (hRJ : ∀ q, R (J q) = q)
    (B : Vec3 →L[ℝ] Vec3 →L[ℝ] Q) (D : (Vec3 →L[ℝ] Q) →L[ℝ] Vec3)
    (proj : (Vec3 → Vec3) → (Vec3 → Vec3)) {Cproj : ℝ} (hCproj : 0 ≤ Cproj)
    (hproj : ∀ f : Vec3 → Vec3, SpatiallyPeriodic f → SpatialHolderHalf 1 f →
      SpatialHolderHalf 1 (proj f) ∧ spatialHolderHalfNorm 1 (proj f) ≤ Cproj * spatialHolderHalfNorm 1 f)
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) (P : ℕ) (hP : 2 ≤ P) :
    let Cr := 4 * Cproj * (2 * (((1 : ℕ) : ℝ) + 1) *
      (1 + cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) 1))
    ∃ Ct : ℝ, 0 ≤ Ct ∧
      ∀ (Λ : ℝ), 1 ≤ Λ → ∀ gV gRV : C(UnitAddTorus (Fin 3), Vec3),
      SpatialHolderHalf P (fun x => gV (toUnitTorus x)) →
      SpatialHolderHalf 1 (fun x => gRV (toUnitTorus x)) →
      let V := fun x => gV (toUnitTorus x)
      let v := (fun x => realVectorFourierCutoff ψ Λ gV (toUnitTorus x)) - V
      let res := truncatedParentProjectedResidual J R B D proj ψ Λ gV gRV
      let ε := Λ ^ ((2 : ℤ) - P) * (1 + spatialHolderHalfNorm P V)^2
      SpatialHolderHalf 2 v ∧ spatialHolderHalfNorm 2 v ≤ Ct * ε ∧
      SpatialHolderHalf 1 res ∧
        spatialHolderHalfNorm 1 res ≤ Cr * spatialHolderHalfNorm 1 (fun x => gRV (toUnitTorus x)) + Ct * ε := by
  let C (m : ℕ) := cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) m
  let Bc (m : ℕ) := 3 * (m + 1) * ‖B‖ * (2 : ℝ)^m
  let Sc (m : ℕ) := 2 * (m + 1) * (1 + C m)
  let Ct₀ := 36 * (Bc 2 * C P * Sc 2 + Bc 2 * C P + (‖R‖ * ‖J‖ * C P) * Bc P)
  let Cr := 4 * Cproj * Sc 1
  let Ct := C P + 4 * Cproj * ‖D‖ * Ct₀
  have hC (m : ℕ) : 0 ≤ C m := cutoffHolderTailUniformConstant_nonneg' _ _
  have hBc (m : ℕ) : 0 ≤ Bc m := by dsimp [Bc]; positivity
  have hSc (m : ℕ) : 0 ≤ Sc m := mul_nonneg (by positivity) (by linarith [hC m])
  have h1 := mul_nonneg (mul_nonneg (hBc 2) (hC P)) (hSc 2)
  have h2 := mul_nonneg (hBc 2) (hC P)
  have hQR : 0 ≤ ‖R‖ * ‖J‖ * C P := mul_nonneg (by positivity) (hC P)
  have hCt₀ : 0 ≤ Ct₀ := mul_nonneg (by norm_num)
    (add_nonneg (add_nonneg h1 h2) (mul_nonneg hQR (hBc P)))
  have hrem : 0 ≤ 4 * Cproj * ‖D‖ * Ct₀ := by positivity
  have hCt : 0 ≤ Ct := add_nonneg (hC P) hrem
  refine ⟨Ct, hCt, ?_⟩
  intro Λ hΛ gV gRV hV hRV
  let V := fun x => gV (toUnitTorus x)
  let u := fun x => realVectorFourierCutoff ψ Λ gV (toUnitTorus x)
  let v := u - V
  let RV := fun x => gRV (toUnitTorus x)
  let cutRV := fun x => realVectorFourierCutoff ψ Λ gRV (toUnitTorus x)
  let gVV : C(UnitAddTorus (Fin 3), Q) :=
    ⟨fun z => B (gV z) (gV z), (B.continuous.comp gV.continuous).clm_apply gV.continuous⟩
  let VV := fun x => gVV (toUnitTorus x)
  let tailVV := VV - fun x => realTensorFourierCutoff J R ψ Λ gVV (toUnitTorus x)
  let vu := fun x => B (v x) (u x)
  let Vv := fun x => B (V x) (v x)
  let E := vu + Vv + tailVV
  let W := cutRV + D ∘ fderiv ℝ E
  let τ := Λ ^ ((2 : ℤ) - P)
  let M := spatialHolderHalfNorm P V
  let ε := τ * (1 + M)^2
  have hτ : 0 ≤ τ := zpow_nonneg (by linarith) _
  have hM : 0 ≤ M := spatialHolderHalfNorm_nonneg' hV
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hΛ' : 0 < Λ := by linarith
  have hV₂ := spatialHolderHalf_mono hP hV
  have htail := spatialHolderHalfNorm_realVectorCutoffTail hψ hs hunit hΛ' gV hP hV
  change SpatialHolderHalf 2 (V - u) ∧ spatialHolderHalfNorm 2 (V - u) ≤ C P * τ * M at htail
  have hv := spatialHolderHalf_neg htail.1
  rw [neg_sub] at hv
  change SpatialHolderHalf 2 v ∧ _ at hv
  have hvN : spatialHolderHalfNorm 2 v ≤ C P * τ * M := hv.2.le.trans htail.2
  have hu := spatialHolderHalf_realVectorCutoff hψ hs hunit hΛ' gV hV₂.1
  change SpatialHolderHalf 2 u ∧ spatialHolderHalfNorm 2 u ≤ Sc 2 * spatialHolderHalfNorm 2 V at hu
  have huN := hu.2.trans (mul_le_mul_of_nonneg_left hV₂.2 (hSc 2))
  have hcut := spatialHolderHalf_realVectorCutoff hψ hs hunit hΛ' gRV hRV
  change SpatialHolderHalf 1 cutRV ∧ spatialHolderHalfNorm 1 cutRV ≤ Sc 1 * spatialHolderHalfNorm 1 RV at hcut
  have hVV := spatialHolderHalf_bilinear B hV hV
  change SpatialHolderHalf P VV ∧ spatialHolderHalfNorm P VV ≤ Bc P * M * M at hVV
  have htailVV := spatialHolderHalfNorm_realTensorCutoffTail J R hRJ hψ hs hunit hΛ' gVV hP hVV.1
  change SpatialHolderHalf 2 tailVV ∧ spatialHolderHalfNorm 2 tailVV ≤
    (‖R‖ * ‖J‖ * C P) * τ * spatialHolderHalfNorm P VV at htailVV
  have h₁ := spatialHolderHalf_bilinear B hv.1 hu.1
  change SpatialHolderHalf 2 vu ∧ spatialHolderHalfNorm 2 vu ≤
    Bc 2 * spatialHolderHalfNorm 2 v * spatialHolderHalfNorm 2 u at h₁
  have h₂ := spatialHolderHalf_bilinear B hV₂.1 hv.1
  change SpatialHolderHalf 2 Vv ∧ spatialHolderHalfNorm 2 Vv ≤
    Bc 2 * spatialHolderHalfNorm 2 V * spatialHolderHalfNorm 2 v at h₂
  have h₁N : spatialHolderHalfNorm 2 vu ≤ Bc 2 * (C P * τ * M) * (Sc 2 * M) :=
    h₁.2.trans (mul_le_mul (mul_le_mul_of_nonneg_left hvN (hBc 2)) huN
      (spatialHolderHalfNorm_nonneg' hu.1) (mul_nonneg (hBc 2) (mul_nonneg (mul_nonneg (hC P) hτ) hM)))
  have h₂N : spatialHolderHalfNorm 2 Vv ≤ Bc 2 * M * (C P * τ * M) :=
    h₂.2.trans (mul_le_mul (mul_le_mul_of_nonneg_left hV₂.2 (hBc 2)) hvN
      (spatialHolderHalfNorm_nonneg' hv.1) (by positivity))
  have h₃N : spatialHolderHalfNorm 2 tailVV ≤ (‖R‖ * ‖J‖ * C P) * τ * (Bc P * M * M) :=
    htailVV.2.trans (mul_le_mul_of_nonneg_left hVV.2 (mul_nonneg hQR hτ))
  have hsum := spatialHolderHalf_add h₁.1 h₂.1
  have hE := spatialHolderHalf_add hsum.1 htailVV.1
  have hE₀ : SpatialHolderHalf 2 E := hE.1
  have hEN : spatialHolderHalfNorm 2 E ≤ Ct₀ * (τ * M^2) := by
    have h₃ := spatialHolderHalfNorm_nonneg' htailVV.1
    change spatialHolderHalfNorm 2 E ≤ _
    have htmp := hE.2
    norm_num at hsum htmp
    dsimp only [Ct₀]
    nlinarith only [htmp, hsum.2, h₁N, h₂N, h₃N, h₃]
  have hdiv := spatialHolderHalf_contraction_fderiv D hE₀
  have hsumW := spatialHolderHalf_add hcut.1 hdiv.1
  have hW : SpatialHolderHalf 1 W := hsumW.1
  have hdivN : spatialHolderHalfNorm 1 (D ∘ fderiv ℝ E) ≤ ‖D‖ * (Ct₀ * (τ * M^2)) :=
    hdiv.2.trans (mul_le_mul_of_nonneg_left hEN (norm_nonneg D))
  have hsumWN : spatialHolderHalfNorm 1 W ≤
      4 * (spatialHolderHalfNorm 1 cutRV + spatialHolderHalfNorm 1 (D ∘ fderiv ℝ E)) := by
    norm_num at hsumW
    exact hsumW.2
  have hWN : spatialHolderHalfNorm 1 W ≤
      4 * (Sc 1 * spatialHolderHalfNorm 1 RV + ‖D‖ * (Ct₀ * (τ * M^2))) :=
    hsumWN.trans (mul_le_mul_of_nonneg_left (add_le_add hcut.2 hdivN) (by norm_num))
  have hWper : SpatiallyPeriodic W := by
    intro n x
    have hx (y : Vec3) : toUnitTorus (y + latticeVector n) = toUnitTorus y :=
      (toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩
    have he (y : Vec3) : E (y + latticeVector n) = E y := by
      simp only [E, vu, Vv, v, V, u, tailVV, VV, Pi.add_apply, Pi.sub_apply, hx]
    have hd : fderiv ℝ E (x + latticeVector n) = fderiv ℝ E x := by
      rw [← fderiv_comp_add_right]
      exact congrArg (fun f : Vec3 → Q => fderiv ℝ f x) (funext he)
    simp only [W, cutRV, Pi.add_apply, Function.comp_apply, hx, hd]
  have hL := hproj W hWper hW
  have hMε : τ * M^2 ≤ ε := mul_le_mul_of_nonneg_left (by nlinarith only [hM]) hτ
  have hMleε : τ * M ≤ ε := mul_le_mul_of_nonneg_left (by nlinarith only [hM, sq_nonneg M]) hτ
  refine ⟨hv.1, hvN.trans ?_, hL.1, hL.2.trans ?_⟩
  · calc
      _ = C P * (τ * M) := by ring
      _ ≤ C P * ε := mul_le_mul_of_nonneg_left hMleε (hC P)
      _ ≤ Ct * ε := by
        apply mul_le_mul_of_nonneg_right _ hε
        exact le_add_of_nonneg_right hrem
  · calc
      _ ≤ Cproj * (4 * (Sc 1 * spatialHolderHalfNorm 1 RV + ‖D‖ * (Ct₀ * (τ * M^2)))) :=
        mul_le_mul_of_nonneg_left hWN hCproj
      _ = Cr * spatialHolderHalfNorm 1 RV + (4 * Cproj * ‖D‖ * Ct₀) * (τ * M^2) := by
        dsimp only [Cr]; ring
      _ ≤ Cr * spatialHolderHalfNorm 1 RV + Ct * ε := by
        refine add_le_add le_rfl ?_
        calc
          _ ≤ (4 * Cproj * ‖D‖ * Ct₀) * ε := mul_le_mul_of_nonneg_left hMε hrem
          _ ≤ Ct * ε := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hC P)) hε


/-- The columns of a real momentum tensor in the Euclidean coordinates of the lift. -/
abbrev MomentumTensor := Fin 3 → Vec3

private abbrev ComplexMomentumTensor := Fin 3 → ComplexEuclideanVec3

/-- The rank-one momentum tensor with column `i` equal to `v i • u`. -/
def momentumTensor : Vec3 →L[ℝ] Vec3 →L[ℝ] MomentumTensor :=
  (LinearMap.mk₂ ℝ (fun (u v : Vec3) (i : Fin 3) => v i • u)
    (fun _ _ _ => by ext i; simp [smul_add])
    (fun c u v => by
      funext i
      change v i • (c • u) = c • (v i • u)
      exact smul_comm (v i) c u)
    (fun _ _ _ => by ext i; simp [add_smul])
    (fun _ _ _ => by ext i; simp [mul_smul])).mkContinuous₂ 1 (fun u v => by
    change ‖fun i : Fin 3 => v i • u‖ ≤ 1 * ‖u‖ * ‖v‖
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    rw [norm_smul, one_mul, mul_comm ‖u‖ ‖v‖]
    exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v i) (norm_nonneg u))

/-- Tensor divergence adds the derivative of the `i`th column in coordinate `i`. -/
def momentumTensorDivergence : (Vec3 →L[ℝ] MomentumTensor) →L[ℝ] Vec3 :=
  ∑ i : Fin 3, (ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.apply ℝ MomentumTensor (EuclideanSpace.single i 1))

@[simp]
theorem momentumTensor_apply (u v : Vec3) (i : Fin 3) : momentumTensor u v i = v i • u := rfl

@[simp]
theorem momentumTensorDivergence_apply (d : Vec3 →L[ℝ] MomentumTensor) :
    momentumTensorDivergence d = ∑ i : Fin 3, d (EuclideanSpace.single i 1) i := by
  simp [momentumTensorDivergence]


/-- For a divergence-free velocity, tensor divergence is the Euler advection term. -/
theorem momentumTensorDivergence_self_eq_advection {v : Vec3 → Vec3}
    (hv : Differentiable ℝ v) (hdiv : ∀ x, divergence v x = 0) :
    momentumTensorDivergence ∘ fderiv ℝ (fun x => momentumTensor (v x) (v x)) =
      fun x => fderiv ℝ v x (v x) := by
  funext x
  let E := fun y => momentumTensor (v y) (v y)
  have hE : DifferentiableAt ℝ E x := ((momentumTensor.differentiableAt.comp x (hv x)).clm_apply (hv x))
  have hcol (i : Fin 3) :
      fderiv ℝ E x (EuclideanSpace.single i 1) i =
        (v x) i • fderiv ℝ v x (EuclideanSpace.single i 1) +
          (fderiv ℝ v x (EuclideanSpace.single i 1)) i • v x := by
    let π : MomentumTensor →L[ℝ] Vec3 := ContinuousLinearMap.proj i
    let p : Vec3 →L[ℝ] ℝ := EuclideanSpace.proj i
    have hπ := π.hasFDerivAt.comp x hE.hasFDerivAt
    have hp := p.hasFDerivAt.comp x (hv x).hasFDerivAt
    have hd := hp.smul (hv x).hasFDerivAt
    have h := congrArg (fun L : Vec3 →L[ℝ] Vec3 => L (EuclideanSpace.single i 1))
      (hπ.fderiv.symm.trans hd.fderiv)
    exact h
  have hbasis : (∑ i : Fin 3, (v x) i • EuclideanSpace.single i (1 : ℝ)) = v x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (v x)
  change momentumTensorDivergence (fderiv ℝ E x) = _
  simp only [momentumTensorDivergence_apply, hcol, Finset.sum_add_distrib, ← Finset.sum_smul]
  rw [← divergence, hdiv x, zero_smul, add_zero]
  conv_rhs => rw [← hbasis]
  simp only [map_smul, map_sum]

/-- The second divergence of the momentum tensor is the gradient trace in the pressure equation. -/
theorem divergence_momentumTensorDivergence_self {v : Vec3 → Vec3}
    (hv : ContDiff ℝ 2 v) (hdiv : ∀ x, divergence v x = 0) (x : Vec3) :
    divergence (momentumTensorDivergence ∘ fderiv ℝ (fun y => momentumTensor (v y) (v y))) x =
      LinearMap.trace ℝ Vec3 ((fderiv ℝ v x).comp (fderiv ℝ v x)).toLinearMap := by
  rw [momentumTensorDivergence_self_eq_advection (hv.differentiable (by norm_num)) hdiv]
  exact divergence_advection_eq_trace_square hv hdiv x

private def momentumTensorComplexify : MomentumTensor →L[ℝ] ComplexMomentumTensor :=
  ContinuousLinearMap.piMap fun _ => periodicComplexifyVector

private def momentumTensorRealPart : ComplexMomentumTensor →L[ℝ] MomentumTensor :=
  ContinuousLinearMap.piMap fun _ => periodicRealPartVector

private theorem momentumTensorRealPart_complexify (q : MomentumTensor) :
    momentumTensorRealPart (momentumTensorComplexify q) = q :=
  funext fun i => periodicRealPartVector_complexifyVector (q i)

/-- The projected cutoff residual in (5.58) with the Euclidean momentum tensor and its divergence. -/
def truncatedEulerProjectedResidual (proj : (Vec3 → Vec3) → (Vec3 → Vec3))
    (ψ : Vec3 → ℝ) (Λ : ℝ) (gV gRV : C(UnitAddTorus (Fin 3), Vec3)) : Vec3 → Vec3 :=
  truncatedParentProjectedResidual momentumTensorComplexify momentumTensorRealPart momentumTensor
    momentumTensorDivergence proj ψ Λ gV gRV

/-- The velocity tail and (5.58) in physical Hölder norms. The constants work uniformly
on time slices, and the coefficient of the input residual is independent of `P`. -/
theorem truncatedEulerProjectedResidual_holder_bound
    (proj : (Vec3 → Vec3) → (Vec3 → Vec3)) {Cproj : ℝ} (hCproj : 0 ≤ Cproj)
    (hproj : ∀ f : Vec3 → Vec3, SpatiallyPeriodic f → SpatialHolderHalf 1 f →
      SpatialHolderHalf 1 (proj f) ∧ spatialHolderHalfNorm 1 (proj f) ≤ Cproj * spatialHolderHalfNorm 1 f)
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) (P : ℕ) (hP : 2 ≤ P) :
    let Cr := 4 * Cproj * (2 * (((1 : ℕ) : ℝ) + 1) *
      (1 + cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) 1))
    ∃ Ct : ℝ, 0 ≤ Ct ∧
      ∀ (Λ : ℝ), 1 ≤ Λ → ∀ gV gRV : C(UnitAddTorus (Fin 3), Vec3),
      SpatialHolderHalf P (fun x => gV (toUnitTorus x)) →
      SpatialHolderHalf 1 (fun x => gRV (toUnitTorus x)) →
      let V := fun x => gV (toUnitTorus x)
      let v := (fun x => realVectorFourierCutoff ψ Λ gV (toUnitTorus x)) - V
      let res := truncatedEulerProjectedResidual proj ψ Λ gV gRV
      let ε := Λ ^ ((2 : ℤ) - P) * (1 + spatialHolderHalfNorm P V)^2
      SpatialHolderHalf 2 v ∧ spatialHolderHalfNorm 2 v ≤ Ct * ε ∧
      SpatialHolderHalf 1 res ∧
        spatialHolderHalfNorm 1 res ≤ Cr * spatialHolderHalfNorm 1 (fun x => gRV (toUnitTorus x)) + Ct * ε :=
  truncatedParentProjectedResidual_holder_bound momentumTensorComplexify momentumTensorRealPart
    momentumTensorRealPart_complexify momentumTensor momentumTensorDivergence proj hCproj hproj
    hψ hs hunit P hP


/-- The bounds of Proposition 5.11 in the time-uniform spatial norms.
The time index can be the subtype of the closed time slab. -/
theorem truncatedEulerProjectedResidual_time_bound {ι : Type*} [Nonempty ι]
    (proj : (Vec3 → Vec3) → (Vec3 → Vec3)) {Cproj : ℝ} (hCproj : 0 ≤ Cproj)
    (hproj : ∀ f : Vec3 → Vec3, SpatiallyPeriodic f → SpatialHolderHalf 1 f →
      SpatialHolderHalf 1 (proj f) ∧ spatialHolderHalfNorm 1 (proj f) ≤ Cproj * spatialHolderHalfNorm 1 f)
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) (P : ℕ) (hP : 2 ≤ P) :
    let Cr := 4 * Cproj * (2 * (((1 : ℕ) : ℝ) + 1) *
      (1 + cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) 1))
    ∃ Ct : ℝ, 0 ≤ Ct ∧ ∀ (Λ : ℝ), 1 ≤ Λ →
      ∀ gV gRV : ι → C(UnitAddTorus (Fin 3), Vec3),
      let V := fun t x => gV t (toUnitTorus x)
      let RV := fun t x => gRV t (toUnitTorus x)
      (∀ t, SpatialHolderHalf P (V t)) →
      (∀ t, SpatialHolderHalf 1 (RV t)) →
      BddAbove (range fun t => spatialHolderHalfNorm P (V t)) →
      BddAbove (range fun t => spatialHolderHalfNorm 1 (RV t)) →
      let v := fun t => (fun x => realVectorFourierCutoff ψ Λ (gV t) (toUnitTorus x)) - V t
      let res := fun t => truncatedEulerProjectedResidual proj ψ Λ (gV t) (gRV t)
      let ε := Λ ^ ((2 : ℤ) - P) * (1 + (⨆ t, spatialHolderHalfNorm P (V t)))^2
      (⨆ t, spatialHolderHalfNorm 2 (v t)) ≤ Ct * ε ∧
      (⨆ t, spatialHolderHalfNorm 1 (res t)) ≤ Cr * (⨆ t, spatialHolderHalfNorm 1 (RV t)) + Ct * ε := by
  obtain ⟨Ct, hCt, h⟩ := truncatedEulerProjectedResidual_holder_bound proj hCproj hproj hψ hs hunit P hP
  refine ⟨Ct, hCt, ?_⟩
  intro Λ hΛ gV gRV V RV hV hRV hVbdd hRVbdd v res ε
  have hCr : 0 ≤ 4 * Cproj * (2 * (((1 : ℕ) : ℝ) + 1) *
      (1 + cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) 1)) := by
    have hC := cutoffHolderTailUniformConstant_nonneg' (cutoffSchwartzKernel hψ hs) 1
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (by linarith))
  have hτ : 0 ≤ Λ ^ ((2 : ℤ) - P) := zpow_nonneg (by linarith) _
  have hε (t : ι) : Λ ^ ((2 : ℤ) - P) * (1 + spatialHolderHalfNorm P (V t))^2 ≤ ε :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (by linarith [spatialHolderHalfNorm_nonneg' (hV t)])
      (add_le_add le_rfl (le_ciSup hVbdd t)) 2) hτ
  constructor
  · apply ciSup_le
    intro t
    exact (h Λ hΛ (gV t) (gRV t) (hV t) (hRV t)).2.1.trans
      (mul_le_mul_of_nonneg_left (hε t) hCt)
  · apply ciSup_le
    intro t
    exact (h Λ hΛ (gV t) (gRV t) (hV t) (hRV t)).2.2.2.trans
      (add_le_add (mul_le_mul_of_nonneg_left (le_ciSup hRVbdd t) hCr)
        (mul_le_mul_of_nonneg_left (hε t) hCt))

end QuantitativeResidual


/-- The truncation error in Proposition 5.11 satisfies (7.10) under the
full-depth bound for the approximate velocity in item 4 of §7. -/
theorem frequencySchedule_truncation_error_budget {μ size : ℝ} {b q qNext : ℕ}
    (hμ : 2 ≤ μ) (hb : 1 ≤ b) (hsize : 0 ≤ size)
    (hV : 1 + size ≤ 3 * (μ ^ frequencyExponent b q) ^
      (2 * (6 * frequencyExponent b qNext + 1))) :
    let freq := μ ^ frequencyExponent b q
    let P := 6 * frequencyExponent b qNext
    μ * ((freq ^ (5 : ℕ)) ^ ((2 : ℤ) - P) * (1 + size) ^ (2 : ℕ)) ≤
      (freq ^ frequencyExponent b qNext) ^ (-5 : ℝ) := by
  dsimp only
  let freq := μ ^ frequencyExponent b q
  let P := 6 * frequencyExponent b qNext
  have hfreq : 0 < freq := pow_pos (by linarith) _
  change 1 + size ≤ 3 * freq ^ (2 * (P + 1)) at hV
  change μ * ((freq ^ (5 : ℕ)) ^ ((2 : ℤ) - P) * (1 + size) ^ (2 : ℕ)) ≤ _
  have hcutoff : (freq ^ (5 : ℕ)) ^ ((2 : ℤ) - P) = freq ^ (5 * (2 - (P : ℝ))) := by
    rw [← Real.rpow_intCast, ← Real.rpow_natCast freq, ← Real.rpow_mul hfreq.le]
    push_cast
    norm_num
  have hhigh : (freq ^ (2 * (P + 1))) ^ (2 : ℕ) = freq ^ (4 * ((P : ℝ) + 1)) := by
    rw [← Real.rpow_natCast (freq ^ _), ← Real.rpow_natCast freq, ← Real.rpow_mul hfreq.le]
    push_cast
    congr 1
    ring
  calc
    _ ≤ μ * ((freq ^ (5 : ℕ)) ^ ((2 : ℤ) - P) * (3 * freq ^ (2 * (P + 1))) ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hV 2) (by positivity))
        (by linarith)
    _ = 9 * μ * freq ^ (5 * (2 - (P : ℝ)) + 4 * ((P : ℝ) + 1)) := by
      rw [hcutoff, mul_pow, hhigh, Real.rpow_add hfreq]
      ring
    _ ≤ _ := frequencySchedule_tail_absorption (q := q) (qNext := qNext) hμ hb

/-- A common lower bound on the next frequency absorbs the two terms of
the projected residual estimate into the third inverse power in §7, item 5. -/
theorem truncatedParent_residual_rate {next C : ℝ} (hC : 0 ≤ C)
    (hnext : max 2 ((2 * C) ^ (2 : ℕ)) ≤ next) :
    C * next ^ (-7 / 2 : ℝ) + next ^ (-5 : ℝ) ≤ next ^ (-3 : ℝ) := by
  have h₂ : 2 ≤ next := (le_max_left _ _).trans hnext
  have hp : 0 < next := by linarith
  have hroot : 2 * C ≤ next ^ (1 / 2 : ℝ) := by
    have h := Real.rpow_le_rpow (show 0 ≤ (2 * C) ^ (2 : ℕ) by positivity)
      ((le_max_right _ _).trans hnext) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ 2 * C by positivity)] at h
    norm_num at h
    exact h
  have hquadratic : 2 ≤ next ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact h₂.trans (le_self_pow₀ (by linarith) (by decide))
  have hR : (2 * C) * next ^ (-7 / 2 : ℝ) ≤ next ^ (-3 : ℝ) := by
    calc
      _ ≤ next ^ (1 / 2 : ℝ) * next ^ (-7 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hroot (by positivity)
      _ = _ := by rw [← Real.rpow_add hp]; norm_num
  have hE : 2 * next ^ (-5 : ℝ) ≤ next ^ (-3 : ℝ) := by
    calc
      _ ≤ next ^ (2 : ℝ) * next ^ (-5 : ℝ) :=
        mul_le_mul_of_nonneg_right hquadratic (by positivity)
      _ = _ := by rw [← Real.rpow_add hp]; norm_num
  linarith only [hR, hE]

/-- Proposition 5.11 and the residual and tail inputs from item 4 give
the two smallness bounds used to start item 5 of the induction. -/
theorem frequencySchedule_truncatedParent_rates
    {μ size C Ctail approxResidual residual velocityError : ℝ} {b q qNext : ℕ}
    (hμ : 2 ≤ μ) (hb : 1 ≤ b) (hsize : 0 ≤ size) (hC : 0 ≤ C) (hCtail : Ctail ≤ μ)
    (hV : 1 + size ≤ 3 * (μ ^ frequencyExponent b q) ^
      (2 * (6 * frequencyExponent b qNext + 1)))
    (hlarge : max 2 ((2 * C) ^ (2 : ℕ)) ≤ (μ ^ frequencyExponent b q) ^ frequencyExponent b qNext)
    (happrox : approxResidual ≤ 2 * (μ ^ frequencyExponent b q) ^ (2 + 1 / 16 : ℝ) *
      ((μ ^ frequencyExponent b q) ^ frequencyExponent b qNext) ^ (-4 : ℝ))
    (htruncated : let freq := μ ^ frequencyExponent b q
      let P := 6 * frequencyExponent b qNext
      let ε := (freq ^ (5 : ℕ)) ^ ((2 : ℤ) - P) * (1 + size) ^ (2 : ℕ)
      residual ≤ C * approxResidual + Ctail * ε ∧ velocityError ≤ Ctail * ε) :
    let next := (μ ^ frequencyExponent b q) ^ frequencyExponent b qNext
    residual ≤ next ^ (-3 : ℝ) ∧ velocityError ≤ next ^ (-5 : ℝ) := by
  dsimp only at htruncated ⊢
  let freq := μ ^ frequencyExponent b q
  let next := freq ^ frequencyExponent b qNext
  let P := 6 * frequencyExponent b qNext
  let ε := (freq ^ (5 : ℕ)) ^ ((2 : ℤ) - P) * (1 + size) ^ (2 : ℕ)
  have hfreq : 2 ≤ freq := by
    calc
      2 ≤ μ := hμ
      _ ≤ freq := le_self_pow₀ (by linarith) (by unfold frequencyExponent; positivity)
  have hεnonneg : 0 ≤ ε := by dsimp [ε, freq]; positivity
  have htail : Ctail * ε ≤ next ^ (-5 : ℝ) :=
    (mul_le_mul_of_nonneg_right hCtail hεnonneg).trans
      (frequencySchedule_truncation_error_budget hμ hb hsize hV)
  have hap : approxResidual ≤ next ^ (-7 / 2 : ℝ) :=
    happrox.trans (frequencySchedule_residual_budget hfreq hb)
  refine ⟨?_, htruncated.2.trans htail⟩
  calc
    residual ≤ C * approxResidual + Ctail * ε := htruncated.1
    _ ≤ C * next ^ (-7 / 2 : ℝ) + next ^ (-5 : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hap hC) htail
    _ ≤ next ^ (-3 : ℝ) := truncatedParent_residual_rate hC hlarge


end

end TorusEuler
