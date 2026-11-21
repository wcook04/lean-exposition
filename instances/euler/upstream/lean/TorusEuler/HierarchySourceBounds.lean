import TorusEuler.HierarchyProductEstimates
import TorusEuler.PhaseSource
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.List.Sort

/-! Finite weighted directional derivative and advection estimates for the
quadratic sources in (5.35). Coordinate directions may carry their weights
and the coframe or phase coefficient the reciprocal scale. -/

open scoped ContDiff InnerProductSpace

namespace TorusEuler

section ConstantDirections

variable {ι U E : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem phaseOperatorWord_append (D : ι → U → U) (v w : List ι) (f : U → E) :
    phaseOperatorWord D (v ++ w) f = phaseOperatorWord D v (phaseOperatorWord D w f) := by
  induction v with
  | nil => rfl
  | cons i v ih => simp only [List.cons_append, phaseOperatorWord, ih]

private theorem constantDirections_comm {f : U → E} (hf : ContDiff ℝ ∞ f) (v w : U) :
    phaseDirectionalDerivative (fun _ => v) (phaseDirectionalDerivative (fun _ => w) f) =
      phaseDirectionalDerivative (fun _ => w) (phaseDirectionalDerivative (fun _ => v) f) := by
  funext x
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hF : DifferentiableAt ℝ (fderiv ℝ f) x := hdf.differentiable (by simp) x
  have h (a b : U) :
      fderiv ℝ (fun y => fderiv ℝ f y b) x a = fderiv ℝ (fderiv ℝ f) x a b := by
    have h' := fderiv_clm_apply (u := fun _ : U => b) hF (differentiableAt_const b)
    rw [h', fderiv_const_apply]
    simp
  change fderiv ℝ (fun y => fderiv ℝ f y w) x v =
    fderiv ℝ (fun y => fderiv ℝ f y v) x w
  rw [h, h]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) v w

/-- Smooth directional derivatives in constant real directions are unchanged
by a permutation of the ordered coordinate word. -/
theorem phaseOperatorWord_constantDirections_perm (d : ι → U) {f : U → E}
    (hf : ContDiff ℝ ∞ f) {v w : List ι} (hvw : v.Perm w) :
    phaseOperatorWord (fun i _ => d i) v f = phaseOperatorWord (fun i _ => d i) w f := by
  induction hvw with
  | nil => rfl
  | cons i p ih => simp only [phaseOperatorWord, ih]
  | swap i j l =>
    simp only [phaseOperatorWord]
    exact constantDirections_comm (contDiff_phaseOperatorWord (fun _ => contDiff_const) hf l) _ _
  | trans p q hp hq => exact hp.trans hq

end ConstantDirections

section FiniteDerivatives

variable {ι T U E : Type*} [Fintype ι] [LinearOrder ι]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup E] [NormedSpace ℝ E]

private def appendSorted (i : ι) (w : List ι) : List ι := (w ++ [i]).mergeSort

omit [Fintype ι] in
private theorem appendSorted_perm (i : ι) (w : List ι) :
    (appendSorted i w).Perm (w ++ [i]) := List.mergeSort_perm _ _

private theorem appendSorted_mem (i : ι) {n : ℕ} {w : List ι}
    (hw : w ∈ hierarchyAdmissibleWords ι n) :
    appendSorted i w ∈ hierarchyAdmissibleWords ι (n + 1) := by
  have hlen := (appendSorted_perm i w).length_eq
  have hwlen := (mem_hierarchyAdmissibleWords.mp hw).1
  have hsort : (appendSorted i w).Pairwise (· ≤ ·) := List.pairwise_mergeSort' _ _
  apply mem_hierarchyAdmissibleWords.mpr
  simpa only [hlen, List.length_append, List.length_singleton] using ⟨Nat.succ_le_succ hwlen, hsort⟩

private theorem appendSorted_injective (i : ι) {n : ℕ} :
    Set.InjOn (appendSorted i) (hierarchyAdmissibleWords ι n : Set (List ι)) := by
  intro v hv w hw h
  have h₁' : (v ++ [i]).Perm (w ++ [i]) :=
    (appendSorted_perm i v).symm.trans (h ▸ appendSorted_perm i w)
  have hv' : (v ++ [i]).Perm (i :: v) := List.perm_append_comm
  have hw' : (w ++ [i]).Perm (i :: w) := List.perm_append_comm
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ a b => le_antisymm a b)
    (mem_hierarchyAdmissibleWords.mp hv).2 (mem_hierarchyAdmissibleWords.mp hw).2
    ((hv'.symm.trans (h₁'.trans hw')).cons_inv)

omit [Fintype ι] in
private theorem hierarchyJetValues_constDerivative (holder : Prop) (d : ι → U)
    {f : T → U → E} (hf : ∀ t, ContDiff ℝ ∞ (f t)) (i : ι) (w : List ι) :
    hierarchyJetValues holder (fun j _ => d j) w
        (fun t => phaseDirectionalDerivative (fun _ => d i) (f t)) =
      hierarchyJetValues holder (fun j _ => d j) (appendSorted i w) f := by
  have heq (t : T) :
      phaseOperatorWord (fun j _ => d j) w (phaseDirectionalDerivative (fun _ => d i) (f t)) =
        phaseOperatorWord (fun j _ => d j) (appendSorted i w) (f t) := by
    have h := phaseOperatorWord_constantDirections_perm d (hf t) (appendSorted_perm i w)
    rw [h, phaseOperatorWord_append]
    rfl
  simp only [hierarchyJetValues, heq]

/-- One additional admissible order controls differentiation in any one
constant weighted coordinate. This uses injective insertion of the
letter, with no factor depending on the number of words. -/
theorem hierarchyFiniteWordNorm_constDerivative_le (holder : Prop) (d : ι → U)
    {f : T → U → E} (hf : ∀ t, ContDiff ℝ ∞ (f t)) (i : ι) (n : ℕ)
    (hbdd : ∀ w ∈ hierarchyAdmissibleWords ι (n + 1),
      BddAbove (hierarchyJetValues holder (fun j _ => d j) w f)) :
    (∀ w ∈ hierarchyAdmissibleWords ι n,
      BddAbove (hierarchyJetValues holder (fun j _ => d j) w
        (fun t => phaseDirectionalDerivative (fun _ => d i) (f t)))) ∧
    hierarchyFiniteWordNorm holder (fun j _ => d j) n
        (fun t => phaseDirectionalDerivative (fun _ => d i) (f t)) ≤
      hierarchyFiniteWordNorm holder (fun j _ => d j) (n + 1) f := by
  classical
  let k := hierarchyAdmissibleWords ι n
  let k' := hierarchyAdmissibleWords ι (n + 1)
  let v (w : List ι) := sSup (hierarchyJetValues holder (fun j _ => d j) w f)
  have hsub : k.image (appendSorted i) ⊆ k' := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact appendSorted_mem i hz
  refine ⟨?_, ?_⟩
  · intro w hw
    rw [hierarchyJetValues_constDerivative holder d hf i w]
    exact hbdd _ (appendSorted_mem i hw)
  · unfold hierarchyFiniteWordNorm
    simp_rw [hierarchyJetValues_constDerivative holder d hf i]
    change (∑ w ∈ k, v (appendSorted i w)) ≤ ∑ w ∈ k', v w
    rw [← Finset.sum_image (appendSorted_injective i (n := n))]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun w hw _ => le_csSup (hbdd w hw) (Or.inl rfl))

end FiniteDerivatives

section Quadratic

variable {ι T U E F G : Type*} [Fintype ι] [LinearOrder ι]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem hierarchyFiniteWordNorm_nonneg (holder : Prop) (D : ι → U → U)
    (n : ℕ) (f : T → U → E)
    (hb : ∀ w ∈ hierarchyAdmissibleWords ι n, BddAbove (hierarchyJetValues holder D w f)) :
    0 ≤ hierarchyFiniteWordNorm holder D n f :=
  Finset.sum_nonneg fun w hw => le_csSup (hb w hw) (Or.inl rfl)

private theorem hierarchy_admissible_jet_bounds {holder : Prop} {D : ι → U → U}
    {n : ℕ} {f : T → U → E}
    (hb : ∀ w ∈ hierarchyAdmissibleWords ι n, BddAbove (hierarchyJetValues holder D w f))
    {w : List ι} (hw : w ∈ hierarchyAdmissibleWords ι n) (t : T) :
    let F := hierarchyFiniteWordNorm holder D n f
    (∀ x, ‖phaseOperatorWord D w (f t) x‖ ≤ F) ∧
      (holder → ∀ x y, ‖phaseOperatorWord D w (f t) x - phaseOperatorWord D w (f t) y‖ ≤
        F * Real.sqrt (dist x y)) := by
  have h : sSup (hierarchyJetValues holder D w f) ≤ hierarchyFiniteWordNorm holder D n f := by
    apply Finset.single_le_sum _ hw
    intro v hv
    exact le_csSup (hb v hv) (Or.inl rfl)
  refine ⟨fun x => (le_csSup (hb w hw) (Or.inr (Or.inl ⟨t, x, rfl⟩))).trans h, ?_⟩
  intro hh x y
  by_cases hxy : x = y
  · subst y
    simp
  · apply (div_le_iff₀ (Real.sqrt_pos.2 (dist_pos.mpr hxy))).mp
    exact (le_csSup (hb w hw) (Or.inr (Or.inr ⟨hh, t, x, y, rfl⟩))).trans h

private theorem hierarchyJetValues_bdd_bilinear (B : E →L[ℝ] F →L[ℝ] G)
    (holder : Prop) {D : ι → U → U} (hD : ∀ i, ContDiff ℝ ∞ (D i))
    (n : ℕ) {f : T → U → E} {g : T → U → F}
    (hf : ∀ t, ContDiff ℝ ∞ (f t)) (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (hfb : ∀ w ∈ hierarchyAdmissibleWords ι n, BddAbove (hierarchyJetValues holder D w f))
    (hgb : ∀ w ∈ hierarchyAdmissibleWords ι n, BddAbove (hierarchyJetValues holder D w g))
    (w : List ι) (hw : w ∈ hierarchyAdmissibleWords ι n) :
    BddAbove (hierarchyJetValues holder D w (fun t x => B (f t x) (g t x))) := by
  let fN := hierarchyFiniteWordNorm holder D n f
  let gN := hierarchyFiniteWordNorm holder D n g
  have hf₀ : 0 ≤ fN := hierarchyFiniteWordNorm_nonneg holder D n f hfb
  have hg₀ : 0 ≤ gN := hierarchyFiniteWordNorm_nonneg holder D n g hgb
  obtain ⟨hord, hsort⟩ := mem_hierarchyAdmissibleWords.mp hw
  have hsub (v : List ι) (hv : List.Sublist v w) : v ∈ hierarchyAdmissibleWords ι n :=
    mem_hierarchyAdmissibleWords.mpr ⟨hv.length_le.trans hord, hsort.sublist hv⟩
  have bound (t : T) := phaseOperatorWord_bilinear_bounds B hD (hf t) (hg t)
    w hf₀ (fun v hv => (hierarchy_admissible_jet_bounds hfb (hsub v hv) t).1)
    (fun v hv => (hierarchy_admissible_jet_bounds hgb (hsub v hv) t).1)
  let C := (2 : ℝ) ^ w.length * (2 * ‖B‖ * fN * gN)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, ?_⟩
  rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hh, t, x, y, rfl⟩)
  · exact hC
  · exact ((bound t).1 x).trans (by dsimp [C, fN, gN] at *; nlinarith)
  · by_cases hxy : x = y
    · subst y
      simpa only [sub_self, norm_zero, zero_div] using hC
    · exact (div_le_iff₀ (Real.sqrt_pos.2 (dist_pos.mpr hxy))).2
        ((bound t).2 (fun v hv => (hierarchy_admissible_jet_bounds hfb (hsub v hv) t).2 hh)
          (fun v hv => (hierarchy_admissible_jet_bounds hgb (hsub v hv) t).2 hh) x y)

/-- The product constant from (D.4) for an operator of norm at most one. -/
noncomputable def hierarchyQuadraticConstant (ι : Type*) [Fintype ι] [LinearOrder ι] (n : ℕ) : ℝ :=
  (hierarchyAdmissibleWords ι n).card * (2 : ℝ) ^ n * 2

/-- A concrete term of (5.35). The scalar coefficient is a linear form
applied to the advecting field. The reciprocal coordinate width may be
included in that form, leaving the derivative in the weighted direction. -/
theorem hierarchyFiniteWordNorm_advective_component_le
    (holder : Prop) (d : ι → U) (i : ι) (n : ℕ)
    {a : T → U → F →L[ℝ] ℝ} {z : T → U → F} {g : T → U → G}
    (ha : ∀ t, ContDiff ℝ ∞ (a t)) (hz : ∀ t, ContDiff ℝ ∞ (z t))
    (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (hab : ∀ w ∈ hierarchyAdmissibleWords ι n, BddAbove (hierarchyJetValues holder (fun j _ => d j) w a))
    (hzb : ∀ w ∈ hierarchyAdmissibleWords ι n, BddAbove (hierarchyJetValues holder (fun j _ => d j) w z))
    (hgb : ∀ w ∈ hierarchyAdmissibleWords ι (n + 1),
      BddAbove (hierarchyJetValues holder (fun j _ => d j) w g)) :
    let D := fun j (_ : U) => d j
    hierarchyFiniteWordNorm holder D n (fun t x =>
      a t x (z t x) • phaseDirectionalDerivative (D i) (g t) x) ≤
      hierarchyQuadraticConstant ι n ^ 2 * hierarchyFiniteWordNorm holder D n a *
        hierarchyFiniteWordNorm holder D n z * hierarchyFiniteWordNorm holder D (n + 1) g := by
  let D := fun j (_ : U) => d j
  let v (t : T) := phaseDirectionalDerivative (D i) (g t)
  let c := fun (t : T) (x : U) => a t x (z t x)
  let K := hierarchyQuadraticConstant ι n
  let aN := hierarchyFiniteWordNorm holder D n a
  let zN := hierarchyFiniteWordNorm holder D n z
  let gN := hierarchyFiniteWordNorm holder D (n + 1) g
  have hD (j : ι) : ContDiff ℝ ∞ (D j) := contDiff_const
  have hc (t : T) : ContDiff ℝ ∞ (c t) := (ha t).clm_apply (hz t)
  have hv (t : T) : ContDiff ℝ ∞ (v t) := ((hg t).fderiv_right (by simp)).clm_apply contDiff_const
  obtain ⟨hvbd, hvle⟩ := hierarchyFiniteWordNorm_constDerivative_le holder d hg i n hgb
  have hcbd := hierarchyJetValues_bdd_bilinear
    (ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℝ))
    holder hD n ha hz hab hzb
  have hcle : hierarchyFiniteWordNorm holder D n c ≤ K * aN * zN := by
    exact (hierarchyFiniteWordNorm_clm_apply_le holder hD n ha hz hab hzb).trans_eq (by
      dsimp [K, aN, zN, hierarchyQuadraticConstant]
      ring)
  let B : ℝ →L[ℝ] G →L[ℝ] G := ContinuousLinearMap.lsmul ℝ ℝ
  have hB : ‖B‖ ≤ 1 := ContinuousLinearMap.opNorm_lsmul_le
  have ha₀ : 0 ≤ aN := hierarchyFiniteWordNorm_nonneg holder D n a hab
  have hz₀ : 0 ≤ zN := hierarchyFiniteWordNorm_nonneg holder D n z hzb
  have hc₀ : 0 ≤ hierarchyFiniteWordNorm holder D n c :=
    hierarchyFiniteWordNorm_nonneg holder D n c hcbd
  have hv₀ : 0 ≤ hierarchyFiniteWordNorm holder D n v :=
    hierarchyFiniteWordNorm_nonneg holder D n v hvbd
  have hg₀ : 0 ≤ gN := hierarchyFiniteWordNorm_nonneg holder D (n + 1) g hgb
  have hK : 0 ≤ K := by dsimp [K, hierarchyQuadraticConstant]; positivity
  change hierarchyFiniteWordNorm holder D n (fun t x => B (c t x) (v t x)) ≤ _
  calc
    _ ≤ (hierarchyAdmissibleWords ι n).card * (2 : ℝ) ^ n *
        (2 * ‖B‖ * hierarchyFiniteWordNorm holder D n c * hierarchyFiniteWordNorm holder D n v) :=
      hierarchyFiniteWordNorm_bilinear_le B holder hD n hc hv hcbd hvbd
    _ ≤ (hierarchyAdmissibleWords ι n).card * (2 : ℝ) ^ n * (2 * 1 * (K * aN * zN) * gN) := by
      gcongr
    _ = _ := by dsimp [K, aN, zN, gN, hierarchyQuadraticConstant]; ring

end Quadratic

section PhaseAdvection

variable {T G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The phase coefficient after factoring out the width in the scaled
derivative. It is the linear form (Z \mapsto (Z\cdot\kappa)/h\). -/
noncomputable def hierarchyScaledPhaseCoefficient (h : ℝ) (κ : T → (Vec3 × ℝ) → Vec3) :
    T → (Vec3 × ℝ) → Vec3 →L[ℝ] ℝ :=
  fun t x => h⁻¹ • innerSL ℝ (κ t x)

/-- Fast advection in (5.35), with the exact undifferentiated advector and
one derivative on the advected field. The supplied coefficient bound
accounts for the phase cost (h^{-1}|\kappa|\). -/
theorem hierarchyFastAdvection_le (ℓ h : ℝ) (hh : h ≠ 0) (n : ℕ) {freq L : ℝ}
    {κ z : T → (Vec3 × ℝ) → Vec3} {g : T → (Vec3 × ℝ) → G}
    (hκ : ∀ t, ContDiff ℝ ∞ (κ t)) (hz : ∀ t, ContDiff ℝ ∞ (z t))
    (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (hκb : ∀ w ∈ hierarchyAdmissibleWords (Fin 4) n,
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w
        (hierarchyScaledPhaseCoefficient h κ)))
    (hzb : ∀ w ∈ hierarchyAdmissibleWords (Fin 4) n,
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w z))
    (hgb : ∀ w ∈ hierarchyAdmissibleWords (Fin 4) (n + 1),
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w g))
    (hκN : hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n
      (hierarchyScaledPhaseCoefficient h κ) ≤ L * freq ^ (3 / 2 : ℝ)) :
    hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n
      (fun t x => ⟪κ t x, z t x⟫_ℝ • fderiv ℝ (g t) x (0, 1)) ≤
      hierarchyQuadraticConstant (Fin 4) n ^ 2 * (L * freq ^ (3 / 2 : ℝ)) *
        hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n z *
        hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) (n + 1) g := by
  let d (i : Fin 4) := hierarchyMixedDirection ℓ h i 0
  let D := hierarchyMixedDirection ℓ h
  let a := hierarchyScaledPhaseCoefficient h κ
  have ha (t : T) : ContDiff ℝ ∞ (a t) :=
    ((innerSL ℝ).contDiff.comp (hκ t)).const_smul h⁻¹
  have heq :
      (fun t x => a t x (z t x) • phaseDirectionalDerivative (D (Fin.last 3)) (g t) x) =
      (fun t x => ⟪κ t x, z t x⟫_ℝ • fderiv ℝ (g t) x (0, 1)) := by
    funext t x
    simp only [a, hierarchyScaledPhaseCoefficient, _root_.smul_apply, innerSL_apply_apply,
      phaseDirectionalDerivative, D, hierarchyMixedDirection, Fin.lastCases_last,
      phaseCoordinateDirection, map_smul, smul_eq_mul, smul_smul]
    rw [mul_right_comm, inv_mul_cancel₀ hh, one_mul]
  have hb := hierarchyFiniteWordNorm_advective_component_le False d (Fin.last 3) n
    ha hz hg hκb hzb hgb
  change hierarchyFiniteWordNorm False D n
      (fun t x => a t x (z t x) • phaseDirectionalDerivative (D (Fin.last 3)) (g t) x) ≤ _ at hb
  rw [heq] at hb
  have hz₀ := hierarchyFiniteWordNorm_nonneg False D n z hzb
  have hg₀ := hierarchyFiniteWordNorm_nonneg False D (n + 1) g hgb
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκN (sq_nonneg _)) hz₀) hg₀)

/-- A row of the inverse deformation divided by the label scale. -/
noncomputable def hierarchyScaledCoframeRow (ℓ : ℝ)
    (A : T → (Vec3 × ℝ) → Vec3 →L[ℝ] Vec3) (i : Fin 3) :
    T → (Vec3 × ℝ) → Vec3 →L[ℝ] ℝ :=
  fun t x => ℓ⁻¹ • (EuclideanSpace.proj i).comp (A t x)

/-- A label component of slow advection in (5.35). Its coefficient
contains the inverse deformation and the reciprocal label scale. -/
theorem hierarchySlowAdvectionComponent_le (ℓ h : ℝ) (hℓ : ℓ ≠ 0) (i : Fin 3) (n : ℕ) {L : ℝ}
    {A : T → (Vec3 × ℝ) → Vec3 →L[ℝ] Vec3} {z : T → (Vec3 × ℝ) → Vec3}
    {g : T → (Vec3 × ℝ) → G}
    (hA : ∀ t, ContDiff ℝ ∞ (A t)) (hz : ∀ t, ContDiff ℝ ∞ (z t))
    (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (hAb : ∀ w ∈ hierarchyAdmissibleWords (Fin 4) n,
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w
        (hierarchyScaledCoframeRow ℓ A i)))
    (hzb : ∀ w ∈ hierarchyAdmissibleWords (Fin 4) n,
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w z))
    (hgb : ∀ w ∈ hierarchyAdmissibleWords (Fin 4) (n + 1),
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w g))
    (hAN : hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n
      (hierarchyScaledCoframeRow ℓ A i) ≤ L) :
    hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n
      (fun t x => (A t x (z t x)) i • fderiv ℝ (g t) x (coordinateDirection i, 0)) ≤
      hierarchyQuadraticConstant (Fin 4) n ^ 2 * L *
        hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n z *
        hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) (n + 1) g := by
  let d (j : Fin 4) := hierarchyMixedDirection ℓ h j 0
  let D := hierarchyMixedDirection ℓ h
  let a := hierarchyScaledCoframeRow ℓ A i
  have ha (t : T) : ContDiff ℝ ∞ (a t) :=
    ((ContinuousLinearMap.compL ℝ Vec3 Vec3 ℝ (EuclideanSpace.proj i)).contDiff.comp
      (hA t)).const_smul ℓ⁻¹
  have heq :
      (fun t x => a t x (z t x) • phaseDirectionalDerivative (D i.castSucc) (g t) x) =
      (fun t x => (A t x (z t x)) i • fderiv ℝ (g t) x (coordinateDirection i, 0)) := by
    funext t x
    change (ℓ⁻¹ * (A t x (z t x)) i) •
      (fderiv ℝ (g t) x) (D i.castSucc x) = _
    simp only [D, hierarchyMixedDirection, Fin.lastCases_castSucc, phaseCoordinateDirection,
      map_smul, smul_smul]
    rw [mul_right_comm, inv_mul_cancel₀ hℓ, one_mul]
  have hb := hierarchyFiniteWordNorm_advective_component_le False d i.castSucc n ha hz hg hAb hzb hgb
  change hierarchyFiniteWordNorm False D n
      (fun t x => a t x (z t x) • phaseDirectionalDerivative (D i.castSucc) (g t) x) ≤ _ at hb
  rw [heq] at hb
  have hz₀ := hierarchyFiniteWordNorm_nonneg False D n z hzb
  have hg₀ := hierarchyFiniteWordNorm_nonneg False D (n + 1) g hgb
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAN (sq_nonneg _)) hz₀) hg₀)

end PhaseAdvection

section HolderInterpolation

variable {T G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The weighted label directions for a phase-independent field. -/
noncomputable def hierarchyLabelDirection (ℓ : ℝ) (i : Fin 3) (_ : Vec3) : Vec3 :=
  ℓ • coordinateDirection i

private theorem norm_labelLinearMap_le_sum (A : Vec3 →L[ℝ] G) :
    ‖A‖ ≤ ∑ i : Fin 3, ‖A (coordinateDirection i)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro x
  have hx : ∑ i : Fin 3, (x i) • coordinateDirection i = x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, coordinateDirection]
      using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
  calc
    ‖A x‖ = ‖∑ i : Fin 3, (x i) • A (coordinateDirection i)‖ := by
      have h := congrArg A hx
      rw [map_sum] at h
      simp only [map_smul] at h
      exact congrArg norm h.symm
    _ ≤ ∑ i : Fin 3, ‖(x i) • A (coordinateDirection i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖A (coordinateDirection i)‖ * ‖x‖ := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x i) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]

/-- The geometric-mean estimate used in (D.2), with one supplied bound
on the derivative. -/
private theorem norm_sub_sqrt_of_derivative {f : Vec3 → G} (hf : Differentiable ℝ f)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hval : ∀ x, ‖f x‖ ≤ A) (hderiv : ∀ x, ‖fderiv ℝ f x‖ ≤ B) (x y : Vec3) :
    ‖f x - f y‖ ≤ Real.sqrt (2 * A * B) * Real.sqrt (dist x y) := by
  have hdiff : ‖f x - f y‖ ≤ B * dist x y := by
    simpa only [dist_eq_norm] using
      (convex_univ : Convex ℝ (Set.univ : Set Vec3)).norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => hf z) (fun z _ => hderiv z) (Set.mem_univ y) (Set.mem_univ x)
  have hsum : ‖f x - f y‖ ≤ 2 * A := by
    rw [two_mul]
    exact (norm_sub_le _ _).trans (add_le_add (hval x) (hval y))
  have hsq : ‖f x - f y‖ ^ 2 ≤ (2 * A * B) * dist x y := by
    rw [sq, mul_assoc]
    exact mul_le_mul hsum hdiff (norm_nonneg _) (by positivity)
  rw [← Real.sqrt_mul (by positivity)]
  exact Real.le_sqrt_of_sq_le hsq

/-- The phase-independent half-Hölder estimate (D.2) in the finite
coordinate norm. With the max convention for the Hölder norm, the bound
uses the absolute constant four and one extra label derivative. -/
theorem hierarchyFiniteWordNorm_holder_le (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ₁ : ℓ ≤ 1)
    (n : ℕ) {f : T → Vec3 → G} (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hb : ∀ w ∈ hierarchyAdmissibleWords (Fin 3) (n + 1),
      BddAbove (hierarchyJetValues False (hierarchyLabelDirection ℓ) w f)) :
    hierarchyFiniteWordNorm True (hierarchyLabelDirection ℓ) n f ≤
      4 * hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) (n + 1) f /
        Real.sqrt ℓ := by
  let D := hierarchyLabelDirection ℓ
  let d (i : Fin 3) := D i 0
  let K := hierarchyAdmissibleWords (Fin 3) n
  let K' := hierarchyAdmissibleWords (Fin 3) (n + 1)
  let A (w : List (Fin 3)) := sSup (hierarchyJetValues False D w f)
  let B (i : Fin 3) (w : List (Fin 3)) := A (appendSorted i w)
  let N := hierarchyFiniteWordNorm False D (n + 1) f
  have hK : K ⊆ K' := fun w hw => by
    obtain ⟨hord, hsort⟩ := mem_hierarchyAdmissibleWords.mp hw
    exact mem_hierarchyAdmissibleWords.mpr ⟨hord.trans (Nat.le_succ _), hsort⟩
  have ha₀ (w : List (Fin 3)) (hw : w ∈ K') : 0 ≤ A w := le_csSup (hb w hw) (Or.inl rfl)
  have hsℓ : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ
  have hsℓ₁ : Real.sqrt ℓ ≤ 1 := by simpa using Real.sqrt_le_sqrt hℓ₁
  have hTerm (w : List (Fin 3)) (hw : w ∈ K) :
      sSup (hierarchyJetValues True D w f) ≤ (A w + ∑ i : Fin 3, B i w) / Real.sqrt ℓ := by
    let b := ∑ i : Fin 3, B i w
    let g (t : T) := phaseOperatorWord D w (f t)
    have ha : 0 ≤ A w := ha₀ w (hK hw)
    have hbi (i : Fin 3) : 0 ≤ B i w := ha₀ _ (appendSorted_mem i hw)
    have hbb : 0 ≤ b := Finset.sum_nonneg fun i _ => hbi i
    have hval (t : T) (x : Vec3) : ‖g t x‖ ≤ A w :=
      le_csSup (hb w (hK hw)) (Or.inr (Or.inl ⟨t, x, rfl⟩))
    have hderiv (t : T) (x : Vec3) : ‖fderiv ℝ (g t) x‖ ≤ b / ℓ := by
      refine (norm_labelLinearMap_le_sum _).trans ?_
      rw [show b / ℓ = ∑ i : Fin 3, B i w / ℓ from Finset.sum_div _ _ _]
      refine Finset.sum_le_sum fun i _ => ?_
      have hperm : (i :: w).Perm (appendSorted i w) :=
        (show ([i] ++ w).Perm (w ++ [i]) from List.perm_append_comm).trans
          (appendSorted_perm i w).symm
      have heq := congrFun (phaseOperatorWord_constantDirections_perm d (hf t) hperm) x
      have hp : ‖phaseOperatorWord D (appendSorted i w) (f t) x‖ ≤ B i w :=
        le_csSup (hb _ (appendSorted_mem i hw)) (Or.inr (Or.inl ⟨t, x, rfl⟩))
      change fderiv ℝ (g t) x (ℓ • coordinateDirection i) =
        phaseOperatorWord D (appendSorted i w) (f t) x at heq
      rw [← heq, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hℓ] at hp
      exact (le_div_iff₀ hℓ).2 (by simpa only [mul_comm] using hp)
    have h0 : 0 ≤ (A w + b) / Real.sqrt ℓ := by positivity
    apply csSup_le (show (hierarchyJetValues True D w f).Nonempty from ⟨0, Or.inl rfl⟩)
    rintro r (rfl | ⟨t, x, rfl⟩ | ⟨_, t, x, y, rfl⟩)
    · exact h0
    · apply (le_div_iff₀ hsℓ).2
      exact (mul_le_mul (hval t x) hsℓ₁ (Real.sqrt_nonneg _) ha).trans (by linarith)
    · by_cases hxy : x = y
      · subst y
        simpa only [sub_self, norm_zero, zero_div] using h0
      · apply (div_le_iff₀ (Real.sqrt_pos.2 (dist_pos.mpr hxy))).2
        have hd : Differentiable ℝ (g t) :=
          (contDiff_phaseOperatorWord (fun _ => contDiff_const) (hf t) w).differentiable (by simp)
        refine (norm_sub_sqrt_of_derivative hd ha (div_nonneg hbb hℓ.le)
          (hval t) (hderiv t) x y).trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
        rw [show 2 * A w * (b / ℓ) = (2 * A w * b) / ℓ by ring,
          Real.sqrt_div (by positivity)]
        apply div_le_div_of_nonneg_right _ hsℓ.le
        exact Real.sqrt_le_iff.mpr ⟨add_nonneg ha hbb, by nlinarith [sq_nonneg (A w), sq_nonneg b]⟩
  have hsumA : ∑ w ∈ K, A w ≤ N :=
    Finset.sum_le_sum_of_subset_of_nonneg hK (fun w hw _ => ha₀ w hw)
  have hsumB (i : Fin 3) : ∑ w ∈ K, B i w ≤ N := by
    have h := (hierarchyFiniteWordNorm_constDerivative_le False d hf i n hb).2
    unfold hierarchyFiniteWordNorm at h
    simp_rw [hierarchyJetValues_constDerivative False d hf i] at h
    exact h
  calc
    _ ≤ ∑ w ∈ K, (A w + ∑ i : Fin 3, B i w) / Real.sqrt ℓ := Finset.sum_le_sum hTerm
    _ = ((∑ w ∈ K, A w) + ∑ i : Fin 3, ∑ w ∈ K, B i w) / Real.sqrt ℓ := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_comm (s := K)]
    _ ≤ (N + ∑ _i : Fin 3, N) / Real.sqrt ℓ :=
      div_le_div_of_nonneg_right (add_le_add hsumA (Finset.sum_le_sum fun i _ => hsumB i)) hsℓ.le
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

end HolderInterpolation

end TorusEuler
