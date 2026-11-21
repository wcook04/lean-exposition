import Breakdown.FracCell.GivenModelDefs

open MeasureTheory

noncomputable section

namespace Breakdown.FracInternal.GivenModelModelFrame

open CellCert CellCert.GivenModel CellCert.CellAnalysis SteadyCert

theorem frameUnit_coord (θ : ℝ) (a b : Fin 3) :
    ∑ i : Fin 3, frameUnit θ a i * frameUnit θ b i = if a = b then 1 else 0 := by
  have h := Real.cos_sq_add_sin_sq θ
  fin_cases a <;> fin_cases b <;>
    simp [frameUnit, radialUnit, angularUnit, axialUnit, Fin.sum_univ_three] <;> nlinarith [h]

theorem frameUnit_norm (θ : ℝ) (a : Fin 3) : ‖frameUnit θ a‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  fin_cases a <;> simp [Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit]

theorem single_cont (i : Fin 3) :
    Continuous fun t : ℝ => (EuclideanSpace.single i t : Space) := by
  have h : (fun t : ℝ => (EuclideanSpace.single i t : Space)) =
      fun t => t • (EuclideanSpace.single i 1 : Space) := by
    funext t
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [h]
  exact continuous_id.smul continuous_const

theorem frameUnit_cont (a : Fin 3) : Continuous fun θ : ℝ => frameUnit θ a := by
  fin_cases a
  · exact ((single_cont 0).comp Real.continuous_cos).add ((single_cont 1).comp Real.continuous_sin)
  · exact ((single_cont 0).comp Real.continuous_sin.neg).add ((single_cont 1).comp Real.continuous_cos)
  · exact continuous_const

theorem cartOp_apply (θ : ℝ) (M : Fin 3 → Fin 3 → ℝ) (u : Space) :
    cartOpOfFrame θ M u = ∑ a : Fin 3, ∑ b : Fin 3, (M a b * inner ℝ (frameUnit θ b) u) • frameUnit θ a := by
  simp [cartOpOfFrame, ContinuousLinearMap.smulRight_apply, smul_smul]

theorem cartOp_symm (θ : ℝ) (M : Fin 3 → Fin 3 → ℝ) (hM : ∀ a b, M a b = M b a) (u w : Space) :
    inner ℝ (cartOpOfFrame θ M u) w = inner ℝ u (cartOpOfFrame θ M w) := by
  simp only [cartOp_apply, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hM b a, real_inner_comm (frameUnit θ a) u]
  ring

theorem entry_eq (A : Space →L[ℝ] Space) (i : Fin 3) : entry A i i = inner ℝ (A (unitVector i)) (unitVector i) := by
  simp [entry, unitVector, EuclideanSpace.inner_single_right]

theorem cartOp_trace (θ : ℝ) (M : Fin 3 → Fin 3 → ℝ) :
    ∑ i : Fin 3, entry (cartOpOfFrame θ M) i i = ∑ a : Fin 3, M a a := by
  simp only [entry_eq, cartOp_apply, sum_inner, real_inner_smul_left]
  simp only [unitVector, EuclideanSpace.inner_single_right, one_mul, conj_trivial]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum, frameUnit_coord]
  simp

theorem cartOp_cont : Continuous fun q : ℝ × (Fin 3 → Fin 3 → ℝ) => cartOpOfFrame q.1 q.2 := by
  unfold cartOpOfFrame
  have h := frameUnit_cont
  fun_prop

theorem cart_cont : Continuous fun q : ℝ × (Fin 3 → ℝ) => cartOfFrame q.1 q.2 := by
  unfold cartOfFrame
  have h := frameUnit_cont
  fun_prop

end Breakdown.FracInternal.GivenModelModelFrame

namespace Breakdown.FracInternal.GivenModelModelFrame

open CellCert CellCert.GivenModel CellCert.CellAnalysis SteadyCert

def harmonicAt (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → CellPoly d) (r z θ : ℝ) : ℝ :=
  (∑ β : Fin (J + 1), (((if (β : ℕ) = 0 then (1 : ℝ) else 2) : ℝ) : ℂ) * evalPoly (P β) r z *
    Complex.exp ((azimuth m (β : ℤ) * θ : ℝ) * Complex.I)).re

theorem harmonicValue_eq (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → CellPoly d) (y : Space) :
    harmonicValue m P y = harmonicAt m P (cylRadius y) |cylHeight y| (cylAngle y) := rfl

theorem evalPoly_cont {d : ℕ} (P : CellPoly d) : Continuous fun q : ℝ × ℝ => evalPoly P q.1 q.2 := by
  unfold evalPoly
  fun_prop

theorem harmonicAt_cont (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → CellPoly d) :
    Continuous fun q : ℝ × ℝ × ℝ => harmonicAt m P q.1 q.2.1 q.2.2 := by
  unfold harmonicAt evalPoly
  fun_prop

theorem cont_coord (i : Fin 3) : Continuous fun y : Space => y i := by fun_prop

theorem cylRadius_cont : Continuous cylRadius := by
  unfold cylRadius
  fun_prop

theorem cylHeight_cont : Continuous cylHeight := by
  unfold cylHeight
  fun_prop

theorem cylAngle_meas : Measurable cylAngle := by
  unfold cylAngle
  exact Complex.measurable_arg.comp (by fun_prop : Continuous fun y : Space => (y 0 : ℂ) + (y 1 : ℂ) * Complex.I).measurable

theorem harmonicValue_meas (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → CellPoly d) : Measurable (harmonicValue m P) := by
  have e : harmonicValue m P = (fun q : ℝ × ℝ × ℝ => harmonicAt m P q.1 q.2.1 q.2.2) ∘
      (fun y => (cylRadius y, |cylHeight y|, cylAngle y)) := rfl
  rw [e]
  exact (harmonicAt_cont m P).measurable.comp (cylRadius_cont.measurable.prodMk
    ((cylHeight_cont.abs).measurable.prodMk cylAngle_meas))

theorem harmonicValue_bound (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → CellPoly d) (R Z : ℝ) :
    ∃ C : ℝ, ∀ y, cylRadius y ≤ R → |cylHeight y| ≤ Z → |harmonicValue m P y| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R)).prod ((isCompact_Icc (a := (0 : ℝ)) (b := Z)).prod
    (isCompact_Icc (a := -Real.pi) (b := Real.pi))) |>.exists_bound_of_continuousOn (harmonicAt_cont m P).continuousOn
  refine ⟨C, fun y hr hz => ?_⟩
  have := hC (cylRadius y, |cylHeight y|, cylAngle y)
    ⟨⟨Real.sqrt_nonneg _, hr⟩, ⟨abs_nonneg _, hz⟩, ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩⟩
  simpa [harmonicValue_eq, Real.norm_eq_abs] using this

theorem vectorSign_meas (a : Fin 3) : Measurable fun y => vectorSign y a := by
  unfold vectorSign
  exact Measurable.ite ((measurableSet_lt cylHeight_cont.measurable measurable_const).inter
    (MeasurableSet.const _)) measurable_const measurable_const

theorem pseudoSign_meas (a : Fin 3) : Measurable fun y => pseudoSign y a := by
  unfold pseudoSign
  exact Measurable.ite (measurableSet_lt cylHeight_cont.measurable measurable_const) (vectorSign_meas a).neg
    measurable_const

theorem vectorSign_abs (y : Space) (a : Fin 3) : |vectorSign y a| = 1 := by
  unfold vectorSign
  split_ifs <;> simp

theorem pseudoSign_abs (y : Space) (a : Fin 3) : |pseudoSign y a| = 1 := by
  unfold pseudoSign
  split_ifs <;> simp [vectorSign_abs]

theorem cart_norm (θ : ℝ) (w : Fin 3 → ℝ) : ‖cartOfFrame θ w‖ ≤ ∑ a, |w a| := by
  unfold cartOfFrame
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [norm_smul, frameUnit_norm, mul_one, Real.norm_eq_abs]

theorem cartOp_norm (θ : ℝ) (M : Fin 3 → Fin 3 → ℝ) : ‖cartOpOfFrame θ M‖ ≤ ∑ a, ∑ b, |M a b| := by
  unfold cartOpOfFrame
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, frameUnit_norm, frameUnit_norm,
    Real.norm_eq_abs]
  simp

end Breakdown.FracInternal.GivenModelModelFrame

namespace Breakdown.FracInternal.GivenModelModelFrame

open CellCert CellCert.GivenModel CellCert.CellAnalysis SteadyCert

theorem cart_sm (σ : Space → Fin 3 → ℝ) (hσ : ∀ a, Measurable fun y => σ y a) (h : Fin 3 → Space → ℝ)
    (hh : ∀ a, Measurable (h a)) :
    StronglyMeasurable fun y => cartOfFrame (cylAngle y) (fun a => σ y a * h a y) := by
  have hm : Measurable fun y => (cylAngle y, fun a => σ y a * h a y) :=
    cylAngle_meas.prodMk (measurable_pi_lambda _ fun a => (hσ a).mul (hh a))
  exact cart_cont.comp_stronglyMeasurable hm.stronglyMeasurable

theorem cartOp_sm0 (F : Space → Fin 3 → Fin 3 → ℝ) (hF : Measurable F) :
    StronglyMeasurable fun y => cartOpOfFrame (cylAngle y) (F y) := by
  have hs : StronglyMeasurable fun y => (cylAngle y, F y) := (cylAngle_meas.prodMk hF).stronglyMeasurable
  have h := cartOp_cont.comp_stronglyMeasurable hs
  exact h

theorem cartOp_sm (σ : Space → Fin 3 → Fin 3 → ℝ) (hσ : ∀ a b, Measurable fun y => σ y a b)
    (h : Fin 3 → Fin 3 → Space → ℝ) (hh : ∀ a b, Measurable (h a b)) :
    StronglyMeasurable fun y => cartOpOfFrame (cylAngle y) (fun a b => σ y a b * h a b y) := by
  have hF : Measurable fun y => fun a b => σ y a b * h a b y :=
    measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => (hσ a b).mul (hh a b)
  exact cartOp_sm0 _ hF

theorem cart_bound (σ : Space → Fin 3 → ℝ) (hσ : ∀ y a, |σ y a| ≤ 1) (h : Fin 3 → Space → ℝ) (S : Set Space)
    (hb : ∀ a, ∃ C, ∀ y ∈ S, |h a y| ≤ C) :
    ∃ C, ∀ y ∈ S, ‖cartOfFrame (cylAngle y) (fun a => σ y a * h a y)‖ ≤ C := by
  choose C hC using hb
  refine ⟨∑ a, C a, fun y hy => (cart_norm _ _).trans (Finset.sum_le_sum fun a _ => ?_)⟩
  rw [abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (hσ y a)).trans (hC a y hy)

theorem cartOp_bound (σ : Space → Fin 3 → Fin 3 → ℝ) (hσ : ∀ y a b, |σ y a b| ≤ 1) (h : Fin 3 → Fin 3 → Space → ℝ)
    (S : Set Space) (hb : ∀ a b, ∃ C, ∀ y ∈ S, |h a b y| ≤ C) :
    ∃ C, ∀ y ∈ S, ‖cartOpOfFrame (cylAngle y) (fun a b => σ y a b * h a b y)‖ ≤ C := by
  choose C hC using hb
  refine ⟨∑ a, ∑ b, C a b, fun y hy => (cartOp_norm _ _).trans (Finset.sum_le_sum fun a _ =>
    Finset.sum_le_sum fun b _ => ?_)⟩
  rw [abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (hσ y a b)).trans (hC a b y hy)

theorem harmonic_solid (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → CellPoly d) (K : CellBox) :
    ∃ C, ∀ y ∈ K.solid, |harmonicValue m P y| ≤ C := by
  obtain ⟨C, hC⟩ := harmonicValue_bound m P K.r₂ K.z₂
  exact ⟨C, fun y hy => hC y hy.2.1 hy.2.2.2⟩

theorem vectorOf_sm (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → CellPoly d) : StronglyMeasurable (vectorOf m P) :=
  cart_sm _ vectorSign_meas _ fun a => harmonicValue_meas m _

theorem pseudoOf_sm (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → CellPoly d) : StronglyMeasurable (pseudoOf m P) :=
  cart_sm _ pseudoSign_meas _ fun a => harmonicValue_meas m _

theorem tensorOf_sm (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d) :
    StronglyMeasurable (tensorOf m P) :=
  cartOp_sm (fun y a b => vectorSign y a * vectorSign y b) (fun a b => (vectorSign_meas a).mul (vectorSign_meas b))
    _ fun a b => harmonicValue_meas m _

theorem pseudoTensorOf_sm (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d) :
    StronglyMeasurable (pseudoTensorOf m P) :=
  cartOp_sm (fun y a b => pseudoSign y a * vectorSign y b) (fun a b => (pseudoSign_meas a).mul (vectorSign_meas b))
    _ fun a b => harmonicValue_meas m _

theorem vectorOf_bd (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → CellPoly d) (K : CellBox) :
    ∃ C, ∀ y ∈ K.solid, ‖vectorOf m P y‖ ≤ C :=
  cart_bound _ (fun y a => (vectorSign_abs y a).le) _ _ fun a => harmonic_solid m _ K

theorem pseudoOf_bd (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → CellPoly d) (K : CellBox) :
    ∃ C, ∀ y ∈ K.solid, ‖pseudoOf m P y‖ ≤ C :=
  cart_bound _ (fun y a => (pseudoSign_abs y a).le) _ _ fun a => harmonic_solid m _ K

theorem tensorOf_bd (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d) (K : CellBox) :
    ∃ C, ∀ y ∈ K.solid, ‖tensorOf m P y‖ ≤ C :=
  cartOp_bound (fun y a b => vectorSign y a * vectorSign y b)
    (fun y a b => by rw [abs_mul, vectorSign_abs, vectorSign_abs, one_mul]) _ _ fun a b => harmonic_solid m _ K

theorem pseudoTensorOf_bd (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d) (K : CellBox) :
    ∃ C, ∀ y ∈ K.solid, ‖pseudoTensorOf m P y‖ ≤ C :=
  cartOp_bound (fun y a b => pseudoSign y a * vectorSign y b)
    (fun y a b => by rw [abs_mul, pseudoSign_abs, vectorSign_abs, one_mul]) _ _ fun a b => harmonic_solid m _ K

theorem solid_meas (K : CellBox) : MeasurableSet K.solid :=
  (measurableSet_le measurable_const cylRadius_cont.measurable).inter
    ((measurableSet_le cylRadius_cont.measurable measurable_const).inter
      ((measurableSet_le measurable_const cylHeight_cont.abs.measurable).inter
        (measurableSet_le cylHeight_cont.abs.measurable measurable_const)))

theorem piece_meas (M : CellMesh) (K : Fin M.cellCount) : MeasurableSet (M.piece K) :=
  (solid_meas _).diff (Finset.measurableSet_biUnion _ fun K' _ => solid_meas _)

theorem region_meas (M : CellMesh) : MeasurableSet M.region := MeasurableSet.iUnion fun K => solid_meas _

theorem piece_sub (M : CellMesh) (K : Fin M.cellCount) : M.piece K ⊆ (M.box K).solid := Set.sdiff_subset

theorem solid_sub (M : CellMesh) (K : Fin M.cellCount) : (M.box K).solid ⊆ M.region :=
  Set.subset_iUnion (fun K => (M.box K).solid) K

theorem piecewise_out {E : Type*} [AddCommMonoid E] (M : CellMesh) (f : Fin M.cellCount → Space → E) {y : Space}
    (hy : y ∉ M.region) : M.piecewise f y = 0 := by
  unfold CellMesh.piecewise
  exact Finset.sum_eq_zero fun K _ => Set.indicator_of_notMem (fun h => hy (solid_sub M K (piece_sub M K h))) _

theorem piecewise_sm {E : Type*} [NormedAddCommGroup E] (M : CellMesh) (f : Fin M.cellCount → Space → E)
    (hf : ∀ K, StronglyMeasurable (f K)) : StronglyMeasurable (M.piecewise f) := by
  unfold CellMesh.piecewise
  exact Finset.stronglyMeasurable_fun_sum _ fun K _ => (hf K).indicator (piece_meas M K)

theorem piecewise_bd {E : Type*} [NormedAddCommGroup E] (M : CellMesh) (f : Fin M.cellCount → Space → E)
    (hf : ∀ K, ∃ C, ∀ y ∈ (M.box K).solid, ‖f K y‖ ≤ C) : ∃ C, ∀ y, ‖M.piecewise f y‖ ≤ C := by
  choose C hC using hf
  refine ⟨∑ K, max (C K) 0, fun y => ?_⟩
  unfold CellMesh.piecewise
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun K _ => ?_)
  by_cases h : y ∈ M.piece K
  · rw [Set.indicator_of_mem h]
    exact (hC K y (piece_sub M K h)).trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem h, norm_zero]
    exact le_max_right _ _

theorem piecewise_induct {E : Type*} [AddCommMonoid E] (M : CellMesh) (f : Fin M.cellCount → Space → E)
    (p : E → Prop) (h0 : p 0) (hadd : ∀ a b, p a → p b → p (a + b)) (y : Space)
    (hf : ∀ K, y ∈ M.piece K → p (f K y)) : p (M.piecewise f y) := by
  unfold CellMesh.piecewise
  refine Finset.sum_induction _ p hadd h0 fun K _ => ?_
  by_cases h : y ∈ M.piece K
  · rw [Set.indicator_of_mem h]
    exact hf K h
  · rw [Set.indicator_of_notMem h]
    exact h0

theorem mem_piece_congr (M : CellMesh) (K : Fin M.cellCount) {y y' : Space} (hr : cylRadius y = cylRadius y')
    (hz : |cylHeight y| = |cylHeight y'|) : y ∈ M.piece K ↔ y' ∈ M.piece K := by
  simp only [CellMesh.piece, CellBox.solid, Set.mem_sdiff, Set.mem_iUnion, Set.mem_ofPred_eq, hr, hz]

end Breakdown.FracInternal.GivenModelModelFrame

namespace Breakdown.FracInternal.GivenModelModelFrame

open CellCert CellCert.GivenModel CellCert.CellAnalysis SteadyCert

def zSign (a : Fin 3) : ℝ := if a = 2 then -1 else 1

def mirrorLin : Space →ₗ[ℝ] Space where
  toFun := mirror
  map_add' u w := by
    ext i
    fin_cases i <;> simp [mirror] <;> ring
  map_smul' s u := by
    ext i
    fin_cases i <;> simp [mirror]

theorem mirrorLin_apply (y : Space) : mirrorLin y = mirror y := rfl

theorem mirror_fsum {ι : Type*} (s : Finset ι) (f : ι → Space) : mirror (∑ i ∈ s, f i) = ∑ i ∈ s, mirror (f i) :=
  map_sum mirrorLin f s

theorem mirror_zero' : mirror 0 = 0 := map_zero mirrorLin

theorem cylRadius_mirror (y : Space) : cylRadius (mirror y) = cylRadius y := by simp [cylRadius, mirror]

theorem cylHeight_mirror (y : Space) : cylHeight (mirror y) = -cylHeight y := by simp [cylHeight, mirror]

theorem cylAngle_mirror (y : Space) : cylAngle (mirror y) = cylAngle y := by simp [cylAngle, mirror]

theorem frame_mirror (θ : ℝ) (a : Fin 3) : mirror (frameUnit θ a) = zSign a • frameUnit θ a := by
  fin_cases a <;> ext i <;> fin_cases i <;> simp [mirror, frameUnit, radialUnit, angularUnit, axialUnit, zSign]

theorem inner_mirror (x u : Space) : inner ℝ x (mirror u) = inner ℝ (mirror x) u := by
  simp [mirror, PiLp.inner_apply, Fin.sum_univ_three]

theorem cart_congr (θ : ℝ) {w w' : Fin 3 → ℝ} (h : ∀ a, w a = w' a) : cartOfFrame θ w = cartOfFrame θ w' := by
  rw [show w = w' from funext h]

theorem cartOp_congr (θ : ℝ) {M M' : Fin 3 → Fin 3 → ℝ} (h : ∀ a b, M a b = M' a b) (u : Space) :
    cartOpOfFrame θ M u = cartOpOfFrame θ M' u := by
  rw [show M = M' from funext fun a => funext fun b => h a b]

theorem cart_mirror (θ : ℝ) (w : Fin 3 → ℝ) :
    mirror (cartOfFrame θ w) = cartOfFrame θ (fun a => zSign a * w a) := by
  rw [← mirrorLin_apply]
  unfold cartOfFrame
  simp only [map_sum, map_smul, mirrorLin_apply, frame_mirror, smul_smul]
  exact Finset.sum_congr rfl fun a _ => by rw [mul_comm]

theorem cart_smul (s θ : ℝ) (w : Fin 3 → ℝ) : s • cartOfFrame θ w = cartOfFrame θ (fun a => s * w a) := by
  simp [cartOfFrame, Finset.smul_sum, smul_smul]

theorem cartOp_mirror (θ : ℝ) (M : Fin 3 → Fin 3 → ℝ) (u : Space) :
    mirror (cartOpOfFrame θ M (mirror u)) = cartOpOfFrame θ (fun a b => zSign a * zSign b * M a b) u := by
  rw [cartOp_apply, cartOp_apply, ← mirrorLin_apply]
  simp only [map_sum, map_smul, mirrorLin_apply, frame_mirror, inner_mirror, real_inner_smul_left, smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ring

theorem cartOp_smul (s θ : ℝ) (M : Fin 3 → Fin 3 → ℝ) (u : Space) :
    s • cartOpOfFrame θ M u = cartOpOfFrame θ (fun a b => s * M a b) u := by
  rw [cartOp_apply, cartOp_apply]
  simp only [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ring

theorem vectorSign_mirror {y : Space} (hy : cylHeight y ≠ 0) (a : Fin 3) :
    vectorSign (mirror y) a = zSign a * vectorSign y a := by
  unfold vectorSign zSign
  rw [cylHeight_mirror]
  rcases lt_or_gt_of_ne hy with h | h
  · have h' : ¬ (-cylHeight y < 0) := by linarith
    fin_cases a <;> simp [h, h']
  · have h' : -cylHeight y < 0 := by linarith
    have h'' : ¬ (cylHeight y < 0) := by linarith
    fin_cases a <;> simp [h', h'']

theorem pseudoSign_mirror {y : Space} (hy : cylHeight y ≠ 0) (a : Fin 3) :
    pseudoSign (mirror y) a = -(zSign a * pseudoSign y a) := by
  unfold pseudoSign vectorSign zSign
  rw [cylHeight_mirror]
  rcases lt_or_gt_of_ne hy with h | h
  · have h' : ¬ (-cylHeight y < 0) := by linarith
    fin_cases a <;> simp [h, h']
  · have h' : -cylHeight y < 0 := by linarith
    have h'' : ¬ (cylHeight y < 0) := by linarith
    fin_cases a <;> simp [h', h'']

theorem harmonic_mirror (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → CellPoly d) (y : Space) :
    harmonicValue m P (mirror y) = harmonicValue m P y := by
  rw [harmonicValue_eq, harmonicValue_eq, cylRadius_mirror, cylHeight_mirror, abs_neg, cylAngle_mirror]

theorem vectorOf_mirror (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → CellPoly d) {y : Space} (hy : cylHeight y ≠ 0) :
    vectorOf m P (mirror y) = (1 : ℝ) • mirror (vectorOf m P y) := by
  unfold vectorOf
  rw [cart_mirror, cart_smul, cylAngle_mirror]
  apply cart_congr
  intro a
  rw [vectorSign_mirror hy, harmonic_mirror]
  ring

theorem pseudoOf_mirror (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → CellPoly d) {y : Space} (hy : cylHeight y ≠ 0) :
    pseudoOf m P (mirror y) = (-1 : ℝ) • mirror (pseudoOf m P y) := by
  unfold pseudoOf
  rw [cart_mirror, cart_smul, cylAngle_mirror]
  apply cart_congr
  intro a
  rw [pseudoSign_mirror hy, harmonic_mirror]
  ring

theorem tensorOf_mirror (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d) {y : Space}
    (hy : cylHeight y ≠ 0) (u : Space) :
    tensorOf m P (mirror y) u = (1 : ℝ) • mirror (tensorOf m P y (mirror u)) := by
  unfold tensorOf
  rw [cartOp_mirror, cartOp_smul, cylAngle_mirror]
  apply cartOp_congr
  intro a b
  rw [vectorSign_mirror hy, vectorSign_mirror hy, harmonic_mirror]
  ring

theorem pseudoTensorOf_mirror (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d) {y : Space}
    (hy : cylHeight y ≠ 0) (u : Space) :
    pseudoTensorOf m P (mirror y) u = (-1 : ℝ) • mirror (pseudoTensorOf m P y (mirror u)) := by
  unfold pseudoTensorOf
  rw [cartOp_mirror, cartOp_smul, cylAngle_mirror]
  apply cartOp_congr
  intro a b
  rw [pseudoSign_mirror hy, vectorSign_mirror hy, harmonic_mirror]
  ring

theorem mem_region_mirror (M : CellMesh) (y : Space) : mirror y ∈ M.region ↔ y ∈ M.region := by
  simp only [CellMesh.region, CellBox.solid, Set.mem_iUnion, Set.mem_ofPred_eq, cylRadius_mirror, cylHeight_mirror,
    abs_neg]

theorem piecewise_mirror_vec (M : CellMesh) (f g : Fin M.cellCount → Space → Space) (s : ℝ) (y : Space)
    (hf : ∀ K, y ∈ M.piece K → f K (mirror y) = s • mirror (g K y)) :
    M.piecewise f (mirror y) = s • mirror (M.piecewise g y) := by
  unfold CellMesh.piecewise
  rw [mirror_fsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  have e := mem_piece_congr M K (cylRadius_mirror y) (by rw [cylHeight_mirror, abs_neg])
  by_cases h : y ∈ M.piece K
  · rw [Set.indicator_of_mem (e.2 h), Set.indicator_of_mem h, hf K h]
  · rw [Set.indicator_of_notMem (fun h' => h (e.1 h')), Set.indicator_of_notMem h, mirror_zero', smul_zero]

theorem piecewise_mirror_op (M : CellMesh) (f g : Fin M.cellCount → Space → (Space →L[ℝ] Space)) (s : ℝ)
    (y : Space) (hf : ∀ K, y ∈ M.piece K → ∀ u, f K (mirror y) u = s • mirror (g K y (mirror u))) (u : Space) :
    M.piecewise f (mirror y) u = s • mirror (M.piecewise g y (mirror u)) := by
  unfold CellMesh.piecewise
  rw [sum_apply, sum_apply, mirror_fsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  have e := mem_piece_congr M K (cylRadius_mirror y) (by rw [cylHeight_mirror, abs_neg])
  by_cases h : y ∈ M.piece K
  · rw [Set.indicator_of_mem (e.2 h), Set.indicator_of_mem h, hf K h]
  · rw [Set.indicator_of_notMem (fun h' => h (e.1 h')), Set.indicator_of_notMem h, zero_apply,
      zero_apply, mirror_zero', smul_zero]

end Breakdown.FracInternal.GivenModelModelFrame
