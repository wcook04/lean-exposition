import Breakdown.FracCell.StEnergyProof
import Breakdown.FracCell.EnergyCrossProj
import Breakdown.FracCell.LowEntry

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis CellFormula SteadyCert Assembly

namespace EnergyClassInternal

lemma quad_slot {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ}
    (I : LowIndex D modes Q q) (Gm : Matrix (modes × LowSlot Q) (modes × LowSlot Q) ℂ) (u : D → ℂ) :
    quadFormValue (formOfRows (slotRow I) Gm) u =
      (∑ σ, ∑ σ', (starRingEnd ℂ) (u (slotIndex I σ.1 σ.2)) * Gm σ σ' * u (slotIndex I σ'.1 σ'.2)).re := by
  unfold quadFormValue formOfRows
  congr 1
  have hr : ∀ σ σ' : modes × LowSlot Q, ∑ d, ∑ d', (starRingEnd ℂ) (u d) *
      ((starRingEnd ℂ) (slotRow I σ d) * Gm σ σ' * slotRow I σ' d' * u d') =
      (starRingEnd ℂ) (u (slotIndex I σ.1 σ.2)) * Gm σ σ' * u (slotIndex I σ'.1 σ'.2) := by
    intro σ σ'
    simp only [slotRow, apply_ite (starRingEnd ℂ), map_one, map_zero, ite_mul, mul_ite, zero_mul, mul_zero,
      one_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hl : star u ⬝ᵥ ((fun d d' => ∑ σ, ∑ σ', (starRingEnd ℂ) (slotRow I σ d) * Gm σ σ' * slotRow I σ' d') *ᵥ u) =
      ∑ d, ∑ d', ∑ σ, ∑ σ', (starRingEnd ℂ) (u d) *
        ((starRingEnd ℂ) (slotRow I σ d) * Gm σ σ' * slotRow I σ' d' * u d') := by
    simp only [dotProduct, mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum, Finset.sum_mul]
  rw [hl]
  refine ((Finset.sum_congr rfl fun d _ => Finset.sum_comm.trans
    (Finset.sum_congr rfl fun σ _ => Finset.sum_comm)).trans
      (Finset.sum_comm.trans (Finset.sum_congr rfl fun σ _ => Finset.sum_comm))).trans ?_
  exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun σ' _ => hr σ σ'

def lossSesq (x y ℓ : ℂ) (U U' : (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)) : ℂ :=
  x * curlSesq U.1 U'.1 + y * (ℓ * sumSesq U.1 U'.1 + vecSesq U.2 U'.2 / ℓ)

lemma curl_add (s t : Fin 3 → Fin 3 → ℂ) (i : Fin 3) :
    curlComp (s + t) i = curlComp s i + curlComp t i := by
  simp only [curlComp, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma curl_smul (x : ℂ) (s : Fin 3 → Fin 3 → ℂ) (i : Fin 3) :
    curlComp (x • s) i = x * curlComp s i := by
  simp only [curlComp, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

lemma loss_add_left (x y ℓ : ℂ) (U V W : (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)) :
    lossSesq x y ℓ (U + V) W = lossSesq x y ℓ U W + lossSesq x y ℓ V W := by
  simp only [lossSesq, curlSesq, sumSesq, vecSesq, Prod.fst_add, Prod.snd_add, curl_add, Pi.add_apply,
    map_add, Fin.sum_univ_three]
  ring

lemma loss_add_right (x y ℓ : ℂ) (U V W : (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)) :
    lossSesq x y ℓ W (U + V) = lossSesq x y ℓ W U + lossSesq x y ℓ W V := by
  simp only [lossSesq, curlSesq, sumSesq, vecSesq, Prod.fst_add, Prod.snd_add, curl_add, Pi.add_apply,
    Fin.sum_univ_three]
  ring

lemma loss_smul_left (x y ℓ c : ℂ) (U W : (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)) :
    lossSesq x y ℓ (c • U) W = (starRingEnd ℂ) c * lossSesq x y ℓ U W := by
  simp only [lossSesq, curlSesq, sumSesq, vecSesq, Prod.smul_fst, Prod.smul_snd, curl_smul, Pi.smul_apply,
    smul_eq_mul, map_mul, Fin.sum_univ_three]
  ring

lemma loss_smul_right (x y ℓ c : ℂ) (U W : (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)) :
    lossSesq x y ℓ W (c • U) = c * lossSesq x y ℓ W U := by
  simp only [lossSesq, curlSesq, sumSesq, vecSesq, Prod.smul_fst, Prod.smul_snd, curl_smul, Pi.smul_apply,
    smul_eq_mul, Fin.sum_univ_three]
  ring

lemma loss_sum_left {ι : Type} (s : Finset ι) (x y ℓ : ℂ) (c : ι → ℂ)
    (U : ι → (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)) (W : (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)) :
    lossSesq x y ℓ (∑ τ ∈ s, c τ • U τ) W = ∑ τ ∈ s, (starRingEnd ℂ) (c τ) * lossSesq x y ℓ (U τ) W := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := loss_smul_left x y ℓ 0 0 W
    simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, loss_add_left, loss_smul_left, ih]

lemma loss_sum_right {ι : Type} (s : Finset ι) (x y ℓ : ℂ) (c : ι → ℂ)
    (U : ι → (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)) (W : (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)) :
    lossSesq x y ℓ W (∑ τ ∈ s, c τ • U τ) = ∑ τ ∈ s, c τ * lossSesq x y ℓ W (U τ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := loss_smul_right x y ℓ 0 0 W
    simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, loss_add_right, loss_smul_right, ih]

lemma loss_self (x y ℓ : ℝ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) :
    lossSesq (x : ℂ) (y : ℂ) (ℓ : ℂ) (s, v) (s, v) =
      ((x * curlSq s + y * (ℓ * sumSq s + vecSq v / ℓ) : ℝ) : ℂ) := by
  simp only [lossSesq, curlSesq, sumSesq, vecSesq, curlSq, sumSq, vecSq, Complex.conj_mul',
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_pow]

def slotUnit {Q : ℕ} : LowSlot Q → (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)
  | .strain a b _ _ => (fun a' b' => if a' = a ∧ b' = b then 1 else 0, fun _ => 0)
  | .velocity a _ _ => (fun _ _ => 0, fun a' => if a' = a then 1 else 0)

def slotPoly (B : CellBases) {Q : ℕ} : LowSlot Q → ℝ × ℝ → ℝ
  | .strain _ _ j l => basisFn B j l
  | .velocity _ j l => basisFn B j l

lemma slotValue_eq (B : CellBases) {Q : ℕ} (τ : LowSlot Q) (p : ℝ × ℝ) :
    slotValue B τ p = ((slotPoly B τ p : ℝ) : ℂ) • slotUnit τ := by
  cases τ with
  | strain a b j l =>
    refine Prod.ext (funext fun a' => funext fun b' => ?_) (funext fun a' => ?_) <;>
      simp only [slotValue, slotPoly, slotUnit, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul] <;>
      (try split_ifs) <;> simp
  | velocity a j l =>
    refine Prod.ext (funext fun a' => funext fun b' => ?_) (funext fun a' => ?_) <;>
      simp only [slotValue, slotPoly, slotUnit, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul] <;>
      (try split_ifs) <;> simp

lemma basisFn_cont (B : CellBases) (j l : ℕ) : Continuous (basisFn B j l) :=
  ((LowEntry.Internal.radialPoly_cont B j).comp continuous_fst).mul
    ((LowEntry.Internal.heightPoly_cont B l).comp continuous_snd)

lemma slotPoly_cont (B : CellBases) {Q : ℕ} (τ : LowSlot Q) : Continuous (slotPoly B τ) := by
  cases τ with
  | strain a b j l => exact basisFn_cont B j l
  | velocity a j l => exact basisFn_cont B j l

lemma rect_fin (K : CellBox) : volume K.rect ≠ ⊤ :=
  (LowEntry.Internal.rect_compact K).measure_lt_top.ne

lemma term_int (K : CellBox) {f g φ : ℝ × ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (Cf Cg : ℝ) (hbf : ∀ p ∈ K.rect, |f p| ≤ Cf) (hbg : ∀ p ∈ K.rect, |g p| ≤ Cg) (hφ : Continuous φ)
    (c₁ c₂ : ℂ) :
    IntegrableOn (fun p => ((φ p : ℝ) : ℂ) * ((f p : ℂ) * c₁ + (g p : ℂ) * c₂)) K.rect := by
  have hm : MeasurableSet K.rect := LowEntry.Internal.rect_meas K
  have h1 : IntegrableOn (fun p => (f p : ℂ) * c₁ + (g p : ℂ) * c₂) K.rect := by
    refine Measure.integrableOn_of_bounded (M := Cf * ‖c₁‖ + Cg * ‖c₂‖) (rect_fin K) ?_ ?_
    · exact ((Complex.measurable_ofReal.comp hf).mul_const c₁ |>.add
        ((Complex.measurable_ofReal.comp hg).mul_const c₂)).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem hm fun p hp => ?_
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hbf p hp) (norm_nonneg _)
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hbg p hp) (norm_nonneg _)
  exact h1.continuousOn_mul (Complex.continuous_ofReal.comp hφ).continuousOn (LowEntry.Internal.rect_compact K)

def slotEquiv (Q : ℕ) : (Fin 3 × Fin 3 × Fin (Q + 1) × Fin (Q + 1)) ⊕ (Fin 3 × Fin Q × Fin Q) ≃ LowSlot Q where
  toFun
    | .inl x => .strain x.1 x.2.1 x.2.2.1 x.2.2.2
    | .inr x => .velocity x.1 x.2.1 x.2.2
  invFun
    | .strain a b j l => .inl (a, b, j, l)
    | .velocity a j l => .inr (a, j, l)
  left_inv := by rintro (⟨a, b, j, l⟩ | ⟨a, j, l⟩) <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

lemma slot_sum (B : CellBases) {Q : ℕ} (x : LowSlot Q → ℂ) (p : ℝ × ℝ) :
    ∑ τ, x τ • slotValue B τ p =
      ((fun a b => ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), x (.strain a b j l) * ((basisFn B j l p : ℝ) : ℂ)),
       (fun a => ∑ j : Fin Q, ∑ l : Fin Q, x (.velocity a j l) * ((basisFn B j l p : ℝ) : ℂ))) := by
  rw [← Fintype.sum_equiv (slotEquiv Q) (fun y => x (slotEquiv Q y) • slotValue B (slotEquiv Q y) p) _
    (fun _ => rfl)]
  rw [Fintype.sum_sum_type]
  refine Prod.ext ?_ ?_
  · funext a b
    simp [Prod.fst_sum, Finset.sum_apply, Fintype.sum_prod_type, slotEquiv, slotValue, ite_and]
  · funext a
    simp [Prod.snd_sum, Finset.sum_apply, Fintype.sum_prod_type, slotEquiv, slotValue]

end EnergyClassInternal


open EnergyClassInternal in
theorem classForm_holds : ClassFormStatement := by
  intro α D _ _ k N c K B S Cl modes Q q I v G H u h hreg
  obtain ⟨hm, hQ, -, hK, hB, hsc, hfield, hrep, -⟩ := h
  subst hm
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by have := hsc.degrees; omega⟩
  have hrect : MeasurableSet K.rect := LowEntry.Internal.rect_meas K
  have hX : ∀ n : S.resolved, ∀ᵐ p ∂(volume.restrict K.rect),
      ∑ τ, u (slotIndex I n τ) • slotValue B τ p =
        (K.lowStrainAt c.order n (Q' + 1) G p, K.lowVelocityAt c.order n (Q' + 1) v p) := by
    intro n
    have hs : ∀ a b : Fin 3, ∀ᵐ p ∂(volume.restrict K.rect),
        K.proj (Q' + 1) (Q' + 1) (gradMode c.order n G a b) p =
          ∑ j : Fin (Q' + 1 + 1), ∑ l : Fin (Q' + 1 + 1),
            B.coef K (gradMode c.order n G a b) j l * ((basisFn B j l p : ℝ) : ℂ) := fun a b =>
      lowProj_ae_eq_coefSum K B hK hB _ (LowEntry.Internal.gradMode_int K hK c.order n
        hfield.measurable_gradient hfield.gradient_two a b) (Q' + 1)
    have hv : ∀ a : Fin 3, ∀ᵐ p ∂(volume.restrict K.rect),
        K.proj Q' Q' (fun p => modeVec c.order n v p.1 p.2 a) p =
          ∑ j : Fin (Q' + 1), ∑ l : Fin (Q' + 1),
            B.coef K (fun p => modeVec c.order n v p.1 p.2 a) j l * ((basisFn B j l p : ℝ) : ℂ) := fun a =>
      lowProj_ae_eq_coefSum K B hK hB _ (LowEntry.Internal.modeVec_int K hK c.order n
        hfield.velocity_six a) Q'
    have hs' := Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => hs a b
    have hv' := Filter.eventually_all.2 hv
    filter_upwards [hs', hv'] with p hps hpv
    rw [slot_sum]
    refine Prod.ext ?_ ?_
    · funext a b
      simp only [slotIndex, hrep.strain, CellBox.lowStrainAt, CellBox.lowStrain]
      rw [hps a b]
    · funext a
      simp only [slotIndex, hrep.velocity, CellBox.lowVelocityAt, CellBox.lowVelocity, Nat.add_sub_cancel]
      rw [hpv a]
  have hint : ∀ (i : Fin Cl.count) (τ τ' : LowSlot (Q' + 1)), IntegrableOn (fun p => ((p.1 : ℝ) : ℂ) *
      lossSesq ((Cl.strainDev i p : ℝ) : ℂ) (((1 / 2) * Exterior.traceFreeConst * Cl.gradDev i p : ℝ) : ℂ)
        ((S.splitLength : ℝ) : ℂ) (slotValue B τ p) (slotValue B τ' p)) K.rect := by
    intro i τ τ'
    obtain ⟨h1, h2, -, -, C, hC⟩ := hreg i
    have e : (fun p => ((p.1 : ℝ) : ℂ) *
        lossSesq ((Cl.strainDev i p : ℝ) : ℂ) (((1 / 2) * Exterior.traceFreeConst * Cl.gradDev i p : ℝ) : ℂ)
          ((S.splitLength : ℝ) : ℂ) (slotValue B τ p) (slotValue B τ' p)) =
        fun p => ((p.1 * slotPoly B τ p * slotPoly B τ' p : ℝ) : ℂ) *
          (((Cl.strainDev i p : ℝ) : ℂ) * curlSesq (slotUnit τ).1 (slotUnit τ').1
            + (((1 / 2) * Exterior.traceFreeConst * Cl.gradDev i p : ℝ) : ℂ) *
              (((S.splitLength : ℝ) : ℂ) * sumSesq (slotUnit τ).1 (slotUnit τ').1
                + vecSesq (slotUnit τ).2 (slotUnit τ').2 / ((S.splitLength : ℝ) : ℂ))) := by
      funext p
      rw [slotValue_eq B τ p, slotValue_eq B τ' p, loss_smul_left, loss_smul_right, Complex.conj_ofReal]
      simp only [lossSesq, Complex.ofReal_mul]
      ring
    rw [e]
    refine term_int K h1 (h2.const_mul _) C (|(1 / 2) * Exterior.traceFreeConst| * C)
      (fun p hp => (hC p hp).1) (fun p hp => ?_)
      ((continuous_fst.mul (slotPoly_cont B τ)).mul (slotPoly_cont B τ')) _ _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hC p hp).2.1 (abs_nonneg _)
  have key : ∀ (n : S.resolved) (i : Fin Cl.count),
      ∑ τ, ∑ τ', (starRingEnd ℂ) (u (slotIndex I n τ)) *
        (∫ p in K.rect, ((p.1 : ℝ) : ℂ) *
          lossSesq ((Cl.strainDev i p : ℝ) : ℂ) (((1 / 2) * Exterior.traceFreeConst * Cl.gradDev i p : ℝ) : ℂ)
            ((S.splitLength : ℝ) : ℂ) (slotValue B τ p) (slotValue B τ' p)) * u (slotIndex I n τ') =
      ((∫ p in K.rect, p.1 * Cl.classLoss S.splitLength i p (K.lowStrainAt c.order n (Q' + 1) G p)
        (K.lowVelocityAt c.order n (Q' + 1) v p) : ℝ) : ℂ) := by
    intro n i
    rw [← integral_complex_ofReal]
    have hsum : ∑ τ, ∑ τ', (starRingEnd ℂ) (u (slotIndex I n τ)) *
        (∫ p in K.rect, ((p.1 : ℝ) : ℂ) *
          lossSesq ((Cl.strainDev i p : ℝ) : ℂ) (((1 / 2) * Exterior.traceFreeConst * Cl.gradDev i p : ℝ) : ℂ)
            ((S.splitLength : ℝ) : ℂ) (slotValue B τ p) (slotValue B τ' p)) * u (slotIndex I n τ') =
        ∫ p in K.rect, ∑ τ, ∑ τ', ((starRingEnd ℂ) (u (slotIndex I n τ)) * u (slotIndex I n τ')) *
          (((p.1 : ℝ) : ℂ) *
          lossSesq ((Cl.strainDev i p : ℝ) : ℂ) (((1 / 2) * Exterior.traceFreeConst * Cl.gradDev i p : ℝ) : ℂ)
            ((S.splitLength : ℝ) : ℂ) (slotValue B τ p) (slotValue B τ' p)) := by
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl (fun τ _ => ?_)
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl (fun τ' _ => ?_)
          rw [integral_const_mul]
          ring
        · intro τ' _
          exact (hint i τ τ').const_mul _
      · intro τ _
        exact integrable_finsetSum _ (fun τ' _ => (hint i τ τ').const_mul _)
    rw [hsum]
    refine integral_congr_ae ?_
    filter_upwards [hX n] with p hp
    have e2 : ∑ τ, ∑ τ', ((starRingEnd ℂ) (u (slotIndex I n τ)) * u (slotIndex I n τ')) *
          (((p.1 : ℝ) : ℂ) *
          lossSesq ((Cl.strainDev i p : ℝ) : ℂ) (((1 / 2) * Exterior.traceFreeConst * Cl.gradDev i p : ℝ) : ℂ)
            ((S.splitLength : ℝ) : ℂ) (slotValue B τ p) (slotValue B τ' p)) =
        ((p.1 : ℝ) : ℂ) *
          lossSesq ((Cl.strainDev i p : ℝ) : ℂ) (((1 / 2) * Exterior.traceFreeConst * Cl.gradDev i p : ℝ) : ℂ)
            ((S.splitLength : ℝ) : ℂ) (∑ τ, u (slotIndex I n τ) • slotValue B τ p)
            (∑ τ, u (slotIndex I n τ) • slotValue B τ p) := by
      rw [loss_sum_left, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [loss_sum_right, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun τ' _ => ?_)
      ring
    rw [e2, hp, loss_self]
    simp only [CellClasses.classLoss, Complex.ofReal_mul]
  have hfin : ∀ n : S.resolved, ∀ τ : LowSlot (Q' + 1),
      ∑ σ' : S.resolved × LowSlot (Q' + 1), (starRingEnd ℂ) (u (slotIndex I n τ)) *
        (if n = σ'.1 then ∑ i : Fin Cl.count, (if (n : ℤ) ∈ Cl.resolvedPart i then
          ((Cl.shareWeight i : ℝ) : ℂ) * ∫ p in K.rect, ((p.1 : ℝ) : ℂ) *
            lossSesq ((Cl.strainDev i p : ℝ) : ℂ) (((1 / 2) * Exterior.traceFreeConst * Cl.gradDev i p : ℝ) : ℂ)
              ((S.splitLength : ℝ) : ℂ) (slotValue B τ p) (slotValue B σ'.2 p) else 0) else 0) *
        u (slotIndex I σ'.1 σ'.2) =
      ∑ i : Fin Cl.count, ∑ τ' : LowSlot (Q' + 1), (if (n : ℤ) ∈ Cl.resolvedPart i then
        ((Cl.shareWeight i : ℝ) : ℂ) * ((starRingEnd ℂ) (u (slotIndex I n τ)) * (∫ p in K.rect, ((p.1 : ℝ) : ℂ) *
            lossSesq ((Cl.strainDev i p : ℝ) : ℂ) (((1 / 2) * Exterior.traceFreeConst * Cl.gradDev i p : ℝ) : ℂ)
              ((S.splitLength : ℝ) : ℂ) (slotValue B τ p) (slotValue B τ' p)) * u (slotIndex I n τ')) else 0) := by
    intro n τ
    rw [Fintype.sum_prod_type, Finset.sum_eq_single n]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun τ' _ => ?_)
      rw [if_pos rfl, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      split_ifs
      · ring
      · ring
    · intro n' _ hn'
      refine Finset.sum_eq_zero (fun τ' _ => ?_)
      rw [if_neg (Ne.symm hn')]
      ring
    · intro hn
      exact absurd (Finset.mem_univ n) hn
  unfold classForm
  refine (quad_slot I _ u).trans ?_
  unfold CellScalars.classTerm
  rw [← hQ]
  rw [← Complex.ofReal_re (∑ n ∈ S.resolved, _)]
  congr 1
  rw [Fintype.sum_prod_type, Complex.ofReal_sum, ← Finset.sum_coe_sort S.resolved]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  refine (Finset.sum_congr rfl fun τ _ => hfin n τ).trans ?_
  rw [Finset.sum_comm, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : (n : ℤ) ∈ Cl.resolvedPart i
  · simp only [if_pos hi]
    rw [Complex.ofReal_mul, ← key n i, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [Finset.mul_sum]
  · simp only [if_neg hi, Finset.sum_const_zero, Complex.ofReal_zero]

end Breakdown.CellCert.CellEnergy
