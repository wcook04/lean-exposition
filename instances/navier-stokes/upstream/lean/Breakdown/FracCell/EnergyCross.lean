import Breakdown.FracCell.EnergyCrossProj

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis CellFormula SteadyCert Assembly

def CrossIntegrable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (G : Space → (Space →L[ℝ] Space)) : Prop :=
  ∀ (n : ℤ) (a b : Fin 3),
    IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * gradMode c.order n G a b p) K.rect ∧
    ∀ i : Fin k,
      IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b) K.rect ∧
      IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeMat c.order n (c.modelPinField i) p.1 p.2 a b) K.rect

namespace EnergyCrossInternal

lemma block_value {D ι : Type} [Fintype D] [Fintype ι] (A : Matrix D D ℂ) (R : ι → D → ℂ)
    (u : D → ℂ) (x : ι → ℂ) (hx : ∀ y, (starRingEnd ℂ) (x y) = x y) :
    quadFormValue (Matrix.fromBlocks A (fun d y => (starRingEnd ℂ) (R y d)) (fun y d => R y d) 0)
        (Sum.elim u x) =
      quadFormValue A u + 2 * (∑ y, x y * rowApply (R y) u).re := by
  have h1 : (∑ d, (starRingEnd ℂ) (u d) * ∑ y, (starRingEnd ℂ) (R y d) * x y) =
      (starRingEnd ℂ) (∑ y, x y * rowApply (R y) u) := by
    simp only [rowApply, map_sum, map_mul, hx, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  have h2 : (∑ y, (starRingEnd ℂ) (x y) * ∑ d, R y d * u d) = ∑ y, x y * rowApply (R y) u := by
    simp only [rowApply, hx]
  simp only [quadFormValue, dotProduct, mulVec, Fintype.sum_sum_type, Pi.star_apply, Sum.elim_inl,
    Sum.elim_inr, fromBlocks, of_apply, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
    RCLike.star_def, mul_add, Finset.sum_add_distrib]
  rw [h1, h2]
  simp only [mul_zero, Finset.sum_const_zero, add_zero, Complex.add_re, Complex.conj_re]
  ring

lemma rowApply_slot {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ}
    (I : LowIndex D modes Q q) (X : modes × LowSlot Q → ℂ) (u : D → ℂ) :
    rowApply (fun d => ∑ σ, slotRow I σ d * X σ) u = ∑ σ, X σ * u (slotIndex I σ.1 σ.2) := by
  unfold rowApply slotRow
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [ite_mul]

def slotEquiv (Q : ℕ) : LowSlot Q ≃ (Fin 3 × Fin 3 × Fin (Q + 1) × Fin (Q + 1)) ⊕ (Fin 3 × Fin Q × Fin Q) where
  toFun s := match s with
    | .strain a b j l => .inl (a, b, j, l)
    | .velocity a j l => .inr (a, j, l)
  invFun t := match t with
    | .inl (a, b, j, l) => .strain a b j l
    | .inr (a, j, l) => .velocity a j l
  left_inv s := by cases s <;> rfl
  right_inv t := by rcases t with ⟨a, b, j, l⟩ | ⟨a, j, l⟩ <;> rfl

lemma slot_sum {Q : ℕ} (f : LowSlot Q → ℂ) :
    ∑ s, f s = ∑ a : Fin 3, ∑ b : Fin 3, ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), f (.strain a b j l)
      + ∑ a : Fin 3, ∑ j : Fin Q, ∑ l : Fin Q, f (.velocity a j l) := by
  rw [← (slotEquiv Q).symm.sum_comp f]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type]
  rfl

lemma entry_unit (a b : Fin 3) (z : ℂ) (t : Fin 3 → Fin 3 → ℂ) :
    entryPairing (fun a' b' => if a' = a ∧ b' = b then z else 0) t = z * (starRingEnd ℂ) (t a b) := by
  unfold entryPairing
  rw [Finset.sum_eq_single a (fun a' _ ha => by simp [ha]) (by simp),
    Finset.sum_eq_single b (fun b' _ hb => by simp [hb]) (by simp)]
  simp

lemma entry_zero_left (t : Fin 3 → Fin 3 → ℂ) : entryPairing (fun _ _ => 0) t = 0 := by
  simp [entryPairing]

lemma integral_expand {d : ℕ} {μ : Measure (ℝ × ℝ)} (ω : ℝ × ℝ → ℂ)
    (P Ma Mp : Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (C : Fin 3 → Fin 3 → Fin (d + 1) → Fin (d + 1) → ℂ)
    (β : Fin (d + 1) → Fin (d + 1) → ℝ × ℝ → ℂ) (x y : ℂ)
    (hP : ∀ a b, P a b =ᵐ[μ] fun p => ∑ j, ∑ l, C a b j l * β j l p)
    (ha : ∀ a b j l, Integrable (fun p => ω p * (β j l p * (starRingEnd ℂ) (Ma a b p))) μ)
    (hp : ∀ a b j l, Integrable (fun p => ω p * (β j l p * (starRingEnd ℂ) (Mp a b p))) μ) :
    ∫ p, ω p * (x * entryPairing (fun a b => P a b p) (fun a b => Ma a b p)
        + y * entryPairing (fun a b => P a b p) (fun a b => Mp a b p)) ∂μ =
      ∑ a, ∑ b, ∑ j, ∑ l, C a b j l * (x * ∫ p, ω p * (β j l p * (starRingEnd ℂ) (Ma a b p)) ∂μ
        + y * ∫ p, ω p * (β j l p * (starRingEnd ℂ) (Mp a b p)) ∂μ) := by
  have hall : ∀ᵐ p ∂μ, ∀ a b, P a b p = ∑ j, ∑ l, C a b j l * β j l p := by
    rw [ae_all_iff]
    intro a
    rw [ae_all_iff]
    exact hP a
  have hcongr : (fun p => ω p * (x * entryPairing (fun a b => P a b p) (fun a b => Ma a b p)
        + y * entryPairing (fun a b => P a b p) (fun a b => Mp a b p))) =ᵐ[μ]
      fun p => ∑ a, ∑ b, ∑ j, ∑ l, C a b j l * (x * (ω p * (β j l p * (starRingEnd ℂ) (Ma a b p)))
        + y * (ω p * (β j l p * (starRingEnd ℂ) (Mp a b p)))) := by
    filter_upwards [hall] with p hp
    calc ω p * (x * entryPairing (fun a b => P a b p) (fun a b => Ma a b p)
          + y * entryPairing (fun a b => P a b p) (fun a b => Mp a b p))
        = ω p * (x * ∑ a, ∑ b, ∑ j, ∑ l, C a b j l * β j l p * (starRingEnd ℂ) (Ma a b p)
          + y * ∑ a, ∑ b, ∑ j, ∑ l, C a b j l * β j l p * (starRingEnd ℂ) (Mp a b p)) := by
          simp only [entryPairing, hp, Finset.sum_mul]
      _ = _ := by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
          ring
  have hT : ∀ a b j l, Integrable (fun p => C a b j l * (x * (ω p * (β j l p * (starRingEnd ℂ) (Ma a b p)))
        + y * (ω p * (β j l p * (starRingEnd ℂ) (Mp a b p))))) μ :=
    fun a b j l => (((ha a b j l).const_mul x).add ((hp a b j l).const_mul y)).const_mul _
  rw [integral_congr_ae hcongr, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => hT a b j l]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun l _ => hT a b j l]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => hT a b j l]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun l _ => hT a b j l]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, integral_add ((ha a b j l).const_mul x) ((hp a b j l).const_mul y),
    integral_const_mul, integral_const_mul]

lemma weight_eq (K : CellBox) (p : ℝ × ℝ) :
    K.lineWeight p.1 * CellScalars.rHat K p = p.1 := by
  unfold CellScalars.rHat CellBox.lineWeight
  split_ifs with h
  · rcases eq_or_ne p.1 0 with h0 | h0
    · simp [h0]
    · field_simp
  · simp

lemma basis_continuous (B : CellBases) (j l : ℕ) : Continuous (fun p : ℝ × ℝ => basisFn B j l p) := by
  unfold basisFn CellBases.radialPoly CellBases.heightPoly
  fun_prop

lemma term_integrable (K : CellBox) (B : CellBases) (j l : ℕ) (M : ℝ × ℝ → ℂ)
    (hM : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * M p) K.rect) :
    Integrable (fun p => ((K.lineWeight p.1 * CellScalars.rHat K p : ℝ) : ℂ)
      * (((basisFn B j l p : ℝ) : ℂ) * (starRingEnd ℂ) (M p))) (volume.restrict K.rect) := by
  have hc : IntegrableOn (fun p : ℝ × ℝ => (starRingEnd ℂ) ((p.1 : ℂ) * M p)) K.rect := by
    have h0 := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hM
    simpa [IntegrableOn] using h0
  have hcont : ContinuousOn (fun p : ℝ × ℝ => ((basisFn B j l p : ℝ) : ℂ)) K.rect :=
    (Complex.continuous_ofReal.comp (basis_continuous B j l)).continuousOn
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have h := hc.continuousOn_mul hcont hcomp
  refine h.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
  simp only [weight_eq, map_mul, Complex.conj_ofReal]
  ring

end EnergyCrossInternal

open EnergyCrossInternal in
theorem crossForm_holds (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ} (c : FracCellData k N)
    (K : CellBox) (B : CellBases) (S : CellScalars) (Cl : CellClasses) {modes : Finset ℤ} {Q q : ℕ}
    (I : LowIndex D modes Q q) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (u : D → ℂ) (hs : EnergySetting α c K B S I v G H u)
    (hint : CrossIntegrable c K G) (κ ζ : Fin k → ℝ) :
    quadFormValue (localForm c K B S Cl I) (dataVector u κ ζ) =
      quadFormValue (energyForm K B I c.order S.energyWeight S.vorticityWeight S.tailShift
          - classForm K B S Cl I + pairForm c K B S I) u
        + CellScalars.linearTerm c K S κ ζ G := by
  obtain ⟨hmodes, hQ, -, hK, hB, -, -, hrep⟩ := hs
  subst hmodes hQ
  have hx : ∀ y, (starRingEnd ℂ) (Sum.elim (fun i => ((κ i : ℝ) : ℂ)) (fun i => ((ζ i : ℝ) : ℂ)) y) =
      Sum.elim (fun i => ((κ i : ℝ) : ℂ)) (fun i => ((ζ i : ℝ) : ℂ)) y := by
    rintro (i | i) <;> simp
  unfold localForm dataVector
  rw [block_value _ (crossRow c K B I) u _ hx]
  congr 1
  unfold CellScalars.linearTerm
  congr 2
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, crossRow]
  rw [← Finset.sum_add_distrib]
  conv_rhs => rw [← Finset.sum_coe_sort S.resolved, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold actuatorRow pinRow
  rw [rowApply_slot, rowApply_slot, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hE := integral_expand (μ := volume.restrict K.rect)
    (fun p => ((K.lineWeight p.1 * CellScalars.rHat K p : ℝ) : ℂ))
    (fun a b p => K.lowStrain c.order n S.degHigh G a b p)
    (fun a b p => modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b)
    (fun a b p => modeMat c.order n (c.modelPinField i) p.1 p.2 a b)
    (fun a b j l => B.coef K (gradMode c.order n G a b) j l) (fun j l p => ((basisFn B j l p : ℝ) : ℂ))
    (((κ i / 2 : ℝ) : ℂ)) ((ζ i : ℝ) : ℂ)
    (fun a b => lowProj_ae_eq_coefSum K B hK hB _ (hint n a b).1 S.degHigh)
    (fun a b j l => term_integrable K B j l _ ((hint n a b).2 i).1)
    (fun a b j l => term_integrable K B j l _ ((hint n a b).2 i).2)
  refine Eq.trans ?_ hE.symm
  have h12 : ∀ f : ℝ × ℝ → ℂ, ∫ p in K.rect, ((K.lineWeight p.1 * CellScalars.rHat K p : ℝ) : ℂ) * (1 / 2 : ℂ) * f p
      = (1 / 2 : ℂ) * ∫ p in K.rect, ((K.lineWeight p.1 * CellScalars.rHat K p : ℝ) : ℂ) * f p := by
    intro f
    rw [← integral_const_mul]
    congr 1
    funext p
    ring
  rw [slot_sum, slot_sum]
  simp only [slotIndex, slotValue, entry_unit, entry_zero_left, mul_zero, integral_zero, zero_mul,
    Finset.sum_const_zero, add_zero, hrep.strain, h12]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  push_cast
  ring

end Breakdown.CellCert.CellEnergy
