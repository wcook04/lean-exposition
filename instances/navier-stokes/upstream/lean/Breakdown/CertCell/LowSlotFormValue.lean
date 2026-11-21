import Breakdown.CertCell.RowProfileDefs
import Breakdown.FracCell.EnergyPairIntegrable
import Breakdown.FracCell.EnergyRadialForm

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

namespace LowSlotForm.Internal

open Breakdown.FracInternal.EnergyPairIntegrable

def slotSplit (Q : ℕ) : (Fin 3 × Fin 3 × Fin (Q + 1) × Fin (Q + 1)) ⊕ (Fin 3 × Fin Q × Fin Q) ≃ LowSlot Q where
  toFun x := Sum.elim (fun y => LowSlot.strain y.1 y.2.1 y.2.2.1 y.2.2.2) (fun y => LowSlot.velocity y.1 y.2.1 y.2.2) x
  invFun
    | .strain a b j l => Sum.inl (a, b, j, l)
    | .velocity a j l => Sum.inr (a, j, l)
  left_inv := by rintro (⟨a, b, j, l⟩ | ⟨a, j, l⟩) <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

theorem sum_slot {Q : ℕ} (F : LowSlot Q → ℂ) :
    ∑ s, F s = (∑ a : Fin 3, ∑ b : Fin 3, ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), F (.strain a b j l))
      + ∑ a : Fin 3, ∑ j : Fin Q, ∑ l : Fin Q, F (.velocity a j l) := by
  rw [← Fintype.sum_equiv (slotSplit Q) (fun y => F (slotSplit Q y)) F (fun _ => rfl), Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  rfl

theorem strain_sum (B : CellBases) {Q : ℕ} (x : LowSlot Q → ℂ) (p : ℝ × ℝ) (a b : Fin 3) :
    ∑ s, x s * (slotValue B s p).1 a b
      = ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), x (.strain a b j l) * ((basisFn B j l p : ℝ) : ℂ) := by
  rw [sum_slot]
  simp [slotValue, ite_and]

theorem velocity_sum (B : CellBases) {Q : ℕ} (x : LowSlot Q → ℂ) (p : ℝ × ℝ) (a : Fin 3) :
    ∑ s, x s * (slotValue B s p).2 a
      = ∑ j : Fin Q, ∑ l : Fin Q, x (.velocity a j l) * ((basisFn B j l p : ℝ) : ℂ) := by
  rw [sum_slot]
  simp [slotValue]

theorem sesq_sum_left {ι : Type} [Fintype ι] (A : Matrix (Fin 12) (Fin 12) ℂ) (c : ι → ℂ) (U : ι → Fin 12 → ℂ)
    (W : Fin 12 → ℂ) :
    matrixSesq A (∑ s, c s • U s) W = ∑ s, (starRingEnd ℂ) (c s) * matrixSesq A (U s) W := by
  simp only [matrixSesq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans (Finset.sum_comm.trans
    (Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring))

theorem sesq_sum_right {ι : Type} [Fintype ι] (A : Matrix (Fin 12) (Fin 12) ℂ) (c : ι → ℂ) (U : ι → Fin 12 → ℂ)
    (W : Fin 12 → ℂ) :
    matrixSesq A W (∑ s, c s • U s) = ∑ s, c s * matrixSesq A W (U s) := by
  simp only [matrixSesq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans (Finset.sum_comm.trans
    (Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring))

theorem pair_expand (L : CellLayout) (u : L.Datum → ℂ) (n : L.modes) (p : ℝ × ℝ) :
    pairVec (lowStrainOf L u n · · p) (lowVelocityOf L u n · p)
      = ∑ s, u (slotIndex (layoutIndex L) n s) • pairVec (slotValue L.bases s p).1 (slotValue L.bases s p).2 := by
  funext i
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases h : i.val < 9
  · simp only [pairVec, dif_pos h]
    rw [strain_sum]
    rfl
  · simp only [pairVec, dif_neg h]
    rw [velocity_sum]
    rfl

theorem value_slot {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ}
    (I : LowIndex D modes Q q) (Gm : Matrix (modes × LowSlot Q) (modes × LowSlot Q) ℂ) (u : D → ℂ) :
    quadFormValue (formOfRows (slotRow I) Gm) u =
      (∑ σ, (starRingEnd ℂ) (u (slotIndex I σ.1 σ.2)) * ∑ σ', Gm σ σ' * u (slotIndex I σ'.1 σ'.2)).re := by
  rw [RadialForm.value_formOfRows]
  have hr : ∀ σ : modes × LowSlot Q, rowApply (slotRow I σ) u = u (slotIndex I σ.1 σ.2) := by
    intro σ
    simp [rowApply, slotRow]
  simp only [hr, dotProduct, mulVec, Pi.star_apply, RCLike.star_def]

end LowSlotForm.Internal

open LowSlotForm.Internal Breakdown.FracInternal.EnergyPairIntegrable

theorem lowSlotFormValue_holds : LowSlotFormValueStatement := by
  intro L A u hmeas hbd _
  obtain ⟨C, hC⟩ := hbd
  set K := L.box
  set B := L.bases
  set w : ℝ × ℝ → ℂ := fun p => ((K.lineWeight p.1 * CellScalars.rHat K p : ℝ) : ℂ) with hwdef
  set V : LowSlot L.degCoef → ℝ × ℝ → Fin 12 → ℂ := fun s p => pairVec (slotValue B s p).1 (slotValue B s p).2
    with hVdef
  set x : L.modes → LowSlot L.degCoef → ℂ := fun n s => u (slotIndex (layoutIndex L) n s) with hxdef
  have hA : ∀ i j, Bdd K (fun p => A p i j) :=
    fun i j => ⟨(hmeas i j).aestronglyMeasurable, C, fun p hp => hC p hp i j⟩
  have hw : Bdd K w := by
    have e : w = fun p => ((p.1 : ℝ) : ℂ) := funext fun p => by rw [hwdef]; simp only [weight_eq]
    rw [e]
    exact bdd_cont K (by fun_prop)
  have hint : ∀ s s' : LowSlot L.degCoef,
      IntegrableOn (fun p => w p * matrixSesq (A p) (V s p) (V s' p)) K.rect := by
    intro s s'
    exact Bdd.integrableOn (bdd_mul hw (bdd_msesq hA (bdd_pairVec (bdd_slot_fst K B s) (bdd_slot_snd K B s))
      (bdd_pairVec (bdd_slot_fst K B s') (bdd_slot_snd K B s'))))
  have key : ∀ n : L.modes,
      ∑ s, (starRingEnd ℂ) (x n s) * ∑ s', (∫ p in K.rect, w p * matrixSesq (A p) (V s p) (V s' p)) * x n s'
        = ∫ p in K.rect, w p * matrixSesq (A p) (pairVec (lowStrainOf L u n · · p) (lowVelocityOf L u n · p))
            (pairVec (lowStrainOf L u n · · p) (lowVelocityOf L u n · p)) := by
    intro n
    have hpt : ∀ p, w p * matrixSesq (A p) (pairVec (lowStrainOf L u n · · p) (lowVelocityOf L u n · p))
            (pairVec (lowStrainOf L u n · · p) (lowVelocityOf L u n · p))
          = ∑ s, ∑ s', ((starRingEnd ℂ) (x n s) * x n s') * (w p * matrixSesq (A p) (V s p) (V s' p)) := by
      intro p
      rw [pair_expand, sesq_sum_left, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [sesq_sum_right, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      ring
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun s' _ => (hint s s').const_mul _))]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [integral_finsetSum _ (fun s' _ => (hint s s').const_mul _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [integral_const_mul]
    ring
  unfold lowSlotForm
  refine (value_slot (layoutIndex L) _ u).trans ?_
  rw [← Complex.re_sum]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun n _ => Eq.trans ?_ (key n)
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => ?_
  dsimp only
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  all_goals rfl

end CellCalculus

end CertCell

end Breakdown
