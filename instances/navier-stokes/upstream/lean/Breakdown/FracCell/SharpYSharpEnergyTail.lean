import Breakdown.FracCell.SharpYChargeSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly SharpParts

namespace SharpEnergyTailParts

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (x : FieldTuple k)

def yTerm (n : ℤ) (j l : ℕ) : ℝ :=
  if n ∉ S.resolved ∨ S.degHigh < max j l then
    S.symWeight n j l * symSq (sharpStrainCoef c K B x n j l) + S.antiWeight n j l * antiSq (sharpStrainCoef c K B x n j l)
  else 0

def vTerm (n : ℤ) (j l : ℕ) : ℝ :=
  if S.degHigh ≤ max j l then S.velWeight n j l * vecSq (sharpVelocityCoef c K B x n j l) else 0

def splitSum (d : ℕ) (f : ℕ → ℕ → ℝ) : ℝ :=
  (∑ j ∈ Finset.range (d + 1), ∑ l ∈ Finset.range (d + 1), f j l)
    + ∑' jl : ℕ × ℕ, if d < max jl.1 jl.2 then f jl.1 jl.2 else 0

def energyAt (n : ℤ) : ℝ :=
  S.energyWeight n * K.strainEnergy c.order n S.degHigh S.degLow x.2.1 x.2.2.1
    + S.vorticityWeight n * K.vorticityEnergy c.order n S.degHigh S.degLow x.2.1 x.2.2.1
    - S.tailShift n * ∑ a : Fin 3, K.topPart S.degHigh (gradMode c.order n x.2.1 a 0) (gradMode c.order n x.2.1 a 2)

def absorbAt (n : ℤ) : ℝ :=
  ∫ p in K.rect, K.lineWeight p.1 * absorbDensity c K S x n p

def modeEnergyAt (n : ℤ) : ℝ :=
  ∫ p in K.rect, p.1 * ((c.innerWeight - c.coercivity) * secondModeSq c.order n x.2.2.1 p
    + (c.splitVisc - c.innerWeight) * curlGradModeSq c.order n x.2.2.1 p)

end SharpEnergyTailParts

open SharpEnergyTailParts

def ModeEnergyTailStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ n : ℤ,
      (if n ∈ S.resolved then energyAt c K S x n else 0)
          + (if n ∈ R.yModes then splitSum S.degNear (yTerm c K S B x n) else 0)
          + (if n ∈ S.resolved then splitSum S.degNear (vTerm c K S B x n) else 0)
          + absorbAt c K S x n
        ≤ modeEnergyAt c K x n

def EnergyTailRegularStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      Summable (modeEnergyAt c K x) ∧ Summable (absorbAt c K S x)

namespace SharpEnergyTailInternal

theorem tsum_add_le {f g : ℕ × ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    ∑' i, (f i + g i) ≤ ∑' i, f i + ∑' i, g i := by
  by_cases h1 : Summable f
  · by_cases h2 : Summable g
    · rw [Summable.tsum_add h1 h2]
    · have hn : ¬ Summable (fun i => f i + g i) := by
        intro hs
        exact h2 (Summable.of_nonneg_of_le hg (fun i => by linarith [hf i]) hs)
      rw [tsum_eq_zero_of_not_summable hn]
      exact add_nonneg (tsum_nonneg hf) (tsum_nonneg hg)
  · have hn : ¬ Summable (fun i => f i + g i) := by
      intro hs
      exact h1 (Summable.of_nonneg_of_le hf (fun i => by linarith [hg i]) hs)
    rw [tsum_eq_zero_of_not_summable hn]
    exact add_nonneg (tsum_nonneg hf) (tsum_nonneg hg)

theorem tsum_finset_le {ι : Type*} (s : Finset ι) (f : ι → ℕ × ℕ → ℝ) (hf : ∀ n ∈ s, ∀ i, 0 ≤ f n i) :
    ∑' i, ∑ n ∈ s, f n i ≤ ∑ n ∈ s, ∑' i, f n i := by
  classical
  by_cases h : ∀ n ∈ s, Summable (f n)
  · rw [Summable.tsum_finsetSum h]
  · simp only [not_forall] at h
    obtain ⟨n, hn, hns⟩ := h
    have hnot : ¬ Summable (fun i => ∑ m ∈ s, f m i) := by
      intro hs
      refine hns (Summable.of_nonneg_of_le (hf n hn) (fun i => ?_) hs)
      exact Finset.single_le_sum (f := fun m => f m i) (fun m hm => hf m hm i) hn
    rw [tsum_eq_zero_of_not_summable hnot]
    exact Finset.sum_nonneg (fun m hm => tsum_nonneg (hf m hm))

theorem finset_as_tsum (s : Finset ℤ) (f : ℤ → ℝ) :
    ∑ n ∈ s, f n = ∑' n, (if n ∈ s then f n else 0) := by
  classical
  rw [tsum_eq_sum (s := s) (fun n hn => by simp [hn])]
  exact Finset.sum_congr rfl (fun n hn => by simp [hn])

theorem finset_summable (s : Finset ℤ) (f : ℤ → ℝ) : Summable (fun n => if n ∈ s then f n else 0) :=
  summable_of_ne_finset_zero (s := s) (fun n hn => by simp [hn])

end SharpEnergyTailInternal

open SharpEnergyTailInternal

theorem sharpEnergyTail_of (hM : ModeEnergyTailStatement) (hR : EnergyTailRegularStatement) :
    SharpEnergyTailStatement := by
  classical
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx
  have hy0 : ∀ n j l, 0 ≤ yTerm c K S B x n j l := by
    intro n j l
    unfold yTerm
    split_ifs with h
    · have a1 := (hd.scalars.sym_weight n j l h).1
      have a2 := (hd.scalars.anti_weight n j l h).1
      have f0 := hd.scalars.weightFloor_pos
      have s0 : 0 ≤ symSq (sharpStrainCoef c K B x n j l) := by
        unfold symSq; positivity
      have s1 : 0 ≤ antiSq (sharpStrainCoef c K B x n j l) := by
        unfold antiSq; positivity
      nlinarith
    · exact le_refl 0
  have hv0 : ∀ n ∈ S.resolved, ∀ j l, 0 ≤ vTerm c K S B x n j l := by
    intro n hn j l
    unfold vTerm
    split_ifs with h
    · have a1 := (hd.scalars.vel_weight n hn j l h).1
      have f0 := hd.scalars.weightFloor_pos
      have s0 : 0 ≤ vecSq (sharpVelocityCoef c K B x n j l) := by
        unfold vecSq; positivity
      nlinarith
    · exact le_refl 0
  have hW : weightedSharp c K S x B R ≤
      (∑ n ∈ R.yModes, splitSum S.degNear (yTerm c K S B x n))
        + ∑ n ∈ S.resolved, splitSum S.degNear (vTerm c K S B x n) := by
    have e3 : ∀ jl : ℕ × ℕ, (if S.degNear < max jl.1 jl.2 then
        (∑ n ∈ R.yModes, if n ∉ S.resolved ∨ S.degHigh < max jl.1 jl.2 then
            S.symWeight n jl.1 jl.2 * symSq (sharpStrainCoef c K B x n jl.1 jl.2)
              + S.antiWeight n jl.1 jl.2 * antiSq (sharpStrainCoef c K B x n jl.1 jl.2)
          else 0)
        + ∑ n ∈ S.resolved, if S.degHigh ≤ max jl.1 jl.2 then
            S.velWeight n jl.1 jl.2 * vecSq (sharpVelocityCoef c K B x n jl.1 jl.2) else 0
      else 0) =
        (∑ n ∈ R.yModes, if S.degNear < max jl.1 jl.2 then yTerm c K S B x n jl.1 jl.2 else 0)
          + ∑ n ∈ S.resolved, if S.degNear < max jl.1 jl.2 then vTerm c K S B x n jl.1 jl.2 else 0 := by
      intro jl
      by_cases h : S.degNear < max jl.1 jl.2
      · simp only [if_pos h]
        rfl
      · simp only [if_neg h, Finset.sum_const_zero, add_zero]
    have t1 := tsum_finset_le R.yModes
      (fun n jl => if S.degNear < max jl.1 jl.2 then yTerm c K S B x n jl.1 jl.2 else 0)
      (fun n _ jl => by split_ifs <;> simp [hy0])
    have t2 := tsum_finset_le S.resolved
      (fun n jl => if S.degNear < max jl.1 jl.2 then vTerm c K S B x n jl.1 jl.2 else 0)
      (fun n hn jl => by split_ifs <;> simp [hv0 n hn])
    have t3 := tsum_add_le
      (f := fun jl => ∑ n ∈ R.yModes, if S.degNear < max jl.1 jl.2 then yTerm c K S B x n jl.1 jl.2 else 0)
      (g := fun jl => ∑ n ∈ S.resolved, if S.degNear < max jl.1 jl.2 then vTerm c K S B x n jl.1 jl.2 else 0)
      (fun jl => Finset.sum_nonneg (fun n _ => by split_ifs <;> simp [hy0]))
      (fun jl => Finset.sum_nonneg (fun n hn => by split_ifs <;> simp [hv0 n hn]))
    unfold weightedSharp
    rw [tsum_congr e3]
    unfold splitSum
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have q1 : (∑ n ∈ R.yModes, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
        (if n ∉ S.resolved ∨ S.degHigh < max j l then
          S.symWeight n j l * symSq (sharpStrainCoef c K B x n j l) + S.antiWeight n j l * antiSq (sharpStrainCoef c K B x n j l)
        else 0)) = ∑ n ∈ R.yModes, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
          yTerm c K S B x n j l := rfl
    have q2 : (∑ n ∈ S.resolved, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
        (if S.degHigh ≤ max j l then S.velWeight n j l * vecSq (sharpVelocityCoef c K B x n j l) else 0))
          = ∑ n ∈ S.resolved, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
          vTerm c K S B x n j l := rfl
    rw [q1, q2]
    linarith
  obtain ⟨sM, sA⟩ := hR α h1 h2 c hc K S B Cl R hd hw x hx
  have hE : CellScalars.energyTerm c K S x.2.1 x.2.2.1 = ∑ n ∈ S.resolved, energyAt c K S x n := rfl
  have hA : absorbSum c K S x = ∑' n, absorbAt c K S x n := rfl
  have hME : modeEnergy c K x = ∑' n, modeEnergyAt c K x n := rfl
  rw [hE, hA, hME]
  rw [finset_as_tsum S.resolved (energyAt c K S x)]
  have hW' := hW
  rw [finset_as_tsum R.yModes, finset_as_tsum S.resolved] at hW'
  have sE := finset_summable S.resolved (energyAt c K S x)
  have sY := finset_summable R.yModes (fun n => splitSum S.degNear (yTerm c K S B x n))
  have sV := finset_summable S.resolved (fun n => splitSum S.degNear (vTerm c K S B x n))
  have key := Summable.tsum_le_tsum (fun n => hM α h1 h2 c hc K S B Cl R hd hw x hx n)
    (((sE.add sY).add sV).add sA) sM
  rw [Summable.tsum_add ((sE.add sY).add sV) sA, Summable.tsum_add (sE.add sY) sV,
    Summable.tsum_add sE sY] at key
  linarith

open SharpEnergyTailParts

namespace SharpEnergyTailParts

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (x : FieldTuple k)

def strainIdx (n : ℤ) (jl : ℕ × ℕ) : Prop := n ∉ S.resolved ∨ S.degHigh < max jl.1 jl.2

def symCoefSq (n : ℤ) (jl : ℕ × ℕ) : ℝ := symSq (sharpStrainCoef c K B x n jl.1 jl.2)

def antiCoefSq (n : ℤ) (jl : ℕ × ℕ) : ℝ := antiSq (sharpStrainCoef c K B x n jl.1 jl.2)

def velCoefSq (n : ℤ) (jl : ℕ × ℕ) : ℝ := vecSq (sharpVelocityCoef c K B x n jl.1 jl.2)

def symShift (n : ℤ) : ℝ := CellBox.angularWeight K n * (max (modeNumber c.order n - 2) 0) ^ 2

def antiShift (n : ℤ) : ℝ := CellBox.angularWeight K n * (max (modeNumber c.order n - 1) 0) ^ 2

def velEigen (jl : ℕ × ℕ) : ℝ := if S.degHigh ≤ jl.1 then radialEigen K jl.1 else heightEigen K jl.2

end SharpEnergyTailParts

open Classical in
def ModeCoefEnergyStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ n : ℤ,
      IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * sumSq (sharpGrad c K S x n p)) K.rect ∧
      IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * curlSq (sharpGrad c K S x n p)) K.rect ∧
      IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * vecSq (sharpVel c K S x n p)) K.rect ∧
      IntegrableOn (fun p : ℝ × ℝ => p.1 * secondModeSq c.order n x.2.2.1 p) K.rect ∧
      IntegrableOn (fun p : ℝ × ℝ => p.1 * curlGradModeSq c.order n x.2.2.1 p) K.rect ∧
      0 ≤ ∫ p in K.rect, p.1 * secondModeSq c.order n x.2.2.1 p ∧
      0 ≤ ∫ p in K.rect, p.1 * curlGradModeSq c.order n x.2.2.1 p ∧
      HasSum (fun jl => if strainIdx S n jl then symCoefSq c K B x n jl + antiCoefSq c K B x n jl else 0)
        (∫ p in K.rect, K.lineWeight p.1 * sumSq (sharpGrad c K S x n p)) ∧
      HasSum (fun jl => if strainIdx S n jl then 2 * antiCoefSq c K B x n jl else 0)
        (∫ p in K.rect, K.lineWeight p.1 * curlSq (sharpGrad c K S x n p)) ∧
      (n ∈ S.resolved → HasSum (fun jl : ℕ × ℕ => if S.degHigh ≤ max jl.1 jl.2 then velCoefSq c K B x n jl else 0)
        (∫ p in K.rect, K.lineWeight p.1 * vecSq (sharpVel c K S x n p))) ∧
      Summable (fun jl => if strainIdx S n jl then
        (CellScalars.tailLam K jl.1 jl.2 + symShift c K n) * symCoefSq c K B x n jl else 0) ∧
      Summable (fun jl => if strainIdx S n jl then
        (CellScalars.tailLam K jl.1 jl.2 + antiShift c K n) * antiCoefSq c K B x n jl else 0) ∧
      (if n ∈ S.resolved then K.strainEnergy c.order n S.degHigh S.degLow x.2.1 x.2.2.1 else 0)
          + (∑' jl, if strainIdx S n jl then
              (CellScalars.tailLam K jl.1 jl.2 + symShift c K n) * symCoefSq c K B x n jl else 0)
          + (∑' jl, if strainIdx S n jl then
              (CellScalars.tailLam K jl.1 jl.2 + antiShift c K n) * antiCoefSq c K B x n jl else 0)
        ≤ ∫ p in K.rect, p.1 * secondModeSq c.order n x.2.2.1 p ∧
      (if n ∈ S.resolved then K.vorticityEnergy c.order n S.degHigh S.degLow x.2.1 x.2.2.1 else 0)
          + 2 * (∑' jl, if strainIdx S n jl then
              (CellScalars.tailLam K jl.1 jl.2 + antiShift c K n) * antiCoefSq c K B x n jl else 0)
        ≤ ∫ p in K.rect, p.1 * curlGradModeSq c.order n x.2.2.1 p ∧
      (n ∈ S.resolved →
        Summable (fun jl : ℕ × ℕ => if S.degHigh ≤ max jl.1 jl.2 then velEigen K S jl * velCoefSq c K B x n jl else 0) ∧
        (∑' jl : ℕ × ℕ, if S.degHigh ≤ max jl.1 jl.2 then velEigen K S jl * velCoefSq c K B x n jl else 0)
          ≤ (∑ a : Fin 3, K.topPart S.degHigh (gradMode c.order n x.2.1 a 0) (gradMode c.order n x.2.1 a 2))
            + ∑' jl, if strainIdx S n jl then symCoefSq c K B x n jl + antiCoefSq c K B x n jl else 0)

namespace SharpEnergyTailInternal

theorem split_eq {d : ℕ} {f : ℕ → ℕ → ℝ} (hf : Summable (fun jl : ℕ × ℕ => f jl.1 jl.2)) :
    splitSum d f = ∑' jl : ℕ × ℕ, f jl.1 jl.2 := by
  classical
  set s : Finset (ℕ × ℕ) := Finset.range (d + 1) ×ˢ Finset.range (d + 1) with hs
  have hbox : ∀ jl : ℕ × ℕ, (jl ∈ s ↔ ¬ d < max jl.1 jl.2) := by
    intro jl
    simp only [hs, Finset.mem_product, Finset.mem_range, not_lt, max_le_iff]
    omega
  have hh : Summable (fun jl : ℕ × ℕ => if d < max jl.1 jl.2 then 0 else f jl.1 jl.2) :=
    summable_of_ne_finset_zero (s := s) (fun jl hjl => by
      have := (hbox jl).not.mp hjl
      simp only [not_not] at this
      simp [this])
  have hg : Summable (fun jl : ℕ × ℕ => if d < max jl.1 jl.2 then f jl.1 jl.2 else 0) := by
    refine (hf.sub hh).congr (fun jl => ?_)
    split_ifs <;> simp
  have e1 : ∑' jl : ℕ × ℕ, f jl.1 jl.2 = (∑' jl : ℕ × ℕ, if d < max jl.1 jl.2 then 0 else f jl.1 jl.2)
      + ∑' jl : ℕ × ℕ, if d < max jl.1 jl.2 then f jl.1 jl.2 else 0 := by
    rw [← Summable.tsum_add hh hg]
    exact tsum_congr (fun jl => by split_ifs <;> simp)
  have e2 : (∑' jl : ℕ × ℕ, if d < max jl.1 jl.2 then 0 else f jl.1 jl.2)
      = ∑ j ∈ Finset.range (d + 1), ∑ l ∈ Finset.range (d + 1), f j l := by
    rw [tsum_eq_sum (s := s) (fun jl hjl => by
      have := (hbox jl).not.mp hjl
      simp only [not_not] at this
      simp [this])]
    rw [hs, Finset.sum_product]
    refine Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun l hl => ?_))
    have : ¬ d < max j l := by
      simp only [Finset.mem_range] at hj hl
      omega
    simp [this]
  unfold splitSum
  rw [e1, e2]

theorem split_le {d : ℕ} {f : ℕ → ℕ → ℝ} {F : ℕ × ℕ → ℝ} {v : ℝ} (h0 : ∀ j l, 0 ≤ f j l)
    (hle : ∀ jl : ℕ × ℕ, f jl.1 jl.2 ≤ F jl) (hF : HasSum F v) : splitSum d f ≤ v := by
  have hs : Summable (fun jl : ℕ × ℕ => f jl.1 jl.2) :=
    Summable.of_nonneg_of_le (fun jl => h0 jl.1 jl.2) hle hF.summable
  rw [split_eq hs, ← hF.tsum_eq]
  exact Summable.tsum_le_tsum hle hs hF.summable

end SharpEnergyTailInternal

open SharpEnergyTailInternal

theorem modeEnergyTail_of (h : ModeCoefEnergyStatement) : ModeEnergyTailStatement := by
  classical
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx n
  obtain ⟨iS, iC, iV, iM, iN, nM, nN, pS, pC, pV, sA1, sA2, eS, eC, eV⟩ :=
    h α h1 h2 c hc K S B Cl R hd hw x hx n
  have sc := hd.scalars
  have hab : absorbAt c K S x n = S.curlAbsorb n * (∫ p in K.rect, K.lineWeight p.1 * curlSq (sharpGrad c K S x n p))
      + S.strainAbsorb n * (∫ p in K.rect, K.lineWeight p.1 * sumSq (sharpGrad c K S x n p))
      + (if n ∈ S.resolved then S.velocityAbsorb n * (∫ p in K.rect, K.lineWeight p.1 * vecSq (sharpVel c K S x n p))
        else 0) := by
    unfold absorbAt absorbDensity
    by_cases hr : n ∈ S.resolved
    · simp only [hr, if_true]
      have e : (fun p : ℝ × ℝ => K.lineWeight p.1 * (S.curlAbsorb n * curlSq (sharpGrad c K S x n p)
          + S.strainAbsorb n * sumSq (sharpGrad c K S x n p) + S.velocityAbsorb n * vecSq (sharpVel c K S x n p)))
          = fun p => (S.curlAbsorb n * (K.lineWeight p.1 * curlSq (sharpGrad c K S x n p))
            + S.strainAbsorb n * (K.lineWeight p.1 * sumSq (sharpGrad c K S x n p)))
            + S.velocityAbsorb n * (K.lineWeight p.1 * vecSq (sharpVel c K S x n p)) := by
        funext p
        ring
      rw [e, integral_add ?_ (iV.const_mul _),
        integral_add (iC.const_mul _) (iS.const_mul _), integral_const_mul, integral_const_mul, integral_const_mul]
      exact (iC.const_mul _).add (iS.const_mul _)
    · simp only [hr, if_false, add_zero]
      have e : (fun p : ℝ × ℝ => K.lineWeight p.1 * (S.curlAbsorb n * curlSq (sharpGrad c K S x n p)
          + S.strainAbsorb n * sumSq (sharpGrad c K S x n p)))
          = fun p => S.curlAbsorb n * (K.lineWeight p.1 * curlSq (sharpGrad c K S x n p))
            + S.strainAbsorb n * (K.lineWeight p.1 * sumSq (sharpGrad c K S x n p)) := by
        funext p
        ring
      rw [e, integral_add (iC.const_mul _) (iS.const_mul _), integral_const_mul, integral_const_mul]
  have hme : modeEnergyAt c K x n = (c.innerWeight - c.coercivity) * (∫ p in K.rect, p.1 * secondModeSq c.order n x.2.2.1 p)
      + (c.splitVisc - c.innerWeight) * (∫ p in K.rect, p.1 * curlGradModeSq c.order n x.2.2.1 p) := by
    unfold modeEnergyAt
    have e : (fun p : ℝ × ℝ => p.1 * ((c.innerWeight - c.coercivity) * secondModeSq c.order n x.2.2.1 p
        + (c.splitVisc - c.innerWeight) * curlGradModeSq c.order n x.2.2.1 p))
        = fun p => (c.innerWeight - c.coercivity) * (p.1 * secondModeSq c.order n x.2.2.1 p)
          + (c.splitVisc - c.innerWeight) * (p.1 * curlGradModeSq c.order n x.2.2.1 p) := by
      funext p
      ring
    rw [e, integral_add (iM.const_mul _) (iN.const_mul _), integral_const_mul, integral_const_mul]
  rw [hab, hme]
  set E := S.energyWeight n with hE
  set V := S.vorticityWeight n with hV
  set tS := S.tailShift n with htS
  set cA := S.curlAbsorb n with hcA
  set sA := S.strainAbsorb n with hsA
  set vA := S.velocityAbsorb n with hvA
  set F1 := ∑' jl, if strainIdx S n jl then
      (CellScalars.tailLam K jl.1 jl.2 + symShift c K n) * symCoefSq c K B x n jl else 0 with hF1
  set F2 := ∑' jl, if strainIdx S n jl then
      (CellScalars.tailLam K jl.1 jl.2 + antiShift c K n) * antiCoefSq c K B x n jl else 0 with hF2
  set Is := ∫ p in K.rect, K.lineWeight p.1 * sumSq (sharpGrad c K S x n p) with hIs
  set Ic := ∫ p in K.rect, K.lineWeight p.1 * curlSq (sharpGrad c K S x n p) with hIc
  set Iv := ∫ p in K.rect, K.lineWeight p.1 * vecSq (sharpVel c K S x n p) with hIv
  have hbound : HasSum (fun jl : ℕ × ℕ => if strainIdx S n jl then
      (E * (CellScalars.tailLam K jl.1 jl.2 + symShift c K n) - sA - tS) * symCoefSq c K B x n jl
        + ((E + 2 * V) * (CellScalars.tailLam K jl.1 jl.2 + antiShift c K n) - 2 * cA - sA - tS)
          * antiCoefSq c K B x n jl else 0)
      (E * F1 + (E + 2 * V) * F2 - (sA + tS) * Is - cA * Ic) := by
    have := (((sA1.hasSum.mul_left E).add (sA2.hasSum.mul_left (E + 2 * V))).sub
      (pS.mul_left (sA + tS))).sub (pC.mul_left cA)
    have e : (fun jl : ℕ × ℕ => if strainIdx S n jl then
        (E * (CellScalars.tailLam K jl.1 jl.2 + symShift c K n) - sA - tS) * symCoefSq c K B x n jl
          + ((E + 2 * V) * (CellScalars.tailLam K jl.1 jl.2 + antiShift c K n) - 2 * cA - sA - tS)
            * antiCoefSq c K B x n jl else 0) = fun b =>
      (((E * if strainIdx S n b then (CellScalars.tailLam K b.1 b.2 + symShift c K n) * symCoefSq c K B x n b else 0) +
            (E + 2 * V) *
              if strainIdx S n b then (CellScalars.tailLam K b.1 b.2 + antiShift c K n) * antiCoefSq c K B x n b
              else 0) -
          (sA + tS) * if strainIdx S n b then symCoefSq c K B x n b + antiCoefSq c K B x n b else 0) -
        cA * if strainIdx S n b then 2 * antiCoefSq c K B x n b else 0 := by
      funext jl
      split_ifs <;> ring
    rw [e]
    exact this
  have ysplit : (if n ∈ R.yModes then splitSum S.degNear (yTerm c K S B x n) else 0)
      ≤ E * F1 + (E + 2 * V) * F2 - (sA + tS) * Is - cA * Ic := by
    have hle : ∀ jl : ℕ × ℕ, yTerm c K S B x n jl.1 jl.2 ≤ (if strainIdx S n jl then
        (E * (CellScalars.tailLam K jl.1 jl.2 + symShift c K n) - sA - tS) * symCoefSq c K B x n jl
          + ((E + 2 * V) * (CellScalars.tailLam K jl.1 jl.2 + antiShift c K n) - 2 * cA - sA - tS)
            * antiCoefSq c K B x n jl else 0) := by
      intro jl
      unfold yTerm strainIdx
      split_ifs with hi
      · have w1 := (sc.sym_weight n jl.1 jl.2 hi).2
        have w2 := (sc.anti_weight n jl.1 jl.2 hi).2
        have s0 : 0 ≤ symSq (sharpStrainCoef c K B x n jl.1 jl.2) := by unfold symSq; positivity
        have s1 : 0 ≤ antiSq (sharpStrainCoef c K B x n jl.1 jl.2) := by unfold antiSq; positivity
        unfold symCoefSq antiCoefSq symShift antiShift
        nlinarith [mul_le_mul_of_nonneg_right w1 s0, mul_le_mul_of_nonneg_right w2 s1]
      · exact le_refl 0
    have y0 : ∀ j l, 0 ≤ yTerm c K S B x n j l := by
      intro j l
      unfold yTerm
      split_ifs with hi
      · have a1 := (sc.sym_weight n j l hi).1
        have a2 := (sc.anti_weight n j l hi).1
        have f0 := sc.weightFloor_pos
        have s0 : 0 ≤ symSq (sharpStrainCoef c K B x n j l) := by unfold symSq; positivity
        have s1 : 0 ≤ antiSq (sharpStrainCoef c K B x n j l) := by unfold antiSq; positivity
        nlinarith
      · exact le_refl 0
    by_cases hy : n ∈ R.yModes
    · rw [if_pos hy]
      exact split_le y0 hle hbound
    · rw [if_neg hy]
      exact hbound.nonneg (fun jl => le_trans (y0 jl.1 jl.2) (hle jl))
  set Xs := ∫ p in K.rect, p.1 * secondModeSq c.order n x.2.2.1 p with hXs
  set Xc := ∫ p in K.rect, p.1 * curlGradModeSq c.order n x.2.2.1 p with hXc
  have E0 : 0 < E := sc.energyWeight_pos n
  have E1 : E ≤ c.innerWeight - c.coercivity := sc.energyWeight_le n
  have V0 : 0 ≤ V := sc.vorticityWeight_nonneg n
  have V1 : V ≤ c.splitVisc - c.innerWeight := sc.vorticityWeight_le n
  have m1 : 0 ≤ (c.innerWeight - c.coercivity - E) * Xs := mul_nonneg (by linarith) nM
  have m2 : 0 ≤ (c.splitVisc - c.innerWeight - V) * Xc := mul_nonneg (by linarith) nN
  by_cases hr : n ∈ S.resolved
  · obtain ⟨sV, eV'⟩ := eV hr
    have pV' := pV hr
    have T0 : 0 ≤ tS := sc.tailShift_nonneg n
    set Fv := ∑' jl : ℕ × ℕ, if S.degHigh ≤ max jl.1 jl.2 then velEigen K S jl * velCoefSq c K B x n jl else 0 with hFv
    have hvb : HasSum (fun jl : ℕ × ℕ => if S.degHigh ≤ max jl.1 jl.2 then
        (tS * velEigen K S jl - vA) * velCoefSq c K B x n jl else 0) (tS * Fv - vA * Iv) := by
      have := (sV.hasSum.mul_left tS).sub (pV'.mul_left vA)
      have e : (fun jl : ℕ × ℕ => if S.degHigh ≤ max jl.1 jl.2 then
          (tS * velEigen K S jl - vA) * velCoefSq c K B x n jl else 0) = fun b =>
          (tS * if S.degHigh ≤ max b.1 b.2 then velEigen K S b * velCoefSq c K B x n b else 0)
            - vA * if S.degHigh ≤ max b.1 b.2 then velCoefSq c K B x n b else 0 := by
        funext jl
        split_ifs <;> ring
      rw [e]
      exact this
    have vsplit : splitSum S.degNear (vTerm c K S B x n) ≤ tS * Fv - vA * Iv := by
      refine split_le (fun j l => ?_) (fun jl => ?_) hvb
      · unfold vTerm
        split_ifs with hi
        · have a1 := (sc.vel_weight n hr j l hi).1
          have f0 := sc.weightFloor_pos
          have s0 : 0 ≤ vecSq (sharpVelocityCoef c K B x n j l) := by unfold vecSq; positivity
          nlinarith
        · exact le_refl 0
      · unfold vTerm
        split_ifs with hi
        · have w := (sc.vel_weight n hr jl.1 jl.2 hi).2
          have s0 : 0 ≤ vecSq (sharpVelocityCoef c K B x n jl.1 jl.2) := by unfold vecSq; positivity
          unfold velCoefSq velEigen
          exact mul_le_mul_of_nonneg_right w s0
        · exact le_refl 0
    have hIs' : (∑' jl, if strainIdx S n jl then symCoefSq c K B x n jl + antiCoefSq c K B x n jl else 0) = Is :=
      pS.tsum_eq
    rw [hIs'] at eV'
    simp only [hr, if_true] at eS eC ⊢
    have k1 := mul_le_mul_of_nonneg_left eS E0.le
    have k2 := mul_le_mul_of_nonneg_left eC V0
    have k3 := mul_le_mul_of_nonneg_left eV' T0
    unfold energyAt
    linear_combination ysplit + vsplit + k1 + k2 + k3 + m1 + m2
  · have T0 : tS = 0 := sc.tailShift_zero n hr
    simp only [hr, if_false, zero_add, add_zero] at eS eC ⊢
    have k1 := mul_le_mul_of_nonneg_left eS E0.le
    have k2 := mul_le_mul_of_nonneg_left eC V0
    rw [T0] at ysplit
    linear_combination ysplit + k1 + k2 + m1 + m2

theorem sharpEnergyTail_of_coef (hC : ModeCoefEnergyStatement) (hR : EnergyTailRegularStatement) :
    SharpEnergyTailStatement :=
  sharpEnergyTail_of (modeEnergyTail_of hC) hR

open Classical in
def ModeEnergySumStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ n : ℤ,
      IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * sumSq (sharpGrad c K S x n p)) K.rect ∧
      IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * curlSq (sharpGrad c K S x n p)) K.rect ∧
      IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * vecSq (sharpVel c K S x n p)) K.rect ∧
      IntegrableOn (fun p : ℝ × ℝ => p.1 * secondModeSq c.order n x.2.2.1 p) K.rect ∧
      IntegrableOn (fun p : ℝ × ℝ => p.1 * curlGradModeSq c.order n x.2.2.1 p) K.rect ∧
      HasSum (fun jl => if strainIdx S n jl then symCoefSq c K B x n jl + antiCoefSq c K B x n jl else 0)
        (∫ p in K.rect, K.lineWeight p.1 * sumSq (sharpGrad c K S x n p)) ∧
      HasSum (fun jl => if strainIdx S n jl then 2 * antiCoefSq c K B x n jl else 0)
        (∫ p in K.rect, K.lineWeight p.1 * curlSq (sharpGrad c K S x n p)) ∧
      (n ∈ S.resolved → HasSum (fun jl : ℕ × ℕ => if S.degHigh ≤ max jl.1 jl.2 then velCoefSq c K B x n jl else 0)
        (∫ p in K.rect, K.lineWeight p.1 * vecSq (sharpVel c K S x n p)))

open Classical in
def ModeStrainCoefStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ n : ℤ,
      Summable (fun jl => if strainIdx S n jl then
        (CellScalars.tailLam K jl.1 jl.2 + symShift c K n) * symCoefSq c K B x n jl else 0) ∧
      Summable (fun jl => if strainIdx S n jl then
        (CellScalars.tailLam K jl.1 jl.2 + antiShift c K n) * antiCoefSq c K B x n jl else 0) ∧
      (if n ∈ S.resolved then K.strainEnergy c.order n S.degHigh S.degLow x.2.1 x.2.2.1 else 0)
          + (∑' jl, if strainIdx S n jl then
              (CellScalars.tailLam K jl.1 jl.2 + symShift c K n) * symCoefSq c K B x n jl else 0)
          + (∑' jl, if strainIdx S n jl then
              (CellScalars.tailLam K jl.1 jl.2 + antiShift c K n) * antiCoefSq c K B x n jl else 0)
        ≤ ∫ p in K.rect, p.1 * secondModeSq c.order n x.2.2.1 p

open Classical in
def ModeVorticityCoefStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ n : ℤ,
      (if n ∈ S.resolved then K.vorticityEnergy c.order n S.degHigh S.degLow x.2.1 x.2.2.1 else 0)
          + 2 * (∑' jl, if strainIdx S n jl then
              (CellScalars.tailLam K jl.1 jl.2 + antiShift c K n) * antiCoefSq c K B x n jl else 0)
        ≤ ∫ p in K.rect, p.1 * curlGradModeSq c.order n x.2.2.1 p

open Classical in
def ModeVelocityCoefStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ n ∈ S.resolved,
      Summable (fun jl : ℕ × ℕ => if S.degHigh ≤ max jl.1 jl.2 then velEigen K S jl * velCoefSq c K B x n jl else 0) ∧
      (∑' jl : ℕ × ℕ, if S.degHigh ≤ max jl.1 jl.2 then velEigen K S jl * velCoefSq c K B x n jl else 0)
        ≤ (∑ a : Fin 3, K.topPart S.degHigh (gradMode c.order n x.2.1 a 0) (gradMode c.order n x.2.1 a 2))
          + ∑' jl, if strainIdx S n jl then symCoefSq c K B x n jl + antiCoefSq c K B x n jl else 0

namespace SharpEnergyTailInternal

theorem rect_nonneg_integral {K : CellBox} (hK : IsCellBox K) {f : ℝ × ℝ → ℝ} (hf : ∀ p, 0 ≤ f p) :
    0 ≤ ∫ p in K.rect, p.1 * f p := by
  refine setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) (fun p hp => ?_)
  have h1 : K.r₁ ≤ p.1 := hp.1.1
  exact mul_nonneg (le_trans hK.r_order.1 h1) (hf p)

end SharpEnergyTailInternal

open SharpEnergyTailInternal

theorem modeCoefEnergy_of (hP : ModeEnergySumStatement) (hS : ModeStrainCoefStatement)
    (hV : ModeVorticityCoefStatement) (hT : ModeVelocityCoefStatement) : ModeCoefEnergyStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx n
  obtain ⟨iS, iC, iV, iM, iN, pS, pC, pV⟩ := hP α h1 h2 c hc K S B Cl R hd hw x hx n
  obtain ⟨sA1, sA2, eS⟩ := hS α h1 h2 c hc K S B Cl R hd hw x hx n
  have eC := hV α h1 h2 c hc K S B Cl R hd hw x hx n
  have eV := hT α h1 h2 c hc K S B Cl R hd hw x hx n
  have nM : 0 ≤ ∫ p in K.rect, p.1 * secondModeSq c.order n x.2.2.1 p :=
    rect_nonneg_integral hd.box (fun p => by unfold secondModeSq; positivity)
  have nN : 0 ≤ ∫ p in K.rect, p.1 * curlGradModeSq c.order n x.2.2.1 p :=
    rect_nonneg_integral hd.box (fun p => by unfold curlGradModeSq; positivity)
  exact ⟨iS, iC, iV, iM, iN, nM, nN, pS, pC, pV, sA1, sA2, eS, eC, eV⟩

theorem sharpEnergyTail_of_parts (hP : ModeEnergySumStatement) (hS : ModeStrainCoefStatement)
    (hV : ModeVorticityCoefStatement) (hT : ModeVelocityCoefStatement) (hR : EnergyTailRegularStatement) :
    SharpEnergyTailStatement :=
  sharpEnergyTail_of_coef (modeCoefEnergy_of hP hS hV hT) hR

open Classical in
def ModeVelocityIdentityStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ n ∈ S.resolved,
      Summable (fun jl : ℕ × ℕ => if S.degHigh ≤ max jl.1 jl.2 then velEigen K S jl * velCoefSq c K B x n jl else 0) ∧
      (∑' jl : ℕ × ℕ, if S.degHigh ≤ max jl.1 jl.2 then velEigen K S jl * velCoefSq c K B x n jl else 0)
        ≤ ∑ a : Fin 3, K.velocityTail S.degHigh (fun p => modeVec c.order n x.1 p.1 p.2 a) ∧
      (∑ a : Fin 3, ∑ b : Fin 3, K.tailNormSq S.degHigh (gradMode c.order n x.2.1 a b))
        ≤ ∑' jl, if strainIdx S n jl then symCoefSq c K B x n jl + antiCoefSq c K B x n jl else 0

theorem modeVelocityCoef_of (hT : VelocityTailStatement) (hI : ModeVelocityIdentityStatement) :
    ModeVelocityCoefStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx n hn
  obtain ⟨hs, e1, e2⟩ := hI α h1 h2 c hc K S B Cl R hd hw x hx n hn
  have hQ : 5 ≤ S.degHigh := by
    have := hd.scalars.degrees
    omega
  have ht := hT K hd.box c.order S.degHigh hQ x.1 x.2.1 x.2.2.1 hx.1 n 1 zero_le_one
  simp only [one_mul] at ht
  exact ⟨hs, by linarith⟩

open Classical in
def ModeStrainIdentityStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ n : ℤ,
      Summable (fun jl => if strainIdx S n jl then
        (CellScalars.tailLam K jl.1 jl.2 + symShift c K n) * symCoefSq c K B x n jl else 0) ∧
      Summable (fun jl => if strainIdx S n jl then
        (CellScalars.tailLam K jl.1 jl.2 + antiShift c K n) * antiCoefSq c K B x n jl else 0) ∧
      (n ∈ S.resolved →
        (∑' jl, if strainIdx S n jl then
              (CellScalars.tailLam K jl.1 jl.2 + symShift c K n) * symCoefSq c K B x n jl else 0)
          + (∑' jl, if strainIdx S n jl then
              (CellScalars.tailLam K jl.1 jl.2 + antiShift c K n) * antiCoefSq c K B x n jl else 0)
        ≤ ∑ a : Fin 3, ∑ b : Fin 3,
            (K.tailGradWeight S.degHigh (gradMode c.order n x.2.1 a b) (radialGradMode c.order n x.2.2.1 a b)
                (heightGradMode c.order n x.2.2.1 a b)
              + K.angularWeight n * K.tailNormSq S.degHigh (angularGradMode c.order n x.2.2.1 a b))) ∧
      (n ∉ S.resolved →
        (∑' jl, if strainIdx S n jl then
              (CellScalars.tailLam K jl.1 jl.2 + symShift c K n) * symCoefSq c K B x n jl else 0)
          + (∑' jl, if strainIdx S n jl then
              (CellScalars.tailLam K jl.1 jl.2 + antiShift c K n) * antiCoefSq c K B x n jl else 0)
        ≤ ∑ a : Fin 3, ∑ b : Fin 3,
            (K.fullGradWeight (radialGradMode c.order n x.2.2.1 a b) (heightGradMode c.order n x.2.2.1 a b)
              + K.angularWeight n * K.normSqOn K.lineWeightFn (angularGradMode c.order n x.2.2.1 a b)))

open Classical in
def ModeVorticityIdentityStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ n : ℤ,
      (n ∈ S.resolved →
        2 * (∑' jl, if strainIdx S n jl then
              (CellScalars.tailLam K jl.1 jl.2 + antiShift c K n) * antiCoefSq c K B x n jl else 0)
        ≤ ∑ i : Fin 3,
            (K.tailGradWeight S.degHigh (fun p => curlComp (fun a b => gradMode c.order n x.2.1 a b p) i)
                (fun p => curlComp (fun a b => radialGradMode c.order n x.2.2.1 a b p) i)
                (fun p => curlComp (fun a b => heightGradMode c.order n x.2.2.1 a b p) i)
              + K.angularWeight n * K.tailNormSq S.degHigh
                (fun p => curlComp (fun a b => angularGradMode c.order n x.2.2.1 a b p) i))) ∧
      (n ∉ S.resolved →
        2 * (∑' jl, if strainIdx S n jl then
              (CellScalars.tailLam K jl.1 jl.2 + antiShift c K n) * antiCoefSq c K B x n jl else 0)
        ≤ ∫ p in K.rect, p.1 * curlGradModeSq c.order n x.2.2.1 p)

theorem modeStrainCoef_of (hRE : ResolvedEnergyStatement) (hUE : UnresolvedEnergyStatement)
    (hI : ModeStrainIdentityStatement) : ModeStrainCoefStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx n
  obtain ⟨s1, s2, eR, eU⟩ := hI α h1 h2 c hc K S B Cl R hd hw x hx n
  refine ⟨s1, s2, ?_⟩
  by_cases hn : n ∈ S.resolved
  · have hax : K.IsAxis → n = 0 := by
      intro h
      have := hd.scalars.axis_resolved h
      rw [this] at hn
      simpa using hn
    have hdeg := hd.scalars.degrees
    have e := (hRE K hd.box c.order S.degHigh S.degLow hdeg.1 hdeg.2.1 x.1 x.2.1 x.2.2.1 hx.1 n hax).1
    have e' := eR hn
    simp only [hn, if_true]
    linarith
  · have e := hUE K hd.box c.order x.1 x.2.1 x.2.2.1 hx.1 n
    have e' := eU hn
    simp only [hn, if_false]
    linarith

theorem modeVorticityCoef_of (hRE : ResolvedEnergyStatement) (hI : ModeVorticityIdentityStatement) :
    ModeVorticityCoefStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx n
  obtain ⟨eR, eU⟩ := hI α h1 h2 c hc K S B Cl R hd hw x hx n
  by_cases hn : n ∈ S.resolved
  · have hax : K.IsAxis → n = 0 := by
      intro h
      have := hd.scalars.axis_resolved h
      rw [this] at hn
      simpa using hn
    have hdeg := hd.scalars.degrees
    have e := (hRE K hd.box c.order S.degHigh S.degLow hdeg.1 hdeg.2.1 x.1 x.2.1 x.2.2.1 hx.1 n hax).2
    have e' := eR hn
    simp only [hn, if_true]
    linarith
  · have e' := eU hn
    simp only [hn, if_false]
    linarith


theorem sharpEnergyTail_of_leaves (hRE : ResolvedEnergyStatement) (hUE : UnresolvedEnergyStatement)
    (hVT : VelocityTailStatement) (hP : ModeEnergySumStatement) (hSI : ModeStrainIdentityStatement)
    (hVI : ModeVorticityIdentityStatement) (hTI : ModeVelocityIdentityStatement) (hR : EnergyTailRegularStatement) :
    SharpEnergyTailStatement :=
  sharpEnergyTail_of_parts hP (modeStrainCoef_of hRE hUE hSI) (modeVorticityCoef_of hRE hVI)
    (modeVelocityCoef_of hVT hTI) hR

end CellAnalysis

end CellCert

end Breakdown
