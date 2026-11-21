import Breakdown.FracCell.StEnergyProof

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis CellFormula SteadyCert Assembly

private lemma quad_slot {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ}
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

private lemma sum3_left (x : ℂ) (c T : Fin 3 → ℂ) :
    ∑ a, (starRingEnd ℂ) (x * c a) * T a = (starRingEnd ℂ) x * ∑ a, (starRingEnd ℂ) (c a) * T a := by
  simp only [Fin.sum_univ_three, map_mul]
  ring

private lemma sum3_right (x : ℂ) (c d : Fin 3 → ℂ) (T : Fin 3 → Fin 3 → ℂ) :
    ∑ a, d a * ∑ b, T a b * (x * c b) = x * ∑ a, d a * ∑ b, T a b * c b := by
  simp only [Fin.sum_univ_three]
  ring

private lemma curl_add (s t : Fin 3 → Fin 3 → ℂ) (i : Fin 3) :
    curlComp (s + t) i = curlComp s i + curlComp t i := by
  simp only [curlComp, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma curl_smul (x : ℂ) (s : Fin 3 → Fin 3 → ℂ) (i : Fin 3) :
    curlComp (x • s) i = x * curlComp s i := by
  simp only [curlComp, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

private lemma coupling_add (Gm : Fin 3 → Fin 3 → ℂ) (v w : Fin 3 → ℂ) :
    couplingMap Gm (v + w) = couplingMap Gm v + couplingMap Gm w := by
  funext i l
  simp only [couplingMap, bracketMat, Pi.add_apply, Fin.sum_univ_three]
  ring

private lemma coupling_smul (Gm : Fin 3 → Fin 3 → ℂ) (x : ℂ) (v : Fin 3 → ℂ) :
    couplingMap Gm (x • v) = x • couplingMap Gm v := by
  funext i l
  simp only [couplingMap, bracketMat, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

private lemma pairing_add_left (s t w : Fin 3 → Fin 3 → ℂ) : entryPairing (s + t) w = entryPairing s w + entryPairing t w := by
  simp only [entryPairing, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma pairing_add_right (s t w : Fin 3 → Fin 3 → ℂ) : entryPairing w (s + t) = entryPairing w s + entryPairing w t := by
  simp only [entryPairing, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

private lemma pairing_smul_left (x : ℂ) (s w : Fin 3 → Fin 3 → ℂ) : entryPairing (x • s) w = x * entryPairing s w := by
  simp only [entryPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private lemma pairing_smul_right (x : ℂ) (s w : Fin 3 → Fin 3 → ℂ) :
    entryPairing w (x • s) = (starRingEnd ℂ) x * entryPairing w s := by
  simp only [entryPairing, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

private lemma pvec_add (s t : Fin 3 → Fin 3 → ℂ) (v w : Fin 3 → ℂ) :
    pairVec (s + t) (v + w) = pairVec s v + pairVec t w := by
  funext i
  simp only [pairVec, Pi.add_apply]
  split_ifs <;> rfl

private lemma pvec_smul (x : ℂ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) :
    pairVec (x • s) (x • v) = x • pairVec s v := by
  funext i
  simp only [pairVec, Pi.smul_apply]
  split_ifs <;> rfl

private lemma msesq_add_left (A : Matrix (Fin 12) (Fin 12) ℂ) (U V W : Fin 12 → ℂ) :
    matrixSesq A (U + V) W = matrixSesq A U W + matrixSesq A V W := by
  simp only [matrixSesq, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

private lemma msesq_add_right (A : Matrix (Fin 12) (Fin 12) ℂ) (U V W : Fin 12 → ℂ) :
    matrixSesq A W (U + V) = matrixSesq A W U + matrixSesq A W V := by
  simp only [matrixSesq, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma msesq_smul_left (A : Matrix (Fin 12) (Fin 12) ℂ) (x : ℂ) (U W : Fin 12 → ℂ) :
    matrixSesq A (x • U) W = (starRingEnd ℂ) x * matrixSesq A U W := by
  simp only [matrixSesq, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

private lemma msesq_smul_right (A : Matrix (Fin 12) (Fin 12) ℂ) (x : ℂ) (U W : Fin 12 → ℂ) :
    matrixSesq A W (x • U) = x * matrixSesq A W U := by
  simp only [matrixSesq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

section Sesq

variable {k N : ℕ} (c : FracCellData k N) (S : CellScalars)

private lemma ps_add_left (n n' : ℤ) (p : ℝ × ℝ) (U V W : (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)) :
    pairSesq c S n n' p (U + V) W = pairSesq c S n n' p U W + pairSesq c S n n' p V W := by
  simp only [pairSesq, waveForm, Prod.fst_add, Prod.snd_add, curl_add, coupling_add,
    pairing_add_right, pvec_add, msesq_add_left, map_add, add_mul, Finset.sum_add_distrib]
  split_ifs <;> ring

private lemma ps_add_right (n n' : ℤ) (p : ℝ × ℝ) (U V W : (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)) :
    pairSesq c S n n' p W (U + V) = pairSesq c S n n' p W U + pairSesq c S n n' p W V := by
  simp only [pairSesq, waveForm, Prod.fst_add, Prod.snd_add, curl_add, coupling_add, pairing_add_left,
    pvec_add, msesq_add_right, mul_add, Finset.sum_add_distrib]
  split_ifs <;> ring

private lemma ps_smul_left (n n' : ℤ) (p : ℝ × ℝ) (x : ℂ) (U W : (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)) :
    pairSesq c S n n' p (x • U) W = (starRingEnd ℂ) x * pairSesq c S n n' p U W := by
  simp only [pairSesq, waveForm, Prod.smul_fst, Prod.smul_snd, curl_smul, coupling_smul,
    pairing_smul_right, pvec_smul, msesq_smul_left, sum3_left]
  split_ifs <;> ring

private lemma ps_smul_right (n n' : ℤ) (p : ℝ × ℝ) (x : ℂ) (U W : (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)) :
    pairSesq c S n n' p W (x • U) = x * pairSesq c S n n' p W U := by
  simp only [pairSesq, waveForm, Prod.smul_fst, Prod.smul_snd, curl_smul, coupling_smul, pairing_smul_left,
    pvec_smul, msesq_smul_right, sum3_right]
  split_ifs <;> ring

end Sesq


private def slotEquiv (Q : ℕ) : (Fin 3 × Fin 3 × Fin (Q + 1) × Fin (Q + 1)) ⊕ (Fin 3 × Fin Q × Fin Q) ≃ LowSlot Q where
  toFun
    | .inl x => .strain x.1 x.2.1 x.2.2.1 x.2.2.2
    | .inr x => .velocity x.1 x.2.1 x.2.2
  invFun
    | .strain a b j l => .inl (a, b, j, l)
    | .velocity a j l => .inr (a, j, l)
  left_inv := by rintro (⟨a, b, j, l⟩ | ⟨a, j, l⟩) <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

private lemma slot_sum (B : CellBases) {Q : ℕ} (x : LowSlot Q → ℂ) (p : ℝ × ℝ) :
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

private lemma selfAdjoint_real (A : Matrix (Fin 12) (Fin 12) ℂ) (hA : A.IsHermitian) (U : Fin 12 → ℂ) :
    ((sesqValue A U : ℝ) : ℂ) = matrixSesq A U U := by
  have h1 : sesqValue A U = (matrixSesq A U U).re := rfl
  rw [h1]
  refine Complex.conj_eq_iff_re.mp ?_
  simp only [matrixSesq, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  have := hA.apply i j
  simp only [RCLike.star_def] at this
  rw [this]
  ring

section Sum

variable {k N : ℕ} (c : FracCellData k N) (S : CellScalars)

private lemma ps_zero_left (n n' : ℤ) (p : ℝ × ℝ) (W : (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)) :
    pairSesq c S n n' p 0 W = 0 := by
  have := ps_smul_left c S n n' p 0 0 W
  simpa using this

private lemma ps_zero_right (n n' : ℤ) (p : ℝ × ℝ) (W : (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)) :
    pairSesq c S n n' p W 0 = 0 := by
  have := ps_smul_right c S n n' p 0 0 W
  simpa using this

private lemma ps_sum_left {ι : Type} (s : Finset ι) (n n' : ℤ) (p : ℝ × ℝ) (x : ι → ℂ)
    (U : ι → (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)) (W : (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)) :
    pairSesq c S n n' p (∑ τ ∈ s, x τ • U τ) W = ∑ τ ∈ s, (starRingEnd ℂ) (x τ) * pairSesq c S n n' p (U τ) W := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ps_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ps_add_left, ps_smul_left, ih]

private lemma ps_sum_right {ι : Type} (s : Finset ι) (n n' : ℤ) (p : ℝ × ℝ) (x : ι → ℂ)
    (U : ι → (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)) (W : (Fin 3 → Fin 3 → ℂ) × (Fin 3 → ℂ)) :
    pairSesq c S n n' p W (∑ τ ∈ s, x τ • U τ) = ∑ τ ∈ s, x τ * pairSesq c S n n' p W (U τ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ps_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ps_add_right, ps_smul_right, ih]

end Sum

theorem pairForm_holds_of (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ} (c : FracCellData k N)
    (K : CellBox) (B : CellBases) (S : CellScalars) {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q)
    (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (u : D → ℂ) (h : EnergySetting α c K B S I v G H u)
    (hint : ∀ (n n' : modes) (τ τ' : LowSlot Q), IntegrableOn (fun p =>
        ((K.lineWeight p.1 * CellScalars.rHat K p : ℝ) : ℂ) *
          pairSesq c S n n' p (slotValue B τ p) (slotValue B τ' p)) K.rect)
    (hstrain : ∀ (n : modes) (a b : Fin 3), ∀ p ∈ K.rect, K.lowStrain c.order n Q G a b p =
        ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), B.coef K (gradMode c.order n G a b) j l * ((basisFn B j l p : ℝ) : ℂ))
    (hvel : ∀ (n : modes) (a : Fin 3), ∀ p ∈ K.rect, K.lowVelocity c.order n Q v a p =
        ∑ j : Fin Q, ∑ l : Fin Q,
          B.coef K (fun p => modeVec c.order n v p.1 p.2 a) j l * ((basisFn B j l p : ℝ) : ℂ)) :
    quadFormValue (pairForm c K B S I) u = CellScalars.localPairForm c K S v G := by
  obtain ⟨hm, hQ, -, -, -, hsc, -, hrep⟩ := h
  subst hm hQ
  have hX : ∀ (n : S.resolved), ∀ p ∈ K.rect, ∑ τ, u (slotIndex I n τ) • slotValue B τ p =
      (K.lowStrainAt c.order n S.degHigh G p, K.lowVelocityAt c.order n S.degHigh v p) := by
    intro n p hp
    rw [slot_sum]
    refine Prod.ext ?_ ?_
    · funext a b
      simp only [slotIndex, hrep.strain, CellBox.lowStrainAt]
      rw [hstrain n a b p hp]
    · funext a
      simp only [slotIndex, hrep.velocity, CellBox.lowVelocityAt]
      rw [hvel n a p hp]
  have hrect : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have key : ∀ n n' : S.resolved,
      (∑ τ, ∑ τ', (starRingEnd ℂ) (u (slotIndex I n τ)) *
        (∫ p in K.rect, ((K.lineWeight p.1 * CellScalars.rHat K p : ℝ) : ℂ) *
          pairSesq c S n n' p (slotValue B τ p) (slotValue B τ' p)) * u (slotIndex I n' τ')) =
      ∫ p in K.rect, ((K.lineWeight p.1 * CellScalars.rHat K p : ℝ) : ℂ) *
        CellScalars.pairIntegrand c K S v G n n' p := by
    intro n n'
    rw [setIntegral_congr_fun hrect (g := fun p => ∑ τ, ∑ τ', ((starRingEnd ℂ) (u (slotIndex I n τ)) *
        u (slotIndex I n' τ')) * (((K.lineWeight p.1 * CellScalars.rHat K p : ℝ) : ℂ) *
          pairSesq c S n n' p (slotValue B τ p) (slotValue B τ' p)))]
    · rw [integral_finsetSum]
      · refine Finset.sum_congr rfl (fun τ _ => ?_)
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl (fun τ' _ => ?_)
          rw [integral_const_mul]
          ring
        · intro τ' _
          exact (hint n n' τ τ').const_mul _
      · intro τ _
        exact integrable_finsetSum _ (fun τ' _ => (hint n n' τ τ').const_mul _)
    · intro p hp
      simp only
      have hpi : CellScalars.pairIntegrand c K S v G n n' p =
          pairSesq c S n n' p (K.lowStrainAt c.order n S.degHigh G p, K.lowVelocityAt c.order n S.degHigh v p)
            (K.lowStrainAt c.order n' S.degHigh G p, K.lowVelocityAt c.order n' S.degHigh v p) := by
        unfold CellScalars.pairIntegrand pairSesq
        split_ifs with hnn
        · rw [selfAdjoint_real _ (hsc.localMatrix_selfAdjoint _ _)]
          have hnn' : n = n' := Subtype.ext hnn
          subst hnn'
          rfl
        · rfl
      rw [hpi, ← hX n p hp, ← hX n' p hp, ps_sum_left]
      simp_rw [ps_sum_right]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun τ' _ => ?_)
      ring
  unfold pairForm CellScalars.localPairForm
  refine (quad_slot I _ u).trans ?_
  congr 1
  rw [← Finset.sum_coe_sort S.resolved]
  simp_rw [← Finset.sum_coe_sort S.resolved, ← key]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]

def PairIntegrableStatement : Prop :=
  ∀ (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ} (c : FracCellData k N) (K : CellBox) (B : CellBases)
    (S : CellScalars) {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q)
    (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (u : D → ℂ), EnergySetting α c K B S I v G H u →
      ∀ (n n' : modes) (τ τ' : LowSlot Q), IntegrableOn (fun p =>
        ((K.lineWeight p.1 * CellScalars.rHat K p : ℝ) : ℂ) *
          pairSesq c S n n' p (slotValue B τ p) (slotValue B τ' p)) K.rect

def LowStrainExpansionStatement : Prop :=
  ∀ (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ} (c : FracCellData k N) (K : CellBox) (B : CellBases)
    (S : CellScalars) {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q)
    (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (u : D → ℂ), EnergySetting α c K B S I v G H u →
      ∀ (n : modes) (a b : Fin 3), ∀ p ∈ K.rect, K.lowStrain c.order n Q G a b p =
        ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), B.coef K (gradMode c.order n G a b) j l * ((basisFn B j l p : ℝ) : ℂ)

def LowVelocityExpansionStatement : Prop :=
  ∀ (α : ℝ) {D : Type} [Fintype D] [DecidableEq D] {k N : ℕ} (c : FracCellData k N) (K : CellBox) (B : CellBases)
    (S : CellScalars) {modes : Finset ℤ} {Q q : ℕ} (I : LowIndex D modes Q q)
    (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (u : D → ℂ), EnergySetting α c K B S I v G H u →
      ∀ (n : modes) (a : Fin 3), ∀ p ∈ K.rect, K.lowVelocity c.order n Q v a p =
        ∑ j : Fin Q, ∑ l : Fin Q,
          B.coef K (fun p => modeVec c.order n v p.1 p.2 a) j l * ((basisFn B j l p : ℝ) : ℂ)

theorem pairForm_holds_of_parts (h1 : PairIntegrableStatement) (h2 : LowStrainExpansionStatement)
    (h3 : LowVelocityExpansionStatement) : PairFormStatement := by
  intro α D _ _ k N c K B S modes Q q I v G H u h
  exact pairForm_holds_of α c K B S I v G H u h (h1 α c K B S I v G H u h) (h2 α c K B S I v G H u h)
    (h3 α c K B S I v G H u h)

end Breakdown.CellCert.CellEnergy
