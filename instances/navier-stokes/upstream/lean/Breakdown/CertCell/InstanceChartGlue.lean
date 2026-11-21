import Breakdown.CertCell.InstanceStatements

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace Instance

open CellCert.GivenFields

private def polyAt (P : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) : ℂ :=
  MvPolynomial.eval ![(q.1 : ℂ), (q.2 : ℂ)] P

private def polyDiff (P : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (polyAt (MvPolynomial.pderiv 0 P) q) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (polyAt (MvPolynomial.pderiv 1 P) q)

private theorem polyDiff_apply (P : MvPolynomial (Fin 2) ℂ) (q v : ℝ × ℝ) :
    polyDiff P q v = (v.1 : ℂ) * polyAt (MvPolynomial.pderiv 0 P) q +
      (v.2 : ℂ) * polyAt (MvPolynomial.pderiv 1 P) q := by
  simp [polyDiff, Complex.real_smul]

private theorem polyAt_neg (P : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) : polyAt (-P) q = -polyAt P q := by
  simp [polyAt]

private theorem polyAt_hasFDerivAt (P : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) :
    HasFDerivAt (polyAt P) (polyDiff P q) q := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have e : polyAt (MvPolynomial.C a) = fun _ => a := funext fun z => by simp [polyAt]
    rw [e]
    exact (hasFDerivAt_const a q).congr_fderiv (ContinuousLinearMap.ext fun v => by simp [polyDiff_apply, polyAt])
  | add p r hp hr =>
    have e : polyAt (p + r) = fun z => polyAt p z + polyAt r z := funext fun z => by simp [polyAt]
    rw [e]
    refine (hp.add hr).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp only [add_apply, polyDiff_apply, map_add, polyAt]
    ring
  | mul_X p i hp =>
    have hi : HasFDerivAt (fun z : ℝ × ℝ => ![(z.1 : ℂ), (z.2 : ℂ)] i) (polyDiff (MvPolynomial.X i) q) q := by
      fin_cases i
      · exact (Complex.ofRealCLM.hasFDerivAt.comp q hasFDerivAt_fst).congr_fderiv
          (ContinuousLinearMap.ext fun v => by simp [polyDiff_apply, polyAt, MvPolynomial.pderiv_X])
      · exact (Complex.ofRealCLM.hasFDerivAt.comp q hasFDerivAt_snd).congr_fderiv
          (ContinuousLinearMap.ext fun v => by simp [polyDiff_apply, polyAt, MvPolynomial.pderiv_X])
    have e : polyAt (p * MvPolynomial.X i) = fun z => polyAt p z * ![(z.1 : ℂ), (z.2 : ℂ)] i :=
      funext fun z => by simp [polyAt]
    rw [e]
    refine (hp.mul hi).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    fin_cases i <;> simp [polyDiff_apply, polyAt, Derivation.leibniz, MvPolynomial.pderiv_X] <;> ring

private theorem polyAt_continuous (P : MvPolynomial (Fin 2) ℂ) : Continuous (polyAt P) :=
  continuous_iff_continuousAt.2 fun q => (polyAt_hasFDerivAt P q).continuousAt

private theorem polyDiff_continuous (P : MvPolynomial (Fin 2) ℂ) : Continuous (polyDiff P) := by
  have h0 := polyAt_continuous (MvPolynomial.pderiv 0 P)
  have h1 := polyAt_continuous (MvPolynomial.pderiv 1 P)
  exact ((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℂ (ContinuousLinearMap.fst ℝ ℝ ℝ)).continuous.comp h0).add
    ((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℂ (ContinuousLinearMap.snd ℝ ℝ ℝ)).continuous.comp h1)

private theorem deriv_along_t {P Q : MvPolynomial (Fin 2) ℂ} {x0 : ℝ}
    (h : ∀ t, polyAt P (t, x0) = polyAt Q (t, x0)) (t : ℝ) :
    polyAt (MvPolynomial.pderiv 0 P) (t, x0) = polyAt (MvPolynomial.pderiv 0 Q) (t, x0) := by
  have hl : HasDerivAt (fun s : ℝ => (s, x0)) ((1 : ℝ), (0 : ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x0)
  have hP := (polyAt_hasFDerivAt P (t, x0)).comp_hasDerivAt t hl
  have hQ := (polyAt_hasFDerivAt Q (t, x0)).comp_hasDerivAt t hl
  rw [show (polyAt P ∘ fun s : ℝ => (s, x0)) = polyAt Q ∘ fun s : ℝ => (s, x0) from funext fun s => h s] at hP
  simpa [polyDiff_apply] using hP.unique hQ

private theorem deriv_along_x {P Q : MvPolynomial (Fin 2) ℂ} {t0 : ℝ}
    (h : ∀ x, polyAt P (t0, x) = polyAt Q (t0, x)) (x : ℝ) :
    polyAt (MvPolynomial.pderiv 1 P) (t0, x) = polyAt (MvPolynomial.pderiv 1 Q) (t0, x) := by
  have hl : HasDerivAt (fun s : ℝ => (t0, s)) ((0 : ℝ), (1 : ℝ)) x :=
    (hasDerivAt_const x t0).prodMk (hasDerivAt_id x)
  have hP := (polyAt_hasFDerivAt P (t0, x)).comp_hasDerivAt x hl
  have hQ := (polyAt_hasFDerivAt Q (t0, x)).comp_hasDerivAt x hl
  rw [show (polyAt P ∘ fun s : ℝ => (t0, s)) = polyAt Q ∘ fun s : ℝ => (t0, s) from funext fun s => h s] at hP
  simpa [polyDiff_apply] using hP.unique hQ

private theorem pderiv_comm (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 P) = MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp [hp, hr]
  | mul_X p i hp => fin_cases i <;> simp [Derivation.leibniz, MvPolynomial.pderiv_X, hp] <;> ring

private theorem polyAt_bind (g : Fin 2 → MvPolynomial (Fin 2) ℂ) (Q : MvPolynomial (Fin 2) ℂ)
    (v : Fin 2 → ℂ) :
    MvPolynomial.eval v (MvPolynomial.bind₁ g Q) = MvPolynomial.eval (fun i => MvPolynomial.eval v (g i)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp [hp, hr]
  | mul_X p i hp => simp [hp]

private theorem polyAt_atFirst (c : ℝ) (Q : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) :
    polyAt (atFirst (c : ℂ) Q) q = polyAt Q (c, q.2) := by
  unfold polyAt atFirst
  rw [polyAt_bind]
  refine congrArg (fun v => MvPolynomial.eval v Q) (funext fun i => ?_)
  fin_cases i <;> simp

private theorem polyAt_atSecond (c : ℝ) (Q : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) :
    polyAt (atSecond (c : ℂ) Q) q = polyAt Q (q.1, c) := by
  unfold polyAt atSecond
  rw [polyAt_bind]
  refine congrArg (fun v => MvPolynomial.eval v Q) (funext fun i => ?_)
  fin_cases i <;> simp

private theorem value_of_atFirst {Q R : MvPolynomial (Fin 2) ℂ} {c : ℝ}
    (h : atFirst (c : ℂ) Q = atFirst (c : ℂ) R) (x : ℝ) : polyAt Q (c, x) = polyAt R (c, x) := by
  have := congrArg (fun W => polyAt W (0, x)) h
  simpa [polyAt_atFirst] using this

private theorem value_of_atSecond {Q R : MvPolynomial (Fin 2) ℂ} {c : ℝ}
    (h : atSecond (c : ℂ) Q = atSecond (c : ℂ) R) (t : ℝ) : polyAt Q (t, c) = polyAt R (t, c) := by
  have := congrArg (fun W => polyAt W (t, 0)) h
  simpa [polyAt_atSecond] using this

private def slot (l : List ℝ) (u : ℝ) : ℕ := (l.filter (fun b => decide (b ≤ u))).length

private theorem slot_le (l : List ℝ) (u : ℝ) : slot l u ≤ l.length := List.length_filter_le _ _

private theorem slot_cons (b : ℝ) (bs : List ℝ) (h : (b :: bs).Pairwise (· < ·)) (u : ℝ) :
    slot (b :: bs) u = if b ≤ u then slot bs u + 1 else 0 := by
  unfold slot
  split_ifs with hb
  · rw [List.filter_cons_of_pos (by simpa using hb), List.length_cons]
  · rw [List.filter_cons_of_neg (by simpa using hb), List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    have := List.rel_of_pairwise_cons h hc
    simp only [decide_eq_true_eq, not_le]
    linarith [not_le.1 hb]

private theorem slot_of_below (l : List ℝ) {u : ℝ} (h : ∀ b ∈ l, u < b) : slot l u = 0 := by
  unfold slot
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro b hb
  simpa using h b hb

private theorem glue_pair {A B : ℝ × ℝ → ℂ} {A' B' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℂ)} (π : ℝ × ℝ → ℝ)
    (hπ : Continuous π) (c : ℝ) (hA : ∀ p, HasFDerivAt A (A' p) p) (hB : ∀ p, HasFDerivAt B (B' p) p)
    (hA' : Continuous A') (hB' : Continuous B')
    (hv : ∀ p, π p = c → A p = B p) (hd : ∀ p, π p = c → A' p = B' p) :
    (∀ p, HasFDerivAt (fun q => if c ≤ π q then B q else A q) (if c ≤ π p then B' p else A' p) p) ∧
      Continuous (fun p => if c ≤ π p then B' p else A' p) := by
  refine ⟨fun p => ?_, Continuous.if_le hB' hA' continuous_const hπ fun p hp => (hd p hp.symm).symm⟩
  rcases lt_trichotomy (π p) c with h | h | h
  · rw [if_neg (not_le.2 h)]
    refine (hA p).congr_of_eventuallyEq ?_
    filter_upwards [(hπ.tendsto p).eventually (eventually_lt_nhds h)] with q hq
    rw [if_neg (not_le.2 hq)]
  · rw [if_pos h.ge]
    have hz : HasFDerivAt (fun q => A q - B q) (0 : ℝ × ℝ →L[ℝ] ℂ) p := by
      have hs := (hA p).sub (hB p)
      rw [hd p h, sub_self] at hs
      exact hs
    have hk : HasFDerivAt (fun q => if c ≤ π q then (0 : ℂ) else A q - B q) (0 : ℝ × ℝ →L[ℝ] ℂ) p := by
      rw [hasFDerivAt_iff_isLittleO] at hz ⊢
      refine Asymptotics.IsBigO.trans_isLittleO (Asymptotics.IsBigO.of_bound 1
        (Filter.Eventually.of_forall fun q => ?_)) hz
      simp only [if_pos h.ge, zero_apply, sub_zero, hv p h, sub_self, one_mul]
      split_ifs <;> simp
    refine ((hB p).add hk).congr_fderiv (add_zero _) |>.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun q => ?_)
    simp only [Pi.add_apply]
    split_ifs <;> ring
  · rw [if_pos h.le]
    refine (hB p).congr_of_eventuallyEq ?_
    filter_upwards [(hπ.tendsto p).eventually (eventually_gt_nhds h)] with q hq
    rw [if_pos hq.le]

private theorem glue_chain (π : ℝ × ℝ → ℝ) (hπ : Continuous π) : ∀ (l : List ℝ), l.Pairwise (· < ·) →
    ∀ (F : ℕ → ℝ × ℝ → ℂ) (F' : ℕ → ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℂ)),
    (∀ k p, HasFDerivAt (F k) (F' k p) p) → (∀ k, Continuous (F' k)) →
    (∀ k (hk : k < l.length) p, π p = l[k] → F k p = F (k + 1) p ∧ F' k p = F' (k + 1) p) →
    (∀ p, HasFDerivAt (fun q => F (slot l (π q)) q) (F' (slot l (π p)) p) p) ∧
      Continuous (fun p => F' (slot l (π p)) p)
  | [], _, F, F', hF, hF', _ => by
    simp only [slot, List.filter_nil, List.length_nil]
    exact ⟨hF 0, hF' 0⟩
  | b :: bs, hl, F, F', hF, hF', hj => by
    obtain ⟨ih1, ih2⟩ := glue_chain π hπ bs hl.of_cons (fun k => F (k + 1)) (fun k => F' (k + 1))
      (fun k p => hF (k + 1) p) (fun k => hF' (k + 1))
      (fun k hk p hp => hj (k + 1) (by simp; omega) p (by simpa using hp))
    have hz : ∀ p, π p = b → slot bs (π p) = 0 := fun p hp =>
      slot_of_below bs fun c hc => hp ▸ List.rel_of_pairwise_cons hl hc
    have hg := glue_pair (A := F 0) (B := fun q => F (slot bs (π q) + 1) q) (A' := F' 0)
      (B' := fun q => F' (slot bs (π q) + 1) q) π hπ b (hF 0) ih1 (hF' 0) ih2
      (fun p hp => by simpa [hz p hp] using (hj 0 (by simp) p (by simpa using hp)).1)
      (fun p hp => by simpa [hz p hp] using (hj 0 (by simp) p (by simpa using hp)).2)
    have e1 : (fun q => F (slot (b :: bs) (π q)) q) =
        fun q => if b ≤ π q then F (slot bs (π q) + 1) q else F 0 q := by
      funext q
      rw [slot_cons b bs hl]
      split_ifs <;> rfl
    have e2 : (fun p => F' (slot (b :: bs) (π p)) p) =
        fun p => if b ≤ π p then F' (slot bs (π p) + 1) p else F' 0 p := by
      funext q
      rw [slot_cons b bs hl]
      split_ifs <;> rfl
    refine ⟨fun p => ?_, e2 ▸ hg.2⟩
    rw [e1, congrFun e2 p]
    exact hg.1 p

private structure HalfJoined (lt lx : List ℝ) (P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) : Prop where
  ht : ∀ k (hk : k < lt.length), ∀ j ≤ lx.length, ∀ x,
    polyAt (P k j) (lt[k], x) = polyAt (P (k + 1) j) (lt[k], x) ∧
    polyAt (MvPolynomial.pderiv 0 (P k j)) (lt[k], x) = polyAt (MvPolynomial.pderiv 0 (P (k + 1) j)) (lt[k], x)
  hx : ∀ k (hk : k < lx.length), ∀ i ≤ lt.length, ∀ t,
    polyAt (P i k) (t, lx[k]) = polyAt (P i (k + 1)) (t, lx[k]) ∧
    polyAt (MvPolynomial.pderiv 1 (P i k)) (t, lx[k]) = polyAt (MvPolynomial.pderiv 1 (P i (k + 1))) (t, lx[k])

private def halfF (lt lx : List ℝ) (P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) : ℂ :=
  polyAt (P (slot lt q.1) (slot lx q.2)) q

private def halfD (lt lx : List ℝ) (P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℂ :=
  polyDiff (P (slot lt q.1) (slot lx q.2)) q

private theorem half_glue (lt lx : List ℝ) (hlt : lt.Pairwise (· < ·)) (hlx : lx.Pairwise (· < ·))
    (P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (hP : HalfJoined lt lx P) :
    (∀ p, HasFDerivAt (halfF lt lx P) (halfD lt lx P p) p) ∧ Continuous (halfD lt lx P) := by
  have hrow : ∀ j ≤ lx.length,
      (∀ p, HasFDerivAt (fun q => polyAt (P (slot lt q.1) j) q) (polyDiff (P (slot lt p.1) j) p) p) ∧
        Continuous (fun p => polyDiff (P (slot lt p.1) j) p) := by
    intro j hj
    have h := glue_chain Prod.fst continuous_fst lt hlt (fun k => polyAt (P (min k lt.length) j))
      (fun k => polyDiff (P (min k lt.length) j)) (fun k p => polyAt_hasFDerivAt _ p)
      (fun k => polyDiff_continuous _) (fun k hk p hp => by
        obtain ⟨t, x⟩ := p
        simp only at hp
        subst hp
        rw [Nat.min_eq_left hk.le, Nat.min_eq_left hk]
        obtain ⟨h1, h2⟩ := hP.ht k hk j hj x
        refine ⟨h1, ContinuousLinearMap.ext fun v => ?_⟩
        rw [polyDiff_apply, polyDiff_apply, h2, deriv_along_x (fun x' => (hP.ht k hk j hj x').1) x])
    simpa only [Nat.min_eq_left (slot_le lt _)] using h
  have h := glue_chain Prod.snd continuous_snd lx hlx
    (fun j q => polyAt (P (slot lt q.1) (min j lx.length)) q)
    (fun j q => polyDiff (P (slot lt q.1) (min j lx.length)) q)
    (fun j p => (hrow _ (min_le_right _ _)).1 p) (fun j => (hrow _ (min_le_right _ _)).2) (fun k hk p hp => by
      obtain ⟨t, x⟩ := p
      simp only at hp
      subst hp
      simp only
      rw [Nat.min_eq_left hk.le, Nat.min_eq_left hk]
      obtain ⟨h1, h2⟩ := hP.hx k hk _ (slot_le lt t) t
      refine ⟨h1, ContinuousLinearMap.ext fun v => ?_⟩
      rw [polyDiff_apply, polyDiff_apply, h2, deriv_along_t (fun t' => (hP.hx k hk _ (slot_le lt t) t').1) t])
  simp only [Nat.min_eq_left (slot_le lx _)] at h
  exact h

private structure BothJoined (lt lu lw : List ℝ) (P Q : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) : Prop where
  up : HalfJoined lt lu P
  low : HalfJoined lt lw Q
  plane : ∀ i ≤ lt.length, ∀ t, polyAt (P i 0) (t, 0) = polyAt (Q i 0) (t, 0) ∧
    polyAt (MvPolynomial.pderiv 1 (P i 0)) (t, 0) = -polyAt (MvPolynomial.pderiv 1 (Q i 0)) (t, 0)

private def flipSecond : ℝ × ℝ →L[ℝ] ℝ × ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (-ContinuousLinearMap.snd ℝ ℝ ℝ)

private theorem flipSecond_apply (q : ℝ × ℝ) : flipSecond q = (q.1, -q.2) := by simp [flipSecond]

private def bothF (lt lu lw : List ℝ) (P Q : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) : ℂ :=
  if 0 ≤ q.2 then halfF lt lu P q else halfF lt lw Q (flipSecond q)

private def bothD (lt lu lw : List ℝ) (P Q : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℂ :=
  if 0 ≤ q.2 then halfD lt lu P q else (halfD lt lw Q (flipSecond q)).comp flipSecond

private structure Grid (lt lu lw : List ℝ) : Prop where
  st : lt.Pairwise (· < ·)
  su : lu.Pairwise (· < ·)
  sw : lw.Pairwise (· < ·)
  pu : ∀ b ∈ lu, 0 < b
  pw : ∀ b ∈ lw, 0 < b

private theorem both_glue {lt lu lw : List ℝ} (hg : Grid lt lu lw) {P Q : ℕ → ℕ → MvPolynomial (Fin 2) ℂ}
    (h : BothJoined lt lu lw P Q) :
    (∀ p, HasFDerivAt (bothF lt lu lw P Q) (bothD lt lu lw P Q p) p) ∧ Continuous (bothD lt lu lw P Q) := by
  obtain ⟨hU, hU'⟩ := half_glue lt lu hg.st hg.su P h.up
  obtain ⟨hL, hL'⟩ := half_glue lt lw hg.st hg.sw Q h.low
  have hu0 : slot lu 0 = 0 := slot_of_below lu hg.pu
  have hw0 : slot lw 0 = 0 := slot_of_below lw hg.pw
  have g := glue_pair (A := fun q => halfF lt lw Q (flipSecond q)) (B := halfF lt lu P)
    (A' := fun p => (halfD lt lw Q (flipSecond p)).comp flipSecond) (B' := halfD lt lu P)
    Prod.snd continuous_snd 0 (fun p => (hL (flipSecond p)).comp p flipSecond.hasFDerivAt) hU
    ((hL'.comp flipSecond.continuous).clm_comp continuous_const) hU'
    (fun p hp => by
      obtain ⟨t, x⟩ := p
      simp only at hp
      subst hp
      simp only [halfF, flipSecond_apply, neg_zero, hu0, hw0]
      exact (h.plane _ (slot_le lt t) t).1.symm)
    (fun p hp => by
      obtain ⟨t, x⟩ := p
      simp only at hp
      subst hp
      refine ContinuousLinearMap.ext fun v => ?_
      have hi := slot_le lt t
      have h0 := deriv_along_t (fun t' => (h.plane _ hi t').1) t
      simp only [halfD, flipSecond_apply, neg_zero, hu0, hw0, ContinuousLinearMap.comp_apply, polyDiff_apply,
        (h.plane _ hi t).2, h0]
      push_cast
      ring)
  exact ⟨fun p => g.1 p, g.2⟩

private theorem bothD_t (lt lu lw : List ℝ) (P Q : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (p : ℝ × ℝ) :
    bothD lt lu lw P Q p ((1 : ℝ), (0 : ℝ)) =
      bothF lt lu lw (fun i j => MvPolynomial.pderiv 0 (P i j)) (fun i j => MvPolynomial.pderiv 0 (Q i j)) p := by
  unfold bothD bothF halfD halfF
  split_ifs <;> simp [polyDiff_apply, flipSecond_apply]

private theorem bothD_x (lt lu lw : List ℝ) (P Q : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (p : ℝ × ℝ) :
    bothD lt lu lw P Q p ((0 : ℝ), (1 : ℝ)) =
      bothF lt lu lw (fun i j => MvPolynomial.pderiv 1 (P i j)) (fun i j => -MvPolynomial.pderiv 1 (Q i j)) p := by
  unfold bothD bothF halfD halfF
  split_ifs <;> simp [polyDiff_apply, flipSecond_apply, polyAt_neg]

private theorem both_contDiff_two {lt lu lw : List ℝ} (hg : Grid lt lu lw) {P Q : ℕ → ℕ → MvPolynomial (Fin 2) ℂ}
    (h0 : BothJoined lt lu lw P Q)
    (ht : BothJoined lt lu lw (fun i j => MvPolynomial.pderiv 0 (P i j)) (fun i j => MvPolynomial.pderiv 0 (Q i j)))
    (hx : BothJoined lt lu lw (fun i j => MvPolynomial.pderiv 1 (P i j)) (fun i j => -MvPolynomial.pderiv 1 (Q i j))) :
    ContDiff ℝ 2 (bothF lt lu lw P Q) := by
  obtain ⟨d0, -⟩ := both_glue hg h0
  obtain ⟨dt, ct⟩ := both_glue hg ht
  obtain ⟨dx, cx⟩ := both_glue hg hx
  have kt : ContDiff ℝ 1 (bothF lt lu lw (fun i j => MvPolynomial.pderiv 0 (P i j))
      (fun i j => MvPolynomial.pderiv 0 (Q i j))) := contDiff_one_iff_hasFDerivAt.2 ⟨_, ct, dt⟩
  have kx : ContDiff ℝ 1 (bothF lt lu lw (fun i j => MvPolynomial.pderiv 1 (P i j))
      (fun i j => -MvPolynomial.pderiv 1 (Q i j))) := contDiff_one_iff_hasFDerivAt.2 ⟨_, cx, dx⟩
  have e : bothD lt lu lw P Q = fun p =>
      (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (bothF lt lu lw (fun i j => MvPolynomial.pderiv 0 (P i j))
        (fun i j => MvPolynomial.pderiv 0 (Q i j)) p) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (bothF lt lu lw (fun i j => MvPolynomial.pderiv 1 (P i j))
        (fun i j => -MvPolynomial.pderiv 1 (Q i j)) p) := by
    funext p
    refine ContinuousLinearMap.ext fun v => ?_
    rw [add_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply,
      ← bothD_t, ← bothD_x]
    have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul]
    simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  have hD : ContDiff ℝ 1 (bothD lt lu lw P Q) := by
    rw [e]
    exact (contDiff_const.smulRight kt).add (contDiff_const.smulRight kx)
  exact contDiff_succ_iff_hasFDerivAt (n := 1).2 ⟨_, hD, d0⟩

private theorem polyAt_C_mul (a : ℂ) (W : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) :
    polyAt (MvPolynomial.C a * W) q = a * polyAt W q := by
  simp [polyAt]

private def inner (l : List ℝ) : List ℝ := (l.drop 1).dropLast

private theorem inner_facts (l : List ℝ) (hs : l.Pairwise (· < ·)) (h0 : l.head? = some 0)
    (h1 : l.getLast? = some 1) :
    (inner l).Pairwise (· < ·) ∧ (∀ b ∈ inner l, 0 < b) ∧ (inner l).length + 1 = cellCount l ∧
      ∀ k (hk : k < (inner l).length), (inner l)[k] = l.getD (k + 1) 0 := by
  obtain ⟨r, rfl⟩ : ∃ r, l = 0 :: r := by
    cases l with
    | nil => simp at h0
    | cons a r => exact ⟨r, by simp at h0; rw [h0]⟩
  have hr : r ≠ [] := by
    rintro rfl
    simp at h1
  simp only [inner, List.drop_succ_cons, List.drop_zero]
  refine ⟨hs.of_cons.sublist (List.dropLast_sublist _),
    fun b hb => List.rel_of_pairwise_cons hs (List.mem_of_mem_dropLast hb), ?_, fun k hk => ?_⟩
  · have := List.length_pos_of_ne_nil hr
    simp [cellCount]
    omega
  · have hk' : k < r.length := by simp at hk; omega
    rw [List.getElem_dropLast, List.getD_cons_succ, List.getD_eq_getElem _ _ hk']

private theorem t_join (S : Spline) (hS : SplineJoins 2 S) {k j : ℕ} (hk : k < (inner S.mesh.tBreaks).length)
    (hj : j ≤ (inner S.mesh.xBreaks).length) {o : ℕ} (ho : o ≤ 2) (x : ℝ) :
    polyAt ((MvPolynomial.pderiv 0)^[o] (S.piece k j)) ((inner S.mesh.tBreaks)[k], x) =
      polyAt ((MvPolynomial.pderiv 0)^[o] (S.piece (k + 1) j)) ((inner S.mesh.tBreaks)[k], x) := by
  obtain ⟨-, -, ct, gt⟩ := inner_facts _ hS.mesh.t_sorted hS.mesh.t_first hS.mesh.t_last
  obtain ⟨-, -, cx, -⟩ := inner_facts _ hS.mesh.x_sorted hS.mesh.x_first hS.mesh.x_last
  have h := hS.t_joins (k + 1) (by omega) (by omega) j (by omega) o ho
  rw [Nat.add_sub_cancel] at h
  rw [gt k hk]
  exact value_of_atFirst h x

private theorem x_join (S : Spline) (hS : SplineJoins 2 S) {k i : ℕ} (hk : k < (inner S.mesh.xBreaks).length)
    (hi : i ≤ (inner S.mesh.tBreaks).length) {o : ℕ} (ho : o ≤ 2) (t : ℝ) :
    polyAt ((MvPolynomial.pderiv 1)^[o] (S.piece i k)) (t, (inner S.mesh.xBreaks)[k]) =
      polyAt ((MvPolynomial.pderiv 1)^[o] (S.piece i (k + 1))) (t, (inner S.mesh.xBreaks)[k]) := by
  obtain ⟨-, -, ct, -⟩ := inner_facts _ hS.mesh.t_sorted hS.mesh.t_first hS.mesh.t_last
  obtain ⟨-, -, cx, gx⟩ := inner_facts _ hS.mesh.x_sorted hS.mesh.x_first hS.mesh.x_last
  have h := hS.x_joins (k + 1) (by omega) (by omega) i (by omega) o ho
  rw [Nat.add_sub_cancel] at h
  rw [gx k hk]
  exact value_of_atSecond h t

private theorem joined_zero (S : Spline) (hS : SplineJoins 2 S) :
    HalfJoined (inner S.mesh.tBreaks) (inner S.mesh.xBreaks) S.piece :=
  ⟨fun _ hk _ hj x => ⟨t_join S hS hk hj (o := 0) (by norm_num) x, t_join S hS hk hj (o := 1) (by norm_num) x⟩,
    fun _ hk _ hi t => ⟨x_join S hS hk hi (o := 0) (by norm_num) t, x_join S hS hk hi (o := 1) (by norm_num) t⟩⟩

private theorem joined_t (S : Spline) (hS : SplineJoins 2 S) :
    HalfJoined (inner S.mesh.tBreaks) (inner S.mesh.xBreaks) (fun i j => MvPolynomial.pderiv 0 (S.piece i j)) :=
  ⟨fun _ hk _ hj x => ⟨t_join S hS hk hj (o := 1) (by norm_num) x, t_join S hS hk hj (o := 2) (by norm_num) x⟩,
    fun _ hk _ hi t => ⟨deriv_along_t (fun t' => x_join S hS hk hi (o := 0) (by norm_num) t') t, by
      rw [← pderiv_comm, ← pderiv_comm]
      exact deriv_along_t (fun t' => x_join S hS hk hi (o := 1) (by norm_num) t') t⟩⟩

private theorem joined_x (S : Spline) (hS : SplineJoins 2 S) :
    HalfJoined (inner S.mesh.tBreaks) (inner S.mesh.xBreaks) (fun i j => MvPolynomial.pderiv 1 (S.piece i j)) :=
  ⟨fun _ hk _ hj x => ⟨deriv_along_x (fun x' => t_join S hS hk hj (o := 0) (by norm_num) x') x, by
      rw [pderiv_comm, pderiv_comm]
      exact deriv_along_x (fun x' => t_join S hS hk hj (o := 1) (by norm_num) x') x⟩,
    fun _ hk _ hi t => ⟨x_join S hS hk hi (o := 1) (by norm_num) t, x_join S hS hk hi (o := 2) (by norm_num) t⟩⟩

private theorem joined_neg {lt lx : List ℝ} {P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ} (h : HalfJoined lt lx P) :
    HalfJoined lt lx (fun i j => -P i j) :=
  ⟨fun k hk j hj x => by simp only [map_neg, polyAt_neg, (h.ht k hk j hj x).1, (h.ht k hk j hj x).2, and_self],
    fun k hk i hi t => by simp only [map_neg, polyAt_neg, (h.hx k hk i hi t).1, (h.hx k hk i hi t).2, and_self]⟩

private theorem plane_value (S : ChartScalar) (hS : IsJoinedScalar 2 S) {i : ℕ}
    (hi : i ≤ (inner S.upper.mesh.tBreaks).length) {o : ℕ} (ho : o ≤ 2) (t : ℝ) :
    polyAt ((MvPolynomial.pderiv 1)^[o] (S.upper.piece i 0)) (t, 0) =
      (-1) ^ o * polyAt ((MvPolynomial.pderiv 1)^[o] (S.lower.piece i 0)) (t, 0) := by
  obtain ⟨-, -, ct, -⟩ := inner_facts _ hS.upper.mesh.t_sorted hS.upper.mesh.t_first hS.upper.mesh.t_last
  have h := hS.plane_joins i (by omega) o ho
  unfold xDeriv at h
  have e1 := polyAt_atSecond 0 ((MvPolynomial.pderiv 1)^[o] (S.upper.piece i 0)) (t, 0)
  have e2 := polyAt_atSecond 0 ((MvPolynomial.pderiv 1)^[o] (S.lower.piece i 0)) (t, 0)
  rw [Complex.ofReal_zero] at e1 e2
  have h' := congrArg (fun W => polyAt W (t, 0)) h
  simp only [polyAt_C_mul] at h'
  rw [e1, e2] at h'
  exact h'

theorem chartScalar_halves_contDiffOn (S : ChartScalar) (hS : IsJoinedScalar 2 S) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => if 0 ≤ p.2 then (S.upper.evalHalf p.1 p.2).re
      else (S.lower.evalHalf p.1 (-p.2)).re) (Set.Ioo 0 1 ×ˢ Set.univ) := by
  obtain ⟨st, -, -, -⟩ := inner_facts _ hS.upper.mesh.t_sorted hS.upper.mesh.t_first hS.upper.mesh.t_last
  obtain ⟨su, pu, -, -⟩ := inner_facts _ hS.upper.mesh.x_sorted hS.upper.mesh.x_first hS.upper.mesh.x_last
  obtain ⟨sw, pw, -, -⟩ := inner_facts _ hS.lower.mesh.x_sorted hS.lower.mesh.x_first hS.lower.mesh.x_last
  have hg : Grid (inner S.upper.mesh.tBreaks) (inner S.upper.mesh.xBreaks) (inner S.lower.mesh.xBreaks) :=
    ⟨st, su, sw, pu, pw⟩
  have hL0 := joined_zero S.lower hS.lower
  have hLt := joined_t S.lower hS.lower
  have hLx := joined_x S.lower hS.lower
  rw [← hS.same_t] at hL0 hLt hLx
  have v0 : ∀ i ≤ (inner S.upper.mesh.tBreaks).length, ∀ t,
      polyAt (S.upper.piece i 0) (t, 0) = polyAt (S.lower.piece i 0) (t, 0) := fun i hi t => by
    simpa using plane_value S hS hi (o := 0) (by norm_num) t
  have v1 : ∀ i ≤ (inner S.upper.mesh.tBreaks).length, ∀ t,
      polyAt (MvPolynomial.pderiv 1 (S.upper.piece i 0)) (t, 0) =
        polyAt (-MvPolynomial.pderiv 1 (S.lower.piece i 0)) (t, 0) := fun i hi t => by
    simpa [polyAt_neg] using plane_value S hS hi (o := 1) (by norm_num) t
  have v2 : ∀ i ≤ (inner S.upper.mesh.tBreaks).length, ∀ t,
      polyAt (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (S.upper.piece i 0))) (t, 0) =
        polyAt (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (S.lower.piece i 0))) (t, 0) := fun i hi t => by
    simpa using plane_value S hS hi (o := 2) (by norm_num) t
  have key := both_contDiff_two hg (P := S.upper.piece) (Q := S.lower.piece)
    ⟨joined_zero S.upper hS.upper, hL0, fun i hi t => ⟨v0 i hi t, by simpa [polyAt_neg] using v1 i hi t⟩⟩
    ⟨joined_t S.upper hS.upper, hLt, fun i hi t => ⟨deriv_along_t (v0 i hi) t, by
      rw [← pderiv_comm, ← pderiv_comm]
      simpa [polyAt_neg] using deriv_along_t (v1 i hi) t⟩⟩
    ⟨joined_x S.upper hS.upper, joined_neg hLx, fun i hi t => ⟨v1 i hi t, by
      simpa [polyAt_neg] using v2 i hi t⟩⟩
  have e : (fun p : ℝ × ℝ => if 0 ≤ p.2 then (S.upper.evalHalf p.1 p.2).re
      else (S.lower.evalHalf p.1 (-p.2)).re) = fun p => Complex.reCLM
        (bothF (inner S.upper.mesh.tBreaks) (inner S.upper.mesh.xBreaks) (inner S.lower.mesh.xBreaks)
          S.upper.piece S.lower.piece p) := by
    funext p
    simp only [bothF, halfF, flipSecond_apply, Complex.reCLM_apply]
    split_ifs
    · rfl
    · rw [hS.same_t]
      rfl
  rw [e]
  exact (Complex.reCLM.contDiff.comp key).contDiffOn

end Instance

end CertCell

end Breakdown
