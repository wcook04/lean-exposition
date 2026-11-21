import Breakdown.CertCell.ShapeStatements

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline cellCount atFirst atSecond tDeriv xDeriv)

namespace Internal

namespace JoinedSpline

def belowCount (l : List ℝ) (u : ℝ) : ℕ := (l.filter (fun b => decide (b ≤ u))).length

theorem belowCount_cons (b : ℝ) (bs : List ℝ) (h : (b :: bs).Pairwise (· < ·)) (u : ℝ) :
    belowCount (b :: bs) u = if b ≤ u then belowCount bs u + 1 else 0 := by
  unfold belowCount
  by_cases hb : b ≤ u
  · rw [if_pos hb, List.filter_cons_of_pos (by simpa using hb), List.length_cons]
  · rw [if_neg hb, List.filter_cons_of_neg (by simpa using hb), List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    have := List.rel_of_pairwise_cons h hc
    simp only [decide_eq_true_eq, not_le]
    linarith [not_le.1 hb]

theorem belowCount_le (l : List ℝ) (u : ℝ) : belowCount l u ≤ l.length := List.length_filter_le _ _

theorem belowCount_at (b : ℝ) (bs : List ℝ) (h : (b :: bs).Pairwise (· < ·)) : belowCount bs b = 0 := by
  unfold belowCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro c hc
  have := List.rel_of_pairwise_cons h hc
  simp only [decide_eq_true_eq, not_le]
  exact this

theorem glue_continuous (π : ℝ × ℝ → ℝ) (hπ : Continuous π) : ∀ (l : List ℝ), l.Pairwise (· < ·) →
    ∀ (F : ℕ → ℝ × ℝ → ℂ), (∀ k, Continuous (F k)) →
    (∀ k (hk : k < l.length) p, π p = l[k] → F k p = F (k + 1) p) →
    Continuous (fun q => F (belowCount l (π q)) q)
  | [], _, F, hF, _ => by
    simpa [belowCount] using hF 0
  | b :: bs, hl, F, hF, hj => by
    have ih := glue_continuous π hπ bs hl.of_cons (fun k => F (k + 1)) (fun k => hF (k + 1))
      (fun k hk p hp => hj (k + 1) (by simp; omega) p (by simpa using hp))
    have e : (fun q => F (belowCount (b :: bs) (π q)) q) =
        fun q => if b ≤ π q then F (belowCount bs (π q) + 1) q else F 0 q := by
      funext q
      rw [belowCount_cons b bs hl]
      split_ifs <;> rfl
    rw [e]
    refine Continuous.if_le ih (hF 0) continuous_const hπ (fun p hp => ?_)
    rw [← hp, belowCount_at b bs hl]
    exact (hj 0 (by simp) p (by simpa using hp.symm)).symm

theorem glue_step {A B : ℝ × ℝ → ℂ} {A' B' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℂ)} (π : ℝ × ℝ → ℝ)
    (hπ : Continuous π) (c : ℝ)
    (hA : ∀ p, HasFDerivAt A (A' p) p) (hB : ∀ p, HasFDerivAt B (B' p) p)
    (h0 : ∀ p, c = π p → B p = A p) (h1 : ∀ p, c = π p → B' p = A' p) (p : ℝ × ℝ) :
    HasFDerivAt (fun q => if c ≤ π q then B q else A q) (if c ≤ π p then B' p else A' p) p := by
  rcases lt_trichotomy (π p) c with h | h | h
  · rw [if_neg (not_le.2 h)]
    refine (hA p).congr_of_eventuallyEq ?_
    filter_upwards [(hπ.tendsto p).eventually (eventually_lt_nhds h)] with q hq
    rw [if_neg (not_le.2 hq)]
  · rw [if_pos h.ge]
    have hd : HasFDerivAt (fun q => A q - B q) (0 : ℝ × ℝ →L[ℝ] ℂ) p := by
      have := (hA p).sub (hB p)
      rwa [h1 p h.symm, sub_self] at this
    have hK : HasFDerivAt (fun q => if c ≤ π q then (0 : ℂ) else A q - B q) (0 : ℝ × ℝ →L[ℝ] ℂ) p := by
      rw [hasFDerivAt_iff_isLittleO] at hd ⊢
      refine Asymptotics.IsBigO.trans_isLittleO ?_ hd
      refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun q => ?_)
      have hp0 : A p - B p = 0 := by rw [h0 p h.symm, sub_self]
      simp only [if_pos h.ge, zero_apply, sub_zero, one_mul, hp0]
      split_ifs <;> simp
    have := (hB p).add hK
    rw [add_zero] at this
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
    simp only [Pi.add_apply]
    split_ifs <;> ring
  · rw [if_pos h.le]
    refine (hB p).congr_of_eventuallyEq ?_
    filter_upwards [(hπ.tendsto p).eventually (eventually_gt_nhds h)] with q hq
    rw [if_pos hq.le]

theorem glue_hasFDerivAt (π : ℝ × ℝ → ℝ) (hπ : Continuous π) : ∀ (l : List ℝ), l.Pairwise (· < ·) →
    ∀ (F : ℕ → ℝ × ℝ → ℂ) (F' : ℕ → ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℂ)),
    (∀ k p, HasFDerivAt (F k) (F' k p) p) →
    (∀ k (hk : k < l.length) p, π p = l[k] → F k p = F (k + 1) p ∧ F' k p = F' (k + 1) p) →
    ∀ p, HasFDerivAt (fun q => F (belowCount l (π q)) q) (F' (belowCount l (π p)) p) p
  | [], _, F, F', hF, _ => by
    simpa [belowCount] using hF 0
  | b :: bs, hl, F, F', hF, hj => by
    have ih := glue_hasFDerivAt π hπ bs hl.of_cons (fun k => F (k + 1)) (fun k => F' (k + 1))
      (fun k p => hF (k + 1) p) (fun k hk p hp => hj (k + 1) (by simp; omega) p (by simpa using hp))
    have e1 : (fun q => F (belowCount (b :: bs) (π q)) q) =
        fun q => if b ≤ π q then F (belowCount bs (π q) + 1) q else F 0 q := by
      funext q
      rw [belowCount_cons b bs hl]
      split_ifs <;> rfl
    have e2 : ∀ p, F' (belowCount (b :: bs) (π p)) p =
        if b ≤ π p then F' (belowCount bs (π p) + 1) p else F' 0 p := by
      intro q
      rw [belowCount_cons b bs hl]
      split_ifs <;> rfl
    intro p
    rw [e1, e2]
    refine glue_step (A := F 0) (B := fun q => F (belowCount bs (π q) + 1) q) (A' := F' 0)
      (B' := fun q => F' (belowCount bs (π q) + 1) q) π hπ b (hF 0) ih ?_ ?_ p
    · intro q hq
      show F (belowCount bs (π q) + 1) q = F 0 q
      rw [← hq, belowCount_at b bs hl]
      exact (hj 0 (by simp) q (by simpa using hq.symm)).1.symm
    · intro q hq
      show F' (belowCount bs (π q) + 1) q = F' 0 q
      rw [← hq, belowCount_at b bs hl]
      exact (hj 0 (by simp) q (by simpa using hq.symm)).2.symm

def evP (P : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) : ℂ := MvPolynomial.eval ![(q.1 : ℂ), (q.2 : ℂ)] P

def dP (P : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (evP (MvPolynomial.pderiv 0 P) q) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (evP (MvPolynomial.pderiv 1 P) q)

theorem dP_apply (P : MvPolynomial (Fin 2) ℂ) (q v : ℝ × ℝ) :
    dP P q v = (v.1 : ℂ) * evP (MvPolynomial.pderiv 0 P) q + (v.2 : ℂ) * evP (MvPolynomial.pderiv 1 P) q := by
  simp [dP, Complex.real_smul]

theorem evP_hasFDerivAt (P : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) : HasFDerivAt (evP P) (dP P q) q := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have e : evP (MvPolynomial.C a) = fun _ => a := by funext z; simp [evP]
    rw [e]
    refine (hasFDerivAt_const a q).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    rw [dP_apply]
    simp [evP]
  | add p r hp hr =>
    have e : evP (p + r) = fun z => evP p z + evP r z := by funext z; simp [evP]
    rw [e]
    refine (hp.add hr).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    rw [add_apply, dP_apply, dP_apply, dP_apply]
    simp [evP]
    ring
  | mul_X p i hp =>
    have hc : ∀ j : Fin 2, HasFDerivAt (fun z : ℝ × ℝ => (![(z.1 : ℂ), (z.2 : ℂ)] j))
        (![Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ),
          Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)] j) q := by
      intro j
      fin_cases j
      · exact Complex.ofRealCLM.hasFDerivAt.comp q (hasFDerivAt_fst)
      · exact Complex.ofRealCLM.hasFDerivAt.comp q (hasFDerivAt_snd)
    have e : evP (p * MvPolynomial.X i) = fun z => evP p z * ![(z.1 : ℂ), (z.2 : ℂ)] i := by
      funext z; simp [evP]
    rw [e]
    refine (hp.mul (hc i)).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    rw [dP_apply]
    fin_cases i <;> simp [dP_apply, evP, Derivation.leibniz, MvPolynomial.pderiv_X] <;> ring

theorem evP_continuous (P : MvPolynomial (Fin 2) ℂ) : Continuous (evP P) :=
  continuous_iff_continuousAt.2 fun q => (evP_hasFDerivAt P q).continuousAt

theorem evP_line_t {P Q : MvPolynomial (Fin 2) ℂ} {x0 : ℝ} (h : ∀ t, evP P (t, x0) = evP Q (t, x0))
    (t : ℝ) : evP (MvPolynomial.pderiv 0 P) (t, x0) = evP (MvPolynomial.pderiv 0 Q) (t, x0) := by
  have hl : HasDerivAt (fun s : ℝ => (s, x0)) ((1 : ℝ), (0 : ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x0)
  have h1 := (evP_hasFDerivAt P (t, x0)).comp_hasDerivAt t hl
  have h2 := (evP_hasFDerivAt Q (t, x0)).comp_hasDerivAt t hl
  have e : (evP P ∘ fun s : ℝ => (s, x0)) = (evP Q ∘ fun s : ℝ => (s, x0)) := funext fun s => h s
  rw [e] at h1
  have := h1.unique h2
  simpa [dP_apply] using this

theorem evP_line_x {P Q : MvPolynomial (Fin 2) ℂ} {t0 : ℝ} (h : ∀ x, evP P (t0, x) = evP Q (t0, x))
    (x : ℝ) : evP (MvPolynomial.pderiv 1 P) (t0, x) = evP (MvPolynomial.pderiv 1 Q) (t0, x) := by
  have hl : HasDerivAt (fun s : ℝ => (t0, s)) ((0 : ℝ), (1 : ℝ)) x :=
    (hasDerivAt_const x t0).prodMk (hasDerivAt_id x)
  have h1 := (evP_hasFDerivAt P (t0, x)).comp_hasDerivAt x hl
  have h2 := (evP_hasFDerivAt Q (t0, x)).comp_hasDerivAt x hl
  have e : (evP P ∘ fun s : ℝ => (t0, s)) = (evP Q ∘ fun s : ℝ => (t0, s)) := funext fun s => h s
  rw [e] at h1
  have := h1.unique h2
  simpa [dP_apply] using this

theorem pderiv_swap (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 P) = MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp [hp, hr]
  | mul_X p i hp =>
    fin_cases i <;> simp [Derivation.leibniz, MvPolynomial.pderiv_X, hp] <;> ring

theorem xDeriv_pderiv_first (o : ℕ) (Q : MvPolynomial (Fin 2) ℂ) :
    xDeriv o (MvPolynomial.pderiv 0 Q) = MvPolynomial.pderiv 0 (xDeriv o Q) := by
  induction o with
  | zero => rfl
  | succ o ih =>
    simp only [xDeriv, Function.iterate_succ_apply'] at ih ⊢
    rw [ih, pderiv_swap]

theorem tDeriv_pderiv_second (o : ℕ) (Q : MvPolynomial (Fin 2) ℂ) :
    tDeriv o (MvPolynomial.pderiv 1 Q) = MvPolynomial.pderiv 1 (tDeriv o Q) := by
  induction o with
  | zero => rfl
  | succ o ih =>
    simp only [tDeriv, Function.iterate_succ_apply'] at ih ⊢
    rw [ih, pderiv_swap]

theorem eval_bind_two (v : Fin 2 → ℂ) (g : Fin 2 → MvPolynomial (Fin 2) ℂ) (Q : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval v (MvPolynomial.bind₁ g Q) = MvPolynomial.eval (fun i => MvPolynomial.eval v (g i)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp [hp, hr]
  | mul_X p i hp => simp [hp]

theorem evP_atFirst (c : ℝ) (Q : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) :
    evP (atFirst (c : ℂ) Q) q = evP Q (c, q.2) := by
  unfold evP atFirst
  rw [eval_bind_two]
  refine congrArg (fun v => MvPolynomial.eval v Q) (funext fun i => ?_)
  fin_cases i <;> simp

theorem evP_atSecond (c : ℝ) (Q : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) :
    evP (atSecond (c : ℂ) Q) q = evP Q (q.1, c) := by
  unfold evP atSecond
  rw [eval_bind_two]
  refine congrArg (fun v => MvPolynomial.eval v Q) (funext fun i => ?_)
  fin_cases i <;> simp

theorem join_t {Q R : MvPolynomial (Fin 2) ℂ} {c : ℝ} (h : atFirst (c : ℂ) Q = atFirst (c : ℂ) R) (x : ℝ) :
    evP Q (c, x) = evP R (c, x) := by
  have := congrArg (fun W => evP W (0, x)) h
  simpa [evP_atFirst] using this

theorem join_x {Q R : MvPolynomial (Fin 2) ℂ} {c : ℝ} (h : atSecond (c : ℂ) Q = atSecond (c : ℂ) R) (t : ℝ) :
    evP Q (t, c) = evP R (t, c) := by
  have := congrArg (fun W => evP W (t, 0)) h
  simpa [evP_atSecond] using this

structure Joins (lt lx : List ℝ) (a b : ℕ) (P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) : Prop where
  ht : ∀ k (hk : k < lt.length), ∀ j ≤ lx.length, ∀ o ≤ a, ∀ x,
    evP (tDeriv o (P k j)) (lt[k], x) = evP (tDeriv o (P (k + 1) j)) (lt[k], x)
  hx : ∀ k (hk : k < lx.length), ∀ i ≤ lt.length, ∀ o ≤ b, ∀ t,
    evP (xDeriv o (P i k)) (t, lx[k]) = evP (xDeriv o (P i (k + 1))) (t, lx[k])

theorem Joins.mono {lt lx : List ℝ} {a b a' b' : ℕ} {P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ}
    (J : Joins lt lx a b P) (ha : a' ≤ a) (hb : b' ≤ b) : Joins lt lx a' b' P :=
  ⟨fun k hk j hj o ho x => J.ht k hk j hj o (ho.trans ha) x,
    fun k hk i hi o ho t => J.hx k hk i hi o (ho.trans hb) t⟩

theorem Joins.first {lt lx : List ℝ} {a b : ℕ} {P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ}
    (J : Joins lt lx a b P) (ha : 1 ≤ a) :
    Joins lt lx (a - 1) b (fun i j => MvPolynomial.pderiv 0 (P i j)) := by
  refine ⟨fun k hk j hj o ho x => ?_, fun k hk i hi o ho t => ?_⟩
  · have h := J.ht k hk j hj (o + 1) (by omega) x
    simpa only [tDeriv, Function.iterate_succ_apply] using h
  · rw [xDeriv_pderiv_first, xDeriv_pderiv_first]
    exact evP_line_t (fun t' => J.hx k hk i hi o ho t') t

theorem Joins.second {lt lx : List ℝ} {a b : ℕ} {P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ}
    (J : Joins lt lx a b P) (hb : 1 ≤ b) :
    Joins lt lx a (b - 1) (fun i j => MvPolynomial.pderiv 1 (P i j)) := by
  refine ⟨fun k hk j hj o ho x => ?_, fun k hk i hi o ho t => ?_⟩
  · rw [tDeriv_pderiv_second, tDeriv_pderiv_second]
    exact evP_line_x (fun x' => J.ht k hk j hj o ho x') x
  · have h := J.hx k hk i hi (o + 1) (by omega) t
    simpa only [xDeriv, Function.iterate_succ_apply] using h

def spl (lt lx : List ℝ) (P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) : ℂ :=
  evP (P (belowCount lt q.1) (belowCount lx q.2)) q

theorem spl_continuous {lt lx : List ℝ} (hlt : lt.Pairwise (· < ·)) (hlx : lx.Pairwise (· < ·))
    {a b : ℕ} {P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ} (J : Joins lt lx a b P) : Continuous (spl lt lx P) := by
  have hrow : ∀ j ≤ lx.length, Continuous (fun q : ℝ × ℝ => evP (P (belowCount lt q.1) j) q) := by
    intro j hj
    refine glue_continuous Prod.fst continuous_fst lt hlt (fun k => evP (P k j)) (fun k => evP_continuous _)
      (fun k hk p hp => ?_)
    obtain ⟨t, x⟩ := p
    simp only at hp
    subst hp
    simpa [tDeriv] using J.ht k hk j hj 0 (Nat.zero_le _) x
  have h := glue_continuous Prod.snd continuous_snd lx hlx
    (fun j q => evP (P (belowCount lt q.1) (min j lx.length)) q) (fun j => hrow _ (min_le_right _ _))
    (fun k hk p hp => by
      obtain ⟨t, x⟩ := p
      simp only at hp
      subst hp
      simp only
      rw [Nat.min_eq_left hk.le, Nat.min_eq_left hk]
      simpa [xDeriv] using J.hx k hk _ (belowCount_le lt t) 0 (Nat.zero_le _) t)
  have e : ∀ u, min (belowCount lx u) lx.length = belowCount lx u := fun u => Nat.min_eq_left (belowCount_le lx u)
  simp only [e] at h
  exact h

theorem spl_hasFDerivAt {lt lx : List ℝ} (hlt : lt.Pairwise (· < ·)) (hlx : lx.Pairwise (· < ·))
    {a b : ℕ} {P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ} (J : Joins lt lx a b P) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (p : ℝ × ℝ) : HasFDerivAt (spl lt lx P) (dP (P (belowCount lt p.1) (belowCount lx p.2)) p) p := by
  have hrow : ∀ j ≤ lx.length, ∀ p : ℝ × ℝ, HasFDerivAt (fun q : ℝ × ℝ => evP (P (belowCount lt q.1) j) q)
      (dP (P (belowCount lt p.1) j) p) p := by
    intro j hj
    refine glue_hasFDerivAt Prod.fst continuous_fst lt hlt (fun k => evP (P k j)) (fun k => dP (P k j))
      (fun k p => evP_hasFDerivAt _ p) (fun k hk p hp => ?_)
    obtain ⟨t, x⟩ := p
    simp only at hp
    subst hp
    have h0 : ∀ x', evP (P k j) (lt[k], x') = evP (P (k + 1) j) (lt[k], x') := fun x' => by
      simpa [tDeriv] using J.ht k hk j hj 0 (Nat.zero_le _) x'
    have h1 := J.ht k hk j hj 1 ha x
    simp only [tDeriv, Function.iterate_one] at h1
    refine ⟨h0 x, ContinuousLinearMap.ext fun v => ?_⟩
    rw [dP_apply, dP_apply, h1, evP_line_x h0 x]
  have h := glue_hasFDerivAt Prod.snd continuous_snd lx hlx
    (fun j q => evP (P (belowCount lt q.1) (min j lx.length)) q)
    (fun j q => dP (P (belowCount lt q.1) (min j lx.length)) q)
    (fun j p => hrow _ (min_le_right _ _) p) (fun k hk p hp => by
      obtain ⟨t, x⟩ := p
      simp only at hp
      subst hp
      simp only
      rw [Nat.min_eq_left hk.le, Nat.min_eq_left hk]
      have hi := belowCount_le lt t
      have h0 : ∀ t', evP (P (belowCount lt t) k) (t', lx[k]) = evP (P (belowCount lt t) (k + 1)) (t', lx[k]) :=
        fun t' => by simpa [xDeriv] using J.hx k hk _ hi 0 (Nat.zero_le _) t'
      have h1 := J.hx k hk _ hi 1 hb t
      simp only [xDeriv, Function.iterate_one] at h1
      refine ⟨h0 t, ContinuousLinearMap.ext fun v => ?_⟩
      rw [dP_apply, dP_apply, h1, evP_line_t h0 t]) p
  have e : ∀ u, min (belowCount lx u) lx.length = belowCount lx u := fun u => Nat.min_eq_left (belowCount_le lx u)
  simp only [e] at h
  exact h

theorem spl_contDiff {lt lx : List ℝ} (hlt : lt.Pairwise (· < ·)) (hlx : lx.Pairwise (· < ·)) :
    ∀ (n a b : ℕ) (P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ), n ≤ a → n ≤ b → Joins lt lx a b P →
      ContDiff ℝ n (spl lt lx P)
  | 0, a, b, P, _, _, J => contDiff_zero.2 (spl_continuous hlt hlx J)
  | n + 1, a, b, P, ha, hb, J => by
    have cT := spl_contDiff hlt hlx n (a - 1) b (fun i j => MvPolynomial.pderiv 0 (P i j)) (by omega) (by omega)
      (J.first (by omega))
    have cX := spl_contDiff hlt hlx n a (b - 1) (fun i j => MvPolynomial.pderiv 1 (P i j)) (by omega) (by omega)
      (J.second (by omega))
    rw [Nat.cast_succ]
    refine contDiff_succ_iff_hasFDerivAt.2 ⟨fun p => dP (P (belowCount lt p.1) (belowCount lx p.2)) p, ?_,
      spl_hasFDerivAt hlt hlx J (by omega) (by omega)⟩
    exact (contDiff_const.smulRight cT).add (contDiff_const.smulRight cX)

theorem inner_facts (l : List ℝ) {lo hi : ℝ} (hlh : lo < hi) (hs : l.Pairwise (· < ·))
    (h0 : l.head? = some lo) (h1 : l.getLast? = some hi) :
    ((l.drop 1).dropLast).Pairwise (· < ·) ∧ ((l.drop 1).dropLast).length + 1 = cellCount l ∧
      ∀ k (hk : k < ((l.drop 1).dropLast).length), ((l.drop 1).dropLast)[k] = l.getD (k + 1) 0 := by
  refine ⟨hs.sublist ((List.dropLast_sublist _).trans (List.drop_sublist _ _)), ?_, ?_⟩
  · have : 2 ≤ l.length := by
      match l, h0, h1 with
      | [], h0, _ => simp at h0
      | [a], h0, h1 => simp at h0 h1; linarith
      | a :: b :: r, _, _ => simp
    simp [cellCount]
    omega
  · intro k hk
    simp [List.getD_eq_getElem?_getD, List.getElem_dropLast]
    rw [List.getElem?_eq_getElem]
    · simp
    · simp at hk; omega

theorem joins_of_joined {a b : ℕ} {S : Spline} (hS : IsJoinedSpline a b S) :
    Joins ((S.mesh.tBreaks.drop 1).dropLast) ((S.mesh.xBreaks.drop 1).dropLast) a b S.piece := by
  obtain ⟨-, ct, gt⟩ := inner_facts _ zero_lt_one hS.mesh.t_sorted hS.mesh.t_first hS.mesh.t_last
  obtain ⟨-, cx, gx⟩ := inner_facts _ (by norm_num : (-1 : ℝ) < 1) hS.mesh.x_sorted hS.mesh.x_first
    hS.mesh.x_last
  refine ⟨fun k hk j hj o ho x => ?_, fun k hk i hi o ho t => ?_⟩
  · rw [gt k hk]
    have h := hS.t_joins (k + 1) (by omega) (by omega) j (by omega) o ho
    rw [Nat.add_sub_cancel] at h
    exact join_t h x
  · rw [gx k hk]
    have h := hS.x_joins (k + 1) (by omega) (by omega) i (by omega) o ho
    rw [Nat.add_sub_cancel] at h
    exact join_x h t

end JoinedSpline

end Internal

open Internal.JoinedSpline in
theorem joinedSplineSmooth : JoinedSplineSmooth := by
  intro a b S hS
  have st := (inner_facts _ zero_lt_one hS.mesh.t_sorted hS.mesh.t_first hS.mesh.t_last).1
  have sx := (inner_facts _ (by norm_num : (-1 : ℝ) < 1) hS.mesh.x_sorted hS.mesh.x_first hS.mesh.x_last).1
  have h := spl_contDiff st sx (min a b) a b S.piece (min_le_left _ _) (min_le_right _ _) (joins_of_joined hS)
  have e : (fun z : ℝ × ℝ => S.evalHalf z.1 z.2) =
      spl ((S.mesh.tBreaks.drop 1).dropLast) ((S.mesh.xBreaks.drop 1).dropLast) S.piece := by
    funext z
    rfl
  rw [e]
  exact_mod_cast h

end GivenShape

end CertCell

end Breakdown
