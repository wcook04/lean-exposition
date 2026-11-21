import Breakdown.FracCell.GivenAuxActuatorSmooth

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

private def glueIdx (l : List ℝ) (u : ℝ) : ℕ := (l.filter (fun b => decide (b ≤ u))).length

private theorem glueIdx_cons (b : ℝ) (bs : List ℝ) (h : (b :: bs).Pairwise (· < ·)) (u : ℝ) :
    glueIdx (b :: bs) u = if b ≤ u then glueIdx bs u + 1 else 0 := by
  unfold glueIdx
  by_cases hb : b ≤ u
  · rw [if_pos hb, List.filter_cons_of_pos (by simpa using hb), List.length_cons]
  · rw [if_neg hb, List.filter_cons_of_neg (by simpa using hb), List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    have := List.rel_of_pairwise_cons h hc
    simp only [decide_eq_true_eq, not_le]
    linarith [not_le.1 hb]

private theorem glueIdx_le (l : List ℝ) (u : ℝ) : glueIdx l u ≤ l.length := List.length_filter_le _ _

private theorem glue_two {A B : ℝ × ℝ → ℂ} {A' B' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℂ)} (π : ℝ × ℝ → ℝ)
    (hπ : Continuous π) (c : ℝ)
    (hA : ∀ p, HasFDerivAt A (A' p) p) (hB : ∀ p, HasFDerivAt B (B' p) p)
    (hA' : Continuous A') (hB' : Continuous B')
    (h0 : ∀ p, c = π p → B p = A p) (h1 : ∀ p, c = π p → B' p = A' p) :
    (∀ p, HasFDerivAt (fun q => if c ≤ π q then B q else A q) (if c ≤ π p then B' p else A' p) p) ∧
      Continuous (fun p => if c ≤ π p then B' p else A' p) := by
  refine ⟨fun p => ?_, Continuous.if_le hB' hA' continuous_const hπ h1⟩
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
      simp only [if_pos h.ge, ContinuousLinearMap.zero_apply, sub_zero, one_mul, hp0]
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

private theorem glue_list (π : ℝ × ℝ → ℝ) (hπ : Continuous π) : ∀ (l : List ℝ), l.Pairwise (· < ·) →
    ∀ (F : ℕ → ℝ × ℝ → ℂ) (F' : ℕ → ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℂ)),
    (∀ k p, HasFDerivAt (F k) (F' k p) p) → (∀ k, Continuous (F' k)) →
    (∀ k (hk : k < l.length) p, π p = l[k] → F k p = F (k + 1) p ∧ F' k p = F' (k + 1) p) →
    (∀ p, HasFDerivAt (fun q => F (glueIdx l (π q)) q) (F' (glueIdx l (π p)) p) p) ∧
      Continuous (fun p => F' (glueIdx l (π p)) p)
  | [], _, F, F', hF, hF', _ => by
    simp only [glueIdx, List.filter_nil, List.length_nil]
    exact ⟨hF 0, hF' 0⟩
  | b :: bs, hl, F, F', hF, hF', hj => by
    have hbs : bs.Pairwise (· < ·) := hl.of_cons
    have ih := glue_list π hπ bs hbs (fun k => F (k + 1)) (fun k => F' (k + 1)) (fun k p => hF (k + 1) p)
      (fun k => hF' (k + 1)) (fun k hk p hp => hj (k + 1) (by simp; omega) p (by simpa using hp))
    have h0 : ∀ u, b ≤ u → u ≤ b → glueIdx bs u = 0 := by
      intro u h1 h2
      unfold glueIdx
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro c hc
      have := List.rel_of_pairwise_cons hl hc
      simp only [decide_eq_true_eq, not_le]
      linarith
    have e1 : (fun q => F (glueIdx (b :: bs) (π q)) q) =
        fun q => if b ≤ π q then F (glueIdx bs (π q) + 1) q else F 0 q := by
      funext q
      rw [glueIdx_cons b bs hl]
      split_ifs <;> rfl
    have e2 : (fun p => F' (glueIdx (b :: bs) (π p)) p) =
        fun p => if b ≤ π p then F' (glueIdx bs (π p) + 1) p else F' 0 p := by
      funext q
      rw [glueIdx_cons b bs hl]
      split_ifs <;> rfl
    have hg := glue_two (A := F 0) (B := fun q => F (glueIdx bs (π q) + 1) q) (A' := F' 0)
      (B' := fun q => F' (glueIdx bs (π q) + 1) q) π hπ b (hF 0) ih.1 (hF' 0) ih.2
      (fun p hp => by
        show F (glueIdx bs (π p) + 1) p = F 0 p
        rw [h0 (π p) hp.le hp.ge]
        exact (hj 0 (by simp) p (by simpa using hp.symm)).1.symm)
      (fun p hp => by
        show F' (glueIdx bs (π p) + 1) p = F' 0 p
        rw [h0 (π p) hp.le hp.ge]
        exact (hj 0 (by simp) p (by simpa using hp.symm)).2.symm)
    refine ⟨fun p => ?_, ?_⟩
    · rw [e1]
      have := hg.1 p
      rwa [← congrFun e2 p] at this
    · rw [e2]
      exact hg.2

private def evP (P : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) : ℂ := MvPolynomial.eval ![(q.1 : ℂ), (q.2 : ℂ)] P

private def dP (P : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (evP (MvPolynomial.pderiv 0 P) q) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (evP (MvPolynomial.pderiv 1 P) q)

private theorem dP_apply (P : MvPolynomial (Fin 2) ℂ) (q v : ℝ × ℝ) :
    dP P q v = (v.1 : ℂ) * evP (MvPolynomial.pderiv 0 P) q + (v.2 : ℂ) * evP (MvPolynomial.pderiv 1 P) q := by
  simp [dP, Complex.real_smul]

private theorem evP_hasFDerivAt (P : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) : HasFDerivAt (evP P) (dP P q) q := by
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
    rw [ContinuousLinearMap.add_apply, dP_apply, dP_apply, dP_apply]
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

private theorem evP_line_t {P Q : MvPolynomial (Fin 2) ℂ} {x0 : ℝ} (h : ∀ t, evP P (t, x0) = evP Q (t, x0))
    (t : ℝ) : evP (MvPolynomial.pderiv 0 P) (t, x0) = evP (MvPolynomial.pderiv 0 Q) (t, x0) := by
  have hl : HasDerivAt (fun s : ℝ => (s, x0)) ((1 : ℝ), (0 : ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x0)
  have h1 := (evP_hasFDerivAt P (t, x0)).comp_hasDerivAt t hl
  have h2 := (evP_hasFDerivAt Q (t, x0)).comp_hasDerivAt t hl
  have e : (evP P ∘ fun s : ℝ => (s, x0)) = (evP Q ∘ fun s : ℝ => (s, x0)) := funext fun s => h s
  rw [e] at h1
  have := h1.unique h2
  simpa [dP_apply] using this

private theorem evP_line_x {P Q : MvPolynomial (Fin 2) ℂ} {t0 : ℝ} (h : ∀ x, evP P (t0, x) = evP Q (t0, x))
    (x : ℝ) : evP (MvPolynomial.pderiv 1 P) (t0, x) = evP (MvPolynomial.pderiv 1 Q) (t0, x) := by
  have hl : HasDerivAt (fun s : ℝ => (t0, s)) ((0 : ℝ), (1 : ℝ)) x :=
    (hasDerivAt_const x t0).prodMk (hasDerivAt_id x)
  have h1 := (evP_hasFDerivAt P (t0, x)).comp_hasDerivAt x hl
  have h2 := (evP_hasFDerivAt Q (t0, x)).comp_hasDerivAt x hl
  have e : (evP P ∘ fun s : ℝ => (t0, s)) = (evP Q ∘ fun s : ℝ => (t0, s)) := funext fun s => h s
  rw [e] at h1
  have := h1.unique h2
  simpa [dP_apply] using this

private theorem pderiv_swap (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 P) = MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp [hp, hr]
  | mul_X p i hp =>
    fin_cases i <;> simp [Derivation.leibniz, MvPolynomial.pderiv_X, hp] <;> ring

private theorem dP_continuous (P : MvPolynomial (Fin 2) ℂ) : Continuous (dP P) := by
  unfold dP
  have h : ∀ Q : MvPolynomial (Fin 2) ℂ, Continuous (evP Q) := fun Q =>
    continuous_iff_continuousAt.2 fun q => (evP_hasFDerivAt Q q).continuousAt
  fun_prop

private structure Glued (lt lx : List ℝ) (odd : Bool) (P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) : Prop where
  ht : ∀ k (hk : k < lt.length), ∀ j ≤ lx.length, ∀ x,
    evP (P k j) (lt[k], x) = evP (P (k + 1) j) (lt[k], x) ∧
    evP (MvPolynomial.pderiv 0 (P k j)) (lt[k], x) = evP (MvPolynomial.pderiv 0 (P (k + 1) j)) (lt[k], x)
  hx : ∀ k (hk : k < lx.length), ∀ i ≤ lt.length, ∀ t,
    evP (P i k) (t, lx[k]) = evP (P i (k + 1)) (t, lx[k]) ∧
    evP (MvPolynomial.pderiv 1 (P i k)) (t, lx[k]) = evP (MvPolynomial.pderiv 1 (P i (k + 1))) (t, lx[k])
  par : ∀ i ≤ lt.length, ∀ t, (odd = true → evP (P i 0) (t, 0) = 0) ∧
    (odd = false → evP (MvPolynomial.pderiv 1 (P i 0)) (t, 0) = 0)

private theorem rows_glue (lt : List ℝ) (hlt : lt.Pairwise (· < ·)) (P : ℕ → MvPolynomial (Fin 2) ℂ)
    (ht : ∀ k (hk : k < lt.length), ∀ x,
      evP (P k) (lt[k], x) = evP (P (k + 1)) (lt[k], x) ∧
      evP (MvPolynomial.pderiv 0 (P k)) (lt[k], x) = evP (MvPolynomial.pderiv 0 (P (k + 1))) (lt[k], x)) :
    (∀ p, HasFDerivAt (fun q => evP (P (glueIdx lt q.1)) q) (dP (P (glueIdx lt p.1)) p) p) ∧
      Continuous (fun p => dP (P (glueIdx lt p.1)) p) := by
  have h := glue_list Prod.fst continuous_fst lt hlt (fun k => evP (P (min k lt.length)))
    (fun k => dP (P (min k lt.length)))
    (fun k p => evP_hasFDerivAt _ p) (fun k => dP_continuous _) (fun k hk p hp => by
      obtain ⟨t, x⟩ := p
      simp only at hp
      subst hp
      rw [Nat.min_eq_left hk.le, Nat.min_eq_left hk]
      obtain ⟨h1, h2⟩ := ht k hk x
      refine ⟨h1, ContinuousLinearMap.ext fun v => ?_⟩
      rw [dP_apply, dP_apply, h2, evP_line_x (fun x' => (ht k hk x').1) x])
  have e : ∀ u, min (glueIdx lt u) lt.length = glueIdx lt u := fun u => Nat.min_eq_left (glueIdx_le lt u)
  simp only [e] at h
  exact h

private theorem half_glue (lt lx : List ℝ) (hlt : lt.Pairwise (· < ·)) (hlx : lx.Pairwise (· < ·)) {odd : Bool}
    (P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (hP : Glued lt lx odd P) :
    (∀ p, HasFDerivAt (fun q => evP (P (glueIdx lt q.1) (glueIdx lx q.2)) q)
      (dP (P (glueIdx lt p.1) (glueIdx lx p.2)) p) p) ∧
      Continuous (fun p => dP (P (glueIdx lt p.1) (glueIdx lx p.2)) p) := by
  have hrow : ∀ j ≤ lx.length,
      (∀ p, HasFDerivAt (fun q => evP (P (glueIdx lt q.1) j) q) (dP (P (glueIdx lt p.1) j) p) p) ∧
        Continuous (fun p => dP (P (glueIdx lt p.1) j) p) :=
    fun j hj => rows_glue lt hlt (fun i => P i j) (fun k hk x => hP.ht k hk j hj x)
  have h := glue_list Prod.snd continuous_snd lx hlx
    (fun j q => evP (P (glueIdx lt q.1) (min j lx.length)) q)
    (fun j q => dP (P (glueIdx lt q.1) (min j lx.length)) q)
    (fun j p => (hrow _ (min_le_right _ _)).1 p) (fun j => (hrow _ (min_le_right _ _)).2) (fun k hk p hp => by
      obtain ⟨t, x⟩ := p
      simp only at hp
      subst hp
      simp only
      rw [Nat.min_eq_left hk.le, Nat.min_eq_left hk]
      obtain ⟨h1, h2⟩ := hP.hx k hk _ (glueIdx_le lt t) t
      refine ⟨h1, ContinuousLinearMap.ext fun v => ?_⟩
      rw [dP_apply, dP_apply, h2, evP_line_t (fun t' => (hP.hx k hk _ (glueIdx_le lt t) t').1) t])
  have e : ∀ u, min (glueIdx lx u) lx.length = glueIdx lx u := fun u => Nat.min_eq_left (glueIdx_le lx u)
  simp only [e] at h
  exact h

private def fullF (lt lx : List ℝ) (odd : Bool) (P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) : ℂ :=
  (if odd && decide (q.2 < 0) then -1 else 1) * evP (P (glueIdx lt q.1) (glueIdx lx |q.2|)) (q.1, |q.2|)

private def reflX : ℝ × ℝ →L[ℝ] ℝ × ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (-ContinuousLinearMap.snd ℝ ℝ ℝ)

private theorem reflX_apply (q : ℝ × ℝ) : reflX q = (q.1, -q.2) := by simp [reflX]

private def fullD (lt lx : List ℝ) (odd : Bool) (P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) :
    ℝ × ℝ →L[ℝ] ℂ :=
  if 0 ≤ q.2 then dP (P (glueIdx lt q.1) (glueIdx lx q.2)) q
  else (if odd then (-1 : ℂ) else 1) • (dP (P (glueIdx lt q.1) (glueIdx lx (-q.2))) (q.1, -q.2)).comp reflX

private theorem glueIdx_zero (lx : List ℝ) (hpos : ∀ b ∈ lx, 0 < b) : glueIdx lx 0 = 0 := by
  unfold glueIdx
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro b hb
  simpa using hpos b hb

private theorem full_glue (lt lx : List ℝ) (hlt : lt.Pairwise (· < ·)) (hlx : lx.Pairwise (· < ·))
    (hpos : ∀ b ∈ lx, 0 < b) {odd : Bool}
    (P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (hP : Glued lt lx odd P) :
    (∀ p, HasFDerivAt (fullF lt lx odd P) (fullD lt lx odd P p) p) ∧ Continuous (fullD lt lx odd P) := by
  obtain ⟨hH, hH'⟩ := half_glue lt lx hlt hlx P hP
  set H : ℝ × ℝ → ℂ := fun q => evP (P (glueIdx lt q.1) (glueIdx lx q.2)) q with hHdef
  set H' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℂ) := fun q => dP (P (glueIdx lt q.1) (glueIdx lx q.2)) q with hH'def
  set σ : ℂ := if odd then -1 else 1 with hσ
  have hA : ∀ p, HasFDerivAt (fun q => σ * H (reflX q)) (σ • (H' (reflX p)).comp reflX) p := by
    intro p
    exact ((hH (reflX p)).comp p reflX.hasFDerivAt).const_mul σ
  have hA' : Continuous (fun p => σ • (H' (reflX p)).comp reflX) :=
    ((hH'.comp reflX.continuous).clm_comp (continuous_const (y := reflX))).const_smul σ
  have hJ0 := glueIdx_zero lx hpos
  have g := glue_two (A := fun q => σ * H (reflX q)) (B := H) (A' := fun p => σ • (H' (reflX p)).comp reflX)
    (B' := H') Prod.snd continuous_snd 0 hA hH hA' hH'
    (fun p hp => by
      obtain ⟨t, x⟩ := p
      simp only at hp
      subst hp
      simp only [hHdef, reflX_apply, neg_zero, hJ0]
      cases odd
      · simp [hσ]
      · simp [hσ, (hP.par _ (glueIdx_le lt t) t).1 rfl])
    (fun p hp => by
      obtain ⟨t, x⟩ := p
      simp only at hp
      subst hp
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [hH'def, reflX_apply, neg_zero, hJ0, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply, dP_apply, smul_eq_mul]
      have hi := glueIdx_le lt t
      cases odd
      · simp [hσ, (hP.par _ hi t).2 rfl]
      · have h0 : evP (MvPolynomial.pderiv 0 (P (glueIdx lt t) 0)) (t, 0) = 0 := by
          have := evP_line_t (P := P (glueIdx lt t) 0) (Q := 0) (x0 := 0) (fun t' => by
            rw [show evP 0 (t', 0) = 0 by simp [evP]]
            exact (hP.par _ hi t').1 rfl) t
          simpa [evP] using this
        simp [hσ, h0])
  have e1 : fullF lt lx odd P = fun q => if 0 ≤ q.2 then H q else σ * H (reflX q) := by
    funext q
    obtain ⟨t, x⟩ := q
    simp only [fullF, hHdef, reflX_apply]
    by_cases hx : 0 ≤ x
    · rw [if_pos hx, abs_of_nonneg hx]
      simp [not_lt.2 hx]
    · rw [if_neg hx, abs_of_neg (not_le.1 hx)]
      simp [hσ, not_le.1 hx]
  have e2 : fullD lt lx odd P = fun q => if 0 ≤ q.2 then H' q else σ • (H' (reflX q)).comp reflX := by
    funext q
    simp only [fullD, hH'def, hσ, reflX_apply]
  rw [e1, e2]
  exact g

private theorem fullD_t (lt lx : List ℝ) (odd : Bool) (P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (p : ℝ × ℝ) :
    fullD lt lx odd P p ((1 : ℝ), (0 : ℝ)) = fullF lt lx odd (fun i j => MvPolynomial.pderiv 0 (P i j)) p := by
  obtain ⟨t, x⟩ := p
  by_cases hx : 0 ≤ x
  · simp [fullD, fullF, hx, not_lt.2 hx, abs_of_nonneg hx, dP_apply]
  · have hx' : x < 0 := not_le.1 hx
    cases odd <;> simp [fullD, fullF, hx, hx', abs_of_neg hx', dP_apply, reflX_apply]

private theorem fullD_x (lt lx : List ℝ) (odd : Bool) (P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (p : ℝ × ℝ) :
    fullD lt lx odd P p ((0 : ℝ), (1 : ℝ)) = fullF lt lx (!odd) (fun i j => MvPolynomial.pderiv 1 (P i j)) p := by
  obtain ⟨t, x⟩ := p
  by_cases hx : 0 ≤ x
  · simp [fullD, fullF, hx, not_lt.2 hx, abs_of_nonneg hx, dP_apply]
  · have hx' : x < 0 := not_le.1 hx
    cases odd <;> simp [fullD, fullF, hx, hx', abs_of_neg hx', dP_apply, reflX_apply]

private theorem eval_bind_two (v : Fin 2 → ℂ) (g : Fin 2 → MvPolynomial (Fin 2) ℂ) (Q : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval v (MvPolynomial.bind₁ g Q) = MvPolynomial.eval (fun i => MvPolynomial.eval v (g i)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp [hp, hr]
  | mul_X p i hp => simp [hp]

private theorem evP_atFirst (c : ℝ) (Q : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) :
    evP (atFirst (c : ℂ) Q) q = evP Q (c, q.2) := by
  unfold evP atFirst
  rw [eval_bind_two]
  refine congrArg (fun v => MvPolynomial.eval v Q) (funext fun i => ?_)
  fin_cases i <;> simp

private theorem evP_atSecond (c : ℝ) (Q : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) :
    evP (atSecond (c : ℂ) Q) q = evP Q (q.1, c) := by
  unfold evP atSecond
  rw [eval_bind_two]
  refine congrArg (fun v => MvPolynomial.eval v Q) (funext fun i => ?_)
  fin_cases i <;> simp

private theorem join_t {Q R : MvPolynomial (Fin 2) ℂ} {c : ℝ} (h : atFirst (c : ℂ) Q = atFirst (c : ℂ) R) (x : ℝ) :
    evP Q (c, x) = evP R (c, x) := by
  have := congrArg (fun W => evP W (0, x)) h
  simpa [evP_atFirst] using this

private theorem join_x {Q R : MvPolynomial (Fin 2) ℂ} {c : ℝ} (h : atSecond (c : ℂ) Q = atSecond (c : ℂ) R) (t : ℝ) :
    evP Q (t, c) = evP R (t, c) := by
  have := congrArg (fun W => evP W (t, 0)) h
  simpa [evP_atSecond] using this

private theorem par_zero {Q : MvPolynomial (Fin 2) ℂ} (h : atSecond 0 Q = 0) (t : ℝ) : evP Q (t, 0) = 0 := by
  have := congrArg (fun W => evP W (t, 0)) h
  have e := evP_atSecond 0 Q (t, 0)
  rw [Complex.ofReal_zero] at e
  rw [← e]
  exact this.trans (by simp [evP])

private theorem mesh_facts (l : List ℝ) (hs : l.Pairwise (· < ·)) (h0 : l.head? = some 0) (h1 : l.getLast? = some 1) :
    ((l.drop 1).dropLast).Pairwise (· < ·) ∧ (∀ b ∈ (l.drop 1).dropLast, 0 < b) ∧
      ((l.drop 1).dropLast).length + 1 = cellCount l ∧
      ∀ k (hk : k < ((l.drop 1).dropLast).length), ((l.drop 1).dropLast)[k] = l.getD (k + 1) 0 := by
  refine ⟨hs.sublist ((List.dropLast_sublist _).trans (List.drop_sublist _ _)), ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨r, rfl⟩ : ∃ r, l = 0 :: r := by
      cases l with
      | nil => simp at h0
      | cons a r => simp at h0; exact ⟨r, by rw [h0]⟩
    have hb' : b ∈ r := by simpa using List.mem_of_mem_dropLast hb
    exact List.rel_of_pairwise_cons hs hb'
  · have : 2 ≤ l.length := by
      match l, h0, h1 with
      | [], h0, _ => simp at h0
      | [a], h0, h1 => simp at h0 h1; linarith
      | a :: b :: r, _, _ => simp
    simp [cellCount]
    omega
  · intro k hk
    simp [List.getD_eq_getElem?_getD, List.getElem_dropLast, List.getElem_drop]
    rw [List.getElem?_eq_getElem]
    · simp [add_comm]
    · simp at hk; omega

private theorem spline_eq (S : Spline) (odd : Bool) :
    (fun p : ℝ × ℝ => S.eval odd p.1 p.2) =
      fullF ((S.mesh.tBreaks.drop 1).dropLast) ((S.mesh.xBreaks.drop 1).dropLast) odd S.piece := by
  funext p
  rfl

private theorem glued_base (S : Spline) {a b : ℕ} {odd : Bool} (hS : IsSplineClass a b odd S) (ha : 1 ≤ a)
    (hb : 1 ≤ b) : Glued ((S.mesh.tBreaks.drop 1).dropLast) ((S.mesh.xBreaks.drop 1).dropLast) odd S.piece := by
  obtain ⟨-, -, ct, gt⟩ := mesh_facts _ hS.mesh.t_sorted hS.mesh.t_first hS.mesh.t_last
  obtain ⟨-, -, cx, gx⟩ := mesh_facts _ hS.mesh.x_sorted hS.mesh.x_first hS.mesh.x_last
  refine ⟨fun k hk j hj x => ?_, fun k hk i hi t => ?_, fun i hi t => ⟨fun ho => ?_, fun ho => ?_⟩⟩
  · rw [gt k hk]
    have h0 := hS.t_joins (k + 1) (by omega) (by omega) j (by omega) 0 (Nat.zero_le _)
    have h1 := hS.t_joins (k + 1) (by omega) (by omega) j (by omega) 1 ha
    simp only [Nat.add_sub_cancel, tDeriv, Function.iterate_zero, id, Function.iterate_one] at h0 h1
    exact ⟨join_t h0 x, join_t h1 x⟩
  · rw [gx k hk]
    have h0 := hS.x_joins (k + 1) (by omega) (by omega) i (by omega) 0 (Nat.zero_le _)
    have h1 := hS.x_joins (k + 1) (by omega) (by omega) i (by omega) 1 hb
    simp only [Nat.add_sub_cancel, xDeriv, Function.iterate_zero, id, Function.iterate_one] at h0 h1
    exact ⟨join_x h0 t, join_x h1 t⟩
  · have h := hS.parity i (by omega) 0 (Nat.zero_le _) (by simp [ho])
    simp only [xDeriv, Function.iterate_zero, id] at h
    exact par_zero h t
  · have h := hS.parity i (by omega) 1 hb (by simp [ho])
    simp only [xDeriv, Function.iterate_one] at h
    exact par_zero h t

private theorem glued_t (S : Spline) {a b : ℕ} {odd : Bool} (hS : IsSplineClass a b odd S) (ha : 2 ≤ a)
    (hb : 1 ≤ b) : Glued ((S.mesh.tBreaks.drop 1).dropLast) ((S.mesh.xBreaks.drop 1).dropLast) odd
      (fun i j => MvPolynomial.pderiv 0 (S.piece i j)) := by
  have G := glued_base S hS (by omega) hb
  obtain ⟨-, -, ct, gt⟩ := mesh_facts _ hS.mesh.t_sorted hS.mesh.t_first hS.mesh.t_last
  obtain ⟨-, -, cx, gx⟩ := mesh_facts _ hS.mesh.x_sorted hS.mesh.x_first hS.mesh.x_last
  refine ⟨fun k hk j hj x => ?_, fun k hk i hi t => ?_, fun i hi t => ⟨fun ho => ?_, fun ho => ?_⟩⟩
  · rw [gt k hk]
    have h1 := hS.t_joins (k + 1) (by omega) (by omega) j (by omega) 1 (by omega)
    have h2 := hS.t_joins (k + 1) (by omega) (by omega) j (by omega) 2 ha
    simp only [Nat.add_sub_cancel, tDeriv, Function.iterate_one, Function.iterate_succ_apply'] at h1 h2
    exact ⟨join_t h1 x, join_t h2 x⟩
  · refine ⟨evP_line_t (fun t' => (G.hx k hk i hi t').1) t, ?_⟩
    rw [← pderiv_swap, ← pderiv_swap]
    exact evP_line_t (fun t' => (G.hx k hk i hi t').2) t
  · have := evP_line_t (P := S.piece i 0) (Q := 0) (x0 := 0) (fun t' => by
      rw [show evP 0 (t', 0) = 0 by simp [evP]]
      exact (G.par i hi t').1 ho) t
    simpa [evP] using this
  · rw [← pderiv_swap]
    have := evP_line_t (P := MvPolynomial.pderiv 1 (S.piece i 0)) (Q := 0) (x0 := 0) (fun t' => by
      rw [show evP 0 (t', 0) = 0 by simp [evP]]
      exact (G.par i hi t').2 ho) t
    simpa [evP] using this

private theorem glued_x (S : Spline) {a b : ℕ} {odd : Bool} (hS : IsSplineClass a b odd S) (ha : 1 ≤ a)
    (hb : 2 ≤ b) : Glued ((S.mesh.tBreaks.drop 1).dropLast) ((S.mesh.xBreaks.drop 1).dropLast) (!odd)
      (fun i j => MvPolynomial.pderiv 1 (S.piece i j)) := by
  have G := glued_base S hS ha (by omega)
  obtain ⟨-, -, ct, gt⟩ := mesh_facts _ hS.mesh.t_sorted hS.mesh.t_first hS.mesh.t_last
  obtain ⟨-, -, cx, gx⟩ := mesh_facts _ hS.mesh.x_sorted hS.mesh.x_first hS.mesh.x_last
  refine ⟨fun k hk j hj x => ?_, fun k hk i hi t => ?_, fun i hi t => ⟨fun ho => ?_, fun ho => ?_⟩⟩
  · refine ⟨evP_line_x (fun x' => (G.ht k hk j hj x').1) x, ?_⟩
    rw [pderiv_swap, pderiv_swap]
    exact evP_line_x (fun x' => (G.ht k hk j hj x').2) x
  · rw [gx k hk]
    have h1 := hS.x_joins (k + 1) (by omega) (by omega) i (by omega) 1 (by omega)
    have h2 := hS.x_joins (k + 1) (by omega) (by omega) i (by omega) 2 hb
    simp only [Nat.add_sub_cancel, xDeriv, Function.iterate_one, Function.iterate_succ_apply'] at h1 h2
    exact ⟨join_x h1 t, join_x h2 t⟩
  · have ho' : odd = false := by simpa using ho
    have h := hS.parity i (by omega) 1 (by omega) (by simp [ho'])
    simp only [xDeriv, Function.iterate_one] at h
    exact par_zero h t
  · have ho' : odd = true := by simpa using ho
    have h := hS.parity i (by omega) 2 hb (by simp [ho'])
    simp only [xDeriv, Function.iterate_succ_apply', Function.iterate_one] at h
    exact par_zero h t

private theorem slope_glue_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A B : ℝ × ℝ → E}
    (π : ℝ × ℝ →L[ℝ] ℝ) (c : ℝ) {U : Set (ℝ × ℝ)} (hU : Convex ℝ U) {K : NNReal}
    (hA : LipschitzOnWith K A U) (hB : LipschitzOnWith K B U) (h : ∀ p, c = π p → B p = A p) :
    LipschitzOnWith K (fun q => if c ≤ π q then B q else A q) U := by
  have key : ∀ p ∈ U, ∀ q ∈ U, π p < c → c ≤ π q → dist (A p) (B q) ≤ K * dist p q := by
    intro p hp q hq h1 h2
    have hpos : 0 < π q - π p := by linarith
    set s : ℝ := (c - π p) / (π q - π p) with hs
    have s0 : 0 ≤ s := div_nonneg (by linarith) hpos.le
    have s1 : s ≤ 1 := (div_le_one hpos).2 (by linarith)
    set r := AffineMap.lineMap p q s with hr
    have hrU : r ∈ U := hU.lineMap_mem hp hq ⟨s0, s1⟩
    have hπr : c = π r := by
      rw [hr, AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul, hs]
      field_simp
      ring
    have e := h r hπr
    calc dist (A p) (B q) ≤ dist (A p) (A r) + dist (A r) (B q) := dist_triangle _ _ _
      _ = dist (A p) (A r) + dist (B r) (B q) := by rw [e]
      _ ≤ K * dist p r + K * dist r q := add_le_add (hA.dist_le_mul p hp r hrU) (hB.dist_le_mul r hrU q hq)
      _ = K * dist p q := by
        rw [dist_comm p r, hr, dist_lineMap_left, dist_lineMap_right, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg s0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s)]
        ring
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  by_cases h1 : c ≤ π p <;> by_cases h2 : c ≤ π q <;> simp only [h1, h2, if_true, if_false]
  · exact hB.dist_le_mul p hp q hq
  · rw [dist_comm, dist_comm p q]
    exact key q hq p hp (not_le.1 h2) h1
  · exact key p hp q hq (not_le.1 h1) h2
  · exact hA.dist_le_mul p hp q hq

private theorem slope_glue_list {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (π : ℝ × ℝ →L[ℝ] ℝ)
    {U : Set (ℝ × ℝ)} (hU : Convex ℝ U) {K : NNReal} : ∀ (l : List ℝ), l.Pairwise (· < ·) →
    ∀ (F' : ℕ → ℝ × ℝ → E), (∀ k, LipschitzOnWith K (F' k) U) →
    (∀ k (hk : k < l.length) p, π p = l[k] → F' k p = F' (k + 1) p) →
    LipschitzOnWith K (fun p => F' (glueIdx l (π p)) p) U
  | [], _, F', hF', _ => by
    simpa [glueIdx] using hF' 0
  | b :: bs, hl, F', hF', hj => by
    have hbs : bs.Pairwise (· < ·) := hl.of_cons
    have ih := slope_glue_list π hU bs hbs (fun k => F' (k + 1)) (fun k => hF' (k + 1))
      (fun k hk p hp => hj (k + 1) (by simp; omega) p (by simpa using hp))
    have h0 : ∀ u, b ≤ u → u ≤ b → glueIdx bs u = 0 := by
      intro u h1 h2
      unfold glueIdx
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro c hc
      have := List.rel_of_pairwise_cons hl hc
      simp only [decide_eq_true_eq, not_le]
      linarith
    have e2 : (fun p => F' (glueIdx (b :: bs) (π p)) p) =
        fun p => if b ≤ π p then F' (glueIdx bs (π p) + 1) p else F' 0 p := by
      funext q
      rw [glueIdx_cons b bs hl]
      split_ifs <;> rfl
    rw [e2]
    exact slope_glue_two (A := F' 0) (B := fun q => F' (glueIdx bs (π q) + 1) q) π b hU (hF' 0) ih
      (fun p hp => by
        show F' (glueIdx bs (π p) + 1) p = F' 0 p
        rw [h0 (π p) hp.le hp.ge]
        exact (hj 0 (by simp) p (by simpa using hp.symm)).symm)

private theorem slope_half (lt lx : List ℝ) (hlt : lt.Pairwise (· < ·)) (hlx : lx.Pairwise (· < ·)) {odd : Bool}
    (P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (hP : Glued lt lx odd P) {U : Set (ℝ × ℝ)} (hU : Convex ℝ U)
    {K : NNReal} (hK : ∀ i ≤ lt.length, ∀ j ≤ lx.length, LipschitzOnWith K (dP (P i j)) U) :
    LipschitzOnWith K (fun p => dP (P (glueIdx lt p.1) (glueIdx lx p.2)) p) U := by
  have hrow : ∀ j ≤ lx.length, LipschitzOnWith K (fun p => dP (P (glueIdx lt p.1) j) p) U := by
    intro j hj
    have h := slope_glue_list (ContinuousLinearMap.fst ℝ ℝ ℝ) hU lt hlt (fun k => dP (P (min k lt.length) j))
      (fun k => hK _ (min_le_right _ _) j hj) (fun k hk p hp => by
        obtain ⟨t, x⟩ := p
        simp only [ContinuousLinearMap.coe_fst'] at hp
        subst hp
        rw [Nat.min_eq_left hk.le, Nat.min_eq_left hk]
        obtain ⟨h1, h2⟩ := hP.ht k hk j hj x
        refine ContinuousLinearMap.ext fun v => ?_
        rw [dP_apply, dP_apply, h2, evP_line_x (fun x' => (hP.ht k hk j hj x').1) x])
    have e : ∀ u, min (glueIdx lt u) lt.length = glueIdx lt u := fun u => Nat.min_eq_left (glueIdx_le lt u)
    simpa only [ContinuousLinearMap.coe_fst', e] using h
  have h := slope_glue_list (ContinuousLinearMap.snd ℝ ℝ ℝ) hU lx hlx
    (fun j q => dP (P (glueIdx lt q.1) (min j lx.length)) q) (fun j => hrow _ (min_le_right _ _))
    (fun k hk p hp => by
      obtain ⟨t, x⟩ := p
      simp only [ContinuousLinearMap.coe_snd'] at hp
      subst hp
      simp only
      rw [Nat.min_eq_left hk.le, Nat.min_eq_left hk]
      obtain ⟨h1, h2⟩ := hP.hx k hk _ (glueIdx_le lt t) t
      refine ContinuousLinearMap.ext fun v => ?_
      rw [dP_apply, dP_apply, h2, evP_line_t (fun t' => (hP.hx k hk _ (glueIdx_le lt t) t').1) t])
  have e : ∀ u, min (glueIdx lx u) lx.length = glueIdx lx u := fun u => Nat.min_eq_left (glueIdx_le lx u)
  simpa only [ContinuousLinearMap.coe_snd', e] using h

private theorem reflX_norm (q : ℝ × ℝ) : ‖reflX q‖ = ‖q‖ := by
  rw [reflX_apply, Prod.norm_def, Prod.norm_def]
  simp

private theorem reflX_opNorm : ‖reflX‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun q => by rw [reflX_norm, one_mul])

private theorem slope_full (lt lx : List ℝ) (hlt : lt.Pairwise (· < ·)) (hlx : lx.Pairwise (· < ·))
    (hpos : ∀ b ∈ lx, 0 < b) {odd : Bool} (P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (hP : Glued lt lx odd P)
    (R : ℝ) {K : NNReal}
    (hK : ∀ i ≤ lt.length, ∀ j ≤ lx.length, LipschitzOnWith K (dP (P i j)) (Metric.closedBall 0 R)) :
    LipschitzOnWith K (fullD lt lx odd P) (Metric.closedBall 0 R) := by
  have hU : Convex ℝ (Metric.closedBall (0 : ℝ × ℝ) R) := convex_closedBall _ _
  have hH := slope_half lt lx hlt hlx P hP hU hK
  set H' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℂ) := fun q => dP (P (glueIdx lt q.1) (glueIdx lx q.2)) q with hH'def
  set σ : ℂ := if odd then -1 else 1 with hσ
  have hσn : ‖σ‖ = 1 := by
    rw [hσ]
    split_ifs <;> simp
  have hmem : ∀ p ∈ Metric.closedBall (0 : ℝ × ℝ) R, reflX p ∈ Metric.closedBall (0 : ℝ × ℝ) R := by
    intro p hp
    simpa [Metric.mem_closedBall, dist_zero_right, reflX_norm] using hp
  have hA : LipschitzOnWith K (fun p => σ • (H' (reflX p)).comp reflX) (Metric.closedBall 0 R) := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    rw [dist_eq_norm, ← smul_sub, ← ContinuousLinearMap.sub_comp, norm_smul, hσn, one_mul]
    calc ‖(H' (reflX p) - H' (reflX q)).comp reflX‖ ≤ ‖H' (reflX p) - H' (reflX q)‖ * ‖reflX‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖H' (reflX p) - H' (reflX q)‖ * 1 := by gcongr; exact reflX_opNorm
      _ = dist (H' (reflX p)) (H' (reflX q)) := by rw [mul_one, dist_eq_norm]
      _ ≤ K * dist (reflX p) (reflX q) := hH.dist_le_mul _ (hmem p hp) _ (hmem q hq)
      _ = K * dist p q := by rw [dist_eq_norm, dist_eq_norm, ← map_sub, reflX_norm]
  have hJ0 := glueIdx_zero lx hpos
  have g := slope_glue_two (A := fun p => σ • (H' (reflX p)).comp reflX) (B := H')
    (ContinuousLinearMap.snd ℝ ℝ ℝ) 0 hU hA hH
    (fun p hp => by
      obtain ⟨t, x⟩ := p
      simp only [ContinuousLinearMap.coe_snd'] at hp
      subst hp
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [hH'def, reflX_apply, neg_zero, hJ0, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply, dP_apply, smul_eq_mul]
      have hi := glueIdx_le lt t
      cases odd
      · simp [hσ, (hP.par _ hi t).2 rfl]
      · have h0 : evP (MvPolynomial.pderiv 0 (P (glueIdx lt t) 0)) (t, 0) = 0 := by
          have := evP_line_t (P := P (glueIdx lt t) 0) (Q := 0) (x0 := 0) (fun t' => by
            rw [show evP 0 (t', 0) = 0 by simp [evP]]
            exact (hP.par _ hi t').1 rfl) t
          simpa [evP] using this
        simp [hσ, h0])
  have e2 : fullD lt lx odd P =
      fun q => if 0 ≤ (ContinuousLinearMap.snd ℝ ℝ ℝ) q then H' q else σ • (H' (reflX q)).comp reflX := by
    funext q
    simp only [fullD, hH'def, hσ, reflX_apply, ContinuousLinearMap.coe_snd']
  rw [e2]
  exact g

private theorem evP_contDiff (Q : MvPolynomial (Fin 2) ℂ) : ContDiff ℝ 1 (evP Q) :=
  contDiff_one_iff_hasFDerivAt.2 ⟨dP Q, dP_continuous Q, evP_hasFDerivAt Q⟩

private theorem dP_contDiff (Q : MvPolynomial (Fin 2) ℂ) : ContDiff ℝ 1 (dP Q) := by
  unfold dP
  exact (contDiff_const.smulRight (evP_contDiff _)).add (contDiff_const.smulRight (evP_contDiff _))

private theorem dP_slope (Q : MvPolynomial (Fin 2) ℂ) (R : ℝ) :
    ∃ K, LipschitzOnWith K (dP Q) (Metric.closedBall 0 R) :=
  LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (isCompact_closedBall 0 R)
    ((dP_contDiff Q).locallyLipschitz.locallyLipschitzOn)

private theorem fullD_locSlope (lt lx : List ℝ) (hlt : lt.Pairwise (· < ·)) (hlx : lx.Pairwise (· < ·))
    (hpos : ∀ b ∈ lx, 0 < b) {odd : Bool} (P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (hP : Glued lt lx odd P) :
    LocallyLipschitz (fullD lt lx odd P) := by
  intro p
  have hK : ∀ i j, ∃ K, LipschitzOnWith K (dP (P i j)) (Metric.closedBall 0 (‖p‖ + 1)) :=
    fun i j => dP_slope _ _
  choose K hK using hK
  have hmem : p ∈ Metric.ball (0 : ℝ × ℝ) (‖p‖ + 1) := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  refine ⟨∑ i ∈ Finset.range (lt.length + 1), ∑ j ∈ Finset.range (lx.length + 1), K i j,
    Metric.closedBall 0 (‖p‖ + 1),
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hmem) Metric.ball_subset_closedBall, ?_⟩
  refine slope_full lt lx hlt hlx hpos P hP _ (fun i hi j hj => (hK i j).weaken ?_)
  calc K i j ≤ ∑ j ∈ Finset.range (lx.length + 1), K i j :=
        Finset.single_le_sum (f := fun j => K i j) (fun _ _ => by positivity) (Finset.mem_range.2 (by omega))
    _ ≤ _ := Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range (lx.length + 1), K i j)
        (fun _ _ => by positivity) (Finset.mem_range.2 (by omega))

private theorem fderiv_fullF (lt lx : List ℝ) (hlt : lt.Pairwise (· < ·)) (hlx : lx.Pairwise (· < ·))
    (hpos : ∀ b ∈ lx, 0 < b) {odd : Bool} (P : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (hP : Glued lt lx odd P) :
    LocallyLipschitz (fderiv ℝ (fullF lt lx odd P)) := by
  obtain ⟨h1, -⟩ := full_glue lt lx hlt hlx hpos P hP
  have e : fderiv ℝ (fullF lt lx odd P) = fullD lt lx odd P := funext fun p => (h1 p).fderiv
  rw [e]
  exact fullD_locSlope lt lx hlt hlx hpos P hP

theorem spline_eval_localSlope (S : Spline) {a b : ℕ} {odd : Bool} (hS : IsSplineClass a b odd S) (ha : 1 ≤ a)
    (hb : 1 ≤ b) : LocallyLipschitz (fderiv ℝ (fun p : ℝ × ℝ => S.eval odd p.1 p.2)) := by
  obtain ⟨st, pt, -, -⟩ := mesh_facts _ hS.mesh.t_sorted hS.mesh.t_first hS.mesh.t_last
  obtain ⟨sx, px, -, -⟩ := mesh_facts _ hS.mesh.x_sorted hS.mesh.x_first hS.mesh.x_last
  rw [spline_eq]
  exact fderiv_fullF _ _ st sx px _ (glued_base S hS ha hb)

theorem spline_tderiv_localSlope (S : Spline) {a b : ℕ} {odd : Bool} (hS : IsSplineClass a b odd S) (ha : 2 ≤ a)
    (hb : 1 ≤ b) : LocallyLipschitz (fderiv ℝ (fun p : ℝ × ℝ => deriv (fun t => S.eval odd t p.2) p.1)) := by
  obtain ⟨st, pt, -, -⟩ := mesh_facts _ hS.mesh.t_sorted hS.mesh.t_first hS.mesh.t_last
  obtain ⟨sx, px, -, -⟩ := mesh_facts _ hS.mesh.x_sorted hS.mesh.x_first hS.mesh.x_last
  obtain ⟨h1, -⟩ := full_glue _ _ st sx px _ (glued_base S hS (by omega) hb)
  have e : (fun p : ℝ × ℝ => deriv (fun t => S.eval odd t p.2) p.1) =
      fullF ((S.mesh.tBreaks.drop 1).dropLast) ((S.mesh.xBreaks.drop 1).dropLast) odd
        (fun i j => MvPolynomial.pderiv 0 (S.piece i j)) := by
    funext p
    have hl : HasDerivAt (fun s : ℝ => (s, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
      (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
    have hd := (h1 (p.1, p.2)).comp_hasDerivAt p.1 hl
    have ef : (fun t => S.eval odd t p.2) =
        (fullF ((S.mesh.tBreaks.drop 1).dropLast) ((S.mesh.xBreaks.drop 1).dropLast) odd S.piece ∘
          fun s : ℝ => (s, p.2)) := by
      funext s
      exact congrFun (spline_eq S odd) (s, p.2)
    rw [ef, hd.deriv, fullD_t]
  rw [e]
  exact fderiv_fullF _ _ st sx px _ (glued_t S hS ha hb)

theorem spline_xderiv_localSlope (S : Spline) {a b : ℕ} {odd : Bool} (hS : IsSplineClass a b odd S) (ha : 1 ≤ a)
    (hb : 2 ≤ b) : LocallyLipschitz (fderiv ℝ (fun p : ℝ × ℝ => deriv (fun x => S.eval odd p.1 x) p.2)) := by
  obtain ⟨st, pt, -, -⟩ := mesh_facts _ hS.mesh.t_sorted hS.mesh.t_first hS.mesh.t_last
  obtain ⟨sx, px, -, -⟩ := mesh_facts _ hS.mesh.x_sorted hS.mesh.x_first hS.mesh.x_last
  obtain ⟨h1, -⟩ := full_glue _ _ st sx px _ (glued_base S hS ha (by omega))
  have e : (fun p : ℝ × ℝ => deriv (fun x => S.eval odd p.1 x) p.2) =
      fullF ((S.mesh.tBreaks.drop 1).dropLast) ((S.mesh.xBreaks.drop 1).dropLast) (!odd)
        (fun i j => MvPolynomial.pderiv 1 (S.piece i j)) := by
    funext p
    have hl : HasDerivAt (fun s : ℝ => (p.1, s)) ((0 : ℝ), (1 : ℝ)) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    have hd := (h1 (p.1, p.2)).comp_hasDerivAt p.2 hl
    have ef : (fun x => S.eval odd p.1 x) =
        (fullF ((S.mesh.tBreaks.drop 1).dropLast) ((S.mesh.xBreaks.drop 1).dropLast) odd S.piece ∘
          fun s : ℝ => (p.1, s)) := by
      funext s
      exact congrFun (spline_eq S odd) (p.1, s)
    rw [ef, hd.deriv, fullD_x]
  rw [e]
  exact fderiv_fullF _ _ st sx px _ (glued_x S hS ha hb)


section Tame

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

private def TameAt (f : E → F) (y : E) : Prop :=
  ∃ r > 0, ∃ f' : E → (E →L[ℝ] F), ∃ K : ℝ, 0 ≤ K ∧ (∀ z ∈ Metric.ball y r, HasFDerivAt f (f' z) z) ∧
    ∀ z ∈ Metric.ball y r, ∀ w ∈ Metric.ball y r, ‖f' z - f' w‖ ≤ K * ‖z - w‖

private theorem tame_bounds {f : E → F} {y : E} {r : ℝ} {f' : E → (E →L[ℝ] F)} {K : ℝ} (hr : 0 < r)
    (hK0 : 0 ≤ K) (hd : ∀ z ∈ Metric.ball y r, HasFDerivAt f (f' z) z)
    (hK : ∀ z ∈ Metric.ball y r, ∀ w ∈ Metric.ball y r, ‖f' z - f' w‖ ≤ K * ‖z - w‖) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ z ∈ Metric.ball y r, ‖f' z‖ ≤ M) ∧
      (∀ z ∈ Metric.ball y r, ∀ w ∈ Metric.ball y r, ‖f z - f w‖ ≤ M * ‖z - w‖) ∧
      (∀ z ∈ Metric.ball y r, ‖f z‖ ≤ ‖f y‖ + M * r) := by
  have hy : y ∈ Metric.ball y r := Metric.mem_ball_self hr
  have hb : ∀ z ∈ Metric.ball y r, ‖f' z‖ ≤ ‖f' y‖ + K * r := by
    intro z hz
    have h1 := hK z hz y hy
    have h2 : ‖z - y‖ < r := by rw [Metric.mem_ball, dist_eq_norm] at hz; exact hz
    have h3 : ‖f' z‖ ≤ ‖f' y‖ + ‖f' z - f' y‖ := by
      have := norm_add_le (f' y) (f' z - f' y)
      simpa using this
    nlinarith [norm_nonneg (z - y)]
  have hM0 : 0 ≤ ‖f' y‖ + K * r := by positivity
  have hl : ∀ z ∈ Metric.ball y r, ∀ w ∈ Metric.ball y r, ‖f z - f w‖ ≤ (‖f' y‖ + K * r) * ‖z - w‖ := by
    intro z hz w hw
    have := (convex_ball y r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x hx => (hd x hx).hasFDerivWithinAt) hb hw hz
    exact this
  refine ⟨‖f' y‖ + K * r, hM0, hb, hl, fun z hz => ?_⟩
  have h1 := hl z hz y hy
  have h2 : ‖z - y‖ < r := by rw [Metric.mem_ball, dist_eq_norm] at hz; exact hz
  have h3 : ‖f z‖ ≤ ‖f y‖ + ‖f z - f y‖ := by
    have := norm_add_le (f y) (f z - f y)
    simpa using this
  nlinarith [norm_nonneg (z - y)]

private theorem tame_of_contDiffAt {f : E → F} {y : E} (hf : ContDiffAt ℝ 2 f y) : TameAt f y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) y := hf.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := h1.exists_lipschitzOnWith
  have hev : ∀ᶠ z in nhds y, ContDiffAt ℝ 2 f z := hf.eventually (by simp)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem ht hev)
  refine ⟨r, hr, fderiv ℝ f, K, K.2, fun z hz => ((show ContDiffAt ℝ 2 f z from (hsub hz).2).differentiableAt (by norm_num)).hasFDerivAt,
    fun z hz w hw => ?_⟩
  have := hK.dist_le_mul z (hsub hz).1 w (hsub hw).1
  rwa [dist_eq_norm, dist_eq_norm] at this

private theorem tame_of_global {f : E → F} (hd : Differentiable ℝ f) (hl : LocallyLipschitz (fderiv ℝ f))
    (y : E) : TameAt f y := by
  obtain ⟨K, t, ht, hK⟩ := hl y
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 ht
  refine ⟨r, hr, fderiv ℝ f, K, K.2, fun z _ => (hd z).hasFDerivAt, fun z hz w hw => ?_⟩
  have := hK.dist_le_mul z (hsub hz) w (hsub hw)
  rwa [dist_eq_norm, dist_eq_norm] at this

private theorem tame_slope {f : E → F} {y : E} (h : TameAt f y) :
    ∃ K : NNReal, ∃ U ∈ nhds y, LipschitzOnWith K (fderiv ℝ f) U := by
  obtain ⟨r, hr, f', K, hK0, h1, h2⟩ := h
  refine ⟨⟨K, hK0⟩, Metric.ball y r, Metric.ball_mem_nhds y hr, LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_⟩
  rw [(h1 z hz).fderiv, (h1 w hw).fderiv, dist_eq_norm, dist_eq_norm]
  exact h2 z hz w hw

private theorem tame_congr {f g : E → F} {y : E} (hg : TameAt g y) (h : f =ᶠ[nhds y] g) : TameAt f y := by
  obtain ⟨r, hr, g', K, hK0, h1, h2⟩ := hg
  obtain ⟨s, hs, hsub⟩ := Metric.mem_nhds_iff.1 h
  have sr : Metric.ball y (min r s) ⊆ Metric.ball y r := Metric.ball_subset_ball (min_le_left _ _)
  refine ⟨min r s, lt_min hr hs, g', K, hK0, fun z hz => ?_, fun z hz w hw => h2 z (sr hz) w (sr hw)⟩
  have hz' : z ∈ Metric.ball y s := Metric.ball_subset_ball (min_le_right _ _) hz
  have hev : f =ᶠ[nhds z] g :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz') (fun x hx => hsub hx)
  exact (h1 z (sr hz)).congr_of_eventuallyEq hev

private theorem tame_add {f g : E → F} {y : E} (hf : TameAt f y) (hg : TameAt g y) :
    TameAt (fun z => f z + g z) y := by
  obtain ⟨r1, hr1, f', K1, hK1, h1, h2⟩ := hf
  obtain ⟨r2, hr2, g', K2, hK2, k1, k2⟩ := hg
  have s1 : Metric.ball y (min r1 r2) ⊆ Metric.ball y r1 := Metric.ball_subset_ball (min_le_left _ _)
  have s2 : Metric.ball y (min r1 r2) ⊆ Metric.ball y r2 := Metric.ball_subset_ball (min_le_right _ _)
  refine ⟨min r1 r2, lt_min hr1 hr2, fun z => f' z + g' z, K1 + K2, by positivity,
    fun z hz => (h1 z (s1 hz)).add (k1 z (s2 hz)), fun z hz w hw => ?_⟩
  have e : f' z + g' z - (f' w + g' w) = (f' z - f' w) + (g' z - g' w) := by abel
  rw [e]
  have a1 := h2 z (s1 hz) w (s1 hw)
  have a2 := k2 z (s2 hz) w (s2 hw)
  calc _ ≤ ‖f' z - f' w‖ + ‖g' z - g' w‖ := norm_add_le _ _
    _ ≤ K1 * ‖z - w‖ + K2 * ‖z - w‖ := add_le_add a1 a2
    _ = (K1 + K2) * ‖z - w‖ := by ring

private theorem tame_clm {f : E → F} {y : E} (L : F →L[ℝ] G) (hf : TameAt f y) :
    TameAt (fun z => L (f z)) y := by
  obtain ⟨r, hr, f', K, hK0, h1, h2⟩ := hf
  refine ⟨r, hr, fun z => L.comp (f' z), ‖L‖ * K, by positivity,
    fun z hz => L.hasFDerivAt.comp z (h1 z hz), fun z hz w hw => ?_⟩
  rw [← ContinuousLinearMap.comp_sub]
  calc _ ≤ ‖L‖ * ‖f' z - f' w‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖L‖ * (K * ‖z - w‖) := mul_le_mul_of_nonneg_left (h2 z hz w hw) (norm_nonneg _)
    _ = ‖L‖ * K * ‖z - w‖ := by ring

private theorem tame_comp {Φ : E → F} {g : F → G} {y : E} (hg : TameAt g (Φ y)) (hΦ : TameAt Φ y) :
    TameAt (fun z => g (Φ z)) y := by
  obtain ⟨r1, hr1, g', K1, hK1, hg1, hg2⟩ := hg
  obtain ⟨r2, hr2, Φ', K2, hK2, hΦ1, hΦ2⟩ := hΦ
  obtain ⟨M1, hM1, hb1, -, -⟩ := tame_bounds hr1 hK1 hg1 hg2
  obtain ⟨M2, hM2, hb2, hl2, -⟩ := tame_bounds hr2 hK2 hΦ1 hΦ2
  have hq : 0 < r1 / (M2 + 1) := div_pos hr1 (by linarith)
  have s2 : Metric.ball y (min r2 (r1 / (M2 + 1))) ⊆ Metric.ball y r2 := Metric.ball_subset_ball (min_le_left _ _)
  have hmap : ∀ z ∈ Metric.ball y (min r2 (r1 / (M2 + 1))), Φ z ∈ Metric.ball (Φ y) r1 := by
    intro z hz
    have h := hl2 z (s2 hz) y (Metric.mem_ball_self hr2)
    have hzr : ‖z - y‖ < r1 / (M2 + 1) := by
      rw [Metric.mem_ball, dist_eq_norm] at hz
      exact lt_of_lt_of_le hz (min_le_right _ _)
    have h3 : ‖z - y‖ * (M2 + 1) < r1 := (lt_div_iff₀ (by linarith)).1 hzr
    rw [Metric.mem_ball, dist_eq_norm]
    nlinarith [norm_nonneg (z - y)]
  refine ⟨min r2 (r1 / (M2 + 1)), lt_min hr2 hq, fun z => (g' (Φ z)).comp (Φ' z), K1 * M2 * M2 + M1 * K2,
    by positivity, fun z hz => (hg1 (Φ z) (hmap z hz)).comp z (hΦ1 z (s2 hz)), fun z hz w hw => ?_⟩
  have e : (g' (Φ z)).comp (Φ' z) - (g' (Φ w)).comp (Φ' w) =
      (g' (Φ z) - g' (Φ w)).comp (Φ' z) + (g' (Φ w)).comp (Φ' z - Φ' w) := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  rw [e]
  have a1 := hg2 (Φ z) (hmap z hz) (Φ w) (hmap w hw)
  have a2 := hl2 z (s2 hz) w (s2 hw)
  have a3 := hb2 z (s2 hz)
  have a4 := hb1 (Φ w) (hmap w hw)
  have a5 := hΦ2 z (s2 hz) w (s2 hw)
  calc _ ≤ ‖g' (Φ z) - g' (Φ w)‖ * ‖Φ' z‖ + ‖g' (Φ w)‖ * ‖Φ' z - Φ' w‖ :=
        (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
          (ContinuousLinearMap.opNorm_comp_le _ _))
    _ ≤ (K1 * (M2 * ‖z - w‖)) * M2 + M1 * (K2 * ‖z - w‖) := by
        refine add_le_add (mul_le_mul (a1.trans (mul_le_mul_of_nonneg_left a2 hK1)) a3 (norm_nonneg _)
          (by positivity)) (mul_le_mul a4 a5 (norm_nonneg _) hM1)
    _ = (K1 * M2 * M2 + M1 * K2) * ‖z - w‖ := by ring

private theorem tame_mul {c d : E → ℂ} {y : E} (hc : TameAt c y) (hd : TameAt d y) :
    TameAt (fun z => c z * d z) y := by
  obtain ⟨r1, hr1, c', K1, hK1, hc1, hc2⟩ := hc
  obtain ⟨r2, hr2, d', K2, hK2, hd1, hd2⟩ := hd
  obtain ⟨M1, hM1, hb1, hl1, hv1⟩ := tame_bounds hr1 hK1 hc1 hc2
  obtain ⟨M2, hM2, hb2, hl2, hv2⟩ := tame_bounds hr2 hK2 hd1 hd2
  have s1 : Metric.ball y (min r1 r2) ⊆ Metric.ball y r1 := Metric.ball_subset_ball (min_le_left _ _)
  have s2 : Metric.ball y (min r1 r2) ⊆ Metric.ball y r2 := Metric.ball_subset_ball (min_le_right _ _)
  have hA1 : 0 ≤ ‖c y‖ + M1 * r1 := by positivity
  have hA2 : 0 ≤ ‖d y‖ + M2 * r2 := by positivity
  refine ⟨min r1 r2, lt_min hr1 hr2, fun z => c z • d' z + d z • c' z,
    (‖c y‖ + M1 * r1) * K2 + M1 * M2 + (‖d y‖ + M2 * r2) * K1 + M2 * M1, by positivity,
    fun z hz => (hc1 z (s1 hz)).mul (hd1 z (s2 hz)), fun z hz w hw => ?_⟩
  have e : (c z • d' z + d z • c' z) - (c w • d' w + d w • c' w) =
      (c z • (d' z - d' w) + (c z - c w) • d' w) + (d z • (c' z - c' w) + (d z - d w) • c' w) := by
    simp only [smul_sub, sub_smul]
    abel
  rw [e]
  have t1 : ‖c z • (d' z - d' w)‖ ≤ (‖c y‖ + M1 * r1) * (K2 * ‖z - w‖) :=
    (norm_smul_le _ _).trans (mul_le_mul (hv1 z (s1 hz)) (hd2 z (s2 hz) w (s2 hw)) (norm_nonneg _) hA1)
  have t2 : ‖(c z - c w) • d' w‖ ≤ (M1 * ‖z - w‖) * M2 :=
    (norm_smul_le _ _).trans (mul_le_mul (hl1 z (s1 hz) w (s1 hw)) (hb2 w (s2 hw)) (norm_nonneg _)
      (by positivity))
  have t3 : ‖d z • (c' z - c' w)‖ ≤ (‖d y‖ + M2 * r2) * (K1 * ‖z - w‖) :=
    (norm_smul_le _ _).trans (mul_le_mul (hv2 z (s2 hz)) (hc2 z (s1 hz) w (s1 hw)) (norm_nonneg _) hA2)
  have t4 : ‖(d z - d w) • c' w‖ ≤ (M2 * ‖z - w‖) * M1 :=
    (norm_smul_le _ _).trans (mul_le_mul (hl2 z (s2 hz) w (s2 hw)) (hb1 w (s1 hw)) (norm_nonneg _)
      (by positivity))
  calc _ ≤ (‖c z • (d' z - d' w)‖ + ‖(c z - c w) • d' w‖) + (‖d z • (c' z - c' w)‖ + ‖(d z - d w) • c' w‖) :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ ((‖c y‖ + M1 * r1) * (K2 * ‖z - w‖) + (M1 * ‖z - w‖) * M2) +
        ((‖d y‖ + M2 * r2) * (K1 * ‖z - w‖) + (M2 * ‖z - w‖) * M1) :=
        add_le_add (add_le_add t1 t2) (add_le_add t3 t4)
    _ = _ := by ring

private theorem tame_neg {f : E → F} {y : E} (hf : TameAt f y) : TameAt (fun z => -f z) y :=
  tame_congr (tame_clm (-(ContinuousLinearMap.id ℝ F)) hf) (Filter.Eventually.of_forall fun z => by simp)

private theorem tame_sub {f g : E → F} {y : E} (hf : TameAt f y) (hg : TameAt g y) :
    TameAt (fun z => f z - g z) y :=
  tame_congr (tame_add hf (tame_neg hg)) (Filter.Eventually.of_forall fun z => by simp [sub_eq_add_neg])

end Tame

private theorem pin_coord (i : Fin 3) : ContDiff ℝ ⊤ (fun y : Space => y i) :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff

private theorem pin_norm {y : Space} (hy : y ≠ 0) : ContDiffAt ℝ ⊤ (fun y : Space => ‖y‖) y :=
  contDiffAt_norm ℝ hy

private theorem pin_ratio {y : Space} (hy : y ≠ 0) (j : Fin 3) : ContDiffAt ℝ ⊤ (fun y : Space => y j / ‖y‖) y :=
  (pin_coord j).contDiffAt.div (pin_norm hy) (norm_ne_zero_iff.2 hy)

private theorem pin_chartT (P : ChartParams) (hP : IsChartParams P) {y : Space} (hy : y ≠ 0) :
    ContDiffAt ℝ ⊤ (chartT P) y := by
  have h1 := pin_norm hy
  have hne : ‖y‖ + P.L0 ≠ 0 := by have := hP.L0_pos; positivity
  exact h1.div (h1.add contDiffAt_const) hne

private theorem pin_height {y : Space} (hy : y ≠ 0) : ContDiffAt ℝ ⊤ heightRatio y :=
  pin_ratio hy 2

private theorem pin_decay (P : ChartParams) (hP : IsChartParams P) {y : Space} (hy : y ≠ 0) :
    ContDiffAt ℝ ⊤ (decayFactor P) y := by
  have hs : chartS P y ≠ 0 := by
    unfold chartS chartT
    have hL := hP.L0_pos
    have hd : 0 < ‖y‖ + P.L0 := by positivity
    rw [sub_ne_zero]
    intro h
    rw [eq_comm, div_eq_one_iff_eq hd.ne'] at h
    linarith
  exact (contDiffAt_const.sub (pin_chartT P hP hy)).rpow_const_of_ne hs

private theorem pin_logPhase (P : ChartParams) (hP : IsChartParams P) : ContDiff ℝ ⊤ (logPhase P) := by
  unfold logPhase
  refine contDiff_const.mul (ContDiff.log (contDiff_const.add ((contDiff_norm_sq ℝ).div_const _)) ?_)
  intro y
  have := hP.rc_pos
  positivity

private theorem pin_radial {y : Space} (hy : y ≠ 0) (i : Fin 3) : ContDiffAt ℝ ⊤ (fun y => radialVec y i) y :=
  pin_ratio hy i

private theorem pin_polar {y : Space} (hy : y ≠ 0) (i : Fin 3) : ContDiffAt ℝ ⊤ (fun y => polarVecQ y i) y := by
  have hh := pin_height hy
  fin_cases i
  · simpa [polarVecQ, mul_div_assoc] using hh.mul (pin_ratio hy 0)
  · simpa [polarVecQ, mul_div_assoc] using hh.mul (pin_ratio hy 1)
  · simpa [polarVecQ, qOf] using (contDiffAt_const.sub (hh.pow 2)).neg

private theorem pin_azim {y : Space} (hy : y ≠ 0) (i : Fin 3) : ContDiffAt ℝ ⊤ (fun y => azimVecQ y i) y := by
  fin_cases i
  · simpa [azimVecQ, neg_div] using (pin_ratio hy 1).neg
  · simpa [azimVecQ] using pin_ratio hy 0
  · simpa [azimVecQ] using (contDiffAt_const : ContDiffAt ℝ ⊤ (fun _ : Space => (0 : ℝ)) y)

private def pinPlane (y : Space) : ℂ := ⟨y 0, y 1⟩

private theorem pinPlane_contDiff : ContDiff ℝ ⊤ pinPlane := by
  have e : pinPlane = fun y => ((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I := by
    funext y
    apply Complex.ext <;> simp [pinPlane]
  rw [e]
  exact (Complex.ofRealCLM.contDiff.comp (pin_coord 0)).add
    ((Complex.ofRealCLM.contDiff.comp (pin_coord 1)).mul contDiff_const)

private theorem pin_exp_arg (w : ℂ) (hw : w ≠ 0) (k : ℤ) :
    Complex.exp (Complex.I * (((k : ℝ) * Complex.arg w : ℝ) : ℂ)) = (w * ((‖w‖⁻¹ : ℝ) : ℂ)) ^ k := by
  have h1 : Complex.I * (((k : ℝ) * Complex.arg w : ℝ) : ℂ) = (k : ℂ) * ((Complex.arg w : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h1, Complex.exp_int_mul]
  congr 1
  have h2 := Complex.norm_mul_exp_arg_mul_I w
  have h3 : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hw)
  rw [Complex.ofReal_inv, eq_mul_inv_iff_mul_eq₀ h3, mul_comm]
  exact h2

private theorem pin_zpow {f : Space → ℂ} {y : Space} (hf : ContDiffAt ℝ 2 f y) (hy : f y ≠ 0) (j : ℤ) :
    ContDiffAt ℝ 2 (fun z => f z ^ j) y := by
  cases j with
  | ofNat k => simpa using hf.pow k
  | negSucc k =>
    simp only [zpow_negSucc]
    exact (hf.pow (k + 1)).inv (pow_ne_zero _ hy)

private theorem pin_phase (P : ChartParams) (hP : IsChartParams P) (n : ℤ) (β : ℝ) {y : Space}
    (hw : pinPlane y ≠ 0) : ContDiffAt ℝ 2 (modePhase P n β) y := by
  have hpl : ContDiffAt ℝ 2 pinPlane y := pinPlane_contDiff.contDiffAt.of_le le_top
  have hnorm : ContDiffAt ℝ 2 (fun z => ‖pinPlane z‖) y := hpl.norm ℝ hw
  have hinv : ContDiffAt ℝ 2 (fun z => ‖pinPlane z‖⁻¹) y := hnorm.inv (norm_ne_zero_iff.2 hw)
  have hu : ContDiffAt ℝ 2 (fun z => pinPlane z * ((‖pinPlane z‖⁻¹ : ℝ) : ℂ)) y :=
    hpl.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp y hinv)
  have hu0 : pinPlane y * ((‖pinPlane y‖⁻¹ : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero hw (Complex.ofReal_ne_zero.2 (inv_ne_zero (norm_ne_zero_iff.2 hw)))
  have hE : ContDiffAt ℝ 2 (fun z => Complex.exp (Complex.I * ((n * β * logPhase P z : ℝ) : ℂ))) y :=
    (Complex.contDiff_exp.contDiffAt.comp y (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp y
      (contDiffAt_const.mul ((pin_logPhase P hP).contDiffAt))))).of_le le_top
  have hall := (pin_zpow hu hu0 (n * P.m)).mul hE
  have hev : ∀ᶠ z in nhds y, pinPlane z ≠ 0 := pinPlane_contDiff.continuous.continuousAt.eventually_ne hw
  refine hall.congr_of_eventuallyEq ?_
  filter_upwards [hev] with z hz
  unfold modePhase
  rw [← pin_exp_arg _ hz, ← Complex.exp_add, ← mul_add]
  congr 2
  push_cast
  simp [angleOf, pinPlane]

private theorem pin_single (i : Fin 3) (a : ℝ) :
    EuclideanSpace.single i a = a • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  by_cases h : j = i <;> simp [h]

private theorem tame_ofComponents {w : Fin 3 → ℝ × Space → ℝ} {y : ℝ × Space} (h : ∀ i, TameAt (w i) y) :
    TameAt (fun z => ofComponents (fun i => w i z)) y := by
  have e : (fun z => ofComponents (fun i => w i z)) = fun z =>
      ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (w 0 z) +
      ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) (w 1 z) +
      ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (w 2 z) := by
    funext z
    simp only [ofComponents, ContinuousLinearMap.toSpanSingleton_apply]
    rw [pin_single 0 (w 0 z), pin_single 1 (w 1 z), pin_single 2 (w 2 z)]
  rw [e]
  exact tame_add (tame_add (tame_clm _ (h 0)) (tame_clm _ (h 1))) (tame_clm _ (h 2))

private theorem pin_tame_all {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 2 f) (q : ℝ × ℝ) : TameAt f q :=
  tame_of_contDiffAt hf.contDiffAt

private theorem pin_partial_t {G : ℝ → ℝ → ℂ} (hG : ContDiff ℝ 3 (fun p : ℝ × ℝ => G p.1 p.2)) :
    ContDiff ℝ 2 (fun p : ℝ × ℝ => deriv (fun t => G t p.2) p.1) := by
  have e : (fun p : ℝ × ℝ => deriv (fun t => G t p.2) p.1) =
      fun p => fderiv ℝ (fun q : ℝ × ℝ => G q.1 q.2) p ((1 : ℝ), (0 : ℝ)) := by
    funext p
    have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => G q.1 q.2) (p.1, p.2) :=
      (hG.differentiable (by norm_num)) _
    have h1 : HasDerivAt (fun t : ℝ => (t, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
      (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
    exact (hd.hasFDerivAt.comp_hasDerivAt p.1 h1).deriv
  rw [e]
  exact (hG.fderiv_right (by norm_num)).clm_apply contDiff_const

private theorem pin_partial_x {G : ℝ → ℝ → ℂ} (hG : ContDiff ℝ 3 (fun p : ℝ × ℝ => G p.1 p.2)) :
    ContDiff ℝ 2 (fun p : ℝ × ℝ => deriv (fun x => G p.1 x) p.2) := by
  have e : (fun p : ℝ × ℝ => deriv (fun x => G p.1 x) p.2) =
      fun p => fderiv ℝ (fun q : ℝ × ℝ => G q.1 q.2) p ((0 : ℝ), (1 : ℝ)) := by
    funext p
    have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => G q.1 q.2) (p.1, p.2) :=
      (hG.differentiable (by norm_num)) _
    have h1 : HasDerivAt (fun x : ℝ => (p.1, x)) ((0 : ℝ), (1 : ℝ)) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    exact (hd.hasFDerivAt.comp_hasDerivAt p.2 h1).deriv
  rw [e]
  exact (hG.fderiv_right (by norm_num)).clm_apply contDiff_const

private theorem pin_tderiv_mul {G F : ℝ → ℝ → ℂ} (hG : ContDiff ℝ 3 (fun p : ℝ × ℝ => G p.1 p.2))
    (hF : Differentiable ℝ (fun p : ℝ × ℝ => F p.1 p.2)) (hF2 : ∀ q, TameAt (fun p : ℝ × ℝ => F p.1 p.2) q)
    (hFt : ∀ q, TameAt (fun p : ℝ × ℝ => deriv (fun t => F t p.2) p.1) q) (q : ℝ × ℝ) :
    TameAt (fun p : ℝ × ℝ => deriv (fun t => G t p.2 * F t p.2) p.1) q := by
  have e : (fun p : ℝ × ℝ => deriv (fun t => G t p.2 * F t p.2) p.1) =
      fun p => deriv (fun t => G t p.2) p.1 * F p.1 p.2 + G p.1 p.2 * deriv (fun t => F t p.2) p.1 := by
    funext p
    have h1 : DifferentiableAt ℝ (fun t : ℝ => (t, p.2)) p.1 :=
      differentiableAt_id.prodMk (differentiableAt_const _)
    have hdF : DifferentiableAt ℝ (fun t => F t p.2) p.1 := (hF _).comp p.1 h1
    have hdG : DifferentiableAt ℝ (fun t => G t p.2) p.1 := ((hG.differentiable (by norm_num)) _).comp p.1 h1
    exact deriv_mul hdG hdF
  rw [e]
  exact tame_add (tame_mul (pin_tame_all (pin_partial_t hG) q) (hF2 q))
    (tame_mul (pin_tame_all (hG.of_le (by norm_num)) q) (hFt q))

private theorem pin_xderiv_mul {G F : ℝ → ℝ → ℂ} (hG : ContDiff ℝ 3 (fun p : ℝ × ℝ => G p.1 p.2))
    (hF : Differentiable ℝ (fun p : ℝ × ℝ => F p.1 p.2)) (hF2 : ∀ q, TameAt (fun p : ℝ × ℝ => F p.1 p.2) q)
    (hFx : ∀ q, TameAt (fun p : ℝ × ℝ => deriv (fun x => F p.1 x) p.2) q) (q : ℝ × ℝ) :
    TameAt (fun p : ℝ × ℝ => deriv (fun x => G p.1 x * F p.1 x) p.2) q := by
  have e : (fun p : ℝ × ℝ => deriv (fun x => G p.1 x * F p.1 x) p.2) =
      fun p => deriv (fun x => G p.1 x) p.2 * F p.1 p.2 + G p.1 p.2 * deriv (fun x => F p.1 x) p.2 := by
    funext p
    have h1 : DifferentiableAt ℝ (fun x : ℝ => (p.1, x)) p.2 :=
      (differentiableAt_const _).prodMk differentiableAt_id
    have hdF : DifferentiableAt ℝ (fun x => F p.1 x) p.2 := (hF _).comp p.2 h1
    have hdG : DifferentiableAt ℝ (fun x => G p.1 x) p.2 := ((hG.differentiable (by norm_num)) _).comp p.2 h1
    exact deriv_mul hdG hdF
  rw [e]
  exact tame_add (tame_mul (pin_tame_all (pin_partial_x hG) q) (hF2 q))
    (tame_mul (pin_tame_all (hG.of_le (by norm_num)) q) (hFx q))

private theorem pin_coreRatio (P : ChartParams) (hP : IsChartParams P) : ContDiff ℝ 2 (coreRatioT P) := by
  unfold coreRatioT
  refine ContDiff.div (by fun_prop) (by fun_prop) ?_
  intro t
  have hL := hP.L0_pos
  have hr := hP.rc_pos
  by_cases ht : t = 0
  · subst ht
    simp
    exact hr.ne'
  · have h1 : 0 < P.L0 ^ 2 * t ^ 2 := by positivity
    have h2 : 0 ≤ P.rc ^ 2 * (1 - t) ^ 2 := by positivity
    linarith

private theorem pin_scaleA : ContDiff ℝ 2 (fun p : ℝ × ℝ => ((p.1 * (1 - p.1) : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_fst.mul (contDiff_const.sub contDiff_fst))

private theorem pin_scaleB (P : ChartParams) (hP : IsChartParams P) (m : ℤ) (β : ℝ) :
    ContDiff ℝ 2 (fun p : ℝ × ℝ => Complex.I * (((m : ℝ) * β * coreRatioT P p.1 : ℝ) : ℂ) -
      ((2 * P.eps * p.1 : ℝ) : ℂ)) := by
  refine (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp ?_)).sub
    (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst))
  exact contDiff_const.mul ((pin_coreRatio P hP).comp contDiff_fst)

private theorem pin_weight (a e k : ℕ) :
    ContDiff ℝ 3 (fun p : ℝ × ℝ => weightPoly a e p.1 * ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ k) := by
  unfold weightPoly
  have h1 : ContDiff ℝ 3 (fun p : ℝ × ℝ => p.1 ^ a * (1 - p.1) ^ e) := by fun_prop
  have h2 : ContDiff ℝ 3 (fun p : ℝ × ℝ => 1 - p.2 ^ 2) := by fun_prop
  exact (Complex.ofRealCLM.contDiff.comp h1).mul ((Complex.ofRealCLM.contDiff.comp h2).pow k)

private theorem pin_q : ContDiff ℝ 3 (fun p : ℝ × ℝ => ((1 - p.2 ^ 2 : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (by fun_prop : ContDiff ℝ 3 (fun p : ℝ × ℝ => 1 - p.2 ^ 2))

private theorem pin_p (a e : ℕ) : ContDiff ℝ 3 (fun p : ℝ × ℝ => weightPoly a e p.1) := by
  unfold weightPoly
  have h1 : ContDiff ℝ 3 (fun p : ℝ × ℝ => p.1 ^ a * (1 - p.1) ^ e) := by fun_prop
  exact Complex.ofRealCLM.contDiff.comp h1

private theorem pin_spline {S : Spline} {a b : ℕ} {odd : Bool} (hS : IsSplineClass a b odd S) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (q : ℝ × ℝ) : TameAt (fun p : ℝ × ℝ => S.eval odd p.1 p.2) q :=
  tame_of_global ((spline_eval_contDiff S hS ha hb).differentiable (by norm_num))
    (spline_eval_localSlope S hS ha hb) q

private theorem pin_spline_t {S : Spline} {a b : ℕ} {odd : Bool} (hS : IsSplineClass a b odd S) (ha : 2 ≤ a)
    (hb : 1 ≤ b) (q : ℝ × ℝ) : TameAt (fun p : ℝ × ℝ => deriv (fun t => S.eval odd t p.2) p.1) q :=
  tame_of_global ((spline_tderiv_contDiff S hS ha hb).differentiable (by norm_num))
    (spline_tderiv_localSlope S hS ha hb) q

private theorem pin_spline_x {S : Spline} {a b : ℕ} {odd : Bool} (hS : IsSplineClass a b odd S) (ha : 1 ≤ a)
    (hb : 2 ≤ b) (q : ℝ × ℝ) : TameAt (fun p : ℝ × ℝ => deriv (fun x => S.eval odd p.1 x) p.2) q :=
  tame_of_global ((spline_xderiv_contDiff S hS ha hb).differentiable (by norm_num))
    (spline_xderiv_localSlope S hS ha hb) q


private def planeMap (j : ℤ) (w : ℂ) : ℂ :=
  ((‖w‖ ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (((j : ℝ) * Complex.arg w : ℝ) : ℂ))

private theorem planeMap_diff (j : ℤ) : Differentiable ℝ (planeMap j) :=
  (planePhase_contDiff j).differentiable (by norm_num)

private theorem planeMap_scale (j : ℤ) {s : ℝ} (hs : 0 < s) :
    (fun w => planeMap j ((s : ℂ) * w)) = fun w => ((s ^ 2 : ℝ) : ℂ) * planeMap j w := by
  funext w
  unfold planeMap
  rw [Complex.arg_real_mul w hs, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
  push_cast
  ring

private theorem planeMap_fderiv_scale (j : ℤ) {s : ℝ} (hs : 0 < s) (w : ℂ) :
    fderiv ℝ (planeMap j) ((s : ℂ) * w) = s • fderiv ℝ (planeMap j) w := by
  have hd := planeMap_diff j
  have hlin : HasFDerivAt (fun w : ℂ => (s : ℂ) * w) (s • ContinuousLinearMap.id ℝ ℂ) w := by
    have e : (fun w : ℂ => (s : ℂ) * w) = fun w => s • w := by
      funext x
      simp [Complex.real_smul]
    rw [e]
    exact (hasFDerivAt_id (𝕜 := ℝ) w).const_smul s
  have h1 : HasFDerivAt (fun w => planeMap j ((s : ℂ) * w))
      ((fderiv ℝ (planeMap j) ((s : ℂ) * w)).comp (s • ContinuousLinearMap.id ℝ ℂ)) w :=
    (hd _).hasFDerivAt.comp w hlin
  have h2 : HasFDerivAt (fun w => ((s ^ 2 : ℝ) : ℂ) * planeMap j w) ((s ^ 2) • fderiv ℝ (planeMap j) w) w := by
    have e : (fun w => ((s ^ 2 : ℝ) : ℂ) * planeMap j w) = fun w => (s ^ 2) • planeMap j w := by
      funext x
      simp [Complex.real_smul]
    rw [e]
    exact (hd w).hasFDerivAt.const_smul (s ^ 2)
  rw [planeMap_scale j hs] at h1
  have e := h1.unique h2
  have hc : (fderiv ℝ (planeMap j) ((s : ℂ) * w)).comp (s • ContinuousLinearMap.id ℝ ℂ) =
      s • fderiv ℝ (planeMap j) ((s : ℂ) * w) := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp
  rw [hc] at e
  have hs0 : s ≠ 0 := hs.ne'
  calc fderiv ℝ (planeMap j) ((s : ℂ) * w) = s⁻¹ • (s • fderiv ℝ (planeMap j) ((s : ℂ) * w)) := by
        rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    _ = s⁻¹ • (s ^ 2 • fderiv ℝ (planeMap j) w) := by rw [e]
    _ = s • fderiv ℝ (planeMap j) w := by
        rw [smul_smul]
        congr 1
        field_simp

private theorem planeMap_fderiv_zero (j : ℤ) : fderiv ℝ (planeMap j) 0 = 0 := by
  have h := planeMap_fderiv_scale j (s := 2) (by norm_num) 0
  rw [mul_zero] at h
  have h3 : (2 : ℝ) • fderiv ℝ (planeMap j) 0 - fderiv ℝ (planeMap j) 0 = 0 := by rw [← h, sub_self]
  rwa [two_smul, add_sub_cancel_right] at h3

private theorem plane_exp_arg (w : ℂ) (hw : w ≠ 0) (k : ℤ) :
    Complex.exp (Complex.I * (((k : ℝ) * Complex.arg w : ℝ) : ℂ)) = (w * ((‖w‖⁻¹ : ℝ) : ℂ)) ^ k := by
  have h1 : Complex.I * (((k : ℝ) * Complex.arg w : ℝ) : ℂ) = (k : ℂ) * ((Complex.arg w : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h1, Complex.exp_int_mul]
  congr 1
  have h2 := Complex.norm_mul_exp_arg_mul_I w
  have h3 : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hw)
  rw [Complex.ofReal_inv, eq_mul_inv_iff_mul_eq₀ h3, mul_comm]
  exact h2

private theorem plane_zpow {f : ℂ → ℂ} {y : ℂ} (hf : ContDiffAt ℝ 2 f y) (hy : f y ≠ 0) (j : ℤ) :
    ContDiffAt ℝ 2 (fun z => f z ^ j) y := by
  cases j with
  | ofNat k => simpa using hf.pow k
  | negSucc k =>
    simp only [zpow_negSucc]
    exact (hf.pow (k + 1)).inv (pow_ne_zero _ hy)

private theorem planeMap_smooth (j : ℤ) {w : ℂ} (hw : w ≠ 0) : ContDiffAt ℝ 2 (planeMap j) w := by
  have hid : ContDiffAt ℝ 2 (fun z : ℂ => z) w := contDiffAt_id
  have hnorm : ContDiffAt ℝ 2 (fun z : ℂ => ‖z‖) w := hid.norm ℝ hw
  have hinv : ContDiffAt ℝ 2 (fun z : ℂ => ‖z‖⁻¹) w := hnorm.inv (norm_ne_zero_iff.2 hw)
  have hu : ContDiffAt ℝ 2 (fun z : ℂ => z * ((‖z‖⁻¹ : ℝ) : ℂ)) w :=
    hid.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp w hinv)
  have hu0 : w * ((‖w‖⁻¹ : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero hw (Complex.ofReal_ne_zero.2 (inv_ne_zero (norm_ne_zero_iff.2 hw)))
  have hsq : ContDiffAt ℝ 2 (fun z : ℂ => ((‖z‖ ^ 2 : ℝ) : ℂ)) w :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp w (hnorm.pow 2)
  have hall := hsq.mul (plane_zpow hu hu0 j)
  refine hall.congr_of_eventuallyEq ?_
  filter_upwards [eventually_ne_nhds hw] with z hz
  unfold planeMap
  rw [plane_exp_arg z hz j]

private theorem planeSlope (j : ℤ) : LocallyLipschitz (fderiv ℝ (planeMap j)) := by
  show LocallyLipschitz (fderiv ℝ (planeMap j))
  set F := fderiv ℝ (planeMap j) with hF
  have hcont : Continuous F := (planePhase_contDiff j).continuous_fderiv (by norm_num)
  set S : Set ℂ := {w | 1 / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 1} with hS
  have hSc : IsCompact S := by
    refine (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
    · intro w hw
      simpa using hw.2
  have hloc : LocallyLipschitzOn S F := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro h
      have h1 := hw.1
      rw [h, norm_zero] at h1
      norm_num at h1
    obtain ⟨K, t, ht, hK⟩ := ((planeMap_smooth j hw0).fderiv_right (m := 1) (by norm_num)).exists_lipschitzOnWith
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hSc
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hcont.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (Metric.mem_closedBall_self zero_le_one))
  have key : ∀ z w : ℂ, ‖w‖ ≤ ‖z‖ → ‖F z - F w‖ ≤ (L + 4 * M) * ‖z - w‖ := by
    intro z w hzw
    by_cases hz : z = 0
    · have hw : w = 0 := by
        rw [hz, norm_zero] at hzw
        exact norm_le_zero_iff.1 hzw
      rw [hz, hw]
      simp
    set s := ‖z‖ with hs
    have hs0 : 0 < s := norm_pos_iff.2 hz
    set z' := ((s⁻¹ : ℝ) : ℂ) * z with hz'
    set w' := ((s⁻¹ : ℝ) : ℂ) * w with hw'
    have ez : z = (s : ℂ) * z' := by
      rw [hz', ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hs0.ne', Complex.ofReal_one, one_mul]
    have ew : w = (s : ℂ) * w' := by
      rw [hw', ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hs0.ne', Complex.ofReal_one, one_mul]
    have nz : ‖z'‖ = 1 := by
      rw [hz', norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hs0.le), ← hs,
        inv_mul_cancel₀ hs0.ne']
    have nw : ‖w'‖ = ‖w‖ / s := by
      rw [hw', norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hs0.le), inv_mul_eq_div]
    have nd : ‖z - w‖ = s * ‖z' - w'‖ := by
      rw [ez, ew, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    have nw1 : ‖w'‖ ≤ 1 := by rw [nw, div_le_one hs0]; exact hzw
    have eF : F z - F w = s • (F z' - F w') := by
      rw [ez, ew, hF, planeMap_fderiv_scale j hs0, planeMap_fderiv_scale j hs0, smul_sub]
    rw [eF, norm_smul, Real.norm_of_nonneg hs0.le, nd]
    have hfin : ‖F z' - F w'‖ ≤ (L + 4 * M) * ‖z' - w'‖ := by
      by_cases hc : 1 / 2 ≤ ‖w'‖
      · have h1 := hL.dist_le_mul z' ⟨by rw [nz]; norm_num, le_of_eq nz⟩ w' ⟨hc, nw1⟩
        rw [dist_eq_norm, dist_eq_norm] at h1
        have h2 : 0 ≤ 4 * M * ‖z' - w'‖ := by positivity
        nlinarith
      · push Not at hc
        have a1 := hM z' (by rw [Metric.mem_closedBall, dist_zero_right, nz])
        have a2 := hM w' (by rw [Metric.mem_closedBall, dist_zero_right]; exact nw1)
        have a3 : 1 / 2 ≤ ‖z' - w'‖ := by
          have := norm_sub_norm_le z' w'
          rw [nz] at this
          linarith
        have a4 : ‖F z' - F w'‖ ≤ ‖F z'‖ + ‖F w'‖ := norm_sub_le _ _
        have a5 : 0 ≤ (L : ℝ) * ‖z' - w'‖ := by positivity
        nlinarith
    calc s * ‖F z' - F w'‖ ≤ s * ((L + 4 * M) * ‖z' - w'‖) := mul_le_mul_of_nonneg_left hfin hs0.le
      _ = (L + 4 * M) * (s * ‖z' - w'‖) := by ring
  have hglob : LipschitzWith ⟨L + 4 * M, by positivity⟩ F := by
    refine LipschitzWith.of_dist_le_mul fun z w => ?_
    rw [dist_eq_norm, dist_eq_norm]
    rcases le_total ‖w‖ ‖z‖ with h | h
    · exact key z w h
    · rw [norm_sub_rev (F z), norm_sub_rev z]
      exact key w z h
  exact hglob.locallyLipschitz

private theorem tame_contDiff {f : ℝ × ℝ → ℂ} (h : ∀ y, TameAt f y) :
    ContDiff ℝ 1 f ∧ LocallyLipschitz (fderiv ℝ f) := by
  have hl : LocallyLipschitz (fderiv ℝ f) := fun y => tame_slope (h y)
  refine ⟨contDiff_one_iff_fderiv.2 ⟨fun y => ?_, hl.continuous⟩, hl⟩
  obtain ⟨r, hr, f', K, -, h1, -⟩ := h y
  exact (h1 y (Metric.mem_ball_self hr)).differentiableAt



private theorem orig_ofComponents_apply (w : Fin 3 → ℝ) (k : Fin 3) : (ofComponents w) k = w k := by
  fin_cases k <;> simp [ofComponents]

private theorem orig_weightPoly_two (a e : ℕ) (t : ℝ) :
    weightPoly (a + 2) e t = ((t ^ 2 : ℝ) : ℂ) * weightPoly a e t := by
  unfold weightPoly
  push_cast
  ring

private theorem orig_factor (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) (h0 : n ≠ 0) :
    ∃ H : ℝ → ℝ → Fin 3 → ℂ, (∀ k : Fin 3, ∀ q0 : ℝ × ℝ, TameAt (fun p : ℝ × ℝ => H p.1 p.2 k) q0) ∧
      ∀ t x k, reducedField P D n β t x k = ((1 - x ^ 2 : ℝ) : ℂ) * (((t ^ 2 : ℝ) : ℂ) * H t x k) := by
  obtain ⟨k1, hk1⟩ : ∃ k1, D.axisOrder n = k1 + 1 :=
    ⟨D.axisOrder n - 1, by have := hD.axisOrder_ge n hn h0; omega⟩
  obtain ⟨a, ha⟩ : ∃ a, D.lowOrder n = a + 2 :=
    ⟨D.lowOrder n - 2, by have := hD.lowOrder_ge n hn h0; omega⟩
  have hR := hD.waveRadial n hn h0
  have hT := hD.wavePolar n hn h0
  have cT := spline_eval_contDiff _ hT (by norm_num) (by norm_num)
  have cR := spline_eval_contDiff _ hR (by norm_num) (by norm_num)
  have dR := cR.differentiable (by norm_num)
  have eR := pin_spline hR (by norm_num) (by norm_num)
  have eT := pin_spline hT (by norm_num) (by norm_num)
  have tR := pin_spline_t hR (by norm_num) (by norm_num)
  have xT := pin_spline_x hT (by norm_num) (by norm_num)
  set ee := D.highOrder
  set R := (D.amp n).radialAmp
  set Θ := (D.amp n).polarAmp
  set q : ℝ → ℂ := fun x => ((1 - x ^ 2 : ℝ) : ℂ) with hq
  set A : ℝ → ℝ → ℂ := fun t x => weightPoly a ee t * q x ^ k1 * R.eval false t x with hA
  set B : ℝ → ℝ → ℂ := fun t x => weightPoly a ee t * q x ^ k1 * Θ.eval true t x with hB
  set C : ℝ → ℝ → ℂ := fun t x => (Complex.I / ((n * P.m : ℤ) : ℂ)) *
    (((t * (1 - t) : ℝ) : ℂ) * deriv (fun t' => A t' x) t + ((2 * (1 - t) : ℝ) : ℂ) * A t x +
      (Complex.I * ((n : ℝ) * β * coreRatioT P t : ℝ) - ((2 * P.eps * t : ℝ) : ℂ)) * A t x + 2 * A t x -
      (((D.axisOrder n + 1 : ℕ) : ℂ) * q x ^ k1 * ((-2 * x : ℝ) : ℂ) * (weightPoly a ee t * Θ.eval true t x) +
        q x ^ D.axisOrder n * (weightPoly a ee t * deriv (fun x' => Θ.eval true t x') x))) with hC
  have hW := pin_weight a ee k1
  have hAc : ∀ q0, TameAt (fun p : ℝ × ℝ => A p.1 p.2) q0 := fun q0 =>
    tame_mul (pin_tame_all (hW.of_le (by norm_num)) q0) (eR q0)
  refine ⟨fun t x => ![A t x, B t x, C t x], ?_, ?_⟩
  · intro k q0
    fin_cases k
    · refine tame_congr (hAc q0) (Filter.Eventually.of_forall fun p => ?_)
      simp
    · refine tame_congr (tame_mul (pin_tame_all (hW.of_le (by norm_num)) q0) (eT q0))
        (Filter.Eventually.of_forall fun p => ?_)
      simp [hB, hq]
    · have hAt := pin_tderiv_mul (G := fun t x => weightPoly a ee t * ((1 - x ^ 2 : ℝ) : ℂ) ^ k1)
        (F := fun t x => R.eval false t x) hW dR eR tR q0
      have hqk : ContDiff ℝ 2 (fun p : ℝ × ℝ => ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ k1 * ((-2 * p.2 : ℝ) : ℂ)) :=
        ((pin_q.of_le (by norm_num)).pow k1).mul
          (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_snd))
      have hqk0 : ContDiff ℝ 2 (fun p : ℝ × ℝ => ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ D.axisOrder n) :=
        (pin_q.of_le (by norm_num)).pow _
      have hp : ContDiff ℝ 2 (fun p : ℝ × ℝ => weightPoly a ee p.1) := (pin_p a ee).of_le (by norm_num)
      have hc3 : ContDiff ℝ 2 (fun p : ℝ × ℝ => ((2 * (1 - p.1) : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_fst))
      have hall := tame_mul (pin_tame_all (contDiff_const (c := Complex.I / ((n * P.m : ℤ) : ℂ))) q0)
        (tame_sub (tame_add (tame_add (tame_add (tame_mul (pin_tame_all pin_scaleA q0) hAt)
          (tame_mul (pin_tame_all hc3 q0) (hAc q0)))
          (tame_mul (pin_tame_all (pin_scaleB P hP n β) q0) (hAc q0)))
          (tame_mul (pin_tame_all (contDiff_const (c := (2 : ℂ))) q0) (hAc q0)))
          (tame_add (tame_mul (tame_mul (pin_tame_all (contDiff_const (c := ((D.axisOrder n + 1 : ℕ) : ℂ))) q0)
            (pin_tame_all hqk q0)) (tame_mul (pin_tame_all hp q0) (eT q0)))
            (tame_mul (pin_tame_all hqk0 q0) (tame_mul (pin_tame_all hp q0) (xT q0)))))
      refine tame_congr hall (Filter.Eventually.of_forall fun p => ?_)
      simp [hC, hA, hq, mul_assoc]
  · have hdT : ∀ t x, HasDerivAt (fun x' => Θ.eval true t x') (deriv (fun x' => Θ.eval true t x') x) x := by
      intro t x
      have h1 : DifferentiableAt ℝ (fun x' : ℝ => (t, x')) x :=
        (differentiableAt_const _).prodMk differentiableAt_id
      exact (((cT.differentiable (by norm_num)) _).comp x h1).hasDerivAt
    have hdA : ∀ t x, HasDerivAt (fun t' => A t' x) (deriv (fun t' => A t' x) t) t := by
      intro t x
      have h1 : DifferentiableAt ℝ (fun t' : ℝ => (t', x)) t :=
        differentiableAt_id.prodMk (differentiableAt_const _)
      have hAc1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => A p.1 p.2) := (hW.of_le (by norm_num)).mul cR
      exact (((hAc1.differentiable (by norm_num)) _).comp t h1).hasDerivAt
    have hdq : ∀ x : ℝ, HasDerivAt q (((-2 * x : ℝ)) : ℂ) x := by
      intro x
      have := ((hasDerivAt_pow 2 x).const_sub 1).ofReal_comp
      convert this using 1
      push_cast
      ring
    have hdt2 : ∀ t : ℝ, HasDerivAt (fun t' : ℝ => ((t' ^ 2 : ℝ) : ℂ)) (((2 * t : ℝ)) : ℂ) t := by
      intro t
      have := (hasDerivAt_pow 2 t).ofReal_comp
      convert this using 1
      push_cast
      ring
    intro t x k
    fin_cases k
    · simp only [reducedField, if_neg h0, hk1, ha, orig_weightPoly_two]
      simp [hA, hq, pow_succ]
      ring
    · simp only [reducedField, if_neg h0, hk1, ha, orig_weightPoly_two]
      simp [hB, hq, pow_succ]
      ring
    · show reducedField P D n β t x 2 = q x * (((t ^ 2 : ℝ) : ℂ) * C t x)
      have hder1 : deriv (fun t' => weightPoly (D.lowOrder n) ee t' * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
          R.eval false t' x) t =
          q x * (((2 * t : ℝ) : ℂ) * A t x + ((t ^ 2 : ℝ) : ℂ) * deriv (fun t' => A t' x) t) := by
        have e1 : (fun t' => weightPoly (D.lowOrder n) ee t' * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
            R.eval false t' x) = fun t' => q x * (((t' ^ 2 : ℝ) : ℂ) * A t' x) := by
          funext t'
          simp only [hA, hq, hk1, ha, orig_weightPoly_two, pow_succ]
          ring
        have hm : HasDerivAt (fun t' => ((t' ^ 2 : ℝ) : ℂ) * A t' x)
            (((2 * t : ℝ) : ℂ) * A t x + ((t ^ 2 : ℝ) : ℂ) * deriv (fun t' => A t' x) t) t :=
          (hdt2 t).mul (hdA t x)
        rw [e1, deriv_const_mul_field, hm.deriv]
      have hder2 : deriv (fun x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly (D.lowOrder n) ee t *
          ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * Θ.eval true t x')) x =
          q x * (((t ^ 2 : ℝ) : ℂ) * (((D.axisOrder n + 1 : ℕ) : ℂ) * q x ^ k1 * ((-2 * x : ℝ) : ℂ) *
            (weightPoly a ee t * Θ.eval true t x) +
            q x ^ D.axisOrder n * (weightPoly a ee t * deriv (fun x' => Θ.eval true t x') x))) := by
        have e2 : (fun x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly (D.lowOrder n) ee t *
            ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * Θ.eval true t x')) =
            fun x' => (((t ^ 2 : ℝ) : ℂ) * weightPoly a ee t) * (q x' ^ (D.axisOrder n + 1) * Θ.eval true t x') := by
          funext x'
          simp only [hq, ha, orig_weightPoly_two, pow_succ]
          ring
        rw [e2]
        have hh := (((hdq x).pow (D.axisOrder n + 1)).mul (hdT t x)).const_mul
          (((t ^ 2 : ℝ) : ℂ) * weightPoly a ee t)
        have hh' : HasDerivAt (fun x' => ((t ^ 2 : ℝ) : ℂ) * weightPoly a ee t *
            (q x' ^ (D.axisOrder n + 1) * Θ.eval true t x'))
            (((t ^ 2 : ℝ) : ℂ) * weightPoly a ee t * (((D.axisOrder n + 1 : ℕ) : ℂ) * q x ^ (D.axisOrder n + 1 - 1) *
              ((-2 * x : ℝ) : ℂ) * Θ.eval true t x + q x ^ (D.axisOrder n + 1) *
                deriv (fun x' => Θ.eval true t x') x)) x := hh
        rw [hh'.deriv]
        simp only [hk1, Nat.add_sub_cancel]
        push_cast
        ring
      simp only [reducedField, if_neg h0, twistedScale, radialScale, heightDeriv]
      try simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [hder1, hder2]
      have eA : weightPoly (D.lowOrder n) ee t * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * R.eval false t x =
          q x * (((t ^ 2 : ℝ) : ℂ) * A t x) := by
        simp only [hA, hq, hk1, ha, orig_weightPoly_two, pow_succ]
        ring
      rw [eA]
      simp only [hC, hq]
      push_cast
      ring

private def orProf (P : ChartParams) (n : ℤ) (β : ℝ) (K : ℝ → ℝ → Fin 3 → ℂ) (i : Fin 3)
    (p : ℝ × Space) : ℂ :=
  (((1 - p.1 / (p.1 + P.L0)) ^ (2 * P.eps) : ℝ) : ℂ) * ((((p.1 + P.L0) ^ 2)⁻¹ : ℝ) : ℂ) *
    Complex.exp (Complex.I * ((n * β * ((1 / 2) * Real.log (1 + p.1 ^ 2 / P.rc ^ 2)) : ℝ) : ℂ)) *
    (K (p.1 / (p.1 + P.L0)) (p.2 2) 0 * ((p.2 i : ℝ) : ℂ) +
      K (p.1 / (p.1 + P.L0)) (p.2 2) 1 * ((![p.2 2 * p.2 0, p.2 2 * p.2 1, -(1 - p.2 2 ^ 2)] i : ℝ) : ℂ) +
      K (p.1 / (p.1 + P.L0)) (p.2 2) 2 * ((![-(p.2 1), p.2 0, 0] i : ℝ) : ℂ))

private theorem orProf_tame (P : ChartParams) (hP : IsChartParams P) (n : ℤ) (β : ℝ)
    (K : ℝ → ℝ → Fin 3 → ℂ) (hK : ∀ k : Fin 3, ∀ q0 : ℝ × ℝ, TameAt (fun p : ℝ × ℝ => K p.1 p.2 k) q0)
    (i : Fin 3) (p : ℝ × Space) (hp : 0 ≤ p.1) : TameAt (orProf P n β K i) p := by
  have hL := hP.L0_pos
  have hrc := hP.rc_pos
  have hne : p.1 + P.L0 ≠ 0 := by linarith
  have hr : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => q.1) p := contDiffAt_fst
  have hτ : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => q.1 / (q.1 + P.L0)) p := hr.div (hr.add contDiffAt_const) hne
  have hs : 1 - p.1 / (p.1 + P.L0) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    rw [eq_comm, div_eq_one_iff_eq hne] at h
    linarith
  have hdec : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => (1 - q.1 / (q.1 + P.L0)) ^ (2 * P.eps)) p :=
    (contDiffAt_const.sub hτ).rpow_const_of_ne hs
  have hinv : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => ((q.1 + P.L0) ^ 2)⁻¹) p :=
    ((hr.add contDiffAt_const).pow 2).inv (pow_ne_zero 2 hne)
  have hlog : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => Real.log (1 + q.1 ^ 2 / P.rc ^ 2)) p := by
    refine (contDiffAt_const.add ((hr.pow 2).div_const _)).log ?_
    positivity
  have hu : ∀ j : Fin 3, ContDiffAt ℝ ⊤ (fun q : ℝ × Space => q.2 j) p := fun j =>
    ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd).contDiffAt
  have hKc : ∀ k : Fin 3, TameAt (fun q : ℝ × Space => K (q.1 / (q.1 + P.L0)) (q.2 2) k) p := fun k =>
    tame_comp (g := fun r : ℝ × ℝ => K r.1 r.2 k) (Φ := fun q : ℝ × Space => (q.1 / (q.1 + P.L0), q.2 2))
      (hK k _) (tame_of_contDiffAt ((hτ.prodMk (hu 2)).of_le le_top))
  have hc : ∀ f : ℝ × Space → ℝ, ContDiffAt ℝ ⊤ f p → TameAt (fun q => (f q : ℂ)) p :=
    fun f hf => tame_of_contDiffAt ((Complex.ofRealCLM.contDiff.contDiffAt.comp p hf).of_le le_top)
  have hE : TameAt (fun q : ℝ × Space =>
      Complex.exp (Complex.I * ((n * β * ((1 / 2) * Real.log (1 + q.1 ^ 2 / P.rc ^ 2)) : ℝ) : ℂ))) p :=
    tame_of_contDiffAt ((Complex.contDiff_exp.contDiffAt.comp p (contDiffAt_const.mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiffAt_const.mul (contDiffAt_const.mul hlog))))).of_le le_top)
  have hv1 : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => ![q.2 2 * q.2 0, q.2 2 * q.2 1, -(1 - q.2 2 ^ 2)] i) p := by
    fin_cases i
    · simpa using (hu 2).mul (hu 0)
    · simpa using (hu 2).mul (hu 1)
    · simpa using (contDiffAt_const.sub ((hu 2).pow 2)).neg
  have hv2 : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => ![-(q.2 1), q.2 0, 0] i) p := by
    fin_cases i
    · simpa using (hu 1).neg
    · simpa using hu 0
    · simpa using (contDiffAt_const : ContDiffAt ℝ ⊤ (fun _ : ℝ × Space => (0 : ℝ)) p)
  exact tame_mul (tame_mul (tame_mul (hc _ hdec) (hc _ hinv)) hE)
    (tame_add (tame_add (tame_mul (hKc 0) (hc _ (hu i))) (tame_mul (hKc 1) (hc _ hv1)))
      (tame_mul (hKc 2) (hc _ hv2)))

private theorem orig_one_sub_height (y : Space) (hy : y ≠ 0) :
    1 - heightRatio y ^ 2 = ‖pinPlane y‖ ^ 2 / ‖y‖ ^ 2 := by
  have hn : ‖y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hy)
  have e1 : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [sq_abs]
  have e2 : ‖pinPlane y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [pinPlane]
    ring
  unfold heightRatio
  rw [div_pow, e2]
  field_simp
  linarith

private theorem orig_phase_factor (P : ChartParams) (hP : IsChartParams P) (n : ℤ) (β : ℝ) (y : Space)
    (hy : y ≠ 0) (c : ℂ) :
    modePhase P n β y * (((1 - heightRatio y ^ 2 : ℝ) : ℂ) * (((chartT P y ^ 2 : ℝ) : ℂ) * c)) =
      ((‖pinPlane y‖ ^ 2 : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * Complex.arg (pinPlane y) : ℝ) : ℂ)) *
        ((((‖y‖ + P.L0) ^ 2)⁻¹ : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((n * β * ((1 / 2) * Real.log (1 + ‖y‖ ^ 2 / P.rc ^ 2)) : ℝ) : ℂ)) * c := by
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have hL : ‖y‖ + P.L0 ≠ 0 := by have := hP.L0_pos; positivity
  rw [orig_one_sub_height y hy]
  unfold modePhase chartT logPhase
  have ea : Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * angleOf y +
      n * β * ((1 / 2) * Real.log (1 + ‖y‖ ^ 2 / P.rc ^ 2)) : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * Complex.arg (pinPlane y) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((n * β * ((1 / 2) * Real.log (1 + ‖y‖ ^ 2 / P.rc ^ 2)) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← mul_add]
    congr 2
    push_cast
    simp [angleOf, pinPlane]
  rw [ea]
  have hn' : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  have hL' : ((‖y‖ : ℂ) + (P.L0 : ℂ)) ≠ 0 := by exact_mod_cast hL
  push_cast
  field_simp

private theorem orig_key (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (β : ℝ) (n : ℤ)
    (K : ℝ → ℝ → Fin 3 → ℂ)
    (hRK : ∀ t x k, reducedField P D n β t x k = ((1 - x ^ 2 : ℝ) : ℂ) * (((t ^ 2 : ℝ) : ℂ) * K t x k))
    (i : Fin 3) (y : Space) (hy : y ≠ 0) :
    (modeFieldOf P D β n y) i = (planeMap (n * P.m) (pinPlane y) * orProf P n β K i (‖y‖, ‖y‖⁻¹ • y)).re := by
  rw [modeFieldOf, orig_ofComponents_apply]
  congr 1
  have hsm : ∀ j : Fin 3, (‖y‖⁻¹ • y) j = y j / ‖y‖ := by
    intro j
    rw [PiLp.smul_apply, smul_eq_mul, div_eq_inv_mul]
  have hph := fun c => orig_phase_factor P hP n β y hy c
  simp only [orProf, hsm, hRK]
  have e2 : ‖y‖ / (‖y‖ + P.L0) = chartT P y := rfl
  have e3 : y 2 / ‖y‖ = heightRatio y := rfl
  have e1 : ((1 - chartT P y) ^ (2 * P.eps)) = decayFactor P y := rfl
  rw [e2, e3, e1]
  linear_combination (norm := skip)
    ((decayFactor P y : ℂ) * (radialVec y i : ℂ)) * hph (K (chartT P y) (heightRatio y) 0) +
      ((decayFactor P y : ℂ) * (polarVecQ y i : ℂ)) * hph (K (chartT P y) (heightRatio y) 1) +
      ((decayFactor P y : ℂ) * (azimVecQ y i : ℂ)) * hph (K (chartT P y) (heightRatio y) 2)
  fin_cases i <;> simp [radialVec, polarVecQ, azimVecQ, qOf, planeMap] <;> push_cast <;> ring

private def scaledWave (P : ChartParams) (n : ℤ) (β : ℝ) (K : ℝ → ℝ → Fin 3 → ℂ) (p : ℝ × Space) : Space :=
  ofComponents (fun i => (planeMap (n * P.m) (pinPlane p.2) *
    orProf P n β K i (p.1 * ‖p.2‖, ‖p.2‖⁻¹ • p.2)).re)

private theorem tame_region {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f : E → G} {y : E} (h : TameAt f y) :
    ∃ U ∈ nhds y, (∀ q ∈ U, DifferentiableAt ℝ f q) ∧ ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ f) U := by
  obtain ⟨r, hr, f', K, hK0, h1, h2⟩ := h
  refine ⟨Metric.ball y r, Metric.ball_mem_nhds y hr, fun z hz => (h1 z hz).differentiableAt, ⟨K, hK0⟩,
    LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_⟩
  rw [(h1 z hz).fderiv, (h1 w hw).fderiv, dist_eq_norm, dist_eq_norm]
  exact h2 z hz w hw

private theorem scaleT_norm (s : ℝ) (hs : 0 < s) :
    ‖(0 : Space →L[ℝ] ℝ).prod (s⁻¹ • ContinuousLinearMap.id ℝ Space)‖ ≤ s⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hs.le) (fun v => ?_)
  rw [ContinuousLinearMap.prod_apply, Prod.norm_def]
  have ha : |s| = s := abs_of_pos hs
  simp [norm_smul, ha]
  positivity

private theorem scaled_hasFDerivAt {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : Space → G} {F : ℝ × Space → G}
    (hscale : ∀ s : ℝ, 0 < s → ∀ v : Space, v ≠ 0 → f (s • v) = (s ^ 2) • F (s, v))
    {s : ℝ} (hs : 0 < s) {w : Space} (hw : w ≠ 0) (hd : DifferentiableAt ℝ F (s, s⁻¹ • w)) :
    HasFDerivAt f ((s ^ 2) • (fderiv ℝ F (s, s⁻¹ • w)).comp
      ((0 : Space →L[ℝ] ℝ).prod (s⁻¹ • ContinuousLinearMap.id ℝ Space))) w := by
  have hT : HasFDerivAt (fun w' : Space => (s, s⁻¹ • w'))
      ((0 : Space →L[ℝ] ℝ).prod (s⁻¹ • ContinuousLinearMap.id ℝ Space)) w :=
    (hasFDerivAt_const s w).prodMk ((hasFDerivAt_id w).const_smul s⁻¹)
  have h1 := (hd.hasFDerivAt.comp w hT).const_smul (s ^ 2)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne.mem_nhds hw] with w' hw'
  have hv : s⁻¹ • w' ≠ 0 := smul_ne_zero (inv_ne_zero hs.ne') hw'
  have := hscale s hs (s⁻¹ • w') hv
  rw [smul_inv_smul₀ hs.ne'] at this
  rw [this]
  rfl

private theorem scaled_fderiv_slopeBound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : Space → G} {F : ℝ × Space → G} {ρ : ℝ} (hρ : 0 < ρ) (hf0 : f 0 = 0)
    (hscale : ∀ s : ℝ, 0 < s → ∀ v : Space, v ≠ 0 → f (s • v) = (s ^ 2) • F (s, v))
    (hF : ∀ p ∈ Set.Icc 0 ρ ×ˢ (Metric.closedBall (0 : Space) 1 \ Metric.ball 0 (1 / 2)),
      ∃ U ∈ nhds p, (∀ q ∈ U, DifferentiableAt ℝ F q) ∧ ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ F) U) :
    (∀ y ∈ Metric.ball (0 : Space) ρ, DifferentiableAt ℝ f y) ∧
      ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ f) (Metric.ball 0 ρ) := by
  set C : Set (ℝ × Space) := Set.Icc 0 ρ ×ˢ (Metric.closedBall (0 : Space) 1 \ Metric.ball 0 (1 / 2)) with hC
  have hCc : IsCompact C := isCompact_Icc.prod ((isCompact_closedBall _ _).diff Metric.isOpen_ball)
  have hdiff : ∀ p ∈ C, DifferentiableAt ℝ F p := fun p hp => by
    obtain ⟨U, hU, hd, -⟩ := hF p hp
    exact hd p (mem_of_mem_nhds hU)
  have hloc : LocallyLipschitzOn C (fderiv ℝ F) := by
    intro p hp
    obtain ⟨U, hU, -, K, hK⟩ := hF p hp
    exact ⟨K, U, mem_nhdsWithin_of_mem_nhds hU, hK⟩
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hCc
  obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn hL.continuousOn
  obtain ⟨N, hN⟩ := hCc.exists_bound_of_continuousOn
    (fun p hp => (hdiff p hp).continuousAt.continuousWithinAt : ContinuousOn F C)
  have hM0 : 0 ≤ M := by
    have h := hM (0, EuclideanSpace.single 0 1) ⟨⟨le_rfl, hρ.le⟩, by simp [Metric.mem_closedBall, Metric.mem_ball]; norm_num⟩
    exact (norm_nonneg _).trans h
  have memC : ∀ s w, 0 < s → s ≤ ρ → 1 / 2 * s ≤ ‖w‖ → ‖w‖ ≤ s → (s, s⁻¹ • w) ∈ C := by
    intro s w hs hsρ h1 h2
    refine ⟨⟨hs.le, hsρ⟩, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]
      rw [inv_mul_le_iff₀ hs]
      linarith
    · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs), not_lt]
      rw [le_inv_mul_iff₀ hs]
      linarith
  have hd0 : HasFDerivAt f (0 : Space →L[ℝ] G) 0 := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have hbig : (fun h : Space => f (0 + h) - f 0 - (0 : Space →L[ℝ] G) h) =O[nhds 0] fun h => ‖h‖ ^ 2 := by
      refine Asymptotics.IsBigO.of_bound N ?_
      filter_upwards [Metric.ball_mem_nhds (0 : Space) hρ] with h hh
      rw [Metric.mem_ball, dist_zero_right] at hh
      simp only [zero_add, hf0, sub_zero, zero_apply, norm_pow, norm_norm]
      by_cases h0 : h = 0
      · simp [h0, hf0]
      have hs : 0 < ‖h‖ := norm_pos_iff.2 h0
      have e := hscale ‖h‖ hs (‖h‖⁻¹ • h) (smul_ne_zero (inv_ne_zero hs.ne') h0)
      rw [smul_inv_smul₀ hs.ne'] at e
      rw [e, norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos hs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hN _ (memC _ _ hs hh.le (by linarith) le_rfl)) (by positivity)
    exact hbig.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by norm_num))
  have hat : ∀ s w, 0 < s → s ≤ ρ → 1 / 2 * s ≤ ‖w‖ → ‖w‖ ≤ s →
      fderiv ℝ f w = (s ^ 2) • (fderiv ℝ F (s, s⁻¹ • w)).comp
        ((0 : Space →L[ℝ] ℝ).prod (s⁻¹ • ContinuousLinearMap.id ℝ Space)) := by
    intro s w hs hsρ h1 h2
    have hw : w ≠ 0 := by
      intro h; rw [h, norm_zero] at h1; linarith
    exact (scaled_hasFDerivAt hscale hs hw (hdiff _ (memC s w hs hsρ h1 h2))).fderiv
  have hbound : ∀ w, ‖w‖ < ρ → ‖fderiv ℝ f w‖ ≤ M * ‖w‖ := by
    intro w hw
    by_cases h0 : w = 0
    · rw [h0, hd0.fderiv]; simp
    have hs : 0 < ‖w‖ := norm_pos_iff.2 h0
    rw [hat ‖w‖ w hs hw.le (by linarith) le_rfl, norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos hs]
    calc ‖w‖ ^ 2 * ‖(fderiv ℝ F (‖w‖, ‖w‖⁻¹ • w)).comp
          ((0 : Space →L[ℝ] ℝ).prod (‖w‖⁻¹ • ContinuousLinearMap.id ℝ Space))‖
        ≤ ‖w‖ ^ 2 * (M * ‖w‖⁻¹) := by
          gcongr
          refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
          exact mul_le_mul (hM _ (memC _ _ hs hw.le (by linarith) le_rfl)) (scaleT_norm _ hs) (norm_nonneg _) hM0
      _ = M * ‖w‖ := by field_simp
  have key : ∀ y z, ‖y‖ < ρ → ‖z‖ ≤ ‖y‖ → ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ (L + 4 * M) * ‖y - z‖ := by
    intro y z hy hzy
    by_cases hfar : ‖y‖ ≤ 2 * ‖y - z‖
    · calc ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ ‖fderiv ℝ f y‖ + ‖fderiv ℝ f z‖ := norm_sub_le _ _
        _ ≤ M * ‖y‖ + M * ‖z‖ := add_le_add (hbound y hy) (hbound z (lt_of_le_of_lt hzy hy))
        _ ≤ 4 * M * ‖y - z‖ := by nlinarith
        _ ≤ (L + 4 * M) * ‖y - z‖ := by gcongr; simp
    · push Not at hfar
      have hs : 0 < ‖y‖ := by have := norm_nonneg (y - z); linarith
      have hz1 : 1 / 2 * ‖y‖ ≤ ‖z‖ := by
        have := norm_sub_norm_le y z
        linarith
      rw [hat ‖y‖ y hs hy.le (by linarith) le_rfl, hat ‖y‖ z hs hy.le hz1 hzy, ← smul_sub,
        ← ContinuousLinearMap.sub_comp, norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos hs]
      have hyC := memC _ y hs hy.le (by linarith) le_rfl
      have hzC := memC _ z hs hy.le hz1 hzy
      have hLd := hL.dist_le_mul _ hyC _ hzC
      rw [dist_eq_norm, dist_eq_norm, Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero, ← smul_sub,
        norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)] at hLd
      have hmax : max 0 (‖y‖⁻¹ * ‖y - z‖) = ‖y‖⁻¹ * ‖y - z‖ := max_eq_right (by positivity)
      rw [hmax] at hLd
      calc ‖y‖ ^ 2 * ‖(fderiv ℝ F (‖y‖, ‖y‖⁻¹ • y) - fderiv ℝ F (‖y‖, ‖y‖⁻¹ • z)).comp
            ((0 : Space →L[ℝ] ℝ).prod (‖y‖⁻¹ • ContinuousLinearMap.id ℝ Space))‖
          ≤ ‖y‖ ^ 2 * ((L * (‖y‖⁻¹ * ‖y - z‖)) * ‖y‖⁻¹) := by
            gcongr
            exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul hLd (scaleT_norm _ hs) (norm_nonneg _) (by positivity))
        _ = L * ‖y - z‖ := by field_simp
        _ ≤ (L + 4 * M) * ‖y - z‖ := by gcongr; linarith
  refine ⟨fun y hy => ?_, Real.toNNReal (L + 4 * M), LipschitzOnWith.of_dist_le' fun y hy z hz => ?_⟩
  · rw [Metric.mem_ball, dist_zero_right] at hy
    by_cases h0 : y = 0
    · rw [h0]; exact hd0.differentiableAt
    have hs : 0 < ‖y‖ := norm_pos_iff.2 h0
    exact (scaled_hasFDerivAt hscale hs h0 (hdiff _ (memC _ y hs hy.le (by linarith) le_rfl))).differentiableAt
  · rw [Metric.mem_ball, dist_zero_right] at hy hz
    rw [dist_eq_norm, dist_eq_norm]
    rcases le_total ‖z‖ ‖y‖ with h | h
    · exact key y z hy h
    · rw [← norm_neg, neg_sub, ← norm_neg (y - z), neg_sub]
      exact key z y hz h

theorem modeFieldOf_scaledProfile_wave (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) (h0 : n ≠ 0) :
    ∃ F : ℝ × Space → Space, ∃ ρ : ℝ, 0 < ρ ∧ modeFieldOf P D β n 0 = 0 ∧
      (∀ s : ℝ, 0 < s → ∀ v : Space, v ≠ 0 → modeFieldOf P D β n (s • v) = (s ^ 2) • F (s, v)) ∧
      ∀ p ∈ Set.Icc 0 ρ ×ˢ (Metric.closedBall (0 : Space) 1 \ Metric.ball 0 (1 / 2)),
        ∃ U ∈ nhds p, (∀ q ∈ U, DifferentiableAt ℝ F q) ∧ ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ F) U := by
  obtain ⟨K, hK, hRK⟩ := orig_factor P hP hD β n hn h0
  have hf0 : modeFieldOf P D β n 0 = 0 := by
    have hz : ∀ k, reducedField P D n β (chartT P 0) (heightRatio 0) k = 0 := by
      intro k
      rw [hRK]
      simp [chartT]
    refine PiLp.ext fun i => ?_
    rw [modeFieldOf, orig_ofComponents_apply]
    simp [hz]
  have hsc : ∀ s : ℝ, 0 < s → ∀ v : Space, v ≠ 0 →
      modeFieldOf P D β n (s • v) = (s ^ 2) • scaledWave P n β K (s, v) := by
    intro s hs v hv
    have hsv : s • v ≠ 0 := smul_ne_zero hs.ne' hv
    have hnorm : ‖s • v‖ = s * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg hs.le]
    have hdir : ‖s • v‖⁻¹ • (s • v) = ‖v‖⁻¹ • v := by
      rw [hnorm, smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hs.ne', mul_one]
    have hpl : pinPlane (s • v) = (s : ℂ) * pinPlane v := by
      apply Complex.ext <;> simp [pinPlane]
    refine PiLp.ext fun i => ?_
    rw [orig_key P hP D β n K hRK i _ hsv, hdir, hnorm, hpl, congrFun (planeMap_scale (n * P.m) hs) (pinPlane v)]
    simp only [scaledWave, PiLp.smul_apply, smul_eq_mul, orig_ofComponents_apply]
    rw [mul_assoc, Complex.re_ofReal_mul]
  have htame : ∀ p : ℝ × Space, 0 ≤ p.1 → p.2 ≠ 0 → TameAt (scaledWave P n β K) p := by
    intro p hp1 hp2
    have hn' : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => ‖q.2‖) p := (contDiffAt_norm ℝ hp2).comp p contDiffAt_snd
    have hΛ : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => (q.1 * ‖q.2‖, ‖q.2‖⁻¹ • q.2)) p :=
      (contDiffAt_fst.mul hn').prodMk ((hn'.inv (norm_ne_zero_iff.2 hp2)).smul contDiffAt_snd)
    have hpl : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => pinPlane q.2) p :=
      pinPlane_contDiff.contDiffAt.comp p contDiffAt_snd
    have hA : TameAt (fun q : ℝ × Space => planeMap (n * P.m) (pinPlane q.2)) p :=
      tame_comp (g := planeMap (n * P.m)) (Φ := fun q : ℝ × Space => pinPlane q.2)
        (tame_of_global (planeMap_diff _) (planeSlope _) _) (tame_of_contDiffAt (hpl.of_le le_top))
    have hB : ∀ i, TameAt (fun q : ℝ × Space => orProf P n β K i (q.1 * ‖q.2‖, ‖q.2‖⁻¹ • q.2)) p := fun i =>
      tame_comp (g := orProf P n β K i) (Φ := fun q : ℝ × Space => (q.1 * ‖q.2‖, ‖q.2‖⁻¹ • q.2))
        (orProf_tame P hP n β K hK i _ (mul_nonneg hp1 (norm_nonneg _))) (tame_of_contDiffAt (hΛ.of_le le_top))
    exact tame_ofComponents (w := fun i q => (planeMap (n * P.m) (pinPlane q.2) *
      orProf P n β K i (q.1 * ‖q.2‖, ‖q.2‖⁻¹ • q.2)).re) fun i => by
        have := tame_clm Complex.reCLM (tame_mul hA (hB i))
        simpa only [Complex.reCLM_apply] using this
  refine ⟨scaledWave P n β K, 1, one_pos, hf0, hsc, fun p hp => tame_region (htame p hp.1.1 ?_)⟩
  intro h
  apply hp.2.2
  rw [h]
  exact Metric.mem_ball_self (by norm_num)
private theorem divd_pos_list_lower (L : List ℝ) (h : ∀ b ∈ L, 0 < b) : ∃ c > 0, ∀ b ∈ L, c ≤ b := by
  induction L with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons b L ih =>
    obtain ⟨c, hc, hcL⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨min b c, lt_min (h b (by simp)) hc, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hcL x hx)

private theorem divd_atFirst_mul_X (c : ℂ) (p : MvPolynomial (Fin 2) ℂ) (i : Fin 2) :
    atFirst c (p * MvPolynomial.X i) =
      atFirst c p * (if i = 0 then MvPolynomial.C c else MvPolynomial.X 1) := by
  simp [atFirst]

private theorem divd_sub_atFirst_dvd (R : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.X 0 ∣ R - atFirst 0 R := by
  induction R using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp [atFirst]⟩
  | add p r hp hr =>
    have e : p + r - atFirst 0 (p + r) = (p - atFirst 0 p) + (r - atFirst 0 r) := by
      simp only [atFirst, map_add]
      ring
    rw [e]
    exact dvd_add hp hr
  | mul_X p i hp =>
    obtain ⟨q, hq⟩ := hp
    rw [divd_atFirst_mul_X]
    fin_cases i
    · exact ⟨p, by simp; ring⟩
    · refine ⟨q * MvPolynomial.X 1, ?_⟩
      have e : p * MvPolynomial.X 1 - atFirst 0 p * MvPolynomial.X 1 = (p - atFirst 0 p) * MvPolynomial.X 1 := by ring
      simp only [Fin.mk_one, one_ne_zero, if_false]
      rw [e, hq]
      ring

private theorem divd_atFirst_add (c : ℂ) (p q : MvPolynomial (Fin 2) ℂ) :
    atFirst c (p + q) = atFirst c p + atFirst c q := by
  simp [atFirst]

private theorem divd_atSecond_add (c : ℂ) (p q : MvPolynomial (Fin 2) ℂ) :
    atSecond c (p + q) = atSecond c p + atSecond c q := by
  simp [atSecond]

private theorem divd_atSecond_X0_mul (c : ℂ) (q : MvPolynomial (Fin 2) ℂ) :
    atSecond c (MvPolynomial.X 0 * q) = MvPolynomial.X 0 * atSecond c q := by
  simp [atSecond]

private theorem divd_atFirst_zero (c : ℂ) : atFirst c (0 : MvPolynomial (Fin 2) ℂ) = 0 := by
  simp [atFirst]

private theorem divd_xDeriv_add (o : ℕ) (p q : MvPolynomial (Fin 2) ℂ) :
    xDeriv o (p + q) = xDeriv o p + xDeriv o q := by
  induction o generalizing p q with
  | zero => rfl
  | succ o ih =>
    simp only [xDeriv, Function.iterate_succ_apply] at ih ⊢
    rw [map_add, ih]

private theorem divd_xDeriv_X0_mul (o : ℕ) (q : MvPolynomial (Fin 2) ℂ) :
    xDeriv o (MvPolynomial.X 0 * q) = MvPolynomial.X 0 * xDeriv o q := by
  induction o generalizing q with
  | zero => rfl
  | succ o ih =>
    simp only [xDeriv, Function.iterate_succ_apply] at ih ⊢
    have : MvPolynomial.pderiv 1 (MvPolynomial.X 0 * q) = MvPolynomial.X 0 * MvPolynomial.pderiv 1 q := by
      rw [Derivation.leibniz, MvPolynomial.pderiv_X_of_ne (by decide)]
      simp
    rw [this, ih]

private theorem divd_pderiv_atFirst (c : ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.pderiv 1 (atFirst c P) = atFirst c (MvPolynomial.pderiv 1 P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [atFirst]
  | add p r hp hr => rw [divd_atFirst_add, map_add, map_add, divd_atFirst_add, hp, hr]
  | mul_X p i hp =>
    rw [divd_atFirst_mul_X, Derivation.leibniz, Derivation.leibniz, divd_atFirst_add]
    unfold atFirst at hp ⊢
    fin_cases i <;> simp [MvPolynomial.pderiv_X, hp]

private theorem divd_xDeriv_atFirst (c : ℂ) (o : ℕ) (P : MvPolynomial (Fin 2) ℂ) :
    xDeriv o (atFirst c P) = atFirst c (xDeriv o P) := by
  induction o generalizing P with
  | zero => rfl
  | succ o ih =>
    simp only [xDeriv, Function.iterate_succ_apply] at ih ⊢
    rw [divd_pderiv_atFirst, ih]

private theorem divd_atSecond_atFirst (c d : ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    atSecond d (atFirst c P) = atFirst c (atSecond d P) := by
  unfold atFirst atSecond
  rw [MvPolynomial.bind₁_bind₁, MvPolynomial.bind₁_bind₁]
  refine congrArg (fun f => MvPolynomial.bind₁ f P) (funext fun i => ?_)
  fin_cases i <;> simp

private theorem divd_split (o : ℕ) (d : ℂ) (P Q : MvPolynomial (Fin 2) ℂ)
    (h : P = atFirst 0 P + MvPolynomial.X 0 * Q) :
    atSecond d (xDeriv o P) - atFirst 0 (atSecond d (xDeriv o P)) =
      MvPolynomial.X 0 * atSecond d (xDeriv o Q) := by
  have e : atSecond d (xDeriv o P) = atSecond d (xDeriv o (atFirst 0 P)) +
      MvPolynomial.X 0 * atSecond d (xDeriv o Q) := by
    conv_lhs => rw [h]
    rw [divd_xDeriv_add, divd_xDeriv_X0_mul, divd_atSecond_add, divd_atSecond_X0_mul]
  have e2 : atFirst 0 (atSecond d (xDeriv o P)) = atSecond d (xDeriv o (atFirst 0 P)) := by
    rw [divd_xDeriv_atFirst, divd_atSecond_atFirst]
  rw [e2, e]
  ring

private theorem spline_firstRow_split (S : Spline) {a b : ℕ} {odd : Bool} (hS : IsSplineClass a b odd S) :
    ∃ T : Spline, IsSplineClass 2 b odd T ∧ ∃ t1 > 0, ∀ t < t1, ∀ x : ℝ,
      S.eval odd t x = S.eval odd 0 x + (t : ℂ) * T.eval odd t x := by
  obtain ⟨-, pt, ct, -⟩ := mesh_facts _ hS.mesh.t_sorted hS.mesh.t_first hS.mesh.t_last
  obtain ⟨c, hc, hcL⟩ := divd_pos_list_lower _ pt
  have hQ : ∀ j, ∃ Q : MvPolynomial (Fin 2) ℂ, S.piece 0 j = atFirst 0 (S.piece 0 j) + MvPolynomial.X 0 * Q := by
    intro j
    obtain ⟨Q, hQ⟩ := divd_sub_atFirst_dvd (S.piece 0 j)
    exact ⟨Q, by rw [← hQ]; ring⟩
  choose Q hQ using hQ
  have hi : ∀ t < c, cellIndex S.mesh.tBreaks t = 0 := by
    intro t ht
    unfold cellIndex
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro y hy
    simpa using lt_of_lt_of_le ht (hcL y hy)
  have hT0 : ∀ t, cellIndex [0, 1] t = 0 := fun t => by simp [cellIndex]
  have hct : 0 < cellCount S.mesh.tBreaks := by omega
  have hX : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ≠ 0 := MvPolynomial.X_ne_zero 0
  refine ⟨⟨⟨[0, 1], S.mesh.xBreaks⟩, fun _ j => Q j⟩, ?_, c, hc, ?_⟩
  · refine ⟨⟨by simp, hS.mesh.x_sorted, by simp, by simp, hS.mesh.x_first, hS.mesh.x_last⟩, ?_, ?_, ?_⟩
    · intro i hi1 hi2
      simp [cellCount] at hi2
      omega
    · intro j hj1 hj2 i hi o ho
      have h1 := divd_split o (S.mesh.xBreaks.getD j 0 : ℂ) _ _ (hQ (j - 1))
      have h2 := divd_split o (S.mesh.xBreaks.getD j 0 : ℂ) _ _ (hQ j)
      rw [hS.x_joins j hj1 hj2 0 hct o ho, h2] at h1
      exact (mul_left_cancel₀ hX h1).symm
    · intro i hi o ho hpar
      have h1 := divd_split o 0 _ _ (hQ 0)
      rw [hS.parity 0 hct o ho hpar, divd_atFirst_zero, sub_zero] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left hX
  · intro t ht x
    simp only [Spline.eval, Spline.evalHalf, hT0, hi t ht, hi 0 hc]
    have e := congrArg (fun W => evP W (t, |x|)) (hQ (cellIndex S.mesh.xBreaks |x|))
    change _ * evP _ (t, |x|) = _ * evP _ (0, |x|) + _ * (_ * evP _ (t, |x|))
    rw [e]
    have e1 := evP_atFirst 0 (S.piece 0 (cellIndex S.mesh.xBreaks |x|)) (t, |x|)
    rw [Complex.ofReal_zero] at e1
    have e2 : evP (MvPolynomial.X 0 * Q (cellIndex S.mesh.xBreaks |x|)) (t, |x|) =
        (t : ℂ) * evP (Q (cellIndex S.mesh.xBreaks |x|)) (t, |x|) := by
      simp [evP]
    rw [show evP (atFirst 0 (S.piece 0 (cellIndex S.mesh.xBreaks |x|)) + MvPolynomial.X 0 * Q (cellIndex S.mesh.xBreaks |x|)) (t, |x|) = evP (atFirst 0 (S.piece 0 (cellIndex S.mesh.xBreaks |x|))) (t, |x|) + evP (MvPolynomial.X 0 * Q (cellIndex S.mesh.xBreaks |x|)) (t, |x|) by simp [evP], e1, e2]
    ring

private theorem weightPoly_one_split (e : ℕ) (t : ℝ) : weightPoly 1 e t = (t : ℂ) * weightPoly 0 e t := by
  unfold weightPoly
  push_cast
  ring

private theorem divd_stream_zero (P : ChartParams) {e : ℕ} {D : FieldData} (hD : IsFieldData P e D)
    (hn : (0 : ℤ) ∈ D.modes) (x : ℝ) :
    (D.amp 0).streamAmp.eval true 0 x = ((D.guardStream * x : ℝ) : ℂ) := by
  have hS := (hD.meanStream hn).1
  obtain ⟨-, pt, -, -⟩ := mesh_facts _ hS.mesh.t_sorted hS.mesh.t_first hS.mesh.t_last
  have ht : cellIndex (D.amp 0).streamAmp.mesh.tBreaks 0 = 0 := glueIdx_zero _ pt
  have hj : cellIndex (D.amp 0).streamAmp.mesh.xBreaks |x| < cellCount (D.amp 0).streamAmp.mesh.xBreaks := by
    obtain ⟨-, -, cx, -⟩ := mesh_facts _ hS.mesh.x_sorted hS.mesh.x_first hS.mesh.x_last
    have := glueIdx_le (((D.amp 0).streamAmp.mesh.xBreaks.drop 1).dropLast) |x|
    change glueIdx _ |x| < _
    omega
  have hg := hD.guard_stream hn _ hj
  have hv : (D.amp 0).streamAmp.evalHalf 0 |x| = ((D.guardStream * |x| : ℝ) : ℂ) := by
    unfold Spline.evalHalf
    rw [ht]
    have h1 : evP (atFirst ((0 : ℝ) : ℂ) ((D.amp 0).streamAmp.piece 0
        (cellIndex (D.amp 0).streamAmp.mesh.xBreaks |x|))) (0, |x|) =
        evP ((D.amp 0).streamAmp.piece 0 (cellIndex (D.amp 0).streamAmp.mesh.xBreaks |x|)) (0, |x|) :=
      evP_atFirst 0 _ (0, |x|)
    rw [Complex.ofReal_zero, hg] at h1
    change evP _ (0, |x|) = _
    rw [← h1]
    simp [evP]
  unfold Spline.eval
  rw [hv]
  rcases lt_or_ge x 0 with hx | hx
  · rw [if_pos (by simp [hx]), abs_of_neg hx]
    push_cast
    ring
  · rw [if_neg (by simp [not_lt.2 hx]), abs_of_nonneg hx, one_mul]

private theorem divd_swirl_zero (P : ChartParams) {e : ℕ} {D : FieldData} (hD : IsFieldData P e D)
    (hn : (0 : ℤ) ∈ D.modes) (x : ℝ) :
    (D.amp 0).swirlAmp.eval false 0 x = ((D.guardSwirl : ℝ) : ℂ) := by
  have hS := (hD.meanSwirl hn).1
  obtain ⟨-, pt, -, -⟩ := mesh_facts _ hS.mesh.t_sorted hS.mesh.t_first hS.mesh.t_last
  have ht : cellIndex (D.amp 0).swirlAmp.mesh.tBreaks 0 = 0 := glueIdx_zero _ pt
  have hj : cellIndex (D.amp 0).swirlAmp.mesh.xBreaks |x| < cellCount (D.amp 0).swirlAmp.mesh.xBreaks := by
    obtain ⟨-, -, cx, -⟩ := mesh_facts _ hS.mesh.x_sorted hS.mesh.x_first hS.mesh.x_last
    have := glueIdx_le (((D.amp 0).swirlAmp.mesh.xBreaks.drop 1).dropLast) |x|
    change glueIdx _ |x| < _
    omega
  have hg := hD.guard_swirl hn _ hj
  unfold Spline.eval Spline.evalHalf
  rw [ht, if_neg (by simp), one_mul]
  have h1 : evP (atFirst ((0 : ℝ) : ℂ) ((D.amp 0).swirlAmp.piece 0
      (cellIndex (D.amp 0).swirlAmp.mesh.xBreaks |x|))) (0, |x|) =
      evP ((D.amp 0).swirlAmp.piece 0 (cellIndex (D.amp 0).swirlAmp.mesh.xBreaks |x|)) (0, |x|) :=
    evP_atFirst 0 _ (0, |x|)
  rw [Complex.ofReal_zero, hg] at h1
  change evP _ (0, |x|) = _
  rw [← h1]
  simp [evP]

private def geomSumOneSub (e : ℕ) (t : ℝ) : ℂ := ((∑ i ∈ Finset.range e, (1 - t) ^ i : ℝ) : ℂ)

private theorem divd_w_eq (e : ℕ) (t : ℝ) : weightPoly 0 e t = 1 - (t : ℂ) * geomSumOneSub e t := by
  have h : (1 - t) ^ e = 1 - t * ∑ i ∈ Finset.range e, (1 - t) ^ i := by
    have := geom_sum_mul (1 - t) e
    linear_combination -this
  unfold weightPoly geomSumOneSub
  rw [pow_zero, one_mul, h]
  push_cast
  ring

private def meanLeading (D : FieldData) (x : ℝ) : Fin 3 → ℂ :=
  ![((-(D.guardStream * (1 - 3 * x ^ 2)) : ℝ) : ℂ), ((-(3 * D.guardStream * x)) : ℝ), ((D.guardSwirl : ℝ) : ℂ)]

private def meanRemainder (P : ChartParams) (D : FieldData) (TS TG : Spline) (t x : ℝ) : Fin 3 → ℂ :=
  ![geomSumOneSub D.highOrder t * ((D.guardStream * (1 - 3 * x ^ 2) : ℝ) : ℂ) -
      weightPoly 0 D.highOrder t * deriv (fun x' => ((1 - x' ^ 2 : ℝ) : ℂ) * TS.eval true t x') x,
    (((1 + 2 * P.eps) * D.guardStream * x : ℝ) : ℂ) -
      (((3 - (1 + 2 * P.eps) * t) : ℝ) : ℂ) * (weightPoly 0 D.highOrder t * TS.eval true t x -
        geomSumOneSub D.highOrder t * ((D.guardStream * x : ℝ) : ℂ)) -
      (((1 - t) : ℝ) : ℂ) * deriv (fun t' => weightPoly 0 D.highOrder t' * (D.amp 0).streamAmp.eval true t' x) t,
    weightPoly 0 D.highOrder t * TG.eval false t x - geomSumOneSub D.highOrder t * ((D.guardSwirl : ℝ) : ℂ)]

private theorem divd_reduced_split (P : ChartParams) {e : ℕ} {D : FieldData} (hD : IsFieldData P e D) (β : ℝ)
    (hn : (0 : ℤ) ∈ D.modes) :
    ∃ TS TG : Spline, IsSplineClass 2 2 true TS ∧ IsSplineClass 2 1 false TG ∧ ∃ t1 > 0,
      ∀ t < t1, ∀ x : ℝ, ∀ k : Fin 3,
        reducedField P D 0 β t x k = (t : ℂ) * meanLeading D x k + ((t ^ 2 : ℝ) : ℂ) * meanRemainder P D TS TG t x k := by
  have hS := (hD.meanStream hn).1
  have hG := (hD.meanSwirl hn).1
  obtain ⟨TS, hTS, c1, hc1, hsS⟩ := spline_firstRow_split _ hS
  obtain ⟨TG, hTG, c2, hc2, hsG⟩ := spline_firstRow_split _ hG
  refine ⟨TS, TG, hTS, hTG, min c1 c2, lt_min hc1 hc2, ?_⟩
  intro t ht x k
  have ht1 : t < c1 := lt_of_lt_of_le ht (min_le_left _ _)
  have ht2 : t < c2 := lt_of_lt_of_le ht (min_le_right _ _)
  have eS := spline_eval_contDiff _ hS (by norm_num) (by norm_num)
  have eTS := spline_eval_contDiff _ hTS (by norm_num) (by norm_num)
  set ee := D.highOrder
  have hw := divd_w_eq ee t
  fin_cases k
  · have hd1 : HasDerivAt (fun x' : ℝ => (((D.guardStream * (x' - x' ^ 3)) : ℝ) : ℂ))
        (((D.guardStream * (1 - 3 * x ^ 2)) : ℝ) : ℂ) x := by
      have h1 := (((hasDerivAt_id x).sub (hasDerivAt_pow 3 x)).const_mul D.guardStream).ofReal_comp
      refine h1.congr_deriv ?_
      norm_num
    have hd2 : DifferentiableAt ℝ (fun x' : ℝ => ((1 - x' ^ 2 : ℝ) : ℂ) * TS.eval true t x') x := by
      have h1 : DifferentiableAt ℝ (fun x' : ℝ => (t, x')) x :=
        (differentiableAt_const _).prodMk differentiableAt_id
      have h2 : DifferentiableAt ℝ (fun x' : ℝ => TS.eval true t x') x :=
        ((eTS.differentiable (by norm_num)) _).comp x h1
      have h3 : DifferentiableAt ℝ (fun x' : ℝ => ((1 - x' ^ 2 : ℝ) : ℂ)) x :=
        ((hasDerivAt_pow 2 x).const_sub 1).ofReal_comp.differentiableAt
      exact h3.mul h2
    have ef : (fun x' : ℝ => ((1 - x' ^ 2 : ℝ) : ℂ) * (D.amp 0).streamAmp.eval true t x') =
        fun x' => (((D.guardStream * (x' - x' ^ 3)) : ℝ) : ℂ) +
          (t : ℂ) * (((1 - x' ^ 2 : ℝ) : ℂ) * TS.eval true t x') := by
      funext x'
      rw [hsS t ht1 x', divd_stream_zero P hD hn]
      push_cast
      ring
    have hder : deriv (fun x' : ℝ => ((1 - x' ^ 2 : ℝ) : ℂ) * (D.amp 0).streamAmp.eval true t x') x =
        (((D.guardStream * (1 - 3 * x ^ 2)) : ℝ) : ℂ) +
          (t : ℂ) * deriv (fun x' => ((1 - x' ^ 2 : ℝ) : ℂ) * TS.eval true t x') x := by
      rw [ef]
      exact (hd1.add (hd2.hasDerivAt.const_mul (t : ℂ))).deriv
    simp only [reducedField, if_pos rfl, heightDeriv, Matrix.cons_val_zero, meanLeading, meanRemainder]
    rw [hder, weightPoly_one_split, hw]
    push_cast
    ring
  · have hdiff : DifferentiableAt ℝ (fun t' : ℝ => weightPoly 0 ee t' * (D.amp 0).streamAmp.eval true t' x) t := by
      have h1 : DifferentiableAt ℝ (fun t' : ℝ => (t', x)) t := differentiableAt_id.prodMk (differentiableAt_const _)
      have h2 : ContDiff ℝ 1 (fun p : ℝ × ℝ => weightPoly 0 ee p.1 * (D.amp 0).streamAmp.eval true p.1 p.2) :=
        ((pin_p 0 ee).of_le (by norm_num)).mul eS
      exact ((h2.differentiable (by norm_num)) _).comp t h1
    have hder : deriv (fun t' : ℝ => weightPoly 1 ee t' * (D.amp 0).streamAmp.eval true t' x) t =
        weightPoly 0 ee t * (D.amp 0).streamAmp.eval true t x +
          (t : ℂ) * deriv (fun t' : ℝ => weightPoly 0 ee t' * (D.amp 0).streamAmp.eval true t' x) t := by
      have e1 : (fun t' : ℝ => weightPoly 1 ee t' * (D.amp 0).streamAmp.eval true t' x) =
          fun t' : ℝ => ((t' : ℝ) : ℂ) * (weightPoly 0 ee t' * (D.amp 0).streamAmp.eval true t' x) := by
        funext t'
        rw [weightPoly_one_split]
        ring
      have hm : HasDerivAt (fun t' : ℝ => ((t' : ℝ) : ℂ) * (weightPoly 0 ee t' * (D.amp 0).streamAmp.eval true t' x))
          (((1 : ℝ) : ℂ) * (weightPoly 0 ee t * (D.amp 0).streamAmp.eval true t x) + ((t : ℝ) : ℂ) *
            deriv (fun t' : ℝ => weightPoly 0 ee t' * (D.amp 0).streamAmp.eval true t' x) t) t :=
        ((hasDerivAt_id t).ofReal_comp).mul hdiff.hasDerivAt
      rw [e1, hm.deriv]
      simp
    simp only [reducedField, if_pos rfl, twistedScale, radialScale, meanLeading, meanRemainder, Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.head_cons]
    rw [hder, weightPoly_one_split, hw, hsS t ht1 x, divd_stream_zero P hD hn]
    push_cast
    ring
  · simp only [reducedField, if_pos rfl, meanLeading, meanRemainder, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [hsG t ht2 x, divd_swirl_zero P hD hn, weightPoly_one_split, hw]
    push_cast
    ring

private def meanLinearPart (D : FieldData) (v : Space) : Fin 3 → ℝ :=
  ![-(D.guardStream * v 0) - D.guardSwirl * v 1, -(D.guardStream * v 1) + D.guardSwirl * v 0,
    2 * D.guardStream * v 2]

private def meanLinearMap (P : ChartParams) (D : FieldData) : Space →ₗ[ℝ] Space where
  toFun v := ofComponents (fun i => P.L0⁻¹ * meanLinearPart D v i)
  map_add' v w := by
    refine PiLp.ext fun i => ?_
    simp only [PiLp.add_apply, orig_ofComponents_apply]
    fin_cases i <;> simp [meanLinearPart] <;> ring
  map_smul' c v := by
    refine PiLp.ext fun i => ?_
    simp only [PiLp.smul_apply, orig_ofComponents_apply, RingHom.id_apply, smul_eq_mul]
    fin_cases i <;> simp [meanLinearPart] <;> ring

private def meanLinearCLM (P : ChartParams) (D : FieldData) : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap (meanLinearMap P D)

private theorem meanLinearCLM_apply (P : ChartParams) (D : FieldData) (v : Space) (i : Fin 3) :
    meanLinearCLM P D v i = P.L0⁻¹ * meanLinearPart D v i := by
  simp only [meanLinearCLM, LinearMap.coe_toContinuousLinearMap', meanLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    orig_ofComponents_apply]

private theorem meanLinearPart_contDiff (D : FieldData) (i : Fin 3) : ContDiff ℝ ⊤ (fun v : Space => meanLinearPart D v i) := by
  have h0 := pin_coord 0
  have h1 := pin_coord 1
  have h2 := pin_coord 2
  fin_cases i
  · simpa [meanLinearPart] using (contDiff_const.mul h0).neg.sub (contDiff_const.mul h1)
  · simpa [meanLinearPart] using (contDiff_const.mul h1).neg.add (contDiff_const.mul h0)
  · simpa [meanLinearPart] using contDiff_const.mul h2

private def decayOverShift (P : ChartParams) (r : ℝ) : ℝ := (1 - r / (r + P.L0)) ^ (2 * P.eps) * (r + P.L0)⁻¹

private theorem decayOverShift_analytic (P : ChartParams) (hP : IsChartParams P) : AnalyticAt ℝ (decayOverShift P) 0 := by
  have hL := hP.L0_pos
  have h1 : AnalyticAt ℝ (fun r : ℝ => 1 - r / (r + P.L0)) 0 :=
    analyticAt_const.sub (analyticAt_id.div (analyticAt_id.add analyticAt_const) (by simp; linarith))
  have h2 : AnalyticAt ℝ (fun r : ℝ => Real.exp (Real.log (1 - r / (r + P.L0)) * (2 * P.eps)) * (r + P.L0)⁻¹) 0 :=
    ((h1.log (by simp)).mul analyticAt_const).rexp'.mul
      ((analyticAt_id.add analyticAt_const).inv (by simp; linarith))
  refine h2.congr ?_
  filter_upwards [Ioi_mem_nhds (show -P.L0 / 2 < (0 : ℝ) by linarith)] with r hr
  have hr' : 0 < r + P.L0 := by simp only [Set.mem_Ioi] at hr; linarith
  have hpos : 0 < 1 - r / (r + P.L0) := by
    rw [sub_pos, div_lt_one hr']
    linarith
  simp only [decayOverShift]
  rw [Real.rpow_def_of_pos hpos]

private theorem decaySlope_smooth (P : ChartParams) (hP : IsChartParams P) (r : ℝ) (hr : 0 ≤ r) :
    ContDiffAt ℝ 2 (dslope (decayOverShift P) 0) r := by
  have hL := hP.L0_pos
  rcases hr.eq_or_lt with rfl | hr
  · obtain ⟨p, hp⟩ := decayOverShift_analytic P hP
    exact AnalyticAt.contDiffAt (⟨_, hp.has_fpower_series_dslope_fslope⟩ : AnalyticAt ℝ (dslope (decayOverShift P) 0) 0)
  · have hne : r + P.L0 ≠ 0 := by linarith
    have hs : 1 - r / (r + P.L0) ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      rw [eq_comm, div_eq_one_iff_eq hne] at h
      linarith
    have hd : ContDiffAt ℝ 2 (decayOverShift P) r :=
      ((contDiffAt_const.sub (contDiffAt_id.div (contDiffAt_id.add contDiffAt_const) hne)).rpow_const_of_ne hs).mul
        ((contDiffAt_id.add contDiffAt_const).inv hne)
    have he : dslope (decayOverShift P) 0 =ᶠ[nhds r] fun z => (z - 0)⁻¹ • (decayOverShift P z - decayOverShift P 0) := by
      filter_upwards [isOpen_ne.mem_nhds hr.ne'] with z hz
      rw [dslope_of_ne _ hz, slope_def_module]
    refine ContDiffAt.congr_of_eventuallyEq ?_ he
    simp only [sub_zero, smul_eq_mul]
    exact (contDiffAt_id.inv hr.ne').mul (hd.sub contDiffAt_const)

private def meanScaledQuotient (P : ChartParams) (D : FieldData) (TS TG : Spline) (q : ℝ × Space) : Space :=
  ofComponents (fun i => ‖q.2‖ * dslope (decayOverShift P) 0 (q.1 * ‖q.2‖) * meanLinearPart D q.2 i +
    ((((1 - q.1 * ‖q.2‖ / (q.1 * ‖q.2‖ + P.L0)) ^ (2 * P.eps) * ‖q.2‖ ^ 2 *
        ((q.1 * ‖q.2‖ + P.L0) ^ 2)⁻¹ : ℝ) : ℂ) *
      (meanRemainder P D TS TG (q.1 * ‖q.2‖ / (q.1 * ‖q.2‖ + P.L0)) (q.2 2 / ‖q.2‖) 0 * ((q.2 i / ‖q.2‖ : ℝ) : ℂ) +
        meanRemainder P D TS TG (q.1 * ‖q.2‖ / (q.1 * ‖q.2‖ + P.L0)) (q.2 2 / ‖q.2‖) 1 *
          ((![q.2 2 / ‖q.2‖ * q.2 0 / ‖q.2‖, q.2 2 / ‖q.2‖ * q.2 1 / ‖q.2‖, -(1 - (q.2 2 / ‖q.2‖) ^ 2)] i : ℝ) : ℂ) +
        meanRemainder P D TS TG (q.1 * ‖q.2‖ / (q.1 * ‖q.2‖ + P.L0)) (q.2 2 / ‖q.2‖) 2 *
          ((![-(q.2 1) / ‖q.2‖, q.2 0 / ‖q.2‖, 0] i : ℝ) : ℂ))).re)

private theorem divd_identity (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (β : ℝ) (TS TG : Spline)
    (t1 : ℝ) (hsplit : ∀ t < t1, ∀ x : ℝ, ∀ k : Fin 3,
        reducedField P D 0 β t x k = (t : ℂ) * meanLeading D x k + ((t ^ 2 : ℝ) : ℂ) * meanRemainder P D TS TG t x k)
    (s : ℝ) (hs : 0 < s) (v : Space) (hv : v ≠ 0) (hτ : s * ‖v‖ / (s * ‖v‖ + P.L0) < t1) :
    modeFieldOf P D β 0 (s • v) - meanLinearCLM P D (s • v) = (s ^ 2) • meanScaledQuotient P D TS TG (s, v) := by
  have hL := hP.L0_pos
  have hNv : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hN : ‖s • v‖ = s * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg hs.le]
  have hsv : ∀ j, (s • v) j = s * v j := fun j => by rw [PiLp.smul_apply, smul_eq_mul]
  have hT : chartT P (s • v) = s * ‖v‖ / (s * ‖v‖ + P.L0) := by rw [chartT, hN]
  have hH : heightRatio (s • v) = v 2 / ‖v‖ := by
    rw [heightRatio, hsv, hN]
    field_simp
  have hk := sub_smul_dslope (decayOverShift P) 0 (s * ‖v‖)
  have hph : modePhase P 0 β (s • v) = 1 := by simp [modePhase]
  have hsN : 0 < s * ‖v‖ := mul_pos hs hNv
  have hk' : dslope (decayOverShift P) 0 (s * ‖v‖) =
      ((1 - s * ‖v‖ / (s * ‖v‖ + P.L0)) ^ (2 * P.eps) * (s * ‖v‖ + P.L0)⁻¹ - P.L0⁻¹) / (s * ‖v‖) := by
    rw [eq_div_iff hsN.ne']
    simp only [decayOverShift, zero_div, sub_zero, Real.one_rpow, one_mul, zero_add, smul_eq_mul] at hk
    linear_combination hk
  refine PiLp.ext fun i => ?_
  rw [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, modeFieldOf, orig_ofComponents_apply, meanLinearCLM_apply, meanScaledQuotient,
    orig_ofComponents_apply, hph, one_mul]
  dsimp only
  rw [hk']
  simp only [hT, hH, hsplit _ hτ, decayFactor, chartS, radialVec, polarVecQ, azimVecQ, qOf, hsv, hN]
  generalize (1 - s * ‖v‖ / (s * ‖v‖ + P.L0)) ^ (2 * P.eps) = A
  generalize hτd : s * ‖v‖ / (s * ‖v‖ + P.L0) = τ
  generalize meanRemainder P D TS TG τ (v 2 / ‖v‖) 0 = h0
  generalize meanRemainder P D TS TG τ (v 2 / ‖v‖) 1 = h1
  generalize meanRemainder P D TS TG τ (v 2 / ‖v‖) 2 = h2
  subst hτd
  generalize hNd : ‖v‖ = N at *
  have hL' : s * N + P.L0 ≠ 0 := by positivity
  fin_cases i <;>
  · simp only [meanLeading, meanLinearPart, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, hsv]
    field_simp
    ring

private theorem divd_H_tame (P : ChartParams) {e : ℕ} {D : FieldData} (hD : IsFieldData P e D)
    (hn : (0 : ℤ) ∈ D.modes) {TS TG : Spline} (hTS : IsSplineClass 2 2 true TS) (hTG : IsSplineClass 2 1 false TG)
    (k : Fin 3) (q : ℝ × ℝ) : TameAt (fun p : ℝ × ℝ => meanRemainder P D TS TG p.1 p.2 k) q := by
  have hS := (hD.meanStream hn).1
  have hsig : ContDiff ℝ 2 (fun p : ℝ × ℝ => geomSumOneSub D.highOrder p.1) := by
    show ContDiff ℝ 2 (fun p : ℝ × ℝ => (((∑ i ∈ Finset.range D.highOrder, (1 - p.1) ^ i : ℝ)) : ℂ))
    have h1 : ContDiff ℝ 2 (fun p : ℝ × ℝ => ∑ i ∈ Finset.range D.highOrder, (1 - p.1) ^ i) :=
      ContDiff.sum fun i _ => (contDiff_const.sub contDiff_fst).pow i
    exact Complex.ofRealCLM.contDiff.comp h1
  have hw : ContDiff ℝ 2 (fun p : ℝ × ℝ => weightPoly 0 D.highOrder p.1) := (pin_p 0 _).of_le (by norm_num)
  have cast2 : ∀ f : ℝ × ℝ → ℝ, ContDiff ℝ 2 f → TameAt (fun p => (f p : ℂ)) q := fun f hf =>
    pin_tame_all (Complex.ofRealCLM.contDiff.comp hf) q
  have eTS := pin_spline hTS (by norm_num) (by norm_num)
  fin_cases k
  · have hY := pin_xderiv_mul (G := fun _ x => ((1 - x ^ 2 : ℝ) : ℂ)) (F := fun t x => TS.eval true t x) pin_q
      ((spline_eval_contDiff _ hTS (by norm_num) (by norm_num)).differentiable (by norm_num)) eTS
      (pin_spline_x hTS (by norm_num) (by norm_num)) q
    have hall := tame_sub (tame_mul (pin_tame_all hsig q)
      (cast2 (fun p => D.guardStream * (1 - 3 * p.2 ^ 2)) (by fun_prop))) (tame_mul (pin_tame_all hw q) hY)
    refine tame_congr hall (Filter.Eventually.of_forall fun p => ?_)
    simp [meanRemainder]
  · have hV := pin_tderiv_mul (G := fun t _ => weightPoly 0 D.highOrder t)
      (F := fun t x => (D.amp 0).streamAmp.eval true t x)
      (pin_p 0 _) ((spline_eval_contDiff _ hS (by norm_num) (by norm_num)).differentiable (by norm_num))
      (pin_spline hS (by norm_num) (by norm_num)) (pin_spline_t hS (by norm_num) (by norm_num)) q
    have hall := tame_sub (tame_sub (cast2 (fun p => (1 + 2 * P.eps) * D.guardStream * p.2) (by fun_prop))
      (tame_mul (cast2 (fun p => 3 - (1 + 2 * P.eps) * p.1) (by fun_prop))
        (tame_sub (tame_mul (pin_tame_all hw q) (eTS q))
          (tame_mul (pin_tame_all hsig q) (cast2 (fun p => D.guardStream * p.2) (by fun_prop))))))
      (tame_mul (cast2 (fun p => 1 - p.1) (by fun_prop)) hV)
    refine tame_congr hall (Filter.Eventually.of_forall fun p => ?_)
    simp [meanRemainder]
  · have hall := tame_sub (tame_mul (pin_tame_all hw q) (pin_spline hTG (by norm_num) (by norm_num) q))
      (tame_mul (pin_tame_all hsig q) (cast2 (fun _ => D.guardSwirl) contDiff_const))
    refine tame_congr hall (Filter.Eventually.of_forall fun p => ?_)
    simp [meanRemainder]

private theorem divd_Fm_tame (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (hn : (0 : ℤ) ∈ D.modes) {TS TG : Spline} (hTS : IsSplineClass 2 2 true TS)
    (hTG : IsSplineClass 2 1 false TG) (p : ℝ × Space) (hp1 : 0 ≤ p.1) (hp2 : p.2 ≠ 0) :
    TameAt (meanScaledQuotient P D TS TG) p := by
  have hL := hP.L0_pos
  have hn' : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => ‖q.2‖) p := (contDiffAt_norm ℝ hp2).comp p contDiffAt_snd
  have hN0 : ‖p.2‖ ≠ 0 := norm_ne_zero_iff.2 hp2
  have hr : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => q.1 * ‖q.2‖) p := contDiffAt_fst.mul hn'
  have hr0 : 0 ≤ p.1 * ‖p.2‖ := mul_nonneg hp1 (norm_nonneg _)
  have hden : p.1 * ‖p.2‖ + P.L0 ≠ 0 := by positivity
  have hτ : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => q.1 * ‖q.2‖ / (q.1 * ‖q.2‖ + P.L0)) p :=
    hr.div (hr.add contDiffAt_const) hden
  have hu : ∀ j : Fin 3, ContDiffAt ℝ ⊤ (fun q : ℝ × Space => q.2 j) p := fun j =>
    ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd).contDiffAt
  have hrat : ∀ j, ContDiffAt ℝ ⊤ (fun q : ℝ × Space => q.2 j / ‖q.2‖) p := fun j => (hu j).div hn' hN0
  have hs1 : 1 - p.1 * ‖p.2‖ / (p.1 * ‖p.2‖ + P.L0) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    rw [eq_comm, div_eq_one_iff_eq hden] at h
    linarith
  have hcoef : ContDiffAt ℝ 2 (fun q : ℝ × Space => (1 - q.1 * ‖q.2‖ / (q.1 * ‖q.2‖ + P.L0)) ^ (2 * P.eps) *
      ‖q.2‖ ^ 2 * ((q.1 * ‖q.2‖ + P.L0) ^ 2)⁻¹) p :=
    ((((contDiffAt_const.sub hτ).rpow_const_of_ne hs1).mul (hn'.pow 2)).mul
      (((hr.add contDiffAt_const).pow 2).inv (pow_ne_zero 2 hden))).of_le le_top
  have hk : ContDiffAt ℝ 2 (fun q : ℝ × Space => dslope (decayOverShift P) 0 (q.1 * ‖q.2‖)) p :=
    (decaySlope_smooth P hP _ hr0).comp p (hr.of_le le_top)
  have hH : ∀ k, TameAt (fun q : ℝ × Space =>
      meanRemainder P D TS TG (q.1 * ‖q.2‖ / (q.1 * ‖q.2‖ + P.L0)) (q.2 2 / ‖q.2‖) k) p := fun k =>
    tame_comp (g := fun z : ℝ × ℝ => meanRemainder P D TS TG z.1 z.2 k)
      (Φ := fun q : ℝ × Space => (q.1 * ‖q.2‖ / (q.1 * ‖q.2‖ + P.L0), q.2 2 / ‖q.2‖))
      (divd_H_tame P hD hn hTS hTG k _) (tame_of_contDiffAt ((hτ.prodMk (hrat 2)).of_le le_top))
  have cC : ∀ f : ℝ × Space → ℝ, ContDiffAt ℝ 2 f p → TameAt (fun q => (f q : ℂ)) p := fun f hf =>
    tame_of_contDiffAt (Complex.ofRealCLM.contDiff.contDiffAt.comp p hf)
  unfold meanScaledQuotient
  refine tame_ofComponents fun i => ?_
  have hv1 : ContDiffAt ℝ 2 (fun q : ℝ × Space => ![q.2 2 / ‖q.2‖ * q.2 0 / ‖q.2‖, q.2 2 / ‖q.2‖ * q.2 1 / ‖q.2‖,
      -(1 - (q.2 2 / ‖q.2‖) ^ 2)] i) p := by
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    · exact (((hrat 2).mul (hu 0)).div hn' hN0).of_le le_top
    · exact (((hrat 2).mul (hu 1)).div hn' hN0).of_le le_top
    · exact ((contDiffAt_const.sub ((hrat 2).pow 2)).neg).of_le le_top
  have hv2 : ContDiffAt ℝ 2 (fun q : ℝ × Space => ![-(q.2 1) / ‖q.2‖, q.2 0 / ‖q.2‖, 0] i) p := by
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    · exact (((hu 1).neg).div hn' hN0).of_le le_top
    · exact (hrat 0).of_le le_top
    · exact contDiffAt_const
  have hlin : ContDiffAt ℝ 2 (fun q : ℝ × Space => meanLinearPart D q.2 i) p :=
    ((meanLinearPart_contDiff D i).comp contDiff_snd).contDiffAt.of_le le_top
  have h1 : TameAt (fun q : ℝ × Space => ‖q.2‖ * dslope (decayOverShift P) 0 (q.1 * ‖q.2‖) * meanLinearPart D q.2 i) p :=
    tame_of_contDiffAt (((hn'.of_le le_top).mul hk).mul hlin)
  have h2 := tame_clm Complex.reCLM (tame_mul (cC _ hcoef)
    (tame_add (tame_add (tame_mul (hH 0) (cC _ ((hrat i).of_le le_top))) (tame_mul (hH 1) (cC _ hv1)))
      (tame_mul (hH 2) (cC _ hv2))))
  simp only [Complex.reCLM_apply] at h2
  exact tame_add h1 h2

theorem modeFieldOf_scaledProfile_mean (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (hn : (0 : ℤ) ∈ D.modes) :
    ∃ ℓ : Space →L[ℝ] Space, ∃ F : ℝ × Space → Space, ∃ ρ : ℝ, 0 < ρ ∧ modeFieldOf P D β 0 0 = 0 ∧
      (∀ s : ℝ, 0 < s → ∀ v : Space, v ≠ 0 →
        modeFieldOf P D β 0 (s • v) - ℓ (s • v) = (s ^ 2) • F (s, v)) ∧
      ∀ p ∈ Set.Icc 0 ρ ×ˢ (Metric.closedBall (0 : Space) 1 \ Metric.ball 0 (1 / 2)),
        ∃ U ∈ nhds p, (∀ q ∈ U, DifferentiableAt ℝ F q) ∧ ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ F) U := by
  obtain ⟨TS, TG, hTS, hTG, t1, ht1, hsplit⟩ := divd_reduced_split P hD β hn
  have hL := hP.L0_pos
  let F : ℝ × Space → Space := fun q => if 0 < q.1 ∧ q.2 ≠ 0 then
    ((q.1 ^ 2)⁻¹ : ℝ) • (modeFieldOf P D β 0 (q.1 • q.2) - meanLinearCLM P D (q.1 • q.2)) else meanScaledQuotient P D TS TG q
  have hρ : 0 < P.L0 * t1 / 4 := by positivity
  refine ⟨meanLinearCLM P D, F, P.L0 * t1 / 4, hρ, ?_, ?_, ?_⟩
  · have hz : ∀ k, reducedField P D 0 β (chartT P 0) (heightRatio 0) k = 0 := by
      intro k
      have h0 : chartT P 0 = 0 := by simp [chartT]
      rw [h0, hsplit 0 ht1]
      simp
    refine PiLp.ext fun i => ?_
    rw [modeFieldOf, orig_ofComponents_apply]
    simp [hz]
  · intro s hs v hv
    simp only [F, if_pos (And.intro hs hv), smul_smul]
    rw [show s ^ 2 * (s ^ 2)⁻¹ = 1 by field_simp, one_smul]
  · intro p hp
    have hp1 : 0 ≤ p.1 := hp.1.1
    have hp1' : p.1 ≤ P.L0 * t1 / 4 := hp.1.2
    have hp2 : ‖p.2‖ ≤ 1 := by simpa using hp.2.1
    have hp3 : 1 / 2 ≤ ‖p.2‖ := by simpa using hp.2.2
    have hpv : p.2 ≠ 0 := by
      intro h
      rw [h, norm_zero] at hp3
      norm_num at hp3
    have hev : F =ᶠ[nhds p] meanScaledQuotient P D TS TG := by
      filter_upwards [Metric.ball_mem_nhds p (lt_min (by norm_num : (0 : ℝ) < 1 / 8) hρ)] with q hq
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hq
      have hq1 : q.1 < P.L0 * t1 / 2 := by
        have := hq.1
        rw [Real.dist_eq] at this
        have := (abs_lt.1 (lt_of_lt_of_le this (min_le_right _ _))).2
        linarith
      have hq2 : ‖q.2‖ < 9 / 8 := by
        have := lt_of_lt_of_le hq.2 (min_le_left _ _)
        rw [dist_eq_norm] at this
        have := norm_le_norm_add_norm_sub' q.2 p.2
        linarith [norm_sub_rev q.2 p.2]
      have hq3 : 3 / 8 < ‖q.2‖ := by
        have := lt_of_lt_of_le hq.2 (min_le_left _ _)
        rw [dist_eq_norm] at this
        have := norm_le_norm_add_norm_sub' p.2 q.2
        linarith [norm_sub_rev q.2 p.2]
      have hqv : q.2 ≠ 0 := by
        intro h
        rw [h, norm_zero] at hq3
        norm_num at hq3
      by_cases hq0 : 0 < q.1
      · simp only [F, if_pos (And.intro hq0 hqv)]
        have hτ : q.1 * ‖q.2‖ / (q.1 * ‖q.2‖ + P.L0) < t1 := by
          have hqn : 0 ≤ q.1 * ‖q.2‖ := mul_nonneg hq0.le (norm_nonneg _)
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
        rw [divd_identity P hP D β TS TG t1 hsplit q.1 hq0 q.2 hqv hτ, smul_smul,
          show (q.1 ^ 2)⁻¹ * q.1 ^ 2 = 1 by field_simp, one_smul]
      · simp only [F, if_neg (show ¬(0 < q.1 ∧ q.2 ≠ 0) from fun h => hq0 h.1)]
    exact tame_region (tame_congr (divd_Fm_tame P hP hD hn hTS hTG p hp1 hpv) hev)

theorem modeFieldOf_fderiv_slopeNearOrigin_wave (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) (h0 : n ≠ 0) :
    ∃ K : NNReal, ∃ U ∈ nhds (0 : Space), LipschitzOnWith K (fderiv ℝ (modeFieldOf P D β n)) U := by
  obtain ⟨F, ρ, hρ, hf0, hs, hF⟩ := modeFieldOf_scaledProfile_wave P hP hD β n hn h0
  obtain ⟨-, K, hK⟩ := scaled_fderiv_slopeBound hρ hf0 hs hF
  exact ⟨K, Metric.ball 0 ρ, Metric.ball_mem_nhds 0 hρ, hK⟩

theorem modeFieldOf_fderiv_slopeNearOrigin_mean (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (hn : (0 : ℤ) ∈ D.modes) :
    ∃ K : NNReal, ∃ U ∈ nhds (0 : Space), LipschitzOnWith K (fderiv ℝ (modeFieldOf P D β 0)) U := by
  obtain ⟨ℓ, F, ρ, hρ, hf0, hs, hF⟩ := modeFieldOf_scaledProfile_mean P hP hD β hn
  obtain ⟨hd, K, hK⟩ := scaled_fderiv_slopeBound (f := fun y => modeFieldOf P D β 0 y - ℓ y) hρ
    (by simp [hf0]) hs hF
  refine ⟨K, Metric.ball 0 ρ, Metric.ball_mem_nhds 0 hρ, LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_⟩
  have e : ∀ w ∈ Metric.ball (0 : Space) ρ,
      fderiv ℝ (modeFieldOf P D β 0) w = fderiv ℝ (fun y => modeFieldOf P D β 0 y - ℓ y) w + ℓ := by
    intro w hw
    have h2 := ((hd w hw).hasFDerivAt.add ℓ.hasFDerivAt).congr_of_eventuallyEq
      (f₁ := modeFieldOf P D β 0) (Filter.Eventually.of_forall fun y => by simp)
    exact h2.fderiv
  rw [e y hy, e z hz, dist_add_right]
  exact hK.dist_le_mul y hy z hz

end GivenFields

end CellCert

end Breakdown
