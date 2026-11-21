import Breakdown.FracCell.GivenAuxDefs

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

def modeFieldOf (P : ChartParams) (D : FieldData) (β : ℝ) (n : ℤ) (y : Space) : Space :=
  ofComponents (fun i => ((decayFactor P y : ℂ) * (modePhase P n β y *
    (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
      reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
      reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re)

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

theorem spline_eval_contDiff (S : Spline) {a b : ℕ} {odd : Bool} (hS : IsSplineClass a b odd S) (ha : 1 ≤ a)
    (hb : 1 ≤ b) : ContDiff ℝ 1 (fun p : ℝ × ℝ => S.eval odd p.1 p.2) := by
  obtain ⟨st, pt, -, -⟩ := mesh_facts _ hS.mesh.t_sorted hS.mesh.t_first hS.mesh.t_last
  obtain ⟨sx, px, -, -⟩ := mesh_facts _ hS.mesh.x_sorted hS.mesh.x_first hS.mesh.x_last
  obtain ⟨h1, h2⟩ := full_glue _ _ st sx px _ (glued_base S hS ha hb)
  rw [spline_eq]
  exact contDiff_one_iff_hasFDerivAt.2 ⟨_, h2, h1⟩

theorem spline_tderiv_contDiff (S : Spline) {a b : ℕ} {odd : Bool} (hS : IsSplineClass a b odd S) (ha : 2 ≤ a)
    (hb : 1 ≤ b) : ContDiff ℝ 1 (fun p : ℝ × ℝ => deriv (fun t => S.eval odd t p.2) p.1) := by
  obtain ⟨st, pt, -, -⟩ := mesh_facts _ hS.mesh.t_sorted hS.mesh.t_first hS.mesh.t_last
  obtain ⟨sx, px, -, -⟩ := mesh_facts _ hS.mesh.x_sorted hS.mesh.x_first hS.mesh.x_last
  obtain ⟨h1, -⟩ := full_glue _ _ st sx px _ (glued_base S hS (by omega) hb)
  obtain ⟨k1, k2⟩ := full_glue _ _ st sx px _ (glued_t S hS ha hb)
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
  exact contDiff_one_iff_hasFDerivAt.2 ⟨_, k2, k1⟩

theorem spline_xderiv_contDiff (S : Spline) {a b : ℕ} {odd : Bool} (hS : IsSplineClass a b odd S) (ha : 1 ≤ a)
    (hb : 2 ≤ b) : ContDiff ℝ 1 (fun p : ℝ × ℝ => deriv (fun x => S.eval odd p.1 x) p.2) := by
  obtain ⟨st, pt, -, -⟩ := mesh_facts _ hS.mesh.t_sorted hS.mesh.t_first hS.mesh.t_last
  obtain ⟨sx, px, -, -⟩ := mesh_facts _ hS.mesh.x_sorted hS.mesh.x_first hS.mesh.x_last
  obtain ⟨h1, -⟩ := full_glue _ _ st sx px _ (glued_base S hS ha (by omega))
  obtain ⟨k1, k2⟩ := full_glue _ _ st sx px _ (glued_x S hS ha hb)
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
  exact contDiff_one_iff_hasFDerivAt.2 ⟨_, k2, k1⟩

private theorem partial_t_contDiff {G : ℝ → ℝ → ℂ} (hG : ContDiff ℝ 2 (fun p : ℝ × ℝ => G p.1 p.2)) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => deriv (fun t => G t p.2) p.1) := by
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

private theorem partial_x_contDiff {G : ℝ → ℝ → ℂ} (hG : ContDiff ℝ 2 (fun p : ℝ × ℝ => G p.1 p.2)) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => deriv (fun x => G p.1 x) p.2) := by
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

private theorem tderiv_mul_contDiff {G F : ℝ → ℝ → ℂ} (hG : ContDiff ℝ 2 (fun p : ℝ × ℝ => G p.1 p.2))
    (hF : ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2))
    (hFt : ContDiff ℝ 1 (fun p : ℝ × ℝ => deriv (fun t => F t p.2) p.1)) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => deriv (fun t => G t p.2 * F t p.2) p.1) := by
  have e : (fun p : ℝ × ℝ => deriv (fun t => G t p.2 * F t p.2) p.1) =
      fun p => deriv (fun t => G t p.2) p.1 * F p.1 p.2 + G p.1 p.2 * deriv (fun t => F t p.2) p.1 := by
    funext p
    have hdF : DifferentiableAt ℝ (fun t => F t p.2) p.1 := by
      have h1 : DifferentiableAt ℝ (fun t : ℝ => (t, p.2)) p.1 :=
        differentiableAt_id.prodMk (differentiableAt_const _)
      exact ((hF.differentiable (by norm_num)) _).comp p.1 h1
    have hdG : DifferentiableAt ℝ (fun t => G t p.2) p.1 := by
      have h1 : DifferentiableAt ℝ (fun t : ℝ => (t, p.2)) p.1 :=
        differentiableAt_id.prodMk (differentiableAt_const _)
      exact ((hG.differentiable (by norm_num)) _).comp p.1 h1
    exact deriv_mul hdG hdF
  rw [e]
  exact ((partial_t_contDiff hG).mul hF).add ((hG.of_le (by norm_num)).mul hFt)

private theorem xderiv_mul_contDiff {G F : ℝ → ℝ → ℂ} (hG : ContDiff ℝ 2 (fun p : ℝ × ℝ => G p.1 p.2))
    (hF : ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2))
    (hFx : ContDiff ℝ 1 (fun p : ℝ × ℝ => deriv (fun x => F p.1 x) p.2)) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => deriv (fun x => G p.1 x * F p.1 x) p.2) := by
  have e : (fun p : ℝ × ℝ => deriv (fun x => G p.1 x * F p.1 x) p.2) =
      fun p => deriv (fun x => G p.1 x) p.2 * F p.1 p.2 + G p.1 p.2 * deriv (fun x => F p.1 x) p.2 := by
    funext p
    have hdF : DifferentiableAt ℝ (fun x => F p.1 x) p.2 := by
      have h1 : DifferentiableAt ℝ (fun x : ℝ => (p.1, x)) p.2 :=
        (differentiableAt_const _).prodMk differentiableAt_id
      exact ((hF.differentiable (by norm_num)) _).comp p.2 h1
    have hdG : DifferentiableAt ℝ (fun x => G p.1 x) p.2 := by
      have h1 : DifferentiableAt ℝ (fun x : ℝ => (p.1, x)) p.2 :=
        (differentiableAt_const _).prodMk differentiableAt_id
      exact ((hG.differentiable (by norm_num)) _).comp p.2 h1
    exact deriv_mul hdG hdF
  rw [e]
  exact ((partial_x_contDiff hG).mul hF).add ((hG.of_le (by norm_num)).mul hFx)

private theorem contDiff_of_eq {f g : ℝ × ℝ → ℂ} (h : ∀ p, f p = g p) (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 f := by
  rwa [funext h]

private theorem coreRatioT_contDiff (P : ChartParams) (hP : IsChartParams P) : ContDiff ℝ ⊤ (coreRatioT P) := by
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

private theorem smooth_weight (a e k : ℕ) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => weightPoly a e p.1 * ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ k) := by
  unfold weightPoly
  have h1 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => p.1 ^ a * (1 - p.1) ^ e) := by fun_prop
  have h2 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => 1 - p.2 ^ 2) := by fun_prop
  exact (Complex.ofRealCLM.contDiff.comp h1).mul ((Complex.ofRealCLM.contDiff.comp h2).pow k)

private theorem smooth_weight' (a e k : ℕ) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => ((1 - p.2 ^ 2 : ℝ) : ℂ) * (weightPoly a e p.1 * ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ k)) := by
  have h2 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => 1 - p.2 ^ 2) := by fun_prop
  exact (Complex.ofRealCLM.contDiff.comp h2).mul (smooth_weight a e k)

theorem reducedField_wave_contDiff (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) (h0 : n ≠ 0) (k : Fin 3) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => reducedField P D n β p.1 p.2 k) := by
  have hR := hD.waveRadial n hn h0
  have hT := hD.wavePolar n hn h0
  have eR := spline_eval_contDiff _ hR (by norm_num) (by norm_num)
  have eT := spline_eval_contDiff _ hT (by norm_num) (by norm_num)
  have tR := spline_tderiv_contDiff _ hR (by norm_num) (by norm_num)
  have xT := spline_xderiv_contDiff _ hT (by norm_num) (by norm_num)
  have hW := (smooth_weight (D.lowOrder n) D.highOrder (D.axisOrder n)).of_le (m := 1) le_top
  have hur : ContDiff ℝ 1 (fun p : ℝ × ℝ => weightPoly (D.lowOrder n) D.highOrder p.1 *
      ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).radialAmp.eval false p.1 p.2) := hW.mul eR
  fin_cases k
  · simpa [reducedField, h0] using hur
  · simpa [reducedField, h0] using hW.mul eT
  · have hA := tderiv_mul_contDiff (G := fun t x => weightPoly (D.lowOrder n) D.highOrder t *
        ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n) (F := fun t x => (D.amp n).radialAmp.eval false t x)
        ((smooth_weight _ _ _).of_le le_top) eR tR
    have hB := xderiv_mul_contDiff (G := fun t x => ((1 - x ^ 2 : ℝ) : ℂ) * (weightPoly (D.lowOrder n) D.highOrder t *
        ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n)) (F := fun t x => (D.amp n).polarAmp.eval true t x)
        ((smooth_weight' _ _ _).of_le le_top) eT xT
    have hc1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => ((p.1 * (1 - p.1) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_fst.mul (contDiff_const.sub contDiff_fst))
    have hc2 : ContDiff ℝ 1 (fun p : ℝ × ℝ => Complex.I * ((n : ℝ) * β * coreRatioT P p.1 : ℝ) - ((2 * P.eps * p.1 : ℝ) : ℂ)) := by
      refine (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp ?_)).sub (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst))
      exact contDiff_const.mul (((coreRatioT_contDiff P hP).of_le le_top).comp contDiff_fst)
    have hall := contDiff_const (c := Complex.I / ((n * P.m : ℤ) : ℂ)) |>.mul
      ((((hc1.mul hA).add (hc2.mul hur)).add ((contDiff_const (c := (2 : ℂ))).mul hur)).sub hB)
    refine contDiff_of_eq (fun p => ?_) hall
    simp [reducedField, h0, twistedScale, radialScale, heightDeriv, mul_assoc]

private theorem smooth_p (a e : ℕ) : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => weightPoly a e p.1) := by
  unfold weightPoly
  have h1 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => p.1 ^ a * (1 - p.1) ^ e) := by fun_prop
  exact Complex.ofRealCLM.contDiff.comp h1

private theorem smooth_q : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => ((1 - p.2 ^ 2 : ℝ) : ℂ)) := by
  have h2 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => 1 - p.2 ^ 2) := by fun_prop
  exact Complex.ofRealCLM.contDiff.comp h2


theorem reducedField_mean_contDiff (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (hn : (0 : ℤ) ∈ D.modes) (k : Fin 3) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => reducedField P D 0 β p.1 p.2 k) := by
  have hS := (hD.meanStream hn).1
  have hG := (hD.meanSwirl hn).1
  have eS := spline_eval_contDiff _ hS (by norm_num) (by norm_num)
  have eG := spline_eval_contDiff _ hG (by norm_num) (by norm_num)
  have tS := spline_tderiv_contDiff _ hS (by norm_num) (by norm_num)
  have xS := spline_xderiv_contDiff _ hS (by norm_num) (by norm_num)
  have hp := (smooth_p 1 D.highOrder).of_le (m := 1) le_top
  fin_cases k
  · have hB := xderiv_mul_contDiff (G := fun t x => ((1 - x ^ 2 : ℝ) : ℂ))
        (F := fun t x => (D.amp 0).streamAmp.eval true t x) (smooth_q.of_le le_top) eS xS
    have hall := (hp.mul hB).neg
    refine contDiff_of_eq (fun p => ?_) hall
    simp [reducedField, heightDeriv]
  · have hA := tderiv_mul_contDiff (G := fun t x => weightPoly 1 D.highOrder t)
        (F := fun t x => (D.amp 0).streamAmp.eval true t x) ((smooth_p 1 D.highOrder).of_le le_top) eS tS
    have hc1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => ((p.1 * (1 - p.1) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_fst.mul (contDiff_const.sub contDiff_fst))
    have hc2 : ContDiff ℝ 1 (fun p : ℝ × ℝ => Complex.I * (((0 : ℤ) : ℝ) * β * coreRatioT P p.1 : ℝ) - ((2 * P.eps * p.1 : ℝ) : ℂ)) := by
      refine (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp ?_)).sub (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst))
      exact contDiff_const.mul (((coreRatioT_contDiff P hP).of_le le_top).comp contDiff_fst)
    have hpS := hp.mul eS
    have hall := ((((hc1.mul hA).add (hc2.mul hpS)).add ((contDiff_const (c := (2 : ℂ))).mul hpS))).neg
    refine contDiff_of_eq (fun p => ?_) hall
    simp [reducedField, twistedScale, radialScale]
  · have hall := hp.mul eG
    refine contDiff_of_eq (fun p => ?_) hall
    simp [reducedField]


private theorem ofComponents_apply' (w : Fin 3 → ℝ) (k : Fin 3) : (ofComponents w) k = w k := by
  fin_cases k <;> simp [ofComponents]

private theorem coord_contDiff (i : Fin 3) : ContDiff ℝ ⊤ (fun y : Space => y i) :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff

private theorem norm_contDiffAt {y : Space} (hy : y ≠ 0) : ContDiffAt ℝ ⊤ (fun y : Space => ‖y‖) y :=
  contDiffAt_norm ℝ hy

private theorem norm_ne {y : Space} (hy : y ≠ 0) : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy

private theorem chartT_contDiffAt (P : ChartParams) (hP : IsChartParams P) {y : Space} (hy : y ≠ 0) :
    ContDiffAt ℝ ⊤ (chartT P) y := by
  have h1 := norm_contDiffAt hy
  have hne : ‖y‖ + P.L0 ≠ 0 := by have := hP.L0_pos; positivity
  exact h1.div (h1.add contDiffAt_const) hne

private theorem heightRatio_contDiffAt {y : Space} (hy : y ≠ 0) :
    ContDiffAt ℝ ⊤ heightRatio y :=
  (coord_contDiff 2).contDiffAt.div (norm_contDiffAt hy) (norm_ne hy)

private theorem decayFactor_contDiffAt (P : ChartParams) (hP : IsChartParams P) {y : Space} (hy : y ≠ 0) :
    ContDiffAt ℝ ⊤ (decayFactor P) y := by
  have hs : chartS P y ≠ 0 := by
    unfold chartS chartT
    have hL := hP.L0_pos
    have hn : 0 ≤ ‖y‖ := norm_nonneg y
    have hd : 0 < ‖y‖ + P.L0 := by positivity
    rw [sub_ne_zero]
    intro h
    rw [eq_comm, div_eq_one_iff_eq hd.ne'] at h
    linarith
  exact (contDiffAt_const.sub (chartT_contDiffAt P hP hy)).rpow_const_of_ne hs

private theorem logPhase_contDiff (P : ChartParams) (hP : IsChartParams P) : ContDiff ℝ ⊤ (logPhase P) := by
  unfold logPhase
  refine contDiff_const.mul (ContDiff.log (contDiff_const.add ((contDiff_norm_sq ℝ).div_const _)) ?_)
  intro y
  have := hP.rc_pos
  positivity

private theorem radialVec_contDiffAt {y : Space} (hy : y ≠ 0) (i : Fin 3) :
    ContDiffAt ℝ ⊤ (fun y => radialVec y i) y :=
  (coord_contDiff i).contDiffAt.div (norm_contDiffAt hy) (norm_ne hy)

private theorem polarVecQ_contDiffAt {y : Space} (hy : y ≠ 0) (i : Fin 3) :
    ContDiffAt ℝ ⊤ (fun y => polarVecQ y i) y := by
  have hh := heightRatio_contDiffAt hy
  have hr : ∀ j, ContDiffAt ℝ ⊤ (fun y : Space => y j / ‖y‖) y := fun j =>
    (coord_contDiff j).contDiffAt.div (norm_contDiffAt hy) (norm_ne hy)
  fin_cases i
  · simpa [polarVecQ, mul_div_assoc] using hh.mul (hr 0)
  · simpa [polarVecQ, mul_div_assoc] using hh.mul (hr 1)
  · simpa [polarVecQ, qOf] using (contDiffAt_const.sub (hh.pow 2)).neg

private theorem azimVecQ_contDiffAt {y : Space} (hy : y ≠ 0) (i : Fin 3) :
    ContDiffAt ℝ ⊤ (fun y => azimVecQ y i) y := by
  have hr : ∀ j, ContDiffAt ℝ ⊤ (fun y : Space => y j / ‖y‖) y := fun j =>
    (coord_contDiff j).contDiffAt.div (norm_contDiffAt hy) (norm_ne hy)
  fin_cases i
  · simpa [azimVecQ, neg_div] using (hr 1).neg
  · simpa [azimVecQ] using hr 0
  · simpa [azimVecQ] using (contDiffAt_const : ContDiffAt ℝ ⊤ (fun _ : Space => (0 : ℝ)) y)

private theorem ofReal_contDiffAt {f : Space → ℝ} {y : Space} {N : WithTop ℕ∞} (hf : ContDiffAt ℝ N f y) :
    ContDiffAt ℝ N (fun z => (f z : ℂ)) y :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp y hf

private def planeOf (y : Space) : ℂ := ⟨y 0, y 1⟩

private theorem planeOf_eq (y : Space) : planeOf y = (y 0 : ℂ) + (y 1 : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [planeOf]

private theorem planeOf_contDiff : ContDiff ℝ ⊤ planeOf := by
  have e : planeOf = fun y => ((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I := funext planeOf_eq
  rw [e]
  exact (Complex.ofRealCLM.contDiff.comp (coord_contDiff 0)).add
    ((Complex.ofRealCLM.contDiff.comp (coord_contDiff 1)).mul contDiff_const)

private theorem exp_arg_int (w : ℂ) (hw : w ≠ 0) (k : ℤ) :
    Complex.exp (Complex.I * (((k : ℝ) * Complex.arg w : ℝ) : ℂ)) = (w / (‖w‖ : ℂ)) ^ k := by
  have h1 : Complex.I * (((k : ℝ) * Complex.arg w : ℝ) : ℂ) = (k : ℂ) * ((Complex.arg w : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h1, Complex.exp_int_mul]
  congr 1
  have h2 := Complex.norm_mul_exp_arg_mul_I w
  have h3 : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hw)
  rw [eq_div_iff h3, mul_comm]
  exact h2

private theorem field_contDiffAt_gen (P : ChartParams) (hP : IsChartParams P) (R : ℝ → ℝ → Fin 3 → ℂ)
    (ph : Space → ℂ) (hred : ∀ k : Fin 3, ContDiff ℝ 1 (fun p : ℝ × ℝ => R p.1 p.2 k)) (y : Space) (hy : y ≠ 0)
    (hph : ContDiffAt ℝ 1 ph y) :
    ContDiffAt ℝ 1 (fun y => ofComponents (fun i => ((decayFactor P y : ℂ) * (ph y *
      (R (chartT P y) (heightRatio y) 0 * radialVec y i +
        R (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        R (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re)) y := by
  rw [contDiffAt_piLp]
  intro j
  simp only [ofComponents_apply']
  have hc : ContDiffAt ℝ 1 (fun x => (chartT P x, heightRatio x)) y :=
    ((chartT_contDiffAt P hP hy).of_le le_top).prodMk ((heightRatio_contDiffAt hy).of_le le_top)
  have hR : ∀ k : Fin 3, ContDiffAt ℝ 1 (fun x => R (chartT P x) (heightRatio x) k) y :=
    fun k => (hred k).comp_contDiffAt y hc
  have hv : ∀ f : Space → ℝ, ContDiffAt ℝ ⊤ f y → ContDiffAt ℝ 1 (fun x => (f x : ℂ)) y :=
    fun f hf => ofReal_contDiffAt (hf.of_le le_top)
  have h0 := (hR 0).mul (hv _ (radialVec_contDiffAt hy j))
  have h1 := (hR 1).mul (hv _ (polarVecQ_contDiffAt hy j))
  have h2 := (hR 2).mul (hv _ (azimVecQ_contDiffAt hy j))
  have hs := (hv _ (decayFactor_contDiffAt P hP hy)).mul (hph.mul ((h0.add h1).add h2))
  exact Complex.reCLM.contDiff.contDiffAt.comp y hs

theorem modeFieldOf_contDiffAt_of (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (β : ℝ) (n : ℤ)
    (hred : ∀ k : Fin 3, ContDiff ℝ 1 (fun p : ℝ × ℝ => reducedField P D n β p.1 p.2 k)) (y : Space) (hy : y ≠ 0)
    (hph : ContDiffAt ℝ 1 (modePhase P n β) y) : ContDiffAt ℝ 1 (modeFieldOf P D β n) y :=
  field_contDiffAt_gen P hP (reducedField P D n β) (modePhase P n β) hred y hy hph

theorem reducedField_wave_axisFactor (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) (h0 : n ≠ 0) :
    ∃ H : ℝ → ℝ → Fin 3 → ℂ, (∀ k : Fin 3, ContDiff ℝ 1 (fun p : ℝ × ℝ => H p.1 p.2 k)) ∧
      ∀ t x k, reducedField P D n β t x k = ((1 - x ^ 2 : ℝ) : ℂ) * H t x k := by
  obtain ⟨k1, hk1⟩ : ∃ k1, D.axisOrder n = k1 + 1 :=
    ⟨D.axisOrder n - 1, by have := hD.axisOrder_ge n hn h0; omega⟩
  have hR := hD.waveRadial n hn h0
  have hT := hD.wavePolar n hn h0
  have eR := spline_eval_contDiff _ hR (by norm_num) (by norm_num)
  have eT := spline_eval_contDiff _ hT (by norm_num) (by norm_num)
  have tR := spline_tderiv_contDiff _ hR (by norm_num) (by norm_num)
  have xT := spline_xderiv_contDiff _ hT (by norm_num) (by norm_num)
  set a := D.lowOrder n
  set ee := D.highOrder
  set R := (D.amp n).radialAmp
  set Θ := (D.amp n).polarAmp
  set q : ℝ → ℂ := fun x => ((1 - x ^ 2 : ℝ) : ℂ) with hq
  set A : ℝ → ℝ → ℂ := fun t x => weightPoly a ee t * q x ^ k1 * R.eval false t x with hA
  set B : ℝ → ℝ → ℂ := fun t x => weightPoly a ee t * q x ^ k1 * Θ.eval true t x with hB
  set C : ℝ → ℝ → ℂ := fun t x => (Complex.I / ((n * P.m : ℤ) : ℂ)) *
    (((t * (1 - t) : ℝ) : ℂ) * deriv (fun t' => A t' x) t +
      (Complex.I * ((n : ℝ) * β * coreRatioT P t : ℝ) - ((2 * P.eps * t : ℝ) : ℂ)) * A t x + 2 * A t x -
      (((D.axisOrder n + 1 : ℕ) : ℂ) * q x ^ k1 * ((-2 * x : ℝ) : ℂ) * (weightPoly a ee t * Θ.eval true t x) +
        q x ^ D.axisOrder n * (weightPoly a ee t * deriv (fun x' => Θ.eval true t x') x))) with hC
  refine ⟨fun t x => ![A t x, B t x, C t x], ?_, ?_⟩
  · have hW := (smooth_weight a ee k1).of_le (m := 1) le_top
    have hAc : ContDiff ℝ 1 (fun p : ℝ × ℝ => A p.1 p.2) := hW.mul eR
    intro k
    fin_cases k
    · simpa using hAc
    · refine contDiff_of_eq (fun p => ?_) (hW.mul eT)
      simp [hB, hq]
    · have hAt := tderiv_mul_contDiff (G := fun t x => weightPoly a ee t * ((1 - x ^ 2 : ℝ) : ℂ) ^ k1)
        (F := fun t x => R.eval false t x) ((smooth_weight _ _ _).of_le le_top) eR tR
      have hc1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => ((p.1 * (1 - p.1) : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (contDiff_fst.mul (contDiff_const.sub contDiff_fst))
      have hc2 : ContDiff ℝ 1 (fun p : ℝ × ℝ => Complex.I * ((n : ℝ) * β * coreRatioT P p.1 : ℝ) -
          ((2 * P.eps * p.1 : ℝ) : ℂ)) := by
        refine (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp ?_)).sub
          (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst))
        exact contDiff_const.mul (((coreRatioT_contDiff P hP).of_le le_top).comp contDiff_fst)
      have hqk : ContDiff ℝ 1 (fun p : ℝ × ℝ => ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ k1 * ((-2 * p.2 : ℝ) : ℂ)) :=
        ((smooth_q.of_le le_top).pow k1).mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_snd))
      have hqk0 : ContDiff ℝ 1 (fun p : ℝ × ℝ => ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ D.axisOrder n) :=
        (smooth_q.of_le le_top).pow _
      have hp := (smooth_p a ee).of_le (m := 1) le_top
      have hall := (contDiff_const (c := Complex.I / ((n * P.m : ℤ) : ℂ))).mul
        ((((hc1.mul hAt).add (hc2.mul hAc)).add ((contDiff_const (c := (2 : ℂ))).mul hAc)).sub
          ((((contDiff_const (c := ((D.axisOrder n + 1 : ℕ) : ℂ))).mul hqk).mul (hp.mul eT)).add
            (hqk0.mul (hp.mul xT))))
      refine contDiff_of_eq (fun p => ?_) hall
      simp [hC, hA, hq, mul_assoc]
  · have hdT : ∀ t x, HasDerivAt (fun x' => Θ.eval true t x') (deriv (fun x' => Θ.eval true t x') x) x := by
      intro t x
      have h1 : DifferentiableAt ℝ (fun x' : ℝ => (t, x')) x :=
        (differentiableAt_const _).prodMk differentiableAt_id
      exact (((eT.differentiable (by norm_num)) _).comp x h1).hasDerivAt
    have hdq : ∀ x : ℝ, HasDerivAt q (((-2 * x : ℝ)) : ℂ) x := by
      intro x
      have := ((hasDerivAt_pow 2 x).const_sub 1).ofReal_comp
      convert this using 1
      push_cast
      ring
    intro t x k
    fin_cases k
    · simp only [reducedField, if_neg h0, hk1]
      simp [hA, hq, pow_succ]
      ring
    · simp only [reducedField, if_neg h0, hk1]
      simp [hB, hq, pow_succ]
      ring
    · show reducedField P D n β t x 2 = q x * C t x
      have hder1 : deriv (fun t' => weightPoly a ee t' * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * R.eval false t' x) t =
          q x * deriv (fun t' => A t' x) t := by
        have e1 : (fun t' => weightPoly a ee t' * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * R.eval false t' x) =
            fun t' => q x * A t' x := by
          funext t'
          simp only [hA, hq, hk1, pow_succ]
          ring
        rw [e1, deriv_const_mul_field]
      have hder2 : deriv (fun x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly a ee t * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
          Θ.eval true t x')) x =
          q x * (((D.axisOrder n + 1 : ℕ) : ℂ) * q x ^ k1 * ((-2 * x : ℝ) : ℂ) * (weightPoly a ee t * Θ.eval true t x) +
            q x ^ D.axisOrder n * (weightPoly a ee t * deriv (fun x' => Θ.eval true t x') x)) := by
        have e2 : (fun x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly a ee t * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
            Θ.eval true t x')) = fun x' => weightPoly a ee t * (q x' ^ (D.axisOrder n + 1) * Θ.eval true t x') := by
          funext x'
          simp only [hq, pow_succ]
          ring
        rw [e2]
        have hh := (((hdq x).pow (D.axisOrder n + 1)).mul (hdT t x)).const_mul (weightPoly a ee t)
        have hh' : HasDerivAt (fun x' => weightPoly a ee t * (q x' ^ (D.axisOrder n + 1) * Θ.eval true t x'))
            (weightPoly a ee t * (((D.axisOrder n + 1 : ℕ) : ℂ) * q x ^ (D.axisOrder n + 1 - 1) * ((-2 * x : ℝ) : ℂ) *
              Θ.eval true t x + q x ^ (D.axisOrder n + 1) * deriv (fun x' => Θ.eval true t x') x)) x := hh
        rw [hh'.deriv]
        simp only [hk1, Nat.add_sub_cancel]
        push_cast
        ring
      simp only [reducedField, if_neg h0, twistedScale, radialScale, heightDeriv]
      try simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [hder1, hder2]
      simp only [hC, hA, hq, hk1, pow_succ]
      ring

private theorem weightPoly_two (a e : ℕ) (t : ℝ) : weightPoly (a + 2) e t = ((t ^ 2 : ℝ) : ℂ) * weightPoly a e t := by
  unfold weightPoly
  push_cast
  ring

private theorem reducedField_wave_originFactor (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) (h0 : n ≠ 0) :
    ∃ H : ℝ → ℝ → Fin 3 → ℂ, (∀ k : Fin 3, ContDiff ℝ 1 (fun p : ℝ × ℝ => H p.1 p.2 k)) ∧
      ∀ t x k, reducedField P D n β t x k = ((1 - x ^ 2 : ℝ) : ℂ) * (((t ^ 2 : ℝ) : ℂ) * H t x k) := by
  obtain ⟨k1, hk1⟩ : ∃ k1, D.axisOrder n = k1 + 1 :=
    ⟨D.axisOrder n - 1, by have := hD.axisOrder_ge n hn h0; omega⟩
  obtain ⟨a, ha⟩ : ∃ a, D.lowOrder n = a + 2 :=
    ⟨D.lowOrder n - 2, by have := hD.lowOrder_ge n hn h0; omega⟩
  have hR := hD.waveRadial n hn h0
  have hT := hD.wavePolar n hn h0
  have eR := spline_eval_contDiff _ hR (by norm_num) (by norm_num)
  have eT := spline_eval_contDiff _ hT (by norm_num) (by norm_num)
  have tR := spline_tderiv_contDiff _ hR (by norm_num) (by norm_num)
  have xT := spline_xderiv_contDiff _ hT (by norm_num) (by norm_num)
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
  refine ⟨fun t x => ![A t x, B t x, C t x], ?_, ?_⟩
  · have hW := (smooth_weight a ee k1).of_le (m := 1) le_top
    have hAc : ContDiff ℝ 1 (fun p : ℝ × ℝ => A p.1 p.2) := hW.mul eR
    intro k
    fin_cases k
    · simpa using hAc
    · refine contDiff_of_eq (fun p => ?_) (hW.mul eT)
      simp [hB, hq]
    · have hAt := tderiv_mul_contDiff (G := fun t x => weightPoly a ee t * ((1 - x ^ 2 : ℝ) : ℂ) ^ k1)
        (F := fun t x => R.eval false t x) ((smooth_weight _ _ _).of_le le_top) eR tR
      have hc1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => ((p.1 * (1 - p.1) : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (contDiff_fst.mul (contDiff_const.sub contDiff_fst))
      have hc3 : ContDiff ℝ 1 (fun p : ℝ × ℝ => ((2 * (1 - p.1) : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_fst))
      have hc2 : ContDiff ℝ 1 (fun p : ℝ × ℝ => Complex.I * ((n : ℝ) * β * coreRatioT P p.1 : ℝ) -
          ((2 * P.eps * p.1 : ℝ) : ℂ)) := by
        refine (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp ?_)).sub
          (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst))
        exact contDiff_const.mul (((coreRatioT_contDiff P hP).of_le le_top).comp contDiff_fst)
      have hqk : ContDiff ℝ 1 (fun p : ℝ × ℝ => ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ k1 * ((-2 * p.2 : ℝ) : ℂ)) :=
        ((smooth_q.of_le le_top).pow k1).mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_snd))
      have hqk0 : ContDiff ℝ 1 (fun p : ℝ × ℝ => ((1 - p.2 ^ 2 : ℝ) : ℂ) ^ D.axisOrder n) :=
        (smooth_q.of_le le_top).pow _
      have hp := (smooth_p a ee).of_le (m := 1) le_top
      have hall := (contDiff_const (c := Complex.I / ((n * P.m : ℤ) : ℂ))).mul
        (((((hc1.mul hAt).add (hc3.mul hAc)).add (hc2.mul hAc)).add ((contDiff_const (c := (2 : ℂ))).mul hAc)).sub
          ((((contDiff_const (c := ((D.axisOrder n + 1 : ℕ) : ℂ))).mul hqk).mul (hp.mul eT)).add
            (hqk0.mul (hp.mul xT))))
      refine contDiff_of_eq (fun p => ?_) hall
      simp [hC, hA, hq, mul_assoc]
  · have hdT : ∀ t x, HasDerivAt (fun x' => Θ.eval true t x') (deriv (fun x' => Θ.eval true t x') x) x := by
      intro t x
      have h1 : DifferentiableAt ℝ (fun x' : ℝ => (t, x')) x :=
        (differentiableAt_const _).prodMk differentiableAt_id
      exact (((eT.differentiable (by norm_num)) _).comp x h1).hasDerivAt
    have hdA : ∀ t x, HasDerivAt (fun t' => A t' x) (deriv (fun t' => A t' x) t) t := by
      intro t x
      have h1 : DifferentiableAt ℝ (fun t' : ℝ => (t', x)) t :=
        differentiableAt_id.prodMk (differentiableAt_const _)
      have hAc : ContDiff ℝ 1 (fun p : ℝ × ℝ => A p.1 p.2) := ((smooth_weight a ee k1).of_le le_top).mul eR
      exact (((hAc.differentiable (by norm_num)) _).comp t h1).hasDerivAt
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
    · simp only [reducedField, if_neg h0, hk1, ha, weightPoly_two]
      simp [hA, hq, pow_succ]
      ring
    · simp only [reducedField, if_neg h0, hk1, ha, weightPoly_two]
      simp [hB, hq, pow_succ]
      ring
    · show reducedField P D n β t x 2 = q x * (((t ^ 2 : ℝ) : ℂ) * C t x)
      have hder1 : deriv (fun t' => weightPoly (D.lowOrder n) ee t' * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
          R.eval false t' x) t = q x * (((2 * t : ℝ) : ℂ) * A t x + ((t ^ 2 : ℝ) : ℂ) * deriv (fun t' => A t' x) t) := by
        have e1 : (fun t' => weightPoly (D.lowOrder n) ee t' * ((1 - x ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * R.eval false t' x) =
            fun t' => q x * (((t' ^ 2 : ℝ) : ℂ) * A t' x) := by
          funext t'
          simp only [hA, hq, hk1, ha, weightPoly_two, pow_succ]
          ring
        have hm : HasDerivAt (fun t' => ((t' ^ 2 : ℝ) : ℂ) * A t' x)
            (((2 * t : ℝ) : ℂ) * A t x + ((t ^ 2 : ℝ) : ℂ) * deriv (fun t' => A t' x) t) t := (hdt2 t).mul (hdA t x)
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
          simp only [hq, ha, weightPoly_two, pow_succ]
          ring
        rw [e2]
        have hh := (((hdq x).pow (D.axisOrder n + 1)).mul (hdT t x)).const_mul (((t ^ 2 : ℝ) : ℂ) * weightPoly a ee t)
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
        simp only [hA, hq, hk1, ha, weightPoly_two, pow_succ]
        ring
      rw [eA]
      simp only [hC, hq]
      push_cast
      ring

theorem planePhase_contDiff (j : ℤ) :
    ContDiff ℝ 1 (fun w : ℂ => ((‖w‖ ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (((j : ℝ) * Complex.arg w : ℝ) : ℂ))) := by
  set Φ : ℂ → ℂ := fun w => ((‖w‖ ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (((j : ℝ) * Complex.arg w : ℝ) : ℂ))
    with hΦ
  have hsm : ∀ w : ℂ, w ≠ 0 → ContDiffAt ℝ 1 Φ w := by
    intro w hw
    have hev : ∀ᶠ z in nhds w, z ≠ 0 := eventually_ne_nhds hw
    have heq : (fun z : ℂ => ((‖z‖ ^ 2 : ℝ) : ℂ) * (z * ((‖z‖⁻¹ : ℝ) : ℂ)) ^ j) =ᶠ[nhds w] Φ := by
      filter_upwards [hev] with z hz
      simp only [hΦ]
      rw [exp_arg_int z hz j]
      congr 2
      push_cast
      rw [div_eq_mul_inv]
    refine ContDiffAt.congr_of_eventuallyEq ?_ heq.symm
    have hn : ContDiffAt ℝ ⊤ (fun z : ℂ => ‖z‖⁻¹) w :=
      (contDiffAt_norm ℝ hw).inv (norm_ne_zero_iff.2 hw)
    have hu : ContDiffAt ℝ ⊤ (fun z : ℂ => z * ((‖z‖⁻¹ : ℝ) : ℂ)) w :=
      contDiffAt_id.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp w hn)
    have hu0 : w * ((‖w‖⁻¹ : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero hw (by exact_mod_cast (inv_ne_zero (norm_ne_zero_iff.2 hw)))
    have hz : ContDiffAt ℝ ⊤ (fun z : ℂ => (z * ((‖z‖⁻¹ : ℝ) : ℂ)) ^ j) w := by
      obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg j
      · simpa using hu.pow m
      · simp only [zpow_neg, zpow_natCast]
        exact (hu.pow m).inv (pow_ne_zero _ hu0)
    have hq : ContDiffAt ℝ ⊤ (fun z : ℂ => ((‖z‖ ^ 2 : ℝ) : ℂ)) w :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp w (contDiff_norm_sq ℝ).contDiffAt
    exact (hq.mul hz).of_le le_top
  have hnorm : ∀ w, ‖Φ w‖ = ‖w‖ ^ 2 := by
    intro w
    simp only [hΦ, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  have hd0 : HasFDerivAt Φ (0 : ℂ →L[ℝ] ℂ) 0 := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have h00 : Φ 0 = 0 := by simp [hΦ]
    simp only [zero_add, h00, sub_zero, zero_apply]
    refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hc] with h hh
    rw [hnorm, sq]
    have : ‖h‖ < c := by simpa using hh
    exact mul_le_mul_of_nonneg_right this.le (norm_nonneg _)
  have hdiff : ∀ w, DifferentiableAt ℝ Φ w := by
    intro w
    by_cases hw : w = 0
    · subst hw
      exact hd0.differentiableAt
    · exact (hsm w hw).differentiableAt (by norm_num)
  have hcont : ∀ w : ℂ, w ≠ 0 → ContinuousAt (fderiv ℝ Φ) w := fun w hw =>
    ((hsm w hw).fderiv_right (m := 0) (by norm_num)).continuousAt
  have hhom : ∀ w : ℂ, w ≠ 0 → fderiv ℝ Φ w = ‖w‖ • fderiv ℝ Φ (((‖w‖⁻¹ : ℝ) : ℂ) * w) := by
    intro w hw
    set c : ℝ := ‖w‖ with hc
    have hc0 : 0 < c := norm_pos_iff.2 hw
    set u : ℂ := ((c⁻¹ : ℝ) : ℂ) * w with hu
    have hcu : (c : ℂ) * u = w := by
      rw [hu, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hc0.ne', Complex.ofReal_one, one_mul]
    have hscale : (fun v : ℂ => Φ ((c : ℂ) * v)) = fun v => ((c ^ 2 : ℝ) : ℂ) * Φ v := by
      funext v
      simp only [hΦ]
      rw [Complex.arg_real_mul v hc0, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
      push_cast
      ring
    have hlin : HasFDerivAt (fun v : ℂ => (c : ℂ) * v) (c • ContinuousLinearMap.id ℝ ℂ) u := by
      have := (hasFDerivAt_id (𝕜 := ℝ) u).const_smul c
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_)
      simp [Complex.real_smul]
    have h1 : HasFDerivAt (fun v : ℂ => Φ ((c : ℂ) * v)) ((fderiv ℝ Φ w).comp (c • ContinuousLinearMap.id ℝ ℂ)) u := by
      have hw' : HasFDerivAt Φ (fderiv ℝ Φ w) ((c : ℂ) * u) := by
        rw [hcu]
        exact (hdiff w).hasFDerivAt
      exact hw'.comp u hlin
    have h2 : HasFDerivAt (fun v : ℂ => Φ ((c : ℂ) * v)) ((c ^ 2) • fderiv ℝ Φ u) u := by
      rw [hscale]
      have := ((hdiff u).hasFDerivAt).const_smul (c ^ 2)
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_)
      simp [Complex.real_smul]
    have h3 := h1.unique h2
    rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id, sq, mul_smul] at h3
    exact smul_right_injective _ hc0.ne' h3
  obtain ⟨M, hM⟩ : ∃ M, ∀ u ∈ Metric.sphere (0 : ℂ) 1, ‖fderiv ℝ Φ u‖ ≤ M := by
    have hco : ContinuousOn (fderiv ℝ Φ) (Metric.sphere (0 : ℂ) 1) := by
      intro u hu
      have hu0 : u ≠ 0 := by
        intro h
        rw [h] at hu
        simp at hu
      exact (hcont u hu0).continuousWithinAt
    obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn hco
    exact ⟨M, hM⟩
  have hbound : ∀ w : ℂ, ‖fderiv ℝ Φ w‖ ≤ M * ‖w‖ := by
    intro w
    by_cases hw : w = 0
    · subst hw
      rw [hd0.fderiv]
      simp
    · rw [hhom w hw, norm_smul, norm_norm, mul_comm]
      refine mul_le_mul_of_nonneg_right (hM _ ?_) (norm_nonneg _)
      rw [mem_sphere_zero_iff_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 (norm_pos_iff.2 hw)), inv_mul_cancel₀ (norm_ne_zero_iff.2 hw)]
  refine contDiff_one_iff_fderiv.2 ⟨hdiff, continuous_iff_continuousAt.2 fun w => ?_⟩
  by_cases hw : w = 0
  · subst hw
    rw [ContinuousAt, hd0.fderiv]
    refine squeeze_zero_norm' (Filter.Eventually.of_forall hbound) ?_
    have ht : Filter.Tendsto (fun x : ℂ => M * ‖x‖) (nhds 0) (nhds (M * ‖(0 : ℂ)‖)) :=
      (continuous_const.mul continuous_norm).tendsto 0
    simpa using ht
  · exact hcont w hw

private theorem field_contDiffAt_gen' (P : ChartParams) (hP : IsChartParams P) (R : ℝ → ℝ → Fin 3 → ℂ)
    (ph : Space → ℂ) (y : Space) (hy : y ≠ 0)
    (hR : ∀ k : Fin 3, ContDiffAt ℝ 1 (fun x => ph x * R (chartT P x) (heightRatio x) k) y) :
    ContDiffAt ℝ 1 (fun y => ofComponents (fun i => ((decayFactor P y : ℂ) * (ph y *
      (R (chartT P y) (heightRatio y) 0 * radialVec y i +
        R (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        R (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re)) y := by
  rw [contDiffAt_piLp]
  intro j
  simp only [ofComponents_apply']
  have hv : ∀ f : Space → ℝ, ContDiffAt ℝ ⊤ f y → ContDiffAt ℝ 1 (fun x => (f x : ℂ)) y :=
    fun f hf => ofReal_contDiffAt (hf.of_le le_top)
  have hd := hv _ (decayFactor_contDiffAt P hP hy)
  have h0 := (hd.mul (hR 0)).mul (hv _ (radialVec_contDiffAt hy j))
  have h1 := (hd.mul (hR 1)).mul (hv _ (polarVecQ_contDiffAt hy j))
  have h2 := (hd.mul (hR 2)).mul (hv _ (azimVecQ_contDiffAt hy j))
  refine (Complex.reCLM.contDiff.contDiffAt.comp y ((h0.add h1).add h2)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, Complex.reCLM_apply]
  congr 1
  ring

private theorem one_sub_heightRatio_sq (y : Space) (hy : y ≠ 0) :
    1 - heightRatio y ^ 2 = ‖planeOf y‖ ^ 2 / ‖y‖ ^ 2 := by
  have hn : ‖y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne hy)
  have e1 : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [sq_abs]
  have e2 : ‖planeOf y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [planeOf]
    ring
  unfold heightRatio
  rw [div_pow, e2]
  field_simp
  linarith

theorem modeFieldOf_contDiffAt_axis_of (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) (h0 : n ≠ 0) (y : Space) (hy : y ≠ 0) :
    ContDiffAt ℝ 1 (modeFieldOf P D β n) y := by
  obtain ⟨H, hH, hRH⟩ := reducedField_wave_axisFactor P hP hD β n hn h0
  refine field_contDiffAt_gen' P hP (reducedField P D n β) (modePhase P n β) y hy (fun k => ?_)
  have hev : ∀ᶠ z in nhds y, z ≠ 0 := eventually_ne_nhds hy
  have heq : (fun z => ((‖planeOf z‖ ^ 2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * Complex.arg (planeOf z) : ℝ) : ℂ)) *
      ((‖z‖ ^ 2)⁻¹ : ℝ) * Complex.exp (Complex.I * ((n * β * logPhase P z : ℝ) : ℂ)) *
      H (chartT P z) (heightRatio z) k) =ᶠ[nhds y]
      (fun z => modePhase P n β z * reducedField P D n β (chartT P z) (heightRatio z) k) := by
    filter_upwards [hev] with z hz
    rw [hRH, one_sub_heightRatio_sq z hz]
    unfold modePhase
    have ea : Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * angleOf z + n * β * logPhase P z : ℝ) : ℂ)) =
        Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * Complex.arg (planeOf z) : ℝ) : ℂ)) *
          Complex.exp (Complex.I * ((n * β * logPhase P z : ℝ) : ℂ)) := by
      rw [← Complex.exp_add, ← mul_add]
      congr 2
      push_cast
      simp [angleOf, planeOf]
    rw [ea]
    push_cast
    ring
  refine ContDiffAt.congr_of_eventuallyEq ?_ heq.symm
  have hA := (planePhase_contDiff (n * P.m)).contDiffAt.comp y ((planeOf_contDiff.of_le le_top).contDiffAt)
  have hB : ContDiffAt ℝ 1 (fun z : Space => (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ)) y :=
    ofReal_contDiffAt ((((contDiff_norm_sq ℝ).contDiffAt).inv (pow_ne_zero 2 (norm_ne hy))).of_le le_top)
  have hC : ContDiffAt ℝ 1 (fun z => Complex.exp (Complex.I * ((n * β * logPhase P z : ℝ) : ℂ))) y :=
    (Complex.contDiff_exp.contDiffAt.comp y (contDiffAt_const.mul (ofReal_contDiffAt
      (contDiffAt_const.mul ((logPhase_contDiff P hP).contDiffAt))))).of_le le_top
  have hc : ContDiffAt ℝ 1 (fun x => (chartT P x, heightRatio x)) y :=
    ((chartT_contDiffAt P hP hy).of_le le_top).prodMk ((heightRatio_contDiffAt hy).of_le le_top)
  have hD' : ContDiffAt ℝ 1 (fun z => H (chartT P z) (heightRatio z) k) y := (hH k).comp_contDiffAt y hc
  exact ((hA.mul hB).mul hC).mul hD'

private theorem quad_hasFDerivAt {f : Space → ℂ} (C r : ℝ) (hC : 0 ≤ C) (hr : 0 < r)
    (hv : ∀ y, ‖y‖ < r → ‖f y‖ ≤ C * ‖y‖ ^ 2) : HasFDerivAt f (0 : Space →L[ℝ] ℂ) 0 := by
    have h00 : f 0 = 0 := by
      have := hv 0 (by simpa using hr)
      simpa using this
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, h00, sub_zero, ContinuousLinearMap.zero_apply]
    refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
    have hc1 : 0 < c / (C + 1) := div_pos hc (by linarith)
    filter_upwards [Metric.ball_mem_nhds (0 : Space) (lt_min hr hc1)] with h hh
    rw [Metric.mem_ball, dist_zero_right, lt_min_iff] at hh
    have h2 : (C + 1) * ‖h‖ ≤ c := by
      have := hh.2
      rw [lt_div_iff₀ (by linarith)] at this
      linarith
    calc ‖f h‖ ≤ C * ‖h‖ ^ 2 := hv h hh.1
      _ ≤ (C + 1) * ‖h‖ * ‖h‖ := by nlinarith [norm_nonneg h]
      _ ≤ c * ‖h‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg h)

private theorem origin_crit {f : Space → ℂ} (C r : ℝ) (hC : 0 ≤ C) (hr : 0 < r) (β : Space → ℝ)
    (hβ : ContinuousAt β 0) (hβ0 : β 0 = 0)
    (hf : ∀ y, y ≠ 0 → ‖y‖ < r → ContDiffAt ℝ 1 f y)
    (hv : ∀ y, ‖y‖ < r → ‖f y‖ ≤ C * ‖y‖ ^ 2)
    (hd : ∀ y, y ≠ 0 → ‖y‖ < r → ‖fderiv ℝ f y‖ ≤ β y) : ContDiffAt ℝ 1 f 0 := by
  have hd0 := quad_hasFDerivAt C r hC hr hv
  refine contDiffAt_one_iff.2 ⟨fderiv ℝ f, Metric.ball 0 r, Metric.ball_mem_nhds 0 hr, ?_, ?_⟩
  · intro y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    by_cases h0 : y = 0
    · subst h0
      refine ContinuousAt.continuousWithinAt ?_
      rw [ContinuousAt, hd0.fderiv]
      refine squeeze_zero_norm' (a := β) ?_ ?_
      · filter_upwards [Metric.ball_mem_nhds (0 : Space) hr] with z hz
        rw [Metric.mem_ball, dist_zero_right] at hz
        by_cases hz0 : z = 0
        · subst hz0
          rw [hd0.fderiv, hβ0]
          simp
        · exact hd z hz0 hz
      · have ht := hβ.tendsto
        rwa [hβ0] at ht
    · exact ((hf y h0 hy).fderiv_right (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  · intro y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    by_cases h0 : y = 0
    · subst h0
      rw [hd0.fderiv]
      exact hd0
    · exact ((hf y h0 hy).differentiableAt (by norm_num)).hasFDerivAt

private theorem prod_fderiv_bound {F G : Space → ℂ} {y : Space} (hF : DifferentiableAt ℝ F y)
    (hG : DifferentiableAt ℝ G y) {a b c d : ℝ} (h1 : ‖F y‖ ≤ a) (h2 : ‖fderiv ℝ F y‖ ≤ b) (h3 : ‖G y‖ ≤ c)
    (h4 : ‖fderiv ℝ G y‖ ≤ d) : ‖fderiv ℝ (fun z => F z * G z) y‖ ≤ a * d + c * b := by
  have e : (fun z => F z * G z) = F * G := rfl
  rw [e, (hF.hasFDerivAt.mul hG.hasFDerivAt).fderiv]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul]
    exact mul_le_mul h1 h4 (norm_nonneg _) ((norm_nonneg _).trans h1)
  · rw [norm_smul]
    exact mul_le_mul h3 h2 (norm_nonneg _) ((norm_nonneg _).trans h3)

private theorem dir_slope (y z : Space) (hy : y ≠ 0) :
    ‖(‖z‖, ‖z‖⁻¹ • z) - (‖y‖, ‖y‖⁻¹ • y)‖ ≤ (1 + 2 / ‖y‖) * ‖z - y‖ := by
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have e1 : |‖z‖ - ‖y‖| ≤ ‖z - y‖ := abs_norm_sub_norm_le z y
  have e2 : ‖‖z‖⁻¹ • z - ‖y‖⁻¹ • y‖ ≤ 2 / ‖y‖ * ‖z - y‖ := by
    have split : ‖z‖⁻¹ • z - ‖y‖⁻¹ • y = (‖z‖⁻¹ - ‖y‖⁻¹) • z + ‖y‖⁻¹ • (z - y) := by
      rw [sub_smul, smul_sub]
      abel
    rw [split]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_norm]
    have k1 : |‖z‖⁻¹ - ‖y‖⁻¹| * ‖z‖ ≤ ‖z - y‖ / ‖y‖ := by
      by_cases hz : z = 0
      · subst hz
        simp
        positivity
      · have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
        have ez : (‖z‖⁻¹ - ‖y‖⁻¹) * ‖z‖ = (‖y‖ - ‖z‖) / ‖y‖ := by field_simp
        calc |‖z‖⁻¹ - ‖y‖⁻¹| * ‖z‖ = |(‖z‖⁻¹ - ‖y‖⁻¹) * ‖z‖| := by rw [abs_mul, abs_norm]
          _ = |‖y‖ - ‖z‖| / ‖y‖ := by rw [ez, abs_div, abs_norm]
          _ ≤ ‖z - y‖ / ‖y‖ := div_le_div_of_nonneg_right (by rw [abs_sub_comm]; exact e1) hn.le
    have k2 : ‖y‖⁻¹ * ‖z - y‖ = ‖z - y‖ / ‖y‖ := by rw [inv_mul_eq_div]
    rw [k2]
    have : 2 / ‖y‖ * ‖z - y‖ = ‖z - y‖ / ‖y‖ + ‖z - y‖ / ‖y‖ := by ring
    rw [this]
    linarith
  rw [Prod.mk_sub_mk]
  refine (norm_prod_le_iff.2 ⟨?_, ?_⟩)
  · rw [Real.norm_eq_abs]
    refine e1.trans ?_
    have : 0 ≤ 2 / ‖y‖ * ‖z - y‖ := by positivity
    nlinarith [norm_nonneg (z - y)]
  · refine e2.trans ?_
    nlinarith [norm_nonneg (z - y)]

private theorem dir_fderiv_bound (y : Space) (hy : y ≠ 0) :
    ‖fderiv ℝ (fun z : Space => (‖z‖, ‖z‖⁻¹ • z)) y‖ ≤ 1 + 2 / ‖y‖ :=
  norm_fderiv_le_of_lip' ℝ (by positivity) (Filter.Eventually.of_forall fun z => dir_slope y z hy)

private theorem dir_contDiffAt (y : Space) (hy : y ≠ 0) :
    ContDiffAt ℝ ⊤ (fun z : Space => (‖z‖, ‖z‖⁻¹ • z)) y :=
  (contDiffAt_norm ℝ hy).prodMk (((contDiffAt_norm ℝ hy).inv (norm_ne_zero_iff.2 hy)).smul contDiffAt_id)

private theorem comp_dir_bounds (ψ : ℝ × Space → ℂ) (r0 : ℝ)
    (hψ : ∀ p ∈ (Set.Icc 0 r0) ×ˢ Metric.sphere (0 : Space) 1, ContDiffAt ℝ 1 ψ p) :
    ∃ B, 0 ≤ B ∧ ∀ y : Space, y ≠ 0 → ‖y‖ ≤ r0 →
      ContDiffAt ℝ 1 (fun z => ψ (‖z‖, ‖z‖⁻¹ • z)) y ∧
      ‖ψ (‖y‖, ‖y‖⁻¹ • y)‖ ≤ B ∧ ‖fderiv ℝ (fun z => ψ (‖z‖, ‖z‖⁻¹ • z)) y‖ ≤ B * (1 + 2 / ‖y‖) := by
  have hK : IsCompact ((Set.Icc 0 r0) ×ˢ Metric.sphere (0 : Space) 1) := isCompact_Icc.prod (isCompact_sphere 0 1)
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn (f := ψ)
    (fun p hp => (hψ p hp).continuousAt.continuousWithinAt)
  obtain ⟨B2, hB2⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ ψ)
    (fun p hp => ((hψ p hp).fderiv_right (m := 0) (by norm_num)).continuousAt.continuousWithinAt)
  refine ⟨max (max B1 B2) 0, le_max_right _ _, fun y hy hyr => ?_⟩
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hmem : (‖y‖, ‖y‖⁻¹ • y) ∈ (Set.Icc 0 r0) ×ˢ Metric.sphere (0 : Space) 1 := by
    refine ⟨⟨norm_nonneg _, hyr⟩, ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']
  have hΛ := dir_contDiffAt y hy
  have hc : ContDiffAt ℝ 1 (fun z => ψ (‖z‖, ‖z‖⁻¹ • z)) y := (hψ _ hmem).comp y (hΛ.of_le le_top)
  refine ⟨hc, (hB1 _ hmem).trans (le_max_of_le_left (le_max_left _ _)), ?_⟩
  have e : (fun z : Space => ψ (‖z‖, ‖z‖⁻¹ • z)) = ψ ∘ (fun z : Space => (‖z‖, ‖z‖⁻¹ • z)) := rfl
  rw [e, fderiv_comp y ((hψ _ hmem).differentiableAt (by norm_num)) (hΛ.differentiableAt (by simp))]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact mul_le_mul ((hB2 _ hmem).trans (le_max_of_le_left (le_max_right _ _))) (dir_fderiv_bound y hy)
    (norm_nonneg _) (le_max_right _ _)

private theorem planeOf_sq_le (y : Space) : ‖planeOf y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  have e1 : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [sq_abs]
  have e2 : ‖planeOf y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [planeOf]
    ring
  rw [e1, e2]
  nlinarith [sq_nonneg (y 2)]

private def originProfile (P : ChartParams) (n : ℤ) (β : ℝ) (K : ℝ → ℝ → Fin 3 → ℂ) (i : Fin 3)
    (p : ℝ × Space) : ℂ :=
  (((1 - p.1 / (p.1 + P.L0)) ^ (2 * P.eps) : ℝ) : ℂ) * ((((p.1 + P.L0) ^ 2)⁻¹ : ℝ) : ℂ) *
    Complex.exp (Complex.I * ((n * β * ((1 / 2) * Real.log (1 + p.1 ^ 2 / P.rc ^ 2)) : ℝ) : ℂ)) *
    (K (p.1 / (p.1 + P.L0)) (p.2 2) 0 * ((p.2 i : ℝ) : ℂ) +
      K (p.1 / (p.1 + P.L0)) (p.2 2) 1 * ((![p.2 2 * p.2 0, p.2 2 * p.2 1, -(1 - p.2 2 ^ 2)] i : ℝ) : ℂ) +
      K (p.1 / (p.1 + P.L0)) (p.2 2) 2 * ((![-(p.2 1), p.2 0, 0] i : ℝ) : ℂ))

private theorem originProfile_contDiffAt (P : ChartParams) (hP : IsChartParams P) (n : ℤ) (β : ℝ)
    (K : ℝ → ℝ → Fin 3 → ℂ) (hK : ∀ k : Fin 3, ContDiff ℝ 1 (fun p : ℝ × ℝ => K p.1 p.2 k)) (i : Fin 3)
    (p : ℝ × Space) (hp : 0 ≤ p.1) : ContDiffAt ℝ 1 (originProfile P n β K i) p := by
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
  have hKc : ∀ k : Fin 3, ContDiffAt ℝ 1 (fun q : ℝ × Space => K (q.1 / (q.1 + P.L0)) (q.2 2) k) p := fun k =>
    (hK k).comp_contDiffAt p ((hτ.of_le le_top).prodMk ((hu 2).of_le le_top))
  have hc : ∀ f : ℝ × Space → ℝ, ContDiffAt ℝ ⊤ f p → ContDiffAt ℝ 1 (fun q => (f q : ℂ)) p :=
    fun f hf => (Complex.ofRealCLM.contDiff.contDiffAt.comp p hf).of_le le_top
  have hE : ContDiffAt ℝ 1 (fun q : ℝ × Space =>
      Complex.exp (Complex.I * ((n * β * ((1 / 2) * Real.log (1 + q.1 ^ 2 / P.rc ^ 2)) : ℝ) : ℂ))) p :=
    Complex.contDiff_exp.contDiffAt.comp p (contDiffAt_const.mul (hc _ (contDiffAt_const.mul (contDiffAt_const.mul hlog))))
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
  exact (((hc _ hdec).mul (hc _ hinv)).mul hE).mul
    ((((hKc 0).mul (hc _ (hu i))).add ((hKc 1).mul (hc _ hv1))).add ((hKc 2).mul (hc _ hv2)))

private theorem phase_origin_factor (P : ChartParams) (hP : IsChartParams P) (n : ℤ) (β : ℝ) (y : Space)
    (hy : y ≠ 0) (c : ℂ) :
    modePhase P n β y * (((1 - heightRatio y ^ 2 : ℝ) : ℂ) * (((chartT P y ^ 2 : ℝ) : ℂ) * c)) =
      ((‖planeOf y‖ ^ 2 : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * Complex.arg (planeOf y) : ℝ) : ℂ)) *
        ((((‖y‖ + P.L0) ^ 2)⁻¹ : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((n * β * ((1 / 2) * Real.log (1 + ‖y‖ ^ 2 / P.rc ^ 2)) : ℝ) : ℂ)) * c := by
  have hn : ‖y‖ ≠ 0 := norm_ne hy
  have hL : ‖y‖ + P.L0 ≠ 0 := by have := hP.L0_pos; positivity
  rw [one_sub_heightRatio_sq y hy]
  unfold modePhase chartT logPhase
  have ea : Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * angleOf y + n * β * ((1 / 2) * Real.log (1 + ‖y‖ ^ 2 / P.rc ^ 2)) : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * Complex.arg (planeOf y) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((n * β * ((1 / 2) * Real.log (1 + ‖y‖ ^ 2 / P.rc ^ 2)) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← mul_add]
    congr 2
    push_cast
    simp [angleOf, planeOf]
  rw [ea]
  have hn' : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  have hL' : ((‖y‖ : ℂ) + (P.L0 : ℂ)) ≠ 0 := by exact_mod_cast hL
  push_cast
  field_simp

theorem modeFieldOf_contDiffAt_origin_wave (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) (h0 : n ≠ 0) :
    ContDiffAt ℝ 1 (modeFieldOf P D β n) 0 := by
  obtain ⟨K, hK, hRK⟩ := reducedField_wave_originFactor P hP hD β n hn h0
  set Φ : ℂ → ℂ := fun w => ((‖w‖ ^ 2 : ℝ) : ℂ) *
    Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * Complex.arg w : ℝ) : ℂ)) with hΦdef
  have hΦ : ContDiff ℝ 1 Φ := planePhase_contDiff (n * P.m)
  have hF : ContDiff ℝ 1 (fun y => Φ (planeOf y)) := hΦ.comp (planeOf_contDiff.of_le le_top)
  have hFv : ∀ y, ‖Φ (planeOf y)‖ ≤ 1 * ‖y‖ ^ 2 := by
    intro y
    simp only [hΦdef, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real, Real.norm_eq_abs,
      one_mul]
    rw [abs_of_nonneg (by positivity)]
    exact planeOf_sq_le y
  have hF0 : HasFDerivAt (fun y => Φ (planeOf y)) (0 : Space →L[ℝ] ℂ) 0 :=
    quad_hasFDerivAt 1 1 zero_le_one one_pos (fun y _ => hFv y)
  have key : ∀ i y, (modeFieldOf P D β n y) i =
      (Φ (planeOf y) * originProfile P n β K i (‖y‖, ‖y‖⁻¹ • y)).re := by
    intro i y
    rw [modeFieldOf, ofComponents_apply']
    congr 1
    by_cases hy : y = 0
    · subst hy
      have hz : ∀ k, reducedField P D n β (chartT P 0) (heightRatio 0) k = 0 := by
        intro k
        rw [hRK]
        simp [chartT]
      have hp0 : planeOf 0 = 0 := by apply Complex.ext <;> simp [planeOf]
      simp [hz, hΦdef, hp0]
    · have hsm : ∀ j : Fin 3, (‖y‖⁻¹ • y) j = y j / ‖y‖ := by
        intro j
        rw [PiLp.smul_apply, smul_eq_mul, div_eq_inv_mul]
      have hph := fun c => phase_origin_factor P hP n β y hy c
      simp only [originProfile, hsm, hRK]
      have e2 : ‖y‖ / (‖y‖ + P.L0) = chartT P y := rfl
      have e3 : y 2 / ‖y‖ = heightRatio y := rfl
      have e1 : ((1 - chartT P y) ^ (2 * P.eps)) = decayFactor P y := rfl
      rw [e2, e3, e1]
      linear_combination (norm := skip)
        ((decayFactor P y : ℂ) * (radialVec y i : ℂ)) * hph (K (chartT P y) (heightRatio y) 0) +
          ((decayFactor P y : ℂ) * (polarVecQ y i : ℂ)) * hph (K (chartT P y) (heightRatio y) 1) +
          ((decayFactor P y : ℂ) * (azimVecQ y i : ℂ)) * hph (K (chartT P y) (heightRatio y) 2)
      fin_cases i <;> simp [radialVec, polarVecQ, azimVecQ, qOf, hΦdef] <;> push_cast <;> ring
  rw [contDiffAt_piLp]
  intro i
  have ef : (fun y => (modeFieldOf P D β n y) i) =
      fun y => (Φ (planeOf y) * originProfile P n β K i (‖y‖, ‖y‖⁻¹ • y)).re := funext (key i)
  rw [ef]
  obtain ⟨B, hB0, hB⟩ := comp_dir_bounds (originProfile P n β K i) 1
    (fun p hp => originProfile_contDiffAt P hP n β K hK i p hp.1.1)
  suffices hg : ContDiffAt ℝ 1 (fun y => Φ (planeOf y) * originProfile P n β K i (‖y‖, ‖y‖⁻¹ • y)) 0 from
    Complex.reCLM.contDiff.contDiffAt.comp (0 : Space) hg
  refine origin_crit B 1 hB0 one_pos
    (fun y => B * ‖fderiv ℝ (fun z => Φ (planeOf z)) y‖ + B * (‖y‖ ^ 2 + 2 * ‖y‖)) ?_ ?_ ?_ ?_ ?_
  · exact ((continuous_const.mul ((hF.continuous_fderiv (by norm_num)).norm)).add
      (continuous_const.mul ((continuous_norm.pow 2).add (continuous_const.mul continuous_norm)))).continuousAt
  · simp [hF0.fderiv]
  · intro y hy hyr
    exact hF.contDiffAt.mul (hB y hy hyr.le).1
  · intro y hyr
    by_cases hy : y = 0
    · subst hy
      have hp0 : planeOf 0 = 0 := by apply Complex.ext <;> simp [planeOf]
      simp [hΦdef, hp0]
    · rw [norm_mul]
      have h1 := hFv y
      have h2 := (hB y hy hyr.le).2.1
      rw [one_mul] at h1
      calc ‖Φ (planeOf y)‖ * ‖originProfile P n β K i (‖y‖, ‖y‖⁻¹ • y)‖ ≤ ‖y‖ ^ 2 * B :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = B * ‖y‖ ^ 2 := by ring
  · intro y hy hyr
    have hn : ‖y‖ ≠ 0 := norm_ne hy
    have h1 := hFv y
    rw [one_mul] at h1
    have hb := prod_fderiv_bound (hF.differentiable (by norm_num) y)
      ((hB y hy hyr.le).1.differentiableAt (by norm_num)) h1 le_rfl (hB y hy hyr.le).2.1 (hB y hy hyr.le).2.2
    refine hb.trans (le_of_eq ?_)
    field_simp
    ring


private theorem origin_crit_eps {f : Space → ℂ} (C r : ℝ) (hC : 0 ≤ C) (hr : 0 < r)
    (hf : ∀ y, y ≠ 0 → ‖y‖ < r → ContDiffAt ℝ 1 f y)
    (hv : ∀ y, ‖y‖ < r → ‖f y‖ ≤ C * ‖y‖ ^ 2)
    (hd : ∀ ε > 0, ∃ δ > 0, ∀ y, y ≠ 0 → ‖y‖ < δ → ‖fderiv ℝ f y‖ ≤ ε) : ContDiffAt ℝ 1 f 0 := by
  have hd0 := quad_hasFDerivAt C r hC hr hv
  refine contDiffAt_one_iff.2 ⟨fderiv ℝ f, Metric.ball 0 r, Metric.ball_mem_nhds 0 hr, ?_, ?_⟩
  · intro y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    by_cases h0 : y = 0
    · subst h0
      refine ContinuousAt.continuousWithinAt ?_
      rw [Metric.continuousAt_iff]
      intro ε hε
      obtain ⟨δ, hδ, hδd⟩ := hd (ε / 2) (by positivity)
      refine ⟨δ, hδ, fun z hz => ?_⟩
      rw [dist_zero_right] at hz
      rw [hd0.fderiv, dist_zero_right]
      by_cases hz0 : z = 0
      · subst hz0
        rw [hd0.fderiv]
        simpa using hε
      · exact (hδd z hz0 hz).trans_lt (by linarith)
    · exact ((hf y h0 hy).fderiv_right (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  · intro y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    by_cases h0 : y = 0
    · subst h0
      rw [hd0.fderiv]
      exact hd0
    · exact ((hf y h0 hy).differentiableAt (by norm_num)).hasFDerivAt

private theorem slice_deriv_zero {χ : ℝ × Space → ℂ} (h0 : ∀ u, χ (0, u) = 0) (u : Space)
    (hd : DifferentiableAt ℝ χ (0, u)) (v : Space) : fderiv ℝ χ (0, u) (0, v) = 0 := by
  have h1 : HasFDerivAt (fun w : Space => χ (0, w))
      ((fderiv ℝ χ (0, u)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) u :=
    hd.hasFDerivAt.comp u (hasFDerivAt_prodMk_right (0 : ℝ) u)
  have e : (fun w : Space => χ (0, w)) = fun _ => 0 := funext h0
  rw [e] at h1
  have h2 := h1.unique (hasFDerivAt_const (0 : ℂ) u)
  have h3 := congrArg (fun L : Space →L[ℝ] ℂ => L v) h2
  simpa using h3

private theorem slice_bound {χ : ℝ × Space → ℂ} {B : ℝ} (u : Space) (r : ℝ) (hr : 0 ≤ r)
    (hd : ∀ s ∈ Set.Icc 0 r, DifferentiableAt ℝ χ (s, u))
    (hB : ∀ s ∈ Set.Icc 0 r, ‖fderiv ℝ χ (s, u)‖ ≤ B) :
    ‖χ (r, u) - χ (0, u)‖ ≤ B * r := by
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s : ℝ => χ (s, u))
    (f' := fun s => fderiv ℝ χ (s, u) ((1 : ℝ), (0 : Space))) (C := B) (a := 0) (b := r) ?_ ?_ r ⟨hr, le_rfl⟩
  · simpa using key
  · intro s hs
    have hl : HasDerivAt (fun s' : ℝ => (s', u)) ((1 : ℝ), (0 : Space)) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s u)
    exact ((hd s hs).hasFDerivAt.comp_hasDerivAt s hl).hasDerivWithinAt
  · intro s hs
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have e : ‖((1 : ℝ), (0 : Space))‖ = 1 := by simp
    rw [e, mul_one]
    exact hB s (Set.Ico_subset_Icc_self hs)

private theorem norm_mul_slice_contDiffAt {χ : ℝ × Space → ℂ}
    (hχ : ∀ p : ℝ × Space, 0 ≤ p.1 → ContDiffAt ℝ 1 χ p) (h0 : ∀ u, χ (0, u) = 0) :
    ContDiffAt ℝ 1 (fun y : Space => (‖y‖ : ℂ) * χ (‖y‖, ‖y‖⁻¹ • y)) 0 := by
  have hK : IsCompact ((Set.Icc (0 : ℝ) 1) ×ˢ Metric.sphere (0 : Space) 1) :=
    isCompact_Icc.prod (isCompact_sphere 0 1)
  have hcont : ContinuousOn (fderiv ℝ χ) ((Set.Icc (0 : ℝ) 1) ×ˢ Metric.sphere (0 : Space) 1) := fun p hp =>
    ((hχ p hp.1.1).fderiv_right (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn hcont
  have hB0 : 0 ≤ max B1 0 := le_max_right _ _
  have hB : ∀ p ∈ (Set.Icc (0 : ℝ) 1) ×ˢ Metric.sphere (0 : Space) 1, ‖fderiv ℝ χ p‖ ≤ max B1 0 :=
    fun p hp => (hB1 p hp).trans (le_max_left _ _)
  have huc := hK.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  have hdiff : ∀ p : ℝ × Space, 0 ≤ p.1 → DifferentiableAt ℝ χ p := fun p hp =>
    (hχ p hp).differentiableAt (by norm_num)
  have hsph : ∀ y : Space, y ≠ 0 → ‖y‖⁻¹ • y ∈ Metric.sphere (0 : Space) 1 := by
    intro y hy
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hy)]
  have hval : ∀ y : Space, ‖y‖ ≤ 1 → ‖χ (‖y‖, ‖y‖⁻¹ • y)‖ ≤ max B1 0 * ‖y‖ := by
    intro y hy1
    by_cases hy : y = 0
    · subst hy
      simp [h0]
    · have := slice_bound (χ := χ) (B := max B1 0) (‖y‖⁻¹ • y) ‖y‖ (norm_nonneg _)
        (fun s hs => hdiff _ hs.1) (fun s hs => hB _ ⟨⟨hs.1, hs.2.trans hy1⟩, hsph y hy⟩)
      rwa [h0, sub_zero] at this
  have hnorm_slope : ∀ y : Space, ‖fderiv ℝ (fun z : Space => (‖z‖ : ℂ)) y‖ ≤ 1 := by
    intro y
    refine norm_fderiv_le_of_lip' ℝ zero_le_one (Filter.Eventually.of_forall fun z => ?_)
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, one_mul]
    exact abs_norm_sub_norm_le z y
  refine origin_crit_eps (max B1 0) 1 hB0 one_pos ?_ ?_ ?_
  · intro y hy _
    exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp y (contDiffAt_norm ℝ hy)).of_le le_top).mul
      ((hχ _ (norm_nonneg y)).comp y ((dir_contDiffAt y hy).of_le le_top))
  · intro y hy
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    calc ‖y‖ * ‖χ (‖y‖, ‖y‖⁻¹ • y)‖ ≤ ‖y‖ * (max B1 0 * ‖y‖) :=
          mul_le_mul_of_nonneg_left (hval y hy.le) (norm_nonneg _)
      _ = max B1 0 * ‖y‖ ^ 2 := by ring
  · intro ε hε
    obtain ⟨δ1, hδ1, hδ1c⟩ := huc (ε / 6) (by positivity)
    refine ⟨min (min δ1 1) (ε / (4 * max B1 0 + 1)), by positivity, fun y hy hyd => ?_⟩
    have hyd1 : ‖y‖ < δ1 := hyd.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hy1 : ‖y‖ < 1 := hyd.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hyε : ‖y‖ < ε / (4 * max B1 0 + 1) := hyd.trans_le (min_le_right _ _)
    have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
    have hΛK : (‖y‖, ‖y‖⁻¹ • y) ∈ (Set.Icc (0 : ℝ) 1) ×ˢ Metric.sphere (0 : Space) 1 :=
      ⟨⟨hn.le, hy1.le⟩, hsph y hy⟩
    have h0K : ((0 : ℝ), ‖y‖⁻¹ • y) ∈ (Set.Icc (0 : ℝ) 1) ×ˢ Metric.sphere (0 : Space) 1 :=
      ⟨⟨le_rfl, zero_le_one⟩, hsph y hy⟩
    have hdist : dist (‖y‖, ‖y‖⁻¹ • y) ((0 : ℝ), ‖y‖⁻¹ • y) < δ1 := by
      have e : dist (‖y‖, ‖y‖⁻¹ • y) ((0 : ℝ), ‖y‖⁻¹ • y) = ‖y‖ := by
        simp [Prod.dist_eq]
      rw [e]
      exact hyd1
    have hclose : ‖fderiv ℝ χ (‖y‖, ‖y‖⁻¹ • y) - fderiv ℝ χ (0, ‖y‖⁻¹ • y)‖ < ε / 6 := by
      rw [← dist_eq_norm]
      exact hδ1c _ hΛK _ h0K hdist
    have hnc1 : ContDiffAt ℝ 1 (fun z : Space => ‖z‖) y := contDiffAt_norm ℝ hy
    have hnd : DifferentiableAt ℝ (fun z : Space => ‖z‖) y := hnc1.differentiableAt (by simp)
    have hud : DifferentiableAt ℝ (fun z : Space => ‖z‖⁻¹ • z) y :=
      ((hnc1.inv (norm_ne_zero_iff.2 hy)).smul contDiffAt_id).differentiableAt (by simp)
    have hΛ : HasFDerivAt (fun z : Space => (‖z‖, ‖z‖⁻¹ • z))
        ((fderiv ℝ (fun z : Space => ‖z‖) y).prod (fderiv ℝ (fun z : Space => ‖z‖⁻¹ • z) y)) y :=
      hnd.hasFDerivAt.prodMk hud.hasFDerivAt
    have hΛn : ‖(fderiv ℝ (fun z : Space => ‖z‖) y).prod (fderiv ℝ (fun z : Space => ‖z‖⁻¹ • z) y)‖ ≤
        1 + 2 / ‖y‖ := by
      rw [← hΛ.fderiv]
      exact dir_fderiv_bound y hy
    have hAn : ‖fderiv ℝ (fun z : Space => ‖z‖) y‖ ≤ 1 := by
      refine norm_fderiv_le_of_lip' ℝ zero_le_one (Filter.Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, one_mul]
      exact abs_norm_sub_norm_le z y
    have hχc : HasFDerivAt (fun z : Space => χ (‖z‖, ‖z‖⁻¹ • z))
        ((fderiv ℝ χ (‖y‖, ‖y‖⁻¹ • y)).comp
          ((fderiv ℝ (fun z : Space => ‖z‖) y).prod (fderiv ℝ (fun z : Space => ‖z‖⁻¹ • z) y))) y :=
      (hdiff _ hn.le).hasFDerivAt.comp y hΛ
    have hnc : HasFDerivAt (fun z : Space => (‖z‖ : ℂ)) (fderiv ℝ (fun z : Space => (‖z‖ : ℂ)) y) y :=
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp y hnc1).differentiableAt (by simp)).hasFDerivAt
    have hprod : HasFDerivAt (fun z : Space => (‖z‖ : ℂ) * χ (‖z‖, ‖z‖⁻¹ • z))
        ((‖y‖ : ℂ) • ((fderiv ℝ χ (‖y‖, ‖y‖⁻¹ • y)).comp
          ((fderiv ℝ (fun z : Space => ‖z‖) y).prod (fderiv ℝ (fun z : Space => ‖z‖⁻¹ • z) y))) +
          χ (‖y‖, ‖y‖⁻¹ • y) • fderiv ℝ (fun z : Space => (‖z‖ : ℂ)) y) y := hnc.mul hχc
    rw [hprod.fderiv]
    set A := fderiv ℝ (fun z : Space => ‖z‖) y with hA
    set V := fderiv ℝ (fun z : Space => ‖z‖⁻¹ • z) y with hV
    set u := ‖y‖⁻¹ • y with hu
    have hslice : ‖(fderiv ℝ χ (0, u)).comp (A.prod V)‖ ≤ max B1 0 := by
      refine ContinuousLinearMap.opNorm_le_bound _ hB0 fun h => ?_
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
      have e : ((A h, V h) : ℝ × Space) = (A h, 0) + (0, V h) := by simp
      rw [e, map_add, slice_deriv_zero h0 u (hdiff _ le_rfl), add_zero]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      have h1 : ‖((A h, (0 : Space)) : ℝ × Space)‖ ≤ ‖h‖ := by
        rw [Prod.norm_def]
        simp only [norm_zero]
        refine max_le ((A.le_opNorm h).trans ?_) (norm_nonneg _)
        exact mul_le_of_le_one_left (norm_nonneg _) hAn
      exact mul_le_mul (hB _ h0K) h1 (norm_nonneg _) hB0
    have hsplit : (fderiv ℝ χ (‖y‖, u)).comp (A.prod V) =
        (fderiv ℝ χ (‖y‖, u) - fderiv ℝ χ (0, u)).comp (A.prod V) + (fderiv ℝ χ (0, u)).comp (A.prod V) := by
      rw [ContinuousLinearMap.sub_comp]
      abel
    have hmain : ‖(fderiv ℝ χ (‖y‖, u)).comp (A.prod V)‖ ≤ ε / 6 * (1 + 2 / ‖y‖) + max B1 0 := by
      rw [hsplit]
      refine (norm_add_le _ _).trans (add_le_add ?_ hslice)
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hclose.le hΛn (norm_nonneg _) (by positivity))
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    have hv := hval y hy1.le
    have t1 : ‖y‖ * ‖(fderiv ℝ χ (‖y‖, u)).comp (A.prod V)‖ ≤ ε / 6 * (‖y‖ + 2) + max B1 0 * ‖y‖ := by
      calc _ ≤ ‖y‖ * (ε / 6 * (1 + 2 / ‖y‖) + max B1 0) := mul_le_mul_of_nonneg_left hmain hn.le
        _ = ε / 6 * (‖y‖ + 2) + max B1 0 * ‖y‖ := by field_simp
    have t2 : ‖χ (‖y‖, u)‖ * ‖fderiv ℝ (fun z : Space => (‖z‖ : ℂ)) y‖ ≤ max B1 0 * ‖y‖ :=
      (mul_le_mul hv (hnorm_slope y) (norm_nonneg _) (by positivity)).trans (by rw [mul_one])
    have t3 : 2 * max B1 0 * ‖y‖ ≤ ε / 2 := by
      have : ‖y‖ * (4 * max B1 0 + 1) < ε := by rwa [lt_div_iff₀ (by positivity)] at hyε
      nlinarith
    nlinarith


private def meanCore (D : FieldData) (P : ChartParams) (t x : ℝ) : Fin 3 → ℂ :=
  ![-(weightPoly 0 D.highOrder t *
      heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (D.amp 0).streamAmp.eval true t' x') t x),
    -(((1 - t : ℝ) : ℂ) * deriv (fun t' => weightPoly 1 D.highOrder t' * (D.amp 0).streamAmp.eval true t' x) t -
      ((2 * P.eps * t : ℝ) : ℂ) * (weightPoly 0 D.highOrder t * (D.amp 0).streamAmp.eval true t x) +
      2 * (weightPoly 0 D.highOrder t * (D.amp 0).streamAmp.eval true t x)),
    weightPoly 0 D.highOrder t * (D.amp 0).swirlAmp.eval false t x]

private theorem weightPoly_one (e : ℕ) (t : ℝ) : weightPoly 1 e t = (t : ℂ) * weightPoly 0 e t := by
  unfold weightPoly
  push_cast
  ring

private theorem meanCore_factor (P : ChartParams) (D : FieldData) (β t x : ℝ) (k : Fin 3) :
    reducedField P D 0 β t x k = (t : ℂ) * meanCore D P t x k := by
  fin_cases k
  · simp [reducedField, meanCore, weightPoly_one]
    ring
  · simp [reducedField, meanCore, twistedScale, radialScale, weightPoly_one]
    ring
  · simp [reducedField, meanCore, weightPoly_one]
    ring

private theorem meanCore_contDiff (P : ChartParams) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (hn : (0 : ℤ) ∈ D.modes) (k : Fin 3) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => meanCore D P p.1 p.2 k) := by
  have hS := (hD.meanStream hn).1
  have hG := (hD.meanSwirl hn).1
  have eS := spline_eval_contDiff _ hS (by norm_num) (by norm_num)
  have eG := spline_eval_contDiff _ hG (by norm_num) (by norm_num)
  have tS := spline_tderiv_contDiff _ hS (by norm_num) (by norm_num)
  have xS := spline_xderiv_contDiff _ hS (by norm_num) (by norm_num)
  have hp := (smooth_p 0 D.highOrder).of_le (m := 1) le_top
  fin_cases k
  · have hB := xderiv_mul_contDiff (G := fun t x => ((1 - x ^ 2 : ℝ) : ℂ))
        (F := fun t x => (D.amp 0).streamAmp.eval true t x) (smooth_q.of_le le_top) eS xS
    have hall := (hp.mul hB).neg
    refine contDiff_of_eq (fun p => ?_) hall
    simp [meanCore, heightDeriv]
  · have hA := tderiv_mul_contDiff (G := fun t x => weightPoly 1 D.highOrder t)
        (F := fun t x => (D.amp 0).streamAmp.eval true t x) ((smooth_p 1 D.highOrder).of_le le_top) eS tS
    have hc1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => ((1 - p.1 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_const.sub contDiff_fst)
    have hc2 : ContDiff ℝ 1 (fun p : ℝ × ℝ => ((2 * P.eps * p.1 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst)
    have hpS := hp.mul eS
    have hall := (((hc1.mul hA).sub (hc2.mul hpS)).add ((contDiff_const (c := (2 : ℂ))).mul hpS)).neg
    refine contDiff_of_eq (fun p => ?_) hall
    simp [meanCore]
  · have hall := hp.mul eG
    refine contDiff_of_eq (fun p => ?_) hall
    simp [meanCore]

private theorem meanStream_at_zero (P : ChartParams) {e : ℕ} {D : FieldData} (hD : IsFieldData P e D)
    (hn : (0 : ℤ) ∈ D.modes) (x : ℝ) :
    (D.amp 0).streamAmp.eval true 0 x = ((D.guardStream * x : ℝ) : ℂ) := by
  have hS := (hD.meanStream hn).1
  obtain ⟨-, pt, -, -⟩ := mesh_facts _ hS.mesh.t_sorted hS.mesh.t_first hS.mesh.t_last
  obtain ⟨-, -, cx, -⟩ := mesh_facts _ hS.mesh.x_sorted hS.mesh.x_first hS.mesh.x_last
  have ht : cellIndex (D.amp 0).streamAmp.mesh.tBreaks 0 = 0 := glueIdx_zero _ pt
  have hj : cellIndex (D.amp 0).streamAmp.mesh.xBreaks |x| < cellCount (D.amp 0).streamAmp.mesh.xBreaks := by
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

private theorem meanSwirl_at_zero (P : ChartParams) {e : ℕ} {D : FieldData} (hD : IsFieldData P e D)
    (hn : (0 : ℤ) ∈ D.modes) (x : ℝ) :
    (D.amp 0).swirlAmp.eval false 0 x = ((D.guardSwirl : ℝ) : ℂ) := by
  have hS := (hD.meanSwirl hn).1
  obtain ⟨-, pt, -, -⟩ := mesh_facts _ hS.mesh.t_sorted hS.mesh.t_first hS.mesh.t_last
  obtain ⟨-, -, cx, -⟩ := mesh_facts _ hS.mesh.x_sorted hS.mesh.x_first hS.mesh.x_last
  have ht : cellIndex (D.amp 0).swirlAmp.mesh.tBreaks 0 = 0 := glueIdx_zero _ pt
  have hj : cellIndex (D.amp 0).swirlAmp.mesh.xBreaks |x| < cellCount (D.amp 0).swirlAmp.mesh.xBreaks := by
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

private theorem meanCore_zero (P : ChartParams) {e : ℕ} {D : FieldData} (hD : IsFieldData P e D)
    (hn : (0 : ℤ) ∈ D.modes) (x : ℝ) :
    meanCore D P 0 x 0 = ((-(D.guardStream * (1 - 3 * x ^ 2)) : ℝ) : ℂ) ∧
      meanCore D P 0 x 1 = (((-(3 * D.guardStream * x)) : ℝ) : ℂ) ∧
      meanCore D P 0 x 2 = ((D.guardSwirl : ℝ) : ℂ) := by
  have hS := (hD.meanStream hn).1
  have eS := spline_eval_contDiff _ hS (by norm_num) (by norm_num)
  have hw0 : weightPoly 0 D.highOrder 0 = 1 := by simp [weightPoly]
  refine ⟨?_, ?_, ?_⟩
  · have ef : (fun x' : ℝ => ((1 - x' ^ 2 : ℝ) : ℂ) * (D.amp 0).streamAmp.eval true 0 x') =
        fun x' => (((D.guardStream * (x' - x' ^ 3)) : ℝ) : ℂ) := by
      funext x'
      rw [meanStream_at_zero P hD hn]
      push_cast
      ring
    have hd : HasDerivAt (fun x' : ℝ => (((D.guardStream * (x' - x' ^ 3)) : ℝ) : ℂ))
        (((D.guardStream * (1 - 3 * x ^ 2)) : ℝ) : ℂ) x := by
      have h1 := (((hasDerivAt_id x).sub (hasDerivAt_pow 3 x)).const_mul D.guardStream).ofReal_comp
      refine h1.congr_deriv ?_
      norm_num
    simp only [meanCore, Matrix.cons_val_zero, heightDeriv, hw0, one_mul]
    rw [ef, hd.deriv]
    push_cast
    ring
  · have hΨ : HasDerivAt (fun t' : ℝ => (D.amp 0).streamAmp.eval true t' x)
        (deriv (fun t' : ℝ => (D.amp 0).streamAmp.eval true t' x) 0) 0 := by
      have h1 : DifferentiableAt ℝ (fun t' : ℝ => (t', x)) 0 :=
        differentiableAt_id.prodMk (differentiableAt_const _)
      exact (((eS.differentiable (by norm_num)) _).comp (0 : ℝ) h1).hasDerivAt
    have hp : HasDerivAt (fun t' : ℝ => weightPoly 1 D.highOrder t') (1 : ℂ) 0 := by
      have h1 := ((hasDerivAt_pow 1 (0 : ℝ)).mul (((hasDerivAt_id (0 : ℝ)).const_sub 1).pow D.highOrder)).ofReal_comp
      refine h1.congr_deriv ?_
      simp [Pi.pow_apply]
    have hd : HasDerivAt (fun t' : ℝ => weightPoly 1 D.highOrder t' * (D.amp 0).streamAmp.eval true t' x)
        (1 * (D.amp 0).streamAmp.eval true 0 x +
          weightPoly 1 D.highOrder 0 * deriv (fun t' : ℝ => (D.amp 0).streamAmp.eval true t' x) 0) 0 :=
      hp.mul hΨ
    simp only [meanCore, Matrix.cons_val_one, Matrix.cons_val_zero, hw0, one_mul]
    rw [hd.deriv, meanStream_at_zero P hD hn]
    simp [weightPoly]
    ring
  · simp only [meanCore, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hw0, one_mul]
    exact meanSwirl_at_zero P hD hn x


private def meanProfile (P : ChartParams) (D : FieldData) (i : Fin 3) (p : ℝ × Space) : ℂ :=
  (((1 - p.1 / (p.1 + P.L0)) ^ (2 * P.eps) : ℝ) : ℂ) * (((p.1 + P.L0)⁻¹ : ℝ) : ℂ) *
    (meanCore D P (p.1 / (p.1 + P.L0)) (p.2 2) 0 * ((p.2 i : ℝ) : ℂ) +
      meanCore D P (p.1 / (p.1 + P.L0)) (p.2 2) 1 * ((![p.2 2 * p.2 0, p.2 2 * p.2 1, -(1 - p.2 2 ^ 2)] i : ℝ) : ℂ) +
      meanCore D P (p.1 / (p.1 + P.L0)) (p.2 2) 2 * ((![-(p.2 1), p.2 0, 0] i : ℝ) : ℂ))

private theorem meanProfile_contDiffAt (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (hn : (0 : ℤ) ∈ D.modes) (i : Fin 3)
    (p : ℝ × Space) (hp : 0 ≤ p.1) : ContDiffAt ℝ 1 (meanProfile P D i) p := by
  have hL := hP.L0_pos
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
  have hinv : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => (q.1 + P.L0)⁻¹) p :=
    (hr.add contDiffAt_const).inv hne
  have hu : ∀ j : Fin 3, ContDiffAt ℝ ⊤ (fun q : ℝ × Space => q.2 j) p := fun j =>
    ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd).contDiffAt
  have hKc : ∀ k : Fin 3, ContDiffAt ℝ 1 (fun q : ℝ × Space => meanCore D P (q.1 / (q.1 + P.L0)) (q.2 2) k) p :=
    fun k => by
      have hτx : ContDiffAt ℝ 1 (fun q : ℝ × Space => (q.1 / (q.1 + P.L0), q.2 2)) p :=
        (hτ.of_le le_top).prodMk ((hu 2).of_le le_top)
      have h := (meanCore_contDiff P hD hn k).contDiffAt.comp p hτx
      simpa only [Function.comp_def] using h
  have hc : ∀ f : ℝ × Space → ℝ, ContDiffAt ℝ ⊤ f p → ContDiffAt ℝ 1 (fun q => (f q : ℂ)) p :=
    fun f hf => (Complex.ofRealCLM.contDiff.contDiffAt.comp p hf).of_le le_top
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
  have hsum : ContDiffAt ℝ 1 (fun q : ℝ × Space =>
      meanCore D P (q.1 / (q.1 + P.L0)) (q.2 2) 0 * ((q.2 i : ℝ) : ℂ) +
        meanCore D P (q.1 / (q.1 + P.L0)) (q.2 2) 1 *
          ((![q.2 2 * q.2 0, q.2 2 * q.2 1, -(1 - q.2 2 ^ 2)] i : ℝ) : ℂ) +
        meanCore D P (q.1 / (q.1 + P.L0)) (q.2 2) 2 * ((![-(q.2 1), q.2 0, 0] i : ℝ) : ℂ)) p :=
    (((hKc 0).mul (hc _ (hu i))).add ((hKc 1).mul (hc _ hv1))).add ((hKc 2).mul (hc _ hv2))
  have hpre : ContDiffAt ℝ 1 (fun q : ℝ × Space =>
      (((1 - q.1 / (q.1 + P.L0)) ^ (2 * P.eps) : ℝ) : ℂ) * (((q.1 + P.L0)⁻¹ : ℝ) : ℂ)) p :=
    (hc _ hdec).mul (hc _ hinv)
  exact hpre.mul hsum

private def meanLinear (P : ChartParams) (D : FieldData) (i : Fin 3) (y : Space) : ℂ :=
  ((P.L0⁻¹ * ![-(D.guardStream * y 0) - D.guardSwirl * y 1, -(D.guardStream * y 1) + D.guardSwirl * y 0,
    2 * D.guardStream * y 2] i : ℝ) : ℂ)

private theorem meanLinear_contDiff (P : ChartParams) (D : FieldData) (i : Fin 3) :
    ContDiff ℝ 1 (meanLinear P D i) := by
  have h0 := (coord_contDiff 0).of_le (m := 1) le_top
  have h1 := (coord_contDiff 1).of_le (m := 1) le_top
  have h2 := (coord_contDiff 2).of_le (m := 1) le_top
  refine Complex.ofRealCLM.contDiff.comp (contDiff_const.mul ?_)
  fin_cases i
  · simpa using (contDiff_const.mul h0).neg.sub (contDiff_const.mul h1)
  · simpa using (contDiff_const.mul h1).neg.add (contDiff_const.mul h0)
  · simpa using contDiff_const.mul h2

private theorem meanProfile_origin (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (hn : (0 : ℤ) ∈ D.modes) (i : Fin 3) (y : Space) :
    (‖y‖ : ℂ) * meanProfile P D i (0, ‖y‖⁻¹ • y) = meanLinear P D i y := by
  have hL := hP.L0_pos
  by_cases hy : y = 0
  · subst hy
    fin_cases i <;> simp [meanLinear]
  · have hsm : ∀ j : Fin 3, (‖y‖⁻¹ • y) j = y j / ‖y‖ := by
      intro j
      rw [PiLp.smul_apply, smul_eq_mul, div_eq_inv_mul]
    obtain ⟨c0, c1, c2⟩ := meanCore_zero P hD hn (y 2 / ‖y‖)
    have hn' : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne hy
    have hL' : (P.L0 : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    simp only [meanProfile, hsm, zero_div, zero_add, sub_zero, Real.one_rpow, Complex.ofReal_one, one_mul, c0, c1, c2]
    fin_cases i <;> simp [meanLinear] <;> field_simp <;> ring

private theorem modeField_mean_eq (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (β : ℝ)
    (i : Fin 3) (y : Space) :
    (modeFieldOf P D β 0 y) i = ((‖y‖ : ℂ) * meanProfile P D i (‖y‖, ‖y‖⁻¹ • y)).re := by
  rw [modeFieldOf, ofComponents_apply']
  congr 1
  have hph : modePhase P 0 β y = 1 := by simp [modePhase]
  rw [hph, one_mul]
  simp only [meanCore_factor]
  by_cases hy : y = 0
  · subst hy
    simp [chartT]
  · have hsm : ∀ j : Fin 3, (‖y‖⁻¹ • y) j = y j / ‖y‖ := by
      intro j
      rw [PiLp.smul_apply, smul_eq_mul, div_eq_inv_mul]
    have hn' : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne hy
    have hLp : (‖y‖ : ℂ) + (P.L0 : ℂ) ≠ 0 := by
      have : ‖y‖ + P.L0 ≠ 0 := by have := hP.L0_pos; positivity
      exact_mod_cast this
    simp only [meanProfile, hsm]
    have e2 : ‖y‖ / (‖y‖ + P.L0) = chartT P y := rfl
    have e3 : y 2 / ‖y‖ = heightRatio y := rfl
    have e1 : ((1 - chartT P y) ^ (2 * P.eps)) = decayFactor P y := rfl
    rw [e2, e3, e1]
    fin_cases i <;> simp [radialVec, polarVecQ, azimVecQ, qOf, heightRatio, chartT] <;> field_simp

theorem modeFieldOf_contDiffAt_origin_mean (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {D : FieldData}
    (hD : IsFieldData P e D) (β : ℝ) (hn : (0 : ℤ) ∈ D.modes) :
    ContDiffAt ℝ 1 (modeFieldOf P D β 0) 0 := by
  rw [contDiffAt_piLp]
  intro i
  have ef : (fun y => (modeFieldOf P D β 0 y) i) =
      fun y => ((‖y‖ : ℂ) * meanProfile P D i (‖y‖, ‖y‖⁻¹ • y)).re :=
    funext (modeField_mean_eq P hP D β i)
  rw [ef]
  have hψ : ∀ p : ℝ × Space, 0 ≤ p.1 → ContDiffAt ℝ 1 (meanProfile P D i) p :=
    fun p hp => meanProfile_contDiffAt P hP hD hn i p hp
  have hχ : ∀ p : ℝ × Space, 0 ≤ p.1 →
      ContDiffAt ℝ 1 (fun q : ℝ × Space => meanProfile P D i q - meanProfile P D i (0, q.2)) p := by
    intro p hp
    have hz : ContDiffAt ℝ 1 (fun q : ℝ × Space => ((0 : ℝ), q.2)) p := contDiffAt_const.prodMk contDiffAt_snd
    have h2 : ContDiffAt ℝ 1 (meanProfile P D i ∘ fun q : ℝ × Space => ((0 : ℝ), q.2)) p :=
      (hψ (0, p.2) le_rfl).comp p hz
    exact (hψ p hp).sub h2
  have hc := norm_mul_slice_contDiffAt hχ (fun u => sub_self _)
  have e2 : (fun y : Space => (‖y‖ : ℂ) * meanProfile P D i (‖y‖, ‖y‖⁻¹ • y)) =
      fun y => (‖y‖ : ℂ) * (meanProfile P D i (‖y‖, ‖y‖⁻¹ • y) - meanProfile P D i (0, ‖y‖⁻¹ • y)) +
        meanLinear P D i y := by
    funext y
    rw [← meanProfile_origin P hP hD hn i y]
    ring
  have hg : ContDiffAt ℝ 1 (fun y : Space => (‖y‖ : ℂ) * meanProfile P D i (‖y‖, ‖y‖⁻¹ • y)) 0 := by
    rw [e2]
    exact hc.add ((meanLinear_contDiff P D i).contDiffAt)
  exact Complex.reCLM.contDiff.contDiffAt.comp (0 : Space) hg

theorem modeFieldOf_contDiff_wave (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {tb : ℝ} {D : FieldData}
    (hc : IsCompactFieldData P e tb D) (hpos : 0 < tb) (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) (h0 : n ≠ 0) :
    ContDiff ℝ 1 (modeFieldOf P D β n) := by
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  by_cases hy : y = 0
  · subst hy
    exact modeFieldOf_contDiffAt_origin_wave P hP hc.field β n hn h0
  exact modeFieldOf_contDiffAt_axis_of P hP hc.field β n hn h0 y hy

theorem modeFieldOf_contDiff_mean (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {tb : ℝ} {D : FieldData}
    (hc : IsCompactFieldData P e tb D) (hpos : 0 < tb) (β : ℝ) (hn : (0 : ℤ) ∈ D.modes) :
    ContDiff ℝ 1 (modeFieldOf P D β 0) := by
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  by_cases hy : y = 0
  · subst hy
    exact modeFieldOf_contDiffAt_origin_mean P hP hc.field β hn
  · have hph : modePhase P 0 β = fun _ => 1 := by
      funext z
      simp [modePhase]
    refine modeFieldOf_contDiffAt_of P hP D β 0 (reducedField_mean_contDiff P hP hc.field β hn) y hy ?_
    rw [hph]
    exact contDiffAt_const

end GivenFields

end CellCert

end Breakdown
