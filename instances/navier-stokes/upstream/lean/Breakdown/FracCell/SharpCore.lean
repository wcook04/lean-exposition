import Breakdown.FracCell.SharpCoreSt
import Breakdown.FracCell.CellSharpBound

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace SharpCoreInternal

lemma ep_add (s t t' : Fin 3 → Fin 3 → ℂ) :
    entryPairing s (fun a b => t a b + t' a b) = entryPairing s t + entryPairing s t' := by
  simp only [entryPairing, map_add, mul_add, Finset.sum_add_distrib]

lemma vp_add (s t t' : Fin 3 → ℂ) :
    CellScalars.vecPair s (fun a => t a + t' a) = CellScalars.vecPair s t + CellScalars.vecPair s t' := by
  simp only [CellScalars.vecPair, map_add, mul_add, Finset.sum_add_distrib]

lemma pen_add (hs ha : ℝ) (σ Z W : Fin 3 → Fin 3 → ℂ) :
    strainPen hs ha σ (fun i q => Z i q + W i q) = strainPen hs ha σ Z + strainLin σ W := by
  have e1 : (fun a b => ((fun i q => Z i q + W i q) a b + (fun i q => Z i q + W i q) b a) / 2)
      = fun a b => (Z a b + Z b a) / 2 + (W a b + W b a) / 2 := by
    funext a b; ring
  have e2 : (fun a b => ((fun i q => Z i q + W i q) a b - (fun i q => Z i q + W i q) b a) / 2)
      = fun a b => (Z a b - Z b a) / 2 + (W a b - W b a) / 2 := by
    funext a b; ring
  unfold strainPen strainLin
  rw [e1, e2, ep_add, ep_add]
  simp only [Complex.add_re]
  ring

lemma vpen_add (hv : ℝ) (τ Z W : Fin 3 → ℂ) :
    velPen hv τ (fun i => Z i + W i) = velPen hv τ Z + velLin τ W := by
  unfold velPen velLin
  rw [vp_add, Complex.add_re]
  ring

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) {slots : ℕ}
  (R : CellRows N slots k) (B : CellBases)

lemma target_split (μ : Fin N → ℝ) (κ ζ : Fin k → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (n : ℤ) (j l : ℕ) :
    CellScalars.targetStrain c K S R B μ κ ζ v G n j l = fun i q =>
      CellScalars.targetStrain c K S R B (fun _ => 0) κ ζ v G n j l i q
        + CellScalars.rowStrainTarget c K S R B μ n j l i q := by
  funext i q
  simp only [CellScalars.targetStrain, CellScalars.rowStrainTarget]
  split_ifs <;> simp

lemma vtarget_split (μ : Fin N → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (n : ℤ) (j l : ℕ) :
    CellScalars.targetVelocity c K S R B μ v G n j l = fun i =>
      CellScalars.targetVelocity c K S R B (fun _ => 0) v G n j l i
        + CellScalars.rowVelocityTarget c K R B μ n j l i := by
  funext i
  simp [CellScalars.targetVelocity, CellScalars.rowVelocityTarget]

lemma strain_split (μ : Fin N → ℝ) (κ ζ : Fin k → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (σ : ℤ → ℕ → ℕ → Fin 3 → Fin 3 → ℂ) (n : ℤ) (j l : ℕ) :
    CellScalars.sharpStrainTerm c K S R B μ κ ζ v G σ n j l
      = CellScalars.sharpStrainTerm c K S R B (fun _ => 0) κ ζ v G σ n j l
        + CellScalars.rowStrainTerm c K S R B μ σ n j l := by
  unfold CellScalars.sharpStrainTerm CellScalars.rowStrainTerm
  split_ifs
  · rw [target_split c K S R B μ κ ζ v G n j l, pen_add]
  · simp

lemma vel_split (μ : Fin N → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (τ : ℤ → ℕ → ℕ → Fin 3 → ℂ) (n : ℤ) (j l : ℕ) :
    CellScalars.sharpVelocityTerm c K S R B μ v G τ n j l
      = CellScalars.sharpVelocityTerm c K S R B (fun _ => 0) v G τ n j l
        + CellScalars.rowVelocityTerm c K S R B μ τ n j l := by
  unfold CellScalars.sharpVelocityTerm CellScalars.rowVelocityTerm
  split_ifs
  · rw [vtarget_split c K S R B μ v G n j l, vpen_add]
  · simp

lemma far_split (μ : Fin N → ℝ) (κ ζ : Fin k → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (σ : ℤ → ℕ → ℕ → Fin 3 → Fin 3 → ℂ)
    (τ : ℤ → ℕ → ℕ → Fin 3 → ℂ) (jl : ℕ × ℕ) :
    CellScalars.sharpFarTerm c K S R B μ κ ζ v G σ τ jl
      = CellScalars.sharpFarTerm c K S R B (fun _ => 0) κ ζ v G σ τ jl
        + CellScalars.rowFarTerm c K S R B μ σ τ jl := by
  unfold CellScalars.sharpFarTerm CellScalars.rowFarTerm
  split_ifs
  · have e1 := fun n => strain_split c K S R B μ κ ζ v G σ n jl.1 jl.2
    have e2 := fun n => vel_split c K S R B μ v G τ n jl.1 jl.2
    simp only [e1, e2, Finset.sum_add_distrib]
    ring
  · simp

lemma form_split (μ : Fin N → ℝ) (κ ζ : Fin k → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (σ : ℤ → ℕ → ℕ → Fin 3 → Fin 3 → ℂ)
    (τ : ℤ → ℕ → ℕ → Fin 3 → ℂ)
    (h0 : Summable (CellScalars.sharpFarTerm c K S R B (fun _ => 0) κ ζ v G σ τ))
    (hμ : Summable (CellScalars.sharpFarTerm c K S R B μ κ ζ v G σ τ)) :
    CellScalars.sharpForm c K S R B μ κ ζ v G σ τ
      = CellScalars.sharpForm c K S R B (fun _ => 0) κ ζ v G σ τ
        + CellScalars.sharpRowForm c K S R B μ σ τ := by
  have hr : Summable (CellScalars.rowFarTerm c K S R B μ σ τ) :=
    (hμ.sub h0).congr fun jl => by
      rw [far_split c K S R B μ κ ζ v G σ τ jl]
      ring
  have e1 := fun n j l => strain_split c K S R B μ κ ζ v G σ n j l
  have e2 := fun n j l => vel_split c K S R B μ v G τ n j l
  have e3 := fun jl => far_split c K S R B μ κ ζ v G σ τ jl
  unfold CellScalars.sharpForm CellScalars.sharpRowForm
  simp only [e1, e2, e3, Finset.sum_add_distrib]
  rw [h0.tsum_add hr]
  ring

end SharpCoreInternal

open CellSharpBoundInternal SharpCoreInternal in
theorem sharpFar_summable (h1 : SharpTargetSquareStatement) {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4)
    {k N : ℕ} {c : FracCellData k N} (hc : IsFormData α c) {K : CellBox} {S : CellScalars} {B : CellBases}
    {Cl : CellClasses} {slots : ℕ} {R : CellRows N slots k} (hd : IsCellData α c K S B Cl R)
    (hax : IsAxisymmetricWeight c K) {x : FieldTuple k} (hx : IsAdmissible c x) (ζ : Fin k → ℝ)
    (μ : Fin N → ℝ) (σ : ℤ → ℕ → ℕ → Fin 3 → Fin 3 → ℂ) (τ : ℤ → ℕ → ℕ → Fin 3 → ℂ)
    (hE : Summable (fun jl : ℕ × ℕ => if S.degNear < max jl.1 jl.2 then
            (∑ n ∈ R.yModes, (S.symWeight n jl.1 jl.2 * symSq (σ n jl.1 jl.2)
              + S.antiWeight n jl.1 jl.2 * antiSq (σ n jl.1 jl.2)))
            + ∑ n ∈ S.resolved, S.velWeight n jl.1 jl.2 * vecSq (τ n jl.1 jl.2)
          else 0)) :
    Summable (CellScalars.sharpFarTerm c K S R B μ x.2.2.2.1 ζ x.1 x.2.1 σ τ) := by
  obtain ⟨hY, hV, hX, hXv⟩ := h1 α hα1 hα2 c hc K S B Cl R hd hax x hx ζ
  have sY : ∀ n ∈ R.yModes, Summable (fun jl : ℕ × ℕ => sumSq (fun a b =>
      B.coef K (fun p => CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b) jl.1 jl.2)) :=
    fun n hn => sumSq_summable
      (fun jl a b => B.coef K (fun p => CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b) jl.1 jl.2)
      (fun a b => coef_summable hd.bases _ (hY n hn a b).1 (hY n hn a b).2)
  have sV : ∀ n ∈ S.resolved, Summable (fun jl : ℕ × ℕ => vecSq (fun a =>
      B.coef K (fun p => CellScalars.yVelocity c K S x.1 x.2.1 n p a) jl.1 jl.2)) :=
    fun n hn => vecSq_summable
      (fun jl a => B.coef K (fun p => CellScalars.yVelocity c K S x.1 x.2.1 n p a) jl.1 jl.2)
      (fun a => coef_summable hd.bases _ (hV n hn a).1 (hV n hn a).2)
  have sW : ∀ n ∈ S.resolved ∪ S.band, Summable (fun jl : ℕ × ℕ => sumSq (fun i q =>
      ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n p i q) jl.1 jl.2)) :=
    fun n hn => combo_summable R.rowSet μ
      (fun a jl i q => B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n p i q) jl.1 jl.2)
      (fun a ha i q => coef_summable hd.bases _ (hX a ha n hn i q).1 (hX a ha n hn i q).2)
  have sWv : ∀ n ∈ S.resolved, Summable (fun jl : ℕ × ℕ => vecSq (fun i =>
      ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingVelocity c K R a n p i) jl.1 jl.2)) :=
    fun n hn => combo_vec_summable R.rowSet μ
      (fun a jl i => B.coef K (fun p => CellScalars.rowCouplingVelocity c K R a n p i) jl.1 jl.2)
      (fun a ha i => coef_summable hd.bases _ (hXv a ha n hn i).1 (hXv a ha n hn i).2)
  have hb := far_y hd R.yModes
    (fun n j l a b => B.coef K (fun p => CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b) j l)
    (fun n j l a => B.coef K (fun p => CellScalars.yVelocity c K S x.1 x.2.1 n p a) j l) sY sV
  have hw := far_y hd (S.resolved ∪ S.band)
    (fun n j l i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) *
      B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n p i q) j l)
    (fun n j l i => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) *
      B.coef K (fun p => CellScalars.rowCouplingVelocity c K R a n p i) j l) sW sWv
  exact far_a hd μ x.2.2.2.1 ζ x.1 x.2.1 σ τ
    (fun n j l a b => B.coef K (fun p => CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b) j l)
    (fun n j l i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) *
      B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n p i q) j l)
    (fun n j l a => B.coef K (fun p => CellScalars.yVelocity c K S x.1 x.2.1 n p a) j l)
    (fun n j l i => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) *
      B.coef K (fun p => CellScalars.rowCouplingVelocity c K R a n p i) j l)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) hE hb hw

open SharpCoreInternal in
theorem sharpCore_of (h1 : SharpTargetSquareStatement) (h2 : SharpSplitStatement) : SharpCoreStatement := by
  intro α hα1 hα2 k N c hc K S B Cl slots R hd hax x hx ζ μ hμ
  obtain ⟨σ, τ, hE, Q, hy, hrow⟩ := h2 α hα1 hα2 c hc K S B Cl R hd hax x hx ζ
  refine ⟨σ, τ, hE, ?_⟩
  have h0 := sharpFar_summable h1 hα1 hα2 hc hd hax hx ζ (fun _ => 0) σ τ hE
  have hm := sharpFar_summable h1 hα1 hα2 hc hd hax hx ζ μ σ τ hE
  rw [form_split c K S R B μ x.2.2.2.1 ζ x.1 x.2.1 σ τ h0 hm]
  have := hrow μ hμ
  linarith

theorem sharpSplit_of (hE : SharpEnergyStatement) (hB : SharpBoundStatement) : SharpSplitStatement := by
  intro α hα1 hα2 k N c hc K S B Cl slots R hd hax x hx ζ
  obtain ⟨Q, hy, hrow⟩ := hB α hα1 hα2 c hc K S B Cl R hd hax x hx ζ
  exact ⟨sharpStrainCoef c K B x, sharpVelocityCoef c K B x, hE α hα1 hα2 c hc K S B Cl R hd hax x hx,
    Q, hy, hrow⟩

theorem sharpCore_of_parts (h1 : SharpTargetSquareStatement) (hE : SharpEnergyStatement)
    (hB : SharpBoundStatement) : SharpCoreStatement :=
  sharpCore_of h1 (sharpSplit_of hE hB)

namespace SharpCoreInternal

lemma eig_nonneg (K : CellBox) (j l : ℕ) : 0 ≤ radialEigen K j + heightEigen K l := by
  unfold radialEigen heightEigen
  split_ifs <;> positivity

lemma lin_bound {w e r L a s t : ℝ} (hL : 0 ≤ L) (hw : w ≤ e * (r * L + a) - s - t) :
    w ≤ (|e| * |r| + |e * a| + |s| + |t|) * (1 + L) := by
  have h1 : e * (r * L) ≤ |e| * |r| * L := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (abs_mul e r).le) hL
  have h2 : e * a ≤ |e * a| := le_abs_self _
  have h3 : -s ≤ |s| := neg_le_abs s
  have h4 : -t ≤ |t| := neg_le_abs t
  have h5 : 0 ≤ (|e * a| + |s| + |t|) * L := by positivity
  have h6 : 0 ≤ |e| * |r| := by positivity
  have e1 : e * (r * L + a) = e * (r * L) + e * a := by ring
  have e2 : (|e| * |r| + |e * a| + |s| + |t|) * (1 + L)
      = |e| * |r| + |e| * |r| * L + (|e * a| + |s| + |t|) + (|e * a| + |s| + |t|) * L := by ring
  rw [e2]
  rw [e1] at hw
  linarith

end SharpCoreInternal

open CellSharpBoundInternal SharpCoreInternal in
theorem sharpEnergy_of (h : SharpCoefTailStatement) : SharpEnergyStatement := by
  intro α hα1 hα2 k N c hc K S B Cl slots R hd hax x hx
  obtain ⟨hs, hv⟩ := h α hα1 hα2 c hc K S B Cl R hd hax x hx
  obtain ⟨_, _, hdeg⟩ := hd.scalars.degrees
  set σ := sharpStrainCoef c K B x
  set τ := sharpVelocityCoef c K B x
  set Lm : ℕ × ℕ → ℝ := fun jl => radialEigen K jl.1 + heightEigen K jl.2 with hLm
  set As : ℤ → ℝ := fun n => |S.energyWeight n| * |CellBox.innerRadius K|
      + |S.energyWeight n * (CellBox.angularWeight K n * (max (modeNumber c.order n - 2) 0) ^ 2)|
      + |S.strainAbsorb n| + |S.tailShift n| with hAs
  set Aa : ℤ → ℝ := fun n => |S.energyWeight n + 2 * S.vorticityWeight n| * |CellBox.innerRadius K|
      + |(S.energyWeight n + 2 * S.vorticityWeight n) *
          (CellBox.angularWeight K n * (max (modeNumber c.order n - 1) 0) ^ 2)|
      + |2 * S.curlAbsorb n + S.strainAbsorb n| + |S.tailShift n| with hAa
  set Av : ℤ → ℝ := fun n => |S.tailShift n| + |S.velocityAbsorb n| with hAv
  have sS : ∀ n ∈ R.yModes, Summable (fun jl : ℕ × ℕ => (1 + Lm jl) * sumSq (σ n jl.1 jl.2)) := by
    intro n hn
    have := summable_sum (s := Finset.univ) fun a _ => summable_sum (s := Finset.univ) fun b _ => hs n hn a b
    refine this.congr fun jl => ?_
    simp only [sumSq, Finset.mul_sum]
    rfl
  have sV : ∀ n ∈ S.resolved, Summable (fun jl : ℕ × ℕ => (1 + Lm jl) * vecSq (τ n jl.1 jl.2)) := by
    intro n hn
    have := summable_sum (s := Finset.univ) fun a _ => hv n hn a
    refine this.congr fun jl => ?_
    simp only [vecSq, Finset.mul_sum]
    rfl
  refine Summable.of_nonneg_of_le (fun jl => ?_) (fun jl => ?_)
    ((summable_sum fun n hn => (sS n hn).mul_left (As n + Aa n)).add
      (summable_sum fun n hn => (sV n hn).mul_left (Av n)))
  · split_ifs with hfar
    · have hlt : S.degHigh < max jl.1 jl.2 := lt_of_le_of_lt (by omega) hfar
      refine add_nonneg (Finset.sum_nonneg fun n _ => add_nonneg ?_ ?_) (Finset.sum_nonneg fun n hn => ?_)
      · exact mul_nonneg (sym_pos hd (Or.inr hlt)).le (symSq_nonneg' _)
      · exact mul_nonneg (anti_pos hd (Or.inr hlt)).le (antiSq_nonneg' _)
      · exact mul_nonneg (vel_pos hd hn hlt.le).le (vecSq_nonneg' _)
    · exact le_refl 0
  · have hL := eig_nonneg K jl.1 jl.2
    have hAs0 : ∀ n, 0 ≤ As n := fun n => by simp only [hAs]; positivity
    have hAa0 : ∀ n, 0 ≤ Aa n := fun n => by simp only [hAa]; positivity
    have hAv0 : ∀ n, 0 ≤ Av n := fun n => by simp only [hAv]; positivity
    have g0 : 0 ≤ (∑ n ∈ R.yModes, (As n + Aa n) * ((1 + Lm jl) * sumSq (σ n jl.1 jl.2)))
        + ∑ n ∈ S.resolved, Av n * ((1 + Lm jl) * vecSq (τ n jl.1 jl.2)) :=
      add_nonneg (Finset.sum_nonneg fun n _ => mul_nonneg (add_nonneg (hAs0 n) (hAa0 n))
          (mul_nonneg (by linarith) (sumSq_nn _)))
        (Finset.sum_nonneg fun n _ => mul_nonneg (hAv0 n) (mul_nonneg (by linarith) (vecSq_nonneg' _)))
    split_ifs with hfar
    · have hlt : S.degHigh < max jl.1 jl.2 := lt_of_le_of_lt (by omega) hfar
      refine add_le_add (Finset.sum_le_sum fun n _ => ?_) (Finset.sum_le_sum fun n hn => ?_)
      · have ws : S.symWeight n jl.1 jl.2 ≤ As n * (1 + Lm jl) := by
          have h0 := (hd.scalars.sym_weight n jl.1 jl.2 (Or.inr hlt)).2
          unfold CellScalars.tailLam at h0
          exact lin_bound hL h0
        have wa : S.antiWeight n jl.1 jl.2 ≤ Aa n * (1 + Lm jl) := by
          have h0 := (hd.scalars.anti_weight n jl.1 jl.2 (Or.inr hlt)).2
          unfold CellScalars.tailLam at h0
          exact lin_bound hL (by linarith)
        have p1 := mul_le_mul ws (symSq_le (σ n jl.1 jl.2)) (symSq_nonneg' _)
          (mul_nonneg (hAs0 n) (by linarith))
        have p2 := mul_le_mul wa (antiSq_le (σ n jl.1 jl.2)) (antiSq_nonneg' _)
          (mul_nonneg (hAa0 n) (by linarith))
        have e : (As n + Aa n) * ((1 + Lm jl) * sumSq (σ n jl.1 jl.2))
            = As n * (1 + Lm jl) * sumSq (σ n jl.1 jl.2) + Aa n * (1 + Lm jl) * sumSq (σ n jl.1 jl.2) := by ring
        rw [e]
        exact add_le_add p1 p2
      · have wv : S.velWeight n jl.1 jl.2 ≤ Av n * (1 + Lm jl) := by
          have h0 := (hd.scalars.vel_weight n hn jl.1 jl.2 hlt.le).2
          have hE0 : 0 ≤ (if S.degHigh ≤ jl.1 then radialEigen K jl.1 else heightEigen K jl.2) ∧
              (if S.degHigh ≤ jl.1 then radialEigen K jl.1 else heightEigen K jl.2) ≤ Lm jl := by
            have r0 : 0 ≤ radialEigen K jl.1 := by unfold radialEigen; split_ifs <;> positivity
            have z0 : 0 ≤ heightEigen K jl.2 := by unfold heightEigen; positivity
            simp only [hLm]
            split_ifs <;> constructor <;> linarith
          have q1 : S.tailShift n * (if S.degHigh ≤ jl.1 then radialEigen K jl.1 else heightEigen K jl.2)
              ≤ |S.tailShift n| * Lm jl :=
            (mul_le_mul_of_nonneg_right (le_abs_self _) hE0.1).trans
              (mul_le_mul_of_nonneg_left hE0.2 (abs_nonneg _))
          have q2 := neg_le_abs (S.velocityAbsorb n)
          have q3 : 0 ≤ |S.velocityAbsorb n| * Lm jl := mul_nonneg (abs_nonneg _) hL
          have e : Av n * (1 + Lm jl) = |S.tailShift n| + |S.velocityAbsorb n|
              + |S.tailShift n| * Lm jl + |S.velocityAbsorb n| * Lm jl := by simp only [hAv]; ring
          rw [e]
          linarith [abs_nonneg (S.tailShift n)]
        have := mul_le_mul_of_nonneg_right wv (vecSq_nonneg' (τ n jl.1 jl.2))
        calc S.velWeight n jl.1 jl.2 * vecSq (τ n jl.1 jl.2) ≤ Av n * (1 + Lm jl) * vecSq (τ n jl.1 jl.2) := this
          _ = Av n * ((1 + Lm jl) * vecSq (τ n jl.1 jl.2)) := by ring
    · exact g0

theorem sharpCore_of_leaves (h1 : SharpTargetSquareStatement) (hT : SharpCoefTailStatement)
    (hB : SharpBoundStatement) : SharpCoreStatement :=
  sharpCore_of_parts h1 (sharpEnergy_of hT) hB

end CellAnalysis

end CellCert

end Breakdown
