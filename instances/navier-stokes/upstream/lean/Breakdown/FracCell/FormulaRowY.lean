import Breakdown.FracCell.StFormulaProof

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis CellAnalysis.CellScalars

namespace FormulaRowY

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)

theorem yStrain_eq (x : FieldTuple k) (ζ : Fin k → ℝ) (n : ℤ) (p : ℝ × ℝ)
    (hs : ∀ n ∈ S.resolved,
      K.lowStrainAt c.order n S.degHigh x.2.1 p = synthStrain S B (augVector c K S B x ζ) n p ∧
        K.lowVelocityAt c.order n S.degHigh x.1 p = synthVelocity S B (augVector c K S B x ζ) n p) :
    yStrain c K S x.2.2.2.1 ζ x.1 x.2.1 n p =
      yStrainOf c K S (synthStrain S B (augVector c K S B x ζ)) (synthVelocity S B (augVector c K S B x ζ))
        (kappaPart S (augVector c K S B x ζ)) (pinPart S (augVector c K S B x ζ)) n p := by
  funext a b
  unfold yStrain yStrainOf
  have h1 : (if n ∈ S.resolved ∪ S.band then ∑ n' ∈ S.resolved, waveActionStrain (strainMode c (n - n') p)
        (curlGradMode c (n - n') p) (K.lowStrainAt c.order n' S.degHigh x.2.1 p)
        (K.lowVelocityAt c.order n' S.degHigh x.1 p) a b else 0) =
      (if n ∈ S.resolved ∪ S.band then ∑ n' ∈ S.resolved, waveActionStrain (strainMode c (n - n') p)
        (curlGradMode c (n - n') p) (synthStrain S B (augVector c K S B x ζ) n' p)
        (synthVelocity S B (augVector c K S B x ζ) n' p) a b else 0) := by
    split_ifs
    · refine Finset.sum_congr rfl fun n' hn' => ?_
      rw [(hs n' hn').1, (hs n' hn').2]
    · rfl
  have h2 : (if n ∈ S.resolved then splitStrain (matAct (S.localMatrix n p)
          (pairVec (K.lowStrainAt c.order n S.degHigh x.2.1 p) (K.lowVelocityAt c.order n S.degHigh x.1 p))) a b
          else 0) =
      (if n ∈ S.resolved then splitStrain (matAct (S.localMatrix n p)
          (pairVec (synthStrain S B (augVector c K S B x ζ) n p)
            (synthVelocity S B (augVector c K S B x ζ) n p))) a b else 0) := by
    split_ifs with h
    · rw [(hs n h).1, (hs n h).2]
    · rfl
  have h3 : (∑ i : Fin k, (((x.2.2.2.1 i / 2 : ℝ) : ℂ) * modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b
          + ((ζ i : ℝ) : ℂ) * modeMat c.order n (c.modelPinField i) p.1 p.2 a b)) =
      ∑ i : Fin k, ((kappaPart S (augVector c K S B x ζ) i / 2) *
          modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b
          + pinPart S (augVector c K S B x ζ) i * modeMat c.order n (c.modelPinField i) p.1 p.2 a b) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [kappaPart, pinPart, augVector, Sum.elim_inr, Sum.elim_inl]
    push_cast
    ring
  rw [h1, h2, h3]

theorem yVelocity_eq (x : FieldTuple k) (ζ : Fin k → ℝ) (n : ℤ) (p : ℝ × ℝ)
    (hs : ∀ n ∈ S.resolved,
      K.lowStrainAt c.order n S.degHigh x.2.1 p = synthStrain S B (augVector c K S B x ζ) n p ∧
        K.lowVelocityAt c.order n S.degHigh x.1 p = synthVelocity S B (augVector c K S B x ζ) n p) :
    yVelocity c K S x.1 x.2.1 n p =
      yVelocityOf c K S (synthStrain S B (augVector c K S B x ζ)) (synthVelocity S B (augVector c K S B x ζ)) n p := by
  funext b
  unfold yVelocity yVelocityOf
  have h1 : (if n ∈ S.resolved ∪ S.band then ∑ n' ∈ S.resolved, waveActionVelocity (curlGradMode c (n' - n) p)
        (K.lowStrainAt c.order n' S.degHigh x.2.1 p) b else 0) =
      (if n ∈ S.resolved ∪ S.band then ∑ n' ∈ S.resolved, waveActionVelocity (curlGradMode c (n' - n) p)
        (synthStrain S B (augVector c K S B x ζ) n' p) b else 0) := by
    split_ifs
    · refine Finset.sum_congr rfl fun n' hn' => ?_
      rw [(hs n' hn').1]
    · rfl
  have h2 : (if n ∈ S.resolved then splitVelocity (matAct (S.localMatrix n p)
          (pairVec (K.lowStrainAt c.order n S.degHigh x.2.1 p) (K.lowVelocityAt c.order n S.degHigh x.1 p))) b
          else 0) =
      (if n ∈ S.resolved then splitVelocity (matAct (S.localMatrix n p)
          (pairVec (synthStrain S B (augVector c K S B x ζ) n p)
            (synthVelocity S B (augVector c K S B x ζ) n p))) b else 0) := by
    split_ifs with h
    · rw [(hs n h).1, (hs n h).2]
    · rfl
  rw [h1, h2]

theorem yFolded_eq (x : FieldTuple k) (ζ : Fin k → ℝ) (n : ℤ) (p : ℝ × ℝ)
    (hs : ∀ n ∈ S.resolved,
      K.lowStrainAt c.order n S.degHigh x.2.1 p = synthStrain S B (augVector c K S B x ζ) n p ∧
        K.lowVelocityAt c.order n S.degHigh x.1 p = synthVelocity S B (augVector c K S B x ζ) n p) :
    yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p =
      yFoldedOf c K S (synthStrain S B (augVector c K S B x ζ)) (synthVelocity S B (augVector c K S B x ζ))
        (kappaPart S (augVector c K S B x ζ)) (pinPart S (augVector c K S B x ζ)) n p := by
  unfold yFolded yFoldedOf
  rw [yStrain_eq c K S B x ζ n p hs, yVelocity_eq c K S B x ζ n p hs]

theorem rect_measurable : MeasurableSet K.rect := by
  unfold CellBox.rect
  exact measurableSet_Icc.prod measurableSet_Icc

theorem coef_yFolded (x : FieldTuple k) (ζ : Fin k → ℝ)
    (hs : ∀ n ∈ S.resolved, ∀ p ∈ K.rect,
      K.lowStrainAt c.order n S.degHigh x.2.1 p = synthStrain S B (augVector c K S B x ζ) n p ∧
        K.lowVelocityAt c.order n S.degHigh x.1 p = synthVelocity S B (augVector c K S B x ζ) n p)
    (n : ℤ) (j l : ℕ) (i q : Fin 3) :
    B.coef K (fun p => yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p i q) j l =
      yCoef c K S B (augVector c K S B x ζ) n j l i q := by
  unfold yCoef CellBases.coef
  refine setIntegral_congr_fun (rect_measurable K) fun p hp => ?_
  simp only
  rw [yFolded_eq c K S B x ζ n p fun n hn => hs n hn p hp]

theorem coef_yVelocity (x : FieldTuple k) (ζ : Fin k → ℝ)
    (hs : ∀ n ∈ S.resolved, ∀ p ∈ K.rect,
      K.lowStrainAt c.order n S.degHigh x.2.1 p = synthStrain S B (augVector c K S B x ζ) n p ∧
        K.lowVelocityAt c.order n S.degHigh x.1 p = synthVelocity S B (augVector c K S B x ζ) n p)
    (n : ℤ) (j l : ℕ) (i : Fin 3) :
    B.coef K (fun p => yVelocity c K S x.1 x.2.1 n p i) j l =
      yVelCoef c K S B (augVector c K S B x ζ) n j l i := by
  unfold yVelCoef CellBases.coef
  refine setIntegral_congr_fun (rect_measurable K) fun p hp => ?_
  simp only
  rw [yVelocity_eq c K S B x ζ n p fun n hn => hs n hn p hp]

theorem pair_term {ι : Type} [Fintype ι] (u y1 y2 : ι → ℂ) (sx ax hs ha : ℂ) :
    ((∑ e, u e * y1 e + ∑ e, u e * y2 e) / 2 * sx) / hs + ((∑ e, u e * y1 e - ∑ e, u e * y2 e) / 2 * ax) / ha =
      ∑ e, ((y1 e + y2 e) / 2 * sx / hs + (y1 e - y2 e) / 2 * ax / ha) * u e := by
  rw [show ((∑ e, u e * y1 e + ∑ e, u e * y2 e) / 2 * sx) / hs
        + ((∑ e, u e * y1 e - ∑ e, u e * y2 e) / 2 * ax) / ha =
      (∑ e, u e * y1 e) * ((sx / hs + ax / ha) / 2) + (∑ e, u e * y2 e) * ((sx / hs - ax / ha) / 2) by ring]
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => by ring

theorem swap_inner {ι : Type} [Fintype ι] (g : ι → Fin 3 → Fin 3 → ℂ) (u : ι → ℂ) :
    ∑ e, (∑ i : Fin 3, ∑ q : Fin 3, g e i q) * u e = ∑ i : Fin 3, ∑ q : Fin 3, ∑ e, g e i q * u e := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

theorem swap_outer {ι : Type} [Fintype ι] (s : Finset ℤ) (t : Finset ℕ) (F : ℤ → ℕ → ℕ → ι → ℂ) (u : ι → ℂ) :
    ∑ e, (∑ n ∈ s, ∑ j ∈ t, ∑ l ∈ t, F n j l e) * u e = ∑ n ∈ s, ∑ j ∈ t, ∑ l ∈ t, ∑ e, F n j l e * u e := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

theorem ite_sum {ι : Type} [Fintype ι] (P : Prop) [Decidable P] (T : ι → ℂ) (u : ι → ℂ) :
    ∑ e, (if P then T e else 0) * u e = if P then ∑ e, T e * u e else 0 := by
  split_ifs <;> simp

end FormulaRowY

open FormulaRowY in
theorem rowYIdentity_of (hS : SynthesisStatement) (hY : YCoefLinearStatement) : RowYIdentityStatement := by
  intro α hα1 hα2 k N slots c hc K S B Cl R hd x hx ζ a _
  set U := augVector c K S B x ζ with hU
  have hs : ∀ n ∈ S.resolved, ∀ p ∈ K.rect,
      K.lowStrainAt c.order n S.degHigh x.2.1 p = synthStrain S B U n p ∧
        K.lowVelocityAt c.order n S.degHigh x.1 p = synthVelocity S B U n p :=
    fun n hn p hp => hS α hα1 hα2 c hc K S B hd.box hd.bases x hx ζ n hn p hp
  unfold rowYPair
  congr 1
  unfold linForm rowYVec
  simp only [add_mul, Finset.sum_add_distrib]
  rw [swap_outer, swap_outer]
  congr 1
  · refine Finset.sum_congr rfl fun n' _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [ite_sum]
    split_ifs
    · simp only [← Finset.sum_add_distrib]
      rw [swap_inner]
      simp only [coef_yFolded c K S B x ζ hs]
      unfold sigmaWeightedPair entryPairing
      simp only [Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q _ => ?_
      rw [(hY α hα1 hα2 c hc K S B Cl R hd U n' j l).1 i q, (hY α hα1 hα2 c hc K S B Cl R hd U n' j l).1 q i]
      rw [pair_term]
      refine Finset.sum_congr rfl fun e _ => ?_
      unfold symVec antiVec rowCouplingCoef
      ring
    · rfl
  · refine Finset.sum_congr rfl fun n' _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [ite_sum]
    split_ifs
    · simp only [coef_yVelocity c K S B x ζ hs]
      unfold vecPair
      simp only [Finset.sum_mul, Finset.sum_div]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [(hY α hα1 hα2 c hc K S B Cl R hd U n' j l).2 i, Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl fun e _ => ?_
      unfold velVec rowCouplingVelCoef
      ring
    · rfl

end CellFormula

end CellCert

end Breakdown
