import Breakdown.FracCell.StFormulaProof

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis CellAnalysis.CellScalars

namespace FormulaNear.Internal

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)

theorem yStrain_eq_of (κ ζ : Fin k → ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (n : ℤ)
    (p : ℝ × ℝ) (sAt : ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ) (vAt : ℤ → ℝ × ℝ → Fin 3 → ℂ)
    (hs : ∀ n' ∈ S.resolved, K.lowStrainAt c.order n' S.degHigh G p = sAt n' p)
    (hv : ∀ n' ∈ S.resolved, K.lowVelocityAt c.order n' S.degHigh v p = vAt n' p)
    (κ' ζ' : Fin k → ℂ) (hκ : ∀ i, κ' i = ((κ i : ℝ) : ℂ)) (hζ : ∀ i, ζ' i = ((ζ i : ℝ) : ℂ)) :
    yStrain c K S κ ζ v G n p = yStrainOf c K S sAt vAt κ' ζ' n p := by
  funext a b
  have e1 : ∀ n'' ∈ S.resolved,
      waveActionStrain (strainMode c (n - n'') p) (curlGradMode c (n - n'') p)
          (K.lowStrainAt c.order n'' S.degHigh G p) (K.lowVelocityAt c.order n'' S.degHigh v p) a b =
        waveActionStrain (strainMode c (n - n'') p) (curlGradMode c (n - n'') p) (sAt n'' p) (vAt n'' p) a b :=
    fun n'' h => by rw [hs n'' h, hv n'' h]
  have e2 : ∀ i : Fin k,
      ((κ i / 2 : ℝ) : ℂ) * modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b
          + ((ζ i : ℝ) : ℂ) * modeMat c.order n (c.modelPinField i) p.1 p.2 a b =
        (κ' i / 2) * modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b
          + ζ' i * modeMat c.order n (c.modelPinField i) p.1 p.2 a b := by
    intro i
    rw [hκ i, hζ i]
    push_cast
    ring
  simp only [yStrain, yStrainOf]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl (fun i _ => e2 i)]
  by_cases h2 : n ∈ S.resolved
  · rw [if_pos h2, if_pos h2, hs n h2, hv n h2]
  · rw [if_neg h2, if_neg h2]

theorem yVelocity_eq_of (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (n : ℤ)
    (p : ℝ × ℝ) (sAt : ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ) (vAt : ℤ → ℝ × ℝ → Fin 3 → ℂ)
    (hs : ∀ n' ∈ S.resolved, K.lowStrainAt c.order n' S.degHigh G p = sAt n' p)
    (hv : ∀ n' ∈ S.resolved, K.lowVelocityAt c.order n' S.degHigh v p = vAt n' p) :
    yVelocity c K S v G n p = yVelocityOf c K S sAt vAt n p := by
  funext b
  have e1 : ∀ n'' ∈ S.resolved,
      waveActionVelocity (curlGradMode c (n'' - n) p) (K.lowStrainAt c.order n'' S.degHigh G p) b =
        waveActionVelocity (curlGradMode c (n'' - n) p) (sAt n'' p) b :=
    fun n'' h => by rw [hs n'' h]
  simp only [yVelocity, yVelocityOf]
  rw [Finset.sum_congr rfl e1]
  by_cases h2 : n ∈ S.resolved
  · rw [if_pos h2, if_pos h2, hs n h2, hv n h2]
  · rw [if_neg h2, if_neg h2]

theorem yFolded_eq_of (κ ζ : Fin k → ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (n : ℤ)
    (p : ℝ × ℝ) (sAt : ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ) (vAt : ℤ → ℝ × ℝ → Fin 3 → ℂ)
    (hs : ∀ n' ∈ S.resolved, K.lowStrainAt c.order n' S.degHigh G p = sAt n' p)
    (hv : ∀ n' ∈ S.resolved, K.lowVelocityAt c.order n' S.degHigh v p = vAt n' p)
    (κ' ζ' : Fin k → ℂ) (hκ : ∀ i, κ' i = ((κ i : ℝ) : ℂ)) (hζ : ∀ i, ζ' i = ((ζ i : ℝ) : ℂ)) :
    yFolded c K S κ ζ v G n p = yFoldedOf c K S sAt vAt κ' ζ' n p := by
  simp only [yFolded, yFoldedOf]
  rw [yStrain_eq_of c K S κ ζ v G n p sAt vAt hs hv κ' ζ' hκ hζ, yVelocity_eq_of c K S v G n p sAt vAt hs hv]

theorem coef_congr (B : CellBases) (F F' : ℝ × ℝ → ℂ) (h : ∀ p ∈ K.rect, F p = F' p) (j l : ℕ) :
    B.coef K F j l = B.coef K F' j l := by
  unfold CellBases.coef
  refine setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) ?_
  intro p hp
  simp only [h p hp]

variable {D : Type} [Fintype D]

def quadHom (u : D → ℂ) : Matrix D D ℂ →+ ℝ where
  toFun Φ := quadFormValue Φ u
  map_zero' := by simp [quadFormValue]
  map_add' Φ Ψ := by simp [quadFormValue, Matrix.add_mulVec, dotProduct_add]

theorem quad_add (Φ Ψ : Matrix D D ℂ) (u : D → ℂ) :
    quadFormValue (Φ + Ψ) u = quadFormValue Φ u + quadFormValue Ψ u := (quadHom u).map_add Φ Ψ

theorem quad_sum {ι : Type} (s : Finset ι) (Φ : ι → Matrix D D ℂ) (u : D → ℂ) :
    quadFormValue (∑ i ∈ s, Φ i) u = ∑ i ∈ s, quadFormValue (Φ i) u := map_sum (quadHom u) Φ s

theorem quad_ite (P : Prop) [Decidable P] (Φ : Matrix D D ℂ) (u : D → ℂ) :
    quadFormValue (if P then Φ else 0) u = if P then quadFormValue Φ u else 0 := by
  split_ifs
  · rfl
  · exact (quadHom u).map_zero

theorem quad_smul (r : ℝ) (Φ : Matrix D D ℂ) (u : D → ℂ) :
    quadFormValue ((r : ℂ) • Φ) u = r * quadFormValue Φ u := by
  simp only [quadFormValue, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]

theorem quad_rankOne (s u : D → ℂ) :
    quadFormValue (rankOne s) u = ‖∑ e, s e * u e‖ ^ 2 := by
  have h : star u ⬝ᵥ (rankOne s *ᵥ u) = (starRingEnd ℂ) (∑ e, s e * u e) * (∑ e, s e * u e) := by
    simp only [dotProduct, mulVec, rankOne, Pi.star_apply, map_sum, map_mul, RCLike.star_def]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e' _ => ?_
    ring
  rw [quadFormValue, h, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.sq_norm]

end FormulaNear.Internal

open FormulaNear.Internal in
theorem nearIdentity_of (hS : SynthesisStatement) (hY : YCoefLinearStatement) : NearIdentityStatement := by
  intro α hα1 hα2 k N slots c hc K S B Cl R hD x hx ζ
  have hsv : ∀ p ∈ K.rect, ∀ n' ∈ S.resolved,
      K.lowStrainAt c.order n' S.degHigh x.2.1 p = synthStrain S B (augVector c K S B x ζ) n' p ∧
        K.lowVelocityAt c.order n' S.degHigh x.1 p = synthVelocity S B (augVector c K S B x ζ) n' p :=
    fun p hp n' hn' => hS α hα1 hα2 c hc K S B hD.box hD.bases x hx ζ n' hn' p hp
  have hκ : ∀ i, kappaPart S (augVector c K S B x ζ) i = ((x.2.2.2.1 i : ℝ) : ℂ) := fun i => rfl
  have hζ : ∀ i, pinPart S (augVector c K S B x ζ) i = ((ζ i : ℝ) : ℂ) := fun i => rfl
  have hC : ∀ n j l a b, B.coef K (fun p => yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b) j l =
      ∑ e, augVector c K S B x ζ e * yVec c K S B n j l a b e := by
    intro n j l a b
    rw [← (hY α hα1 hα2 c hc K S B Cl R hD (augVector c K S B x ζ) n j l).1 a b]
    unfold yCoef
    refine coef_congr K B _ _ (fun p hp => ?_) j l
    rw [yFolded_eq_of c K S x.2.2.2.1 ζ x.1 x.2.1 n p (synthStrain S B (augVector c K S B x ζ))
      (synthVelocity S B (augVector c K S B x ζ)) (fun n' h => (hsv p hp n' h).1) (fun n' h => (hsv p hp n' h).2)
      _ _ hκ hζ]
  have hW : ∀ n j l a, B.coef K (fun p => yVelocity c K S x.1 x.2.1 n p a) j l =
      ∑ e, augVector c K S B x ζ e * velVec c K S B n j l a e := by
    intro n j l a
    rw [← (hY α hα1 hα2 c hc K S B Cl R hD (augVector c K S B x ζ) n j l).2 a]
    unfold yVelCoef
    refine coef_congr K B _ _ (fun p hp => ?_) j l
    rw [yVelocity_eq_of c K S x.1 x.2.1 n p (synthStrain S B (augVector c K S B x ζ))
      (synthVelocity S B (augVector c K S B x ζ)) (fun n' h => (hsv p hp n' h).1) (fun n' h => (hsv p hp n' h).2)]
  have hsym : ∀ n j l, symSq (fun a b => B.coef K (fun p => yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b) j l) =
      ∑ a, ∑ b, ‖∑ e, symVec c K S B n j l a b e * augVector c K S B x ζ e‖ ^ 2 := by
    intro n j l
    unfold symSq
    simp only [hC]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    congr 2
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun e _ => by simp only [symVec]; ring
  have hanti : ∀ n j l, antiSq (fun a b => B.coef K (fun p => yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b) j l) =
      ∑ a, ∑ b, ‖∑ e, antiVec c K S B n j l a b e * augVector c K S B x ζ e‖ ^ 2 := by
    intro n j l
    unfold antiSq
    simp only [hC]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    congr 2
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun e _ => by simp only [antiVec]; ring
  have hvel : ∀ n j l, vecSq (fun a => B.coef K (fun p => yVelocity c K S x.1 x.2.1 n p a) j l) =
      ∑ a, ‖∑ e, velVec c K S B n j l a e * augVector c K S B x ζ e‖ ^ 2 := by
    intro n j l
    unfold vecSq
    simp only [hW]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 2
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _
  unfold nearWeighted weightedCoefSum nearMatrix
  rw [quad_add, quad_sum, quad_sum]
  congr 1
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [quad_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [quad_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [quad_ite]
    simp only [true_and]
    split_ifs
    · rw [quad_sum, hsym, hanti, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [quad_sum, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [quad_add, quad_smul, quad_smul, quad_rankOne, quad_rankOne]
      ring
    · rfl
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [quad_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [quad_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [quad_ite]
    simp only [true_and]
    split_ifs
    · rw [quad_sum, hvel, Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [quad_smul, quad_rankOne]
      ring
    · rfl

end CellFormula

end CellCert

end Breakdown
