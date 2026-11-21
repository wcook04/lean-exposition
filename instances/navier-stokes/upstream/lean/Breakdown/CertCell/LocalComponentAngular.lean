import Breakdown.CertCell.LocalComponentAngularBasis

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CertCell.LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy
open Internal.AngularValue

theorem localComponentAngular : LocalComponentAngularStatement := by
  intro D _ _ modes Q q m K B I F T u hK hB hq hqQ hmd n C
  set A := angularArray (azimuth m n) C with hA
  set g := modeSum A (F n) with hg
  set Fa := modeSum C (fun a b p => (p.1 : ℂ) * T n a b 1 p) with hFdef
  have hint : ∀ a b, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F n a b p) K.rect :=
    fun a b => hmd.line_integrable n a b
  have hgint : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * g p) K.rect := by
    have : (fun p => (K.lineWeight p.1 : ℂ) * g p) =
        fun p => ∑ a, ∑ b, A a b * ((K.lineWeight p.1 : ℂ) * F n a b p) := by
      funext p
      simp only [hg, modeSum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [this]
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hint a b).const_mul _
  have hae : ∀ᵐ p ∂(volume.restrict K.rect), Fa p = g p := by
    have h9 : ∀ᵐ p ∂(volume.restrict K.rect), ∀ a b, (p.1 : ℂ) * T n a b 1 p =
        ∑ a', ∑ b', angularComb (azimuth m n) a b a' b' * F n a' b' p := by
      rw [ae_all_iff]; intro a; rw [ae_all_iff]; intro b
      exact hmd.angular_frame n a b
    filter_upwards [h9] with p hp
    simp only [hFdef, hg, modeSum, hp, hA, angularArray, Finset.mul_sum, Finset.sum_mul]
    rw [sum_swap4 (fun a b a' b' => C a b * (angularComb (azimuth m n) a b a' b' * F n a' b' p))]
    refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hrow : ∀ j l : Fin (Q + 1), rowApply (lowRow I n A j l) u = B.coef K g j l := by
    intro j l
    rw [lowRow_apply, hg, coef_modeSum K B A (F n) hint]
    simp only [hmd.strain]
  have hpair : ∀ φ : ℝ × ℝ → ℝ, rowApply (lowPairRow K B I n A φ) u = ∑ jl : Fin (Q + 1) × Fin (Q + 1),
      ((rectIntegral K (fun p => basisFn B jl.1 jl.2 p * φ p) : ℝ) : ℂ) * B.coef K g jl.1 jl.2 := by
    intro φ
    rw [lowPair_apply]
    simp only [hrow]
  have hcont : ∀ (f : ℝ × ℝ → ℝ), Continuous f →
      IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * g p * (f p : ℂ)) K.rect :=
    fun f hf => hgint.mul_continuousOn (Complex.continuous_ofReal.comp hf).continuousOn (rect_compact K)
  by_cases h0 : K.r₁ = 0
  · have hw : ∀ r, K.lineWeight r = r := fun r => by simp [CellBox.lineWeight, h0]
    rw [if_pos h0]
    unfold CellBox.angularEnergy
    rw [if_pos h0]
    unfold angularAxisForm testSupForm
    rw [quad_formOfRows]
    symm
    refine supremum_case K (fun p => p.1) _ _ (fun jl : Fin (Q + 1) × Fin (Q + 1) => angularTest jl.1 jl.2)
      (fun P => scaled_mem (Equiv.refl _) P) (pairMatrix_axis_pd K hK h0 Q) ?_ ?_ _ ?_
    · intro i
      refine (hcont _ (by unfold monomial; fun_prop : Continuous (monomial i.1 i.2))).congr ?_
      refine (ae_restrict_iff' (rect_meas K)).2 ?_
      filter_upwards [(ae_restrict_iff' (rect_meas K)).1 hae] with p hp hpr
      rw [hp hpr, hw]
      exact axis_pt _ _ _
    · intro i i'
      exact (by unfold angularTest monomial; fun_prop : Continuous fun p : ℝ × ℝ =>
        p.1 * angularTest i.1 i.2 p * angularTest i'.1 i'.2 p).continuousOn.integrableOn_compact (rect_compact K)
    · intro i
      rw [hpair]
      have h1 : ∫ p in K.rect, ((p.1 : ℝ) : ℂ) * (Fa p / (p.1 : ℂ)) * ((angularTest i.1 i.2 p : ℝ) : ℂ) =
          ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * g p * ((monomial i.1 i.2 p : ℝ) : ℂ) := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with p hp
        rw [hp, hw]
        exact (axis_pt _ _ _).symm
      rw [h1, expand K B hK hB Q g hgint _ (mono_span K B hB Q i.1 i.2 (Nat.lt_succ_iff.mp i.1.2)
        (Nat.lt_succ_iff.mp i.2.2))]
      refine Finset.sum_congr rfl fun jl _ => ?_
      congr 2
      unfold rectIntegral
      congr 1
      funext p
      rw [hw]
      unfold angularTest
      ring
  · have hw : ∀ r, K.lineWeight r = 1 := fun r => by simp [CellBox.lineWeight, h0]
    rw [if_neg h0]
    unfold CellBox.angularEnergy
    rw [if_neg h0]
    unfold angularOffForm
    rw [quad_add]
    have hr1 : 0 < K.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h0)
    have hr2 : 0 < K.r₂ := hr1.trans hK.r_order.2
    have hpos : ∀ p ∈ K.rect, 0 < p.1 := fun p hp => hr1.trans_le hp.1.1
    have hFint : IntegrableOn Fa K.rect := by
      have : IntegrableOn g K.rect := by simpa [hw] using hgint
      exact this.congr (by filter_upwards [hae] with p hp; exact hp.symm)
    have hcoef : ∀ j l, B.coef K Fa j l = B.coef K g j l := by
      intro j l
      unfold CellBases.coef
      exact integral_congr_ae (by filter_upwards [hae] with p hp; rw [hp])
    congr 1
    · erw [quad_formOfRows]
      rw [proj_norm K B hK hB h0 Q Fa hFint]
      simp only [hrow, hcoef]
      simp only [mulVec, dotProduct, Pi.star_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true, RCLike.star_def]
      rw [Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun jl _ => ?_
      rw [show (starRingEnd ℂ) (B.coef K g jl.1 jl.2) * (((K.r₂⁻¹ : ℝ) : ℂ) * B.coef K g jl.1 jl.2) =
          ((K.r₂⁻¹ * ‖B.coef K g jl.1 jl.2‖ ^ 2 : ℝ) : ℂ) by
        rw [mul_left_comm, Complex.conj_mul']; push_cast; ring, Complex.ofReal_re]
    · have hQ : 1 ≤ Q := by omega
      obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      unfold testSupForm
      rw [quad_formOfRows]
      symm
      have hco : ∀ i : Fin (Q' + 1) × Fin (Q' + 1 + 1),
          ContinuousOn (fun p : ℝ × ℝ => angularOffWeight K p * angularTest i.1 i.2 p) K.rect := by
        intro i
        unfold angularOffWeight angularTest monomial
        refine ContinuousOn.mul (ContinuousOn.div (by fun_prop) (by fun_prop) ?_) (by fun_prop)
        intro p hp
        exact mul_ne_zero (hpos p hp).ne' hr2.ne'
      have hψ : ∀ i : Fin (Q' + 1) × Fin (Q' + 1 + 1), ∀ p ∈ K.rect,
          angularOffWeight K p * angularTest i.1 i.2 p = (monomial i.1 i.2 - K.r₂⁻¹ • monomial (i.1 + 1) i.2) p := by
        intro i p hp
        have := (hpos p hp).ne'
        simp only [angularOffWeight, angularTest, monomial, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
        ring
      refine supremum_case K (angularOffWeight K) _ Fa
        (fun jl : Fin (Q' + 1) × Fin (Q' + 1 + 1) => angularTest jl.1 jl.2)
        (fun P => scaled_mem (Equiv.refl _) P) (pairMatrix_off_pd K hK h0 (Q' + 1)) ?_ ?_ _ ?_
      · intro i
        have := hFint.mul_continuousOn (Complex.continuous_ofReal.comp_continuousOn (hco i)) (rect_compact K)
        refine this.congr (Filter.Eventually.of_forall fun p => ?_)
        simp only [Function.comp_apply]
        push_cast; ring
      · intro i i'
        have hcw : ContinuousOn (angularOffWeight K) K.rect := by
          unfold angularOffWeight
          refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
          intro p hp
          exact mul_ne_zero (hpos p hp).ne' hr2.ne'
        refine ContinuousOn.integrableOn_compact (rect_compact K) ?_
        refine (hcw.mul ?_).mul ?_
        · exact (by unfold angularTest monomial; fun_prop : Continuous (angularTest i.1 i.2)).continuousOn
        · exact (by unfold angularTest monomial; fun_prop : Continuous (angularTest i'.1 i'.2)).continuousOn
      · intro i
        rw [hpair]
        have hmem : (monomial i.1 i.2 - K.r₂⁻¹ • monomial (i.1 + 1) i.2) ∈ Submodule.span ℝ
            (Set.range (fun jl : Fin (Q' + 1 + 1) × Fin (Q' + 1 + 1) => basisFn B jl.1 jl.2)) :=
          Submodule.sub_mem _ (mono_span K B hB _ _ _ (by omega) (by omega))
            (Submodule.smul_mem _ _ (mono_span K B hB _ _ _ (by omega) (by omega)))
        have h1 : ∫ p in K.rect, ((angularOffWeight K p : ℝ) : ℂ) * Fa p * ((angularTest i.1 i.2 p : ℝ) : ℂ) =
            ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * g p *
              (((monomial i.1 i.2 - K.r₂⁻¹ • monomial (i.1 + 1) i.2) p : ℝ) : ℂ) := by
          refine integral_congr_ae ?_
          filter_upwards [hae, ae_restrict_mem (rect_meas K)] with p hp hpr
          rw [hp, hw, ← hψ i p hpr]
          push_cast; ring
        rw [h1, expand K B hK hB (Q' + 1) g hgint _ hmem]
        refine Finset.sum_congr rfl fun jl _ => ?_
        congr 2
        unfold rectIntegral
        refine setIntegral_congr_fun (rect_meas K) fun p hp => ?_
        rw [hw, ← hψ i p hp]
        ring

end Breakdown.CertCell.LocalField
