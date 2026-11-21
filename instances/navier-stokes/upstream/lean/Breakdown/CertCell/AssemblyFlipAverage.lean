import Breakdown.CertCell.AssemblyStatements
import Breakdown.CertCell.RowSharesInstance
import Breakdown.CertCell.PlaneDataFlipLinks
import Breakdown.Cert.ExtendedInvariance

open MeasureTheory Filter
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal.FlipAverageRight

open Bridge.Internal.ModeTermFlip (flipIsometryEquiv flipPoint_flipPoint frameSign_mul_self)
open Bridge.Internal.ModeFlip (flipPoint_unitVector)
open CertCell.Internal.RowShares (inner_flipPoint flipPoint_add flipPoint_smul)

def flipConj (φ : ℝ → Space → Space) : ℝ → Space → Space := fun σ y => flipPoint (φ σ (flipPoint y))

def flipPair (z : ℝ × Space) : ℝ × Space := (z.1, flipPoint z.2)

theorem flipPair_eq (z : ℝ × Space) : flipPair z = (z.1, flipIsometryEquiv z.2) := rfl

theorem flipPoint_sub (a b : Space) : flipPoint (a - b) = flipPoint a - flipPoint b :=
  map_sub flipIsometryEquiv a b

theorem flipPoint_sum {k : ℕ} (f : Fin k → Space) : flipPoint (∑ i, f i) = ∑ i, flipPoint (f i) :=
  map_sum flipIsometryEquiv f _

theorem integral_flip (f : ℝ × Space → ℝ) : ∫ z, f (flipPair z) = ∫ z, f z :=
  Breakdown.Cert.Internal.ExtendedInvariance.integral_rot f flipIsometryEquiv

theorem integrable_flip_iff (f : ℝ × Space → ℝ) : Integrable (fun z => f (flipPair z)) ↔ Integrable f :=
  (Breakdown.Cert.Internal.ExtendedInvariance.measurePreserving_rot flipIsometryEquiv).integrable_comp_emb
    ((MeasurableEquiv.refl ℝ).prodCongr flipIsometryEquiv.toHomeomorph.toMeasurableEquiv).measurableEmbedding

theorem flipConj_test {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    IsSpaceTimeTestField (flipConj φ) :=
  Breakdown.Cert.Internal.ExtendedInvarianceTest.isSpaceTimeTestField_rot hφ flipIsometryEquiv

theorem fderiv_conj (f : Space → Space) (y a : Space) :
    fderiv ℝ (fun x => flipPoint (f (flipPoint x))) y a = flipPoint (fderiv ℝ f (flipPoint y) (flipPoint a)) := by
  let L := flipIsometryEquiv.toContinuousLinearEquiv
  have e : (fun x => flipPoint (f (flipPoint x))) = L ∘ (f ∘ L) := rfl
  rw [e, L.comp_fderiv, L.comp_right_fderiv]
  rfl

theorem deriv_conj (f : ℝ → Space) (σ : ℝ) : deriv (fun s => flipPoint (f s)) σ = flipPoint (deriv f σ) := by
  let L := flipIsometryEquiv.toContinuousLinearEquiv
  have e : (fun s => flipPoint (f s)) = L ∘ f := rfl
  rw [e, ← fderiv_apply_one_eq_deriv, L.comp_fderiv, ← fderiv_apply_one_eq_deriv]
  rfl

theorem fderiv_field_flip {W : Space → Space} (hW : ∀ y, W (flipPoint y) = flipPoint (W y)) (y a : Space) :
    fderiv ℝ W (flipPoint y) (flipPoint a) = flipPoint (fderiv ℝ W y a) := by
  have e : W = fun x => flipPoint (W (flipPoint x)) := by
    funext x
    rw [hW, flipPoint_flipPoint]
  have h := fderiv_conj W y a
  rw [← e] at h
  rw [h, flipPoint_flipPoint]

theorem matInner_conj (A B : Space →L[ℝ] Space) (A' B' : Space →L[ℝ] Space)
    (hA : ∀ u, A' u = flipPoint (A (flipPoint u))) (hB : ∀ u, B' u = flipPoint (B (flipPoint u))) :
    matInner A B' = matInner A' B := by
  unfold matInner
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hA, hB, flipPoint_unitVector, map_smul, map_smul, flipPoint_smul, flipPoint_smul, real_inner_smul_left,
    real_inner_smul_right, inner_flipPoint]

def transportTest (P : ℝ) (φ : ℝ → Space → Space) (z : ℝ × Space) : Space :=
  -(1 / P) • deriv (fun s => φ s z.2) z.1 - φ z.1 z.2 - (1 / 2 : ℝ) • fderiv ℝ (φ z.1) z.2 z.2

theorem transportTest_conj (P : ℝ) (φ : ℝ → Space → Space) (z : ℝ × Space) :
    transportTest P (flipConj φ) z = flipPoint (transportTest P φ (flipPair z)) := by
  unfold transportTest flipConj flipPair
  simp only
  rw [deriv_conj (fun s => φ s (flipPoint z.2)), fderiv_conj (φ z.1) z.2 z.2, flipPoint_sub, flipPoint_sub,
    flipPoint_smul, flipPoint_smul]

theorem derivative_pairing_flip {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hp : IsPerturbation Γ P v G H g)
    (hv : ∀ᵐ z : ℝ × Space, v z.1 (flipPoint z.2) = flipPoint (v z.1 z.2))
    {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    ∫ z : ℝ × Space, inner ℝ (g z.1 z.2) (flipConj φ z.1 z.2) = ∫ z : ℝ × Space, inner ℝ (g z.1 z.2) (φ z.1 z.2) := by
  have hψ := flipConj_test hφ
  have t1 := hp.transport (flipConj φ) ⟨hψ.1, hψ.2.1⟩
  have t2 := hp.transport φ ⟨hφ.1, hφ.2.1⟩
  rw [← t1, ← t2]
  have e : (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (transportTest P (flipConj φ) z))
      =ᵐ[volume] fun z => inner ℝ (v (flipPair z).1 (flipPair z).2) (transportTest P φ (flipPair z)) := by
    filter_upwards [hv] with z hz
    rw [transportTest_conj, ← inner_flipPoint, ← hz]
    rfl
  have h1 := integral_congr_ae e
  have h2 := integral_flip (fun z => inner ℝ (v z.1 z.2) (transportTest P φ z))
  exact h1.trans h2

def restIntegrand {k : ℕ} (W : ℝ → Space → Space) (b : Fin k → ℝ → Space → Space) (κ : Fin k → ℝ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (φ : ℝ → Space → Space) (z : ℝ × Space) : ℝ :=
  inner ℝ (G z.1 z.2 (W z.1 z.2) + fderiv ℝ (W z.1) z.2 (v z.1 z.2) + ∑ i, κ i • b i z.1 z.2) (φ z.1 z.2)
    + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)

theorem integrand_split {k : ℕ} (W : ℝ → Space → Space) (b : Fin k → ℝ → Space → Space) (κ : Fin k → ℝ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (g φ : ℝ → Space → Space) (z : ℝ × Space) :
    inner ℝ (g z.1 z.2 + G z.1 z.2 (W z.1 z.2) + fderiv ℝ (W z.1) z.2 (v z.1 z.2)
        + ∑ i, κ i • b i z.1 z.2) (φ z.1 z.2) + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)
      = inner ℝ (g z.1 z.2) (φ z.1 z.2) + restIntegrand W b κ v G φ z := by
  unfold restIntegrand
  simp only [inner_add_left]
  ring

theorem rest_flip {k : ℕ} {W : ℝ → Space → Space} {b : Fin k → ℝ → Space → Space} (κ : Fin k → ℝ)
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)} (φ : ℝ → Space → Space)
    (hW : ∀ σ y, W σ (flipPoint y) = flipPoint (W σ y))
    (hae : ∀ᵐ z : ℝ × Space, v z.1 (flipPoint z.2) = flipPoint (v z.1 z.2)
      ∧ (∀ u, G z.1 (flipPoint z.2) u = flipPoint (G z.1 z.2 (flipPoint u)))
      ∧ ∀ i, b i z.1 (flipPoint z.2) = flipPoint (b i z.1 z.2)) :
    restIntegrand W b κ v G (flipConj φ) =ᵐ[volume] fun z => restIntegrand W b κ v G φ (flipPair z) := by
  filter_upwards [hae] with z hz
  obtain ⟨hv, hG, hb⟩ := hz
  unfold restIntegrand flipPair
  simp only
  have hX : G z.1 (flipPoint z.2) (W z.1 (flipPoint z.2)) + fderiv ℝ (W z.1) (flipPoint z.2) (v z.1 (flipPoint z.2))
      + ∑ i, κ i • b i z.1 (flipPoint z.2)
      = flipPoint (G z.1 z.2 (W z.1 z.2) + fderiv ℝ (W z.1) z.2 (v z.1 z.2) + ∑ i, κ i • b i z.1 z.2) := by
    rw [hW, hG, flipPoint_flipPoint, hv, fderiv_field_flip (hW z.1), flipPoint_add, flipPoint_add, flipPoint_sum]
    simp only [hb, flipPoint_smul]
  rw [hX, inner_flipPoint]
  congr 1
  have hD : ∀ u, fderiv ℝ (flipConj φ z.1) z.2 u = flipPoint (fderiv ℝ (φ z.1) (flipPoint z.2) (flipPoint u)) :=
    fun u => fderiv_conj (φ z.1) z.2 u
  exact matInner_conj (G z.1 z.2) (fderiv ℝ (φ z.1) (flipPoint z.2)) _ _ hG hD

theorem rhs_flip {k : ℕ} {W : ℝ → Space → Space} {b : Fin k → ℝ → Space → Space} (κ : Fin k → ℝ)
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (φ : ℝ → Space → Space)
    (hW : ∀ σ y, W σ (flipPoint y) = flipPoint (W σ y))
    (hae : ∀ᵐ z : ℝ × Space, v z.1 (flipPoint z.2) = flipPoint (v z.1 z.2)
      ∧ (∀ u, G z.1 (flipPoint z.2) u = flipPoint (G z.1 z.2 (flipPoint u)))
      ∧ ∀ i, b i z.1 (flipPoint z.2) = flipPoint (b i z.1 z.2))
    (hg : ∫ z : ℝ × Space, inner ℝ (g z.1 z.2) (flipConj φ z.1 z.2)
      = ∫ z : ℝ × Space, inner ℝ (g z.1 z.2) (φ z.1 z.2))
    (hg1 : Integrable (fun z : ℝ × Space => inner ℝ (g z.1 z.2) (φ z.1 z.2)))
    (hg2 : Integrable (fun z : ℝ × Space => inner ℝ (g z.1 z.2) (flipConj φ z.1 z.2))) :
    (∫ z : ℝ × Space, (inner ℝ (g z.1 z.2 + G z.1 z.2 (W z.1 z.2) + fderiv ℝ (W z.1) z.2 (v z.1 z.2)
        + ∑ i, κ i • b i z.1 z.2) (flipConj φ z.1 z.2) + matInner (G z.1 z.2) (fderiv ℝ (flipConj φ z.1) z.2)))
      = ∫ z : ℝ × Space, (inner ℝ (g z.1 z.2 + G z.1 z.2 (W z.1 z.2) + fderiv ℝ (W z.1) z.2 (v z.1 z.2)
        + ∑ i, κ i • b i z.1 z.2) (φ z.1 z.2) + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) := by
  simp only [integrand_split W b κ v G g]
  have hr := rest_flip (b := b) κ (v := v) (G := G) φ hW hae
  have hiff : Integrable (restIntegrand W b κ v G (flipConj φ)) ↔ Integrable (restIntegrand W b κ v G φ) :=
    (integrable_congr hr).trans (integrable_flip_iff _)
  by_cases hi : Integrable (restIntegrand W b κ v G φ)
  · have hi' := hiff.2 hi
    rw [integral_add hg2 hi', integral_add hg1 hi, hg, integral_congr_ae hr,
      integral_flip (restIntegrand W b κ v G φ)]
  · have hn1 : ¬ Integrable (fun z => inner ℝ (g z.1 z.2) (φ z.1 z.2) + restIntegrand W b κ v G φ z) := by
      intro h
      exact hi ((h.sub hg1).congr (Eventually.of_forall fun z => by simp))
    have hn2 : ¬ Integrable (fun z => inner ℝ (g z.1 z.2) (flipConj φ z.1 z.2)
        + restIntegrand W b κ v G (flipConj φ) z) := by
      intro h
      exact hi (hiff.1 ((h.sub hg2).congr (Eventually.of_forall fun z => by simp)))
    rw [integral_undef hn1, integral_undef hn2]

theorem pairing_integrable {F : ℝ → Space → Space} (hF : Breakdown.Cert.IsPeriodicField F)
    {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    Integrable (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (φ z.1 z.2)) := by
  obtain ⟨R, -, hR⟩ := Breakdown.Cert.Internal.TestPairing.exists_bound hφ.2.1
  exact Breakdown.Cert.Internal.TestPairing.integrable_pairing hF hφ.1 hφ.2.1 hR

theorem average_pairing {F : ℝ → Space → Space} (hF : Breakdown.Cert.IsPeriodicField F)
    {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    ∫ z : ℝ × Space, inner ℝ (flipAverage F z.1 z.2) (φ z.1 z.2)
      = (1 / 2 : ℝ) * (∫ z : ℝ × Space, inner ℝ (F z.1 z.2) (φ z.1 z.2))
        + (1 / 2 : ℝ) * ∫ z : ℝ × Space, inner ℝ (F z.1 z.2) (flipConj φ z.1 z.2) := by
  have ha := pairing_integrable hF hφ
  have hc := pairing_integrable hF (flipConj_test hφ)
  have hc' := (integrable_flip_iff (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (flipConj φ z.1 z.2))).2 hc
  have e : (fun z : ℝ × Space => inner ℝ (flipAverage F z.1 z.2) (φ z.1 z.2))
      = fun z => (1 / 2 : ℝ) * inner ℝ (F z.1 z.2) (φ z.1 z.2)
        + (1 / 2 : ℝ) * inner ℝ (F (flipPair z).1 (flipPair z).2) (flipConj φ (flipPair z).1 (flipPair z).2) := by
    funext z
    unfold flipAverage flipConj flipPair
    simp only
    rw [flipPoint_flipPoint, real_inner_smul_left, inner_add_left, inner_flipPoint]
    ring
  rw [e, integral_add (ha.const_mul _) (hc'.const_mul _), integral_const_mul, integral_const_mul,
    integral_flip (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (flipConj φ z.1 z.2))]

end Internal.FlipAverageRight

open Internal.FlipAverageRight in
theorem flipAverage_rightSide {k : ℕ} {Γ : Set Symmetry} {P : ℝ} {W : ℝ → Space → Space}
    {b : Fin k → ℝ → Space → Space} {κ : Fin k → ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g F : ℝ → Space → Space} (hp : IsPerturbation Γ P v G H g)
    (hflip : ∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0)
    (hW : ∀ σ y, W σ (flipPoint y) = flipPoint (W σ y))
    (hb : ∀ i, ∀ᵐ z : ℝ × Space, b i z.1 (flipPoint z.2) = flipPoint (b i z.1 z.2))
    (hF : Breakdown.Cert.IsPeriodicField F) (hR : IsRightSide W b κ v G g F) :
    IsRightSide W b κ v G g (flipAverage F) := by
  intro φ hφ
  have hvG := Bridge.Internal.PlaneDataFlip.ae_field_flip hp hflip
  have hae : ∀ᵐ z : ℝ × Space, v z.1 (flipPoint z.2) = flipPoint (v z.1 z.2)
      ∧ (∀ u, G z.1 (flipPoint z.2) u = flipPoint (G z.1 z.2 (flipPoint u)))
      ∧ ∀ i, b i z.1 (flipPoint z.2) = flipPoint (b i z.1 z.2) := by
    filter_upwards [hvG, ae_all_iff.2 hb] with z h1 h2
    exact ⟨h1.1, h1.2.1, h2⟩
  have hg : Breakdown.Cert.IsPeriodicField g :=
    ⟨hp.measurable_derivative, hp.periodic_derivative, hp.derivative_finite⟩
  have hψ := flipConj_test hφ
  rw [average_pairing hF hφ, hR φ hφ, hR _ hψ,
    rhs_flip κ φ hW hae (derivative_pairing_flip hp (hvG.mono fun z hz => hz.1) hφ)
      (pairing_integrable hg hφ) (pairing_integrable hg hψ)]
  ring

theorem flipAverageRightSide_holds : FlipAverageRightSideHolds := by
  intro k C nE nM D hD q hq x
  have hF : Breakdown.Cert.IsPeriodicField x.F := ⟨x.right_measurable, x.right_periodic, x.right_finite⟩
  have hR := x.right_side
  rw [hD.model_eq q hq] at hR
  refine ⟨CertCell.Internal.RowShares.flipAverage_measurable x.right_measurable,
    CertCell.Internal.RowShares.flipAverage_periodic x.right_periodic,
    CertCell.Internal.RowShares.flipAverage_finite x.right_measurable x.right_finite, ?_⟩
  refine flipAverage_rightSide x.perturbation hD.mode_class.flip hD.flip_model.field_flip (fun i => ?_) hF hR
  obtain ⟨S, hS⟩ := hD.actuators i
  exact hS.invariant.mono fun z hz => hz.2

end Assembly

end CertCell

end Breakdown
