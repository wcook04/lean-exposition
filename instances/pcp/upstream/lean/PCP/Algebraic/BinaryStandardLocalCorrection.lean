import PCP.Algebraic.StandardLocalCorrection
import PCP.Algebraic.BinaryConstraintRobust

/-!
# Binary weighted local correction

Each Lagrange coefficient is absorbed into the homogeneous Hadamard label.
Nonzero weights permute labels, so the correction error is at most `c+1`
times the received word's homogeneous distance.
-/

namespace PCP.Algebraic.BinaryStandardLocalCorrection

open Finset PolynomialLine BinaryPolynomialSpace Hadamard HadamardWeights
open GeneratorLowDegreeTest

variable {F σ : Type*} [Field F] [Algebra (ZMod 2) F] {c t : ℕ} {ζ : F}

noncomputable def correct (c : ℕ) (ζ : F) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (H : (σ → F) → Coefficients t 1 → ZMod 2)
    (u v : σ → F) (w : Fin t → ZMod 2) : ZMod 2 :=
  ∑ i : Fin (c + 1), H (point u v (nodes c ζ i))
    (homogeneousIndex (le_refl 1) (scaleLabel ρ (weights c ζ i) w))

noncomputable def queries (c : ℕ) (ζ : F) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (u v : σ → F) (w : Fin t → ZMod 2) : List ((σ → F) × Coefficients t 1) :=
  List.ofFn (fun i : Fin (c + 1) => (point u v (nodes c ζ i),
    homogeneousIndex (le_refl 1) (scaleLabel ρ (weights c ζ i) w)))

@[simp] theorem queries_length (c : ℕ) (ζ : F) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (u v : σ → F) (w : Fin t → ZMod 2) :
    (queries c ζ ρ u v w).length = c + 1 := by simp [queries]

theorem correct_congr (c : ℕ) (ζ : F) (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (u v : σ → F) (w : Fin t → ZMod 2)
    (H G : (σ → F) → Coefficients t 1 → ZMod 2)
    (h : ∀ p ∈ queries c ζ ρ u v w, H p.1 p.2 = G p.1 p.2) :
    correct c ζ ρ H u v w = correct c ζ ρ G u v w := by
  apply sum_congr rfl
  intro i _
  exact h _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem correct_encode (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (c : ℕ) (ζ : F) (f : (σ → F) → F) (u v : σ → F) (w : Fin t → ZMod 2) :
    correct c ζ ρ (fun x => encode 1 (ρ (f x))) u v w =
      linearEncode (ρ (StandardLocalCorrection.correct c ζ f u v)) w := by
  simp only [correct, encode_scaled_homogeneousIndex, StandardLocalCorrection.correct,
    linearEncode_comm, map_sum]

theorem correct_eval (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (hζ : StandardLocalCorrection.GoodNodes c ζ)
    (Q : MvPolynomial σ F) (hQ : Q.totalDegree ≤ c)
    (u v : σ → F) (w : Fin t → ZMod 2) :
    correct c ζ ρ (fun x => encode 1 (ρ (MvPolynomial.eval x Q))) u v w =
      linearEncode (ρ (MvPolynomial.eval u Q)) w := by
  rw [correct_encode, StandardLocalCorrection.correct_eval hζ Q hQ]

variable [Fintype F] [Fintype σ] [DecidableEq σ]

theorem correct_distance_le (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (hζ : StandardLocalCorrection.GoodNodes c ζ)
    (H G : (σ → F) → Coefficients t 1 → ZMod 2) (u : σ → F) :
    relativeDistance
      (fun vw : (σ → F) × (Fin t → ZMod 2) => correct c ζ ρ H u vw.1 vw.2)
      (fun vw => correct c ζ ρ G u vw.1 vw.2) ≤
      (c + 1 : ℕ) * BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) H G := by
  classical
  apply (relativeDistance_sum_le
    (fun (i : Fin (c + 1)) (vw : (σ → F) × (Fin t → ZMod 2)) =>
      H (point u vw.1 (nodes c ζ i))
        (homogeneousIndex (le_refl 1) (scaleLabel ρ (weights c ζ i) vw.2)))
    (fun (i : Fin (c + 1)) (vw : (σ → F) × (Fin t → ZMod 2)) =>
      G (point u vw.1 (nodes c ζ i))
        (homogeneousIndex (le_refl 1) (scaleLabel ρ (weights c ζ i) vw.2)))).trans
  have he (i : Fin (c + 1)) :
      relativeDistance
        (fun vw : (σ → F) × (Fin t → ZMod 2) => H (point u vw.1 (nodes c ζ i))
          (homogeneousIndex (le_refl 1) (scaleLabel ρ (weights c ζ i) vw.2)))
        (fun vw => G (point u vw.1 (nodes c ζ i))
          (homogeneousIndex (le_refl 1) (scaleLabel ρ (weights c ζ i) vw.2))) =
        BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) H G :=
    relativeDistance_comp_equiv
      ((affineSamplingEquiv u (nodes c ζ i) (pow_ne_zero _ hζ.2)).prodCongr
        (scaleLabelEquiv ρ (weights c ζ i) (hζ.weight_ne_zero i)).toEquiv)
      (fun xw => H xw.1 (homogeneousIndex (le_refl 1) xw.2))
      (fun xw => G xw.1 (homogeneousIndex (le_refl 1) xw.2))
  simp only [he, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, le_refl]

theorem failure_le (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (hζ : StandardLocalCorrection.GoodNodes c ζ)
    (Q : MvPolynomial σ F) (hQ : Q.totalDegree ≤ c)
    (H : (σ → F) → Coefficients t 1 → ZMod 2) (u : σ → F) :
    relativeDistance
      (fun vw : (σ → F) × (Fin t → ZMod 2) => correct c ζ ρ H u vw.1 vw.2)
      (fun vw => linearEncode (ρ (MvPolynomial.eval u Q)) vw.2) ≤
      (c + 1 : ℕ) * BinaryLagrangeConstraint.homogeneousDistance (le_refl 1) H
        (fun x => encode 1 (ρ (MvPolynomial.eval x Q))) := by
  simpa only [correct_eval ρ hζ Q hQ] using correct_distance_le ρ hζ H
    (fun x => encode 1 (ρ (MvPolynomial.eval x Q))) u

end PCP.Algebraic.BinaryStandardLocalCorrection
