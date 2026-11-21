import TorusEuler.Paper.Proofs.S5c.Library.HigherFields
import TorusEuler.Paper.SBD.Statements

/-!
# Norms of the gradient profile of (5.52): Lemma D.1 applied to the label and phase gradients

For the proof of (5.52) of Lemma 5.9 (`sections/08_exact_wave.tex:206-232`): the profile
`𝐝̃ q = 𝐝q + κ∂_s q` is bounded in `‖·‖_{[1],γ}` by Lemma D.1 (`hD_1`), applied

* to the label gradient `𝐝q = ∑_j (∂_{a_j} q) Gᵀe_j`, through (D.4) for the product of the
  coefficient `G = (D_aX)⁻¹` with `∂_{a_j} q` and (D.3) for the label derivatives
  (`wNorm_labelGrad_le`: `‖𝐝q‖_{[1],γ} ≤ C ‖G‖_{[1]} ℓ_*⁻¹ ‖q‖_{[2],γ}`);
* to the phase gradient of a transverse solution, `κ∂_s𝗉 = P_κ(f - 2MV)`, through (D.4) twice
  (`wNorm_phaseGrad_le`: `‖κ∂_s𝗉‖_{[1],γ} ≤ C ‖P_κ‖_{[1]}(‖f‖_{[1],γ} + C ‖M‖_{[1]} ‖V‖_{[1],γ})`);
* `coefNorm` gives the norm of a phase-independent coefficient `L(c(t,a))` from (D.6) and (5.8)
  of Proposition 5.1 (the pattern of the proof of Lemma 5.7 in package S5b).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5c

open HierarchyTwistedProfile InnerProductSpace AppendixD

noncomputable section

/-- **The norm of a phase-independent coefficient** `L(c(t,a))` on a time domain mapped into
`[0,T]`, from the bounds (D.6) (`hD6`, finiteness of the jets) and (5.8) (`h58`) of
Proposition 5.1: finite, and at most `#W_n ‖L‖ B`. -/
theorem coefNorm {I : Type} {T : ℝ} (ι : I → ℝ) (hι : ∀ t, ι t ∈ Icc 0 T) {E' : Type}
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (L : (Vec3 →L[ℝ] Vec3) →L[ℝ] E') {c : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {ℓ h : ℝ} (hℓ : 0 < ℓ)
    (n : ℕ) {b : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hsm : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (c t))
    (hD6 : ∀ m, ∀ t ∈ Icc 0 T, ∀ a, ‖iteratedFDeriv ℝ m (c t) a‖ ≤ b m)
    (h58 : ∀ t ∈ Icc 0 T,
      (∑ j ∈ Finset.range (n + 1), ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (c t))) ≤ B) :
    FieldNormFinite ℓ h n (fun (t : I) (x : Vec3 × ℝ) => L (c (ι t) x.1)) ∧
      fieldNorm ℓ h n (fun (t : I) (x : Vec3 × ℝ) => L (c (ι t) x.1)) ≤
        (hierarchyAdmissibleWords (Fin 3) n).card * (‖L‖ * B) := by
  have hunif (m : ℕ) : ∃ b', ∀ (t : I) a, ‖iteratedFDeriv ℝ m (c (ι t)) a‖ ≤ b' :=
    ⟨b m, fun t a => hD6 m _ (hι t) a⟩
  have hjet : ∀ m ≤ n, ∀ (t : I) a, ℓ ^ m * ‖iteratedFDeriv ℝ m (c (ι t)) a‖ ≤ B := by
    intro m hm t a
    have hbdd : BddAbove (range fun x => ‖iteratedFDeriv ℝ m (c (ι t)) x‖) :=
      ⟨b m, forall_mem_range.mpr fun x => hD6 m _ (hι t) x⟩
    have hsup := norm_le_spatialSupNorm hbdd a
    have hterm : ℓ ^ m * spatialSupNorm (iteratedFDeriv ℝ m (c (ι t))) ≤
        ∑ j ∈ Finset.range (n + 1), ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (c (ι t))) :=
      Finset.single_le_sum
        (f := fun j => ℓ ^ j * spatialSupNorm (iteratedFDeriv ℝ j (c (ι t))))
        (fun j _ => mul_nonneg (pow_nonneg hℓ.le _) (Real.iSup_nonneg fun _ => norm_nonneg _))
        (Finset.mem_range.mpr (by omega))
    exact (mul_le_mul_of_nonneg_left hsup (pow_nonneg hℓ.le _)).trans (hterm.trans (h58 _ (hι t)))
  exact coef_bounds (G := fun (t : I) => c (ι t)) L hℓ.le h n hB (fun t => hsm _ (hι t)) hunif hjet

/-- Time domains: `[t₀,T] ⊆ [0,T]`. -/
theorem Icc_subset_Icc_zero {T t₀ : ℝ} (ht₀ : 0 ≤ t₀) : Icc t₀ T ⊆ Icc 0 T :=
  Icc_subset_Icc ht₀ le_rfl

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {k : Vec3}

/-- **`‖𝐝q‖_{[1],γ} ≤ C ‖G‖_{[1]} ℓ_*⁻¹ ‖q‖_{[2],γ}`** (`08_exact_wave.tex:219-221`: "The label
derivative costs a power of `𝖣`"), by (D.4) for the products `(∂_{a_j} q) Gᵀe_j` and (D.3) for
`∑_j ‖∂_{a_j} q‖_{[1],γ} ≤ 3 ℓ_*⁻¹ ‖q‖_{[2],γ}` (both from `hD_1`). -/
theorem wNorm_labelGrad_le (hD1 : Statement.lemma_D_1) (d : ParentGeometry hT U X k)
    {t₀ ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) {γ : ℝ → ℝ}
    (hγc : ContinuousOn γ (Icc t₀ T)) (hγ : ∀ t ∈ Icc t₀ T, 0 < γ t) {BG : ℝ}
    (hGfin : FieldNormFinite ℓ h 1
      (fun (t : Icc t₀ T) (x : Vec3 × ℝ) => fderiv ℝ (X t.1 0) (X 0 t.1 x.1)))
    (hGn : fieldNorm ℓ h 1
      (fun (t : Icc t₀ T) (x : Vec3 × ℝ) => fderiv ℝ (X t.1 0) (X 0 t.1 x.1)) ≤ BG)
    (q : HierarchyTwistedProfile T k ℝ) :
    S5.wNorm ℓ h t₀ γ 1 ((S5.ops d).labelGrad q) ≤
      ((hierarchyAdmissibleWords (Fin 4) 1).card * (2 : ℝ) ^ 1 * 2) * BG *
        (3 * ℓ⁻¹ * S5.wNorm ℓ h t₀ γ 2 q) := by
  have hA : Icc t₀ T ⊆ Icc 0 T := Icc_subset_Icc_zero ht₀
  obtain ⟨hD3, hD4, -, -⟩ := hD1 (Icc t₀ T) ℓ h hℓ hh (Bridge.restrictWeight (Icc t₀ T) γ)
    (fun t => hγ t t.2) 1
  have hqfin := Bridge.fieldNormFinite_weighted hT ℓ h 2 ht₀ htT hγc hγ q
  obtain ⟨hlfin, -, hl3, -⟩ := hD3 ℝ (Bridge.slices (Icc t₀ T) q) hqfin
  have hslice : Bridge.slices (Icc t₀ T) ((S5.ops d).labelGrad q) =
      ∑ j : Fin 3, (fun (t : Icc t₀ T) (x : Vec3 × ℝ) =>
        labelB j (fderiv ℝ (X t.1 0) (X 0 t.1 x.1))
          (labelPartial j (Bridge.slices (Icc t₀ T) q) t x)) := by
    funext t x
    rw [slices_labelGrad_eq d hA q t x]
    simp only [Finset.sum_apply]
  have hprod (j : Fin 3) := hD4 (Vec3 →L[ℝ] Vec3) ℝ Vec3 (labelB j)
    (fun (t : Icc t₀ T) (x : Vec3 × ℝ) => fderiv ℝ (X t.1 0) (X 0 t.1 x.1))
    (labelPartial j (Bridge.slices (Icc t₀ T) q)) hGfin (hlfin j)
  rw [Bridge.wNorm_eq_weightedFieldNorm, hslice]
  unfold weightedFieldNorm
  rw [weighted_sum]
  refine (fieldNorm_sum_le Finset.univ (fun j _ => (hprod j).1)).trans ?_
  have hGn0 := fieldNorm_nonneg hGfin
  have hBG : 0 ≤ BG := hGn0.trans hGn
  set c0 : ℝ := (hierarchyAdmissibleWords (Fin 4) 1).card * (2 : ℝ) ^ 1 * 2 with hc0
  have hc00 : 0 ≤ c0 := by positivity
  calc _ ≤ ∑ j : Fin 3, c0 * BG * weightedFieldNorm ℓ h (Bridge.restrictWeight (Icc t₀ T) γ) 1
          (labelPartial j (Bridge.slices (Icc t₀ T) q)) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h2 := (hprod j).2
        have hw0 : 0 ≤ weightedFieldNorm ℓ h (Bridge.restrictWeight (Icc t₀ T) γ) 1
            (labelPartial j (Bridge.slices (Icc t₀ T) q)) := fieldNorm_nonneg (hlfin j)
        refine h2.trans (mul_le_mul ?_ le_rfl hw0 (by positivity))
        have hlb := norm_labelB_le j
        have hcard : 0 ≤ ((hierarchyAdmissibleWords (Fin 4) 1).card : ℝ) * (2 : ℝ) ^ 1 := by positivity
        calc _ ≤ ((hierarchyAdmissibleWords (Fin 4) 1).card * (2 : ℝ) ^ 1 * (2 * 1)) *
              fieldNorm ℓ h 1 (fun (t : Icc t₀ T) (x : Vec3 × ℝ) => fderiv ℝ (X t.1 0) (X 0 t.1 x.1)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hlb (by norm_num)) hcard) hGn0
          _ ≤ c0 * BG := mul_le_mul (by rw [hc0]; linarith) hGn hGn0 hc00
    _ = c0 * BG * ∑ j : Fin 3, weightedFieldNorm ℓ h (Bridge.restrictWeight (Icc t₀ T) γ) 1
          (labelPartial j (Bridge.slices (Icc t₀ T) q)) := by rw [Finset.mul_sum]
    _ ≤ c0 * BG * (3 * ℓ⁻¹ * weightedFieldNorm ℓ h (Bridge.restrictWeight (Icc t₀ T) γ) 2
          (Bridge.slices (Icc t₀ T) q)) :=
        mul_le_mul_of_nonneg_left hl3 (mul_nonneg hc00 hBG)

/-- **`‖κ∂_s𝗉‖_{[1],γ} ≤ C ‖P_κ‖_{[1]} (‖f‖_{[1],γ} + C ‖M‖_{[1]} ‖V‖_{[1],γ})`** for a transverse
solution `(V, 𝗉)` of (5.15) with source `f` (`08_exact_wave.tex:219-221`: "the phase term is
bounded by the source and velocity"): `κ∂_s𝗉 = P_κ(f - 2MV)` is a product of the coefficient `P_κ`
with `f + (-2)MV`, itself the sum of `f` and a product of the coefficient `M` with `V`; (D.4) of
`hD_1` is used twice. -/
theorem wNorm_phaseGrad_le (hD1 : Statement.lemma_D_1) (d : ParentGeometry hT U X k)
    {t₀ ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) {γ : ℝ → ℝ}
    (hγc : ContinuousOn γ (Icc t₀ T)) (hγ : ∀ t ∈ Icc t₀ T, 0 < γ t) {BP BM : ℝ}
    (hPfin : FieldNormFinite ℓ h 1 (fun (t : Icc t₀ T) (x : Vec3 × ℝ) =>
      hierarchyLongitudinalProjection (S5.waveVector X k t.1 x.1)))
    (hPn : fieldNorm ℓ h 1 (fun (t : Icc t₀ T) (x : Vec3 × ℝ) =>
      hierarchyLongitudinalProjection (S5.waveVector X k t.1 x.1)) ≤ BP)
    (hMfin : FieldNormFinite ℓ h 1 (fun (t : Icc t₀ T) (x : Vec3 × ℝ) =>
      S5.strainField U X t.1 x.1))
    (hMn : fieldNorm ℓ h 1 (fun (t : Icc t₀ T) (x : Vec3 × ℝ) =>
      S5.strainField U X t.1 x.1) ≤ BM)
    {F V : HierarchyTwistedProfile T k Vec3} {q : HierarchyTwistedProfile T k ℝ}
    (hq : S5.TransverseSolution d F V q) (hF0 : (S5.ops d).average F = 0) :
    S5.wNorm ℓ h t₀ γ 1 ((S5.ops d).phaseGrad q) ≤
      ((hierarchyAdmissibleWords (Fin 4) 1).card * (2 : ℝ) ^ 1 * 2) * BP *
        (S5.wNorm ℓ h t₀ γ 1 F + ((hierarchyAdmissibleWords (Fin 4) 1).card * (2 : ℝ) ^ 1 * 4) *
          BM * S5.wNorm ℓ h t₀ γ 1 V) := by
  have hA : Icc t₀ T ⊆ Icc 0 T := Icc_subset_Icc_zero ht₀
  obtain ⟨-, hD4, -, -⟩ := hD1 (Icc t₀ T) ℓ h hℓ hh (Bridge.restrictWeight (Icc t₀ T) γ)
    (fun t => hγ t t.2) 1
  have hFfin := Bridge.fieldNormFinite_weighted hT ℓ h 1 ht₀ htT hγc hγ F
  have hVfin := Bridge.fieldNormFinite_weighted hT ℓ h 1 ht₀ htT hγc hγ V
  let Pf := fun (t : Icc t₀ T) (x : Vec3 × ℝ) =>
    hierarchyLongitudinalProjection (S5.waveVector X k t.1 x.1)
  let Mf := fun (t : Icc t₀ T) (x : Vec3 × ℝ) => S5.strainField U X t.1 x.1
  let gM : Icc t₀ T → Vec3 × ℝ → Vec3 := fun t x =>
    negB (Mf t x) (Bridge.slices (Icc t₀ T) V t x)
  have hM4 := hD4 (Vec3 →L[ℝ] Vec3) Vec3 Vec3 negB Mf (Bridge.slices (Icc t₀ T) V) hMfin hVfin
  have hgfin : FieldNormFinite ℓ h 1
      (weighted (Bridge.restrictWeight (Icc t₀ T) γ) (Bridge.slices (Icc t₀ T) F + gM)) := by
    rw [weighted_add]
    exact fieldNormFinite_add hFfin hM4.1
  have hP4 := hD4 (Vec3 →L[ℝ] Vec3) Vec3 Vec3 idB Pf (Bridge.slices (Icc t₀ T) F + gM) hPfin hgfin
  have hslice : Bridge.slices (Icc t₀ T) ((S5.ops d).phaseGrad q) =
      fun t x => idB (Pf t x) ((Bridge.slices (Icc t₀ T) F + gM) t x) := by
    funext t x
    rw [slices_phaseGrad_eq d hA hq hF0 t x]
    rfl
  simp only [Bridge.wNorm_eq_weightedFieldNorm]
  rw [hslice]
  have hPn0 := fieldNorm_nonneg hPfin
  have hMn0 := fieldNorm_nonneg hMfin
  have hBP : 0 ≤ BP := hPn0.trans hPn
  have hBM : 0 ≤ BM := hMn0.trans hMn
  set c0 : ℝ := (hierarchyAdmissibleWords (Fin 4) 1).card * (2 : ℝ) ^ 1 with hc0
  have hc00 : 0 ≤ c0 := by positivity
  have hFw0 := fieldNorm_nonneg hFfin
  have hVw0 := fieldNorm_nonneg hVfin
  -- the product `M V`
  have hgM : weightedFieldNorm ℓ h (Bridge.restrictWeight (Icc t₀ T) γ) 1 gM ≤
      c0 * 4 * BM * weightedFieldNorm ℓ h (Bridge.restrictWeight (Icc t₀ T) γ) 1
        (Bridge.slices (Icc t₀ T) V) := by
    refine hM4.2.trans (mul_le_mul ?_ le_rfl (fieldNorm_nonneg hVfin) (by positivity))
    have hn := norm_negB_le
    calc _ ≤ (c0 * (2 * 2)) * fieldNorm ℓ h 1 Mf :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hn (by norm_num)) hc00) hMn0
      _ ≤ c0 * 4 * BM := mul_le_mul (by linarith) hMn hMn0 (by positivity)
  have hsum : weightedFieldNorm ℓ h (Bridge.restrictWeight (Icc t₀ T) γ) 1
      (Bridge.slices (Icc t₀ T) F + gM) ≤
      weightedFieldNorm ℓ h (Bridge.restrictWeight (Icc t₀ T) γ) 1 (Bridge.slices (Icc t₀ T) F) +
        weightedFieldNorm ℓ h (Bridge.restrictWeight (Icc t₀ T) γ) 1 gM := by
    unfold weightedFieldNorm
    rw [weighted_add]
    exact fieldNorm_add_le hFfin hM4.1
  refine hP4.2.trans (mul_le_mul ?_ ?_ (fieldNorm_nonneg hgfin) (by positivity))
  · have hn := norm_idB_le
    calc _ ≤ (c0 * (2 * 1)) * fieldNorm ℓ h 1 Pf :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hn (by norm_num)) hc00) hPn0
      _ ≤ c0 * 2 * BP := mul_le_mul (by linarith) hPn hPn0 (by positivity)
  · refine hsum.trans ?_
    linarith [hgM]

end

end TorusEuler.Paper.Lib.S5c
