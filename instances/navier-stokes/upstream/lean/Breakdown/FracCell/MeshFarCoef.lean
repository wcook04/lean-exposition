import Breakdown.FracCell.MeshFarSt
import Breakdown.FracCell.MeshFarPoly
import Breakdown.FracCell.MeshFarCoefEnergy
import Breakdown.FracCell.MeshFarRegular
import Breakdown.FracCell.LowVelocityExpansion

open MeasureTheory ComplexConjugate

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace MeshFarCoefInternal

theorem exp_shift (m : ℕ) (n n' : ℤ) (θ : ℝ) :
    Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * Complex.exp ((azimuth m n' * θ : ℝ) * Complex.I)
      = Complex.exp (-(azimuth m (n - n') * θ : ℝ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  simp only [azimuth]
  push_cast
  ring

theorem iint_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume 0 (2 * Real.pi)) :
    IntervalIntegrable (fun θ => ∑ i ∈ s, f i θ) volume 0 (2 * Real.pi) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp
  · intro a s ha ih h
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem exp_cont (m : ℕ) (β : ℤ) :
    ContinuousOn (fun θ : ℝ => Complex.exp (-(azimuth m β * θ : ℝ) * Complex.I)) (Set.uIcc 0 (2 * Real.pi)) :=
  Continuous.continuousOn (by fun_prop)

theorem output_expand {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O) (m : ℕ) (B : CellBases)
    (w : (i : I) → ℤ → ℕ → ℕ → Fin (T.dim i) → ℂ) (o : O) (n : ℤ) (p : ℝ × ℝ)
    (hint : ∀ i c, IntervalIntegrable (fun θ => T.mult i o c p θ) volume 0 (2 * Real.pi)) :
    T.outputMode m B w o n p = ∑ i, ∑ c : Fin (T.dim i), ∑ n' ∈ T.inModes,
      (∑ j ∈ Finset.range (T.inputDeg i + 1), ∑ l ∈ Finset.range (T.inputDeg i + 1),
        w i n' j l c * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) *
      ((1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(azimuth m (n - n') * θ : ℝ) * Complex.I) * T.mult i o c p θ) := by
  unfold TailFamily.outputMode TailFamily.inputFn
  have hpt : ∀ θ : ℝ, Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
      (∑ i, ∑ c : Fin (T.dim i), T.mult i o c p θ *
        ∑ n' ∈ T.inModes, ∑ j ∈ Finset.range (T.inputDeg i + 1), ∑ l ∈ Finset.range (T.inputDeg i + 1),
          w i n' j l c * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) *
            Complex.exp ((azimuth m n' * θ : ℝ) * Complex.I))
      = ∑ i, ∑ c : Fin (T.dim i), ∑ n' ∈ T.inModes,
        (∑ j ∈ Finset.range (T.inputDeg i + 1), ∑ l ∈ Finset.range (T.inputDeg i + 1),
          w i n' j l c * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) *
        (Complex.exp (-(azimuth m (n - n') * θ : ℝ) * Complex.I) * T.mult i o c p θ) := by
    intro θ
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n' _ => ?_
    have e1 : (∑ j ∈ Finset.range (T.inputDeg i + 1), ∑ l ∈ Finset.range (T.inputDeg i + 1),
          w i n' j l c * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) *
            Complex.exp ((azimuth m n' * θ : ℝ) * Complex.I)) =
        (∑ j ∈ Finset.range (T.inputDeg i + 1), ∑ l ∈ Finset.range (T.inputDeg i + 1),
          w i n' j l c * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) *
            Complex.exp ((azimuth m n' * θ : ℝ) * Complex.I) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
    rw [e1, ← exp_shift m n n' θ]
    ring
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
  have hI : ∀ i (c : Fin (T.dim i)) (n' : ℤ) (X : ℂ), IntervalIntegrable (fun θ => X *
      (Complex.exp (-(azimuth m (n - n') * θ : ℝ) * Complex.I) * T.mult i o c p θ)) volume 0 (2 * Real.pi) :=
    fun i c n' X => ((hint i c).continuousOn_mul (exp_cont m (n - n'))).const_mul X
  rw [intervalIntegral.integral_finsetSum (fun i _ => iint_sum _ _ fun c _ => iint_sum _ _ fun n' _ => hI i c n' _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun c _ => iint_sum _ _ fun n' _ => hI i c n' _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun n' _ => hI i c n' _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun n' _ => ?_
  rw [intervalIntegral.integral_const_mul]
  ring

def unitE (x y : Fin 3) : Fin 3 → Fin 3 → ℂ := fun a b => if a = x ∧ b = y then 1 else 0

theorem lin_rep (L : (Fin 3 → Fin 3 → ℂ) → ℂ) (hadd : ∀ M N, L (M + N) = L M + L N)
    (hsmul : ∀ (t : ℂ) M, L (t • M) = t * L M) (M : Fin 3 → Fin 3 → ℂ) :
    L M = ∑ x, ∑ y, M x y * L (unitE x y) := by
  let Λ : (Fin 3 → Fin 3 → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := L, map_add' := hadd, map_smul' := fun t U => by simpa using hsmul t U }
  have hM : M = ∑ x, ∑ y, M x y • unitE x y := by
    funext a b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, unitE]
    rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp
    · intro y _ hy
      simp [Ne.symm hy]
    · simp
    · intro x _ hx
      exact Finset.sum_eq_zero fun y _ => by simp [Ne.symm hx]
    · simp
  change Λ M = _
  conv_lhs => rw [hM]
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Λ.map_smul, smul_eq_mul]
  rfl

theorem mode_map (m : ℕ) (β : ℤ) (L : (Fin 3 → Fin 3 → ℂ) → ℂ) (hadd : ∀ M N, L (M + N) = L M + L N)
    (hsmul : ∀ (t : ℂ) M, L (t • M) = t * L M) (f : ℝ → Fin 3 → Fin 3 → ℂ) (r : ℂ)
    (hf : ∀ x y, IntervalIntegrable (fun θ => f θ x y) volume 0 (2 * Real.pi)) :
    (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(azimuth m β * θ : ℝ) * Complex.I) * (r * L (f θ))
    = r * L (fun x y => (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(azimuth m β * θ : ℝ) * Complex.I) * f θ x y) := by
  have hpt : ∀ θ, Complex.exp (-(azimuth m β * θ : ℝ) * Complex.I) * (r * L (f θ)) =
      ∑ x, ∑ y, (r * L (unitE x y)) * (Complex.exp (-(azimuth m β * θ : ℝ) * Complex.I) * f θ x y) := by
    intro θ
    rw [lin_rep L hadd hsmul (f θ), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
  have hI : ∀ x y (X : ℂ), IntervalIntegrable (fun θ => X *
      (Complex.exp (-(azimuth m β * θ : ℝ) * Complex.I) * f θ x y)) volume 0 (2 * Real.pi) :=
    fun x y X => ((hf x y).continuousOn_mul (exp_cont m β)).const_mul X
  rw [intervalIntegral.integral_finsetSum (fun x _ => iint_sum _ _ fun y _ => hI x y _)]
  rw [lin_rep L hadd hsmul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun y _ => hI x y _), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [intervalIntegral.integral_const_mul]
  ring


theorem iint_of_bound (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume) (C : ℝ) (hC : ∀ θ, ‖f θ‖ ≤ C) :
    IntervalIntegrable f volume 0 (2 * Real.pi) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) :=
    isFiniteMeasure_restrict.mpr (by simp [ENNReal.mul_eq_top])
  exact Integrable.mono' (integrable_const C) hf.restrict (ae_of_all _ hC)

theorem rect_meas (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

theorem mult_int (K : CellBox) {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O) (hT : IsTailRegular K T) :
    ∀ᵐ p ∂(volume.restrict K.rect), ∀ i o c, IntervalIntegrable (fun θ => T.mult i o c p θ) volume 0 (2 * Real.pi) := by
  filter_upwards [ae_restrict_mem (rect_meas K), ae_all_iff.2 fun i => ae_all_iff.2 fun o => ae_all_iff.2 fun c =>
    (hT.mult_measurable i o c).prodMk_left] with p hp h i o c
  obtain ⟨C, hC⟩ := hT.mult_bounded i o c
  exact iint_of_bound _ (h i o c) C (fun θ => hC p hp θ)

theorem entries_int (hcyl : CylinderCompStatement) {α : ℝ} {k N : ℕ} (c : FracCellData k N) (hc : IsFormData α c)
    (K : CellBox) (hK : IsCellBox K) (hsol : K.solid ⊆ c.cellRegion) :
    ∀ᵐ p ∂(volume.restrict K.rect), ∀ x y,
      IntervalIntegrable (fun θ => CellScalars.strainAt c p θ x y) volume 0 (2 * Real.pi) ∧
      IntervalIntegrable (fun θ => CellScalars.curlGradAt c p θ x y) volume 0 (2 * Real.pi) := by
  obtain ⟨Cm, hCm⟩ := hc.model_bounded
  have hS := fun x y => (MeshFarRegularInternal.entry_meas hcyl K c.modelStrain hc.model_measurable.2.2.1 x y).prodMk_left
  have hG := fun x y => (MeshFarRegularInternal.entry_meas hcyl K c.modelCurlGrad hc.model_measurable.2.2.2 x y).prodMk_left
  filter_upwards [ae_restrict_mem (rect_meas K), ae_all_iff.2 fun x => ae_all_iff.2 fun y => hS x y,
    ae_all_iff.2 fun x => ae_all_iff.2 fun y => hG x y] with p hp hSp hGp
  intro x y
  have hmem : ∀ θ, cylPoint p.1 θ p.2 ∈ c.cellRegion := fun θ => hsol (MeshFarRegularInternal.cyl_mem K hK p hp θ)
  constructor
  · refine iint_of_bound _ (hSp x y) (4 * Cm) (fun θ => ?_)
    simp only [CellScalars.strainAt, Complex.norm_real]
    exact (MeshFarRegularInternal.frameMat_bound θ _ x y).trans (by linarith [(hCm _ (hmem θ)).2.2.1])
  · refine iint_of_bound _ (hGp x y) (4 * Cm) (fun θ => ?_)
    simp only [CellScalars.curlGradAt, Complex.norm_real]
    exact (MeshFarRegularInternal.frameMat_bound θ _ x y).trans (by linarith [(hCm _ (hmem θ)).2.2.2])

theorem conj_mode (m : ℕ) (β : ℤ) (G : Space → (Space →L[ℝ] Space)) (r z : ℝ) (x y : Fin 3) :
    conj (modeMat m β G r z x y) = modeMat m (-β) G r z x y := by
  have h2 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  unfold modeMat
  rw [map_mul, intervalIntegral.integral_of_le h2, intervalIntegral.integral_of_le h2, ← integral_conj]
  congr 1
  · simp [Complex.conj_ofReal, map_ofNat]
  · congr 1
    funext θ
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, azimuth]
    push_cast
    ring

def velLin (s : Fin 3 → Fin 3 → ℂ) (b : Fin 3) (M : Fin 3 → Fin 3 → ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∑ i : Fin 3, ∑ l : Fin 3,
    (-(∑ j : Fin 3, (CellCert.permSign i l j : ℂ) * M j b)
      + (1 / 2 : ℂ) * ∑ q : Fin 3, (CellCert.permSign i q b : ℂ) * M l q) * s i l

theorem wav_eq (Gm s : Fin 3 → Fin 3 → ℂ) (b : Fin 3) :
    waveActionVelocity Gm s b = velLin s b (fun x y => conj (Gm x y)) := rfl

theorem lin9 (Kc s : Fin 3 → Fin 3 → ℂ) :
    ∑ e : Fin 9, s ⟨e.val / 3, by omega⟩ ⟨e.val % 3, Nat.mod_lt _ (by norm_num)⟩ *
      ∑ i : Fin 3, ∑ l : Fin 3, Kc i l * CellScalars.unitMat e i l = ∑ i : Fin 3, ∑ l : Fin 3, Kc i l * s i l := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single (⟨3 * i.val + l.val, by omega⟩ : Fin 9)]
  · simp only [CellScalars.unitMat, if_true]
    have e1 : (⟨(3 * i.val + l.val) / 3, by omega⟩ : Fin 3) = i := Fin.ext (by simp only; omega)
    have e2 : (⟨(3 * i.val + l.val) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = l := Fin.ext (by simp only; omega)
    rw [e1, e2]
    ring
  · intro e _ he
    have : ¬ (3 * i.val + l.val = e.val) := fun h => he (Fin.ext h.symm)
    simp [CellScalars.unitMat, this]
  · simp

theorem vel_sum (G s : Fin 3 → Fin 3 → ℂ) (o : Fin 3) (r : ℂ) :
    ∑ e : Fin 9, s ⟨e.val / 3, by omega⟩ ⟨e.val % 3, Nat.mod_lt _ (by norm_num)⟩ *
      (r * waveActionVelocity G (CellScalars.unitMat e) o) = r * waveActionVelocity G s o := by
  have h := lin9 (fun i l => (-(∑ j : Fin 3, (CellCert.permSign i l j : ℂ) * conj (G j o))
      + (1 / 2 : ℂ) * ∑ q : Fin 3, (CellCert.permSign i q o : ℂ) * conj (G l q))) s
  simp only [waveActionVelocity, couplingAdj]
  rw [← h, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

theorem strain_sum (M G s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (a b : Fin 3) (r : ℂ) :
    (∑ c' : Fin 3, curlComp s c' * (r * -curlAdj (matVec M (CellScalars.unitVec3 c')) a b))
      + ∑ c' : Fin 3, v c' * (r * ((1 / 2 : ℂ) * couplingMap G (CellScalars.unitVec3 c') a b))
    = r * waveActionStrain M G s v a b := by
  simp only [waveActionStrain, curlAdj, matVec, couplingMap, bracketMat, CellScalars.unitVec3, Fin.sum_univ_three,
    Fin.isValue]
  simp
  ring

theorem curl_sum (s t : Finset ℕ) (C : ℕ → ℕ → Fin 3 → Fin 3 → ℂ) (β : ℕ → ℕ → ℂ) (i : Fin 3) :
    ∑ j ∈ s, ∑ l ∈ t, curlComp (C j l) i * β j l = curlComp (fun a b => ∑ j ∈ s, ∑ l ∈ t, C j l a b * β j l) i := by
  unfold curlComp
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [CellEnergy.LowVelocityExpansion.Internal.swap4]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem proj_mem (K : CellBox) (d d' : ℕ) (F : ℝ × ℝ → ℂ) : K.proj d d' F ∈ polyFn d d' := by
  unfold CellBox.proj
  split_ifs with h
  · exact h.choose_spec.1
  · exact ⟨0, fun p => by simp⟩

theorem expand (K : CellBox) (B : CellBases) (hB : IsCellBases K B) {d : ℕ} {P : ℝ × ℝ → ℂ} (hP : P ∈ polyFn d d)
    (p : ℝ × ℝ) :
    ∑ j ∈ Finset.range (d + 1), ∑ l ∈ Finset.range (d + 1),
      B.coef K P j l * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) = P p := by
  rw [CellEnergy.LowVelocityExpansion.Internal.poly_recon K hB hP p]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [CellEnergy.TopFormInternal.coef_eq K B P j l]
  rfl


theorem sum_swap2 (s : Finset ℤ) (f g : Fin 3 → ℤ → ℂ) :
    (∑ c' : Fin 3, ∑ n' ∈ s, f c' n') + ∑ c' : Fin 3, ∑ n' ∈ s, g c' n' =
      ∑ n' ∈ s, ((∑ c' : Fin 3, f c' n') + ∑ c' : Fin 3, g c' n') := by
  rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (Fin 3))) (f := g), ← Finset.sum_add_distrib]


theorem sum_swap9 (s : Finset ℤ) (f : Fin 9 → ℤ → ℂ) :
    (∑ e : Fin 9, ∑ n' ∈ s, f e n') = ∑ n' ∈ s, ∑ e : Fin 9, f e n' := Finset.sum_comm

theorem velLin_add (s : Fin 3 → Fin 3 → ℂ) (o : Fin 3) (M M' : Fin 3 → Fin 3 → ℂ) :
    velLin s o (M + M') = velLin s o M + velLin s o M' := by
  simp only [velLin, Pi.add_apply, Fin.sum_univ_three]
  ring

theorem velLin_smul (s : Fin 3 → Fin 3 → ℂ) (o : Fin 3) (t : ℂ) (M : Fin 3 → Fin 3 → ℂ) :
    velLin s o (t • M) = t * velLin s o M := by
  simp only [velLin, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

theorem vel_mode {k N : ℕ} (c : FracCellData k N) (p : ℝ × ℝ) (n n' : ℤ) (o : Fin 3) (e : Fin 9) (r : ℂ)
    (hent : ∀ x y, IntervalIntegrable (fun θ => CellScalars.curlGradAt c p θ x y) volume 0 (2 * Real.pi)) :
    (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(azimuth c.order (n - n') * θ : ℝ) * Complex.I) *
        (r * waveActionVelocity (CellScalars.curlGradAt c p θ) (CellScalars.unitMat e) o)
    = r * waveActionVelocity (CellScalars.curlGradMode c (n' - n) p) (CellScalars.unitMat e) o := by
  have hre : ∀ θ, waveActionVelocity (CellScalars.curlGradAt c p θ) (CellScalars.unitMat e) o =
      velLin (CellScalars.unitMat e) o (CellScalars.curlGradAt c p θ) := by
    intro θ
    rw [wav_eq]
    congr 1
    funext x y
    simp [CellScalars.curlGradAt, Complex.conj_ofReal]
  simp_rw [hre]
  rw [mode_map c.order (n - n') (velLin (CellScalars.unitMat e) o) (velLin_add _ o) (velLin_smul _ o)
    (CellScalars.curlGradAt c p) r hent, wav_eq]
  congr 2
  funext x y
  rw [CellScalars.curlGradMode, conj_mode, neg_sub]
  rfl


theorem conv_strain {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)
    (hB : IsCellBases K B) (F : FarMajorantData) (x : FieldTuple k) (ζ : Fin k → ℝ) (n : ℤ) (a b : Fin 3) (p : ℝ × ℝ)
    (hint : ∀ i o c', IntervalIntegrable (fun θ => (CellScalars.strainGroupFamily c K S F).mult i o c' p θ)
      volume 0 (2 * Real.pi))
    (hent : ∀ x y, IntervalIntegrable (fun θ => CellScalars.strainAt c p θ x y) volume 0 (2 * Real.pi) ∧
      IntervalIntegrable (fun θ => CellScalars.curlGradAt c p θ x y) volume 0 (2 * Real.pi)) :
    (CellScalars.strainGroupFamily c K S F).outputMode c.order B
        (CellScalars.strainInput (CellScalars.farVector c K S B x ζ)) (a, b) n p
      = ((CellScalars.rHat K p : ℝ) : ℂ) * ∑ n' ∈ S.resolved,
        waveActionStrain (CellScalars.strainMode c (n - n') p) (CellScalars.curlGradMode c (n - n') p)
          (K.lowStrainAt c.order n' S.degHigh x.2.1 p) (K.lowVelocityAt c.order n' S.degHigh x.1 p) a b := by
  refine (output_expand (CellScalars.strainGroupFamily c K S F) c.order B
    (CellScalars.strainInput (CellScalars.farVector c K S B x ζ)) (a, b) n p (fun i c' => hint i _ c')).trans ?_
  have h10 : ¬ ((1 : Fin 2) = 0) := by decide
  simp only [CellScalars.strainGroupFamily, Fin.sum_univ_two, Fin.isValue, ↓reduceIte, h10]
  have hM0 : ∀ (c' : Fin 3) (n' : ℤ), (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(azimuth c.order (n - n') * θ : ℝ) * Complex.I) *
        (((CellScalars.rHat K p : ℝ) : ℂ) * -curlAdj (matVec (CellScalars.strainAt c p θ) (CellScalars.unitVec3 c')) a b)
      = ((CellScalars.rHat K p : ℝ) : ℂ) *
        -curlAdj (matVec (CellScalars.strainMode c (n - n') p) (CellScalars.unitVec3 c')) a b := by
    intro c' n'
    exact mode_map c.order (n - n') (fun M => -curlAdj (matVec M (CellScalars.unitVec3 c')) a b)
      (fun M N => by simp only [curlAdj, matVec, Pi.add_apply, Fin.sum_univ_three]; ring)
      (fun t M => by simp only [curlAdj, matVec, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]; ring)
      (CellScalars.strainAt c p) _ (fun x y => (hent x y).1)
  have hM1 : ∀ (c' : Fin 3) (n' : ℤ), (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(azimuth c.order (n - n') * θ : ℝ) * Complex.I) *
        (((CellScalars.rHat K p : ℝ) : ℂ) *
          ((1 / 2 : ℂ) * couplingMap (CellScalars.curlGradAt c p θ) (CellScalars.unitVec3 c') a b))
      = ((CellScalars.rHat K p : ℝ) : ℂ) *
        ((1 / 2 : ℂ) * couplingMap (CellScalars.curlGradMode c (n - n') p) (CellScalars.unitVec3 c') a b) := by
    intro c' n'
    exact mode_map c.order (n - n') (fun M => (1 / 2 : ℂ) * couplingMap M (CellScalars.unitVec3 c') a b)
      (fun M N => by simp only [couplingMap, bracketMat, Pi.add_apply, Fin.sum_univ_three]; ring)
      (fun t M => by simp only [couplingMap, bracketMat, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]; ring)
      (CellScalars.curlGradAt c p) _ (fun x y => (hent x y).2)
  have hX0 : ∀ (c' : Fin 3) (n' : ℤ), (∑ j ∈ Finset.range (S.degHigh + 1), ∑ l ∈ Finset.range (S.degHigh + 1),
      CellScalars.strainInput (CellScalars.farVector c K S B x ζ) 0 n' j l c' *
        ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) = curlComp (K.lowStrainAt c.order n' S.degHigh x.2.1 p) c' := by
    intro c' n'
    have e : ∀ j l, CellScalars.strainInput (CellScalars.farVector c K S B x ζ) 0 n' j l c' =
        curlComp (fun a b => B.coef K (fun q => K.lowStrainAt c.order n' S.degHigh x.2.1 q a b) j l) c' := by
      intro j l
      simp only [CellScalars.strainInput, CellScalars.farVector, Fin.isValue, ↓reduceIte]
      congr 1
      funext a' b'
      simp [CellScalars.lowStrainCoef, CellScalars.lowCoef]
    simp_rw [e]
    rw [curl_sum]
    congr 1
    funext a' b'
    exact expand K B hB (proj_mem K _ _ _) p
  have hX1 : ∀ (c' : Fin 3) (n' : ℤ), (∑ j ∈ Finset.range (S.degHigh - 1 + 1), ∑ l ∈ Finset.range (S.degHigh - 1 + 1),
      CellScalars.strainInput (CellScalars.farVector c K S B x ζ) 1 n' j l c' *
        ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) = K.lowVelocityAt c.order n' S.degHigh x.1 p c' := by
    intro c' n'
    have e : ∀ j l, CellScalars.strainInput (CellScalars.farVector c K S B x ζ) 1 n' j l c' =
        B.coef K (fun q => K.lowVelocityAt c.order n' S.degHigh x.1 q c') j l := by
      intro j l
      simp [CellScalars.strainInput, CellScalars.lowVelocityCoef, CellScalars.farVector, CellScalars.lowCoef]
    simp_rw [e]
    exact expand K B hB (proj_mem K _ _ _) p
  simp only [hX0, hX1, hM0, hM1]
  refine (sum_swap2 S.resolved _ _).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun n' _ => strain_sum _ _ _ _ _ _ _

theorem conv_vel {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)
    (hB : IsCellBases K B) (F : FarMajorantData) (x : FieldTuple k) (ζ : Fin k → ℝ) (n : ℤ) (o : Fin 3) (p : ℝ × ℝ)
    (hint : ∀ i o c', IntervalIntegrable (fun θ => (CellScalars.velocityGroupFamily c K S F).mult i o c' p θ)
      volume 0 (2 * Real.pi))
    (hent : ∀ x y, IntervalIntegrable (fun θ => CellScalars.curlGradAt c p θ x y) volume 0 (2 * Real.pi)) :
    (CellScalars.velocityGroupFamily c K S F).outputMode c.order B
        (CellScalars.velocityInput (CellScalars.farVector c K S B x ζ)) o n p
      = ((CellScalars.rHat K p : ℝ) : ℂ) * ∑ n' ∈ S.resolved,
        waveActionVelocity (CellScalars.curlGradMode c (n' - n) p) (K.lowStrainAt c.order n' S.degHigh x.2.1 p) o := by
  refine (output_expand (CellScalars.velocityGroupFamily c K S F) c.order B
    (CellScalars.velocityInput (CellScalars.farVector c K S B x ζ)) o n p (fun i c' => hint i _ c')).trans ?_
  simp only [CellScalars.velocityGroupFamily, Finset.univ_unique, Finset.sum_singleton]
  have hX : ∀ (e : Fin 9) (n' : ℤ), (∑ j ∈ Finset.range (S.degHigh + 1), ∑ l ∈ Finset.range (S.degHigh + 1),
      CellScalars.velocityInput (CellScalars.farVector c K S B x ζ) () n' j l e *
        ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) =
        K.lowStrainAt c.order n' S.degHigh x.2.1 p ⟨e.val / 3, by omega⟩ ⟨e.val % 3, Nat.mod_lt _ (by norm_num)⟩ := by
    intro e n'
    have h : ∀ j l, CellScalars.velocityInput (CellScalars.farVector c K S B x ζ) () n' j l e =
        B.coef K (fun q => K.lowStrainAt c.order n' S.degHigh x.2.1 q ⟨e.val / 3, by omega⟩
          ⟨e.val % 3, Nat.mod_lt _ (by norm_num)⟩) j l := by
      intro j l
      simp only [CellScalars.velocityInput, CellScalars.farVector, CellScalars.lowStrainCoef, CellScalars.lowCoef,
        Sum.elim_inl]
      rw [dif_pos (Nat.mod_lt _ (by norm_num))]
    simp_rw [h]
    exact expand K B hB (proj_mem K _ _ _) p
  simp only [hX, vel_mode c p n _ o _ _ hent]
  refine (sum_swap9 S.resolved _).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun n' _ => vel_sum _ _ _ _

theorem conv_band {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)
    (hB : IsCellBases K B) (F : FarMajorantData) (x : FieldTuple k) (ζ : Fin k → ℝ) (n : ℤ) (o : Fin 3) (p : ℝ × ℝ)
    (hint : ∀ i o c', IntervalIntegrable (fun θ => (CellScalars.bandGroupFamily c K S F).mult i o c' p θ)
      volume 0 (2 * Real.pi))
    (hent : ∀ x y, IntervalIntegrable (fun θ => CellScalars.curlGradAt c p θ x y) volume 0 (2 * Real.pi)) :
    (CellScalars.bandGroupFamily c K S F).outputMode c.order B
        (CellScalars.velocityInput (CellScalars.farVector c K S B x ζ)) o n p
      = ((p.1 * CellScalars.rHat K p : ℝ) : ℂ) * ∑ n' ∈ S.resolved,
        waveActionVelocity (CellScalars.curlGradMode c (n' - n) p) (K.lowStrainAt c.order n' S.degHigh x.2.1 p) o := by
  refine (output_expand (CellScalars.bandGroupFamily c K S F) c.order B
    (CellScalars.velocityInput (CellScalars.farVector c K S B x ζ)) o n p (fun i c' => hint i _ c')).trans ?_
  simp only [CellScalars.bandGroupFamily, Finset.univ_unique, Finset.sum_singleton]
  have hX : ∀ (e : Fin 9) (n' : ℤ), (∑ j ∈ Finset.range (S.degHigh + 1), ∑ l ∈ Finset.range (S.degHigh + 1),
      CellScalars.velocityInput (CellScalars.farVector c K S B x ζ) () n' j l e *
        ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) =
        K.lowStrainAt c.order n' S.degHigh x.2.1 p ⟨e.val / 3, by omega⟩ ⟨e.val % 3, Nat.mod_lt _ (by norm_num)⟩ := by
    intro e n'
    have h : ∀ j l, CellScalars.velocityInput (CellScalars.farVector c K S B x ζ) () n' j l e =
        B.coef K (fun q => K.lowStrainAt c.order n' S.degHigh x.2.1 q ⟨e.val / 3, by omega⟩
          ⟨e.val % 3, Nat.mod_lt _ (by norm_num)⟩) j l := by
      intro j l
      simp only [CellScalars.velocityInput, CellScalars.farVector, CellScalars.lowStrainCoef, CellScalars.lowCoef,
        Sum.elim_inl]
      rw [dif_pos (Nat.mod_lt _ (by norm_num))]
    simp_rw [h]
    exact expand K B hB (proj_mem K _ _ _) p
  simp only [hX, vel_mode c p n _ o _ _ hent]
  refine (sum_swap9 S.resolved _).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun n' _ => vel_sum _ _ _ _

theorem poly_raise {d d' D D' : ℕ} {P : ℝ × ℝ → ℂ} (h : P ∈ polyFn d d') (hd : d ≤ D) (hd' : d' ≤ D') :
    P ∈ polyFn D D' := by
  obtain ⟨cf, hcf⟩ := h
  have e : P = fun p => ∑ j : Fin (d + 1), ∑ l : Fin (d' + 1),
      cf j l * ((p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ)) := by
    funext p
    rw [hcf p]
    simp only [mul_assoc]
  rw [e]
  exact LowEntry.Internal.poly_sum _ _ fun j _ => LowEntry.Internal.poly_sum _ _ fun l _ =>
    LowEntry.Internal.poly_smul _ (LowEntry.Internal.poly_mono (by have := j.isLt; omega) (by have := l.isLt; omega))

theorem poly_mulfst {d d' : ℕ} {P : ℝ × ℝ → ℂ} (h : P ∈ polyFn d d') :
    (fun p : ℝ × ℝ => (p.1 : ℂ) * P p) ∈ polyFn (d + 1) d' := by
  obtain ⟨cf, hcf⟩ := h
  have e : (fun p : ℝ × ℝ => (p.1 : ℂ) * P p) = fun p => ∑ j : Fin (d + 1), ∑ l : Fin (d' + 1),
      cf j l * ((p.1 : ℂ) ^ ((j : ℕ) + 1) * (p.2 : ℂ) ^ (l : ℕ)) := by
    funext p
    rw [hcf p, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [e]
  exact LowEntry.Internal.poly_sum _ _ fun j _ => LowEntry.Internal.poly_sum _ _ fun l _ =>
    LowEntry.Internal.poly_smul _ (LowEntry.Internal.poly_mono (by have := j.isLt; omega) (by have := l.isLt; omega))

theorem rhat_poly (K : CellBox) {H D : ℕ} {Q : ℝ × ℝ → ℂ} (hQ : Q ∈ polyFn H H) (hD : H + 1 ≤ D) :
    ∃ P ∈ polyFn D D, ∀ p : ℝ × ℝ, p.1 ≠ 0 → ((CellScalars.rHat K p : ℝ) : ℂ) * Q p = P p := by
  by_cases h : K.r₁ = 0
  · refine ⟨Q, poly_raise hQ (by omega) (by omega), fun p hp => ?_⟩
    simp [CellScalars.rHat, CellBox.lineWeight, h, hp]
  · refine ⟨fun p => (p.1 : ℂ) * Q p, poly_raise (poly_mulfst hQ) (by omega) (by omega), fun p _ => ?_⟩
    simp [CellScalars.rHat, CellBox.lineWeight, h]

theorem matAct_poly {d : ℕ} (A : Matrix (Fin 12) (Fin 12) ℂ) (s : ℝ × ℝ → Fin 3 → Fin 3 → ℂ) (v : ℝ × ℝ → Fin 3 → ℂ)
    (hs : ∀ a b, (fun q => s q a b) ∈ polyFn d d) (hv : ∀ a, (fun q => v q a) ∈ polyFn d d) (i : Fin 12) :
    (fun q => matAct A (pairVec (s q) (v q)) i) ∈ polyFn d d := by
  unfold matAct
  refine LowEntry.Internal.poly_sum _ _ fun j _ => LowEntry.Internal.poly_smul _ ?_
  by_cases h : j.val < 9
  · simp only [pairVec, dif_pos h]
    exact hs _ _
  · simp only [pairVec, dif_neg h]
    exact hv _

theorem intg (K : CellBox) (B : CellBases) {f : ℝ × ℝ → ℂ} (hm : AEStronglyMeasurable f (volume.restrict K.rect))
    (hb : ∃ C, ∀ p ∈ K.rect, ‖f p‖ ≤ C) (j l : ℕ) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * f p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
      K.rect := by
  obtain ⟨C, hC⟩ := hb
  have := MeshFarCoefEnergyInternal.rect_finite K
  have hf : IntegrableOn f K.rect := Integrable.mono' (integrable_const C) hm
    (by filter_upwards [ae_restrict_mem (rect_meas K)] with p hp using hC p hp)
  have hlw := MeshFarPolyInternal.lineWeight_continuous K
  have hr := MeshFarPolyInternal.radialPoly_continuous B j
  have hh := MeshFarPolyInternal.heightPoly_continuous B l
  have hc : ContinuousOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect := Continuous.continuousOn (by fun_prop)
  refine (hf.mul_continuousOn hc (isCompact_Icc.prod isCompact_Icc)).congr_fun (fun p _ => by ring) (rect_meas K)

theorem coef_lin2 (K : CellBox) (B : CellBases) (F G : ℝ × ℝ → ℂ) (j l : ℕ) (s t : ℂ)
    (hF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect)
    (hG : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * G p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect) :
    B.coef K (fun p => s * F p + t * G p) j l = s * B.coef K F j l + t * B.coef K G j l := by
  unfold CellBases.coef
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hF.const_mul s) (hG.const_mul t)]
  congr 1
  funext p
  ring

theorem coef_ae (K : CellBox) (B : CellBases) (F G : ℝ × ℝ → ℂ) (j l : ℕ)
    (h : ∀ᵐ p ∂(volume.restrict K.rect), F p = G p) : B.coef K F j l = B.coef K G j l := by
  unfold CellBases.coef
  exact integral_congr_ae (h.mono fun p hp => by simp only [hp])

theorem turn_smul (k t : ℝ) (w : Fin 3 → ℂ) (a : Fin 3) :
    (t : ℂ) * turnAdjInv k w a = turnAdjInv k (fun a' => (t : ℂ) * w a') a := by
  fin_cases a <;> simp [turnAdjInv] <;> ring

theorem coef_turn (K : CellBox) (B : CellBases) (k : ℝ) (W : Fin 3 → ℝ × ℝ → ℂ) (j l : ℕ)
    (hW : ∀ a', IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * W a' p *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect) (a : Fin 3) :
    B.coef K (fun p => turnAdjInv k (fun a' => W a' p) a) j l = turnAdjInv k (fun a' => B.coef K (W a') j l) a := by
  fin_cases a
  · have e : (fun p => turnAdjInv k (fun a' => W a' p) 0) = fun p =>
        (1 / (1 - (k : ℂ) ^ 2) * (-(k : ℂ) * Complex.I)) * W 0 p + (-(1 / (1 - (k : ℂ) ^ 2))) * W 1 p := by
      funext p
      simp [turnAdjInv]
      ring
    simp only [Fin.zero_eta, Fin.isValue]
    rw [e, coef_lin2 K B _ _ j l _ _ (hW 0) (hW 1)]
    simp [turnAdjInv]
    ring
  · have e : (fun p => turnAdjInv k (fun a' => W a' p) 1) = fun p =>
        (1 / (1 - (k : ℂ) ^ 2)) * W 0 p + (-(1 / (1 - (k : ℂ) ^ 2) * ((k : ℂ) * Complex.I))) * W 1 p := by
      funext p
      simp [turnAdjInv]
      ring
    simp only [Fin.mk_one, Fin.isValue]
    rw [e, coef_lin2 K B _ _ j l _ _ (hW 0) (hW 1)]
    simp [turnAdjInv]
    ring
  · have e : (fun p => turnAdjInv k (fun a' => W a' p) 2) = fun p =>
        (1 / (-(k : ℂ) * Complex.I)) * W 2 p + 0 * W 0 p := by
      funext p
      change W 2 p / (-(k : ℂ) * Complex.I) = _
      ring
    simp only [Fin.reduceFinMk, Fin.isValue]
    rw [e, coef_lin2 K B _ _ j l _ _ (hW 2) (hW 0)]
    change _ = B.coef K (W 2) j l / (-(k : ℂ) * Complex.I)
    ring

theorem axis_ae (K : CellBox) : ∀ᵐ p ∂(volume.restrict K.rect), p.1 ≠ 0 := by
  have hnull : (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | p.1 = 0} = 0 := by
    have e : {p : ℝ × ℝ | p.1 = 0} = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
      ext p
      simp
    rw [e, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hae : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p.1 ≠ 0 := by
    rw [ae_iff]
    simpa using hnull
  exact ae_restrict_of_ae hae


theorem intg_turn (K : CellBox) (B : CellBases) (k : ℝ) (W : Fin 3 → ℝ × ℝ → ℂ) (j l : ℕ)
    (hW : ∀ a', IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * W a' p *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect) (a : Fin 3) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * turnAdjInv k (fun a' => W a' p) a *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect := by
  fin_cases a
  · refine IntegrableOn.congr_fun (((hW 0).const_mul (1 / (1 - (k : ℂ) ^ 2) * (-(k : ℂ) * Complex.I))).add
      ((hW 1).const_mul (-(1 / (1 - (k : ℂ) ^ 2))))) (fun p _ => ?_) (rect_meas K)
    simp [turnAdjInv]
    ring
  · refine IntegrableOn.congr_fun (((hW 0).const_mul (1 / (1 - (k : ℂ) ^ 2))).add
      ((hW 1).const_mul (-(1 / (1 - (k : ℂ) ^ 2) * ((k : ℂ) * Complex.I))))) (fun p _ => ?_) (rect_meas K)
    simp [turnAdjInv]
    ring
  · refine IntegrableOn.congr_fun ((hW 2).const_mul (1 / (-(k : ℂ) * Complex.I))) (fun p _ => ?_) (rect_meas K)
    show _ = (K.lineWeight p.1 : ℂ) * (W 2 p / (-(k : ℂ) * Complex.I)) * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)
    ring

theorem turn_zero (k : ℝ) (a : Fin 3) : turnAdjInv k (fun _ => (0 : ℂ)) a = 0 := by
  fin_cases a <;> simp [turnAdjInv]


theorem fst_ne_ae (r : ℝ) : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ r := by
  have e : {p : ℝ × ℝ | ¬ p.1 ≠ r} = ({r} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
    ext p
    simp
  rw [ae_iff, e, Measure.volume_eq_prod, Measure.prod_prod]
  simp

theorem snd_ne_ae (z : ℝ) : ∀ᵐ p : ℝ × ℝ ∂volume, p.2 ≠ z := by
  have e : {p : ℝ × ℝ | ¬ p.2 ≠ z} = (Set.univ : Set ℝ) ×ˢ ({z} : Set ℝ) := by
    ext p
    simp
  rw [ae_iff, e, Measure.volume_eq_prod, Measure.prod_prod]
  simp

theorem open_ae (K : CellBox) :
    ∀ᵐ p ∂(volume.restrict K.rect), p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂ := by
  filter_upwards [ae_restrict_mem (rect_meas K), ae_restrict_of_ae (fst_ne_ae K.r₁), ae_restrict_of_ae (fst_ne_ae K.r₂),
    ae_restrict_of_ae (snd_ne_ae K.z₁), ae_restrict_of_ae (snd_ne_ae K.z₂)] with p hp h1 h2 h3 h4
  exact ⟨⟨lt_of_le_of_ne hp.1.1 (Ne.symm h1), lt_of_le_of_ne hp.1.2 h2⟩,
    ⟨lt_of_le_of_ne hp.2.1 (Ne.symm h3), lt_of_le_of_ne hp.2.2 h4⟩⟩


theorem farCoef_main (hcyl : CylinderCompStatement) : FarCoefStatement := by
  intro α hα1 hα2 k N c hc K S B slots R F hK hsol hS hB hsub hF x hx ζ n hn j l hjl
  obtain ⟨hregS, hregV, hregB⟩ := farRegular_of hcyl α hα1 hα2 c hc K S F hK hsol hS
  have hdeg : S.degHigh + 1 ≤ S.degNear := hS.degrees.2.2
  have hgood : ∀ᵐ p ∂(volume.restrict K.rect), p ∈ K.rect ∧ p.1 ≠ 0 ∧ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂ ∧
      (∀ i o c', IntervalIntegrable (fun θ => (CellScalars.strainGroupFamily c K S F).mult i o c' p θ)
        volume 0 (2 * Real.pi)) ∧
      (∀ i o c', IntervalIntegrable (fun θ => (CellScalars.velocityGroupFamily c K S F).mult i o c' p θ)
        volume 0 (2 * Real.pi)) ∧
      (∀ i o c', IntervalIntegrable (fun θ => (CellScalars.bandGroupFamily c K S F).mult i o c' p θ)
        volume 0 (2 * Real.pi)) ∧
      (∀ x y, IntervalIntegrable (fun θ => CellScalars.strainAt c p θ x y) volume 0 (2 * Real.pi) ∧
        IntervalIntegrable (fun θ => CellScalars.curlGradAt c p θ x y) volume 0 (2 * Real.pi)) := by
    filter_upwards [ae_restrict_mem (rect_meas K), axis_ae K, open_ae K, mult_int K _ hregS, mult_int K _ hregV,
      mult_int K _ hregB, entries_int hcyl c hc K hK hsol] with p h0 h1 h6 h2 h3 h4 h5
    exact ⟨h0, h1, h6, h2, h3, h4, h5⟩
  have iS : ∀ o, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) *
      (CellScalars.strainGroupFamily c K S F).outputMode c.order B
        (CellScalars.strainInput (CellScalars.farVector c K S B x ζ)) o n p *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect := fun o =>
    intg K B (MeshFarCoefEnergyInternal.outputMode_regular K c.order B _ hregS _ o n).1
      (MeshFarCoefEnergyInternal.outputMode_regular K c.order B _ hregS _ o n).2 j l
  have iB : ∀ o, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) *
      (CellScalars.bandGroupFamily c K S F).outputMode c.order B
        (CellScalars.velocityInput (CellScalars.farVector c K S B x ζ)) o n p *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect := fun o =>
    intg K B (MeshFarCoefEnergyInternal.outputMode_regular K c.order B _ hregB _ o n).1
      (MeshFarCoefEnergyInternal.outputMode_regular K c.order B _ hregB _ o n).2 j l
  have hact : ∀ a b : Fin 3, ∃ P ∈ polyFn S.degNear S.degNear, ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 →
      ((CellScalars.rHat K p : ℝ) : ℂ) * ∑ i : Fin k,
        (((x.2.2.2.1 i / 2 : ℝ) : ℂ) * modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b
          + ((ζ i : ℝ) : ℂ) * modeMat c.order n (c.modelPinField i) p.1 p.2 a b) = P p := by
    intro a b
    choose Pa hPa hPae using fun i => hF.actuator_poly i n hn a b
    choose Pp hPp hPpe using fun i => hF.pin_poly i n hn a b
    refine ⟨fun p => ∑ i, (((x.2.2.2.1 i / 2 : ℝ) : ℂ) * Pa i p + ((ζ i : ℝ) : ℂ) * Pp i p),
      LowEntry.Internal.poly_sum _ _ fun i _ => LowEntry.Internal.poly_add
        (LowEntry.Internal.poly_smul _ (hPa i)) (LowEntry.Internal.poly_smul _ (hPp i)), fun p hp hp1 => ?_⟩
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hPae i p hp hp1, ← hPpe i p hp hp1]
    ring
  have hloc : n ∈ S.resolved → ∀ i : Fin 12, ∃ P ∈ polyFn S.degNear S.degNear, ∀ p ∈ K.rect, p.1 ≠ 0 →
      ((CellScalars.rHat K p : ℝ) : ℂ) * matAct (S.localMatrix n p)
        (pairVec (K.lowStrainAt c.order n S.degHigh x.2.1 p) (K.lowVelocityAt c.order n S.degHigh x.1 p)) i = P p := by
    intro hnR i
    obtain ⟨P, hP, hPe⟩ := rhat_poly K (matAct_poly (S.localMatrix n (K.r₁, K.z₁))
      (fun q => K.lowStrainAt c.order n S.degHigh x.2.1 q) (fun q => K.lowVelocityAt c.order n S.degHigh x.1 q)
      (fun a b => proj_mem K _ _ _) (fun a => poly_raise (proj_mem K _ _ _) (by omega) (by omega)) i) hdeg
    refine ⟨P, hP, fun p hp hp1 => ?_⟩
    rw [hF.localMatrix_const n hnR p hp]
    exact hPe p hp1
  refine ⟨fun a b => ?_, fun hnR a => ?_⟩
  · obtain ⟨Pact, hPact, hPacte⟩ := hact a b
    by_cases hnR : n ∈ S.resolved
    · have hnB : n ∉ S.band := Finset.disjoint_left.1 hS.disjoint hnR
      obtain ⟨Pl, hPl, hPle⟩ := hloc hnR ⟨3 * a.val + b.val, by omega⟩
      rw [if_pos (Finset.mem_union_left _ hnR), if_neg (fun h => hnB h.1), add_zero]
      have hpt : ∀ᵐ p ∂(volume.restrict K.rect),
          CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b =
            (CellScalars.strainGroupFamily c K S F).outputMode c.order B
              (CellScalars.strainInput (CellScalars.farVector c K S B x ζ)) (a, b) n p + (Pl p + Pact p) := by
        filter_upwards [hgood] with p hp
        obtain ⟨hp, hp1, hpo, h1, h2, h3, h4⟩ := hp
        have hl : ((CellScalars.rHat K p : ℝ) : ℂ) * splitStrain (matAct (S.localMatrix n p)
            (pairVec (K.lowStrainAt c.order n S.degHigh x.2.1 p) (K.lowVelocityAt c.order n S.degHigh x.1 p))) a b
            = Pl p := hPle p hp hp1
        rw [conv_strain c K S B hB F x ζ n a b p h1 h4, ← hl, ← hPacte p hpo hp1]
        simp only [CellScalars.yFolded, if_pos hnR, CellScalars.yStrain, if_pos (Finset.mem_union_left _ hnR)]
        ring
      rw [coef_ae K B _ _ j l hpt]
      exact MeshFarPolyInternal.coef_add_poly K B hB _ _ _ (LowEntry.Internal.poly_add hPl hPact) j l hjl
    · by_cases hnB : n ∈ S.band
      · rw [if_pos (Finset.mem_union_right _ hnB)]
        by_cases hb1 : b = 1
        · rw [if_pos ⟨hnB, hb1⟩]
          have hpt : ∀ᵐ p ∂(volume.restrict K.rect),
              CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b =
                ((CellScalars.strainGroupFamily c K S F).outputMode c.order B
                  (CellScalars.strainInput (CellScalars.farVector c K S B x ζ)) (a, b) n p
                + turnAdjInv (azimuth c.order n) (fun a' => (CellScalars.bandGroupFamily c K S F).outputMode c.order B
                  (CellScalars.velocityInput (CellScalars.farVector c K S B x ζ)) a' n p) a) + Pact p := by
            filter_upwards [hgood] with p hp
            obtain ⟨hp, hp1, hpo, h1, h2, h3, h4⟩ := hp
            have hband : ∀ a', (CellScalars.bandGroupFamily c K S F).outputMode c.order B
                (CellScalars.velocityInput (CellScalars.farVector c K S B x ζ)) a' n p =
                (p.1 : ℂ) * (((CellScalars.rHat K p : ℝ) : ℂ) * ∑ n' ∈ S.resolved,
                  waveActionVelocity (CellScalars.curlGradMode c (n' - n) p)
                    (K.lowStrainAt c.order n' S.degHigh x.2.1 p) a') := by
              intro a'
              rw [conv_band c K S B hB F x ζ n a' p h3 (fun x y => (h4 x y).2)]
              push_cast
              ring
            have hv : CellScalars.yVelocity c K S x.1 x.2.1 n p = fun a' => ((CellScalars.rHat K p : ℝ) : ℂ) *
                ∑ n' ∈ S.resolved, waveActionVelocity (CellScalars.curlGradMode c (n' - n) p)
                  (K.lowStrainAt c.order n' S.degHigh x.2.1 p) a' := by
              funext a'
              simp only [CellScalars.yVelocity, if_pos (Finset.mem_union_right _ hnB), if_neg hnR, add_zero]
            have hs : CellScalars.yStrain c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b =
                ((CellScalars.rHat K p : ℝ) : ℂ) * ∑ n' ∈ S.resolved,
                  waveActionStrain (CellScalars.strainMode c (n - n') p) (CellScalars.curlGradMode c (n - n') p)
                    (K.lowStrainAt c.order n' S.degHigh x.2.1 p) (K.lowVelocityAt c.order n' S.degHigh x.1 p) a b
                + ((CellScalars.rHat K p : ℝ) : ℂ) * ∑ i : Fin k,
                  (((x.2.2.2.1 i / 2 : ℝ) : ℂ) * modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b
                    + ((ζ i : ℝ) : ℂ) * modeMat c.order n (c.modelPinField i) p.1 p.2 a b) := by
              simp only [CellScalars.yStrain, if_pos (Finset.mem_union_right _ hnB), if_neg hnR, add_zero]
              ring
            have hf : CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b =
                CellScalars.yStrain c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b +
                  (p.1 : ℂ) * turnAdjInv (azimuth c.order n) (CellScalars.yVelocity c K S x.1 x.2.1 n p) a := by
              simp only [CellScalars.yFolded, if_neg hnR, foldVelocity, if_pos hb1]
            rw [hf, hs, hv, turn_smul, conv_strain c K S B hB F x ζ n a b p h1 h4, ← hPacte p hpo hp1]
            simp only [hband]
            ring
          rw [coef_ae K B _ _ j l hpt, MeshFarPolyInternal.coef_add_poly K B hB _ _ _ hPact j l hjl]
          have h := coef_lin2 K B _ _ j l 1 1 (iS (a, b)) (intg_turn K B (azimuth c.order n) _ j l iB a)
          simp only [one_mul] at h
          rw [h, coef_turn K B (azimuth c.order n) _ j l iB a]
        · rw [if_neg (fun h => hb1 h.2), add_zero]
          have hpt : ∀ᵐ p ∂(volume.restrict K.rect),
              CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b =
                (CellScalars.strainGroupFamily c K S F).outputMode c.order B
                  (CellScalars.strainInput (CellScalars.farVector c K S B x ζ)) (a, b) n p + Pact p := by
            filter_upwards [hgood] with p hp
            obtain ⟨hp, hp1, hpo, h1, h2, h3, h4⟩ := hp
            rw [conv_strain c K S B hB F x ζ n a b p h1 h4, ← hPacte p hpo hp1]
            simp only [CellScalars.yFolded, if_neg hnR, foldVelocity, if_neg hb1, CellScalars.yStrain,
              if_pos (Finset.mem_union_right _ hnB)]
            ring
          rw [coef_ae K B _ _ j l hpt]
          exact MeshFarPolyInternal.coef_add_poly K B hB _ _ _ hPact j l hjl
      · have hnRB : n ∉ S.resolved ∪ S.band := fun h => (Finset.mem_union.1 h).elim hnR hnB
        rw [if_neg hnRB, if_neg (fun h => hnB h.1), add_zero]
        have hpt : ∀ᵐ p ∂(volume.restrict K.rect),
            CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b = (fun _ => (0 : ℂ)) p + Pact p := by
          filter_upwards [hgood] with p hp
          obtain ⟨hp, hp1, hpo, h1, h2, h3, h4⟩ := hp
          rw [← hPacte p hpo hp1]
          have hv0 : CellScalars.yVelocity c K S x.1 x.2.1 n p = fun _ => (0 : ℂ) := by
            funext a'
            simp only [CellScalars.yVelocity, if_neg hnRB, if_neg hnR, add_zero, mul_zero]
          simp only [CellScalars.yFolded, if_neg hnR, foldVelocity, CellScalars.yStrain, hv0, turn_zero,
            if_neg hnRB, zero_add, add_zero, mul_zero]
          split_ifs <;> ring
        rw [coef_ae K B _ _ j l hpt, MeshFarPolyInternal.coef_add_poly K B hB _ _ _ hPact j l hjl]
        simp [CellBases.coef]
  · obtain ⟨Pl, hPl, hPle⟩ := hloc hnR ⟨9 + a.val, by omega⟩
    have hpt : ∀ᵐ p ∂(volume.restrict K.rect),
        CellScalars.yVelocity c K S x.1 x.2.1 n p a =
          (CellScalars.velocityGroupFamily c K S F).outputMode c.order B
            (CellScalars.velocityInput (CellScalars.farVector c K S B x ζ)) a n p + Pl p := by
      filter_upwards [hgood] with p hp
      obtain ⟨hp, hp1, hpo, h1, h2, h3, h4⟩ := hp
      have hl : ((CellScalars.rHat K p : ℝ) : ℂ) * splitVelocity (matAct (S.localMatrix n p)
          (pairVec (K.lowStrainAt c.order n S.degHigh x.2.1 p) (K.lowVelocityAt c.order n S.degHigh x.1 p))) a
          = Pl p := hPle p hp hp1
      rw [conv_vel c K S B hB F x ζ n a p h2 (fun x y => (h4 x y).2), ← hl]
      simp only [CellScalars.yVelocity, if_pos (Finset.mem_union_left _ hnR), if_pos hnR]
      ring
    rw [coef_ae K B _ _ j l hpt]
    exact MeshFarPolyInternal.coef_add_poly K B hB _ _ _ hPl j l hjl

end MeshFarCoefInternal

theorem farCoef (hcyl : CylinderCompStatement) : FarCoefStatement :=
  MeshFarCoefInternal.farCoef_main hcyl

end CellAnalysis

end CellCert

end Breakdown
