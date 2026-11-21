import Breakdown.CertCell.AssemblyPotentialParts
import Breakdown.CertCell.AssemblyPotentialModelFrame
import Breakdown.CertCell.StretchTripleBound
import Breakdown.Cert.CoerciveSmoothMuDecay

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

namespace ModelPart

open Bridge

def curlGradPreimage (Gω : Fin 3 → Fin 3 → ℂ) : Fin 3 × Fin 3 × Fin 3 → ℂ :=
  fun mlj => (1 / 2 : ℂ) * ∑ i : Fin 3, (alternatingSymbol i mlj.2.2 mlj.1 : ℂ) * Gω i mlj.2.1

theorem curlGradOfSecondDeriv_preimage (Gω : Fin 3 → Fin 3 → ℂ) (j l : Fin 3) :
    curlGradOfSecondDeriv (curlGradPreimage Gω) (j, l) = Gω j l := by
  fin_cases j <;> simp [curlGradOfSecondDeriv, curlGradPreimage, Fin.sum_univ_three, alternatingSymbol] <;> norm_num <;> ring

theorem modelTriple_eq_stretchTriple (S Gω : Fin 3 → Fin 3 → ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ)
    (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) :
    modelTriple S Gω a g a' g' = stretchTriple (fun ij => S ij.1 ij.2) (curlGradPreimage Gω) a g a' g' := by
  have hc : ∀ j l, curlGradOfSecondDeriv (curlGradPreimage Gω) (j, l) = Gω j l := curlGradOfSecondDeriv_preimage Gω
  simp only [modelTriple, stretchTriple, modelBilin, stretchBilin, hc]
  simp only [Fin.sum_univ_three]
  ring


def monoFn (i j : ℕ) : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) ^ i * (p.2 : ℂ) ^ j

def lowSpan (a b : ℕ) : Submodule ℂ (ℝ × ℝ → ℂ) :=
  Submodule.span ℂ {h | ∃ i ≤ a, ∃ j ≤ b, h = monoFn i j}

theorem monoFn_mem_lowSpan {a b i j : ℕ} (hi : i ≤ a) (hj : j ≤ b) : monoFn i j ∈ lowSpan a b :=
  Submodule.subset_span ⟨i, hi, j, hj, rfl⟩

theorem lowSpan_mono {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') : lowSpan a b ≤ lowSpan a' b' := by
  apply Submodule.span_mono
  rintro h ⟨i, hi, j, hj, rfl⟩
  exact ⟨i, hi.trans ha, j, hj.trans hb, rfl⟩

theorem monoFn_mul (i j i' j' : ℕ) : monoFn i j * monoFn i' j' = monoFn (i + i') (j + j') := by
  funext p
  simp only [monoFn, Pi.mul_apply, pow_add]
  ring

theorem mul_mem_lowSpan {a b a' b' : ℕ} {g g' : ℝ × ℝ → ℂ} (hg : g ∈ lowSpan a b) (hg' : g' ∈ lowSpan a' b') :
    g * g' ∈ lowSpan (a + a') (b + b') := by
  have h := Submodule.mul_mem_mul hg hg'
  rw [lowSpan, lowSpan, Submodule.span_mul_span] at h
  refine (Submodule.span_le.2 ?_) h
  rintro h ⟨x, ⟨i, hi, j, hj, rfl⟩, y, ⟨i', hi', j', hj', rfl⟩, rfl⟩
  simp only [monoFn_mul]
  exact monoFn_mem_lowSpan (Nat.add_le_add hi hi') (Nat.add_le_add hj hj')

theorem const_mem_lowSpan (a b : ℕ) (c : ℂ) : (fun _ : ℝ × ℝ => c) ∈ lowSpan a b := by
  have h : (fun _ : ℝ × ℝ => c) = c • monoFn 0 0 := by
    funext p
    simp [monoFn]
  rw [h]
  exact Submodule.smul_mem _ _ (monoFn_mem_lowSpan (Nat.zero_le _) (Nat.zero_le _))

theorem star_mem_lowSpan {a b : ℕ} {g : ℝ × ℝ → ℂ} (hg : g ∈ lowSpan a b) :
    (fun p => star (g p)) ∈ lowSpan a b := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    have e : (fun p => star (monoFn i j p)) = monoFn i j := by
      funext p
      simp [monoFn]
    rw [e]
    exact monoFn_mem_lowSpan hi hj
  | zero =>
    have e : (fun p : ℝ × ℝ => star ((0 : ℝ × ℝ → ℂ) p)) = 0 := by
      funext p
      simp
    rw [e]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have e : (fun p => star ((x + y) p)) = (fun p => star (x p)) + (fun p => star (y p)) := by
      funext p
      simp
    rw [e]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have e : (fun p => star ((c • x) p)) = (star c) • (fun p => star (x p)) := by
      funext p
      simp
    rw [e]
    exact Submodule.smul_mem _ _ hx

theorem radialPoly_mem_lowSpan (B : CellCert.CellAnalysis.CellBases) (j : ℕ) :
    (fun p : ℝ × ℝ => ((B.radialPoly j p.1 : ℝ) : ℂ)) ∈ lowSpan j 0 := by
  have e : (fun p : ℝ × ℝ => ((B.radialPoly j p.1 : ℝ) : ℂ))
      = ∑ i ∈ Finset.range (j + 1), ((B.radialCoef j i : ℝ) : ℂ) • monoFn i 0 := by
    funext p
    simp [CellCert.CellAnalysis.CellBases.radialPoly, monoFn, Finset.sum_apply]
  rw [e]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (monoFn_mem_lowSpan ?_ le_rfl)
  exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)

theorem heightPoly_mem_lowSpan (B : CellCert.CellAnalysis.CellBases) (l : ℕ) :
    (fun p : ℝ × ℝ => ((B.heightPoly l p.2 : ℝ) : ℂ)) ∈ lowSpan 0 l := by
  have e : (fun p : ℝ × ℝ => ((B.heightPoly l p.2 : ℝ) : ℂ))
      = ∑ i ∈ Finset.range (l + 1), ((B.heightCoef l i : ℝ) : ℂ) • monoFn 0 i := by
    funext p
    simp [CellCert.CellAnalysis.CellBases.heightPoly, monoFn, Finset.sum_apply]
  rw [e]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (monoFn_mem_lowSpan le_rfl ?_)
  exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)

theorem basisFn_mem_lowSpan (B : CellCert.CellAnalysis.CellBases) (j l : ℕ) :
    (fun p : ℝ × ℝ => ((CellCert.CellEnergy.basisFn B j l p : ℝ) : ℂ)) ∈ lowSpan j l := by
  have h := mul_mem_lowSpan (radialPoly_mem_lowSpan B j) (heightPoly_mem_lowSpan B l)
  simp only [Nat.add_zero, Nat.zero_add] at h
  convert h using 1
  funext p
  simp [CellCert.CellEnergy.basisFn]


def coefS (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) (i j : Fin 3) : ℂ :=
  -(curlOfGrad g i * curlOfGrad g' j + curlOfGrad g' i * curlOfGrad g j) / 2

def coefG (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) (j l : Fin 3) : ℂ :=
  (a l * curlOfGrad g' j + a' l * curlOfGrad g j) / 2
    + (1 / 4 : ℂ) * ∑ i : Fin 3, ∑ n : Fin 3, (alternatingSymbol i l n : ℂ) * (g (i, j) * a' n + g' (i, j) * a n)

theorem modelTriple_eq_coef (S Gω : Fin 3 → Fin 3 → ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ)
    (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) :
    modelTriple S Gω a g a' g'
      = ∑ i : Fin 3, ∑ j : Fin 3, S i j * coefS a g a' g' i j + ∑ j : Fin 3, ∑ l : Fin 3, Gω j l * coefG a g a' g' j l := by
  simp only [modelTriple, modelBilin, coefS, coefG, Fin.sum_univ_three]
  ring



theorem curlOfGrad_add_fn (g g' : Fin 3 × Fin 3 → ℂ) (i : Fin 3) :
    curlOfGrad (g + g') i = curlOfGrad g i + curlOfGrad g' i := by
  simp only [curlOfGrad, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem curlOfGrad_smul_fn (c : ℂ) (g : Fin 3 × Fin 3 → ℂ) (i : Fin 3) :
    curlOfGrad (c • g) i = c * curlOfGrad g i := by
  simp only [curlOfGrad, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem coefS_add_left (a a' : Fin 3 → ℂ) (g g' : Fin 3 × Fin 3 → ℂ) (b : Fin 3 → ℂ) (h : Fin 3 × Fin 3 → ℂ) (i j : Fin 3) :
    coefS (a + a') (g + g') b h i j = coefS a g b h i j + coefS a' g' b h i j := by
  simp only [coefS, curlOfGrad_add_fn]
  ring

theorem coefS_add_right (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (b b' : Fin 3 → ℂ) (h h' : Fin 3 × Fin 3 → ℂ) (i j : Fin 3) :
    coefS a g (b + b') (h + h') i j = coefS a g b h i j + coefS a g b' h' i j := by
  simp only [coefS, curlOfGrad_add_fn]
  ring

theorem coefS_smul_left (c : ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (b : Fin 3 → ℂ) (h : Fin 3 × Fin 3 → ℂ) (i j : Fin 3) :
    coefS (c • a) (c • g) b h i j = c * coefS a g b h i j := by
  simp only [coefS, curlOfGrad_smul_fn]
  ring

theorem coefS_smul_right (c : ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (b : Fin 3 → ℂ) (h : Fin 3 × Fin 3 → ℂ) (i j : Fin 3) :
    coefS a g (c • b) (c • h) i j = c * coefS a g b h i j := by
  simp only [coefS, curlOfGrad_smul_fn]
  ring

theorem coefG_add_left (a a' : Fin 3 → ℂ) (g g' : Fin 3 × Fin 3 → ℂ) (b : Fin 3 → ℂ) (h : Fin 3 × Fin 3 → ℂ) (j l : Fin 3) :
    coefG (a + a') (g + g') b h j l = coefG a g b h j l + coefG a' g' b h j l := by
  simp only [coefG, curlOfGrad_add_fn, Pi.add_apply, Fin.sum_univ_three]
  ring

theorem coefG_add_right (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (b b' : Fin 3 → ℂ) (h h' : Fin 3 × Fin 3 → ℂ) (j l : Fin 3) :
    coefG a g (b + b') (h + h') j l = coefG a g b h j l + coefG a g b' h' j l := by
  simp only [coefG, curlOfGrad_add_fn, Pi.add_apply, Fin.sum_univ_three]
  ring

theorem coefG_smul_left (c : ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (b : Fin 3 → ℂ) (h : Fin 3 × Fin 3 → ℂ) (j l : Fin 3) :
    coefG (c • a) (c • g) b h j l = c * coefG a g b h j l := by
  simp only [coefG, curlOfGrad_smul_fn, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

theorem coefG_smul_right (c : ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (b : Fin 3 → ℂ) (h : Fin 3 × Fin 3 → ℂ) (j l : Fin 3) :
    coefG a g (c • b) (c • h) j l = c * coefG a g b h j l := by
  simp only [coefG, curlOfGrad_smul_fn, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

def tripleBil (S Gω : Fin 3 → Fin 3 → ℂ) :
    ((Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ)) →ₗ[ℂ] ((Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ)) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun x y => modelTriple S Gω x.1 x.2 y.1 y.2)
    (fun x x' y => by
      simp only [modelTriple_eq_coef, Prod.fst_add, Prod.snd_add, coefS_add_left, coefG_add_left, mul_add]
      simp only [Finset.sum_add_distrib]
      ring)
    (fun c x y => by
      simp only [modelTriple_eq_coef, Prod.smul_fst, Prod.smul_snd, coefS_smul_left, coefG_smul_left, smul_eq_mul]
      simp only [mul_add, Finset.mul_sum, mul_left_comm c])
    (fun x y y' => by
      simp only [modelTriple_eq_coef, Prod.fst_add, Prod.snd_add, coefS_add_right, coefG_add_right, mul_add]
      simp only [Finset.sum_add_distrib]
      ring)
    (fun c x y => by
      simp only [modelTriple_eq_coef, Prod.smul_fst, Prod.smul_snd, coefS_smul_right, coefG_smul_right, smul_eq_mul]
      simp only [mul_add, Finset.mul_sum, mul_left_comm c])

theorem tripleBil_apply (S Gω : Fin 3 → Fin 3 → ℂ) (x y : (Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ)) :
    tripleBil S Gω x y = modelTriple S Gω x.1 x.2 y.1 y.2 := rfl


def tripleMatrix (S Gω : Fin 3 → Fin 3 → ℂ) : Matrix (Fin 12) (Fin 12) ℂ :=
  fun i j => modelTriple S Gω (velOf (Pi.single j 1)) (gradOf (Pi.single j 1)) (star (velOf (Pi.single i 1)))
    (star (gradOf (Pi.single i 1)))

def vgOf (U : Fin 12 → ℂ) : (Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ) := (velOf U, gradOf U)

def svgOf (U : Fin 12 → ℂ) : (Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ) := (star (velOf U), star (gradOf U))

theorem vgOf_eq_sum (U : Fin 12 → ℂ) : vgOf U = ∑ j, U j • vgOf (Pi.single j 1) := by
  refine Prod.ext ?_ ?_
  · funext a
    simp [vgOf, velOf, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
  · funext ab
    simp [vgOf, gradOf, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]

theorem svgOf_eq_sum (U : Fin 12 → ℂ) : svgOf U = ∑ i, (starRingEnd ℂ) (U i) • svgOf (Pi.single i 1) := by
  refine Prod.ext ?_ ?_
  · funext a
    simp [svgOf, velOf, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
  · funext ab
    simp [svgOf, gradOf, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]

theorem sesq_tripleMatrix (S Gω : Fin 3 → Fin 3 → ℂ) (U U' : Fin 12 → ℂ) :
    pairSesq (tripleMatrix S Gω) U U'
      = modelTriple S Gω (velOf U') (gradOf U') (star (velOf U)) (star (gradOf U)) := by
  have h : modelTriple S Gω (velOf U') (gradOf U') (star (velOf U)) (star (gradOf U))
      = tripleBil S Gω (vgOf U') (svgOf U) := rfl
  rw [h, vgOf_eq_sum U', svgOf_eq_sum U]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  simp only [pairSesq, tripleMatrix]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [tripleBil_apply]
  simp only [vgOf, svgOf]
  ring


section Torus

open Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation

theorem labelPhase_norm_one (m : ℕ) (ι : ℤ × ℤ) (τ φ : ℝ) : ‖labelPhase m ι τ φ‖ = 1 := by
  unfold labelPhase
  rw [Complex.norm_exp_ofReal_mul_I]

theorem labelPhase_continuous_pair (m : ℕ) (ι : ℤ × ℤ) : Continuous (fun z : ℝ × ℝ => labelPhase m ι z.1 z.2) := by
  unfold labelPhase
  fun_prop

theorem conj_mul_labelPhase (m : ℕ) (ι ι' : ℤ × ℤ) (τ φ : ℝ) :
    (starRingEnd ℂ) (labelPhase m ι τ φ) * labelPhase m ι' τ φ = (starRingEnd ℂ) (labelPhase m (ι - ι') τ φ) := by
  unfold labelPhase labelTime labelAzimuth
  rw [← Complex.exp_conj, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Prod.fst_sub, Prod.snd_sub]
  push_cast
  ring

theorem torusMean_const_mul (c : ℂ) (f : ℝ → ℝ → ℂ) : torusMean (fun τ φ => c * f τ φ) = c * torusMean f := by
  unfold torusMean
  simp only [intervalIntegral.integral_const_mul]
  ring

theorem torusMean_zero : torusMean (fun _ _ => (0 : ℂ)) = 0 := by
  simp [torusMean]

theorem torusIntegrable_add {f g : ℝ → ℝ → ℂ} (hf : IsTorusIntegrable f) (hg : IsTorusIntegrable g) :
    IsTorusIntegrable (fun τ φ => f τ φ + g τ φ) := Integrable.add hf hg

theorem torusIntegrable_sub {f g : ℝ → ℝ → ℂ} (hf : IsTorusIntegrable f) (hg : IsTorusIntegrable g) :
    IsTorusIntegrable (fun τ φ => f τ φ - g τ φ) := Integrable.sub hf hg

theorem torusIntegrable_const_mul (c : ℂ) {f : ℝ → ℝ → ℂ} (hf : IsTorusIntegrable f) :
    IsTorusIntegrable (fun τ φ => c * f τ φ) := Integrable.const_mul hf c

theorem torusIntegrable_finsum {σ : Type*} (S : Finset σ) (f : σ → ℝ → ℝ → ℂ) (hf : ∀ s ∈ S, IsTorusIntegrable (f s)) :
    IsTorusIntegrable (fun τ φ => ∑ s ∈ S, f s τ φ) := by
  unfold IsTorusIntegrable
  have := integrable_finsetSum S (fun s hs => hf s hs)
  simpa [Finset.sum_apply] using this

theorem torusMean_finsum (hT : TorusFacts) {σ : Type*} (S : Finset σ) (f : σ → ℝ → ℝ → ℂ)
    (hf : ∀ s ∈ S, IsTorusIntegrable (f s)) :
    torusMean (fun τ φ => ∑ s ∈ S, f s τ φ) = ∑ s ∈ S, torusMean (f s) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [torusMean_zero]
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    rw [hT.add _ _ (hf a (Finset.mem_insert_self a S))
      (torusIntegrable_finsum S f fun s hs => hf s (Finset.mem_insert_of_mem hs))]
    rw [ih fun s hs => hf s (Finset.mem_insert_of_mem hs)]

theorem torusIntegrable_of_continuous (hT : TorusFacts) {f : ℝ → ℝ → ℂ} (hf : Continuous (fun z : ℝ × ℝ => f z.1 z.2))
    (C : ℝ) (hC : ∀ τ φ, ‖f τ φ‖ ≤ C) : IsTorusIntegrable f :=
  hT.bounded f hf.aestronglyMeasurable ⟨C, fun τ φ _ _ _ _ => hC τ φ⟩

theorem torusMean_wave_normSq (hT : TorusFacts) {m : ℕ} (hm : 1 ≤ m) (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) :
    torusMean (fun τ φ => (((‖∑ ι ∈ S, labelPhase m ι τ φ * c ι‖ ^ 2 : ℝ)) : ℂ)) = ∑ ι ∈ S, ((‖c ι‖ ^ 2 : ℝ) : ℂ) := by
  classical
  have hpt : ∀ τ φ, (((‖∑ ι ∈ S, labelPhase m ι τ φ * c ι‖ ^ 2 : ℝ)) : ℂ)
      = ∑ ι ∈ S, ∑ ι' ∈ S, ((starRingEnd ℂ) (c ι) * c ι') * (starRingEnd ℂ) (labelPhase m (ι - ι') τ φ) := by
    intro τ φ
    rw [Complex.ofReal_pow, ← Complex.conj_mul', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun ι _ => Finset.sum_congr rfl fun ι' _ => ?_
    rw [← conj_mul_labelPhase, map_mul]
    ring
  simp only [hpt]
  have hint : ∀ ι ι' : ℤ × ℤ, IsTorusIntegrable
      (fun τ φ => ((starRingEnd ℂ) (c ι) * c ι') * (starRingEnd ℂ) (labelPhase m (ι - ι') τ φ)) := by
    intro ι ι'
    refine torusIntegrable_of_continuous hT ?_ (‖c ι‖ * ‖c ι'‖) fun τ φ => ?_
    · exact continuous_const.mul (Complex.continuous_conj.comp (labelPhase_continuous_pair m (ι - ι')))
    · rw [norm_mul, Complex.norm_conj, labelPhase_norm_one, mul_one, norm_mul, Complex.norm_conj]
  rw [torusMean_finsum hT S _ fun ι _ => torusIntegrable_finsum S _ fun ι' _ => hint ι ι']
  refine Finset.sum_congr rfl fun ι hι => ?_
  rw [torusMean_finsum hT S _ fun ι' _ => hint ι ι']
  simp only [torusMean_const_mul, hT.label_mean m hm]
  rw [Finset.sum_eq_single ι]
  · simp [sub_self, Complex.conj_mul']
  · intro ι' _ hne
    have : ι - ι' ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    simp [this]
  · intro h
    exact absurd hι h

end Torus

end ModelPart

end Internal

end Assembly

end CertCell

end Breakdown
