import Breakdown.FracCell.SharpModeExpansionRegular
import Breakdown.FracCell.CircleSliceCoupling
import Breakdown.FracCell.CircleSliceRegular
import Breakdown.FracCell.CellDensityModesCoupling
import Breakdown.FracCell.CellDensityModesSolid

open MeasureTheory Real ComplexConjugate

noncomputable section

namespace Breakdown.CellCert.CellAnalysis.SharpMxModeWaveRegular.Internal

open SteadyCert Assembly SharpParts ModeExpansionParts
open Breakdown.FracInternal.DensitySlice Breakdown.FracInternal.CircleSliceCoupling

theorem atom_sum {m : ℕ} (hm : 0 < m) {w g : ℝ → ℝ} (hw : MemLp w 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (hg : IsCircleSliceRegular m g) (hgp : ∀ θ, g (θ + 2 * π) = g θ) (n : ℤ) :
    Summable (fun n' : ℤ => cf m (n - n') w * cf m n' g) :=
  (atom_inner hm hw hg hgp n).summable

theorem atom_sum_conj {m : ℕ} (hm : 0 < m) {w g : ℝ → ℝ} (hw : MemLp w 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (hg : IsCircleSliceRegular m g) (hgp : ∀ θ, g (θ + 2 * π) = g θ) (n : ℤ) (X : ℂ) :
    Summable (fun n' : ℤ => conj (cf m n' g) * (cf m (n' - n) w * X)) := by
  refine ((Complex.summable_conj.2 (atom_sum hm hw hg hgp n)).mul_right X).congr fun n' => ?_
  rw [map_mul, cf_conj m n' n w]
  ring

theorem right_sum {m : ℕ} (hm : 0 < m) (D S G : ℝ → Fin 3 → Fin 3 → ℝ) (V : ℝ → Fin 3 → ℝ)
    (hD : ∀ a b, IsCircleSliceRegular m (fun θ => D θ a b)) (hDp : ∀ θ, D (θ + 2 * π) = D θ)
    (hV : ∀ a, IsCircleSliceRegular m (fun θ => V θ a)) (hVp : ∀ θ, V (θ + 2 * π) = V θ)
    (mS : ∀ a b, MemLp (fun θ => S θ a b) 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (mG : ∀ a b, MemLp (fun θ => G θ a b) 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (n : ℤ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) :
    Summable (fun n' : ℤ => waveForm (fun a b => cf m (n - n') (fun θ => S θ a b))
        (fun a b => cf m (n - n') (fun θ => G θ a b)) (fun a b => cf m (n' - n) (fun θ => G θ a b))
        s v (fun a b => cf m n' (fun θ => D θ a b)) (fun a => cf m n' (fun θ => V θ a))) := by
  have rK : ∀ a, IsCircleSliceRegular m (fun θ => curlRow (D θ) a) := fun a =>
    regular_sum _ fun j _ => regular_sum _ fun l _ => regular_const _ (hD l j)
  have pK : ∀ a θ, curlRow (D (θ + 2 * π)) a = curlRow (D θ) a := fun a θ => by rw [hDp]
  have pD : ∀ a b θ, D (θ + 2 * π) a b = D θ a b := fun a b θ => by rw [hDp]
  have pV : ∀ a θ, V (θ + 2 * π) a = V θ a := fun a θ => by rw [hVp]
  have cK : ∀ (n : ℤ) a, curlComp (fun a b => cf m n (fun θ => D θ a b)) a = cf m n (fun θ => curlRow (D θ) a) :=
    fun n a => curl_coeff D (fun a b => regular_integrable (hD a b)) n a
  simp only [wave_expand, cK, cf_conj]
  refine ((((Summable.neg (summable_sum fun a _ => summable_sum fun b _ => ?_)).add
    (summable_sum fun i _ => summable_sum fun l _ => summable_sum fun j _ => summable_sum fun b _ => ?_)).add
    (summable_sum fun i _ => summable_sum fun l _ => summable_sum fun q _ => summable_sum fun j _ => ?_)).add
    (summable_sum fun i _ => summable_sum fun l _ => summable_sum fun j _ => summable_sum fun b _ => ?_)).add
    (summable_sum fun i _ => summable_sum fun l _ => summable_sum fun q _ => summable_sum fun j _ => ?_)
  · exact (atom_sum hm (mS a b) (rK b) (pK b) n).mul_left _
  · exact ((atom_sum hm (mG j b) (hV b) (pV b) n).mul_left _).mul_left _
  · exact ((atom_sum hm (mG l q) (hV j) (pV j) n).mul_left _).mul_left _
  · exact ((atom_sum hm (mG j b) (hD i l) (pD i l) n).mul_left _).mul_left _
  · exact ((atom_sum hm (mG l q) (hD i l) (pD i l) n).mul_left _).mul_left _

theorem left_sum {m : ℕ} (hm : 0 < m) (D S G : ℝ → Fin 3 → Fin 3 → ℝ) (V : ℝ → Fin 3 → ℝ)
    (hD : ∀ a b, IsCircleSliceRegular m (fun θ => D θ a b)) (hDp : ∀ θ, D (θ + 2 * π) = D θ)
    (hV : ∀ a, IsCircleSliceRegular m (fun θ => V θ a)) (hVp : ∀ θ, V (θ + 2 * π) = V θ)
    (mS : ∀ a b, MemLp (fun θ => S θ a b) 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (mG : ∀ a b, MemLp (fun θ => G θ a b) 2 (volume.restrict (Set.Ioc 0 (2 * π))))
    (n : ℤ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) :
    Summable (fun n' : ℤ => waveForm (fun a b => cf m (n' - n) (fun θ => S θ a b))
        (fun a b => cf m (n' - n) (fun θ => G θ a b)) (fun a b => cf m (n - n') (fun θ => G θ a b))
        (fun a b => cf m n' (fun θ => D θ a b)) (fun a => cf m n' (fun θ => V θ a)) s v) := by
  have rK : ∀ a, IsCircleSliceRegular m (fun θ => curlRow (D θ) a) := fun a =>
    regular_sum _ fun j _ => regular_sum _ fun l _ => regular_const _ (hD l j)
  have pK : ∀ a θ, curlRow (D (θ + 2 * π)) a = curlRow (D θ) a := fun a θ => by rw [hDp]
  have pD : ∀ a b θ, D (θ + 2 * π) a b = D θ a b := fun a b θ => by rw [hDp]
  have pV : ∀ a θ, V (θ + 2 * π) a = V θ a := fun a θ => by rw [hVp]
  have cK : ∀ (n : ℤ) a, curlComp (fun a b => cf m n (fun θ => D θ a b)) a = cf m n (fun θ => curlRow (D θ) a) :=
    fun n a => curl_coeff D (fun a b => regular_integrable (hD a b)) n a
  simp only [wave_expand, cK, cf_conj]
  refine ((((Summable.neg (summable_sum fun a _ => summable_sum fun b _ => ?_)).add
    (summable_sum fun i _ => summable_sum fun l _ => summable_sum fun j _ => summable_sum fun b _ => ?_)).add
    (summable_sum fun i _ => summable_sum fun l _ => summable_sum fun q _ => summable_sum fun j _ => ?_)).add
    (summable_sum fun i _ => summable_sum fun l _ => summable_sum fun j _ => summable_sum fun b _ => ?_)).add
    (summable_sum fun i _ => summable_sum fun l _ => summable_sum fun q _ => summable_sum fun j _ => ?_)
  · exact atom_sum_conj hm (mS a b) (rK a) (pK a) n _
  · exact (atom_sum_conj hm (mG j b) (hD i l) (pD i l) n _).mul_left _
  · exact (atom_sum_conj hm (mG l q) (hD i l) (pD i l) n _).mul_left _
  · exact (atom_sum_conj hm (mG j b) (hV b) (pV b) n _).mul_left _
  · exact (atom_sum_conj hm (mG l q) (hV j) (pV j) n _).mul_left _

theorem wave_sub_right (A B C s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (s₁ s₂ : Fin 3 → Fin 3 → ℂ)
    (v₁ v₂ : Fin 3 → ℂ) :
    waveForm A B C s v (fun a b => s₁ a b - s₂ a b) (fun a => v₁ a - v₂ a) =
      waveForm A B C s v s₁ v₁ - waveForm A B C s v s₂ v₂ := by
  simp only [wave_expand, curlComp, Fin.sum_univ_three]
  ring

theorem wave_sub_left (A B C : Fin 3 → Fin 3 → ℂ) (s₁ s₂ : Fin 3 → Fin 3 → ℂ) (v₁ v₂ : Fin 3 → ℂ)
    (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) :
    waveForm A B C (fun a b => s₁ a b - s₂ a b) (fun a => v₁ a - v₂ a) s v =
      waveForm A B C s₁ v₁ s v - waveForm A B C s₂ v₂ s v := by
  have h1 : ∀ a, curlComp (fun a b => s₁ a b - s₂ a b) a = curlComp s₁ a - curlComp s₂ a := by
    intro a
    simp only [curlComp, mul_sub, Finset.sum_sub_distrib]
  simp only [wave_expand, h1, map_sub, sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring

theorem wave_zero_right (A B C s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) :
    waveForm A B C s v 0 0 = 0 := by
  simp [wave_expand, curlComp]

theorem wave_zero_left (A B C s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) :
    waveForm A B C 0 0 s v = 0 := by
  simp [wave_expand, curlComp]

section Concrete

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

def fullPair (n n' : ℤ) (p : ℝ × ℝ) : ℂ :=
  pairWave c n n' p (fun a b => gradMode c.order n x.2.1 a b p) (modeVec c.order n x.1 p.1 p.2)
    (fun a b => gradMode c.order n' x.2.1 a b p) (modeVec c.order n' x.1 p.1 p.2)

def lowFullPair (n n' : ℤ) (p : ℝ × ℝ) : ℂ :=
  pairWave c n n' p (lowGrad c K S x n p) (lowVel c K S x n p)
    (fun a b => gradMode c.order n' x.2.1 a b p) (modeVec c.order n' x.1 p.1 p.2)

def sharpLowTerm (n n' : ℤ) (p : ℝ × ℝ) : ℂ :=
  pairWave c n n' p (sharpGrad c K S x n p) (sharpVel c K S x n p) (lowGrad c K S x n' p) (lowVel c K S x n' p)

theorem low_out {n : ℤ} (hn : n ∉ S.resolved) (p : ℝ × ℝ) :
    lowGrad c K S x n p = 0 ∧ lowVel c K S x n p = 0 := by
  simp only [lowGrad, lowVel, if_neg hn, and_self]

theorem sharp_split (n n' : ℤ) (p : ℝ × ℝ) :
    sharpPair c K S x n n' p = fullPair c x n n' p - lowFullPair c K S x n n' p - sharpLowTerm c K S x n n' p := by
  have e3 := wave_sub_right (CellScalars.strainMode c (n - n') p) (CellScalars.curlGradMode c (n - n') p)
    (CellScalars.curlGradMode c (n' - n) p) (sharpGrad c K S x n p) (sharpVel c K S x n p)
    (fun a b => gradMode c.order n' x.2.1 a b p) (lowGrad c K S x n' p) (modeVec c.order n' x.1 p.1 p.2)
    (lowVel c K S x n' p)
  have e2 := wave_sub_left (CellScalars.strainMode c (n - n') p) (CellScalars.curlGradMode c (n - n') p)
    (CellScalars.curlGradMode c (n' - n) p) (fun a b => gradMode c.order n x.2.1 a b p) (lowGrad c K S x n p)
    (modeVec c.order n x.1 p.1 p.2) (lowVel c K S x n p)
    (fun a b => gradMode c.order n' x.2.1 a b p) (modeVec c.order n' x.1 p.1 p.2)
  exact e3.trans (congrArg (· - sharpLowTerm c K S x n n' p) e2)

variable (p : ℝ × ℝ)

theorem slice_right (hm : 0 < c.order) (hd : IsCircleSliceData c x p) (n : ℤ) (s : Fin 3 → Fin 3 → ℂ)
    (v : Fin 3 → ℂ) :
    Summable (fun n' : ℤ => waveForm (CellScalars.strainMode c (n - n') p) (CellScalars.curlGradMode c (n - n') p)
      (CellScalars.curlGradMode c (n' - n) p) s v (fun a b => gradMode c.order n' x.2.1 a b p)
      (modeVec c.order n' x.1 p.1 p.2)) := by
  obtain ⟨hV, hD, -, hSG, ⟨C, hC⟩, -, -⟩ := hd
  exact right_sum hm (fun θ => frameMat θ (x.2.1 (cylPoint p.1 θ p.2)))
    (fun θ => frameMat θ (c.modelStrain (cylPoint p.1 θ p.2)))
    (fun θ => frameMat θ (c.modelCurlGrad (cylPoint p.1 θ p.2)))
    (fun θ => frameVec θ (x.1 (cylPoint p.1 θ p.2))) hD
    (fun θ => by funext a b; simp only [cyl_per, frameMat_add]) hV
    (fun θ => by
      funext a
      simp only [cyl_per, frameVec, radialUnit, angularUnit, Real.cos_add_two_pi, Real.sin_add_two_pi])
    (fun a b => bounded_memLp_self (hSG a b).1 (fun θ => (hC θ a b).1))
    (fun a b => bounded_memLp_self (hSG a b).2 (fun θ => (hC θ a b).2)) n s v

theorem slice_left (hm : 0 < c.order) (hd : IsCircleSliceData c x p) (n : ℤ) (s : Fin 3 → Fin 3 → ℂ)
    (v : Fin 3 → ℂ) :
    Summable (fun n' : ℤ => waveForm (CellScalars.strainMode c (n' - n) p) (CellScalars.curlGradMode c (n' - n) p)
      (CellScalars.curlGradMode c (n - n') p) (fun a b => gradMode c.order n' x.2.1 a b p)
      (modeVec c.order n' x.1 p.1 p.2) s v) := by
  obtain ⟨hV, hD, -, hSG, ⟨C, hC⟩, -, -⟩ := hd
  exact left_sum hm (fun θ => frameMat θ (x.2.1 (cylPoint p.1 θ p.2)))
    (fun θ => frameMat θ (c.modelStrain (cylPoint p.1 θ p.2)))
    (fun θ => frameMat θ (c.modelCurlGrad (cylPoint p.1 θ p.2)))
    (fun θ => frameVec θ (x.1 (cylPoint p.1 θ p.2))) hD
    (fun θ => by funext a b; simp only [cyl_per, frameMat_add]) hV
    (fun θ => by
      funext a
      simp only [cyl_per, frameVec, radialUnit, angularUnit, Real.cos_add_two_pi, Real.sin_add_two_pi])
    (fun a b => bounded_memLp_self (hSG a b).1 (fun θ => (hC θ a b).1))
    (fun a b => bounded_memLp_self (hSG a b).2 (fun θ => (hC θ a b).2)) n s v

theorem full_outer (hm : 0 < c.order) (hd : IsCircleSliceData c x p) :
    Summable (fun n : ℤ => ∑' n' : ℤ, fullPair c x n n' p) := by
  obtain ⟨hV, hD, -, hSG, ⟨C, hC⟩, -, -⟩ := hd
  exact (hbase hm (fun θ => frameMat θ (x.2.1 (cylPoint p.1 θ p.2)))
    (fun θ => frameMat θ (c.modelStrain (cylPoint p.1 θ p.2)))
    (fun θ => frameMat θ (c.modelCurlGrad (cylPoint p.1 θ p.2)))
    (fun θ => frameVec θ (x.1 (cylPoint p.1 θ p.2))) hD
    (fun θ => by funext a b; simp only [cyl_per, frameMat_add]) hV
    (fun θ => by
      funext a
      simp only [cyl_per, frameVec, radialUnit, angularUnit, Real.cos_add_two_pi, Real.sin_add_two_pi])
    (fun a b => (hSG a b).1) (fun a b => (hSG a b).2) C hC).2.summable

theorem sharp_right (hm : 0 < c.order) (hd : IsCircleSliceData c x p) (n : ℤ) (s : Fin 3 → Fin 3 → ℂ)
    (v : Fin 3 → ℂ) :
    Summable (fun n' : ℤ => waveForm (CellScalars.strainMode c (n - n') p) (CellScalars.curlGradMode c (n - n') p)
      (CellScalars.curlGradMode c (n' - n) p) s v (sharpGrad c K S x n' p) (sharpVel c K S x n' p)) := by
  have low : Summable (fun n' : ℤ => waveForm (CellScalars.strainMode c (n - n') p)
      (CellScalars.curlGradMode c (n - n') p) (CellScalars.curlGradMode c (n' - n) p) s v
      (lowGrad c K S x n' p) (lowVel c K S x n' p)) := by
    refine summable_of_ne_finset_zero (s := S.resolved) fun n' hn' => ?_
    rw [(low_out c K S x hn' p).1, (low_out c K S x hn' p).2]
    exact wave_zero_right _ _ _ _ _
  refine ((slice_right c x p hm hd n s v).sub low).congr fun n' => ?_
  exact (wave_sub_right _ _ _ _ _ _ _ _ _).symm

theorem sharp_left (hm : 0 < c.order) (hd : IsCircleSliceData c x p) (n : ℤ) (s : Fin 3 → Fin 3 → ℂ)
    (v : Fin 3 → ℂ) :
    Summable (fun n' : ℤ => waveForm (CellScalars.strainMode c (n' - n) p) (CellScalars.curlGradMode c (n' - n) p)
      (CellScalars.curlGradMode c (n - n') p) (sharpGrad c K S x n' p) (sharpVel c K S x n' p) s v) := by
  have low : Summable (fun n' : ℤ => waveForm (CellScalars.strainMode c (n' - n) p)
      (CellScalars.curlGradMode c (n' - n) p) (CellScalars.curlGradMode c (n - n') p)
      (lowGrad c K S x n' p) (lowVel c K S x n' p) s v) := by
    refine summable_of_ne_finset_zero (s := S.resolved) fun n' hn' => ?_
    rw [(low_out c K S x hn' p).1, (low_out c K S x hn' p).2]
    exact wave_zero_left _ _ _ _ _
  refine ((slice_left c x p hm hd n s v).sub low).congr fun n' => ?_
  exact (wave_sub_left _ _ _ _ _ _ _ _ _).symm

theorem entry_sub (s t u : Fin 3 → Fin 3 → ℂ) :
    entryPairing (fun a b => s a b - t a b) u = entryPairing s u - entryPairing t u := by
  simp only [entryPairing, sub_mul, Finset.sum_sub_distrib]

theorem field_sum (hm : 0 < c.order) (hd : IsCircleSliceData c x p) (E : Space → (Space →L[ℝ] Space))
    (hE : ∀ a b, MemLp (fun θ => frameMat θ (E (cylPoint p.1 θ p.2)) a b) 2 (volume.restrict (Set.Ioc 0 (2 * π)))) :
    Summable (fun n : ℤ => fieldSharp c K S x E n p) := by
  have full := (slice_pair hm x.2.1 E p.1 p.2 hd.2.1 hE).summable
  have low : Summable (fun n : ℤ => entryPairing (lowGrad c K S x n p) (fun a b => modeMat c.order n E p.1 p.2 a b)) := by
    refine summable_of_ne_finset_zero (s := S.resolved) fun n hn => ?_
    rw [(low_out c K S x hn p).1]
    simp [entryPairing]
  refine (full.sub low).congr fun n => ?_
  exact (entry_sub _ _ _).symm

theorem pointwise (hm : 0 < c.order) (hd : IsCircleSliceData c x p) :
    (∀ n, Summable (fun n' => sharpPair c K S x n n' p)) ∧
    Summable (fun n => ∑' n', sharpPair c K S x n n' p) ∧
    (∀ n ∈ S.resolved, Summable (fun n' => lowSharpPair c K S x n n' p) ∧
      Summable (fun n' => sharpLowPair c K S x n' n p)) ∧
    (∀ i, Summable (fun n => fieldSharp c K S x (c.modelActuatorGrad i) n p) ∧
      Summable (fun n => fieldSharp c K S x (c.modelPinField i) n p)) := by
  refine ⟨fun n => sharp_right c K S x p hm hd n (sharpGrad c K S x n p) (sharpVel c K S x n p), ?_,
    fun n _ => ⟨sharp_right c K S x p hm hd n (lowGrad c K S x n p) (lowVel c K S x n p),
      sharp_left c K S x p hm hd n (lowGrad c K S x n p) (lowVel c K S x n p)⟩,
    fun i => ⟨field_sum c K S x p hm hd _ fun a b => (hd.2.2.2.2.2.1 i a b).1,
      field_sum c K S x p hm hd _ fun a b => (hd.2.2.2.2.2.1 i a b).2⟩⟩
  have hF : ∀ n, Summable (fun n' => fullPair c x n n' p) := fun n =>
    slice_right c x p hm hd n (fun a b => gradMode c.order n x.2.1 a b p) (modeVec c.order n x.1 p.1 p.2)
  have hL : ∀ n, Summable (fun n' => lowFullPair c K S x n n' p) := fun n =>
    slice_right c x p hm hd n (lowGrad c K S x n p) (lowVel c K S x n p)
  have hS0 : ∀ n, ∀ n' ∉ S.resolved, sharpLowTerm c K S x n n' p = 0 := by
    intro n n' hn'
    unfold sharpLowTerm pairWave
    rw [(low_out c K S x hn' p).1, (low_out c K S x hn' p).2]
    exact wave_zero_right _ _ _ _ _
  have e : ∀ n, ∑' n', sharpPair c K S x n n' p = ∑' n', fullPair c x n n' p - ∑' n', lowFullPair c K S x n n' p
      - ∑ n' ∈ S.resolved, sharpLowTerm c K S x n n' p := by
    intro n
    refine HasSum.tsum_eq ?_
    have H := ((hF n).hasSum.sub (hL n).hasSum).sub (hasSum_sum_of_ne_finset_zero (hS0 n))
    rw [show (fun n' => sharpPair c K S x n n' p) = fun n' => fullPair c x n n' p - lowFullPair c K S x n n' p
      - sharpLowTerm c K S x n n' p from funext fun n' => sharp_split c K S x n n' p]
    exact H
  have hB : Summable (fun n : ℤ => ∑' n', lowFullPair c K S x n n' p) := by
    refine summable_of_ne_finset_zero (s := S.resolved) fun n hn => ?_
    have h0 : ∀ n', lowFullPair c K S x n n' p = 0 := by
      intro n'
      unfold lowFullPair pairWave
      rw [(low_out c K S x hn p).1, (low_out c K S x hn p).2]
      exact wave_zero_left _ _ _ _ _
    simp only [h0, tsum_zero]
  have hC : Summable (fun n : ℤ => ∑ n' ∈ S.resolved, sharpLowTerm c K S x n n' p) :=
    summable_sum fun n' _ => sharp_left c K S x p hm hd n' (lowGrad c K S x n' p) (lowVel c K S x n' p)
  exact (((full_outer c x p hm hd).sub hB).sub hC).congr fun n => (e n).symm

end Concrete

section Slice

open Breakdown.CellCert.CellAnalysis.LowEntry.Internal
open Breakdown.FracInternal.CircleSliceRegular Breakdown.FracInternal.CellDensityModesSolid

theorem slice_avg_int {f : Space → ℝ} (hf : Integrable f) {K : CellBox} (hK : IsCellBox K) :
    IntegrableOn (fun p : ℝ × ℝ => ∫ θ in Set.Ioo (-π) π, p.1 * f (cylPoint p.1 θ p.2)) K.rect := by
  have hpos : ∀ᵐ q ∂muU, 0 < q.1.1 := by
    rw [muU_eq]
    exact ae_restrict_of_forall_mem ((measurableSet_Ioi.prod MeasurableSet.univ).prod measurableSet_Ioo)
      fun q hq => hq.1.1
  have hF : Integrable (fun q : (ℝ × ℝ) × ℝ => q.1.1 * f (cylArg q)) muU := by
    refine ⟨(continuous_fst.comp continuous_fst).aestronglyMeasurable.mul
      (hf.1.comp_quasiMeasurePreserving qmp), ?_⟩
    have e : ∫⁻ q, ‖q.1.1 * f (cylArg q)‖ₑ ∂muU = ∫⁻ q, ENNReal.ofReal q.1.1 * ‖f (cylArg q)‖ₑ ∂muU :=
      lintegral_congr_ae (hpos.mono fun q hq => by dsimp only; rw [enorm_mul, Real.enorm_eq_ofReal hq.le])
    show ∫⁻ q, ‖q.1.1 * f (cylArg q)‖ₑ ∂muU < ⊤
    rw [e, key (fun y => ‖f y‖ₑ)]
    exact hf.2
  rw [muU_def] at hF
  have h2 := hF.integral_prod_left
  refine IntegrableOn.of_forall_sdiff_eq_zero h2 (measurableSet_Icc.prod measurableSet_Icc) fun p hp => ?_
  have h0 : p.1 = 0 :=
    le_antisymm (not_lt.1 fun h => hp.2 ⟨h, Set.mem_univ _⟩) (hK.r_order.1.trans hp.1.1.1)
  simp [h0]

theorem coupling_int (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4) {k N : ℕ} (c : FracCellData k N)
    (hc : IsFormData α c) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
    (R : CellRows N slots k) (hd : IsCellData α c K S B Cl R) (hax : IsAxisymmetricWeight c K)
    (x : FieldTuple k) (hx : IsAdmissible c x) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * modeCoupling c x p) K.rect := by
  have hm : 3 ≤ c.order := hc.base.order_ge
  have hK := hd.box
  have hf : Integrable (K.solid.indicator
      (fun y => jForm (c.modelStrain y) (c.modelCurlGrad y) (x.2.1 y) (x.1 y))) :=
    (integrable_indicator_iff (solid_closed K)).2 (jFormIntegrable α hα₁ hα₂ c hc K hK x hx)
  have hI := (slice_avg_int hf hK).const_mul (2 * π)⁻¹
  have hreg := circleSliceRegular_holds α hα₁ hα₂ c hc K hK hax hd.model_mirror hd.solid_in_region x hx
  refine hI.congr ?_
  filter_upwards [hreg, ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp hmem
  have hin : ∀ θ, K.solid.indicator (fun y => jForm (c.modelStrain y) (c.modelCurlGrad y) (x.2.1 y) (x.1 y))
      (cylPoint p.1 θ p.2) = jForm (c.modelStrain (cylPoint p.1 θ p.2)) (c.modelCurlGrad (cylPoint p.1 θ p.2))
        (x.2.1 (cylPoint p.1 θ p.2)) (x.1 (cylPoint p.1 θ p.2)) :=
    fun θ => Set.indicator_of_mem (cyl_solid hK hmem θ) _
  have hJc := circleSliceCoupling_holds c hm x p hp
  have hper : Function.Periodic (fun θ => jForm (c.modelStrain (cylPoint p.1 θ p.2))
      (c.modelCurlGrad (cylPoint p.1 θ p.2)) (x.2.1 (cylPoint p.1 θ p.2)) (x.1 (cylPoint p.1 θ p.2))) (2 * π) :=
    fun θ => by simp only [cyl_per]
  have e1 := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at e1
  have e2 : ∫ θ in Set.Ioo (-π) π, p.1 * K.solid.indicator
      (fun y => jForm (c.modelStrain y) (c.modelCurlGrad y) (x.2.1 y) (x.1 y)) (cylPoint p.1 θ p.2) =
      p.1 * ∫ θ in (-π)..π, jForm (c.modelStrain (cylPoint p.1 θ p.2)) (c.modelCurlGrad (cylPoint p.1 θ p.2))
        (x.2.1 (cylPoint p.1 θ p.2)) (x.1 (cylPoint p.1 θ p.2)) := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), ← integral_Ioc_eq_integral_Ioo,
      ← integral_const_mul]
    simp only [hin]
  show (2 * π)⁻¹ * ∫ θ in Set.Ioo (-π) π, p.1 * K.solid.indicator
      (fun y => jForm (c.modelStrain y) (c.modelCurlGrad y) (x.2.1 y) (x.1 y)) (cylPoint p.1 θ p.2) =
    p.1 * modeCoupling c x p
  rw [e2, e1, hJc.2, mul_left_comm, inv_mul_cancel_left₀ (by positivity : (2 * π) ≠ 0)]

end Slice

end Breakdown.CellCert.CellAnalysis.SharpMxModeWaveRegular.Internal

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly SharpParts ModeExpansionParts
open Breakdown.CellCert.CellAnalysis.SharpMxModeWaveRegular.Internal

def ModeWaveCrossStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      ∀ n ∈ S.resolved, Summable (fun n' : ℤ => ∫ p in K.rect, ‖p.1 * (crossPair c K S x n n' p).re‖)

def ModeWaveTotalStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      IntegrableOn (fun p : ℝ × ℝ => p.1 * (∑' n, ∑' n', sharpPair c K S x n n' p).re) K.rect

theorem modeWavePointwise_holds (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4) {k N : ℕ} (c : FracCellData k N)
    (hc : IsFormData α c) (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
    (R : CellRows N slots k) (hd : IsCellData α c K S B Cl R) (hax : IsAxisymmetricWeight c K)
    (x : FieldTuple k) (hx : IsAdmissible c x) :
    ∀ᵐ p ∂(volume.restrict K.rect),
      (∀ n, Summable (fun n' => sharpPair c K S x n n' p)) ∧
      Summable (fun n => ∑' n', sharpPair c K S x n n' p) ∧
      (∀ n ∈ S.resolved, Summable (fun n' => lowSharpPair c K S x n n' p) ∧
        Summable (fun n' => sharpLowPair c K S x n' n p)) ∧
      (∀ i, Summable (fun n => fieldSharp c K S x (c.modelActuatorGrad i) n p) ∧
        Summable (fun n => fieldSharp c K S x (c.modelPinField i) n p)) := by
  have hm : 0 < c.order := by
    have := hc.base.order_ge
    omega
  have hreg := circleSliceRegular_holds α hα₁ hα₂ c hc K hd.box hax hd.model_mirror hd.solid_in_region x hx
  exact hreg.mono fun p hp => pointwise c K S x p hm hp

theorem modeWaveRegular_of (hX : ModeWaveCrossStatement) (hT : ModeWaveTotalStatement) :
    ModeWaveRegularStatement := by
  intro α hα₁ hα₂ k N c hc K S B Cl slots R hd hax x hx
  exact ⟨modeWavePointwise_holds α hα₁ hα₂ c hc K S B Cl R hd hax x hx,
    hX α hα₁ hα₂ c hc K S B Cl R hd hax x hx, hT α hα₁ hα₂ c hc K S B Cl R hd hax x hx⟩


open SharpYModeExpansion.Internal SharpModeExpansionRegular.Internal in
theorem modeWaveTotal_of (hX : ModeWaveCrossStatement) : ModeWaveTotalStatement := by
  intro α hα₁ hα₂ k N c hc K S B Cl slots R hd hax x hx
  have hK := hd.box
  have hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1 := hx.1
  have hpt := modeWavePointwise_holds α hα₁ hα₂ c hc K S B Cl R hd hax x hx
  have hMC := coupling_int α hα₁ hα₂ c hc K S B Cl R hd hax x hx
  have hLL : Integrable (fun p : ℝ × ℝ => ∑ n ∈ S.resolved, ∑ n' ∈ S.resolved, p.1 * (lowLowPair c K S x n n' p).re)
      (volume.restrict K.rect) :=
    integrable_finsetSum _ fun n _ => integrable_finsetSum _ fun n' _ =>
      re_integrable K (lowLow_int c K S x α hc hK n n')
  have hXt : Integrable (fun p : ℝ × ℝ => ∑ n ∈ S.resolved, p.1 * (∑' n', crossPair c K S x n n' p).re)
      (volume.restrict K.rect) := by
    refine integrable_finsetSum _ fun n hn => ?_
    refine re_tsum_int (fun n' => wt_re K (cross_wt c K S x α hc hK hs n n'))
      (hX α hα₁ hα₂ c hc K S B Cl R hd hax x hx n hn) ?_
    filter_upwards [hpt] with p hp
    exact (hp.2.2.1 n hn).1.add (hp.2.2.1 n hn).2
  refine ((hMC.sub hLL).sub hXt).congr ?_
  filter_upwards [hpt] with p hp
  simp only [Pi.sub_apply]
  rw [coupling_split c K S x p hp.1 hp.2.1 hp.2.2.1]
  simp only [Complex.add_re, Complex.re_sum, mul_add, Finset.mul_sum]
  ring

theorem modeWaveRegular_of_cross (hX : ModeWaveCrossStatement) : ModeWaveRegularStatement :=
  modeWaveRegular_of hX (modeWaveTotal_of hX)

end Breakdown.CellCert.CellAnalysis
