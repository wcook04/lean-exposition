import Breakdown.CertCell.BridgeStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal.ModeTermFlip

open PieceWeights

theorem flipPoint_coord (y : Space) (i : Fin 3) : flipPoint y i = frameSign i * y i := by
  fin_cases i <;> simp [flipPoint, unitVector, frameSign]

theorem frameSign_mul_self (i : Fin 3) : frameSign i * frameSign i = 1 := by
  fin_cases i <;> simp [frameSign]

theorem abs_frameSign (i : Fin 3) : |frameSign i| = 1 := by
  fin_cases i <;> simp [frameSign]

theorem flipPoint_flipPoint (y : Space) : flipPoint (flipPoint y) = y := by
  ext i
  rw [flipPoint_coord, flipPoint_coord, ← mul_assoc, frameSign_mul_self, one_mul]

def flipLinearMap : Space →ₗ[ℝ] Space where
  toFun := flipPoint
  map_add' x z := by
    ext i
    simp only [flipPoint_coord, PiLp.add_apply]
    ring
  map_smul' c x := by
    ext i
    simp only [flipPoint_coord, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem norm_flipPoint (y : Space) : ‖flipPoint y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [flipPoint_coord, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_frameSign, one_mul]

def flipIsometryEquiv : Space ≃ₗᵢ[ℝ] Space where
  toLinearEquiv := LinearEquiv.ofInvolutive flipLinearMap flipPoint_flipPoint
  norm_map' := norm_flipPoint

theorem flipIsometryEquiv_apply (y : Space) : flipIsometryEquiv y = flipPoint y := rfl

theorem comp_flip_eq {f g : Space → ℝ} (hfg : ∀ y, f (flipPoint y) = g y) : g = f ∘ flipIsometryEquiv := by
  funext z
  exact (hfg z).symm

theorem secondDerivNorm_flip {f g : Space → ℝ} (hfg : ∀ y, f (flipPoint y) = g y) (y : Space) :
    ModeWeights.secondDerivNorm f (flipPoint y) = ModeWeights.secondDerivNorm g y := by
  rw [comp_flip_eq hfg]
  unfold ModeWeights.secondDerivNorm
  rw [LinearIsometryEquiv.norm_iteratedFDeriv_comp_right]
  rfl

theorem wtGrad_flip {f g : Space → ℝ} (hfg : ∀ y, f (flipPoint y) = g y) (y : Space) :
    wtGrad f (flipPoint y) = wtGrad g y := by
  rw [comp_flip_eq hfg]
  unfold wtGrad
  rw [← norm_iteratedFDeriv_one, ← norm_iteratedFDeriv_one,
    LinearIsometryEquiv.norm_iteratedFDeriv_comp_right]
  rfl

theorem flipLabel_flipLabel (ι : ℤ × ℤ) : flipLabel (flipLabel ι) = ι := by
  simp [flipLabel]

theorem flipLabel_neg (ι : ℤ × ℤ) : flipLabel (-ι) = -flipLabel ι := by
  simp [flipLabel]

theorem flipLabel_add (ι β : ℤ × ℤ) : flipLabel (ι + β) = flipLabel ι + flipLabel β := by
  ext <;> simp [flipLabel]
  ring

theorem flipLabel_sub (ι β : ℤ × ℤ) : flipLabel (ι - β) = flipLabel ι - flipLabel β := by
  ext <;> simp [flipLabel]
  ring

theorem flipLabel_injective : Function.Injective flipLabel :=
  Function.LeftInverse.injective flipLabel_flipLabel

theorem mem_flip_image {T : Set (ℤ × ℤ)} {ι : ℤ × ℤ} : flipLabel ι ∈ flipLabel '' T ↔ ι ∈ T :=
  flipLabel_injective.mem_set_image

theorem inPiece_flip {T : Set (ℤ × ℤ)} {ι : ℤ × ℤ} :
    inPiece (flipLabel '' T) (flipLabel ι) ↔ inPiece T ι := by
  unfold inPiece
  rw [← flipLabel_neg, mem_flip_image, mem_flip_image]

theorem frameFreq_flip (P a : ℝ) (ι : ℤ × ℤ) : frameFreq P (-a) (flipLabel ι) = frameFreq P a ι := by
  simp only [frameFreq, flipLabel, Int.cast_neg]
  ring

theorem backSum_flip (h : HarmonicBounds) (hH : ∀ β ∈ h.harmonics, flipLabel β ∈ h.harmonics)
    {T : Set (ℤ × ℤ)} {amp : ℤ × ℤ → Space → ℝ} (hamp : ∀ β y, amp (flipLabel β) (flipPoint y) = amp β y)
    (ι : ℤ × ℤ) (y : Space) :
    backSum h (flipLabel '' T) amp (flipLabel ι) (flipPoint y) = backSum h T amp ι y := by
  unfold backSum
  refine (Finset.sum_nbij' flipLabel flipLabel hH hH (fun β _ => flipLabel_flipLabel β)
    (fun β _ => flipLabel_flipLabel β) fun β _ => ?_).symm
  rw [← flipLabel_sub, mem_flip_image, hamp]

theorem fwdSum_flip (h : HarmonicBounds) (hH : ∀ β ∈ h.harmonics, flipLabel β ∈ h.harmonics)
    {T : Set (ℤ × ℤ)} {amp : ℤ × ℤ → Space → ℝ} (hamp : ∀ β y, amp (flipLabel β) (flipPoint y) = amp β y)
    (ι : ℤ × ℤ) (y : Space) :
    fwdSum h (flipLabel '' T) amp (flipLabel ι) (flipPoint y) = fwdSum h T amp ι y := by
  unfold fwdSum
  refine (Finset.sum_nbij' flipLabel flipLabel hH hH (fun β _ => flipLabel_flipLabel β)
    (fun β _ => flipLabel_flipLabel β) fun β _ => ?_).symm
  rw [← flipLabel_add, mem_flip_image, hamp]

theorem inward_flip (h : HarmonicBounds) (hH : ∀ β ∈ h.harmonics, flipLabel β ∈ h.harmonics)
    {T : Set (ℤ × ℤ)} {amp : ℤ × ℤ → Space → ℝ} (hamp : ∀ β y, amp (flipLabel β) (flipPoint y) = amp β y)
    (ι : ℤ × ℤ) (y : Space) :
    inward h (flipLabel '' T) amp (flipLabel ι) (flipPoint y) = inward h T amp ι y := by
  unfold inward
  rw [← flipLabel_neg, mem_flip_image, mem_flip_image, backSum_flip h hH hamp,
    backSum_flip h hH hamp]

theorem outward_flip (h : HarmonicBounds) (hH : ∀ β ∈ h.harmonics, flipLabel β ∈ h.harmonics)
    {T : Set (ℤ × ℤ)} {amp : ℤ × ℤ → Space → ℝ} (hamp : ∀ β y, amp (flipLabel β) (flipPoint y) = amp β y)
    (ι : ℤ × ℤ) (y : Space) :
    outward h (flipLabel '' T) amp (flipLabel ι) (flipPoint y) = outward h T amp ι y := by
  unfold outward
  rw [← flipLabel_neg, mem_flip_image, mem_flip_image, fwdSum_flip h hH hamp,
    fwdSum_flip h hH hamp]

theorem harmonicSum_flip (h : HarmonicBounds) (hH : ∀ β ∈ h.harmonics, flipLabel β ∈ h.harmonics)
    (hamp : ∀ β y, h.ampGradW (flipLabel β) (flipPoint y) = h.ampGradW β y) (y : Space) :
    harmonicSum h (flipPoint y) = harmonicSum h y := by
  unfold harmonicSum
  refine (Finset.sum_nbij' flipLabel flipLabel hH hH (fun β _ => flipLabel_flipLabel β)
    (fun β _ => flipLabel_flipLabel β) fun β _ => ?_).symm
  rw [hamp]

theorem cnormSq_sign_mul {β : Type*} [Fintype β] (s : β → ℝ) (hs : ∀ b, |s b| = 1) (x : β → ℂ) :
    cnormSq (fun b => ((s b : ℝ) : ℂ) * x b) = cnormSq x := by
  unfold cnormSq
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hs, one_mul]

theorem curlOfGrad_sign (g : Fin 3 × Fin 3 → ℂ) :
    curlOfGrad (fun ab => ((frameSign ab.1 * frameSign ab.2 : ℝ) : ℂ) * g ab)
      = fun i => ((frameSign i : ℝ) : ℂ) * curlOfGrad g i := by
  funext i
  fin_cases i <;>
    simp [curlOfGrad, Fin.sum_univ_three, alternatingSymbol, frameSign] <;> ring

theorem curlGradOfSecondDeriv_sign (hs : Fin 3 × Fin 3 × Fin 3 → ℂ) :
    curlGradOfSecondDeriv (fun abc => ((frameSign abc.1 * frameSign abc.2.1 * frameSign abc.2.2 : ℝ) : ℂ) * hs abc)
      = fun jl => ((frameSign jl.1 * frameSign jl.2 : ℝ) : ℂ) * curlGradOfSecondDeriv hs jl := by
  funext jl
  obtain ⟨j, l⟩ := jl
  fin_cases j <;> fin_cases l <;>
    simp [curlGradOfSecondDeriv, Fin.sum_univ_three, alternatingSymbol, frameSign] <;> ring


variable {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {h : HarmonicBounds} {w : Space → ℝ}

theorem shareHat_flip (hc : IsFlipCompatible m h w) (ξ : ℤ × ℤ) (y : Space) (hy : y 2 ≠ 0) :
    m.shareHat h (flipLabel ξ) (flipPoint y) = m.shareHat h ξ y := by
  obtain ⟨π, hπ⟩ := hc.eps_mirror
  have hampW : ∀ β y, h.ampW (flipLabel β) (flipPoint y) = h.ampW β y := fun β y => (hc.amplitudes_flip β y).1
  unfold shareHat
  refine (Equiv.sum_comp π _).symm.trans (Finset.sum_congr rfl fun β _ => ?_)
  obtain ⟨hmo, -, hpt⟩ := hπ β
  obtain ⟨hwt, -, hrest⟩ := hpt y
  obtain ⟨hs1, hs2, -, -, -, -, -, hsc⟩ := hrest hy
  have hwf : ∀ z, (m.epsP (π β)).wt (flipPoint z) = (m.epsP β).wt z := fun z => (hpt z).1
  rw [wtGrad_flip hwf, hs1, hs2, hsc, hwt, hmo, outward_flip h hc.harmonics_flip hampW]
  simp only [inPiece_flip]

theorem coefA_flip (hc : IsFlipCompatible m h w) (P : ℝ) (ξ : ℤ × ℤ) (y : Space) (hy : y 2 ≠ 0) :
    m.coefA P h (flipLabel ξ) (flipPoint y) = m.coefA P h ξ y := by
  obtain ⟨π, hπ⟩ := hc.eps_mirror
  have hH := hc.harmonics_flip
  have hampW : ∀ β y, h.ampW (flipLabel β) (flipPoint y) = h.ampW β y := fun β y => (hc.amplitudes_flip β y).1
  have hampGW : ∀ β y, h.ampGradW (flipLabel β) (flipPoint y) = h.ampGradW β y :=
    fun β y => (hc.amplitudes_flip β y).2.1
  have hampV : ∀ β y, h.ampVort (flipLabel β) (flipPoint y) = h.ampVort β y :=
    fun β y => (hc.amplitudes_flip β y).2.2.1
  have hampGV : ∀ β y, h.ampGradVort (flipLabel β) (flipPoint y) = h.ampGradVort β y :=
    fun β y => (hc.amplitudes_flip β y).2.2.2
  obtain ⟨hsv, hsgv⟩ := hc.sups_flip y
  unfold coefA
  congr 1
  · congr 1
    refine (Equiv.sum_comp π _).symm.trans (Finset.sum_congr rfl fun β _ => ?_)
    obtain ⟨hmo, hfr, hpt⟩ := hπ β
    obtain ⟨hwt, hsp, hrest⟩ := hpt y
    obtain ⟨hs1, hs2, hlen, ht0, ht1, ht2, ht3, hsc⟩ := hrest hy
    have hwf : ∀ z, (m.epsP (π β)).wt (flipPoint z) = (m.epsP β).wt z := fun z => (hpt z).1
    rw [wtGrad_flip hwf, hs1, hs2, hsc, hwt, hsp, hlen, ht0, ht1, ht2, ht3, hsv, hsgv, hmo, hfr,
      frameFreq_flip, abs_neg, inward_flip h hH hampW, inward_flip h hH hampGW, inward_flip h hH hampV,
      inward_flip h hH hampGV]
    simp only [inPiece_flip]
  · refine (Equiv.sum_comp π _).symm.trans (Finset.sum_congr rfl fun β _ => ?_)
    obtain ⟨hmo, -, hpt⟩ := hπ β
    obtain ⟨hwt, -, hrest⟩ := hpt y
    obtain ⟨-, -, -, -, ht1, -, -, -⟩ := hrest hy
    rw [hwt, ht1, hmo, outward_flip h hH hampGW]

theorem coefAA_flip (hc : IsFlipCompatible m h w) (ξ : ℤ × ℤ) (y : Space) (hy : y 2 ≠ 0) :
    m.coefAA h w (flipLabel ξ) (flipPoint y) = m.coefAA h w ξ y := by
  obtain ⟨π, hπ⟩ := hc.eps_mirror
  obtain ⟨ρ, hρ⟩ := hc.mu_mirror
  have hH := hc.harmonics_flip
  have hampW : ∀ β y, h.ampW (flipLabel β) (flipPoint y) = h.ampW β y := fun β y => (hc.amplitudes_flip β y).1
  have hampV : ∀ β y, h.ampVort (flipLabel β) (flipPoint y) = h.ampVort β y :=
    fun β y => (hc.amplitudes_flip β y).2.2.1
  obtain ⟨hsv, -⟩ := hc.sups_flip y
  unfold coefAA
  rw [hc.vorticity_flip, secondDerivNorm_flip (hc.strain_flip ξ), hc.weight_flip]
  congr 1
  · congr 1
    refine (Equiv.sum_comp π _).symm.trans (Finset.sum_congr rfl fun β _ => ?_)
    obtain ⟨hmo, -, hpt⟩ := hπ β
    obtain ⟨hwt, -, hrest⟩ := hpt y
    obtain ⟨-, -, -, ht0, -, -, ht3, -⟩ := hrest hy
    rw [hwt, ht0, ht3, hsv, hmo, outward_flip h hH hampV]
    simp only [inPiece_flip]
  · refine (Equiv.sum_comp ρ _).symm.trans (Finset.sum_congr rfl fun β _ => ?_)
    obtain ⟨hmo, -, -, hpt⟩ := hρ β
    obtain ⟨hwt, -, hrest⟩ := hpt y
    obtain ⟨hsh, ht4⟩ := hrest hy
    have hwf : ∀ z, (m.muP (ρ β)).wt (flipPoint z) = (m.muP β).wt z := fun z => (hpt z).1
    rw [wtGrad_flip hwf, hwt, hsh, ht4, hmo, outward_flip h hH hampW]
    simp only [inPiece_flip]

theorem coefB_flip (hc : IsFlipCompatible m h w) (P : ℝ) (ξ : ℤ × ℤ) (y : Space) (hy : y 2 ≠ 0) :
    m.coefB P h (flipLabel ξ) (flipPoint y) = m.coefB P h ξ y := by
  obtain ⟨π, hπ⟩ := hc.eps_mirror
  obtain ⟨ρ, hρ⟩ := hc.mu_mirror
  have hH := hc.harmonics_flip
  have hampW : ∀ β y, h.ampW (flipLabel β) (flipPoint y) = h.ampW β y := fun β y => (hc.amplitudes_flip β y).1
  have hampGW : ∀ β y, h.ampGradW (flipLabel β) (flipPoint y) = h.ampGradW β y :=
    fun β y => (hc.amplitudes_flip β y).2.1
  have hampGV : ∀ β y, h.ampGradVort (flipLabel β) (flipPoint y) = h.ampGradVort β y :=
    fun β y => (hc.amplitudes_flip β y).2.2.2
  obtain ⟨-, hsgv⟩ := hc.sups_flip y
  have hhs := harmonicSum_flip h hH hampGW y
  unfold coefB
  rw [secondDerivNorm_flip (hc.vorticity_flip ξ)]
  congr 1
  · congr 1
    · congr 1
      refine (Equiv.sum_comp π _).symm.trans (Finset.sum_congr rfl fun β _ => ?_)
      obtain ⟨hmo, -, hpt⟩ := hπ β
      obtain ⟨hwt, -, hrest⟩ := hpt y
      obtain ⟨-, -, hlen, -, -, ht2, -, -⟩ := hrest hy
      rw [hwt, hlen, ht2, hsgv, hmo, outward_flip h hH hampGV]
      simp only [inPiece_flip]
    · refine (Equiv.sum_comp ρ _).symm.trans (Finset.sum_congr rfl fun β _ => ?_)
      obtain ⟨hmo, hfr, het, hpt⟩ := hρ β
      obtain ⟨hwt, hsp, hrest⟩ := hpt y
      obtain ⟨hsh, ht4⟩ := hrest hy
      have hwf : ∀ z, (m.muP (ρ β)).wt (flipPoint z) = (m.muP β).wt z := fun z => (hpt z).1
      rw [wtGrad_flip hwf, hwt, hsp, hsh, ht4, het, hhs, hmo, hfr, frameFreq_flip, abs_neg,
        inward_flip h hH hampW, inward_flip h hH hampGW]
      simp only [inPiece_flip]
  · refine (Equiv.sum_comp ρ _).symm.trans (Finset.sum_congr rfl fun β _ => ?_)
    obtain ⟨hmo, -, het, -⟩ := hρ β
    rw [het, hhs, hmo, outward_flip h hH hampGW]

end Internal.ModeTermFlip

open Internal.ModeTermFlip in
theorem modeTermFlip : ModeTermFlipHolds := by
  intro C nE nM m P h w hc v G H ξ σ y hy hV hG hHs
  unfold PieceWeights.modeTerm PieceWeights.modeDensity
  rw [hV, hG, hHs, curlOfGrad_sign, curlGradOfSecondDeriv_sign,
    cnormSq_sign_mul (fun a => frameSign a) abs_frameSign,
    cnormSq_sign_mul (fun a => frameSign a) abs_frameSign,
    cnormSq_sign_mul (fun ab : Fin 3 × Fin 3 => frameSign ab.1 * frameSign ab.2)
      (fun ab => by rw [abs_mul, abs_frameSign, abs_frameSign, one_mul]),
    cnormSq_sign_mul (fun ab : Fin 3 × Fin 3 => frameSign ab.1 * frameSign ab.2)
      (fun ab => by rw [abs_mul, abs_frameSign, abs_frameSign, one_mul]),
    cnormSq_sign_mul (fun abc : Fin 3 × Fin 3 × Fin 3 => frameSign abc.1 * frameSign abc.2.1 * frameSign abc.2.2)
      (fun abc => by rw [abs_mul, abs_mul, abs_frameSign, abs_frameSign, abs_frameSign, one_mul, one_mul]),
    shareHat_flip hc ξ y hy, coefA_flip hc P ξ y hy, coefAA_flip hc ξ y hy, coefB_flip hc P ξ y hy,
    hc.strain_flip, hc.vorticity_flip]

end Bridge

end CertCell

end Breakdown
