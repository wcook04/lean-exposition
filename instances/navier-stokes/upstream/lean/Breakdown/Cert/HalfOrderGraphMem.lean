import Breakdown.Cert.Basic

open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown.Cert

open Freq

namespace HalfOrderGraph.Internal

def halfSspSubmodule : Submodule ℝ (WithLp 2 (Freq.X × Freq.X)) where
  carrier := {q | IsHalfSspOf (WithLp.fst q) (WithLp.snd q)}
  zero_mem' := by
    show ∀ᵐ ξ ∂volume, ((0 : L2C) : Space → CSpace) ξ =
      (2 * Real.pi * ‖ξ‖) • ((0 : L2C) : Space → CSpace) ξ
    filter_upwards [Lp.coeFn_zero (E := CSpace) (p := 2) (μ := (volume : Measure Space))] with ξ h
    rw [h, Pi.zero_apply, smul_zero]
  add_mem' := by
    intro a b ha hb
    show ∀ᵐ ξ ∂volume, ((WithLp.snd (a + b) : Freq.X) : L2C) ξ =
      (2 * Real.pi * ‖ξ‖) • ((WithLp.fst (a + b) : Freq.X) : L2C) ξ
    have ha' : IsHalfSspOf (WithLp.fst a) (WithLp.snd a) := ha
    have hb' : IsHalfSspOf (WithLp.fst b) (WithLp.snd b) := hb
    simp only [WithLp.add_fst, WithLp.add_snd, Submodule.coe_add]
    filter_upwards [ha', hb', Lp.coeFn_add ((WithLp.snd a : Freq.X) : L2C) (WithLp.snd b : Freq.X),
      Lp.coeFn_add ((WithLp.fst a : Freq.X) : L2C) (WithLp.fst b : Freq.X)] with ξ h1 h2 h3 h4
    rw [h3, h4, Pi.add_apply, Pi.add_apply, h1, h2, smul_add]
  smul_mem' := by
    intro c a ha
    show ∀ᵐ ξ ∂volume, ((WithLp.snd (c • a) : Freq.X) : L2C) ξ =
      (2 * Real.pi * ‖ξ‖) • ((WithLp.fst (c • a) : Freq.X) : L2C) ξ
    have ha' : IsHalfSspOf (WithLp.fst a) (WithLp.snd a) := ha
    simp only [WithLp.smul_fst, WithLp.smul_snd, Submodule.coe_smul]
    filter_upwards [ha', Lp.coeFn_smul c ((WithLp.snd a : Freq.X) : L2C),
      Lp.coeFn_smul c ((WithLp.fst a : Freq.X) : L2C)] with ξ h1 h2 h3
    rw [h2, h3, Pi.smul_apply, Pi.smul_apply, h1, smul_comm]

theorem mem_halfSspSubmodule (q : WithLp 2 (Freq.X × Freq.X)) :
    q ∈ halfSspSubmodule ↔ IsHalfSspOf (WithLp.fst q) (WithLp.snd q) := Iff.rfl

theorem tendsto_fst_coe {q : ℕ → WithLp 2 (Freq.X × Freq.X)} {q₀ : WithLp 2 (Freq.X × Freq.X)}
    (h : Tendsto q atTop (𝓝 q₀)) :
    Tendsto (fun n => ((WithLp.fst (q n) : Freq.X) : L2C)) atTop (𝓝 ((WithLp.fst q₀ : Freq.X) : L2C)) :=
  ((Sig.subtypeL.comp (WithLp.fstL 2 ℝ Freq.X Freq.X)).continuous.tendsto q₀).comp h

theorem tendsto_snd_coe {q : ℕ → WithLp 2 (Freq.X × Freq.X)} {q₀ : WithLp 2 (Freq.X × Freq.X)}
    (h : Tendsto q atTop (𝓝 q₀)) :
    Tendsto (fun n => ((WithLp.snd (q n) : Freq.X) : L2C)) atTop (𝓝 ((WithLp.snd q₀ : Freq.X) : L2C)) :=
  ((Sig.subtypeL.comp (WithLp.sndL 2 ℝ Freq.X Freq.X)).continuous.tendsto q₀).comp h

theorem isClosed_halfSspSubmodule :
    IsClosed (halfSspSubmodule : Set (WithLp 2 (Freq.X × Freq.X))) := by
  refine IsSeqClosed.isClosed fun q q₀ hq hlim => ?_
  have hq' : ∀ n, ∀ᵐ ξ ∂volume, ((WithLp.snd (q n) : Freq.X) : L2C) ξ =
      (2 * Real.pi * ‖ξ‖) • ((WithLp.fst (q n) : Freq.X) : L2C) ξ := fun n => hq n
  obtain ⟨φ, hφm, hφ⟩ := (tendstoInMeasure_of_tendsto_Lp (tendsto_fst_coe hlim)).exists_seq_tendsto_ae
  obtain ⟨ψ, hψm, hψ⟩ := (tendstoInMeasure_of_tendsto_Lp
    (tendsto_snd_coe (hlim.comp hφm.tendsto_atTop))).exists_seq_tendsto_ae
  show ∀ᵐ ξ ∂volume, ((WithLp.snd q₀ : Freq.X) : L2C) ξ =
    (2 * Real.pi * ‖ξ‖) • ((WithLp.fst q₀ : Freq.X) : L2C) ξ
  filter_upwards [ae_all_iff.mpr hq', hφ, hψ] with ξ hall hx hk
  have hx' : Tendsto (fun i => ((WithLp.fst (q (φ (ψ i))) : Freq.X) : L2C) ξ) atTop
      (𝓝 (((WithLp.fst q₀ : Freq.X) : L2C) ξ)) := hx.comp hψm.tendsto_atTop
  refine tendsto_nhds_unique hk ?_
  have heq : (fun i => ((WithLp.snd ((q ∘ φ) (ψ i)) : Freq.X) : L2C) ξ) =
      fun i => (2 * Real.pi * ‖ξ‖) • ((WithLp.fst (q (φ (ψ i))) : Freq.X) : L2C) ξ :=
    funext fun i => hall (φ (ψ i))
  rw [heq]
  exact hx'.const_smul _

theorem halfOrderGraph_eq_halfSspSubmodule : halfOrderGraph = halfSspSubmodule := by
  unfold halfOrderGraph
  rw [show {q : WithLp 2 (Freq.X × Freq.X) | IsHalfSspOf (WithLp.fst q) (WithLp.snd q)} =
      (halfSspSubmodule : Set (WithLp 2 (Freq.X × Freq.X))) from rfl, Submodule.span_eq,
    isClosed_halfSspSubmodule.submodule_topologicalClosure_eq]

end HalfOrderGraph.Internal

open HalfOrderGraph.Internal

theorem mem_halfOrderGraph_iff (q : WithLp 2 (Freq.X × Freq.X)) :
    q ∈ halfOrderGraph ↔ Freq.IsHalfSspOf (WithLp.fst q) (WithLp.snd q) := by
  rw [halfOrderGraph_eq_halfSspSubmodule]
  exact mem_halfSspSubmodule q

theorem halfSsp_of_xbar (q : XBar) : Freq.IsHalfSspOf (gradPart q) (secondPart q) :=
  (mem_halfOrderGraph_iff (q : WithLp 2 (Freq.X × Freq.X))).1 q.2

theorem exists_xbar_of_halfSsp (x k : Freq.X) (h : Freq.IsHalfSspOf x k) :
    ∃ q : XBar, gradPart q = x ∧ secondPart q = k :=
  ⟨⟨WithLp.toLp 2 (x, k), (mem_halfOrderGraph_iff (WithLp.toLp 2 (x, k))).2 h⟩, rfl, rfl⟩

theorem norm_xbar_sq (q : XBar) : ‖q‖ ^ 2 = ‖gradPart q‖ ^ 2 + ‖secondPart q‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 (q : WithLp 2 (Freq.X × Freq.X))

theorem halfSsp_unique (x k k' : Freq.X) (h : Freq.IsHalfSspOf x k) (h' : Freq.IsHalfSspOf x k') :
    k = k' := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [h, h'] with ξ h1 h2
  rw [h1, h2]

end Breakdown.Cert
