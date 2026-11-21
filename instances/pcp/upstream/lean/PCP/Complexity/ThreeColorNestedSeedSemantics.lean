import PCP.Complexity.ThreeColorNestedSeedRadices

/-! # Exact ordered component codes produced by the nested seed programs -/

namespace PCP.Lang.NestedSeed

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {t : ℕ}
variable (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))

theorem outer_run {σ : Type*} (σc : Codec σ) (n m c : ℕ) (cubic : Bool)
    (hn : σc.size = n)
    (s : EncodedLineLowDegreeTest.Sample F σ m c t (if cubic then 3 else 1))
    (st : State 16 4)
    (hc : ComputedSeed.Context n m c t
      ((outerCodec ρ σc m c (if cubic then 3 else 1)).equiv s).val st) :
    ((outer cubic).run st).1.lists 1 =
      [(innerCodec ρ m c).equiv s.2.2.2.2 |>.val,
       (hadamardCodec t (if cubic then 3 else 1)).equiv s.2.2.2.1 |>.val,
       (bitsCodec t).equiv s.2.2.1.2 |>.val,
       (innerPointCodec ρ m c).equiv s.2.2.1.1 |>.val,
       (fieldCodec ρ).equiv s.2.1 |>.val,
       (σc.function (fieldCodec ρ)).equiv s.1.2 |>.val,
       (σc.function (fieldCodec ρ)).equiv s.1.1 |>.val] := by
  have hr := ComputedSeed.program_run (outerTerms cubic) n m c t _ st hc
  rw [← outer_radices ρ σc n m c cubic hn] at hr
  rw [(outerLayout ρ σc m c (if cubic then 3 else 1)).decode] at hr
  simpa only [outer, outerLayout, SeedLayout.prod, SeedLayout.leaf, List.append_assoc,
    List.cons_append, List.nil_append] using hr

theorem inner_run (n m c : ℕ) (s : BinaryLocalCorrection.InnerSeed F m c t)
    (st : State 16 4)
    (hc : ComputedSeed.Context n m c t ((innerCodec ρ m c).equiv s).val st) :
    (inner.run st).1.lists 1 =
      [(bitsCodec t).equiv s.2.2.2 |>.val,
       (fieldCodec ρ).equiv s.2.2.1.2 |>.val,
       (innerPointCodec ρ m c).equiv s.2.2.1.1.2 |>.val,
       (innerPointCodec ρ m c).equiv s.2.2.1.1.1 |>.val,
       (hadamardCodec t 1).equiv s.2.1.2 |>.val,
       (innerPointCodec ρ m c).equiv s.2.1.1 |>.val,
       boolCodec.equiv s.1 |>.val] := by
  have hr := ComputedSeed.program_run innerTerms n m c t _ st hc
  rw [← inner_radices ρ n m c] at hr
  rw [(innerLayout ρ m c).decode] at hr
  simpa only [inner, innerLayout, SeedLayout.prod, SeedLayout.leaf, List.append_assoc,
    List.cons_append, List.nil_append] using hr

theorem call_run {σ : Type*} (σc : Codec σ) (n m c : ℕ) (hn : σc.size = n)
    (s : RawCallSeed F σ m c t) (st : State 16 4)
    (hc : ComputedSeed.Context n m c t ((callCodec ρ σc m c).equiv s).val st) :
    (call.run st).1.lists 1 =
      [(innerCodec ρ m c).equiv s.2.2.2 |>.val,
       (innerPointCodec ρ m c).equiv s.2.2.1 |>.val,
       (fieldCodec ρ).equiv s.2.1 |>.val,
       (σc.function (fieldCodec ρ)).equiv s.1 |>.val, 0, 0, 0] := by
  have hr := ComputedSeed.program_run callTerms n m c t _ st hc
  rw [← call_radices ρ σc n m c hn] at hr
  rw [(callLayout ρ σc m c).decode_padded s 3] at hr
  simpa only [call, callLayout, SeedLayout.prod, SeedLayout.leaf, List.append_assoc,
    List.cons_append, List.nil_append, List.replicate_succ, List.replicate_zero] using hr

theorem derived_run (n m c : ℕ) (s : RawDerivedSample F n m c t 3) (st : State 16 4)
    (hc : ComputedSeed.Context n m c t ((derivedCodec ρ n m c 3).equiv s).val st) :
    (derived.run st).1.lists 1 =
      [(coefficientCodec t 3).equiv s.2.2 |>.val,
       (callCodec ρ ((Codec.fin n).sum (Codec.fin n)) m c).equiv s.2.1.2.2 |>.val,
       (callCodec ρ ((Codec.fin n).sum (Codec.fin n)) m c).equiv s.2.1.2.1 |>.val,
       (bitsCodec t).equiv s.2.1.1 |>.val,
       ((Codec.fin n).function (fieldCodec ρ)).equiv s.1 |>.val, 0, 0] := by
  have hr := ComputedSeed.program_run derivedTerms n m c t _ st hc
  rw [← derived_radices ρ n m c] at hr
  rw [(derivedLayout ρ n m c).decode_padded s 2] at hr
  simpa only [derived, derivedLayout, SeedLayout.prod, SeedLayout.leaf, List.append_assoc,
    List.cons_append, List.nil_append, List.replicate_succ, List.replicate_zero] using hr

theorem difference_run (n m c : ℕ) (s : ((Fin n → F) × (Fin n → F)) × (Fin t → ZMod 2))
    (st : State 16 4)
    (hc : ComputedSeed.Context n m c t
      (((((Codec.fin n).function (fieldCodec ρ)).prod
        ((Codec.fin n).function (fieldCodec ρ))).prod (bitsCodec t)).equiv s).val st) :
    (difference.run st).1.lists 1 =
      [(bitsCodec t).equiv s.2 |>.val,
       ((Codec.fin n).function (fieldCodec ρ)).equiv s.1.2 |>.val,
       ((Codec.fin n).function (fieldCodec ρ)).equiv s.1.1 |>.val, 0, 0, 0, 0] := by
  have hr := ComputedSeed.program_run differenceTerms n m c t _ st hc
  rw [← difference_radices ρ n m c] at hr
  rw [(differenceLayout ρ n).decode_padded s 4] at hr
  simpa only [difference, differenceLayout, SeedLayout.prod, SeedLayout.leaf, List.append_assoc,
    List.cons_append, List.nil_append, List.replicate_succ, List.replicate_zero] using hr

end PCP.Lang.NestedSeed
