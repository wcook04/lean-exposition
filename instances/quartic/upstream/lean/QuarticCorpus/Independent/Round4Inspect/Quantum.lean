module

public import QuarticQuery.Upper.UniformEndpoint
public import QuarticQuery.Upper.FinalBScalarPhysical
public import QuarticQuery.Paper.ConstructionForrelationSharp
public import QuarticQuery.Paper.ForrelationTensorSharp
public import QuarticQuery.Paper.ReadSpecOneQuery
public import QuarticQuery.Paper.TensorCoordinates

/-! Type and transitive-axiom inspection of round-four return 04.
Native validation: `research/adjudication/round4_formal.json`. -/

#check @QuarticQuery.Upper.uniformOpaqueAmplifier
#check @QuarticQuery.Upper.finalB_physical_on_embedding
#check @QuarticQuery.Paper.forr_walsh_physical
#check @QuarticQuery.Paper.forr_walsh_tensor_physical
#check @QuarticQuery.Paper.construction_decoder_sharp
#check @QuarticQuery.Paper.P_runs_sharp
#check @QuarticQuery.Upper.compile_circ_one

#print axioms QuarticQuery.Upper.uniformOpaqueAmplifier
#print axioms QuarticQuery.Upper.finalB_physical_on_embedding
#print axioms QuarticQuery.Paper.forr_walsh_physical
#print axioms QuarticQuery.Paper.forr_walsh_tensor_physical
#print axioms QuarticQuery.Paper.construction_decoder_sharp
#print axioms QuarticQuery.Paper.P_runs_sharp
#print axioms QuarticQuery.Upper.compile_circ_one
#print axioms QuarticQuery.Paper.construction_projection_test_sharp
#print axioms QuarticQuery.Paper.tensorVector_coord_product
