module

public import QuarticCorpus.Independent.Degree.Solution
public import QuarticCorpus.Independent.Degree.Controls

set_option pp.universes true

#check @QuarticQuery.Independent.Degree.coefficients_ext
#check @QuarticQuery.Independent.Degree.exists_unique_coefficients
#check @QuarticQuery.Independent.Degree.canonical_degree_le_iff
#check @QuarticQuery.Independent.Degree.checked_degree_conventions
#check @QuarticQuery.Independent.Degree.empty_coefficient_is_value_at_zero
#check @QuarticQuery.Independent.Degree.constant_one_expectation
#check @QuarticQuery.Independent.Degree.projection_expectation
#check @QuarticQuery.Independent.Degree.two_bit_xor_expectation

#print axioms QuarticQuery.Independent.Degree.coefficients_ext
#print axioms QuarticQuery.Independent.Degree.exists_unique_coefficients
#print axioms QuarticQuery.Independent.Degree.canonical_degree_le_iff
#print axioms QuarticQuery.Independent.Degree.checked_degree_conventions
#print axioms QuarticQuery.Independent.Degree.empty_coefficient_is_value_at_zero
#print axioms QuarticQuery.Independent.Degree.constant_one_expectation
#print axioms QuarticQuery.Independent.Degree.projection_expectation
#print axioms QuarticQuery.Independent.Degree.two_bit_xor_expectation
