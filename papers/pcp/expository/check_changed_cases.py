#!/usr/bin/env python3
"""Three exact, discriminating changed cases for the PCP exposition review.

This file uses the Python standard library only. It does not read or modify the
supplied packet. Run:

    python3 check_changed_cases.py > stdout.json

The finite checks accompany the ordinary derivations in DERIVATIONS.md. They
are not Lean replay, a full PCP instance, or a human-learning experiment.
"""

from fractions import Fraction
from itertools import combinations, product
import json


def ratio(numerator, denominator):
    return str(Fraction(numerator, denominator))


def changed_mask():
    """A marginally uniform mask can fail if it is coupled to the request."""
    # The 8 squarefree monomials of degree <= 3 in three message bits.
    monomials = [
        indices
        for degree in range(4)
        for indices in combinations(range(3), degree)
    ]
    message = (1, 0, 1)
    evaluations = [
        int(all(message[index] for index in indices))
        for indices in monomials
    ]
    evaluation_vector = sum(bit << index for index, bit in enumerate(evaluations))
    count = 1 << len(monomials)
    assert count == 256

    def honest(label):
        # Evaluating a Boolean polynomial is linear in its label coefficients.
        return (label & evaluation_vector).bit_count() % 2

    def received(label):
        return honest(label) ^ int(label == 0)

    errors = sum(received(label) != honest(label) for label in range(count))
    assert errors == 1
    # Exhaustively check the honest additivity used in both corrections.
    assert all(
        honest(left) ^ honest(right) == honest(left ^ right)
        for left in range(count)
        for right in range(count)
    )

    # U is uniform; the request Lambda and mask R are both set equal to U.
    # R is marginally uniform, but R+Lambda is always zero.
    coupled_failures = sum(
        received(uniform) ^ received(uniform ^ uniform) != honest(uniform)
        for uniform in range(count)
    )
    assert coupled_failures == count - 1
    first_location_counts = [0] * count
    second_location_counts = [0] * count
    for uniform in range(count):
        first_location_counts[uniform] += 1
        second_location_counts[uniform ^ uniform] += 1
    assert first_location_counts == [1] * count
    assert second_location_counts[0] == count
    assert sum(second_location_counts[1:]) == 0

    # Hold each request fixed in turn, and give it a genuinely fresh uniform R.
    fresh_failures = [
        sum(
            received(mask) ^ received(mask ^ request) != honest(request)
            for mask in range(count)
        )
        for request in range(count)
    ]
    assert fresh_failures[0] == 0
    assert fresh_failures[1:] == [2] * (count - 1)
    assert all(number <= 2 * errors for number in fresh_failures)
    return {
        "name": "request_dependent_mask",
        "label_space": "F_2^8: coefficient labels of squarefree degree-at-most-three polynomials in three bits",
        "monomial_order": [list(indices) for indices in monomials],
        "message": list(message),
        "evaluation_vector_bits": evaluations,
        "honest_additivity_pairs_checked": count * count,
        "received_word": "Flip only label 0 in the honest evaluation word",
        "labels": count,
        "corrupt_labels": errors,
        "row_error_fraction": ratio(errors, count),
        "coupled_request_and_mask": {
            "experiment": "U uniform; Lambda=U; R=U; output g(R)+g(R+Lambda)",
            "mask_marginal_uniform": True,
            "request_marginal_uniform": True,
            "second_query_always_zero": True,
            "failures": coupled_failures,
            "trials": count,
            "failure_fraction": ratio(coupled_failures, count),
        },
        "fixed_request_fresh_uniform_mask": {
            "requests_checked": count,
            "masks_per_request": count,
            "total_pairs_checked": count * count,
            "failures_for_request_zero": fresh_failures[0],
            "failures_for_every_nonzero_request": 2,
            "max_failure_fraction": ratio(max(fresh_failures), count),
            "two_times_row_error": ratio(2 * errors, count),
            "all_requests_satisfy_bound": True,
        },
        "ordinary_derivation": "For Lambda=R=U!=0, g(U)+g(0)=h(U)+1; for U=0 both errors cancel. With a fixed nonzero Lambda and fresh R, exactly R=0 or R=Lambda contributes one corruption.",
        "lesson": "Marginal uniformity of R does not replace uniformity conditional on the request. The two actual reads need not be independent.",
    }


def binary_polynomial_remainder(polynomial, divisor):
    while polynomial and polynomial.bit_length() >= divisor.bit_length():
        polynomial ^= divisor << (polynomial.bit_length() - divisor.bit_length())
    return polynomial


def gf16_multiply(left, right):
    # F_2[T]/(T^4+T+1), encoded by the four coefficient bits.
    result = 0
    while right:
        if right & 1:
            result ^= left
        right >>= 1
        left <<= 1
        if left & 0b10000:
            left ^= 0b10011
    return result


def gf16_power(value, exponent):
    result = 1
    while exponent:
        if exponent & 1:
            result = gf16_multiply(result, value)
        value = gf16_multiply(value, value)
        exponent >>= 1
    return result


def changed_decoded_polynomial():
    """An arbitrary inner polynomial can exceed the honest line capacity."""
    radix, inner_degree = 3, 2
    honest_capacity = radix ** inner_degree
    selected_block, selected_digit = 1, 2
    selected_exponent = selected_digit * radix ** selected_block
    decoded_degree = 2 * selected_exponent
    sharp_generic_bound = inner_degree * (radix - 1) * radix ** (inner_degree - 1)
    relaxed_generic_bound = inner_degree * radix ** inner_degree
    assert (honest_capacity, selected_exponent, decoded_degree) == (9, 6, 12)
    assert decoded_degree == sharp_generic_bound <= relaxed_generic_bound
    assert decoded_degree >= honest_capacity

    # A quartic over F_2 is irreducible if it has no monic divisor of degree 1 or 2.
    modulus = 0b10011
    possible_small_factors = [2, 3, 4, 5, 6, 7]
    remainders = {
        str(divisor): binary_polynomial_remainder(modulus, divisor)
        for divisor in possible_small_factors
    }
    assert all(remainders.values())
    assert all(gf16_power(nonzero, 15) == 1 for nonzero in range(1, 16))

    values = []
    for field_element in range(16):
        power_point = {
            (block, digit): gf16_power(field_element, digit * radix ** block)
            for block in range(inner_degree)
            for digit in range(radix)
        }
        inner_value = gf16_power(power_point[selected_block, selected_digit], 2)
        decoded_value = gf16_power(field_element, decoded_degree)
        assert inner_value == decoded_value
        values.append(decoded_value)
    assert decoded_degree < 16
    return {
        "name": "arbitrary_inner_polynomial",
        "digit_base_b": radix,
        "inner_degree_c": inner_degree,
        "inner_polynomial": "Q(W)=W_(1,2)^2",
        "inner_total_degree": 2,
        "honest_set_multilinear_form": False,
        "power_point_coordinate": "Phi(Y)_(1,2)=Y^6",
        "formal_substitution": "Q(Phi(Y))=Y^12",
        "decoded_degree": decoded_degree,
        "honest_capacity_requires_degree_strictly_below": honest_capacity,
        "sharp_generic_substitution_bound": sharp_generic_bound,
        "relaxed_bound_D_equals_c_times_b_to_c": relaxed_generic_bound,
        "finite_field": {
            "size": 16,
            "modulus": "T^4+T+1",
            "modulus_bit_encoding": modulus,
            "remainders_for_all_monic_degree_1_or_2_divisors": remainders,
            "irreducibility_check_passed": True,
            "nonzero_elements_checked_for_a_to_15_equals_1": 15,
            "evaluation_points_checked": 16,
            "decoded_values_in_coefficient_bit_encoding": values,
            "substitution_values_agree_at_all_points": True,
        },
        "ordinary_root_bound_deduction": {
            "claim": "No polynomial of degree <9 has the same function as Y^12 on F_16",
            "method": "For any such p, Y^12-p is nonzero of degree 12 and therefore has at most 12 roots; function equality would require 16 roots.",
            "enumerated_all_candidate_polynomials": False,
        },
        "lesson": "An inner degree-c guarantee does not imply the honest univariate capacity bound. The arbitrary decoded polynomial needs the enlarged substitution degree bound.",
        "scope": "This is a degree/representation changed case, not a complete PCP parameter instance.",
    }


def changed_anchor_fibre():
    """A tiny global bad-row fraction may be one at a prescribed anchor."""
    field_size, dimension = 4, 2
    points = list(product(range(field_size), repeat=dimension))
    prescribed_anchor = (1, 2)
    row_count = len(points) ** 2
    global_bad_rows = sum(
        anchor == prescribed_anchor for anchor in points for _direction in points
    )
    bad_per_anchor = {
        anchor: sum(anchor == prescribed_anchor for _direction in points)
        for anchor in points
    }
    assert len(points) == field_size ** dimension == 16
    assert row_count == 256
    assert global_bad_rows == 16
    assert Fraction(global_bad_rows, row_count) == Fraction(1, field_size ** dimension)
    assert bad_per_anchor[prescribed_anchor] == len(points)
    assert all(
        count == 0 for anchor, count in bad_per_anchor.items()
        if anchor != prescribed_anchor
    )
    return {
        "name": "bad_auxiliary_anchor_fibre",
        "field_size_Q": field_size,
        "ambient_dimension_k": dimension,
        "ambient_points": len(points),
        "prescribed_anchor": list(prescribed_anchor),
        "oriented_row_index": "(anchor a, direction v), with both in F_Q^k; zero direction included",
        "bad_rows": "Every row whose anchor is the prescribed a*, regardless of its direction",
        "all_rows": row_count,
        "globally_bad_rows": global_bad_rows,
        "global_bad_row_fraction": ratio(global_bad_rows, row_count),
        "rows_sampled_conditional_on_target_a_star": len(points),
        "bad_rows_conditional_on_target_a_star": bad_per_anchor[prescribed_anchor],
        "conditional_bad_row_fraction": ratio(bad_per_anchor[prescribed_anchor], len(points)),
        "all_other_anchor_fibres_have_zero_bad_rows": True,
        "ordinary_derivation": "There are Q^(2k) pairs (a,v), and Q^k bad pairs with a=a*. Their fraction is Q^(-k). Conditioning on the fixed target a* leaves only those Q^k bad rows, so the bad fraction is 1.",
        "lesson": "A global auxiliary-row average alone cannot control a prescribed target. The actual corrector rejection term is essential to the target-specific guarantee.",
        "scope": "Exact row-index counting. No field arithmetic, inner-test rejection rate, or complete cheating PCP is asserted.",
    }


def main():
    result = {
        "description": "Three independent changed-case checks for the revised worked PCP exposition",
        "execution_kind": "Exact finite computation with ordinary mathematical derivations recorded separately",
        "all_assertions_passed": True,
        "cases": [changed_mask(), changed_decoded_polynomial(), changed_anchor_fibre()],
        "limitations": [
            "No Lean elaboration, kernel replay, or axiom extraction was performed.",
            "No small-field example is claimed to satisfy the full PCP parameter regime.",
            "Successful model calculations are not measured human-learning outcomes.",
            "The no-low-degree-representative conclusion uses the ordinary root bound, not exhaustive enumeration of polynomials.",
        ],
    }
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
