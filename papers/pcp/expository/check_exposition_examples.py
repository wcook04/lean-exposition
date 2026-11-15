"""Exact finite checks for the PCP exposition's additional teaching examples.

Run with Python 3; uses only its standard library. These finite examples do not
instantiate the large-field parameter hypotheses of the complete PCP theorem.
The unbounded family refuting the old scalar test is an ordinary proof in the
manuscript, not established by this finite enumeration.
"""

from fractions import Fraction
from itertools import combinations, product


def check(condition, description):
    if not condition:
        raise AssertionError(description)


def check_graph_examples():
    edges = tuple(combinations(range(4), 2))

    def bad_edges(colouring):
        return sum(colouring[u] == colouring[v] for u, v in edges)

    check(len(edges) == 6, "K4 has six edges")
    check(bad_edges((0, 0, 1, 2)) == 1, "displayed K4 colouring has one bad edge")
    all_counts = [bad_edges(c) for c in product(range(3), repeat=4)]
    check(min(all_counts) == 1, "every one of 81 three-colour assignments to K4 fails")
    for triangle_count in range(12):
        vertices = [0, 0, 1, 2]
        graph_edges = list(edges)
        for _ in range(triangle_count):
            start = len(vertices)
            vertices.extend((0, 1, 2))
            graph_edges.extend(combinations(range(start, start + 3), 2))
        bad = sum(vertices[u] == vertices[v] for u, v in graph_edges)
        check(bad == 1, "added proper triangles create no extra bad edges")
        check(len(graph_edges) == 6 + 3 * triangle_count, "disjoint edge count")
        check(Fraction(bad, len(graph_edges)) == Fraction(1, 6 + 3 * triangle_count),
              "edge sampling probability")
    check(Fraction(1, 6 + 3 * 3) == Fraction(1, 15), "three extra triangles")
    print("K4: all 81 three-colour assignments checked; displayed assignment has one bad edge;")
    print("  disjoint-triangle construction checked for 0..11 triangles; t=3 gives 1/15.")


def check_interpolation_and_grid():
    def z(x):
        return x * (x - 1) % 5

    check([z(x) for x in range(5)] == [0, 0, 2, 1, 2], "displayed vanishing table")
    nodes = (0, 1, 2)
    weights = []
    for i, node in enumerate(nodes):
        numerator = denominator = 1
        for j, other in enumerate(nodes):
            if i != j:
                numerator = numerator * (3 - other) % 5
                denominator = denominator * (node - other) % 5
        weights.append(numerator * pow(denominator, -1, 5) % 5)
    check(weights == [1, 2, 3], "Lagrange weights at 3")
    for a, b, c in product(range(5), repeat=3):
        def polynomial(x):
            return (a + b * x + c * x * x) % 5

        predicted = sum(w * polynomial(x) for w, x in zip(weights, nodes)) % 5
        check(polynomial(3) == predicted, "quadratic interpolation")
    check((0 + 2 * 1 + 3 * 4) % 5 == 4, "worked square polynomial")
    check((0 + 1 + 4) % 5 == 0, "unit weights fail for this requested evaluation")

    def p(x, y):
        return (z(x) * (y + 1) + z(y) * (x + 2)) % 5

    def certificate(x, y, u, v):
        return (u * (y + 1) + v * (x + 2)) % 5

    for x, y in product(range(5), repeat=2):
        check(certificate(x, y, 0, 0) == 0, "zero-substitution identity")
        check(certificate(x, y, z(x), z(y)) == p(x, y), "certificate substitution")
        # The constant pair P=1, M=1 satisfies only the second required identity.
        bad_p = 1
        bad_certificate = lambda _u, _v: 1
        check(bad_certificate(z(x), z(y)) == bad_p, "constant certificate substitution")
        check(bad_certificate(0, 0) != 0, "first identity excludes constant certificate")
    check(all(p(x, y) == 0 for x, y in product((0, 1), repeat=2)), "four grid points")
    check(p(2, 2) == certificate(2, 2, 2, 2) == 4, "ambient evaluation can be nonzero")
    print("F5: all 125 quadratics satisfy the [1,2,3] interpolation formula;")
    print("  both certificate identities checked at 25 ambient points; P(2,2)=4;")
    print("  P=M=1 shows why the first identity cannot be omitted.")


def check_weighted_interpolation_and_slice():
    nodes = tuple(pow(2, k, 5) for k in (1, 2, 3))
    weights = []
    for node in nodes:
        weight = 1
        for other in nodes:
            if other != node:
                weight = weight * (-other) * pow(node - other, -1, 5) % 5
        weights.append(weight)
    check((nodes, weights) == ((2, 4, 3), [1, 3, 2]), "weighted nodes and coefficients at zero")
    for a, b, c in product(range(5), repeat=3):
        predicted = sum(w * (a + b * x + c * x * x) for w, x in zip(weights, nodes)) % 5
        check(predicted == a, "weighted interpolation gives the constant coefficient")

    points = tuple(product(range(5), repeat=4))
    slice_points = tuple(point for point in points if point[2:] == (0, 0))
    check((len(points), len(slice_points)) == (625, 25), "zero certificate slice size")
    print("F5: weights [1,3,2] at nodes (2,4,3) interpolate all 125 quadratics at zero;")
    print("  all 25 zero-slice points can be corrupted with overall error 1/25.")


def check_digit_encoding():
    evaluations = []
    for value in range(5):
        first_block = (1, value, value * value % 5)
        second_block = (1, pow(value, 3, 5), pow(value, 6, 5))
        encoded = (first_block[1] * second_block[1]
                   + 2 * first_block[1] * second_block[0]
                   + 3 * first_block[0] * second_block[0]) % 5
        original = (value ** 4 + 2 * value + 3) % 5
        evaluations.append(original)
        check(encoded == original, "base-three digit substitution")
        if value == 2:
            check(first_block == (1, 2, 4) and second_block == (1, 3, 4),
                  "displayed substitution blocks")
            check(encoded == 3, "displayed substitution value")

    for coefficients in product(range(5), repeat=4):
        cubic = [sum(a * value ** j for j, a in enumerate(coefficients)) % 5
                 for value in range(5)]
        check(cubic != evaluations, "no polynomial of degree at most three gives these values")
    print("Digit encoding: substitution equality checked at all five field elements; lambda=2 gives 3;")
    print("  none of the 625 polynomials of degree at most three has the same evaluations.")


def check_label_counterexample():
    # Bit positions encode coefficients of 1, Z1, Z2 and Z1*Z2, respectively.
    def h(label):
        return ((label >> 0) ^ (label >> 3)) & 1

    for left, right in product(range(16), repeat=2):
        check(h(left) ^ h(right) == h(left ^ right), "linearity in the label")
    check(tuple(h(label) for label in (1, 2, 4, 8)) == (1, 0, 0, 1),
          "values of the four basis labels")
    for x, y in product(range(2), repeat=2):
        check((1, x, y, x * y) != (1, 0, 0, 1), "no evaluation point has these answers")
    print("Label counterexample: all 256 BLR pairs pass; none of four evaluation points matches.")


def check_label_domains_and_correction():
    messages = range(1 << 3)
    # A monomial is its variable mask. Bit m of a label selects monomial m.
    monomials = tuple(messages)
    full_labels = range(1 << len(monomials))
    full_label_set = set(full_labels)
    linear_term_mask = sum(1 << m for m in monomials if m.bit_count() == 1)
    affine_labels = tuple(label for label in full_labels if (label & ~(linear_term_mask | 1)) == 0)
    homogeneous_labels = tuple(label for label in full_labels if (label & ~linear_term_mask) == 0)
    check((len(full_labels), len(affine_labels), len(homogeneous_labels)) == (256, 16, 8),
          "three-bit full, affine and homogeneous label counts")

    def evaluate(label, message):
        return sum((label >> m) & 1 for m in monomials if (message & m) == m) % 2

    evaluations = {tuple(evaluate(label, x) for x in messages) for label in full_labels}
    check(len(evaluations) == len(full_labels), "each full label has a distinct evaluation table")
    for a, b in combinations(messages, 2):
        for labels in (full_labels, affine_labels, homogeneous_labels):
            disagreements = sum(evaluate(label, a) != evaluate(label, b) for label in labels)
            check(2 * disagreements == len(labels), "half distance on each label domain")

    honest = [evaluate(label, 0b101) for label in full_labels]
    received = honest.copy()
    for label in homogeneous_labels:
        received[label] = evaluate(label, 0b001)
    errors = sum(a != b for a, b in zip(honest, received))
    homogeneous_errors = sum(received[label] != honest[label] for label in homogeneous_labels)
    check((errors, homogeneous_errors) == (4, 4), "distance after replacing homogeneous answers")
    print("Label domains: 256 full, 16 affine, 8 homogeneous; replacing four bits gives")
    print("  error 1/64 on full labels and 1/2 on homogeneous labels.")

    maximum_wrong = 0
    for requested in full_labels:
        check({mask ^ requested for mask in full_labels} == full_label_set,
              "shifting a uniform mask preserves uniformity")
        wrong = sum((received[mask] ^ received[mask ^ requested]) != honest[requested]
                    for mask in full_labels)
        check(wrong <= 2 * errors, "two-read correction obeys the union bound")
        maximum_wrong = max(maximum_wrong, wrong)
    check(maximum_wrong == 2 * errors, "the two-read correction bound is attained")
    print("Label correction: all 256 requests and all 256 masks per request checked;")
    print("  maximum error 1/32 equals twice the full-label error.")


def check_nae_gadget():
    def nae(a, b, c):
        return not a == b == c

    for a, b, c in product(range(2), repeat=3):
        has_z = any(nae(a, b, z) and nae(1 - z, c, 0) for z in range(2))
        check(bool(a or b or c) == has_z, "OR to two NAE relations")
        literal_colours = (a, b, c)
        extensions = [triangle for triangle in product(range(3), repeat=3)
                      if len(set(triangle)) == 3
                      and all(triangle[i] != literal_colours[i] for i in range(3))]
        check(bool(extensions) == nae(a, b, c), "NAE triangle extension equivalence")
    check(all(x != y for x, y in zip((1, 2, 0), (0, 0, 1))),
          "displayed triangle avoids its adjacent literal colours")
    variable_pairs = [(a, b) for a, b in product(range(3), repeat=2)
                      if a != 2 and b != 2 and a != b]
    check(variable_pairs == [(0, 1), (1, 0)], "variable/negation palette gadget")
    print("NAE: all eight Boolean cases checked for OR conversion and triangle extension;")
    print("  palette gadget permits exactly the complementary pairs (0,1), (1,0).")


def check_review_additions():
    for z, u, v in product(range(2), repeat=3):
        clauses = (bool(z or not u), bool(z or not v), bool(not z or u or v))
        check(all(clauses) == (bool(z) == bool(u or v)), "three-clause OR gate")
    for pattern, actual in product(product(range(2), repeat=3), repeat=2):
        flag = 0
        for x, p in zip(actual, pattern):
            flag = flag or (x ^ p)
        check(bool(flag) == (actual != pattern), "prefix mismatch flags")
    small = 5 * Fraction(1, 32) + Fraction(1, 16)
    boundary = 5 * Fraction(1, 16) + Fraction(1, 16)
    check(small == Fraction(7, 32) < Fraction(3, 8), "strict toy error budget")
    check(boundary == Fraction(3, 8), "boundary toy error budget")
    print("Review additions: all eight OR-gate cases and 64 prefix-mismatch cases pass;")
    print("  toy soundness budgets give 7/32 < 3/8 and equality 3/8 at the boundary.")


def check_construction_constants():
    c = 4
    inner_decoding = 4 * (c + 2) ** 2 * (112 * (c + 2) + 60)
    point_line = 2 * ((c + 1) * inner_decoding + 29)
    outer_decoding = 28 + point_line
    outer_correction = 2 + 2 * (c + 1) * inner_decoding
    check((inner_decoding, point_line, outer_decoding, outer_correction)
          == (105408, 1054138, 1054166, 1054082), "degree-four constants K, E, S, C")

    difference_error = 1 + 3 * outer_decoding
    two_correctors = 1 + 2 * outer_correction
    derived_grid_error = two_correctors * (1 + 2 * outer_decoding) + 2 * outer_decoding
    gap = min(Fraction(1, 4_000_000 * (point_line + 1)),
              Fraction(1, 16 * difference_error),
              Fraction(1, 16 * (derived_grid_error + 1)))
    sampling_gap = gap / 16
    repetitions = (sampling_gap.denominator + sampling_gap.numerator - 1) // sampling_gap.numerator
    queries_per_run = 20 * c + 107
    check(gap == Fraction(1, 71_115_455_156_448), "gap before fair-bit sampling")
    check(sampling_gap == Fraction(1, 1_137_847_282_503_168), "gap after fair-bit sampling")
    check(repetitions == 1_137_847_282_503_168 and queries_per_run == 187,
          "repetitions and per-run queries")
    check(repetitions * queries_per_run == 212_777_441_828_092_416, "amplified query bound")
    print("Degree four: (K,E,S,C)=(105408,1054138,1054166,1054082);")
    print("  fair-bit gap 1/1137847282503168, 1137847282503168 repetitions at 187 queries each.")


def main():
    check_graph_examples()
    check_interpolation_and_grid()
    check_weighted_interpolation_and_slice()
    check_digit_encoding()
    check_label_counterexample()
    check_label_domains_and_correction()
    check_nae_gadget()
    check_review_additions()
    check_construction_constants()
    print("All additional exposition checks passed.")


if __name__ == "__main__":
    main()
