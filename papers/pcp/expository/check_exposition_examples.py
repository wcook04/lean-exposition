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


def check_digit_encoding():
    for value in range(5):
        first_block = (1, value, value * value % 5)
        second_block = (1, pow(value, 3, 5), pow(value, 6, 5))
        encoded = (first_block[2] * second_block[1]
                   + 2 * first_block[1] * second_block[0]
                   + 3 * first_block[0] * second_block[0]) % 5
        original = (value ** 5 + 2 * value + 3) % 5
        check(encoded == original, "base-three digit substitution")
        if value == 2:
            check(first_block == (1, 2, 4) and second_block == (1, 3, 4),
                  "displayed substitution blocks")
            check(encoded == 4, "displayed substitution value")
    print("Digit encoding: substitution equality checked at all five field elements; lambda=2 gives 4.")


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


def main():
    check_graph_examples()
    check_interpolation_and_grid()
    check_digit_encoding()
    check_label_counterexample()
    check_nae_gadget()
    check_review_additions()
    print("All additional exposition checks passed.")


if __name__ == "__main__":
    main()
