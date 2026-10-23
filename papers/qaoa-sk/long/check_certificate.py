"""Re-expand the rational identity in OpenAI's 2026 SK support manuscript.

This checks one finite polynomial identity, not its analytic hypotheses or a
Lean proof. Requires SymPy; run from any directory with Python 3.11 or newer.
Source: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/Full-support-of-the-zero-temperature-Sherrington-Kirkpatrick-order-parameter-September-27-2026/build/certificate.tex,
labels cert:identity and cert:table. The source is Apache-2.0.
"""

import sympy as s


def check() -> dict:
    R, K, v, b, j, z, L, B = s.symbols("R K v b j z L B")
    rat = s.Rational
    A, C, k, T0, g0, h = map(rat, (
        "1/13", "53/24", "19/16", "73/48", "2331/10000", "87/2500"))
    x0, y, m, n0 = map(rat, ("4663/5000", "6853/10000", "-1051/400", "-1073/500"))
    Q = A*v*b + C*v**2 + k*K*v - 2*k*R*b + T0*R*v
    T = g0*R*v + h*j*v
    F = ((A*v-2*k*R)*b**2
         + b*(2*C*v**2+2*k*K*v+(g0+2*T0)*R*v+h*j*v)
         + x0*v**2*j+y*v**3+m*K*v**2+n0*R*v**2)
    rules = (2*R*v, 2*v*K+R*j, -R*b, -z-b*v, -j*v+K*b-L)
    W = sum(s.diff(F, t)*d for t, d in zip((R, K, v, b, j), rules)) + (v+R-K)*F
    squares = (
        R*j*(b-7*v)**2,
        R*(b-2*v)*(b-rat(7, 3)*v)**2,
        K*v*(b-rat(9, 2)*v)**2,
        v*(b-2*v)*(K+R/4-v/7)**2,
        (v*b-rat(14, 5)*v**2-rat(13, 4)*K*v+rat(4, 3)*R*v)**2,
    )
    weights = map(rat, ("337/10000", "183/2500", "411/10000", "11461/5000", "647/10000"))
    residual = s.expand((z**2-12*R*v*b**2+6*v**4-(z+Q)**2
                        -(z+b*v-2*R*b)*T-W-L*(x0*v**2+h*b*v)
                        -sum(p*q for p, q in zip(weights, squares))).subs(b, B+2*v))
    terms = (
        (R**2*v**2,"223/160000"), (R**2*v*B,"4007/240000"),
        (R**2*B**2,"1097/120000"), (R*K*v**2,"83/80000"),
        (R*K*v*B,"3343/24000"), (R*v**3,"16259/23400000"),
        (R*v**2*B,"30179/5460000"), (R*v**2*j,"26/625"),
        (R*v*B**2,"107/15000"), (R*v*B*j,"3/2500"),
        (R*B**3,"121/32500"), (R*B**2*j,"11/10000"),
        (K**2*v**2,"579/20000"), (K**2*v*B,"207/2500"),
        (K*v**3,"911/975000"), (K*v**2*B,"349/420000"),
        (K*v**2*j,"5011/5000"), (K*v*B**2,"133/130000"),
        (K*v*B*j,"87/2500"), (v**4,"1661507/1521000000"),
        (v**3*B,"633799/621075000"), (v**2*B**2,"10657/1690000"),
    )
    expected = sum(term*rat(coefficient) for term, coefficient in terms)
    if s.expand(residual-expected) != 0:
        raise ValueError("Published polynomial identity does not match its table")
    if len(s.Poly(residual, R, K, v, B, j).terms()) != 22:
        raise ValueError("Unexpected remainder monomials")
    if not all(rat(c) > 0 for _, c in terms):
        raise ValueError("Remainder has a nonpositive coefficient")
    surplus = rat("1661507/1521000000")-rat(1, 1000)
    if surplus <= 0:
        raise ValueError("Coercive coefficient is insufficient")
    return {"identity": "exact", "positive_remainder_terms": 22,
            "coercive_surplus": str(surplus), "sympy": s.__version__}


if __name__ == "__main__":
    print(check())
