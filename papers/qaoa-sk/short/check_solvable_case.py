"""Reproduce the calculations of Section 3 of the short paper.

1. The rational identity (5), exactly as printed, in exact arithmetic (SymPy).
2. The explicitly solvable case of Section 3.1: gamma = 1 with terminal value
   log(2 cosh x), where r = tanh x and X_t has law N(t,t)/2 + N(-t,t)/2.
3. The change of variables of Section 3.5 between the quantities B, S of the
   identity and the slope-coordinate quantities K, dK, J, checked by numerical
   differentiation for the terminal value |x| and a constant coefficient.

These are finite calculations. They check no analytic hypothesis of the
source and are not a Lean proof. Requires SymPy and mpmath; Python 3.11+.
"""

import mpmath as mp
import sympy as sp

mp.mp.dps = 30
Q_ = sp.Rational


def identity_as_printed() -> dict:
    R, K, v, b, j, z, L = sp.symbols("R K v b j z L")
    B = b - 2 * v
    S = z + b * v - 2 * R * b
    Q = Q_(1, 13) * v * b + Q_(53, 24) * v**2 + Q_(19, 16) * K * v - Q_(19, 8) * R * b + Q_(73, 48) * R * v
    T = v * (Q_(2331, 10000) * R + Q_(87, 2500) * j)
    F2 = ((Q_(1, 13) * v - Q_(19, 8) * R) * b**2
          + b * (Q_(53, 12) * v**2 + Q_(19, 8) * K * v + Q_(98243, 30000) * R * v + Q_(87, 2500) * j * v)
          + Q_(4663, 5000) * v**2 * j + Q_(6853, 10000) * v**3
          - Q_(1051, 400) * K * v**2 - Q_(1073, 500) * R * v**2)
    rules = {R: 2 * R * v, K: 2 * v * K + R * j, v: -R * b, b: -z - b * v, j: -j * v + K * b - L}
    W = sum(sp.diff(F2, x) * d for x, d in rules.items()) + (v + R - K) * F2
    table = {
        "R**2*v**2": "223/160000", "R**2*v*B": "4007/240000", "R**2*B**2": "1097/120000",
        "R*K*v**2": "83/80000", "R*K*v*B": "3343/24000", "R*v**3": "16259/23400000",
        "R*v**2*B": "30179/5460000", "R*v**2*j": "26/625", "R*v*B**2": "107/15000",
        "R*v*B*j": "3/2500", "R*B**3": "121/32500", "R*B**2*j": "11/10000",
        "K**2*v**2": "579/20000", "K**2*v*B": "207/2500", "K*v**3": "911/975000",
        "K*v**2*B": "349/420000", "K*v**2*j": "5011/5000", "K*v*B**2": "133/130000",
        "K*v*B*j": "87/2500", "v**4": "1661507/1521000000", "v**3*B": "633799/621075000",
        "v**2*B**2": "10657/1690000",
    }
    names = {"R": R, "K": K, "v": v, "B": B, "j": j}
    P_rem = sum(Q_(c) * sp.sympify(m, locals=names) for m, c in table.items())
    right = (W + (z + Q)**2 + S * T + Q_(4663, 5000) * L * v**2 + Q_(87, 2500) * L * b * v
             + Q_(337, 10000) * R * j * (b - 7 * v)**2
             + Q_(183, 2500) * R * B * (b - Q_(7, 3) * v)**2
             + Q_(411, 10000) * K * v * (b - Q_(9, 2) * v)**2
             + Q_(11461, 5000) * v * B * (K + R / 4 - v / 7)**2
             + Q_(647, 10000) * v**2 * (b - Q_(14, 5) * v - Q_(13, 4) * K + Q_(4, 3) * R)**2
             + P_rem)
    left = z**2 - 12 * R * v * b**2 + 6 * v**4
    if sp.expand(left - right) != 0:
        raise ValueError("identity (5) as printed does not hold")
    if sp.expand(sp.diff(F2, b) - 2 * Q - T) != 0:
        raise ValueError("d F_2 / d b is not 2Q + T")
    kappa = Q_(table["v**4"])
    if not all(Q_(c) > 0 for c in table.values()) or kappa <= Q_(1, 1000):
        raise ValueError("coefficients of the remainder")
    return {"identity": "exact", "monomials": len(table), "kappa_minus_1_over_1000": str(kappa - Q_(1, 1000))}


def _model(x, t):
    th = mp.tanh(x)
    R = th**2
    v = 1 - R
    z = v * (6 * R - 2)
    K = x * th / t
    j = (1 - (2 * x / mp.sinh(2 * x) if x != 0 else 1)) / t
    return R, K, v, 2 * v, j, z


def _density(x, t):
    return (mp.npdf(x, t, mp.sqrt(t)) + mp.npdf(x, -t, mp.sqrt(t))) / 2


def _expect(fn, t):
    top = t + 12 * mp.sqrt(t) + 5
    return 2 * mp.quad(lambda x: fn(x, t) * _density(x, t), mp.linspace(0, top, 40))


def _curvature(x, t):
    R, K, v, b, j, z = _model(x, t)
    return z**2 - 12 * R * v * b**2 + 6 * v**4


def _pieces(x, t):
    R, K, v, b, j, z = _model(x, t)
    f = lambda p, q: mp.mpf(p) / q
    Q = f(1, 13) * v * b + f(53, 24) * v**2 + f(19, 16) * K * v - f(19, 8) * R * b + f(73, 48) * R * v
    rem = (f(223, 160000) * R**2 * v**2 + f(83, 80000) * R * K * v**2 + f(16259, 23400000) * R * v**3
           + f(26, 625) * R * v**2 * j + f(579, 20000) * K**2 * v**2 + f(911, 975000) * K * v**3
           + f(5011, 5000) * K * v**2 * j + f(1661507, 1521000000) * v**4)
    return ((z + Q)**2, f(337, 10000) * R * j * (b - 7 * v)**2, f(411, 10000) * K * v * (b - f(9, 2) * v)**2,
            f(647, 10000) * v**2 * (b - f(14, 5) * v - f(13, 4) * K + f(4, 3) * R)**2, rem)


def solvable_case() -> dict:
    half = mp.mpf(1) / 2
    theta = mp.mpf(1) / 2
    pointwise = (1 - theta)**2 * (90 * theta**2 - 84 * theta + 10)
    lo, hi = (7 - 2 * mp.sqrt(6)) / 15, (7 + 2 * mp.sqrt(6)) / 15
    band = 2 * mp.quad(lambda x: _density(x, half), [mp.atanh(mp.sqrt(lo)), mp.atanh(mp.sqrt(hi))])
    rho = lambda t: _expect(_curvature, t) / _expect(lambda x, s: _model(x, s)[2]**4, t)
    grid = [mp.mpf(k) / 20 for k in range(1, 41)] + [mp.mpf(k) for k in (3, 5, 10, 30, 100)]
    values = [rho(t) for t in grid]
    if any(a <= b for a, b in zip(values, values[1:])):
        raise ValueError("rho is not decreasing on the grid")
    sech = lambda n: mp.quad(lambda x: mp.sech(x)**n, [-mp.inf, 0, mp.inf])
    limit = (16 * sech(3) - 96 * sech(5) + 90 * sech(7)) / sech(7)
    # rho(t) > 2/5 for all t: F changes sign twice, has zero integral and negative second moment
    F = lambda x: 16 * mp.sech(x)**3 - 96 * mp.sech(x)**5 + mp.mpf(448) / 5 * mp.sech(x)**7
    zeroth = mp.quad(F, [0, 1, 3, mp.inf])
    second = mp.quad(lambda x: x * x * F(x), [0, 1, 3, mp.inf])
    if abs(zeroth) > mp.mpf(10)**-20 or abs(second + 52 * mp.pi / 225) > mp.mpf(10)**-20:
        raise ValueError("moments of F")
    signs = [mp.sign(mp.quad(F, [0, mp.mpf(k) / 20])) for k in range(1, 200)]
    if signs[0] != 1 or sum(a != b for a, b in zip(signs, signs[1:])) != 1:
        raise ValueError("G should be positive and then negative")
    if any(v <= mp.mpf(2) / 5 for v in values):
        raise ValueError("rho fell to 2/5 on the grid")
    pieces = [_expect(lambda x, s, i=i: _pieces(x, s)[i], half) for i in range(5)]
    total = _expect(_curvature, half)
    if abs(sum(pieces) - total) > mp.mpf(10)**-20:
        raise ValueError("the reduced identity does not integrate to the expectation")
    return {
        "value_at_theta_half": mp.nstr(pointwise, 6),
        "negative_band": (mp.nstr(lo, 4), mp.nstr(hi, 4)),
        "probability_of_band_at_t_half": mp.nstr(band, 4),
        "rho(0.5)": mp.nstr(rho(half), 4), "rho(1)": mp.nstr(rho(mp.mpf(1)), 4),
        "rho(100)": mp.nstr(values[-1], 4), "limit_t_to_infinity": mp.nstr(limit, 12),
        "pieces_at_t_half": [mp.nstr(p, 3) for p in pieces], "expectation_at_t_half": mp.nstr(total, 4),
        "kappa_times_E_v4_at_t_half": mp.nstr(mp.mpf(1661507) / 1521000000
                                              * _expect(lambda x, s: _model(x, s)[2]**4, half), 3),
    }


def slope_coordinates() -> dict:
    """K = cB/(2v), dK = c^2 (BRb - Sv)/(2 r v^3), J = c (B(v^2 + Rb) - Sv)/(2 v^3)."""
    mp.mp.dps = 40
    worst = mp.mpf(0)
    signs = True
    for c in (mp.mpf("0.4"), mp.mpf(1), mp.mpf(3)):
        for t in (mp.mpf("0.2"), mp.mpf("0.6"), mp.mpf("0.9")):
            tau = 1 - t
            h = lambda x: (mp.exp(c * x) * mp.ncdf((x + c * tau) / mp.sqrt(tau))
                           + mp.exp(-c * x) * mp.ncdf((-x + c * tau) / mp.sqrt(tau)))
            l = lambda x: mp.log(h(x))
            der = lambda x, n: mp.diff(l, x, n)
            # slope-coordinate quantities as functions of x; d/d(slope) = (c / v) d/dx
            Kc = lambda x: -der(x, 3) / (2 * der(x, 1) * der(x, 2) / c) - c
            slopeK = lambda x: der(x, 1) / c * Kc(x)
            for x in (mp.mpf("0.3"), mp.mpf(1), mp.mpf("2.5")):
                r, v, w, z = (der(x, n) for n in (1, 2, 3, 4))
                R, b = r * r, -w / r
                B, S = b - 2 * v, z + b * v - 2 * R * b
                d_slope = lambda fn: c / v * mp.diff(fn, x)
                errs = (Kc(x) - c * B / (2 * v),
                        d_slope(Kc) - c**2 * (B * R * b - S * v) / (2 * r * v**3),
                        d_slope(slopeK) - c * (B * (v * v + R * b) - S * v) / (2 * v**3))
                worst = max(worst, *(abs(e) for e in errs))
                signs = signs and B >= 0 and S >= 0 and S * v <= B * R * b
    if worst > mp.mpf(10)**-15:
        raise ValueError("slope-coordinate formulas")
    return {"largest_error": mp.nstr(worst, 3), "0<=Sv<=BRb_on_samples": signs}


if __name__ == "__main__":
    print(identity_as_printed())
    print(solvable_case())
    print(slope_coordinates())
