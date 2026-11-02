"""Certified computations for Section 5.5 of the paper (tex/): tables which wobble at every angle
(Theorem 5.7 and Proposition 5.8).

For a table with a degenerate mode k (m(k) = 0), the terrain is (on the closed unit disc, z = x + iy)

    g = eps * g1 + eps^3 * g3,
    g1 = Re z^k + (1/2) (|z|^2 - 1) Re(b z^{2k}),
    g3 = Re(a_{2k} z^{2k} + a_{3k} z^{3k} + a_{4k} z^{4k}),

where b is chosen so that the mean kappa'(b) of the third order term is large, and a_{2k}, a_{3k}, a_{4k}
cancel the modes 2k, 3k, 4k of the third order term w_3 (Proposition 5.6); the coefficients
of g3 are rounded to 3 decimals.  For each example, the script checks with interval arithmetic
(mpmath.iv) that
  1. m(0) = m(1) = m(k) = 0, and the closed formulas of Lemma 5.3(e) and Proposition 5.6;
  2. W_3 = w_3 + F_0[g3] (the third order term of Proposition 5.2) is bounded below by W3min > 0:
     the Fourier coefficients of W_3 are computed exactly (as intervals) by a discrete Fourier transform of
     64 samples, which is exact since W_3 is a trigonometric polynomial of degree 4k < 32;
  3. the remainder bound R(eps) of Proposition 5.2 satisfies R(eps0) < eps0^3 W3min, and (4.3) holds at eps0.
Since R(eps)/eps^3 is non-decreasing in eps, w_AC(theta) > 0 for all theta and all 0 < eps <= eps0: the
table wobbles at every angle (Lemma 4.7).

Examples:
  * trapezoid: the isosceles trapezoid (equal diagonals) with feet e^{i alpha}, e^{-i alpha}, e^{-i beta},
    e^{i beta}, cos(alpha) = 3/5, cos(beta) = (sqrt 23 - 3)/10; k = 4, b = 6i  (Theorem 5.7);
  * unequal diagonals: the table whose feet are the four zeros of 2 cos(2 theta) - 2 cos(theta + pi/6) + 1/2
    (the case chi = pi/6 of Lemma 5.3(f)), labelled A, B, C, D in the order -21.2, 44.5, 101.8, 234.9 degrees;
    k = 5, b = -80 e^{i pi/6}  (Proposition 5.8).
With --nonlinear, w_AC is also computed directly (floating point, fixed point iteration of Prop. 4.4).

Usage:  python3 always_wobbles.py [--nonlinear]
"""
import sys
from mpmath import iv, mpf, nint

iv.dps = 40
I = iv.mpc(0, 1)
PI = iv.pi
N_DFT = 64


def conj(z):
    return iv.mpc(z.real, -z.imag)


def as_c(z):
    return z if hasattr(z, '_mpci_') else iv.mpc(z)


def contains_zero(z):
    z = as_c(z)
    return z.real.a <= 0 <= z.real.b and z.imag.a <= 0 <= z.imag.b


def width(z):
    z = as_c(z)
    return max(z.real.b - z.real.a, z.imag.b - z.imag.a)


def fmt(z):
    z = as_c(z)
    re, im = float(z.real.mid), float(z.imag.mid)
    return "%.6f" % re if abs(im) < 1e-12 else "%.6f%+.6fi" % (re, im)


def rnd(x, digits=3):
    """Round a real interval to a decimal number (exact interval)."""
    return iv.mpf(int(nint(mpf(x.mid) * 10 ** digits))) / 10 ** digits


def f(s):
    return 1 / (1 + iv.sqrt(1 - s))


def certify(name, e, k, b, eps0, W3min):
    """e = [e_A, e_B, e_C, e_D] (interval complex numbers on the unit circle, in cyclic order)."""
    print("=" * 100)
    print(name)
    D1, D2 = e[0] - e[2], e[1] - e[3]
    Delta = (conj(D1) * D2).imag                                 # det(D1, D2)
    # X = tau A + (1 - tau) C = mu B + (1 - mu) D:  tau D1 - mu D2 = e_D - e_C
    R_ = e[3] - e[2]
    tau = ((conj(R_) * D2).imag) / Delta
    mu = ((conj(R_) * D1).imag) / Delta
    c = [tau, -mu, 1 - tau, -(1 - mu)]

    def m(j):
        return -sum(cE * eE ** j for cE, eE in zip(c, e))

    for j in (0, 1, k):
        assert contains_zero(m(j)) and width(m(j)) < 1e-25, (j, m(j))
    assert not contains_zero(m(2))
    d1, d2 = abs(D1), abs(D2)
    dmin = d1 if d1.b <= d2.b else d2
    cosphi = (D1.real * D2.real + D1.imag * D2.imag) / (d1 * d2)
    K = iv.sqrt(2 / (1 - abs(cosphi)))
    print("tau = %s, mu = %s, diagonals %s and %s, K = %s; m(0), m(1), m(%d) contain 0"
          % (fmt(tau), fmt(mu), fmt(d1), fmt(d2), fmt(K), k))

    def XY(j):
        """Idealised tilt for gamma = Re(zeta e^{ij phi}): p = X zeta + Y conj(zeta) in the frame of the table."""
        E1, E2 = e[0] ** j - e[2] ** j, e[1] ** j - e[3] ** j
        return (D2 * E1 - D1 * E2) / (2 * I * Delta), (D2 * conj(E1) - D1 * conj(E2)) / (2 * I * Delta)

    # ------------------------------------------------ closed forms
    X, Y = XY(k)
    for u, v in ((X, m(k - 1) / conj(m(2))), (Y, conj(m(k + 1)) / conj(m(2)))):
        assert contains_zero(u - v) and width(u - v) < 1e-25
    assert contains_zero((m(2) * m(k - 1) * conj(m(k + 1))).real)
    print("xi_+ = X = m(k-1)/conj m(2) = %s, xi_- = Y = conj m(k+1)/conj m(2) = %s, Re(m(2) m(k-1) conj m(k+1)) contains 0"
          % (fmt(X), fmt(Y)))
    S = -m(2 * k + 2) * conj(X) ** 2 - 2 * m(2 * k) * conj(X) * Y - m(2 * k - 2) * Y ** 2
    kappa = -(b * S).real / 8
    Ak = iv.mpf(k) / 4 * (2 * m(k - 2) * X * Y + conj(m(k - 2)) * conj(Y) ** 2)
    coef = {2 * k: b / 4 * ((abs(X) ** 2 + abs(Y) ** 2) * m(2 * k) + X * Y * m(2 * k - 2) + conj(X * Y) * m(2 * k + 2)),
            3 * k: iv.mpf(k) / 4 * m(k - 2) * X ** 2,
            4 * k: b / 8 * (X ** 2 * m(2 * k - 2) + 2 * X * conj(Y) * m(2 * k) + conj(Y) ** 2 * m(2 * k + 2))}
    a_exact = {j: coef[j] / m(j) for j in coef}
    a = {j: iv.mpc(rnd(v.real), rnd(v.imag)) for j, v in a_exact.items()}
    print("b = %s: kappa'(b) = %s, |A_%d| = %s, |S|/8 = %s" % (fmt(b), fmt(kappa), k, fmt(abs(Ak)), fmt(abs(S) / 8)))
    for j in sorted(a):
        print("  mode %2d of w_3: %s; |m(%d)| = %s; a_%d = %s, rounded to %s"
              % (j, fmt(coef[j]), j, fmt(abs(m(j))), j, fmt(a_exact[j]), fmt(a[j])))
    closed_min = kappa - abs(Ak) - sum(abs(m(j)) * abs(a[j] - a_exact[j]) for j in a)
    print("closed form: W_3 = kappa' + Re(A_k e^{ik theta}) + (rounding) >= %s" % mpf(closed_min.a))

    # ------------------------------------------------ W_3 by an exact (interval) DFT
    def W3_sample(theta):
        rot = iv.mpc(iv.cos(theta), iv.sin(theta))
        zeta = rot ** k
        q0 = rot * (X * zeta + Y * conj(zeta))                   # q_0(theta)
        total = iv.mpf(0)
        for cE, eE in zip(c, e):
            u = rot * eE
            grad = conj(k * u ** (k - 1)) + (b * u ** (2 * k)).real * u        # gradient of g1 on the circle
            total += -cE * (conj(grad) * q0).real * (conj(u) * q0).real / 2   # w_3
            total += cE * sum((aj * u ** j).real for j, aj in a.items())      # F_0[g3]
        return total

    assert 4 * k < N_DFT // 2
    samples = [W3_sample(2 * PI * n / N_DFT) for n in range(N_DFT)]
    F = [sum(samples[n] * iv.mpc(iv.cos(2 * PI * n * j / N_DFT), -iv.sin(2 * PI * n * j / N_DFT))
             for n in range(N_DFT)) / N_DFT for j in range(N_DFT // 2 + 1)]
    # W_3(theta) = F_0 + sum_{j >= 1} 2 Re(F_j e^{ij theta}), exactly
    assert contains_zero(F[0] - kappa) and contains_zero(2 * F[k] - Ak)
    big = [j for j in range(1, N_DFT // 2 + 1) if abs(F[j]).b > 1e-3]
    dft_min = F[0].real - 2 * sum(abs(F[j]) for j in range(1, N_DFT // 2 + 1))
    print("DFT: mean = %s, 2 F_%d = %s (= A_%d), modes j >= 1 with |F_j| > 1e-3: %s, min W_3 >= %s"
          % (fmt(F[0]), k, fmt(2 * F[k]), k, big, mpf(dft_min.a)))
    assert dft_min.a > W3min and closed_min.a > W3min

    # ------------------------------------------------ remainder bound (Proposition 5.2)
    L1 = k + abs(b)                                  # sup |grad g1| on the disc
    M1 = k * (k - 1) + (4 * k + 1) * abs(b)          # sup ||D^2 g1|| on the disc
    L3 = sum(j * abs(v) for j, v in a.items())       # sup |grad g3| on the disc
    P = abs(X) + abs(Y)                              # sup |q_0|
    P3 = sum(abs(v) * (abs(XY(j)[0]) + abs(XY(j)[1])) for j, v in a.items())    # sup |q_0^(3)|

    def remainder(eps):
        L = eps * L1 + eps ** 3 * L3
        t0 = L * K
        ok = t0.b <= 0.5 and (4 / iv.sqrt(3) / dmin * t0 ** 2).b < 1          # (4.3)
        t1 = eps * P + eps ** 3 * P3 + 2 * K * L * f(t0 ** 2) * t0 ** 2 / dmin
        if t1.b > t0.a:
            t1 = t0
        Phi1 = f(t1 ** 2) * t1 ** 2
        delta = eps ** 3 * P3 + 2 * K * L * Phi1 / dmin
        DPhi = (f(t1 ** 2) - iv.mpf(1) / 2) * t1 ** 2 + (t1 + eps * P) * delta / 2
        return ok, eps * M1 * Phi1 ** 2 + 2 * eps * L1 * DPhi + 2 * eps ** 3 * L3 * Phi1, L

    eps0 = iv.mpf(eps0)
    ok, R, L = remainder(eps0)
    print("constants: L1 = %s, M1 = %s, L3 <= %.3f, P = %s, P3 <= %.3f"
          % (fmt(L1), fmt(M1), float(L3.b), fmt(P), float(P3.b)))
    print("eps0 = %s: (4.3) holds: %s, Lipschitz constant <= %.4f, R(eps0)/eps0^3 <= %.4f < %s"
          % (mpf(eps0.mid), ok, float(L.b), float((R / eps0 ** 3).b), W3min))
    assert ok and (R / eps0 ** 3).b < W3min
    print("=> w_AC(theta) > 0 for all theta and all 0 < eps <= %s" % mpf(eps0.mid))
    return dict(tau=tau, mu=mu, a=a)


def float_table(e):
    import numpy as np
    return np.array([[float(z.real.mid), float(z.imag.mid)] for z in e])


def nonlinear(e, k, b, a, eps_list):
    import numpy as np
    sys.path.insert(0, __file__.rsplit('/', 1)[0] if '/' in __file__ else '.')
    from wobble import table, wobble
    feet = float_table(e)
    at, tau, mu = table(*np.arctan2(feet[:, 1], feet[:, 0]))
    bf = complex(float(b.real.mid), float(b.imag.mid))
    af = {j: complex(float(v.real.mid), float(v.imag.mid)) for j, v in a.items()}
    for eps in eps_list:
        def g(x, y, eps=eps):
            z = x + 1j * y
            g1 = np.real(z ** k) + 0.5 * (x * x + y * y - 1) * np.real(bf * z ** (2 * k))
            g3 = sum(np.real(v * z ** j) for j, v in af.items())
            return eps * g1 + eps ** 3 * g3
        th, w, q = wobble(g, at, tau, mu, N=8192)
        print("  nonlinear, eps = %.4f: min w_AC/eps^3 = %.5f, max w_AC/eps^3 = %.5f"
              % (eps, w.min() / eps ** 3, w.max() / eps ** 3))


# ---------------------------------------------------------------- example 1: trapezoid, equal diagonals
ca, sa = iv.mpf(3) / 5, iv.mpf(4) / 5
cb = (iv.sqrt(iv.mpf(23)) - 3) / 10
sb = iv.sqrt(1 - cb ** 2)
assert contains_zero(ca ** 2 + ca * cb + cb ** 2 - iv.mpf(1) / 2)
e_trap = [iv.mpc(ca, sa), iv.mpc(ca, -sa), iv.mpc(cb, -sb), iv.mpc(cb, sb)]
b_trap = iv.mpc(0, 6)
res1 = certify("Trapezoid cos(alpha) = 3/5, cos(beta) = (sqrt 23 - 3)/10 (equal diagonals), k = 4, "
               "g1 = Re z^4 - 3(|z|^2 - 1) Im z^8", e_trap, 4, b_trap, '4e-3', 1.43)


# ---------------------------------------------------------------- example 2: unequal diagonals, k = 5
def feet_chi(chi, n_grid=720, steps=140):
    """The four zeros of G(theta) = 2 cos(2 theta) - 2 cos(theta + chi) + cos(2 chi) in [-pi/2, 3 pi/2),
    certified by sign changes (G is a trigonometric polynomial of degree 2, so it has at most 4 zeros)."""
    Gv = lambda t: 2 * iv.cos(2 * t) - 2 * iv.cos(t + chi) + iv.cos(2 * chi)
    brackets = []
    for n in range(n_grid):
        lo, hi = -PI / 2 + 2 * PI * n / n_grid, -PI / 2 + 2 * PI * (n + 1) / n_grid
        lo, hi = iv.mpf(lo.a), iv.mpf(hi.a)
        glo, ghi = Gv(lo), Gv(hi)
        if glo.b < 0 < ghi.a or ghi.b < 0 < glo.a:
            brackets.append([lo, hi])
    assert len(brackets) == 4, len(brackets)
    roots = []
    for lo, hi in brackets:
        neg_lo = Gv(lo).b < 0
        for _ in range(steps):
            mid = iv.mpf(((lo + hi) / 2).mid)
            gm = Gv(mid)
            if gm.b < 0:
                lo, hi = (mid, hi) if neg_lo else (lo, mid)
            elif gm.a > 0:
                lo, hi = (lo, mid) if neg_lo else (mid, hi)
            else:
                break
        roots.append(iv.mpf([lo.a, hi.b]))
    return roots


chi = PI / 6
thetas = feet_chi(chi)
e_uneq = [iv.mpc(iv.cos(t), iv.sin(t)) for t in thetas]
print("=" * 100)
print("feet of the table with unequal diagonals (degrees):", [round(float((t * 180 / PI).mid), 4) for t in thetas])
# s_3 = 2 s_1 s_2 - s_1^3 for the polynomial z^4 - e^{i chi} z^3 + cos(2 chi) z^2 - e^{-i chi} z + 1 (so 5 is degenerate)
s1, s2, s3 = iv.mpc(iv.cos(chi), iv.sin(chi)), iv.cos(2 * chi), iv.mpc(iv.cos(chi), -iv.sin(chi))
assert contains_zero(s3 - (2 * s1 * s2 - s1 ** 3))
# b = 80 conj(S)/|S| direction = -80 e^{i pi/6}
b_uneq = -40 * iv.mpc(iv.sqrt(3), 1)
res2 = certify("Unequal diagonals: feet = zeros of 2cos(2t) - 2cos(t + pi/6) + 1/2, k = 5, "
               "g1 = Re z^5 - 40(|z|^2 - 1) Re(e^{i pi/6} z^10)", e_uneq, 5, b_uneq, '1e-3', 0.5)

if '--nonlinear' in sys.argv:
    print("=" * 100)
    print("trapezoid:")
    nonlinear(e_trap, 4, b_trap, res1['a'], (0.02, 0.01, 0.004, 0.002))
    print("table with unequal diagonals:")
    nonlinear(e_uneq, 5, b_uneq, res2['a'], (0.004, 0.002, 0.001))
