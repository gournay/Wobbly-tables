"""Physical size and robustness of the always wobbling trapezoid (Remark 5.9(f) of the paper, tex/).

1. For the terrain of Theorem 5.7 and larger eps (outside the range of the theorem), the minimal wobble
   min_theta w_AC (fixed point iteration of Prop. 4.4, r = 1), the maximal slope and the height of the
   terrain; multiply lengths by r (e.g. r = 100 mm) for a physical table.
2. Moving the rotation axis by delta (in 8 directions): min over theta and over the directions of
   w_AC / eps^3.  The table stops wobbling at every angle for delta ~ 0.15 eps^2 r.
3. With --optimise: re-optimise eps and the coefficients of g1 (b) and g3 for a prescribed maximal slope
   (Nelder-Mead, slow).

Usage: python3 physical.py [--optimise]
"""
import sys, math
import numpy as np
from wobble import table, wobble

ca, cb = 3 / 5, (math.sqrt(23) - 3) / 10
al, be = math.acos(ca), math.acos(cb)
AT, TAU, MU = table(al, -al, -be, be)
P0 = [6, 0, 4.970, -5.138, 0, 0, 4.173]          # b = 6i, a_8 = 4.970 i, a_12 = -5.138, a_16 = 4.173 i


def terrain(eps, p=P0, v=0j):
    """eps g1 + eps^3 g3 on the unit disc (g1 = Re z^4 + (|z|^2-1)/2 Re(i b z^8)), extended radially,
    seen from the axis through v."""
    bb, a8r, a8i, a12r, a12i, a16r, a16i = p
    a = {8: a8r + 1j * a8i, 12: a12r + 1j * a12i, 16: a16r + 1j * a16i}

    def g(x, y):
        x, y = x + v.real, y + v.imag
        rr = np.sqrt(x * x + y * y)
        s = np.where(rr > 1, 1 / np.maximum(rr, 1e-300), 1.0)
        x, y = x * s, y * s
        z = x + 1j * y
        g1 = np.real(z ** 4) + 0.5 * (x * x + y * y - 1) * np.real(1j * bb * z ** 8)
        return eps * g1 + eps ** 3 * sum(np.real(c * z ** j) for j, c in a.items())
    return g


XS = np.linspace(-1, 1, 401)
X, Y = np.meshgrid(XS, XS)
DISC = X ** 2 + Y ** 2 <= 1


def slope_height(g):
    G = g(X, Y)
    gy, gx = np.gradient(G, XS[1] - XS[0])
    return np.sqrt(gx ** 2 + gy ** 2)[DISC].max(), G[DISC].max() - G[DISC].min()


def min_wobble(g, N=4096, iters=2000):
    th, w, q = wobble(g, AT, TAU, MU, N=N, iters=iters)
    return w.min(), np.abs(q).max()


print("1. terrain of Theorem 5.7 (r = 1; for r = 100 mm multiply lengths by 100 to get mm)")
for eps in [0.004, 0.02, 0.04, 0.06, 0.08, 0.1, 0.12]:
    g = terrain(eps)
    m, qm = min_wobble(g)
    L, h = slope_height(g)
    print("  eps = %.3f: min w = %.3e (min w/eps^3 = %6.3f), max slope %.3f (%4.1f deg), height %.4f, max tilt %.1f deg"
          % (eps, m, m / eps ** 3, L, math.degrees(math.atan(L)), h, math.degrees(math.asin(min(qm, 1)))))

print("2. moving the axis by delta: min over theta and 8 directions of w_AC / eps^3")
for eps in [0.004, 0.02, 0.06, 0.08]:
    row = []
    for d in [0, 1e-6, 3e-6, 1e-5, 3e-5, 1e-4, 3e-4, 1e-3, 3e-3]:
        m = min(min_wobble(terrain(eps, v=d * np.exp(1j * t)), N=2048, iters=800)[0]
                for t in np.linspace(0, 2 * np.pi, 8, endpoint=False))
        row.append("delta=%.0e: %.2f" % (d, m / eps ** 3))
    print("  eps = %.3f: " % eps + ", ".join(row))

if '--optimise' in sys.argv:
    from scipy.optimize import minimize
    print("3. re-optimised terrains with maximal slope S")
    for S in [0.2, 0.35, 0.5]:
        def obj(p):
            if p[0] <= 0:
                return 1
            g = terrain(p[0], p[1:])
            return -min_wobble(g, N=512, iters=500)[0] + 10 * max(0, slope_height(g)[0] - S)
        r = minimize(obj, [0.03] + P0, method='Nelder-Mead',
                     options={'maxiter': 1500, 'xatol': 1e-4, 'fatol': 1e-10})
        g = terrain(r.x[0], r.x[1:])
        m, qm = min_wobble(g, iters=4000)
        L, h = slope_height(g)
        print("  S = %.2f: eps = %.4f, min w = %.3e, max slope %.3f (%.1f deg), height %.4f, parameters %s"
              % (S, r.x[0], m, L, math.degrees(math.atan(L)), h, np.round(r.x[1:], 3)))
