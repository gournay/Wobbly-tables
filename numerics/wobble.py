"""Numerical experiments for Sections 4 and 5 of the paper (tex/); floating point, not certified.

(The tables of Theorem 5.7 and Proposition 5.8, which wobble at every angle, are certified by
numerics/always_wobbles.py. The `counterexample` command below reproduces an earlier, uncertified
numerical example of an isosceles trapezoid which wobbles at every angle, which is not in the current
version of the paper; its radial slope correction is stored in counterexample_trap4_beta.txt.)

Model (Section 4): table with feet on the unit circle (r = 1), position (theta, q, c),
foot E at horizontal position x_E = u_E - Phi_{u_E}(q), height z_E = c + u_E.q, where
u_E = R_theta a_E.  The equal hovering tilt q is the fixed point of Q_theta (Prop. 4.4),
the wobbling function is w_AC = sum_E c_E g(x_E) (Prop. 4.8) with
(c_A, c_B, c_C, c_D) = (tau, -mu, 1 - tau, -(1 - mu)).

Usage:
    python3 wobble.py hexagon          # Prop. 5.4, Cor. 5.5: orbit sums of w_3 vanish for the hexagon table
    python3 wobble.py counterexample   # earlier example: w_AC > 0 for all angles (trapezoid, 4 in K)
    python3 wobble.py counterexample --lp   # recompute the radial slope B by linear programming
    python3 wobble.py hexsearch L [seed]    # CMA-ES search for an always-wobbling terrain for the hexagon table

Requires numpy and scipy (and cma for hexsearch).
"""
import sys
import numpy as np

HERE = __file__.rsplit('/', 1)[0] if '/' in __file__ else '.'


# ---------------------------------------------------------------- tables
def table(*angles):
    """Feet at the given angles (cyclic order A, B, C, D) on the unit circle; returns a, tau, mu."""
    th = np.array(angles, dtype=float)
    a = np.stack([np.cos(th), np.sin(th)], 1)
    A, B, C, D = a
    tau, mu = np.linalg.solve(np.array([A - C, -(B - D)]).T, D - C)   # X = tau A + (1-tau) C = mu B + (1-mu) D
    return a, tau, mu


def trapezoid(alpha, beta):
    """Isosceles trapezoid A = alpha, B = -alpha, C = -beta, D = beta (0 < alpha < beta < pi)."""
    return table(alpha, -alpha, -beta, beta)


def m(k, a, tau, mu):
    """m(k) = -sum_E c_E e^{i k theta_E}; F_0 = -sum_k m(k) hat(gamma)(k) e^{ik theta}."""
    tE = np.arctan2(a[:, 1], a[:, 0])
    cE = np.array([tau, -mu, 1 - tau, -(1 - mu)])
    return -(cE * np.exp(1j * k * tE)).sum()


# ---------------------------------------------------------------- nonlinear model (Section 4)
def wobble(g, a, tau, mu, N=4096, iters=400):
    """Wobbling function w_AC on N equally spaced angles (fixed point iteration of Prop. 4.4)."""
    th = np.linspace(0, 2 * np.pi, N, endpoint=False)
    c, s = np.cos(th), np.sin(th)
    u = np.stack([np.stack([c * a[E, 0] - s * a[E, 1], s * a[E, 0] + c * a[E, 1]], -1) for E in range(4)])
    Minv = np.linalg.inv(np.stack([u[0] - u[2], u[1] - u[3]], 1))
    q = np.zeros((N, 2))

    def feet(q):
        f = 1 / (1 + np.sqrt(1 - (q * q).sum(-1)))
        return u - (f * (u * q).sum(-1))[..., None] * q[None]

    for _ in range(iters):
        x = feet(q)
        G = g(x[..., 0], x[..., 1])
        qn = np.einsum('nij,nj->ni', Minv, np.stack([G[0] - G[2], G[1] - G[3]], -1))
        done = np.abs(qn - q).max() < 1e-18
        q = qn
        if done:
            break
    x = feet(q)
    G = g(x[..., 0], x[..., 1])
    return th, tau * G[0] + (1 - tau) * G[2] - mu * G[1] - (1 - mu) * G[3], q


# ---------------------------------------------------------------- third order term (Prop. 5.2)
def w3_pieces(a, tau, mu, gamma, dgamma, N):
    """w_3(theta) = T(theta) + sum_E W_E(theta) beta(theta + theta_E), beta = radial derivative of g_1 on the circle."""
    th = np.linspace(0, 2 * np.pi, N, endpoint=False)
    tE = np.arctan2(a[:, 1], a[:, 0])
    cE = np.array([tau, -mu, 1 - tau, -(1 - mu)])
    phi = th[None, :] + tE[:, None]
    u = np.stack([np.cos(phi), np.sin(phi)], -1)
    Ju = np.stack([-np.sin(phi), np.cos(phi)], -1)
    gam, dgam = gamma(phi), dgamma(phi)
    M = np.stack([u[0] - u[2], u[1] - u[3]], 1)
    q0 = np.linalg.solve(M, np.stack([gam[0] - gam[2], gam[1] - gam[3]], -1)[..., None])[..., 0]
    uq = (u * q0[None]).sum(-1)
    Juq = (Ju * q0[None]).sum(-1)
    T = -0.5 * (cE[:, None] * uq * dgam * Juq).sum(0)
    W = -0.5 * cE[:, None] * uq ** 2
    return th, phi, T, W


def trig(coef, J, p):
    return sum(coef[j] * np.cos(j * p) for j in range(J + 1)) + sum(coef[J + j] * np.sin(j * p) for j in range(1, J + 1))


def lp_best_beta(T, W, phi, J, bound=100.0):
    """Maximise min_theta w_3 over trigonometric polynomials beta of degree J (linear programme)."""
    from scipy.optimize import linprog
    A = np.array([(W * np.cos(j * phi)).sum(0) for j in range(J + 1)]
                 + [(W * np.sin(j * phi)).sum(0) for j in range(1, J + 1)]).T
    n, N = A.shape[1], A.shape[0]
    res = linprog(np.r_[np.zeros(n), -1.0], A_ub=np.c_[-A, np.ones(N)], b_ub=T,
                  bounds=[(-bound, bound)] * n + [(None, None)], method='highs')
    return res.x[:n], -res.fun


# ---------------------------------------------------------------- experiments
def hexagon():
    a, tau, mu = table(0, np.pi / 3, 2 * np.pi / 3, np.pi)
    print("hexagon table: tau = %.4f, mu = %.4f" % (tau, mu))
    print("degenerate modes k <= 24:", [k for k in range(25) if abs(m(k, a, tau, mu)) < 1e-12])
    rng = np.random.default_rng(0)
    N, J = 1440, 20
    for k in (5, 6, 7):
        b = rng.normal(size=2)
        gamma = lambda p: np.cos(k * p) + b[0] * np.cos(p) + b[1] * np.sin(p)
        dgamma = lambda p: -k * np.sin(k * p) - b[0] * np.sin(p) + b[1] * np.cos(p)
        th, phi, T, W = w3_pieces(a, tau, mu, gamma, dgamma, N)
        w3 = T + (W * trig(rng.normal(size=2 * J + 1), J, phi)).sum(0)
        orbit = sum(np.roll(w3, -j * N // 6) for j in range(6))
        print("k = %d: max|w_3| = %.3g, max|sum_j w_3(theta + j pi/3)| = %.1e" % (k, abs(w3).max(), abs(orbit).max()))


def counterexample(recompute=False):
    ca = 0.6
    cb = (np.sqrt(23) - 3) / 10                      # cos^2 a + cos a cos b + cos^2 b = 1/2  <=>  4 in K
    a, tau, mu = trapezoid(np.arccos(ca), np.arccos(cb))
    print("trapezoid: cos(alpha) = 3/5, cos(beta) = (sqrt 23 - 3)/10, |m(4)| = %.1e, diagonals %.4f %.4f"
          % (abs(m(4, a, tau, mu)), np.linalg.norm(a[0] - a[2]), np.linalg.norm(a[1] - a[3])))
    k, J = 4, 64
    gamma = lambda p: np.cos(k * p) + np.cos(p)       # g_1 on the circle: Re z^4 + x
    dgamma = lambda p: -k * np.sin(k * p) - np.sin(p)
    fname = HERE + '/counterexample_trap4_beta.txt'
    if recompute:
        th, phi, T, W = w3_pieces(a, tau, mu, gamma, dgamma, 1440)
        coef, val = lp_best_beta(T, W, phi, J)
        np.savetxt(fname, coef, header='beta(phi) = sum_{j=0}^{64} c_j cos(j phi) + sum_{j=1}^{64} c_{64+j} sin(j phi)')
        print("LP: min w_3 = %.4f on the LP grid" % val)
    coef = np.loadtxt(fname)
    th, phi, T, W = w3_pieces(a, tau, mu, gamma, dgamma, 20000)
    w3 = T + (W * trig(coef, J, phi)).sum(0)
    print("third order term on 20000 angles: min w_3 = %.4f, max w_3 = %.2f" % (w3.min(), w3.max()))
    B = lambda p: trig(coef, J, p) - k * np.cos(k * p) - np.cos(p)   # radial slope correction

    for eps in (2.5e-3, 6.25e-4, 2e-5, 1e-5):
        def g(X, Y, eps=eps):
            ph = np.arctan2(Y, X)
            return eps * (np.real((X + 1j * Y) ** k) + X + (np.sqrt(X * X + Y * Y) - 1) * B(ph))
        th, w, q = wobble(g, a, tau, mu, N=20000)
        print("nonlinear, eps = %.2e: min w/eps^3 = %.4f, max w/eps^3 = %.2f" % (eps, w.min() / eps ** 3, w.max() / eps ** 3))


# ---------------------------------------------------------------- hexagon: nonlinear search (cf. Section 5.6)
def hexagon_search(L_target, seed=0, maxfevals=6000, N=240, K_modes=10):
    """CMA-ES search for a terrain with Lipschitz constant L_target (on the disc of radius 1.05) such that the
    hexagonal table wobbles at every angle; objective = min_theta w / max_theta |w| (a counterexample needs > 0)."""
    import cma
    a, tau, mu = table(0, np.pi / 3, 2 * np.pi / 3, np.pi)

    def basis(X, Y):
        Z = X + 1j * Y
        R2 = X * X + Y * Y - 1
        cols = []
        for k in range(1, K_modes + 1):
            cols += [np.real(Z ** k), np.imag(Z ** k)]
        for k in range(0, K_modes + 1):
            cols += [R2 * np.real(Z ** k)] + ([R2 * np.imag(Z ** k)] if k > 0 else [])
        return np.stack(cols, -1)

    rr, tt = np.meshgrid(np.linspace(0, 1.05, 22), np.linspace(0, 2 * np.pi, 97))
    X0, Y0 = (rr * np.cos(tt)).ravel(), (rr * np.sin(tt)).ravel()
    h = 1e-6
    Dx = (basis(X0 + h, Y0) - basis(X0 - h, Y0)) / (2 * h)
    Dy = (basis(X0, Y0 + h) - basis(X0, Y0 - h)) / (2 * h)
    nb = Dx.shape[1]

    def normalise(c):
        lip = np.sqrt((Dx @ c) ** 2 + (Dy @ c) ** 2).max()
        return c * (L_target / lip)

    def ratio(c):
        c = normalise(np.asarray(c))
        g = lambda X, Y: basis(X, Y) @ c
        th, w, q = wobble(g, a, tau, mu, N=N, iters=100)
        return w.min() / np.abs(w).max(), c, w

    rng = np.random.default_rng(seed)
    es = cma.CMAEvolutionStrategy(rng.normal(size=nb), 0.7,
                                  {'seed': seed + 1, 'maxfevals': maxfevals, 'verbose': -9})
    best = (-2, None, None)
    while not es.stop():
        X = es.ask()
        vals = []
        for x in X:
            r, c, w = ratio(x)
            vals.append(-r)
            if r > best[0]:
                best = (r, c, w)
        es.tell(X, vals)
    r, c, w = best
    idx = np.arange(N // 6)
    orb = np.array([[w[(i + j * N // 6) % N] for j in range(6)] for i in idx])
    orbit_ratio = np.abs(orb.sum(1)).max() / np.abs(w).max()
    return r, orbit_ratio, c


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'hexagon'
    if cmd == 'hexagon':
        hexagon()
    elif cmd == 'hexsearch':
        L = float(sys.argv[2]); seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
        r, orb, c = hexagon_search(L, seed)
        print("hexagon search L = %.2f seed %d: best min w / max |w| = %.4f (counterexample needs > 0); "
              "max orbit ratio |sum_j w(theta_j)| / max|w| = %.3g" % (L, seed, r, orb))
    elif cmd == 'counterexample':
        counterexample(recompute='--lp' in sys.argv)
    else:
        print(__doc__)
