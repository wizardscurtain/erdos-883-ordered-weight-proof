"""Analytic tail for Theorem G (FAMILY_G.md): verifies, by a finite computation with explicit constants, that
N_GA(n) <= y1(n) - m(n) for EVERY n >= N0.  See ANALYTIC_TAIL_G.md for the derivation.

Bounds (v odd <= n, Q = odd primes <= z, P = 2*prod(Q), kappa = phi(P)/P, S(v) = Q-primes of v):
  N0(tau) := #{odd v <= n : G(v) <= tau} <= sum_S B_S(n, tau),
  B_S <= min{ n/(2 prod S) + 1,
              (n/2) dens(S) + Dp n^sig Us(S),
              min_s (tau/G(S))^s [ (n/2) dens(S) M_z(s) + Dp n^sig Us(S) C_sig(s) ]   (only if tau < G(S)) },
  dens(S) = prod_{p in S} 1/p prod_{p in Q-S} (1-1/p),  Us(S) = prod_{p in S} 1/(p^sig - 1),
  M_z(s) = prod_{p>z} (1 + h_s(p)/p),  C_sig(s) = prod_{p>z} (1 + h_s(p)/p^sig),  h_s(p) = (1-1/p)^{-s} - 1,
  Dp = max_y ( #{w <= y : (w,P)=1} - kappa y )  (one period scan).
For n >= N0 every error term n^sig, 1 is <= (n/2) * 2 N0^{sig-1} resp. (n/2) * 2/N0, giving N0(tau) <= (n/2) Phi(tau).
Shift: Gt_q(v) <= u  =>  G(v) <= u + e_sup,  e_sup = sup_{n>=N0} 2^{omega_max(n)}/sqrt(2q).
Low range (u <= u_mid): single Rankin over all odd primes with exponent s_low and n-decaying errors.
All floating quantities carry a relative safety factor (1 + 1e-9) in the conservative direction.
"""
import math, itertools, json, sys
import numpy as np

SAFE = 1 + 1e-9


def primes_upto(N):
    s = np.ones(N + 1, dtype=bool); s[:2] = False
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0]


PLIM = 10 ** 7
PR = primes_upto(PLIM).astype(np.float64)


def discrepancy(P, Q):
    """Dp = max over integers 0 <= y < P of C(y) - kappa*y, C(y) = #{1<=w<=y : gcd(w,P)=1}."""
    ok = np.ones(P + 1, dtype=bool); ok[0] = False
    for p in [2] + list(Q):
        ok[::p] = False
    C = np.cumsum(ok, dtype=np.int64)
    phi = int(C[P])
    kappa = phi / P
    y = np.arange(P + 1, dtype=np.float64)
    return float(np.max(C - kappa * y)), kappa, phi


def log_prod_bound(s, z, sig):
    """upper bound for log prod_{p>z} (1 + h_s(p)/p^sig) (sig=1 gives M_z(s))."""
    ps = PR[PR > z]
    h = np.power(1 - 1 / ps, -s) - 1
    val = float(np.sum(np.log1p(h / np.power(ps, sig))))
    # tail p > PLIM: h_s(p) <= s/(p-1) * (1-1/p)^{-s} <= 1.001 s/p for p > 1e7, s <= 1000 ;
    # sum_{p>X} p^{-1-sig} <= sum_{k>X} k^{-1-sig} <= X^{-sig}/sig
    val += 1.001 * s * (PLIM ** (-sig)) / sig
    return val * SAFE


def omega_jumps(limit_k=40):
    """odd primorials Pi_k = 3*5*...*p_k with k = number of odd primes; returns list of (Pi_k, k)."""
    out, prod, k = [], 1, 0
    for p in PR[1:]:
        p = int(p)
        prod *= p; k += 1
        out.append((prod, k))
        if k >= limit_k:
            break
    return out


def e_sup(N0, x_of_n):
    """sup_{n >= N0} 2^{omega_max(n)}/sqrt(x(n)); omega_max is constant between odd primorials and
    2^k/sqrt(Pi_k) decreases (Pi_{k+1}/Pi_k >= 5 > 4), so the sup is at N0 or at the next jump."""
    J = omega_jumps()
    k0 = max(k for P_, k in J if P_ <= N0)
    best = 2 ** k0 / math.sqrt(x_of_n(N0))
    for P_, k in J:
        if P_ > N0:
            best = max(best, 2 ** k / math.sqrt(x_of_n(P_)))
    return best * SAFE


def Gmin_at_jumps():
    J = omega_jumps()
    out, g = [], 1.0
    for (P_, k), p in zip(J, PR[1:]):
        g *= (1 - 1 / float(p))
        out.append((P_, k, g))
    return out


class Setup:
    def __init__(self, z, N0, sig=0.5, sgrid=None, u1=0.95, u_mid=0.33, s_low=4):
        self.z, self.N0, self.sig, self.u1, self.u_mid, self.s_low = z, N0, sig, u1, u_mid, s_low
        self.Q = [int(p) for p in PR if 3 <= p <= z]
        P = 2 * math.prod(self.Q)
        self.Dp, self.kappa, _ = discrepancy(P, self.Q)
        self.sgrid = sgrid or [1, 1.5, 2, 3, 4, 5, 6, 8, 10, 12, 15, 18, 22, 26, 30, 35, 40, 50, 60, 80]
        self.M = {s: math.exp(log_prod_bound(s, z, 1.0)) for s in self.sgrid}
        self.C = {s: math.exp(log_prod_bound(s, z, sig)) for s in self.sgrid}
        self.classes = []
        for r in range(len(self.Q) + 1):
            for S in itertools.combinations(self.Q, r):
                dens, G, prodS, Us = 1.0, 1.0, 1, 1.0
                for p in self.Q:
                    if p in S:
                        dens /= p; G *= (1 - 1 / p); prodS *= p; Us /= (p ** sig - 1)
                    else:
                        dens *= (1 - 1 / p)
                self.classes.append((dens * SAFE, G, prodS, Us * SAFE))
        self.errfac = 2 * N0 ** (sig - 1)          # n^sig <= (n/2) * errfac for n >= N0
        self.onefac = 2.0 / N0                     # 1 <= (n/2) * onefac

    def Phi(self, tau):
        """N0(tau) <= (n/2) Phi(tau) for every n >= N0."""
        tot = 0.0
        for dens, G, prodS, Us in self.classes:
            best = 1.0 / prodS + self.onefac
            best = min(best, dens + self.Dp * Us * self.errfac)
            if tau < G:
                th = tau / G
                for s in self.sgrid:
                    val = th ** s * (dens * self.M[s] + self.Dp * Us * self.C[s] * self.errfac)
                    if val < best:
                        best = val
            tot += best
        return tot * SAFE

    def verify(self, step=0.0005):
        N0 = self.N0
        delta = 1.0 / (N0 - 1)
        eq = e_sup(N0, lambda n: 2 * (n // 2))           # shift for Gt_q
        en = e_sup(N0, lambda n: 2 * n)                  # shift for Gt_n
        rep = dict(z=self.z, N0=N0, sig=self.sig, Dp=self.Dp, e_sup_q=eq, e_sup_n=en, u1=self.u1, u_mid=self.u_mid)
        # (A1-high): for u in [u_mid, u1]:  Phi(u + eq)(1 + delta) + 2 delta <= u^2  (checked on a grid, monotone)
        us = np.arange(self.u_mid, self.u1 + step / 2, step)
        worst = (9.0, None)
        for a, b in zip(us[:-1], us[1:]):
            lhs = self.Phi(b + eq) * (1 + delta) + 2 * delta
            mg = a * a - lhs
            if mg < worst[0]:
                worst = (mg, float(a))
        rep["A1_high_min_margin"], rep["A1_high_argmin"] = worst
        # (A2'): b_A <= Y1 + 1 - m, where b_A = max(N_A(t_1), max_{j>=2} N_A(t_j) - j + 2) is the least b with GA(b,m)
        #   (GA(b,l) is monotone in l and b; FAMILY_G.md GA2), t_j^2 = (n-T+m+j-1)/n <= 1/2 + 7/(6 N0) + xi, xi=(j-1)/n,
        #   j - 2 >= 2 q xi - 1.  Sufficient for xi in [xa, xb] (grid over [0, 1/6]):
        #   (1+delta) Phi(sqrt(1/2 + 7/(6N0) + xb) + en) - 2 xa + 3 delta <= u1^2 - 1/3
        eps0 = 7.0 / (6 * N0)
        xis = np.linspace(0.0, 1.0 / 6 + 1e-12, 401)
        worst2 = (9.0, None)
        for xa, xb in zip(xis[:-1], xis[1:]):
            lhs2 = (1 + delta) * self.Phi(math.sqrt(0.5 + eps0 + xb) * SAFE + en) - 2 * xa + 3 * delta
            mg = self.u1 ** 2 - 1.0 / 3 - lhs2
            if mg < worst2[0]:
                worst2 = (mg, float(xa))
        rep["A2_margin"], rep["A2_argmin_xi"] = worst2
        # (A1-low) and (A0): single Rankin over all odd primes, exponent s_low, for every n >= N0:
        #   tau^{s-2} (M_odd (1+delta) + 2(1+delta) N0^{sig-1} C_odd) + 1/(q Gmin^2) <= (1 - e/Gmin)^2 for
        #   tau in [Gmin(n), u_mid + eq];  sup of e/Gmin and of 1/(q Gmin^2) over n >= N0 taken at jumps.
        s = self.s_low
        Modd = math.exp(log_prod_bound(s, 2, 1.0))      # all odd primes (p > 2)
        Codd = math.exp(log_prod_bound(s, 2, self.sig))
        tau_hi = self.u_mid + eq
        lhs_low = tau_hi ** (s - 2) * (Modd * (1 + delta) + 2 * (1 + delta) * N0 ** (self.sig - 1) * Codd)
        J = Gmin_at_jumps()
        # on [Pi_k, Pi_{k+1}): omega_max = k, Gmin = g_k; sup of e/Gmin at the left end (q smallest)
        r_sup, inv_sup = 0.0, 0.0
        kN = max(k for P_, k, g in J if P_ <= N0)
        for P_, k, g in J:
            if k < kN:
                continue
            left = max(P_, N0)
            q = left // 2
            r_sup = max(r_sup, 2 ** k / math.sqrt(2 * q) / g)
            inv_sup = max(inv_sup, 1.0 / (q * g * g))
        rep["A1_low_lhs"] = lhs_low + inv_sup
        rep["A1_low_rhs"] = (1 - r_sup) ** 2
        rep["A1_low_margin"] = rep["A1_low_rhs"] - rep["A1_low_lhs"]
        rep["A0_ok"] = r_sup < 1
        rep["Modd"], rep["r_sup"] = Modd, r_sup
        rep["ALL_OK"] = bool(rep["A1_high_min_margin"] > 0 and rep["A2_margin"] > 0 and rep["A1_low_margin"] > 0 and rep["A0_ok"])
        return rep


if __name__ == "__main__":
    z, N0 = int(sys.argv[1]), int(float(sys.argv[2]))
    kw = {}
    for a in sys.argv[3:]:
        k, v = a.split("=")
        kw[k] = float(v) if k != "s_low" else int(v)
    S = Setup(z, N0, **kw)
    print(json.dumps(S.verify(), indent=1))
