"""Regression test for the Family M admissibility guard (external review, audit D-1).

(1) For every (n, b, l, c) with l+1 <= |X| = b+c+1 < g_C+1, certM.MFam.ok_c must return False
    (no coprime pair is guaranteed by L2).
(2) For |X| >= s0 = max(l+1, g_C+1), certM's R branch must never certify a case that the scanners' Family R
    (cert10.Cert8.R_with_X, independently implemented, skeleton pool s0) rejects.
(3) The scanners' own Family M (cert10.Cert8.M_ok_c) must return False whenever |X| < g_C+1.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cert10, certM

SS = ((5, 7, 11, 13), (5, 7), ())


def run(ns):
    spf = cert10.spf_table(max(ns))
    bad1 = bad2 = bad3 = checked1 = checked2 = 0
    for n in ns:
        for sg in SS:
            C = cert10.Cert8(n, spf, sig=sg, full_grid=False)
            M = certM.MFam(C)
            gc, h, m = C.gc, C.h, C.m
            for l in range(1, m + 1):
                for c in range(0, h + 1):
                    for b in range(0, C.bmax + 1):
                        X = b + c + 1
                        if l + 1 <= X < gc + 1:
                            checked1 += 1
                            if M.ok_c(b, l, c):
                                bad1 += 1
                        if X < gc + 1:
                            r = C.M_ok_c(b, l, c)
                            if r:
                                bad3 += 1
                        if X >= max(l + 1, gc + 1) and X - 1 <= C.bmax + h:
                            checked2 += 1
                            if M.ok_c(b, l, c) and not C.R_with_X(X, l):
                                bad2 += 1
    return dict(checked_guard=checked1, guard_violations=bad1, checked_R=checked2, R_violations=bad2, scanner_M_violations=bad3)


if __name__ == "__main__":
    ns = [int(x) for x in sys.argv[1:]] or [30, 48, 66, 79, 96, 120]
    r = run(ns)
    print(r)
    print("FAMILY_M_GUARD_OK" if r["guard_violations"] == r["R_violations"] == r["scanner_M_violations"] == 0 else "FAMILY_M_GUARD_FAIL")
