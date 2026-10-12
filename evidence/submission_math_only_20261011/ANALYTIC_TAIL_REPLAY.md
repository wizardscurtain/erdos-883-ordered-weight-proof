# Fresh analytic-tail replay and mathematical supplement

Date: 2026-10-11. Prepared for Cecil Jentges's mathematical-only submission.

## Executed result

The exact 6,969-byte `hall_tail_20261010/code/analytic_interval.py` from mathematical snapshot `66321f74ed35db1df594fd026ae3b2c50bc9528d` was reconstructed locally, verified against Git blob `d716b1a27bbdd5a01cf91738e79bf79397e6a52f`, and executed without mathematical source changes. It returned exit code 0 and `ALL_OK: true` in 139.44432544708252 seconds. Environment: Python 3.13.5, NumPy 2.3.5, mpmath 1.3.0, interval precision 100 bits.

The adjacent `analytic_interval_replay.json` contains the actual output. Displayed decimal values are approximate; the pass/fail decisions were made using intervals before conversion to display floats.

- A0: true.
- A1 high-range margin: approximately 0.02454513441320001.
- A1 low-range margin: approximately 0.3646407884916685.
- A2 margin: approximately 0.05896440285042424.
- Exact periodic discrepancy: 2799708/323323.

The high-range grid covers 1,140 rational cells; the GA grid covers 400 rational cells. This is a replay of uniform bounding inequalities, not a simulation at one large n.

## Infinite primorial continuation

Let P=P_k be an odd primorial and p the next odd prime. The next q-shift divided by the current q-shift has squared ratio

4(P-1)/(pP-1) < 4/p < 1 for p>=5.

For the ratio of the shift to g_k=product(1-1/p), its squared successive ratio is

4p^2(P-1)/((p-1)^2(pP-1)) < 4p/(p-1)^2 < 1 for p>=7.

For 1/(floor(n/2)*g_k^2), the corresponding ratio is

p^2(P-1)/((p-1)^2(pP-1)) < p/(p-1)^2 < 1 for p>=3.

Within each primorial interval these quantities decrease as n increases. The first relevant interval begins at N0=100000000, not at P_7=4849845; the next begins at P_8=111546435. Comparing those endpoints therefore controls all later intervals. No claim about the infinite tail depends on simply assuming that the finite primorial loop continues to behave as observed.

## Euler-product tails

For 0<s<=80 and p>X=10000000, use -log(1-x)<=x/(1-x) and exp(t)-1<=t/(1-t), 0<=t<1. They give

h_s(p)=(1-1/p)^(-s)-1 <= s/(p-1-s) <= (s/p)*p/(p-81) < 1.001*s/p.

The last bound is checked by integer cross-multiplication at X and improves for larger p. Together with log(1+y)<=y and the integral bound for sum_(m>X) m^(-1-tau), this gives the implemented Euler-product tail upper bound 1.001*s*X^(-tau)/tau, for tau=1 or 1/2. Intermediate prime buckets use exact prime counts and a decreasing positive summand.

## Period and grid-to-theorem justification

The discrepancy with P=9699690 is periodic, and its maximum occurs at an integer endpoint. The exact numerator P*C(y)-phi(P)*y has magnitude below P^2<2^63, justifying the stated integer scan.

For q=floor(n/2), m=floor(n/6), delta=1/(N0-1), one has n/(2q)<=1+delta, 1/q<=2delta and m<=q/3+1/6. Phi is nondecreasing. Consequently the interval upper bound at the right endpoint of an A1 cell, compared with the squared left endpoint and the 2*delta reserve, bounds every y represented by that cell. The low-range Rankin estimate uses the uniform primorial bounds above, and shift/g_k<1 establishes A0.

For GA, T(n)>=2n/3-7/6 and xi=(j-1)/n give t_j^2<=1/2+7/(6N0)+xi. Also j-2>=2q*xi-1 and Y+1-m>=0.81*q-q/3-1/6. The 3*delta reserve in each GA cell is at least (7/6)/q, so the checked inequalities imply b_A<=Y+1-m. With the A1 inequalities through Y, this supplies the analytic sufficient criterion for every n>=100000000.

## Small wording correction

The manuscript's rounded phrase 'A2 margin >=0.059' overstates the displayed interval lower margin. Read it as 'approximately 0.059' or use the conservative 'greater than 0.058'. The positive-sign criterion is unchanged. The original source remains frozen; this dated supplement records the correction.

## Scope and trust

This is a fresh execution plus AI-assisted mathematical source analysis, not an external human endorsement or organizer acceptance. It supports the analytic component for n>=100000000. The 99 SAT/LRAT instances, all finite scanners, and the block-certificate set were not freshly rerun in this execution. Neither an all-n Lean proof nor a full new all-n verification is claimed. Interpreter, NumPy integer operations, mpmath interval arithmetic and the mathematical reductions remain in the stated trust base.
