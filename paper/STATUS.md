# PSD-tail route: paper status

This directory records the status of the research extension built on Anthropic's `zeta-23-lean` formalization.

## What is proved

The scratch development kernel-checks the following finite-dimensional facts.

1. A reflected off-critical-line pair is hyperbolic rather than positive-semidefinite, so a direct scalar transfer of an RH pair-correlation kernel is not valid.
2. If `Q` is Hermitian and `N` is positive-semidefinite, then `n_+(Q-N) <= n_+(Q)`. Thus a favorable negative Fourier tail represented by `-N` costs no additional positive-index budget.
3. If `A = P + Q - N`, with the usual rank and reflected-pair counting hypotheses, then
   `2 NI - frobSq A <= r`.
4. Consequently, `frobSq A <= 1.3208 NI` and `tr A >= NI` force `r >= 0.6792 NI`.
5. A finite nonnegative form-factor quadrature `N = sum_t w_t u_t u_t^*`, `w_t >= 0`, is positive-semidefinite and plugs directly into this endpoint.
6. The reflected complex variable of the unconditional Montgomery form factor and Anthropic's complex ordinate satisfy the exact identity
   `rho + conj(rho') - 1 = i * (gammaOf rho - conj(gammaOf rho'))`.
7. `AnalyticTarget.lean` states the exact remaining finite-dimensional analytic seam as `analytic_formFactor_bridge_implies_6792`: any nonnegative form-factor tail with the required decomposition, counting, trace, and `1.3208` Frobenius hypotheses forces the complete 67.92% endgame.

Relevant Lean files are `TransferObstruction.lean`, `MatrixSignRelax.lean`, `SignedMatrixRelax.lean`, `FrameMultiplier.lean`, `OfflineSignedBridge.lean`, `TwoSidedInertia.lean`, `NegativeTail.lean`, `MultiRankTrace.lean`, `HyperbolicLine.lean`, `TailCounting.lean`, `FormFactorTail.lean`, `BGSBridge.lean`, and `AnalyticTarget.lean`.

## What is not yet proved

There is not yet a stronger unconditional theorem for the Riemann zeta function. In particular, 67.92% must not be stated as an unconditional result at this stage.

The remaining theorem is analytic: construct the favorable sign-relaxed Fourier tail as a positive-semidefinite matrix-valued form factor in the same finite family used by the zeta zero-side matrix, and prove after normalization

- `tr A >= (1-o(1)) N(T,2T)`, and
- `frobSq A <= (1.3208+o(1)) N(T,2T)`.

The main known loss in the current prime-side argument occurs in `Zeta23/PrimeSideB/PPOffDiag.lean`: the difference-frequency contribution is decomposed into eight oscillatory Montgomery-Vaughan sums and their absolute values are added. The resulting `O(L^2 X)` term prevents a fixed bandwidth exponent `lambda > 1` from being used directly.

The proposed route is therefore to regroup before this triangle-inequality step and identify the favorable signed Fourier tail with the nonnegative unconditional reflected form factor. The exact BGS/Anthropic variable identity is now formalized, but positivity of the continuous form factor has not yet been transferred to the required finite grid kernel with the needed trace/Frobenius estimates.

## Paper claim discipline

A current paper can rigorously claim a new formalized matrix mechanism and an exact analytic reduction to a 67.92% endpoint. It cannot claim a new unconditional numerical record until the analytic bridge above is proved.
