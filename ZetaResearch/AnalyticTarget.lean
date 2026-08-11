import ZetaResearch.FormFactorTail

open Matrix RHLinalg
open scoped ComplexOrder

noncomputable section

namespace ZetaResearch

variable {n s : Type*} [Fintype n] [DecidableEq n] [Fintype s] [DecidableEq s]

/-- **Exact verified analytic seam.** This theorem states the finite-dimensional
input that a new unconditional form-factor argument must construct.  Once the
weights are nonnegative, the corrected zero-side matrix has the usual
critical-line/off-line decomposition, and its trace and Frobenius square meet
the `1.3208` target, the `67.92%` endpoint is automatic.

The theorem itself is unconditional finite-dimensional linear algebra.  The
remaining open analytic task is to instantiate these hypotheses from the zeta
explicit formula and the unconditional reflected form factor. -/
theorem analytic_formFactor_bridge_implies_6792
    {A P Q : Matrix n n ℂ}
    (weights : s → ℝ) (vectors : s → n → ℂ)
    (hweights : ∀ t, 0 ≤ weights t)
    (hA : A = P + Q - frameOperator weights vectors)
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {rankBudget pairBudget : ℕ}
    (hrank : P.rank ≤ rankBudget) (hidx : posIndex hQ ≤ pairBudget)
    {nOn nI : ℝ}
    (htraceP : rtrace P ≤ nOn)
    (hcount : nOn + 2 * (pairBudget : ℝ) ≤ nI)
    (hnI : 0 ≤ nI)
    (htraceA : nI ≤ rtrace A)
    (hfrob : frobSq A ≤ (1651 / 1250 : ℝ) * nI) :
    (849 / 1250 : ℝ) * nI ≤ (rankBudget : ℝ) := by
  exact finite_formFactor_tail_cgdL weights vectors hweights hA hP hQ
    hrank hidx htraceP hcount hnI htraceA hfrob

/-- The arithmetic margin between 67.92% and Anthropic's 67.25007% benchmark
is 0.66993 percentage points.  This is the available asymptotic error budget
before the new endpoint ceases to improve the benchmark. -/
theorem cgdL_margin_over_anthropic :
    (849 / 1250 : ℝ) - (6725007 / 10000000 : ℝ) = 66993 / 10000000 := by
  norm_num

end ZetaResearch
