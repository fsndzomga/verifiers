import ZetaResearch.NegativeTail
import Zeta23.LinAlg.RankTrace

open Matrix RHLinalg
open scoped ComplexOrder

noncomputable section

namespace ZetaResearch

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A negative-semidefinite contribution coming from the critical-line channel
can be moved into the error block without increasing its positive index.

This is the algebraic fact needed for complex/signed windows: the line
contribution may be `Pplus - Pminus` rather than PSD, while only `Pplus`
consumes the rank budget. -/
theorem rank_trace_with_negative_line_part
    {A Pplus Pminus Q : Matrix n n ℂ}
    (hA : A = Pplus - Pminus + Q)
    (hPplus : Pplus.PosSemidef) (hPminus : Pminus.PosSemidef)
    (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : Pplus.rank ≤ r) (hb : posIndex hQ ≤ b)
    {c : ℝ} (hc : 0 < c) :
    c * rtrace Pplus - c ^ 2 / 4 * (r : ℝ)
      + 2 * c * rtrace (Q - Pminus) - c ^ 2 * (b : ℝ)
      ≤ frobSq A := by
  have hQm : (Q - Pminus).IsHermitian := hQ.sub hPminus.isHermitian
  have hidx : posIndex hQm ≤ b :=
    (posIndex_sub_posSemidef_le hQ hPminus).trans hb
  have hrt := rank_trace_ineq hPplus hQm hr hidx hc
  have hsum : Pplus + (Q - Pminus) = A := by
    rw [hA]
    abel
  rw [hsum] at hrt
  exact hrt

/-- `c = 2` form of the preceding theorem.  The formula has exactly the same
shape as Anthropic's ordinary rank-counting core, except that `Pminus` has
already been absorbed into the Hermitian error block. -/
theorem rank_two_with_negative_line_part
    {A Pplus Pminus Q : Matrix n n ℂ}
    (hA : A = Pplus - Pminus + Q)
    (hPplus : Pplus.PosSemidef) (hPminus : Pminus.PosSemidef)
    (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : Pplus.rank ≤ r) (hb : posIndex hQ ≤ b) :
    2 * rtrace Pplus + 4 * rtrace (Q - Pminus)
      - 4 * (b : ℝ) - frobSq A ≤ (r : ℝ) := by
  have h := rank_trace_with_negative_line_part hA hPplus hPminus hQ hr hb
    (c := 2) (by norm_num)
  norm_num at h ⊢
  linarith

/-- Full counting endgame with a hyperbolic critical-line contribution.

If `A = Pplus - Pminus + Q`, `Pplus` has rank at most the number `r` of
distinct line zeros, `Pminus` is merely PSD, and the off-line block `Q` has
positive index at most `b`, then the usual zero-count hypotheses imply exactly
the same lower bound as in the PSD-line case:

`2 NI - frobSq A ≤ r`.

Thus a negative PSD line channel is *free* for the rank method; this removes the
main linear-algebra obstruction to using a complex spectral factor for a signed
Fourier density. -/
theorem hyperbolic_line_counting_core
    {A Pplus Pminus Q : Matrix n n ℂ}
    (hA : A = Pplus - Pminus + Q)
    (hPplus : Pplus.PosSemidef) (hPminus : Pminus.PosSemidef)
    (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : Pplus.rank ≤ r) (hb : posIndex hQ ≤ b)
    {Non NI : ℝ}
    (htrP : rtrace Pplus ≤ Non)
    (hcount : Non + 2 * (b : ℝ) ≤ NI)
    (htrA : NI ≤ rtrace A) :
    2 * NI - frobSq A ≤ (r : ℝ) := by
  have hrt := rank_two_with_negative_line_part hA hPplus hPminus hQ hr hb
  have htrace : rtrace A = rtrace Pplus - rtrace Pminus + rtrace Q := by
    rw [hA, rtrace_add, rtrace_sub]
  rw [rtrace_sub] at hrt
  linarith

end ZetaResearch
