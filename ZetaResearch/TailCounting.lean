import ZetaResearch.NegativeTail
import Zeta23.Assembly

open Matrix RHLinalg
open scoped ComplexOrder

noncomputable section

namespace ZetaResearch

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A negative positive-semidefinite tail may be absorbed into the Hermitian
error block without spending any positive-index budget.  Consequently the
usual zero-count rank core survives unchanged.

This is the matrix version of the Cohn--Elkies / CGdL sign relaxation: a
Fourier tail with the favorable sign should enter as `-N`, `N ⪰ 0`; once such
a representation is obtained analytically, no extra off-line pair penalty is
needed in the rank argument. -/
theorem psd_tail_counting_core
    {A P Q N : Matrix n n ℂ}
    (hA : A = P + Q - N)
    (hP : P.PosSemidef) (hQ : Q.IsHermitian) (hN : N.PosSemidef)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b)
    {Non NI : ℝ}
    (htrP : rtrace P ≤ Non)
    (hcount : Non + 2 * (b : ℝ) ≤ NI)
    (htrA : NI ≤ rtrace A) :
    2 * NI - frobSq A ≤ (r : ℝ) := by
  have hQtail : (Q - N).IsHermitian := hQ.sub hN.isHermitian
  have hidx : posIndex hQtail ≤ b :=
    (posIndex_sub_posSemidef_le hQ hN).trans hb
  have hdecomp : A = P + (Q - N) := by
    rw [hA]
    abel
  have hcore := Zeta23.Assembly.zeroside_rank_core
    hdecomp hP hQtail hr hidx htrP hcount
  linarith

/-- Numerical CGdL endpoint with a rank-free PSD tail.  If the sign-relaxed
matrix has trace at least the zero count and Frobenius square at most
`1.3208 N`, then at least `67.92%` of the rank budget is forced. -/
theorem psd_tail_cgdL_13208
    {A P Q N : Matrix n n ℂ}
    (hA : A = P + Q - N)
    (hP : P.PosSemidef) (hQ : Q.IsHermitian) (hN : N.PosSemidef)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b)
    {Non NI : ℝ}
    (htrP : rtrace P ≤ Non)
    (hcount : Non + 2 * (b : ℝ) ≤ NI)
    (hNI : 0 ≤ NI)
    (htrA : NI ≤ rtrace A)
    (hfrob : frobSq A ≤ (1651 / 1250 : ℝ) * NI) :
    (849 / 1250 : ℝ) * NI ≤ (r : ℝ) := by
  have h := psd_tail_counting_core hA hP hQ hN hr hb htrP hcount htrA
  norm_num at hfrob ⊢
  linarith

end ZetaResearch
