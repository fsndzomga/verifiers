import ZetaResearch.NegativeTail

open Matrix RHLinalg
open scoped ComplexOrder

noncomputable section

namespace ZetaResearch

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Minimal record target.**  To obtain an unconditional record it is not
necessary to reach the much stronger CGdL value `0.6792`.  A corrected matrix
with normalized trace at least one and Frobenius-square constant `1.32749`
already gives `0.67251`, which strictly exceeds the published decimal
benchmark `0.6725007`.

The PSD correction costs no additional positive-index budget. -/
theorem record_67251_psd_tail_target
    {Ahat P Q N : Matrix n n ℂ}
    (hPQ : Ahat = P + Q) (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (hN : N.PosSemidef)
    {r b : ℕ} (hrank : P.rank ≤ r) (hpos : posIndex hQ ≤ b)
    {Non NI : ℝ} (htrP : rtrace P ≤ Non) (hNcount : Non + 2 * b ≤ NI)
    (htr : NI ≤ rtrace (Ahat - N))
    (hfrob : frobSq (Ahat - N) ≤ (132749 / 100000 : ℝ) * NI) :
    (67251 / 100000 : ℝ) * NI ≤ r := by
  have hcore := zeroside_rank_core_psd_tail
    hPQ hP hQ hN hrank hpos htrP hNcount
  norm_num at hcore ⊢
  linarith

/-- The same arithmetic endpoint without a correction matrix. -/
theorem record_67251_rank_target
    {Ahat P Q : Matrix n n ℂ}
    (hPQ : Ahat = P + Q) (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hrank : P.rank ≤ r) (hpos : posIndex hQ ≤ b)
    {Non NI : ℝ} (htrP : rtrace P ≤ Non) (hNcount : Non + 2 * b ≤ NI)
    (htr : NI ≤ rtrace Ahat)
    (hfrob : frobSq Ahat ≤ (132749 / 100000 : ℝ) * NI) :
    (67251 / 100000 : ℝ) * NI ≤ r := by
  have hcore := Zeta23.Assembly.zeroside_rank_core
    hPQ hP hQ hrank hpos htrP hNcount
  norm_num at hcore ⊢
  linarith

/-- Exact margin over the displayed Anthropic benchmark: `0.0000093` in
proportion, i.e. `0.00093` percentage points. -/
theorem record_67251_margin_over_anthropic :
    (67251 / 100000 : ℝ) - (6725007 / 10000000 : ℝ)
      = 93 / 10000000 := by
  norm_num

/-- Equivalently, relative to the rounded Frobenius constant `1.3274993`, one
only needs to save `0.0000093` in the normalized Frobenius square to certify
`67.251%`. -/
theorem record_67251_required_frob_saving :
    (13274993 / 10000000 : ℝ) - (132749 / 100000 : ℝ)
      = 93 / 10000000 := by
  norm_num

end ZetaResearch
