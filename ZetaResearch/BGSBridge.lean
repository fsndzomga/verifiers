import Zeta23.ZeroSide

open Complex

noncomputable section

namespace ZetaResearch

/-- The reflected pair variable used by the unconditional Montgomery form factor
of Baluyot--Goldston--Suriajaya--Turnage-Butterbaugh. -/
def bgsPairArg (rho rho' : ℂ) : ℂ := rho + star rho' - 1

/-- Exact dictionary between the BGS reflected variable and Anthropic's
complex ordinate `gammaOf`.

If `rho = 1/2 + delta + i gamma` and `rho' = 1/2 + delta' + i gamma'`,
then the left side is `delta + delta' + i(gamma-gamma')`, while
`gammaOf rho - conj (gammaOf rho')` is `(gamma-gamma') - i(delta+delta')`.
Thus multiplication by `i` identifies the two variables exactly. -/
theorem bgsPairArg_eq_I_mul_gammaDiff (rho rho' : ℂ) :
    bgsPairArg rho rho' = I * (Zeta23.gammaOf rho - star (Zeta23.gammaOf rho')) := by
  apply Complex.ext <;> simp [bgsPairArg, Zeta23.gammaOf] <;> ring

/-- The Fourier argument `i * (rho + conj rho' - 1)` is the negative of the
Anthropic complex-ordinate difference. -/
theorem I_mul_bgsPairArg_eq_neg_gammaDiff (rho rho' : ℂ) :
    I * bgsPairArg rho rho' = -(Zeta23.gammaOf rho - star (Zeta23.gammaOf rho')) := by
  rw [bgsPairArg_eq_I_mul_gammaDiff]
  ring_nf

/-- Equivalently, the Anthropic difference is `-i` times the BGS variable. -/
theorem gammaDiff_eq_neg_I_mul_bgsPairArg (rho rho' : ℂ) :
    Zeta23.gammaOf rho - star (Zeta23.gammaOf rho') = -I * bgsPairArg rho rho' := by
  rw [bgsPairArg_eq_I_mul_gammaDiff]
  ring_nf

/-- On the critical line the bridge reduces to the ordinary real ordinate
difference. -/
theorem gammaDiff_of_re_eq_half
    {rho rho' : ℂ} (hrho : rho.re = 1 / 2) (hrho' : rho'.re = 1 / 2) :
    Zeta23.gammaOf rho - star (Zeta23.gammaOf rho') = ((rho.im - rho'.im : ℝ) : ℂ) := by
  rw [Zeta23.gammaOf_of_re_eq_half hrho, Zeta23.gammaOf_of_re_eq_half hrho']
  simp

/-- Correspondingly the reflected BGS variable is purely imaginary on the
critical line. -/
theorem bgsPairArg_of_re_eq_half
    {rho rho' : ℂ} (hrho : rho.re = 1 / 2) (hrho' : rho'.re = 1 / 2) :
    bgsPairArg rho rho' = I * ((rho.im - rho'.im : ℝ) : ℂ) := by
  rw [bgsPairArg_eq_I_mul_gammaDiff, gammaDiff_of_re_eq_half hrho hrho']

end ZetaResearch
