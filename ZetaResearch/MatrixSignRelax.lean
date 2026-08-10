import Zeta23.ZeroSide
import Zeta23.LinAlg

open Matrix Finset RHLinalg
open scoped BigOperators ComplexOrder

noncomputable section

namespace ZetaResearch

/-!
A finite-dimensional matrix sign-relaxation lemma.

The eventual target is to control an indefinite off-line contribution Q using only
its positive index.  The right finite-dimensional statement is that the positive
part of a Hermitian Q has rank equal to n_+(Q), hence any positive test matrix B
can see at most a rank-n_+(Q) positive contribution.
-/

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

-- Placeholder: this file will be filled with a kernel-checked statement after
-- inspecting the exact Mathlib/Zeta23 spectral API available at the pinned commit.

end ZetaResearch
