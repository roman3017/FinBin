import Mathlib

/-!
# Algebraic Core Lemmas

The pure ring-theoretic core of the obstruction argument: in a commutative ring,
a nilpotent element `t` makes `1 + t` a unit, so `z * (1 + t) = 0` forces `z = 0`.

## Main results

* `Finbin.nilpotent_cancel`: If `z * (1 + t) = 0` and `t` is nilpotent, then `z = 0`.

Ported from `brcm/archive/lean/cursor/unified_obstruction_aristotle_aristotle/`
`RequestProject/UnifiedObstruction/AlgebraicCore.lean`.
-/

namespace Finbin

/-- **Nilpotent unit cancellation**.
If `t` is nilpotent then `1 + t` is a unit, so `z * (1 + t) = 0` forces `z = 0`. -/
theorem nilpotent_cancel {R : Type*} [CommRing R] {z t : R}
    (hn : IsNilpotent t) (h : z * (1 + t) = 0) : z = 0 := by
  have hu : IsUnit (1 + t) := hn.isUnit_one_add
  rw [mul_comm] at h
  rwa [IsUnit.mul_right_eq_zero hu] at h

end Finbin
