import Mathlib

/-!
# Canonical notion of polynomial embedding

The three results of this project are phrased in three different ways in their original
sources.  This file introduces a single canonical notion, `Finbin.EmbedsInDegree`, into
which all three are translated (see `Finbin.Bridge`).

A function `f : Xᵏ → X` *embeds in degree `d`* when there is a commutative ring `R`, an
injective `j : X → R`, and a `k`-variable polynomial `g` over `R` of total degree at most
`d` such that `j` intertwines `f` with the polynomial map `g`:
`j (f v) = g(j ∘ v)` for every `v : Fin k → X`.

This is the formal analogue of enlarging the alphabet of a cellular automaton (`j`) so that
the transition function `f` becomes the restriction of a polynomial map.
-/

open MvPolynomial

namespace Finbin

/-- `f : (Fin k → X) → X` embeds into a polynomial of total degree `≤ d`: there is an
injective `j : X → R` into a commutative ring `R` and a `k`-variable polynomial `g` over `R`
of total degree `≤ d` with `j (f v) = g (j ∘ v)` for all `v`. -/
def EmbedsInDegree {k : ℕ} {X : Type} (f : (Fin k → X) → X) (d : ℕ) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (j : X → R) (g : MvPolynomial (Fin k) R),
    Function.Injective j ∧ g.totalDegree ≤ d ∧
    ∀ v : Fin k → X, j (f v) = MvPolynomial.eval (fun i => j (v i)) g

/-- Embeddability is monotone in the degree bound. -/
theorem EmbedsInDegree.mono {k : ℕ} {X : Type} {f : (Fin k → X) → X} {d d' : ℕ}
    (h : EmbedsInDegree f d) (hdd : d ≤ d') : EmbedsInDegree f d' := by
  obtain ⟨R, inst, j, g, hj, hdeg, he⟩ := h
  exact ⟨R, inst, j, g, hj, hdeg.trans hdd, he⟩

/-- The **inversion indicator** on `ZMod p`, as a binary function in `Fin 2 → ZMod p` form:
`f(x, y) = 1` if `x * y = 1` and `0` otherwise. -/
def invIndicator (p : ℕ) : (Fin 2 → ZMod p) → ZMod p :=
  fun v => if v 0 * v 1 = 1 then 1 else 0

end Finbin
