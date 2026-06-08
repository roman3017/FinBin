import Finbin.Embedding
import Finbin.UnaryLinear
import Finbin.QuarticDelta
import Finbin.Obstruction.Quartic

/-!
# Bridges to the canonical embedding notion

The three results, originally stated with three different formalizations, are translated
here into the single canonical notion `Finbin.EmbedsInDegree`:

* `Finbin.embedsInDegree_unary`     — every unary `f : ZMod n → ZMod n` embeds in degree 1.
* `Finbin.embedsInDegree_kronecker` — every binary Kronecker delta embeds in degree 4.
* `Finbin.not_embedsInDegree_invIndicator` — the inversion indicator on `ZMod p`
  (`p` prime) does not embed in degree `p - 1`.
* `Finbin.arbitrary_degree_obstruction` — for every `d` there is a binary function that
  embeds in no degree `d`.
-/

open MvPolynomial

namespace Finbin

/-- **Unary linear embedding**, in canonical form: every `f : ZMod n → ZMod n`, viewed as a
function `Fin 1 → ZMod n → ZMod n`, embeds into a polynomial of degree `1`. -/
theorem embedsInDegree_unary {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) :
    EmbedsInDegree (fun v : Fin 1 → ZMod n => f (v 0)) 1 := by
  obtain ⟨m, a, j, _hm, hj, hlin⟩ := linear_representation f
  refine ⟨ZMod m, inferInstance, j, MvPolynomial.C a * MvPolynomial.X 0, hj, ?_, ?_⟩
  · rw [MvPolynomial.C_mul_X_eq_monomial]
    refine le_trans (MvPolynomial.totalDegree_monomial_le _ _) ?_
    simp
  · intro v
    rw [hlin (v 0)]
    simp

/-- **Degree-four embedding of binary Kronecker deltas**, in canonical form. -/
theorem embedsInDegree_kronecker {n : ℕ} [NeZero n] (a b : ZMod n) :
    EmbedsInDegree (fun v : Fin 2 → ZMod n => kronecker_delta n a b (v 0, v 1)) 4 := by
  obtain ⟨m, g, ⟨j, hjrep⟩, hdeg⟩ := quartic_d n a b
  refine ⟨ZMod m, inferInstance, (j : ZMod n → ZMod m), g, j.injective, hdeg, ?_⟩
  intro v
  have hconv : (fun i => (j : ZMod n → ZMod m) (v i)) = (![j (v 0), j (v 1)] : Fin 2 → ZMod m) := by
    funext i; fin_cases i <;> simp
  rw [hconv, hjrep (v 0) (v 1)]

/-- **No degree-`(p-1)` embedding of the inversion indicator** on `ZMod p`, in canonical
form, for every prime `p`. -/
theorem not_embedsInDegree_invIndicator {p : ℕ} (hp : p.Prime) :
    ¬ EmbedsInDegree (invIndicator p) (p - 1) := by
  rintro ⟨R, _inst, j, g, hj, hdeg, heval⟩
  apply thm_invp hp j hj g hdeg
  intro x y
  have h := heval ![x, y]
  rw [show (![j x, j y] : Fin 2 → R) = fun i => j (![x, y] i) from by
        funext i; fin_cases i <;> simp, ← h]
  simp [invIndicator]

/-- **Arbitrarily large degree is required**: for every `d` there is a binary function that
embeds into no polynomial of degree `d`. The witness is the inversion indicator on `ZMod p`
for a prime `p > d` (so that `d ≤ p - 1`, the degree ruled out by the obstruction). -/
theorem arbitrary_degree_obstruction (d : ℕ) :
    ∃ p : ℕ, p.Prime ∧ ¬ EmbedsInDegree (invIndicator p) d := by
  obtain ⟨p, hp_ge, hp_prime⟩ := (d + 1).exists_infinite_primes
  refine ⟨p, hp_prime, fun h => ?_⟩
  exact not_embedsInDegree_invIndicator hp_prime (h.mono (by omega))

end Finbin
