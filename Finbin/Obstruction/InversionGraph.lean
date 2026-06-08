import Mathlib
import Finbin.Obstruction.AlgebraicCore

/-!
# Non-Representability of the Inversion Graph (matrix-equation abstraction)

For every odd prime `p`, the **inversion indicator** `f(x,y) = 𝟙[xy ≡ 1 (mod p)]`
on `ℤ/p × ℤ/p` has no polynomial representation of total degree `≤ p - 1` over any
commutative ring.

The proof uses a determinant-rank argument: the anchored mixed-difference relations
assemble into a matrix equation `D · (ΦAΦᵀ) · D = c · F`, where `ΦAΦᵀ` factors
through a space of dimension `p - 2 < p - 1`, forcing `det(ΦAΦᵀ) = 0`, while `F` is a
permutation matrix with `det(F) = ±1`. Taking determinants gives `c^(p-1) = 0`,
and the `(1,1)` entry gives the delta relation `c² · e = c`.

## Main results

* `Finbin.det_mul_eq_zero_of_card_lt`: determinant of a product through a smaller dimension is 0.
* `Finbin.inv_graph_core`: if `c² · e = c` and `c` is nilpotent, then `c = 0`.
* `Finbin.nilpotent_from_rank_deficient_matrix_eq`: nilpotency of the scalar from the matrix equation.
* `Finbin.inv_graph_no_rep`: the combined obstruction at the matrix-equation level.

Ported from `brcm/archive/lean/cursor/unified_obstruction_aristotle_aristotle/`
`RequestProject/UnifiedObstruction/InversionGraph.lean`.
-/

open Matrix

namespace Finbin

/-- If `A` is an `n × m` matrix and `B` is an `m × n` matrix with `m < n`, then
`det(A * B) = 0`. Proof via the Leibniz expansion: every function `f : n → m` is
non-injective (by pigeonhole), so the corresponding determinant of a matrix with
repeated rows vanishes. -/
theorem det_mul_eq_zero_of_card_lt {R : Type*} [CommRing R]
    {n m : Type*} [DecidableEq n] [DecidableEq m] [Fintype n] [Fintype m]
    (hlt : Fintype.card m < Fintype.card n)
    (A : Matrix n m R) (B : Matrix m n R) :
    (A * B).det = 0 := by
  have h_det : Matrix.det (A * B) = ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ) * ∑ f : n → m,
      (∏ i, A i (f i)) * (∏ i, B (f i) (σ i)) := by
    have h_det : Matrix.det (A * B) = ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ) *
        ∏ i, (∑ k, A i k * B k (σ i)) := by
      rw [Matrix.det_apply']
      refine Finset.sum_bij (fun σ _ => σ⁻¹) ?_ ?_ ?_ ?_ <;> simp +decide
      · exact fun b => ⟨b⁻¹, inv_inv b⟩
      · intro σ; rw [← Equiv.prod_comp σ⁻¹]; simp +decide [Matrix.mul_apply]
    simp +decide only [h_det, Finset.prod_sum, ← Finset.prod_mul_distrib]
    refine Finset.sum_congr rfl fun σ _ => congr_arg _ (Finset.sum_bij
      (fun f _ => fun i => f i (Finset.mem_univ i)) ?_ ?_ ?_ ?_) <;> simp +decide
    · simp +decide [funext_iff]
    · exact fun b => ⟨fun i _ => b i, rfl⟩
  have h_exchange : Matrix.det (A * B) = ∑ f : n → m, (∏ i, A i (f i)) *
      ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ) * (∏ i, B (f i) (σ i)) := by
    simp +decide only [h_det, Finset.mul_sum _ _ _, mul_left_comm]
    exact Finset.sum_comm
  have h_inner_det : ∀ f : n → m, ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ) *
      (∏ i, B (f i) (σ i)) = Matrix.det (Matrix.of (fun i j => B (f i) j)) := by
    intro f; rw [Matrix.det_apply']
    refine Finset.sum_bij (fun σ _ => σ⁻¹) ?_ ?_ ?_ ?_ <;> simp +decide
    · exact fun b => ⟨b⁻¹, inv_inv b⟩
    · intro σ; rw [← Equiv.prod_comp σ.symm]; simp +decide
  have h_noninjective : ∀ f : n → m, ∃ i j : n, i ≠ j ∧ f i = f j := by
    exact fun f => not_forall_not.mp fun h => hlt.not_ge <|
      Fintype.card_le_of_injective f fun i j hij =>
        Classical.not_not.1 fun hi => h i <| by tauto
  rw [h_exchange, Finset.sum_eq_zero]
  intro f _; obtain ⟨i, j, hij, h⟩ := h_noninjective f
  rw [h_inner_det f, Matrix.det_zero_of_row_eq hij]
  · simp
  · exact funext fun k => by simp +decide [h]

/-- **Algebraic core of the inversion graph obstruction**.

Given `c, e ∈ R` with the delta relation `c² * e = c` and `c` nilpotent (`c ^ k = 0`),
then `c = 0`. -/
theorem inv_graph_core {R : Type*} [CommRing R] {d₀₁ e : R} {k : ℕ}
    (hdelta : d₀₁ ^ 2 * e = d₀₁)
    (hnil : d₀₁ ^ k = 0) :
    d₀₁ = 0 := by
  have h_eq : d₀₁ * (1 - d₀₁ * e) = 0 := by linear_combination -hdelta
  set t : R := -d₀₁ * e
  have h_t : d₀₁ * (1 + t) = 0 := by grind
  have h_t_nil : t ^ k = 0 := by rw [mul_pow, neg_pow, hnil]; norm_num
  exact nilpotent_cancel ⟨k, h_t_nil⟩ h_t

/-- **Nilpotency from a rank-deficient matrix equation**.

If `D * (Φ A Φᵀ) * D = c • F` with `Φ A Φᵀ` factoring through a space of dimension
`m < n` and `F` of unit determinant, then `c ^ (card n) = 0`. -/
theorem nilpotent_from_rank_deficient_matrix_eq {R : Type*} [CommRing R]
    {n m : Type*} [DecidableEq n] [DecidableEq m] [Fintype n] [Fintype m]
    (hlt : Fintype.card m < Fintype.card n)
    {Φ : Matrix n m R} {A : Matrix m m R}
    {D F : Matrix n n R} {c : R}
    (hmat : D * (Φ * A * Φᵀ) * D = c • F)
    (hdet_F : IsUnit F.det) :
    c ^ Fintype.card n = 0 := by
  apply_fun Matrix.det at hmat;
  simp_all +decide [Matrix.det_mul];
  rw [ ← hdet_F.mul_left_inj ];
  rw [ ← hmat, det_mul_eq_zero_of_card_lt hlt ] ; ring

/-- **Full inversion graph obstruction** (matrix-equation abstraction).

If `D * (Φ A Φᵀ) * D = c • F` with rank deficiency and `det F` a unit, and the delta
relation `c² * e = c` holds, then `c = 0`. -/
theorem inv_graph_no_rep {R : Type*} [CommRing R]
    {n m : Type*} [DecidableEq n] [DecidableEq m] [Fintype n] [Fintype m]
    (hlt : Fintype.card m < Fintype.card n)
    {Φ : Matrix n m R} {A : Matrix m m R}
    {D F : Matrix n n R} {c e : R}
    (hmat : D * (Φ * A * Φᵀ) * D = c • F)
    (hdet_F : IsUnit F.det)
    (hdelta : c ^ 2 * e = c) :
    c = 0 := by
  exact inv_graph_core hdelta (nilpotent_from_rank_deficient_matrix_eq hlt hmat hdet_F)

end Finbin
