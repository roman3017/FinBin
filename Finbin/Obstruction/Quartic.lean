import Mathlib
import Finbin.Obstruction.InversionGraph

/-!
# Non-Representability of the Inversion Graph: Quartic and General Cases

* `Finbin.thm_quartic`: the inversion indicator on `ℤ/5` has no polynomial representation
  of total degree ≤ 4 over any commutative ring.
* `Finbin.thm_invp`: for any prime `p`, the inversion indicator on `ℤ/p` has no
  polynomial representation of total degree ≤ `p - 1` over any commutative ring.

Ported from `brcm/archive/lean/cursor/unified_obstruction_aristotle_aristotle/`
`RequestProject/UnifiedObstruction/QuarticInvp.lean`.
-/

open MvPolynomial Matrix Finset

-- The ports below were originally checked under Lean v4.28/v4.29; under v4.30 a few of
-- the heavier `simp`/`aesop` steps need a larger heartbeat budget.
set_option maxHeartbeats 1000000

namespace Finbin

noncomputable section

/-! ### Mixed difference factorization for bivariate polynomials -/

/-- The "Newton divided difference" or geometric partial sum:
`newtonDiff a b n = ∑_{i=0}^{n-1} b^i * a^{n-1-i}`, so that
`b^n - a^n = (b - a) * newtonDiff a b n`. -/
def newtonDiff {R : Type*} [CommRing R] (a b : R) (n : ℕ) : R :=
  ∑ i ∈ Finset.range n, b ^ i * a ^ (n - 1 - i)

/-- Key factorization: `b^n - a^n = (b - a) * newtonDiff a b n`. -/
theorem pow_sub_eq_mul_newtonDiff {R : Type*} [CommRing R] (a b : R) (n : ℕ) :
    b ^ n - a ^ n = (b - a) * newtonDiff a b n := by
  unfold newtonDiff
  rw [mul_comm]
  exact (geom_sum₂_mul b a n).symm

/-
The evaluation of a bivariate polynomial at `![a, b]` expressed as a sum
over the support.
-/
theorem eval_fin2_eq_sum {R : Type*} [CommRing R]
    (q : MvPolynomial (Fin 2) R) (a b : R) :
    MvPolynomial.eval ![a, b] q =
    q.support.sum (fun m => MvPolynomial.coeff m q * a ^ (m 0) * b ^ (m 1)) := by
  rw [ MvPolynomial.eval_eq' ];
  simp +decide [ mul_assoc, Fin.prod_univ_two ]

/-
The mixed difference of a bivariate polynomial evaluation factors as
a sum of products of differences.
-/
theorem eval_mixed_diff_eq {R : Type*} [CommRing R]
    (q : MvPolynomial (Fin 2) R) (a b c d : R) :
    MvPolynomial.eval ![b, d] q - MvPolynomial.eval ![a, d] q -
    MvPolynomial.eval ![b, c] q + MvPolynomial.eval ![a, c] q =
    q.support.sum (fun m =>
      MvPolynomial.coeff m q * (b ^ (m 0) - a ^ (m 0)) * (d ^ (m 1) - c ^ (m 1))) := by
  rw [ eval_fin2_eq_sum, eval_fin2_eq_sum, eval_fin2_eq_sum, eval_fin2_eq_sum ];
  simp +decide only [mul_assoc, mul_sub, mul_comm, sum_sub_distrib] ; ring

/-
The mixed difference factors through `(b-a)*(d-c)` times a bilinear form
expressed using `newtonDiff`.
-/
theorem eval_mixed_diff_factored {R : Type*} [CommRing R]
    (q : MvPolynomial (Fin 2) R) (a b c d : R) :
    MvPolynomial.eval ![b, d] q - MvPolynomial.eval ![a, d] q -
    MvPolynomial.eval ![b, c] q + MvPolynomial.eval ![a, c] q =
    (b - a) * (d - c) *
    q.support.sum (fun m =>
      MvPolynomial.coeff m q * newtonDiff a b (m 0) * newtonDiff c d (m 1)) := by
  rw [ eval_mixed_diff_eq ];
  simp +decide only [mul_assoc, mul_comm, mul_left_comm, mul_sum];
  exact Finset.sum_congr rfl fun x hx => by rw [ pow_sub_eq_mul_newtonDiff a b ( x 0 ), pow_sub_eq_mul_newtonDiff c d ( x 1 ) ] ; ring;

/-
Re-indexing the mixed difference bilinear form: the sum over the support
can be replaced by a sum over `Fin N × Fin N` using degree-bounded indices,
where extra terms vanish because their coefficients are zero or the Newton
differences are trivially zero.
-/
theorem eval_mixed_diff_finsum {R : Type*} [CommRing R]
    {N : ℕ} (q : MvPolynomial (Fin 2) R) (hdeg : q.totalDegree ≤ N + 1) (a b c d : R) :
    MvPolynomial.eval ![b, d] q - MvPolynomial.eval ![a, d] q -
    MvPolynomial.eval ![b, c] q + MvPolynomial.eval ![a, c] q =
    (b - a) * (d - c) *
    ∑ k₁ : Fin N, ∑ k₂ : Fin N,
      MvPolynomial.coeff (Finsupp.single 0 (k₁.val + 1) + Finsupp.single 1 (k₂.val + 1)) q *
      newtonDiff a b (k₁.val + 1) * newtonDiff c d (k₂.val + 1) := by
  rw [ eval_mixed_diff_factored ];
  have h_sum : ∑ m ∈ q.support, MvPolynomial.coeff m q * newtonDiff a b (m 0) * newtonDiff c d (m 1) = ∑ m ∈ Finset.filter (fun m => m 0 > 0 ∧ m 1 > 0) q.support, MvPolynomial.coeff m q * newtonDiff a b (m 0) * newtonDiff c d (m 1) := by
    rw [ Finset.sum_filter_of_ne ];
    intro m hm h; constructor <;> contrapose! h <;> simp_all +decide [ newtonDiff ] ;
  rw [ h_sum, Finset.sum_subset ( show q.support.filter ( fun m => m 0 > 0 ∧ m 1 > 0 ) ⊆ Finset.image ( fun k : Fin N × Fin N => Finsupp.single 0 ( k.1.val + 1 ) + Finsupp.single 1 ( k.2.val + 1 ) ) ( Finset.univ ) from ?_ ) ];
  · rw [ Finset.sum_image ] <;> simp +decide;
    · rw [ Finset.sum_sigma' ];
      refine' congr_arg _ ( Finset.sum_bij ( fun x _ => ⟨ ⟨ x.1, by
        exact x.1.2 ⟩, ⟨ x.2, by
        exact x.2.2 ⟩ ⟩ ) _ _ _ _ ) <;> simp +decide;
    · intro k l hkl; replace hkl := congr_arg ( fun f => ( f 0, f 1 ) ) hkl; aesop;
  · aesop;
  · intro m hm; simp_all +decide [ Finsupp.ext_iff, Fin.forall_fin_two ] ;
    have h_deg : m 0 + m 1 ≤ N + 1 := by
      have h_deg : m.sum (fun _ e => e) ≤ N + 1 := by
        exact le_trans ( Finset.le_sup ( f := fun s => s.sum fun x e => e ) ( Finsupp.mem_support_iff.mpr hm.1 ) ) hdeg;
      rw [ Finsupp.sum_fintype ] at h_deg <;> aesop;
    exact ⟨ ⟨ ⟨ m 0 - 1, by omega ⟩, by simp +decide [ Nat.sub_add_cancel hm.2.1 ] ⟩, ⟨ ⟨ m 1 - 1, by omega ⟩, by simp +decide [ Nat.sub_add_cancel hm.2.2 ] ⟩ ⟩

/-! ### Quartic case (p = 5) -/

/-
**No quartic representation of the inversion indicator on ℤ/5**.

For every commutative ring `R` and every injective `j : ℤ/5 → R`, there is no
polynomial `q` of total degree `≤ 4` with `q(j(x), j(y)) = j(f(x,y))` for all
`x, y ∈ ℤ/5`, where `f(x,y) = 𝟙[xy ≡ 1 (mod 5)]`.
-/
set_option maxHeartbeats 800000 in
theorem thm_quartic {R : Type*} [CommRing R]
    (j : ZMod 5 → R) (hj : Function.Injective j)
    (q : MvPolynomial (Fin 2) R) (hdeg : q.totalDegree ≤ 4)
    (heval : ∀ x y : ZMod 5,
      MvPolynomial.eval ![j x, j y] q = j (if x * y = 1 then 1 else 0)) :
    False := by
  -- Define the matrices Φ, A, D, and F.
  set Φ : Matrix (Fin 4) (Fin 3) R := fun b i => newtonDiff (j 0) (j (b.val + 1)) (i.val + 1)
  set A : Matrix (Fin 3) (Fin 3) R := fun i j => MvPolynomial.coeff ((Finsupp.single 0 (i.val + 1)) + (Finsupp.single 1 (j.val + 1))) q
  set D : Matrix (Fin 4) (Fin 4) R := Matrix.diagonal (fun b => j (b.val + 1) - j 0)
  set F : Matrix (Fin 4) (Fin 4) R := fun b d => if (b.val + 1) * (d.val + 1) ≡ 1 [MOD 5] then 1 else 0;
  -- The matrix equation D * (Φ * A * Φᵀ) * D = d₀₁ • F follows from combining steps 2 and 3.
  have hmat : D * (Φ * A * Φᵀ) * D = (j 1 - j 0) • F := by
    have hmat : ∀ b d : Fin 4, (j (b.val + 1) - j 0) * (j (d.val + 1) - j 0) * (∑ k₁ : Fin 3, ∑ k₂ : Fin 3, MvPolynomial.coeff (Finsupp.single 0 (k₁.val + 1) + Finsupp.single 1 (k₂.val + 1)) q * newtonDiff (j 0) (j (b.val + 1)) (k₁.val + 1) * newtonDiff (j 0) (j (d.val + 1)) (k₂.val + 1)) = (j 1 - j 0) * (if (b.val + 1) * (d.val + 1) ≡ 1 [MOD 5] then 1 else 0) := by
      intro b d
      have h_eval : MvPolynomial.eval ![j (b.val + 1), j (d.val + 1)] q - MvPolynomial.eval ![j 0, j (d.val + 1)] q - MvPolynomial.eval ![j (b.val + 1), j 0] q + MvPolynomial.eval ![j 0, j 0] q = (j 1 - j 0) * (if (b.val + 1) * (d.val + 1) ≡ 1 [MOD 5] then 1 else 0) := by
        fin_cases b <;> fin_cases d <;> simp +decide [ heval ];
      rw [ ← h_eval, eval_mixed_diff_finsum q hdeg ];
    ext b d;
    simp +zetaDelta at *;
    convert hmat b d using 1 ; simp +decide [ Matrix.mul_apply, Fin.sum_univ_three ] ; ring!;
  -- The determinant of F is ±1 (a unit) because F is the permutation matrix of inversion on (ZMod 5)*, which is the permutation (2 3)(1)(4), a transposition with sign -1.
  have hdet_F : IsUnit F.det := by
    simp +decide [ F, Matrix.det_succ_row_zero ];
    simp +decide [ Fin.sum_univ_succ, Fin.succAbove ];
  -- The delta relation: from (b,d) = (0,0) (i.e., units 1,1), f(1,1)=1 so the mixed diff = d₀₁. Also d₀₁ * d₀₁ * e₁₁ = d₀₁, giving d₀₁² * e₁₁ = d₀₁.
  have hdelta : (j 1 - j 0) ^ 2 * (Φ 0 0 * A 0 0 * Φ 0 0 + Φ 0 1 * A 1 0 * Φ 0 0 + Φ 0 2 * A 2 0 * Φ 0 0 + Φ 0 0 * A 0 1 * Φ 0 1 + Φ 0 1 * A 1 1 * Φ 0 1 + Φ 0 2 * A 2 1 * Φ 0 1 + Φ 0 0 * A 0 2 * Φ 0 2 + Φ 0 1 * A 1 2 * Φ 0 2 + Φ 0 2 * A 2 2 * Φ 0 2) = j 1 - j 0 := by
    have := congr_fun ( congr_fun hmat 0 ) 0; simp +decide [ Matrix.mul_apply, Fin.sum_univ_succ ] at this ⊢;
    simp +zetaDelta at *;
    convert this using 1 ; ring;
  convert inv_graph_no_rep ( show Fintype.card ( Fin 3 ) < Fintype.card ( Fin 4 ) from by decide ) hmat hdet_F hdelta using 1;
  simp +decide [ sub_eq_iff_eq_add, hj.eq_iff ]

/-! ### General prime case -/

/-
**No degree-(p-1) representation of the inversion indicator on ℤ/p**.

For every prime `p`, every commutative ring `R`, and every injective `j : ℤ/p → R`,
there is no polynomial `q` of total degree `≤ p - 1` with `q(j(x), j(y)) = j(f(x,y))`
for all `x, y ∈ ℤ/p`, where `f(x,y) = 𝟙[xy ≡ 1 (mod p)]`.
-/
set_option maxHeartbeats 1600000 in
theorem thm_invp {R : Type*} [CommRing R]
    {p : ℕ} (hp : Nat.Prime p)
    (j : ZMod p → R) (hj : Function.Injective j)
    (q : MvPolynomial (Fin 2) R) (hdeg : q.totalDegree ≤ p - 1)
    (heval : ∀ x y : ZMod p,
      MvPolynomial.eval ![j x, j y] q = j (if x * y = 1 then 1 else 0)) :
    False := by
  haveI := Fact.mk hp;
  -- Define the matrices D, Φ, A, and F as described.
  set N := p - 2
  set n := p - 1
  set D : Matrix (Fin n) (Fin n) R := Matrix.diagonal (fun b => j (b.val + 1) - j 0)
  set Φ : Matrix (Fin n) (Fin N) R := fun b k => newtonDiff (j 0) (j (b.val + 1)) (k.val + 1)
  set A : Matrix (Fin N) (Fin N) R := fun k₁ k₂ => q.coeff (Finsupp.single 0 (k₁.val + 1) + Finsupp.single 1 (k₂.val + 1))
  set F : Matrix (Fin n) (Fin n) R := fun b d => if (b.val + 1) * (d.val + 1) ≡ 1 [ZMOD p] then 1 else 0;
  -- The matrix equation D * (Φ * A * Φᵀ) * D = d₀₁ • F follows from:
  -- 1. From heval: the anchored mixed diff equals d₀₁ * f(b+1,d+1)
  -- 2. From eval_mixed_diff_finsum: the mixed diff equals (j(b+1)-j0)*(j(d+1)-j0) * bilinear form
  have hmat : D * (Φ * A * Φᵀ) * D = (j 1 - j 0) • F := by
    have hmat : ∀ b d : Fin n, (j (b.val + 1) - j 0) * (j (d.val + 1) - j 0) * (∑ k₁ : Fin N, ∑ k₂ : Fin N, q.coeff (Finsupp.single 0 (k₁.val + 1) + Finsupp.single 1 (k₂.val + 1)) * newtonDiff (j 0) (j (b.val + 1)) (k₁.val + 1) * newtonDiff (j 0) (j (d.val + 1)) (k₂.val + 1)) = (j 1 - j 0) * (if (b.val + 1) * (d.val + 1) ≡ 1 [ZMOD p] then 1 else 0) := by
      intro b d;
      have hmat : MvPolynomial.eval ![j (b.val + 1), j (d.val + 1)] q - MvPolynomial.eval ![j 0, j (d.val + 1)] q - MvPolynomial.eval ![j (b.val + 1), j 0] q + MvPolynomial.eval ![j 0, j 0] q = (j 1 - j 0) * (if (b.val + 1) * (d.val + 1) ≡ 1 [ZMOD p] then 1 else 0) := by
        simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ];
        split_ifs <;> simp +decide [ * ];
      rw [ ← hmat, eval_mixed_diff_finsum ];
      grind;
    ext b d; simp +decide [ Matrix.mul_apply ] ;
    convert hmat b d using 1;
    simp +decide [ D, Φ, A, Matrix.diagonal ];
    simp +decide only [mul_comm, mul_left_comm, mul_assoc];
    simp +decide only [Finset.mul_sum _ _ _, mul_left_comm];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
  -- The determinant of F is ±1, hence a unit.
  have hdet_F : IsUnit F.det := by
    -- Since $F$ is a permutation matrix, its determinant is $\pm 1$.
    have hF_perm : ∃ σ : Equiv.Perm (Fin n), ∀ b d : Fin n, F b d = if d = σ b then 1 else 0 := by
      have hF_perm : ∀ b : Fin n, ∃! d : Fin n, (b.val + 1) * (d.val + 1) ≡ 1 [ZMOD p] := by
        intro b
        obtain ⟨d, hd⟩ : ∃ d : Fin n, (b.val + 1) * (d.val + 1) ≡ 1 [ZMOD p] := by
          -- Since $p$ is prime, $(b.val + 1)$ has a multiplicative inverse modulo $p$.
          obtain ⟨d, hd⟩ : ∃ d : ZMod p, (b.val + 1) * d = 1 := by
            exact ⟨ _, mul_inv_cancel₀ ( show ( b : ZMod p ) + 1 ≠ 0 from by simpa [ ← ZMod.natCast_eq_zero_iff ] using Nat.not_dvd_of_pos_of_lt ( Nat.succ_pos _ ) ( Nat.lt_pred_iff.mp b.2 ) ) ⟩;
          use ⟨ d.val - 1, by
            grind ⟩
          generalize_proofs at *;
          simp +decide [ ← ZMod.intCast_eq_intCast_iff, hd, Nat.cast_sub ( show 1 ≤ d.val from Nat.pos_of_ne_zero fun h => by simp_all +decide [ ZMod.val_eq_zero ] ) ];
        refine' ⟨ d, hd, fun e he => _ ⟩;
        haveI := Fact.mk hp; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
        exact Fin.ext ( Nat.mod_eq_of_lt ( show ( e : ℕ ) < p from lt_of_lt_of_le e.2 ( Nat.pred_le _ ) ) ▸ Nat.mod_eq_of_lt ( show ( d : ℕ ) < p from lt_of_lt_of_le d.2 ( Nat.pred_le _ ) ) ▸ by simpa [ ← ZMod.natCast_eq_natCast_iff' ] using mul_left_cancel₀ ( show ( b : ZMod p ) + 1 ≠ 0 from by aesop_cat ) <| by linear_combination' he - hd );
      choose σ hσ₁ hσ₂ using hF_perm;
      use Equiv.ofBijective σ (by
      have hσ_inj : Function.Injective σ := by
        intro b c hbc
        generalize_proofs at *;
        have := hσ₁ b; have := hσ₁ c; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
        grind
      generalize_proofs at *;
      exact ⟨ hσ_inj, Finite.injective_iff_surjective.mp hσ_inj ⟩)
      intro b d
      simp only [Equiv.ofBijective_apply]
      generalize_proofs at *;
      grind;
    obtain ⟨ σ, hσ ⟩ := hF_perm
    have hF_det : F.det = Equiv.Perm.sign σ := by
      rw [ ← Matrix.det_transpose, Matrix.det_apply' ];
      rw [ Finset.sum_eq_single σ ] <;> simp +decide [ hσ ];
      intro b hb; rw [ Finset.prod_eq_zero ( Finset.mem_univ ( Classical.choose ( show ∃ x, b x ≠ σ x from not_forall.mp fun h => hb <| Equiv.ext h ) ) ) ] <;> simp +decide [ Classical.choose_spec ( show ∃ x, b x ≠ σ x from not_forall.mp fun h => hb <| Equiv.ext h ) ] ;
    generalize_proofs at *;
    cases' Int.units_eq_one_or ( Equiv.Perm.sign σ ) with h h <;> simp +decide [ h, hF_det ];
  -- The delta relation: (b,d) = (0,0) gives d₀₁² * e₁₁ = d₀₁ since f(1,1)=1.
  have hdelta : (j 1 - j 0) ^ 2 * (∑ k₁ : Fin N, ∑ k₂ : Fin N, q.coeff (Finsupp.single 0 (k₁.val + 1) + Finsupp.single 1 (k₂.val + 1)) * newtonDiff (j 0) (j 1) (k₁.val + 1) * newtonDiff (j 0) (j 1) (k₂.val + 1)) = j 1 - j 0 := by
    convert congr_arg ( fun m => m ⟨ 0, Nat.sub_pos_of_lt hp.one_lt ⟩ ⟨ 0, Nat.sub_pos_of_lt hp.one_lt ⟩ ) hmat using 1;
    · simp +zetaDelta at *;
      simp +decide [ Matrix.mul_apply, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, sq ];
      exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
    · simp +zetaDelta at *;
  -- Apply the nilpotent_from_rank_deficient_matrix_eq theorem to conclude that (j 1 - j 0) ^ (p - 1) = 0.
  have hnil : (j 1 - j 0) ^ (p - 1) = 0 := by
    convert nilpotent_from_rank_deficient_matrix_eq _ hmat hdet_F using 1;
    · simp +zetaDelta at *;
    · simp +zetaDelta at *;
      exact Nat.pred_lt ( ne_bot_of_gt ( Nat.sub_pos_of_lt hp.one_lt ) );
  -- Apply the nilpotent_from_rank_deficient_matrix_eq theorem to conclude that j 1 - j 0 = 0.
  have hnil : j 1 - j 0 = 0 := by
    apply inv_graph_core hdelta hnil;
  exact absurd ( hj ( sub_eq_zero.mp hnil ) ) ( by simp +decide )

end

end Finbin
