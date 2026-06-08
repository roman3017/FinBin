import Mathlib

/-!
# Degree-four embedding of binary Kronecker delta functions

Every binary Kronecker delta `δ_{a,b} : (ZMod n)² → ZMod n` embeds into a polynomial
function of total degree ≤ 4 (`Finbin.quartic_d`).

Ported from `brcm/archive/lean/cursor/quartic_dab.lean`.
-/

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 30000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

namespace Finbin

open Function Set MvPolynomial

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `j` represents `f` by `g`: the embedding `j` intertwines the binary function `f` with the
binary function `g`. -/
def representation (f : α × α → α) {β : Type*} (g : β × β → β) (j : α ↪ β) : Prop :=
  ∀ x y : α, j (f (x, y)) = g (j x, j y)

/-- `f` is represented by `g` if some embedding `j` represents `f` by `g`. -/
def represents (f : α × α → α) {β : Type*} (g : β × β → β) : Prop :=
  ∃ j, representation f g j

/-- `f` is represented by a polynomial of total degree `≤ d` over `ZMod n`. -/
def representedByPolynomialOfDegreeIn (n : ℕ) (f : α × α → α) (d : ℕ) : Prop :=
  ∃ g : MvPolynomial (Fin 2) (ZMod n),
    represents f (fun v => g.eval ![v.1, v.2]) ∧
    g.totalDegree ≤ d

/-- `f` is represented by a polynomial of total degree `≤ d` over `ZMod n` for some `n`. -/
def representedByPolynomialOfDegree (f : α × α → α) (d : ℕ) : Prop :=
  ∃ n : ℕ, representedByPolynomialOfDegreeIn n f d

/-- The binary Kronecker delta `δ_{a,b}` on `ZMod n`: it sends `(a,b)` to `1` and every
other pair to `0`. The modulus is kept nonzero throughout, so `[NeZero n]` is part of the
intended interface even though the definition does not use it. -/
@[nolint unusedArguments]
def kroneckerDelta (n : ℕ) [NeZero n] (a b : ZMod n) : ZMod n × ZMod n → ZMod n :=
  fun p => if p.1 = a ∧ p.2 = b then 1 else 0

theorem quadratic_d2 (a b : ZMod 2) :
  representedByPolynomialOfDegree (kroneckerDelta 2 a b) 2 := by
    -- Let's choose the polynomial $g(x, y) = (1 + x + a)(1 + y + b)$.
    use 2, MvPolynomial.C 1 * ((MvPolynomial.X 0 + MvPolynomial.C a + MvPolynomial.C 1) * (MvPolynomial.X 1 + MvPolynomial.C b + MvPolynomial.C 1));
    constructor;
    · use ⟨ fun x => x, by
        exact Function.injective_id ⟩
      intro x y
      fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;> simp +decide [ kroneckerDelta ] ;
    · refine' le_trans ( MvPolynomial.totalDegree_mul _ _ ) _ ; norm_num;
      refine' le_trans ( MvPolynomial.totalDegree_mul _ _ ) _;
      refine' le_trans ( add_le_add ( MvPolynomial.totalDegree_add _ _ ) ( MvPolynomial.totalDegree_add _ _ ) ) _ ; norm_num;
      refine' le_trans ( add_le_add ( MvPolynomial.totalDegree_add _ _ ) ( MvPolynomial.totalDegree_add _ _ ) ) _ ; norm_num

theorem cubic_d3_02 : representedByPolynomialOfDegree (kroneckerDelta 3 0 2) 3 := by
  use 4;
  -- Define the polynomial $g(x, y) = (x^2 + x + 2) * y$.
  let g : MvPolynomial (Fin 2) (ZMod 4) := (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 0 + 2) * MvPolynomial.X 1;
  use g
  constructor;
  · use ⟨ fun x => if x = 0 then 0 else if x = 1 then 2 else 1, by decide ⟩
    intro x y
    simp only [g, map_mul, map_add, map_pow, map_ofNat, MvPolynomial.eval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [kroneckerDelta, Function.Embedding.coeFn_mk]
    fin_cases x <;> fin_cases y <;> rfl
  ·
    refine' le_trans ( MvPolynomial.totalDegree_mul _ _ ) _;
    refine' le_trans ( add_le_add ( _ : _ ≤ _ ) ( _ : _ ≤ _ ) ) _ <;> norm_num [ MvPolynomial.totalDegree ];
    exact 2;
    exact 1;
    · intro b hb; contrapose! hb; erw [ MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X', MvPolynomial.coeff_C ] at *; aesop;
    · simp +decide [ MvPolynomial.coeff_X' ];
    · norm_num +zetaDelta at *

theorem quadratic_d_00 (n : ℕ) [NeZero n] :
    representedByPolynomialOfDegree (kroneckerDelta n 0 0) 2 := by
  by_contra h;
  obtain ⟨j, hj⟩ : ∃ j : ZMod n ↪ ZMod (n * (n + 1)), ∀ x y : ZMod n, j (if x = 0 ∧ y = 0 then 1 else 0) = (n : ZMod (n * (n + 1))) * (j x + 1) * (j y + 1) := by
    refine' ⟨ ⟨ fun x => if x = 0 then 0 else x.val * ( n + 1 ) - 1, _ ⟩, _ ⟩ <;> simp +decide [ Function.Injective ];
    · intro a₁ a₂ h; split_ifs at h <;> simp_all +decide [ sub_eq_iff_eq_add ] ;
      · -- Since $a₂.cast * (n + 1) = 1$ in $ZMod (n * (n + 1))$, we have $a₂.cast * (n + 1) ≡ 1 \pmod{n * (n + 1)}$.
        have h_cong : a₂.val * (n + 1) ≡ 1 [MOD n * (n + 1)] := by
          simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
          exact eq_of_sub_eq_zero h.symm;
        have := congr_arg ( · % ( n + 1 ) ) h_cong; norm_num [ Nat.ModEq, Nat.mul_mod, Nat.mod_eq_of_lt ( show 1 < n + 1 from Nat.succ_lt_succ ( NeZero.pos n ) ) ] at this;
      · -- Since $a₁$ is non-zero, we can multiply both sides of the equation by $a₁⁻¹$ to get $(n + 1) = a₁⁻¹$.
        have h_inv : (n + 1 : ZMod (n * (n + 1))) = 1 := by
          have h_inv : (a₁.val * (n + 1) : ℕ) ≡ 1 [MOD n * (n + 1)] := by
            simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
          have := h_inv.of_dvd ( dvd_mul_left ( n + 1 ) n ) ; simp_all +decide [ Nat.ModEq, Nat.mul_mod_mul_right ] ;
        rcases n with ( _ | _ | n ) <;> simp_all +decide ;
        · exact NeZero.ne 0 rfl;
        · norm_cast at h_inv;
          erw [ ZMod.natCast_eq_zero_iff ] at h_inv ; exact Nat.not_dvd_of_pos_of_lt ( Nat.succ_pos _ ) ( by nlinarith ) h_inv;
      · -- Since $a₁$ and $a₂$ are elements of $ZMod n$, we can simplify the equation $a₁.cast * (n + 1) = a₂.cast * (n + 1)$ to $a₁ = a₂$.
        have h_simplified : (a₁.val : ℕ) * (n + 1) ≡ (a₂.val : ℕ) * (n + 1) [MOD n * (n + 1)] := by
          erw [ ← ZMod.natCast_eq_natCast_iff ] ; aesop;
        -- Since $n + 1$ is coprime to $n$, we can divide both sides of the congruence by $n + 1$.
        have h_div : (a₁.val : ℕ) ≡ (a₂.val : ℕ) [MOD n] := by
          rw [ Nat.modEq_iff_dvd ] at *;
          exact h_simplified.imp fun x hx => by push_cast at *; nlinarith;
        cases n <;> simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
    · intro x y; split_ifs <;> simp_all +decide [ sub_eq_iff_eq_add ] ;
      · rcases n with ( _ | _ | n ) <;> cases ‹_› ; trivial;
        · contrapose! h;
          refine' ⟨ 1, _ ⟩;
          refine' ⟨ 1, _, _ ⟩ <;> norm_num [ represents ];
          exact ⟨ ⟨ fun _ => 0, by decide ⟩, by simp +decide [ representation ] ⟩;
        · cases ‹ ( 1 : ZMod ( n + 1 + 1 ) ) = 0 ›;
      · norm_cast ; simp +decide [ mul_comm, Nat.mul_succ ];
        norm_cast ; simp +decide [ ← mul_assoc ];
        norm_cast ; simp +decide ;
      · norm_cast ; norm_num [ mul_assoc, mul_comm, mul_left_comm ];
        norm_cast ; norm_num [ ← mul_assoc, ← ZMod.natCast_eq_zero_iff ];
        norm_cast ; aesop;
      · -- Since $n$ is a factor, and we're working modulo $n(n+1)$, the product $n * (x.cast * (n + 1)) * (y.cast * (n + 1))$ is congruent to $0$ modulo $n(n+1)$.
        have h_cong : (n : ZMod (n * (n + 1))) * (x.cast * ((n : ZMod (n * (n + 1))) + 1)) * (y.cast * ((n : ZMod (n * (n + 1))) + 1)) = 0 := by
          have h_div : (n : ZMod (n * (n + 1))) * (n + 1) = 0 := by
            norm_cast at * ; aesop;
          linear_combination' h_div * x.cast * y.cast * ( n + 1 );
        exact h_cong.symm;
      · rcases n with ( _ | _ | n ) <;> norm_cast;
        erw [ one_mul ]
  refine' h ⟨ n * ( n + 1 ), _, _, _ ⟩;
  exact MvPolynomial.C ( n : ZMod ( n * ( n + 1 ) ) ) * ( MvPolynomial.X 0 + 1 ) * ( MvPolynomial.X 1 + 1 );
  · use j; aesop;
  · refine' le_trans ( MvPolynomial.totalDegree_mul _ _ ) _;
    refine' le_trans ( add_le_add ( MvPolynomial.totalDegree_mul _ _ ) ( MvPolynomial.totalDegree_add _ _ ) ) _ ; norm_num;
    refine' le_trans ( add_le_add_three ( Finset.sup_le _ ) ( Finset.sup_le _ ) ( Finset.sup_le _ ) ) _ <;> norm_num;
    exact 0;
    rotate_left;
    exact 1;
    rotate_left;
    exact 1;
    · simp +decide [ MvPolynomial.coeff_X' ];
    · norm_num;
    · intro b hb; erw [ MvPolynomial.coeff_C ] at hb; aesop;
    · intro b hb; rw [ MvPolynomial.coeff_X', MvPolynomial.coeff_one ] at hb; aesop;

theorem quadratic_d_11 (n : ℕ) [NeZero n] :
    representedByPolynomialOfDegree (kroneckerDelta n 1 1) 2 := by
  have := quadratic_d_00 n;
  obtain ⟨ m, g, hg, h_deg ⟩ := this;
  -- Let $j'$ be the embedding of $\text{ZMod } n$ into $\text{ZMod } m$ defined by $j'(x) = j(\sigma(x))$, where $\sigma$ is the permutation that swaps 0 and 1.
  obtain ⟨ j, hj ⟩ := hg;
  set j' : ZMod n ↪ ZMod m := ⟨fun x => j (if x = 0 then 1 else if x = 1 then 0 else x), by
    intro x y; aesop;⟩
  -- We define a new polynomial $G = -g + (j(0) + j(1))$.
  set G : MvPolynomial (Fin 2) (ZMod m) := -g + MvPolynomial.C (j 0 + j 1) * 1
  -- We need to show that $G$ represents $\delta_{1,1}$ via $j'$.
  have hG_rep : ∀ x y, j' (kroneckerDelta n 1 1 (x, y)) = G.eval ![j' x, j' y] := by
    intro x y
    simp [G, j'];
    convert congr_arg ( fun z => -z + ( j 0 + j 1 ) ) ( hj ( if x = 0 then 1 else if x = 1 then 0 else x ) ( if y = 0 then 1 else if y = 1 then 0 else y ) ) using 1 ; simp +decide [ kroneckerDelta ] ; ring_nf!; (
    grind)
  -- The degree of $G$ is at most the maximum of the degrees of $-g$ and $(j(0) + j(1)) * 1$.
  have hG_deg : G.totalDegree ≤ max g.totalDegree 0 := by
    refine' le_trans ( MvPolynomial.totalDegree_add _ _ ) _ ; norm_num
    refine' le_trans ( MvPolynomial.totalDegree_add _ _ ) _ ; norm_num [ h_deg ]
  exact ⟨ m, G, ⟨ j', hG_rep ⟩, hG_deg.trans ( max_le h_deg ( by norm_num ) ) ⟩

theorem quadratic_d_22 (n : ℕ) [NeZero n] :
    representedByPolynomialOfDegree (kroneckerDelta n 2 2) 2 := by
  by_cases hn : n < 3;
  · interval_cases n <;> simp_all +decide ;
    · exact False.elim <| NeZero.ne 0 rfl;
    · convert quadratic_d_00 1 using 1;
    · convert quadratic_d_00 2 using 1;
  · have hn_ge3 : n ≥ 3 := by linarith
    let j_map_22 : ∀ m : ℕ, ZMod m → ZMod (4 * m) :=
      fun m x => if x = 2 then 1 else if x = 1 then 2 * m else 2 * x.val
    have h_j_map_22_injective_aux : ∀ {m : ℕ}, m ≥ 3 → Function.Injective (j_map_22 m) := by
      intro m hm x y hxy
      by_cases hx : x = 1 ∨ x = 2
      by_cases hy : y = 1 ∨ y = 2;
      · cases hx <;> cases hy <;> simp_all +decide [ j_map_22 ];
        · rcases m with ( _ | _ | _ | m ) <;> norm_cast at *;
          erw [ ZMod.natCast_eq_natCast_iff ] at hxy ; norm_num [ Nat.ModEq, Nat.mul_mod ] at hxy;
          simp_all +arith +decide [ Nat.mod_eq_of_lt ];
        · rcases m with ( _ | _ | _ | m ) <;> norm_cast at *;
          erw [ eq_comm, ZMod.natCast_eq_natCast_iff ] at hxy ; norm_num [ Nat.modEq_iff_dvd ] at hxy;
          specialize hxy ( by exact_mod_cast Nat.not_dvd_of_pos_of_lt ( by norm_num ) ( by linarith ) ) ; norm_cast at hxy;
          erw [ eq_comm, ZMod.natCast_eq_natCast_iff ] at hxy ; norm_num [ Nat.modEq_iff_dvd ] at hxy;
          exact absurd hxy ( by rintro ⟨ k, hk ⟩ ; nlinarith [ show k = 0 by nlinarith ] );
      · rcases hx with ( rfl | rfl ) <;> simp_all +decide [ j_map_22 ];
        · split_ifs at hxy <;> norm_cast at hxy ⊢ ; simp_all +decide ; (
          rcases m with ( _ | _ | _ | m ) <;> cases ‹ ( 1 : ZMod _ ) = 2 › ; contradiction;);
          erw [ ZMod.natCast_eq_natCast_iff ] at * ; norm_num at *;
          rw [ Nat.ModEq ] at hxy ; rcases m with ( _ | _ | m ) <;> simp_all +arith +decide [ Nat.mod_eq_of_lt ] ;
          rw [ Nat.mod_eq_of_lt ] at hxy <;> linarith [ show y.val < m + 2 from y.val_lt ] ;
        · obtain ⟨k, hk⟩ : ∃ k : ℤ, 2 * y.val = 1 + k * 4 * m := by
            have h_cong : (2 * y.val : ℤ) ≡ 1 [ZMOD (4 * m)] := by
              erw [ ← ZMod.intCast_eq_intCast_iff ] ; aesop;
            exact h_cong.symm.dvd.imp fun k hk => by linarith;
          replace hk := congr_arg Even hk ; simp_all +decide [ parity_simps ];
      · by_cases hy : y = 1 ∨ y = 2 <;> simp_all +decide [ j_map_22 ];
        · rcases hy with ( rfl | rfl ) <;> simp_all +decide ;
          · rcases m with ( _ | _ | _ | m ) <;> norm_cast at *;
            erw [ ZMod.natCast_eq_natCast_iff ] at hxy ; norm_num [ Nat.ModEq, Nat.mul_mod ] at hxy;
            split_ifs at hxy <;> simp_all +decide [ Nat.mod_eq_of_lt ];
            · cases ‹ ( 1 : ZMod ( m + 1 + 1 + 1 ) ) = 2 ›;
            · rw [ Nat.mod_eq_of_lt ] at hxy <;> linarith [ show x.val < m + 1 + 1 + 1 from x.val_lt ];
          · have h_contra : 2 * x.val ≡ 1 [MOD 4 * m] := by
              erw [ ← ZMod.natCast_eq_natCast_iff ] ; aesop;
            have := congr_arg ( · % 2 ) h_contra; norm_num [ Nat.ModEq, Nat.mul_mod ] at this;
            norm_num [ Nat.mod_mod_of_dvd _ ( dvd_mul_of_dvd_left ( by decide : 2 ∣ 4 ) _ ) ] at this;
        · have h_val : x.val = y.val := by
            have h_val : (2 * x.val : ℕ) ≡ (2 * y.val : ℕ) [MOD 4 * m] := by
              erw [ ← ZMod.natCast_eq_natCast_iff ] ; aesop;
            rw [ Nat.ModEq ] at h_val;
            rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] at h_val;
            · linarith;
            · haveI := Fact.mk ( by linarith : 1 < m ) ; linarith [ y.val_lt ] ;
            · haveI := Fact.mk ( by linarith : 1 < m ) ; linarith [ x.val_lt ] ;
          convert ZMod.val_injective m h_val;
          exact ⟨ by linarith ⟩
    have h_j_map_22_injective : Function.Injective (j_map_22 n) :=
      h_j_map_22_injective_aux hn_ge3
    have h_ge3_case : representedByPolynomialOfDegree (kroneckerDelta n 2 2) 2 := by
      use 4 * n, MvPolynomial.C (2 * n : ZMod (4 * n)) * MvPolynomial.X 0 * MvPolynomial.X 1, by
        have h_rep : ∀ x y : ZMod n, (if x = 2 ∧ y = 2 then 2 * n else 0) = (2 * n : ZMod (4 * n)) * (j_map_22 n x) * (j_map_22 n y) := by
          intro x y; split_ifs <;> simp_all +decide [ mul_comm, mul_left_comm ] ;
          · unfold j_map_22; aesop;
          · have h_even : ∀ x : ZMod n, x ≠ 2 → j_map_22 n x * ((n : ZMod (4 * n)) * 2) = 0 := by
              intro x hx; unfold j_map_22; simp +decide [ hx ] ; ring_nf;
              split_ifs <;> norm_cast <;> ring_nf;
              · erw [ ZMod.natCast_eq_zero_iff ] ; exact ⟨ n, by ring ⟩;
              · norm_num [ mul_assoc, mul_comm, mul_left_comm ];
                erw [ ← mul_assoc, mul_comm ] ; norm_cast ; aesop;
            by_cases hx : x = 2 <;> by_cases hy : y = 2 <;>
              simp_all +decide [ j_map_22, mul_assoc, mul_comm, mul_left_comm ];
        use ⟨ j_map_22 n, ?_ ⟩;
        intro x y; specialize h_rep x y; simp_all +decide [ kroneckerDelta ] ;
        convert h_rep x y using 1;
        swap;
        apply h_j_map_22_injective;
        split_ifs;
        · unfold j_map_22; simp +decide [ * ] ; ring_nf;
          rcases n with ( _ | _ | _ | n ) <;> norm_cast;
          simp +decide [ ZMod, Fin.ext_iff ];
          rintro ⟨ ⟩
        · rcases n with ( _ | _ | _ | n ) <;> norm_cast, by
        refine' le_trans ( MvPolynomial.totalDegree_mul _ _ ) _ ; norm_num [ MvPolynomial.totalDegree ];
        refine' le_trans ( add_le_add ( Finset.sup_le _ ) ( Finset.sup_le _ ) ) _ <;> norm_num;
        exact 1;
        rotate_left;
        exact 1;
        · simp +decide [ MvPolynomial.coeff_X' ];
        · norm_num;
        · intro b hb; erw [ MvPolynomial.coeff_C ] at hb; aesop;
    exact h_ge3_case

/-
Let m = n if n odd else n+1,
g(x, y) = mx(x+1)y mod 4m, j = (0, 2m, 3, 12, 16, 20,..., 4*(m-1))
-/

/-- Odd modulus parameter for the degree-three representation of `δ_{1,2}`: `n` if `n` is odd,
otherwise `n + 1`. -/
def mVal12 (n : ℕ) : ℕ := if n % 2 = 1 then n else n + 1

/-- The modulus `4 · mVal12 n` (with a trivial value at `n = 1`) for the `δ_{1,2}`
representation. -/
def nVal12 (n : ℕ) : ℕ := if n = 1 then 1 else 4 * mVal12 n

theorem cubic_d_12 (n : ℕ) [NeZero n] :
    representedByPolynomialOfDegree (kroneckerDelta n 1 2) 3 := by
  let N_val_final : ℕ := if n = 2 then 3 else nVal12 n
  let j_map_fun_12 : ZMod n → ZMod (nVal12 n) :=
    fun x =>
      if n = 1 then 0
      else
        let m := mVal12 n
        if x = 1 then (2 * m : ℕ)
        else if x = 2 then (3 : ℕ)
        else (4 * x.val : ℕ)
  let poly_G_12 : MvPolynomial (Fin 2) (ZMod (nVal12 n)) :=
    if n = 1 then 0
    else
      let m : ZMod (nVal12 n) := mVal12 n
      let X := MvPolynomial.X (0 : Fin 2)
      let Y := MvPolynomial.X (1 : Fin 2)
      (MvPolynomial.C m) * X * (X + 1) * Y
  let poly_G_final : MvPolynomial (Fin 2) (ZMod N_val_final) :=
    if h : n = 2 then
      let X := MvPolynomial.X (0 : Fin 2)
      let Y := MvPolynomial.X (1 : Fin 2)
      X - X * Y
    else
      MvPolynomial.map (ZMod.castHom (by simp only [N_val_final, if_neg h]; exact dvd_refl _) (ZMod N_val_final)) poly_G_12
  let j_map_final : ZMod n → ZMod N_val_final :=
    fun x =>
      if h : n = 2 then
        if x = 0 then 0 else 1
      else
        cast (by simp only [N_val_final, if_neg h]) (j_map_fun_12 x)
  have j_map_injective : Function.Injective j_map_fun_12 := by
    clear_value j_map_final poly_G_final N_val_final
    by_cases hn : n = 1 <;> simp_all +decide [ Function.Injective, j_map_fun_12 ];
    · subst hn; simp +decide ;
    · intros a₁ a₂ h_eq
      by_cases ha₁ : a₁ = 1 ∨ a₁ = 2
      by_cases ha₂ : a₂ = 1 ∨ a₂ = 2;
      · rcases ha₁ with ( rfl | rfl ) <;> rcases ha₂ with ( rfl | rfl ) <;> simp_all +decide [ mVal12 ];
        · split_ifs at h_eq <;> norm_cast at h_eq;
          · erw [ ZMod.natCast_eq_natCast_iff ] at h_eq ; simp_all +decide [ Nat.ModEq ];
            rcases n with ( _ | _ | _ | n ) <;> simp_all +arith +decide [ nVal12 ];
            have := h_eq ( by rintro ⟨ ⟩ ) ; rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] at this <;> simp_all +arith +decide [ mVal12 ] ;
          · erw [ ZMod.natCast_eq_natCast_iff ] at h_eq ; simp_all +decide [ Nat.ModEq ];
            rcases n with ( _ | _ | _ | _ | _ | n ) <;> simp_all +arith +decide [ nVal12 ];
            have := h_eq ( by rintro ⟨ ⟩ ) ; rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] at this <;> linarith [ show mVal12 ( n + 5 ) > n + 5 from by { unfold mVal12; split_ifs <;> omega } ] ;
        · rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> norm_num [ ZMod, nVal12 ] at *;
          · rcases k with ( _ | _ | k ) <;> norm_cast at * ; simp_all +arith +decide ;
            · cases h_eq ( by decide );
            · erw [ eq_comm, ZMod.natCast_eq_natCast_iff ] at h_eq ; norm_num [ Nat.ModEq, Nat.mul_mod ] at h_eq;
              unfold nVal12 at h_eq ; norm_num [ Nat.add_mod, Nat.mul_mod ] at h_eq;
              unfold mVal12 at h_eq ; norm_num [ Nat.add_mod, Nat.mul_mod ] at h_eq;
              simp +arith +decide [ Nat.mod_eq_of_lt ] at h_eq;
              cases h_eq;
          · rcases k with ( _ | _ | k ) <;> norm_cast at *;
            erw [ eq_comm, ZMod.natCast_eq_natCast_iff ] at h_eq ; norm_num [ Nat.ModEq, Nat.mul_mod ] at h_eq;
            unfold nVal12 at h_eq ; norm_num [ Nat.mod_eq_of_lt ] at h_eq;
            unfold mVal12 at h_eq ; norm_num [ Nat.mod_eq_of_lt ] at h_eq;
            exact absurd ( h_eq ( by rintro ⟨ ⟩ ) ) ( by rw [ Nat.mod_eq_of_lt ] <;> linarith );
      · split_ifs at h_eq <;> simp_all +decide ;
        · have h_mod : 2 * (mVal12 n : ℕ) ≡ 4 * a₂.val [MOD 4] := by
            have h_mod : 2 * (mVal12 n : ℕ) ≡ 4 * a₂.val [MOD nVal12 n] := by
              simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
            exact h_mod.of_dvd <| by unfold nVal12; aesop;
          rcases Nat.even_or_odd' ( mVal12 n ) with ⟨ k, hk | hk ⟩ <;> simp_all +decide [ Nat.ModEq, Nat.mul_mod ];
          · unfold mVal12 at hk; split_ifs at hk <;> omega;
          · grind +ring;
        · have h_eq_mod : 3 ≡ 4 * a₂.val [MOD nVal12 n] := by
            simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
          have := congr_arg ( · % 4 ) h_eq_mod; norm_num [ Nat.ModEq, Nat.mul_mod ] at this;
          rcases n with ( _ | _ | _ | n ) <;> simp_all +arith +decide [ nVal12 ];
      · by_cases ha₂ : a₂ = 1 ∨ a₂ = 2 <;> simp_all +decide [ not_or ];
        · have h_contra : 4 * a₁.val ≡ 2 * mVal12 n [MOD nVal12 n] ∨ 4 * a₁.val ≡ 3 [MOD nVal12 n] := by
            split_ifs at h_eq <;> simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
          rcases h_contra with h | h <;> have := congr_arg ( · % 4 ) h <;> norm_num [ Nat.ModEq, Nat.mul_mod ] at this ⊢ <;> rcases Nat.even_or_odd' ( mVal12 n ) with ⟨ k, hk | hk ⟩ <;> simp_all +decide [ Nat.ModEq, Nat.add_mod, Nat.mul_mod ] ;
          · unfold mVal12 at hk; split_ifs at hk <;> omega;
          · unfold nVal12 at *; simp_all +decide [ Nat.add_mod, Nat.mul_mod ] ;
            have := Nat.mod_lt k zero_lt_four; interval_cases k % 4 <;> contradiction;
          · unfold mVal12 at hk; split_ifs at hk <;> omega;
          · unfold nVal12 at h; simp_all +decide ;
            have := congr_arg ( · % 4 ) h; norm_num [ Nat.add_mod, Nat.mul_mod ] at this;
        · have h_cast : a₁.val ≡ a₂.val [MOD mVal12 n] := by
            have h_cast : 4 * a₁.val ≡ 4 * a₂.val [MOD nVal12 n] := by
              simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
            unfold nVal12 at h_cast; simp_all +decide [ Nat.ModEq, Nat.mul_mod_mul_left ] ;
          have h_val_eq : a₁.val = a₂.val := by
            have h_val_eq : a₁.val < mVal12 n ∧ a₂.val < mVal12 n := by
              exact ⟨ lt_of_lt_of_le ( ZMod.val_lt a₁ ) ( by unfold mVal12; split_ifs <;> linarith ), lt_of_lt_of_le ( ZMod.val_lt a₂ ) ( by unfold mVal12; split_ifs <;> linarith ) ⟩;
            exact Nat.mod_eq_of_lt h_val_eq.1 ▸ Nat.mod_eq_of_lt h_val_eq.2 ▸ h_cast;
          exact ZMod.val_injective n h_val_eq
  have poly_G_final_degree : poly_G_final.totalDegree ≤ 3 := by
    by_cases hn : n = 2;
    · simp [hn, poly_G_final];
      refine' le_trans ( MvPolynomial.totalDegree_sub _ _ ) _ ; norm_num [ MvPolynomial.totalDegree_X ];
      norm_num [ MvPolynomial.totalDegree, MvPolynomial.X ];
      norm_num [ Finsupp.sum_add_index' ];
    · have h_total_degree_map : poly_G_final.totalDegree ≤ poly_G_12.totalDegree := by
        simp only [poly_G_final];
        simp +decide [ hn, MvPolynomial.totalDegree ];
        intro b hb; contrapose! hb; simp_all +decide [ MvPolynomial.coeff_map ] ;
        rw [ MvPolynomial.coeff_eq_zero_of_totalDegree_lt ] <;> aesop;
      have poly_G_degree : poly_G_12.totalDegree ≤ 3 := by
        unfold poly_G_12
        split_ifs with h
        · simp
        · show (MvPolynomial.C (mVal12 n : ZMod (nVal12 n)) * MvPolynomial.X 0 *
                  (MvPolynomial.X 0 + 1) * MvPolynomial.X 1 :
                  MvPolynomial (Fin 2) (ZMod (nVal12 n))).totalDegree ≤ 3
          haveI : Fact (1 < nVal12 n) := ⟨by unfold nVal12; simp [h]; unfold mVal12; split_ifs <;> omega⟩
          have h1 := MvPolynomial.totalDegree_mul
            (MvPolynomial.C (mVal12 n : ZMod (nVal12 n)) * MvPolynomial.X 0 * (MvPolynomial.X 0 + 1) :
              MvPolynomial (Fin 2) (ZMod (nVal12 n)))
            (MvPolynomial.X (1 : Fin 2))
          have h2 := MvPolynomial.totalDegree_mul
            (MvPolynomial.C (mVal12 n : ZMod (nVal12 n)) * MvPolynomial.X 0 :
              MvPolynomial (Fin 2) (ZMod (nVal12 n)))
            (MvPolynomial.X (0 : Fin 2) + 1)
          have h3 := MvPolynomial.totalDegree_mul
            (MvPolynomial.C (mVal12 n : ZMod (nVal12 n)) : MvPolynomial (Fin 2) (ZMod (nVal12 n)))
            (MvPolynomial.X (0 : Fin 2))
          have hX0 : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) (ZMod (nVal12 n))).totalDegree = 1 :=
            MvPolynomial.totalDegree_X _
          have hX1 : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) (ZMod (nVal12 n))).totalDegree = 1 :=
            MvPolynomial.totalDegree_X _
          have hXadd : (MvPolynomial.X (0 : Fin 2) + 1 : MvPolynomial (Fin 2) (ZMod (nVal12 n))).totalDegree ≤ 1 :=
            le_trans (MvPolynomial.totalDegree_add _ _)
              (by rw [hX0, MvPolynomial.totalDegree_one]; norm_num)
          have hC : (MvPolynomial.C (mVal12 n : ZMod (nVal12 n)) : MvPolynomial (Fin 2) (ZMod (nVal12 n))).totalDegree = 0 :=
            MvPolynomial.totalDegree_C _
          linarith
      exact h_total_degree_map.trans poly_G_degree
  have j_map_final_injective : Function.Injective j_map_final := by
    intro a₁ a₂ h_eq
    by_cases h : n = 2
    · subst h
      simp +decide [j_map_final] at h_eq
      fin_cases a₁ <;> fin_cases a₂ <;>
        (first | rfl | (norm_num at h_eq; cases h_eq))
    · have h_eq_cast : j_map_fun_12 a₁ = j_map_fun_12 a₂ := by
        simpa [j_map_final, h] using h_eq
      exact j_map_injective h_eq_cast
  have poly_G_final_works : representation (kroneckerDelta n 1 2)
      (fun v => poly_G_final.eval ![v.1, v.2]) (⟨j_map_final, j_map_final_injective⟩) := by
    have poly_G_works_n_ne_2 : ∀ (hn : n ≠ 2),
        representation (kroneckerDelta n 1 2) (fun v => poly_G_12.eval ![v.1, v.2]) (⟨j_map_fun_12, j_map_injective⟩) := by
      clear_value j_map_final poly_G_final N_val_final
      have poly_G_eval_1_2 : poly_G_12.eval ![j_map_fun_12 1, j_map_fun_12 2] = j_map_fun_12 1 := by
        have h_simp : (mVal12 n : ZMod (nVal12 n)) * (2 * mVal12 n) * (2 * mVal12 n + 1) * 3 = 2 * mVal12 n := by
          have m_val_odd : Odd (mVal12 n) := by
            unfold mVal12; by_cases h : n % 2 = 1 <;> simp +decide [ * ] ;
            · exact Nat.odd_iff.mpr h;
            · grind
          have h_mod : 12 * (mVal12 n) ^ 3 + 6 * (mVal12 n) ^ 2 ≡ 2 * (mVal12 n) [ZMOD 4 * (mVal12 n)] := by
            rw [ Int.modEq_iff_dvd ];
            rcases Nat.even_or_odd' ( mVal12 n ) with ⟨ c, d | d ⟩ <;> push_cast [ * ] <;> ring_nf;
            · exact absurd m_val_odd ( by simp +decide [ d, parity_simps ] );
            · exact ⟨ -4 - c * 15 - c ^ 2 * 12, by ring ⟩;
          norm_cast at *;
          erw [ ZMod.natCast_eq_natCast_iff ] at *;
          unfold nVal12; ring_nf at *; aesop;
        have hn0 : n ≠ 0 := NeZero.ne n
        cases n with
        | zero => cases (hn0 rfl)
        | succ n1 =>
          cases n1 with
          | zero => rfl
          | succ n2 =>
            convert h_simp using 1;
            · unfold poly_G_12; norm_num [ j_map_fun_12 ] ; ring_nf;
              simp +decide [ ZMod ];
              cases ‹ℕ› <;> simp +decide [ Fin.ext_iff ] at *;
              exact fun h => absurd h ( by exact Nat.ne_of_beq_eq_false rfl )
            · unfold j_map_fun_12; aesop;
      have j_map_fun_zero_of_ne_2 : ∀ (hn : n ≠ 2), j_map_fun_12 0 = 0 := by
        intro hn; unfold j_map_fun_12;
        rcases n with ( _ | _ | _ | n ) <;> norm_num [ ZMod.val ] at *;
        rcases n with ( _ | _ | n ) <;> norm_num [ mVal12 ] at *;
        · native_decide
        · native_decide
        · have h01 : (0 : ZMod (n + 5)) ≠ 1 := by
            have : Fact (1 < n + 5) := ⟨by omega⟩; exact zero_ne_one
          have h02 : (0 : ZMod (n + 5)) ≠ 2 := by
            intro heq
            have h := congr_arg ZMod.val heq
            rw [ZMod.val_zero] at h
            rw [show (2 : ZMod (n + 5)) = ((2 : ℕ) : ZMod (n + 5)) from by norm_cast] at h
            rw [ZMod.val_natCast] at h
            have : 2 % (n + 5) = 2 := Nat.mod_eq_of_lt (by omega)
            linarith
          simp [h01, h02]
          refine mul_eq_zero_of_right 4 ?_
          refine (ZMod.natCast_eq_zero_iff (↑0) (nVal12 (n + 1 + 1 + 1 + 1 + 1))).mpr ?_
          dsimp [nVal12, mVal12]; norm_num;
      have poly_G_eval_y_ne_2 : ∀ (x y : ZMod n) (hy : y ≠ 2),
          poly_G_12.eval ![j_map_fun_12 x, j_map_fun_12 y] = 0 := by
        intro x y hy
        unfold poly_G_12;
        by_cases hy1 : y = 1 ∨ y = 2;
        · cases hy1 <;> simp_all +decide [ j_map_fun_12 ];
          split_ifs <;> simp_all +decide ;
          · have h_mod : (mVal12 n : ℕ) * (2 * mVal12 n) * (2 * mVal12 n + 1) * (2 * mVal12 n) ≡ 0 [MOD 4 * mVal12 n] := by
              exact Nat.modEq_zero_iff_dvd.mpr ⟨ mVal12 n ^ 2 * ( 2 * mVal12 n + 1 ), by ring ⟩;
            convert h_mod using 1;
            rw [ ← ZMod.natCast_eq_natCast_iff ] ; norm_num [ nVal12 ] ; ring_nf;
            rw [ show nVal12 n = 4 * mVal12 n from ?_ ];
            unfold nVal12; aesop;
          · norm_cast at *;
            rw [ ZMod.natCast_eq_zero_iff ];
            exact ⟨ 6 * mVal12 n, by rw [ show nVal12 n = 4 * mVal12 n by unfold nVal12; aesop ] ; ring_nf ⟩;
          · have h4m : (4 * mVal12 n : ZMod (nVal12 n)) = 0 := by
              norm_cast; rw [ ZMod.natCast_eq_zero_iff ]; unfold nVal12; aesop;
            grind +ring;
        · unfold j_map_fun_12;
          split_ifs <;> simp_all +decide [ MvPolynomial.eval_X ];
          · have h_factor : (4 * mVal12 n : ZMod (nVal12 n)) = 0 := by
              norm_cast; rw [ ZMod.natCast_eq_zero_iff ] ; unfold nVal12 ; aesop;
            grind;
          · have h_zero : (4 * mVal12 n : ZMod (nVal12 n)) = 0 := by
              norm_cast; rw [ ZMod.natCast_eq_zero_iff ] ; unfold nVal12 ; aesop;
            grind;
          · have h_mod : (4 * mVal12 n : ZMod (nVal12 n)) = 0 := by
              norm_cast; rw [ ZMod.natCast_eq_zero_iff ] ; unfold nVal12 ; aesop;
            grind +ring
      have poly_G_eval_y_eq_2_x_ne_1 : ∀ (x y : ZMod n) (hy : y = 2) (hx : x ≠ 1),
          poly_G_12.eval ![j_map_fun_12 x, j_map_fun_12 y] = 0 := by
        intro x y hy hx
        by_cases hn : n = 1 <;> simp_all +decide [ poly_G_12 ];
        unfold j_map_fun_12;
        have h_mod : (4 * mVal12 n : ZMod (nVal12 n)) = 0 := by
          norm_cast;
          rw [ ZMod.natCast_eq_zero_iff ];
          unfold nVal12; aesop;
        grind +ring
      intro hn x y;
      by_cases hy : y = 2 <;> by_cases hx : x = 1 <;> simp_all +decide [ kroneckerDelta, -j_map_fun_zero_of_ne_2, -poly_G_eval_y_eq_2_x_ne_1, -poly_G_eval_y_ne_2, -poly_G_eval_1_2 ];
      · exact Eq.symm poly_G_eval_1_2;
      · convert poly_G_eval_y_eq_2_x_ne_1 x y hy hx |> Eq.symm using 1;
        · exact j_map_fun_zero_of_ne_2 hn;
        · rw [ hy ];
      · rw [ poly_G_eval_y_ne_2 _ _ (by assumption) ];
        exact j_map_fun_zero_of_ne_2 hn;
      · rw [ poly_G_eval_y_ne_2 _ _ hy ];
        exact j_map_fun_zero_of_ne_2 hn
    by_cases hn : n = 2;
    · subst hn;
      intro x y
      dsimp [j_map_final, poly_G_final, kroneckerDelta];
      simp
      fin_cases x <;> fin_cases y <;>
      exact ZMod.valMinAbs_inj.mp rfl
    · convert poly_G_works_n_ne_2 hn using 1;
      · simp only [N_val_final, if_neg hn];
      · rw [ show poly_G_final = MvPolynomial.map ( ZMod.castHom ( by simp only [N_val_final, if_neg hn]; exact dvd_refl _ ) ( ZMod N_val_final ) ) poly_G_12 from ?_ ];
        · simp +decide [ MvPolynomial.eval₂_eq' ];
          simp +decide [ MvPolynomial.eval_eq' ];
          have hNeq : N_val_final = nVal12 n := if_neg hn
          rw [hNeq]
          apply heq_of_eq; ext v
          simp
        · simp only [poly_G_final]; aesop;
      · simp only [j_map_final];
        congr! 2;
        grind
  use N_val_final;
  use poly_G_final;
  exact ⟨ ⟨ _, poly_G_final_works ⟩, poly_G_final_degree ⟩

/-
g(x, y) = 4nxy(y - 1) mod 16n, j = (0, 8n, 1, 2, 16, 20,..., 4*(n-1))
-/
/-- The embedding `ZMod n → ZMod (16 n)` used in the degree-three representation of
`δ_{2,3}`. -/
def jMap23Final (n : ℕ) (x : ZMod n) : ZMod (16 * n) :=
  if x = 2 then 1
  else if x = 3 then 2
  else if x = 1 then 8 * n
  else 4 * x.val

/-- The degree-three polynomial representing `δ_{2,3}` over `ZMod (16 n)`. -/
def poly23Final (n : ℕ) : MvPolynomial (Fin 2) (ZMod (16 * n)) :=
  let X := MvPolynomial.X (0 : Fin 2)
  let Y := MvPolynomial.X (1 : Fin 2)
  (C (4 * n : ZMod (16 * n))) * X * Y * (Y - 1)

theorem cubic_d_23 (n : ℕ) [NeZero n] :
    representedByPolynomialOfDegree (kroneckerDelta n 2 3) 3 := by
  by_cases hn : n ≥ 4;
  · -- Since $n \geq 4$, we can apply the lemma `poly_23_final_represents`.
    have j_map_23_final_injective {n : ℕ} (hn : n ≥ 2) : Function.Injective (jMap23Final n) := by
      intro x y hxy
      simp only [jMap23Final] at hxy
      by_cases hx : x = 2 ∨ x = 3 ∨ x = 1
      by_cases hy : y = 2 ∨ y = 3 ∨ y = 1
      · rcases hx with ( rfl | rfl | rfl ) <;> rcases hy with ( rfl | rfl | rfl ) <;> simp +decide at hxy ⊢
        simp_all +decide [ ZMod ];
        -- Since $16n \geq 32$, the elements $1$ and $2$ are distinct in $ZMod (16n)$.
        have h_distinct : (1 : ZMod (16 * n)) ≠ 2 := by
          have h_distinct : (1 : ℕ) % (16 * n) ≠ (2 : ℕ) % (16 * n) := by
            rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> linarith
          exact fun h => h_distinct <| by simpa [ ← ZMod.natCast_eq_natCast_iff' ] using h;
        cases n <;> simp_all +decide [ ZMod ];
        · -- Since $1 \neq 2$ in $ZMod (16n)$, we have a contradiction.
          have h_contra : ¬(1 : ZMod (16 * n)) = 2 := by
            intro h; rcases n with ( _ | _ | n ) <;> cases h;
          -- Since $n \geq 2$, we have $8n \geq 16$, and thus $8n \neq 1$ in $ZMod (16n)$.
          have h_contra : (8 * n : ZMod (16 * n)) ≠ 1 := by
            intro h
            have : 8 * n ≡ 1 [MOD 16 * n] := by
              erw [ ← ZMod.natCast_eq_natCast_iff ] ; aesop;
            rw [ Nat.ModEq ] at this; rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] at this <;> linarith;
          grind +ring;
        · -- Since $2 \neq 1$ in $ZMod 16n$, this leads to a contradiction, implying that our assumption $3 \neq 2$ must be false.
          have h_contra : ¬(2 : ZMod (16 * n)) = 1 := by
            intro h; rcases n with ( _ | _ | n ) <;> cases h;
          exact Classical.not_not.1 fun h => h_contra <| hxy h ▸ rfl;
        · split_ifs at hxy <;> norm_cast at hxy ⊢ ; simp_all +decide ; (
          grind +ring);
          · grind;
          · grind;
          · grind +ring;
          · erw [ eq_comm, ZMod.natCast_eq_natCast_iff ] at hxy ; norm_num [ Nat.modEq_iff_dvd ] at hxy ⊢ ; obtain ⟨ k, hk ⟩ := hxy ; nlinarith [ show k = 0 by nlinarith ] ;
        · split_ifs at hxy <;> norm_cast at hxy ⊢ ; simp_all +decide [ ZMod ] ; (
          rcases n with ( _ | _ | _ | _ | n ) <;> cases ‹(1 : ZMod _) = _› ; trivial;
          grind);
          -- Since $8n$ is not congruent to $1$ modulo $16n$ for $n \geq 2$, we have a contradiction.
          have h_contra : ¬(8 * n : ZMod (16 * n)) = 1 := by
            have h_contra : ¬(8 * n : ℕ) ≡ 1 [MOD 16 * n] := by
              rw [ Nat.ModEq, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> linarith [ show n > 0 from pos_of_gt hn ] ;
            exact fun h => h_contra <| by simpa [ ← ZMod.natCast_eq_natCast_iff ] using h;
          cases n <;> simp_all +decide ;
        · split_ifs at hxy <;> norm_cast at hxy ⊢ ; simp_all +decide [ ZMod ] ; (
          grind);
          · rcases n with ( _ | _ | _ | _ | _ | _ | _ | n ) <;> cases ‹ ( 3 : ZMod _ ) = 2 › ; contradiction;
          · -- Since $8n \equiv 2 \pmod{16n}$ is impossible, we have a contradiction.
            have h_contra : ¬(8 * n ≡ 2 [MOD 16 * n]) := by
              rw [ Nat.ModEq, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> linarith [ show n > 0 from pos_of_gt hn ] ;
            exact False.elim <| h_contra <| by rw [ ← ZMod.natCast_eq_natCast_iff ] ; aesop;
      · split_ifs at hxy <;> simp_all +decide ;
        · norm_cast at hxy;
          -- Since $4 * y.val \equiv 1 \pmod{16n}$, we have $4 * y.val = 1 + k * 16n$ for some integer $k$.
          obtain ⟨k, hk⟩ : ∃ k : ℤ, 4 * y.val = 1 + k * 16 * n := by
            have h_cong : (4 * y.val : ℤ) ≡ 1 [ZMOD 16 * n] := by
              erw [ ← ZMod.intCast_eq_intCast_iff ] ; aesop;
            exact h_cong.symm.dvd.imp fun k hk => by linarith;
          exact absurd ( congr_arg ( · % 4 ) hk ) ( by norm_num [ Int.add_emod, Int.mul_emod ] );
        · have h_contra : (2 - 4 * y.val : ℤ) ≡ 0 [ZMOD 16 * n] := by
            erw [ ← ZMod.intCast_eq_intCast_iff ] ; aesop;
          rw [ Int.modEq_zero_iff_dvd ] at h_contra ; obtain ⟨ k, hk ⟩ := h_contra ; replace hk := congr_arg ( · % 4 ) hk ; norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod ] at hk;
        · -- Since $8n \equiv 4y.val \pmod{16n}$, we have $4n \equiv 2y.val \pmod{8n}$. This implies $2n \equiv y.val \pmod{4n}$.
          have h_cong : 2 * n ≡ y.val [MOD 4 * n] := by
            have h_cong : 8 * n ≡ 4 * y.val [MOD 16 * n] := by
              erw [ ← ZMod.natCast_eq_natCast_iff ] ; aesop;
            rw [ Nat.modEq_iff_dvd ] at *;
            exact Exists.elim h_cong fun k hk => ⟨ k, by push_cast at *; linarith ⟩ ;
          -- Since $y$ is an element of $ZMod n$, its value $y.val$ is between $0$ and $n-1$. Therefore, $y.val = 2n$ implies $2n < n$, which is impossible.
          have h_impossible : y.val < n := by
            rcases n with ( _ | _ | n ) <;> simp_all +decide [ ZMod ] ;
            exact Nat.lt_succ_iff.mp y.val_lt
          exact absurd h_cong ( by rw [ Nat.ModEq, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> linarith );
      · by_cases hy : y = 2 ∨ y = 3 ∨ y = 1 <;> simp_all +decide ;
        · split_ifs at hxy <;> norm_cast at hxy;
          · have := congr_arg ( fun z => z.val ) hxy ; norm_num [ ZMod.val_add, ZMod.val_mul ] at this;
            replace this := congr_arg ( · % 4 ) this ; norm_num [ Nat.add_mod, Nat.mul_mod ] at this;
            rcases n with ( _ | _ | n ) <;> simp_all +arith +decide [ ZMod.val ];
            erw [ Nat.mod_mod_of_dvd _ ( by exact ⟨ 4 * n + 8, by ring ⟩ ) ] at this;
            erw [ Nat.mod_eq_zero_of_dvd ( dvd_mul_right _ _ ) ] at this ;
            cases this;
          · have := congr_arg ( ·.val ) hxy; norm_num [ ZMod.val_add, ZMod.val_mul ] at this; have := congr_arg ( · % 4 ) this; norm_num [ Nat.add_mod, Nat.mul_mod ] at this;
            erw [ ZMod.val_cast_of_lt ] at this <;> try linarith ;
            rcases n with ( _ | _ | n ) <;> simp_all +arith +decide [ Nat.mod_eq_of_lt ];
            -- Since $4 * x.val$ is divisible by $4$, we have $4 * x.val % 4 = 0$.
            have h_div : 4 * x.val % 4 = 0 := by
              norm_num [ Nat.mul_mod ] at this ⊢ ;
            erw [ Nat.mod_mod_of_dvd _ ( dvd_add ( dvd_mul_of_dvd_left ( by decide ) _ ) ( by decide ) ) ] at this; simp_all +decide ;
            cases this;
          · erw [ ZMod.natCast_eq_natCast_iff ] at hxy ; norm_num [ Nat.ModEq, Nat.mul_mod ] at hxy ⊢
            rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
            rw [ Nat.mod_eq_of_lt ] at hxy <;> try linarith [ show x.val < n + 2 from x.val_lt ] ;
          · grind +ring;
        · -- Since $4 * x.val = 4 * y.val$, we can divide both sides by 4 to get $x.val = y.val$.
          have h_val_eq : x.val = y.val := by
            norm_cast at hxy ⊢
            erw [ ZMod.natCast_eq_natCast_iff ] at hxy ; norm_num [ Nat.ModEq, Nat.mul_mod ] at hxy ⊢
            rcases n with ( _ | _ | n ) <;> simp_all +arith +decide [ Nat.mod_eq_of_lt ];
            rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] at hxy <;> linarith [ show x.val < n + 2 from x.val_lt, show y.val < n + 2 from y.val_lt ] ;
          convert h_val_eq using 1
          rcases n with ( _ | _ | n ) <;> simp_all +decide [ ZMod, Fin.ext_iff ];
          exact h_val_eq
    have j_map_23_final_injective_all : Function.Injective (jMap23Final n) := by
      have hn2 : n ≥ 2 := by linarith
      exact j_map_23_final_injective hn2
    have poly_23_final_represents : representation (kroneckerDelta n 2 3) (fun v => (poly23Final n).eval ![v.1, v.2]) ⟨jMap23Final n, j_map_23_final_injective_all⟩ := by
      intro x y; by_cases hx : x = 2 <;> by_cases hy : y = 3 <;> simp +decide [ hx, hy, poly23Final ] ;
      · unfold jMap23Final; simp +decide [ kroneckerDelta ] ; ring_nf;
        have h3ne2 : ( 3 : ZMod n ) ≠ 2 := by
          intro h; rcases n with ( _ | _ | _ | _ | n ) <;> cases h ; contradiction
        have h1ne2 : ( 1 : ZMod n ) ≠ 2 := by
          intro h; rcases n with ( _ | _ | _ | _ | n ) <;> cases h ; contradiction
        simp +decide [ h3ne2, h1ne2 ] ; ring_nf;
        rcases n with ( _ | _ | _ | _ | n ) <;> norm_num [ ZMod, Fin.ext_iff ] at *;
        rintro ⟨ ⟩;
      · -- Since $y \neq 3$, we have $\delta_{2,3}(2, y) = 0$.
        have h_delta : kroneckerDelta n 2 3 (2, y) = 0 := by
          exact if_neg ( by aesop )
        simp [h_delta] at *;
        -- Substitute the values of jMap23Final n 0 and jMap23Final n 2 into the equation.
        simp [jMap23Final] at *;
        -- Since $y \neq 2$, $y \neq 3$, and $y \neq 1$, the expression simplifies to $0$.
        by_cases hy2 : y = 2 <;> by_cases hy3 : y = 3 <;> by_cases hy1 : y = 1 <;> simp_all +decide ;
        · rcases n with ( _ | _ | _ | _ | n ) <;> cases hy2 ; contradiction;
        · rcases n with ( _ | _ | _ | _ | n ) <;> norm_cast at *;
        · split_ifs <;> ring_nf at * <;> norm_cast at * <;> simp_all +decide ;
          · rcases n with ( _ | _ | _ | _ | n ) <;> cases ‹_› ; contradiction;
            contradiction;
          · rcases n with ( _ | _ | _ | _ | n ) <;> cases ‹_› ; contradiction;
            contradiction;
          · rcases n with ( _ | _ | _ | n ) <;> cases ‹_› ; contradiction
          · norm_cast; norm_num [ show n ^ 2 * 32 = 16 * n * ( n * 2 ) by ring, show n ^ 3 * 256 = 16 * n * ( n ^ 2 * 16 ) by ring ] ;
        · -- Since $y \neq 0$, $y \neq 2$, $y \neq 3$, and $y \neq 1$, the expression simplifies to $0$.
          by_contra h_contra
          have h_y_zero : y = 0 := by
            split_ifs at h_contra <;> norm_cast at * ; simp_all +decide ;
            · rcases n with ( _ | _ | _ | n ) <;> cases ‹ ( 0 : ZMod _ ) = 2 › ; contradiction;
              contradiction;
            · rcases n with ( _ | _ | _ | _ | n ) <;> cases ‹ ( 0 : ZMod _ ) = 3 › ; contradiction;
              contradiction;
            · rcases n with ( _ | _ | _ | _ | n ) <;> cases ‹ ( 0 : ZMod _ ) = 1 › ; contradiction;
            · -- Since $4n \cdot 4y \cdot (4y - 1)$ is a multiple of $16n$, it is congruent to $0$ modulo $16n$.
              have h_mul : (4 * n : ℤ) * (4 * y.val) * (4 * y.val - 1) ≡ 0 [ZMOD 16 * n] := by
                exact Int.modEq_zero_iff_dvd.mpr ⟨ y.val * ( 4 * y.val - 1 ), by ring ⟩
              erw [ ← ZMod.intCast_eq_intCast_iff ] at * ; aesop;
          simp [h_y_zero] at *;
          split_ifs at h_contra <;> simp_all +decide ;
      · simp +decide [ *, kroneckerDelta ];
        unfold jMap23Final; simp +decide [ hx ] ;
        rcases n with ( _ | _ | _ | _ | n ) <;> norm_cast;
        -- Since $x \neq 2$, the term $4 * (n + 4) * 2 * 2$ simplifies to $16 * (n + 4)$, which is congruent to $0$ modulo $16 * (n + 4)$.
        have h_zero : (4 * (n + 4) * 2 * 2 : ZMod (16 * (n + 4))) = 0 := by
          norm_cast
          erw [ ZMod.natCast_eq_zero_iff ] ; exact ⟨ 1, by ring ⟩ ;
        -- Since $4 * (n + 4) * 2 * 2 = 0$ in $ZMod (16 * (n + 4))$, multiplying it by any integer will still yield $0$.
        have h_zero_mul : ∀ k : ℤ, (4 * (n + 4) * 2 * 2 : ZMod (16 * (n + 4))) * k = 0 := by
          exact fun k => by rw [ h_zero, MulZeroClass.zero_mul ] ;
        convert h_zero_mul ( x.val : ℤ ) using 1 ; ring_nf!;
        · -- Since $16 * n + 64 = 16 * (n + 4)$, and in $ZMod (16 * (n + 4))$, this is congruent to $0$.
          have h_cong : (16 * n + 64 : ZMod (16 * (n + 4))) = 0 := by
            grind +ring
          convert congr_arg ( fun z : ZMod ( 16 * ( n + 4 ) ) => z * x.val ) h_cong.symm using 1 ; ring_nf!; norm_cast; ring_nf;
          norm_num +zetaDelta at *;
        · split_ifs <;> norm_num [ Int.subNatNat_eq_coe ] ; ring_nf at * ; aesop ( simp_config := { decide := true } ) ;
          · grind;
          · grind;
      · -- Since $x \neq 2$ and $y \neq 3$, the Kronecker delta $\delta_{23}(x, y)$ is 0.
        have h_delta_zero : kroneckerDelta n 2 3 (x, y) = 0 := by
          exact if_neg ( by aesop );
        -- Since $x \neq 2$ and $y \neq 3$, the term $(4n) * X * Y * (Y - 1)$ will be zero because $X$ and $Y$ are not 2 or 3, respectively.
        have h_poly_zero : (4 * n : ZMod (16 * n)) * jMap23Final n x * jMap23Final n y * (jMap23Final n y - 1) = 0 := by
          by_cases hy1 : y = 1 <;> simp +decide [ *, jMap23Final ];
          · have h_zero : (4 * n : ZMod (16 * n)) * (8 * n : ZMod (16 * n)) = 0 := by
              norm_cast
              erw [ ZMod.natCast_eq_zero_iff ] ; exact ⟨ 2 * n, by ring ⟩ ;
            grind;
          · split_ifs <;> simp_all +decide [ mul_assoc, mul_left_comm, mul_comm ];
            · -- Since $n$ is a multiple of $16n$, multiplying by $n$ will result in $0$ in $ZMod (16n)$.
              have h_mul_zero : (n : ZMod (16 * n)) * 32 = 0 := by
                norm_cast;
                rw [ ZMod.natCast_eq_zero_iff ] ; exact ⟨ 2, by ring ⟩;
              linear_combination' h_mul_zero * y.cast * ( 4 * y.cast - 1 );
            · -- Since $16n^2$ is a multiple of $16n$, it is zero in $ZMod (16n)$.
              have h_zero : (16 * n^2 : ZMod (16 * n)) = 0 := by
                norm_cast;
                rw [ ZMod.natCast_eq_zero_iff ] ; exact ⟨ n, by ring ⟩;
              convert congr_arg ( · * ( y.cast * ( 8 * ( 4 * y.cast - 1 ) ) ) ) h_zero using 1 <;> ring;
            · -- Since $16n$ is a multiple of $n$, multiplying by $n$ gives zero in $ZMod (16n)$.
              have h_zero : (16 * n : ZMod (16 * n)) = 0 := by
                norm_cast;
                erw [ ZMod.natCast_self ];
              linear_combination' h_zero * ( x.cast * ( y.cast * ( 4 * y.cast - 1 ) ) ) * 4;
        rw [ h_delta_zero, h_poly_zero ];
        rcases n with ( _ | _ | _ | _ | n ) <;> norm_cast
    use 16 * n, poly23Final n;
    have poly_23_final_degree : (poly23Final n).totalDegree ≤ 3 := by
      refine' le_trans _ ( _ : _ ≤ _ );
      exact ( poly23Final n |> MvPolynomial.support |> Finset.sup <| fun x => x 0 + x 1 );
      · simp +decide [ MvPolynomial.totalDegree ];
        intro b hb; refine' le_trans _ ( Finset.le_sup <| show b ∈ MvPolynomial.support ( poly23Final n ) from by aesop ) ; simp +decide [ Finsupp.sum_fintype ] ;
      · simp +decide [ poly23Final ];
        intro b hb; contrapose! hb; simp_all +decide [ mul_sub ] ;
        simp_all +decide [ mul_assoc, MvPolynomial.X ];
        erw [ MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul ] ; aesop
    exact ⟨ ⟨ ⟨ jMap23Final n, j_map_23_final_injective_all ⟩, poly_23_final_represents ⟩, poly_23_final_degree ⟩;
  · interval_cases n <;> simp_all +decide only [representedByPolynomialOfDegree];
    · exact False.elim <| NeZero.ne 0 rfl;
    · use 1;
      refine' ⟨ 0, _, _ ⟩ <;> norm_num [ represents ];
      exact ⟨ ⟨ fun x => x, by decide ⟩, by simp +decide [ representation, kroneckerDelta ] ⟩;
    · obtain ⟨ g, hg ⟩ := quadratic_d2 0 1;
      use g, hg.choose;
      exact ⟨ hg.choose_spec.1, hg.choose_spec.2.trans ( by norm_num ) ⟩;
    · obtain ⟨ g, hg ⟩ := cubic_d3_02;
      use g, MvPolynomial.eval₂ MvPolynomial.C ( fun i => if i = 0 then MvPolynomial.X 1 else MvPolynomial.X 0 ) hg.choose;
      refine' ⟨ _, _ ⟩;
      · obtain ⟨ j, hj ⟩ := hg.choose_spec.1;
        use j; intro x y; specialize hj y x; simp_all +decide [ kroneckerDelta ] ;
        convert hj using 1 <;> simp +decide [ MvPolynomial.eval₂_eq' ] ; ring_nf!;
        · fin_cases x <;> fin_cases y <;> rfl;
        · simp +decide [ MvPolynomial.eval_eq' ];
      · refine' le_trans _ hg.choose_spec.2;
        refine' le_trans ( Finset.sup_mono _ ) _;
        exact Finset.image ( fun s => Finsupp.single 0 ( s 1 ) + Finsupp.single 1 ( s 0 ) ) ( hg.choose.support );
        · intro s hs; simp_all +decide [ MvPolynomial.eval₂_eq' ] ;
          contrapose! hs; simp_all +decide [ MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul ] ;
          rw [ Finset.sum_eq_zero ] ; intros ; simp_all +decide [ MvPolynomial.X_pow_eq_monomial ];
          grind;
        · simp +decide [ Finsupp.sum_add_index' ];
          intro b hb; exact (by
          refine' le_trans _ ( Finset.le_sup ( f := fun s => s.sum fun x e => e ) ( MvPolynomial.mem_support_iff.mpr hb ) ) ; simp +decide [ Finsupp.sum_fintype ] ; ring_nf ; aesop;)

theorem cubic_d_02 (n : ℕ) [NeZero n] :
    representedByPolynomialOfDegree (kroneckerDelta n 0 2) 3 := by
  by_cases hn : n = 1 ∨ n = 2;
  · obtain rfl | rfl := hn;
    · use 1, 0; simp +decide ;
      exists ⟨ fun _ => 0, by simp +decide ⟩;
      simp +decide [ representation, kroneckerDelta ];
    · exact quadratic_d2 0 0 |> fun ⟨ n, g, h₁, h₂ ⟩ => ⟨ n, g, h₁, h₂.trans ( by norm_num ) ⟩;
  · -- Let (m, H, J) be the representation for `kroneckerDelta n 1 2`.
    obtain ⟨m, H, J, hJ⟩ : ∃ m : ℕ, ∃ H : MvPolynomial (Fin 2) (ZMod m), ∃ J : ZMod n ↪ ZMod m, (∀ x y, J (kroneckerDelta n 1 2 (x, y)) = H.eval ![J x, J y]) ∧ H.totalDegree ≤ 3 := by
      have := @cubic_d_12 n ‹_›; aesop;
    -- Define `k` as the permutation on `ZMod n` that swaps 0 and 1.
    set k : ZMod n → ZMod n := fun x => if x = 0 then 1 else if x = 1 then 0 else x;
    refine' ⟨ m, MvPolynomial.C ( J 0 + J 1 ) - H, ⟨ ⟨ J ∘ k, fun x y hxy => _ ⟩, _ ⟩, _ ⟩ <;> simp_all +decide ;
    all_goals norm_num [ kroneckerDelta ] at *;
    grind +ring;
    · intro x y; by_cases hx : x = 0 <;> by_cases hy : y = 2 <;> simp +decide [ hx, hy ] ;
      · simp +decide [ ← hJ.1, kroneckerDelta ];
        simp +zetaDelta at *;
        rcases n with ( _ | _ | _ | n ) <;> norm_num [ Fin.ext_iff, ZMod ] at *;
        simp +decide [ Fin.ext_iff, ZMod ];
        rcases n with ( _ | _ | n ) <;> simp +arith +decide at *
        all_goals exact Eq.symm (add_sub_cancel_right (J 0) (J 1))
      · simp +decide [ ← hJ.1, kroneckerDelta ];
        simp +zetaDelta at *;
        split_ifs <;> simp_all +decide [ add_comm ];
        · rcases n with ( _ | _ | _ | n ) <;> cases ‹_› ; trivial;
        · rcases n with ( _ | _ | _ | n ) <;> cases ‹_› ; contradiction;
          tauto;
      · simp +decide [ ← hJ.1, hx, kroneckerDelta ];
        grind;
      · simp +decide [ ← hJ.1, hx, hy, kroneckerDelta ];
        grind;
    · refine' le_trans _ hJ.2;
      refine' le_trans ( MvPolynomial.totalDegree_sub _ _ ) _ ; norm_num [ hJ.2 ];
      refine' le_trans _ ( Nat.zero_le _ ) ; norm_num [ MvPolynomial.totalDegree ] ; ring_nf; aesop;

/-- The modulus factor `n^3 + n^2 + 1` used in the degree-four representation of `δ_{0,1}`. -/
def kVal01 (n : ℕ) : ℕ := n^3 + n^2 + 1

/-- The embedding `ZMod n → ZMod (n * kVal01 n)` used in the degree-four representation of
`δ_{0,1}`. The modulus is kept nonzero, so `[NeZero n]` is part of the interface. -/
@[nolint unusedArguments]
def jMap01 (n : ℕ) [NeZero n] (x : ZMod n) : ZMod (n * kVal01 n) :=
  if x = 0 then 1
  else if x = 1 then 1 + n
  else (kVal01 n : ZMod (n * kVal01 n)) * (x.val : ZMod (n * kVal01 n))

/-- The degree-four polynomial representing `δ_{0,1}` over `ZMod (n * kVal01 n)`. -/
def poly01 (n : ℕ) : MvPolynomial (Fin 2) (ZMod (n * kVal01 n)) :=
  let X := MvPolynomial.X (0 : Fin 2)
  let Y := MvPolynomial.X (1 : Fin 2)
  1 + C (n : ZMod (n * kVal01 n)) * X * Y * (X - C (1 + n : ZMod (n * kVal01 n))) * (Y - 1)

theorem quartic_d_01 (n : ℕ) [NeZero n] :
    representedByPolynomialOfDegree (kroneckerDelta n 0 1) 4 := by
  have j_map_injective : Function.Injective (jMap01 n) := by
    intro x y hxy;
    unfold jMap01 at hxy;
    split_ifs at hxy <;> simp_all +decide [ ZMod.natCast_eq_zero_iff ];
    all_goals norm_cast at *;
    any_goals have := Nat.le_of_dvd ( NeZero.pos n ) hxy; rcases n with ( _ | _ | n ) <;> simp_all +decide [ kVal01 ];
    · -- Since $k_val n$ is coprime to $n$, $k_val n * y.cast$ cannot be congruent to $1$ modulo $n * k_val n$ unless $y.cast$ is $0$.
      have h_contra : kVal01 n * y.val ≡ 1 [MOD n * kVal01 n] := by
        rw [ ← ZMod.natCast_eq_natCast_iff ] ; aesop;
      have := congr_arg ( · % kVal01 n ) h_contra; norm_num [ Nat.ModEq, Nat.mul_mod, Nat.mod_eq_of_lt ] at this;
      unfold kVal01 at this; aesop;
    · have h_contra : 1 + n ≡ kVal01 n * y.val [MOD n * kVal01 n] := by
        simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
      have := congr_arg ( · % kVal01 n ) h_contra; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt ( show 1 + n < kVal01 n from by { unfold kVal01; nlinarith [ NeZero.pos n ] } ) ] at this;
      rcases n with ( _ | _ | n ) <;> simp_all +decide ;
      rw [ Nat.mod_eq_of_lt ] at this <;> norm_num [ kVal01 ] at * ; nlinarith [ pow_succ' n 2 ];
    · replace hxy := congr_arg ( fun z => z.val ) hxy ; simp_all +decide [ ZMod.val_mul ];
      rcases n with ( _ | _ | n ) <;> simp_all +decide [ ZMod.val ];
      replace hxy := congr_arg ( fun z => z % kVal01 ( n + 1 + 1 ) ) hxy ; simp_all +decide ;
      rw [ eq_comm, Nat.mod_eq_of_lt ] at hxy <;> norm_num [ kVal01 ] at *;
      · cases hxy;
      · exact Nat.lt_succ_of_le ( Nat.le_add_left _ _ );
    · have h_contra : (kVal01 n : ℕ) * x.val ≡ 1 + n [MOD n * kVal01 n] := by
        erw [ ← ZMod.natCast_eq_natCast_iff ] ; aesop;
      have := congr_arg ( · % kVal01 n ) h_contra; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt ] at this;
      rcases n with ( _ | _ | n ) <;> simp +arith +decide [ Nat.mod_eq_of_lt, kVal01 ] at *;
      rw [ eq_comm, Nat.mod_eq_of_lt ] at this <;> nlinarith only [ this ];
    · -- Since $k_val n$ is coprime to $n$, we can divide both sides of the equation by $k_val n$.
      have h_div : (x.val : ℕ) ≡ (y.val : ℕ) [MOD n] := by
        have h_div : (kVal01 n : ℕ) * x.val ≡ (kVal01 n : ℕ) * y.val [MOD n * kVal01 n] := by
          simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
        rw [ Nat.modEq_iff_dvd ] at *;
        exact h_div.imp fun a ha => by push_cast at *; nlinarith [ show 0 < kVal01 n from Nat.pos_of_ne_zero ( by unfold kVal01; aesop ) ] ;
      cases n <;> simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ]
  have poly_01_eval (x y : ZMod n) :
      (poly01 n).eval ![jMap01 n x, jMap01 n y] = jMap01 n (kroneckerDelta n 0 1 (x, y)) := by
    unfold jMap01 poly01 kroneckerDelta;
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp +decide [ hx, hy ];
    · grind;
    · split_ifs <;> simp_all +decide ;
      · rw [ neg_eq_iff_add_eq_zero ] ; ring_nf;
        norm_cast;
        rw [ ZMod.natCast_eq_zero_iff ] ; exact ⟨ 1, by unfold kVal01; ring ⟩;
      · -- Since $n^2 * k_val n$ is a multiple of $n * k_val n$, it follows that $n^2 * k_val n \equiv 0 \pmod{n * k_val n}$.
        have h_mod : (n^2 * kVal01 n : ZMod (n * kVal01 n)) = 0 := by
          norm_cast;
          rw [ ZMod.natCast_eq_zero_iff ] ; exact ⟨ n, by ring ⟩;
        linear_combination' h_mod * y.cast * ( kVal01 n * y.cast - 1 );
    · split_ifs <;> simp_all +decide [ ← mul_assoc ];
      · norm_cast ; simp +decide [ mul_comm ];
      · norm_cast ; simp +decide [ mul_comm ]
  refine' ⟨ n * ( n ^ 3 + n ^ 2 + 1 ), poly01 n, _, _ ⟩;
  · use ⟨ jMap01 n, j_map_injective ⟩;
    intro x y
    simpa using (poly_01_eval x y).symm
  · have poly_01_degree : (poly01 n).totalDegree ≤ 4 := by
      refine' le_trans ( Finset.sup_le _ ) _ <;> norm_num;
      exact 4;
      · unfold poly01;
        intro b hb; contrapose! hb; simp_all +decide [ MvPolynomial.coeff_one, mul_assoc ] ;
        split_ifs <;> simp_all +decide [ ← mul_assoc ];
        · aesop;
        · simp_all +decide [ mul_assoc, mul_sub, sub_mul, MvPolynomial.X ];
          simp_all +decide [ mul_add, add_mul, mul_comm, mul_left_comm ];
          erw [ MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul ] ; norm_num;
          erw [ MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul ] ; norm_num;
          erw [ MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial ] ; norm_num;
          simp_all +decide [ Finsupp.ext_iff, Fin.forall_fin_two ];
          rw [ Finsupp.sum_fintype ] at hb ; norm_num at hb ; split_ifs <;> norm_num at * <;> omega;
          norm_num;
      · norm_num +zetaDelta at *
    exact poly_01_degree

/-
One can use theorems above to prove theorem below.
A stronger version one should be able to prove is:
a=b: quadratic
{a,b}={0,1}: quartic
otherwise: cubic
-/

/-
Permuting the arguments of the Kronecker delta function by a permutation `σ` is equivalent to permuting the indices `a` and `b` by `σ`.
-/
lemma kronecker_delta_perm (n : ℕ) [NeZero n] (a b : ZMod n) (σ : ZMod n ≃ ZMod n) (x y : ZMod n) :
  kroneckerDelta n (σ a) (σ b) (σ x, σ y) = kroneckerDelta n a b (x, y) := by
    unfold kroneckerDelta; aesop;

/-
If `σ` fixes `0` and `1`, then `kroneckerDelta` for permuted indices has the same polynomial representation complexity as for original indices.
-/
theorem degree_perm_fix_01 (n : ℕ) [NeZero n] (a b : ZMod n) (σ : ZMod n ≃ ZMod n) (d : ℕ)
    (h0 : σ 0 = 0) (h1 : σ 1 = 1) :
    representedByPolynomialOfDegree (kroneckerDelta n (σ a) (σ b)) d →
    representedByPolynomialOfDegree (kroneckerDelta n a b) d := by
      rintro ⟨ m, k, hk ⟩;
      refine' ⟨ m, _, _, hk.2 ⟩;
      use ⟨ fun x => hk.1.choose ( σ x ), fun x y hxy => ?_ ⟩;
      intro x y; have := hk.1.choose_spec; simp_all +decide [ representation ] ;
      · convert this ( σ x ) ( σ y ) using 1 ; simp +decide [ kroneckerDelta ] ; aesop;
      · have := hk.1.choose_spec ( σ x ) ( σ y ) ; aesop;

/-
If a function `f(x, y)` is represented by a polynomial of degree `d`, then `f(y, x)` is also represented by a polynomial of degree `d`.
-/
omit [Fintype α] [DecidableEq α] in
lemma represented_swap (f : α × α → α) (d : ℕ) :
  representedByPolynomialOfDegree f d →
  representedByPolynomialOfDegree (fun p => f (p.2, p.1)) d := by
    intro h
    obtain ⟨n, hn⟩ := h
    generalize_proofs at *; (
    obtain ⟨ g, hg₁, hg₂ ⟩ := hn
    generalize_proofs at *; (
    -- Let $g'$ be the polynomial obtained by swapping the variables in $g$.
    set g' : MvPolynomial (Fin 2) (ZMod n) := MvPolynomial.rename (Equiv.swap 0 1) g
    generalize_proofs at *; (
    refine' ⟨ n, g', _, _ ⟩ <;> simp_all +decide [ represents ];
    · obtain ⟨ j, hj ⟩ := hg₁; use j; intro x y; simp_all +decide [ representation ] ;
      erw [ MvPolynomial.eval_rename ];
      congr ; ext i ; fin_cases i <;> rfl;
    · refine' le_trans _ hg₂
      generalize_proofs at *; (
      exact totalDegree_rename_le (⇑(Equiv.swap 0 1)) g))))

/-
The Kronecker delta `δ(x, y)` where `x=y=a` can be represented by a polynomial of degree 2.
-/
lemma degree_d_eq (n : ℕ) [NeZero n] (a : ZMod n) :
  representedByPolynomialOfDegree (kroneckerDelta n a a) 2 := by
    by_cases ha : n > 2 ∧ a ≠ 0 ∧ a ≠ 1 ∧ a ≠ 2;
    · -- Since `n > 2` and `a \notin {0, 1, 2}`, we can use `σ = Equiv.swap a 2` to permute the indices.
      obtain ⟨σ, hσ⟩ : ∃ σ : ZMod n ≃ ZMod n, σ 0 = 0 ∧ σ 1 = 1 ∧ σ a = 2 := by
        use Equiv.swap a 2 * Equiv.refl (ZMod n);
        simp +decide [ Equiv.swap_apply_def ];
        rcases n with ( _ | _ | _ | n ) <;> simp_all +decide [ ZMod ];
        simp_all +decide [ eq_comm ];
        exact ⟨ by rintro ⟨ ⟩, by rintro ⟨ ⟩ ⟩;
      have h_perm : representedByPolynomialOfDegree (kroneckerDelta n (σ a) (σ a)) 2 := by
        convert quadratic_d_22 n using 1 ; aesop;
      convert degree_perm_fix_01 n a a σ 2 _ _ h_perm using 1 <;> aesop ( simp_config := { singlePass := true } ) ;
    · by_cases hn : n > 2 <;> simp_all +decide;
      · by_cases ha0 : a = 0 <;> by_cases ha1 : a = 1 <;> simp_all +decide;
        · rcases n with ( _ | _ | _ | n ) <;> cases ha0 ; contradiction;
        · exact quadratic_d_00 n;
        · exact quadratic_d_11 n;
        · exact quadratic_d_22 n;
      · interval_cases n <;> simp_all +decide;
        · exact False.elim <| NeZero.ne 0 rfl;
        · fin_cases a ; simp_all +decide ;
          exact quadratic_d_00 1;
        · exact quadratic_d2 a a

/-
If `{a, b} = {0, 1}`, then `kroneckerDelta n a b` is represented by a polynomial of degree 4.
-/
lemma degree_d_01 (n : ℕ) [NeZero n] (a b : ZMod n) (h : ({a, b} : Finset (ZMod n)) = {0, 1}) :
  representedByPolynomialOfDegree (kroneckerDelta n a b) 4 := by
    by_cases h_cases : a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 0;
    · rcases h_cases with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ );
      · exact quartic_d_01 n;
      · convert represented_swap _ _ ( quartic_d_01 n ) using 1;
        exact funext fun p => by unfold kroneckerDelta; aesop;
    · simp_all +decide [ Finset.ext_iff ];
      cases h a ; cases h b ; aesop

/-
For `b \notin \{0, 1\}`, `kroneckerDelta n 0 b` is represented by a polynomial of degree 3.
-/
lemma degree_d_0_b (n : ℕ) [NeZero n] (b : ZMod n) (h0 : b ≠ 0) (h1 : b ≠ 1) :
  representedByPolynomialOfDegree (kroneckerDelta n 0 b) 3 := by
    by_contra h_contra;
    -- Consider the permutation σ that swaps b and 2.
    obtain ⟨σ, hσ⟩ : ∃ σ : ZMod n ≃ ZMod n, σ b = 2 ∧ σ 0 = 0 ∧ σ 1 = 1 := by
      -- Define the permutation σ that swaps b and 2.
      use Equiv.swap b 2 * Equiv.refl (ZMod n);
      simp +decide [ Equiv.swap_apply_def, * ];
      rcases n with ( _ | _ | _ | n ) <;> simp_all +decide [ ZMod ];
      · exact False.elim <| NeZero.ne 0 rfl;
      · fin_cases b ; trivial;
      · fin_cases b <;> contradiction;
      · simp_all +decide [ eq_comm ];
        exact ⟨ by rintro ⟨ ⟩, by rintro ⟨ ⟩ ⟩;
    -- By Lemma `degree_perm_fix_01`, we have that `kroneckerDelta n 0 b` is represented by a polynomial of degree 3.
    have h_rep : representedByPolynomialOfDegree (kroneckerDelta n (σ 0) (σ b)) 3 := by
      convert cubic_d_02 n using 1 ; aesop;
    apply h_contra;
    apply degree_perm_fix_01 n 0 b σ 3 hσ.right.left hσ.right.right h_rep

/-
For `b \notin \{0, 1\}`, `kroneckerDelta n 1 b` is represented by a polynomial of degree 3.
-/
lemma degree_d_1_b (n : ℕ) [NeZero n] (b : ZMod n) (h0 : b ≠ 0) (h1 : b ≠ 1) :
  representedByPolynomialOfDegree (kroneckerDelta n 1 b) 3 := by
    by_cases hn : n ≤ 2;
    · interval_cases n <;> simp_all +decide [ ZMod ];
      · exact False.elim <| NeZero.ne 0 rfl;
      · fin_cases b ; contradiction;
      · fin_cases b <;> contradiction;
    · by_contra h_contra;
      -- Use `σ = Equiv.swap b 2`.
      obtain ⟨σ, hσ⟩ : ∃ σ : ZMod n ≃ ZMod n, σ b = 2 ∧ σ 0 = 0 ∧ σ 1 = 1 := by
        use Equiv.swap b 2;
        rcases n with ( _ | _ | _ | n ) <;> simp_all +decide [ ZMod ];
        refine ⟨?_, ?_⟩
        · exact Equiv.swap_apply_left b 2
        · constructor
          · exact Equiv.swap_apply_of_ne_of_ne (Ne.symm h0) (by exact not_eq_of_beq_eq_false rfl : (0 : ZMod (n + 1 + 1 + 1)) ≠ 2)
          · exact Equiv.swap_apply_of_ne_of_ne (Ne.symm h1) (by exact not_eq_of_beq_eq_false rfl : (1 : ZMod (n + 1 + 1 + 1)) ≠ 2)
      -- Apply the permutation σ to the function and use the fact that the degree is preserved.
      have h_perm : representedByPolynomialOfDegree (kroneckerDelta n (σ 1) (σ b)) 3 := by
        convert cubic_d_12 n using 1 ; aesop;
      exact h_contra <| degree_perm_fix_01 n 1 b σ 3 hσ.2.1 hσ.2.2 h_perm

/-
If `a, b \notin \{0, 1\}` and `a \ne b`, then `kroneckerDelta n a b` is represented by a polynomial of degree 3.
-/
lemma degree_d_others (n : ℕ) [NeZero n] (a b : ZMod n)
  (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hb0 : b ≠ 0) (hb1 : b ≠ 1) (hab : a ≠ b) :
  representedByPolynomialOfDegree (kroneckerDelta n a b) 3 := by
    -- Let's find a permutation σ that maps a to 2 and b to 3.
    by_cases hn : n < 4;
    · interval_cases n <;> simp_all +decide [ ZMod ];
      · exact False.elim <| NeZero.ne 0 rfl;
      · fin_cases a ; fin_cases b ; contradiction;
      · fin_cases a <;> fin_cases b <;> trivial;
      · fin_cases a <;> fin_cases b <;> trivial;
    · -- Let's find a permutation σ that maps a to 2 and b to 3. We can use the fact that if n ≥ 4, then 0, 1, 2, 3 are distinct in ZMod n.
      obtain ⟨σ, hσ⟩ : ∃ σ : ZMod n ≃ ZMod n, σ a = 2 ∧ σ b = 3 ∧ σ 0 = 0 ∧ σ 1 = 1 := by
        -- Let's find a permutation σ that maps a to 2 and b to 3. We can use the fact that if n ≥ 4, then 0, 1, 2, 3 are distinct in ZMod n and we can construct such a permutation.
        obtain ⟨σ, hσ⟩ : ∃ σ : ZMod n ≃ ZMod n, σ a = 2 ∧ σ 0 = 0 ∧ σ 1 = 1 := by
          use Equiv.swap a 2 * Equiv.refl (ZMod n);
          simp +decide [ Equiv.swap_apply_def ];
          rcases n with ( _ | _ | _ | n ) <;> norm_num [ ZMod ] at *;
          simp_all +decide [ eq_comm ];
          exact ⟨ fun h => by rcases h with ⟨ ⟩, fun h => by rcases h with ⟨ ⟩ ⟩;
        -- Let's find a permutation σ that maps b to 3. We can use the fact that if n ≥ 4, then 0, 1, 2, 3 are distinct in ZMod n and we can construct such a permutation.
        obtain ⟨τ, hτ⟩ : ∃ τ : ZMod n ≃ ZMod n, τ (σ b) = 3 ∧ τ 2 = 2 ∧ τ 0 = 0 ∧ τ 1 = 1 := by
          by_cases h₂ : σ b = 2 ∨ σ b = 3 ∨ σ b = 0 ∨ σ b = 1;
          · rcases h₂ with ( h₂ | h₂ | h₂ | h₂ ) <;> simp_all +decide ;
            · exact False.elim <| hab <| σ.injective <| by aesop;
            · exact ⟨ Equiv.refl _, rfl, rfl, rfl, rfl ⟩;
            · have := σ.injective ( h₂.trans hσ.2.1.symm ) ; aesop;
            · have := σ.injective ( h₂.trans hσ.2.2.symm ) ; aesop;
          · use Equiv.swap (σ b) 3; simp_all +decide [ Equiv.swap_apply_def ] ;
            rcases n with ( _ | _ | _ | _ | n ) <;> simp_all +decide [ ZMod ];
            exact ⟨ by rw [ if_neg ( Ne.symm h₂.1 ) ] ; rcases n with ( _ | _ | n ) <;> trivial, by rw [ if_neg ( Ne.symm h₂.2.2.1 ) ] ; rcases n with ( _ | _ | n ) <;> trivial, by rw [ if_neg ( Ne.symm h₂.2.2.2 ) ] ; rcases n with ( _ | _ | n ) <;> trivial ⟩ ;
        exact ⟨ τ * σ, by aesop ⟩;
      -- Use `cubic_d_23` to conclude.
      have h_cubic : representedByPolynomialOfDegree (kroneckerDelta n 2 3) 3 := by
        exact cubic_d_23 n;
      convert degree_perm_fix_01 n a b σ 3 hσ.2.2.1 hσ.2.2.2 _ using 1 ; aesop

theorem degree_d (n : ℕ) [NeZero n] (a b : ZMod n) :
  if a = b then representedByPolynomialOfDegree (kroneckerDelta n a b) 3
  else if ({a, b} : Finset (ZMod n)) = {0, 1} then representedByPolynomialOfDegree (kroneckerDelta n a b) 4
  else
    representedByPolynomialOfDegree (kroneckerDelta n a b) 3 := by
  by_cases hab : a = b <;> simp_all +decide [ degree_d_01 ];
  · exact degree_d_eq n b |> fun h => h.imp fun n hn => ⟨ hn.choose, hn.choose_spec.1, by linarith [ hn.choose_spec.2 ] ⟩;
  · by_cases ha : a = 0 ∨ a = 1 <;> by_cases hb : b = 0 ∨ b = 1 <;> simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
    · grind;
    · cases ha <;> simp_all +decide [ degree_d_0_b, degree_d_1_b ];
    · cases hb <;> simp_all +decide ;
      · convert represented_swap _ _ _ using 1;
        rotate_left;
        exact ZMod n;
        exact fun p => kroneckerDelta n 0 a p;
        · convert degree_d_0_b n a ha.1 ha.2 using 1;
        · congr! 2;
          unfold kroneckerDelta; aesop;
      · convert represented_swap _ 3 ( degree_d_1_b n a ( by tauto ) ( by tauto ) ) using 1;
        ext ⟨ x, y ⟩ ; unfold kroneckerDelta; aesop;
    · exact degree_d_others n a b ha.1 ha.2 hb.1 hb.2 hab

/-
This is a colorrary of theorems above
-/
theorem quartic_d (n : ℕ) [NeZero n] (a b : ZMod n) :
    representedByPolynomialOfDegree (kroneckerDelta n a b) 4 := by
  have := @degree_d n ‹_› a b;
  split_ifs at this <;> simp_all +decide [ representedByPolynomialOfDegree ];
  · exact ⟨ this.choose, by rcases this.choose_spec with ⟨ g, hg₁, hg₂ ⟩ ; exact ⟨ g, hg₁, hg₂.trans ( by norm_num ) ⟩ ⟩;
  · exact ⟨ this.choose, by rcases this.choose_spec with ⟨ g, hg₁, hg₂ ⟩ ; exact ⟨ g, hg₁, hg₂.trans ( by norm_num ) ⟩ ⟩

end Finbin
