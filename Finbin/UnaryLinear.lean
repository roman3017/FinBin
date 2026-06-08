import Mathlib

/-!
# Linear embedding of unary functions

Every function `f : ZMod n → ZMod n` admits a linear representation: an injective
`j : ZMod n → ZMod m` and `a : ZMod m` with `j (f i) = a * j i` for all `i`
(`Finbin.linear_representation`).

Ported from `brcm/archive/lean/cursor/Cursor/aristotle_crt.lean` (the unary linear
result; the file's subsequent quadratic-representation material is out of scope here).
-/

open scoped Classical

noncomputable section

namespace Finbin

/-
A linear representation of f is an injective function j: Z/nZ -> Z/mZ such that j(f(i)) = a * j(i) for some a in Z/mZ and m > 0.
-/
/-- `f` has a linear representation: an injective `j` into some `ZMod m` and an `a` with `j (f i) = a * j i`. -/
def hasLinearRepresentation {n : ℕ} (f : ZMod n → ZMod n) : Prop :=
  ∃ m : ℕ, ∃ a : ZMod m, ∃ j : ZMod n → ZMod m,
    m > 0 ∧ Function.Injective j ∧ ∀ i, j (f i) = a * j i

/-
x is in a cycle if f^k(x) = x for some k > 0.
-/
/-- `x` lies on a cycle of `f`, i.e. `f^[k] x = x` for some `k > 0`. -/
def inCycle {n : ℕ} (f : ZMod n → ZMod n) (x : ZMod n) : Prop :=
  ∃ k > 0, f^[k] x = x

/-
For any x, there exists k such that f^k(x) is in a cycle. The depth of x is the smallest such k.
-/
lemma exists_iterate_in_cycle {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) :
  ∃ k, inCycle f (f^[k] x) := by
  by_contra h_no_k;
  -- Since $f$ is a function from a finite set to itself, the sequence $x, f(x), f(f(x)), \ldots$ must eventually repeat.
  have h_repeat : ∃ m n : ℕ, m < n ∧ f^[m] x = f^[n] x := by
    have h_finite : Set.Finite (Set.range (fun k => f^[k] x)) := by
      exact Set.toFinite _;
    by_contra! h;
    exact h_finite.not_infinite <| Set.infinite_range_of_injective fun m n hmn => le_antisymm ( le_of_not_gt fun hmn' => h _ _ hmn' hmn.symm ) ( le_of_not_gt fun hmn' => h _ _ hmn' hmn );
  obtain ⟨ m, n, hmn, h ⟩ := h_repeat;
  refine' h_no_k ⟨ m, n - m, tsub_pos_of_lt hmn, _ ⟩;
  rw [ ← Function.iterate_add_apply, Nat.sub_add_cancel hmn.le, h ]

/-- The number of applications of `f` needed to bring `x` onto a cycle. -/
noncomputable def depth {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) : ℕ :=
  Nat.find (exists_iterate_in_cycle f x)

/-
The root of x is the element in the cycle that x reaches after `depth f x` steps. The root is always in a cycle.
-/
/-- The cycle point reached from `x` after `depth f x` steps. -/
noncomputable def root {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) : ZMod n :=
  f^[depth f x] x

lemma root_in_cycle {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) :
  inCycle f (root f x) := by
  exact Nat.find_spec ( exists_iterate_in_cycle f x )

/-
The cycle period of x is the smallest k > 0 such that f^k(root f x) = root f x.
-/
/-- The length of the cycle that `x` eventually enters. -/
noncomputable def cyclePeriod {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) : ℕ :=
  Nat.find (root_in_cycle f x)

lemma cycle_period_pos {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) :
  cyclePeriod f x > 0 := by
  exact (Nat.find_spec (root_in_cycle f x)).1

lemma iterate_cycle_period_root {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) :
  f^[cyclePeriod f x] (root f x) = root f x := by
  exact (Nat.find_spec (root_in_cycle f x)).2

/-
The cycle elements of x are the elements in the cycle reachable from x.
-/
/-- The set of points lying on the cycle reached from `x`. -/
noncomputable def cycleElements {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) : Finset (ZMod n) :=
  (Finset.range (cyclePeriod f x)).image (fun k => f^[k] (root f x))

/-
The component representative is the element in the cycle with the smallest integer value.
-/
/-- A chosen cycle representative of the connected component of `x`. -/
noncomputable def componentRep {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) : ZMod n :=
  let s := cycleElements f x
  let vals := s.image ZMod.val
  let min_val := vals.min' (by
  -- Since the cycleElements is nonempty, there exists some element y in it. The value of y is an element of vals, so vals is nonempty.
  obtain ⟨y, hy⟩ : ∃ y, y ∈ s := by
    refine' ⟨ _, Finset.mem_image_of_mem _ <| Finset.mem_range.mpr <| cycle_period_pos f x ⟩;
  exact ⟨ _, Finset.mem_image_of_mem _ hy ⟩)
  (min_val : ZMod n)

/-
The set of components is the image of the component representative function.
-/
/-- The set of component representatives of `f`. -/
def components {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) : Finset (ZMod n) :=
  Finset.univ.image (componentRep f)

/-
The cycle position is the number of steps from the component representative to the root of x.
-/
/-- The position, along its cycle, of the root of `x`, measured from the component representative. -/
noncomputable def cyclePosition {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) : ℕ :=
  Nat.find (show ∃ k, f^[k] (componentRep f x) = root f x by
              -- By definition of componentRep, we know that componentRep f x is in the cycle of x.
              have h_cycle : componentRep f x ∈ cycleElements f x := by
                have h_root_in_cycle : ∃ y ∈ Finset.image ZMod.val (cycleElements f x), ∀ z ∈ Finset.image ZMod.val (cycleElements f x), y ≤ z := by
                  apply_rules [ Finset.exists_min_image ];
                  simp +zetaDelta at *;
                  exact ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_range.mpr ( cycle_period_pos f x ) ) ⟩;
                unfold componentRep;
                obtain ⟨ y, hy₁, hy₂ ⟩ := h_root_in_cycle;
                have h_min_val : (Finset.image ZMod.val (cycleElements f x)).min' (by
                exact ⟨ _, hy₁ ⟩) = y := by
                  exact le_antisymm ( Finset.min'_le _ _ hy₁ ) ( hy₂ _ ( Finset.min'_mem _ _ ) )
                generalize_proofs at *;
                rw [ Finset.mem_image ] at hy₁; obtain ⟨ z, hz₁, rfl ⟩ := hy₁; aesop;
              obtain ⟨ k, hk ⟩ := Finset.mem_image.mp h_cycle;
              -- By definition of $cycle\_period$, we know that $f^{cycle\_period f x} (root f x) = root f x$.
              have h_cycle_period : f^[cyclePeriod f x] (root f x) = root f x := by
                exact iterate_cycle_period_root f x;
              use cyclePeriod f x - k;
              rw [ ← hk.2, ← Function.iterate_add_apply, Nat.sub_add_cancel ( Finset.mem_range_le hk.1 ), h_cycle_period ])

/-
The max depth is the maximum depth of any element in the graph.
-/
/-- The maximum depth over all points of `ZMod n`. -/
noncomputable def maxDepth {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) : ℕ :=
  Finset.univ.sup (fun x => depth f x)

/-
If x is in a cycle, then the root of x is x itself.
-/
lemma root_eq_self_of_in_cycle {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) (h : inCycle f x) :
  root f x = x := by
  -- Since x is in a cycle, depth f x = 0.
  have h_depth_zero : depth f x = 0 := by
    unfold depth; aesop;
  unfold root; aesop;

/-
If y is in the cycle elements of x, then y is in a cycle.
-/
lemma in_cycle_of_mem_cycle_elements {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x y : ZMod n) (h : y ∈ cycleElements f x) :
  inCycle f y := by
  -- By definition of cycle elements, there exists some k such that f^[k] (root f x) = y.
  obtain ⟨k, hk⟩ : ∃ k, f^[k] (root f x) = y := by
    unfold cycleElements at h; aesop;
  -- By definition of $inCycle$, we need to show that there exists some $m > 0$ such that $f^m(y) = y$.
  use cyclePeriod f x;
  rw [ ← hk ];
  exact ⟨ cycle_period_pos f x, by rw [ ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, iterate_cycle_period_root ] ⟩

/-
If y is in the cycle elements of x, then the cycle period of x is equal to the cycle period of y.
-/
lemma cycle_period_eq_of_mem_cycle_elements {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x y : ZMod n) (h : y ∈ cycleElements f x) :
  cyclePeriod f x = cyclePeriod f y := by
  -- Since y is in the cycle elements of x, there exists some k such that y = f^[k] (root f x).
  obtain ⟨k, hk⟩ : ∃ k, y = f^[k] (root f x) := by
    unfold cycleElements at h; aesop;
  -- Since y is in the cycle elements of x, there exists some m such that y = f^[m] (root f x).
  obtain ⟨m, hm⟩ : ∃ m, f^[m] y = root f x := by
    -- Since $y$ is in the cycle elements of $x$, there exists some $m$ such that $f^[m] y = root f x$.
    use cyclePeriod f x - k % cyclePeriod f x;
    rw [ hk, ← Nat.mod_add_div k ( cyclePeriod f x ) ] ; simp +decide [ Function.iterate_add_apply, Function.iterate_mul ] ;
    simp +decide [ ← Function.iterate_add_apply, Nat.sub_add_cancel ( Nat.mod_lt _ ( cycle_period_pos f x ) |> Nat.le_of_lt ) ];
    induction k / cyclePeriod f x <;> simp_all +decide [ Function.iterate_succ_apply' ];
    · exact iterate_cycle_period_root f x;
    · exact iterate_cycle_period_root f x;
  -- Since $y$ is in the cycle elements of $x$, we have $f^[cycle\_period f x] y = y$.
  have h_cycle_period_y : f^[cyclePeriod f x] y = y := by
    have h_cycle_period_y : f^[cyclePeriod f x] (root f x) = root f x := by
      exact iterate_cycle_period_root f x;
    simp_all +decide [ ← Function.iterate_add_apply ];
    rw [ add_comm, Function.iterate_add_apply, h_cycle_period_y ];
  have h_cycle_period_y : cyclePeriod f y ≤ cyclePeriod f x := by
    refine' Nat.find_min' _ _;
    -- Since $y$ is in the cycle elements of $x$, we have $root f y = y$.
    have h_root_y : root f y = y := by
      apply root_eq_self_of_in_cycle;
      exact in_cycle_of_mem_cycle_elements f x y h;
    exact ⟨ cycle_period_pos f x, by rw [ h_root_y, h_cycle_period_y ] ⟩;
  refine' le_antisymm _ h_cycle_period_y;
  have h_cycle_period_x : f^[cyclePeriod f y] (root f x) = root f x := by
    have := iterate_cycle_period_root f y;
    rw [ root_eq_self_of_in_cycle ] at this;
    · rw [ ← hm, ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply ] at * ; aesop ( simp_config := { singlePass := true } ) ;
    · exact in_cycle_of_mem_cycle_elements f x y h;
  apply Nat.find_min';
  exact ⟨ cycle_period_pos f y, h_cycle_period_x ⟩

/-
If x is in a cycle, then the cycle period of f(x) is equal to the cycle period of x.
-/
lemma cycle_period_apply_of_in_cycle {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) (h : inCycle f x) :
  cyclePeriod f (f x) = cyclePeriod f x := by
  -- Since $f x$ is in the cycle elements of $x$, we can apply the lemma that states the cycle period is the same for elements in the cycle elements.
  have h_cycle_elements : f x ∈ cycleElements f x := by
    unfold cycleElements;
    have h_root : root f x = x := by
      exact root_eq_self_of_in_cycle f x h;
    rcases k : cyclePeriod f x with ( _ | _ | k ) <;> simp_all +decide;
    · exact absurd k ( Nat.ne_of_gt ( cycle_period_pos f x ) );
    · have := iterate_cycle_period_root f x; aesop;
    · exact ⟨ 1, by linarith, rfl ⟩;
  exact Eq.symm (cycle_period_eq_of_mem_cycle_elements f x (f x) h_cycle_elements)

/-
The component representative of x is in the set of cycle elements of x.
-/
lemma component_rep_mem_cycle {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) :
  componentRep f x ∈ cycleElements f x := by
  unfold componentRep cycleElements;
  -- By definition of `Finset.min'`, the minimum element in the image of the cycle elements is indeed in the image.
  have h_min_in_image : (Finset.image ZMod.val (Finset.image (fun k => f^[k] (root f x)) (Finset.range (cyclePeriod f x)))).min' (by
  exact ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_image_of_mem _ ( Finset.mem_range.mpr ( cycle_period_pos f x ) ) ) ⟩) ∈ Finset.image ZMod.val (Finset.image (fun k => f^[k] (root f x)) (Finset.range (cyclePeriod f x))) := by
    exact Finset.min'_mem _ _;
  norm_num +zetaDelta at *;
  obtain ⟨ a, ha₁, ha₂ ⟩ := h_min_in_image; use a, ha₁; rw [ ← ha₂, ZMod.natCast_zmod_val ] ;

/-
If two elements have the same component representative, they have the same cycle period.
-/
lemma cycle_period_eq_of_component_rep_eq {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x y : ZMod n) (h : componentRep f x = componentRep f y) :
  cyclePeriod f x = cyclePeriod f y := by
  -- Since the component representatives are the same, the smallest k such that f^k(componentRep f x) = componentRep f x must be the same as the smallest k such that f^k(componentRep f y) = componentRep f y.
  have h_cycle_period_eq : cyclePeriod f (componentRep f x) = cyclePeriod f (componentRep f y) := by
    rw [h];
  have h_cycle_period_eq : cyclePeriod f x = cyclePeriod f (componentRep f x) := by
    apply cycle_period_eq_of_mem_cycle_elements;
    exact component_rep_mem_cycle f x
  have h_cycle_period_eq' : cyclePeriod f y = cyclePeriod f (componentRep f y) := by
    apply cycle_period_eq_of_mem_cycle_elements;
    exact component_rep_mem_cycle f y
  rw [h_cycle_period_eq, h_cycle_period_eq'] at * ; aesop

/-
jp maps x to a power of zeta based on its position in the cycle and depth.
-/
/-- Cyclic coordinate: a power of the root of unity `zeta` encoding the cycle position of `x`. -/
def jp {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (p : ℕ) (zeta : ZMod p) (x : ZMod n) : ZMod p :=
  zeta ^ (cyclePosition f (root f x)) * (zeta⁻¹) ^ (depth f x)

example (p : ℕ) [Fact p.Prime] : IsCyclic (ZMod p)ˣ := by infer_instance

/-
Definitions of preimages and signature map.
-/
/-- The list of `f`-preimages of `y`. -/
def preimages {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (y : ZMod n) : List (ZMod n) :=
  (Finset.univ.filter (fun x => f x = y)).toList

/-- The index of `x` among the `f`-preimages of `f x`. -/
def signatureMap {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) : ℕ :=
  (preimages f (f x)).idxOf x

/-
Injectivity of the signature map for elements with the same image.
-/
lemma signature_inj {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x y : ZMod n) (h_eq : f x = f y) (h_sig : signatureMap f x = signatureMap f y) : x = y := by
  unfold signatureMap at h_sig;
  unfold preimages at h_sig;
  simp_all +decide [ List.idxOf_inj ]

/-
The signature of an element is bounded by n.
-/
lemma signature_bound {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) : signatureMap f x < n := by
  have h_idx_lt_n : List.idxOf x (preimages f (f x)) < List.length (preimages f (f x)) := by
    have h_idx_lt_n : x ∈ preimages f (f x) := by
      unfold preimages; aesop;
    exact List.idxOf_lt_length_of_mem h_idx_lt_n;
  simp_all +decide [ preimages ];
  exact h_idx_lt_n.trans_le ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) )

/-
If x is not in a cycle, the depth of f(x) is the depth of x minus 1.
-/
lemma depth_f_of_not_in_cycle {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) (h : ¬ inCycle f x) :
  depth f (f x) = depth f x - 1 := by
    -- Let $k = \text{depth}(f, x)$. Since $x$ is not in a cycle, $k > 0$.
    set k := depth f x with hk;
    -- By definition of depth, we know that $f^k(x)$ is in a cycle and for all $j < k$, $f^j(x)$ is not in a cycle.
    have h_depth_def : inCycle f (f^[k] x) ∧ ∀ j < k, ¬inCycle f (f^[j] x) := by
      exact ⟨ Nat.find_spec ( exists_iterate_in_cycle f x ), fun j hj => fun hj' => hj.not_ge ( Nat.find_min' ( exists_iterate_in_cycle f x ) hj' ) ⟩;
    -- Since $k > 0$, we have $depth(f, f(x)) \leq k - 1$.
    have h_depth_le : depth f (f x) ≤ k - 1 := by
      refine' Nat.find_min' _ _;
      cases a : depth f x <;> simp_all +decide;
    refine' le_antisymm h_depth_le _;
    refine' Nat.le_of_not_lt fun h => h_depth_def.2 ( depth f ( f x ) + 1 ) _ _;
    · omega;
    · convert Nat.find_spec ( exists_iterate_in_cycle f ( f x ) ) using 1

/-
If x is not in a cycle, the root of f(x) is the same as the root of x.
-/
lemma root_f_eq_root_of_not_in_cycle {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) (h : ¬ inCycle f x) :
  root f (f x) = root f x := by
    -- Since $x$ is not in a cycle, we have $depth f x > 0$.
    have h_depth_pos : 0 < depth f x := by
      contrapose! h;
      unfold depth at h; aesop;
    have h_root_eq : root f (f x) = f^[depth f x - 1] (f x) := by
      have h_root_eq : depth f (f x) = depth f x - 1 := by
        exact depth_f_of_not_in_cycle f x h;
      exact h_root_eq ▸ rfl;
    cases k : depth f x <;> simp_all +decide;
    unfold root; aesop;

/-
Two iterates of the component representative are equal if and only if the iteration counts are congruent modulo the cycle period.
-/
lemma iterate_eq_iff_modEq_of_component_rep {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) (k j : ℕ) :
  f^[k] (componentRep f x) = f^[j] (componentRep f x) ↔ k ≡ j [MOD cyclePeriod f x] := by
    -- Let `rep = componentRep f x`.
    set rep := componentRep f x;
    -- Since `rep` is in the cycle of `x`, `cyclePeriod f rep = cyclePeriod f x`.
    have h_cycle_period_rep : cyclePeriod f rep = cyclePeriod f x := by
      have h_cycle_period_rep : rep ∈ cycleElements f x := by
        exact component_rep_mem_cycle f x;
      exact Eq.symm (cycle_period_eq_of_mem_cycle_elements f x rep h_cycle_period_rep);
    -- Since `rep` is in the cycle of `x`, `f^[p] rep = rep` where `p = cyclePeriod f rep`.
    have h_cycle_rep : f^[cyclePeriod f rep] rep = rep := by
      have := Nat.find_spec ( root_in_cycle f rep );
      convert this.2;
      · rw [ root_eq_self_of_in_cycle ];
        exact in_cycle_of_mem_cycle_elements f x rep ( component_rep_mem_cycle f x );
      · rw [ root_eq_self_of_in_cycle ];
        exact in_cycle_of_mem_cycle_elements f x rep ( component_rep_mem_cycle f x );
    -- The elements `f^0 rep, f^1 rep, ..., f^{p-1} rep` are distinct and form the cycle.
    have h_distinct : ∀ k l : ℕ, k < l → l < cyclePeriod f rep → f^[k] rep ≠ f^[l] rep := by
      intros k l hkl hl_lt_cycle_period h_eq
      have h_contradiction : f^[cyclePeriod f rep - l + k] rep = rep := by
        have h_contradiction : f^[cyclePeriod f rep - l] (f^[l] rep) = rep := by
          rw [ ← Function.iterate_add_apply, Nat.sub_add_cancel hl_lt_cycle_period.le, h_cycle_rep ];
        rw [ Function.iterate_add_apply, h_eq, h_contradiction ];
      have h_contradiction : cyclePeriod f rep ≤ cyclePeriod f rep - l + k := by
        apply Nat.find_min';
        have h_root_eq_rep : root f rep = rep := by
          apply root_eq_self_of_in_cycle;
          exact ⟨ cyclePeriod f rep, Nat.pos_of_ne_zero ( by aesop_cat ), h_cycle_rep ⟩;
        grind;
      omega;
    -- Thus `f^[k] rep = f^[j] rep` iff `k ≡ j [MOD p]`.
    apply Iff.intro;
    · intro h_eq
      have h_mod : f^[k % cyclePeriod f rep] rep = f^[j % cyclePeriod f rep] rep := by
        rw [ ← Nat.mod_add_div k ( cyclePeriod f rep ), ← Nat.mod_add_div j ( cyclePeriod f rep ) ] at *; simp_all +decide [ Function.iterate_add_apply, Function.iterate_mul, Function.iterate_fixed ] ;
      by_contra h_contra;
      exact h_distinct ( Min.min ( k % cyclePeriod f rep ) ( j % cyclePeriod f rep ) ) ( Max.max ( k % cyclePeriod f rep ) ( j % cyclePeriod f rep ) ) ( lt_of_le_of_ne ( min_le_max ) ( by contrapose! h_contra; simp_all +decide [ Nat.ModEq ] ) ) ( by cases max_cases ( k % cyclePeriod f rep ) ( j % cyclePeriod f rep ) <;> linarith [ Nat.mod_lt k ( show cyclePeriod f rep > 0 from h_cycle_period_rep ▸ cycle_period_pos f x ), Nat.mod_lt j ( show cyclePeriod f rep > 0 from h_cycle_period_rep ▸ cycle_period_pos f x ) ] ) ( by cases max_cases ( k % cyclePeriod f rep ) ( j % cyclePeriod f rep ) <;> cases min_cases ( k % cyclePeriod f rep ) ( j % cyclePeriod f rep ) <;> aesop );
    · intro h; rw [ ← Nat.mod_add_div k ( cyclePeriod f rep ), ← Nat.mod_add_div j ( cyclePeriod f rep ), h_cycle_period_rep ] ; simp_all +decide [ Function.iterate_add_apply, Function.iterate_mul, Function.iterate_fixed ] ;
      rw [ h ]

/-
If x is in a cycle, its cycle position advances by 1 (modulo the period) when applying f.
-/
lemma cycle_position_f_of_in_cycle {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) (h : inCycle f x) :
  cyclePosition f (f x) ≡ cyclePosition f x + 1 [MOD cyclePeriod f x] := by
    -- By definition of cyclePosition, we know that $f^{cyclePosition f x} (componentRep f x) = root f x$ and $f^{cyclePosition f (f x)} (componentRep f x) = root f (f x)$.
    have h_cycle_pos : f^[cyclePosition f x] (componentRep f x) = root f x ∧ f^[cyclePosition f (f x)] (componentRep f x) = root f (f x) := by
      apply And.intro;
      · exact Nat.find_spec ( _ : ∃ k, f^[k] ( componentRep f x ) = root f x );
      · have h_cycle_pos_f : componentRep f (f x) = componentRep f x := by
          -- Since $x$ is in a cycle, we have $root f x = x$.
          have h_root_x : root f x = x := by
            exact root_eq_self_of_in_cycle f x h;
          have h_root_fx : root f (f x) = f x := by
            apply root_eq_self_of_in_cycle;
            obtain ⟨ k, hk ⟩ := h;
            exact ⟨ k, hk.1, by erw [ Function.iterate_succ_apply', hk.2 ] ⟩;
          have h_comp_rep_fx : cycleElements f (f x) = cycleElements f x := by
            ext y
            simp [cycleElements, h_root_fx];
            rw [ h_root_x, cycle_period_apply_of_in_cycle f x h ];
            constructor <;> rintro ⟨ a, ha, rfl ⟩;
            · use if a = cyclePeriod f x - 1 then 0 else a + 1;
              split_ifs <;> simp_all +decide [ Function.iterate_succ_apply' ];
              · have := iterate_cycle_period_root f x; cases k : cyclePeriod f x <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
                erw [ Function.iterate_succ_apply', this ];
              · exact ⟨ Nat.lt_of_le_of_ne ( Nat.succ_le_of_lt ha ) ( by omega ), by erw [ Function.iterate_succ_apply' ] ⟩;
            · rcases a with ( _ | a ) <;> simp_all +decide [ Function.iterate_succ_apply' ];
              · use cyclePeriod f x - 1;
                have := iterate_cycle_period_root f x; rcases k : cyclePeriod f x with ( _ | _ | k ) <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
                simpa only [ ← Function.iterate_succ_apply' f ] using this;
              · exact ⟨ a, by linarith, by erw [ Function.iterate_succ_apply' ] ⟩;
          unfold componentRep; aesop;
        rw [ ← h_cycle_pos_f, cyclePosition ];
        grind;
    -- By definition of $root$, we know that $root f (f x) = f x$.
    have h_root_fx : root f (f x) = f x := by
      -- By definition of `root`, we know that `root f (f x) = f x` since `f x` is in a cycle.
      apply root_eq_self_of_in_cycle;
      obtain ⟨ k, hk ⟩ := h;
      refine' ⟨ k, hk.1, _ ⟩;
      erw [ Function.iterate_succ_apply', hk.2 ];
    have h_root_fx_eq : f^[cyclePosition f (f x)] (componentRep f x) = f^[cyclePosition f x + 1] (componentRep f x) := by
      simp_all +decide [ Function.iterate_succ_apply' ];
      rw [ root_eq_self_of_in_cycle f x h ];
    exact
      (iterate_eq_iff_modEq_of_component_rep f x (cyclePosition f (f x))
            (cyclePosition f x + 1)).mp
        h_root_fx_eq

/-
The set of cycle elements is invariant under f for elements in a cycle.
-/
lemma cycle_elements_eq_of_in_cycle {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) (h : inCycle f x) :
  cycleElements f (f x) = cycleElements f x := by
    -- Since x is in a cycle, the root of x is x itself.
    have h_root_eq : root f x = x := by
      exact root_eq_self_of_in_cycle f x h;
    rw [ show cycleElements f ( f x ) = ( Finset.range ( cyclePeriod f x ) ).image ( fun k => f^[k] ( root f ( f x ) ) ) from ?_, show cycleElements f x = ( Finset.range ( cyclePeriod f x ) ).image ( fun k => f^[k] ( root f x ) ) from ?_ ];
    · rw [ show root f ( f x ) = f x from ?_, show root f x = x from h_root_eq ];
      · ext; simp +decide ;
        constructor <;> rintro ⟨ a, ha, rfl ⟩;
        · by_cases ha' : a + 1 < cyclePeriod f x;
          · exact ⟨ a + 1, ha', by simp +decide ⟩;
          · use 0;
            cases lt_or_eq_of_le ( Nat.le_of_not_lt ha' ) <;> simp_all +decide;
            · linarith;
            · have := iterate_cycle_period_root f x; aesop;
        · use if a = 0 then cyclePeriod f x - 1 else a - 1;
          rcases a with ( _ | a ) <;> simp_all +decide;
          · have := iterate_cycle_period_root f x; cases k : cyclePeriod f x <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
            erw [ Function.iterate_succ_apply', this ];
          · linarith;
      · convert root_eq_self_of_in_cycle f ( f x ) _;
        exact ⟨ h.choose, h.choose_spec.1, by erw [ Function.iterate_succ_apply', h.choose_spec.2 ] ⟩;
    · exact rfl;
    · unfold cycleElements;
      rw [ cycle_period_apply_of_in_cycle f x h ]

/-
The map jp satisfies the linear relation j(f(x)) = zeta * j(x), given that zeta is a root of unity of the correct order.
-/
lemma jp_linear {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (p : ℕ) (zeta : ZMod p) (x : ZMod n) (h_zeta : zeta ^ (cyclePeriod f x) = 1) :
  jp f p zeta (f x) = zeta * jp f p zeta x := by
    by_cases hx : inCycle f x <;> simp_all +decide [ jp ];
    · -- Since $x$ is in a cycle, we have $root f x = x$ and $depth f x = 0$.
      have h_root_depth : root f x = x ∧ depth f x = 0 := by
        have h_root : root f x = x := by
          exact root_eq_self_of_in_cycle f x hx;
        unfold depth; aesop;
      have h_cycle_pos : cyclePosition f (f x) ≡ cyclePosition f x + 1 [MOD cyclePeriod f x] := by
        exact cycle_position_f_of_in_cycle f x hx;
      have h_cycle_pos_eq : zeta ^ cyclePosition f (f x) = zeta ^ (cyclePosition f x + 1) := by
        rw [ ← Nat.mod_add_div ( cyclePosition f ( f x ) ) ( cyclePeriod f x ), ← Nat.mod_add_div ( cyclePosition f x + 1 ) ( cyclePeriod f x ), h_cycle_pos ] ; simp_all +decide [ pow_add, pow_mul ];
      have h_depth_f : depth f (f x) = 0 := by
        have h_depth_f : inCycle f (f x) := by
          obtain ⟨ k, hk ⟩ := hx;
          exact ⟨ k, hk.1, by erw [ Function.iterate_succ_apply', hk.2 ] ⟩;
        exact le_antisymm ( Nat.find_le ( by aesop ) ) ( Nat.zero_le _ );
      have h_root_f : root f (f x) = f x := by
        unfold root; aesop;
      grind;
    · -- Since x is not in a cycle, we have depth f (f x) = depth f x - 1 and root f (f x) = root f x.
      have h_depth : depth f (f x) = depth f x - 1 := by
        exact depth_f_of_not_in_cycle f x hx
      have h_root : root f (f x) = root f x := by
        exact root_f_eq_root_of_not_in_cycle f x hx;
      rcases k : depth f x with ( _ | k ) <;> simp_all +decide [ pow_succ' ];
      · unfold depth at k; aesop;
      · by_cases h : IsUnit zeta <;> simp_all +decide [ mul_left_comm zeta ];
        · cases h ; aesop;
        · exact False.elim <| h <| isUnit_iff_dvd_one.mpr <| h_zeta ▸ dvd_pow_self _ <| Nat.ne_of_gt <| cycle_period_pos f x

--#check ZMod.chineseRemainder

/-
The tree part of the linear representation satisfies the linear equation modulo q^N.
-/
/-- Tree coordinate: a base-`q` numeral recording the signatures along the path from `x` to its cycle. -/
def jq {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (q N : ℕ) (x : ZMod n) : ℕ :=
  (Finset.range (depth f x)).sum (fun k => (signatureMap f (f^[k] x) + 1) * q ^ (N - 1 - k))

lemma jq_mod_linear {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (q N : ℕ) (x : ZMod n) (hN : N ≥ depth f x) :
  (jq f q N (f x) : ZMod (q ^ N)) = (q : ZMod (q ^ N)) * jq f q N x := by
    unfold jq;
    by_cases h : inCycle f x <;> simp_all +decide;
    · -- Since x is in a cycle, depth f x = 0.
      have h_depth_zero : depth f x = 0 := by
        rw [ depth ];
        aesop;
      -- Since x is in a cycle, we have depth f (f x) = 0.
      have h_depth_f_x_zero : depth f (f x) = 0 := by
        unfold depth at *;
        simp_all +decide [ Nat.find_eq_iff ];
        obtain ⟨ k, hk₁, hk₂ ⟩ := h;
        use k;
        exact ⟨ hk₁, by erw [ Function.iterate_succ_apply', hk₂ ] ⟩;
      aesop;
    · -- Since $x$ is not in a cycle, we have $depth f (f x) = depth f x - 1$.
      have h_depth : depth f (f x) = depth f x - 1 := by
        exact depth_f_of_not_in_cycle f x h;
      rcases k : depth f x with ( _ | k ) <;> simp_all +decide [ Function.iterate_succ_apply', Finset.sum_range_succ', mul_add, Finset.mul_sum _ _ _ ];
      simp_all +decide [ ← mul_assoc, ← Function.iterate_succ_apply' ];
      rw [ ← Finset.sum_congr rfl fun i hi => by rw [ show N - 1 - i = N - 1 - ( i + 1 ) + 1 by exact Nat.sub_eq_of_eq_add <| by linarith [ Nat.sub_add_cancel <| show i + 1 ≤ N - 1 from Nat.le_sub_one_of_lt <| by linarith [ Finset.mem_range.mp hi ] ] ] ] ; simp +decide [ pow_succ', mul_assoc, mul_left_comm ] ; ring_nf;
      norm_cast ; simp +decide [ ← pow_succ', Nat.sub_add_cancel ( by linarith : 1 ≤ N ) ]

/-
Recursive step for jq: multiplying by q shifts the digits, exposing the signature of x as the leading term.
-/
lemma jq_step {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (q N : ℕ) (x : ZMod n) (h_not_cycle : ¬ inCycle f x) (hN : N ≥ depth f x) :
  q * jq f q N x = (signatureMap f x + 1) * q ^ N + jq f q N (f x) := by
    -- By definition of `depth`, we know that `depth f (f x) = depth f x - 1`.
    have h_depth : depth f (f x) = depth f x - 1 := by
      exact depth_f_of_not_in_cycle f x h_not_cycle;
    rcases k : depth f x with ( _ | k ) <;> simp_all +decide;
    · unfold depth at k; aesop;
    · unfold jq; simp +decide [ *, Finset.sum_range_succ' ] ; ring_nf;
      rcases N <;> simp_all +decide [ pow_succ', mul_assoc, mul_add, Finset.mul_sum _ _ _, Finset.sum_add_distrib ];
      refine' congrArg₂ ( · + · ) ( Finset.sum_congr rfl fun i hi => _ ) ( Finset.sum_congr rfl fun i hi => _ ) <;> rw [ show ( _ : ℕ ) - i = ( _ : ℕ ) - ( 1 + i ) + 1 by exact Nat.sub_eq_of_eq_add <| by linarith [ Nat.sub_add_cancel <| show 1 + i ≤ _ from by linarith [ Finset.mem_range.mp hi ] ] ] <;> ring

/-
jq is bounded by q^N.
-/
lemma jq_bound {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (q N : ℕ) (x : ZMod n) (hq : q > n) (hN : N ≥ depth f x) :
  jq f q N x < q ^ N := by
    -- The sum of the terms in jq is bounded by the sum of a geometric series.
    have h_geo_series : ∑ k ∈ Finset.range (depth f x), (q - 1) * q ^ (N - 1 - k) < q ^ N := by
      rcases q with ( _ | _ | q ) <;> simp_all +decide [ ← Finset.mul_sum _ _ _ ];
      have h_geo_series : ∑ i ∈ Finset.range (depth f x), (q + 1 + 1) ^ (N - 1 - i) ≤ (∑ i ∈ Finset.range N, (q + 1 + 1) ^ i) := by
        have h_geo_series : ∑ i ∈ Finset.range (depth f x), (q + 1 + 1) ^ (N - 1 - i) ≤ ∑ i ∈ Finset.range (N), (q + 1 + 1) ^ (N - 1 - i) := by
          exact Finset.sum_le_sum_of_subset ( Finset.range_mono hN );
        convert h_geo_series using 1;
        rw [ ← Finset.sum_range_reflect ];
      nlinarith [ geom_sum_mul_neg ( q + 1 + 1 : ℤ ) N, pow_pos ( by linarith : 0 < q + 1 + 1 ) N ];
    refine' lt_of_le_of_lt ( Finset.sum_le_sum _ ) h_geo_series;
    intro i hi;
    exact Nat.mul_le_mul_right _ ( Nat.succ_le_of_lt ( Nat.lt_of_lt_of_le ( signature_bound f _ ) ( Nat.le_sub_one_of_lt hq ) ) )

/-
jq is injective for elements with the same root, provided q is large enough.
-/
lemma jq_inj {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (q N : ℕ) (x y : ZMod n)
  (hq : q > n) (hN : N ≥ n)
  (h_root : root f x = root f y)
  (h_eq : jq f q N x = jq f q N y) :
  x = y := by
    induction' k : depth f x using Nat.strong_induction_on with k ih generalizing x y;
    by_cases hx : inCycle f x <;> by_cases hy : inCycle f y;
    · have := root_eq_self_of_in_cycle f x hx; have := root_eq_self_of_in_cycle f y hy; aesop;
    · -- Since x is in a cycle, we have depth f x = 0.
      have h_depth_x : depth f x = 0 := by
        exact le_antisymm ( Nat.find_le <| by aesop ) ( Nat.zero_le _ );
      contrapose! h_eq;
      unfold jq; simp +decide [ h_depth_x ] ;
      refine' ne_of_lt ( Finset.sum_pos _ _ ) <;> norm_num;
      · exact fun i hi => pow_pos ( by linarith ) _;
      · unfold depth at *; aesop;
    · have h_depth_y : depth f y = 0 := by
        unfold depth; aesop;
      have h_jq_y : jq f q N y = 0 := by
        unfold jq; aesop;
      have h_jq_x : jq f q N x > 0 := by
        refine' Nat.pos_of_ne_zero _;
        simp [jq];
        exact ⟨ 0, Nat.pos_of_ne_zero fun h => hx <| by simp_all +decide [ depth ], fun h => absurd h <| by linarith ⟩;
      grind;
    · -- Since $x$ and $y$ are not in cycles, we have $jq f q N x = (signatureMap f x + 1) * q ^ N + jq f q N (f x)$ and $jq f q N y = (signatureMap f y + 1) * q ^ N + jq f q N (f y)$.
      have h_jq_step : q * jq f q N x = (signatureMap f x + 1) * q ^ N + jq f q N (f x) ∧ q * jq f q N y = (signatureMap f y + 1) * q ^ N + jq f q N (f y) := by
        apply And.intro;
        · apply jq_step;
          · assumption;
          · -- Since `depth f x` is the smallest `k` such that `f^[k] x` is in a cycle, and `x` is not in a cycle, `depth f x` must be less than or equal to `n`.
            have h_depth_le_n : depth f x ≤ n := by
              have h_depth_le_n : ∃ k ≤ n, inCycle f (f^[k] x) := by
                have h_seq : ∃ k ≤ n, ∃ j < k, f^[k] x = f^[j] x := by
                  by_contra h_contra;
                  have h_seq : Finset.card (Finset.image (fun k => f^[k] x) (Finset.range (n + 1))) = n + 1 := by
                    rw [ Finset.card_image_of_injOn ] <;> norm_num;
                    exact fun a ha b hb hab => le_antisymm ( le_of_not_gt fun h => h_contra ⟨ a, by linarith [ Set.mem_Iio.mp ha ], b, by linarith [ Set.mem_Iio.mp hb ], by tauto ⟩ ) ( le_of_not_gt fun h => h_contra ⟨ b, by linarith [ Set.mem_Iio.mp hb ], a, by linarith [ Set.mem_Iio.mp ha ], by tauto ⟩ );
                  exact h_seq.not_lt ( lt_of_le_of_lt ( Finset.card_le_univ _ ) ( by norm_num ) );
                obtain ⟨ k, hk₁, j, hj₁, hj₂ ⟩ := h_seq;
                use j;
                exact ⟨ by linarith, ⟨ k - j, Nat.sub_pos_of_lt hj₁, by rw [ ← Function.iterate_add_apply, Nat.sub_add_cancel hj₁.le, hj₂ ] ⟩ ⟩;
              exact Nat.find_min' _ h_depth_le_n.choose_spec.2 |> le_trans <| h_depth_le_n.choose_spec.1;
            linarith;
        · convert jq_step f q N y hy _ using 1;
          have h_depth_le_n : ∀ x : ZMod n, depth f x ≤ n := by
            intro x;
            have h_depth_le_n : ∀ x : ZMod n, ∃ k ≤ n, inCycle f (f^[k] x) := by
              intro x
              have h_seq : ∃ i j : ℕ, i < j ∧ i ≤ n ∧ j ≤ n ∧ f^[i] x = f^[j] x := by
                by_contra h_contra;
                exact absurd ( Finset.card_le_univ ( Finset.image ( fun i => f^[i] x ) ( Finset.Iic n ) ) ) ( by rw [ Finset.card_image_of_injOn fun i hi j hj hij => le_antisymm ( not_lt.mp fun hi' => h_contra ⟨ j, i, hi', by aesop, by aesop, hij.symm ⟩ ) ( not_lt.mp fun hj' => h_contra ⟨ i, j, hj', by aesop, by aesop, hij ⟩ ) ] ; simp +decide );
              obtain ⟨ i, j, hij, hi, hj, h ⟩ := h_seq;
              use i;
              refine' ⟨ hi, _ ⟩;
              use j - i;
              exact ⟨ Nat.sub_pos_of_lt hij, by rw [ ← Function.iterate_add_apply, Nat.sub_add_cancel hij.le, h ] ⟩;
            exact Nat.find_min' _ ( h_depth_le_n x |> Classical.choose_spec |> And.right ) |> le_trans <| h_depth_le_n x |> Classical.choose_spec |> And.left;
          linarith [ h_depth_le_n y ];
      -- Since $q > n$, we have $jq f q N (f x) < q^N$ and $jq f q N (f y) < q^N$.
      have h_jq_lt_qN : jq f q N (f x) < q ^ N ∧ jq f q N (f y) < q ^ N := by
        apply And.intro;
        · apply jq_bound;
          · linarith;
          · rw [ depth_f_of_not_in_cycle f x hx ];
            refine' Nat.sub_le_of_le_add _;
            refine' le_trans _ ( Nat.le_succ_of_le hN );
            have h_depth_le_n : ∀ x : ZMod n, depth f x ≤ n := by
              intro x
              have h_depth_le_n : ∃ k ≤ n, inCycle f (f^[k] x) := by
                by_contra h_contra;
                -- Since $f$ is a function from a finite set to itself, the sequence $x, f(x), f(f(x)), \ldots$ must eventually repeat.
                have h_seq_repeat : ∃ i j : ℕ, i < j ∧ i ≤ n ∧ j ≤ n ∧ f^[i] x = f^[j] x := by
                  have h_seq_repeat : Finset.card (Finset.image (fun k => f^[k] x) (Finset.range (n + 1))) ≤ n := by
                    haveI := Fact.mk ( NeZero.pos n ) ; exact le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ;
                  by_cases h_eq : ∀ i j : ℕ, i < j → i ≤ n → j ≤ n → f^[i] x ≠ f^[j] x;
                  · exact absurd h_seq_repeat ( by rw [ Finset.card_image_of_injOn fun i hi j hj hij => le_antisymm ( not_lt.mp fun hi' => h_eq _ _ hi' ( by linarith [ Finset.mem_range.mp hj ] ) ( by linarith [ Finset.mem_range.mp hi ] ) hij.symm ) ( not_lt.mp fun hj' => h_eq _ _ hj' ( by linarith [ Finset.mem_range.mp hi ] ) ( by linarith [ Finset.mem_range.mp hj ] ) hij ) ] ; simp +arith +decide );
                  · exact by push Not at h_eq; exact h_eq;
                obtain ⟨ i, j, hij, hi, hj, h ⟩ := h_seq_repeat;
                refine' h_contra ⟨ i, hi, _ ⟩;
                use j - i;
                exact ⟨ Nat.sub_pos_of_lt hij, by rw [ ← Function.iterate_add_apply, Nat.sub_add_cancel hij.le, h ] ⟩;
              exact le_trans ( Nat.find_min' _ h_depth_le_n.choose_spec.2 ) h_depth_le_n.choose_spec.1;
            exact h_depth_le_n x;
        · apply jq_bound;
          · linarith;
          · rw [ depth_f_of_not_in_cycle f y hy ];
            have h_depth_y : depth f y ≤ n := by
              have h_depth_le_n : ∀ x : ZMod n, depth f x ≤ n := by
                intro x
                have h_depth_le_n : ∃ k ≤ n, inCycle f (f^[k] x) := by
                  by_contra h_contra;
                  -- Since $f$ is a function from a finite set to itself, the sequence $x, f(x), f(f(x)), \ldots$ must eventually repeat.
                  have h_seq_repeat : ∃ i j : ℕ, i < j ∧ i ≤ n ∧ j ≤ n ∧ f^[i] x = f^[j] x := by
                    have h_seq_repeat : Finset.card (Finset.image (fun k => f^[k] x) (Finset.range (n + 1))) ≤ n := by
                      haveI := Fact.mk ( NeZero.pos n ) ; exact le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ;
                    by_cases h_eq : ∀ i j : ℕ, i < j → i ≤ n → j ≤ n → f^[i] x ≠ f^[j] x;
                    · exact absurd h_seq_repeat ( by rw [ Finset.card_image_of_injOn fun i hi j hj hij => le_antisymm ( not_lt.mp fun hi' => h_eq _ _ hi' ( by linarith [ Finset.mem_range.mp hj ] ) ( by linarith [ Finset.mem_range.mp hi ] ) hij.symm ) ( not_lt.mp fun hj' => h_eq _ _ hj' ( by linarith [ Finset.mem_range.mp hi ] ) ( by linarith [ Finset.mem_range.mp hj ] ) hij ) ] ; simp +arith +decide );
                    · exact by push Not at h_eq; exact h_eq;
                  obtain ⟨ i, j, hij, hi, hj, h ⟩ := h_seq_repeat;
                  refine' h_contra ⟨ i, hi, _ ⟩;
                  use j - i;
                  exact ⟨ Nat.sub_pos_of_lt hij, by rw [ ← Function.iterate_add_apply, Nat.sub_add_cancel hij.le, h ] ⟩;
                exact le_trans ( Nat.find_min' _ h_depth_le_n.choose_spec.2 ) h_depth_le_n.choose_spec.1;
              exact h_depth_le_n y;
            omega;
      -- Since $q > n$, we have $signatureMap f x = signatureMap f y$.
      have h_signature_eq : signatureMap f x = signatureMap f y := by
        nlinarith [ pow_pos ( by linarith : 0 < q ) N ];
      -- Since $signatureMap f x = signatureMap f y$, we have $f x = f y$.
      have h_fx_fy : f x = f y := by
        apply ih (depth f (f x)) (by
        rw [ ← k, depth_f_of_not_in_cycle f x hx ];
        exact Nat.sub_lt ( Nat.pos_of_ne_zero ( by rintro h; exact hx <| by rw [ depth ] at h; aesop ) ) zero_lt_one) (f x) (f y) (by
        rw [ root_f_eq_root_of_not_in_cycle f x hx, root_f_eq_root_of_not_in_cycle f y hy, h_root ]) (by
        grind) (by
        rfl);
      exact signature_inj f x y h_fx_fy h_signature_eq

/-
If the depth is positive, the tree value is positive.
-/
lemma jq_pos_of_depth_pos {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (q N : ℕ) (x : ZMod n) (h : depth f x > 0) (hq : q > 0) (_hN : N > 0) :
  jq f q N x > 0 := by
    refine' Finset.sum_pos _ _;
    · exact fun i hi => mul_pos ( Nat.succ_pos _ ) ( pow_pos hq _ );
    · exact ⟨ _, Finset.mem_range.mpr h ⟩

/-
The valuation of jq with respect to q is exactly N - depth.
-/
lemma jq_valuation {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (q N : ℕ) (x : ZMod n)
  (hq : q > n) (hN : N ≥ depth f x) (h_depth : depth f x > 0) :
  (q ^ (N - depth f x)) ∣ jq f q N x ∧ ¬ (q ^ (N - depth f x + 1)) ∣ jq f q N x := by
    -- By definition of jq, we can write it as a sum of terms involving powers of q.
    have h_jq_sum :jq f q N x = (signatureMap f (f^[depth f x - 1] x) + 1) * q^(N - depth f x) + ∑ k ∈ Finset.range (depth f x - 1), (signatureMap f (f^[k] x) + 1) * q^(N - 1 - k) := by
      rcases k : depth f x with ( _ | k ) <;> simp_all +decide [ Nat.sub_sub, add_comm ];
      unfold jq; simp +decide [ Nat.sub_sub ] ; ring_nf;
      simp +decide [ k, add_comm, add_assoc, Finset.sum_range_succ ] ; ring_nf;
    -- The sum of the terms involving lower powers of q is divisible by q^(N-depth).
    have h_sum_div : q ^ (N - depth f x + 1) ∣ ∑ k ∈ Finset.range (depth f x - 1), (signatureMap f (f^[k] x) + 1) * q^(N - 1 - k) := by
      refine' Finset.dvd_sum fun k hk => dvd_mul_of_dvd_right ( pow_dvd_pow _ _ ) _;
      norm_num at * ; omega;
    simp_all +decide [ Nat.pow_succ ];
    rw [ Nat.dvd_add_left h_sum_div ];
    rw [ mul_comm ];
    refine' ⟨ dvd_add ( dvd_mul_right _ _ ) _, _ ⟩;
    · exact dvd_of_mul_right_dvd h_sum_div;
    · rw [ Nat.mul_dvd_mul_iff_left ( pow_pos ( by linarith ) _ ) ];
      refine' Nat.not_dvd_of_pos_of_lt _ _;
      · exact Nat.succ_pos _;
      · refine' lt_of_le_of_lt ( Nat.succ_le_of_lt ( signature_bound f _ ) ) hq

/-
jq is zero if and only if the depth is zero.
-/
lemma jq_eq_zero_iff_depth_eq_zero {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (q N : ℕ) (x : ZMod n) (hq : q > 0) (hN : N > 0) :
  jq f q N x = 0 ↔ depth f x = 0 := by
    -- If `depth f x = 0`, then the sum is empty, so `jq = 0`.
    have h_zero : depth f x = 0 → jq f q N x = 0 := by
      unfold jq; aesop;
    exact ⟨ fun h => Nat.eq_zero_of_not_pos fun h' => absurd ( jq_pos_of_depth_pos f q N x h' hq hN ) ( by aesop ), h_zero ⟩

/-
The combined map j satisfies the linear equation.
-/
lemma j_combined_linear {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (p q N : ℕ) (zeta : ZMod p) (x : ZMod n)
  (hpq : Nat.Coprime p (q ^ N)) (h_zeta : zeta ^ (cyclePeriod f x) = 1)
  (_hq : q > n) (_hN : N ≥ n) (hN_depth : N ≥ depth f x) :
  let iso := ZMod.chineseRemainder hpq
  let a := iso.symm (zeta, (q : ZMod (q ^ N)))
  let j := iso.symm (jp f p zeta x, (jq f q N x : ZMod (q ^ N)))
  let j_f := iso.symm (jp f p zeta (f x), (jq f q N (f x) : ZMod (q ^ N)))
  j_f = a * j := by
    -- By definition of $jp$ and $jq$, we know that $jp f p zeta (f x) = zeta * jp f p zeta x$ and $jq f q N (f x) = q * jq f q N x$ modulo $q^N$.
    have h_jp : jp f p zeta (f x) = zeta * jp f p zeta x := by
      exact jp_linear f p zeta x h_zeta
    have h_jq : (jq f q N (f x) : ZMod (q ^ N)) = (q : ZMod (q ^ N)) * jq f q N x := by
      exact jq_mod_linear f q N x hN_depth;
    field_simp;
    rw [ ← map_mul ] ; aesop;

/-
The combined map j satisfies the linear equation.
-/
/-- The CRT combination of `zeta` and `q`; the fixed multiplier of the local representation. -/
noncomputable def multiplier (p q N : ℕ) (zeta : ZMod p) (hpq : Nat.Coprime p (q ^ N)) : ZMod (p * q ^ N) :=
  (ZMod.chineseRemainder hpq).symm (zeta, (q : ZMod (q ^ N)))

/-- Local representation of `f` on a component into `ZMod (p * q ^ N)`, combining `jp` and `jq` by CRT. -/
noncomputable def jMap {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (p q N : ℕ) (zeta : ZMod p) (hpq : Nat.Coprime p (q ^ N)) (x : ZMod n) : ZMod (p * q ^ N) :=
  (ZMod.chineseRemainder hpq).symm (jp f p zeta x, (jq f q N x : ZMod (q ^ N)))

lemma j_map_linear {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (p q N : ℕ) (zeta : ZMod p) (x : ZMod n)
  (hpq : Nat.Coprime p (q ^ N)) (h_zeta : zeta ^ (cyclePeriod f x) = 1)
  (hq : q > n) (hN : N ≥ n) (hN_depth : N ≥ depth f x) :
  jMap f p q N zeta hpq (f x) = multiplier p q N zeta hpq * jMap f p q N zeta hpq x := by
    exact j_combined_linear f p q N zeta x hpq h_zeta hq hN hN_depth

/-
There exists a primitive k-th root of unity modulo p if p = 1 mod k.
-/
lemma exists_primitive_root_of_unity {p k : ℕ} (hp : p.Prime) (hk : k > 0) (h_mod : p ≡ 1 [MOD k]) :
  ∃ zeta : ZMod p, orderOf zeta = k := by
    haveI := Fact.mk hp;
    -- Since $p \equiv 1 \pmod{k}$, we know that $k$ divides $p-1$.
    have h_div : k ∣ p - 1 := by
      simpa [ ← Int.natCast_dvd_natCast, hp.pos ] using h_mod.symm.dvd;
    obtain ⟨ g, hg ⟩ := IsCyclic.exists_generator ( α := ( ZMod p )ˣ );
    -- Since $g$ is a generator of the multiplicative group modulo $p$, we know that $g^{(p-1)/k}$ has order $k$.
    use g ^ ((p - 1) / k);
    rw [ orderOf_pow' ] <;> norm_num [ orderOf_units ];
    · rw [ orderOf_eq_card_of_forall_mem_zpowers hg ];
      norm_num [ Nat.totient_prime hp ];
      rw [ Nat.gcd_eq_right ( Nat.div_dvd_of_dvd h_div ), Nat.div_div_self h_div ( Nat.sub_ne_zero_of_lt hp.one_lt ) ];
    · exact ⟨ hk.ne', Nat.le_of_dvd ( Nat.sub_pos_of_lt hp.one_lt ) h_div ⟩

/-
There exist families of primes P and Q indexed by components satisfying necessary conditions.
-/
lemma exists_valid_primes {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) :
  ∃ P Q : {r // r ∈ components f} → ℕ,
    (∀ r, (P r).Prime) ∧ (∀ r, (Q r).Prime) ∧
    (∀ r, P r > n) ∧ (∀ r, Q r > n) ∧
    (∀ r, P r ≡ 1 [MOD cyclePeriod f r.1]) ∧
    Function.Injective P ∧ Function.Injective Q ∧
    (∀ r1 r2, P r1 ≠ Q r2) := by
      simp +zetaDelta at *;
      have h_inf_primes : Set.Infinite {p : ℕ | Nat.Prime p ∧ p > n ∧ ∀ r ∈ components f, p ≡ 1 [MOD cyclePeriod f r]} := by
        have h_inf_primes : Set.Infinite {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD (∏ r ∈ components f, cyclePeriod f r)]} := by
          apply_rules [ Nat.infinite_setOf_prime_modEq_one ];
          exact Finset.prod_ne_zero_iff.mpr fun x hx => Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by unfold cyclePeriod; aesop;
        refine Set.Infinite.mono ?_ ( h_inf_primes.diff ( Set.finite_le_nat n ) );
        exact fun p hp => ⟨ hp.1.1, not_le.mp hp.2, fun r hr => hp.1.2.of_dvd <| Finset.dvd_prod_of_mem _ hr ⟩;
      have := h_inf_primes.exists_subset_card_eq ( 2 * Finset.card ( components f ) );
      obtain ⟨ t, ht₁, ht₂ ⟩ := this;
      -- We can split the set `t` into two disjoint subsets of equal size, each containing primes greater than `n` and congruent to `1` modulo the cycle period of each component.
      obtain ⟨t₁, t₂, ht₁₂, ht₁, ht₂⟩ : ∃ t₁ t₂ : Finset ℕ, t₁ ∩ t₂ = ∅ ∧ t₁ ∪ t₂ = t ∧ t₁.card = (components f).card ∧ t₂.card = (components f).card := by
        obtain ⟨t₁, ht₁⟩ : ∃ t₁ : Finset ℕ, t₁ ⊆ t ∧ t₁.card = (components f).card := by
          exact Finset.exists_subset_card_eq ( by linarith );
        use t₁, t \ t₁;
        simp_all +decide [ Finset.card_sdiff ];
        rw [ Finset.inter_eq_left.mpr ht₁.1, ht₁.2, two_mul, add_tsub_cancel_left ];
      -- We can define the functions P and Q using the elements of t₁ and t₂.
      obtain ⟨P, hP⟩ : ∃ P : { r // r ∈ components f } → ℕ, Function.Injective P ∧ ∀ r, P r ∈ t₁ := by
        have hP : Nonempty (components f ≃ t₁) := by
          exact ⟨ Fintype.equivOfCardEq <| by aesop ⟩;
        exact ⟨ _, Subtype.val_injective.comp hP.some.injective, fun r => hP.some r |>.2 ⟩
      obtain ⟨Q, hQ⟩ : ∃ Q : { r // r ∈ components f } → ℕ, Function.Injective Q ∧ ∀ r, Q r ∈ t₂ := by
        have h_equiv : Nonempty (components f ≃ t₂) := by
          exact ⟨ Fintype.equivOfCardEq <| by aesop ⟩;
        exact ⟨ fun r => h_equiv.some r |>.1, Subtype.coe_injective.comp h_equiv.some.injective, fun r => h_equiv.some r |>.2 ⟩;
      refine' ⟨ P, _, Q, _, _, _, _ ⟩ <;> simp_all +decide [ Finset.ext_iff, Set.subset_def ];
      · exact fun a b => ( ‹∀ x ∈ t, Nat.Prime x ∧ n < x ∧ ∀ r ∈ components f, x ≡ 1 [MOD cyclePeriod f r]› _ ( ht₁ _ |>.1 ( Or.inl ( hP.2 a b ) ) ) ) |>.1;
      · exact fun a ha => by have := hQ.2 a ha; specialize ht₁ ( Q ⟨ a, ha ⟩ ) ; aesop;
      · exact fun a ha => ( ‹∀ x ∈ t, Nat.Prime x ∧ n < x ∧ ∀ r ∈ components f, x ≡ 1 [MOD cyclePeriod f r]› _ ( ht₁ _ |>.1 ( Or.inl ( hP.2 _ ha ) ) ) ) |>.2.1;
      · exact fun a ha => ( ‹∀ x ∈ t, Nat.Prime x ∧ n < x ∧ ∀ r ∈ components f, x ≡ 1 [MOD cyclePeriod f r]› _ ( ht₁ _ |>.1 ( Or.inr ( hQ.2 _ ha ) ) ) ) |>.2.1;
      · exact ⟨ fun a ha => by have := ‹∀ x ∈ t, Nat.Prime x ∧ n < x ∧ ∀ r ∈ components f, x ≡ 1 [MOD cyclePeriod f r]› ( P ⟨ a, ha ⟩ ) ( ht₁ _ |>.1 ( Or.inl ( hP.2 a ha ) ) ) ; aesop, fun a ha b hb => fun h => ht₁₂ _ ( hP.2 a ha ) ( h.symm ▸ hQ.2 b hb ) ⟩

/-
Equality of jMap implies equality of its components jp and jq.
-/
lemma j_map_eq_implies_parts {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (p q N : ℕ) (zeta : ZMod p)
  (hpq : Nat.Coprime p (q ^ N)) (x y : ZMod n)
  (hq : q > n) (_hN : N ≥ n) (hN_depth : ∀ z, N ≥ depth f z)
  (h_eq : jMap f p q N zeta hpq x = jMap f p q N zeta hpq y) :
  jp f p zeta x = jp f p zeta y ∧ jq f q N x = jq f q N y := by
    -- Since the Chinese Remainder Theorem isomorphism is injective, if $jMap x = jMap y$, then their components must be equal.
    have h_components : (jp f p zeta x, (jq f q N x : ZMod (q ^ N))) = (jp f p zeta y, (jq f q N y : ZMod (q ^ N))) := by
      exact ( ZMod.chineseRemainder hpq ).symm.injective h_eq;
    simp +zetaDelta at *;
    exact ⟨ h_components.1, Nat.mod_eq_of_lt ( show jq f q N x < q ^ N from by exact jq_bound f q N x hq (hN_depth x) ) ▸ Nat.mod_eq_of_lt ( show jq f q N y < q ^ N from by exact jq_bound f q N y hq (hN_depth y) ) ▸ by simpa [ ← ZMod.natCast_eq_natCast_iff' ] using h_components.2 ⟩

/-
Equality of jq implies equality of depth.
-/
lemma depth_eq_of_jq_eq {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (q N : ℕ) (x y : ZMod n)
  (hq : q > n) (hN : N ≥ n) (hN_depth : ∀ z, N ≥ depth f z)
  (h_eq : jq f q N x = jq f q N y) :
  depth f x = depth f y := by
    by_cases hx : depth f x > 0 <;> by_cases hy : depth f y > 0 <;> simp_all +decide;
    · -- Since these are powers of $q$, and $q$ is greater than $n$, the only way for these two expressions to be equal is if the exponents are equal.
      have h_exp_eq : N - depth f x = N - depth f y := by
        have h_val_eq : (q ^ (N - depth f x)) ∣ jq f q N x ∧ ¬(q ^ (N - depth f x + 1)) ∣ jq f q N x ∧ (q ^ (N - depth f y)) ∣ jq f q N y ∧ ¬(q ^ (N - depth f y + 1)) ∣ jq f q N y := by
          exact ⟨ by simpa [ h_eq ] using jq_valuation f q N x ( by linarith ) ( by linarith [ hN_depth x ] ) hx |>.1, by simpa [ h_eq ] using jq_valuation f q N x ( by linarith ) ( by linarith [ hN_depth x ] ) hx |>.2, by simpa [ h_eq ] using jq_valuation f q N y ( by linarith ) ( by linarith [ hN_depth y ] ) hy |>.1, by simpa [ h_eq ] using jq_valuation f q N y ( by linarith ) ( by linarith [ hN_depth y ] ) hy |>.2 ⟩
        generalize_proofs at *; (
        exact le_antisymm ( Nat.le_of_not_lt fun h => h_val_eq.2.2.2 <| h_eq ▸ dvd_trans ( pow_dvd_pow _ h ) h_val_eq.1 ) ( Nat.le_of_not_lt fun h => h_val_eq.2.1 <| h_eq ▸ dvd_trans ( pow_dvd_pow _ h ) h_val_eq.2.2.1 ))
      generalize_proofs at *; (
      rw [ tsub_right_inj ] at h_exp_eq <;> linarith [ hN_depth x, hN_depth y ]);
    · -- Since $depth f y = 0$, we have $jq f q N y = 0$.
      have h_jq_y_zero : jq f q N y = 0 := by
        unfold jq; aesop;
      have := jq_valuation f q N x hq ( hN_depth x ) hx; aesop;
    · have h_contra : jq f q N y = 0 := by
        rw [ ← h_eq, jq_eq_zero_iff_depth_eq_zero ] ; aesop;
        · linarith;
        · linarith [ NeZero.pos n ];
      have := jq_valuation f q N y ; aesop

/-
The cycle position is less than the cycle period.
-/
lemma cycle_position_lt_cycle_period {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) :
  cyclePosition f x < cyclePeriod f x := by
    have h_exists_k : ∃ k, f^[k] (componentRep f x) = root f x ∧ k < cyclePeriod f x := by
      -- By definition of `Nat.find`, we know that `root f x` is in the cycle elements and thus there exists some `k` such that `f^[k] (componentRep f x) = root f x`.
      obtain ⟨k, hk⟩ : ∃ k, f^[k] (componentRep f x) = root f x := by
        exact ⟨ cyclePosition f x, by exact Nat.find_spec ( _ : ∃ k, f^[k] ( componentRep f x ) = root f x ) ⟩;
      refine' ⟨ k % cyclePeriod f x, _, _ ⟩;
      · rw [ ← hk, ← Nat.mod_add_div k ( cyclePeriod f x ), Function.iterate_add_apply ];
        induction k / cyclePeriod f x <;> simp_all +decide [ Nat.mul_succ, ← Function.iterate_add_apply ];
        simp_all +decide [ ← add_assoc, Nat.add_mod ];
        -- By definition of cyclePeriod, we know that f^[cyclePeriod f x] (componentRep f x) = componentRep f x.
        have h_cycle : f^[cyclePeriod f x] (componentRep f x) = componentRep f x := by
          have h_root : f^[cyclePeriod f x] (root f x) = root f x := by
            exact iterate_cycle_period_root f x
          have h_root : componentRep f x ∈ cycleElements f x := by
            exact component_rep_mem_cycle f x;
          obtain ⟨ k, hk ⟩ := Finset.mem_image.mp h_root;
          rw [ ← hk.2, ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply ] ; aesop;
        simp +decide [ *, Function.iterate_add_apply ];
      · exact Nat.mod_lt _ ( cycle_period_pos f x );
    unfold cyclePosition; aesop;

/-
If two elements have the same component representative and cycle position, they have the same root.
-/
lemma root_eq_of_cycle_position_eq {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x y : ZMod n)
  (h_comp : componentRep f x = componentRep f y)
  (h_pos : cyclePosition f x = cyclePosition f y) :
  root f x = root f y := by
    -- By definition of $cycle\_position$, we know that $f^{cycle\_position f x} (component\_rep f x) = root f x$ and $f^{cycle\_position f y} (component\_rep f y) = root f y$.
    have h_cycle_pos_eq : f^[cyclePosition f x] (componentRep f x) = root f x ∧ f^[cyclePosition f y] (componentRep f y) = root f y := by
      exact ⟨ Nat.find_spec ( _ : ∃ k, f^[k] ( componentRep f x ) = root f x ), Nat.find_spec ( _ : ∃ k, f^[k] ( componentRep f y ) = root f y ) ⟩;
    aesop

/-
Equality of jp implies equality of cycle positions for the roots.
-/
lemma cycle_position_eq_of_jp_eq {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (p : ℕ) (zeta : ZMod p) (x y : ZMod n)
  (h_comp : componentRep f x = componentRep f y)
  (h_zeta_order : orderOf zeta = cyclePeriod f x)
  (h_depth : depth f x = depth f y)
  (h_jp : jp f p zeta x = jp f p zeta y) :
  cyclePosition f (root f x) = cyclePosition f (root f y) := by
    have h_jp_exp : zeta ^ (cyclePosition f (root f x)) * (zeta⁻¹) ^ (depth f x) = zeta ^ (cyclePosition f (root f y)) * (zeta⁻¹) ^ (depth f y) := by
      exact h_jp;
    by_cases h : IsUnit zeta <;> simp_all +decide;
    · have h_cycle_pos_eq : zeta ^ (cyclePosition f (root f x)) = zeta ^ (cyclePosition f (root f y)) := by
        have h_inv : IsUnit (zeta⁻¹ ^ depth f y) := by
          exact IsUnit.pow _ ( by cases h ; aesop );
        exact h_inv.mul_left_inj.mp h_jp_exp;
      have h_cycle_pos_eq : cyclePosition f (root f x) ≡ cyclePosition f (root f y) [MOD orderOf zeta] := by
        rw [ Nat.modEq_iff_dvd ];
        rw [ dvd_sub_comm ];
        have h_cycle_pos_eq : zeta ^ (cyclePosition f (root f x) - cyclePosition f (root f y)) = 1 := by
          cases le_total ( cyclePosition f ( root f x ) ) ( cyclePosition f ( root f y ) ) <;> simp_all +decide;
          cases le_iff_exists_add'.mp ‹_› ; simp_all +decide [ pow_add ];
          have h_cycle_pos_eq : IsUnit (zeta ^ cyclePosition f (root f y)) := by
            exact h.pow _;
          exact h_cycle_pos_eq.mul_left_inj.mp ( by linear_combination' ‹zeta ^ _ * zeta ^ cyclePosition f ( root f y ) = zeta ^ cyclePosition f ( root f y ) › );
        cases le_total ( cyclePosition f ( root f x ) ) ( cyclePosition f ( root f y ) ) <;> simp_all +decide;
        · have h_cycle_pos_eq : zeta ^ (cyclePosition f (root f y) - cyclePosition f (root f x)) = 1 := by
            have h_cycle_pos_eq : zeta ^ (cyclePosition f (root f y) - cyclePosition f (root f x)) * zeta ^ (cyclePosition f (root f x)) = zeta ^ (cyclePosition f (root f x)) := by
              rw [ ← pow_add, Nat.sub_add_cancel ‹_›, h_cycle_pos_eq ];
            have h_cycle_pos_eq : IsUnit (zeta ^ cyclePosition f (root f x)) := by
              exact h.pow _;
            exact h_cycle_pos_eq.mul_left_cancel ( by linear_combination' ‹zeta ^ ( cyclePosition f ( root f y ) - cyclePosition f ( root f x ) ) * zeta ^ cyclePosition f ( root f x ) = zeta ^ cyclePosition f ( root f x ) › );
          rw [ dvd_sub_comm ] ; exact_mod_cast h_zeta_order ▸ orderOf_dvd_iff_pow_eq_one.mpr h_cycle_pos_eq;
        · have := orderOf_dvd_iff_pow_eq_one.mpr h_cycle_pos_eq;
          simpa [ h_zeta_order, Nat.cast_sub ‹_› ] using Int.natCast_dvd_natCast.mpr this;
      have h_cycle_pos_eq : cyclePosition f (root f x) < cyclePeriod f x ∧ cyclePosition f (root f y) < cyclePeriod f x := by
        have h_cycle_pos_eq : ∀ x, cyclePosition f (root f x) < cyclePeriod f x := by
          intros x; exact (by
          convert cycle_position_lt_cycle_period f ( root f x ) using 1;
          apply cycle_period_eq_of_mem_cycle_elements;
          exact Finset.mem_image.mpr ⟨ 0, Finset.mem_range.mpr ( Nat.pos_of_ne_zero ( by
            exact Nat.ne_of_gt ( cycle_period_pos f x ) ) ), by simp +decide ⟩);
        have h_cycle_pos_eq : cyclePeriod f x = cyclePeriod f y := by
          exact cycle_period_eq_of_component_rep_eq f x y h_comp;
        grind;
      simp_all +decide [ Nat.ModEq, Nat.mod_eq_of_lt ];
    · have := orderOf_dvd_iff_pow_eq_one.1 ( dvd_of_eq h_zeta_order );
      contrapose! h;
      exact isUnit_iff_dvd_one.mpr ( this ▸ dvd_pow_self _ ( Nat.ne_of_gt ( cycle_period_pos f x ) ) )

/-
jMap is injective for elements in the same component.
-/
lemma j_map_injective {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (p q N : ℕ) (zeta : ZMod p)
  (hpq : Nat.Coprime p (q ^ N))
  (hq : q > n) (hN : N ≥ n) (hN_depth : ∀ z, N ≥ depth f z)
  (x y : ZMod n)
  (h_comp : componentRep f x = componentRep f y)
  (h_zeta_order : orderOf zeta = cyclePeriod f x)
  (h_eq : jMap f p q N zeta hpq x = jMap f p q N zeta hpq y) :
  x = y := by
  have h_parts : jp f p zeta x = jp f p zeta y ∧ jq f q N x = jq f q N y := by
    exact j_map_eq_implies_parts f p q N zeta hpq x y hq hN hN_depth h_eq
  have h_depth : depth f x = depth f y := by
    -- Since $jq f q N x = jq f q N y$, and $q > n$, it follows that $depth f x = depth f y$.
    apply depth_eq_of_jq_eq f q N x y hq hN hN_depth h_parts.right
  have h_pos : cyclePosition f (root f x) = cyclePosition f (root f y) := by
    -- Apply the lemma cycle_position_eq_of_jp_eq with the given hypotheses.
    apply cycle_position_eq_of_jp_eq f p zeta x y h_comp h_zeta_order h_depth h_parts.left
  have h_root : root f x = root f y := by
    -- Since the roots are in the same cycle and have the same cycle position, they must be the same element.
    have h_root_eq : ∀ {x y : ZMod n}, inCycle f x → inCycle f y → componentRep f x = componentRep f y → cyclePosition f x = cyclePosition f y → x = y := by
      intros x y hx hy h_comp h_pos;
      have h_root_eq : root f x = root f y := by
        exact root_eq_of_cycle_position_eq f x y h_comp h_pos;
      rw [ root_eq_self_of_in_cycle f x hx, root_eq_self_of_in_cycle f y hy ] at h_root_eq ; aesop;
    apply h_root_eq (root_in_cycle f x) (root_in_cycle f y);
    · have h_root_comp : componentRep f x = componentRep f (root f x) ∧ componentRep f y = componentRep f (root f y) := by
        have h_root_comp : ∀ x, componentRep f x = componentRep f (root f x) := by
          intros x
          apply Eq.symm;
          have h_root_cycle : cycleElements f (root f x) = cycleElements f x := by
            unfold cycleElements;
            rw [ root_eq_self_of_in_cycle f ( root f x ) ( root_in_cycle f x ) ];
            rw [ cycle_period_eq_of_mem_cycle_elements f x ( root f x ) ( by
              exact Finset.mem_image.mpr ⟨ 0, Finset.mem_range.mpr ( Nat.pos_of_ne_zero ( by linarith [ cycle_period_pos f x ] ) ), by simp +decide ⟩ ) ];
          unfold componentRep; aesop;
        exact ⟨ h_root_comp x, h_root_comp y ⟩;
      rw [ ← h_root_comp.1, ← h_root_comp.2, h_comp ];
    · exact h_pos
  -- Apply the lemma that states if the roots are equal and the jq values are equal, then the elements must be equal.
  apply jq_inj f q N x y hq hN h_root h_parts.2

/-
jp is a unit.
-/
lemma jp_is_unit {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (p : ℕ) (zeta : ZMod p) (x : ZMod n)
  (h_zeta_order : orderOf zeta = cyclePeriod f x) :
  IsUnit (jp f p zeta x) := by
    by_contra h_not_unit;
    have h_unit : IsUnit zeta := by
      have h_unit : zeta ^ cyclePeriod f x = 1 := by
        rw [ ← h_zeta_order, pow_orderOf_eq_one ];
      exact isUnit_iff_dvd_one.mpr ( h_unit ▸ dvd_pow_self _ ( by linarith [ cycle_period_pos f x ] ) );
    obtain ⟨ k, hk ⟩ := h_unit;
    exact h_not_unit <| by rw [ show jp f p zeta x = zeta ^ ( cyclePosition f ( root f x ) ) * zeta⁻¹ ^ ( depth f x ) by rfl ] ; exact IsUnit.mul ( IsUnit.pow _ <| by aesop ) ( IsUnit.pow _ <| by aesop ) ;

/-
jMap is non-zero.
-/
lemma j_map_ne_zero {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (p q N : ℕ) (zeta : ZMod p)
  (hpq : Nat.Coprime p (q ^ N)) (x : ZMod n)
  (hp : p.Prime)
  (h_zeta_order : orderOf zeta = cyclePeriod f x) :
  jMap f p q N zeta hpq x ≠ 0 := by
    unfold jMap;
    -- Since $jp$ is a unit and $jq$ is non-zero, their combination is non-zero.
    have h_jp_nonzero : jp f p zeta x ≠ 0 := by
      haveI := Fact.mk hp; exact IsUnit.ne_zero ( jp_is_unit f p zeta x h_zeta_order ) ;
    have := ( ZMod.chineseRemainder hpq ).symm.injective ; aesop

/-
The component representative is invariant under f.
-/
lemma component_rep_apply {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) :
  componentRep f (f x) = componentRep f x := by
    -- Consider two cases: when x is in a cycle and when it is not.
    by_cases hx_cycle : inCycle f x;
    · unfold componentRep;
      -- Since $x$ is in the cycle, we have $cycleElements f (f x) = cycleElements f x$.
      have h_cycle_elements_eq : cycleElements f (f x) = cycleElements f x := by
        exact cycle_elements_eq_of_in_cycle f x hx_cycle;
      aesop;
    · -- Since x is not in a cycle, its root is the same as the root of f(x).
      have h_root_eq : root f x = root f (f x) := by
        exact Eq.symm (root_f_eq_root_of_not_in_cycle f x hx_cycle);
      -- Since the roots are the same, the cycle elements are the same, and thus their component representatives are the same.
      have h_cycle_elements_eq : cycleElements f x = cycleElements f (f x) := by
        unfold cycleElements;
        unfold cyclePeriod at * ; aesop;
      unfold componentRep; aesop;

/-
Helper lemma: The moduli P_r * Q_r^n are pairwise coprime.
-/
lemma global_coprime {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (P Q : {r // r ∈ components f} → ℕ)
  (hP : ∀ r, (P r).Prime) (hQ : ∀ r, (Q r).Prime)
  (h_disjoint : ∀ r1 r2, P r1 ≠ Q r2)
  (hP_inj : Function.Injective P) (hQ_inj : Function.Injective Q) :
  Pairwise (Function.onFun Nat.Coprime (fun r => P r * (Q r) ^ n)) := by
    intros r1 r2 hr ; simp_all +decide [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right ];
    refine' ⟨ ⟨ Nat.coprime_iff_gcd_eq_one.mpr _, _ ⟩, _, _ ⟩;
    · exact Nat.coprime_iff_gcd_eq_one.mpr ( by have := Nat.coprime_primes ( hP _ r1.2 ) ( hP _ r2.2 ) ; tauto );
    · exact Nat.Coprime.pow_left _ ( Nat.Coprime.symm ( hP _ _ |> Nat.Prime.coprime_iff_not_dvd |> Iff.mpr <| fun h => h_disjoint _ _ _ _ <| by have := Nat.prime_dvd_prime_iff_eq ( hP _ r2.2 ) ( hQ _ r1.2 ) ; tauto ) );
    · exact Nat.Coprime.pow_right _ ( Nat.coprime_iff_gcd_eq_one.mpr <| by have := Nat.coprime_primes ( hP _ r1.2 ) ( hQ _ r2.2 ) ; aesop );
    · exact Nat.coprime_pow_primes _ _ ( hQ _ _ ) ( hQ _ _ ) ( hQ_inj.ne hr )

/-
The global injection and multiplier using N = n.
-/
/-- The global injection assembling the per-component local representations by CRT. -/
def globalJ {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (P Q : {r // r ∈ components f} → ℕ)
  (zeta : Π r, ZMod (P r))
  (hpq : ∀ r, Nat.Coprime (P r) ((Q r) ^ n))
  (hP : ∀ r, (P r).Prime) (hQ : ∀ r, (Q r).Prime)
  (h_disjoint : ∀ r1 r2, P r1 ≠ Q r2)
  (hP_inj : Function.Injective P) (hQ_inj : Function.Injective Q)
  (x : ZMod n) : ZMod (∏ r, P r * (Q r) ^ n) :=
  (ZMod.prodEquivPi (fun r => P r * (Q r) ^ n)
    (global_coprime f P Q hP hQ h_disjoint hP_inj hQ_inj)).symm (fun r =>
    if _h : r.val = componentRep f x then
      jMap f (P r) (Q r) n (zeta r) (hpq r) x
    else
      0)

/-- The global multiplier: the per-component multipliers assembled by CRT. -/
def globalMultiplier {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (P Q : {r // r ∈ components f} → ℕ)
  (zeta : Π r, ZMod (P r))
  (hpq : ∀ r, Nat.Coprime (P r) ((Q r) ^ n))
  (hP : ∀ r, (P r).Prime) (hQ : ∀ r, (Q r).Prime)
  (h_disjoint : ∀ r1 r2, P r1 ≠ Q r2)
  (hP_inj : Function.Injective P) (hQ_inj : Function.Injective Q) :
  ZMod (∏ r, P r * (Q r) ^ n) :=
  (ZMod.prodEquivPi (fun r => P r * (Q r) ^ n)
    (global_coprime f P Q hP hQ h_disjoint hP_inj hQ_inj)).symm (fun r =>
    multiplier (P r) (Q r) n (zeta r) (hpq r))

/-
Lemma: depth is bounded by n. Definition: global isomorphism for N=n.
-/
lemma depth_le_n {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (x : ZMod n) : depth f x ≤ n := by
  -- By definition of depth, we know that there exists some k such that f^[k] x is in a cycle.
  obtain ⟨k, hk⟩ : ∃ k, inCycle f (f^[k] x) ∧ k ≤ n := by
    -- By the pigeonhole principle, since the sequence $f^[k] x$ is finite, there must exist $i < j$ such that $f^[i] x = f^[j] x$.
    obtain ⟨i, j, hij, h_eq⟩ : ∃ i j : ℕ, i < j ∧ i ≤ n ∧ j ≤ n ∧ f^[i] x = f^[j] x := by
      by_contra! h;
      exact absurd ( Finset.card_le_univ ( Finset.image ( fun i => f^[i] x ) ( Finset.Iic n ) ) ) ( by rw [ Finset.card_image_of_injOn fun i hi j hj hij => le_antisymm ( Nat.le_of_not_lt fun hi' => h _ _ hi' ( by aesop ) ( by aesop ) hij.symm ) ( Nat.le_of_not_lt fun hj' => h _ _ hj' ( by aesop ) ( by aesop ) hij ) ] ; simp +arith +decide );
    refine' ⟨ i, ⟨ j - i, Nat.sub_pos_of_lt hij, _ ⟩, h_eq.1 ⟩;
    rw [ ← Function.iterate_add_apply, Nat.sub_add_cancel hij.le, h_eq.2.2 ];
  apply le_trans (Nat.find_min' (exists_iterate_in_cycle f x) hk.left) hk.right

/-- The CRT isomorphism `ZMod (∏ r, P r * Q r ^ n) ≃+* ∏ r, ZMod (P r * Q r ^ n)`. -/
def globalIso {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (P Q : {r // r ∈ components f} → ℕ)
  (hP : ∀ r, (P r).Prime) (hQ : ∀ r, (Q r).Prime)
  (h_disjoint : ∀ r1 r2, P r1 ≠ Q r2)
  (hP_inj : Function.Injective P) (hQ_inj : Function.Injective Q) :
  ZMod (∏ r, P r * (Q r) ^ n) ≃+* Π r, ZMod (P r * (Q r) ^ n) :=
  ZMod.prodEquivPi (fun r => P r * (Q r) ^ n) (global_coprime f P Q hP hQ h_disjoint hP_inj hQ_inj)

/-
The global modulus m for the construction.
-/
/-- The global modulus `∏ r, P r * Q r ^ n`. -/
def globalM {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (P Q : {r // r ∈ components f} → ℕ) : ℕ :=
  ∏ r, P r * (Q r) ^ n

lemma global_m_pos {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (P Q : {r // r ∈ components f} → ℕ)
  (hP : ∀ r, (P r).Prime) (hQ : ∀ r, (Q r).Prime) :
  globalM f P Q > 0 := by
    exact Finset.prod_pos fun r hr => mul_pos ( Nat.Prime.pos ( hP r ) ) ( pow_pos ( Nat.Prime.pos ( hQ r ) ) _ )

/-
Injectivity of globalJ.
-/
lemma global_j_injective {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (P Q : {r // r ∈ components f} → ℕ)
  (zeta : Π r, ZMod (P r))
  (hpq : ∀ r, Nat.Coprime (P r) ((Q r) ^ n))
  (hP : ∀ r, (P r).Prime) (hQ : ∀ r, (Q r).Prime)
  (h_disjoint : ∀ r1 r2, P r1 ≠ Q r2)
  (hP_inj : Function.Injective P) (hQ_inj : Function.Injective Q)
  (_hP_gt : ∀ r, P r > n) (hQ_gt : ∀ r, Q r > n)
  (h_zeta : ∀ r, orderOf (zeta r) = cyclePeriod f r.1) :
  Function.Injective (globalJ f P Q zeta hpq hP hQ h_disjoint hP_inj hQ_inj) := by
    -- By definition of `globalJ`, if `globalJ x = globalJ y`, then for every component `r`, the `jMap` values for `x` and `y` must be equal.
    intro x y h_eq
    have h_comp : componentRep f x = componentRep f y := by
      contrapose! h_eq;
      unfold globalJ;
      -- Since componentRep f x ≠ componentRep f y, there exists some component r where the jMap values are different.
      obtain ⟨r, hr⟩ : ∃ r : { r // r ∈ components f }, (r.val = componentRep f x) ∧ (r.val ≠ componentRep f y) := by
        exact ⟨ ⟨ componentRep f x, Finset.mem_image.mpr ⟨ x, Finset.mem_univ _, rfl ⟩ ⟩, rfl, h_eq ⟩;
      simp_all +decide [ funext_iff, ZMod.prodEquivPi ];
      use r.val, r.prop;
      simp_all +decide;
      apply j_map_ne_zero;
      · exact hP _ _;
      · convert h_zeta r.val r.prop using 1;
        rw [ hr.1 ];
        rw [ ← hr.1, cycle_period_eq_of_mem_cycle_elements ];
        exact hr.1.symm ▸ component_rep_mem_cycle f x;
    have h_jp : ∀ r : { r // r ∈ components f }, r.val = componentRep f x → jMap f (P r) (Q r) n (zeta r) (hpq r) x = jMap f (P r) (Q r) n (zeta r) (hpq r) y := by
      intro r hr
      have h_eq_j_map : (globalIso f P Q hP hQ h_disjoint hP_inj hQ_inj).symm (fun r => if h : r.val = componentRep f x then jMap f (P r) (Q r) n (zeta r) (hpq r) x else 0) = (globalIso f P Q hP hQ h_disjoint hP_inj hQ_inj).symm (fun r => if h : r.val = componentRep f y then jMap f (P r) (Q r) n (zeta r) (hpq r) y else 0) := by
        exact h_eq;
      replace h_eq_j_map := congr_arg ( fun z => ( globalIso f P Q hP hQ h_disjoint hP_inj hQ_inj ) z r ) h_eq_j_map
      simp only [RingEquiv.apply_symm_apply, dif_pos hr, dif_pos (hr.trans h_comp)] at h_eq_j_map
      exact h_eq_j_map
    apply j_map_injective f (P ⟨componentRep f x, by
      exact Finset.mem_image_of_mem _ ( Finset.mem_univ _ )⟩) (Q ⟨componentRep f x, by
      exact Finset.mem_image_of_mem _ ( Finset.mem_univ _ )⟩) n (zeta ⟨componentRep f x, by
      exact Finset.mem_image_of_mem _ ( Finset.mem_univ _ )⟩) (hpq ⟨componentRep f x, by
      exact Finset.mem_image_of_mem _ ( Finset.mem_univ _ )⟩) (by
    exact hQ_gt _) (by
    norm_num) (by
    exact fun z => depth_le_n f z) x y h_comp (by
    all_goals generalize_proofs at *;
    convert h_zeta ⟨ componentRep f x, by assumption ⟩ using 1
    generalize_proofs at *;
    -- Since componentRep f x is in the cycle elements of x, and componentRep f x is in the cycle elements of componentRep f x, the cycle periods must be equal.
    have h_cycle_period_eq : cyclePeriod f x = cyclePeriod f (componentRep f x) := by
      have h_cycle_elements : componentRep f x ∈ cycleElements f x := by
        exact component_rep_mem_cycle f x
      exact cycle_period_eq_of_mem_cycle_elements f x (componentRep f x) h_cycle_elements;
    exact h_cycle_period_eq) (h_jp ⟨componentRep f x, by
      exact Finset.mem_image_of_mem _ ( Finset.mem_univ _ )⟩ rfl)

/-
Linearity of globalJ.
-/
lemma global_j_linear {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) (P Q : {r // r ∈ components f} → ℕ)
  (zeta : Π r, ZMod (P r))
  (hpq : ∀ r, Nat.Coprime (P r) ((Q r) ^ n))
  (hP : ∀ r, (P r).Prime) (hQ : ∀ r, (Q r).Prime)
  (h_disjoint : ∀ r1 r2, P r1 ≠ Q r2)
  (hP_inj : Function.Injective P) (hQ_inj : Function.Injective Q)
  (_hP_gt : ∀ r, P r > n) (hQ_gt : ∀ r, Q r > n)
  (h_zeta : ∀ r, orderOf (zeta r) = cyclePeriod f r.1) :
  ∀ x, globalJ f P Q zeta hpq hP hQ h_disjoint hP_inj hQ_inj (f x) =
       globalMultiplier f P Q zeta hpq hP hQ h_disjoint hP_inj hQ_inj *
       globalJ f P Q zeta hpq hP hQ h_disjoint hP_inj hQ_inj x := by
         intro x;
         apply (globalIso f P Q hP hQ h_disjoint hP_inj hQ_inj).injective;
         ext r;
         by_cases hr : r.val = componentRep f x
         -- Unfold all three `prodEquivPi` uses together so `apply_symm_apply` matches in one pass,
         -- with `hr` in scope so the `dite`s resolve in each branch.
         · simp only [globalJ, globalMultiplier, globalIso, map_mul, Pi.mul_apply,
             RingEquiv.apply_symm_apply, component_rep_apply, dif_pos hr];
           apply j_map_linear;
           · have := h_zeta r;
             -- Since $r.val = componentRep f x$, we have $cyclePeriod f r.val = cyclePeriod f (componentRep f x)$.
             have h_cycle_period_eq : cyclePeriod f r.val = cyclePeriod f (componentRep f x) := by
               rw [ hr ];
             rw [ ← orderOf_dvd_iff_pow_eq_one ];
             rw [ this, h_cycle_period_eq ];
             have h_cycle_period_eq : componentRep f x ∈ cycleElements f x := by
               exact component_rep_mem_cycle f x;
             rw [ cycle_period_eq_of_mem_cycle_elements f x ( componentRep f x ) h_cycle_period_eq ];
           · exact hQ_gt r;
           · norm_num;
           · exact depth_le_n f x;
         · simp only [globalJ, globalMultiplier, globalIso, map_mul, Pi.mul_apply,
             RingEquiv.apply_symm_apply, component_rep_apply, dif_neg hr, mul_zero]

/-
Main Theorem: Any finite function f: Z/nZ -> Z/nZ has a linear representation.
-/
theorem linear_representation {n : ℕ} [NeZero n] (f : ZMod n → ZMod n) : hasLinearRepresentation f := by
  -- Let's denote the set of components as `R`.
  set R := components f with hR_def;
  -- Let's denote the set of components as `R` and choose primes `P` and `Q` for each component.
  obtain ⟨P, Q, hP, hQ, h_disjoint, hP_inj, hQ_inj⟩ : ∃ P Q : {r // r ∈ R} → ℕ, (∀ r, (P r).Prime) ∧ (∀ r, (Q r).Prime) ∧ (∀ r, P r > n) ∧ (∀ r, Q r > n) ∧ (∀ r, P r ≡ 1 [MOD cyclePeriod f r.1]) ∧ Function.Injective P ∧ Function.Injective Q ∧ (∀ r1 r2, P r1 ≠ Q r2) := by
    exact exists_valid_primes f;
  -- Let's choose a primitive root of unity `zeta` for each component.
  obtain ⟨zeta, hzeta⟩ : ∃ zeta : Π r : {r // r ∈ R}, ZMod (P r), ∀ r, orderOf (zeta r) = cyclePeriod f r.1 := by
    have h_primitive_root : ∀ r : {r // r ∈ R}, ∃ zeta : ZMod (P r), orderOf zeta = cyclePeriod f r.1 := by
      intro r;
      have := hQ_inj.1 r;
      have := exists_primitive_root_of_unity ( hP r ) ( show 0 < cyclePeriod f r from ?_ ) this;
      · exact this;
      · exact cycle_period_pos f ↑r;
    exact ⟨ fun r => Classical.choose ( h_primitive_root r ), fun r => Classical.choose_spec ( h_primitive_root r ) ⟩;
  -- Let's choose the global modulus `m` and multiplier `a`.
  use globalM f P Q, globalMultiplier f P Q zeta (fun r => Nat.coprime_iff_gcd_eq_one.mpr (by
  exact Nat.Coprime.pow_right _ ( Nat.coprime_iff_gcd_eq_one.mpr <| by have := Nat.coprime_primes ( hP r ) ( hQ r ) ; aesop ))) hP hQ hQ_inj.right.right.right (hQ_inj.right.left) (hQ_inj.right.right.left), globalJ f P Q zeta (fun r => Nat.coprime_iff_gcd_eq_one.mpr (by
  exact Nat.Coprime.pow_right _ ( Nat.coprime_iff_gcd_eq_one.mpr <| by have := Nat.coprime_primes ( hP r ) ( hQ r ) ; aesop ))) hP hQ hQ_inj.right.right.right (hQ_inj.right.left) (hQ_inj.right.right.left);
  all_goals generalize_proofs at *;
  exact ⟨ global_m_pos f P Q hP hQ, global_j_injective f P Q zeta ‹_› hP hQ ‹_› ‹_› ‹_› ( fun r => h_disjoint r ) ( fun r => hP_inj r ) ( fun r => hzeta r ), global_j_linear f P Q zeta ‹_› hP hQ ‹_› ‹_› ‹_› ( fun r => h_disjoint r ) ( fun r => hP_inj r ) ( fun r => hzeta r ) ⟩

end Finbin
