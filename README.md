# FinBin

Embedding finite functions `X^k → X` into low-degree polynomial functions over commutative
rings, with machine-checked proofs in Lean 4 (Mathlib) and an accompanying blueprint
article.

The motivation is cellular automata: a `k`-neighbour transition function is a map
`X^k → X`, and relabelling the alphabet by an injection `j : X → R` so that the transition
becomes the restriction of a polynomial map leaves the dynamics unchanged (cf. Smith's
universality of two-neighbour cellular automata).

## Results

All statements are formalised under the `Finbin` namespace; the canonical embedding notion
is `Finbin.EmbedsInDegree` ([Finbin/Embedding.lean](Finbin/Embedding.lean)).

| Result | Statement | Canonical form | Underlying theorem |
|---|---|---|---|
| Unary linear embedding | every `f : ZMod n → ZMod n` embeds in degree 1 | `Finbin.embedsInDegree_unary` | `Finbin.linear_representation` ([Finbin/UnaryLinear.lean](Finbin/UnaryLinear.lean)) |
| Quartic delta embedding | every binary Kronecker delta embeds in degree 4 | `Finbin.embedsInDegree_kronecker` | `Finbin.quartic_d` ([Finbin/QuarticDelta.lean](Finbin/QuarticDelta.lean)) |
| No low-degree embedding | for every `d`, some binary function embeds in no degree `d` | `Finbin.arbitrary_degree_obstruction` | `Finbin.thm_invp` ([Finbin/Obstruction/Quartic.lean](Finbin/Obstruction/Quartic.lean)) |

The third result is witnessed by the inversion indicator `Finbin.invIndicator p` on
`ZMod p`: for every prime `p` it embeds in no polynomial of total degree `p - 1`
(`Finbin.not_embedsInDegree_invIndicator`), and the obstruction holds over **any** commutative
ring. The supporting determinant/nilpotency lemmas live in
[Finbin/Obstruction/](Finbin/Obstruction/).

The article (statements, proofs, and dependency graph) is the blueprint in
[blueprint/src/content.tex](blueprint/src/content.tex).

## Building

Lean library and executable (the Mathlib build cache is pinned via `lake-manifest.json`):

```sh
lake exe cache get   # fetch the Mathlib build cache (first time only)
lake build           # build the Finbin library and the `finbin` executable
```

The toolchain is pinned in `lean-toolchain` (Lean `v4.30.0`, Mathlib `v4.30.0`). There are
no `sorry`s.

Blueprint (article PDF + web with dependency graph), requires
[`leanblueprint`](https://github.com/PatrickMassot/leanblueprint):

```sh
leanblueprint pdf    # blueprint/print.pdf
leanblueprint web    # blueprint/web/
```

To check that every `\lean{}` reference resolves to an existing declaration:

```sh
lake exe checkdecls blueprint/lean_decls
```

## License

Released under the Apache License 2.0; see [LICENSE](LICENSE).
