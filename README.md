# FinBin

This repo is a formal verification of results in:
- https://arxiv.org/abs/2606.09045
- https://roman3017.github.io/FinBin

One can show that every unary function `X → X` on finite set can be embedded into a linear function in a possibly larger but finite commutative ring. We show this does not generalize even to binary functions. In particular for every `d` there is a binary function `X^2 → X` such that it does not embed to any polynomial of degree `d`.

The unary case has been posted and formalized here:
- https://arxiv.org/abs/2510.20167
- https://roman3017.github.io/FinLin
- https://github.com/roman3017/FinLin

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
leanblueprint all
leanblueprint serve
```

To check that every `\lean{}` reference resolves to an existing declaration:

```sh
lake exe checkdecls blueprint/lean_decls
```

## License

Released under the Apache License 2.0; see [LICENSE](LICENSE).
