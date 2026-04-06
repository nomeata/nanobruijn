# nanobruijn

**nanobruijn** -- an experimental Lean 4 type checker exploring pure de Bruijn
index representation with shift-homomorphic caching.

## Provenance

Forked from [nanoda_lib](https://github.com/ammkrn/nanoda_lib) by ammkrn
(at commit [`68d5ca9`](https://github.com/ammkrn/nanoda_lib/commit/68d5ca9db226849b41a6fff59d796ff19d0a8840)),
an independent Rust implementation of the Lean 4 kernel. The original uses
locally-nameless binding representation (free variables as names, bound variables
as de Bruijn indices), matching the official Lean kernel.

nanobruijn replaces the binding representation and caching strategy while keeping
the rest of the type-checking logic largely intact.

## Purpose

This is a research vehicle for evaluating specific design decisions in Lean 4
kernel implementation, benchmarked against the original nanoda on real-world
proof artifacts (Mathlib). It is part of the
[lean-kernel-arena](https://github.com/leanprover/lean-kernel-arena)
project.

**This is not intended for production use.**

## Design decisions under evaluation

### Pure de Bruijn indices (replacing locally-nameless)

The standard Lean kernel and nanoda use locally-nameless representation: bound
variables are de Bruijn indices, but when entering a binder (e.g. in
`whnf(forall)` or `infer(lambda)`), the bound variable is replaced by a fresh
free variable (a "local"). This requires a full substitution on binder entry.

nanobruijn instead keeps everything as de Bruijn indices throughout. Entering a
binder is free (no substitution), but looking up a bound variable in the
environment requires adjusting (shifting) the retrieved value to account for the
difference in binding depth.

### Shift nodes (lazy shifting)

Rather than eagerly shifting every subexpression, nanobruijn wraps retrieved values
in a `Shift(n, expr)` node that records the pending adjustment. Shifts compose:
`Shift(a, Shift(b, e))` becomes `Shift(a+b, e)`. Shifts are pushed inward
lazily during whnf normalization.

### Shift-homomorphic caching

The whnf cache uses keys that are invariant under shifting: if `whnf(e) = v`,
then `whnf(Shift(n, e)) = Shift(n, v)`. This means a single cache entry serves
all shifted variants of an expression, giving cross-depth cache hits that the
locally-nameless approach cannot achieve.

## Current status

nanobruijn successfully type-checks all of Mathlib with 0 errors and 0 timeouts.
It is approximately 1.7x slower than the original nanoda. See `PLAN.md` for
detailed benchmark data and analysis of the performance gap.

## Building and running

```
cargo build --release
./target/release/nanobruijn path/to/config.json
```

The config JSON file specifies the export file path and checker options.
Run with `--help` for details.

## Authorship

All code modifications from the original nanoda_lib were written by Claude
(Anthropic), directed by Joachim Breitner. The original nanoda_lib was written
by ammkrn.

## License

Apache-2.0 (inherited from nanoda_lib)
