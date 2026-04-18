# nanobruijn

**nanobruijn** -- an experimental Lean 4 type checker exploring pure de Bruijn
index representation with shift-homomorphic caching.

## Provenance

Forked from [nanoda_lib](https://github.com/ammkrn/nanoda_lib) by ammkrn
(at commit [`68d5ca9`](https://github.com/ammkrn/nanoda_lib/commit/68d5ca9db226849b41a6fff59d796ff19d0a8840)),
an independent Rust implementation of the Lean 4 kernel. The original uses
locally-nameless binding representation (free variables as names, bound variables
as de Bruijn indices), matching the official Lean kernel.

Upstream nanoda commits reviewed and ported through
[`6d2f037`](https://github.com/ammkrn/nanoda_lib/commit/6d2f03717af89dde5b8906bb957a6a50eeecbb94)
(2026-04-07).

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

### Lazy shifting via pointer+offset pairs (`ExprPtr`)

Rather than eagerly shifting every subexpression, every pointer into the
expression DAG is an `ExprPtr = (CorePtr, u16 shift)` pair. `ExprPtr(p, k)`
denotes the expression at `p` with all free variable indices increased by `k`.
There are no explicit `Shift` DAG nodes; shifts are "carried" in the pointer.
Shifting is O(1) "pointer arithmetic". Shifts compose directly at composition
sites (`e.shift_up(k)`). Closed expressions use a sentinel `shift = u16::MAX`
so `is_closed()` is an O(1) field test.

### Shift-homomorphic caching

Caches are keyed by `CorePtr` (the DAG pointer alone) with the shift handled
separately: if `whnf(e) = v`, then `whnf(e.shift_up(k)) = v.shift_up(k)`.
A single cache entry serves all shifted variants of an expression, giving
cross-depth cache hits that the locally-nameless approach cannot achieve.
Per-depth cache buckets (`bucket = depth - shift`) are used for open
expressions; closed expressions live in a single global bucket.

### Parse-time OSNF (Outermost-Shift Normal Form)

Expressions are normalized at parse time into OSNF: in every compound DAG
node, the minimum shift among open children is 0. Expressions that differ
only by a uniform shift of their free variable indices share the same core
in the DAG, with only the shift amount differing in the outer `ExprPtr`.

A literature search found no established name for this specific normal form,
though it sits at the intersection of several well-studied ideas:

- **Nadathur & Wilson's Suspension Notation** (1990, 1998) — terms carry
  deferred shifts as `[[t, ol, nl, e]]`. Closest ancestor, but no canonical
  form requirement.
  [Paper](https://dl.acm.org/doi/pdf/10.1145/91556.91682)

- **McBride's Co-de-Bruijn / Thinnings** (2018) — each node carries a
  bit-vector ("thinning") indicating which scope variables are used. Achieves
  similar sharing but via a more general mechanism (thinnings can drop
  variables from the middle, not just shift uniformly).
  [arXiv:1807.04085](https://arxiv.org/abs/1807.04085)

- **Gallais's Lazy Weakening** — keeps weakenings (uniform shifts) suspended
  outermost, structurally similar to OSNF, but without canonicalization or
  hash-consing.
  [Blog post](https://gallais.github.io/blog/lazy-lambda.html)

- **Zucker's Thinning Hash Cons** (2024–2025) — hash-consing with thinning
  annotations following McBride, explicitly discussing sharing modulo context
  adjustments.
  [Blog post](https://www.philipzucker.com/thin_hash_cons_codebruijn/)

- **Lambda-sigma calculus** (Abadi, Cardelli, Curien & Levy, 1991) — shift as
  a primitive in explicit substitution calculus, but a rewriting system rather
  than a canonical form for DAG sharing.

See `Theory.lean` for a formalization of OSNF and its uniqueness property.

## Current status

nanobruijn successfully type-checks all of Mathlib (670k declarations) with
0 errors and 0 timeouts. See
[arena results](https://arena.lean-lang.org/) for up-to-date cross-checker
performance comparison, and `PLAN.md` for design history.

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
