# Dedup candidate: `InnerProductSpace.Core` vs `InnerProductSpace` (23 duplicated lemmas)

**Model to imitate:** [#41457](https://github.com/leanprover-community/mathlib4/pull/41457)
— "deduplicate lemmas by generalizing to `IsDedekindFiniteMonoid`".

**Why this one is closest in spirit:** unlike the other two candidates, the generalization
target and the bridging instance **already exist in Mathlib**. Nothing new needs to be
invented; the copies just were never collapsed.

## The finding

23 lemmas are proved twice with identical statements: once for
`[PreInnerProductSpace.Core 𝕜 F]` in `Mathlib/Analysis/InnerProductSpace/Defs.lean`, once for
`[InnerProductSpace 𝕜 E]` in `Mathlib/Analysis/InnerProductSpace/Basic.lean`.

| lemma | `Defs.lean` (Core) | `Basic.lean` (class) |
|---|---|---|
| `inner_conj_symm` | 227 | 58 |
| `inner_self_nonneg` | 230 | 202 |
| `inner_self_im` | 233 | 71 |
| `inner_add_left` | 237 | 74 |
| `inner_add_right` | 240 | 77 |
| `inner_re_symm` | 247 | 81 |
| `inner_im_symm` | 249 | 83 |
| `inner_zero_left` | 258 | 189 |
| `inner_zero_right` | 262 | 196 |
| `inner_self_ofReal_re` | 276 | 208 |
| `norm_inner_symm` | 279 | 227 |
| `inner_neg_left` | 281 | 230 |
| `inner_neg_right` | 285 | 235 |
| `inner_sub_left` | 288 | 242 |
| `inner_sub_right` | 291 | 245 |
| `inner_mul_symm_re_eq_norm` | 294 | 248 |
| `inner_add_add_self` | 299 | 253 |
| `inner_sub_sub_self` | 303 | 264 |
| `inner_self_eq_norm_mul_norm` | 384 | 387 |
| `norm_eq_sqrt_re_inner` | 382 | 379 |
| `norm_inner_le_norm` | 390 | 455 |
| `inner_self_eq_zero` | 457 | 316 |
| `inner_self_ne_zero` | 465 | 319 |

(`inner_self_eq_zero` / `inner_self_ne_zero` sit under the stronger
`[InnerProductSpace.Core 𝕜 F]`, which adds the `definite` field; the class-side versions
correspondingly need `NormedAddCommGroup` rather than `SeminormedAddCommGroup`.)

## The bridge that already exists

`Mathlib/Analysis/InnerProductSpace/Defs.lean`:

- `:150` — `attribute [class] PreInnerProductSpace.Core`
- `:162` — `attribute [class] InnerProductSpace.Core`
- `:176-180` — `@[instance_reducible] def PreInnerProductSpace.toCore [SeminormedAddCommGroup E] [c : InnerProductSpace 𝕜 E] : PreInnerProductSpace.Core 𝕜 E`

with the doc comment, verbatim:

> Define `PreInnerProductSpace.Core` from `InnerProductSpace`. **Defined to reuse lemmas about
> `PreInnerProductSpace.Core` for `PreInnerProductSpace`s.** Note that the `Seminorm` instance
> provided by `PreInnerProductSpace.Core.norm` is propositionally but not definitionally equal
> to the original norm.

So the intent is already recorded in the source. The reuse simply did not happen — most
likely because `toCore` is a `def`, not an `instance`, so typeclass synthesis never finds it.

The two structures line up field for field (`Defs.lean:109-118` vs `:139-148`): both carry
`conj_inner_symm`, `add_left`, `smul_left`; `Core` additionally has `re_inner_nonneg`, which
`toCore` derives from `InnerProductSpace.norm_sq_eq_re_inner` via `sq_nonneg`.

## Proposed approach

Two options; investigate which the maintainers prefer.

1. **Make `toCore` an instance** (possibly low priority) and delete the `Basic.lean`
   duplicates, replacing them with `@[deprecated] alias` or with re-exports under the
   expected names. Risk: diamond on the norm (see below).
2. **Factor out a genuine `Prop` mixin** — e.g. `IsInnerProduct 𝕜 F` over
   `[Inner 𝕜 F] [AddCommGroup F] [Module 𝕜 F]` carrying the three algebraic axioms — and
   have both `PreInnerProductSpace.Core` and `InnerProductSpace` provide it. This avoids the
   norm entirely for the algebraic lemmas and is the closer analogue of #41457. Likely the
   cleaner answer.

## The one real hazard

`PreInnerProductSpace.Core.norm` (`Defs.lean:377`, `@[instance_reducible]`) defines a norm
*from* the core, and it is **propositionally but not definitionally** equal to the ambient
norm of a `SeminormedAddCommGroup`. Making `toCore` an unconditional instance therefore
risks a non-defeq norm diamond.

This splits the 23 lemmas:

- **20 are safe** — purely algebraic, no `‖·‖` on the space. All of `Defs.lean:227-354`,
  i.e. everything *before* the norm instance at `:377`. Note `norm_inner_symm` and
  `inner_mul_symm_re_eq_norm` mention `‖⟪x, y⟫‖`, which is the norm on `𝕜` (`RCLike`),
  not on the space — these are safe.
- **3 need care** — they mention `‖x‖` for `x` in the space, and are stated *after* the
  norm instance: `norm_eq_sqrt_re_inner` (`:382`), `inner_self_eq_norm_mul_norm` (`:384`),
  `norm_inner_le_norm` (`:390`). Handle these separately, or leave them duplicated.

A first PR covering only the 20 algebraic lemmas is a reasonable, low-risk scope.

## Verification

```
lake build Mathlib.Analysis.InnerProductSpace.Defs Mathlib.Analysis.InnerProductSpace.Basic
lake build   # downstream analysis is large; expect to need the full build
```

Watch for `simp` regressions: many of these are `@[simp]` on both sides, and unifying them
changes which instance path `simp` takes.
