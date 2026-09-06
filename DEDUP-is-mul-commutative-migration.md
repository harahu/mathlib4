# Dedup candidate: the `IsMulCommutative` / `IsAddCommutative` migration

**Model to imitate:** [#41457](https://github.com/leanprover-community/mathlib4/pull/41457).

**Size:** four verified redundancies, but one of them is `mul_comm`. Highest-impact and
highest-care item in this set. Take it to Zulip before writing code.

## The finding

Mathlib has introduced `Prop` mixins for commutativity:

```lean
class IsAddCommutative (M : Type*) [Add M] : Prop   -- Mathlib/Algebra/Group/Semigroup.lean:169
class IsMulCommutative (M : Type*) [Mul M] : Prop   -- Mathlib/Algebra/Group/Semigroup.lean:174
```

They are already used in 82 files, so this is a live migration rather than an experiment. It has
left behind pairs where the *bundled* version of a lemma is strictly subsumed by the *mixin*
version — including the single most-used commutativity lemma in the library.

| Subsumed | Subsumes | Location |
|---|---|---|
| `mul_comm` `[CommMagma G]` | `mul_comm'` `[Mul G] [IsMulCommutative G]` | `Mathlib/Algebra/Group/Semigroup.lean:228` |
| `add_comm` `[AddCommMagma G]` | `add_comm'` `[Add G] [IsAddCommutative G]` | same file |
| `CommGroup.center_eq_top` `[CommGroup G]` | `Subgroup.center_eq_top` `[Group G] [IsMulCommutative G]` | `Mathlib/GroupTheory/Subgroup/Center.lean:89` vs `:101` |
| `AddCommGroup.center_eq_top` | `AddSubgroup.center_eq_top` | same file |

The bridge is `instance CommMagma.to_isCommutative : IsMulCommutative G`
(`Mathlib/Algebra/Group/Semigroup.lean:231`).

## Verified

```lean
example (α : Type) [CommMagma α] (a b : α) : a * b = b * a := mul_comm' a b        -- ✅
example (G : Type) [CommGroup G] : Subgroup.center G = ⊤ := Subgroup.center_eq_top  -- ✅
example (G : Type) [AddCommGroup G] : AddSubgroup.center G = ⊤ :=
  AddSubgroup.center_eq_top                                                        -- ✅
```

`scripts/find_common_generalization.lean` reports all four as strict subsumptions.

## The decision — note the direction

This is **not** a deprecate-the-primed-name case. Here the redundant lemma is the *canonical,
unprimed, universally used* one:

- `mul_comm` appears in **1336 files** under `Mathlib/`.
- `mul_comm'` is the general form but carries the awkward name.

So the sensible refactor is the reverse of the usual one: **restate `mul_comm` itself over
`[Mul G] [IsMulCommutative G]` and retire `mul_comm'`**, keeping the good name on the general
lemma. Because `CommMagma.to_isCommutative` is an instance, every existing call site continues to
elaborate unchanged — but that claim needs testing at scale, not assuming, since `mul_comm` is
used everywhere including in `simp` sets, `to_additive` output and tactic internals.

Suggested order of work:

1. Do `center_eq_top` first (four call sites, self-contained). It validates the pattern cheaply.
2. Then propose the `mul_comm` / `add_comm` restatement on Zulip. Expect discussion about
   whether the mixin should become the primary spelling library-wide, which is a broader
   question than this PR.

## Risks / things to check

- **Blast radius.** `mul_comm` is `@[to_additive]`-paired, used by `ring`, `abel`, `group` and
  `simp` normalisation. A change in its statement changes unification behaviour at thousands of
  sites even if every one still compiles. Measure the build-time delta.
- **Instance depth.** Replacing `[CommMagma G]` by `[Mul G] [IsMulCommutative G]` adds one
  instance-search step at every use. For a lemma this hot, that is a real performance question —
  check against `scripts/bench`.
- **Direction may be deliberate.** It is possible mathlib intends `mul_comm` to keep the bundled
  hypothesis for exactly the performance reason above, with `mul_comm'` as the escape hatch. If
  so the fix is a comment at `Semigroup.lean:228` saying so, not a refactor. Establish this first
  — it decides whether the PR is worth writing at all.
- **`Subgroup.center_eq_top` already exists in the right form**, so that half needs no new
  design, only deprecation of the `CommGroup.*` spelling.

## Verification

```
lake build Mathlib.Algebra.Group.Semigroup Mathlib.GroupTheory.Subgroup.Center
lake build   # essential here; the blast radius is the whole library
```
