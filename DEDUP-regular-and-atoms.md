# Dedup candidates: `IsRegular` primed lemmas, and `Order/Atoms` Boolean-algebra copies

**Model to imitate:** [#41457](https://github.com/leanprover-community/mathlib4/pull/41457).

Two small, independent items. §1 is verified redundant and retires two primed names — do it
first. §2 needs one genuine (if standard) order-theory lemma added before the copies can go.

---

## §1. `IsRegular.of_ne_zero'` and `isRegular_iff_ne_zero'` are redundant — verified

| | hypotheses | location |
|---|---|---|
| `IsRegular.of_ne_zero` | `[MulZeroClass α] [IsCancelMulZero α]` | `Mathlib/Algebra/GroupWithZero/Regular.lean:102` |
| `IsRegular.of_ne_zero'` | `[NonUnitalNonAssocRing α] [NoZeroDivisors α]` | `Mathlib/Algebra/Ring/Regular.lean:35` |
| `isRegular_iff_ne_zero` | `[MulZeroClass α] [IsCancelMulZero α] [Nontrivial α]` | `Mathlib/Algebra/GroupWithZero/Regular.lean:106` |
| `isRegular_iff_ne_zero'` | `[Nontrivial α] [NonUnitalNonAssocRing α] [NoZeroDivisors α]` | `Mathlib/Algebra/Ring/Regular.lean:42` |

Statements are identical: `a ≠ 0 → IsRegular a` and `IsRegular a ↔ a ≠ 0`.

In a ring, `NoZeroDivisors` gives `IsCancelMulZero`, so the primed versions are strictly
subsumed. All three checks pass:

```lean
example (α : Type) [NonUnitalNonAssocRing α] [NoZeroDivisors α] : IsCancelMulZero α :=
  inferInstance                                                                        -- ✅

example (α : Type) [NonUnitalNonAssocRing α] [NoZeroDivisors α] {k : α} (hk : k ≠ 0) :
    IsRegular k := IsRegular.of_ne_zero hk                                             -- ✅

example (α : Type) [NonUnitalNonAssocRing α] [NoZeroDivisors α] [Nontrivial α] {k : α} :
    IsRegular k ↔ k ≠ 0 := isRegular_iff_ne_zero                                       -- ✅
```

Both were independently reproduced by `scripts/find_common_generalization.lean`, which reports
`IsRegular.of_ne_zero'<=IsRegular.of_ne_zero` and
`isRegular_iff_ne_zero'<=isRegular_iff_ne_zero`.

**Proposed change:** replace the bodies of `IsRegular.of_ne_zero'` and `isRegular_iff_ne_zero'`
with the unprimed versions, then `@[deprecated] alias` both. This also removes two entries from
the primed-name lint exceptions if they are listed there — check `scripts/nolints_prime_decls.txt`.

**Call sites to update** (`grep -rn "of_ne_zero'\|isRegular_iff_ne_zero'" Mathlib`), notably
`Mathlib/RingTheory/DedekindDomain/Instances.lean:98`.

**Watch — this is a real pattern, not a hypothetical.** `Mathlib/Algebra/Ring/Regular.lean` may
exist partly to keep `Mathlib/Algebra/GroupWithZero/Regular.lean` out of the import graph for ring
files. Elsewhere in the library exactly this is done deliberately: `Filter.iInter_mem'`
(`Mathlib/Order/Filter/Basic.lean:126`) is subsumed by `Filter.iInter_mem` but its doc comment
says it exists to assume `Subsingleton` rather than `Finite`, so that `Order/Filter/Basic.lean`
need not import the `Finite` machinery. Confirm the import direction is `Ring/Regular.lean` →
`GroupWithZero/Regular.lean` before rewriting the proofs; if it is the other way round, the fix is
to move the lemmas rather than forward them.

---

## §2. `Order/Atoms`: the `BooleanAlgebra` copies duplicate the `IsAtomistic` ones

`Mathlib/Order/Atoms.lean` contains the same two lemmas twice, about 90 lines apart:

| | hypotheses | location |
|---|---|---|
| `BooleanAlgebra.le_iff_atom_le_imp` | `[BooleanAlgebra α] [IsAtomic α]` | `:522` |
| `BooleanAlgebra.eq_iff_atom_le_iff` | `[BooleanAlgebra α] [IsAtomic α]` | `:533` |
| `le_iff_atom_le_imp` | `[PartialOrder α] [OrderBot α] [IsAtomistic α]` | `:614` |
| `eq_iff_atom_le_iff` | `[PartialOrder α] [OrderBot α] [IsAtomistic α]` | `:618` |

Statements are identical:

```lean
a ≤ b ↔ ∀ c, IsAtom c → c ≤ a → c ≤ b
a = b ↔ ∀ c, IsAtom c → (c ≤ a ↔ c ≤ b)
```

The proofs are completely different — the `BooleanAlgebra` version argues via complements
(`x ⊓ yᶜ = ⊥`), the `IsAtomistic` version via `isLUB_atoms_le`.

### The missing link (verified)

An atomic Boolean algebra *is* atomistic — but **mathlib does not know this**. Both fail:

```lean
example (α : Type) [BooleanAlgebra α] [IsAtomic α] : IsAtomistic α := inferInstance          -- ❌
example (α : Type) [CompleteBooleanAlgebra α] [IsAtomic α] : IsAtomistic α := inferInstance  -- ❌
```

`Mathlib/Order/Atoms.lean:593` has `IsAtomistic → IsAtomic`, the converse direction of the
implication, but nothing supplies `IsAtomistic` from `IsAtomic` in the Boolean case.
Consistently with that, `scripts/find_common_generalization.lean` reports **no** strict
subsumption for this pair in either direction — unlike §1, which it flags immediately. The gap is
in the library, not in the analysis.

### Proposed change

1. Add the instance `[BooleanAlgebra α] [IsAtomic α] → IsAtomistic α`. This is a standard result
   and the existing `BooleanAlgebra.le_iff_atom_le_imp` proof at `:522` is most of the work — it
   establishes exactly the separation property that `IsAtomistic` packages.
2. With that instance in place, delete both `BooleanAlgebra.*` copies in favour of the
   general ones, leaving deprecated aliases.

This is the more interesting of the two items: it turns a duplicated proof into a reusable
structural fact, which is precisely the shape of #41457.

### Risks

- Adding an `IsAtomistic` instance for Boolean algebras affects instance search library-wide.
  Give it a thought re: priority, and check for loops against `IsAtomistic → IsAtomic` at `:593`.
- Check whether `IsAtomistic` in mathlib requires completeness in disguise (via `isLUB_atoms`) —
  if the definition needs suprema that a general `BooleanAlgebra` lacks, step 1 may only work for
  `CompleteBooleanAlgebra`, in which case the `BooleanAlgebra` copies must stay. Settle this
  before writing anything else.
- `Mathlib/Order/Atoms.lean:550` uses `BooleanAlgebra.eq_iff_atom_le_iff` inside a
  `CompleteBooleanAlgebra` instance; that call site must keep working.

---

## Verification

```
lake build Mathlib.Algebra.Ring.Regular Mathlib.Algebra.GroupWithZero.Regular Mathlib.Order.Atoms
lake build
```
