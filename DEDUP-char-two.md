# Dedup candidate: three parallel "characteristic two" APIs

**Model to imitate:** [#41457](https://github.com/leanprover-community/mathlib4/pull/41457)
— "deduplicate lemmas by generalizing to `IsDedekindFiniteMonoid`". That PR found the
weakest property the proofs actually used, stated each lemma once against it, and
deprecated the sibling copies. `-86/+30` lines and shorter `simp only` calls downstream.

**Size:** smallest and most self-contained of the three candidates. Recommended starting point.

## The finding

`a - b = a + b` is proved three times, in three unrelated namespaces, each surrounded by
its own small parallel API. All three rest on exactly one fact: `∀ x, x + x = 0`.

| Namespace | Hypotheses | File |
|---|---|---|
| `BooleanRing` | `[BooleanRing α]` | `Mathlib/Algebra/Ring/BooleanRing.lean` |
| `CharTwo` | `[Ring R] [CharP R 2]` | `Mathlib/Algebra/CharP/Two.lean` |
| `ZModModule` | `[AddCommGroup G] [Module (ZMod 2) G]` | `Mathlib/Data/ZMod/Basic.lean` |

### The overlapping lemmas

```
BooleanRing.add_self        : a + a = 0                Mathlib/Algebra/Ring/BooleanRing.lean:67
BooleanRing.neg_eq          : -a = a                   Mathlib/Algebra/Ring/BooleanRing.lean:76
BooleanRing.add_eq_zero'    : a + b = 0 ↔ a = b        Mathlib/Algebra/Ring/BooleanRing.lean:83
BooleanRing.sub_eq_add      : a - b = a + b            Mathlib/Algebra/Ring/BooleanRing.lean:98

CharTwo.add_self_eq_zero    : x + x = 0                Mathlib/Algebra/CharP/Two.lean:81
CharTwo.two_nsmul           : 2 • x = 0                Mathlib/Algebra/CharP/Two.lean:84
CharTwo.add_cancel_left     : a + (a + b) = b          Mathlib/Algebra/CharP/Two.lean:87
CharTwo.add_cancel_right    : a + b + b = a            Mathlib/Algebra/CharP/Two.lean:91
CharTwo.neg_eq              : -x = x                   Mathlib/Algebra/CharP/Two.lean:101
CharTwo.neg_eq'             : Neg.neg = (id : R → R)   Mathlib/Algebra/CharP/Two.lean:104
CharTwo.sub_eq_add          : x - y = x + y            Mathlib/Algebra/CharP/Two.lean:108
CharTwo.add_eq_iff_eq_add   : a + b = c ↔ a = c + b    Mathlib/Algebra/CharP/Two.lean:110
CharTwo.eq_add_iff_add_eq   : a = b + c ↔ a + c = b    Mathlib/Algebra/CharP/Two.lean:113
CharTwo.two_zsmul           : (2 : ℤ) • x = 0          Mathlib/Algebra/CharP/Two.lean:117
CharTwo.add_eq_zero         : a + b = 0 ↔ a = b        Mathlib/Algebra/CharP/Two.lean:120

ZModModule.add_self         : x + x = 0                Mathlib/Data/ZMod/Basic.lean:1254
ZModModule.neg_eq_self      : -x = x                   Mathlib/Data/ZMod/Basic.lean:1257
ZModModule.sub_eq_add       : x - y = x + y            Mathlib/Data/ZMod/Basic.lean:1259
ZModModule.add_add_add_cancel : (x + y) + (y + z) = x + z  Mathlib/Data/ZMod/Basic.lean:1261
```

None of these lemmas mention multiplication, `CharP`, `ZMod`, or idempotence in their
statements — only `+`, `-`, `0`, `•`. The `Ring`/`Module`/`BooleanRing` hypotheses are used
only to *establish* `x + x = 0`, never in the statements.

## Proposed generalization

Introduce a `Prop` mixin asserting exponent divides two, and make the three existing
structures instances of it.

```lean
/-- A monoid in which every element is its own inverse. -/
@[to_additive /-- An additive monoid in which every element is its own negation. -/]
class IsSelfInvMonoid (M : Type*) [Monoid M] : Prop where
  mul_self (a : M) : a * a = 1
```

Naming is the main open design question — plausible alternatives:
`IsExponentTwoMonoid`, `Monoid.IsExponentTwo`, `IsSelfInvMonoid` / `IsSelfNegAddMonoid`.
Take it to Zulip (`#mathlib4` → naming) before writing the PR.

Then:
- state `add_self`, `neg_eq`, `sub_eq_add`, `add_eq_zero`, `add_cancel_left/right`,
  `add_eq_iff_eq_add`, `eq_add_iff_add_eq`, `two_nsmul`, `two_zsmul`,
  `add_add_add_cancel` once against the mixin (the `neg_*`/`sub_*` ones need
  `AddGroup`/`SubtractionMonoid` in addition);
- add instances `BooleanRing α → …`, `[Ring R] [CharP R 2] → …`,
  `[AddCommGroup G] [Module (ZMod 2) G] → …`;
- `@[deprecated] alias` the three sets of copies.

### Note on prior art

`Mathlib/GroupTheory/Exponent.lean:615-698` already has an `ExponentTwo` section
(`inv_eq_self_of_exponent_two`, `mul_comm_of_exponent_two`,
`commMonoidOfExponentTwo`, …), but it is **hypothesis-based** (`Monoid.exponent G = 2`),
not a typeclass, so it participates in neither instance search nor `simp`. It is also far
too high in the import hierarchy for `Mathlib/Algebra/CharP/Two.lean` (which carries
`assert_not_exists Algebra LinearMap Field`).

`Mathlib/Algebra/Group/SelfInv.lean` has `IsSelfInv (a : α) : Prop := a⁻¹ = a` as a
*predicate on elements* — the natural home for a "every element" class version, and already
imported by `Mathlib/Algebra/CharP/Two.lean`. Check the import graph before choosing a home;
`BooleanRing.lean` and `ZMod/Basic.lean` must both be able to reach it.

## Risks / things to check

- **Import placement.** The mixin must live low enough for all three call sites.
  `Mathlib/Algebra/Group/SelfInv.lean` is the leading candidate.
- **`scoped simp`.** `BooleanRing.add_self`, `BooleanRing.neg_eq`, `BooleanRing.sub_eq_add`,
  `CharTwo.two_eq_zero`, `CharTwo.add_self_eq_zero`, `CharTwo.sub_eq_add` and others are
  `@[scoped simp]`. Generalized versions become globally applicable; decide whether they
  should be plain `@[simp]` (probably yes for the ones keyed on the new class, since the
  class is a `Prop` mixin and won't fire spuriously) and check for simp-set regressions.
- **`to_additive`.** The multiplicative side of this class is "exponent divides 2" for
  groups; check the `to_additive` name mapping produces sane additive names.
- **Blast radius is small.** Qualified downstream uses:
  `CharTwo.` 4, `BooleanRing.` 10, `ZModModule.` 9 (`grep -rn` over `Mathlib`).
  Only one `open BooleanRing` (`Mathlib/Algebra/Ring/BooleanRing.lean:238`).

## Verification

```
lake build Mathlib.Algebra.Ring.BooleanRing Mathlib.Algebra.CharP.Two Mathlib.Data.ZMod.Basic
lake build   # full, for simp-set fallout
```
