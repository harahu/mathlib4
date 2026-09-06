# Dedup candidate: six redundant lemmas in the `Sub*` class hierarchy

**Model to imitate:** [#41457](https://github.com/leanprover-community/mathlib4/pull/41457).

**Size:** small, and the easiest of the set — this is *not* the #41457 pattern of finding a new
weaker class. In each pair the general lemma already exists and already applies; the special
case is dead weight. Every claim below was checked by elaborating the specialized statement
against the general lemma.

## The finding

Six lemmas/instances are stated for a sub-object class that is strictly below another one that
already carries the same result.

| Redundant declaration | Subsumed by | Verified |
|---|---|---|
| `SubgroupClass.coe_pow` (`Mathlib/Algebra/Group/Subgroup/Defs.lean:243`) | `SubmonoidClass.coe_pow` (`Mathlib/Algebra/Group/Submonoid/Defs.lean:375`) | ✅ |
| `AddSubgroupClass.coe_nsmul` (the `to_additive` twin of the above) | `AddSubmonoidClass.coe_nsmul` | ✅ |
| `Subring.range_fst` (`Mathlib/Algebra/Ring/Subring/Basic.lean:929`) | `Subsemiring.range_fst` (`Mathlib/Algebra/Ring/Subsemiring/Basic.lean:846`) | ✅ |
| `Subring.range_snd` (`Mathlib/Algebra/Ring/Subring/Basic.lean:932`) | `Subsemiring.range_snd` (`Mathlib/Algebra/Ring/Subsemiring/Basic.lean:850`) | ✅ |
| `SubsemiringClass.noZeroDivisors` (`Mathlib/Algebra/Ring/Subsemiring/Defs.lean:90`) | `NonUnitalSubsemiringClass.noZeroDivisors` (`Mathlib/RingTheory/NonUnitalSubsemiring/Defs.lean:88`) | ✅ |
| `Subring.toIsOrderedRing` (`Mathlib/Algebra/Ring/Subring/Order.lean:31`) | `SubsemiringClass.toIsOrderedRing` (`Mathlib/Algebra/Ring/Subsemiring/Order.lean:24`) | ✅ |
| `Subring.toIsStrictOrderedRing` (`Mathlib/Algebra/Ring/Subring/Order.lean:35`) | `SubsemiringClass.toIsStrictOrderedRing` (`Mathlib/Algebra/Ring/Subsemiring/Order.lean:29`) | ✅ |

`Subring.range_fst`/`range_snd` are the starkest case: identical statement
(`(RingHom.fst R S).rangeS = ⊤`) **and** identical proof
(`(fst R S).rangeS_top_of_surjective <| Prod.fst_surjective`), differing only in
`[NonAssocRing]` vs `[NonAssocSemiring]`.

## Verification already done

All six of these elaborate:

```lean
example (G A : Type) [Group G] [SetLike A G] [SubgroupClass A G] {S : A} (x : S) (n : ℕ) :
    ((x ^ n : S) : G) = (x : G) ^ n := SubmonoidClass.coe_pow x n
example (R S : Type) [NonAssocRing R] [NonAssocRing S] : (RingHom.fst R S).rangeS = ⊤ :=
  Subsemiring.range_fst
example (R S : Type) [NonAssocRing R] [NonAssocRing S] : (RingHom.snd R S).rangeS = ⊤ :=
  Subsemiring.range_snd
example (R A : Type) [NonAssocSemiring R] [SetLike A R] [SubsemiringClass A R] [NoZeroDivisors R]
    (s : A) : NoZeroDivisors s := NonUnitalSubsemiringClass.noZeroDivisors s
example (R A : Type) [Ring R] [PartialOrder R] [SetLike A R] [SubringClass A R] [IsOrderedRing R]
    (s : A) : IsOrderedRing s := SubsemiringClass.toIsOrderedRing s
example (R A : Type) [Ring R] [PartialOrder R] [SetLike A R] [SubringClass A R]
    [IsStrictOrderedRing R] (s : A) : IsStrictOrderedRing s :=
  SubsemiringClass.toIsStrictOrderedRing s
```

The underlying class implications are all instances already:
`SubgroupClass A G → SubmonoidClass A G`, `SubsemiringClass A R → NonUnitalSubsemiringClass A R`,
and `[Ring R] [SubringClass A R] → SubsemiringClass A R`.

All seven were subsequently reproduced independently by
`scripts/find_common_generalization.lean`, whose strict-subsumption pass reports each as
`<redundant><=<general>`. (`AddSubgroupClass.coe_nsmul` came from that run; the hand pass had
missed it.)

## Proposed change

Delete each redundant declaration, or replace its body by a call to the general one, and
`@[deprecated] alias` the name.

Note the file `Mathlib/Algebra/Ring/Subsemiring/Order.lean` already models the intended pattern:
`Subsemiring.toIsOrderedRing` (`:41`) is defined as `SubsemiringClass.toIsOrderedRing _` rather
than reproved. `Subring.toIsOrderedRing` should follow suit — or be removed outright, since with
`SubringClass A R → SubsemiringClass A R` the general instance already fires.

## Risks / things to check

- **Instance priority and defeq.** The three instances (`noZeroDivisors`, `toIsOrderedRing`,
  `toIsStrictOrderedRing`) are found by typeclass synthesis, so removing one changes which
  instance path is taken. Confirm the resulting instance is defeq to the old one where anything
  depends on it, and watch for priority regressions.
- **`coe_pow` is `@[simp, norm_cast]`** on both sides, and `@[to_additive]`. Removing the
  `SubgroupClass` copy removes `SubgroupClass.coe_nsmul` too; keep deprecated aliases for both.
- **Do not touch `Subgroup.coe_pow`** (`Mathlib/Algebra/Group/Subgroup/Defs.lean:541`). It is a
  different declaration in the `Subgroup` namespace, stated for the concrete `Subgroup G` rather
  than for a `SubgroupClass`, and is not part of this cluster.
- **Naming.** `SubsemiringClass.noZeroDivisors` and `NonUnitalSubsemiringClass.noZeroDivisors`
  live in different namespaces, so deletion changes the name downstream code must use. Check
  whether the `Subsemiring.noZeroDivisors` instance at
  `Mathlib/Algebra/Ring/Subsemiring/Defs.lean:310` also becomes redundant.
- **A subsumed lemma is not always a deletable one.** Elsewhere in the library the same pattern
  is deliberate: `Filter.iInter_mem'` (`Mathlib/Order/Filter/Basic.lean:126`) is subsumed by
  `Filter.iInter_mem` but exists, per its own doc comment, to assume `Subsingleton` instead of
  `Finite` so that `Order/Filter/Basic.lean` need not import the `Finite` machinery. Before
  deleting any of the six above, check the import direction between the two files — if the
  general lemma lives *downstream* of the special one, the fix is to move it, not to forward.
  (For this cluster the `Sub*Class` files are all low in the hierarchy, so this is unlikely to
  bite, but it is worth one `grep` per pair.)

## Verification

```
lake build Mathlib.Algebra.Group.Subgroup.Defs Mathlib.Algebra.Ring.Subring.Basic \
           Mathlib.Algebra.Ring.Subring.Order Mathlib.Algebra.Ring.Subsemiring.Defs
lake build   # instances are globally visible; a full build is required
```
