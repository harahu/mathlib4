# Dedup candidates: one verified redundancy, three look-alike pairs, two leads

**Model to imitate:** [#41457](https://github.com/leanprover-community/mathlib4/pull/41457).

**Size:** one small certain fix (§1), then a survey of pairs that share a statement but whose
hypotheses turned out **not** to nest, so they are not deletions (§2), then two further
redundancies found later that nobody has looked at yet (§3). Every claim was checked rather
than inferred from the class names.

---

## §1. `IsSimpleModule.jacobson_eq_bot` is redundant — verified

`Mathlib/RingTheory/Jacobson/Semiprimary.lean`, lines 26 and 29 — three lines apart:

```lean
theorem IsSimpleModule.jacobson_eq_bot [IsSimpleModule R M] : Module.jacobson R M = ⊥ := …
theorem IsSemisimpleModule.jacobson_eq_bot [IsSemisimpleModule R M] : Module.jacobson R M = ⊥ := …
```

Both under `[Ring R] [AddCommGroup M] [Module R M]`, identical statements. `IsSimpleModule R M →
IsSemisimpleModule R M` is an instance, so the first is strictly subsumed. Both checked:

```lean
example (R M : Type) [Ring R] [AddCommGroup M] [Module R M] [IsSimpleModule R M] :
    IsSemisimpleModule R M := inferInstance                                          -- ✅

example (R M : Type) [Ring R] [AddCommGroup M] [Module R M] [IsSimpleModule R M] :
    Module.jacobson R M = ⊥ := IsSemisimpleModule.jacobson_eq_bot R M                -- ✅
```

Independently reproduced by `scripts/find_common_generalization.lean`, which reports
`IsSimpleModule.jacobson_eq_bot<=IsSemisimpleModule.jacobson_eq_bot`.

**Proposed change:** delete `IsSimpleModule.jacobson_eq_bot`, or make it
`IsSemisimpleModule.jacobson_eq_bot R M`, and add a deprecated alias. Check first whether it is
kept deliberately for discoverability — if so, a one-line comment saying so is the right fix
instead.

Note `IsSemisimpleModule.jacobson_eq_bot` takes `R` and `M` explicitly.

---

## §2. Pairs that share a statement but whose hypotheses do not nest

Each of these came out of the duplicate-statement scan and looks like a strict specialization at
a glance. It isn't. Recording them so nobody re-derives the same dead end — but each is still a
candidate for a *common generalization* in the #41457 sense, which is the open question.

`scripts/find_common_generalization.lean` agrees: its strict-subsumption pass reports **no**
subsumption for any of the three pairs below, in either direction.

### `Ideal.IsMaximal.*` vs `Ideal.IsPrime.*`

| | hypotheses | location |
|---|---|---|
| `Ideal.IsMaximal.mul_mem_pow` | `[CommSemiring R] [I.IsMaximal]` | `Mathlib/RingTheory/Ideal/Operations.lean:1257` |
| `Ideal.IsMaximal.mem_pow_mul` | `[CommSemiring R] [I.IsMaximal]` | `Mathlib/RingTheory/Ideal/Operations.lean:1268` |
| `Ideal.IsPrime.mul_mem_pow` | `[CommRing R] [IsDedekindDomain R] [I.IsPrime]` | `Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean:792` |
| `Ideal.IsPrime.mem_pow_mul` | `[CommRing R] [IsDedekindDomain R] [I.IsPrime]` | `Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean:800` |

`IsMaximal → IsPrime` holds (verified: `example (R) [CommSemiring R] (I : Ideal R) [I.IsMaximal]
: I.IsPrime := inferInstance`), but the `IsPrime` versions additionally demand `CommRing` and
`IsDedekindDomain`, which the `IsMaximal` versions do not have. **Neither subsumes the other.**
The open question is whether a single statement over a weaker ring hypothesis covers both; that
is a genuine piece of commutative algebra, not a refactor.

### `IsNoetherian` vs `OrzechProperty`

| | hypotheses | location |
|---|---|---|
| `IsNoetherian.injective_of_surjective_of_submodule` | `[Ring R] [AddCommGroup M] [Module R M] [IsNoetherian R M]` | `Mathlib/RingTheory/Noetherian/Orzech.lean:52` |
| `OrzechProperty.injective_of_surjective_of_submodule` | `[Semiring R] [OrzechProperty R] [AddCommMonoid M] [Module R M] [Module.Finite R M]` | `Mathlib/RingTheory/OrzechProperty.lean` |

**This one is deliberate and already documented.** `Mathlib/RingTheory/Noetherian/Orzech.lean:80-88`
carries the comment "Any Noetherian ring satisfies Orzech property. See also
`IsNoetherian.injective_of_surjective_of_submodule` …" and the `IsNoetherianRing.orzechProperty`
instance is built *from* the Noetherian lemma. Removing either would be circular. **Leave alone.**

### `Module.rank_self` / `finrank_self` vs `CommSemiring.rank_self` / `finrank_self`

| | hypotheses | location |
|---|---|---|
| `Module.rank_self` | `[Semiring R] [StrongRankCondition R]` | `Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean:470` |
| `Module.finrank_self` | `[Semiring R] [StrongRankCondition R]` | `Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean:476` |
| `CommSemiring.rank_self` | `[CommSemiring R]` | `Mathlib/LinearAlgebra/Dimension/Basic.lean:257` |
| `CommSemiring.finrank_self` | `[CommSemiring R]` | `Mathlib/LinearAlgebra/Dimension/Finrank.lean:108` |

Same statements (`Module.rank R R = 1`, `finrank R R = 1`) under incomparable hypotheses:
commutativity on one side, `StrongRankCondition` on the other. Not a deletion. Worth checking
whether the `CommSemiring` versions are reachable from the `Module` ones for nontrivial
commutative semirings, and if so whether one namespace should forward to the other — but this is
a naming question more than a duplication one.

---

## §3. Related pairs found later, not analysed here

The strict-subsumption pass turned up two more field/ring-theory redundancies of the same shape.
They are not covered above and deserve their own look:

- `IsGalois.fixedField_fixingSubgroup`, `IsGalois.mem_bot_iff_fixed`,
  `IsGalois.mem_range_algebraMap_iff_fixed` (`Mathlib/FieldTheory/Galois/Basic.lean`, all with
  `[IsGalois K L] [FiniteDimensional K L]`) are each subsumed by the `InfiniteGalois.*` lemma of
  the same name (`Mathlib/FieldTheory/Galois/Infinite.lean`, `[IsGalois K L]` only).
- `IsIntegrallyClosed.algebraMap_eq_of_integral` (`[IsFractionRing] [IsIntegrallyClosed]`) is
  subsumed by `IsIntegrallyClosedIn.algebraMap_eq_of_integral` (`[IsIntegrallyClosedIn]`), both in
  `Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean`.

Note the import direction in the Galois case: the general lemma lives in `Galois/Infinite.lean`,
*downstream* of the special one in `Galois/Basic.lean`. So this is a move, not a forward — the
same shape as the `Filter.iInter_mem'` precedent, and possibly deliberate.

## Verification

```
lake build Mathlib.RingTheory.Jacobson.Semiprimary
lake build
```
