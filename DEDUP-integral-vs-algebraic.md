# Dedup candidate: `Algebra.IsIntegral` vs `Algebra.IsAlgebraic` — five duplicated `_iff` lemmas

**Model to imitate:** [#41457](https://github.com/leanprover-community/mathlib4/pull/41457).

**Size:** five lemma pairs across two files. **Not a free win** — read the "obstruction" section
before starting; the merge costs a `Nontrivial R` hypothesis and that is a judgement call for
someone who knows this corner of the library.

## The finding

Five lemmas are stated twice with identical statements, once assuming `[Algebra.IsIntegral R S]`
and once assuming `[Algebra.IsAlgebraic R S]`, in otherwise identical ambient contexts.

| Statement | `IsIntegral` version | `IsAlgebraic` version |
|---|---|---|
| `IsAlgebraic R a ↔ IsAlgebraic S a` | `Integral.lean:361` | `Integral.lean:369` |
| `Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic S A` | `Integral.lean:365` | `Integral.lean:373` |
| `Transcendental R a ↔ Transcendental S a` | `Integral.lean:491` | `Integral.lean:495` |
| `AlgebraicIndependent R x ↔ AlgebraicIndependent S x` | `AlgebraicClosure.lean:87` | `AlgebraicClosure.lean:96` |
| `IsTranscendenceBasis R x ↔ IsTranscendenceBasis S x` | `AlgebraicClosure.lean:92` | `AlgebraicClosure.lean:100` |

Files: `Mathlib/RingTheory/Algebraic/Integral.lean` and
`Mathlib/RingTheory/AlgebraicIndependent/AlgebraicClosure.lean`.

Shared context in both files:

```
[CommRing R] [CommRing S] [Ring A] [Algebra R S] [Algebra R A] [Algebra S A]
[IsScalarTower R S A] [NoZeroDivisors S] [FaithfulSMul R S]
```

with the sole difference being `[Algebra.IsIntegral R S]` vs `[Algebra.IsAlgebraic R S]`.

The proofs differ only in which transfer lemma they call — `.extendScalars_of_isIntegral` and
`.restrictScalars_of_isIntegral` versus `.extendScalars` and `.restrictScalars`. In every pair,
the last two lines of each proof are otherwise the same.

## Why this looks collapsible

`Mathlib/RingTheory/Algebraic/Integral.lean:56` already provides

```lean
instance Algebra.IsIntegral.isAlgebraic [Nontrivial R] [Algebra.IsIntegral R A] :
    Algebra.IsAlgebraic R A
```

so `IsIntegral` is the stronger hypothesis, and the `IsAlgebraic` lemma should subsume its twin.

## The obstruction (verified)

That instance needs `[Nontrivial R]`, and **`Nontrivial R` is not available in the ambient
context of these lemmas**. Both of the following were checked:

```lean
-- FAILS: cannot synthesize Algebra.IsAlgebraic R S
example (R S A : Type) [CommRing R] [CommRing S] [Ring A] [Algebra R S] [Algebra R A]
    [Algebra S A] [IsScalarTower R S A] [NoZeroDivisors S] [Algebra.IsIntegral R S]
    [FaithfulSMul R S] : Algebra.IsAlgebraic R S := inferInstance

-- FAILS: Nontrivial R is not free from FaithfulSMul R S plus Nontrivial S
example (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [FaithfulSMul R S] [Nontrivial S] :
    Nontrivial R := inferInstance
```

This is corroborated by `scripts/find_common_generalization.lean`: its strict-subsumption pass,
which reports a lemma as redundant whenever another member's hypotheses are all available in its
context, finds **no subsumption in either direction** for any of the five pairs. The obstruction
is real, not an artefact of how the examples above were written.

**With `[Nontrivial R]` supplied, the merge works.** These do elaborate:

```lean
example (R S A : Type) [CommRing R] [CommRing S] [Ring A] [Algebra R S] [Algebra R A]
    [Algebra S A] [IsScalarTower R S A] [NoZeroDivisors S] [Algebra.IsIntegral R S]
    [FaithfulSMul R S] [Nontrivial R] {a : A} : IsAlgebraic R a ↔ IsAlgebraic S a :=
  Algebra.IsAlgebraic.isAlgebraic_iff R S

example (R S A : Type) [CommRing R] [CommRing S] [Ring A] [Algebra R S] [Algebra R A]
    [Algebra S A] [IsScalarTower R S A] [NoZeroDivisors S] [Algebra.IsIntegral R S]
    [FaithfulSMul R S] [Nontrivial R] : Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic S A :=
  Algebra.IsAlgebraic.isAlgebraic_iff_top R S

example (R S A : Type) [CommRing R] [CommRing S] [Ring A] [Algebra R S] [Algebra R A]
    [Algebra S A] [IsScalarTower R S A] [NoZeroDivisors S] [Algebra.IsIntegral R S]
    [FaithfulSMul R S] [Nontrivial R] {a : A} : Transcendental R a ↔ Transcendental S a :=
  Algebra.IsAlgebraic.transcendental_iff R S
```

(The two `AlgebraicClosure.lean` pairs have the same shape and were not separately checked.)

## The decision to make

Three options, in rough order of preference:

1. **Add `[Nontrivial R]` to the `IsIntegral` versions and make them one-line forwarders** (or
   deprecate them). Cheapest, but strictly weakens five lemmas. Check the downstream call sites
   first: if every caller has `Nontrivial R` anyway, this is free in practice.
2. **Leave them alone and document why.** If the `IsIntegral` versions are deliberately stated
   without `Nontrivial R`, add a comment saying so — right now nothing in the source explains the
   duplication, which is why it reads as an oversight.
3. **Investigate whether the `IsIntegral` versions are actually true without `Nontrivial R`.**
   Worth a moment's thought: for trivial `R`, `IsAlgebraic R a` is false (no nonzero polynomial
   exists) while `IsAlgebraic S a` may hold, and `FaithfulSMul R S` is vacuous when `R` is
   trivial. If the statements are in fact only provable via some instance in scope that smuggles
   in nontriviality, that is worth knowing regardless of the deduplication.

Option 3 should be settled before 1 or 2.

## Risks / things to check

- `Algebra.IsAlgebraic.isAlgebraic_iff` and `Algebra.IsIntegral.isAlgebraic_iff` are both
  `protected`, so downstream code writes the full name; deprecation aliases will be needed.
- `IsIntegral.isTranscendenceBasis_iff` (`AlgebraicClosure.lean:92`) is proved *via*
  `IsIntegral.algebraicIndependent_iff`, so the two must be handled together.
- These lemmas take `R` and `S` as explicit arguments (`Algebra.IsAlgebraic.isAlgebraic_iff R S`),
  so any forwarder must preserve the argument order.

## Verification

```
lake build Mathlib.RingTheory.Algebraic.Integral \
           Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
lake build
```
