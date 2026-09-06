# Dedup leads: assorted single findings

**Model to imitate:** [#41457](https://github.com/leanprover-community/mathlib4/pull/41457).

A grab-bag of individually small findings that do not justify a briefing each. §1 is the most
interesting item and the closest to #41457 in shape. §2 is verified redundancies. §3 is an open
question. §4 records known false positives so nobody chases them twice.

---

## §1. `Set.star_inv` / `Set.star_inv'` generalize to `DivisionMonoid` — needs one lemma first

`Mathlib/Algebra/Star/Pointwise.lean:119` and the line below it:

```lean
protected theorem Set.star_inv  [Group α]          [StarMul α] (s : Set α) : s⁻¹⋆ = s⋆⁻¹
protected theorem Set.star_inv' [GroupWithZero α]  [StarMul α] (s : Set α) : s⁻¹⋆ = s⋆⁻¹
```

Identical statements over `Group` and `GroupWithZero`. The strongest class common to both is
**`DivisionMonoid`**, which is exactly the generalization wanted — and note that no `Prop`-valued
mixin could have expressed it, so this only turned up once the search was extended to structure
classes.

**But the proof does not transfer as-is.** The existing proof is

```lean
  ext; simp only [mem_star, mem_inv, star_inv]
```

and over `[DivisionMonoid α] [StarMul α]` it leaves the goal

```
⊢ (star x)⁻¹ ∈ s ↔ star x⁻¹ ∈ s
```

i.e. it needs the *element-level* `star_inv : star a⁻¹ = (star a)⁻¹`, which mathlib has for
`Group` (`star_inv`) and for `GroupWithZero`/`DivisionRing` (`star_inv'`) but apparently not for
`DivisionMonoid`.

So the work is:

1. Prove `star_inv` at element level for `[DivisionMonoid α] [StarMul α]`. In a `DivisionMonoid`
   inverses are unique and `star` is a multiplicative anti-automorphism, so this should follow
   from `inv_eq_of_mul_eq_one_right` applied to `star a * star a⁻¹ = star (a⁻¹ * a) = star 1 = 1`.
2. Deduplicate the element-level `star_inv` / `star_inv'` pair itself, which is the same shape.
3. Then collapse `Set.star_inv` / `Set.star_inv'`.

That ordering — find the weakest class, prove the missing base lemma there, then let the
downstream copies collapse — is precisely the #41457 shape.

---

## §2. Verified single redundancies

| Subsumed | Subsumes | Location |
|---|---|---|
| `algebraMap_smul` `[Module R M] [Module A M] [IsScalarTower R A M]` | `IsScalarTower.algebraMap_smul` `[SMul R M] [IsScalarTower R A M]` | `Mathlib/Algebra/Algebra/Basic.lean:409` vs `Mathlib/Algebra/Algebra/Tower.lean:93` |
| `FiniteField.cast_card_eq_zero` `[Field K] [Fintype K]` | `Nat.cast_card_eq_zero` `[AddGroupWithOne K] [Fintype K]` | `Mathlib/FieldTheory/Finite/Basic.lean:274` vs `Mathlib/GroupTheory/OrderOfElement.lean` |
| `BialgHom.coe_copy`, `BialgHom.copy_eq` | `CoalgHom.coe_copy`, `CoalgHom.copy_eq` | `Mathlib/RingTheory/Bialgebra/Hom.lean:233,236` vs `Mathlib/RingTheory/Coalgebra/Hom.lean:191,194` |
| `MeasureTheory.IsStoppingTime.measurableSet_le'` `[LinearOrder ι]` | `MeasureTheory.IsStoppingTime.measurableSet_le` `[Preorder ι]` | `Mathlib/Probability/Process/Stopping.lean:551` |

The first two were checked by hand and both elaborate:

```lean
example (R A M : Type) [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]
    [Module R M] [Module A M] [IsScalarTower R A M] (r : R) (m : M) :
    (algebraMap R A) r • m = r • m := IsScalarTower.algebraMap_smul A r m   -- ✅

example (K : Type) [Field K] [Fintype K] : (Fintype.card K : K) = 0 :=
  Nat.cast_card_eq_zero K                                                  -- ✅
```

The `BialgHom` and `IsStoppingTime` rows come from the tool and were **not** hand-checked.
Verify them the same way before acting.

Note on `BialgHom`: the two `copy` lemmas are stated for the *same* type `A →ₗc[R] B` in both
files, so this may be a straightforward re-export rather than a mathematical duplication. Check
whether `Bialgebra/Hom.lean` is simply restating `CoalgHom` lemmas for discoverability.

---

## §3. Open question: the `rnDeriv` family

`Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean` has five primed/unprimed pairs with
identical statements and **incomparable** hypotheses:

```
rnDeriv_add              / rnDeriv_add'
rnDeriv_smul_left        / rnDeriv_smul_left'
rnDeriv_smul_left_of_ne_top  / rnDeriv_smul_left_of_ne_top'
rnDeriv_smul_right       / rnDeriv_smul_right'
rnDeriv_smul_right_of_ne_top / rnDeriv_smul_right_of_ne_top'
```

Unprimed assume `[IsFiniteMeasure …] [HaveLebesgueDecomposition …]`; primed assume
`[SigmaFinite …] [SigmaFinite …]`. Neither implies the other, so this is not a deletion — it is
the genuine #41457 question: *is there a single hypothesis covering both?* Five lemmas in one
file makes it worth someone's time who knows measure theory. Nobody has looked.

---

## §4. Known false positives — do not chase

The duplicate-statement scan matches statements after erasing typeclass information, so two
lemmas can collide while meaning different things. Confirmed non-findings:

- **`EuclideanDomain.div_self` / `div_zero` / `div_one` vs the generic ones.** Same shape, but
  `EuclideanDomain` division is Euclidean quotient, not field division. Unrelated.
- **`CFC.posPart_*` / `negPart_*` vs `posPart_*` / `negPart_*`.** The `CFC` versions are about
  the continuous functional calculus; only the statement shape coincides.
- **`ProbabilityTheory.bayesRisk_of_isEmpty''` and `minimaxRisk_of_isEmpty''`
  (`Mathlib/Probability/Decision/Risk/Defs.lean:121`).** The subsumption tool reports these as
  redundant, but it is wrong: the unprimed lemma assumes `[IsEmpty 𝓧]` while the `''` version
  assumes `[IsEmpty Θ] [Nonempty 𝓨]`, and `IsEmpty Θ` does not give `IsEmpty 𝓧`. The tool's
  carrier assignment is not constrained to agree with the roles the carriers play in the
  statement, so multi-carrier statements can still yield a spurious match. Treat any subsumption
  involving three or more type variables as a lead, not a certainty.

---

## Verification

```
lake build Mathlib.Algebra.Star.Pointwise Mathlib.Algebra.Algebra.Basic \
           Mathlib.FieldTheory.Finite.Basic
lake build
```
