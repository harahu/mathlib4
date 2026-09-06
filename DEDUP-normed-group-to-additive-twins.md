# Dedup candidate: 84 `to_additive` twins in `Analysis/Normed/Group` that are the same theorem

**Model to imitate:** [#41457](https://github.com/leanprover-community/mathlib4/pull/41457)
— "deduplicate lemmas by generalizing to `IsDedekindFiniteMonoid`".

**Size:** largest of the three candidates, and the only one that requires inventing a new
class. Discuss on Zulip before writing code.

## The finding

`Mathlib/Analysis/Normed/Group/*` contains 84 lemma pairs where the multiplicative and the
`to_additive`-generated additive version have **literally the same statement**, because the
statement never mentions the group operation — only `‖·‖`, `dist`, and the topology.

Canonical example (`Mathlib/Analysis/Normed/Group/Basic.lean:125-128`):

```lean
@[to_additive (attr := simp) norm_nonneg]
theorem norm_nonneg' (a : E) : 0 ≤ ‖a‖ := by
  rw [← dist_one_right]
  exact dist_nonneg
```

`norm_nonneg' : 0 ≤ ‖a‖` for `[SeminormedGroup E]` and `norm_nonneg : 0 ≤ ‖a‖` for
`[SeminormedAddGroup E]` differ only in which `Norm E` instance is projected out. Same for
`abs_norm'`/`abs_norm` (`:133-134`), `continuous_norm'`/`continuous_norm`
(`Continuity.lean:127-128`), and 81 others.

## Why both classes are actually the same thing here

`Mathlib/Analysis/Normed/Group/Defs.lean`:

```lean
class SeminormedAddGroup (E : Type*) extends Norm E, AddGroup E, PseudoMetricSpace E where   -- :183
  dist_eq : ∀ x y, dist x y = ‖-x + y‖

class SeminormedGroup (E : Type*) extends Norm E, Group E, PseudoMetricSpace E where          -- :194
  dist := fun x y => ‖x⁻¹ * y‖
  dist_eq : ∀ x y, dist x y = ‖x⁻¹ * y‖
```

Everything the 84 pairs use is downstream of a single consequence of that axiom —
`dist_one_right (a : E) : dist a 1 = ‖a‖` (`Basic.lean:54`) — i.e. *the norm is the distance
to a distinguished base point*. The group structure plays no other role.

## Proposed generalization

A mixin over `[Norm E] [PseudoMetricSpace E]`, roughly:

```lean
/-- A norm on a pseudometric space that measures distance from a base point. -/
class IsNormDistToBasePoint (E : Type*) [Norm E] [PseudoMetricSpace E] where
  basePoint : E
  dist_basePoint (x : E) : dist x basePoint = ‖x‖
```

with instances from `SeminormedGroup` (base point `1`) and `SeminormedAddGroup` (base point
`0`), after which each of the 84 pairs collapses to one lemma. Name and exact shape are open
— alternatives worth weighing:

- a `Prop`-only mixin `∀ x, 0 ≤ ‖x‖` plus a separate `LipschitzWith 1 (norm : E → ℝ)`
  mixin, which covers most of the list without introducing data (`basePoint`);
- reusing/extending the existing `ContinuousENorm` / `ESeminormedAddMonoid` hierarchy
  (`Defs.lean:108-181`) rather than adding a parallel one.

The `basePoint`-carrying version is data, not a `Prop`, which is a real downside for
instance search and diamonds. **Sound out the design on Zulip first** — a class introduced
purely for deduplication is exactly the kind of thing maintainers will want to weigh in on.

## Scoping suggestion

The list falls into natural, separable blocks. `Real.lean` (3 pairs) or `Constructions.lean`
(9 pairs) would make a good pilot PR before attempting `Basic.lean`.

## The 84 pairs

### `Mathlib/Analysis/Normed/Group/Basic.lean` (26)

```
IndiscreteTopology.nnnorm_eq_zero / '
IndiscreteTopology.of_forall_nnnorm_eq_zero / '
IndiscreteTopology.of_forall_norm_eq_zero / '
NontrivialTopology.of_exists_nnnorm_ne_zero / '
NontrivialTopology.of_exists_norm_ne_zero / '
abs_norm / '
coe_comp_nnnorm / '
coe_nnnorm / '
dist_le_norm_add_norm / '
enorm_eq_iff_norm_eq / enorm'_eq_iff_norm_eq
enorm_le_iff_norm_le / enorm'_le_iff_norm_le
exists_nnnorm_ne_zero / '
exists_norm_ne_zero / '
indiscreteTopology_iff_forall_nnnorm_eq_zero / '
indiscreteTopology_iff_forall_norm_eq_zero / '
nontrivialTopology_iff_exists_nnnorm_ne_zero / '
nontrivialTopology_iff_exists_norm_ne_zero / '
norm_le_norm_add_const_of_dist_le / '
norm_le_of_mem_closedBall / '
norm_lt_of_mem_ball / '
norm_nonneg / '
norm_toNNReal / '
ofReal_norm / '
toReal_coe_nnnorm / '
toReal_enorm / '
zero_lt_one_add_norm_sq / '
```

### `Mathlib/Analysis/Normed/Group/Uniform.lean` (17)

```
AddMonoidHomClass.antilipschitz_of_bound      / MonoidHomClass.antilipschitz_of_bound
AddMonoidHomClass.continuous_of_bound         / MonoidHomClass.continuous_of_bound
AddMonoidHomClass.isometry_iff_norm           / MonoidHomClass.isometry_iff_norm
AddMonoidHomClass.isometry_of_norm            / MonoidHomClass.isometry_of_norm
AddMonoidHomClass.lipschitz_of_bound          / MonoidHomClass.lipschitz_of_bound
AddMonoidHomClass.lipschitz_of_bound_nnnorm   / MonoidHomClass.lipschitz_of_bound_nnnorm
AddMonoidHomClass.uniformContinuous_of_bound  / MonoidHomClass.uniformContinuous_of_bound
ZeroHomClass.bound_of_antilipschitz           / OneHomClass.bound_of_antilipschitz
CauchySeq.norm_bddAbove                       / CauchySeq.mul_norm_bddAbove
SeparationQuotient.nnnorm_mk / '
SeparationQuotient.norm_mk / '
antilipschitzWith_iff_exists_mul_le_norm / '
enorm_map / '
lipschitzWith_one_nnnorm / '
lipschitzWith_one_norm / '
uniformContinuous_nnnorm / '
uniformContinuous_norm / '
```

### `Mathlib/Analysis/Normed/Group/Continuity.lean` (16)

```
Continuous.nnnorm / '            Continuous.norm / '
ContinuousAt.nnnorm / '          ContinuousAt.norm / '
ContinuousOn.nnnorm / '          ContinuousOn.norm / '
ContinuousWithinAt.nnnorm / '    ContinuousWithinAt.norm / '
Filter.Tendsto.nnnorm / '        Filter.Tendsto.norm / '
Inseparable.nnnorm_eq_nnnorm / ' Inseparable.norm_eq_norm / '
continuous_nnnorm / '            continuous_norm / '
eventually_ne_of_tendsto_norm_atTop / '
tendsto_norm / '
```

### `Mathlib/Analysis/Normed/Group/Bounded.lean` (13)

```
Bornology.IsBounded.exists_norm_le / '
Bornology.IsBounded.exists_pos_norm_le / '
Bornology.IsBounded.exists_pos_norm_lt / '
Filter.HasBasis.cobounded_of_norm / '
Filter.hasBasis_cobounded_norm / '
IsCompact.exists_bound_of_continuousOn / '
comap_norm_atTop / '
eventually_cobounded_le_norm / '
isBounded_iff_forall_norm_le / '
tendsto_norm_atTop_iff_cobounded / '
tendsto_norm_cobounded_atTop / '
tendsto_norm_cocompact_atTop / '
tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding / '
```

### `Mathlib/Analysis/Normed/Group/Constructions.lean` (9)

```
Function.Surjective.pi_norm_comp / '
IsGreatest.pi_norm / '
Prod.nnnorm_def / '
Prod.nnnorm_mk / '
pi_nnnorm_const / '
pi_nnnorm_const_le / '
pi_norm_comp_le / '
pi_norm_const / '
pi_norm_const_le / '
```

### `Mathlib/Analysis/Normed/Group/Real.lean` (3)

```
enorm_norm / '
nnnorm_norm / '
norm_norm / '
```

## Risks / things to check

- **New class needs buy-in.** Introducing a class solely to deduplicate is a design
  decision, not a refactor. Zulip first.
- **`basePoint` is data.** A data-carrying class creates diamond risk in a part of the
  library that is already diamond-sensitive. Prefer a `Prop` formulation if one suffices for
  most of the list.
- **Interaction with `to_additive`.** Once a lemma is stated against the mixin there is no
  additive twin to generate; the additive names must survive as `@[deprecated] alias`es (or
  become the primary names) so downstream `simp only [...]` calls keep working.
- **This is the tail of an existing pattern.** 102 such identical-statement twin groups
  exist library-wide; 84 are in `Analysis/Normed/Group`. The remaining 18 are scattered
  (`Topology/Algebra/Group/Pointwise`, `Topology/Algebra/IsUniformGroup/*`,
  `GroupTheory/GroupAction/Basic`, `Algebra/Torsor/Defs`, `GroupTheory/Index`,
  `MeasureTheory/Group/*`, …) and are probably not worth chasing.

## Verification

```
lake build Mathlib.Analysis.Normed.Group.Defs Mathlib.Analysis.Normed.Group.Basic
lake build   # required: the normed group API is very widely used downstream
```
