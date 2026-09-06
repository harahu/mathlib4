# Dedup candidate: redundant primed lemmas in `Mathlib/Order/`

**Model to imitate:** [#41457](https://github.com/leanprover-community/mathlib4/pull/41457).

**Size:** tiny. Of four claimed redundancies, **one** holds — the copy-paste bug — and three are
false positives (§3). The five look-alikes recorded in §2 as must-keep were all correct.

---

## §1. Act on these

**Verified 2026-09-07. Only one of the four original items survived.** The Boolean-vs-Heyting
trio was checked at the statement level only; all three fail on *location*. See §3.

### `CompleteSublattice.subtype_apply` is a copy-paste bug — CONFIRMED, fixed

`Mathlib/Order/CompleteSublattice.lean:124` was character-for-character identical to
`Mathlib/Order/Sublattice.lean:119`, taking `L : Sublattice α` rather than
`L : CompleteSublattice α` — unlike `coe_subtype` (`:123`) and `subtype_injective` (`:125`)
around it. So it did not state what its name said, and the intended lemma was missing.

Nothing in `Mathlib/`, `MathlibTest/`, `Archive/` or `Counterexamples/` referenced it, so it was
**retyped** rather than deleted: that fixes the name and supplies the missing lemma in one go, and
needs no deprecation. Left un-`simp` to match `Sublattice.subtype_apply`. Verified by building
`Mathlib.Order.CompleteSublattice` and all 5 modules downstream of it (2007 jobs, clean).

---

## §2. Do NOT touch these

The same scan flags five more in this area. All are deliberate.

### `Filter.iInter_mem'` — import hierarchy

`Mathlib/Order/Filter/Basic.lean:126` is subsumed by `Filter.iInter_mem`
(`Mathlib/Order/Filter/Finite.lean:48`), since `Subsingleton β → Finite β`. But its own doc
comment says: *"Weaker version of `Filter.iInter_mem` that assumes `Subsingleton β` rather than
`Finite β`."* It exists so that `Order/Filter/Basic.lean` need not import the `Finite`
machinery — the general lemma lives **downstream**. Leave it.

This is the canonical example of "subsumed but not deletable", and worth remembering when
reading any subsumption report.

### `Decidable.le_iff_eq_or_lt`, `Decidable.le_iff_eq_or_lt'`, `Decidable.eq_or_lt_of_le`, `Decidable.eq_or_lt_of_le'`

`Mathlib/Order/Basic.lean:234, 256` and their `to_dual` twins. Each is subsumed by the unprimed
lemma a few lines below (`:238`, `:260`), which needs no `[DecidableLE α]`. But `Order/Basic.lean:232`
carries the marker `-- See Note [decidable namespace]`: these exist so that constructive
developments can use a computable proof. Leave them.

---

## §3. Refuted — the Boolean-vs-Heyting trio must stay

The class-resolution check in the original §1 was correct: for Boolean `α β`,
`BoundedLatticeHomClass.toBiheytingHomClass` (`Mathlib/Order/Heyting/Hom.lean:179`) does
supply the Heyting and Coheyting hom classes, and `BooleanAlgebra.toBiheytingAlgebra`
(`Mathlib/Order/BooleanAlgebra/Basic.lean:448`) supplies both algebra instances. That was never
the binding constraint.

### The `map_*'` lemmas — the general lemma is downstream

(The original table listed `map_compl'` and `map_symmDiff'`; `map_sdiff'` is equally subsumed and
was missed.)

`Mathlib/Order/Heyting/Hom.lean` **imports** `Mathlib/Order/Hom/BoundedLattice.lean`, so
`map_compl`/`map_sdiff`/`map_symmDiff` — and `HeytingHomClass` itself — do not exist at the primed
lemmas' location. Confirmed by `#eval (← getEnv).contains` in a file importing only
`Mathlib.Order.Hom.BoundedLattice`: all three, plus `HeytingHomClass`, return `false`.

Both use sites fail the same check: `Mathlib/Order/BooleanSubalgebra.lean` (`map_compl'`, twice)
and `Mathlib/Algebra/Ring/BooleanRing.lean` (`map_symmDiff'`) sit *sideways* — neither imports
`Heyting.Hom` nor is imported by it — and `map_compl`/`map_symmDiff` are absent in both.

Adding `import Mathlib.Order.Heyting.Hom` to those two files would cost only 1 new module each,
so an import-based removal is *technically* available. It was rejected: `Order.Hom.BoundedLattice`
is imported by 6821 modules against `Order.Heyting.Hom`'s 349, so moving the only Boolean
`BoundedLatticeHomClass` compl/sdiff/symmDiff lemmas behind the Heyting import removes them from
the far larger cohort, to save nine lines. The existing split is coherent, not accidental: the
unprimed lemmas are `@[simp]`, the primed ones are the upstream fallback.

**Done instead:** a note at `Mathlib/Order/Hom/BoundedLattice.lean:162` recording the import
reason, so the trio is not re-flagged.

### `inf_compl_eq_bot'` — in-file bootstrap circularity

This one is not an import problem: `Order.BooleanAlgebra.Basic` does import `Order.Heyting.Basic`,
and `inf_compl_eq_bot` is in scope. It is an *ordering* problem inside the file.
`inf_compl_eq_bot'` (`:417`) is proved from the raw `BooleanAlgebra.inf_compl_le_bot` field and is
used at `:428` to prove `isCompl_compl` and at `:445` in
`BooleanAlgebra.toGeneralizedBooleanAlgebra` — both of which feed
`BooleanAlgebra.toBiheytingAlgebra` at `:448`, the instance that would be needed to apply
`inf_compl_eq_bot`. Substituting it and building gives:

```
error: Mathlib/Order/BooleanAlgebra/Basic.lean:417:42: Type mismatch
  inf_compl_eq_bot has type ?m ⊓ @compl ?α HeytingAlgebra.toCompl ?m = ⊥
  but is expected to have type x ⊓ @compl α inst✝.toCompl x = ⊥
```

No `HeytingAlgebra α` yet, so even the `Compl` structures do not unify. The prime exists to dodge
the name clash with the already-imported general lemma while bootstrapping it.

**Done instead:** a docstring at `:417` recording the bootstrap reason.

---

## Verification

```
lake build Mathlib.Order.Hom.BoundedLattice Mathlib.Order.BooleanAlgebra.Basic \
           Mathlib.Order.CompleteSublattice          # clean, 764 jobs
lake exe lint-style <the three files>                # clean
```

Only `CompleteSublattice.subtype_apply` changed semantically; its 5 downstream modules were built
clean (2007 jobs). The other two edits are comments.
