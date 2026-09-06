/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/

import Mathlib

/-!
# Find lemmas that state the same thing under different typeclass hypotheses

Elaborating this file writes a TSV file with one row per Mathlib theorem, keyed by a canonical
form of its *statement* with all typeclass information erased. Theorems sharing a key state the
same thing modulo their hypotheses, and are therefore candidates for being collapsed into a
single lemma over a weaker class — the refactor carried out in
[#41457](https://github.com/leanprover-community/mathlib4/pull/41457), which replaced five
copies of `mul_eq_one` (for `CommMonoid`, `LeftCancelMonoid`, `RightCancelMonoid`,
`CancelMonoid` and `Ordinal`) by one lemma over `IsDedekindFiniteMonoid`.

The key is computed by erasing every instance subterm and proof term, dropping the
instance-implicit binders, and uniformising universe levels and binder names. Two keys are
emitted per theorem:

* `keyB` also keeps carrier types, so it matches lemmas that differ only in their hypotheses;
* `keyC` additionally erases carrier types, so it matches a generic lemma against a copy stated
  for one concrete type. In practice `keyC` mostly rediscovers the deliberate `Set`/`Finset`
  parallel API, so prefer `keyB`.

Structure projections, `@[deprecated]` declarations, auto-generated equation lemmas and
tactic-internal lemmas are filtered out; without that the output is swamped by them.

The statements are read from the ambient environment, so the file must be run with the full
`Mathlib` import elaborated:

  lake env lean scripts/find_duplicate_statements.lean

It must be run from the repository root, or `lake` picks the default toolchain and fails to find
`Mathlib`. Expect a few minutes and a large output file (~300MB); the keys are verbose.

The output path is taken from the `DEDUP_OUT` environment variable
(default `dedup_statements.tsv`). Columns are

  name, module, hypothesis classes, proof head symbol, hash keyB, hash keyC, keyB

Group the rows with `scripts/group_duplicate_statements.py`, then feed the resulting groups to
`scripts/find_common_generalization.lean`.
-/

open Lean Meta

/-- Rename all binders so that alpha-equivalent expressions print identically. -/
partial def stripNames : Expr → Expr
  | .forallE _ t b bi => .forallE `x (stripNames t) (stripNames b) bi
  | .lam _ t b bi     => .lam `x (stripNames t) (stripNames b) bi
  | .letE _ t v b nd  => .letE `x (stripNames t) (stripNames v) (stripNames b) nd
  | .app f a          => .app (stripNames f) (stripNames a)
  | .mdata _ e        => stripNames e
  | .proj s i e       => .proj s i (stripNames e)
  | e                 => e

/-- Erase instance subterms and proof terms; if `types` is true, also erase carrier types. -/
def eraseInsts (types : Bool) (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun e => do
    match e with
    | .bvar .. | .sort .. | .mvar .. | .lit .. => return .continue
    | _ =>
      try
        let t ← inferType e
        if (← isClass? t).isSome then return .done (mkConst `_I)
        if ← Meta.isProof e then return .done (mkConst `_P)
        if types && t.isSort && !t.isProp then return .done (mkConst `_T)
      catch _ => pure ()
      return .continue)

/-- Drop instance-implicit binders that the (already erased) body no longer mentions. -/
partial def dropInstBinders : Expr → Expr
  | .forallE n t b bi =>
    let b := dropInstBinders b
    if bi == .instImplicit && !b.hasLooseBVar 0 then b.lowerLooseBVars 1 1
    else .forallE n t b bi
  | e => e

/-- Collapse all universe parameters to a single one, so that `Type u` and `Type v` match. -/
def uniformLevels (e : Expr) (ps : List Name) : Expr :=
  e.instantiateLevelParams ps (ps.map fun _ => Level.param `u)

/-- Is `n` a structure field (including inherited ones)? Those are auto-generated, and without
this filter the output is dominated by them (`CommMonoid.mul_comm`, `Semiring.zero_mul`, …). -/
def isFieldLike (env : Environment) (n : Name) : Bool :=
  let p := n.getPrefix
  match n.components.getLast? with
  | some c => isStructure env p && (getStructureFieldsFlattened env p).contains c
  | none => false

/-- Auto-generated declarations that are never interesting here. -/
def badName (n : Name) : Bool :=
  n.isInternal ||
  (n.components.any fun c =>
    let s := c.toString
    s.startsWith "proof_" || s.startsWith "match_" ||
    s == "eq_def" || s == "injEq" || s == "noConfusion" || s == "noConfusionType" ||
    s == "sizeOf_spec" || s == "brecOn" || s == "below" || s == "ndrec" || s == "rec" ||
    s == "casesOn" || s == "recOn" || s == "toCtorIdx" || s == "ofNat_toCtorIdx" ||
    s == "congr_simp" || s == "sizeOf" ||
    (s.startsWith "eq_" && (s.drop 3).all Char.isDigit && s.length > 3))

/-- Head constant of a proof term. Used to recognise `alias`es and one-line forwarders, which
would otherwise show up as duplicates of the lemma they forward to. -/
def fwdHead (v : Expr) : Option Name :=
  let rec go : Expr → Option Name
    | .lam _ _ b _ => go b
    | .mdata _ e => go e
    | e => match e.getAppFn with
           | .const n _ => some n
           | _ => none
  go v

def run (out : System.FilePath) : MetaM Unit := do
  let env ← getEnv
  let mut rows : Array String := #[]
  let mut scanned := 0
  for (name, ci) in env.constants.toList do
    match ci with
    | .thmInfo ti =>
      if badName name then continue
      if isFieldLike env name then continue
      if Lean.Linter.isDeprecated env name then continue
      let some mod := env.getModuleFor? name | continue
      unless (`Mathlib).isPrefixOf mod do continue
      if (`Mathlib.Deprecated).isPrefixOf mod then continue
      if (`Mathlib.Tactic).isPrefixOf mod then continue
      if ti.type.approxDepth > 200 then continue
      scanned := scanned + 1
      try
        let ty := uniformLevels ti.type ti.levelParams
        let classes ← forallTelescopeReducing ty fun xs _ => do
          let mut cs : Array String := #[]
          for x in xs do
            let d ← x.fvarId!.getDecl
            if d.binderInfo == .instImplicit then
              if let some c := d.type.getAppFn.constName? then
                cs := cs.push c.toString
          return cs
        let key (types : Bool) : MetaM String := do
          return toString (stripNames (dropInstBinders (← withReducible (eraseInsts types ty))))
        let keyB ← key false
        let keyC ← key true
        if keyB.length < 40 then continue
        let fwd := match fwdHead ti.value with | some f => f.toString | none => ""
        rows := rows.push <| String.intercalate "\t"
          [toString name, toString mod, String.intercalate "," classes.toList, fwd,
            toString (hash keyB), toString (hash keyC), keyB]
      catch _ => pure ()
    | _ => pure ()
  IO.println s!"scanned {scanned} theorems, emitted {rows.size} rows"
  IO.FS.writeFile out (String.intercalate "\n" rows.toList)
  IO.println s!"wrote {out}"

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
#eval show CoreM Unit from do
  let out := (← IO.getEnv "DEDUP_OUT").getD "dedup_statements.tsv"
  (run out).run'
