/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/

import Mathlib

/-!
# Find a weaker class that a group of sibling lemmas could share

Given groups of theorems that state the same thing under different typeclass hypotheses (as
produced by `scripts/find_duplicate_statements.lean` and
`scripts/group_duplicate_statements.py`), this script proposes, for each group, the classes that
could serve as the single weaker hypothesis they are all stated over.

This is the search that would have found `IsDedekindFiniteMonoid` for
[#41457](https://github.com/leanprover-community/mathlib4/pull/41457): given the four
hypothesis sets that PR collapsed (`CommMonoid`, `LeftCancelMonoid`, `RightCancelMonoid`,
`CancelMonoid`), exactly three of the ~420 candidate classes survive, and
`IsDedekindFiniteMonoid` is one of them. That case is checked on every run as a self-test; see
`selfTest` below.

Two passes run over each group.

**Strict subsumption.** If one member's context already supplies another member's hypotheses,
the second lemma is redundant and can simply be deleted — no new class, no design decision. This
is cheaper and far more certain than the search below, so it is reported first and should be read
first. Building a class application can fail for reasons unrelated to the mathematics, and such a
failure counts as "not subsumed", so this pass errs towards false negatives and never claims a
redundancy that does not hold.

**Common weaker class.** A class `C` is reported for a group when

1. `C α` is synthesizable in **every** member's context, so `C` is implied by each member's
   hypotheses;
2. `C` is *statement-relevant*: the classes `C` is stated over, plus `C`'s own ancestors,
   overlap with the classes the shared statement is written in terms of;
3. `C` is not already a hypothesis of every member, since then there is nothing to gain.

Condition (2) is what makes the output usable. Without it the search returns classes that are
genuinely derivable but have nothing to do with the statement — an order carrier picks up
`R1Space`, `QuasiSober`, `CategoryTheory.Limits.HasStrictInitialObjects` and friends via
instances such as `Preorder.smallCategory` — and these swamp the real hits.

Prop-valued mixins and `Sort`-valued structure classes are reported in separate columns. The
structure classes are cut down to the *maximal* ones: `Mul` is common to everything and says
nothing, whereas `DivisionMonoid` — the strongest class common to a `Group` lemma and a
`GroupWithZero` lemma — is the generalization one actually wants, and no Prop-valued mixin can
express it.

Note what this does **not** establish: that the lemma's *proof* only needs `C`. The search
narrows hundreds of candidates to a handful; confirming one is still a human step, as it was in
#41457. The strict-subsumption pass carries no such caveat.

The declarations are read from the ambient environment, so the file must be run with the full
`Mathlib` import elaborated, from the repository root:

  lake env lean scripts/find_common_generalization.lean

The input path is taken from the `DEDUP_GROUPS` environment variable (default `groups.tsv`; one
tab-separated group of declaration names per line) and the output path from `DEDUP_COMMON_OUT`
(default `dedup_common_classes.tsv`). Output columns are

  members, suggested Prop mixins, suggested structure classes, strict subsumptions

A strict subsumption `A<=B` means B's hypotheses are all available in A's context, so A is
redundant and can be deleted outright -- no new class needed. That is a cheaper and more certain
result than a suggested class, so read the fourth column first.

`#eval` output is buffered until elaboration finishes, so progress cannot be watched live.
-/

open Lean Meta

/-- Build `C α inst…`, synthesizing `C`'s own instance arguments; `none` if that fails.

`mkAppOptM` cannot be used here: it silently drops trailing instance-implicit arguments, so
`IsDedekindFiniteMonoid α` comes back without its `[MulOne α]` argument and every subsequent
`synthInstance?` fails. -/
def mkClassApp (C : Name) (α : Expr) : MetaM (Option Expr) := do
  let ci ← getConstInfo C
  let lvls ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  let cty := ci.type.instantiateLevelParams ci.levelParams lvls
  let (args, bis, _) ← forallMetaTelescope cty
  let mut sawExpl := false
  for h : i in [0:args.size] do
    if bis[i]! != .instImplicit then
      if sawExpl then return none
      unless ← isDefEq args[i] α do return none
      sawExpl := true
  unless sawExpl do return none
  for h : i in [0:args.size] do
    if bis[i]! == .instImplicit then
      let t ← instantiateMVars (← inferType args[i])
      if t.hasExprMVar then return none
      match ← synthInstance? t with
      | some v => unless ← isDefEq args[i] v do return none
      | none => return none
  let e ← instantiateMVars (mkAppN (mkConst C lvls) args)
  if e.hasExprMVar || e.hasLevelMVar then return none
  return some e

/-- Is `C α` inhabited in the current local context? -/
def canSynth (C : Name) (α : Expr) : MetaM Bool := do
  try
    let some ty ← mkClassApp C α | return false
    return (← synthInstance? ty).isSome
  catch _ => return false

/-- Build `C` with its explicit arguments taken, in order, from `sel`. Multi-parameter classes
such as `Module R M` and `IsScalarTower R S A` need this; `mkClassApp` handles only the
one-parameter case. -/
def mkClassAppN (C : Name) (sel : Array Expr) : MetaM (Option Expr) := do
  let ci ← getConstInfo C
  let lvls ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  let cty := ci.type.instantiateLevelParams ci.levelParams lvls
  let (args, bis, _) ← forallMetaTelescope cty
  let mut k := 0
  for h : i in [0:args.size] do
    if bis[i]! != .instImplicit then
      if h : k < sel.size then
        unless ← isDefEq args[i] sel[k] do return none
        k := k + 1
      else return none
  unless k == sel.size do return none
  for h : i in [0:args.size] do
    if bis[i]! == .instImplicit then
      let t ← instantiateMVars (← inferType args[i])
      if t.hasExprMVar then return none
      match ← synthInstance? t with
      | some v => unless ← isDefEq args[i] v do return none
      | none => return none
  let e ← instantiateMVars (mkAppN (mkConst C lvls) args)
  if e.hasExprMVar || e.hasLevelMVar then return none
  return some e

/-- Injective tuples of length `k` drawn from `xs`. Used to try every way of matching a class's
explicit parameters against the carrier types in scope, since the two members of a group need not
list their carriers in the same order. -/
partial def injTuples (xs : Array Expr) (k : Nat) : Array (Array Expr) :=
  if k == 0 then #[#[]]
  else Id.run do
    let mut out := #[]
    for h : i in [0:xs.size] do
      let rest := xs.eraseIdx! i
      for t in injTuples rest (k - 1) do
        out := out.push (#[xs[i]] ++ t)
    return out

/-- Which carriers a hypothesis is applied to, as indices into `carriers`.

`Module R M` in a context whose carriers are `[R, M, N]` gives `#[0, 1]`. Recording the indices
rather than re-searching per hypothesis is what makes the subsumption check use **one** carrier
assignment for the whole hypothesis list: choosing independently per hypothesis lets `Nonempty α`
and `Infinite β` be satisfied by different assignments, which reports subsumptions that do not
hold. -/
def hypIndices (ty : Expr) (carriers : Array Expr) : Array Nat :=
  ty.getAppArgs.filterMap fun a => carriers.findIdx? (· == a)

/-- `n` together with every structure it transitively extends. -/
partial def ancestors (env : Environment) (n : Name) (acc : Std.HashSet Name := {}) :
    Std.HashSet Name :=
  if acc.contains n then acc
  else
    let acc := acc.insert n
    if isStructure env n then
      (getStructureParentInfo env n).foldl (fun a p => ancestors env p.structName a) acc
    else acc

/-- Head names of the classes `C` is itself stated over, closed under `extends`, together with
`C`'s own ancestors. For `IsDedekindFiniteMonoid (M) [MulOne M]` this is `{MulOne, Mul, One}`
(from the instance argument); for a structure class such as `DivisionMonoid`, which takes no
instance arguments and bundles everything through `extends`, it is the ancestor chain
`{DivisionMonoid, DivInvMonoid, Monoid, Mul, One, …}`. Both sources are needed: without the
ancestors, no structure class ever passes the statement-relevance test. -/
def classDeps (C : Name) : MetaM (Std.HashSet Name) := do
  let env ← getEnv
  let ci ← getConstInfo C
  forallTelescopeReducing ci.type fun xs _ => do
    let mut out := ancestors env C
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo == .instImplicit then
        if let some c := d.type.getAppFn.constName? then
          out := out.union (ancestors env c)
    return out

/-- Candidate classes: `class C (α : Type _) [inst…]` with exactly one explicit type argument.
`Prop`-valued explicit arguments (as in `Fact`) are excluded.

Prop-valued (`prop := true`) gives mixins such as `IsDedekindFiniteMonoid`; `Sort`-valued gives
structure classes such as `DivisionMonoid`, which are often the real generalization — the common
generalization of a `Group` lemma and a `GroupWithZero` lemma is `DivisionMonoid`, and no
`Prop`-valued mixin can express that. -/
def candidateClasses (prop : Bool) : MetaM (Array Name) := do
  let env ← getEnv
  let mut out : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    unless isClass env n do continue
    let some mod := env.getModuleFor? n | continue
    unless (`Mathlib).isPrefixOf mod do continue
    if (`Mathlib.Deprecated).isPrefixOf mod then continue
    try
      let ok ← forallTelescopeReducing ci.type fun xs body => do
        if prop then
          unless body.isProp do return false
        else
          unless body.isSort && !body.isProp do return false
        let mut nExpl := 0
        for x in xs do
          let d ← x.fvarId!.getDecl
          if d.binderInfo != .instImplicit then
            nExpl := nExpl + 1
            let t ← whnf (← inferType x)
            unless t.isSort && !t.isProp do return false
        return nExpl == 1
      if ok then out := out.push n
    catch _ => pure ()
  return out

/-- Every class head name occurring in `e` as the type of an instance subterm, closed under
`extends`: "what the statement is written in terms of". -/
def statementClasses (e : Expr) : MetaM (Std.HashSet Name) := do
  let env ← getEnv
  let acc ← IO.mkRef ({} : Std.HashSet Name)
  let _ ← Meta.transform e (pre := fun s => do
    match s with
    | .bvar .. | .sort .. | .mvar .. | .lit .. => return .continue
    | _ =>
      try
        let t ← inferType s
        if let some c ← isClass? t then
          acc.modify (·.union (ancestors env c))
      catch _ => pure ()
      return .continue)
  acc.get

/-- What we need to know about one member of a group. -/
structure MemberInfo where
  /-- Candidate classes synthesizable over one of the member's carrier types. -/
  synthesizable : Std.HashSet Name
  /-- Classes appearing as the member's own instance-implicit binders. -/
  hyps : Std.HashSet Name
  /-- Hypothesis classes with the carrier indices they are applied to, for the subsumption
  check. -/
  hypSpec : Array (Name × Array Nat)
  /-- How many carriers this member's telescope has. -/
  nCarriers : Nat
  /-- Classes the member's statement is written in terms of. -/
  stmt : Std.HashSet Name
  deriving Inhabited

def carriersOf (xs : Array Expr) : MetaM (Array Expr) := do
  let mut carriers : Array Expr := #[]
  for x in xs do
    let d ← x.fvarId!.getDecl
    if d.binderInfo != .instImplicit then
      let t ← whnf (← inferType x)
      if t.isSort && !t.isProp && carriers.size < 3 then carriers := carriers.push x
  return carriers

def classesOf (cands : Array Name) (thm : Name) : MetaM MemberInfo := do
  let ci ← getConstInfo thm
  forallTelescopeReducing ci.type fun xs body => do
    let carriers ← carriersOf xs
    let mut hyps : Std.HashSet Name := {}
    let mut hypSpec : Array (Name × Array Nat) := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo == .instImplicit then
        if let some c := d.type.getAppFn.constName? then
          hyps := hyps.insert c
          hypSpec := hypSpec.push (c, hypIndices d.type carriers)
    let stmt ← statementClasses body
    let mut hit : Std.HashSet Name := {}
    for α in carriers[0:2] do
      for c in cands do
        if hit.contains c then continue
        if ← canSynth c α then hit := hit.insert c
    return { synthesizable := hit, hyps := hyps, hypSpec := hypSpec,
             nCarriers := carriers.size, stmt := stmt }

/-- Does `thm`'s context supply every hypothesis class in `hyps`?

If so, and `thm` states the same thing as the lemma those hypotheses came from, that lemma is
strictly subsumed by `thm` and can simply be deleted — no new class required. This is a cheaper
and more certain pattern than the #41457 one; it accounts for a good share of the duplicate
groups. Failure to build a class application counts as "not implied", so the check errs towards
false negatives and never claims a redundancy that is not there. -/
def contextSupplies (spec : Array (Name × Array Nat)) (nCarriers : Nat) (thm : Name) :
    MetaM Bool := do
  if spec.isEmpty || nCarriers == 0 then return false
  -- every hypothesis must mention only carriers, else we cannot faithfully restate it
  if spec.any fun (_, idxs) => idxs.isEmpty then return false
  let ci ← getConstInfo thm
  forallTelescopeReducing ci.type fun xs _ => do
    let cs ← carriersOf xs
    if nCarriers > cs.size then return false
    for assign in injTuples cs nCarriers do
      let mut ok := true
      for (c, idxs) in spec do
        let sel := idxs.filterMap fun i => assign[i]?
        if sel.size != idxs.size then ok := false; break
        match ← (try mkClassAppN c sel catch _ => pure none) with
        | none => ok := false; break
        | some ty => unless (← synthInstance? ty).isSome do ok := false; break
      if ok then return true
    return false

/-- Rediscover the mathlib4#41457 generalization from its four sibling hypothesis sets.
Run on every invocation: if this stops reporting `IsDedekindFiniteMonoid`, the search is
broken. -/
def selfTest (cands : Array Name) (deps : Std.HashMap Name (Std.HashSet Name)) : MetaM Bool := do
  IO.println "── self-test: rediscover the mathlib4#41457 generalization ──"
  let sigs : List (List Name) :=
    [[``CommMonoid], [``LeftCancelMonoid], [``RightCancelMonoid], [``CancelMonoid]]
  let mut common : Option (Std.HashSet Name) := none
  for cls in sigs do
    let sig ← withLocalDeclD `α (mkSort (.succ Level.zero)) fun α => do
      let rec go (cs : List Name) (acc : Array Expr) : MetaM Expr := do
        match cs with
        | [] => mkForallFVars acc (mkConst ``True)
        | c :: rest => do
          let some cty ← mkClassApp c α | throwError "cannot state {c}"
          withLocalDecl `inst .instImplicit cty fun i => go rest (acc.push i)
      go cls #[α]
    -- Telescoping the signature is what registers the local instances.
    let hit ← forallTelescopeReducing sig fun xs _ => do
      let mut hit : Std.HashSet Name := {}
      for c in cands do
        if ← canSynth c xs[0]! then hit := hit.insert c
      return hit
    common := some (match common with | none => hit | some s => s.filter hit.contains)
  let commonSet := common.getD {}
  -- The statement of `mul_eq_one` is `a * b = 1 ↔ a = 1 ∧ b = 1`.
  let stmt : Std.HashSet Name := Std.HashSet.ofList [`HMul, `Mul, `One, `OfNat, `MulOne]
  let relevant := commonSet.toArray.filter fun c => (deps.getD c {}).toArray.any stmt.contains
  let ok := relevant.contains ``IsDedekindFiniteMonoid
  IO.println s!"  common to all four        : {commonSet.toArray.map toString}"
  IO.println s!"  after statement-relevance : {relevant.map toString}"
  IO.println s!"  found IsDedekindFiniteMonoid: {ok}{if ok then "" else "   *** SELF-TEST FAILED"}"
  IO.println ""
  return ok

def run (groupFile out : System.FilePath) : MetaM Unit := do
  let mixins ← candidateClasses true
  let structs ← candidateClasses false
  IO.println s!"candidate classes: {mixins.size} Prop mixins, {structs.size} structure classes"
  let cands := mixins ++ structs
  let env ← getEnv
  let mut deps : Std.HashMap Name (Std.HashSet Name) := {}
  let mut anc : Std.HashMap Name (Std.HashSet Name) := {}
  for c in cands do
    deps := deps.insert c (← try classDeps c catch _ => pure {})
    anc := anc.insert c (ancestors env c)
  let isMixin : Std.HashSet Name := Std.HashSet.ofList mixins.toList
  unless ← selfTest mixins deps do
    IO.println "self-test failed; results below are not trustworthy"
  let mut groups : Array (Array Name) := #[]
  for line in (← IO.FS.lines groupFile) do
    let names := (line.splitOn "\t").filter (!·.isEmpty) |>.map (·.toName)
    if names.length ≥ 2 then groups := groups.push names.toArray
  IO.println s!"groups to analyse: {groups.size}"
  let mut cache : Std.HashMap Name MemberInfo := {}
  let mut rows : Array String := #[]
  let mut nRedundant := 0
  let mut done := 0
  for g in groups do
    done := done + 1
    if done % 25 == 0 then IO.println s!"  … {done}/{groups.size}"
    let mut infos : Array MemberInfo := #[]
    let mut common : Option (Std.HashSet Name) := none
    let mut stmt : Std.HashSet Name := {}
    let mut bad := false
    for thm in g do
      let mi ← match cache[thm]? with
        | some v => pure v
        | none => do
            let v ← try classesOf cands thm
                     catch _ => pure { synthesizable := {}, hyps := {}, hypSpec := #[],
                                       nCarriers := 0, stmt := {} }
            cache := cache.insert thm v
            pure v
      if mi.synthesizable.isEmpty then bad := true
      infos := infos.push mi
      for s in mi.stmt do stmt := stmt.insert s
      common := some (match common with
        | none => mi.synthesizable
        | some s => s.filter mi.synthesizable.contains)
    if bad then continue
    let commonSet := common.getD {}
    -- statement-relevant, and not already a hypothesis of every member
    let relevant := commonSet.toArray.filter fun c =>
      (deps.getD c {}).toArray.any stmt.contains && infos.any (!·.hyps.contains c)
    let hits := relevant.filter isMixin.contains
    -- Among the structure classes keep only the maximal ones: `Mul` is common to everything and
    -- says nothing, whereas `DivisionMonoid` -- the strongest class common to a `Group` and a
    -- `GroupWithZero` lemma -- is the generalization one actually wants.
    let structHits := relevant.filter fun c =>
      !isMixin.contains c &&
        !relevant.any fun d => d != c && !isMixin.contains d && (anc.getD d {}).contains c
    -- Strict-subsumption pass: is one member's context enough for another member's hypotheses?
    let mut redundant : Array String := #[]
    for i in [0:g.size] do
      for j in [0:g.size] do
        if i != j then
          if ← (try contextSupplies infos[j]!.hypSpec infos[j]!.nCarriers g[i]!
                catch _ => pure false) then
            -- g[i]'s context supplies g[j]'s hypotheses, so g[j] subsumes g[i]
            redundant := redundant.push s!"{g[i]!}<={g[j]!}"
    if redundant.isEmpty && hits.isEmpty && structHits.isEmpty then continue
    unless redundant.isEmpty do nRedundant := nRedundant + 1
    rows := rows.push <| String.intercalate "\t"
      [String.intercalate "," (g.toList.map toString),
        String.intercalate "," (hits.toList.map toString),
        String.intercalate "," (structHits.toList.map toString),
        String.intercalate "," redundant.toList]
  IO.FS.writeFile out (String.intercalate "\n" rows.toList)
  IO.println s!"wrote {rows.size} groups ({nRedundant} with a strict subsumption) to {out}"

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
#eval show CoreM Unit from do
  let groups := (← IO.getEnv "DEDUP_GROUPS").getD "groups.tsv"
  let out := (← IO.getEnv "DEDUP_COMMON_OUT").getD "dedup_common_classes.tsv"
  (run groups out).run'
