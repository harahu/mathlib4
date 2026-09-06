#!/usr/bin/env python3
"""Group the output of `scripts/find_duplicate_statements.lean` into duplicate clusters.

Reads the TSV produced by that script and prints the groups of theorems that state the same
thing under different typeclass hypotheses -- candidates for being collapsed into a single
lemma over a weaker class, as in mathlib4#41457.

Usage:

    lake env lean scripts/find_duplicate_statements.lean       # writes dedup_statements.tsv
    ./scripts/group_duplicate_statements.py dedup_statements.tsv --report
    ./scripts/group_duplicate_statements.py dedup_statements.tsv --groups groups.tsv

`--report` prints a human-readable listing. `--groups FILE` writes the bare member names, one
group per tab-separated line, which is the input format of
`scripts/find_common_generalization.lean`.

Filters applied by default, all of which remove known non-opportunities:

* alias/forwarder members whose proof is a direct application of another member;
* groups whose members do not share a base name (after stripping namespaces and primes);
* groups whose members all carry the same hypotheses (nothing to generalize);
* groups whose statement is not a mathematical claim (no `=`, `<`, `iff`, ...), which are
  overwhelmingly instance-provision lemmas with many unrelated sufficient conditions.

Use `--key C` to group by the carrier-erased key instead, which matches a generic lemma against
a copy stated for one concrete type. That mostly rediscovers the deliberate `Set`/`Finset`
parallel API, so the default is `--key B`.
"""

import argparse
import collections
import re
import sys

MATHY = re.compile(r"Eq\.\{|\bIff\b|LE\.le|LT\.lt|Dvd\.dvd|Membership\.mem|\bNe\b")

# name, module, hypothesis classes, proof head symbol, hash keyB, hash keyC, keyB
NAME, MODULE, CLASSES, FWD, KEY_B, KEY_C, KEY = range(7)


def base_name(name: str) -> str:
    """`Foo.Bar.baz'` -> `baz`."""
    return name.split(".")[-1].rstrip("'")


def hypotheses(row) -> frozenset:
    return frozenset(c for c in row[CLASSES].split(",") if c)


def read_rows(path):
    rows = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            parts = line.rstrip("\n").split("\t")
            if len(parts) >= 7:
                rows.append(parts)
    return rows


def build_groups(rows, key_col, *, same_base_name=True, mathy_only=True,
                 min_members=2, max_members=None):
    buckets = collections.defaultdict(list)
    for row in rows:
        buckets[row[key_col]].append(row)

    groups = []
    for members in buckets.values():
        names = {m[NAME] for m in members}
        if len(names) < min_members:
            continue

        # Drop aliases and one-line forwarders pointing at another member of the group.
        kept, seen = [], set()
        for m in members:
            if m[FWD] in names or m[NAME] in seen:
                continue
            seen.add(m[NAME])
            kept.append(m)
        if len(kept) < min_members:
            continue
        if max_members is not None and len(kept) > max_members:
            continue
        # Differing hypotheses is the whole point; identical ones mean nothing to generalize.
        if len({hypotheses(m) for m in kept}) < 2:
            continue
        if same_base_name and len({base_name(m[NAME]) for m in kept}) != 1:
            continue
        if mathy_only:
            body = kept[0][KEY].split("}, ", 1)[-1]
            if not MATHY.search(body):
                continue
        groups.append(kept)

    groups.sort(key=lambda g: (-len(g), base_name(g[0][NAME])))
    return groups


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("tsv", help="output of scripts/find_duplicate_statements.lean")
    p.add_argument("--key", choices=["B", "C"], default="B",
                   help="B (default): keep carrier types. C: also erase them.")
    p.add_argument("--report", action="store_true", help="print a human-readable listing")
    p.add_argument("--groups", metavar="FILE",
                   help="write bare member names for find_common_generalization.lean")
    p.add_argument("--any-name", action="store_true",
                   help="do not require members to share a base name")
    p.add_argument("--all-statements", action="store_true",
                   help="do not restrict to mathematical statements")
    p.add_argument("--max-members", type=int, default=6,
                   help="skip groups larger than this (default 6)")
    args = p.parse_args()

    rows = read_rows(args.tsv)
    groups = build_groups(rows, KEY_B if args.key == "B" else KEY_C,
                          same_base_name=not args.any_name,
                          mathy_only=not args.all_statements,
                          max_members=args.max_members)
    print(f"{len(groups)} duplicate groups from {len(rows)} theorems", file=sys.stderr)

    if args.groups:
        with open(args.groups, "w", encoding="utf-8") as f:
            for g in groups:
                f.write("\t".join(m[NAME] for m in g) + "\n")
        print(f"wrote {args.groups}", file=sys.stderr)

    if args.report or not args.groups:
        for g in groups:
            print(f"--- {base_name(g[0][NAME])}  ({len(g)})")
            for m in sorted(g, key=lambda m: m[NAME]):
                print(f"    {m[NAME]:<52} [{m[CLASSES]}]  {m[MODULE]}")
            print(f"    KEY: {g[0][KEY][:240]}")
            print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
