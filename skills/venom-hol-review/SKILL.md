---
name: venom-hol-review
description: Review HOL4 theory files for correctness, naming, placement, documentation, and completeness. Use when reviewing PR comments on HOL4 code, auditing theorem statements, checking definition quality, or preparing theories for merge.
---

# HOL4 Theory Review

Structured review for HOL4 theory files. Work each section in order.

## Definitions

**Naming**: Name reflects what it *is*, not where it's used. No implied properties it doesn't have.
- Bad: `cfg_labels` (nothing CFG-specific) → Good: `fn_labels`
- Bad: `ordset_add` (no ordering) → Good: `set_insert`

**Placement**: General IR concepts → base theory. Analysis-specific → analysis theory. If multiple passes need it, don't bury it in one pass.

**Composition**: Composite predicates reference named sub-predicates, not inline conditions.
```sml
(* Bad *)  wf fn <=> ... /\ bb.bb_instructions <> [] /\ is_terminator ... /\ ...
(* Good *) wf fn <=> ... /\ bb_well_formed bb /\ fn_succs_closed fn
```

**Duplication**: Check HOL4 stdlib first:
```sml
DB.apropos ``your_term``; DB.find "suspected_name";
```
Common hits: `INDEX_OF`, `RTC` for reachability, list operations. Prefer stdlib (free lemmas). Wrap for readability when needed: `cfg_path cfg = RTC (λa b. MEM b (cfg_succs_of cfg a))`.

## Theorem statements

**NL descriptions** must be both correct and useful — someone understands the theorem without reading the formal statement.

Failures to catch:
- Restating the name: "succ labels are labels" — vacuous
- Hiding preconditions: "entry is last in postorder" — what about nonemptiness?
- Hiding conclusions: "entry is first in preorder" — also proves nonemptiness
- Jargon: "non-back-edge successors" → "edge a→b where b cannot reach a"

**Strength**: Preconditions minimal, conclusions maximal.
```sml
(* Weak *) entry = SOME bb /\ post <> [] ==> LAST post = bb.bb_label
(* Strong *) entry = SOME bb ==> post <> [] /\ LAST post = bb.bb_label
```

**Completeness**: For each map/relation check domain, range, inverse, and symmetry. If you have a postorder property, state the preorder version too.

**Pruning**: Delete trivially true or practically useless theorems (e.g. acyclic ordering when all real CFGs have cycles).

## File structure

- Modern syntax: `Theory` / `Ancestors`, no `open` / `export_theory()`.
- Separate statement file (API) from proof file (implementation). Statements use `ACCEPT_TAC proof_thm`. Shared definitions in a common ancestor to avoid circular deps.

## Termination

- Prefer proper termination over fuel. Mutual recursion with list helper > FOLDL for HOL4's termination checker.
- Cheated termination produces unsound induction principle and **Holmake won't report it as CHEATED** ([HOL#1832](https://github.com/HOL-Theorem-Prover/HOL/issues/1832)).

## PR response

Reply to each unaddressed comment with addressing commit hash. Resolve own threads. Leave others' threads for them to resolve.
