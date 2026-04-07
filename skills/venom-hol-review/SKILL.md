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

**No catch-alls**: Never use `| _ => T` or `| _ => F` in theorem conclusions. Catch-alls hide missing cases and mask wrong pattern coverage. Enumerate every constructor explicitly — if a case is impossible, state `F` for it with a comment saying why. If a case is uninteresting, state `T` for it explicitly. The reader must see that every case was considered.
```sml
(* Bad *)  | _ => T
(* Good *) | (INR BreakException, _) => F      (* never escapes call_external *)
           | (INR ContinueException, _) => F   (* never escapes call_external *)
           | (INR (ReturnException _), _) => F  (* caught by call_external_function *)
```

**Pruning**: Delete trivially true or practically useless theorems (e.g. acyclic ordering when all real CFGs have cycles).

## File structure

- Modern syntax: `Theory` / `Ancestors`, no `open` / `export_theory()`.
- **Ancestors vs Libs**: Theories (anything ending in `Theory`) go in `Ancestors`, never in `Libs`. Only non-theory libraries belong in `Libs` (e.g. `Defn`, `TotalDefn`, `pairLib`, `BasicProvers`, `intLib`, `fcpLib`, `pred_setLib`). Note: `Ancestors` opens only the *named* theories' namespaces — transitive ancestors are loaded but not opened. If you need theorems from `finite_mapTheory`, list `finite_map` in `Ancestors` even if it's a transitive ancestor of another listed theory.
- Separate statement file (API) from proof file (implementation). Statements use `ACCEPT_TAC proof_thm`. Shared definitions in a common ancestor to avoid circular deps.
- Every exporting API theory must be listed as an ancestor in `vyperHolScript.sml` so it is included in the top-level build.

## Holmakefile conventions

- **Daughter directories only**: A Holmakefile should include its direct children, not grandchildren. Transitive deps are discovered automatically by Holmake.
- **No external `proofs/` includes**: Don't include `proofs/` directories outside the current directory tree. Props theories already depend on proofs transitively, so including `../proofs` is redundant. Stylistically cleaner to keep Holmakefiles minimal.
- **No cycles**: If `A/Holmakefile` includes `B/` and `B/Holmakefile` includes `A/`, Holmake will report an INCLUDES chain loop. Fix by including specific subdirectories (`A/defs`, `A/props`) instead of the parent.

**Props vs proofs**: A props theorem may inline its proof (instead of `ACCEPT_TAC`) only if the proof is a trivial one-liner (e.g. `rw[foo_def]`). But if a theorem's proof is that trivial, question whether it needs to be an exported theorem at all — consumers can just `rw[foo_def]` themselves. Export theorems that save non-trivial work or that name a useful fact for `irule`/`drule`.

## Upstream commit tracking

Every compiler-related definition file (`*DefsScript.sml`) in `venom/passes/`, `venom/analysis/`, and `venom/defs/` **must** include an upstream commit header in its file comment block:

```sml
(*
 * Pass Name — Definitions
 *
 * Upstream: vyperlang/vyper@<commit-hash> (<brief description>)
 *)
```

- The commit hash identifies the Python source this file was ported from or last synced against.
- Update the hash when syncing upstream changes (e.g. `alloca_id` removal, operand changes).
- The description should be the most recent significant upstream change affecting the file.
- Proof files (`*ProofsScript.sml`, `*PropsScript.sml`) do NOT need the header — only definition files that port Python logic.

**Review check**: When reviewing a PR that ports or syncs upstream changes, verify:
1. All modified defs files have an updated `Upstream:` header.
2. The commit hash actually exists in `vyperlang/vyper`.
3. The description matches the change (not stale from a previous sync).

## Termination

- Prefer proper termination over fuel. Mutual recursion with list helper > FOLDL for HOL4's termination checker.
- Cheated termination produces unsound induction principle and **Holmake won't report it as CHEATED** ([HOL#1832](https://github.com/HOL-Theorem-Prover/HOL/issues/1832)).

## LLM artifacts

Read all modified files and check for agent artifacts that don't belong in committed code:

- **Internal task IDs or tracking**: references like "P0", "T5", "Phase 2", "Step 3" that come from an agent's internal planning, not the code's design
- **Process narration**: "Let me...", "Now I'll...", "First we..." — comments that narrate authoring rather than explain the code
- **Markup leakage**: markdown formatting, XML tags, or prompt fragments in SML comments
- **Agent infrastructure references**: paths like `.agent-files/`, `.local/`, task file names, handoff slugs — anything from the agent's working environment

The test: would a human author have written this comment? If it only makes sense in the context of an agent session, remove it.

## PR response

Reply to each unaddressed comment with addressing commit hash. Resolve own threads. Leave others' threads for them to resolve.
