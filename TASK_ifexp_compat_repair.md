# TASK: repair exprSimIfExpCompat after the AbiEncode layout change

## Meta
Status: planned
Priority: P1
Created: 2026-11-08
Location: lowering/exprSimIfExpCompatScript.sml

## Theorem Statement (FROZEN)

`exprSimIfExpCompatTheory` builds with no admissions in `lowering/exprSimIfExpCompatScript.sml`. Every theorem statement in that file stays exactly as it is now. In particular:

- `ifexp_lowered_type_classify`: its third disjunct is now `int_calls_expr e <> []` (it used to say `e` is itself an IntCall). This weakening is approved and already made; keep it.
- `ifexp_compat_lowered_type` and `ifexp_compat_body_pre_lowered_type` (its only consumers): statements unchanged.

If a statement in the file is false as it stands, give a checked counterexample and stop.

## Completion Criteria

- `holbuild -j4 build exprSimIfExpCompatTheory` passes at the default step limit, with no `cheat` in `lowering/exprSimIfExpCompatScript.sml`.
- Proof-only: no definition changes, no statement changes beyond the disjunct above. New helper lemmas may go in this file.
- Commit checked work with the trailer `Bot: opus (Claude Opus 5.5)`; do not push.

## Build

From the project root:

```sh
holbuild -j4 build exprSimIfExpCompatTheory
```

Default tactic timeout and memory limits. Some ancestor theories are admitted by a local overlay (cheated in the work tree, marked skip-worktree); inherited admissions from them are expected. Do not edit, commit or un-skip those files.

## Background

`lowered_value_type` (`lowering/defs/exprLoweringScript.sml`) now lays out AbiEncode arguments at their own lowered types: its AbiEncode clause recurses on the arguments, so its capacity is `abi_size_bound` of the arguments' lowered types (plus 4 with a method id). Before, it used their source types. An argument may be an internal call, whose lowered type is `ce.ce_func_return_type`; the premises of `ifexp_lowered_type_classify` don't constrain that, so the AbiEncode case now has to go to the new third disjunct whenever an argument contains an internal call. Otherwise each argument is either at its source type or a narrower bytestring, and the AbiEncode capacity is at most the annotation.

Useful lemmas, already proved in `lowering/exprSimHypsScript.sml` (an ancestor): the physical ABI capacity monotonicity and narrowing-compatibility results from commits 4689af76f, 1668d94c0, 8bb59944f and 0dd3df936 (`git show` them), and `memory_rhs_read_lowered_typed_unwidened`. For `ifexp_compat_body_pre_lowered_type`'s last disjunct with an internal call nested under AbiEncode, use `expr_body_pre` (which pins `ce_func_return_type` to the real signatures, see `ifexp_body_pre_intcall_physical`) together with those capacity lemmas.

## Domain Constraints

- No new axioms or admissions. Definitions only as proof-only helpers.
- No TRY/ORELSE around search tactics; no timeout overrides.
