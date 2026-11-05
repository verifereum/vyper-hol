# TASK: relabeled counted-path bridges

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/exprSimAbiGasBridgeScript.sml

## Theorem Statements (FROZEN)

Prove `frag_exec_gas_path_relabel` and `abi_decode_sim_gas_path_relabel` at the end of `lowering/exprSimAbiGasBridgeScript.sml`, as stated there, together with the definitions they use (`start_relabel_def`, `start_swap_def`, `frag_start_oblivious_def`, `frag_ops_free_def`). Do not modify those statements or definitions, nor the existing `frag_code_def`, `frag_gas_free_def`, `frag_exec_gas_path` or `abi_decode_sim_gas_path`. Prove them as-is, or produce a counterexample.

## Completion Criteria

- Both theorems are proved with no `cheat` in `lowering/exprSimAbiGasBridgeScript.sml`. Helper lemmas and proof-only definitions may be added to that file (above the two theorems). The file's `Ancestors` may change.
- Remove the ML block near the end that walks theorem tags (`Tag.dest_tag ... DB.thms "exprSimAbiGasBridge"`). Cleanliness is checked with `holbuild check exprSimAbiGasBridgeTheory`, not from the script.
- No new axioms or admissions.
- `holbuild -j4 build exprSimAbiGasBridgeTheory` passes at the default step limit, and `holbuild check exprSimAbiGasBridgeTheory` is clean.
- Commit checked work with the trailer `Bot: opus (Claude Opus 5.5)`; do not push.

## Build

```sh
holbuild -j4 build exprSimAbiGasBridgeTheory
```

Default tactic timeout and memory limits. Some ancestor theories are admitted by a local overlay (cheated in the work tree, skip-worktree); that is expected, do not edit, commit or un-skip them.

## Background

The frozen statements gained one conjunct in the `fn'` hypothesis since the previous run: `(!i. MEM i (fn_insts fn') ==> i.inst_opcode <> INVOKE)`. It only weakens what has to be shown about `fn'`. The previous run's commits on this branch (observer structure, ID distinctness, STOP observer witness package, lookup and alias boundary lemmas, up to 533e937b3) stay valid; build on them.


The existing bridges need `frag_gas_free`, whose two label conjuncts fail when the fragment's entry label `sa.cs_current_bb` equals a label the fragment generates (e.g. its exit label). Nothing at the expression boundary excludes that. Dropping the label conjuncts makes the bridges false (an emitted block `L: JMP L` makes `abi_decode_sim`/`frag_exec` vacuous).

The relabeled bridges avoid it by running the fragment from a relabeled entry block. The intended proof (argon's design):
- Pick a label `L'` that is not `sb.cs_current_bb`, not a block label in `emitted_blocks sa sb`, and not a `Label` operand of any instruction in `frag_code sa sb` (labels are strings, so one exists). Pick `ids` = consecutive numbers above every `inst_id` in `frag_code sa sb` (and above the observer's own STOP id), `LENGTH ids = LENGTH sa.cs_current_insts`.
- `sa' = start_relabel L' ids sa`, `sb' = start_swap sa L' ids sb`. Then `frag_code sa' sb' = frag_code sa sb`, `FRONT (emitted_blocks sa' sb') = FRONT (emitted_blocks sa sb)`, `LAST (emitted_blocks sa' sb')` has label `L'`, and `frag_gas_free sa' sb'` holds (opcodes from `frag_ops_free`; `L'` fresh; `sb.cs_current_bb` not in `FRONT`'s labels and not `L'`).
- Build an observer function `fnO` from `emitted_blocks sa' sb'` and a block for `sb.cs_current_bb` starting with `sb.cs_current_insts` (the existing STOP-observer construction, `frag_observer_cut` etc., can be reused). Its instruction IDs are distinct by the `ALL_DISTINCT` hypothesis and the choice of `ids`. Build it as `fn with fn_blocks := ...`, so `fnO.fn_name = fn.fn_name`; its non-STOP, non-NOP instructions all come from `fn` (the relabeled prefix is NOPs), which the new theorems' hypothesis requires of every `fn'`. The hypothesis also requires every instruction of `fn'` to be non-INVOKE; `fnO` meets it because its code is the fragment's (`frag_ops_free` excludes INVOKE), the NOP prefix and the cut STOP. Apply the existing `frag_exec_gas_path` / `abi_decode_sim_gas_path` at `(sa', sb', fnO)` from `s with vs_current_bb := L'`, using the new theorems' hypothesis for every `fn'` the existing theorem asks about.
- Transfer the resulting `gas_marked_path F ctx fnO (s with vs_current_bb := L') 0 r` to `gas_marked_path F ctx fn s 0 r'`: before the first jump, block `L'` of `fnO` at `idx >= LENGTH sa.cs_current_insts` matches `fn`'s block `sa.cs_current_bb` (by `fn_has_code sa sb fn`, `LAST (emitted_blocks sa sb)` is that block); after it, the run is in `FRONT (emitted_blocks sa sb)` or `sb.cs_current_bb`'s block, which `fn` contains the same way (`fn_has_code`), and nothing jumps to `L'`. States differ only in `vs_current_bb` while in the entry block, and afterwards only in `vs_prev_bb` (`SOME L'` in `fnO` where `fn` has `SOME sa.cs_current_bb`, after a jump out of the entry block). Hence the closures of `Q` under `vs_prev_bb` and of `R`'s exits under both fields. A previous run refuted the statements without the `vs_prev_bb` closures (witness: fragment `JMP A` with entry and exit `A`, `Q t := t.vs_prev_bb <> SOME A`).
- Exit-alias case (`sb.cs_current_bb = sa.cs_current_bb`, blocks emitted): in `fn`, the lookup of `sb.cs_current_bb` is the entry block, which starts with `sb.cs_current_insts` by `fn_has_code`; in `fnO` it is the cut block. Both run the same instructions up to the cut, so the first arrival at `(sb.cs_current_bb, LENGTH sb.cs_current_insts)` is the same in both.

## Domain Constraints

- Only `lowering/exprSimAbiGasBridgeScript.sml` changes.
- No TRY/ORELSE around proof search, no timeout overrides, no unsafe tactics.

## Available Resources

- The existing proofs in `lowering/exprSimAbiGasBridgeScript.sml` (the STOP observer, `frag_observer_cut`, `frag_observer_region`, the path transfer lemmas).
- `lowering/fragGasModeScript.sml`, `lowering/fragGasPathScript.sml`: `gas_marked_path`, `gas_path` composition.
- `lowering/fragExecScript.sml`: `run_from`, `fn_has_code`, `emitted_blocks`; `lowering/abiDecoderLoopScript.sml`: `abi_decode_sim`.
