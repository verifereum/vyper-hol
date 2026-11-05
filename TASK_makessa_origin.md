# TASK: MakeSSA static origin map

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/passes/make_ssa/proofs/makeSsaCurrentOriginScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

```sml
Theorem make_ssa_current_fn_origin:
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  fn_phis_cover_preds fn /\
  (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
     inst.inst_opcode = PHI ==>
     ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
     !l v. MEM (l,v) (phi_pairs inst.inst_operands) ==>
       fn_cfg_edge fn l bb.bb_label) /\
  fn_phi_outputs_single_def fn /\ fn_phis_non_degenerate fn /\
  all_reachable fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  ?orig.
    !inst'. MEM inst' (fn_insts fn') ==>
      (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode <> PHI /\
         inst'.inst_id = inst.inst_id /\
         inst'.inst_opcode = inst.inst_opcode /\
         MAP orig inst'.inst_outputs = inst.inst_outputs /\
         MAP (\op. case op of Var u => Var (orig u) | _ => op)
           inst'.inst_operands = inst.inst_operands) \/
      (inst'.inst_opcode = NOP /\ inst'.inst_outputs = [] /\
       inst'.inst_operands = []) \/
      ((inst'.inst_opcode = PHI \/ inst'.inst_opcode = ASSIGN) /\
       ?w inst. inst'.inst_outputs = [w] /\ MEM inst (fn_insts fn) /\
         MEM (orig w) inst.inst_outputs /\
         (inst'.inst_opcode = ASSIGN ==> ?u. inst'.inst_operands = [Var u]) /\
         (!op. MEM op inst'.inst_operands ==> ?x. op = Var x \/ op = Label x) /\
         !u. MEM (Var u) inst'.inst_operands ==>
             orig u = orig w \/
             (inst.inst_opcode = PHI /\ MEM (Var (orig u)) inst.inst_operands))
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. The build below passes with zero CHEAT warnings in `makeSsaCurrentOriginTheory`, and nothing it depends on is admitted (see Domain Constraints).
2. Helper lemmas go in new theories under `venom/passes/make_ssa/proofs/` (or in `makeSsaCurrentOriginScript.sml`); each exists once in its most general form.
3. No change to any existing theory.

**If the theorem is false as stated:** produce a HOL4 counterexample (EVAL on concrete values of `make_ssa_current_fn`), state the tightest sufficient fix, and do NOT weaken the statement.

## Build

```
holbuild -j4 build makeSsaCurrentOriginTheory
```

Run from this directory (the one with `holproject.toml`).

## Background

MakeSSA (`make_ssa_current_fn`) inserts pruned PHIs at the front of dominance-frontier blocks, renames along the dominator tree (a variable's first definition keeps its spelling, later ones get fresh `formal_var_<n>` names from the IR supply), renames PHI operands per predecessor edge, and, when the input already had PHIs, simplifies degenerate PHIs in each block's leading PHI prefix to ASSIGN or NOP. This theorem says the pass only renames: some map `orig` from output variable names to input names relates every output instruction to an input non-PHI (same id and opcode, equal after `orig`), a NOP, or a PHI/ASSIGN defining a renamed copy of an input variable. The pointer-discipline row of MakeSSA's O1 pass contract (`venom/compiler/o1ContractMakeSsaScript.sml`) uses it. Intuition is in a comment above the theorem.

## Domain Constraints

- Use holbuild only (no Holmake, no REPL sessions). Default tactic timeout; never raise it.
- No `cheat` in the result. No `TRY`/`ORELSE` around metis or other search.
- No `let` in theorem statements.
- Don't use the admitted theories on this branch as ancestors: `makeSsaCurrentWfSsaTheory`, `makeSsaCurrentSimTheory`, `makeSsaCurrentInputOkTheory`, `makeSsaCurrentNonDegenerateTheory`, `makeSsaCurrentFrameRfTheory` (their theorems are cheated). Proved facts from the reference trees below may be ported (copied with their proofs) into new theories here.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| MakeSSA definitions | `venom/passes/make_ssa/defs/makeSsaCurrentDefsScript.sml` | the pass under proof; its own small lemmas at the end (labels, ids, vars, length of the cleaned prefix) |
| Older MakeSSA defs it reuses | `venom/passes/make_ssa/defs/makeSsaDefsScript.sml` | `compute_defs`, `compute_defs_keys`, `block_assignments`, `insert_phi_at_block` |
| Proved basic MakeSSA facts | `venom/passes/make_ssa/proofs/makeSsaCurrentPropsScript.sml`, `makeSsaCurrentInductScript.sml` | proved, usable as ancestors: supply/coverage invariants (`ssa_vars_covered`, `ssa_stacks_covered`, `add_phi_nodes_supply_ok`, `rename_current_blocks_vars_covered`, `push_current_name_covered`, `make_ssa_current_fn_supply_ok`), labels (`rename_current_blocks_labels`), ids (`rename_current_blocks_inst_ids`) |
| IR supply | `venom/defs/irSupplyScript.sml` | `fresh_ir_var`, `fresh_ir_var_contract` (fresh name not in `irs_used_vars`) |
| Supply cover premise | `venom/defs/venomFnScheduleRunnerScript.sml` | `ir_supply_covers_fn` |
| Well-formedness | `venom/defs/venomWfScript.sml` | `wf_function` (distinct labels), `fn_inst_wf`, `inst_wf` (PHI: one output, `phi_well_formed` operands) |
| Block helpers | `venom/defs/cfgTransformScript.sml` (`replace_block`), `venom/defs/venomInstScript.sml` (`lookup_block`, `fn_insts`, `phi_pairs`) | |
| Consumer | `venom/compiler/o1ContractMakeSsaScript.sml` | how the theorem is used |
| Reference: MakeSSA static machinery (proved, older base) | `alan-ref/makessa3/venom/passes/make_ssa/proofs/` | many `makeSsaCurrent*` theories: rename traces (`makeSsaCurrentRenameTraceScript.sml`, `makeSsaCurrentTreeTraceScript.sml`), block shape and positions (`makeSsaCurrentPhaseShapeScript.sml`, `makeSsaCurrentOrdinaryIdsScript.sml`, `makeSsaCurrentCleanupShapeScript.sml`, `makeSsaCurrentFinalBlockScript.sml`), output names (`makeSsaCurrentOutputNamesScript.sml`). Reading only; a file there with an unfinished proof is not proved. Port what you need. |
| Reference: proved `make_ssa_current_fn_wf_ssa` | `alan-ref/makessa-wf/venom/passes/make_ssa/proofs/makeSsaCurrentWfSsaScript.sml` and its helper theories | walks the same rename with fresh-name/distinct-output facts; port what you need |

## Notes

- `makeSsaCurrentDefsScript.sml` in both `alan-ref/*` trees is byte-identical to this branch's; other theories there may differ, so use this branch's definitions.
