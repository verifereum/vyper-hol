# TASK: DFT schedule runs alike with the same fuel

## Meta
Status: planned
Priority: P0
Created: 2026-11-02
Location: venom/passes/dft/proofs/dftRunRelScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem dft_run_blocks_rel:
  !C C'.
    LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions ==>
    !fuel name fn fn' s.
      lookup_function name C.ctx_functions = SOME fn /\
      lookup_function name C'.ctx_functions = SOME fn' /\
      fn_entry_label fn = SOME s.vs_current_bb /\
      ctx_labels_bound C s.vs_labels ==>
      dft_res_rel (run_blocks fuel C fn s) (run_blocks fuel C' fn' s)
```

Supporting definitions (in dftRunRelScript.sml):

```sml
Definition dft_res_rel_def:
  dft_res_rel r r' <=>
    case r of
      OK s => r' = OK s
    | IntRet v s => r' = IntRet v s
    | Halt s => r' = Halt s
    | Abort a s =>
        ?a' s'. r' = Abort a' s' /\ (a = Revert_abort ==> a' = Revert_abort)
    | Error e => (!s. r' <> OK s) /\ (!v s. r' <> IntRet v s)
End
Definition ctx_labels_bound_def:
  ctx_labels_bound C L <=>
    !fn inst l.
      MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) /\
      MEM (Label l) inst.inst_operands /\ inst.inst_opcode <> INVOKE /\
      ~is_terminator inst.inst_opcode /\ ~is_pseudo inst.inst_opcode ==>
      l IN FDOM L
End
Definition dft_fn_rel_def:
  dft_fn_rel fn fn' <=>
    fn'.fn_name = fn.fn_name /\
    wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ fn_pseudos_prefix fn /\
    EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn) /\
    LIST_REL dft_block_rel fn.fn_blocks fn'.fn_blocks /\
    dft_fallible_order_kept fn fn'
End
```

and from venom/passes/dft/proofs/dftScheduleOrderScript.sml:

```sml
Definition id_before_def:
  id_before l a b <=> ?i j. i < j /\ j < LENGTH l /\ EL i l = a /\ EL j l = b
End
Definition dft_must_order_def:
  dft_must_order x y <=>
    ~DISJOINT (set (inst_defs x)) (set (inst_uses y)) \/
    ~DISJOINT (write_effects x.inst_opcode)
              (read_effects y.inst_opcode UNION write_effects y.inst_opcode) \/
    ~DISJOINT (read_effects x.inst_opcode) (write_effects y.inst_opcode) \/
    (x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
     write_effects x.inst_opcode = empty_effects) \/
    is_terminator y.inst_opcode
End
Definition dft_block_rel_def:
  dft_block_rel bb bb' <=>
    bb'.bb_label = bb.bb_label /\
    ?body.
      bb'.bb_instructions =
        FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++ body /\
      PERM (MAP (\i. i.inst_id) body)
           (MAP (\i. i.inst_id)
              (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions)) /\
      EVERY (from_block bb.bb_instructions) body /\
      !x y. MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
            ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
            id_before (MAP (\i. i.inst_id) bb.bb_instructions)
              x.inst_id y.inst_id /\
            dft_must_order x y ==>
            id_before (MAP (\i. i.inst_id) body) x.inst_id y.inst_id
End
Definition dft_fallible_order_kept_def:
  dft_fallible_order_kept fn fn' <=>
    LIST_REL
      (\bb bb'.
         !x y. MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
               is_fallible x /\ is_fallible y /\
               id_before (MAP (\i. i.inst_id) bb.bb_instructions)
                 x.inst_id y.inst_id ==>
               id_before (MAP (\i. i.inst_id) bb'.bb_instructions)
                 x.inst_id y.inst_id)
      fn.fn_blocks fn'.fn_blocks
End
```

**Do not modify this statement. Prove it as-is, or produce a counterexample.**

`dft_block_rel` is a hypothesis here (through `dft_fn_rel`); do not prove anything about `dft_fn` itself. Another task proves `dft_fn_block_rel` in dftScheduleOrderScript.sml; leave that theorem and its cheat alone.

## Completion Criteria

1. `holbuild -j4 build dftRunRelTheory` passes with zero CHEAT warnings from dftRunRelTheory and any helper theory you add (dftScheduleOrderTheory's own cheat on `dft_fn_block_rel` is out of scope and expected).
2. No duplicate or near-duplicate lemmas; reuse existing lemmas.

**If the theorem is false as stated:** produce a concrete counterexample (a context, a state, a fuel), state the tightest sufficient fix, and do not silently weaken the statement.

## Build

```
holbuild --max-heap 7000 -j4 build dftRunRelTheory
```
(from the project root, the directory with `holproject.toml`)

## Background

C' is a context whose functions are DFT schedules of C's (permutations of each block's non-pseudo instructions keeping data, effect, root and terminator order, and keeping fallible instructions in order). The theorem says a run of a function and the run of its schedule, from the entry block with the same fuel, end alike: same OK/IntRet/Halt result, an abort for an abort (revert for revert), and when C errors, C' neither continues nor returns. It feeds the O1 compiler pipeline's pass contract for DFT.

## Domain Constraints

- Build only with holbuild; no Holmake, no hol4-mcp, no interactive `g`/`e` sessions. Read the repo's `AGENTS.md`.
- No `cheat` in the result. Never raise the tactic timeout (2.5 s per step). No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`.
- Do not change existing definitions or existing proved theorems. New helper lemmas go in this theory or new theories next to it under `venom/passes/dft/proofs/`; no new axioms, no new hypotheses on the frozen theorem.
- Keep proofs short (≤ ~50 lines each); split hard subgoals into lemmas.
- Use `--max-heap`, never `--maxheap`.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Semantics | venom/defs/venomExecSemanticsScript.sml | step_inst_base (~559), run_defs (~1644: step_inst, exec_block, run_blocks), setup_callee, merge_callee_state, bind_outputs, eval_phis, lookup_function |
| State | venom/defs/venomStateScript.sml | venom_state, eval_operand (Label via vs_labels) |
| Effects | venom/defs/venomEffectsScript.sml | read_effects, write_effects, opcode_fail_class |
| Well-formedness | venom/defs/venomWfScript.sml | wf_ssa, def_dominates_uses, def_available_at, wf_function, fn_inst_wf, inst_wf, fn_pseudos_prefix, fn_dominates, fn_reachable |
| Dominance invariant | venom/passes/sccp/proofs/sccpCorrectnessProofsScript.sml | strict_dom_vars_defined (~237), _entry, _preserved (~265) |
| Old DFT commutation | venom/passes/dft/proofs/dftPermSimScript.sml, dftCommutationScript.sml, dftBlockSimScript.sml | bi_independent, run_insts_topo_equiv (pure instruction commutation; excludes INVOKE, external calls) |
| Flip semantics | venom/passes/dft/proofs/dftStructuralScript.sml | from_block, flip_operands_step_inst |
| Intuition | comment above the theorem in dftRunRelScript.sml | unchecked proof sketch |

## Notes

- A statement checker read the definitions and judged the theorem provable; it found no opcode whose state access escapes its declared effects.
