# TASK: DFT schedule keeps data, effect, root and terminator order

## Meta
Status: planned
Priority: P0
Created: 2026-11-02
Location: venom/passes/dft/proofs/dftScheduleOrderScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem dft_fn_block_rel:
  !fn. wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn ==>
       (dft_fn fn).fn_name = fn.fn_name /\
       LIST_REL dft_block_rel fn.fn_blocks (dft_fn fn).fn_blocks
```

Supporting definitions (in the same file):

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

(Ignore `dft_fallible_order_kept`; it is a definition used by another task, not part of this theorem.)

## Completion Criteria

1. `holbuild -j4 build dftScheduleOrderTheory` passes with zero CHEAT warnings and zero failures.
2. No duplicate or near-duplicate lemmas; reuse existing DFT lemmas where they exist.

**If the theorem is false as stated:** produce a concrete counterexample (EVAL on a concrete function), state the tightest sufficient fix, and do not silently weaken the statement.

## Build

```
holbuild --max-heap 7000 -j4 build dftScheduleOrderTheory
```
(from the project root, the directory with `holproject.toml`)

## Background

`dft_fn` is Venom's DFT instruction scheduler (a model of vyper's `dft.py`). It reschedules each block's non-pseudo instructions by a DFS over data and effect dependencies, inside a worklist convergence loop that may reschedule a block several times. The old correctness proof relied on a premise that is false for real programs; this theorem replaces it with what the schedule actually guarantees: a permutation (with optional operand flips of commutative/comparator ops) that keeps every `dft_must_order` pair in input order. It is consumed by a context-level simulation proof of DFT.

## Domain Constraints

- Build only with holbuild; no Holmake, no hol4-mcp, no interactive `g`/`e` sessions. Read the repo's `AGENTS.md`.
- No `cheat` in the result. Never raise the tactic timeout (2.5 s per step). No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`.
- Do not change existing definitions or existing proved theorems. New helper lemmas go in this theory or new theories next to it under `venom/passes/dft/proofs/`; no new axioms, no new hypotheses on the frozen theorem.
- Keep proofs short (≤ ~50 lines each); split hard subgoals into lemmas.
- Use `--max-heap`, never `--maxheap`.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| DFT definitions | venom/passes/dft/defs/dftDefsScript.sml | dft_fn, dft_block, build_eda, compute_effect_deps, inst_data_deps, entry_instructions, dfs_step, schedule_from_entries, flip_operands |
| DFT proofs | venom/passes/dft/proofs/ | dftCorrectnessScript.sml (dft_fn_all_perm_of ~8082, dft_fn_dft_inv ~8009, dft_inv_def ~7927, block_perm_of_def ~168, eda_dep_def, full_dep_def, dft_block_body_topo_sorted_mapped_gen ~8212), dftTopoSortScript.sml (schedule_output_eda_before ~1202, schedule_output_producer_before ~1183), dftWfScript.sml (eda_topo_compatible_gen_weak_plain, terminator_not_dep_target), dftStructuralScript.sml (from_block, flip_operands lemmas), dftCompletenessScript.sml (schedule_output_complete) |
| Well-formedness | venom/defs/venomWfScript.sml | wf_ssa, def_dominates_uses, wf_function, fn_pseudos_prefix, pseudos_prefix, bb_well_formed |
| Effects | venom/defs/venomEffectsScript.sml | read_effects, write_effects, empty_effects |
| Instructions | venom/defs/venomInstScript.sml | inst_defs, inst_uses, is_pseudo, is_terminator |
| Intuition | comment above the theorem in dftScheduleOrderScript.sml | unchecked proof sketch |

## Notes

- A statement checker found the theorem false without `fn_pseudos_prefix` (blocks unreachable from the entry are never rescheduled); with it, it judged all parts provable.
