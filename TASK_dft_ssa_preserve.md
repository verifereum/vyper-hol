# TASK: A DFT schedule of an SSA function is SSA

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: venom/passes/dft/proofs/dftSsaPreserveScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem dft_block_rel_wf_ssa:
  !fn bbs.
    wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn /\
    LIST_REL dft_block_rel fn.fn_blocks bbs ==>
    wf_ssa (fn with fn_blocks := bbs)
```

Supporting definitions (venom/passes/dft/proofs/dftScheduleOrderScript.sml):

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
```

**Do not modify this statement. Prove it as-is, or produce a counterexample.**

## Completion Criteria

1. `holbuild --max-heap 7000 -j4 build dftSsaPreserveTheory` passes with zero CHEAT warnings from dftSsaPreserveTheory and any helper theory you add. (dftScheduleOrderTheory has its own cheat on `dft_fn_block_rel`, handled by another task; leave it alone.)
2. No duplicate or near-duplicate lemmas.

**If the theorem is false as stated:** produce a concrete counterexample, state the tightest sufficient fix, do not weaken the statement.

## Build

```
holbuild --max-heap 7000 -j4 build dftSsaPreserveTheory
```
(from the project root, the directory with `holproject.toml`)

## Background

dft_block_rel describes a DFT schedule of a block: same label, same pseudo prefix, then a permutation of the non-pseudo instructions (each unchanged or operand-flipped) keeping data-dependent pairs and the terminator last. The next compiler stage needs the scheduled function to stay SSA (wf_ssa).

## Domain Constraints

- Build only with holbuild; no Holmake, no hol4-mcp, no interactive `g`/`e` sessions. Read the repo's `AGENTS.md`.
- No `cheat` in the result. Never raise the tactic timeout (2.5 s per step). No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`.
- Do not change existing definitions or proved theorems. Helpers go in this theory or new theories next to it; no new axioms or hypotheses.
- Keep proofs short (≤ ~50 lines each). Use `--max-heap`, never `--maxheap`.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Well-formedness | venom/defs/venomWfScript.sml | wf_ssa, ssa_form (~530), def_dominates_uses (~610), def_available_at (~573), phi_edge_uses_wf (~593), fn_dominates (~559), fn_cfg_edge, fn_reachable, wf_function (~513), bb_well_formed (~463), fn_pseudos_prefix (~490) |
| Instructions | venom/defs/venomInstScript.sml | bb_succs (~763), get_successors, fn_entry_label, entry_block, fn_insts, is_pseudo, is_terminator, inst_uses, inst_defs |
| Flips | venom/passes/dft/proofs/dftStructuralScript.sml, venom/passes/dft/defs/dftDefsScript.sml | from_block, flip_operands, is_flippable, flip lemmas |
| Existing DFT lemmas | venom/passes/dft/proofs/dftCorrectnessScript.sml, dftWfScript.sml | block_perm_of, wf lemmas for DFT output |
| Intuition | comment above the theorem | unchecked proof sketch |

## Notes

- A statement checker judged it provable: terminator stays last (bb_well_formed + the terminator clause of dft_must_order, terminators not flippable), so the CFG and dominance are unchanged; the same-block clause of def_available_at is existential over the new instruction.
