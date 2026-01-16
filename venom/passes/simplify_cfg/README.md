# SimplifyCFG Pass - HOL4 Formalization

This directory contains the HOL4 formalization of the Venom IR `simplify_cfg` pass.

## Entry Points

### Pass Definition

**Theory:** `scfgTransformTheory`
**File:** `scfgTransformScript.sml`

```sml
(* The pass is the reflexive-transitive closure of step *)
Definition simplify_cfg_def:
  simplify_cfg fn fn' <=> RTC simplify_cfg_step fn fn'
End

(* Each step is one of three transforms *)
Definition simplify_cfg_step_def:
  simplify_cfg_step fn fn' <=>
    fn' = remove_unreachable_blocks fn \/
    (?a b. merge_blocks_cond fn a b /\ fn' = merge_blocks fn a b) \/
    (?a b. merge_jump_cond fn a b /\ fn' = merge_jump fn a b)
End
```

### Main Correctness Theorem

**Theory:** `scfgCorrectTheory`
**File:** `scfgCorrectScript.sml`

```sml
Theorem simplify_cfg_correct:
  !fn fn' s.
    simplify_cfg fn fn' /\
    cfg_wf fn /\ phi_fn_wf fn /\
    s.vs_current_bb = entry_label fn /\
    s.vs_prev_bb = NONE /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    (* IR invariant: non-PHI, non-terminator instructions have no Label operands *)
    (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
               inst.inst_opcode <> PHI /\ ~is_terminator inst.inst_opcode ==>
               !lbl. ~MEM (Label lbl) inst.inst_operands) ==>
    run_function_equiv_cfg fn fn' s
```

**Meaning:** If `fn` transforms to `fn'` via `simplify_cfg`, then executing `fn` and `fn'` from equivalent initial states produces equivalent results (same observable behavior, possibly different fuel).

## Architecture

```
scfgDefsTheory          Core definitions (cfg_wf, phi_fn_wf, equivalences)
       |
       v
scfgTransformTheory     Pass definition (simplify_cfg_step, transforms)
       |
       +----------------+----------------+
       |                |                |
       v                v                v
scfgEquivTheory    scfgMergeHelpersTheory   scfgPhiLemmasTheory
(state equiv)      (block manipulation)     (PHI well-formedness)
       |                |
       v                v
scfgMergeRunBlockTheory
(run_block through transforms)
       |
       v
scfgMergeCorrectTheory
(merge_blocks_correct, merge_jump_correct)
       |
       v
scfgCorrectTheory       Top-level correctness + WF preservation
```

## Theories Overview

| Theory | Purpose |
|--------|---------|
| `scfgDefs` | Core definitions: `cfg_wf`, `phi_fn_wf`, `state_equiv_cfg`, `run_function_equiv_cfg` |
| `scfgTransform` | Transform definitions: `merge_blocks`, `merge_jump`, `remove_unreachable_blocks`, `simplify_cfg_step` |
| `scfgStateOps` | Lemmas about state operations preserving `state_equiv_cfg` |
| `scfgEquiv` | Execution preserves equivalence (`step_inst`, `run_block` lemmas) |
| `scfgMergeHelpers` | Block list manipulation lemmas |
| `scfgMergeRunBlock` | `run_block` behavior through merge transforms |
| `scfgMergeCorrect` | Per-transform correctness: `merge_blocks_correct`, `merge_jump_correct` |
| `scfgPhiLemmas` | PHI well-formedness preservation lemmas |
| `scfgCorrect` | Top-level: `simplify_cfg_correct`, `wf_simplify_cfg_step` |

## Three Transforms

### 1. `remove_unreachable_blocks`

Removes blocks not reachable from entry, simplifies PHI instructions.

**Correctness:** `remove_unreachable_blocks_correct` (fully proven)

### 2. `merge_blocks`

Merges block `a` with its unique successor `b` when:
- `b` has exactly one predecessor (`a`)
- `b` is not the entry block
- `b` has no PHI instructions
- `a` ends with unconditional jump to `b`

**Correctness:** `merge_blocks_correct` (fully proven)

### 3. `merge_jump`

Eliminates jump-only block `b` that is the unique successor of `a`:
- Updates `a`'s terminator to jump directly to `b`'s target
- Removes `b`
- Updates PHI instructions in affected blocks

**Correctness:** `merge_jump_correct` (cheated - architectural blocker)

## Key Definitions

### Well-Formedness

```sml
(* CFG well-formedness *)
Definition cfg_wf_def:
  cfg_wf fn <=>
    fn.fn_blocks <> [] /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
    !bb. MEM bb fn.fn_blocks ==>
      bb.bb_instructions <> [] /\ block_terminator_last bb
End

(* PHI well-formedness *)
Definition phi_fn_wf_def:
  phi_fn_wf fn <=>
    fn.fn_blocks <> [] /\
    (!bb. MEM bb fn.fn_blocks ==>
          phi_block_wf (pred_labels fn bb.bb_label) bb) /\
    block_has_no_phi (HD fn.fn_blocks)
End
```

### Semantic Equivalence

```sml
(* State equivalence (ignores CFG control fields) *)
Definition state_equiv_cfg_def:
  state_equiv_cfg s1 s2 <=>
    var_equiv s1 s2 /\
    s1.vs_memory = s2.vs_memory /\
    s1.vs_storage = s2.vs_storage /\
    (* ... other observable fields ... *)
End

(* Function execution equivalence *)
Definition run_function_equiv_cfg_def:
  run_function_equiv_cfg fn fn' s <=>
    (* Forward: fn terminates => fn' terminates with equiv result *)
    (!fuel. terminates (run_function fuel fn s) ==>
            ?fuel'. terminates (run_function fuel' fn' s) /\
                    result_equiv_cfg (run_function fuel fn s)
                                     (run_function fuel' fn' s)) /\
    (* Backward: fn' terminates => fn terminates with equiv result *)
    (!fuel'. terminates (run_function fuel' fn' s) ==>
             ?fuel. terminates (run_function fuel fn s) /\
                    result_equiv_cfg (run_function fuel fn s)
                                     (run_function fuel' fn' s))
End
```

## Build

```bash
cd venom/passes/simplify_cfg
VFMDIR=/path/to/verifereum Holmake
```

## Status

| Component | Status |
|-----------|--------|
| `remove_unreachable_blocks_correct` | Proven |
| `merge_blocks_correct` | Proven |
| `merge_jump_correct` | Cheated (architectural blocker) |
| `wf_simplify_cfg_step` (cfg_wf) | Proven |
| `wf_simplify_cfg_step` (phi_fn_wf) | Cheated for merge_jump |
| `simplify_cfg_correct` | Depends on above |

The `merge_jump` proofs require a simulation relation redesign to handle the `vs_prev_bb` state change after executing a jump-only block.

## Reference

Python implementation: `vyper/venom/passes/simplify_cfg.py`
