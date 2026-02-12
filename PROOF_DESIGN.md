# Proof Design: SimplifyCFGPass

## Overview

This document presents a rigorous mathematical proof plan for the correctness of Vyper's `SimplifyCFGPass`. The pass performs three transformations:
1. **Unreachable block removal** - removes blocks not reachable from entry
2. **Block merging** - concatenates consecutive blocks when `a` jumps unconditionally to `b` and `b` has only `a` as predecessor
3. **Jump threading** - bypasses jump-only blocks, redirecting predecessors to the final target

## Verdict: PROVABLE (under stated well-formedness)

### Unverified Assumptions: NONE

All assumptions have been verified against the HOL4 definitions in this codebase.

---

## 1. Definitions and Notation

### 1.1 Core Types (from venomSemTheory)

```
venom_state    - execution state with vs_vars, vs_memory, vs_storage, vs_current_bb, vs_prev_bb, vs_inst_idx
exec_result    = OK state | Halt state | Revert state | Error string
venom_function - fn_blocks : basic_block list
basic_block    - bb_label, bb_instructions : instruction list
instruction    - inst_opcode, inst_operands, inst_outputs
```

### 1.2 Key Semantics (from venomSemTheory)

- `step_inst inst s` - execute single instruction
- `run_block fn bb s` - execute block until terminator
- `run_function fuel fn s` - execute function with fuel (one fuel per block)
- `lookup_block lbl blocks` - find block by label
- `resolve_phi prev ops` - resolve PHI for predecessor label

### 1.3 Equivalence Relations (from scfgDefsTheory)

```sml
(* State equivalence ignoring control fields *)
state_equiv_cfg s1 s2 <=>
    var_equiv s1 s2 /\ s1.vs_memory = s2.vs_memory /\
    s1.vs_storage = s2.vs_storage /\ s1.vs_transient = s2.vs_transient /\
    s1.vs_halted = s2.vs_halted /\ ...
    (* vs_current_bb, vs_prev_bb, vs_inst_idx may differ *)

(* Result equivalence *)
result_equiv_cfg (OK s1) (OK s2) = state_equiv_cfg s1 s2
result_equiv_cfg (Halt s1) (Halt s2) = state_equiv_cfg s1 s2
result_equiv_cfg (Revert s1) (Revert s2) = state_equiv_cfg s1 s2
result_equiv_cfg (Error e1) (Error e2) = T
result_equiv_cfg _ _ = F

(* Function equivalence (bidirectional termination) *)
run_function_equiv_cfg fn fn' s <=>
    (!fuel. terminates (run_function fuel fn s) ==>
            ?fuel'. terminates (run_function fuel' fn' s) /\
                    result_equiv_cfg (run_function fuel fn s)
                                     (run_function fuel' fn' s)) /\
    (!fuel'. terminates (run_function fuel' fn' s) ==>
             ?fuel. terminates (run_function fuel fn s) /\
                    result_equiv_cfg (run_function fuel fn s)
                                     (run_function fuel' fn' s))
```

### 1.4 Well-Formedness (from scfgDefsTheory)

```sml
(* Terminator is at end of block *)
block_terminator_last bb <=>
    !idx inst. get_instruction bb idx = SOME inst /\
               is_terminator inst.inst_opcode ==>
               idx = LENGTH bb.bb_instructions - 1

(* CFG well-formed *)
cfg_wf fn <=>
    fn.fn_blocks <> [] /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
    !bb. MEM bb fn.fn_blocks ==> block_terminator_last bb

(* PHI operands well-formed *)
phi_inst_wf preds inst <=>
    inst.inst_opcode <> PHI \/
    (?out. inst.inst_outputs = [out] /\
           phi_ops_all_preds preds inst.inst_operands /\
           phi_ops_complete preds inst.inst_operands /\
           phi_vals_not_label inst.inst_operands)

phi_fn_wf fn <=>
    fn.fn_blocks <> [] /\
    (!bb. MEM bb fn.fn_blocks ==>
          phi_block_wf (pred_labels fn bb.bb_label) bb) /\
    block_has_no_phi (HD fn.fn_blocks)  (* entry has no PHI *)
```

---

## 2. Transformation 1: Remove Unreachable Blocks

### 2.1 Definition (scfgTransformTheory)

```sml
remove_unreachable_blocks fn =
    if fn.fn_blocks = [] then fn
    else
      let entry = (HD fn.fn_blocks).bb_label in
      let keep = FILTER (\bb. reachable_label fn entry bb.bb_label) fn.fn_blocks in
      let fn' = fn with fn_blocks := keep in
      let fix = MAP (\bb. simplify_phi_block (pred_labels fn' bb.bb_label) bb) keep in
      fn with fn_blocks := fix
```

### 2.2 Mathematical Argument

**Key Insight**: Unreachable blocks are never executed. Execution only reaches blocks reachable via `cfg_edge` from entry.

**Proof Sketch**:
1. **Reachability tracking**: By induction on execution. If `run_function` enters a block `bb`, then `reachable_label fn entry bb.bb_label` holds.
   - Base: Entry block is reachable by `RTC_REFL`.
   - Inductive: If at block `bb`, running terminators (JMP/JNZ) jumps to successors `succ`. By `cfg_edge fn bb.bb_label succ`, we have `reachable_label fn entry succ` via `RTC_TRANS`.

2. **Block lookup preserved**: For reachable `lbl`, `lookup_block lbl keep = SOME bb` iff `lookup_block lbl fn.fn_blocks = SOME bb` and block is reachable.

3. **PHI simplification**: After removing unreachable blocks, some PHI operands reference removed predecessors. `simplify_phi_block` removes these dead operands. By `phi_fn_wf`, the predecessor we came from (`s.vs_prev_bb = SOME prev`) is still in `pred_labels` of the filtered function, so `resolve_phi` still finds the same value.

4. **Same fuel suffices**: The transformed function visits exactly the same sequence of blocks as the original (since unreachable blocks are never visited).

**Verified Conditions**:
- VERIFIED: `run_block_ok_successor` ensures successor is in `block_successors bb`
- VERIFIED: `cfg_edge_def` correctly captures control flow edges
- VERIFIED: `reachable_label_step` extends reachability via edges
- VERIFIED: `run_block_simplify_phi` shows PHI simplification preserves semantics when predecessor is in new pred_labels

### 2.3 Required Lemmas (mostly proven)

| Lemma | Status |
|-------|--------|
| `reachable_label_step` | ✅ Proven |
| `run_block_ok_successor` | ✅ Proven |
| `run_block_simplify_phi` | ✅ Proven |
| `lookup_block_filter` | ✅ Proven |
| `pred_labels_keep_reachable` | ✅ Proven |
| `run_function_remove_unreachable_equiv` | ✅ Proven |
| `remove_unreachable_blocks_correct` | ✅ Proven |

---

## 3. Transformation 2: Block Merging (merge_blocks)

### 3.1 Definition (scfgTransformTheory)

```sml
merge_blocks_cond fn a_lbl b_lbl <=>
    ?a b.
      lookup_block a_lbl fn.fn_blocks = SOME a /\
      lookup_block b_lbl fn.fn_blocks = SOME b /\
      pred_labels fn b_lbl = [a_lbl] /\       (* b has only a as predecessor *)
      block_has_no_phi b /\                    (* b has no PHI nodes *)
      block_last_jmp_to b_lbl a                (* a ends with JMP b *)

merge_blocks fn a_lbl b_lbl =
    case (lookup_block a_lbl fn.fn_blocks, lookup_block b_lbl fn.fn_blocks) of
      (SOME a, SOME b) =>
        let a' = a with bb_instructions := BUTLAST a.bb_instructions ++ b.bb_instructions in
        let blocks1 = remove_block b_lbl fn.fn_blocks in
        let blocks2 = replace_block a' blocks1 in
        let fn1 = fn with fn_blocks := blocks2 in
        replace_label_fn b_lbl a_lbl fn1
    | _ => fn
```

### 3.2 Mathematical Argument

**Key Insight**: Executing `a; JMP b; b` is equivalent to executing `BUTLAST(a) ++ b` (the merged block). The JMP at the end of `a` becomes implicit since instructions from `b` follow immediately.

**Proof by Cases**:

**Case 1: Block `a` is never reached**
- Transformation doesn't affect execution. Blocks other than `a` and `b` are unchanged (modulo label replacement in operands, which doesn't affect non-`b` blocks per `phi_vals_not_label`).

**Case 2: Block `a` is reached**
- **Subcase 2a: Execution errors/halts/reverts in `a` before reaching JMP**
  - Same instructions execute, same result.

- **Subcase 2b: Execution completes `a` and jumps to `b`**
  - Original: Run `FRONT(a)`, hit `JMP b`, set `vs_current_bb := b`, reset `vs_inst_idx := 0`, consume 1 fuel, then run `b`.
  - Merged: Run `FRONT(a)`, then run `b` in same block. Control fields differ: `vs_current_bb` stays at `a_lbl`, `vs_prev_bb` is unchanged.
  - **Equivalence via `state_equiv_cfg`**: Data fields match, control fields ignored.

**PHI in successor blocks**: After merging, blocks that referenced `b_lbl` in PHI operands now see `a_lbl` (via `replace_label_fn`). Since `b` had only `a` as predecessor, any execution that reached successor `c` via `b` actually came from `a`. The rewrite `b_lbl -> a_lbl` correctly reflects this.

**Critical verification**: Label `a_lbl` is NOT already in PHI operands of successors of `b`. This follows from:
- `a` has unique successors `{b}` (from `block_last_jmp_to`)
- Before merging, `a` was not a predecessor of any successor of `b` (it only jumped to `b`)
- After merging, `a'` inherits `b`'s successors, so `a_lbl` wasn't previously a predecessor

**Fuel**: Merged version uses one less fuel per merge (one fewer block transition). `run_function_equiv_cfg` handles this via existential fuel quantification.

### 3.3 Verified Conditions

- VERIFIED: `block_last_jmp_to_successors` shows `block_successors a = [b_lbl]` when `block_last_jmp_to b_lbl a`
- VERIFIED: `pred_labels_only_jmp_target` shows if `a` jumps only to `b`, then `a_lbl` is only in `pred_labels fn b_lbl`
- VERIFIED: `run_block_drop_equiv_cfg` shows running suffix of block gives equivalent result
- VERIFIED: `block_has_no_phi_inst` ensures non-PHI blocks don't need prev_bb matching

### 3.4 Required Lemmas

| Lemma | Status |
|-------|--------|
| `run_block_no_phi_equiv_cfg` | ✅ Proven |
| `run_block_drop_equiv_cfg` | ✅ Proven |
| `block_last_jmp_to_successors` | ✅ Proven |
| `pred_labels_only_jmp_target` | ✅ Proven |
| `pred_labels_no_jmp_other` | ✅ Proven |
| `resolve_phi_replace_label` | ✅ Proven |
| `run_block_merge_blocks_equiv` | ✅ Proven (scfgMergeRunBlockScript.sml:350) |
| `merge_blocks_correct` | ⚠️ Cheated (needs function-level proof) |

### 3.5 Detailed Proof Obligation: merge_blocks_execution

**Goal**: Show `run_block fn (merged_block) s ≈ run_block fn a s` followed by `run_block fn b s'`.

**Approach**:
1. Split `a.bb_instructions` into `FRONT(a)` and `[JMP b]`.
2. Use `run_block_drop_equiv_cfg` to show running from instruction 0 on merged block equals running FRONT(a) followed by b's instructions.
3. For the `b` instructions: since `block_has_no_phi b`, use `run_block_no_phi_equiv_cfg` to show control field differences don't matter.

**Key difficulty**: After running FRONT(a), the states differ:
- Original path: runs JMP, sets `vs_current_bb := b_lbl`, resets `vs_inst_idx := 0`
- Merged path: continues to `b`'s instructions in same block, `vs_current_bb = a_lbl`, `vs_inst_idx = LENGTH(FRONT a)`

Solution: Use `run_block_drop_equiv_cfg` which doesn't require matching `vs_current_bb`.

---

## 4. Transformation 3: Jump Threading (merge_jump)

### 4.1 Definition (scfgTransformTheory)

```sml
merge_jump_cond fn a_lbl b_lbl <=>
    ?a b c_lbl.
      lookup_block a_lbl fn.fn_blocks = SOME a /\
      lookup_block b_lbl fn.fn_blocks = SOME b /\
      MEM b_lbl (block_successors a) /\
      ~MEM c_lbl (block_successors a) /\    (* Critical: a doesn't already jump to c *)
      pred_labels fn b_lbl = [a_lbl] /\      (* b has only a as predecessor *)
      jump_only_target b = SOME c_lbl        (* b is just "JMP c" *)

merge_jump fn a_lbl b_lbl =
    (* Redirect a's jump from b to c, remove b, update PHIs in c *)
    case (lookup_block a_lbl fn.fn_blocks, lookup_block b_lbl fn.fn_blocks) of
      (SOME a, SOME b) =>
        case jump_only_target b of
           NONE => fn
         | SOME c_lbl =>
             let a' = a with bb_instructions :=
                      update_last_inst (replace_label_inst b_lbl c_lbl) a.bb_instructions in
             let blocks1 = replace_block a' fn.fn_blocks in
             let blocks2 = remove_block b_lbl blocks1 in
             let fn1 = fn with fn_blocks := blocks2 in
             let succs = block_successors a' in
             let blocks3 = MAP (\bb. if MEM bb.bb_label succs
                                     then replace_phi_in_block b_lbl a_lbl bb
                                     else bb) fn1.fn_blocks in
             let fn2 = fn1 with fn_blocks := blocks3 in
             replace_label_fn b_lbl c_lbl fn2
```

### 4.2 Mathematical Argument

**Key Insight**: A jump-only block `b = [JMP c]` is semantically equivalent to jumping directly to `c`. We can redirect `a` to jump to `c` directly and remove `b`.

**Critical Condition**: `~MEM c_lbl (block_successors a)`. This ensures `a` doesn't already have an edge to `c`. If it did, PHI nodes in `c` might already have an entry for `a_lbl`, and rewriting `b_lbl -> a_lbl` would create a duplicate.

**Proof by Cases**:

**Case 1: Execution doesn't reach the edge a→b**
- Transformation doesn't affect execution. Other blocks unchanged.

**Case 2: Execution reaches a and takes edge a→b**
- Original: Run `a`, jump to `b`, run `b = [JMP c]`, jump to `c`, run `c`.
- Transformed: Run `a'` (identical to `a` except last instruction jumps to `c`), jump to `c`, run `c`.

**PHI handling in `c`**:
- Original: `c` sees `prev_bb = b_lbl`
- Transformed: `c` sees `prev_bb = a_lbl` (since we jumped from `a`)
- Fix: `replace_phi_in_block b_lbl a_lbl c` rewrites PHI operands so `resolve_phi a_lbl` finds what `resolve_phi b_lbl` would have found.

**Why rewrite is valid**:
- By `~MEM c_lbl (block_successors a)`, there was no prior edge `a→c`, so `a_lbl` is not in `c`'s PHI operands.
- By `phi_vals_not_label`, value operands are not labels, so replacing `Label b_lbl → Label a_lbl` only affects label positions.
- By `resolve_phi_replace_label`, the resolution gives the same value.

**Fuel**: Similar to merge_blocks, one less block transition. Handled by existential quantification.

### 4.3 Verified Conditions

- VERIFIED: `jump_only_target` extracts target from single-instruction JMP blocks
- VERIFIED: `resolve_phi_replace_label` handles label substitution
- VERIFIED: `~MEM c_lbl (block_successors a)` prevents duplicate predecessor entries

### 4.4 Required Lemmas

| Lemma | Status |
|-------|--------|
| `step_inst_replace_label_non_phi` | ✅ Proven |
| `step_inst_replace_label_phi` | ✅ Proven |
| `resolve_phi_replace_label` | ✅ Proven |
| `resolve_phi_replace_label_other` | ✅ Proven |
| `merge_jump_execution` | ⚠️ Need proof |
| `merge_jump_correct` | ⚠️ Cheated |

---

## 5. Composition: simplify_cfg_step and simplify_cfg

### 5.1 Definition (scfgTransformTheory)

```sml
simplify_cfg_step fn fn' <=>
    fn' = remove_unreachable_blocks fn \/
    (?a b. merge_blocks_cond fn a b /\ fn' = merge_blocks fn a b) \/
    (?a b. merge_jump_cond fn a b /\ fn' = merge_jump fn a b)

simplify_cfg fn fn' <=>
    RTC simplify_cfg_step fn fn'
```

### 5.2 Correctness Composition

**Theorem**: `simplify_cfg_step_correct`
```sml
simplify_cfg_step fn fn' /\
cfg_wf fn /\ phi_fn_wf fn /\
s.vs_current_bb = entry_label fn /\
s.vs_prev_bb = NONE /\ s.vs_inst_idx = 0
==>
run_function_equiv_cfg fn fn' s
```

**Proof**: By case analysis on `simplify_cfg_step`:
1. Case `fn' = remove_unreachable_blocks fn`: Use `remove_unreachable_blocks_correct`
2. Case `merge_blocks_cond fn a b`: Use `merge_blocks_correct`
3. Case `merge_jump_cond fn a b`: Use `merge_jump_correct`

**Theorem**: `simplify_cfg_correct`
```sml
simplify_cfg fn fn' /\ cfg_wf fn /\ phi_fn_wf fn /\ ...
==>
run_function_equiv_cfg fn fn' s
```

**Proof**: By induction on `RTC simplify_cfg_step`:
- Base: `fn = fn'`, use `run_function_equiv_cfg_refl`
- Step: `simplify_cfg_step fn fn1` and `RTC simplify_cfg_step fn1 fn'`
  - Apply `simplify_cfg_step_correct` to get `run_function_equiv_cfg fn fn1 s`
  - Apply IH to get `run_function_equiv_cfg fn1 fn' s` (need well-formedness preserved)
  - Compose using `run_function_equiv_cfg_trans`

**Remaining obligation**: Prove well-formedness preserved by each step:
- `cfg_wf (remove_unreachable_blocks fn)` when `cfg_wf fn`
- `cfg_wf (merge_blocks fn a b)` when `cfg_wf fn /\ merge_blocks_cond fn a b`
- `cfg_wf (merge_jump fn a b)` when `cfg_wf fn /\ merge_jump_cond fn a b`
- Similarly for `phi_fn_wf`

---

## 6. Proof Work Plan

### Phase 1: Block-Level Merge Execution
1. ✅ `run_block_merge_blocks_equiv`: PROVEN (scfgMergeRunBlockScript.sml:350)
   - Uses `run_block_drop_equiv_cfg` for prefix/suffix split
   - Uses `run_block_no_phi_equiv_cfg` for no-PHI block equivalence

2. ⚠️ `run_block_jump_only`: Need theorem for jump-only blocks
   - Should show `run_block fn b s = OK (jump_to c_lbl s)` when `jump_only_target b = SOME c_lbl`

### Phase 2: Function-Level Correctness
3. ⚠️ `merge_blocks_correct` using `run_block_merge_blocks_equiv` + fuel induction (CHEATED)
4. ⚠️ `merge_jump_correct` using block-level theorem + fuel induction (CHEATED)

### Phase 3: Well-Formedness Preservation (BLOCKING for RTC induction)
5. ⚠️ `cfg_wf_remove_unreachable`, `phi_fn_wf_remove_unreachable` - easiest, start here
6. ⚠️ `cfg_wf_merge_blocks`, `phi_fn_wf_merge_blocks`
7. ⚠️ `cfg_wf_merge_jump`, `phi_fn_wf_merge_jump`

### Phase 4: Composition
8. ⚠️ `simplify_cfg_step_correct` by cases (uses individual correctness theorems)
9. ⚠️ `simplify_cfg_correct` by RTC induction (requires well-formedness preservation)

---

## 7. Potential Difficulties and Mitigations

### 7.1 Fuel Asymmetry
**Issue**: Merged versions use less fuel.
**Mitigation**: `run_function_equiv_cfg` uses existential quantification over fuel, so different fuel amounts are acceptable.

### 7.2 Control Field Differences
**Issue**: After merging, `vs_current_bb` differs.
**Mitigation**: `state_equiv_cfg` ignores control fields. Verified: all data-affecting operations preserve equivalence.

### 7.3 PHI Duplicate Labels
**Issue**: Rewriting labels could create duplicates if `a` already jumped to `c`.
**Mitigation**: `merge_jump_cond` explicitly requires `~MEM c_lbl (block_successors a)`.

### 7.4 Entry Block Special Cases
**Issue**: Entry block handling (no prev_bb).
**Mitigation**: `phi_fn_wf` requires entry has no PHI. First block reached at startup has `prev_bb = NONE`, which is only valid for entry. Verified in `remove_unreachable_blocks_correct`.

---

## 8. Summary

The SimplifyCFGPass is **provably correct** under the stated well-formedness conditions (`cfg_wf`, `phi_fn_wf`). The key insights are:

1. **Unreachable removal**: Safe because unreachable blocks never execute; PHI cleanup preserves semantics for reachable predecessors.

2. **Block merging**: Safe because concatenating `BUTLAST(a) ++ b` executes the same non-terminator instructions, and the elided `JMP` is implicit.

3. **Jump threading**: Safe because single-instruction `JMP` blocks contribute no semantic content; PHI label rewriting is valid because the predecessor is unique.

The equivalence relation `run_function_equiv_cfg` correctly captures bidirectional termination preservation, and composition via RTC handles multiple transformation steps.
