# TASK: marker-tolerant residual budgets for input emission and reorder

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/codegen/proofs/ (theorems in deepResidualSimScript.sml; helpers in deepResidualBudgetScript.sml)

## Theorem Statement (FROZEN)

In `venom/codegen/proofs/deepResidualSimScript.sml`, the five theorems below, currently `cheat`. Their definitions `residual_budget_wf_marked_def` and `plan_state_residual_wf_marked_def` (in `deepResidualBudgetScript.sml`) are frozen too, as is the proved `generated_plan_state_wf_marked_residual_nil`.

Do not modify these statements. Prove them as-is, or produce a counterexample.

```sml
Definition residual_budget_wf_marked_def:
  residual_budget_wf_marked base pending (ps : plan_state) <=>
    plan_slots_bounded base ps /\
    doSwapSim$spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    dead_stack_marker NOTIN FDOM ps.ps_spilled /\
    (!op. op <> dead_stack_marker ==>
          LIST_ELEM_COUNT op ps.ps_stack <=
          SUC (LIST_ELEM_COUNT op pending)) /\
    (!op. op IN FDOM ps.ps_spilled ==>
          LIST_ELEM_COUNT op ps.ps_stack <= LIST_ELEM_COUNT op pending)
End
Definition plan_state_residual_wf_marked_def:
  plan_state_residual_wf_marked base pending fixed (ps : plan_state) <=>
    plan_slots_bounded base ps /\
    doSwapSim$spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    dead_stack_marker NOTIN FDOM ps.ps_spilled /\
    LENGTH pending <= LENGTH ps.ps_stack /\
    fixed <= LENGTH pending /\
    (!i. i < fixed ==>
       stack_peek (LENGTH pending - 1 - i) ps.ps_stack = EL i pending) /\
    (!op. op <> dead_stack_marker ==>
          LIST_ELEM_COUNT op ps.ps_stack <=
          SUC (LIST_ELEM_COUNT op pending)) /\
    (!op. op IN FDOM ps.ps_spilled ==>
          LIST_ELEM_COUNT op ps.ps_stack <= LIST_ELEM_COUNT op pending)
End
Theorem emit_input_plan_prepared_sim_marked:
  opc <> INVOKE /\
  (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded spill_base ps /\
  residual_budget_wf_marked spill_base [] ps /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
  plan_slots_bounded spill_base ps' /\
  residual_budget_wf_marked spill_base operands ps' /\
  pending_inventory_wf operands ps' /\
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
        venom_asm_rel lo ps' vs st' /\
        st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)

Theorem reorder_plan_venom_asm_rel_numeric_marked:
  !dfg target_ops ps ops ps' base lo o2pc prog vs st.
    residual_budget_wf_marked base target_ops ps /\
    pending_inventory_wf target_ops ps /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) target_ops /\
    LENGTH target_ops <= LENGTH ps.ps_stack /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    reorder_plan dfg target_ops ps = (ops,ps') /\
    (!op1 at. MEM op1 target_ops /\
              (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
              operand_equiv dfg op1 at ==>
              operand_val vs lo op1 = operand_val vs lo at) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
          venom_asm_rel lo ps' vs st' /\
          st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
          residual_budget_wf_marked base target_ops ps' /\
          pending_inventory_wf target_ops ps'

Theorem selected_input_arranged_marked:
  residual_budget_wf_marked spillbase [] ps /\
  (!op. MEM op operands /\ is_var_operand op ==>
     MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  reorder_plan dfg selected prepared = (rops,arranged) ==>
  plan_state_residual_wf_marked spillbase selected (LENGTH selected) arranged /\
  arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected

Theorem selected_prefix_prepared_sim_marked:
  opc <> INVOKE /\
  (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded spillbase ps /\ residual_budget_wf_marked spillbase [] ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  (!op at. MEM op operands /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at operands) /\
    operand_equiv dfg op at ==>
    operand_val vs lo op = operand_val vs lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  venom_asm_rel lo ps vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp (iops ++ rops)) ==>
  plan_state_residual_wf_marked spillbase selected (LENGTH selected) arranged /\
  arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected /\
  ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp (iops ++ rops)))
          st = AsmOK st' /\
    venom_asm_rel lo arranged vs st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops))

Theorem materialised_emit_resources_marked:
  plan_state_residual_wf_marked spillbase selected (LENGTH selected) ps /\
  LENGTH selected = n /\ LENGTH outputs <= 1 /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    outputs) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) outputs) /\
  emitted = ps with ps_stack := FOLDL (\stk out. stack_push (Var out) stk)
    (stack_pop n ps.ps_stack) outputs ==>
  generated_plan_state_wf_marked spillbase emitted

```

## Completion Criteria
1. `holbuild -j4 build deepResidualSimTheory` passes at the default tactic timeout, and its build log shows no CHEAT.
2. The statements and the two definitions above are byte-for-byte unchanged.
3. Helper lemmas go in `venom/codegen/proofs/deepResidualBudgetScript.sml` (already an ancestor of deepResidualSim) or in deepResidualSimScript.sml itself. No other new theory, and no edits to other existing theories.
4. No duplicate lemmas: search before adding one, and reuse existing lemmas.

**If a theorem is false as stated:** give a concrete counterexample, state the tightest fix, and stop. Do NOT weaken the statement.

## Build
```
holbuild -j4 build deepResidualSimTheory
```

## Background
vyper-hol proves the Venom-to-EVM-assembly code generator correct. The stack planner (`venom/codegen/defs/stackPlanOpsScript.sml`, `stackPlanGenScript.sml`) tracks the abstract stack in `ps.ps_stack` and the spilled operands in `ps.ps_spilled`. A cleanup elision (`clean_stack_plan`'s `mark_dead_stack`) replaces dead slots with `dead_stack_marker` (= `Label ""`), and several slots can hold it at once. `plan_stack_rel` (`codegenRelScript.sml`) doesn't read marker slots.

The existing simulation of input emission plus reorder (`generatedPrefixSim$emit_input_plan_prepared_sim`, `generatedReorderSim$reorder_plan_venom_asm_rel_numeric`, `generatedPrefixSim$selected_input_arranged`, `preparedPrefixSim$selected_prefix_prepared_sim`, `generatedPrefixSim$materialised_emit_resources`) is stated over `reorderSim$residual_budget_wf`/`plan_state_residual_wf`. Their count clause `LIST_ELEM_COUNT op ps.ps_stack <= SUC (LIST_ELEM_COUNT op pending)` fails for the marker once it appears twice. The `_marked` budgets drop that clause for the marker and add `dead_stack_marker NOTIN FDOM ps.ps_spilled`. Each frozen theorem is its unmarked namesake over the marked budgets. The unmarked proofs are the model.

Statement-check notes (not a proof plan; verify yourself):
- The marker never enters `ps_spilled`. The only insertion is `do_spill_tos` via `do_spill_at`, called by `reduce_depth_plan` on a slot `select_spill_candidate` chose, which requires `is_var_operand`. `do_restore` only removes. `do_swap`, `do_dup` and `stack_poke` don't touch the spill map.
- The budget preservation lemmas in `reorderSimScript.sml` (about lines 485-1000: `residual_budget_wf_extend_pending`, `_push`, `_restore`, `_do_swap`, `_dup`, `_stack_poke_exchange`, `_do_spill_at`, `emit_one_input_residual_budget_wf`) reason one operand at a time. `residual_budget_wf_do_spill_at` bounds the spilled item `stack_peek d`, which is a var, so not the marker.
- The asm simulations (`emit_input_plan_venom_asm_rel_numeric`, `reduce_depth_plan_venom_asm_rel_numeric`, `do_swap/do_dup_venom_asm_rel_numeric`) need only `spill_alloc_layout_wf` from the budget.
- `reorder_plan_venom_asm_rel_numeric_marked` has no `LENGTH target_ops <= 16` (a join block can have more than 16 live inputs). Its budget half is already proved: `reorder_plan_residual_budget_wf_marked` (deepResidualBudget) gives `residual_budget_wf_marked`, `pending_inventory_wf` and `LENGTH target_ops <= LENGTH ps'.ps_stack` after `reorder_plan`, with per-step forms `reorder_one_residual_budget_wf_marked`, `reorder_one_pending_inventory_wf_marked`, `plan_steps_reorder_residual_budget_wf_marked`, and the bound-free floor `reduce_depth_plan_target_len_floor`. What's left there is the simulation: replay generatedReorderSim's `reorder_one_venom_asm_rel_numeric` / `plan_steps_reorder_venom_asm_rel_numeric` chain, taking the budget facts from these lemmas instead of the unmarked ones (the `16` there is only used for the length floor). `do_swap_venom_asm_rel_numeric` handles any `dist < LENGTH`.
- Already proved in `deepResidualBudget` (use them): `residual_budget_wf_marked_pad` / `residual_budget_wf_unpad` (the marked budget is the unmarked one with the stack's markers appended to pending), `residual_budget_wf_marked_perm`, `emit_one_input_residual_budget_wf_marked`, `emit_input_plan_residual_budget_wf_marked`, `emit_one_input_not_spilled`, `emit_input_plan_not_spilled`, `do_dup_spilled_eq`, `var_operand_not_marker`, `elem_count_replicate`, and for reorder steps: `select_spill_candidate_props`, `select_spill_candidate_not_spilled_marked`, `do_spill_at_spilled_update`, `residual_budget_wf_marked_{do_swap,do_spill_at,restore,stack_poke_exchange}`, `reduce_depth_plan_residual_budget_wf_marked`, `reduce_depth_plan_pending_inventory_mono_marked`, `reorder_restore_residual_budget_wf_marked`.
- `materialised_emit_resources_marked`: the stack is `pop ++ selected`, so non-marker counts in `pop` are at most 1. The pushed `Var out` is fresh and isn't the marker.

## Domain Constraints
- Don't edit anything under `semantics/`, `frontend/`, `lowering/`, `venom/defs/`, `venom/compiler/`, `venom/passes/`, `venom/codegen/defs/`, or any existing theory other than `deepResidualSimScript.sml` (proofs of the five theorems only) and `deepResidualBudgetScript.sml`. A lemma you'd like in a low-level theory goes in the leaf instead.
- No new definitions, axioms or cheats. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>-`, `>~`, `>|`. Never raise the tactic timeout. Keep each proof under about 50 lines, splitting into helper lemmas.
- Don't depend on generated variable names; use `rename1`.
- A few reorderSim/generatedPrefixSim helpers are `[local]`. Reprove the ones you need in the leaf under a different name; don't edit those theories.

## Available Resources
| Resource | Location | Description |
|---|---|---|
| Target theory | `venom/codegen/proofs/deepResidualSimScript.sml` | the definitions and frozen theorems |
| Helper leaf | `venom/codegen/proofs/deepResidualBudgetScript.sml` | put helpers here |
| Unmarked budgets | `venom/codegen/proofs/reorderSimScript.sml` | `residual_budget_wf_def`, `plan_state_residual_wf_def`, preservation lemmas, `plan_state_residual_wf_pop` |
| Emit input | `venom/codegen/proofs/generatedPrefixSimScript.sml`, `genericInputReadyScript.sml` | the emit_input and arranged proofs, `emit_input_plan_residual_budget_wf`, `residual_budget_wf_perm` |
| Reorder | `venom/codegen/proofs/generatedReorderSimScript.sml` | `plan_steps_reorder_venom_asm_rel_numeric`, `reduce_depth_plan_venom_asm_rel_numeric` |
| Composition | `venom/codegen/proofs/preparedPrefixSimScript.sml` | `selected_prefix_prepared_sim`'s proof |
| Marked plan wf | `venom/codegen/proofs/fnPlanPrefixScript.sml` | `generated_plan_state_wf_marked_def` |
| Planner defs | `venom/codegen/defs/stackPlanOpsScript.sml`, `stackPlanGenScript.sml`, `stackModelScript.sml`, `stackPlanTypesScript.sml` | do_* ops, reorder_one, emit_one_input |

## Notes
- The dependency cone is prebuilt in this worktree.
