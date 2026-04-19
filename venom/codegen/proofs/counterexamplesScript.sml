(*
 * Counterexamples for False Frozen Theorem Statements
 *
 * Documents concrete counterexamples showing that certain
 * frozen theorem statements are unsatisfiable as-is.
 *
 * COUNTEREXAMPLE 1: gen_inst_simulation -- PARAM case
 *   The PARAM opcode writes vs_params[i] to vs_vars,
 *   but generates no asm instructions. If vs_vars[param]
 *   differs from vs_params[i], plan_stack_rel breaks.
 *
 *)


Theory counterexamples
Ancestors
  codegenRel stackPlanGen asmSem venomExecSemantics venomState venomInst stackPlanTypes stackModel vfmExecution vfmConstants list rich_list finite_map words
Libs
  BasicProvers wordsLib

(* ============================================================
   Counterexample 1: gen_inst_simulation FALSE for PARAM
   ============================================================

   Setup:
     inst = PARAM with operand [Lit 0w], output ["x"]
     vs.vs_vars("x") = 7w, vs.vs_params = [42w]
     ps.ps_stack = [Var "x"], as.as_stack = [7w]

   generate_inst_plan returns ([], ps) -- empty plan.
   step_inst does update_var "x" 42w vs.
   After update: operand_val (Var "x") = SOME 42w <> SOME 7w.
   plan_stack_rel breaks: needs 42w = 7w on the asm stack.
*)

(* The instruction *)
Definition cex_inst_def:
  cex_inst = <| inst_opcode := PARAM;
                inst_operands := [Lit (0w:bytes32)];
                inst_outputs := ["x"] |>
End

(* generate_inst_plan returns empty plan for PARAM *)
Theorem cex_param_plan:
  !lv dfg cfg fn nl ih nit bbl ps.
    generate_inst_plan lv dfg cfg fn cex_inst nl ih nit bbl ps =
    SOME ([], ps)
Proof
  simp[generate_inst_plan_def, cex_inst_def, is_pre_codegen_opcode_def]
QED

(* plan_stack_rel holds BEFORE the PARAM instruction *)
Theorem cex_plan_stack_rel_before:
  !lo.
    plan_stack_rel lo
      <| vs_vars := FEMPTY |+ ("x", 7w:bytes32);
         vs_params := [42w]; vs_current_bb := "e";
         vs_inst_idx := 0; vs_halted := F; vs_prev_bb := NONE;
         vs_memory := []; vs_accounts := ARB; vs_transient := ARB;
         vs_returndata := []; vs_logs := []; vs_call_ctx := ARB;
         vs_tx_ctx := ARB; vs_block_ctx := ARB; vs_code := [];
         vs_prev_hashes := ARB; vs_immutables := ARB;
         vs_data_section := []; vs_labels := ARB |>
      [Var "x"] [7w:bytes32]
Proof
  simp[plan_stack_rel_def, operand_val_def, FLOOKUP_UPDATE]
QED

(* plan_stack_rel FAILS after update_var "x" 42w *)
Theorem cex_plan_stack_rel_after:
  !lo.
    ~plan_stack_rel lo
      (update_var "x" (42w:bytes32)
        <| vs_vars := FEMPTY |+ ("x", 7w:bytes32);
           vs_params := [42w]; vs_current_bb := "e";
           vs_inst_idx := 0; vs_halted := F; vs_prev_bb := NONE;
           vs_memory := []; vs_accounts := ARB; vs_transient := ARB;
           vs_returndata := []; vs_logs := []; vs_call_ctx := ARB;
           vs_tx_ctx := ARB; vs_block_ctx := ARB; vs_code := [];
           vs_prev_hashes := ARB; vs_immutables := ARB;
           vs_data_section := []; vs_labels := ARB |>)
      [Var "x"] [7w:bytes32]
Proof
  simp[plan_stack_rel_def, operand_val_def, update_var_def,
       FLOOKUP_UPDATE, LET_THM] >>
  WORD_EVAL_TAC
QED

(*
  Summary: gen_inst_simulation is FALSE for PARAM.
  gen_inst_simulation is NOT frozen -- can add inst_opcode <> PARAM precondition.
  PARAM is already excluded at block level (non_param_insts filter).
*)

(* ============================================================
   Counterexample 5: Operand Order Bug in reorder_one_def
   ============================================================

   reorder_one_def uses final_dist = num_ops - 1 - target_idx.
   This was ported from Python where operands are in push order
   (reversed from EVM semantic order). In HOL4, operands are in
   EVM semantic order. The formula puts the LAST operand at TOS
   instead of the FIRST.

   For SUB [a, b] (= a - b):
   - reorder puts b at TOS, a at depth 1
   - asm SUB computes TOS - second = b - a (wrong, should be a - b)

   For RETURN [offset, size]:
   - reorder puts size at TOS, offset at depth 1
   - asm_return_op treats TOS as offset = DROP(size), TAKE(offset)
   - Result: reads wrong memory region

   FIX: Change reorder_one_def to use final_dist = target_idx.
   File: defs/stackPlanOpsScript.sml (FROZEN).
*)

(* ============================================================
   Counterexample 6: asm_bytecode_sim — missing preconditions
   ============================================================

   asm_bytecode_sim is FALSE as stated. Missing preconditions:

   1. no_asm_calls prog — required by asm_evm_step.
      Without it: prog can contain AsmOp "CALL", AsmOp "CREATE", etc.
      asm_step handles these via asm_call/asm_create (single-context).
      EVM step handles them by pushing a new context.
      Behaviors diverge.

   2. LENGTH es.contexts = 1 — required by asm_evm_step.
      Without it: es can have 2+ contexts (nested call).
      EVM STOP in a nested call pops context (returns INL ()).
      asm_step_op STOP returns AsmHalt unconditionally.
      After 1 step: asm_steps = AsmHalt, but run continues with outer
      context. run es ≠ SOME (INR NONE, ...).

   Concrete witness for issue 2:
     prog = [AsmOp "STOP"]
     n = 1
     es.contexts = [(ctxt1, rb1), (ctxt2, rb2)]  (* 2 contexts *)
     as = <| as_pc := 0; as_stack := []; ... |>
     asm_evm_rel prog as es (only constrains top context)

     asm_steps lo o2p prog 1 as
       = case asm_step lo o2p (AsmOp "STOP") as of AsmHalt as' => AsmHalt as'
       (asm_step_op "STOP" returns AsmHalt)

     step es: EVM executes STOP. With 2 contexts, returns value to
     outer context (INL ()). run continues. Does NOT return INR NONE.

     Conclusion says: run es = SOME (INR NONE, es'). But run continues
     with the outer context — contradiction.

   TIGHTEST FIX: Add both preconditions to asm_bytecode_sim:
     no_asm_calls prog ∧ LENGTH es.contexts = 1

   Note: LENGTH es.contexts = 1 is PRESERVED by asm_evm_step
   (proven in its conclusion). no_asm_calls is a static property of prog.
*)

(* Demonstrate: reorder_plan for SUB produces wrong stack order *)
Theorem cex_reorder_sub_wrong_order:
  !dfg ps.
    ps.ps_stack = [Var "a"; Var "b"] /\
    ps.ps_spilled = FEMPTY ==>
    (SND (reorder_plan dfg [Var "a"; Var "b"] ps)).ps_stack =
      [Var "a"; Var "b"]
    (* TOS = Var "b" (last element), but should be Var "a" for SUB *)
Proof
  rpt strip_tac >>
  ASM_REWRITE_TAC[] >>
  simp[stackPlanOpsTheory.reorder_plan_def, LET_THM,
       stackPlanOpsTheory.reorder_one_def,
       stack_get_depth_def, stack_find_def, stack_peek_def]
QED

(* Demonstrate: emit_input + reorder for RETURN puts size at TOS *)
Theorem cex_return_operand_order:
  let ps = <| ps_stack := [Var "off"; Var "sz"];
              ps_spilled := FEMPTY;
              ps_alloc := <| sa_fn_eom := 0; sa_next_offset := 0;
                             sa_free_slots := [] |>;
              ps_label_counter := 0 |> in
  let (ops, ps1) = emit_input_plan RETURN
    [Var "off"; Var "sz"] ["off"; "sz"] ps in
  let (rops, ps2) = reorder_plan empty_dfg [Var "off"; Var "sz"] ps1 in
  (* After emit+reorder: TOS = Var "sz", should be Var "off" *)
  LAST ps2.ps_stack = Var "sz"
Proof
  EVAL_TAC
QED

