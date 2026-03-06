(*
 * Venom Module Execution Semantics
 *
 * Extends single-function execution with cross-function INVOKE support.
 * Uses mutual recursion: run_module_fn / run_module_block / run_module_invoke.
 * The HOL4 recursion stack serves as the call stack (standard interpreter pattern).
 *
 * TOP-LEVEL:
 *   run_module_fn      — run a function in module context
 *   merge_callee_state — propagate callee side effects to caller
 *
 * Helper:
 *   run_module_block   — block loop with INVOKE interception
 *   run_module_invoke  — recursive call to callee function
 *)

Theory venomModuleSem
Ancestors
  venomExecSemantics

(* ===== Side-effect Merging ===== *)

(* After callee returns, propagate shared mutable state back to caller.
   Caller-local state (vs_vars, position, params) is preserved. *)
Definition merge_callee_state_def:
  merge_callee_state caller callee =
    caller with <|
      vs_memory := callee.vs_memory;
      vs_storage := callee.vs_storage;
      vs_transient := callee.vs_transient;
      vs_accounts := callee.vs_accounts;
      vs_logs := callee.vs_logs;
      vs_immutables := callee.vs_immutables
    |>
End

(* ===== Module Execution (Mutual Recursion) ===== *)

(* All three functions share a fuel parameter for termination.
   Every recursive call decreases fuel. *)

Definition run_module_fn_def:
  (run_module_fn 0 ctx fn s = Error "out of fuel") /\
  (run_module_fn (SUC fuel) ctx fn s =
    case lookup_block s.vs_current_bb fn.fn_blocks of
      NONE => Error "block not found"
    | SOME bb =>
        case run_module_block fuel ctx fn bb s of
          OK s' =>
            if s'.vs_halted then Halt s'
            else run_module_fn fuel ctx fn s'
        | other => other) /\

  (* Block loop: execute instructions, intercept INVOKE for recursive call *)
  (run_module_block 0 ctx fn bb s = Error "out of fuel") /\
  (run_module_block (SUC fuel) ctx fn bb s =
    case get_instruction bb s.vs_inst_idx of
      NONE => Error "block not terminated"
    | SOME inst =>
        if inst.inst_opcode = INVOKE then
          case run_module_invoke fuel ctx inst s of
            OK s' => run_module_block fuel ctx fn bb (next_inst s')
          | other => other
        else
          case step_inst inst s of
            OK s' =>
              if is_terminator inst.inst_opcode then OK s'
              else run_module_block fuel ctx fn bb (next_inst s')
          | other => other) /\

  (* INVOKE: set up callee, recurse, merge results *)
  (run_module_invoke 0 ctx inst s = Error "out of fuel") /\
  (run_module_invoke (SUC fuel) ctx inst s =
    case inst.inst_operands of
      Label callee :: arg_ops =>
        (case eval_operands arg_ops s of
          SOME args =>
            (case lookup_function callee ctx.ctx_functions of
              SOME callee_fn =>
                (case entry_block callee_fn of
                  SOME entry_bb =>
                    let callee_s = s with <|
                      vs_params := args;
                      vs_current_bb := entry_bb.bb_label;
                      vs_inst_idx := 0;
                      vs_prev_bb := NONE;
                      vs_vars := FEMPTY
                    |> in
                    (case run_module_fn fuel ctx callee_fn callee_s of
                      IntRet ret_vals ret_s =>
                        if LENGTH inst.inst_outputs = LENGTH ret_vals then
                          OK (update_vars inst.inst_outputs ret_vals
                                (merge_callee_state s ret_s))
                        else Error "invoke: return value count mismatch"
                    | Halt h => Halt h     (* program halt in callee *)
                    | Revert r => Revert r
                    | Error e => Error e
                    | OK _ => Error "invoke: callee did not terminate")
                | NONE => Error "invoke: callee has no entry block")
            | NONE => Error "invoke: function not found")
        | NONE => Error "invoke: undefined argument")
    | _ => Error "invoke requires label target and arguments")
Termination
  WF_REL_TAC `measure $ \x. case x of INL (f,_,_,_) => f | INR (INL (f,_,_,_,_)) => f | INR (INR (f,_,_,_)) => f`
End
