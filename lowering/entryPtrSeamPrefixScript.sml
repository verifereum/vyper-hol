(*
 * Seam of external_entry_reaches_body_ptr (loweringPtrCorrect): the entry's
 * prefix, from __entry's first block to the start of the selected external
 * function's argument registration, on a call whose value the source
 * accepted.
 *
 * The prefix is the selector dispatch (compile_selector_dispatch_linear)
 * and the selected function's entry checks (compile_entry_checks: the call
 * value check when it is nonpayable, the calldata size check), which pass:
 * send_call_value returned INL, and valid_vyper_call bounds the calldata
 * size.  They change only variables and the PC and write no memory, so the
 * ghost there carries no memory, storage, transient or immutable taint.
 * Registration (compile_register_positional_args) starts where the checks
 * end, in the same block, and the guarded body where it ends.
 *
 * The conclusion fixes the ghost (G1, tn1) the run actually reaches, not a
 * universal one: the run after it is only known safe from that ghost.
 *)
Theory entryPtrSeamPrefix
Ancestors
  entryValueRevertPtr entryDispatchPtr sourceEntryCode selectedBodyCode
  rawEntryCode entryCheckIntervals sourceEntrySelection actualRegistrationCode
  entryLocals
  vyperCompiler selectorDispatch moduleLoweringProps stmtLoweringProps
  exprLoweringProps vyperInterpreter vyperContext venomExecSemantics
  venomState compileEnv e2eDefs supportedProgram compileVyper fragExec
  venomInst contextCodegenRel ptrDiscipline ptrSafeRun vyperLoweringCorrect
  loweringRuntimeCorrect bodyPtrDefs moduleLowering venomWf

(* SEAM (cheated; proved by its own alan run).
   Hints (not binding):
   - Code: source_selected_entry_check_code and source_selected_body_code
     come from the same packaged external member; compile_external_fn_bodies
     runs compile_entry_checks and then compile_external_function_body
     (registration, then compile_guarded_body) in that member's block, so
     registration starts at `checked`.  fn_inst_ids_distinct follows from
     lowering_context_ok's ctx_inst_ids_distinct (run_lowering_context_ok);
     local_ptrs_reserved from entryLocals' compile_register_positional_args_reserved.
   - Run: entryDispatchPtr's compile_selector_dispatch_linear_ptr_continuation
     and compile_selector_checks_ptr_continuation take continuations for
     every ghost; this seam needs the actual ghost, so either state ghost-
     specific variants of them or thread ghost_run.  external_entry_value_revert_ptr
     (loweringPtrCorrect) is the rejecting twin of this prefix.
   - The pass path of compile_entry_checks: send_call_value = (INL (), _)
     gives mut = Payable or a zero call value (the converse of
     entryValueRevertPtr's initial_entry_rejected_value); valid_vyper_call's
     calldata_encodes gives the calldata size bound. *)
Theorem external_entry_reaches_registration_ptr:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 efn elbl.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
    fn_entry_label efn = SOME elbl ==>
    ?lbl cenv0 pos_args min_cds is_payable nkey ut' iv rt st cenv sa st' s1
     G1 tn1.
      set_external_package_target rpolicy.rpol_target
        (package_external_fn tops F (assign_nkeys tops 0)
           (mut, F, lookup_raw_return_or_F (NONE : num option)
                       tx.function_name External tops,
            tx.function_name, args, [], ret, fbody)) =
        (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
         rt) /\
      compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) /\
      compile_guarded_body cenv F nkey ut' iv fbody rt sa = ((), st') /\
      fn_has_code st sa efn /\ fn_has_code sa st' efn /\
      fn_inst_ids_distinct efn /\
      local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
      cenv.ce_return_buf = NONE /\
      vars_pc_only
        (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                    vs_inst_idx := 0 |>) s1 /\
      fresh_vars_wrt st s1 /\ ~s1.vs_halted /\
      s1.vs_current_bb = st.cs_current_bb /\
      s1.vs_inst_idx = LENGTH st.cs_current_insts /\
      tn1.t_mem = {} /\ tn1.t_stor = {} /\ tn1.t_trans = {} /\
      tn1.t_imm = {} /\
      !D. (!fuel. ptr_safe_run D 0 fuel unit.cu_context efn [] G1 tn1 s1) ==>
          !fuel. ptr_safe_blocks D 0 fuel unit.cu_context efn [] FEMPTY
                   entry_taint
                   (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                               vs_inst_idx := 0 |>)
Proof
  cheat
QED
