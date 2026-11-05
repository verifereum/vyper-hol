(* A piece of S1 (loweringRuntimeCorrect's lower_vyper_runtime_unit_correct). *)
Theory externalBodyRevertData
Ancestors
  stmtSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list pair fragExec  bodySim bodySimMain loweringHalt stmtLoweringMono  exprLoweringProps
  compileEnv compileVyper moduleLowering stmtLowering
  e2eDefs supportedProgram vyperLoweringCorrect rawReturnHeader
  vyperTypeSelectedEntrySoundness vyperTypeSystem
  vyperInterpreter vyperState vyperContext
  venomState venomExecSemantics venomWf

val _ = Parse.hide "body";

(* ADMITTED (mismatch between the body judgment and S1's result relation):
   when the body's actual source run, at the gas observations of a target
   path from the body's start, ends in a failed external call's
   RevertData, that path aborts with a revert.  stmt_frag's expr_exit
   allows any Abort for RevertData, while external_call_result_rel asks a
   revert. *)
Theorem external_body_revert_data_reverts:
  !tops bindings ctx func cenv cx env_t env' ret_ty RetQ fbody es0 sa sb
   cenv' s0 marks d es_end a t.
    body_inv tops ctx cenv cx /\ supported_stmts tops bindings fbody /\
    expr_sim_inv cenv cx env_t es0 /\ ce_locals_declared cenv env_t /\
    locals_alloc_ok cenv env_t /\
    type_stmts env_t ret_ty fbody = SOME env' /\
    EVERY (stmt_exprs_ok cenv) fbody /\
    call_evaluation_safe cx (int_calls_stmts fbody) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    stmts_env cenv NoLoop ret_ty fbody sa = (cenv', sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
    ~block_is_terminated sa /\ stmt_state_rel ctx func cenv cx es0 s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    gas_marked_exec F (ctx, func) (eval_stmts cx fbody) (es0, s0) marks
      (INR (Error (RevertData d))) es_end (Abort a t) ==>
    a = Revert_abort
Proof
  cheat
QED
