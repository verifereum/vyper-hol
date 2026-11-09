(* Recover activation typing from the original whole-statement execution. *)
Theory bodyIntCallFamStmtMutationActivateTyping
Ancestors
  bodyIntCallFamStmtMutationActivate bodyExprPreFacts
  bodyIntCallJointContract

Theorem intcall_declared_local_activate_stmt_resources:
  let es' = es with scopes :=
        (sc |+ (id,<|assignable := a; type := tv; value := v; popped := []|>)) :: rest
  in
  intcall_expr_res fp ce env es sa s /\
  fn_inst_ids_distinct fp.jc_func /\ es.scopes = sc :: rest /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr ce es.scopes p /\ lookup_var p s = SOME w /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
  type_memory_size tv <= sz /\ val_wf tv v /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  intcall_joint_res fp ce0 env es0 sa0 s0 /\
  supported_program fp.jc_tops /\
  get_module_code fp.jc_cx NONE = SOME fp.jc_tops /\
  supported_stmt fp.jc_tops bindings st /\ ce0.ce_alloca_locals /\
  stmt_exprs_ok ce0 st /\ type_stmt env ret_ty st = SOME env' /\
  call_evaluation_safe fp.jc_cx (int_calls_stmt st) /\
  eval_stmt fp.jc_cx st es0 = (INL (),es') /\
  stmt_env ce0 lctx ret_ty st sa0 = (ce,sm) ==>
  intcall_joint_res fp ce env' es' sa s
Proof
  pure_rewrite_tac [LET_THM] >> BETA_TAC >> strip_tac >>
  `expr_sim_inv ce0 fp.jc_cx env es0 /\ locals_alloc_ok ce0 env /\
   ce_locals_declared ce0 env` by
    fs[intcall_joint_res_def, intcall_expr_res_def] >>
  drule_all expr_sim_inv_stmt >> strip_tac >>
  drule_all locals_alloc_ok_stmt >> strip_tac >>
  drule_all ce_locals_declared_stmt >> strip_tac >>
  irule (intcall_declared_local_activate_resources |> SIMP_RULE bool_ss [LET_THM]) >>
  goal_assum (drule_at Any) >> metis_tac[]
QED
