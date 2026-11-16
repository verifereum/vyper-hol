Theory bodyFullForRangeBody
Ancestors
  bodySimFull bodyFullPreds bodyExprPreFacts gasOutcomeFullCompose
  stmtSimForParts stmtSimForRange gasShadow
  vyperInterpreter vyperState list finite_map supportedStmtTraverse
  allocLimits bodySim compileVyper gasContext stmtSimDefs
  vyperTypeSystem supportedStmts vyperTypeCallGraph vyperTypeCallStackSoundness

Theorem for_frame_ret_ok_full_same_frame:
  same_frame cenv bc /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ cenv ret_ty ==>
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ bc ret_ty
Proof
  rw[frame_ret_ok_full_def] >>
  first_x_assum irule >> simp[] >>
  metis_tac[same_frame_trans]
QED

Theorem for_full_body_abi_targets:
  !tops id typ it n body.
  (!target. supported_stmt_expr_exists
     (expr_abi_decode_target_root target) (For id typ it n body) ==>
     occurs_abi_decode_target target tops) ==>
  !target. supported_stmts_expr_exists
    (expr_abi_decode_target_root target) body ==>
    occurs_abi_decode_target target tops
Proof
  simp[supported_stmt_expr_exists_def]
QED

Theorem for_full_body_exprs_ok:
  !cenv id typ it n body.
  stmt_exprs_ok cenv (For id typ it n body) ==>
  stmts_exprs_ok (cenv with ce_var_type updated_by (id =+ SOME typ)) body
Proof
  simp[stmts_exprs_ok_thm, stmt_exprs_ok_def,
       supported_stmt_expr_exists_def, allocLimitsTheory.alloc_limits_stmt_def,
       stmt_valued_return_def]
QED

Theorem for_full_body_gas_admissible:
  gas_admissible (eval_for cx tyv id stmts (Value v::vs))
    (stmt_res_ok lctx) es /\ lookup_scopes id es.scopes = NONE ==>
  gas_admissible (eval_stmts cx stmts)
    (stmt_res_ok (InLoop exit_lbl incr_lbl))
    (es with <| scopes :=
      (FEMPTY |+ (id, <| assignable := F; type := tyv;
                         value := v; popped := [] |>)) :: es.scopes;
                gas_obs := [] |>)
Proof
  strip_tac >>
  simp[gas_admissible_def] >> rpt gen_tac >> strip_tac >>
  rename1 `eval_stmts cx stmts _ = (res, ee)` >>
  Cases_on `eval_for cx tyv id stmts (Value v::vs) (es with gas_obs := gs)` >>
  rename1 `_ = (lr, le)` >>
  `stmt_res_ok lctx lr` by
    (gvs[gas_admissible_def] >> metis_tac[]) >>
  drule eval_for_cons_cases >> simp[] >> strip_tac >>
  gvs[] >> metis_tac[stmt_res_ok_def]
QED

Theorem for_full_body_fragment:
  !cx id typ it n stmts tops bindings ctx shadow_ctx func shadow_func
    cenv bc env env' ret_ty RetQ ee DF lo d PG st st1.
  body_stmts_full_ok cx stmts /\
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (For id typ it n stmts) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ it n stmts) ==> occurs_abi_decode_target target tops) /\
  ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  type_stmt env ret_ty (For id typ it n stmts) = SOME env' /\
  stmt_exprs_ok cenv (For id typ it n stmts) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ it n stmts)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ cenv ret_ty /\
  declare_local cenv id typ st = (bc,st1) /\ same_frame cenv bc /\
  type_memory_bytes cenv typ = 32 /\
  expr_sim_inv bc cx (extend_local env id typ F) ee ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx (InLoop exit_lbl incr_lbl) RetQ bc
    (stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty stmts)
    (stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty (MAP gas_shadow_stmt stmts))
    (eval_stmts cx stmts) ee
Proof
  rpt gen_tac >> strip_tac >>
  `?env_b. type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b` by
    gvs[type_stmt_def,optionTheory.IS_SOME_EXISTS,AllCaseEqs()] >>
  qpat_x_assum `body_stmts_full_ok _ _` mp_tac >>
  simp[body_stmts_full_ok_def] >> disch_then irule >>
  simp[] >> conj_tac
  >- (gvs[int_calls_stmt_def] >> metis_tac[call_evaluation_safe_append_right]) >>
  conj_tac
  >- metis_tac[for_full_body_exprs_ok,for_declare_stmts_exprs_ok] >>
  conj_tac
  >- (qexistsl_tac [`bindings`,`tops`] >> rpt conj_tac
      >- metis_tac[for_full_body_abi_targets]
      >- gvs[supported_stmt_def]
      >> metis_tac[body_inv_same_frame]) >>
  conj_tac
  >- (qexistsl_tac [`extend_local env id typ F`,`env_b`] >> simp[] >>
      conj_tac >- metis_tac[ce_locals_declared_declare_local] >>
      irule locals_alloc_ok_extend >> qexists_tac `cenv` >> simp[] >>
      metis_tac[same_frame_struct_fields]) >>
  metis_tac[for_frame_ret_ok_full_same_frame]
QED

(* This elimination retains the actual output compile environment and the
   complete full statement post. Normalization does not select another run. *)
Theorem for_full_body_fragment_normalized:
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ bc
    (stmts_env bc lctx ret_ty stmts)
    (stmts_env bc lctx ret_ty (MAP gas_shadow_stmt stmts)) source ee /\
  stmts_env bc lctx ret_ty stmts sb0 = (bc_out,sb1) /\
  stmts_env bc lctx ret_ty (MAP gas_shadow_stmt stmts) shadow_sb0 =
    (bc_out,shadow_sb1) /\
  gas_shadow_state sb0 shadow_sb0 /\ gas_shadow_state sb1 shadow_sb1 /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sb0 sb1 func /\ fn_has_code shadow_sb0 shadow_sb1 shadow_func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo bc cx) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved bc sb0 /\
  ret_pc_ok bc sb0 sstart /\
  (!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sb0 x) /\ ~block_is_terminated sb0 /\
  gas_admissible source (stmt_res_ok lctx) ee /\
  return_buf_frame d bc sb0 sstart /\ alloca_history func sstart /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func bc cx ee sstart /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d bc cx ee Gstart tnstart sstart) /\
  ~sstart.vs_halted /\ sstart.vs_current_bb = sb0.cs_current_bb /\
  sstart.vs_inst_idx = LENGTH sb0.cs_current_insts ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 source (ee,sstart,Gstart,tnstart)
    (\H res mid G tn t. mid.gas_obs = [] /\ ?cenv''.
      stmt_lands lctx sb1 res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb1 /\ cenv'' = bc_out) /\
      cenv_top_ext bc cenv'' mid.scopes /\
      stmt_state_rel H ctx func cenv'' cx mid t /\
      storage_well_formed_on cx mid (FST H) /\
      return_buf_frame d cenv'' sb1 t /\ alloca_history func t /\
      sstart.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx mid G tn t /\
      (!x w. not_fresh_at sb0 x /\ lookup_var x sstart = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP sstart.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sb0 x ==>
        FLOOKUP G x = FLOOKUP Gstart x /\
        op_taint tn (Var x) = op_taint tnstart (Var x)))
    (\H res mid gt r.
      !tail. stmt_exit_ptr (RetQ H) (mid with gas_obs := tail) res gt r)
Proof
  strip_tac >>
  qpat_x_assum `stmt_frag_full _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_frag_full_def] >>
  disch_then (drule_at (Pos hd)) >>
  disch_then (drule_at (Pos hd)) >>
  disch_then (qspecl_then [`st0`,`sstart`,`Gstart`,`tnstart`] mp_tac) >>
  simp[] >>
  impl_tac
  >- (rpt strip_tac >>
      drule_all contextRawReachableTheory.frag_reachable_members >>
      qpat_x_assum `~ctx_has_dalloca ctx` mp_tac >>
      simp[ptrDisciplineTheory.ctx_has_dalloca_def, listTheory.EXISTS_MEM,
           unitMemInvTheory.dalloca_no_wrap_def] >> metis_tac[]) >>
  strip_tac >>
  drule gas_outcome_full_post_source >>
  disch_then irule >> simp[]
QED

Theorem for_range_literal_body_invoke_full:
  body_for_full_ok cx tyv id stmts (Value first::rest) /\
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (For id typ it n stmts) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ it n stmts) ==> occurs_abi_decode_target target tops) /\
  ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  type_stmt env ret_ty (For id typ it n stmts) = SOME env' /\
  stmt_exprs_ok cenv (For id typ it n stmts) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ it n stmts)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ cenv ret_ty /\
  declare_local cenv id typ st = (bc,st1) /\ same_frame cenv bc /\
  type_memory_bytes cenv typ = 32 /\
  pushed = (ee with <| scopes :=
    (FEMPTY |+ (id, <| assignable := F; type := tyv;
                       value := v; popped := [] |>)) :: ee.scopes;
              gas_obs := [] |>) /\
  expr_sim_inv bc cx (extend_local env id typ F) pushed /\
  gas_admissible (eval_for cx tyv id stmts (Value v::vs))
    (stmt_res_ok lctx) ee /\ lookup_scopes id ee.scopes = NONE /\
  stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty stmts sb0 = (bc_out,sb1) /\
  stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty (MAP gas_shadow_stmt stmts)
    shadow_sb0 = (bc_out,shadow_sb1) /\
  gas_shadow_state sb0 shadow_sb0 /\ gas_shadow_state sb1 shadow_sb1 /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sb0 sb1 func /\ fn_has_code shadow_sb0 shadow_sb1 shadow_func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved bc sb0 /\
  ret_pc_ok bc sb0 sstart /\
  (!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sb0 x) /\ ~block_is_terminated sb0 /\
  return_buf_frame d bc sb0 sstart /\ alloca_history func sstart /\
  (!H. valid_horizon cx st0 H pushed.storage_trace ==>
    stmt_state_rel H ctx func bc cx pushed sstart /\
    storage_well_formed_on cx pushed (FST H) /\
    ghost_inv_at (DF H) lo d bc cx pushed Gstart tnstart sstart) /\
  ~sstart.vs_halted /\ sstart.vs_current_bb = sb0.cs_current_bb /\
  sstart.vs_inst_idx = LENGTH sb0.cs_current_insts ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_stmts cx stmts) (pushed,sstart,Gstart,tnstart)
    (\H res mid G tn t. mid.gas_obs = [] /\ ?cenv''.
      stmt_lands (InLoop exit_lbl incr_lbl) sb1 res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb1 /\ cenv'' = bc_out) /\
      cenv_top_ext bc cenv'' mid.scopes /\
      stmt_state_rel H ctx func cenv'' cx mid t /\
      storage_well_formed_on cx mid (FST H) /\
      return_buf_frame d cenv'' sb1 t /\ alloca_history func t /\
      sstart.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx mid G tn t /\
      (!x w. not_fresh_at sb0 x /\ lookup_var x sstart = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP sstart.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sb0 x ==>
        FLOOKUP G x = FLOOKUP Gstart x /\
        op_taint tn (Var x) = op_taint tnstart (Var x)))
    (\H res mid gt r.
      !tail. stmt_exit_ptr (RetQ H) (mid with gas_obs := tail) res gt r)
Proof
  strip_tac >>
  `body_stmts_full_ok cx stmts` by
    (gvs[body_for_full_ok_def] >> first_x_assum irule >>
     qexistsl_tac [`ee`,`first`,`ee`] >> simp[read_result_def,return_def]) >>
  `!H. dead_lo_ok H (DF H) lo bc cx` by
    (drule bodyPtrDefsTheory.same_frame_is_ctor >>
     gvs[bodyPtrDefsTheory.dead_lo_ok_def]) >>
  irule for_full_body_fragment_normalized >> simp[] >>
  conj_tac
  >- (irule for_full_body_gas_admissible >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`ret_ty`,`shadow_func`,`shadow_sb0`,`shadow_sb1`,`stmts`] >>
  simp[] >> irule for_full_body_fragment >> simp[] >> metis_tac[]
QED
