(* Invoke the linked list judgment at the paired declared Array body cut. *)
Theory bodyForArrayDeclaredRunMods
Ancestors
  bodyForEntryInputsMods bodyFullPredsMods bodyFullPostsMods
  bodyFullShadowBodyInv bodyInvCodeProps bodySim exprSimHypsDefs
  gasShadowStmtEnv gasShadowCompileStmtBase
  supportedStmts supportedStmtTraverse vyperSubscriptOverlap vyperTypeCallGraph
  vyperTypeCallStackSoundness stmtSimProps loweringPosts freshWrites compileEnv
  finite_map list

val _ = Parse.hide "body";

Theorem array_body_frame_components[local]:
  same_frame c bc ==>
  bc.ce_module_vars = c.ce_module_vars /\ bc.ce_return_buf = c.ce_return_buf /\
  bc.ce_modules = c.ce_modules /\ bc.ce_is_ctor = c.ce_is_ctor
Proof
  simp[same_frame_def, compile_env_component_equality]
QED

Theorem array_declared_body_checks[local]:
  supported_stmt tops bindings (For id typ (Array e) n body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ (Array e) n body) ==>
      EXISTS (occurs_abi_decode_target target o SND) mods) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root c env)
    (For id typ (Array e) n body) /\
  (!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
      (vyperSubscriptOverlap$accesses_stmt (For id typ (Array e) n body)) /\
      IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
      IS_SOME (FLOOKUP c.ce_module_vars key)) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n body)) /\
  same_frame c bc ==>
  supported_stmts tops bindings body /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
      EXISTS (occurs_abi_decode_target target o SND) mods) /\
  ~supported_stmts_expr_exists (unallocated_bare_global_root bc (extend_local env id typ F)) body /\
  (!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
      (vyperSubscriptOverlap$accesses_stmts body) /\
      IS_SOME (FLOOKUP (extend_local env id typ F).bare_global_assignable key) ==>
      IS_SOME (FLOOKUP bc.ce_module_vars key)) /\
  call_evaluation_safe cx (int_calls_stmts body)
Proof
  strip_tac >> drule_then strip_assume_tac array_body_frame_components >>
  conj_tac >- (drule supported_loop_body_contract >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> simp[Once supported_stmt_expr_exists_def]) >>
  `unallocated_bare_global_root bc (extend_local env id typ F) =
   unallocated_bare_global_root c env` by
    (simp[FUN_EQ_THM] >> Cases >> simp[unallocated_bare_global_root_def]) >>
  conj_tac
  >- (qpat_assum `~supported_stmt_expr_exists _ (For _ _ _ _ _)`
        (mp_tac o ONCE_REWRITE_RULE [supported_stmt_expr_exists_def]) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> simp[] >> first_x_assum irule >>
      fs[Once accesses_stmt_def, extend_local_bare_globals]) >>
  qpat_assum `call_evaluation_safe cx (int_calls_stmt _)`
    (mp_then Any ACCEPT_TAC call_evaluation_safe_append_right o
     ONCE_REWRITE_RULE [int_calls_stmt_def])
QED

Theorem array_paired_body_env[local]:
  stmts_env bc lctx ret_ty body sbCopy = (bc_out,sbBody) /\
  compile_stmts (gas_shadow_env T bc) lctx ret_ty (MAP gas_shadow_stmt body)
    shadow_sbCopy = ((),shadow_sbBody) /\
  gas_shadow_state sbCopy shadow_sbCopy ==>
  stmts_env (gas_shadow_env T bc) lctx ret_ty (MAP gas_shadow_stmt body)
    shadow_sbCopy = (gas_shadow_env T bc_out,shadow_sbBody) /\
  gas_shadow_state sbBody shadow_sbBody
Proof
  strip_tac >>
  qspecl_then [`body`,`bc`,`lctx`,`ret_ty`]
    (mp_tac o REWRITE_RULE [gas_shadow_compiles_env_def])
    (Q.INST [`sd` |-> `T`] gas_shadow_stmts_env_env) >>
  disch_then (qspecl_then [`sbCopy`,`shadow_sbCopy`] mp_tac) >>
  gvs[compile_stmts_env, pairTheory.PAIR_EQ] >>
  metis_tac[pairTheory.PAIR]
QED

Theorem for_array_declared_body_run_mods:
  declare_local c id typ saLen = (bc,saD) /\
  contract_inv mods exps ctx c cx /\ module_body_inv mods src tops c cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  supported_stmt tops bindings (For id typ (Array e) n body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ (Array e) n body) ==>
      EXISTS (occurs_abi_decode_target target o SND) mods) /\
  ce_locals_declared c env /\ locals_alloc_ok c env /\
  type_stmt env ret_ty (For id typ (Array e) n body) = SOME env' /\
  stmt_exprs_ok c (For id typ (Array e) n body) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root c env)
    (For id typ (Array e) n body) /\
  (!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
      (vyperSubscriptOverlap$accesses_stmt (For id typ (Array e) n body)) /\
      IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
      IS_SOME (FLOOKUP c.ce_module_vars key)) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n body)) /\
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ c ret_ty /\
  body_stmts_full_ok_mods mods exps cx body /\
  body_const_cells_agree_mods mods cx (extend_local env id typ F) ep /\
  expr_sim_inv_mods mods bc cx (extend_local env id typ F) ep /\
  stmts_env bc (InLoop exit incr) ret_ty body sbCopy = (bc_out,sbBody) /\
  compile_stmts (gas_shadow_env T bc) (InLoop exit incr) ret_ty (MAP gas_shadow_stmt body)
    shadow_sbCopy = ((),shadow_sbBody) /\
  gas_shadow_state sbCopy shadow_sbCopy /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sbCopy sbBody func /\ fn_has_code shadow_sbCopy shadow_sbBody shadow_func /\
  (!H. dead_lo_ok_mods H (DF H) lo c cx) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved bc sbCopy /\ ret_pc_ok bc sbCopy z /\
  sa.cs_next_var <= sbCopy.cs_next_var /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~block_is_terminated sbCopy /\
  gas_admissible (eval_stmts cx body) (stmt_res_ok (InLoop exit incr)) ep /\
  return_buf_frame d bc sbCopy z /\ return_buf_sep d bc ep z /\
  alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  (!fn inst q. frag_reachable ctx func z fn inst q ==> dalloca_fmp_headroom inst q) /\
  (!H. valid_horizon cx st0 H ep.storage_trace ==>
    stmt_state_rel H ctx func bc cx ep z /\ immutable_frame_mods func bc cx ep z /\
    storage_well_formed_on cx ep (FST H) /\ ghost_inv_at_mods (DF H) lo d bc cx ep Gf tf z) /\
  ~z.vs_halted /\ z.vs_current_bb = sbCopy.cs_current_bb /\
  z.vs_inst_idx = LENGTH sbCopy.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) mods cx st0
    (eval_stmts cx body) (ep,z,Gf,tf)
    (\H raw pre G1 tn1 t. ?cb.
      stmt_lands (InLoop exit incr) sbBody raw t /\ ~t.vs_halted /\
      (raw = INL () ==> ~block_is_terminated sbBody /\ cb = bc_out) /\
      cenv_top_ext bc cb pre.scopes /\
      stmt_state_rel H ctx func cb cx pre t /\ immutable_frame_mods func cb cx pre t /\
      storage_well_formed_on cx pre (FST H) /\ return_buf_frame d cb sbBody t /\
      alloca_history func t /\ return_buf_sep d cb pre t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ z.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cb cx pre G1 tn1 t /\
      (!x w. not_fresh_at sbCopy x /\ lookup_var x z = SOME w ==> lookup_var x t = SOME w) /\
      (!a b. FLOOKUP z.vs_allocas a = SOME b ==> FLOOKUP t.vs_allocas a = SOME b) /\
      (!x. not_fresh_at sbCopy x ==>
           FLOOKUP G1 x = FLOOKUP Gf x /\ op_taint tn1 (Var x) = op_taint tf (Var x)) /\
      alloca_frame bc ep sbCopy z cb pre t /\
      (!aid off sz i. FLOOKUP z.vs_allocas aid = SOME (off,sz) /\ aid < sbCopy.cs_next_id /\
         (!name b len. local_region bc ep.scopes z name b len ==>
                       off + sz <= b \/ b + len <= off) /\
         off <= i /\ i < off + sz /\ i IN tn1.t_mem ==> i IN tf.t_mem))
    (\H raw pre gt r.
      (!tail. stmt_exit_ptr (RetQ H) (pre with gas_obs := tail) raw gt r) /\
      halt_exit H cx pre raw r /\
      (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >>
  drule_all_then strip_assume_tac for_declared_static_inputs_mods >>
  drule_all_then strip_assume_tac array_declared_body_checks >>
  drule_all_then strip_assume_tac array_paired_body_env >>
  drule_then strip_assume_tac array_body_frame_components >>
  `stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cx (InLoop exit incr) RetQ bc
     (stmts_env bc (InLoop exit incr) ret_ty body)
     (stmts_env (gas_shadow_env T bc) (InLoop exit incr) ret_ty
       (MAP gas_shadow_stmt body)) (eval_stmts cx body) ep` by
    (qpat_assum `body_stmts_full_ok_mods _ _ _ _`
       (irule o REWRITE_RULE [body_stmts_full_ok_mods_def]) >>
     rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
     >- (qexistsl_tac [`extend_local env id typ F`,`body_env'`] >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`bindings`,`src`,`tops`] >> simp[]) >>
  `bc.ce_modules = mods` by
    (irule contract_inv_cenv_modules >> qexistsl_tac [`ctx`,`cx`,`exps`] >> first_assum ACCEPT_TAC) >>
  `!H. dead_lo_ok_mods H (DF H) lo bc cx` by
    (qpat_assum `!H. dead_lo_ok_mods H (DF H) lo c cx` mp_tac >>
     qpat_assum `bc.ce_is_ctor = c.ce_is_ctor` (fn ctor =>
       qpat_assum `bc.ce_modules = c.ce_modules` (fn modules =>
         simp[NoAsms, dead_lo_ok_mods_def, ctor, modules]))) >>
  `!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sbCopy x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!x sz. c.ce_return_buf = _ ==> _` irule >> qexists_tac `sz` >> fs[]) >>
  qpat_assum `bc.ce_modules = mods` (SUBST1_TAC o SYM) >>
  qhdtm_assum `stmt_frag_full_mods`
    (irule o REWRITE_RULE [stmt_frag_full_mods_def]) >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
  qexists_tac `shadow_sbCopy` >> simp[]
QED
