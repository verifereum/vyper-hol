(* Empty length-word initialization of a pending declaration. *)
Theory bodyIntCallFamStmtMutationEmptyInit
Ancestors
  bodyIntCallFamStmtMutationInactiveStore bodyIntCallFamStmtMutationActivate
  bodyIntCallJointContract stmtSimDeclMem valueEncodingProps
  localPtrsProps exprLoweringProps venomMemDefs venomState compileEnv
  finite_map placeMemoryCopyEffect bodyExprPreFacts stmtSimDeclSource
  stmtSimDeclCompose gasSummary exprSimSource loweringPosts stmtSimDefs bodySim
  exprSimHypsDefs vyperInterpreter vyperState vyperTypeSystem
  vyperTypeInvariants valueEncoding memoryLocalRhsProps

Theorem intcall_inactive_empty_initialize_state:
  let ee = es with scopes :=
    (sc |+ (id,<|assignable := a; type := tv;
                value := default_value tv; popped := []|>)) :: rest
  in
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  emit_void MSTORE [Var p; Lit 0w] sa = ((),sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr ce es.scopes p /\ lookup_var p s = SOME w /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
  fp.jc_lo <= w2n w /\ has_length_word ty /\
  evaluate_type tenv ty = SOME tv /\ type_memory_size tv <= sz /\
  expr_sim_inv ce fp.jc_cx env' ee /\ locals_alloc_ok ce env' /\
  ce_locals_declared ce env' ==>
  ?u. u = (mstore (w2n w) 0w s with
            vs_inst_idx := LENGTH sb.cs_current_insts) /\
      typed_copy_effect fp.jc_ctx fp.jc_func sa sb s u (w2n w) 32 /\
      intcall_joint_res fp ce env' ee sb u
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  `val_in_memory tv (default_value tv) (w2n w) (mstore (w2n w) 0w s).vs_memory /\
   val_wf tv (default_value tv) /\ 32 <= type_memory_size tv` by
    (irule memory_length_word_layout >>
     simp[mstore_mem_word_at_same] >> qexistsl [`tenv`,`ty`] >> simp[]) >>
  `!n b k. local_region ce es.scopes s n b k ==>
     regions_disjoint (w2n w) sz b k` by
    (rpt strip_tac >> irule local_ptrs_rel_alloca_disjoint >>
     qexistsl [`ce`, `fp.jc_func`, `inst`, `n`, `p`, `es.scopes`, `s`] >>
     fs[intcall_expr_res_def, stmt_state_rel_def, state_rel_def]) >>
  `32 <= sz` by decide_tac >>
  drule_all (intcall_inactive_mstore_resources |>
    Q.INST [`b` |-> `w2n w`, `k` |-> `sz`, `op` |-> `Lit 0w`, `wd` |-> `0w`] |>
    SRULE [eval_operand_def]) >>
  strip_tac >>
  qexists `mstore (w2n w) 0w s with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[] >>
  irule (intcall_declared_local_activate_resources |>
         SIMP_RULE bool_ss [LET_THM]) >>
  goal_assum (drule_at Any) >>
  fs[mstore_def, lookup_var_def] >> metis_tac[]
QED

Theorem intcall_annassign_empty_continuation:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_joint_res fp ce env es sa0 s0 /\
  supported_stmt fp.jc_tops bindings (AnnAssign id ty e) /\
  type_stmt env ret (AnnAssign id ty e) = SOME env' /\
  stmt_exprs_ok ce (AnnAssign id ty e) /\
  call_evaluation_safe fp.jc_cx (int_calls_stmt (AnnAssign id ty e)) /\
  stmt_env ce lctx ret (AnnAssign id ty e) sa0 = (c,sf) /\
  declare_local ce id ty sa0 = (c,st) /\
  gas_admissible (eval_stmt fp.jc_cx (AnnAssign id ty e)) (stmt_res_ok lctx) es /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  has_length_word ty /\ is_empty_value_expr e /\ type_memory_size tv <= sz /\
  expr_body_pre c fp.jc_cx env e es /\
  gas_marked_exec F (fp.jc_ctx,fp.jc_func) (eval_expr fp.jc_cx e)
    (es,salloc) marks (INL rv) ee (OK t) /\
  intcall_expr_cont fp c env es sa salloc (ee with gas_obs := []) sb t /\
  emit_void MSTORE [Var p;Lit 0w] sb = ((),sf) /\
  fn_has_code sb sf fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~block_is_terminated sf /\
  FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_fresh_at sa p /\ lookup_var p salloc = SOME w /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\
  FLOOKUP salloc.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
  fp.jc_lo <= w2n w ==>
  ?ff u. gas_marked_exec F (fp.jc_ctx,fp.jc_func)
    (new_variable id tv (default_value tv))
    (ee with gas_obs := [],t) [] (INL ()) ff (OK u) /\
    stmt_lands lctx sf (INL ()) u /\ ~u.vs_halted /\
    cenv_top_ext ce c ff.scopes /\
    intcall_joint_res fp c env' (ff with gas_obs := []) sf u /\
    (!x wd. not_fresh_at sa x /\ lookup_var x salloc = SOME wd ==>
            lookup_var x u = SOME wd) /\
    (!aid b. FLOOKUP salloc.vs_allocas aid = SOME b ==>
             FLOOKUP u.vs_allocas aid = SOME b) /\
    salloc.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  `well_typed_expr env e /\ type_widens_to env.type_defs (expr_type e) ty` by
    fs[type_stmt_def,AllCaseEqs()] >>
  `env.type_defs = get_tenv fp.jc_cx` by
    fs[expr_body_pre_def,expr_sim_inv_def,env_consistent_def,
       env_context_consistent_def] >>
  `!tail. eval_expr fp.jc_cx e
    (es with gas_obs := gas_explicit marks salloc.vs_gas_readings ++ tail) =
    (INL rv,ee with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  `rv = Value (default_value tv)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` assume_tac) >>
     metis_tac[memory_rhs_empty_eval_destination]) >>
  `!tail. bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
    (es with gas_obs := gas_explicit marks salloc.vs_gas_readings ++ tail) =
    (INL (default_value tv),ee with gas_obs := tail)` by
    (gen_tac >> simp[Once bind_def,read_result_def,return_def]) >>
  drule_all annassign_continuation_all_tails >> strip_tac >>
  suspend "typing"
QED

Resume intcall_annassign_empty_continuation[typing]:
  qabbrev_tac `ff = ee with scopes :=
    (sc |+ (id,<|assignable := T; type := tv;
                value := default_value tv; popped := []|>)) :: rest` >>
  `eval_stmt fp.jc_cx (AnnAssign id ty e)
     (es with gas_obs := gas_explicit marks salloc.vs_gas_readings) =
     (INL (),ff with gas_obs := [])` by
    (drule eval_annassign_action >>
     disch_then (qspecl_then [`id`,`e`] SUBST1_TAC) >>
     qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` assume_tac) >>
     fs[] >> simp[Once bind_def] >> fs[Abbr `ff`]) >>
  `expr_sim_inv ce fp.jc_cx env es /\ locals_alloc_ok ce env /\
   ce_locals_declared ce env` by
    fs[intcall_joint_res_def,intcall_expr_res_def] >>
  `supported_program fp.jc_tops /\
   get_module_code fp.jc_cx NONE = SOME fp.jc_tops /\ ce.ce_alloca_locals` by
    fs[body_inv_def] >>
  drule_all locals_alloc_ok_stmt >> strip_tac >>
  drule_all ce_locals_declared_stmt >> strip_tac >>
  `expr_sim_inv ce fp.jc_cx env
     (es with gas_obs := gas_explicit marks salloc.vs_gas_readings)` by simp[] >>
  drule_all expr_sim_inv_stmt >> strip_tac >> suspend "initialize"
QED

Resume intcall_annassign_empty_continuation[initialize]:
  `not_local_ptr c (ee with gas_obs := []).scopes p` by
    (irule local_ptrs_reserved_not_live >>
     fs[intcall_expr_cont_def,intcall_expr_res_def] >> metis_tac[]) >>
  fs[intcall_expr_cont_def] >>
  `lookup_var p t = SOME w /\
   FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,sz)` by metis_tac[] >>
  `?u. u = (mstore (w2n w) 0w t with
              vs_inst_idx := LENGTH sf.cs_current_insts) /\
       typed_copy_effect fp.jc_ctx fp.jc_func sb sf t u (w2n w) 32 /\
       intcall_joint_res fp c env' (ff with gas_obs := []) sf u` by
    (simp[Abbr `ff`] >>
     irule (intcall_inactive_empty_initialize_state |> SIMP_RULE bool_ss [LET_THM]) >>
     goal_assum (drule_at Any) >> simp[] >>
     qpat_assum `ee.scopes = _` (fn th => fs[th]) >>
     conj_tac >- (qexistsl [`get_tenv fp.jc_cx`,`ty`] >> simp[]) >>
     conj_tac >- (qexists `inst` >> simp[]) >>
     conj_tac >-
       (`!ei ss gs. ei with <|scopes := ss; gas_obs := gs|> =
           (ei with scopes := ss) with gas_obs := gs` by
          simp[evaluation_state_component_equality] >>
        pop_assum (fn th => pure_once_rewrite_tac[th]) >>
        pure_rewrite_tac[expr_sim_inv_gas_obs] >> first_assum ACCEPT_TAC) >>
     qexists `env` >> simp[]) >>
  suspend "framing"
QED

Resume intcall_annassign_empty_continuation[framing]:
  drule typed_copy_effect_endpoint >> strip_tac >>
  qexistsl [`ff`,`u`] >>
  conj_tac >-
    (simp[gas_marked_exec_def,gas_explicit_def] >>
     metis_tac[typed_copy_effect_path]) >>
  simp[stmt_lands_def] >>
  conj_tac >-
    (simp[Abbr `ff`] >> irule cenv_top_ext_declare_local >>
     simp[] >> qexistsl [`id`,`sa0`,`st`,`ty`] >>
     fs[lookup_scopes_def,ce_locals_declared_def,type_stmt_def,AllCaseEqs()] >>
     conj_tac >-
       (rpt strip_tac >>
        qpat_x_assum `!n l. FLOOKUP ce.ce_vars n = SOME l ==> _`
          (drule_then assume_tac) >> fs[]) >>
     qpat_x_assum `lookup_scopes id ee.scopes = NONE` mp_tac >>
     qpat_assum `ee.scopes = _` (fn th => rewrite_tac[th]) >>
     Cases_on `FLOOKUP sc id` >> simp[lookup_scopes_def]) >>
  simp[mstore_def,lookup_var_def] >> metis_tac[lookup_var_def]
QED

Finalise intcall_annassign_empty_continuation
