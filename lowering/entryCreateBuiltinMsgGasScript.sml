(* The one raw GAS fetch is both the selected simulation step and the
   only possible interior native visit. Its shadow fetch is GASPRICE. *)
Theory entryCreateBuiltinMsgGas
Ancestors
  msgGasFull entryCreateCompositeFocus entryCreatePendingScope
  entryCreateFocusSpec createMarkedPath createSizePrefixReplay
  exprSimFullBundleProps s1PrefixDefs gasExplicitSites gasShadow
  msgGasOrigin msgGasPost msgGasSim bodyPtrEnvBuiltinsGas exprSimAbiGasBridge
  bodyFullGhostFrame gasOracleReplay gasEvents gasStorage gasOutcomeFull gasSummary
  exprSimMemDefs exprSimIfExp exprSimProps exprSimHypsDefs vyperStorageTrace
  fragGasOrigin fragGasOriginPtr emitHelper fragExec abiEncoderProps
  exprLowering compileEnv loweringPosts entryCreateCompletedCut
  vyperInterpreter vyperTypeSystem vyperAST vyperState context bodyPtrDefs
  ptrDiscipline exprSimStack
  venomInst venomState venomExecSemantics relation pred_set list

Theorem msg_gas_one_step[local]:
  compile_env_var MsgGas sa = (Var out,sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ create_operand_at sa s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id GAS [] [out]) /\
  (func.fn_name,id) IN E /\ gas_prefix 1 s.vs_gas_readings = [w] ==>
  create_operand_full_scope sa sb E ctx func s [T]
    (OK (update_var out w (s with
      <|vs_gas_readings := DROP 1 s.vs_gas_readings;
        vs_inst_idx := LENGTH sb.cs_current_insts|>))) /\
  !tops cx st0 source es.
    create_operand_cut sa sb E ctx func tops cx st0 source (es,s)
Proof
  strip_tac >>
  `id = sa.cs_next_id` by
    (fs[create_operand_at_def, compile_env_var_def] >>
     drule_all emit_gas_placement_id >> simp[] >> strip_tac >> gvs[mk_inst_def]) >>
  `sb.cs_next_id = SUC sa.cs_next_id /\ sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    gvs[compile_env_var_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  qabbrev_tac `i = mk_inst id GAS [] [out]` >>
  qabbrev_tac `u = update_var out w (s with vs_gas_readings := DROP 1 s.vs_gas_readings)` >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `!k. step_inst k ctx i s = OK u` by
    (mp_tac (Q.INST [`s` |-> `s`, `id` |-> `id`, `out` |-> `out`] gas_builtin_base_step) >>
     simp[Abbr `i`, Abbr `u`, step_inst_non_invoke, mk_inst_def]) >>
  `create_operand_fetch sa sb func s i` by
    (fs[create_operand_fetch_def, create_operand_at_def, frag_ids_def, Abbr `i`, mk_inst_def] >>
     gvs[]) >>
  `create_operand_at sb t /\ u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted /\
   t = update_var out w (s with <|vs_gas_readings := DROP 1 s.vs_gas_readings;
                                  vs_inst_idx := LENGTH sb.cs_current_insts|>)` by
    fs[Abbr `t`, Abbr `u`, create_operand_at_def, update_var_def] >>
  `i.inst_opcode = GAS /\ i.inst_id = id` by simp[Abbr `i`, mk_inst_def] >>
  `gas_origin_edge F E ctx func s [T] (OK t)` by
    (pure_rewrite_tac[gas_origin_edge_def] >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`0`,`bb`,`i`,`OK u`] >>
     simp[gas_events_step_def, is_terminator_def] >> gvs[Abbr `t`]) >>
  conj_tac
  >- (`create_expr_prefix sa sb E ctx func s [T] t` by
        (pure_rewrite_tac[create_expr_prefix_marked] >> irule RTC_SINGLE >>
         fs[create_marked_edge_def, create_operand_fetch_def, create_prefix_step_def,
            create_operand_at_def] >> metis_tac[]) >>
      qpat_assum `t = update_var _ _ _` (SUBST1_TAC o SYM) >>
      simp_tac bool_ss [create_operand_full_scope_def, exec_result_case_def,
                        GSYM create_operand_at_def] >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  `i.inst_opcode <> INVOKE /\ ~MEM i.inst_opcode [CREATE;CREATE2] /\
   ~is_terminator i.inst_opcode` by simp[is_terminator_def] >>
  rw[create_operand_cut_def] >>
  qpat_assum `!k. step_inst _ _ _ _ = _` (qspec_then `k` assume_tac) >>
  `create_operand_at sb (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    metis_tac[] >>
  metis_tac[create_admin_one_step_visit]
QED

Theorem msg_gas_scoped_intro[local]:
  ~s.vs_halted /\ storage_trace_frame source /\
  (storage_trace_domain cx st0 es.storage_trace ==>
   ?res t G' tn'.
     create_operand_full_scope sa sb E ctx func s [T] (OK t) /\
     (!tail. source (es with gas_obs := gas_explicit [T] s.vs_gas_readings ++ tail) =
                    (res, es with gas_obs := tail)) /\
     (!H. valid_horizon cx st0 H es.storage_trace ==>
          gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (s,G,tn) [T] (OK t,G',tn') /\
          Q H res (es with gas_obs := []) G' tn' t)) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sa sb source (es,s,G,tn) Q R
Proof
  strip_tac >> rewrite_tac[scoped_operand_outcome_def] >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- (qexists_tac `[T]` >> disj2_tac >> disj1_tac >> res_tac >>
      qexistsl_tac [`res`,`es`,`OK t`,`G'`,`tn'`] >> simp[]) >>
  qexists_tac `[]` >> disj1_tac >> conj_tac
  >- (simp[gas_bad_storage_at_def, gas_explicit_def] >> gen_tac >>
      Cases_on `source (es with gas_obs := tail)` >> simp[] >>
      `~storage_trace_domain cx st0 (es with gas_obs := tail).storage_trace` by simp[] >>
      drule_all storage_trace_frame_preserves_bad_domain >> simp[]) >>
  conj_tac >- (irule create_operand_focus_scope_caller >> qexists_tac `s` >> simp[]) >>
  qexistsl_tac [`storage_trace_horizon es.storage_trace`,`func`,`PG`,`G`,`tn`,`s`] >>
  simp[gas_origin_ptr_focus_nil]
QED

(* The same result state and ghosts serve both source interpretations. *)
Theorem msg_gas_selected[local]:
  compile_env_var MsgGas sa = (op,sb) /\
  compile_env_var GasPrice sha = (shadow_op,shb) /\
  expr_sim_full_code (ctx,shctx,func,shfunc) (sa,sb,sha,shb) /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ create_operand_at sa s /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at (DF H) lo d ce cx es G tn s) ==>
  ?w t G' tn'.
    create_operand_full_scope sa sb (gas_explicit_sites ctx shctx) ctx func s [T] (OK t) /\
    (!tops source st0 es. create_operand_cut sa sb (gas_explicit_sites ctx shctx)
       ctx func tops cx st0 source (es,s)) /\
    gas_explicit [T] s.vs_gas_readings = [w] /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
        (s,G,tn) [T] (OK t,G',tn') /\
      expr_sim_full_post (DF,lo,d,ctx,func) ce cx (Builtin (env_item_type MsgGas) (Env MsgGas) [])
        (es,sa,sb,s,op,G,tn) H (INL (IntV (&w2n w)) : value + exception)
        (es with gas_obs := []) G' tn' t)
Proof
  simp_tac bool_ss [expr_sim_full_code_def, create_operand_at_def] >> strip_tac >>
  drule_all msg_gas_canonical_placement >> strip_tac >> gvs[] >>
  drule_all msg_gas_full_witness >> strip_tac >>
  qabbrev_tac `i = mk_inst id' GAS [] [out]` >>
  qabbrev_tac `u = update_var out w (s with vs_gas_readings := DROP 1 s.vs_gas_readings)` >>
  qabbrev_tac `t = update_var out w (s with
      <|vs_gas_readings := DROP 1 s.vs_gas_readings;
        vs_inst_idx := LENGTH sb.cs_current_insts|>)` >>
  `create_operand_at sa s` by simp[create_operand_at_def] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME (mk_inst id GAS [] [out])` by simp[] >>
  drule_all msg_gas_one_step >> strip_tac >>
  qexistsl_tac [`w`,`t`,`step_prov PG G i u`,`step_taint i s u tn`] >>
  simp_tac bool_ss [gas_explicit_def] >> simp[Abbr `t`] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!D lo d cx es G0 tn0 PG. _` (drule_then (qspec_then `PG` strip_assume_tac)) >>
  drule_all msg_gas_post_frame >> disch_then (qspec_then `w` assume_tac) >>
  simp[expr_sim_full_post_def, expr_sim_full_endpoint_def, Abbr `i`, Abbr `u`,
       post_value_type_def, expr_store_bound_word, expr_type_def, env_item_type_def,
       is_word_type_def, update_var_def, allocas_below_fmp_def] >>
  Cases_on `ctx_has_dalloca ctx` >>
  gvs[update_var_def, allocas_below_fmp_def, env_item_type_def] >>
  first_assum ACCEPT_TAC
QED

Theorem msg_gas_value_site[local]:
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
    (Builtin (env_item_type MsgGas) (Env MsgGas) []) es
    (st0,sa,sb,sha,shb,op,s,G,tn) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
    (cx_tops cx) cx st0 sa sb
    (bind (eval_expr cx (Builtin (env_item_type MsgGas) (Env MsgGas) [])) (read_result cx))
    (es,s,G,tn)
    (expr_sim_full_post (DF,lo,d,ctx,func) ce cx
      (Builtin (env_item_type MsgGas) (Env MsgGas) []) (es,sa,sb,s,op,G,tn))
    (create_operand_exit_post ctx cx) /\
  create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
    (bind (eval_expr cx (Builtin (env_item_type MsgGas) (Env MsgGas) [])) (read_result cx)) (es,s)
Proof
  simp_tac bool_ss [expr_sim_full_pre_def, GSYM expr_sim_full_code_def,
                    gas_shadow_expr_def, gas_shadow_builtin_def, MAP] >> strip_tac >>
  imp_res_tac lower_value_env >>
  `expr_sim_full_code (ctx,shctx,func,shfunc) (sa,sb,sha,shb)` by simp[expr_sim_full_code_def] >>
  `create_operand_at sa s` by simp[create_operand_at_def] >>
  drule_all (INST_TYPE [alpha |-> ``:value``] msg_gas_selected) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  reverse conj_tac >- simp[] >>
  irule msg_gas_scoped_intro >>
  simp[storage_trace_frame_bind, evaluate_storage_trace_frame, storage_trace_frame_read_result] >>
  strip_tac >> qexistsl_tac [`INL (IntV (&w2n w))`,`t`,`G'`,`tn'`] >>
  simp[msg_gas_source]
QED

Theorem msg_gas_vv_post[local]:
  expr_sim_full_post (DF,lo,d,ctx,func) ce cx (Builtin (env_item_type MsgGas) (Env MsgGas) [])
    (es,sa,sb,s,Var out,G,tn) H (INL v : value + exception) ee G' tn' t ==>
  create_operand_vv_post (DF,lo,d,ctx,func) ce cx (Builtin (env_item_type MsgGas) (Env MsgGas) [])
    (es,sa,sb,s,StackValue (env_item_type MsgGas) (Var out),G,tn)
    H (INL (Value v) : eval_result + exception) ee G' tn' t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  simp[expr_sim_full_post_def, expr_sim_full_endpoint_def, post_value_type_def, expr_type_def] >>
  strip_tac >> drule_at (Pos last) vv_post_of_expr_post >>
  simp[post_value_type_def, expr_type_def] >> strip_tac >>
  gvs[create_operand_vv_post_def, post_value_type_def, expr_type_def, vv_store_bound_stack_word,
      env_item_type_def, is_word_type_def, ptr_vv_ok_def, ptr_val_ok_def, vv_location_def,
      read_result_def, return_def]
QED

(* The compile environment is arbitrary, including the actual shadow one. *)
Theorem msg_gas_stack_compile[local]:
  (it = MsgGas \/ it = GasPrice) ==>
  compile_expr ce ty (Builtin ann (Env it) []) a =
    as_stack_val ann (compile_env_var it a)
Proof
  strip_tac >> gvs[compile_expr_def, compile_builtin_dispatch_body_def, expr_type_def]
QED

Theorem msg_gas_vv_site[local]:
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
    (Builtin (env_item_type MsgGas) (Env MsgGas) []) es
    (st0,sa,sb,sha,shb,vv,s,G,tn) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
    (cx_tops cx) cx st0 sa sb (eval_expr cx (Builtin (env_item_type MsgGas) (Env MsgGas) []))
    (es,s,G,tn)
    (\H res ee G' tn' t.
       create_operand_vv_post (DF,lo,d,ctx,func) ce cx
         (Builtin (env_item_type MsgGas) (Env MsgGas) []) (es,sa,sb,s,vv,G,tn)
         H res ee G' tn' t /\
       t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (create_operand_exit_post ctx cx) /\
  create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
    (eval_expr cx (Builtin (env_item_type MsgGas) (Env MsgGas) [])) (es,s)
Proof
  simp_tac bool_ss [expr_vv_sim_full_pre_def, GSYM expr_sim_full_code_def,
                    gas_shadow_expr_def, gas_shadow_builtin_def, MAP,
                    msg_gas_stack_compile] >> strip_tac >>
  Cases_on `compile_env_var MsgGas sa` >> Cases_on `compile_env_var GasPrice sha` >>
  gvs[as_stack_val_def] >>
  rename [`compile_env_var MsgGas sa = (raw_op,sb)`,
          `compile_env_var GasPrice sha = (_,shb)`] >>
  `expr_sim_full_code (ctx,shctx,func,shfunc) (sa,sb,sha,shb)` by simp[expr_sim_full_code_def] >>
  `create_operand_at sa s` by simp[create_operand_at_def] >>
  drule_all msg_gas_canonical_placement >> strip_tac >> gvs[] >>
  drule_all (INST_TYPE [alpha |-> ``:eval_result``] msg_gas_selected) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  reverse conj_tac >- simp[] >>
  irule msg_gas_scoped_intro >> simp[evaluate_storage_trace_frame] >> strip_tac >>
  qexistsl_tac [`INL (Value (IntV (&w2n w)))`,`t`,`G'`,`tn'`] >> simp[] >>
  conj_tac
  >- (gen_tac >>
      mp_tac (Q.INST [`e` |-> `Builtin (env_item_type MsgGas) (Env MsgGas) []`]
                     eval_expr_force_value) >>
      (impl_tac >- metis_tac[exprLoweringPropsTheory.eval_expr_builtin_value]) >>
      disch_then (qspecl_then [`es with gas_obs := w::tail`, `INL (IntV (&w2n w))`,
                              `es with gas_obs := tail`] mp_tac) >>
      simp[msg_gas_source]) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule msg_gas_vv_post >> simp[]
QED

Theorem create_msg_gas_case:
  expr_body_pre ce cx env (Builtin ann (Env MsgGas) args) es ==>
  (!st0 sa sb sha shb op s G tn.
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
      (Builtin ann (Env MsgGas) args) es (st0,sa,sb,sha,shb,op,s,G,tn) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
      (cx_tops cx) cx st0 sa sb (bind (eval_expr cx (Builtin ann (Env MsgGas) args)) (read_result cx))
      (es,s,G,tn)
      (expr_sim_full_post (DF,lo,d,ctx,func) ce cx
        (Builtin ann (Env MsgGas) args) (es,sa,sb,s,op,G,tn))
      (create_operand_exit_post ctx cx) /\
    create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
      (bind (eval_expr cx (Builtin ann (Env MsgGas) args)) (read_result cx)) (es,s)) /\
  (!st0 sa sb sha shb vv s G tn.
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
      (Builtin ann (Env MsgGas) args) es (st0,sa,sb,sha,shb,vv,s,G,tn) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
      (cx_tops cx) cx st0 sa sb (eval_expr cx (Builtin ann (Env MsgGas) args)) (es,s,G,tn)
      (\H res ee G' tn' t.
         create_operand_vv_post (DF,lo,d,ctx,func) ce cx
           (Builtin ann (Env MsgGas) args) (es,sa,sb,s,vv,G,tn) H res ee G' tn' t /\
         t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (create_operand_exit_post ctx cx) /\
    create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
      (eval_expr cx (Builtin ann (Env MsgGas) args)) (es,s))
Proof
  strip_tac >>
  `args = [] /\ ann = env_item_type MsgGas` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> drule msg_gas_value_site >> simp[]) >>
  rpt gen_tac >> strip_tac >> drule msg_gas_vv_site >> simp[]
QED
