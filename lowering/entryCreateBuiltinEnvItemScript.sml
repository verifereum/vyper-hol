(* Ordinary environment reads and PrevHash own straight-line bands. *)
Theory entryCreateBuiltinEnvItem
Ancestors
  bodyFullBuiltinEnvReads bodyFullBuiltinEnvPrevHash entryCreateAdminSequence
  entryIntCallStageNeutral exprSimFullBundleProps s1PrefixDefs entryCreateFocusSpec
  entryCreateCompletedCut exprSimStack exprSimIfExp exprSimProps exprLoweringProps
  gasShadow gasSummary fragExec emitHelper vyperInterpreter vyperStorageTrace abiEncoderProps
  vyperTypeSystem vyperAST vyperState compileEnv exprLowering loweringPosts
  bodyPtrDefs exprSimMemDefs context exprSimHypsDefs venomState venomInst venomExecSemantics pred_set list rich_list arithmetic

Triviality env_item_band:
  item <> MsgGas /\ compile_env_var item sa = (op,sb) ==>
  (?x. op = Var x) /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_id IN frag_ids sa sb /\ i.inst_opcode <> INVOKE /\
     i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
     i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts sa sb)
Proof
  strip_tac >> Cases_on `item` >>
  gvs[compile_env_var_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >>
  simp[frag_ids_def, mk_inst_def, is_terminator_def]
QED

Triviality env_item_vv_compile:
  compile_expr ce ty (Builtin (env_item_type item) (Env item) []) sa =
  as_stack_val (env_item_type item) (compile_env_var item sa)
Proof
  simp[Once compile_expr_def, compile_expr_def, compile_builtin_dispatch_body_def, expr_type_def]
QED

Triviality env_item_word:
  is_word_type (env_item_type item)
Proof
  Cases_on `item` >> simp[env_item_type_def,is_word_type_def]
QED

Triviality env_item_value_selected:
  item <> MsgGas /\
  expr_sim_full_hypotheses (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
    (Builtin (env_item_type item) (Env item) []) es (st0,sa,sb,sha,shb,op,s,G,tn) /\
  storage_trace_domain cx st0 es.storage_trace ==>
  ?v t G' tn'.
    create_operand_full_scope sa sb (gas_explicit_sites ctx shctx) ctx func s [] (OK t) /\
    (!tail. bind (eval_expr cx (Builtin (env_item_type item) (Env item) []))
       (read_result cx) (es with gas_obs := tail) = (INL v,es with gas_obs := tail)) /\
    !H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
        (s,G,tn) [] (OK t,G',tn') /\
      expr_sim_full_post (DF,lo,d,ctx,func) ce cx
        (Builtin (env_item_type item) (Env item) []) (es,sa,sb,s,op,G,tn)
        H (INL v : value + exception) (es with gas_obs := []) G' tn' t
Proof
  strip_tac >>
  `?raw v G' tn'. run_inst_seq (emitted_insts sa sb) s = OK raw /\
    (!tail. bind (eval_expr cx (Builtin (env_item_type item) (Env item) []))
       (read_result cx) (es with gas_obs := tail) = (INL v,es with gas_obs := tail)) /\
    !H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
        (s,G,tn) [] (OK (raw with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn') /\
      expr_sim_full_post (DF,lo,d,ctx,func) ce cx
        (Builtin (env_item_type item) (Env item) []) (es,sa,sb,s,op,G,tn)
        H (INL v : value + exception) (es with gas_obs := []) G' tn'
        (raw with vs_inst_idx := LENGTH sb.cs_current_insts)` by
      (Cases_on `item = PrevHash` >> gvs[]
       >- (drule_all env_prevhash_value_run >> simp[]) >>
       drule_all env_reads_value_run >> simp[]) >>
  fs[expr_sim_full_hypotheses_def, expr_sim_full_code_def] >>
  drule lower_value_env >> strip_tac >> drule_all env_item_band >> strip_tac >>
  qexistsl_tac [`raw with vs_inst_idx := LENGTH sb.cs_current_insts`,`G'`,`tn'`] >>
  conj_tac
  >- (irule create_admin_sequence_scope >> simp[create_operand_at_def] >> fs[EVERY_MEM]) >>
  simp[]
QED

Triviality env_item_cut:
  item <> MsgGas /\ compile_env_var item sa = (op,sb) /\ fn_has_code sa sb func /\
  create_operand_at sa s ==>
  create_operand_cut sa sb E ctx func tops cx st0 source (es,s)
Proof
  strip_tac >> drule_all env_item_band >> strip_tac >>
  irule create_admin_sequence_cut >> simp[] >> fs[EVERY_MEM]
QED

Triviality env_item_vv_post:
  expr_sim_full_post (DF,lo,d,ctx,func) ce cx (Builtin (env_item_type item) (Env item) [])
    (es,sa,sb,s,Var x,G,tn) H (INL v : value + exception) ee G' tn' t ==>
  create_operand_vv_post (DF,lo,d,ctx,func) ce cx (Builtin (env_item_type item) (Env item) [])
    (es,sa,sb,s,StackValue (env_item_type item) (Var x),G,tn)
    H (INL (Value v) : eval_result + exception) ee G' tn' t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  simp[expr_sim_full_post_def, expr_sim_full_endpoint_def, post_value_type_def, expr_type_def,
       env_item_word] >>
  strip_tac >> drule_at (Pos last) vv_post_of_expr_post >>
  simp[post_value_type_def, expr_type_def,env_item_word] >> strip_tac >>
  gvs[create_operand_vv_post_def, post_value_type_def, expr_type_def, vv_store_bound_stack_word,
      env_item_word, ptr_vv_ok_def, ptr_val_ok_def, vv_location_def,read_result_def,return_def]
QED

(* Both sites are handled by the same pure, but nonempty, selected execution. *)
Triviality env_item_scoped_landing:
  storage_trace_frame source /\ ~s.vs_halted /\
  (storage_trace_domain cx st0 es.storage_trace ==>
   ?res t G' tn'.
     create_operand_full_scope sa sb E ctx func s [] (OK t) /\
     (!tail. source (es with gas_obs := tail) = (res,es with gas_obs := tail)) /\
     !H. valid_horizon cx st0 H es.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
       Q H res (es with gas_obs := []) G' tn' t) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sa sb source (es,s,G,tn) Q R
Proof
  strip_tac >> irule stage_scoped_initial_domain >> simp[] >> strip_tac >> res_tac >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`,`es`,`OK t`,`G'`,`tn'`] >> simp[gas_explicit_def] >> metis_tac[]
QED

Triviality env_item_value_site:
  item <> MsgGas /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
    (Builtin (env_item_type item) (Env item) []) es (st0,sa,sb,sha,shb,op,s,G,tn) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
    (cx_tops cx) cx st0 sa sb
    (bind (eval_expr cx (Builtin (env_item_type item) (Env item) [])) (read_result cx)) (es,s,G,tn)
    (expr_sim_full_post (DF,lo,d,ctx,func) ce cx
      (Builtin (env_item_type item) (Env item) []) (es,sa,sb,s,op,G,tn))
    (create_operand_exit_post ctx cx) /\
  create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
    (bind (eval_expr cx (Builtin (env_item_type item) (Env item) [])) (read_result cx)) (es,s)
Proof
  strip_tac >>
  `expr_sim_full_hypotheses (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
    (Builtin (env_item_type item) (Env item) []) es (st0,sa,sb,sha,shb,op,s,G,tn)` by
    (simp_tac bool_ss [expr_sim_full_hypotheses_def,expr_sim_full_code_def] >>
     fs[expr_sim_full_pre_def] >> metis_tac[]) >>
  fs[expr_sim_full_pre_def] >>
  reverse conj_tac
  >- (drule lower_value_env >> strip_tac >> irule env_item_cut >>
      simp[create_operand_at_def] >> metis_tac[]) >>
  irule env_item_scoped_landing >>
  simp[storage_trace_frame_bind,evaluate_storage_trace_frame,storage_trace_frame_read_result] >>
  strip_tac >> drule_all env_item_value_selected >> strip_tac >>
  qexistsl_tac [`INL v`,`t`,`G'`,`tn'`] >> simp[]
QED

Triviality env_item_vv_site:
  item <> MsgGas /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
    (Builtin (env_item_type item) (Env item) []) es (st0,sa,sb,sha,shb,vv,s,G,tn) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
    (cx_tops cx) cx st0 sa sb
    (eval_expr cx (Builtin (env_item_type item) (Env item) [])) (es,s,G,tn)
    (\H res ee G' tn' t.
      create_operand_vv_post (DF,lo,d,ctx,func) ce cx
        (Builtin (env_item_type item) (Env item) []) (es,sa,sb,s,vv,G,tn) H res ee G' tn' t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (create_operand_exit_post ctx cx) /\
  create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
    (eval_expr cx (Builtin (env_item_type item) (Env item) [])) (es,s)
Proof
  simp_tac bool_ss [expr_vv_sim_full_pre_def,gas_shadow_expr_def,gas_shadow_builtin_def,MAP] >>
  strip_tac >> fs[env_item_vv_compile] >>
  Cases_on `compile_env_var item sa` >> Cases_on `compile_env_var item sha` >>
  gvs[as_stack_val_def] >>
  rename1 `compile_env_var item sa = (op,sb)` >>
  reverse conj_tac
  >- (irule env_item_cut >> simp[create_operand_at_def] >> metis_tac[]) >>
  irule env_item_scoped_landing >> simp[evaluate_storage_trace_frame] >> strip_tac >>
  qabbrev_tac `e = Builtin (env_item_type item) (Env item) []` >>
  `!ss tv ee. eval_expr cx e ss = (INL tv,ee) ==> ?v. tv = Value v` by
    (simp[Abbr `e`] >> metis_tac[eval_expr_builtin_value]) >>
  `gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (fs[Abbr `e`] >> drule_all eval_expr_force_admissible >> simp[]) >>
  `expr_sim_full_hypotheses (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
     e es (st0,sa,sb,sha,shb,op,s,G,tn)` by
    (simp[expr_sim_full_hypotheses_def,expr_sim_full_code_def,Abbr `e`,
          gas_shadow_expr_def,gas_shadow_builtin_def] >>
     rpt conj_tac
     >- simp[lower_value_def,env_item_vv_compile,as_stack_val_def,comp_bind_def,unwrap_value_def,comp_return_def]
     >- simp[lower_value_def,env_item_vv_compile,as_stack_val_def,comp_bind_def,unwrap_value_def,comp_return_def] >>
     metis_tac[]) >>
  qpat_x_assum `expr_sim_full_hypotheses _ _ _ _ e _ _` mp_tac >>
  simp_tac bool_ss [Abbr `e`] >> strip_tac >>
  drule_all env_item_value_selected >> strip_tac >>
  qexistsl_tac [`INL (Value v)`,`t`,`G'`,`tn'`] >> simp[] >>
  conj_tac
  >- (gen_tac >> qpat_assum `!ss tv ee. _` (mp_tac o MATCH_MP eval_expr_force_value) >>
      disch_then (qspecl_then [`es with gas_obs := tail`,`INL v`,`es with gas_obs := tail`] mp_tac) >>
      simp[]) >>
  `?x. op = Var x` by metis_tac[env_item_band] >> gvs[] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule env_item_vv_post >> simp[]
QED

Theorem create_builtin_env_item_cases:
  item <> MsgGas /\ expr_body_pre ce cx env (Builtin ann (Env item) args) es ==>
  (!st0 sa sb sha shb op s G tn.
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
      (Builtin ann (Env item) args) es (st0,sa,sb,sha,shb,op,s,G,tn) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
      (cx_tops cx) cx st0 sa sb (bind (eval_expr cx (Builtin ann (Env item) args)) (read_result cx))
      (es,s,G,tn)
      (expr_sim_full_post (DF,lo,d,ctx,func) ce cx
        (Builtin ann (Env item) args) (es,sa,sb,s,op,G,tn))
      (create_operand_exit_post ctx cx) /\
    create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
      (bind (eval_expr cx (Builtin ann (Env item) args)) (read_result cx)) (es,s)) /\
  (!st0 sa sb sha shb vv s G tn.
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
      (Builtin ann (Env item) args) es (st0,sa,sb,sha,shb,vv,s,G,tn) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
      (cx_tops cx) cx st0 sa sb (eval_expr cx (Builtin ann (Env item) args)) (es,s,G,tn)
      (\H res ee G' tn' t.
         create_operand_vv_post (DF,lo,d,ctx,func) ce cx
           (Builtin ann (Env item) args) (es,sa,sb,s,vv,G,tn) H res ee G' tn' t /\
         t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (create_operand_exit_post ctx cx) /\
    create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
      (eval_expr cx (Builtin ann (Env item) args)) (es,s))
Proof
  strip_tac >>
  `args = [] /\ ann = env_item_type item` by
    gvs[expr_body_pre_def,cj 9 well_typed_expr_def,well_typed_builtin_app_def] >>
  gvs[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all env_item_value_site >> simp[]) >>
  rpt gen_tac >> strip_tac >> drule_all env_item_vv_site >> simp[]
QED
