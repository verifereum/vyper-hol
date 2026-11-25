(* The reached start and length of a code Slice, before any code access. *)
Theory bodySliceCodeTailMods
Ancestors
  bodyReachedWordResultBindMods bodySliceCodeOperandPreMods bodySliceWordEntryMods
  bodySliceSavedWordsMods bodyWordModSourceCutsMods bodyFullPredsMods
  bodyFullPostsMods exprSimFullBundleProps bodyFullIfExpReach exprLoweringProps
  exprBodyPreProps exprSimWordArgs exprSimDefs exprSimHypsDefs vyperStorageTrace
  vyperStorageFootprint vyperState compileEnv vyperInterpreter
Libs monadsyntax

val wp = ``\e es sa sb s0 ee v op t G0 tn0 G tn (H:(bool # 256 word # type_value) list # num list).
  expr_post_mods H ctx func cenv cx e es sa sb s0 ee v op t /\
  expr_store_bound cx (expr_type e) v op t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  ~t.vs_halted /\ ee.gas_obs = [] /\
  (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)``;

val cut = ``\e es sa sb s0 ee v op t G0 tn0 G tn marks.
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL v,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ^wp e es sa sb s0 ee v op t G0 tn0 G tn H)``;

val entry = ``\es sa s0 G0 tn0.
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts``;

val child = ``\ty e sa sb sha shb op.
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) sha = (op,shb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,sha,shb) /\
  sa.cs_next_var <= sb.cs_next_var``;

val forced = ``\e. bind (eval_expr cx e) (read_result cx)``;
val outcome = ``\(source : evaluation_state -> eval_result evaluation_result).
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 source``;
val exit_weaken = ``!(H : (bool # 256 word # type_value) list # num list)
  (res : eval_result + vyperState$exception) ee
  (gt : (string |-> num # num) # taint) r. expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u) ==> R H res ee gt r``;
val saved = ``\x y s2 t2 G2 tn2 v1 v2.
  eval_operand x t2 = SOME (val_to_w256 v1) /\
  eval_operand y t2 = SOME (val_to_w256 v2) /\
  op_prov G2 x = NONE /\ op_prov G2 y = NONE /\
  op_taint tn2 x = {} /\ op_taint tn2 y = {} /\
  (!q. x = Var q ==> not_fresh_at s2 q) /\
  (!q. y = Var q ==> not_fresh_at s2 q) /\
  (!l. x <> Label l) /\ (!l. y <> Label l)``;

Triviality slice_cons_value_sim:
  body_exprs_full_ok_mods mods exps cx (e::rest) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  simp[Once body_exprs_full_ok_mods_def] >> strip_tac >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ e`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
   expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
    (qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
       _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ expr_vv_sim_full_mods _ _ _ _ _ _` irule >>
     simp[] >> conj_tac >- (qexistsl_tac [`src`,`tops`] >> simp[]) >>
     qexists_tac `env` >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Triviality slice_vv_exception_ok:
  !exc. expr_vv_res_ok (INR exc) ==> expr_res_ok (INR exc)
Proof
  simp[expr_vv_res_ok_def,expr_res_ok_def]
QED

Triviality slice_cons_bind:
  body_exprs_full_ok_mods mods exps cx (e::rest) /\ expr_type e = BaseT (UintT 256) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es /\
  ^child ty e sa sb sha shb op /\ ^entry es sa s0 G0 tn0 /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  gas_admissible (bind (^forced e) next) expr_vv_res_ok es /\
  (!v. storage_trace_frame (next v)) /\ ^exit_weaken /\
  (!marks v ee G tn t.
    ^cut e es sa sb s0 ee v op t G0 tn0 G tn marks /\
    v = IntV (&w2n (val_to_w256 v)) /\
    body_exprs_full_ok_mods mods exps cx rest /\ expr_sim_inv_mods mods cenv cx env ee /\
    body_const_cells_agree_mods mods cx env ee /\ ^entry ee sb t G tn /\
    gas_admissible (next v) expr_vv_res_ok ee ==>
    ^outcome (next v) (ee,t,G,tn) Q R) ==>
  ^outcome (bind (^forced e) next) (es,s0,G0,tn0) Q R
Proof
  BETA_TAC >> strip_tac >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
    (irule slice_cons_value_sim >> qexistsl_tac [`env`,`exps`,`mods`,`rest`,`src`,`tops`] >> simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     fs[expr_sim_full_code_def] >> qexists_tac `func` >> simp[]) >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  irule reached_word_result_bind_mods >> asm_rewrite_tac[slice_vv_exception_ok] >>
  qexistsl_tac [`d`,`expr_vv_res_ok`,`op`,`sa`,`sb`,`shadow_func`,`sha`,`shb`,`ty`] >>
  asm_rewrite_tac[slice_vv_exception_ok] >>
  qx_genl_tac [`marks`,`v`,`ee`,`G`,`tn`,`t`] >> strip_tac >>
  `^entry ee sb t G tn /\
   ^forced e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,ee)` by
    (BETA_TAC >> irule (BETA_RULE slice_word_next_entry_mods) >>
     asm_rewrite_tac[] >> qexistsl_tac [`G0`,`op`,`sa`,`tn0`] >> asm_rewrite_tac[]) >>
  RULE_ASSUM_TAC BETA_RULE >>
  qpat_x_assum `local_ptrs_reserved cenv sb /\ _` strip_assume_tac >>
  drule_all_then strip_assume_tac modular_reached_uint256_mods >>
  qpat_assum `!marks v ee G tn t. _ ==> gas_outcome_full_mods _ _ _ _ (next v) _ _ _` irule >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  ((qexists_tac `marks` >> first_assum ACCEPT_TAC) ORELSE
   (qpat_assum `expr_type e = _` (fn th => PURE_REWRITE_TAC [th]) >>
    first_assum ACCEPT_TAC))
QED

Triviality slice_bind_success:
  f s = (INL v,t) ==>
  !k : value -> evaluation_state -> value list evaluation_result. bind f k s = k v t
Proof
  simp[bind_def]
QED

Triviality slice_two_reads:
  (!tail. ^forced start (es with gas_obs := p1 ++ tail) = (INL v1,mid with gas_obs := tail)) /\
  (!tail. ^forced len (mid with gas_obs := p2 ++ tail) = (INL v2,fin with gas_obs := tail)) ==>
  !tail. eval_exprs cx [start;len] (es with gas_obs := p1 ++ (p2 ++ tail)) =
         (INL [v1;v2],fin with gas_obs := tail)
Proof
  BETA_TAC >> strip_tac >> gen_tac >>
  `eval_exprs cx [] = return []` by simp[FUN_EQ_THM,eval_exprs_nil,return_def] >>
  qpat_assum `!tail. bind (eval_expr cx start) _ _ = _`
    (qspec_then `p2 ++ tail` (mp_then Any assume_tac slice_bind_success)) >>
  qpat_assum `!tail. bind (eval_expr cx len) _ _ = _`
    (qspec_then `tail` (mp_then Any assume_tac slice_bind_success)) >>
  simp[Excl "APPEND_ASSOC",eval_exprs_cons_action,bind_return] >>
  pure_once_rewrite_tac[bind_assoc] >> simp[bind_return,return_def]
QED

Theorem slice_code_tail_mods:
  expr_body_pre_mods mods cenv cx env (Builtin ann (Slice n) [Builtin ct (Acc Code) [addr];start;len]) es /\
  body_const_cells_agree_mods mods cx env es /\ body_exprs_full_ok_mods mods exps cx [start;len] /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  ^child ty1 start sa s1 sha sh1 x /\ ^child ty2 len s1 s2 sh1 sh2 y /\
  ^entry es sa s0 G0 tn0 /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  gas_admissible (bind (^forced start) (\v. bind (^forced len) (k v))) expr_vv_res_ok es /\
  (!v w. storage_trace_frame (k v w)) /\ ^exit_weaken /\
  (!marks1 v1 mid G1 tn1 t1 marks2 v2 fin G2 tn2 t2.
    ^cut start es sa s1 s0 mid v1 x t1 G0 tn0 G1 tn1 marks1 /\
    ^cut len mid s1 s2 t1 fin v2 y t2 G1 tn1 G2 tn2 marks2 /\
    ^entry fin s2 t2 G2 tn2 /\
    expr_sim_inv_mods mods cenv cx env fin /\ body_const_cells_agree_mods mods cx env fin /\
    v1 = IntV (&w2n (val_to_w256 v1)) /\ v2 = IntV (&w2n (val_to_w256 v2)) /\
    ^saved x y s2 t2 G2 tn2 v1 v2 /\ gas_admissible (k v1 v2) expr_vv_res_ok fin /\
    (!tail. eval_exprs cx [start;len]
       (es with gas_obs := gas_explicit marks1 s0.vs_gas_readings ++
                            (gas_explicit marks2 t1.vs_gas_readings ++ tail)) =
       (INL [v1;v2],fin with gas_obs := tail)) ==>
    ^outcome (k v1 v2) (fin,t2,G2,tn2) Q R) ==>
  ^outcome (bind (^forced start) (\v. bind (^forced len) (k v))) (es,s0,G0,tn0) Q R
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `code_slice_source (Slice n) [Builtin ct (Acc Code) [addr];start;len] = SOME (ct,addr)` by
    simp[code_slice_source_SOME] >>
  drule_all_then strip_assume_tac slice_code_operand_pre_mods >> gvs[] >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  `expr_body_pre_mods mods cenv cx env start es` by
    (qpat_assum `!e mid. _ ==> expr_body_pre_mods _ _ _ _ e mid` irule >> simp[]) >>
  irule (BETA_RULE slice_cons_bind) >> asm_rewrite_tac[] >>
  conj_tac
  >- (BETA_TAC >> simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
                       storage_trace_frame_read_result]) >>
  qexistsl_tac [`d`,`env`,`exps`,`mods`,`x`,`[len]`,`sa`,`s1`,`sha`,
                `shadow_func`,`sh1`,`src`,`tops`,`ty1`] >>
  asm_rewrite_tac[] >> BETA_TAC >>
  qx_genl_tac [`marks1`,`v1`,`mid`,`G1`,`tn1`,`t1`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `v1 = IntV _` (markerLib.mk_asm "start_word") >>
  `expr_body_pre_mods mods cenv cx env len mid` by
    (qpat_assum `!e mid. _ ==> expr_body_pre_mods _ _ _ _ e mid` irule >> simp[]) >>
  irule (BETA_RULE slice_cons_bind) >> asm_rewrite_tac[] >>
  qexistsl_tac [`d`,`env`,`exps`,`mods`,`y`,`[]`,`s1`,`s2`,`sh1`,
                `shadow_func`,`sh2`,`src`,`tops`,`ty2`] >>
  asm_rewrite_tac[] >> BETA_TAC >>
  qx_genl_tac [`marks2`,`v2`,`fin`,`G2`,`tn2`,`t2`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `^saved x y s2 t2 G2 tn2 v1 v2` by
    (BETA_TAC >>
     qpat_assum `ghost_kept_at lo cenv mid s1 G1 tn1 t1 G2 tn2`
       (mp_then Any (drule_all_then ACCEPT_TAC) slice_saved_words_mods)) >>
  pop_assum (strip_assume_tac o BETA_RULE) >>
  asm_x "start_word" assume_tac >>
  qpat_assum `!marks1 v1 mid G1 tn1 t1 marks2 v2 fin G2 tn2 t2.
     _ ==> gas_outcome_full_mods _ _ _ _ (k v1 v2) _ _ _` irule >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G1`,`marks1`,`marks2`,`mid`,`t1`,`tn1`] >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  irule (BETA_RULE slice_two_reads) >> qexists_tac `mid` >>
  conj_tac >> first_assum ACCEPT_TAC
QED
