(* The AddMod/MulMod prefix follows the three actual forced successes. *)
Theory bodyWordModReachedPrefixMods
Ancestors
  bodyReachedWordBindMods bodyWordModSourceCutsMods bodyMemoryDefs
  bodyFullPredsMods bodyFullPostsMods exprSimFullBundleProps bodyFullIfExpReach
  exprLoweringProps loweringPosts compileEnv exprSimHypsDefs vyperStorageTrace
  vyperStorageFootprint vyperState
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

val child = ``\e sa sb sha shb op.
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) sha = (op,shb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,sha,shb) /\
  sa.cs_next_var <= sb.cs_next_var``;

val outcome = ``\(source : evaluation_state -> value evaluation_result).
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 source``;
val forced = ``\e. bind (eval_expr cx e) (read_result cx)``;
val terminal = ``\v1 v2 v3 (ee : evaluation_state).
  (builtin_result cx ee.accounts ann bt (MAP expr_type [e1;e2;e3]) [v1;v2;v3],ee)``;
val exit_weaken = ``!(H : (bool # 256 word # type_value) list # num list)
  (res : value + vyperState$exception) ee
  (gt : (string |-> num # num) # taint) r. expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u) ==> R H res ee gt r``;

Triviality cons_value_sim:
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
    (first_x_assum irule >> simp[] >> conj_tac
     >- (qexistsl_tac [`src`,`tops`] >> simp[]) >> qexists_tac `env` >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Triviality cut_next_entry:
  ^entry es sa s0 G0 tn0 /\ ^cut e es sa sb s0 ee v op t G0 tn0 G tn marks /\
  sa.cs_next_var <= sb.cs_next_var ==>
  ^entry ee sb t G tn /\
  ^forced e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,ee)
Proof
  BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  conj_tac
  >- (simp[] >> rpt conj_tac
      >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[])
      >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[])
      >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[])
      >- (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
          fs[expr_post_mods_def,expr_post_def])
      >- (rpt strip_tac >> qpat_assum `!fn inst u. frag_reachable _ _ t fn inst u ==> _`
            (drule_then ACCEPT_TAC)) >>
      rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
        (qspec_then `H` (drule_then strip_assume_tac)) >>
      fs[expr_post_mods_def,expr_post_def]) >>
  qpat_assum `ee with gas_obs := [] = ee` (fn frame =>
    qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
      (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [listTheory.APPEND_NIL,frame])))
QED

Triviality modular_cons_bind:
  body_exprs_full_ok_mods mods exps cx (e::rest) /\ expr_type e = BaseT (UintT 256) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es /\
  ^child e sa sb sha shb op /\ ^entry es sa s0 G0 tn0 /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  gas_admissible (bind (^forced e) next) expr_res_ok es /\
  (!v. storage_trace_frame (next v)) /\ ^exit_weaken /\
  (!marks v ee G tn t.
    ^cut e es sa sb s0 ee v op t G0 tn0 G tn marks /\
    v = IntV (&w2n (val_to_w256 v)) /\
    body_exprs_full_ok_mods mods exps cx rest /\ expr_sim_inv_mods mods cenv cx env ee /\
    body_const_cells_agree_mods mods cx env ee /\ ^entry ee sb t G tn /\
    gas_admissible (next v) expr_res_ok ee ==>
    ^outcome (next v) (ee,t,G,tn) Q R) ==>
  ^outcome (bind (^forced e) next) (es,s0,G0,tn0) Q R
Proof
  BETA_TAC >> strip_tac >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
    (irule cons_value_sim >> qexistsl_tac [`env`,`exps`,`mods`,`rest`,`src`,`tops`] >> simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     fs[expr_sim_full_code_def] >> qexists_tac `func` >> simp[]) >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  irule reached_word_bind_mods >> asm_rewrite_tac[] >>
  qexistsl_tac [`d`,`op`,`sa`,`sb`,`shadow_func`,`sha`,`shb`,`ty`] >>
  asm_rewrite_tac[] >>
  qx_genl_tac [`marks`,`v`,`ee`,`G`,`tn`,`t`] >> strip_tac >>
  `^entry ee sb t G tn /\
   ^forced e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,ee)` by
    (BETA_TAC >> irule (BETA_RULE cut_next_entry) >>
     asm_rewrite_tac[] >> qexistsl_tac [`G0`,`op`,`sa`,`tn0`] >>
     asm_rewrite_tac[]) >>
  RULE_ASSUM_TAC BETA_RULE >>
  qpat_x_assum `local_ptrs_reserved cenv sb /\ _` strip_assume_tac >>
  drule_all_then strip_assume_tac modular_reached_uint256_mods >>
  first_x_assum irule >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  ((qexists_tac `marks` >> first_assum ACCEPT_TAC) ORELSE
   (rpt gen_tac >> strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
      (drule_then strip_assume_tac) >>
    rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >> simp[]))
QED

Triviality modular_forced_frame:
  storage_trace_frame (bind (eval_expr cx e) (read_result cx))
Proof
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result]
QED

Triviality modular_terminal_frame:
  storage_trace_frame (\(ee : evaluation_state).
    (builtin_result cx ee.accounts ann bt ts vs,ee))
Proof
  simp[storage_trace_frame_def]
QED

Theorem modular_three_operands_cps_mods:
  (bt = AddMod \/ bt = MulMod) /\ ann = BaseT (UintT 256) /\
  expr_type e1 = BaseT (UintT 256) /\ expr_type e2 = BaseT (UintT 256) /\
  expr_type e3 = BaseT (UintT 256) /\
  body_exprs_full_ok_mods mods exps cx [e1;e2;e3] /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin ann bt [e1;e2;e3]) es /\
  ^child e1 sa s1 sha sh1 x /\ ^child e2 s1 s2 sh1 sh2 y /\ ^child e3 s2 s3 sh2 sh3 z /\
  ^entry es sa s0 G0 tn0 /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  gas_admissible (^forced (Builtin ann bt [e1;e2;e3])) expr_res_ok es /\ ^exit_weaken /\
  (!marks1 v1 mid1 G1 tn1 t1 marks2 v2 mid2 G2 tn2 t2 marks3 v3 fin G3 tn3 t3.
    ^cut e1 es sa s1 s0 mid1 v1 x t1 G0 tn0 G1 tn1 marks1 /\
    ^cut e2 mid1 s1 s2 t1 mid2 v2 y t2 G1 tn1 G2 tn2 marks2 /\
    ^cut e3 mid2 s2 s3 t2 fin v3 z t3 G2 tn2 G3 tn3 marks3 /\
    v1 = IntV (&w2n (val_to_w256 v1)) /\ v2 = IntV (&w2n (val_to_w256 v2)) /\
    v3 = IntV (&w2n (val_to_w256 v3)) ==>
    ^outcome (^terminal v1 v2 v3) (fin,t3,G3,tn3) Q R) ==>
  ^outcome (^forced (Builtin ann bt [e1;e2;e3])) (es,s0,G0,tn0) Q R
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_inv_mods mods cenv cx env es /\
   (!e mid. MEM e [e1;e2;e3] /\ expr_sim_inv_mods mods cenv cx env mid ==>
      expr_body_pre_mods mods cenv cx env e mid)` by
    (drule_all_then strip_assume_tac modular_source_shape_mods >> gvs[] >> first_assum ACCEPT_TAC) >>
  qpat_assum `bt = AddMod \/ bt = MulMod`
    (fn th => let val action = MATCH_MP modular_forced_action th in
      PURE_REWRITE_TAC [action] >> RULE_ASSUM_TAC (PURE_REWRITE_RULE [action]) end) >>
  `expr_body_pre_mods mods cenv cx env e1 es` by
    (first_x_assum irule >> simp[]) >>
  irule (BETA_RULE modular_cons_bind) >> asm_rewrite_tac[] >>
  conj_tac
  >- (BETA_TAC >> simp[storage_trace_frame_bind_all, modular_forced_frame,
                       modular_terminal_frame]) >>
  qexistsl_tac [`d`,`env`,`exps`,`mods`,`x`,`[e2;e3]`,`sa`,`s1`,`sha`,
                `shadow_func`,`sh1`,`src`,`tops`,`ty`] >>
  asm_rewrite_tac[] >> BETA_TAC >>
  qx_genl_tac [`marks1`,`v1`,`mid1`,`G1`,`tn1`,`t1`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `v1 = IntV _` (markerLib.mk_asm "uint1") >>
  `expr_body_pre_mods mods cenv cx env e2 mid1` by
    (qpat_assum `!e mid. MEM e _ /\ _ ==> expr_body_pre_mods _ _ _ _ e mid`
       irule >> simp[]) >>
  irule (BETA_RULE modular_cons_bind) >> asm_rewrite_tac[] >>
  conj_tac
  >- (BETA_TAC >> simp[storage_trace_frame_bind_all, modular_forced_frame,
                       modular_terminal_frame]) >>
  qexistsl_tac [`d`,`env`,`exps`,`mods`,`y`,`[e3]`,`s1`,`s2`,`sh1`,
                `shadow_func`,`sh2`,`src`,`tops`,`ty`] >>
  asm_rewrite_tac[] >> BETA_TAC >>
  qx_genl_tac [`marks2`,`v2`,`mid2`,`G2`,`tn2`,`t2`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `v2 = IntV _` (markerLib.mk_asm "uint2") >>
  `expr_body_pre_mods mods cenv cx env e3 mid2` by
    (qpat_assum `!e mid. MEM e _ /\ _ ==> expr_body_pre_mods _ _ _ _ e mid`
       irule >> simp[]) >>
  irule (BETA_RULE modular_cons_bind) >> asm_rewrite_tac[] >>
  conj_tac >- (BETA_TAC >> simp[modular_terminal_frame]) >>
  qexistsl_tac [`d`,`env`,`exps`,`mods`,`z`,`[]`,`s2`,`s3`,`sh2`,
                `shadow_func`,`sh3`,`src`,`tops`,`ty`] >>
  asm_rewrite_tac[] >> BETA_TAC >>
  qx_genl_tac [`marks3`,`v3`,`fin`,`G3`,`tn3`,`t3`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `ann = BaseT (UintT 256)` SUBST_ALL_TAC >>
  asm_x "uint1" assume_tac >> asm_x "uint2" assume_tac >>
  first_x_assum irule >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G1`,`G2`,`marks1`,`marks2`,`marks3`,`mid1`,`mid2`,`t1`,`t2`,`tn1`,`tn2`] >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  qpat_assum `expr_type e1 = _` (fn a =>
    qpat_assum `expr_type e2 = _` (fn b =>
      qpat_assum `expr_type e3 = _` (fn c => PURE_REWRITE_TAC [a,b,c]))) >>
  first_assum ACCEPT_TAC
QED
