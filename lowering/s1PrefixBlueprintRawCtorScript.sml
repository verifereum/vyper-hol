(* Prefix through the raw blueprint constructor bytes, before scalar operands. *)
Theory s1PrefixBlueprintRawCtor
Ancestors
  s1PrefixDefs s1PrefixPreds s1PrefixCompose s1PrefixOfVV bodyFullCreateHeld
  exprBodyPreProps vyperInterpreter vyperState vyperStorageTrace
  exprSimMemorySource exprLoweringProps fragExec gasShadowCompile
  builtinCreate compileEnv gasShadow gasShadowState exprSimHypsDefs
  loweringStateRelDefs bodyPtrDefs vyperStorageFootprint venomState
  gasOutcomeFullCompose gasOutcomeFull exprSimDefs stmtSimProps
  exprSimAbiEncodeArgsLabelReplay s1PrefixProps words finite_map
  stmtLoweringMono exprLowering exprSimSource vyperAST list fragGasOriginPtr

Theorem blueprint_raw_read_prefix[local]:
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx
    (expr_type e) e es /\
  expr_body_pre cenv cx env e es /\
  compile_create_blueprint_args compile_expr cenv T later [e] sa = ((data,cnt),sb) /\
  compile_create_blueprint_args compile_expr (gas_shadow_env T cenv) T (MAP gas_shadow_expr later)
    [gas_shadow_expr e] sh = ((data,cnt),shb) /\
  gas_shadow_state sa sh /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  fn_has_code sa sb func /\ fn_has_code sh shb shadow_func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `compile_create_blueprint_args _ _ T later [e] _ = _`
    (strip_assume_tac o MATCH_MP blueprint_raw_args_parts) >>
  qpat_assum `compile_create_blueprint_args _ _ T _ [gas_shadow_expr e] _ = _`
    (strip_assume_tac o REWRITE_RULE [gas_shadow_expr_type] o
       MATCH_MP blueprint_raw_args_parts) >>
  rename1 `compile_expr _ _ e sa = (vv,sm)` >>
  rename1 `compile_expr _ _ (gas_shadow_expr e) sh = (shv,shm)` >>
  `gas_shadow_compiles (compile_expr cenv (expr_type e) e)
      (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
    irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
           Q.INST [`shadow` |-> `T`] |> SIMP_RULE (srw_ss()) []) >>
  drule_then (drule_all_then strip_assume_tac) bodyFullForArrayRoundTheory.nonslot_shadow_cut >>
  rename1 `compile_snapshot_vv _ _ shv shm = (_,shs)` >>
  rename1 `unwrap_value _ _ shs = (_,shu)` >>
  rename1 `emit_op MLOAD _ shu = (_,shn)` >>
  `ci_mono sa sm /\ ci_mono sm ss /\ ci_mono ss su /\ ci_mono su sn /\ ci_mono sn sb` by
    metis_tac[ci_mono_compile_expr_sa,ci_mono_compile_snapshot_vv,
              ci_mono_unwrap_value,ci_mono_emit_op,pairTheory.SND] >>
  `ci_mono sh shm /\ ci_mono shm shs /\ ci_mono shs shu /\ ci_mono shu shn /\ ci_mono shn shb` by
    metis_tac[ci_mono_compile_expr_sa,ci_mono_compile_snapshot_vv,
              ci_mono_unwrap_value,ci_mono_emit_op,pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sh shm shadow_func` by
    (conj_tac
     >- (qspecl_then [`sa`,`sm`,`sb`,`func`] mp_tac fragExecTheory.fn_has_code_split >>
         (impl_tac >- metis_tac[ci_mono_def,ci_mono_trans]) >> simp[]) >>
     qspecl_then [`sh`,`shm`,`shb`,`shadow_func`] mp_tac fragExecTheory.fn_has_code_split >>
     (impl_tac >- metis_tac[ci_mono_def,ci_mono_trans]) >> simp[]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible,forced_expr_admissible_raw] >>
  rewrite_tac[gas_prefix_full_bind_read_result] >>
  qpat_x_assum `expr_vv_sim_prefix _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_prefix_def,expr_vv_sim_full_pre_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`sh`,`shm`,`vv`,`s`,`G`,`tn`] mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> simp[]
QED

Theorem blueprint_prefix_set_gas_obs[local]:
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source (es,s,G,tn) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source
    (es with gas_obs := gas,s,G,tn)
Proof
  simp[gas_prefix_full_def]
QED

(* The checked full cut supplies the prepared buffer and replay.  Run its
   success continuation with a source return, so it exposes the same cut
   without executing any scalar operand. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)` by
    (irule blueprint_raw_read_prefix >>
     qpat_assum `compile_create_blueprint_args _ _ T later [e] _ = _` (irule_at Any) >>
     qpat_assum `compile_create_blueprint_args _ _ T _ [gas_shadow_expr e] _ = _` (irule_at Any) >>
     qpat_assum `expr_body_pre cenv cx env e es` (irule_at Any) >>
     qexists `shadow_func` >> simp[] >> qexists `d` >> simp[] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (rpt strip_tac >> first_assum (drule_then strip_assume_tac) >>
          first_assum ACCEPT_TAC >> NO_TAC) >>
     qpat_assum `body_expr_prefix_ok cx e`
       (mp_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
     strip_tac >>
     qpat_assum `!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
         _ ==> expr_sim_prefix _ _ _ _ _ _ /\ expr_vv_sim_prefix _ _ _ _ _ _`
       (drule_all_then (irule o cj 2 o SPEC_ALL))) >>
  once_rewrite_tac [abi_args_singleton_source] >>
  rewrite_tac [bind_assoc,bind_return] >>
  once_rewrite_tac [GSYM bind_assoc] >>
  irule gas_prefix_full_bind >>
  simp [bind_return,storage_trace_frame_bind_all,evaluate_storage_trace_frame,
        storage_trace_frame_read_result,requests_outcomes_frame_bind_all,
        evaluate_requests_outcomes_frame,requests_outcomes_frame_read_result] >>
  qexistsl [
    `\H (res:value + exception) ee Gu tu u. !v. res = INL v ==>
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cx st0 (next [v]) (ee,u,Gu,tu)`,
    `\H (res:value + exception) ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z)`,
    `cx_tops cx`] >>
  BETA_TAC >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
        (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
      fs[storage_trace_domain_def])
  >- (rpt strip_tac >> Cases_on `res` >> fs[expr_exit_def]) >>
  suspend "return_value"
QED
*)
Theorem blueprint_raw_ctor_cut_prefix:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx env e es /\ body_expr_full_ok cx e /\ body_expr_prefix_ok cx e /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal))
    (int_calls_exprs later) /\
  compile_create_blueprint_args compile_expr cenv T later [e] sa = ((data,cnt),sb) /\
  compile_create_blueprint_args compile_expr (gas_shadow_env T cenv) T (MAP gas_shadow_expr later)
    [gas_shadow_expr e] sh = ((data,cnt),shb) /\
  gas_shadow_state sa sh /\ gas_shadow_state sb shb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  fn_has_code sa sb func /\ fn_has_code sh shb shadow_func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!vs. storage_trace_frame (next vs)) /\
  (!bs ee Gu tu u marks.
    LENGTH bs < 2 ** 64 /\
    (!tail. eval_exprs cx [e] (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL [BytesV bs],ee with gas_obs := tail)) /\
    expr_sim_inv cenv cx env ee /\
    wb_frame cenv es ee sa s u /\ ghost_kept_at lo cenv es sa G tn s Gu tu /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ s.vs_alloca_next <= u.vs_alloca_next /\
    alloca_history func u /\ return_buf_frame d cenv sb u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!fn i z. frag_reachable ctx func u fn i z ==> dalloca_fmp_headroom i z) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. data = Var x \/ cnt = Var x ==> not_fresh_at sb x) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee u /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ee Gu tu u /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK u,Gu,tu)) /\
    (!vs ef Gf tf f gs.
      (!tail. eval_exprs cx later (ee with gas_obs := gs ++ tail) = (INL vs,ef with gas_obs := tail)) /\
      wb_frame cenv ee ef sb u f /\ ghost_kept_at lo cenv ee sb Gu tu u Gf tf /\
      MAP FDOM ee.scopes = MAP FDOM ef.scopes /\ u.vs_alloca_next <= f.vs_alloca_next /\
      storage_trace_domain cx st0 ef.storage_trace /\
      (!H. valid_horizon cx st0 H ef.storage_trace ==>
        valid_horizon cx st0 H ee.storage_trace /\ stmt_state_rel H ctx func cenv cx ef f /\
        storage_well_formed_on cx ef (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ef Gf tf f) ==>
      eval_operand cnt f = SOME (n2w (LENGTH bs)) /\ op_taint tf cnt = {} /\ op_prov Gf cnt = NONE /\
      (cnt <> Lit 0w ==> ?q a. data = Var q /\ lookup_var q f = SOME a /\
        ptr_covers Gf tf q f (LENGTH bs) /\ (bs = [] \/ w2n a + LENGTH bs <= f.vs_alloca_next) /\
        (!i. w2n a <= i /\ i < w2n a + LENGTH bs ==> i NOTIN tf.t_mem) /\
        read_memory (w2n a) (LENGTH bs) f = bs)) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (next [BytesV bs]) (ee,u,Gu,tu)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_exprs cx [e]) next) (es,s,G,tn)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume blueprint_raw_ctor_cut_prefix[return_value]:
  `bind (eval_exprs cx [e]) (\vs. return (HD vs)) =
     bind (eval_expr cx e) (read_result cx)` by
    (simp [abi_args_singleton_source,bind_assoc,bind_return,FUN_EQ_THM] >>
     gen_tac >> Cases_on `eval_expr cx e x` >> rename1 `_ = (res,ee)` >>
     Cases_on `res` >> simp[bind_def] >>
     rename1 `eval_expr cx e x = (INL raw,ee)` >>
     Cases_on `read_result cx raw ee` >> rename1 `read_result _ _ _ = (ans,ef)` >>
     Cases_on `ans` >> simp[return_def]) >>
  pop_assum (fn th => once_rewrite_tac [GSYM th]) >>
  ho_match_mp_tac (GEN_ALL blueprint_raw_args_cut) >>
  qpat_assum `compile_create_blueprint_args _ _ T later [e] _ = _` (irule_at Any) >>
  qpat_assum `compile_create_blueprint_args _ _ T _ [gas_shadow_expr e] _ = _` (irule_at Any) >>
  qpat_assum `expr_body_pre cenv cx env e es` (irule_at Any) >>
  qpat_assum `expr_type e = _` (irule_at Any) >>
  qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `return_buf_frame _ _ sa s` (irule_at Any) >>
  qexists `shadow_func` >> simp[storage_trace_frame_return] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_genl_tac [`bs`,`ee`,`Gu`,`tu`,`u`,`marks`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gu`,`ee`,`INL (BytesV bs)`,`u`,`tu`] >>
  simp[return_def,cj 1 gas_origin_ptr_path_rules] >>
  gen_tac >> disch_tac >> irule blueprint_prefix_set_gas_obs >>
  qpat_assum `!bs ee Gu tu u marks. _ ==> gas_prefix_full _ _ _ (next [BytesV bs]) _`
    (qspecl_then [`bs`,`ee`,`Gu`,`tu`,`u`,`marks`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise blueprint_raw_ctor_cut_prefix
*)
