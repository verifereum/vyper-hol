(* The copy target is evaluated before the amount and optional salt.
   Keep its actual address bytes and the path from the original entry. *)
Theory bodyCreateCopyTargetMods
Ancestors
  bodyCreateOperandCutMods bodyFullPredsMods bodyFullPostsMods
  exprBodyPreProps exprSimWordArgs exprSimPrecompiles exprWordOperand exprSimSend
  abiValueEncoding abiEncodeArgsSim emittedSeqComposePtr wordArgsPtr
  fragGasOriginPtr fragExec exprLoweringProps gasShadow compileEnv
  vyperTypeEvalCaseProofs vyperTypeExprResult vyperTypeExprSoundness
  vyperTypeInvariants vyperStorageTrace vyperStorageFootprint vyperTypeSystem
  loweringPosts exprSimSource bodyPtrDefs vyperTyping vyperState loweringShapeDefs

Theorem copy_target_word[local]:
  expr_body_pre_mods mods cenv cx env e es /\ expr_result_typed env e (Value v) /\
  expr_type e = BaseT AddressT /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
  valid_horizon cx st0 H ee.storage_trace /\
  expr_post_mods H ctx func cenv cx e es sa sb s ee v op t ==>
  (?bs. v = BytesV bs /\ LENGTH bs = 20) /\
  eval_operand op t = SOME (typed_val_to_w256 (BaseTV AddressT) v) /\
  op_taint tn op = {} /\ (!x. op = Var x ==> not_fresh_at sb x) /\ (!l. op <> Label l) /\
  wb_frame cenv es ee sa s t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v` by
    fs[expr_result_typed_def,expr_runtime_typed_def,value_result_typed_def] >>
  `tv = BaseTV AddressT` by metis_tac[evaluate_type_base_result] >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type (get_tenv cx) ty` by
    (simp[well_formed_type_def] >> rpt strip_tac >>
     drule_all env_consistent_var_type_evaluates >> simp[]) >>
  drule lower_value_word_shape >> disch_then (qspec_then `env` mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  fs[expr_post_mods_def,ptr_val_ok_def] >>
  drule_then assume_tac expr_post_frame >>
  drule_all_then assume_tac expr_post_typed_stack_operand >> simp[] >>
  Cases_on `v` >> fs[value_has_type_def]
QED

val exit = ``\(H:(bool # 256 word # type_value) list # num list)
  (res:value + exception) ee (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;

Theorem create_copy_target_cut_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env target es /\
  body_exprs_full_ok_mods mods exps cx (target::rest) /\ expr_type target = BaseT AddressT /\
  lower_value compile_expr cenv (expr_type target) target sa = (x,a) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type target)
    (gas_shadow_expr target) sha = (x,ah) /\
  gas_shadow_state sa sha /\ gas_shadow_state a ah /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  fn_has_code sa a func /\ fn_has_code sha ah shadow_func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn i z. frag_reachable ctx func s0 fn i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!vs. storage_trace_frame (next vs)) /\
  (!bs et Gu tu u marks.
    LENGTH bs = 20 /\ body_exprs_full_ok_mods mods exps cx rest /\
    eval_operand x u = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
    op_taint tu x = {} /\ (!z. x = Var z ==> not_fresh_at a z) /\ (!l. x <> Label l) /\
    wb_frame cenv es et sa s0 u /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu /\
    expr_sim_inv_mods mods cenv cx env et /\ body_const_cells_agree_mods mods cx env et /\
    s0.vs_alloca_next <= u.vs_alloca_next /\ alloca_history func u /\
    return_buf_frame d cenv a u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!fn i z. frag_reachable ctx func u fn i z ==> dalloca_fmp_headroom i z) /\
    ~u.vs_halted /\ u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
    storage_trace_domain cx st0 et.storage_trace /\ et.gas_obs = [] /\
    (!tail. bind (eval_expr cx target) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL (BytesV bs),et with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H et.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx et u /\
      immutable_frame_mods func cenv cx et u /\ storage_well_formed_on cx et (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx et Gu tu u /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) marks (OK u,Gu,tu)) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (bind (eval_exprs cx rest) (\vs. next (BytesV bs::vs)))
      (et,u,Gu,tu) Q ^exit) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_exprs cx (target::rest)) next)
    (es,s0,G0,tn0) Q ^exit
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `body_exprs_full_ok_mods _ _ _ (target::_)`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_mods_def]) >>
  once_rewrite_tac[eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  irule create_body_operand_cut_replay_mods >> BETA_TAC >>
  asm_rewrite_tac[] >> conj_tac
  >- simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame] >>
  qexistsl_tac [`d`,`env`,`exps`,`mods`,`x`,`sa`,`a`,`sha`,`shadow_func`,`ah`,`src`,`tops`] >>
  asm_rewrite_tac[] >> reverse conj_tac
  >- (qpat_assum `expr_type target = _` (fn th => once_rewrite_tac [GSYM th]) >>
      asm_rewrite_tac[]) >>
  suspend "landing"
QED

Resume create_copy_target_cut_mods[landing]:
  map_every qx_gen_tac [`v`,`et`,`Gu`,`tu`,`u`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?ms. _ /\ (!H. _ ==> gas_origin_ptr_path _ _ ms _)`
    (qx_choose_then `marks` strip_assume_tac) >>
  `body_exprs_full_ok_mods mods exps cx rest` by
    (qpat_assum `_ ==> body_exprs_full_ok_mods _ _ _ rest` drule >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon et.storage_trace) et.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> expr_post_mods H _ _ _ _ target _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac copy_target_word >>
  qpat_x_assum `v = BytesV _` SUBST_ALL_TAC >>
  first_assum irule >> asm_rewrite_tac[] >>
  qexists_tac `marks` >> asm_rewrite_tac[] >> gen_tac >> disch_tac >>
  qpat_assum `!H. _ ==> expr_post_mods H _ _ _ _ target _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> fs[expr_post_mods_def,expr_post_def]
QED

Finalise create_copy_target_cut_mods

Theorem create_copy_prefix_frame_mods:
  local_ptrs_reserved cenv sa /\ ci_mono sa a /\ ci_mono a sm /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H et.storage_trace ==> valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H et.storage_trace) /\
  (!H. valid_horizon cx st0 H et.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) mt (OK u,Gu,tu)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Gu,tu) ms (OK s,G,tn)) /\
  wb_frame cenv es et sa s0 u /\ wb_frame cenv et ee a u s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu /\ ghost_kept_at lo cenv et a Gu tu u G tn /\
  eval_operand x u = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
  op_taint tu x = {} /\ (!z. x = Var z ==> not_fresh_at a z) /\ (!l. x <> Label l) /\
  s0.vs_alloca_next <= u.vs_alloca_next /\ u.vs_alloca_next <= s.vs_alloca_next ==>
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) (mt ++ ms) (OK s,G,tn)) /\
  valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) es.storage_trace /\
  stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx es s0 /\
  wb_frame cenv es ee sa s0 s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  eval_operand x s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
  op_taint tn x = {} /\ (!z. x = Var z ==> not_fresh_at sm z) /\ (!l. x <> Label l) /\
  s0.vs_alloca_next <= s.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) es.storage_trace` by simp[] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx es s0` by simp[] >>
  `MAP FDOM es.scopes = MAP FDOM et.scopes` by fs[wb_frame_def,locals_kept_def] >>
  fs[ci_mono_def] >>
  `wb_frame cenv es ee sa s0 s` by
    (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >>
     asm_rewrite_tac[] >> conj_tac
     >- (qexistsl_tac [`et`,`a`,`u`] >> asm_rewrite_tac[]) >>
     qexistsl_tac [`storage_trace_horizon ee.storage_trace`,`ctx`,`cx`,`func`] >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G tn` by
    (irule (INST_TYPE [beta |-> ``:256``] ghost_kept_at_wb_trans) >>
     qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ es s0` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv et a Gu tu u G tn` (irule_at Any) >>
     qexists_tac `et` >> simp[]) >>
  drule_all_then assume_tac abi_args_operand_kept >>
  `op_taint tn x = op_taint tu x` by
    (irule old_operand_taint_frame >> qexists_tac `a` >> fs[ghost_kept_at_def]) >>
  `!z. x = Var z ==> not_fresh_at sm z` by metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `s0.vs_alloca_next <= s.vs_alloca_next` by decide_tac >>
  asm_rewrite_tac[] >> gen_tac >> disch_tac >>
  `valid_horizon cx st0 H et.storage_trace` by simp[] >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s0,G0,tn0) mt _` (drule_then assume_tac) >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ (u,Gu,tu) ms _` (drule_then assume_tac) >>
  qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) mt _`
    (mp_then Any mp_tac gas_origin_ptr_path_append) >>
  simp[NoAsms] >> disch_then irule >> first_assum ACCEPT_TAC
QED
