(* The selected forced operand of a linked bytestring comparison. *)
Theory bodyBopBytestringChildMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv bodyFullShared bodyInvSplit
  bodySimStmtFacts exprBodyPreProps exprSimHypsDefs exprSimHashBoundary exprSimWordArgs
  exprOperandVar exprLoweringProps exprSimFullBundleProps builtinHashing
  bodyWriteSubscriptSourceMods gasOutcomeFullPostMods gasOutcomeFull
  exprSimLiteralWord fragGasOriginPtr wordArgsPtr exprLowering vyperValueOperation loweringPosts loweringStateRelDefs
  bodyPtrDefs bodyMemoryDefs vyperTypeSystem vyperTypeExprSoundness
  vyperTypeEvalCaseProofs[qualified,ignore_grammar] abiValueEncoding[qualified,ignore_grammar]
  vyperValue vyperTyping vyperInterpreter vyperState vyperAST vyperContext
  vyperStorageFootprint compileEnv venomState valueCopyBytes ptrDiscipline

Theorem bytestring_child_source[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs ++ tail) =
    (INL v,ee with gas_obs := tail)) /\ ee.gas_obs = [] ==>
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  expr_sim_inv_mods mods cenv cx env ee /\
  ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v
Proof
  strip_tac >>
  `ee with gas_obs := [] = ee` by
    (qpat_assum `ee.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs) = (INL v,ee)` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[]) >>
  conj_tac
  >- (drule_then mp_tac (REWRITE_RULE [ETA_THM] forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := xs)` by
    simp[write_subscript_source_gas_obs_mods] >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >>
  `env.type_defs = get_tenv cx` by
    (drule expr_sim_inv_mods_env >>
     disch_then (irule o MATCH_MP vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv)) >>
  gvs[value_runtime_typed_def]
QED

Theorem bytestring_type_shape[local]:
  is_bytestring_type ty ==>
  (?n. ty = BaseT (StringT n)) \/ (?n. ty = BaseT (BytesT (Dynamic n)))
Proof
  Cases_on `ty` >> fs[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> fs[is_bytestring_type_def]
QED

Theorem bytestring_child_memory[local]:
  is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  expr_post_mods H ctx func cenv cx e es sa cb s ee v m t ==>
  ?bs b. (v = BytesV bs \/ ?str. v = StringV str /\ bs = MAP (n2w o ORD) str) /\
    eval_operand m t = SOME (n2w b) /\
    mem_word_at b t.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b + 32) (LENGTH bs) t.vs_memory = bs /\
    b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256)
Proof
  strip_tac >>
  qhdtm_x_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE[expr_post_mods_def]) >>
  drule_then strip_assume_tac bytestring_type_shape
  >- (`tv = BaseTV (StringT n)` by fs[evaluate_type_def, AllCaseEqs()] >>
      `?str. v = StringV str` by (Cases_on `v` >> fs[value_has_type_def]) >>
      gvs[] >> irule hash_string_post_view >> goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  `tv = BaseTV (BytesT (Dynamic n))` by fs[evaluate_type_def, AllCaseEqs()] >>
  `?bs. v = BytesV bs` by (Cases_on `v` >> fs[value_has_type_def]) >>
  gvs[] >>
  irule hash_dynamic_post_view >> goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]
QED

Theorem bytestring_child_pointer[local]:
  is_bytestring_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ eval_operand m t = SOME w /\ ptr_val_ok cx ty v m G tn t ==>
  ?p. m = Var p
Proof
  strip_tac >>
  `~is_word_type ty` by simp[is_bytestring_word_type] >>
  `val_footprint tv v <> 0` by
    (drule_then strip_assume_tac bytestring_type_shape >>
     gvs[evaluate_type_def, AllCaseEqs()] >> Cases_on `v` >>
     gvs[value_has_type_def, val_footprint_def]) >>
  fs[ptr_val_ok_def, ptr_mem_ok_def] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  first_x_assum (drule_then strip_assume_tac) >> simp[]
QED

val child_entry = ``return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn inst t. frag_reachable ctx func s fn inst t ==> dalloca_fmp_headroom inst t) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts``;

val child_exit = ``\(H : (bool # 256 word # type_value) list # num list)
  (res : value + exception) ee (gt : (string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

val child_post = ``\(H : (bool # 256 word # type_value) list # num list) (res : value + exception) ee G' tn' t. ?v tv bs.
  res = INL v /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  (v = BytesV bs \/ ?str. v = StringV str /\ bs = MAP (n2w o ORD) str) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  expr_sim_inv_mods mods cenv cx env ee /\
  stmt_state_rel H ctx func cenv cx ee t /\
  immutable_frame_mods func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' t /\
  ghost_kept_at lo cenv es sa G tn s G' tn' /\
  ~t.vs_halted /\ alloca_history func t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s.vs_alloca_next <= t.vs_alloca_next /\
  (case bytestring_literal_hash e of
     SOME digest => h = Lit digest /\ sz = sa /\ t = s /\ G' = G /\ tn' = tn /\
        digest = word_of_bytes_be (Keccak_256_w64 bs)
   | NONE => ?m cb b p.
        m = Var p /\ not_fresh_at cb p /\
        lower_value compile_expr cenv (expr_type e) e sa = (m,cb) /\
        compile_bytestring_hash m cb = (h,sz) /\ fn_has_code cb sz func /\
        t.vs_current_bb = cb.cs_current_bb /\ t.vs_inst_idx = LENGTH cb.cs_current_insts /\
        expr_post_mods H ctx func cenv cx e es sa cb s ee v m t /\
        expr_store_bound cx (post_value_type cenv e) v m t /\
        ptr_val_ok cx (post_value_type cenv e) v m G' tn' t /\ ptr_buf_ok cenv e m G' t /\
        eval_operand m t = SOME (n2w b) /\ mem_word_at b t.vs_memory = n2w (LENGTH bs) /\
        mem_bytes_at (b + 32) (LENGTH bs) t.vs_memory = bs /\
        b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256))``;

val child_compiler_start = ``local_ptrs_reserved cenv sa /\
  (!H : (bool # 256 word # type_value) list # num list.
     dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x)``;

Theorem bytestring_child_dynamic[local]:
  bytestring_literal_hash e = NONE /\ is_bytestring_type (expr_type e) /\
  expr_body_pre_mods mods cenv cx env e es /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es /\
  lower_value compile_expr cenv (expr_type e) e sa = (m,cb) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e)
    shadow_sa = (m,shadow_cb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,cb,shadow_sa,shadow_cb) /\
  compile_bytestring_hash m cb = (h,sz) /\ fn_has_code cb sz func /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  ^child_compiler_start /\ ^child_entry ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx))
    (es,s,G,tn) ^child_post ^child_exit
Proof
  strip_tac >>
  qhdtm_x_assum `expr_sim_full_mods`
    (qspecl_then [`st0`,`sa`,`cb`,`shadow_sa`,`shadow_cb`,`m`,`s`,`G`,`tn`] mp_tac o
     REWRITE_RULE[expr_sim_full_mods_def]) >>
  impl_tac
  >- (qhdtm_x_assum `expr_sim_full_code`
        (strip_assume_tac o REWRITE_RULE[expr_sim_full_code_def]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  irule gas_outcome_full_mods_post_source >>
  goal_assum (drule_at (Pat `gas_outcome_full_mods _ _ _ _ _ _ _ _`)) >>
  simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all_then strip_assume_tac bytestring_child_source >>
  drule_all_then strip_assume_tac bytestring_child_memory >>
  `ptr_buf_ok cenv e m G' t` by (first_x_assum irule >> simp[is_bytestring_word_type]) >>
  `stmt_state_rel H ctx func cenv cx ee t /\ immutable_frame_mods func cenv cx ee t /\
   storage_well_formed_on cx ee (FST H)` by
    fs[expr_post_mods_def, expr_post_def] >>
  drule_all_then strip_assume_tac bytestring_child_pointer >>
  drule_all_then strip_assume_tac compile_lower_value_var >>
  gvs[] >> qexists_tac `b` >> simp[]
QED

Theorem bytestring_literal_payload[local]:
  bytestring_literal_hash e = SOME digest ==>
  ?ann l bs. e = Literal ann l /\
    (evaluate_literal l = BytesV bs \/
     ?str. evaluate_literal l = StringV str /\ bs = MAP (n2w o ORD) str) /\
    digest = word_of_bytes_be (Keccak_256_w64 bs)
Proof
  Cases_on `e` >> simp[bytestring_literal_hash_def] >>
  rename1 `Literal ann l` >> Cases_on `l` >>
  simp[bytestring_literal_hash_def, evaluate_literal_def]
QED

Theorem bytestring_child_nil_frame[local]:
  stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
  storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G tn s ==>
  stmt_state_rel H ctx func cenv cx (es with gas_obs := []) s /\
  immutable_frame_mods func cenv cx (es with gas_obs := []) s /\
  storage_well_formed_on cx (es with gas_obs := []) (FST H) /\
  ghost_inv_at_mods (DF H) lo d cenv cx (es with gas_obs := []) G tn s
Proof
  strip_tac >> conj_tac
  >- (drule msg_gas_state_frame >>
      disch_then (qspecl_then [`s.vs_gas_readings`, `s.vs_inst_idx`, `[]`] mp_tac) >> simp[]) >>
  conj_tac
  >- (qpat_assum `immutable_frame_mods _ _ _ es _` mp_tac >>
      PURE_REWRITE_TAC[immutable_frame_mods_def, immutables_rel_mods_def,
           immutable_alloca_sep_mods_def, immutable_alloca_sep_def,
           loweringStateRelDefsTheory.immutables_rel_def,
           evaluation_state_accfupds] >> simp[]) >>
  conj_tac
  >- (`storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
       storage_well_formed_on cx es (FST H)` suffices_by simp[] >>
      irule storage_well_formed_on_backends >> simp[]) >>
  qpat_assum `ghost_inv_at_mods _ _ _ _ _ es _ _ _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[ghost_inv_at_mods_def] >>
  PURE_REWRITE_TAC[evaluation_state_accfupds] >> simp[]
QED

Theorem bytestring_child_literal[local]:
  bytestring_literal_hash e = SOME digest /\ h = Lit digest /\ sz = sa /\
  expr_body_pre_mods mods cenv cx env e es /\ ^child_entry ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx))
    (es,s,G,tn) ^child_post ^child_exit
Proof
  strip_tac >> drule bytestring_literal_payload >> strip_tac >> gvs[] >>
  irule gas_outcome_full_mods_pure >>
  (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G`,`es`,`INL (evaluate_literal l)`,`s`,`tn`] >>
  simp[literal_read_all_tails, gas_origin_ptr_path_rules] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac bytestring_child_nil_frame >>
  `?tv. evaluate_type (get_tenv cx) (expr_type (Literal ann l)) = SOME tv /\
        value_has_type tv (evaluate_literal l)` by
    (drule (Q.INST [`xs` |-> `[]`,`ee` |-> `es with gas_obs := []`,
                    `v` |-> `evaluate_literal l`] bytestring_child_source) >>
     simp[literal_read_all_tails]) >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  gvs[write_subscript_source_gas_obs_mods, ghost_kept_at_refl]
QED

Theorem bop_bytestring_child_mods:
  is_bytestring_type (expr_type e) /\ expr_body_pre_mods mods cenv cx env e es /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es /\
  (case bytestring_literal_hash e of
     SOME digest => h = Lit digest /\ sz = sa
   | NONE => ?m cb shadow_cb.
       lower_value compile_expr cenv (expr_type e) e sa = (m,cb) /\
       lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e)
         shadow_sa = (m,shadow_cb) /\
       expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,cb,shadow_sa,shadow_cb) /\
       compile_bytestring_hash m cb = (h,sz) /\ fn_has_code cb sz func /\
       gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es) /\
  ^child_compiler_start /\ ^child_entry ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx))
    (es,s,G,tn) ^child_post ^child_exit
Proof
  strip_tac >>
  qspec_then `bytestring_literal_hash e` strip_assume_tac optionTheory.option_nchotomy
  >- (irule bytestring_child_dynamic >> gvs[] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> simp[]) >>
      qexistsl_tac [`shadow_cb`,`shadow_func`,`shadow_sa`] >> simp[]) >>
  irule bytestring_child_literal >> gvs[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> simp[]
QED
