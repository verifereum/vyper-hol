(* Joint finite-horizon Keccak leaf. *)
Theory bodyFullHashKeccak
Ancestors
  bodyFullHashKeccakFixed bodyFullHashKeccakBytes bodyFullHashCleanFrame
  bodyPtrHashBuiltinsCases bodyMemBiKeccakSuffix bodyMemBiKeccakOpenFree exprOperandVar
  bodyPtrDefs ptrDiscipline venomState
  bodySimFull bodyFullPreds gasOutcomeFullCompose fragExec
  exprSimHash exprSimHashBoundary exprSimHyps exprSimHypsDefs exprSimSource
  gasShadowCompile gasShadowCompileStmtHelpers gasShadowState gasShadow
  exprLoweringProps exprLowering loweringPosts compileEnv vyperTyping
  vyperInterpreter vyperState vyperAST vyperTypeSystem
  stmtSimProps gasExemptCert vyperStorageTrace vyperStorageFootprint

Theorem keccak_vv_sim_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx env ty ann e es.
    expr_body_pre cenv cx env (Builtin ann Keccak256 [e]) es /\
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (expr_type e) e es ==>
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann Keccak256 [e]) es
Proof
  rpt gen_tac >> strip_tac >>
  `is_bytes_or_string_type (expr_type e) /\ ann = BaseT (BytesT (Fixed 32))` by
    (irule (SRULE [] (Q.INST [`b` |-> `Keccak256`,
       `ts` |-> `[expr_type e]`] hash_builtin_types)) >>
     gvs[expr_body_pre_def, well_typed_expr_def]) >>
  gvs[] >> simp[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr cenv ty (Builtin _ _ _) sa = _` mp_tac >>
  simp[compile_hash_singleton] >> pairarg_tac >> strip_tac >>
  gvs[] >>
  `cs_extends sa sm` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `?shadow_sm. lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e)
      shadow_sa = (v,shadow_sm) /\ gas_shadow_state sm shadow_sm` by
    (mp_tac (Q.INST [`ty` |-> `expr_type e`] gas_shadow_stmt_lower_value) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[] >>
     strip_tac >>
     Cases_on `lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa` >>
     gvs[]) >>
  `?bty. expr_type e = BaseT bty` by
    (Cases_on `expr_type e` >> gvs[is_bytes_or_string_type_def]) >>
  `cs_extends sm sb` by
    (qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
     qmatch_goalsub_abbrev_tac `as_stack_val _ suffix` >>
     Cases_on `suffix` >> simp[as_stack_val_def] >> strip_tac >>
     gvs[markerTheory.Abbrev_def] >>
     Cases_on `bty` >> gvs[is_bytes_or_string_type_def,
       is_bytestring_type_def] >- metis_tac[hash_suffix_appends, cs_appends_def] >>
     rename1 `expr_type e = BaseT (BytesT bd)` >>
     Cases_on `bd` >> gvs[is_bytestring_type_def] >>
     metis_tac[hash_suffix_appends, cs_appends_def]) >>
  `cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sb` by
    (conj_tac >- (drule (cj 2 compile_expr_grows) >> simp[]) >>
     qpat_x_assum `compile_expr cenv ty (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gas_shadow_expr_def, gas_shadow_builtin_def, compile_hash_singleton] >>
     pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
     qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
     qmatch_goalsub_abbrev_tac `as_stack_val _ suffix` >>
     Cases_on `suffix` >> simp[as_stack_val_def] >> strip_tac >>
     gvs[markerTheory.Abbrev_def] >>
     Cases_on `bty` >> gvs[is_bytes_or_string_type_def,
       is_bytestring_type_def] >- metis_tac[hash_suffix_appends, cs_appends_def] >>
     rename1 `expr_type e = BaseT (BytesT bd)` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, as_stack_val_def] >>
     rpt strip_tac >> metis_tac[hash_suffix_appends, cs_appends_def]) >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fn_has_code_split] >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >>
     gvs[expr_body_pre_def]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`,
    `v`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ baseQ baseR` >>
  `eval_expr cx (Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [e]) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v es. ((case builtin_result cx es.accounts (BaseT (BytesT (Fixed 32)))
       Keccak256 [expr_type e] [v] of INL w => INL (Value w) | INR exc => INR exc),es))` by
    (irule eval_expr_unary_builtin_action >> simp[vyperContextTheory.builtin_args_length_ok_def]) >>
  asm_rewrite_tac[] >> irule gas_outcome_full_bind_all >>
  `!res : value + exception. !r.
     (?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r) <=> expr_exit res r` by
    (Cases >> simp[expr_exit_INR_type]) >>
  simp[] >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`, `t`, `v'`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind, evaluate_storage_trace_frame,
          storage_trace_frame_read_result]
  >- simp[storage_trace_frame_def] >>
  qexists_tac `\H res ee G tn t. baseQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac
  >- suspend "hashed" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[Abbr `baseR`] >>
  simp[Abbr `baseQ`, Abbr `baseR`]
QED

Resume keccak_vv_sim_full[hashed]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `s`] >>
  strip_tac >> fs[] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    gvs[storage_trace_domain_def] >>
  `baseQ (storage_trace_horizon mid.storage_trace) res mid G1 tn1 s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> baseQ H _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  qpat_x_assum `baseQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `baseQ`, NoAsms] >> strip_tac >> gvs[] >>
  `~s.vs_halted /\ mid.gas_obs = []` by metis_tac[] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v',mid)` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[] >>
     `mid with gas_obs := [] = mid` by
       (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >> simp[]) >>
  `expr_body_pre cenv cx env e (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    simp[storage_trace_frame_bind, evaluate_storage_trace_frame,
      storage_trace_frame_read_result] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) es.storage_trace` by
    (drule_all valid_horizon_frame >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule (CONV_RULE (DEPTH_CONV ETA_CONV)
      exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_base_result) >>
  strip_tac >> gvs[] >>
  Cases_on `bty` >> gvs[is_bytes_or_string_type_def]
  >- suspend "string" >>
  rename1 `expr_type e = BaseT (BytesT bd)` >>
  Cases_on `bd` >> gvs[is_bytestring_type_def, as_stack_val_def]
  >- suspend "fixed" >>
  suspend "dynamic"
QED

Resume keccak_vv_sim_full[string]:
  gvs[is_bytestring_type_def, as_stack_val_def] >>
  Cases_on `v'` >> gvs[vyperTypingTheory.value_has_type_def] >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e es sa sm s0 mid
     (StringV s') v s` by metis_tac[] >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (StringT n))` by
    (drule expr_body_pre_type_evaluates >>
     simp[vyperValueTheory.evaluate_type_def] >> strip_tac >> gvs[]) >>
  drule_all hash_string_post_view >> strip_tac >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  Cases_on `compile_keccak256_bytes v sm` >>
  simp[as_stack_val_def] >> strip_tac >> gvs[] >>
  `~is_word_type (BaseT (StringT n))` by simp[is_word_type_def] >>
  drule_all hash_string_operand >> strip_tac >>
  `!z. v = Var z ==> not_fresh_at sm z` by
    (metis_tac[compile_lower_value_var]) >>
  gvs[ptr_covers_def, eval_operand_def] >>
  `b < dimword (:256)` by decide_tac >>
  `b + 32 + LENGTH s' <= s.vs_alloca_next` by
    (qpat_x_assum `expr_store_bound _ _ _ _ _` mp_tac >>
     simp[exprSimMemDefsTheory.expr_store_bound_def, eval_operand_def,
       exprSimPropsTheory.val_store_size_def, is_word_type_def] >>
     mp_tac (Q.SPEC `LENGTH (s':string)` exprSimPropsTheory.le_word_size_mul) >>
     decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts sm r) s` by
    (irule keccak_memory_suffix_mem_ok >>
     qexistsl_tac [`b`, `LENGTH (s':string)`, `q`, `Var p`] >>
     simp[eval_operand_def]) >>
  `fn_has_code sm r func` by metis_tac[fn_has_code_split] >>
  `r.cs_current_bb = sm.cs_current_bb /\
   r.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm r` by
    (metis_tac[keccak_suffix_shape, same_blocks_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sm r) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `fn_has_code sm r func` mp_tac >>
     simp[fn_has_code_def] >> strip_tac >>
     qexists_tac `bb` >> gvs[rich_listTheory.IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,
       rich_listTheory.DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qpat_assum `lower_value _ _ _ _ sa = _`
      (mp_tac o MATCH_MP (cj 2 compile_expr_grows)) >> simp[]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[loweringStateRelDefsTheory.not_fresh_at_def, arithmeticTheory.LE_TRANS] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ ghost_inv_at _ _ _ _ _ mid G1 tn1 s`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >> fs[ghost_inv_at_def]) >>
  `b + 32 + LENGTH (MAP (n2w o ORD) s' : word8 list) <= b' + sz' /\
   LENGTH (MAP (n2w o ORD) s' : word8 list) < dimword (:256) /\
   (!i. b <= i /\ i < b + 32 + LENGTH (MAP (n2w o ORD) s' : word8 list) ==>
      i NOTIN tn1.t_mem) /\
   mem_word_at b s.vs_memory = n2w (LENGTH (MAP (n2w o ORD) s' : word8 list)) /\
   mem_bytes_at (b+32) (LENGTH (MAP (n2w o ORD) s' : word8 list)) s.vs_memory =
     MAP (n2w o ORD) s'` by
    (simp[listTheory.LENGTH_MAP] >> rpt strip_tac >> gvs[] >>
     `b + 32 + LENGTH s' = b + (LENGTH s' + 32)` by decide_tac >> metis_tac[]) >>
  drule_all (SRULE [eval_operand_def] hash_bytes_keccak_joint_run) >>
  disch_then (qspecl_then [`PG`, `cx`, `mid`, `d`,
    `gas_explicit_sites ctx shadow_ctx`] strip_assume_tac) >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`, `mid`,
    `INL (Value (BytesV (Keccak_256_w64 (MAP (n2w o ORD) s'))))`,
    `t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm r)`, `tnf`] >>
  conj_tac >- simp[exprSimWordArgsTheory.builtin_result_def,
    vyperContextTheory.evaluate_builtin_def] >>
  rpt strip_tac >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  simp[] >>
  `expr_post H ctx func cenv cx e es sa sm s0 mid (StringV s') (Var p) s /\
   ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 s` by metis_tac[] >>
  `vv_post H ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [e])
    es sa r s0 mid (Value (BytesV (Keccak_256_w64 (MAP (n2w o ORD) s'))))
    (StackValue (BaseT (BytesT (Fixed 32))) q) t` by
    (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac keccak_memory_post_run) >>
     simp[eval_operand_def] >> strip_tac >> gvs[] >>
     first_x_assum irule >> simp[listTheory.LENGTH_MAP] >>
     qexists_tac `b` >> simp[]) >>
  simp[vyperASTTheory.expr_type_def, exprSimMemDefsTheory.vv_store_bound_stack_word,
    compileEnvTheory.is_word_type_def, bodyPtrDefsTheory.ptr_vv_ok_def,
    bodyPtrDefsTheory.ptr_val_ok_def, contextTheory.vv_location_def,
    loweringPostsTheory.post_value_type_def] >>
  `stmt_state_rel H ctx func cenv cx mid s` by
    metis_tac[exprSimWordArgsTheory.expr_post_state] >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `ghost_inv_at (DF H) lo d cenv cx mid Gf tnf
    (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm r)) /\
   ghost_kept_at lo cenv mid sm G1 tn1 s Gf tnf` by metis_tac[] >>
  simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  `wb_frame cenv es mid sa s0 s` by
    metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (qpat_assum `lower_value _ _ _ _ sa = _`
      (mp_tac o MATCH_MP (cj 2 compile_expr_grows)) >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf` by
    (`stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0` by
       (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
         (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
     drule_all hash_ghost_kept_wb_trans >> simp[]) >>
  gvs[]
QED

Resume keccak_vv_sim_full[fixed]:
  rename1 `expr_type e = BaseT (BytesT (Fixed m))` >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Fixed m)))` by
    (qpat_assum `expr_body_pre cenv cx env e es`
      (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
     simp[vyperValueTheory.evaluate_type_def] >> strip_tac >> gvs[AllCaseEqs()]) >>
  `m <= 32` by gvs[vyperValueTheory.evaluate_type_def] >>
  Cases_on `v'` >> fs[vyperTypingTheory.value_has_type_def] >>
  rename1 `expr_post _ _ _ _ _ e es sa sm s0 mid (BytesV bs) v s` >>
  `value_has_type (BaseTV (BytesT (Fixed m))) (BytesV bs)` by
    simp[vyperTypingTheory.value_has_type_def] >>
  Cases_on `compile_keccak256_bytesm v m sm` >>
  gvs[as_stack_val_def] >>
  rename1 `compile_keccak256_bytesm v _ sm = (op,sn)` >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e es sa sm s0 mid
    (BytesV bs) v s` by metis_tac[] >>
  drule_all hash_fixed_post_view >> strip_tac >>
  `fn_has_code sm sn func` by metis_tac[fn_has_code_split] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (qpat_assum `lower_value _ _ _ _ sa = _`
      (mp_tac o MATCH_MP (cj 2 compile_expr_grows)) >> simp[]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_word >> simp[is_word_type_def]) >>
  `expr_store_bound cx (expr_type e) (BytesV bs) v s` by metis_tac[] >>
  `run_inst_seq_mem_ok (emitted_insts sm sn) s` by
    (qpat_assum `expr_post _ _ _ _ _ e es sa sm s0 mid (BytesV bs) v s`
       (mp_then Any mp_tac keccak_typed_suffix_mem_ok_open_free) >>
     simp[is_bytestring_type_def]) >>
  `!z. v = Var z ==> not_fresh_at sm z` by
    metis_tac[compile_lower_value_var] >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid s` by
    metis_tac[exprSimWordArgsTheory.expr_post_state] >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by
    (irule (SRULE [] (Q.INST [`sha` |-> `F`] hash_fixed_alloca_code)) >> metis_tac[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[loweringStateRelDefsTheory.not_fresh_at_def, arithmeticTheory.LE_TRANS] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ ghost_inv_at _ _ _ _ _ mid G1 tn1 s`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >> fs[ghost_inv_at_def]) >>
  `sn.cs_current_bb = sm.cs_current_bb /\
   sn.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sn` by
    metis_tac[keccak_suffix_shape, same_blocks_def] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sm sn) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `fn_has_code sm sn func` mp_tac >>
     simp[fn_has_code_def] >> strip_tac >>
     qexists_tac `bb` >> gvs[rich_listTheory.IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,
       rich_listTheory.DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `op_taint tn1 v = {}` by fs[ptr_val_ok_def] >>
  drule_all (Q.INST [`PG` |-> `PG`, `G` |-> `G1`, `d` |-> `d`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] hash_fixed_keccak_joint_run) >>
  disch_then (qspecl_then [`shadow_ctx`, `d`, `PG`, `G1`] strip_assume_tac) >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`, `mid`, `INL (Value (BytesV (Keccak_256_w64 bs)))`,
    `u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sn)`, `tnf`] >>
  conj_tac >- simp[exprSimWordArgsTheory.builtin_result_def,
    vyperContextTheory.evaluate_builtin_def] >>
  rpt strip_tac >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >> simp[] >>
  `expr_post H ctx func cenv cx e es sa sm s0 mid (BytesV bs) v s /\
   ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 s` by metis_tac[] >>
  `vv_post H ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [e])
    es sa sn s0 mid (Value (BytesV (Keccak_256_w64 bs)))
    (StackValue (BaseT (BytesT (Fixed 32))) op) u` by
    (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
      (mp_then Any mp_tac keccak_fixed_post_run) >> simp[] >> strip_tac >> gvs[]) >>
  simp[vyperASTTheory.expr_type_def, exprSimMemDefsTheory.vv_store_bound_stack_word,
    compileEnvTheory.is_word_type_def, bodyPtrDefsTheory.ptr_vv_ok_def,
    bodyPtrDefsTheory.ptr_val_ok_def, contextTheory.vv_location_def,
    loweringPostsTheory.post_value_type_def, exprSimVVFrameTheory.vv_post_inst_idx,
    bytes_ghost_cursor] >>
  `stmt_state_rel H ctx func cenv cx mid s` by
    metis_tac[exprSimWordArgsTheory.expr_post_state] >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `ghost_inv_at (DF H) lo d cenv cx mid Gf tnf u /\
   ghost_kept_at lo cenv mid sm G1 tn1 s Gf tnf` by metis_tac[] >>
  `alloca_history func
    (u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sn))` by
    (irule allocaHistoryFragmentTheory.alloca_history_run_inst_seq >>
     goal_assum (drule_at Any) >> simp[] >>
     `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sn)` by
       (drule bodyPtrHashBuiltinsKeccakFixedRunTheory.hash_fixed_keccak_emission >>
        simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
     gvs[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]) >>
  `wb_frame cenv es mid sa s0 s` by metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf` by
    (`stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0` by
       (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
         (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
     drule_all hash_ghost_kept_wb_trans >> simp[]) >>
  gvs[vyperStateTheory.read_result_def, vyperStateTheory.return_def,
    bytes_ghost_cursor]
QED

Resume keccak_vv_sim_full[dynamic]:
  rename1 `expr_type e = BaseT (BytesT (Dynamic cap))` >>
  gvs[is_bytestring_type_def, as_stack_val_def] >>
  Cases_on `v'` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `expr_post _ _ _ _ _ e es sa sm s0 mid (BytesV bs) v s` >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e es sa sm s0 mid
     (BytesV bs) v s` by metis_tac[] >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic cap)))` by
    (drule expr_body_pre_type_evaluates >>
     simp[vyperValueTheory.evaluate_type_def] >> strip_tac >> gvs[]) >>
  drule_all hash_dynamic_post_view >> strip_tac >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  Cases_on `compile_keccak256_bytes v sm` >>
  simp[as_stack_val_def] >> strip_tac >> gvs[] >>
  `~is_word_type (BaseT (BytesT (Dynamic cap)))` by simp[is_word_type_def] >>
  drule_all hash_dynamic_bytes_operand >> strip_tac >>
  `!z. v = Var z ==> not_fresh_at sm z` by
    (metis_tac[compile_lower_value_var]) >>
  gvs[ptr_covers_def, eval_operand_def] >>
  `b < dimword (:256)` by decide_tac >>
  `b + 32 + LENGTH bs <= s.vs_alloca_next` by
    (qpat_x_assum `expr_store_bound _ _ _ _ _` mp_tac >>
     simp[exprSimMemDefsTheory.expr_store_bound_def, eval_operand_def,
       exprSimPropsTheory.val_store_size_def, is_word_type_def] >>
     mp_tac (Q.SPEC `LENGTH (bs:word8 list)` exprSimPropsTheory.le_word_size_mul) >>
     decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts sm r) s` by
    (irule keccak_memory_suffix_mem_ok >>
     qexistsl_tac [`b`, `LENGTH bs`, `q`, `Var p`] >>
     simp[eval_operand_def]) >>
  `fn_has_code sm r func` by metis_tac[fn_has_code_split] >>
  `r.cs_current_bb = sm.cs_current_bb /\
   r.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm r` by
    (metis_tac[keccak_suffix_shape, same_blocks_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sm r) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `fn_has_code sm r func` mp_tac >>
     simp[fn_has_code_def] >> strip_tac >>
     qexists_tac `bb` >> gvs[rich_listTheory.IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,
       rich_listTheory.DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qpat_assum `lower_value _ _ _ _ sa = _`
      (mp_tac o MATCH_MP (cj 2 compile_expr_grows)) >> simp[]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[loweringStateRelDefsTheory.not_fresh_at_def, arithmeticTheory.LE_TRANS] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ ghost_inv_at _ _ _ _ _ mid G1 tn1 s`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >> fs[ghost_inv_at_def]) >>
  `b + 32 + LENGTH bs <= b' + sz' /\
   LENGTH bs < dimword (:256) /\
   (!i. b <= i /\ i < b + 32 + LENGTH bs ==>
      i NOTIN tn1.t_mem) /\
   mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
   mem_bytes_at (b+32) (LENGTH bs) s.vs_memory =
     bs` by
    (simp[listTheory.LENGTH_MAP] >> rpt strip_tac >> gvs[] >>
     `b + 32 + LENGTH bs = b + (LENGTH bs + 32)` by decide_tac >> metis_tac[]) >>
  drule_all (SRULE [eval_operand_def] hash_bytes_keccak_joint_run) >>
  disch_then (qspecl_then [`PG`, `cx`, `mid`, `d`,
    `gas_explicit_sites ctx shadow_ctx`] strip_assume_tac) >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`, `mid`,
    `INL (Value (BytesV (Keccak_256_w64 bs)))`,
    `t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm r)`, `tnf`] >>
  conj_tac >- simp[exprSimWordArgsTheory.builtin_result_def,
    vyperContextTheory.evaluate_builtin_def] >>
  rpt strip_tac >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  simp[] >>
  `expr_post H ctx func cenv cx e es sa sm s0 mid (BytesV bs) (Var p) s /\
   ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 s` by metis_tac[] >>
  `vv_post H ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [e])
    es sa r s0 mid (Value (BytesV (Keccak_256_w64 bs)))
    (StackValue (BaseT (BytesT (Fixed 32))) q) t` by
    (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac keccak_memory_post_run) >>
     simp[eval_operand_def] >> strip_tac >> gvs[] >>
     first_x_assum irule >> simp[listTheory.LENGTH_MAP] >>
     qexists_tac `b` >> simp[]) >>
  simp[vyperASTTheory.expr_type_def, exprSimMemDefsTheory.vv_store_bound_stack_word,
    compileEnvTheory.is_word_type_def, bodyPtrDefsTheory.ptr_vv_ok_def,
    bodyPtrDefsTheory.ptr_val_ok_def, contextTheory.vv_location_def,
    loweringPostsTheory.post_value_type_def] >>
  `stmt_state_rel H ctx func cenv cx mid s` by
    metis_tac[exprSimWordArgsTheory.expr_post_state] >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `ghost_inv_at (DF H) lo d cenv cx mid Gf tnf
    (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm r)) /\
   ghost_kept_at lo cenv mid sm G1 tn1 s Gf tnf` by metis_tac[] >>
  simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  `wb_frame cenv es mid sa s0 s` by
    metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (qpat_assum `lower_value _ _ _ _ sa = _`
      (mp_tac o MATCH_MP (cj 2 compile_expr_grows)) >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf` by
    (`stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0` by
       (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
         (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
     drule_all hash_ghost_kept_wb_trans >> simp[]) >>
  gvs[]
QED

Finalise keccak_vv_sim_full
