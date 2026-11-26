(* Source and compiler entry facts at a successful runtime MethodId operand. *)
Theory bodyMethodIdRuntimeInputMods
Ancestors
  bodyFullPostsMods bodySimStmtFacts exprBodyPreProps exprSimHash exprSimWordArgs
  bodyFullHashKeccakFixed[qualified,ignore_grammar] constSubstCorrect
  vyperTypeEvalCaseProofs[qualified,ignore_grammar] vyperTypeExprSoundness
  abiValueEncoding[qualified,ignore_grammar] freshWrites
  bodyWriteSubscriptSourceMods exprSimHypsDefs vyperTypeSystem vyperTypeCallGraph vyperInterpreter vyperState
  allocLimits supportedExprTraverse compileEnv vyperContext vyperAST finite_map
  exprLoweringProps builtinHashing fragExec bodyMemoryDefs bodyPtrDefs
  loweringPosts vyperStorageTrace vyperStorageFootprint emitHelper venomInst vyperValue ptrDiscipline

Theorem method_id_operand_pre_mods:
  expr_body_pre_mods mods cenv cx env (Builtin ann MethodId [e]) es ==>
  expr_body_pre_mods mods cenv cx env e es
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def,
       byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
       expr_has_evm_run_thm, supported_expr_exists_def, DISJ_IMP_THM,
       FORALL_AND_THM, frame_well_typed_exprs_cons]
QED

Theorem method_id_runtime_source_mods[local]:
  expr_body_pre_mods mods cenv cx env (Builtin ann MethodId [e]) es /\
  (?xs. !tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs ++ tail) =
               (INL v,mid with gas_obs := tail)) /\ mid.gas_obs = [] ==>
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  ?bty. expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
        evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
        value_has_type (BaseTV bty) v
Proof
  strip_tac >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs) = (INL v,mid)` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[]) >>
  conj_tac
  >- (drule_then mp_tac (REWRITE_RULE [ETA_THM] forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `is_bytes_or_string_type (expr_type e)` by
    (drule expr_body_pre_mods_well_typed >> simp[Once well_typed_expr_def] >>
     strip_tac >> drule (SRULE [] (Q.INST [`b` |-> `MethodId`] hash_builtin_types)) >> simp[]) >>
  `?bty. expr_type e = BaseT bty` by
    (Cases_on `expr_type e` >> gvs[is_bytes_or_string_type_def]) >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := xs)` by
    (irule method_id_operand_pre_mods >> qexists_tac `ann` >>
     simp[write_subscript_source_gas_obs_mods]) >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >>
  `env.type_defs = get_tenv cx` by
    (drule expr_sim_inv_mods_env >>
     disch_then (irule o MATCH_MP vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv)) >>
  gvs[value_runtime_typed_def] >>
  drule abiValueEncodingTheory.evaluate_type_base_result >> strip_tac >> gvs[]
QED

Theorem method_id_runtime_code_mods[local]:
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_method_id_runtime (expr_type e) x fixed sm = (op,sb) /\
  fn_has_code sa sb func ==>
  cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  cs_extends sm sb /\ fn_has_code sa sm func /\ fn_has_code sm sb func /\
  ?hash sh sel sn word sp.
    compile_method_id_hash (expr_type e) x sm = (hash,sh) /\
    fn_has_code sm sh func /\ fn_has_code sh sb func /\
    emit_op SHR [Lit 224w; hash] sh = (sel,sn) /\
    emit_op SHL [Lit 224w; sel] sn = (word,sp) /\
    fn_has_code sh sp func /\
    (if fixed then op = word /\ sb = sp
     else ?buf su data sd st. compile_alloc_buffer 64 sp = (buf,su) /\
       emit_void MSTORE [buf.buf_operand; Lit 4w] su = ((),st) /\
       emit_op ADD [buf.buf_operand; Lit 32w] st = (data,sd) /\
       emit_void MSTORE [data; word] sd = ((),sb) /\ op = buf.buf_operand /\
       fn_has_code sp sb func /\
       MEM (mk_inst sp.cs_next_id ALLOCA [Lit 64w]
         [STRING #"%" (toString sp.cs_next_var)]) (fn_insts func))
Proof
  strip_tac >> drule_then strip_assume_tac (cj 2 compile_expr_grows) >>
  `cs_extends sm sb` by
    (mp_tac (cj 5 hash_suffix_appends) >> simp[cs_appends_def] >>
     disch_then (qspecl_then [`expr_type e`,`x`,`fixed`,`sm`] mp_tac) >> simp[]) >>
  drule_all_then strip_assume_tac fn_has_code_split >>
  drule_then strip_assume_tac hash_method_id_runtime_cut >>
  drule_all_then strip_assume_tac hash_method_id_hash_cut >>
  simp[] >> Cases_on `fixed` >> gvs[] >>
  drule_all_then strip_assume_tac hash_method_id_mask_cut >>
  simp[]
QED

Theorem method_id_runtime_input_mods:
  expr_body_pre_mods mods cenv cx env (Builtin ann MethodId [e]) es /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_method_id_runtime (expr_type e) x fixed sm = (op,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  return_buf_frame d cenv sa s0 /\ storage_trace_domain cx st0 mid.storage_trace /\
  (?xs. !tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs ++ tail) =
    (INL v,mid with gas_obs := tail)) /\ mid.gas_obs = [] /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x s /\
       s0.vs_alloca_next <= s.vs_alloca_next) ==>
  valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  (?bty. expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\ value_has_type (BaseTV bty) v) /\
  cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  cs_extends sm sb /\ fn_has_code sa sm func /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sm /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  return_buf_frame d cenv sm s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (?hash sh sel sn word sp.
    compile_method_id_hash (expr_type e) x sm = (hash,sh) /\
    fn_has_code sm sh func /\ fn_has_code sh sb func /\
    emit_op SHR [Lit 224w; hash] sh = (sel,sn) /\
    emit_op SHL [Lit 224w; sel] sn = (word,sp) /\ fn_has_code sh sp func /\
    (if fixed then op = word /\ sb = sp
     else ?buf su data sd st. compile_alloc_buffer 64 sp = (buf,su) /\
       emit_void MSTORE [buf.buf_operand; Lit 4w] su = ((),st) /\
       emit_op ADD [buf.buf_operand; Lit 32w] st = (data,sd) /\
       emit_void MSTORE [data; word] sd = ((),sb) /\ op = buf.buf_operand /\
       fn_has_code sp sb func /\
       MEM (mk_inst sp.cs_next_id ALLOCA [Lit 64w]
         [STRING #"%" (toString sp.cs_next_var)]) (fn_insts func)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac method_id_runtime_source_mods >>
  drule_all_then strip_assume_tac method_id_runtime_code_mods >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  first_x_assum (drule_then strip_assume_tac) >>
  qhdtm_x_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  drule_then (assume_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) expr_post_state >>
  simp[] >> rpt conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[])
  >- metis_tac[not_fresh_at_mono]
  >- metis_tac[not_fresh_at_mono] >>
  irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
  fs[expr_post_def]
QED
