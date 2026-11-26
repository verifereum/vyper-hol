(* Join the actual SHA256 suffix to a reached linked operand. *)
Theory bodyShaHashSuffixMods
Ancestors
  bodyShaSuffixCodeMods bodyShaImplicitEndpointMods bodyShaUniformRunMods
  bodyShaFixedMachineMods bodyShaMemoryMachineMods bodyFullHashShaExitCursor
  bodyShaSuccessCertificateMods bodyShaAbortCertificateMods
  bodyForcedStorageFrameMods bodyWriteSubscriptSourceMods bodySimStmtFacts
  exprBodyPreProps exprSimHypsDefs exprSimHash exprSimWordArgs
  gasShadowCompileStmtHelpers gasShadowCompileBase bodyFullShared
  vyperTypeEvalCaseProofs[qualified,ignore_grammar]
  abiValueEncoding[qualified,ignore_grammar]
  vyperTypeCallGraph allocLimits supportedExprTraverse vyperTyping
  vyperTypeSystem vyperTypeExprSoundness constSubstCorrect compileEnv
  gasShadow exprLowering exprLoweringProps fragExec bodyFullPostsMods
  gasOutcomeFullMods gasContext gasExplicitSites gasShadowState gasShadowUnit
  vyperStorageFootprint vyperStorageTrace loweringPosts bodyPtrDefs
  venomInst venomState ptrDiscipline unitTransformDefs
  vyperValue vyperState vyperAST finite_map rich_list list

val sha_expr = ``Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e]``;
val sha_stack = ``StackValue (BaseT (BytesT (Fixed 32))) op``;
val sha_compile = ``\sm.
  if is_bytestring_type (expr_type e) then compile_sha256_bytes x sm
  else case expr_type e of
       BaseT (BytesT (Fixed m)) => compile_sha256_bytesm x m sm
     | _ => compile_sha256_word x sm``;
val sha_arg = ``expr_post_mods (H:(bool # bytes32 # type_value) list # num list) ctx func cenv cx e es sa sm s0 mid v x s /\
  expr_store_bound cx (post_value_type cenv e) v x s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s /\
  ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

Theorem sha_reached_source[local]:
  expr_body_pre_mods mods cenv cx env ^sha_expr es /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix ++ tail) =
          (INL v,mid with gas_obs := tail)) /\ mid.gas_obs = [] ==>
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) = (INL v,mid) /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  ?bty. expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
        evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
        value_has_type (BaseTV bty) v
Proof
  strip_tac >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) = (INL v,mid)` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac
  >- (drule_then mp_tac (REWRITE_RULE [ETA_THM] forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `is_bytes_or_string_type (expr_type e)` by
    (drule expr_body_pre_mods_well_typed >> simp[Once well_typed_expr_def] >>
     strip_tac >> drule (SRULE [] (Q.INST [`b` |-> `Sha256`] hash_builtin_types)) >> simp[]) >>
  `?bty. expr_type e = BaseT bty` by
    (Cases_on `expr_type e` >> gvs[is_bytes_or_string_type_def]) >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := prefix)` by
    (simp[write_subscript_source_gas_obs_mods] >>
     qpat_x_assum `expr_body_pre_mods _ _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_mods_def, Once well_typed_expr_def,
          byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
          expr_has_evm_run_thm, supported_expr_exists_def, DISJ_IMP_THM,
          FORALL_AND_THM, frame_well_typed_exprs_cons]) >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >>
  `env.type_defs = get_tenv cx` by
    (drule expr_sim_inv_mods_env >>
     disch_then (irule o MATCH_MP vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv)) >>
  gvs[value_runtime_typed_def] >>
  drule abiValueEncodingTheory.evaluate_type_base_result >> strip_tac >> gvs[]
QED

Theorem sha_type_route[local]:
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) ==>
  (?m. bty = BytesT (Fixed m)) \/
  (((?k. bty = StringT k) \/ (?k. bty = BytesT (Dynamic k))) /\
   is_bytestring_type (expr_type e))
Proof
  strip_tac >> Cases_on `bty` >> gvs[is_bytes_or_string_type_def, is_bytestring_type_def] >>
  rename1 `expr_type e = BaseT (BytesT bd)` >>
  Cases_on `bd` >> gvs[is_bytestring_type_def]
QED

Theorem sha_stack_pair[local]:
  as_stack_val ty p = (StackValue ty op,sb) <=> p = (op,sb)
Proof
  Cases_on `p` >> simp[as_stack_val_def]
QED

Theorem sha_compile_cut[local]:
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_expr cenv ty ^sha_expr sa = (^sha_stack,sb) ==>
  (^sha_compile) sm = (op,sb)
Proof
  strip_tac >> qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_hash_singleton, sha_stack_pair]
QED

Theorem sha_compiler_appends[local]:
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) ==>
  cs_appends (^sha_compile)
Proof
  strip_tac >> drule_all_then strip_assume_tac sha_type_route >>
  simp[is_bytestring_type_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[hash_suffix_appends]
QED

Theorem sha_reached_compile[local]:
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_expr cenv ty ^sha_expr sa = (^sha_stack,sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^sha_expr) shadow_sa =
    (^sha_stack,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func ==>
  (^sha_compile) sm = (op,sb) /\ fn_has_code sm sb func /\
  ?shadow_sm. (^sha_compile) shadow_sm = (op,shadow_sb) /\
    gas_shadow_state sm shadow_sm /\ fn_has_code shadow_sm shadow_sb shadow_func
Proof
  strip_tac >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
     (gas_shadow_expr e) shadow_sa` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = (sx,shadow_sm)` >>
  `sx = x /\ gas_shadow_state sm shadow_sm` by
    (irule gas_shadow_step >>
     qexistsl_tac [`lower_value compile_expr cenv (expr_type e) e`,
       `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e)`,
       `sa`, `shadow_sa`] >>
     asm_rewrite_tac[gas_shadow_stmt_lower_value_env]) >>
  qpat_x_assum `sx = x` SUBST_ALL_TAC >>
  `(^sha_compile) sm = (op,sb)` by
    (qpat_assum `compile_expr cenv ty (Builtin _ _ _) _ = _`
       (mp_then Any mp_tac sha_compile_cut) >> simp[]) >>
  `(^sha_compile) shadow_sm = (op,shadow_sb)` by
    (qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
       (mp_tac o SIMP_RULE (srw_ss()) [gas_shadow_expr_def, gas_shadow_builtin_def]) >>
     disch_then (mp_then Any mp_tac sha_compile_cut) >>
     disch_then (qspecl_then [`x`,`shadow_sm`] mp_tac) >>
     pure_rewrite_tac[gas_shadow_expr_type] >>
     disch_then irule >> first_assum ACCEPT_TAC) >>
  `cs_appends (^sha_compile)` by (irule sha_compiler_appends >> goal_assum (drule_at Any) >> simp[]) >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    (qpat_assum `cs_appends _` (strip_assume_tac o REWRITE_RULE[cs_appends_def]) >>
     conj_tac >> first_x_assum irule >> qexists_tac `op` >> simp[]) >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    (conj_tac >- (qpat_assum `lower_value _ _ _ e sa = _`
       (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[]) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _`
       (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[]) >>
  `fn_has_code sm sb func /\ fn_has_code shadow_sm shadow_sb shadow_func` by
    metis_tac[fn_has_code_split] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexists_tac `shadow_sm` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

val sha_success = ``?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success``;
val sha_abort = ``if s.vs_outcomes = [] then ExHalt_abort else Revert_abort``;
val sha_run_post = ``if ^sha_success then
    ?z outcome rest. r = OK z /\ s.vs_outcomes = outcome::rest /\ outcome.co_success /\
      ghost_inv_at (DF (H:(bool # bytes32 # type_value) list # num list)) 0 d cenv cx
        (mid with outcomes := SOME rest) Gf tf (z with vs_inst_idx := s.vs_inst_idx + 7) /\
      ghost_kept_at 0 cenv mid sm G tn s Gf tf /\ op_taint tf op = {} /\ op_prov Gf op = NONE /\
      (!p. not_fresh_at sm p ==> lookup_var p z = lookup_var p s) /\ pure_frame cenv func mid sm s z
    else ?z. r = Abort (^sha_abort) z``;

Theorem sha_machine_at_horizon[local]:
  ^sha_arg /\ expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  (^sha_compile) sm = (op,sb) /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s /\
  ?r Gf tf. run_inst_seq (emitted_insts sm sb) s = r /\
    inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sm sb) s Gf tf /\
    ^sha_run_post
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all sha_type_route >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac (CONJUNCTS_THEN assume_tac))
  >- (qpat_x_assum `bty = BytesT (Fixed _)` SUBST_ALL_TAC >>
      `?bs. v = BytesV bs` by (Cases_on `v` >> gvs[value_has_type_def]) >>
      qpat_x_assum `v = BytesV _` SUBST_ALL_TAC >>
      `m <= 32` by
        (qpat_assum `expr_type e = _` (fn th =>
           qpat_assum `evaluate_type _ _ = _` (mp_tac o REWRITE_RULE[th])) >>
         simp[NoAsms, evaluate_type_def, AllCaseEqs()]) >>
      `post_value_type cenv e = expr_type e` by
        (irule post_value_type_word >> simp[is_word_type_def]) >>
      `expr_store_bound cx (expr_type e) (BytesV bs) x s` by
        (qpat_assum `post_value_type cenv e = _` (fn th =>
           qpat_assum `expr_store_bound _ _ _ _ _` (ACCEPT_TAC o REWRITE_RULE[th]))) >>
      `compile_sha256_bytesm x m sm = (op,sb)` by
        (qpat_assum `expr_type e = _` (fn th =>
           qpat_assum `(^sha_compile) sm = _` (mp_tac o REWRITE_RULE[th])) >>
         simp[NoAsms, is_bytestring_type_def]) >>
      drule_all sha_fixed_machine_mods >>
      disch_then (qspec_then `PG` strip_assume_tac) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`r`,`Gf`,`tf`] >>
      (conj_tac >- first_assum ACCEPT_TAC) >> (conj_tac >- first_assum ACCEPT_TAC) >>
      Cases_on `^sha_success` >>
      qpat_x_assum `if ^sha_success then _ else _` mp_tac >> asm_rewrite_tac[] >> strip_tac
      >- (qexistsl_tac [`z`,`outcome`,`rest`] >> asm_rewrite_tac[]) >>
      qexists_tac `z` >> first_assum ACCEPT_TAC) >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_bytestring >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `post_value_type cenv e = _` (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  `compile_sha256_bytes x sm = (op,sb)` by
    (qpat_assum `is_bytestring_type (expr_type e)` (fn th =>
       qpat_assum `(^sha_compile) sm = _` (ACCEPT_TAC o REWRITE_RULE [th] o BETA_RULE))) >>
  qhdtm_x_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE[expr_post_mods_def]) >>
  drule_all sha_memory_machine_mods >>
  disch_then (qspec_then `PG` (strip_assume_tac o BETA_RULE o REWRITE_RULE[LET_THM])) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`r`,`Gf`,`tf`] >>
  (conj_tac >- first_assum ACCEPT_TAC) >> (conj_tac >- first_assum ACCEPT_TAC) >>
  Cases_on `^sha_success`
  >- (qpat_assum `^sha_success` (fn th => pure_rewrite_tac[EQT_INTRO th, COND_CLAUSES]) >>
      qpat_assum `^sha_success ==> _` (drule_then strip_assume_tac) >>
      qexistsl_tac [`z`,`outcome`,`rest`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `~(^sha_success)` (fn th => pure_rewrite_tac[EQF_INTRO th, COND_CLAUSES]) >>
  qpat_assum `~(^sha_success) ==> _` (drule_then ACCEPT_TAC)
QED

val sha_source = ``\(u:evaluation_state).
  case builtin_result cx u.accounts (BaseT (BytesT (Fixed 32))) Sha256 [expr_type e] [v] of
    INR exc => (INR exc,u)
  | INL w => (do precompile_call_success Sha256 [v]; return (Value w) od) u``;
val sha_q = ``\(H:(bool # bytes32 # type_value) list # num list) (res:eval_result + exception) ee G tn t.
  ?tv. res = INL tv /\
    vv_post_mods H ctx func cenv cx ^sha_expr es sa sb s0 ee tv ^sha_stack t /\
    vv_store_bound cx (post_value_type cenv ^sha_expr) (lowered_value_type cenv ^sha_expr)
      ee tv ^sha_stack t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
    ptr_vv_ok cx (post_value_type cenv ^sha_expr) tv ^sha_stack ee G tn t /\
    (!v. tv = Value v /\ ~is_word_type (post_value_type cenv ^sha_expr) /\
         ~is_bytestring_type (post_value_type cenv ^sha_expr) ==>
         vv_own cenv cx (post_value_type cenv ^sha_expr) sa sb ee tv ^sha_stack t /\
         (!t' p. ^sha_stack = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
    (cenv.ce_is_ctor /\ vv_location ^sha_stack = SOME LocCode ==>
     ?v. read_result cx tv ee = (INL v,ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv ^sha_expr) = SOME rt /\
                eval_operand (vv_operand ^sha_stack) t = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                       val_in_memory rt v (w2n w) mem)) /\
    (!t' op'. ^sha_stack = StackValue t' op' /\ ~is_word_type (post_value_type cenv ^sha_expr) ==>
              ptr_buf_ok cenv ^sha_expr op' G t) /\
    (!t' p. ^sha_stack = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok cenv ^sha_expr p.ptr_operand G t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;
val sha_exit = ``\(H:(bool # bytes32 # type_value) list # num list) (res:eval_result + exception)
                    ee (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;

Theorem sha_suffix_landing_code[local]:
  fn_has_code sm sb func /\ same_blocks sm sb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  simp[fn_has_code_def, same_blocks_def] >> strip_tac >>
  qexists_tac `bb` >> simp[] >> fs[IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem sha_hash_suffix_mods:
  expr_body_pre_mods mods cenv cx env ^sha_expr es /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_expr cenv ty ^sha_expr sa = (^sha_stack,sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^sha_expr) shadow_sa =
    (^sha_stack,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix ++ tail) =
          (INL v,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==> ^sha_arg) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 ^sha_source (mid,s,G,tn) ^sha_q ^sha_exit
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac sha_reached_source >>
  drule_all_then (strip_assume_tac o BETA_RULE) sha_reached_compile >>
  drule_all_then strip_assume_tac sha_suffix_code_mods >>
  drule_all_then strip_assume_tac sha_suffix_landing_code >>
  `(ctx_has_dalloca ctx ==> !pre i post u. emitted_insts sm sb = pre ++ i::post /\
       run_inst_seq pre s = OK u ==> dalloca_no_wrap i u)` by
    (rpt strip_tac >>
     qpat_assum `emitted_insts sm sb = pre ++ i::post` (fn th =>
       qpat_assum `EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts sm sb)`
         (mp_tac o REWRITE_RULE[th])) >>
     simp[NoAsms, EVERY_APPEND, dalloca_no_wrap_def]) >>
  qabbrev_tac `J = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 J mid.storage_trace` by fs[Abbr `J`, storage_trace_domain_def] >>
  `valid_horizon cx st0 J es.storage_trace` by
    (drule_all (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] valid_horizon_frame)
       bodyForcedStorageFrameModsTheory.bop_forced_storage_frame) >> simp[]) >>
  `stmt_state_rel J ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` (drule_then ACCEPT_TAC)) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    run_inst_seq_mem_ok (emitted_insts sm sb) s /\
    ?r Gf tf. run_inst_seq (emitted_insts sm sb) s = r /\
      inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sm sb) s Gf tf /\ ^sha_run_post` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     drule_all (BETA_RULE sha_machine_at_horizon) >> disch_then (qspec_then `PG` ACCEPT_TAC)) >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) s` by
    (first_x_assum (qspec_then `J` (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
  `?r Gf tf. run_inst_seq (emitted_insts sm sb) s = r /\
     !H. valid_horizon cx st0 H mid.storage_trace ==>
       inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sm sb) s Gf tf /\ ^sha_run_post` by
    (irule (BETA_RULE (Q.INST [`P` |-> `\H r Gf tf. ^sha_run_post`] sha_uniform_run_mods)) >>
     (reverse conj_tac >- (qexists_tac `J` >> first_assum ACCEPT_TAC)) >>
     gen_tac >> disch_tac >> first_x_assum (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  Cases_on `^sha_success` >- suspend "success" >> suspend "abort"
QED

Resume sha_hash_suffix_mods[success]:
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `J` (drule_then strip_assume_tac)) >>
  qpat_assum `if ^sha_success then _ else _` mp_tac >>
  qpat_assum `^sha_success` (fn th => pure_rewrite_tac[EQT_INTRO th, COND_CLAUSES]) >>
  strip_tac >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x s /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ^sha_arg`
    (qspec_then `J` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  (Q.SUBGOAL_THEN `?H:(bool # 256 word # type_value) list # num list.
                     stmt_state_rel H ctx func cenv cx es s0` assume_tac
    >- (qexists_tac `J` >> first_assum ACCEPT_TAC)) >>
  `run_inst_seq (emitted_insts sm sb) s = OK z` by metis_tac[] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sm sb) s Gf tf /\
    ghost_inv_at (DF H) 0 d cenv cx (mid with outcomes := SOME rest) Gf tf
      (z with vs_inst_idx := s.vs_inst_idx + 7)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qpat_x_assum `if ^sha_success then _ else _` mp_tac >>
     qpat_assum `^sha_success` (fn th => pure_rewrite_tac[EQT_INTRO th, COND_CLAUSES]) >>
     strip_tac >> gvs[] >> first_assum ACCEPT_TAC) >>
  drule_all_then (strip_assume_tac o BETA_RULE o REWRITE_RULE [LET_THM])
    sha_success_certificate_mods >>
  irule sha_implicit_endpoint_mods >> BETA_TAC >>
  qexistsl_tac [`Gf`,`SND (take_call_outcome NONE 2w (precompile_input Sha256 [v]) NONE mid)`,
    `OK (z with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb))`,
    `INL (Value w):eval_result + exception`,`tf`] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  (conj_tac >- first_assum ACCEPT_TAC) >> disj1_tac >>
  qexists_tac `z with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb)` >>
  (conj_tac >- REFL_TAC) >>
  qpat_assum `?tv. INL (Value w) = INL tv /\ _`
    (assume_tac o REWRITE_RULE[sumTheory.INL_11]) >>
  pure_rewrite_tac[sumTheory.INL_11] >> first_assum ACCEPT_TAC
QED

Resume sha_hash_suffix_mods[abort]:
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `J` (drule_then strip_assume_tac)) >>
  qpat_assum `if ^sha_success then _ else _` mp_tac >>
  qpat_assum `~(^sha_success)` (fn th => pure_rewrite_tac[EQF_INTRO th, COND_CLAUSES]) >>
  strip_tac >>
  `run_inst_seq (emitted_insts sm sb) s = Abort (^sha_abort) z` by metis_tac[] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sm sb) s Gf tf` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ^sha_arg`
    (qspec_then `J` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qhdtm_x_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  drule_then assume_tac expr_post_state >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid s` by
    (qpat_assum `stmt_state_rel J _ _ _ _ mid s` mp_tac >> simp[Abbr `J`]) >>
  `?w. builtin_result cx mid.accounts (BaseT (BytesT (Fixed 32))) Sha256 [expr_type e] [v] = INL w` by
    (irule sha256_typed_builtin_result >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all_then strip_assume_tac sha_abort_certificate_mods >>
  irule sha_implicit_endpoint_mods >> BETA_TAC >>
  qexistsl_tac [`Gf`,`ef`,`Abort (^sha_abort) (z with vs_inst_idx := j)`,
    `INR (Error (RuntimeError "precompile failed")):eval_result + exception`,`tf`] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  (conj_tac >- first_assum ACCEPT_TAC) >> disj2_tac >>
  (Q.SUBGOAL_THEN `compile_sha256_bytes x sm = (op,sb) \/
     (?m. compile_sha256_bytesm x m sm = (op,sb))` assume_tac
   >- (drule_all sha_type_route >>
     disch_then (DISJ_CASES_THEN2 strip_assume_tac (CONJUNCTS_THEN assume_tac))
     >- (disj2_tac >> qexists_tac `m` >>
         qpat_assum `expr_type e = BaseT bty` (fn ty_eq =>
           qpat_assum `bty = BytesT (Fixed m)` (fn fixed_eq =>
             qpat_assum `(if _ then compile_sha256_bytes x sm else _) = _`
               (mp_tac o REWRITE_RULE [ty_eq,fixed_eq]))) >>
         simp[NoAsms, is_bytestring_type_def]) >>
     disj1_tac >>
     qpat_assum `is_bytestring_type (expr_type e)` (fn is_bytes =>
       qpat_assum `(if _ then compile_sha256_bytes x sm else _) = _`
         (ACCEPT_TAC o REWRITE_RULE [is_bytes])))) >>
  `create_size_exit_ok ctx
     (INR (Error (RuntimeError "precompile failed")):eval_result + exception)
     (Abort (^sha_abort) (z with vs_inst_idx := j))` by
    (drule_all (Q.INST_TYPE [`:'a` |-> `:eval_result`] sha_abort_path_exit_size) >>
     disch_then irule) >>
  simp[exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def, exit_result_def]
QED

Finalise sha_hash_suffix_mods
