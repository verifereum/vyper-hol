(* Joint finite-horizon SHA256 leaf. *)
Theory bodyFullHashSha
Ancestors
  bodyFullHashShaAlloc bodyFullHashShaPrefix bodyFullHashShaTail bodyFullHashShaOrigin
  bodyFullHashShaFixedSuccess bodyPtrHashBuiltinsShaFixed
  bodyFullHashShaGas bodyFullHashShaFixedAbort bodyFullHashShaAbortOrigin
  bodyFullHashShaLayout fragGasSeqPtr
  bodyFullHashShaBytesSuccess bodyPtrHashBuiltinsShaStringInput
  bodyPtrHashBuiltinsInputWindow
  bodyFullHashKeccakBytes allocaHistoryFragment venomInstProps
  list rich_list arithmetic venomExecSemantics
  bodyFullHashCleanFrame bodyMemBiSha256Compose bodyPtrHashBuiltinsShaSource
  bodyPtrHashBuiltinsCases exprOperandVar bodyPtrDefs ptrDiscipline venomState
  bodySimFull bodyFullPreds gasOutcomeFullCompose fragExec
  exprSimHash exprSimHashBoundary exprSimHyps exprSimHypsDefs exprSimSource
  gasShadowCompile gasShadowCompileStmtHelpers gasShadowState gasShadow
  exprLoweringProps exprLowering loweringPosts compileEnv vyperTyping
  vyperInterpreter vyperState vyperAST vyperTypeSystem
  stmtSimProps gasExemptCert vyperStorageTrace vyperStorageFootprint

fun sha_memory_prepare_tac g = (
  `eval_operand (Var p) s = SOME (n2w b)` by simp[eval_operand_def] >>
  `b+32+LENGTH bs <= b'+sz'` by decide_tac >>
  `!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn1.t_mem` by
    (rpt strip_tac >>
     qpat_assum `!i. _ ==> i NOTIN tn1.t_mem` (qspec_then `i` mp_tac) >>
     (impl_tac >- decide_tac) >> simp[]) >>
  `op_taint tn1 (Var p) = {}` by fs[op_taint_def] >>
  `fn_has_code sm sn func` by metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid s` by
    metis_tac[exprSimWordArgsTheory.expr_post_state] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[loweringStateRelDefsTheory.not_fresh_at_def, arithmeticTheory.LE_TRANS] >>
  `MEM (mk_inst (sm.cs_next_id+2) ALLOCA [Lit 32w]
     [STRING #"%" (toString (sm.cs_next_var+2))]) (fn_insts func)` by
    metis_tac[hash_sha256_memory_alloca_code] >>
  `sn.cs_current_bb = sm.cs_current_bb /\
   sn.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sn /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sn)` by
    (mp_tac (Q.INST [`x` |-> `Var p`, `sa` |-> `sm`, `sb` |-> `sn`,
       `op` |-> `op`, `m` |-> `0`] hash_buffer_suffix_shape) >>
     simp[same_blocks_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sm sn) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `fn_has_code sm sn func` mp_tac >>
     simp[fn_has_code_def] >> strip_tac >>
     qexists_tac `bb` >> gvs[rich_listTheory.IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,
       rich_listTheory.DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts sm sn) s` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
       expr_post H ctx func cenv cx e es sa sm s0 mid _ (Var p) s /\ _`
       (fn family => qpat_assum
         `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
         (fn valid => (mp_then Any mp_tac sha256_typed_suffix_mem_ok)
           (CONJUNCT1 (MATCH_MP (Q.SPEC `storage_trace_horizon mid.storage_trace` family) valid)))) >>
     simp[is_bytestring_type_def]) >>
  `ghost_inv_at (DF (storage_trace_horizon mid.storage_trace)) lo d cenv cx mid G1 tn1 s` by
    metis_tac[] >>
  `compile_sha256_bytes (Var p) shadow_sm = (op,shadow_sb)` by
    (qpat_x_assum `compile_expr cenv ty (gas_shadow_expr _) shadow_sa = _` mp_tac >>
     simp[gas_shadow_expr_def, gas_shadow_builtin_def, compile_hash_singleton,
       is_bytestring_type_def] >>
     Cases_on `compile_sha256_bytes (Var p) shadow_sm` >>
     simp[as_stack_val_def] >> strip_tac >> gvs[]) >>
  `fn_has_code shadow_sm shadow_sb shadow_func` by metis_tac[fn_has_code_split] >>
  `MAP (\i. (func.fn_name,i.inst_id) IN gas_explicit_sites ctx shadow_ctx)
    (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sn)) = [F]` by
    (irule sha_bytes_gas_classified >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[])
) g;

fun sha_memory_abort_origin_tac g = (
`!outcome rest. s.vs_outcomes = outcome::rest ==> ~outcome.co_success` by
    (qpat_assum `~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  drule_all sha_bytes_abort_ptr_at >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    inst_seq_ptr (DF H) lo ctx func PG G1 tn1 (emitted_insts sm sn) s Gf tf` by
    (gen_tac >> disch_tac >>
     `ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 s` by metis_tac[] >>
     `stmt_state_rel H ctx func cenv cx mid s` by
       metis_tac[exprSimWordArgsTheory.expr_post_state] >>
     mp_tac (Q.INST [`D` |-> `DF H`, `H` |-> `H`, `lo` |-> `lo`,
       `ctx` |-> `ctx`, `fn` |-> `func`, `PG` |-> `PG`,
       `G` |-> `G1`, `tn` |-> `tn1`, `s` |-> `s`, `bb` |-> `bb`,
       `x` |-> `p`, `sa` |-> `sm`, `op` |-> `op`, `sb` |-> `sn`,
       `b` |-> `b`, `rootbase` |-> `b'`, `cap` |-> `sz'`,
       `n` |-> `LENGTH (bs:word8 list)`, `d` |-> `d`,
       `cenv` |-> `cenv`, `cx` |-> `cx`, `es` |-> `mid`]
       (SPEC_ALL sha_bytes_abort_ptr_at)) >>
     (impl_tac >- simp[]) >>
     disch_then (qx_choosel_then [`u`, `G2`, `tn2`] strip_assume_tac) >>
     `G2 = Gf /\ tn2 = tf` by
       (qpat_assum `inst_seq_ptr (DF H) lo ctx func PG G1 tn1 _ s G2 tn2` mp_tac >>
        qpat_assum `inst_seq_ptr (DF (storage_trace_horizon mid.storage_trace))
          lo ctx func PG G1 tn1 _ s Gf tf` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[inst_seq_ptr_ghost_unique]) >>
     gvs[]) >>
  qpat_assum `compile_sha256_bytes _ sm = (op,sn)`
    (mp_then Any mp_tac sha_bytes_gas_layout) >> strip_tac >>
  `(func.fn_name,sm.cs_next_id+3) NOTIN gas_explicit_sites ctx shadow_ctx` by
    (qpat_assum `compile_sha256_bytes _ sm = (op,sn)`
       (mp_then Any mp_tac sha_bytes_gas_emitted) >> strip_tac >>
     qpat_assum `MAP _ (FILTER _ (emitted_insts sm sn)) = [F]` mp_tac >>
     simp[venomInstTheory.mk_inst_def]) >>
  qpat_assum `emitted_insts sm sn = _` SUBST_ALL_TAC >>
  drule_all sha_setup_gas_origin_abort_uniform >> strip_tac
) g;

fun sha_memory_abort_post_tac g = (
drule_all hash_sha256_source_failure >> strip_tac >>
  `ef.storage_trace = mid.storage_trace` by
    (Cases_on `s.vs_outcomes` >> gvs[]) >>
  `gas_explicit [F] s.vs_gas_readings = []` by
    ACCEPT_TAC (REWRITE_RULE [EVAL ``REPLICATE 1 F``]
      (Q.SPECL [`1`, `s.vs_gas_readings`]
        gasSummaryTheory.gas_explicit_replicate_false)) >>
  irule gas_outcome_full_intro >>
  qexistsl_tac [`Gf`, `ef`, `[F]`, `Abort Revert_abort (t with vs_inst_idx := j)`,
    `INR (Error (RuntimeError "precompile failed"))`, `tf`] >>
  conj_tac >-
    (simp[] >>
     qpat_assum `expr_type e = _` (fn ty_eq =>
       qpat_assum `ef = _` (fn state_eq =>
         qpat_assum `!tail. _ = (INR _,ef with gas_obs := tail)`
           (ACCEPT_TAC o SIMP_RULE (srw_ss()) [ty_eq,state_eq])))) >>
  rpt strip_tac >>
  simp[fragExecTheory.exit_result_def, exprSimDefsTheory.expr_exit_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _` mp_tac >>
  qpat_assum `ef.storage_trace = mid.storage_trace` mp_tac >>
  qpat_assum `valid_horizon cx st0 H ef.storage_trace` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]
) g;

fun sha_memory_success_endpoint_tac g = (
pop_assum strip_assume_tac >>
  `ghost_inv_at (DF (storage_trace_horizon mid.storage_trace)) lo d cenv cx mid G1 tn1 s` by
    metis_tac[] >>
  drule_all sha_bytes_success_frame_at >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    inst_seq_ptr (DF H) lo ctx func PG G1 tn1 (emitted_insts sm sn) s Gf tf /\
    ghost_inv_at (DF H) lo d cenv cx (mid with outcomes := SOME rest) Gf tf t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (fn family => qpat_assum `valid_horizon cx st0 H mid.storage_trace`
         (fn valid => strip_assume_tac (MATCH_MP (Q.SPEC `H` family) valid))) >>
     `stmt_state_rel H ctx func cenv cx mid s` by
       metis_tac[exprSimWordArgsTheory.expr_post_state] >>
     mp_tac (Q.INST [`D` |-> `DF H`, `H` |-> `H`, `lo` |-> `lo`,
       `ctx` |-> `ctx`, `fn` |-> `func`, `PG` |-> `PG`,
       `G` |-> `G1`, `tn` |-> `tn1`, `s` |-> `s`, `bb` |-> `bb`,
       `x` |-> `p`, `sa` |-> `sm`, `op` |-> `op`, `sb` |-> `sn`,
       `b` |-> `b`, `rootbase` |-> `b'`, `cap` |-> `sz'`,
       `n` |-> `LENGTH (bs:word8 list)`, `d` |-> `d`,
       `cenv` |-> `cenv`, `cx` |-> `cx`, `es` |-> `mid`,
       `bs` |-> `bs`, `outcome` |-> `outcome`, `rest` |-> `rest`]
       (SPEC_ALL sha_bytes_success_frame_at)) >>
     (impl_tac >- simp[]) >>
     disch_then (qx_choosel_then [`u`, `G2`, `tn2`] strip_assume_tac) >>
     `u = t` by
       (qpat_assum `run_inst_seq (emitted_insts sm sn) s = OK u` mp_tac >>
        qpat_assum `run_inst_seq (emitted_insts sm sn) s = OK t`
          (fn th => once_rewrite_tac[th]) >> simp[]) >>
     qpat_x_assum `u = t` SUBST_ALL_TAC >>
     `G2 = Gf /\ tn2 = tf` by
       (qpat_assum `inst_seq_ptr (DF H) lo ctx func PG G1 tn1 _ s G2 tn2` mp_tac >>
        qpat_assum `inst_seq_ptr (DF (storage_trace_horizon mid.storage_trace))
          lo ctx func PG G1 tn1 _ s Gf tf` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[inst_seq_ptr_ghost_unique]) >>
     gvs[bytes_ghost_cursor])
) g;

fun sha_memory_success_frame_tac g = (
`alloca_inv s` by fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sn)` by
    (qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) _`
      mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> simp[EVERY_CONJ]) >>
  `alloca_history func
    (t with vs_inst_idx := s.vs_inst_idx+LENGTH (emitted_insts sm sn))` by
    (irule alloca_history_run_inst_seq >> goal_assum (drule_at Any) >> simp[] >>
     gvs[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `run_inst_seq (emitted_insts sm sn) s = OK t` mp_tac >>
     qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) _`
       mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     irule (SRULE [] (Q.ISPEC `\s:venom_state. s.vs_current_bb` run_inst_seq_preserves_field)) >>
     goal_assum (drule_at Any) >> rpt strip_tac >>
     fs[EVERY_MEM] >> metis_tac[step_preserves_control_flow, step_inst_non_invoke]) >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    metis_tac[sha256_run_inst_seq_alloca_next_mono] >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by decide_tac >>
  `LENGTH sn.cs_current_insts = s.vs_inst_idx+LENGTH (emitted_insts sm sn)` by
    (qpat_assum `sn.cs_current_insts = sm.cs_current_insts ++ _`
      (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `wb_frame cenv es mid sa s0 s` by
    metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf` by
    (`stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0` by
       (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
         (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
     drule_all hash_ghost_kept_wb_trans >> simp[]) >>
  `(mid with outcomes := SOME rest) with gas_obs := [] = mid with outcomes := SOME rest` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `gas_explicit [F] s.vs_gas_readings = []` by
    ACCEPT_TAC (REWRITE_RULE [EVAL ``REPLICATE 1 F``]
      (Q.SPECL [`1`, `s.vs_gas_readings`] gasSummaryTheory.gas_explicit_replicate_false)) >>
  `!tail. ignore_bind (precompile_call_success Sha256)
    (return (Value (BytesV (word_to_bytes (SHA_256_bytes bs) T))))
    (mid with gas_obs := tail) =
    (INL (Value (BytesV (word_to_bytes (SHA_256_bytes bs) T))),
      (mid with outcomes := SOME rest) with gas_obs := tail)` by
    (qpat_assum `expr_type e = _` (fn te =>
       qpat_assum `builtin_result _ _ _ Sha256 [expr_type e] _ = _` (fn br =>
         drule_all hash_sha256_source_success >> simp[te, REWRITE_RULE [te] br])))
) g;

fun sha_memory_success_post_tac g = (
irule gas_outcome_full_intro >>
  qexistsl_tac [`Gf`, `mid with outcomes := SOME rest`, `[F]`,
    `OK (t with vs_inst_idx := s.vs_inst_idx+LENGTH (emitted_insts sm sn))`,
    `INL (Value (BytesV (word_to_bytes (SHA_256_bytes bs) T)))`, `tf`] >>
  qpat_assum `expr_type e = _` (fn te =>
    qpat_assum `builtin_result _ _ _ Sha256 [expr_type e] _ = _`
      (fn br => simp[REWRITE_RULE [te] br])) >>
  gen_tac >> disch_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by fs[] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (fn family => qpat_assum `valid_horizon cx st0 H mid.storage_trace`
         (fn valid => strip_assume_tac (MATCH_MP (Q.SPEC `H` family) valid))) >>
  `inst_seq_ptr (DF H) lo ctx func PG G1 tn1 (emitted_insts sm sn) s Gf tf /\
   ghost_inv_at (DF H) lo d cenv cx (mid with outcomes := SOME rest) Gf tf t` by
    metis_tac[] >>
  conj_tac
  >- (qpat_assum `MAP (\i. (func.fn_name,i.inst_id) IN gas_explicit_sites ctx shadow_ctx) _ = [F]`
        (fn th => once_rewrite_tac[GSYM th]) >>
      qpat_assum `s.vs_inst_idx = LENGTH sm.cs_current_insts`
        (fn th => once_rewrite_tac[GSYM th]) >>
      irule run_inst_seq_gas_origin_ptr_path >> simp[] >>
      qpat_assum `s.vs_inst_idx = LENGTH sm.cs_current_insts` (fn idx =>
        qpat_assum `isPREFIX (emitted_insts sm sn) (DROP s.vs_inst_idx bb.bb_instructions)`
          (ACCEPT_TAC o REWRITE_RULE [idx]))) >>
  simp[] >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `vv_post H ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])
    es sa sn s0 (mid with outcomes := SOME rest)
    (Value (BytesV (word_to_bytes (SHA_256_bytes bs) T)))
    (StackValue (BaseT (BytesT (Fixed 32))) op) t` by
    (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
      (mp_then Any (qspecl_then [`sn`, `rest`, `outcome`, `op`, `bs:word8 list`, `b`] mp_tac)
        sha256_memory_post_run) >>
     (impl_tac >- simp[]) >>
     disch_then (qx_choose_then `u` strip_assume_tac) >>
     `u = t` by
       (qpat_assum `run_inst_seq (emitted_insts sm sn) s = OK u` mp_tac >>
        qpat_assum `run_inst_seq (emitted_insts sm sn) s = OK t`
          (fn th => once_rewrite_tac[th]) >> simp[]) >>
     qpat_x_assum `u = t` SUBST_ALL_TAC >> first_assum ACCEPT_TAC) >>
  simp[vyperASTTheory.expr_type_def, exprSimMemDefsTheory.vv_store_bound_stack_word,
    compileEnvTheory.is_word_type_def, bodyPtrDefsTheory.ptr_vv_ok_def,
    bodyPtrDefsTheory.ptr_val_ok_def, contextTheory.vv_location_def,
    loweringPostsTheory.post_value_type_def, exprSimVVFrameTheory.vv_post_inst_idx,
    bytes_ghost_cursor, vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  qpat_assum `s.vs_inst_idx = LENGTH sm.cs_current_insts` (fn idx =>
    qpat_assum `alloca_history func
      (t with vs_inst_idx := s.vs_inst_idx+LENGTH (emitted_insts sm sn))`
      (ACCEPT_TAC o REWRITE_RULE [idx]))
) g;

Theorem sha_vv_sim_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx env ty ann e es.
    expr_body_pre cenv cx env (Builtin ann Sha256 [e]) es /\
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (expr_type e) e es ==>
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann Sha256 [e]) es
Proof
  rpt gen_tac >> strip_tac >>
  `is_bytes_or_string_type (expr_type e) /\ ann = BaseT (BytesT (Fixed 32))` by
    (irule (SRULE [] (Q.INST [`b` |-> `Sha256`,
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
  rewrite_tac[eval_expr_sha256_action] >> irule gas_outcome_full_bind_all >>
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
  >- simp[sha256_continuation_frame] >>
  qexists_tac `\H res ee G tn t. baseQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac
  >- suspend "hashed" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[Abbr `baseR`] >>
  simp[Abbr `baseQ`, Abbr `baseR`]
QED

Resume sha_vv_sim_full[hashed]:
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

Resume sha_vv_sim_full[fixed]:
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
  Cases_on `compile_sha256_bytesm v m sm` >> gvs[as_stack_val_def] >>
  rename1 `compile_sha256_bytesm v _ sm = (op,sn)` >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e es sa sm s0 mid
    (BytesV bs) v s` by metis_tac[] >>
  drule_all hash_fixed_post_view >> strip_tac >>
  `fn_has_code sm sn func` by metis_tac[fn_has_code_split] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (qpat_assum `lower_value _ _ _ _ sa = _`
      (mp_tac o MATCH_MP (cj 2 compile_expr_grows)) >> simp[]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!z. v = Var z ==> not_fresh_at sm z` by metis_tac[compile_lower_value_var] >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid s` by
    metis_tac[exprSimWordArgsTheory.expr_post_state] >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func) /\
   MEM (mk_inst (sm.cs_next_id+2) ALLOCA [Lit 32w]
      [STRING #"%" (toString (sm.cs_next_var+1))]) (fn_insts func)` by
    (drule_all (SRULE [] (Q.INST [`sha` |-> `T`] hash_fixed_alloca_code)) >> simp[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[loweringStateRelDefsTheory.not_fresh_at_def, arithmeticTheory.LE_TRANS] >>
  suspend "fixed_outcome"
QED

Resume sha_vv_sim_full[fixed_outcome]:
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_word >> simp[is_word_type_def]) >>
  `expr_store_bound cx (expr_type e) (BytesV bs) v s` by metis_tac[] >>
  `sn.cs_current_bb = sm.cs_current_bb /\
   sn.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sn /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sn)` by
    (mp_tac (Q.INST [`x` |-> `v`, `sa` |-> `sm`, `sb` |-> `sn`,
       `op` |-> `op`, `m` |-> `LENGTH (bs:word8 list)`] hash_buffer_suffix_shape) >>
     simp[same_blocks_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sm sn) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `fn_has_code sm sn func` mp_tac >>
     simp[fn_has_code_def] >> strip_tac >>
     qexists_tac `bb` >> gvs[rich_listTheory.IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,
       rich_listTheory.DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts sm sn) s` by
    (qpat_assum `expr_post _ _ _ _ _ e es sa sm s0 mid (BytesV bs) v s`
       (mp_then Any mp_tac sha256_typed_suffix_mem_ok) >>
     simp[is_bytestring_type_def, vyperTypingTheory.value_has_type_def]) >>
  `op_taint tn1 v = {}` by fs[ptr_val_ok_def] >>
  `compile_sha256_bytesm v (LENGTH bs) shadow_sm = (op,shadow_sb)` by
    (qpat_x_assum `compile_expr cenv ty (gas_shadow_expr _) shadow_sa = _` mp_tac >>
     simp[gas_shadow_expr_def, gas_shadow_builtin_def, compile_hash_singleton,
       is_bytestring_type_def] >>
     Cases_on `compile_sha256_bytesm v (LENGTH bs) shadow_sm` >>
     simp[as_stack_val_def] >> strip_tac >> gvs[]) >>
  `fn_has_code shadow_sm shadow_sb shadow_func` by metis_tac[fn_has_code_split] >>
  `MAP (\i. (func.fn_name,i.inst_id) IN gas_explicit_sites ctx shadow_ctx)
    (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sn)) = [F]` by
    (irule sha_fixed_gas_classified >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  Cases_on `?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success`
  >- suspend "fixed_success" >>
  suspend "fixed_abort"
QED

Resume sha_vv_sim_full[fixed_abort]:
  `!outcome rest. s.vs_outcomes = outcome::rest ==> ~outcome.co_success` by
    (qpat_assum `~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `ghost_inv_at (DF (storage_trace_horizon mid.storage_trace)) lo d cenv cx mid G1 tn1 s` by
    metis_tac[] >>
  drule_all sha_fixed_abort_ptr_at >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    inst_seq_ptr (DF H) lo ctx func PG G1 tn1 (emitted_insts sm sn) s Gf tf` by
    (gen_tac >> disch_tac >>
     `ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 s` by metis_tac[] >>
     `stmt_state_rel H ctx func cenv cx mid s` by
       metis_tac[exprSimWordArgsTheory.expr_post_state] >>
     mp_tac (Q.INST [`D` |-> `DF H`, `H` |-> `H`, `lo` |-> `lo`,
       `ctx` |-> `ctx`, `fn` |-> `func`, `PG` |-> `PG`,
       `G` |-> `G1`, `tn` |-> `tn1`, `s` |-> `s`, `bb` |-> `bb`,
       `value` |-> `v`, `m` |-> `LENGTH (bs:word8 list)`,
       `sa` |-> `sm`, `op` |-> `op`, `sb` |-> `sn`, `d` |-> `d`,
       `cenv` |-> `cenv`, `cx` |-> `cx`, `es` |-> `mid`]
       (Q.INST [`v` |-> `w`] (SPEC_ALL sha_fixed_abort_ptr_at))) >>
     (impl_tac >- simp[]) >>
     disch_then (qx_choose_then `u` (qx_choose_then `G2`
       (qx_choose_then `tn2` strip_assume_tac))) >>
     `G2 = Gf /\ tn2 = tf` by
       (qpat_assum `inst_seq_ptr (DF H) _ _ _ _ _ _ _ _ G2 tn2` mp_tac >>
        qpat_assum `inst_seq_ptr (DF (storage_trace_horizon mid.storage_trace))
          _ _ _ _ _ _ _ _ Gf tf` mp_tac >>
        rpt (pop_assum kall_tac) >> metis_tac[inst_seq_ptr_ghost_unique]) >>
     gvs[]) >>
  qpat_assum `compile_sha256_bytesm _ _ sm = (op,sn)`
    (mp_then Any mp_tac sha_fixed_gas_layout) >> strip_tac >>
  `(func.fn_name,sm.cs_next_id+3) NOTIN gas_explicit_sites ctx shadow_ctx` by
    (qpat_assum `compile_sha256_bytesm _ _ sm = (op,sn)`
       (mp_then Any mp_tac sha_fixed_gas_emitted) >> strip_tac >>
     qpat_assum `MAP _ (FILTER _ (emitted_insts sm sn)) = [F]` mp_tac >>
     simp[venomInstTheory.mk_inst_def]) >>
  qpat_assum `emitted_insts sm sn = _` SUBST_ALL_TAC >>
  drule_all sha_setup_gas_origin_abort_uniform >> strip_tac >>
  `builtin_result cx mid.accounts (BaseT (BytesT (Fixed 32))) Sha256
     [expr_type e] [BytesV bs] =
     INL (BytesV (word_to_bytes (SHA_256_bytes bs) T))` by
    simp[exprSimWordArgsTheory.builtin_result_def,
      vyperContextTheory.evaluate_builtin_def] >>
  drule_all hash_sha256_source_failure >> strip_tac >>
  `ef.storage_trace = mid.storage_trace` by
    (Cases_on `s.vs_outcomes` >> gvs[]) >>
  `gas_explicit [F] s.vs_gas_readings = []` by
    ACCEPT_TAC (REWRITE_RULE [EVAL ``REPLICATE 1 F``]
      (Q.SPECL [`1`, `s.vs_gas_readings`]
        gasSummaryTheory.gas_explicit_replicate_false)) >>
  irule gas_outcome_full_intro >>
  qexistsl_tac [`Gf`, `ef`, `[F]`, `Abort Revert_abort (t with vs_inst_idx := j)`,
    `INR (Error (RuntimeError "precompile failed"))`, `tf`] >>
  conj_tac >-
    (simp[] >>
     qpat_assum `expr_type e = _` (fn ty_eq =>
       qpat_assum `ef = _` (fn state_eq =>
         qpat_assum `!tail. _ = (INR _,ef with gas_obs := tail)`
           (ACCEPT_TAC o SIMP_RULE (srw_ss()) [ty_eq,state_eq])))) >>
  rpt strip_tac >>
  simp[fragExecTheory.exit_result_def, exprSimDefsTheory.expr_exit_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _` mp_tac >>
  qpat_assum `ef.storage_trace = mid.storage_trace` mp_tac >>
  qpat_assum `valid_horizon cx st0 H ef.storage_trace` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]
QED

Resume sha_vv_sim_full[string]:
  rename1 `expr_type e = BaseT (StringT cap)` >>
  gvs[is_bytestring_type_def, as_stack_val_def] >>
  Cases_on `v'` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `expr_post _ _ _ _ _ e es sa sm s0 mid (StringV str) v s` >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e es sa sm s0 mid
     (StringV str) v s` by metis_tac[] >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (StringT cap))` by
    (drule expr_body_pre_type_evaluates >>
     simp[vyperValueTheory.evaluate_type_def] >> strip_tac >> gvs[]) >>
  drule_all hash_string_post_view >> strip_tac >>
  Cases_on `compile_sha256_bytes v sm` >> gvs[as_stack_val_def] >>
  rename1 `compile_sha256_bytes v sm = (op,sn)` >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_bytestring >> simp[is_bytestring_type_def]) >>
  `~is_word_type (BaseT (StringT cap))` by simp[is_word_type_def] >>
  `ptr_val_ok cx (expr_type e) (StringV str) v G1 tn1 s` by metis_tac[] >>
  drule_all hash_string_operand >> strip_tac >>
  `!z. v = Var z ==> not_fresh_at sm z` by metis_tac[compile_lower_value_var] >>
  `expr_val_at cenv cx (expr_type e) sa sm mid (StringV str) v s` by
    (`expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e es sa sm s0 mid
       (StringV str) v s` by metis_tac[] >>
     qpat_assum `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e es sa sm s0 mid _ _ s`
       (mp_tac o cj 4 o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
     qpat_assum `post_value_type cenv e = expr_type e` mp_tac >>
     qpat_assum `expr_type e = _` mp_tac >>
     qpat_assum `v = Var p` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (qpat_assum `lower_value _ _ _ _ sa = _`
      (mp_tac o MATCH_MP (cj 2 compile_expr_grows)) >> simp[]) >>
  gvs[ptr_covers_def, eval_operand_def] >>
  `b < dimword (:256)` by decide_tac >>
  `w2n (n2w b:bytes32) = b` by simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  fs[] >>
  Q.SUBGOAL_THEN
    `(LENGTH str = 0 \/
     (?aid a k. FLOOKUP s.vs_allocas aid = SOME (a,k) /\
       aid < sm.cs_next_id /\ a <= b+32 /\ b+32+LENGTH str <= a+k) \/
     (?name a k. local_region cenv mid.scopes s name a k /\
       a <= b+32 /\ b+32+LENGTH str <= a+k))` assume_tac >-
    (drule_at (Pos hd) hash_string_input_window >> simp[] >>
     disch_then (qspecl_then [`n2w b`, `sm`] mp_tac) >> simp[eval_operand_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[ADD_ASSOC,ADD_COMM]) >>
  qabbrev_tac `bs = MAP (n2w o ORD) str : word8 list` >>
  `LENGTH bs = LENGTH str /\
   mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
   mem_word_at b s.vs_memory = n2w (LENGTH bs)` by
    simp[Abbr `bs`, LENGTH_MAP] >>
  `builtin_result cx mid.accounts (BaseT (BytesT (Fixed 32))) Sha256
     [expr_type e] [StringV str] =
     INL (BytesV (word_to_bytes (SHA_256_bytes bs) T))` by
    simp[Abbr `bs`, exprSimWordArgsTheory.builtin_result_def,
      vyperContextTheory.evaluate_builtin_def] >>
  `value_has_type (BaseTV (StringT cap)) (StringV str)` by
    simp[vyperTypingTheory.value_has_type_def] >>
  qpat_assum `LENGTH bs = LENGTH str`
    (fn len => RULE_ASSUM_TAC (REWRITE_RULE [GSYM len])) >>
  suspend "string_memory"
QED

Resume sha_vv_sim_full[dynamic]:
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
  Cases_on `compile_sha256_bytes v sm` >> gvs[as_stack_val_def] >>
  rename1 `compile_sha256_bytes v sm = (op,sn)` >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_bytestring >> simp[is_bytestring_type_def]) >>
  `~is_word_type (BaseT (BytesT (Dynamic cap)))` by simp[is_word_type_def] >>
  `ptr_val_ok cx (expr_type e) (BytesV bs) v G1 tn1 s` by metis_tac[] >>
  drule_all hash_dynamic_bytes_operand >> strip_tac >>
  `!z. v = Var z ==> not_fresh_at sm z` by metis_tac[compile_lower_value_var] >>
  `expr_val_at cenv cx (expr_type e) sa sm mid (BytesV bs) v s` by
    (`expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e es sa sm s0 mid
       (BytesV bs) v s` by metis_tac[] >>
     qpat_assum `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e es sa sm s0 mid _ _ s`
       (mp_tac o cj 4 o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
     qpat_assum `post_value_type cenv e = expr_type e` mp_tac >>
     qpat_assum `expr_type e = _` mp_tac >>
     qpat_assum `v = Var p` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (qpat_assum `lower_value _ _ _ _ sa = _`
      (mp_tac o MATCH_MP (cj 2 compile_expr_grows)) >> simp[]) >>
  gvs[ptr_covers_def, eval_operand_def] >>
  `b < dimword (:256)` by decide_tac >>
  `w2n (n2w b:bytes32) = b` by simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  fs[] >>
  Q.SUBGOAL_THEN
    `(LENGTH bs = 0 \/
     (?aid a k. FLOOKUP s.vs_allocas aid = SOME (a,k) /\
       aid < sm.cs_next_id /\ a <= b+32 /\ b+32+LENGTH bs <= a+k) \/
     (?name a k. local_region cenv mid.scopes s name a k /\
       a <= b+32 /\ b+32+LENGTH bs <= a+k))` assume_tac >-
    (drule_at (Pos hd) hash_dynamic_bytes_input_window >> simp[] >>
     disch_then (qspecl_then [`n2w b`, `sm`] mp_tac) >> simp[eval_operand_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[ADD_ASSOC,ADD_COMM]) >>
  `builtin_result cx mid.accounts (BaseT (BytesT (Fixed 32))) Sha256
     [expr_type e] [BytesV bs] =
     INL (BytesV (word_to_bytes (SHA_256_bytes bs) T))` by
    simp[exprSimWordArgsTheory.builtin_result_def,
      vyperContextTheory.evaluate_builtin_def] >>
  `value_has_type (BaseTV (BytesT (Dynamic cap))) (BytesV bs)` by
    simp[vyperTypingTheory.value_has_type_def] >>
  suspend "dynamic_memory"
QED

Resume sha_vv_sim_full[string_memory]:
  sha_memory_prepare_tac >>
  Cases_on `?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success`
  >- suspend "string_memory_success" >>
  suspend "string_memory_abort"
QED

Resume sha_vv_sim_full[dynamic_memory]:
  sha_memory_prepare_tac >>
  Cases_on `?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success`
  >- suspend "dynamic_memory_success" >>
  suspend "dynamic_memory_abort"
QED

Resume sha_vv_sim_full[string_memory_abort]:
  sha_memory_abort_origin_tac >>
  sha_memory_abort_post_tac
QED

Resume sha_vv_sim_full[dynamic_memory_abort]:
  sha_memory_abort_origin_tac >>
  sha_memory_abort_post_tac
QED

Resume sha_vv_sim_full[string_memory_success]:
  sha_memory_success_endpoint_tac >>
  sha_memory_success_frame_tac >>
  sha_memory_success_post_tac
QED

Resume sha_vv_sim_full[dynamic_memory_success]:
  sha_memory_success_endpoint_tac >>
  sha_memory_success_frame_tac >>
  sha_memory_success_post_tac
QED

Resume sha_vv_sim_full[fixed_success]:
  pop_assum strip_assume_tac >>
  `ghost_inv_at (DF (storage_trace_horizon mid.storage_trace)) lo d cenv cx mid G1 tn1 s` by
    metis_tac[] >>
  drule_all sha_fixed_success_frame_at >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `builtin_result cx mid.accounts (BaseT (BytesT (Fixed 32))) Sha256
    [expr_type e] [BytesV bs] =
    INL (BytesV (word_to_bytes (SHA_256_bytes bs) T))` by
    simp[exprSimWordArgsTheory.builtin_result_def,
      vyperContextTheory.evaluate_builtin_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    inst_seq_ptr (DF H) lo ctx func PG G1 tn1 (emitted_insts sm sn) s Gf tf /\
    ghost_inv_at (DF H) lo d cenv cx (mid with outcomes := SOME rest) Gf tf t` by
    (gen_tac >> disch_tac >>
     `expr_post H ctx func cenv cx e es sa sm s0 mid (BytesV bs) v s /\
      ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 s` by metis_tac[] >>
     `stmt_state_rel H ctx func cenv cx mid s` by
       metis_tac[exprSimWordArgsTheory.expr_post_state] >>
     mp_tac (Q.INST [`D` |-> `DF H`, `H` |-> `H`, `lo` |-> `lo`,
       `ctx` |-> `ctx`, `fn` |-> `func`, `PG` |-> `PG`,
       `G` |-> `G1`, `tn` |-> `tn1`, `s` |-> `s`, `bb` |-> `bb`,
       `value` |-> `v`, `m` |-> `LENGTH (bs:word8 list)`,
       `sa` |-> `sm`, `op` |-> `op`, `sb` |-> `sn`, `d` |-> `d`,
       `cenv` |-> `cenv`, `cx` |-> `cx`, `es` |-> `mid`,
       `bs` |-> `bs`, `outcome` |-> `outcome`, `rest` |-> `rest`]
       (Q.INST [`v` |-> `w`] (SPEC_ALL sha_fixed_success_frame_at))) >>
     (impl_tac >- simp[]) >>
     disch_then (qx_choosel_then [`u`, `G2`, `tn2`] strip_assume_tac) >>
     `u = t` by
       (qpat_assum `run_inst_seq (emitted_insts sm sn) s = OK u` mp_tac >>
        qpat_assum `run_inst_seq (emitted_insts sm sn) s = OK t`
          (fn th => once_rewrite_tac[th]) >> simp[]) >>
     qpat_x_assum `u = t` SUBST_ALL_TAC >>
     `G2 = Gf /\ tn2 = tf` by
       (qpat_assum `inst_seq_ptr (DF H) lo ctx func PG G1 tn1 _ s G2 tn2` mp_tac >>
        qpat_assum `inst_seq_ptr (DF (storage_trace_horizon mid.storage_trace))
          lo ctx func PG G1 tn1 _ s Gf tf` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[inst_seq_ptr_ghost_unique]) >>
     gvs[bytes_ghost_cursor]) >>
  `alloca_inv s` by fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sn)` by
    (qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) _`
      mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> simp[EVERY_CONJ]) >>
  `alloca_history func
    (t with vs_inst_idx := s.vs_inst_idx+LENGTH (emitted_insts sm sn))` by
    (irule alloca_history_run_inst_seq >> goal_assum (drule_at Any) >> simp[] >>
     gvs[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `run_inst_seq (emitted_insts sm sn) s = OK t` mp_tac >>
     qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) _`
       mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     irule (SRULE [] (Q.ISPEC `\s:venom_state. s.vs_current_bb` run_inst_seq_preserves_field)) >>
     goal_assum (drule_at Any) >> rpt strip_tac >>
     fs[EVERY_MEM] >> metis_tac[step_preserves_control_flow, step_inst_non_invoke]) >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    metis_tac[sha256_run_inst_seq_alloca_next_mono] >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by decide_tac >>
  `LENGTH sn.cs_current_insts = s.vs_inst_idx+LENGTH (emitted_insts sm sn)` by
    (qpat_assum `sn.cs_current_insts = sm.cs_current_insts ++ _`
      (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `wb_frame cenv es mid sa s0 s` by
    metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf` by
    (`stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0` by
       (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
         (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
     drule_all hash_ghost_kept_wb_trans >> simp[]) >>
  `(mid with outcomes := SOME rest) with gas_obs := [] = mid with outcomes := SOME rest` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `gas_explicit [F] s.vs_gas_readings = []` by
    ACCEPT_TAC (REWRITE_RULE [EVAL ``REPLICATE 1 F``]
      (Q.SPECL [`1`, `s.vs_gas_readings`] gasSummaryTheory.gas_explicit_replicate_false)) >>
  `!tail. ignore_bind (precompile_call_success Sha256)
    (return (Value (BytesV (word_to_bytes (SHA_256_bytes bs) T))))
    (mid with gas_obs := tail) =
    (INL (Value (BytesV (word_to_bytes (SHA_256_bytes bs) T))),
      (mid with outcomes := SOME rest) with gas_obs := tail)` by
    (qpat_assum `expr_type e = _` (fn te =>
       qpat_assum `builtin_result _ _ _ Sha256 [expr_type e] _ = _` (fn br =>
         drule_all hash_sha256_source_success >> simp[te, REWRITE_RULE [te] br]))) >>
  irule gas_outcome_full_intro >>
  qexistsl_tac [`Gf`, `mid with outcomes := SOME rest`, `[F]`,
    `OK (t with vs_inst_idx := s.vs_inst_idx+LENGTH (emitted_insts sm sn))`,
    `INL (Value (BytesV (word_to_bytes (SHA_256_bytes bs) T)))`, `tf`] >>
  qpat_assum `expr_type e = _` (fn te =>
    qpat_assum `builtin_result _ _ _ Sha256 [expr_type e] _ = _`
      (fn br => simp[REWRITE_RULE [te] br])) >>
  gen_tac >> disch_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by fs[] >>
  `expr_post H ctx func cenv cx e es sa sm s0 mid (BytesV bs) v s /\
   ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 s` by metis_tac[] >>
  `inst_seq_ptr (DF H) lo ctx func PG G1 tn1 (emitted_insts sm sn) s Gf tf /\
   ghost_inv_at (DF H) lo d cenv cx (mid with outcomes := SOME rest) Gf tf t` by
    metis_tac[] >>
  conj_tac
  >- (qpat_assum `MAP (\i. (func.fn_name,i.inst_id) IN gas_explicit_sites ctx shadow_ctx) _ = [F]`
        (fn th => once_rewrite_tac[GSYM th]) >>
      qpat_assum `s.vs_inst_idx = LENGTH sm.cs_current_insts`
        (fn th => once_rewrite_tac[GSYM th]) >>
      irule run_inst_seq_gas_origin_ptr_path >> simp[] >>
      qpat_assum `s.vs_inst_idx = LENGTH sm.cs_current_insts` (fn idx =>
        qpat_assum `isPREFIX (emitted_insts sm sn) (DROP s.vs_inst_idx bb.bb_instructions)`
          (ACCEPT_TAC o REWRITE_RULE [idx]))) >>
  simp[] >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `vv_post H ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])
    es sa sn s0 (mid with outcomes := SOME rest)
    (Value (BytesV (word_to_bytes (SHA_256_bytes bs) T)))
    (StackValue (BaseT (BytesT (Fixed 32))) op) t` by
    (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
      (mp_then Any mp_tac sha256_fixed_post_run) >> simp[] >> strip_tac >> gvs[]) >>
  simp[vyperASTTheory.expr_type_def, exprSimMemDefsTheory.vv_store_bound_stack_word,
    compileEnvTheory.is_word_type_def, bodyPtrDefsTheory.ptr_vv_ok_def,
    bodyPtrDefsTheory.ptr_val_ok_def, contextTheory.vv_location_def,
    loweringPostsTheory.post_value_type_def, exprSimVVFrameTheory.vv_post_inst_idx,
    bytes_ghost_cursor, vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  qpat_assum `s.vs_inst_idx = LENGTH sm.cs_current_insts` (fn idx =>
    qpat_assum `alloca_history func
      (t with vs_inst_idx := s.vs_inst_idx+LENGTH (emitted_insts sm sn))`
      (ACCEPT_TAC o REWRITE_RULE [idx]))
QED

Finalise sha_vv_sim_full
