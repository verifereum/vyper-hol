(* Linked dynamic RawLog continuation from a reached data buffer. *)
Theory bodyRawLogDynamicDataMods
Ancestors
  bodyFullRawLogDynamic bodyFullRawLogDynamicTail bodyFullRawLogDynamicTailPath
  bodyFullPredsMods bodyFullPostsMods gasOutcomeFullMods gasOutcomeFullBindMods
  gasExemptCertMods bodyForcedStorageFrameMods
  gasOutcomeFullPostMods bodyFullShadowBodyInv bodySimFull exprSimHypsDefs
  exprLoweringProps exprOperandVar exprSimMemDefs exprSimDefs bodyPtrDefs loweringPosts
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  vyperValue vyperAST venomState compileEnv ptrDiscipline unitMemInv
  words list rich_list arithmetic

Theorem raw_log_dynamic_data_run_mods:
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type data) data es /\
  lower_value compile_expr cenv (expr_type data) data sa = (data_op,sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type data)
    (gas_shadow_expr data) shadow_sa = (data_op,shadow_sm) /\
  gas_shadow_state sa shadow_sa /\
  gas_shadow_state sm shadow_sm /\
  gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sm func /\
  fn_has_code shadow_sa shadow_sm shadow_func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx data) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\
  alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible
    (bind (bind (eval_expr cx data) (read_result cx))
      (\v. do bs <- lift_option_type (dest_BytesV v) "raw_log data";
              type_check (LENGTH vals <= 4) "raw_log too many topics";
              check_not_static cx;
              push_log (encode_raw_event_values cx.txn.target vals bs);
              return NoneV od)) expr_res_ok es /\
  LENGTH vals <= 4 /\
  LENGTH ops = LENGTH vals /\
  LENGTH ops < dimword (:256) /\
  EVERY (\op. (!x. op = Var x ==> not_fresh_at sa x) /\
               (!l. op <> Label l)) ops /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    eval_operands ops s0 = SOME (MAP event_value_to_word vals) /\
    EVERY (\op. op_taint tn0 op = {}) ops) /\
  expr_type data = BaseT (BytesT (Dynamic cap)) /\
  post_value_type cenv data = expr_type data /\
  evaluate_type (get_tenv cx) (expr_type data) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  expr_type (Call ann RawLog es_call dflt) = NoneT /\
  post_value_type cenv (Call ann RawLog es_call dflt) = NoneT /\
  expr_has_effect (Call ann RawLog es_call dflt) /\
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op;Lit 32w] s1 = (ptr_op,s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] s2 = ((),sb) /\
  fn_has_code sm sb func ==>
  gas_outcome_full_mods
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0
    (bind (bind (eval_expr cx data) (read_result cx))
      (\v. do bs <- lift_option_type (dest_BytesV v) "raw_log data";
              type_check (LENGTH vals <= 4) "raw_log too many topics";
              check_not_static cx;
              push_log (encode_raw_event_values cx.txn.target vals bs);
              return NoneV od)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      expr_post_mods H ctx func cenv cx (Call ann RawLog es_call dflt)
        es sa sb s0 ee v (Lit 0w) t /\
      expr_store_bound cx (expr_type (Call ann RawLog es_call dflt)) v (Lit 0w) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ptr_val_ok cx (post_value_type cenv (Call ann RawLog es_call dflt)) v (Lit 0w) G tn t /\
      (~is_word_type (post_value_type cenv (Call ann RawLog es_call dflt)) ==>
        ptr_buf_ok cenv (Call ann RawLog es_call dflt) (Lit 0w) G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  (* force 1 *)
  strip_tac >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`,
    `data_op`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC, simp[]])) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ dataQ dataR` >>
  irule gas_outcome_full_mods_bind_all >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      qexistsl_tac [`mid`, `t`, `v`] >>
      qpat_x_assum `gas_exempt_cert_mods _ _ _ _ _ _ _ _` mp_tac >>
      qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      rpt (pop_assum kall_tac) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- MATCH_ACCEPT_TAC bodyForcedStorageFrameModsTheory.bop_forced_storage_frame
  >~ [`storage_trace_frame _`]
  >- suspend "suffix_frame" >>
  qexists_tac `\H res ee G tn t. dataQ H res ee G tn t /\ ~t.vs_halted` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "selected" >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `dataR`] >> rpt gen_tac >> Cases_on `res` >>
  simp[expr_exit_def, halt_exit_def]
QED

Resume raw_log_dynamic_data_run_mods[suffix_frame]:
  gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
  reverse conj_tac >- simp[storage_trace_frame_lifts] >>
  gen_tac >> BETA_TAC >> irule storage_trace_frame_ignore_bind >>
  conj_tac >- simp[storage_trace_frame_checks] >>
  irule storage_trace_frame_ignore_bind >>
  conj_tac >- simp[storage_trace_frame_check_not_static] >>
  irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_state_updates, storage_trace_frame_return]
QED

Resume raw_log_dynamic_data_run_mods[selected]:
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  fs[Abbr `dataQ`] >>
  qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[] >>
  BETA_TAC >>
  `?bs. v = BytesV bs` by
    (Cases_on `dest_BytesV v`
     >- (qpat_x_assum `gas_admissible (bind (bind _ _) _) _ _`
           (mp_tac o REWRITE_RULE [gasContextTheory.gas_admissible_def]) >>
         disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings ++ []` mp_tac) >>
         qpat_assum `!tail. bind (eval_expr _ _) _ _ = _`
           (qspec_then `[]` assume_tac) >>
         simp[bind_def, lift_option_type_def, lift_option_def, raise_def,
              expr_res_ok_def]) >>
     Cases_on `v` >> gvs[dest_BytesV_def]) >> gvs[] >>
  `ci_mono sa sm` by
    (qspec_then `sa` mp_tac (Q.SPECL [`cenv`, `BaseT (BytesT (Dynamic cap))`, `data`]
      ci_mono_lower_value_compile_expr) >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. data_op = Var x ==> not_fresh_at sm x` by
    (metis_tac[compile_lower_value_var]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
      eval_operands ops t = SOME (MAP event_value_to_word vals) /\
      EVERY (\op. op_taint tn1 op = {}) ops` by
    suspend "topics_kept" >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[] >>
  `EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) (data_op::ops)` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx data es sa sm s0 mid (BytesV bs) data_op t /\
    expr_store_bound cx (expr_type data) (BytesV bs) data_op t /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t /\
    ptr_val_ok cx (post_value_type cenv data) (BytesV bs) data_op G1 tn1 t /\
    ptr_buf_ok cenv data data_op G1 t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    eval_operands ops t = SOME (MAP event_value_to_word vals) /\
    EVERY (\op. op_taint tn1 op = {}) ops /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==>
       expr_post_mods H ctx func cenv cx data es sa sm s0 mid (BytesV bs) data_op t /\ _`
       (qspec_then `H` mp_tac) >>
     qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> eval_operands _ _ = _ /\ _`
       (qspec_then `H` mp_tac) >> simp[compileEnvTheory.is_word_type_def]) >>
  Cases_on `cx.txn.is_static`
  >- suspend "static" >>
  suspend "normal"
QED
