(* Dynamic RawLog continuation, anchored at the successful topic midpoint. *)
Theory bodyFullRawLogDynamic
Ancestors
  bodyFullRawLogDynamicTail bodySimFull gasOutcomeFullCompose gasOutcomeFull
  gasShadowState gasShadow bodyFullShared exprLoweringProps exprOperandVar
  exprSimMemDefs exprSimDefs gasExemptCert vyperStorageTrace vyperStorageFootprint
  loweringPosts bodyPtrDefs loweringShapeDefs
  vyperInterpreter vyperState vyperValue vyperEvent venomState
  words list rich_list arithmetic

Theorem raw_log_dynamic_data_full:
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type data) data es /\
  lower_value compile_expr cenv (expr_type data) data sa = (data_op,sm) /\
  lower_value compile_expr cenv (expr_type data) (gas_shadow_expr data)
    shadow_sa = (data_op,shadow_sm) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx data) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible
    (bind (bind (eval_expr cx data) (read_result cx))
      (\v. do bs <- lift_option_type (dest_BytesV v) "raw_log data";
              type_check (LENGTH vals <= 4) "raw_log too many topics";
              push_log (encode_raw_event_values cx.txn.target vals bs);
              return NoneV od)) expr_res_ok es /\
  LENGTH vals <= 4 /\ LENGTH ops = LENGTH vals /\
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
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (bind (bind (eval_expr cx data) (read_result cx))
      (\v. do bs <- lift_option_type (dest_BytesV v) "raw_log data";
              type_check (LENGTH vals <= 4) "raw_log too many topics";
              push_log (encode_raw_event_values cx.txn.target vals bs);
              return NoneV od)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      expr_post H ctx func cenv cx (Call ann RawLog es_call dflt)
        es sa sb s0 ee v (Lit 0w) t /\
      expr_store_bound cx (expr_type (Call ann RawLog es_call dflt)) v (Lit 0w) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_val_ok cx (post_value_type cenv (Call ann RawLog es_call dflt)) v (Lit 0w) G tn t /\
      (~is_word_type (post_value_type cenv (Call ann RawLog es_call dflt)) ==>
        ptr_buf_ok cenv (Call ann RawLog es_call dflt) (Lit 0w) G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`,
    `data_op`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ dataQ dataR` >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`, `t`, `v`] >>
      qpat_x_assum `gas_exempt_cert _ _ _ _ _ _ _ _` mp_tac >>
      qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      rpt (pop_assum kall_tac) >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- suspend "suffix_frame" >>
  qexists_tac `\H res ee G tn t. dataQ H res ee G tn t /\ ~t.vs_halted` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "selected" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `dataR`] >> rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def]
QED

Resume raw_log_dynamic_data_full[suffix_frame]:
  gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
  reverse conj_tac >- simp[storage_trace_frame_lifts] >>
  gen_tac >> BETA_TAC >> irule storage_trace_frame_ignore_bind >>
  conj_tac >- simp[storage_trace_frame_checks] >>
  irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_state_updates, storage_trace_frame_return]
QED
Resume raw_log_dynamic_data_full[selected]:
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
    expr_post H ctx func cenv cx data es sa sm s0 mid (BytesV bs) data_op t /\
    expr_store_bound cx (expr_type data) (BytesV bs) data_op t /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
    ptr_val_ok cx (post_value_type cenv data) (BytesV bs) data_op G1 tn1 t /\
    ptr_buf_ok cenv data data_op G1 t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    eval_operands ops t = SOME (MAP event_value_to_word vals) /\
    EVERY (\op. op_taint tn1 op = {}) ops /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> eval_operands _ _ = _ /\ _`
       (qspec_then `H` mp_tac) >> simp[compileEnvTheory.is_word_type_def]) >>
  `?u G2 tn2. !H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK u,G2,tn2) /\
    expr_post H ctx func cenv cx (Call ann RawLog es_call dflt) es sa sb s0
      (mid with logs := mid.logs ++ [encode_raw_event_values cx.txn.target vals bs])
      NoneV (Lit 0w) u /\
    expr_store_bound cx (expr_type (Call ann RawLog es_call dflt)) NoneV (Lit 0w) u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx
      (mid with logs := mid.logs ++ [encode_raw_event_values cx.txn.target vals bs]) G2 tn2 u /\
    ptr_val_ok cx (post_value_type cenv (Call ann RawLog es_call dflt)) NoneV (Lit 0w) G2 tn2 u /\
    (~is_word_type (post_value_type cenv (Call ann RawLog es_call dflt)) ==>
      ptr_buf_ok cenv (Call ann RawLog es_call dflt) (Lit 0w) G2 u) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (irule raw_log_dynamic_tail_full >> simp[] >>
     qexistsl [`cap`, `data`, `data_op`, `len_op`, `ops`, `ptr_op`, `s1`, `s2`, `sm`] >>
     fs[EVERY_DEF, compileEnvTheory.is_word_type_def] >>
     rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  irule gas_outcome_full_intro >>
  qexistsl [`G2`,
    `mid with logs := mid.logs ++ [encode_raw_event_values cx.txn.target vals bs]`,
    `[]`, `OK u`, `INL NoneV`, `tn2`] >>
  simp[lift_option_type_def, lift_option_def, dest_BytesV_def,
       bind_def, ignore_bind_def, type_check_def, push_log_def, return_def] >>
  conj_tac >- simp[assert_def, return_def] >>
  gen_tac >> strip_tac >> disj1_tac >>
  qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `expr_post H _ _ _ _ (Call _ RawLog _ _) _ _ _ _ _ _ _ _` mp_tac >>
      qpat_x_assum `expr_type (Call _ RawLog _ _) = NoneT` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[expr_post_def, expr_val_at_def, locals_kept_def, popped_kept_def,
           storage_well_formed_on_def, evaluation_state_fupdcanon,
           stmt_state_rel_start_gas_obs] >>
      once_rewrite_tac [GSYM evaluation_state_fupdcanon] >>
      simp[stmt_state_rel_start_gas_obs] >>
      simp[oneline vyperStorageBackendTheory.get_storage_def] >>
      rpt strip_tac >> metis_tac[]) >>
  fs[] >>
  qpat_assum `expr_type (Call _ RawLog _ _) = NoneT` SUBST_ALL_TAC >>
  simp[] >>
  qpat_x_assum `ghost_inv_at (DF H) _ _ _ _ _ G2 tn2 u` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[ghost_inv_at_def] >>
  strip_tac >> first_assum ACCEPT_TAC
QED
Resume raw_log_dynamic_data_full[topics_kept]:
  gen_tac >> strip_tac >>
  `storage_trace_frame (bind (eval_expr cx data) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  qpat_assum `!tail. bind (eval_expr _ _) _ _ = _`
    (qspec_then `[]` assume_tac) >>
  drule_all storage_trace_frame_prefix >> simp[] >> strip_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    metis_tac[valid_horizon_append] >>
  qpat_assum `!H. valid_horizon _ _ _ es.storage_trace ==> eval_operands _ _ = _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
     lookup_var x t = SOME w` by fs[expr_post_def] >>
  `!x. not_fresh_at sa x ==> op_taint tn1 (Var x) = op_taint tn0 (Var x)` by
    fs[ghost_kept_at_def] >>
  conj_tac
  >- (`!xs ws. EVERY (\op. (!x. op = Var x ==> not_fresh_at sa x) /\
                     (!l. op <> Label l)) xs /\ eval_operands xs s0 = SOME ws ==>
             eval_operands xs t = SOME ws` suffices_by metis_tac[] >>
      Induct_on `xs` >> simp[eval_operands_def] >>
      rpt gen_tac >> Cases_on `h` >>
      simp[eval_operands_def, eval_operand_def, AllCaseEqs()] >>
      metis_tac[]) >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  Cases_on `op` >> gvs[ptrDisciplineTheory.op_taint_def] >> metis_tac[]
QED
Finalise raw_log_dynamic_data_full
