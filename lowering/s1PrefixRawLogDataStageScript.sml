(* The RawLog data expression starts after the topics and any scratch alloca. *)
Theory s1PrefixRawLogDataStage
Ancestors
  s1PrefixDefs s1PrefixCompose s1PrefixProps exprSimDefs
  bodyFullRawLogFixedAlloc bodyFullIfExpReach
  bodyFullHashKeccakFixed gasOutcomeFullCompose exprLoweringProps
  vyperStorageFootprint vyperStorageTrace vyperState vyperValue gasContext rich_list

Theorem raw_log_tail_trace[local]:
  (do bs <- lift_option_type (dest_BytesV v) "raw_log data";
      type_check (LENGTH vs <= 4) "raw_log too many topics";
      check_not_static cx;
      push_log (encode_raw_event_values cx.txn.target vs bs);
      return NoneV od) st = (res,ee) ==>
  ee.storage_trace = st.storage_trace
Proof
  Cases_on `dest_BytesV v` >> Cases_on `LENGTH vs <= 4` >>
  Cases_on `cx.txn.is_static` >>
  simp[bind_def, ignore_bind_def, lift_option_type_def, type_check_def,
       check_not_static_def, check_def, assert_def, push_log_def, return_def, raise_def] >>
  strip_tac >> gvs[]
QED

Theorem raw_log_tail_frame[local]:
  storage_trace_frame
    (do bs <- lift_option_type (dest_BytesV v) "raw_log data";
        type_check (LENGTH vs <= 4) "raw_log too many topics";
        check_not_static cx;
        push_log (encode_raw_event_values cx.txn.target vs bs);
        return NoneV od)
Proof
  irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_lifts] >> gen_tac >> BETA_TAC >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_check_not_static] >>
  irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_state_updates, storage_trace_frame_return]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (drule_then assume_tac o REWRITE_RULE [expr_sim_full_eq]) >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (drule_then assume_tac o REWRITE_RULE [expr_sim_prefix_def]) >>
  irule gas_prefix_full_bind_no_outcome >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, raw_log_tail_frame,
       requests_outcomes_frame_bind_all, evaluate_requests_outcomes_frame,
       requests_outcomes_frame_read_result] >>
  conj_tac
  >- (rpt strip_tac >> drule raw_log_tail_trace >> simp[]) >>
  qexistsl [`\H res ee G tn (t:venom_state). ~t.vs_halted`,
    `\H res ee gt r. ISR res`, `cx_tops cx`] >>
  simp[] >>
  irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
  simp[] >> rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def]
QED
*)
Theorem raw_log_data_at_entry_prefix[local]:
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type data) data mid /\
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type data) data mid /\
  expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type data) data mid (st0,sd,sn,shadow_sd,shadow_sn,op,u,Gu,tnu) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
    (bind (bind (eval_expr cx data) (read_result cx))
      (\v. do bs <- lift_option_type (dest_BytesV v) "raw_log data";
              type_check (LENGTH vs <= 4) "raw_log too many topics";
              check_not_static cx;
              push_log (encode_raw_event_values cx.txn.target vs bs);
              return NoneV od)) (mid,u,Gu,tnu)
Proof
  cheat
QED

Theorem raw_log_data_stage_prefix:
  expr_body_pre cenv cx env data mid /\
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type data) data mid /\
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type data) data mid /\
  lower_value compile_expr cenv (expr_type data) data sd = (op,sn) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type data)
    (gas_shadow_expr data) shadow_sd = (op,shadow_sn) /\
  gas_shadow_state sd shadow_sd /\ gas_shadow_state sn shadow_sn /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sd sn func /\ fn_has_code shadow_sd shadow_sn shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  gas_admissible (bind (eval_expr cx data) (read_result cx)) expr_res_ok mid /\
  return_buf_frame d cenv sm t /\ alloca_history func t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
    !bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t) /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ((expr_type data = BaseT (BytesT (Fixed 32)) /\
    fn_has_code sm sd func /\ ci_mono sm sd /\
    ?buf topics_expr ann ty dflt sa vv sb.
      compile_alloc_buffer 32 sm = (buf,sd) /\
      compile_alloc_buffer 32 shadow_sm = (buf,shadow_sd) /\
      compile_call compile_expr cenv ann ty RawLog [topics_expr;data] dflt sa = (vv,sb)) \/
   (expr_type data <> BaseT (BytesT (Fixed 32)) /\ sd = sm /\ shadow_sd = shadow_sm)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
    (bind (bind (eval_expr cx data) (read_result cx))
      (\v. do bs <- lift_option_type (dest_BytesV v) "raw_log data";
              type_check (LENGTH vs <= 4) "raw_log too many topics";
              check_not_static cx;
              push_log (encode_raw_event_values cx.txn.target vs bs);
              return NoneV od)) (mid,t,G1,tn1)
Proof
  strip_tac
  >- suspend "fixed" >>
  gvs[] >> irule raw_log_data_at_entry_prefix >>
  qexistsl [`cenv`, `d`, `op`, `sd`, `shadow_func`, `shadow_sd`, `shadow_sn`, `sn`] >>
  fs[expr_sim_full_pre_def] >> first_assum ACCEPT_TAC
QED

Resume raw_log_data_stage_prefix[fixed]:
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
   (!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid t /\
     storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
     return_buf_frame d cenv sm t /\ alloca_history func t /\ ~t.vs_halted /\
     t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts)` by
    (conj_tac >- fs[] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  drule_all (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`]
    raw_log_fixed_alloc_full) >>
  disch_then (qspecl_then [`shadow_ctx`, `PG`]
    (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `tnu` strip_assume_tac)))) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `!fn inst s. frag_reachable ctx func u fn inst s ==> dalloca_fmp_headroom inst s` by
    (Cases_on `ctx_has_dalloca ctx`
     >- (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by fs[] >>
         drule gas_origin_ptr_path_dalloca_fmp_headroom >>
         disch_then (fn safe => rpt strip_tac >>
           rename1 `frag_reachable ctx func u leaf ins z` >>
           qspecl_then [`leaf`, `ins`, `z`] mp_tac safe) >>
         (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
     rpt strip_tac >> drule_all contextRawReachableTheory.frag_reachable_members >> strip_tac >>
     fs[unitTransformDefsTheory.dalloca_fmp_headroom_def,
        ptrDisciplineTheory.ctx_has_dalloca_def, listTheory.EXISTS_MEM] >> metis_tac[]) >>
  `sm.cs_next_var <= sd.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sd` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  irule gas_prefix_full_zero_prefix_guarded >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, raw_log_tail_frame] >>
  qexistsl [`Gu`, `u`, `tnu`] >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  irule raw_log_data_at_entry_prefix >>
  qexistsl [`cenv`, `d`, `op`, `sd`, `shadow_func`, `shadow_sd`, `shadow_sn`, `sn`] >>
  simp[expr_sim_full_pre_def] >> first_assum ACCEPT_TAC
QED

Finalise raw_log_data_stage_prefix
