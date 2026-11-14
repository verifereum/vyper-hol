(* Owned immediate-read external-call operands, on one joint witness. *)
Theory bodyFullExtCallRequestSnapshotFull
Ancestors
  bodyFullExtCallRequestSnapshotFullWord
  bodyFullExtCallRequestSnapshotFullLocated
  gasOutcomeFullCompose gasOutcomeFull gasExemptCert
  vyperStorageTrace vyperStorageFootprint stmtSimProps
  exprSimDefs exprLowering compileEnv

Theorem extcall_request_snapshot_classified_full:
  body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  comp_bind (compile_expr cenv (expr_type e) e)
    (\vv. compile_snapshot_vv cenv F
      (ext_call_arg_value (lowered_value_type cenv e) vv)) sa = (sv,sb) /\
  comp_bind (compile_expr cenv (expr_type (gas_shadow_expr e)) (gas_shadow_expr e))
    (\vv. compile_snapshot_vv cenv F
      (ext_call_arg_value (lowered_value_type cenv (gas_shadow_expr e)) vv))
    shadow_sa = (sv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      ((?tag op0. sv = StackValue tag op0) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
         ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
       (?p sm0. sv = LocatedValue (lowered_value_type cenv e) p /\
         ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
         lowered_value_type cenv e = expr_type e /\
         compile_expr cenv (expr_type e) e sa = (sv,sm0) /\
         sm0.cs_next_var <= sb.cs_next_var /\ sm0.cs_next_id <= sb.cs_next_id)) /\
      (?raw. read_result cx raw ee = (INL v,ee) /\
        vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
        vv_at cenv cx (lowered_value_type cenv e) sa sb ee raw sv t /\
        ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
        vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw sv t) /\
      vv_storage_live H cx sv ee t /\
      (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
        ptr_buf_ok cenv e op G t) /\
      (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand G t) /\
      (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
        !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand sv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem)) /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      pure_frame cenv func es sa s0 t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (ee with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) =
      (es with <|gas_obs := []; outcomes := NONE; storage_trace := []|>))
    (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (cv,sm)` >>
  Cases_on `is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) cv))`
  >- (`!vv sm. compile_expr cenv (expr_type e) e sa = (vv,sm) ==>
        is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv))` by
        (rpt strip_tac >> gvs[]) >>
      `?tag op0. sv = StackValue tag op0` by
        (Cases_on `unwrap_value cenv
           (ext_call_arg_value (lowered_value_type cenv e) cv) sm` >>
         qpat_x_assum `comp_bind (compile_expr _ _ e) _ sa = (sv,sb)` mp_tac >>
         simp[comp_bind_def, compile_snapshot_vv_def, comp_return_def] >>
         metis_tac[]) >>
      drule_all extcall_request_snapshot_word_owned_full >>
      disch_then (qspec_then `PG` assume_tac) >>
      irule gas_outcome_full_post_mono >> goal_assum (drule_at Any) >>
      simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `!vv sm. compile_expr cenv (expr_type e) e sa = (vv,sm) ==>
    ~is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv))` by
    (rpt strip_tac >> gvs[]) >>
  drule_all extcall_request_snapshot_located_classified_full >>
  disch_then (qspec_then `PG` mp_tac) >> simp[]
QED

Theorem extcall_request_snapshot_owned_full:
  body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  comp_bind (compile_expr cenv (expr_type e) e)
    (\vv. compile_snapshot_vv cenv F
      (ext_call_arg_value (lowered_value_type cenv e) vv)) sa = (sv,sb) /\
  comp_bind (compile_expr cenv (expr_type (gas_shadow_expr e)) (gas_shadow_expr e))
    (\vv. compile_snapshot_vv cenv F
      (ext_call_arg_value (lowered_value_type cenv (gas_shadow_expr e)) vv))
    shadow_sa = (sv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      (?raw. read_result cx raw ee = (INL v,ee) /\
        vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
        vv_at cenv cx (lowered_value_type cenv e) sa sb ee raw sv t /\
        ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
        vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw sv t) /\
      vv_storage_live H cx sv ee t /\
      (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
        ptr_buf_ok cenv e op G t) /\
      (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand G t) /\
      (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
        !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand sv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem)) /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      pure_frame cenv func es sa s0 t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (ee with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) =
      (es with <|gas_obs := []; outcomes := NONE; storage_trace := []|>))
    (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule_all extcall_request_snapshot_classified_full >>
  disch_then (qspec_then `PG` assume_tac) >>
  irule gas_outcome_full_post_mono >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem extcall_request_snapshot_classified_cps_full:
  body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  comp_bind (compile_expr cenv (expr_type e) e)
    (\vv. compile_snapshot_vv cenv F
      (ext_call_arg_value (lowered_value_type cenv e) vv)) sa = (sv,sb) /\
  comp_bind (compile_expr cenv (expr_type (gas_shadow_expr e)) (gas_shadow_expr e))
    (\vv. compile_snapshot_vv cenv F
      (ext_call_arg_value (lowered_value_type cenv (gas_shadow_expr e)) vv))
    shadow_sa = (sv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v. storage_trace_frame (next v)) /\
  (!marks v mid G tn t.
    (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL v,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      (\H res ee G tn t. ?v. res = INL v /\
      ((?tag op0. sv = StackValue tag op0) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
         ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
       (?p sm0. sv = LocatedValue (lowered_value_type cenv e) p /\
         ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
         lowered_value_type cenv e = expr_type e /\
         compile_expr cenv (expr_type e) e sa = (sv,sm0) /\
         sm0.cs_next_var <= sb.cs_next_var /\ sm0.cs_next_id <= sb.cs_next_id)) /\
      (?raw. read_result cx raw ee = (INL v,ee) /\
        vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
        vv_at cenv cx (lowered_value_type cenv e) sa sb ee raw sv t /\
        ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
        vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw sv t) /\
      vv_storage_live H cx sv ee t /\
      (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
        ptr_buf_ok cenv e op G t) /\
      (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand G t) /\
      (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
        !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand sv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem)) /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      pure_frame cenv func es sa s0 t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (ee with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) =
      (es with <|gas_obs := []; outcomes := NONE; storage_trace := []|>)) H (INL v) mid G tn t) ==>
    gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (next v) (mid,t,G,tn) Q
      (\H res ee gt r. expr_exit res r)) ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (bind (bind (eval_expr cx e) (read_result cx)) next) (es,s0,G0,tn0)
    Q (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  drule_all extcall_request_snapshot_classified_full >>
  disch_then (qspec_then `PG` assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ P _` >>
  irule gas_outcome_full_bind_all >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >>
      first_assum ACCEPT_TAC) >>
  conj_tac
  >- (irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_read_result, evaluate_storage_trace_frame]) >>
  qexists `P` >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `res`
      >- (disj1_tac >> qexists `x` >> simp[] >>
          qpat_x_assum `!marks v mid G tn t. _`
            (qspecl_then [`marks`, `x`, `mid`, `G1`, `tn1`, `t`] irule) >>
          gvs[Abbr `P`] >> metis_tac[]) >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
         mid.storage_trace` by gvs[storage_trace_domain_def] >>
      first_x_assum drule >> simp[Abbr `P`]) >>
  irule gas_outcome_full_post_mono >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> Cases_on `res` >>
  gvs[expr_exit_def] >> metis_tac[expr_exit_INR_type]
QED

Theorem extcall_request_snapshot_full:
  body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  comp_bind (compile_expr cenv (expr_type e) e)
    (\vv. compile_snapshot_vv cenv F
      (ext_call_arg_value (lowered_value_type cenv e) vv)) sa = (sv,sb) /\
  comp_bind (compile_expr cenv (expr_type (gas_shadow_expr e)) (gas_shadow_expr e))
    (\vv. compile_snapshot_vv cenv F
      (ext_call_arg_value (lowered_value_type cenv (gas_shadow_expr e)) vv))
    shadow_sa = (sv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v. storage_trace_frame (next v)) /\
  (!marks v mid G tn t.
    (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL v,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      (\H res ee G tn t. ?v. res = INL v /\
      (?raw. read_result cx raw ee = (INL v,ee) /\
        vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
        vv_at cenv cx (lowered_value_type cenv e) sa sb ee raw sv t /\
        ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
        vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw sv t) /\
      vv_storage_live H cx sv ee t /\
      (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
        ptr_buf_ok cenv e op G t) /\
      (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand G t) /\
      (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
        !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand sv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem)) /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      pure_frame cenv func es sa s0 t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (ee with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) =
      (es with <|gas_obs := []; outcomes := NONE; storage_trace := []|>)) H (INL v) mid G tn t) ==>
    gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (next v) (mid,t,G,tn) Q
      (\H res ee gt r. expr_exit res r)) ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (bind (bind (eval_expr cx e) (read_result cx)) next) (es,s0,G0,tn0)
    Q (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >> irule extcall_request_snapshot_classified_cps_full >>
  simp[] >>
  qexistsl [`cenv`, `d`, `env`, `sa`, `sb`, `shadow_func`,
    `shadow_sa`, `shadow_sb`, `sv`, `tops`] >>
  simp[] >>
  reverse conj_tac >- gvs[] >>
  map_every qx_gen_tac [`marks`, `v`, `mid`, `G1`, `tn1`, `t`] >> strip_tac >>
  qpat_x_assum `!marks v mid G tn t. _`
    (qspecl_then [`marks`, `v`, `mid`, `G1`, `tn1`, `t`] mp_tac) >>
  impl_tac
  >- (simp[] >> qx_gen_tac `H` >> strip_tac >>
      qpat_x_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
        (qspec_then `H` mp_tac) >> simp[]) >>
  simp[]
QED
