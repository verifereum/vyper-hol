(* Owned immediate-read external-call operands, on one joint witness. *)
Theory bodyFullExtCallRequestSnapshotFull
Ancestors
  bodyFullExtCallRequestSnapshotFullWord
  bodyFullExtCallRequestSnapshotFullLocated
  gasOutcomeFullCompose gasOutcomeFull gasExemptCert
  vyperStorageTrace vyperStorageFootprint stmtSimProps
  exprSimDefs exprLowering

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
  strip_tac >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (cv,sm)` >>
  Cases_on `is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) cv))`
  >- (`!vv sm. compile_expr cenv (expr_type e) e sa = (vv,sm) ==>
        is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv))` by
        (rpt strip_tac >> gvs[]) >>
      drule_all extcall_request_snapshot_word_owned_full >>
      disch_then (qspec_then `PG` ACCEPT_TAC)) >>
  `!vv sm. compile_expr cenv (expr_type e) e sa = (vv,sm) ==>
    ~is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv))` by
    (rpt strip_tac >> gvs[]) >>
  drule_all extcall_request_snapshot_located_owned_full >>
  disch_then (qspec_then `PG` ACCEPT_TAC)
QED
