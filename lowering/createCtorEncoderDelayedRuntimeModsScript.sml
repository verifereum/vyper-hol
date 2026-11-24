(* A delayed non-memory saved aggregate is copied from its runtime-code
   source; the linked encoder consumes the ordinary saved-unwrap post. *)
Theory createCtorEncoderDelayedRuntimeMods
Ancestors
  bodyFullExtCallDirectUnwrap bodyFullExtCallDirectSaved
  createCtorUnwrapRuntimeCodeArrivalMods createCtorEncoderFoldMods
  createExprSizeExitDefsMods

Theorem ctor_encoder_delayed_runtime_mods:
  ty = lowered_value_type ce e /\
  ~ce.ce_is_ctor /\
  saved = LocatedValue ty p /\ p.ptr_location = LocCode /\
  ~is_word_type ty /\ ty = expr_type e /\
  compile_expr ce (expr_type e) e si = (saved,sm) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (~is_word_type ty ==> ~is_word_type (expr_type e)) /\
  sm.cs_next_var <= su.cs_next_var /\ sm.cs_next_id <= su.cs_next_id /\
  local_ptrs_reserved ce si /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  unwrap_value ce saved su = (src,sb) /\
  fn_has_code su sb fn /\ fn_inst_ids_distinct fn /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  evaluate_type (get_tenv cx) ty = SOME rt /\
  type_memory_bytes ce ty = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ value_has_type rt v /\
  storage_trace_domain cx st0 ee.storage_trace /\
  read_result cx raw ee = (INL v,ee) /\
  vv_holds ce cx ty raw saved ee t /\
  ptr_vv_ok cx ty raw saved ee G tn t /\
  vv_store_bound cx ty ty ee raw saved t /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx fn ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    vv_storage_live H cx saved ee t /\
    ghost_inv_at (DF H) lo d ce cx ee G tn t) /\
  vv_at ce cx ty si ss ee raw saved t /\
  (!x. vv_operand saved = Var x ==> not_fresh_at su x) /\
  alloca_history fn t /\ ~t.vs_halted /\ t.vs_current_bb = su.cs_current_bb /\
  t.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?z G' tn'.
    pure_frame ce fn ee su t z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,G',tn') /\
      stmt_state_rel H ctx fn ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee G' tn' z) /\
    expr_val_rel cx ty v src z /\ ptr_val_ok cx ty v src G' tn' z /\
    expr_store_bound cx ty v src z /\
    (~is_word_type ty ==> ptr_buf_ok ce e src G' z) /\
    (~is_word_type ty ==> !w. eval_operand src z = SOME w ==>
       type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    alloca_history fn z /\ t.vs_alloca_next <= z.vs_alloca_next /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at su x ==>
       lookup_var x z = lookup_var x t /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame ce ee ee su t z /\ ghost_kept_at lo ce ee su G tn t G' tn' /\
    (!x. src = Var x ==> not_fresh_at sb x) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,G',tn')) /\
    (~is_word_type ty ==>
      ((src = vv_operand saved /\ sb = su /\ expr_val_at ce cx ty si ss ee v src z) \/
       expr_val_at ce cx ty su sb ee v src z))
Proof
  strip_tac >>
  mp_tac extcall_direct_saved_unwrap_pure >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY (simp[]) >>
     TRY (disj2_tac >> disj2_tac >> qexists_tac `p` >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])) >>
  disch_then ACCEPT_TAC
QED
