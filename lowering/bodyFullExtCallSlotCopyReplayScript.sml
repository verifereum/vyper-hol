(* Delayed preparation of a saved storage/transient aggregate. *)
Theory bodyFullExtCallSlotCopyReplay
Ancestors
  bodyFullUnwrapSlot bodyFullHashKeccakFixed loweringPosts exprSimMemDefs
  fragGasOriginPtrExec fragGasOriginPtrDead context vyperState
  bodyPtrDefs vyperStorageFootprint fragExec
Libs pureFrameLib

Theorem extcall_saved_slot_copy_replay_side:
  unwrap_slot_origin_side_producer ctx fn lo explicit PG Side /\
  lowered_value_type ce e = expr_type e /\
  ~is_word_type (expr_type e) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  compile_expr ce (expr_type e) e si = (LocatedValue (expr_type e) p,sm) /\
  sm.cs_next_var <= su.cs_next_var /\ sm.cs_next_id <= su.cs_next_id /\
  unwrap_value ce (LocatedValue (expr_type e) p) su = (src,sb) /\
  local_ptrs_reserved ce si /\ local_ptrs_reserved ce sm /\
  si.cs_next_var <= sm.cs_next_var /\ si.cs_next_id <= sm.cs_next_id /\
  fn_has_code su sb fn /\ fn_inst_ids_distinct fn /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
  type_memory_bytes ce (expr_type e) = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ value_has_type rt v /\
  storage_trace_domain cx st0 ee.storage_trace /\
  ptr_vv_ok cx (expr_type e) (Value v) (LocatedValue (expr_type e) p) ee G tn t /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx fn ce cx e ee si sm t ee (Value v) (LocatedValue (expr_type e) p) t /\
    ghost_inv_at (DF H) lo d ce cx ee G tn t) /\
  alloca_history fn t /\ ~t.vs_halted /\ t.vs_current_bb = su.cs_current_bb /\
  t.vs_inst_idx = LENGTH su.cs_current_insts /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) ==>
  ?z G' tn'.
    Side su sb t z /\ pure_frame ce fn ee su t z /\
    gas_origin_ptr_path
      (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,
       lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,G',tn') /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,G',tn') /\
      stmt_state_rel H ctx fn ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee G' tn' z) /\
    expr_val_rel cx (expr_type e) v src z /\ ptr_val_ok cx (expr_type e) v src G' tn' z /\
    expr_store_bound cx (expr_type e) v src z /\ ptr_buf_ok ce e src G' z /\
    (!w. eval_operand src z = SOME w ==>
      type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    alloca_history fn z /\ t.vs_alloca_next <= z.vs_alloca_next /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at su x ==>
       lookup_var x z = lookup_var x t /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame ce ee ee su t z /\ ghost_kept_at lo ce ee su G tn t G' tn' /\
    expr_val_at ce cx (expr_type e) su sb ee v src z
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `post_value_type ce e = expr_type e` by metis_tac[post_value_type_lowered] >>
  `vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee
     (Value v) (LocatedValue (expr_type e) p) t` by
    (irule vv_store_bound_nonmem >> fs[]) >>
  `ghost_kept_at lo ce ee si G tn t G tn` by simp[ghost_kept_at_def] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    metis_tac[vv_post_def, stmt_state_rel_allocas_below_fmp] >>
  drule_at_then (Pat `compile_expr`) (drule_at_then (Pat `unwrap_value`)
    (fn th => qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
        vv_post H ctx fn ce cx e ee si sm t ee (Value v) (LocatedValue (expr_type e) p) t /\ _`
      (mp_then (Pat `vv_post`)
        (drule_at_then (Pat `ghost_kept_at`)
          (mp_tac o Q.INST [`rty` |-> `rt`, `explicit` |-> `explicit`, `PG` |-> `PG`] o SPEC_ALL))
        th))) (SIMP_RULE bool_ss []
          (Q.INST [`vv` |-> `LocatedValue t p`] (SPEC_ALL unwrap_slot_copy_origin_ptr_no_dead_side))) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      gvs[contextTheory.vv_operand_def, contextTheory.vv_location_def,
          vyperStateTheory.read_result_def, vyperStateTheory.return_def] >> metis_tac[]) >>
  simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  disch_then (qx_choose_then `z` (qx_choose_then `G'`
    (qx_choose_then `tn'` (REPEAT_TCL CONJUNCTS_THEN assume_tac)))) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) _ _ _ /\
      expr_post H ctx fn ce cx e ee si sb t ee v src z /\
      ghost_inv_at (DF H) lo d ce cx ee G' tn' z`
    (qspec_then `storage_trace_horizon ee.storage_trace` (drule_then strip_assume_tac)) >>
  `expr_val_rel cx (expr_type e) v src z` by
    metis_tac[expr_post_def] >>
  `~z.vs_halted` by
    (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  `expr_val_at ce cx (expr_type e) su sb ee v src z` by
    (fs[vv_own_def, mk_ptr_def, vyperStateTheory.read_result_def, vyperStateTheory.return_def,
        expr_val_at_def] >>
     metis_tac[valueEncodingTypingTheory.value_has_type_val_wf]) >>
  qexistsl [`z`,`G'`,`tn'`] >> simp[] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) _ _ _ /\
      expr_post H ctx fn ce cx e ee si sb t ee v src z /\
      ghost_inv_at (DF H) lo d ce cx ee G' tn' z`
    (qspec_then `H` (drule_then strip_assume_tac)) >> fs[expr_post_def]
QED

Theorem extcall_saved_slot_copy_replay_pure:
  lowered_value_type ce e = expr_type e /\
  ~is_word_type (expr_type e) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  compile_expr ce (expr_type e) e si = (LocatedValue (expr_type e) p,sm) /\
  sm.cs_next_var <= su.cs_next_var /\ sm.cs_next_id <= su.cs_next_id /\
  unwrap_value ce (LocatedValue (expr_type e) p) su = (src,sb) /\
  local_ptrs_reserved ce si /\ local_ptrs_reserved ce sm /\
  si.cs_next_var <= sm.cs_next_var /\ si.cs_next_id <= sm.cs_next_id /\
  fn_has_code su sb fn /\ fn_inst_ids_distinct fn /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
  type_memory_bytes ce (expr_type e) = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ value_has_type rt v /\
  storage_trace_domain cx st0 ee.storage_trace /\
  ptr_vv_ok cx (expr_type e) (Value v) (LocatedValue (expr_type e) p) ee G tn t /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx fn ce cx e ee si sm t ee (Value v) (LocatedValue (expr_type e) p) t /\
    ghost_inv_at (DF H) lo d ce cx ee G tn t) /\
  alloca_history fn t /\ ~t.vs_halted /\ t.vs_current_bb = su.cs_current_bb /\
  t.vs_inst_idx = LENGTH su.cs_current_insts /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) ==>
  ?z G' tn'.
    pure_frame ce fn ee su t z /\
    gas_origin_ptr_path
      (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,
       lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,G',tn') /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,G',tn') /\
      stmt_state_rel H ctx fn ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee G' tn' z) /\
    expr_val_rel cx (expr_type e) v src z /\ ptr_val_ok cx (expr_type e) v src G' tn' z /\
    expr_store_bound cx (expr_type e) v src z /\ ptr_buf_ok ce e src G' z /\
    (!w. eval_operand src z = SOME w ==>
      type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    alloca_history fn z /\ t.vs_alloca_next <= z.vs_alloca_next /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at su x ==>
       lookup_var x z = lookup_var x t /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame ce ee ee su t z /\ ghost_kept_at lo ce ee su G tn t G' tn' /\
    expr_val_at ce cx (expr_type e) su sb ee v src z
Proof
  MATCH_ACCEPT_TAC (SIMP_RULE bool_ss [unwrap_slot_origin_side_producer_true]
    (Q.INST [`Side` |-> `\_ _ _ _. T`] (SPEC_ALL extcall_saved_slot_copy_replay_side)))
QED

Theorem extcall_saved_slot_copy_replay =
  pureFrameLib.drop_frame extcall_saved_slot_copy_replay_pure
