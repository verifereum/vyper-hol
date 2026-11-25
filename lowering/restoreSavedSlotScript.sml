(* Geometry-guarded scope for the selected storage/transient restore. *)
Theory restoreSavedSlot
Ancestors
  bodySavedSlotSide entryStageSlotUnwrap entryCreateCompletedCut
  bodyFullUnwrapSlotOrigin
  compileEnv context venomState venomInst fragExec
  arithmetic list rich_list pair

Definition restore_slot_geom_def:
  restore_slot_geom fn a b <=>
    (!bb. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    (!bb i. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
      i.inst_id NOTIN frag_ids a b)
End

Theorem restore_slot_origin_side_supplier:
  unwrap_slot_origin_side_producer ctx func lo explicit PG
    (\a b s t. restore_slot_geom func a b ==>
      create_operand_full_scope a b explicit ctx func s [] (OK t))
Proof
  pure_rewrite_tac[bodyFullUnwrapSlotTheory.unwrap_slot_origin_side_producer_def] >>
  rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qx_gen_tac `G` >>
  Cases_on `restore_slot_geom func sa sb`
  >- (qpat_assum `restore_slot_geom _ _ _`
        (strip_assume_tac o REWRITE_RULE [restore_slot_geom_def]) >>
      mp_tac (INST_TYPE [alpha |-> ``:256``]
        entryStageSlotUnwrapTheory.stage_ensure_slot_origin_scoped) >>
      impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
      disch_then (qx_choosel_then
        [`root`,`d`,`a`,`G0`,`tn0`,`Gf`,`tnf`,`t`,`sm`,`buf`,`u`]
        strip_assume_tac) >>
      qexistsl_tac [`root`,`d`,`a`,`G0`,`tn0`,`Gf`,`tnf`,`t`,`sm`,`buf`,`u`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      simp[restore_slot_geom_def, create_operand_full_scope_def,
           entryCreateFocusSpecTheory.create_operand_at_def] >>
      metis_tac[])
  >> mp_tac (INST_TYPE [alpha |-> ``:256``]
       bodyFullUnwrapSlotOriginTheory.unwrap_ensure_slot_origin_execution) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
     disch_then (qx_choosel_then
       [`root`,`d`,`a`,`G0`,`tn0`,`Gf`,`tnf`,`t`,`sm`,`buf`,`u`]
       strip_assume_tac) >>
     qexistsl_tac [`root`,`d`,`a`,`G0`,`tn0`,`Gf`,`tnf`,`t`,`sm`,`buf`,`u`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     gvs[restore_slot_geom_def]
QED

Theorem extcall_saved_slot_replay_from_observed_loop:
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
    vv_post H ctx fn ce cx e ee si sm t ee (Value v)
      (LocatedValue (expr_type e) p) t /\
    ghost_inv_at (DF H) lo d ce cx ee G tn t) /\
  alloca_history fn t /\ ~t.vs_halted /\
  t.vs_current_bb = su.cs_current_bb /\
  t.vs_inst_idx = LENGTH su.cs_current_insts /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) ==>
  ?z G' tn'.
    (restore_slot_geom fn su sb ==>
      create_operand_full_scope su sb explicit ctx fn t [] (OK z)) /\
    pure_frame ce fn ee su t z /\
    gas_origin_ptr_path
      (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,
       lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,G',tn') /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (t,G,tn) [] (OK z,G',tn') /\
      stmt_state_rel H ctx fn ce cx ee z /\
      storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee G' tn' z) /\
    expr_val_rel cx (expr_type e) v src z /\
    ptr_val_ok cx (expr_type e) v src G' tn' z /\
    expr_store_bound cx (expr_type e) v src z /\
    ptr_buf_ok ce e src G' z /\
    (!w. eval_operand src z = SOME w ==>
      type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    alloca_history fn z /\ t.vs_alloca_next <= z.vs_alloca_next /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at su x ==>
      lookup_var x z = lookup_var x t /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame ce ee ee su t z /\
    ghost_kept_at lo ce ee su G tn t G' tn' /\
    expr_val_at ce cx (expr_type e) su sb ee v src z
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  mp_tac (Q.INST [`Side` |->
    `\a b s z. restore_slot_geom fn a b ==>
       create_operand_full_scope a b explicit ctx fn s [] (OK z)`]
    (SPEC_ALL bodySavedSlotSideTheory.extcall_saved_slot_copy_replay_side)) >>
  impl_tac >-
    (rpt conj_tac >>
     FIRST [MATCH_ACCEPT_TAC restore_slot_origin_side_supplier,
            first_assum ACCEPT_TAC]) >>
  disch_then (qx_choosel_then [`z`,`G'`,`tn'`]
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  qexistsl_tac [`z`,`G'`,`tn'`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  (gvs[])
QED
