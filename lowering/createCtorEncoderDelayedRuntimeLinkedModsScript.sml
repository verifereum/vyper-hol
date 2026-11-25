(* The linked encoder-facing adapter for a delayed runtime-code read.  The
   runtime arrival theorem already packages the concrete copy endpoint, all-H
   linked posts, and the all-D path at one state. *)
Theory createCtorEncoderDelayedRuntimeLinkedMods
Ancestors
  createCtorUnwrapRuntimeCodeArrivalMods createCtorEncoderSavedAdvanceMods
  createCtorEncoderDelayedRuntimeMods
  loweringPosts exprLoweringProps compileEnv bodyFullPostsMods bodyPtrDefs
  context exprOperandVar gasOriginPtrLabels exprSimProps vyperStorageFootprint

Theorem ctor_encoder_delayed_runtime_linked_mods =
  ctor_unwrap_runtime_code_arrival_mods

(* The delayed read starts from the advanced row, without assuming a
   historical expression post at the encoder cut. *)
Theorem ctor_encoder_delayed_runtime_linked_callback_mods:
  ty = lowered_value_type ce e /\ ty = expr_type e /\ ~is_word_type ty /\
  ~ce.ce_is_ctor /\ saved = LocatedValue ty p /\ p.ptr_location = LocCode /\
  compile_expr ce (expr_type e) e si = (saved,sm) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  sm.cs_next_var <= su.cs_next_var /\ sm.cs_next_id <= su.cs_next_id /\
  local_ptrs_reserved ce si /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  unwrap_value ce saved su = (src,sb) /\ fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  evaluate_type (get_tenv cx) ty = SOME rt /\
  type_memory_bytes ce ty = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ value_has_type rt v /\
  storage_trace_domain cx st0 ee.storage_trace /\ read_result cx raw ee = (INL v,ee) /\
  vv_holds_mods ce cx ty raw saved ee u /\ vv_at ce cx ty si ss ee raw saved u /\
  ptr_vv_ok cx ty raw saved ee Gu tu u /\ vv_store_bound cx ty ty ee raw saved u /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func ce cx ee u /\ immutable_frame_mods func ce cx ee u /\
     storage_well_formed_on cx ee (FST H) /\ vv_storage_live H cx saved ee u /\
     ghost_inv_at_mods (DF H) lo d ce cx ee Gu tu u) /\
  (!x. vv_operand saved = Var x ==> not_fresh_at su x) /\
  alloca_history func u /\ ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
  u.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?z G' tn'.
    pure_frame ce func ee su u z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
       storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at_mods (DF H) lo d ce cx ee G' tn' z) /\
    expr_val_rel cx ty v src z /\ ptr_val_ok cx ty v src G' tn' z /\
    expr_store_bound cx ty v src z /\ ptr_buf_ok ce e src G' z /\
    (!w. eval_operand src z = SOME w ==>
       type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\ z.vs_labels = u.vs_labels /\
    (!x. not_fresh_at su x ==>
       lookup_var x z = lookup_var x u /\ FLOOKUP G' x = FLOOKUP Gu x /\
       op_taint tn' (Var x) = op_taint tu (Var x)) /\
    wb_frame ce ee ee su u z /\ ghost_kept_at lo ce ee su Gu tu u G' tn' /\
    (!x. src = Var x ==> not_fresh_at sb x) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,G',tn')) /\
    expr_val_at ce cx ty su sb ee v src z
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `post_value_type ce e = ty` by metis_tac[post_value_type_lowered] >>
  `si.cs_next_var <= sm.cs_next_var /\ si.cs_next_id <= sm.cs_next_id` by
    (qspecl_then [`ce`,`expr_type e`,`e`,`si`] mp_tac (CONJUNCT1 compile_expr_ci_mono) >>
     simp[ci_mono_def]) >>
  `vv_holds_mods ce cx ty (Value v) saved ee u` by
    (qpat_assum `vv_holds_mods _ _ _ raw _ _ _` mp_tac >>
     gvs[vv_holds_mods_def,immutable_holds_mods_def,immutable_holds_def,
         vyperStateTheory.read_result_def,vyperStateTheory.return_def] >> metis_tac[]) >>
  `ptr_vv_ok cx ty (Value v) saved ee Gu tu u` by
    (qpat_assum `ptr_vv_ok _ _ raw _ _ _ _ _` mp_tac >>
     qpat_assum `saved = LocatedValue _ _` (fn th =>
       qpat_assum `p.ptr_location = LocCode` (fn loc => simp[NoAsms,th,loc,ptr_vv_ok_def]))) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post_mods H ctx func ce cx e ee si sm u ee (Value v) saved u /\
     ghost_inv_at_mods (DF H) lo d ce cx ee Gu tu u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     gvs[] >> simp[vv_post_mods_def,vv_at_def,vv_own_def,vv_place_ptr_mods_def,vv_place_ptr_def]) >>
  `ghost_kept_at lo ce ee si Gu tu u Gu tu` by simp[ghost_kept_at_def] >>
  `!x. vv_operand saved = Var x ==> not_fresh_at sm x` by simp[vv_operand_def] >>
  `!x. src = Var x ==> not_fresh_at sb x` by
    (drule compiler_unwrap_value_var >> simp[vv_operand_def]) >>
  gvs[] >>
  qpat_assum `post_value_type ce e = _` (fn th =>
    drule_all (SRULE [th] (Q.INST
      [`cenv` |-> `ce`, `es` |-> `ee`, `s0` |-> `s`, `Gi` |-> `G`, `ti` |-> `tn`,
       `vv` |-> `LocatedValue t p`]
      ctor_unwrap_runtime_code_arrival_strong_mods))) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  gvs[vyperStateTheory.read_result_def,vyperStateTheory.return_def] >>
  `z.vs_labels = u.vs_labels` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ [] (OK z,_,_)`
       (qspec_then `DF (storage_trace_horizon ee.storage_trace)`
         (mp_then Any ACCEPT_TAC gas_origin_ptr_path_preserves_labels))) >>
  qexistsl_tac [`z`,`G'`,`tn'`] >> simp[] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >>
      fs[expr_post_mods_def,expr_post_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspecl_then [`storage_trace_horizon ee.storage_trace`] (drule_then strip_assume_tac)) >>
  fs[expr_post_mods_def,expr_post_def] >>
  qpat_assum `post_value_type ce e = _` (fn th => fs[th])
QED
