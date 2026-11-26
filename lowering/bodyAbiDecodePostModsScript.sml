(* Interpret the already selected physical decoder endpoint. *)
Theory bodyAbiDecodePostMods
Ancestors
  bodyFullPostsMods gasOutcomeFullPostMods bodySliceWindowGhostMods
  exprSimAbiDecodeValueFrame exprSimAbiDecodeSuccessBoundary
  exprSimAbiDecodeReject abiValidBytesUnwrap abiDecodeUnwrapCase
  exprSimAbiDecodeEntryTyping exprSimAbiDecodeEntryLayout
  exprSimAbiDecodeEntryMetadata exprBodyPreProps exprSimHypsDefs
  loweringPosts bodyPtrDefs compileEnv exprSimDefs exprSimMemDefs
  exprLoweringProps vyperTypeABI vyperTyping vyperAST vyperState vyperContext
  valueEncodingDefs valueEncodingTyping words finite_map venomState
  stateRelProj exprSimAbiDecodeResources exprSimAbiDecodeRegionFrame
  exprSimAbiDecodeImmutableOutcome exprSimAbiDecodeImmutableFrame
  exprSimAbiDecodeQuantifiedLift exprSimAbiDecodeEndpointFrame
  exprSimAbiDecodeStateFrame abiDecoderSiteEffect exprSimAbiDecodeOblivious
  loweringStateRelDefs bodyMemoryDefs abiBoundaryChecks exprSimAbiDecodeSetupExec
  exprSimProps context allocaSiteResource
  bodyFullHashKeccakFixed[qualified,ignore_grammar]

Theorem abi_decode_closed_value_mods[local]:
  (wty = if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) /\
  (wtv = if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  abi_decode_success_closed ce (get_tenv cx) wty wtv bs out dst start final ctx func s t ==>
  ?v. evaluate_type_builtin cx (AbiDecode unwrap) ty tys [BytesV bs] = INL v /\
      vv_holds ce cx ty (Value v) (LocatedValue ty (mk_ptr out LocMemory)) ee t /\
      value_has_type tv v
Proof
  strip_tac >>
  Cases_on `unwrap /\ needs_external_call_wrap ty`
  >- (gvs[] >> `evaluate_type (get_tenv cx) (TupleT [ty]) = SOME (TupleTV [tv])` by
        (drule abi_decode_wrapped_type >> disch_then (qspec_then `T` mp_tac) >> simp[]) >>
      drule_all abi_decode_success_singleton_vv_holds >>
      disch_then (qspec_then `ee` strip_assume_tac) >>
      `value_has_type tv v` by
        (drule_all evaluate_abi_decode_well_typed >> simp[value_has_type_def]) >>
      qexists_tac `v` >> gvs[abi_source_decode_wrapping_iff]) >>
  gvs[] >> drule_all abi_decode_success_vv_holds >>
  disch_then (qspec_then `ee` strip_assume_tac) >>
  `value_has_type tv v` by drule_all_then ACCEPT_TAC evaluate_abi_decode_well_typed >>
  qexists_tac `v` >> gvs[abi_source_decode_wrapping_iff]
QED

Theorem abi_decode_selected_revert_mods[local]:
  evaluate_abi_decode (get_tenv cx)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) bs = INR err /\
  ~s.vs_halted /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort Revert_abort z,Gf,tf)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) ce.ce_modules cx st0
    (bind (lift_sum (evaluate_type_builtin cx (AbiDecode unwrap) ty tys [BytesV bs]))
      (\v. return (Value v))) (ee,s,G,tn) Q
    (\H res ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==> !t. r = Halt t ==> allocas_below_fmp t))
Proof
  strip_tac >> drule (cj 1 abi_decode_builtin_reject) >>
  disch_then (qspecl_then [`tys`] assume_tac) >>
  irule gas_outcome_full_mods_exit_revert >> simp[] >>
  qexistsl_tac [`Gf`, `ee`, `INR (Error (RuntimeError err))`, `tf`, `z`] >>
  simp[lift_sum_def, bind_def, raise_def, fragExecTheory.exit_result_def,
       expr_exit_def, halt_exit_def]
QED

(* The window theorem protects the caller's immutable section regardless of
   which module owns an individual immutable.  The old-frontier taint
   condition is a property of the selected pointer/taint run. *)
Theorem abi_decode_selected_frames_mods[local]:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce wty)
    (abi_static_size ce.ce_struct_fields wty) (abi_size_bound ce.ce_struct_fields wty)
    (type_memory_bytes ce wty) start = (out,final) /\
  fn_has_code start final func /\ fn_inst_ids_distinct func /\
  abi_decode_immutable_success ce (get_tenv cx) wty wtv bs out dst start final
    ctx func cx ee s t /\
  stmt_state_rel H ctx func ce cx ee s /\
  immutable_frame_mods func ce cx ee s /\
  ghost_inv_at_mods D lo d ce cx ee G tn s /\
  local_ptrs_reserved ce start /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x) /\
  (!x. not_fresh_at start x ==>
       lookup_var x t = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!i. i < s.vs_alloca_next /\ i IN tf.t_mem ==> i IN tn.t_mem) /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory ==>
  ghost_inv_at_mods D lo d ce cx ee Gf tf t /\ immutable_frame_mods func ce cx ee t
Proof
  strip_tac >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_then strip_assume_tac lower_abi_decode_frag_facts >>
  `!i. MEM i (frag_code start final) ==> MEM i (fn_insts func)` by
    metis_tac[abi_decode_resources_code_member] >>
  qpat_assum `abi_decode_immutable_success _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_decode_immutable_success_def]) >>
  `!name b n. local_region ce ee.scopes s name b n ==>
      mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC abi_decode_success_local_memory) >>
  `pure_frame ce func ee start s t` by
    (pure_rewrite_tac[pure_frame_def] >> conj_tac
     >- first_assum ACCEPT_TAC >>
     qpat_assum `abi_decode_window_frame _ _ _ _`
       (ACCEPT_TAC o REWRITE_RULE [abi_decode_window_frame_def])) >>
  `t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
   t.vs_data_section = s.vs_data_section` by
    (drule abi_decode_closed_effect >> strip_tac >>
     fs[decode_site_effect_def,decode_static_frame_def] >>
     qpat_x_assum `u = _` (fn th => rpt conj_tac >> simp_tac (srw_ss()) [Once th])) >>
  `abi_decode_allocation_floor s.vs_alloca_next s.vs_allocas t` by
    fs[abi_decode_success_closed_def] >>
  qpat_x_assum `abi_decode_allocation_floor _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_decode_allocation_floor_def]) >>
  `!name b n. local_region ce ee.scopes s name b n ==>
       mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory /\
       (!i. b <= i /\ i < b+n /\ i IN tf.t_mem ==> i IN tn.t_mem)` by
    (rpt strip_tac >- metis_tac[] >>
     drule_all_then assume_tac body_local_region_frontier >>
     first_x_assum irule >> simp[] >> decide_tac) >>
  drule_all_then strip_assume_tac slice_window_ghost_frame_mods >> simp[]
QED

Theorem abi_decode_selected_memory_mods[local]:
  (wty = if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) /\
  (wtv = if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  abi_decode_success_closed ce (get_tenv cx) wty wtv bs out dst start final
    ctx func s t /\
  evaluate_type_builtin cx (AbiDecode unwrap) ty tys [BytesV bs] = INL v /\
  (!x. value_has_type wtv x /\ val_wf wtv x /\
       val_in_memory wtv x dst t.vs_memory ==>
       !mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
             val_in_memory wtv x dst mem) ==>
  val_wf tv v /\ val_in_memory tv v dst t.vs_memory /\
  (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==> val_in_memory tv v dst mem)
Proof
  strip_tac >>
  drule abi_decode_success_value >>
  disch_then (qx_choose_then `x` strip_assume_tac) >>
  `evaluate_type (get_tenv cx) wty = SOME wtv` by simp[abi_decode_wrapped_type] >>
  `evaluate_abi_decode (get_tenv cx) wty bs =
    INL (if unwrap /\ needs_external_call_wrap ty then ArrayV (TupleV [v]) else v)` by
    (qpat_assum `wty = _` SUBST1_TAC >>
     qpat_assum `evaluate_type_builtin _ _ _ _ _ = INL v`
       (ACCEPT_TAC o MATCH_MP (iffLR abi_source_decode_wrapping_iff))) >>
  `x = if unwrap /\ needs_external_call_wrap ty then ArrayV (TupleV [v]) else v` by
    metis_tac[sumTheory.INL_11] >>
  `value_has_type wtv x` by drule_all_then ACCEPT_TAC evaluate_abi_decode_well_typed >>
  `val_wf wtv x` by metis_tac[value_has_type_val_wf] >>
  `!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==> val_in_memory wtv x dst mem` by
    (qpat_assum `!y. value_has_type _ y /\ _ ==> _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  qpat_x_assum `!y. value_has_type _ y /\ _ ==> _` kall_tac >>
  pop_assum mp_tac >> Cases_on `unwrap /\ needs_external_call_wrap ty` >>
  gvs[val_wf_def, val_in_memory_singleton_tuple]
QED

Theorem abi_decode_selected_pointer_mods[local]:
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv <= cap /\ dst + cap < dimword (:256) /\
  dst + cap <= t.vs_alloca_next /\
  lookup_var output t = SOME (n2w dst) /\ FLOOKUP Gf output = SOME (dst,cap) /\
  op_taint tf (Var output) = {} /\ val_wf tv v /\ val_in_memory tv v dst t.vs_memory /\
  (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==> val_in_memory tv v dst mem) ==>
  ptr_vv_ok cx ty (Value v) (LocatedValue ty (mk_ptr (Var output) LocMemory)) ee Gf tf t /\
  ptr_buf_ok ce (TypeBuiltin ty (AbiDecode unwrap) ty [e]) (Var output) Gf t /\
  vv_store_bound cx ty ty ee (Value v) (LocatedValue ty (mk_ptr (Var output) LocMemory)) t
Proof
  strip_tac >>
  `dst < dimword (:256)` by decide_tac >>
  `val_store_size tv v <= type_memory_size tv` by rw[val_store_size_le] >>
  simp[ptr_vv_ok_def, ptr_mem_ok_def, ptr_buf_ok_def, vv_store_bound_def,
       exprLoweringTheory.lowered_value_type_def, expr_type_def, mk_ptr_def, read_result_def, return_def,
       eval_operand_def] >>
  rpt strip_tac >> gvs[] >> simp[w2n_n2w] >> decide_tac
QED

Theorem abi_decode_selected_own_mods[local]:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce wty)
    (abi_static_size ce.ce_struct_fields wty) (abi_size_bound ce.ce_struct_fields wty)
    (type_memory_bytes ce wty) start = (out,final) /\
  fn_has_code start final func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce start /\ stmt_state_rel H ctx func ce cx ee s /\
  abi_decode_success_closed ce (get_tenv cx) wty wtv bs out dst start final ctx func s t /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
  type_memory_size tv <= type_memory_bytes ce wty /\ sa.cs_next_id <= start.cs_next_id /\
  dst < dimword (:256) ==>
  vv_own ce cx ty sa final ee (Value v) (LocatedValue ty (mk_ptr out LocMemory)) t
Proof
  strip_tac >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_then strip_assume_tac abi_decode_output_site_interval >>
  drule_then strip_assume_tac lower_abi_decode_frag_facts >>
  `!i. MEM i (frag_code start final) ==> MEM i (fn_insts func)` by
    metis_tac[abi_decode_resources_code_member] >>
  `val_footprint tv v <= type_memory_bytes ce wty` by
    (irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `type_memory_size tv` >>
     simp[exprSimPropsTheory.val_footprint_le]) >>
  `!n b sz. local_region ce ee.scopes t n b sz ==>
            regions_disjoint dst (type_memory_bytes ce wty) b sz` by
    (rpt strip_tac >> drule_all abi_decode_success_local_region >> strip_tac >>
     `local_region ce ee.scopes s n b sz` by metis_tac[] >>
     drule_all_then ACCEPT_TAC abi_decode_success_output_local_disjoint) >>
  `eval_operand out t = SOME (n2w dst)` by metis_tac[abi_decode_success_value] >>
  qpat_assum `abi_decode_success_closed _ _ _ _ _ _ _ _ _ _ _ _ _`
    (assume_tac o cj 2 o REWRITE_RULE [abi_decode_success_closed_def]) >>
  simp[vv_own_def, mk_ptr_def, read_result_def, return_def, w2n_n2w] >>
  disj1_tac >>
  qexistsl_tac [`abi_builtin_decode_output_site start (abi_static_size ce.ce_struct_fields wty)
                    (abi_size_bound ce.ce_struct_fields wty)`, `dst`, `type_memory_bytes ce wty`] >>
  fs[regions_disjoint_def] >> first_assum ACCEPT_TAC
QED

Theorem abi_decode_selected_vv_mods[local]:
  expr_post_mods H ctx func ce cx e es sa start s0 ee (BytesV bs) data s /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce start /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= start.cs_next_var /\ sa.cs_next_id <= start.cs_next_id /\
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce wty)
    (abi_static_size ce.ce_struct_fields wty) (abi_size_bound ce.ce_struct_fields wty)
    (type_memory_bytes ce wty) start = (out,final) /\
  fn_has_code start final func /\ fn_inst_ids_distinct func /\
  abi_decode_immutable_success ce (get_tenv cx) wty wtv bs out dst start final
    ctx func cx ee s t /\
  vv_holds ce cx ty (Value v) (LocatedValue ty (mk_ptr out LocMemory)) ee t /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  type_memory_size tv <= type_memory_bytes ce wty /\
  ghost_inv_at_mods D lo d ce cx ee G tn s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x) /\
  (!x. not_fresh_at start x ==>
       lookup_var x t = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!i. i < s.vs_alloca_next /\ i IN tf.t_mem ==> i IN tn.t_mem) /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory ==>
  vv_post_mods H ctx func ce cx (TypeBuiltin ty (AbiDecode unwrap) ty [e]) es sa final s0
    ee (Value v) (LocatedValue ty (mk_ptr out LocMemory)) t /\
  ghost_inv_at_mods D lo d ce cx ee Gf tf t
Proof
  rewrite_tac[expr_post_mods_def] >> strip_tac >>
  drule_then assume_tac exprSimWordArgsTheory.expr_post_state >>
  drule_all_then strip_assume_tac abi_decode_selected_frames_mods >>
  drule_all abi_decode_caller_frames >>
  disch_then (qspec_then `unwrap` mp_tac) >>
  rewrite_tac[vv_post_mods_def, vv_post_def] >> strip_tac >>
  rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE simp[vv_holds_mods_def, vv_place_ptr_mods_def, mk_ptr_def])
QED

Theorem abi_decode_selected_kept_mods[local]:
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\ sa.cs_next_var <= start.cs_next_var /\
  (!x. not_fresh_at start x ==>
       lookup_var x t = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
                off + sz <= s.vs_alloca_next) /\
  (!n b sz. local_region ce es.scopes s0 n b sz ==> b + sz <= s.vs_alloca_next) /\
  (!i. i < s.vs_alloca_next /\ i IN tf.t_mem ==> i IN tn.t_mem) ==>
  ghost_kept_at lo ce es sa G0 tn0 s0 Gf tf
Proof
  rewrite_tac[ghost_kept_at_def] >> strip_tac >> rpt conj_tac
  >- (rpt strip_tac >> metis_tac[freshWritesTheory.not_fresh_at_mono])
  >- (rpt strip_tac >>
      `i < s.vs_alloca_next` by (first_x_assum drule_all >> decide_tac) >>
      metis_tac[]) >>
  rpt strip_tac >>
  `i < s.vs_alloca_next` by (first_x_assum drule_all >> decide_tac) >>
  metis_tac[]
QED

(* The cut selector supplies one path, not a separate run at each horizon.
   Rejection needs no output row and no successful caller resources. *)
Theorem abi_decode_selected_post_mods:
  (wty = if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) /\
  (wtv = if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv) /\
  ~s.vs_halted /\ ee.gas_obs = [] /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,Gf,tf)) /\
  ((?z err. r = Abort Revert_abort z /\ evaluate_abi_decode (get_tenv cx) wty bs = INR err) \/
   (?t. r = OK t /\
        lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce wty)
          (abi_static_size ce.ce_struct_fields wty) (abi_size_bound ce.ce_struct_fields wty)
          (type_memory_bytes ce wty) start = (Var output,final) /\
        abi_decode_immutable_success ce (get_tenv cx) wty wtv bs (Var output) dst start final
          ctx func cx ee s t /\
        evaluate_type (get_tenv cx) ty = SOME tv /\
        type_memory_bytes ce wty = type_memory_size wtv /\
        fn_has_code start final func /\ fn_inst_ids_distinct func /\
        local_ptrs_reserved ce sa /\ local_ptrs_reserved ce start /\
        MAP FDOM es.scopes = MAP FDOM ee.scopes /\
        sa.cs_next_var <= start.cs_next_var /\ sa.cs_next_id <= start.cs_next_id /\
        (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x) /\
        (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x) /\
        (!x. not_fresh_at start x ==>
          lookup_var x t = lookup_var x s /\
          FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
        tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
        (!i. i < s.vs_alloca_next /\ i IN tf.t_mem ==> i IN tn.t_mem) /\
        LENGTH s.vs_memory <= LENGTH t.vs_memory /\
        FLOOKUP Gf output = SOME (dst,type_memory_bytes ce wty) /\
        op_taint tf (Var output) = {} /\ dst + type_memory_bytes ce wty < dimword (:256) /\
        (!x. value_has_type wtv x /\ val_wf wtv x /\ val_in_memory wtv x dst t.vs_memory ==>
          !mem. mem_agree_outside tf.t_mem t.vs_memory mem ==> val_in_memory wtv x dst mem) /\
        t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts /\
        alloca_history func t /\ s0.vs_alloca_next <= s.vs_alloca_next /\
        (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
                      off + sz <= s.vs_alloca_next) /\
        (!n b sz. local_region ce es.scopes s0 n b sz ==> b + sz <= s.vs_alloca_next) /\
        ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
        (!H. valid_horizon cx st0 H ee.storage_trace ==>
            expr_post_mods H ctx func ce cx e es sa start s0 ee (BytesV bs) data s /\
            ghost_inv_at_mods (DF H) lo d ce cx ee G tn s))) ==>
  let E = TypeBuiltin ty (AbiDecode unwrap) ty [e];
      vv = LocatedValue ty (mk_ptr (Var output) LocMemory) in
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) ce.ce_modules cx st0
    (bind (lift_sum (evaluate_type_builtin cx (AbiDecode unwrap) ty [expr_type e] [BytesV bs]))
      (\v. return (Value v))) (ee,s,G,tn)
    (\H res eu Gu tu u. ?tv. res = INL tv /\
      vv_post_mods H ctx func ce cx E es sa final s0 eu tv vv u /\
      vv_store_bound cx (post_value_type ce E) (lowered_value_type ce E) eu tv vv u /\
      u.vs_current_bb = final.cs_current_bb /\ u.vs_inst_idx = LENGTH final.cs_current_insts /\
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d ce cx eu Gu tu u /\
      ptr_vv_ok cx (post_value_type ce E) tv vv eu Gu tu u /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type ce E) /\
           ~is_bytestring_type (post_value_type ce E) ==>
           vv_own ce cx (post_value_type ce E) sa final eu tv vv u /\
           (!rt p. vv = LocatedValue rt p ==> p.ptr_location = LocMemory)) /\
      (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?val. read_result cx tv eu = (INL val, eu) /\
             !rt w. evaluate_type (get_tenv cx) (post_value_type ce E) = SOME rt /\
                    eval_operand (vv_operand vv) u = SOME w ==>
                    w2n w + type_memory_size rt <= lo /\
                    (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
                           val_in_memory rt val (w2n w) mem)) /\
      (!rt op. vv = StackValue rt op /\ ~is_word_type (post_value_type ce E) ==>
               ptr_buf_ok ce E op Gu u) /\
      (!rt p. vv = LocatedValue rt p /\ p.ptr_location = LocMemory ==>
              ptr_buf_ok ce E p.ptr_operand Gu u) /\
      ghost_kept_at lo ce es sa G0 tn0 s0 Gu tu)
    (\H res ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
      (ctx_has_dalloca ctx ==> !t. r = Halt t ==> allocas_below_fmp t))
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac
  >- (irule abi_decode_selected_revert_mods >> gvs[] >> metis_tac[]) >>
  qpat_assum `abi_decode_immutable_success _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (assume_tac o cj 1 o REWRITE_RULE [abi_decode_immutable_success_def]) >>
  qpat_x_assum `r = OK t` SUBST_ALL_TAC >>
  `type_memory_bytes ce wty = type_memory_size tv /\
   type_memory_bytes ce ty = type_memory_size tv` by
    (Cases_on `unwrap /\ needs_external_call_wrap ty` >> gvs[singleton_tuple_memory_sizes]) >>
  `?v. evaluate_type_builtin cx (AbiDecode unwrap) ty [expr_type e] [BytesV bs] = INL v /\
       vv_holds ce cx ty (Value v) (LocatedValue ty (mk_ptr (Var output) LocMemory)) ee t /\
       value_has_type tv v` by (drule_all abi_decode_closed_value_mods >> simp[]) >>
  pop_assum strip_assume_tac >>
  drule_all_then strip_assume_tac abi_decode_selected_memory_mods >>
  drule_all_then assume_tac abi_decode_selected_kept_mods >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    fs[abi_decode_success_closed_def, abi_decode_allocation_floor_def] >>
  `lookup_var output t = SOME (n2w dst)` by
    (drule abi_decode_success_value >>
     disch_then (strip_assume_tac o REWRITE_RULE [eval_operand_def]) >>
     first_assum ACCEPT_TAC) >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`Gf`, `ee`, `INL (Value v)`, `t`, `tf`] >>
  conj_tac >- simp[lift_sum_def, bind_def, return_def] >>
  gen_tac >> strip_tac >> conj_tac
  >- (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
        (drule_then ACCEPT_TAC)) >>
  qexists_tac `Value v` >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `type_memory_size tv <= type_memory_bytes ce wty` by simp[] >>
  drule_all abi_decode_selected_vv_mods >>
  disch_then (qspec_then `unwrap` strip_assume_tac) >>
  `stmt_state_rel H ctx func ce cx ee t` by fs[vv_post_mods_def] >>
  qpat_assum `stmt_state_rel H ctx func ce cx ee t`
    (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
  `dst + type_memory_bytes ce wty <= t.vs_alloca_next` by
    (qpat_assum `abi_decode_success_closed _ _ _ _ _ _ _ _ _ _ _ _ _`
       (assume_tac o cj 2 o REWRITE_RULE [abi_decode_success_closed_def]) >>
     drule_all_then ACCEPT_TAC alloca_site_registered_below) >>
  `dst < dimword (:256)` by decide_tac >>
  `stmt_state_rel H ctx func ce cx ee s` by
    (qpat_assum `expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ s`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
     drule_then ACCEPT_TAC exprSimWordArgsTheory.expr_post_state) >>
  drule_all_then assume_tac abi_decode_selected_own_mods >>
  drule_all abi_decode_selected_pointer_mods >>
  disch_then (qspecl_then [`unwrap`,`ee`,`e`] strip_assume_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    metis_tac[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp] >>
  `((mk_ptr (Var output) LocMemory).ptr_location = LocMemory) /\
   ((mk_ptr (Var output) LocMemory).ptr_operand = Var output)` by simp[mk_ptr_def] >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by decide_tac >>
  simp[post_value_type_def, exprLoweringTheory.lowered_value_type_def, expr_type_def,
       vv_location_def]
QED
