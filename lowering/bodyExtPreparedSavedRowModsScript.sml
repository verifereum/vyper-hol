(* Transport the saved positional operand to the already reached ABI prepare cut. *)
Theory bodyExtPreparedSavedRowMods
Ancestors
  bodyExtSavedRowInputMods bodyAbiEncodePackedPostMods bodyPtrIfExpAllocSource
  logValueFramePtr revertReasonPrefixPtr tuplePlaceStep valueEncodingTyping
  bodyFullPostsMods bodyPtrDefs loweringPosts freshWrites exprLoweringProps
  exprSimMemDefs venomState ptrDiscipline context finite_map

Theorem prepared_saved_ptr_ok[local]:
  ptr_vv_ok cx ty raw saved ee G tn s /\ read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
  eval_operand (vv_operand saved) p = eval_operand (vv_operand saved) s /\
  op_taint tp (vv_operand saved) = op_taint tn (vv_operand saved) /\
  (!x. vv_operand saved = Var x ==> FLOOKUP Gp x = FLOOKUP G x) /\
  p.vs_accounts = s.vs_accounts /\ p.vs_transient = s.vs_transient /\
  p.vs_call_ctx = s.vs_call_ctx /\ tp.t_stor = tn.t_stor /\ tp.t_trans = tn.t_trans /\
  (!tag ptr. saved = LocatedValue tag ptr ==> ~is_word_type ty) /\
  (!w. eval_operand (vv_operand saved) s = SOME w /\ ~is_word_type ty /\
       (vv_location saved = NONE \/ vv_location saved = SOME LocMemory) ==>
     mem_bytes_at (w2n w) (val_footprint tv v) p.vs_memory =
       mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory /\
     (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tp.t_mem ==>
          i IN tn.t_mem)) ==>
  ptr_vv_ok cx ty raw saved ee Gp tp p
Proof
  Cases_on `saved` >> simp[vv_operand_def,vv_location_def] >>
  disch_then (map_every assume_tac o CONJUNCTS)
  >- (gvs[ptr_vv_ok_def] >> irule ptr_val_ok_footprint_frame >>
      qexistsl [`G`,`s`,`tn`] >> simp[]) >>
  qmatch_goalsub_rename_tac `LocatedValue ann vp` >>
  Cases_on `vp.ptr_location = LocMemory`
  >- (gvs[ptr_vv_ok_def] >> rpt strip_tac >>
      `ptr_val_ok cx ty v vp.ptr_operand G tn s` by simp[ptr_val_ok_def] >>
      `ptr_val_ok cx ty v vp.ptr_operand Gp tp p` by
        (irule ptr_val_ok_footprint_frame >> qexistsl [`G`,`s`,`tn`] >> simp[]) >>
      fs[ptr_val_ok_def]) >>
  irule ptr_vv_ok_nonmemory_frame >> simp[] >> qexistsl [`G`,`s`,`tn`] >> simp[] >>
  Cases_on `vp.ptr_operand` >> gvs[op_prov_def]
QED

Theorem prepared_saved_holds[local]:
  vv_holds_mods ce cx ty raw saved ee s /\ read_result cx raw ee = (INL v,ee) /\
  ptr_vv_ok cx ty raw saved ee Gp tp p /\
  eval_operand (vv_operand saved) p = eval_operand (vv_operand saved) s /\
  p.vs_accounts = s.vs_accounts /\ p.vs_transient = s.vs_transient /\
  p.vs_call_ctx = s.vs_call_ctx /\
  (!tag ptr. saved = LocatedValue tag ptr ==> ~is_word_type ty) ==>
  vv_holds_mods ce cx ty raw saved ee p
Proof
  Cases_on `saved` >> simp[vv_operand_def,vv_holds_mods_def,vv_holds_def] >>
  disch_then (map_every assume_tac o CONJUNCTS)
  >- (gvs[expr_val_rel_def] >> Cases_on `is_word_type ty` >>
      gvs[ptr_vv_ok_def,ptr_val_ok_def,ptr_mem_ok_def] >>
      rpt strip_tac >> first_x_assum drule >>
      disch_then (mp_tac o CONJUNCT1) >>
      disch_then (qspec_then `p.vs_memory` mp_tac) >> simp[mem_agree_outside_def]) >>
  qmatch_asmsub_rename_tac `LocatedValue ann vp` >>
  Cases_on `vp.ptr_location = LocCode`
  >- (gvs[] >> qpat_x_assum `immutable_holds_mods _ _ _ _ _ _ _` mp_tac >>
      pure_rewrite_tac[immutable_holds_mods_def,immutable_holds_def] >>
      disch_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `vp.ptr_location = LocMemory`
  >- (gvs[ptr_vv_ok_def,ptr_mem_ok_def] >> rpt strip_tac >> first_x_assum drule >>
      disch_then (mp_tac o CONJUNCT1) >>
      disch_then (qspec_then `p.vs_memory` mp_tac) >> simp[mem_agree_outside_def]) >>
  Cases_on `vp.ptr_location` >>
  fs[storage_holds_def,contract_storage_def,contract_transient_def]
QED

Theorem prepared_saved_row_at[local]:
  abi_encode_saved_row_mods lo ce cx sa ready e saved v si sm ss vv copy H ee G tn s /\
  read_result cx raw ee = (INL v,ee) /\
  vv_holds_mods ce cx (lowered_value_type ce e) raw saved ee p /\
  vv_at ce cx (lowered_value_type ce e) si ss ee raw saved p /\
  ptr_vv_ok cx (lowered_value_type ce e) raw saved ee Gp tp p /\
  vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee raw saved p /\
  ready.cs_next_var <= prepared.cs_next_var /\ ready.cs_next_id <= prepared.cs_next_id /\
  (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP p.vs_allocas aid = SOME a) /\
  (!n b sz. local_region ce ee.scopes p n b sz <=> local_region ce ee.scopes s n b sz) /\
  eval_operand (vv_operand saved) p = eval_operand (vv_operand saved) s /\
  (!x. vv_operand saved = Var x ==> FLOOKUP Gp x = FLOOKUP G x) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\ val_wf tv v /\
  (!w. eval_operand (vv_operand saved) s = SOME w /\
       ce.ce_is_ctor /\ vv_location saved = SOME LocCode ==>
     mem_bytes_at (w2n w) (val_footprint tv v) p.vs_memory =
       mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory /\
     (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tp.t_mem ==>
          i IN tn.t_mem)) ==>
  abi_encode_saved_row_mods lo ce cx sa prepared e saved v si sm ss vv copy H ee Gp tp p
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_encode_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
  asm_rewrite_tac[abi_encode_saved_row_mods_def] >>
  conj_tac >- (strip_tac >>
    qpat_x_assum `copy /\ ~is_word_type _ ==> _` mp_tac >> simp[] >>
    disch_then (qx_choosel_then [`x`,`w`] strip_assume_tac) >>
    qexistsl [`x`,`w`] >> simp[] >> first_assum ACCEPT_TAC) >>
  `sm.cs_next_var <= prepared.cs_next_var /\ sm.cs_next_id <= prepared.cs_next_id /\
   ss.cs_next_var <= prepared.cs_next_var /\ ss.cs_next_id <= prepared.cs_next_id` by
    decide_tac >>
  asm_rewrite_tac[] >> conj_tac >- (qexists `raw` >> simp[]) >>
  conj_tac >- (Cases_on `saved` >> fs[vv_operand_def,vv_storage_live_def]) >>
  conj_tac >- (rpt strip_tac >> gvs[vv_operand_def,ptr_buf_ok_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> gvs[vv_operand_def,ptr_buf_ok_def] >> metis_tac[]) >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  `rt = tv` by fs[] >>
  `eval_operand (vv_operand saved) s = SOME w` by simp[] >>
  `w2n w + type_memory_size tv <= lo /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v (w2n w) mem)` by
    (qpat_x_assum `ce.ce_is_ctor /\ vv_location saved = SOME LocCode ==> _` mp_tac >>
     (impl_tac >- asm_rewrite_tac[]) >>
     disch_then (qspecl_then [`tv`,`w`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `rt = tv` SUBST_ALL_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  ho_match_mp_tac robust_val_in_memory_footprint_frame >> qexistsl [`tn.t_mem`,`s.vs_memory`] >>
  qpat_assum `!u. eval_operand _ s = SOME u /\ _ ==> _` (qspec_then `w` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem ext_prepared_saved_row_mods:
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ext_pos_saved_row_mods lo ce cx kw_es sa ready H e saved v ee G tn s /\
    stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo ret ce cx ee G tn s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  ty = lowered_value_type ce e /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < 2**64 /\ vyper_to_abi (get_tenv cx) ty v = SOME av /\
  abi_encoder_layout_valid (vyper_to_abi_type (get_tenv cx) ty) av /\
  ready.cs_next_var <= prepared.cs_next_var /\ ready.cs_next_id <= prepared.cs_next_id /\
  (!x u. not_fresh_at ready x /\ lookup_var x s = SOME u ==> lookup_var x p = SOME u) /\
  (!x. not_fresh_at ready x ==> FLOOKUP Gp x = FLOOKUP G x /\
       op_taint tp (Var x) = op_taint tn (Var x)) /\
  (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP p.vs_allocas aid = SOME a) /\
  s.vs_alloca_next <= p.vs_alloca_next /\ p.vs_labels = s.vs_labels /\
  p.vs_accounts = s.vs_accounts /\ p.vs_transient = s.vs_transient /\
  p.vs_call_ctx = s.vs_call_ctx /\ tp.t_stor = tn.t_stor /\ tp.t_trans = tn.t_trans /\
  (!w. eval_operand (vv_operand saved) s = SOME w /\
       ((~is_word_type ty /\ (vv_location saved = NONE \/ vv_location saved = SOME LocMemory)) \/
        (ce.ce_is_ctor /\ vv_location saved = SOME LocCode)) ==>
     mem_bytes_at (w2n w) (val_footprint tv v) p.vs_memory =
       mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory /\
     (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tp.t_mem ==>
          i IN tn.t_mem)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee p /\ immutable_frame_mods func ce cx ee p /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo ret ce cx ee Gp tp p) ==>
  ?si sm ss vv copy raw w at bytes.
    compile_expr ce (expr_type e) e si = (vv,sm) /\
    compile_snapshot_vv ce copy (ext_call_arg_value ty vv) sm = (saved,ss) /\
    read_result cx raw ee = (INL v,ee) /\ vv_holds_mods ce cx ty raw saved ee p /\
    vv_at ce cx ty si ss ee raw saved p /\ ptr_vv_ok cx ty raw saved ee Gp tp p /\
    vv_store_bound cx ty ty ee raw saved p /\
    (!x. vv_operand saved = Var x ==> not_fresh_at prepared x) /\
    eval_operand (vv_operand saved) p = SOME w /\ op_taint tp (vv_operand saved) = {} /\
    (is_word_type ty ==> (?tag. saved = StackValue tag (vv_operand saved)) /\
      w = typed_val_to_w256 tv v) /\
    at = vyper_to_abi_type (get_tenv cx) ty /\ bytes = enc at av /\
    abi_encoder_layout_valid at av /\ (~is_dynamic at ==> LENGTH bytes = abi_member_head_size at) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      abi_encode_saved_row_mods lo ce cx sa prepared e saved v si sm ss vv copy H ee Gp tp p /\
      stmt_state_rel H ctx func ce cx ee p /\ immutable_frame_mods func ce cx ee p /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo ret ce cx ee Gp tp p)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ext_saved_row_input_mods >>
  disch_then (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`copy`,`raw`,`w`,`at`,`bytes`]
    (map_every assume_tac o CONJUNCTS)) >>
  `eval_operand (vv_operand saved) p = SOME w /\
   op_taint tp (vv_operand saved) = op_taint tn (vv_operand saved) /\
   (!x. vv_operand saved = Var x ==> FLOOKUP Gp x = FLOOKUP G x)` by
    (Cases_on `vv_operand saved` >> fs[eval_operand_def,op_taint_def] >> metis_tac[]) >>
  `!x. vv_operand saved = Var x ==> not_fresh_at prepared x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `ready` >> simp[]) >>
  `val_wf tv v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  qpat_x_assum `ty = lowered_value_type ce e` SUBST_ALL_TAC >>
  qpat_x_assum `?H. valid_horizon _ _ H _` (qx_choose_then `H0` assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> abi_encode_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  `local_ptrs_reserved ce ready` by
    (qpat_assum `abi_encode_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
     `si.cs_next_var <= ready.cs_next_var` by
       (drule (CONJUNCT1 compile_expr_grows) >> strip_tac >> decide_tac) >>
     irule local_ptrs_reserved_next_var >> qexists `si` >> simp[]) >>
  `!n b sz. local_region ce ee.scopes p n b sz <=> local_region ce ee.scopes s n b sz` by
    (irule (INST_TYPE [``:'a`` |-> ``:256``] tuple_place_endpoint_local_regions_some) >> simp[] >>
     conj_tac >- (qexists `ready` >> simp[]) >>
     qexistsl [`H0`,`ctx`,`cx`,`func`] >> simp[]) >>
  `!tag ptr. saved = LocatedValue tag ptr ==> ~is_word_type (lowered_value_type ce e)` by
    (rpt strip_tac >> first_x_assum drule >> gvs[]) >>
  `ptr_vv_ok cx (lowered_value_type ce e) raw saved ee Gp tp p` by
    (irule prepared_saved_ptr_ok >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`G`,`s`,`tn`,`tv`,`v`] >> simp[] >> disch_tac >>
     qpat_x_assum `!u. eval_operand _ s = SOME u /\ _ ==> _` (qspec_then `w` mp_tac) >>
     (impl_tac >- asm_rewrite_tac[]) >> disch_tac >> first_assum ACCEPT_TAC) >>
  `vv_holds_mods ce cx (lowered_value_type ce e) raw saved ee p` by
    (irule prepared_saved_holds >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexists `v` >> simp[]) >>
     conj_tac >- (qexists `s` >> simp[]) >>
     qexistsl [`Gp`,`tp`] >> simp[]) >>
  `vv_at ce cx (lowered_value_type ce e) si ss ee raw saved p` by
    (irule vv_at_alloc_map_frame >> qexistsl [`s`,`ss`] >> simp[]) >>
  `vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee raw saved p` by
    (irule vv_store_bound_frame_mem_src >> qexists `s` >> simp[]) >>
  qexistsl [`si`,`sm`,`ss`,`vv`,`copy`,`raw`,`w`,`at`,`bytes`] >> asm_rewrite_tac[] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> abi_encode_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  reverse conj_tac
  >- (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ p /\ _`
        (qspec_then `H` (drule_then strip_assume_tac)) >> asm_rewrite_tac[]) >>
  irule prepared_saved_row_at >> conj_tac >- (qexists `raw` >> simp[]) >>
  qexistsl [`G`,`ready`,`s`,`tn`,`tv`] >> simp[] >> disch_tac >>
  qpat_x_assum `!u. eval_operand _ s = SOME u /\ _ ==> _` (qspec_then `w` mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> disch_tac >> first_assum ACCEPT_TAC
QED
