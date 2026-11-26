(* Bridge the ExtCall positional snapshot to the ABI row interface. All
   conclusions refer to the machine state where the saved row is observed. *)
Theory bodyExtSavedRowInputMods
Ancestors
  bodyExtPosSavedRowMods bodyAbiEncodeSavedMemoryMods bodyFullExtCallSavedOperand
  abiEncodeValuesSource
  abiEncoderWindowContract abiEncoderOpenInput bodyFullPostsMods freshWrites bodyPtrDefs
  bodyFullAbiEncodeNonwordWindow exprLowering exprSimMemDefs
  bodyAbiEncodePackedPostMods context loweringPosts loweringStateRelDefs
  compileEnv exprSimHypsDefs vyperContext vyperValue
  vyperABI contractABI abiDecodeRanges venomState pred_set finite_map pair

Theorem ext_saved_read_operand[local]:
  vv_holds_mods ce cx ty raw saved ee s /\ ptr_vv_ok cx ty raw saved ee G tn s /\
  read_result cx raw ee = (INL v,ee) /\ evaluate_type (get_tenv cx) ty = SOME tv ==>
  ?w. eval_operand (vv_operand saved) s = SOME w /\ op_taint tn (vv_operand saved) = {} /\
      ((?tag op. saved = StackValue tag op) /\ is_word_type ty ==>
        w = typed_val_to_w256 tv v)
Proof
  strip_tac >> Cases_on `saved` >>
  fs[vv_holds_mods_def, vv_holds_def, ptr_vv_ok_def, ptr_val_ok_def,
     vv_operand_def, expr_val_rel_def] >>
  metis_tac[]
QED

(* The same snapshot witnesses also work at every valid storage horizon:
   only vv_storage_live, not the compiler/read witnesses, varies with H. *)
Theorem ext_saved_row_input_mods:
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ext_pos_saved_row_mods lo ce cx kw_es sa ready H e saved v ee G tn s /\
    stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  ty = lowered_value_type ce e /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < 2**64 /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\
  abi_encoder_layout_valid (vyper_to_abi_type (get_tenv cx) ty) av ==>
  ?si sm ss vv copy raw w at bytes.
    compile_expr ce (expr_type e) e si = (vv,sm) /\
    compile_snapshot_vv ce copy (ext_call_arg_value ty vv) sm = (saved,ss) /\
    read_result cx raw ee = (INL v,ee) /\ vv_holds_mods ce cx ty raw saved ee s /\
    vv_at ce cx ty si ss ee raw saved s /\ ptr_vv_ok cx ty raw saved ee G tn s /\
    vv_store_bound cx ty ty ee raw saved s /\
    (!x. vv_operand saved = Var x ==> not_fresh_at ready x) /\
    eval_operand (vv_operand saved) s = SOME w /\ op_taint tn (vv_operand saved) = {} /\
    (is_word_type ty ==> (?tag. saved = StackValue tag (vv_operand saved)) /\
      w = typed_val_to_w256 tv v) /\
    at = vyper_to_abi_type (get_tenv cx) ty /\ bytes = enc at av /\
    abi_encoder_layout_valid at av /\
    (~is_dynamic at ==> LENGTH bytes = abi_member_head_size at) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      abi_encode_saved_row_mods lo ce cx sa ready e saved v si sm ss vv copy H ee G tn s /\
      stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `ty = lowered_value_type ce e` SUBST_ALL_TAC >>
  qpat_x_assum `?H. valid_horizon _ _ H _` (qx_choose_then `H0` assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  qpat_x_assum `ext_pos_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [ext_pos_saved_row_mods_def]) >>
  disch_then (CONJUNCTS_THEN2
    (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`raw`,`copy`] (map_every assume_tac o CONJUNCTS))
    (map_every assume_tac o CONJUNCTS)) >>
  drule_all ext_saved_read_operand >> disch_then (qx_choose_then `w` strip_assume_tac) >>
  `!x. vv_operand saved = Var x ==> not_fresh_at ss x` by
    (qpat_assum `compile_expr _ _ _ _ = _`
       (mp_then (Pos hd) mp_tac extcall_saved_operand_not_fresh) >>
     disch_then (qspecl_then [`lowered_value_type ce e`,`ss`,`saved`,`copy`] mp_tac) >>
     simp[]) >>
  `!x. vv_operand saved = Var x ==> not_fresh_at ready x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `ss` >> simp[]) >>
  qexistsl [`si`,`sm`,`ss`,`vv`,`copy`,`raw`,`w`,
    `vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)`,
    `enc (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) av`] >>
  asm_rewrite_tac[] >>
  conj_tac >- (strip_tac >> fs[vv_operand_def]) >>
  conj_tac >- fs[abi_encoder_layout_valid_def,abi_member_head_size_def] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  asm_rewrite_tac[abi_encode_saved_row_mods_def] >>
  conj_tac >- (qexists `raw` >> asm_rewrite_tac[]) >>
  qpat_x_assum `ext_pos_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ext_pos_saved_row_mods_def]) >>
  first_assum ACCEPT_TAC
QED

(* For identity unwrap the source is at the original snapshot interval, not
   an artificial allocation at the empty unwrap interval. *)
Theorem ext_saved_row_identity_mods:
  abi_encode_saved_row_mods lo ce cx origin ready e saved v si sm ss vv copy H ee G tn s /\
  ty = lowered_value_type ce e /\
  ((?tag op. saved = StackValue tag op) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory)) /\
  unwrap_value ce saved ready = (src,u) /\
  (!x. vv_operand saved = Var x ==> not_fresh_at ready x) /\ ~s.vs_halted ==>
  u = ready /\ src = vv_operand saved /\
  expr_val_at ce cx ty si ss ee v src s /\ expr_val_rel cx ty v src s /\
  ptr_val_ok cx ty v src G tn s /\ expr_store_bound cx ty v src s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_encode_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
  qpat_x_assum `?raw. read_result _ raw _ = _ /\ _` strip_assume_tac >>
  `src = vv_operand saved` by
    (Cases_on `saved` >> gvs[unwrap_value_def,comp_return_def,vv_operand_def]) >>
  `!x. src = Var x ==> not_fresh_at ready x` by simp[] >>
  `vv_holds_mods ce cx ty raw saved ee s /\ vv_at ce cx ty si ss ee raw saved s /\
   ptr_vv_ok cx ty raw saved ee G tn s /\ vv_store_bound cx ty ty ee raw saved s` by simp[] >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_encode_saved_memory_restore_mods >> simp[]
QED

(* This interface is independent of the destination allocation. The second
   clause can be instantiated with the actual payload or scratch owner. *)
Theorem ext_saved_row_window_mods:
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi (get_tenv cx) ty v = SOME av /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!t rt. evaluate_type (get_tenv cx) t = SOME rt ==> type_memory_bytes ce t = type_memory_size rt) /\
  expr_val_at ce cx ty first last ee v src s /\
  expr_val_rel cx ty v src s /\ ptr_val_ok cx ty v src G tn s /\
  expr_store_bound cx ty v src s ==>
  ?w at rv.
    eval_operand src s = SOME w /\ op_taint tn src = {} /\
    enc at rv = enc (vyper_to_abi_type (get_tenv cx) ty) av /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      abi_encoder_window_input (type_to_abi_enc_info ce.ce_struct_fields ce ty)
        at rv (w2n w) (val_footprint tv v) mem) /\
    (0 < val_footprint tv v ==> w2n w + val_footprint tv v <= s.vs_alloca_next /\
      ?p. src = Var p /\ ptr_covers G tn p s (val_footprint tv v)) /\
    (!H ctx func owner x b n dest len.
      stmt_state_rel H ctx func ce cx ee s /\ fn_inst_ids_distinct func /\
      MEM owner (fn_insts func) /\ owner.inst_outputs = [x] /\
      not_local_ptr ce ee.scopes x /\
      (owner.inst_id < first.cs_next_id \/ last.cs_next_id <= owner.inst_id) /\
      FLOOKUP s.vs_allocas owner.inst_id = SOME (b,n) /\ b <= dest /\ dest + len <= b+n ==>
      venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (dest,len))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_encode_values_memory_operand >> strip_tac >>
  `?at rv. enc at rv = enc (vyper_to_abi_type (get_tenv cx) ty) av /\
     !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       abi_encoder_window_input (type_to_abi_enc_info ce.ce_struct_fields ce ty)
         at rv (w2n w) (val_footprint tv v) mem` by
    (irule abi_encode_uniform_translated_footprint_window >>
     simp[] >> qexists `get_tenv cx` >> simp[]) >>
  qexistsl [`w`,`at`,`rv`] >> asm_rewrite_tac[] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then ACCEPT_TAC abi_encode_values_source_destination
QED
