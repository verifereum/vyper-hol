Theory bodyFullExtCallDirectStore
Ancestors
  bodyFullExtCallDirectState abiEncodeValuesStaticPrefix abiEncodeValuesStatic
  abiEncodeValuesDynamicPrefix abiEncodeValuesSource abiEncodeValuesRun
  exprSimAbiEncodeSiteResources exprSimAbiEncodeExecFrame exprSimAbiEncodePlanMetadata
  abiEncoderWindowPhase abiEncoderWindowContract abiEncoderOpenInput
  abiEncoderWindow abiEncoderAdmissible
  abiEncoderProps abiDecodeRanges abiCallerTupleLayout allocaSiteResource
  stateRelProj bodyPtrDefs loweringPosts loweringStateRelDefs fragGasOriginPtr fragExec
  compileEnv exprLowering exprLoweringProps context contractABI
  valueEncodingDefs vyperValue vyperTyping vyperABI
  venomState venomInst venomMemDefs finite_map pred_set list arithmetic pair words
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
Libs horizonTypeLib pureFrameLib

Theorem abi_encode_saved_store_static_phase:
  abi_values_source_phase ctx func lo explicit PG R /\
  (!a u. u.vs_current_bb = a.cs_current_bb /\
         u.vs_inst_idx = LENGTH a.cs_current_insts ==> R a a u u) /\
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  shared <> loc /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i a u Gu tu /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ at = vyper_to_abi_type (get_tenv cx) ty /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  hs = abi_member_head_size at /\ h + hs <= hl /\ off <= capacity-dst_offset /\
  ~is_word_type ty /\ ~is_abi_dynamic ce.ce_struct_fields ty /\ ~is_dynamic at /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\ type_memory_bytes ce ty = type_memory_size tv /\
  eval_operand (Var head) u = SOME (n2w (pbase+dst_offset+h)) /\ ptr_covers Gu tu head u hs /\
  not_fresh_at a head /\ (!x. src = Var x ==> not_fresh_at a x) /\
  expr_val_rel cx ty v src u /\ ptr_val_ok cx ty v src Gu tu u /\ expr_store_bound cx ty v src u /\
  (?first last. expr_val_at ce cx ty first last ee v src u /\
     (shared < first.cs_next_id \/ last.cs_next_id <= shared)) /\
  compile_store_memory ce src (Var head) ty ty a = ((),c) /\ fn_has_code a c func /\ ci_mono a c ==>
  ?z Gz tz.
    (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix c z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot (SUC i) c z Gz tz /\
    R a c u z /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_saved_state_resources >> strip_tac >>
  qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_def]) >>
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ u /\ _`
    (drule_then strip_assume_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u /\
    u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp` by
    (`ctx_has_dalloca ctx ==> allocas_below_fmp u` by
       (drule_then ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
     drule stmt_state_rel_fmp_room >> strip_tac >> strip_tac >>
     fs[fmp_room_def] >> decide_tac) >>
  qpat_x_assum `?first last. expr_val_at _ _ _ _ _ _ _ _ _ /\ _`
    (qx_choosel_then [`first`,`last`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `hl <= off /\ dst_offset+h+hs <= capacity` by decide_tac >>
  `~is_dynamic (vyper_to_abi_type (get_tenv cx) ty)` by
    (qpat_assum `at = vyper_to_abi_type (get_tenv cx) ty`
       (fn th => PURE_REWRITE_TAC [GSYM th]) >> first_assum ACCEPT_TAC) >>
  `type_memory_size tv = static_length at /\ LENGTH (enc at av) = hs` by
    (conj_tac >- metis_tac[abi_caller_static_memory] >>
     fs[abi_encoder_layout_valid_def, abi_member_head_size_def]) >>
  `val_footprint tv v = hs` by
    (drule_all abi_encode_values_static_footprint >>
     fs[abi_member_head_size_def]) >>
  `pbase + capacity <= u.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
  `pbase+dst_offset+h+hs <= u.vs_alloca_next` by decide_tac >>
  qpat_assum `inst.inst_id = shared` (fn th =>
    qpat_assum `FLOOKUP u.vs_allocas shared = SOME (pbase,capacity)`
      (assume_tac o REWRITE_RULE [GSYM th]) >>
    qpat_assum `shared < first.cs_next_id \/ last.cs_next_id <= shared`
      (assume_tac o REWRITE_RULE [GSYM th])) >>
  mp_tac (Q.INST [`H` |-> `hz`,`s` |-> `u`,`G` |-> `Gu`,`tn` |-> `tu`,
    `sa` |-> `first`,`sb` |-> `last`,`x` |-> `root`,`b` |-> `pbase`,
    `n` |-> `capacity`,`d` |-> `pbase+dst_offset+h`,`len` |-> `hs`]
    (horizonTypeLib.at_horizon_named "H" abi_encode_values_memory_source)) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >> metis_tac[]) >>
  disch_then (qx_choose_then `w` strip_assume_tac) >>
  `eval_operand src u = SOME (n2w (w2n w))` by simp[] >>
  qpat_assum `ptr_covers Gu tu head u hs`
    (assume_tac o CONJUNCT1 o REWRITE_RULE [ptr_covers_def]) >>
  `!x. src = Var x \/ Var head = Var x ==> not_fresh_at a x` by
    (gen_tac >> disch_then DISJ_CASES_TAC
     >- (qpat_assum `!x. src = Var x ==> _` (qspec_then `x` irule) >> first_assum ACCEPT_TAC) >>
     qpat_assum `Var head = Var x` (SUBST1_TAC o SYM o REWRITE_RULE [operand_11]) >>
     first_assum ACCEPT_TAC) >>
  `0 < hs ==> w2n w + hs <= u.vs_alloca_next /\
    venomMemDefs$regions_disjoint (w2n w,hs) (pbase+dst_offset+h,hs) /\
    (?p. src = Var p /\ ptr_covers Gu tu p u hs) /\
    (?p. Var head = Var p /\ ptr_covers Gu tu p u hs)` by
    (qpat_assum `val_footprint tv v = hs` (fn th =>
       qpat_assum `0 < val_footprint tv v ==> _` (assume_tac o PURE_REWRITE_RULE [th])) >>
     disch_tac >> qpat_assum `0 < hs ==> _` (drule_then (MAP_EVERY assume_tac o CONJUNCTS)) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> qexists_tac `head` >> asm_rewrite_tac[]) >>
  mp_tac (Q.INST [`env` |-> `get_tenv cx`,`s` |-> `u`,`G` |-> `Gu`,`tn` |-> `tu`,
    `st` |-> `a`,`en` |-> `c`,`dst` |-> `Var head`,
    `d` |-> `pbase+dst_offset+h`,`sb` |-> `w2n (w:bytes32)`,`bs` |-> `enc at av`]
    abi_encode_values_static_store_phase) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY (qpat_assum `!a u. _ ==> R a a u u` irule >> conj_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
    qpat_assum `at = vyper_to_abi_type (get_tenv cx) ty` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
    qpat_assum `LENGTH (enc at av) = hs` (fn th => PURE_REWRITE_TAC [th]) >>
    asm_rewrite_tac[]) >>
  qpat_assum `LENGTH (enc at av) = hs` (fn th =>
    disch_then (qx_choosel_then [`z`,`Gz`,`tz`] (strip_assume_tac o PURE_REWRITE_RULE [th]))) >>
  `(pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix c z Gz tz` by
    (mp_tac (Q.INST [`v` |-> `z`,`Gv` |-> `Gz`,`tv` |-> `tz`,
         `ids` |-> `{}`,`outs` |-> `[(pbase+dst_offset+h,hs)]`] abi_encode_saved_state_phase_pure) >>
      impl_tac >- (simp_tac (srw_ss()) [IN_INSERT, EVERY_DEF] >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY (decide_tac >> NO_TAC) >>
        TRY (qexistsl_tac [`inst`,`root`] >> asm_rewrite_tac[] >> NO_TAC) >>
        qx_gen_tac `j` >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
        qpat_assum `!i. _ ==> (i IN tz.t_mem <=> i IN tu.t_mem)`
          (qspec_then `j` mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >>
        disch_then (irule o iffLR) >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> asm_rewrite_tac[] >>
  mp_tac (Q.INST [`st` |-> `a`,`en` |-> `c`,`s` |-> `u`,`t` |-> `z`,
    `G` |-> `Gu`,`tn` |-> `tu`,`G'` |-> `Gz`,`tn'` |-> `tz`,
    `d` |-> `pbase+dst_offset`,`b` |-> `pbase`,`owner` |-> `shared`]
    abi_encode_values_static_prefix) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >> metis_tac[]) >>
  disch_then ACCEPT_TAC
QED

Theorem abi_encode_saved_store_static_pure:
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  shared <> loc /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i a u Gu tu /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ at = vyper_to_abi_type (get_tenv cx) ty /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  hs = abi_member_head_size at /\ h + hs <= hl /\ off <= capacity-dst_offset /\
  ~is_word_type ty /\ ~is_abi_dynamic ce.ce_struct_fields ty /\ ~is_dynamic at /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\ type_memory_bytes ce ty = type_memory_size tv /\
  eval_operand (Var head) u = SOME (n2w (pbase+dst_offset+h)) /\ ptr_covers Gu tu head u hs /\
  not_fresh_at a head /\ (!x. src = Var x ==> not_fresh_at a x) /\
  expr_val_rel cx ty v src u /\ ptr_val_ok cx ty v src Gu tu u /\ expr_store_bound cx ty v src u /\
  (?first last. expr_val_at ce cx ty first last ee v src u /\
     (shared < first.cs_next_id \/ last.cs_next_id <= shared)) /\
  compile_store_memory ce src (Var head) ty ty a = ((),c) /\ fn_has_code a c func /\ ci_mono a c ==>
  ?z Gz tz.
    (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix c z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot (SUC i) c z Gz tz /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  mp_tac (Q.INST [`R` |-> `\a b u v. T`] abi_encode_saved_store_static_phase) >>
  simp_tac bool_ss [abi_values_source_phase_trivial]
QED

Theorem abi_encode_saved_store_static =
  pureFrameLib.drop_frame abi_encode_saved_store_static_pure

Theorem extcall_direct_store_static:
  extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst selector a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\ 32 <= capacity /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  shared <> loc /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  abi_encode_values_prefix_at ats avs hl (pbase+32) cursor loc slot i a u Gu tu /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ at = vyper_to_abi_type (get_tenv cx) ty /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  hs = abi_member_head_size at /\ h + hs <= hl /\ off <= capacity-32 /\
  ~is_word_type ty /\ ~is_abi_dynamic ce.ce_struct_fields ty /\ ~is_dynamic at /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\ type_memory_bytes ce ty = type_memory_size tv /\
  eval_operand (Var head) u = SOME (n2w (pbase+32+h)) /\ ptr_covers Gu tu head u hs /\
  not_fresh_at a head /\ (!x. src = Var x ==> not_fresh_at a x) /\
  expr_val_rel cx ty v src u /\ ptr_val_ok cx ty v src Gu tu u /\ expr_store_bound cx ty v src u /\
  (?first last. expr_val_at ce cx ty first last ee v src u /\
     (shared < first.cs_next_id \/ last.cs_next_id <= shared)) /\
  compile_store_memory ce src (Var head) ty ty a = ((),c) /\ fn_has_code a c func /\ ci_mono a c ==>
  ?z Gz tz.
    extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst selector c z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+32) cursor loc slot (SUC i) c z Gz tz /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `32 <= capacity` (fn cap =>
    drule_then (fn len =>
      mp_tac (SIMP_RULE bool_ss [MATCH_MP abi_encode_saved_state_extcall len,cap]
        (Q.INST [`dst_offset` |-> `32`,`prefix` |-> `selector`]
          abi_encode_saved_store_static)))
      extcall_direct_state_selector_length) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

Theorem abi_encode_saved_store_dynamic_input_pure:
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  shared <> loc /\
  MEM cursor_inst (fn_insts func) /\ cursor_inst.inst_opcode = ALLOCA /\
  cursor_inst.inst_id = loc /\ cursor_inst.inst_outputs = [cursor_var] /\
  not_local_ptr ce ee.scopes cursor_var /\ se.cs_next_id <= loc /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) (Var cursor) loc slot i a u Gu tu /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ at = vyper_to_abi_type (get_tenv cx) ty /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\
  off + LENGTH (enc at av) <= capacity-dst_offset /\
  ~is_word_type ty /\ is_dynamic at /\
  (!sb. (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
      val_in_memory tv v sb mem) ==>
    abi_encoder_admissible ei /\
    ?ct rv. enc ct rv = enc at av /\
      !mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
        abi_encoder_window_input ei ct rv sb (val_footprint tv v) mem) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\ type_memory_bytes ce ty = type_memory_size tv /\
  eval_operand (Var head) u = SOME (n2w (pbase+dst_offset+h)) /\ ptr_covers Gu tu head u 32 /\
  eval_operand (Var tail) u = SOME (n2w (pbase+dst_offset+off)) /\
  ptr_covers Gu tu tail u (LENGTH (enc at av)) /\
  eval_operand offset u = SOME (n2w off) /\ op_taint tu offset = {} /\
  (!x. src = Var x \/ Var head = Var x \/ Var tail = Var x \/ offset = Var x ==>
    not_fresh_at a x) /\
  expr_val_rel cx ty v src u /\ ptr_val_ok cx ty v src Gu tu u /\ expr_store_bound cx ty v src u /\
  (?first last. expr_val_at ce cx ty first last ee v src u /\ last.cs_next_id <= a.cs_next_id /\
     (shared < first.cs_next_id \/ last.cs_next_id <= shared)) /\
  compile_abi_encode_to_buf (Var tail) src ei a = (len,mid) /\
  abi_encode_child_suffix (Var head) (Var cursor) offset len mid = (len,c) /\
  fn_has_code a mid func /\ fn_has_code mid c func /\ ci_mono a c ==>
  ?z Gz tz.
    (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix c z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) (Var cursor) loc slot (SUC i) c z Gz tz /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_saved_state_resources >> strip_tac >>
  qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_def]) >>
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ u /\ _`
    (drule_then strip_assume_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u /\
    u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp` by
    (`ctx_has_dalloca ctx ==> allocas_below_fmp u` by
       (drule_then ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
     drule stmt_state_rel_fmp_room >> strip_tac >> strip_tac >>
     fs[fmp_room_def] >> decide_tac) >>
  qpat_x_assum `?first last. expr_val_at _ _ _ _ _ _ _ _ _ /\ _`
    (qx_choosel_then [`first`,`last`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `local_ptrs_reserved ce a` by metis_tac[local_ptrs_reserved_next_var] >>
  `pbase <= pbase+dst_offset+off /\ pbase+dst_offset+off+LENGTH (enc at av) <= pbase+capacity` by decide_tac >>
  qpat_assum `inst.inst_id = shared` (fn th =>
    qpat_assum `FLOOKUP u.vs_allocas shared = SOME (pbase,capacity)`
      (assume_tac o REWRITE_RULE [GSYM th]) >>
    qpat_assum `shared < first.cs_next_id \/ last.cs_next_id <= shared`
      (assume_tac o REWRITE_RULE [GSYM th])) >>
  mp_tac (Q.INST [`H` |-> `hz`,`s` |-> `u`,`G` |-> `Gu`,`tn` |-> `tu`,
    `sa` |-> `first`,`sb` |-> `last`,`x` |-> `root`,`b` |-> `pbase`,
    `n` |-> `capacity`,`d` |-> `pbase+dst_offset+off`,`len` |-> `LENGTH (enc at av)`]
    (horizonTypeLib.at_horizon_named "H" abi_encode_values_memory_source)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `w` strip_assume_tac) >>
  qpat_assum `!sb. _ ==> abi_encoder_admissible ei /\ _`
    (qspec_then `w2n (w:bytes32)` (fn th =>
      qpat_assum `!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==> _`
        (fn input => MAP_EVERY assume_tac (CONJUNCTS (MP th input))))) >>
  `eval_operand src u = SOME (n2w (w2n w))` by simp[] >>
  mp_tac (Q.INST [`H` |-> `hz`,`s` |-> `u`,`st` |-> `a`,`en` |-> `mid`,
    `dst` |-> `Var tail`,`out` |-> `len`,`sa` |-> `first`,`sb` |-> `last`,
    `parent` |-> `shared`,`b` |-> `pbase`,`sz` |-> `capacity`,
    `d` |-> `pbase+dst_offset+off`,`n` |-> `LENGTH (enc at av)`,`q` |-> `w2n (w:bytes32)`]
    (horizonTypeLib.at_horizon_named "H" abi_encode_values_scratch_separation)) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  strip_tac >>
  qpat_assum `ptr_covers Gu tu tail u (LENGTH (enc at av))`
    (assume_tac o CONJUNCT1 o REWRITE_RULE [ptr_covers_def]) >>
  `!x. src = Var x \/ Var tail = Var x \/ Var head = Var x \/ offset = Var x ==>
    not_fresh_at a x` by
    (gen_tac >> qpat_assum `!x. src = Var x \/ Var head = Var x \/ _ ==> _`
       (qspec_then `x` mp_tac) >> tautLib.TAUT_TAC) >>
  mp_tac (Q.INST [`s` |-> `u`,`G` |-> `Gu`,`tn` |-> `tu`,
    `st` |-> `a`,`en` |-> `c`,`dest` |-> `tail`,`owner` |-> `shared`,
    `cursor_var` |-> `cursor`,
    `b` |-> `pbase`,`d` |-> `pbase+dst_offset`,`sb` |-> `w2n (w:bytes32)`,
    `cap` |-> `val_footprint tv v`,`bs` |-> `enc at av`]
    abi_encode_values_dynamic_prefix_input) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY (simp_tac (srw_ss()) [ptr_covers_def]) >> TRY decide_tac >> metis_tac[]) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] strip_assume_tac) >>
  qabbrev_tac `sites = loc INSERT window_alloca_sites func (frag_ids a mid)` >>
  `!aid. aid IN window_alloca_sites func (frag_ids a mid) ==> a.cs_next_id <= aid` by
    simp[NoAsms, window_alloca_sites_def, frag_ids_def] >>
  `shared NOTIN window_alloca_sites func (frag_ids a mid)` by
    (strip_tac >> qpat_assum `!aid. aid IN window_alloca_sites func (frag_ids a mid) ==> _`
      (qspec_then `shared` (drule_then assume_tac)) >> decide_tac) >>
  `shared NOTIN sites` by asm_simp_tac bool_ss [Abbr `sites`, IN_INSERT] >>
  `!aid. aid IN sites ==> se.cs_next_id <= aid` by
    (simp_tac (srw_ss()) [Abbr `sites`, IN_INSERT] >> rpt strip_tac >>
     TRY (decide_tac >> NO_TAC) >>
     qpat_assum `!aid. aid IN window_alloca_sites func (frag_ids a mid) ==> _`
       (qspec_then `aid` (drule_then assume_tac)) >> decide_tac) >>
  `!aid. aid IN shared INSERT sites ==>
    ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x` by
    (simp_tac (srw_ss()) [Abbr `sites`, IN_INSERT, window_alloca_sites_def] >>
     gen_tac >> strip_tac
     >- (qexistsl_tac [`inst`,`root`] >> asm_rewrite_tac[])
     >- (qexistsl_tac [`cursor_inst`,`cursor_var`] >> asm_rewrite_tac[]) >>
     rename1 `scratch.inst_id = aid` >>
     mp_tac (Q.INST [`ready` |-> `a`,`body_end` |-> `mid`,`earlier` |-> `a`,
       `obs` |-> `func`,`i` |-> `scratch`,`scopes` |-> `ee.scopes`,
       `dst` |-> `Var tail`,`out` |-> `len`]
       (SPEC_ALL abi_encode_compiled_scratch_site)) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       TRY (qpat_assum `scratch.inst_id = aid` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
       simp[NoAsms]) >>
     strip_tac >> qexistsl_tac [`scratch`,`q`] >> asm_rewrite_tac[]) >>
  qunabbrev_tac `sites` >>
  `abi_member_head_size at = 32` by
    (qpat_assum `is_dynamic at` (fn th => simp_tac bool_ss [abi_member_head_size_def,th])) >>
  `(pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix c z Gz tz` by
    (mp_tac (Q.INST [`v` |-> `z`,`Gv` |-> `Gz`,`tv` |-> `tz`,
        `ids` |-> `loc INSERT window_alloca_sites func (frag_ids a mid)`,
        `outs` |-> `[(pbase+dst_offset+h,32);(pbase+dst_offset+off,LENGTH (enc at av))]`] abi_encode_saved_state_phase_pure) >>
      impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        simp_tac (srw_ss()) [EVERY_DEF] >> rpt conj_tac >> TRY (decide_tac >> NO_TAC) >>
        qx_gen_tac `j` >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
        qpat_assum `!i. _ /\ _ /\ _ ==> (i IN tz.t_mem <=> i IN tu.t_mem)` (qspec_then `j` mp_tac) >>
        impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          PURE_REWRITE_TAC [IN_INSERT] >> first_assum ACCEPT_TAC) >>
        disch_then (irule o iffLR) >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> asm_rewrite_tac[]
QED

Theorem abi_encode_saved_store_dynamic_pure:
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  shared <> loc /\
  MEM cursor_inst (fn_insts func) /\ cursor_inst.inst_opcode = ALLOCA /\
  cursor_inst.inst_id = loc /\ cursor_inst.inst_outputs = [cursor_var] /\
  not_local_ptr ce ee.scopes cursor_var /\ se.cs_next_id <= loc /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) (Var cursor) loc slot i a u Gu tu /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ at = vyper_to_abi_type (get_tenv cx) ty /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\
  off + LENGTH (enc at av) <= capacity-dst_offset /\
  ~is_word_type ty /\ is_dynamic at /\
  abi_enc_plan (get_tenv cx) ty ei /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\ type_memory_bytes ce ty = type_memory_size tv /\
  eval_operand (Var head) u = SOME (n2w (pbase+dst_offset+h)) /\ ptr_covers Gu tu head u 32 /\
  eval_operand (Var tail) u = SOME (n2w (pbase+dst_offset+off)) /\
  ptr_covers Gu tu tail u (LENGTH (enc at av)) /\
  eval_operand offset u = SOME (n2w off) /\ op_taint tu offset = {} /\
  (!x. src = Var x \/ Var head = Var x \/ Var tail = Var x \/ offset = Var x ==>
    not_fresh_at a x) /\
  expr_val_rel cx ty v src u /\ ptr_val_ok cx ty v src Gu tu u /\ expr_store_bound cx ty v src u /\
  (?first last. expr_val_at ce cx ty first last ee v src u /\ last.cs_next_id <= a.cs_next_id /\
     (shared < first.cs_next_id \/ last.cs_next_id <= shared)) /\
  compile_abi_encode_to_buf (Var tail) src ei a = (len,mid) /\
  abi_encode_child_suffix (Var head) (Var cursor) offset len mid = (len,c) /\
  fn_has_code a mid func /\ fn_has_code mid c func /\ ci_mono a c ==>
  ?z Gz tz.
    (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix c z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) (Var cursor) loc slot (SUC i) c z Gz tz /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac abi_encode_saved_store_dynamic_input_pure >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     gen_tac >> disch_tac >>
     qpat_assum `at = vyper_to_abi_type (get_tenv cx) ty`
       (fn th => PURE_REWRITE_TAC [th]) >>
     drule_all abi_encode_values_plan_window_input >> disch_then ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

Theorem abi_encode_saved_store_dynamic =
  pureFrameLib.drop_frame abi_encode_saved_store_dynamic_pure

Theorem extcall_direct_store_dynamic:
  extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst selector a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\ 32 <= capacity /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  shared <> loc /\
  MEM cursor_inst (fn_insts func) /\ cursor_inst.inst_opcode = ALLOCA /\
  cursor_inst.inst_id = loc /\ cursor_inst.inst_outputs = [cursor_var] /\
  not_local_ptr ce ee.scopes cursor_var /\ se.cs_next_id <= loc /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  abi_encode_values_prefix_at ats avs hl (pbase+32) (Var cursor) loc slot i a u Gu tu /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ at = vyper_to_abi_type (get_tenv cx) ty /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\
  off + LENGTH (enc at av) <= capacity-32 /\
  ~is_word_type ty /\ is_dynamic at /\
  abi_enc_plan (get_tenv cx) ty ei /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\ type_memory_bytes ce ty = type_memory_size tv /\
  eval_operand (Var head) u = SOME (n2w (pbase+32+h)) /\ ptr_covers Gu tu head u 32 /\
  eval_operand (Var tail) u = SOME (n2w (pbase+32+off)) /\
  ptr_covers Gu tu tail u (LENGTH (enc at av)) /\
  eval_operand offset u = SOME (n2w off) /\ op_taint tu offset = {} /\
  (!x. src = Var x \/ Var head = Var x \/ Var tail = Var x \/ offset = Var x ==>
    not_fresh_at a x) /\
  expr_val_rel cx ty v src u /\ ptr_val_ok cx ty v src Gu tu u /\ expr_store_bound cx ty v src u /\
  (?first last. expr_val_at ce cx ty first last ee v src u /\ last.cs_next_id <= a.cs_next_id /\
     (shared < first.cs_next_id \/ last.cs_next_id <= shared)) /\
  compile_abi_encode_to_buf (Var tail) src ei a = (len,mid) /\
  abi_encode_child_suffix (Var head) (Var cursor) offset len mid = (len,c) /\
  fn_has_code a mid func /\ fn_has_code mid c func /\ ci_mono a c ==>
  ?z Gz tz.
    extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst selector c z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+32) (Var cursor) loc slot (SUC i) c z Gz tz /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `32 <= capacity` (fn cap =>
    drule_then (fn len =>
      mp_tac (SIMP_RULE bool_ss [MATCH_MP abi_encode_saved_state_extcall len,cap]
        (Q.INST [`dst_offset` |-> `32`,`prefix` |-> `selector`]
          abi_encode_saved_store_dynamic)))
      extcall_direct_state_selector_length) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED
