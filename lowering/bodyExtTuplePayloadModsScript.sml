(* Run the ABI cursor fold on the linked physical endpoint. The row inputs
   describe the saved observations at the original pre-allocation state. *)
Theory bodyExtTuplePayloadMods
Ancestors
  bodyExtPackingEntryMods bodyExtPackingCursorFrameMods bodyExtPackingEndpointMods
  fragExec compileEnv
  bodyExtStaticRowStepMods bodyExtDynamicRowStepMods
  abiEncodeValuesRun abiEncodeValuesMetadata abiEncodeValuesCode
  bodyFullExtCallDirectWindows exprSimAbiEncodePlanMetadata
  bodyFullHashKeccakFixed fragGasOriginPtrLoop stateRelProj
  context emitHelperProps exprLoweringProps abiEncoderWindowContract
  bodyFullShadowBodyInv loweringPosts bodyPtrDefs
  venomState venomInst finite_map pred_set list pair arithmetic words

Triviality packing_resources:
  ext_packing_endpoint_mods ctx func ce cx st0 ee DF lo ret front s G tn
    owner b capacity root dst selector a u Gu tu ==>
  alloca_inv u /\ alloca_room ctx func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next /\
  ~u.vs_halted /\ u.vs_current_bb = a.cs_current_bb /\
  u.vs_inst_idx = LENGTH a.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u /\
    u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp)
Proof
  pure_rewrite_tac[ext_packing_endpoint_mods_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_then assume_tac stmt_state_rel_alloca_room >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  drule_then (assume_tac o REWRITE_RULE[fmp_room_def]) stmt_state_rel_fmp_room >>
  qhdtm_assum `ghost_inv_at_mods` (assume_tac o REWRITE_RULE[ghost_inv_at_mods_def]) >>
  asm_rewrite_tac[] >> disch_tac >> fs[] >> decide_tac
QED

Triviality payload_cursor_site:
  compile_abi_encode_values_to_buf ce dst rows st = (out,en) /\
  fn_has_code st en func /\ local_ptrs_reserved ce st ==>
  ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = st.cs_next_id /\ inst.inst_outputs = [x] /\
    not_local_ptr ce scopes x
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (qx_choosel_then [`cursor`,`allocated`,`ready`,`stored`]
    (map_every assume_tac o CONJUNCTS)) abi_encode_values_to_buf_trace >>
  `ci_mono allocated ready /\ ci_mono ready stored /\ ci_mono stored en` by
    (rpt conj_tac >>
     metis_tac[ci_mono_emit_op,ci_mono_emit_void,ci_mono_compile_abi_encode_value_rows,SND]) >>
  `ci_mono allocated en` by metis_tac[ci_mono_trans] >>
  `ci_mono st allocated` by metis_tac[ci_mono_emit_op,SND] >>
  `fn_has_code st allocated func` by
    (mp_tac (Q.SPECL [`st`,`allocated`,`en`,`func`] fn_has_code_split) >> fs[ci_mono_def]) >>
  `st.cs_next_var <= st.cs_next_var` by simp[] >>
  drule_all extcall_direct_alloca_site >>
  disch_then (qspec_then `scopes` (qx_choosel_then [`op`,`x`] strip_assume_tac)) >>
  qexistsl [`op`,`x`] >> asm_rewrite_tac[]
QED

val initial_horizons = ``!H. valid_horizon cx st0 H ee.storage_trace ==>
  stmt_state_rel H ctx func ce cx ee s /\
  storage_well_formed_on cx ee (FST H) /\
  ghost_inv_at_mods (DF H) lo ret ce cx ee G tn s /\
  immutable_frame_mods func ce cx ee s``;
val indexed_inputs = ``!i. i < LENGTH rows ==>
  ?e saved ty v tv. EL i rows = (saved,ty) /\ ty = lowered_value_type ce e /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64 /\
    EL i ats = vyper_to_abi_type (get_tenv cx) ty /\
    vyper_to_abi (get_tenv cx) ty v = SOME (EL i avs) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      ext_pos_saved_row_mods lo ce cx kw_es pos sa H e saved v ee G tn s)``;

Theorem ext_tuple_payload_mods:
  compile_alloc_buffer n sa = (shared,sb) /\
  emit_void MSTORE [shared.buf_operand;Lit (calldata_method_id bs)] sb = ((),sc) /\
  emit_op ADD [shared.buf_operand;Lit 32w] sc = (dst,sd) /\
  compile_abi_encode_values_to_buf ce dst rows sd = (out,en) /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\
  fn_has_code sc sd func /\ fn_has_code sd en func /\ fn_inst_ids_distinct func /\
  LENGTH bs = 4 /\ 32 <= n /\ n < dimword (:256) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\ ^initial_horizons /\
  storage_trace_domain cx st0 ee.storage_trace /\
  local_ptrs_reserved ce sa /\ return_buf_frame ret ce sa s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!typ rt. evaluate_type (get_tenv cx) typ = SOME rt ==>
    type_memory_bytes ce typ = type_memory_size rt) /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
    abi_member_head_size at) rows ats /\ LIST_REL abi_encoder_layout_valid ats avs /\
  bytes = enc (Tuple ats) (ListV avs) /\ LENGTH bytes <= n-32 /\
  ^indexed_inputs ==>
  ?root dp b z Gz tz.
    shared.buf_operand = Var root /\ dst = Var dp /\
    ext_packing_endpoint_mods ctx func ce cx st0 ee DF lo ret sa s G tn
      sa.cs_next_id b n root dp bs en z Gz tz /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]) (fn_insts func) /\
    lo <= b /\ b+n < dimword (:256) /\
    eval_operand out z = SOME (n2w (LENGTH bytes)) /\ op_taint tz out = {} /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    mem_bytes_at (b+32) (LENGTH bytes) z.vs_memory = bytes /\
    (!j. b+32 <= j /\ j < b+32+LENGTH bytes ==> j NOTIN tz.t_mem) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac ext_packing_entry_mods >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`root`,`dp`,`b`,`u`,`Gu`,`tu`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `dst = Var dp` SUBST_ALL_TAC >>
  qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `hz` assume_tac) >>
  qpat_assum `^initial_horizons` (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qhdtm_assum `ext_packing_endpoint_mods` (fn th =>
    let val facts = REWRITE_RULE[ext_packing_endpoint_mods_def] th
    in map_every (assume_tac o (fn i => cj i facts)) [8,10,11] end) >>
  suspend "sites"
QED

Resume ext_tuple_payload_mods[sites]:
  `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [root] /\
    not_local_ptr ce ee.scopes root` by
    (`emit_op ALLOCA [Lit (n2w n)] sa = (shared.buf_operand,sb)` by
       (qhdtm_assum `compile_alloc_buffer` mp_tac >>
        qpat_assum `shared.buf_operand = Var root` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        Cases_on `emit_op ALLOCA [Lit (n2w n)] sa` >>
        simp[compile_alloc_buffer_def,comp_bind_def,comp_return_def] >>
        strip_tac >> strip_tac >>
        qpat_assum `<|buf_operand := q; buf_size := n|> = shared`
          (mp_tac o Q.AP_TERM `\bb. bb.buf_operand`) >> simp[]) >>
     `sa.cs_next_var <= sa.cs_next_var` by simp[] >>
     drule_all extcall_direct_alloca_site >> disch_then (qspec_then `ee.scopes` mp_tac) >>
     disch_then (qx_choosel_then [`op`,`x`] strip_assume_tac) >>
     `Var x = Var root` by metis_tac[] >>
     `x = root` by (qpat_assum `Var x = Var root` mp_tac >> simp[]) >>
     qpat_x_assum `x = root` SUBST_ALL_TAC >>
     qexists `op` >> asm_rewrite_tac[]) >>
  rename1 `inst.inst_id = sa.cs_next_id` >>
  `?cu croot. MEM cu (fn_insts func) /\ cu.inst_opcode = ALLOCA /\
    cu.inst_id = sd.cs_next_id /\ cu.inst_outputs = [croot] /\
    not_local_ptr ce ee.scopes croot` by
    (drule_all payload_cursor_site >> simp[]) >>
  rename1 `cu.inst_id = sd.cs_next_id` >>
  rename1 `cu.inst_outputs = [croot]` >>
  qabbrev_tac `hl = head_lengths ats 0` >>
  `hl = head_lengths ats 0` by simp[Abbr `hl`] >>
  mp_tac (Q.INST
    [`st` |-> `sd`, `dst` |-> `Var dp`, `s` |-> `u`, `G` |-> `Gu`, `tn` |-> `tu`,
     `owner` |-> `sa.cs_next_id`, `cap` |-> `n`, `d` |-> `b+32`,
     `P` |-> `\a w Gw tw. ext_packing_endpoint_mods ctx func ce cx st0 ee DF lo ret
       sa s G tn sa.cs_next_id b n root dp bs a w Gw tw`]
    abi_encode_values_execute |> BETA_RULE) >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
    >- (rpt gen_tac >> disch_tac >> drule_then ACCEPT_TAC packing_resources)
    >- suspend "cursor_frame"
    >> suspend "row") >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`root`,`dp`,`b`,`z`,`Gz`,`tz`] >> asm_rewrite_tac[] >>
  gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl [`Gu`,`u`,`tu`] >> simp[]
QED

Resume ext_tuple_payload_mods[cursor_frame]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule ext_packing_cursor_frame_mods >>
  qhdtm_assum `window_phase` (irule_at Any) >>
  qpat_assum `compile_abi_encode_values_to_buf _ _ _ sd = _` (irule_at Any) >>
  qpat_assum `stmt_state_rel hz _ _ _ _ _ s` (irule_at Any) >>
  qpat_assum `ext_packing_endpoint_mods ctx func ce cx st0 ee DF lo ret
    sa s G tn sa.cs_next_id b n root dp bs a _ _ _` (irule_at Any) >>
  qexistsl [`inst`,`explicit`,`PG`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume ext_tuple_payload_mods[row]:
  map_every qx_gen_tac [`i`,`a`,`c`,`w`,`Gw`,`tw`,`cursor`,`slot`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `^indexed_inputs` (qspec_then `i` (drule_then
    (qx_choosel_then [`e`,`saved`,`ty`,`v`,`tv`] (map_every assume_tac o CONJUNCTS)))) >>
  qabbrev_tac `h = SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows))` >>
  qabbrev_tac `at = EL i ats` >> qabbrev_tac `av = EL i avs` >>
  qabbrev_tac `off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs)))` >>
  `at = vyper_to_abi_type (get_tenv cx) ty /\ vyper_to_abi (get_tenv cx) ty v = SOME av` by
    simp[Abbr `at`,Abbr `av`] >>
  `compile_abi_encode_value_rows ce (Var dp) cursor h [(saved,ty)] a = ((),c)` by
    (qpat_assum `EL i rows = (saved,ty)` (fn th => pure_rewrite_tac[GSYM th]) >>
     simp_tac bool_ss [Abbr `h`] >> first_assum ACCEPT_TAC) >>
  `LENGTH rows = LENGTH ats /\ LENGTH ats = LENGTH avs` by
    metis_tac[LIST_REL_LENGTH] >>
  `i < LENGTH ats` by decide_tac >>
  `h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
   hl <= off /\ off <= LENGTH bytes /\ h + abi_member_head_size at <= hl /\
   (is_dynamic at ==> off + LENGTH (enc at av) <= LENGTH bytes) /\
   (~is_dynamic at ==> LENGTH (enc at av) = abi_member_head_size at) /\
   abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs)` by
    (irule (INST_TYPE [alpha |-> ``:vyper_value``, beta |-> ``:string``, gamma |-> ``:num``]
       abi_encode_values_index_bounds) >>
     qpat_assum `LIST_REL _ rows ats` (irule_at Any) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     TRY (simp[NoAsms,Abbr `at`,Abbr `av`,Abbr `h`,Abbr `off`] >> NO_TAC) >>
     qpat_assum `bytes = enc _ _` (fn th => simp[NoAsms,th])) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    ext_pos_saved_row_mods lo ce cx kw_es pos sa H e saved v ee G tn s /\
    stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo ret ce cx ee G tn s` by
    (gen_tac >> disch_tac >>
     qpat_assum `^initial_horizons` (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> ext_pos_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (drule_then assume_tac) >> asm_rewrite_tac[]) >>
  Cases_on `is_dynamic at`
  >- suspend "dynamic" >> suspend "static"
QED

Resume ext_tuple_payload_mods[dynamic]:
  qhdtm_assum `abi_encode_values_prefix_at`
    (qx_choose_then `cursor_var` (assume_tac o cj 1) o cj 1 o
     REWRITE_RULE[abi_encode_values_prefix_at_def]) >>
  qpat_x_assum `cursor = Var cursor_var` SUBST_ALL_TAC >>
  `is_abi_dynamic ce.ce_struct_fields ty` by
    (drule_all abi_encode_translated_dynamic >>
     qpat_assum `at = vyper_to_abi_type _ _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  `abi_member_head_size at = 32` by
    simp[abiDecodeRangesTheory.abi_member_head_size_def] >>
  `h+32 <= hl` by decide_tac >>
  `off+LENGTH (enc at av) <= n-32` by
    (qpat_assum `is_dynamic at ==> _` (drule_then assume_tac) >> decide_tac) >>
  irule ext_dynamic_row_step_mods >>
  qpat_assum `compile_abi_encode_value_rows _ _ _ h [(saved,ty)] a = _` (irule_at Any) >>
  qpat_assum `abi_encode_values_prefix_at _ _ _ _ _ _ _ i a w Gw tw` (irule_at Any) >>
  qexistsl [`v`,`tv`,`pos`,`off`,`kw_es`,`inst`,`e`,`cu`,`croot`,`enc at av`,`av`,`at`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  simp[NoAsms,Abbr `at`,Abbr `av`,Abbr `off`]
QED

Resume ext_tuple_payload_mods[static]:
  `b+32+hl+LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) <= b+n` by
    (`off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs)))` by
       simp[NoAsms,Abbr `off`] >> decide_tac) >>
  irule ext_static_row_step_mods >>
  qpat_assum `compile_abi_encode_value_rows _ _ _ h [(saved,ty)] a = _` (irule_at Any) >>
  qpat_assum `abi_encode_values_prefix_at _ _ _ _ _ _ _ i a w Gw tw` (irule_at Any) >>
  qexistsl [`v`,`tv`,`pos`,`kw_es`,`inst`,`abi_member_head_size at`,
    `e`,`croot`,`cu`,`av`,`at`,`hz`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (simp[NoAsms,Abbr `at`,Abbr `av`] >> NO_TAC) >>
  qpat_assum `at = vyper_to_abi_type _ _` (fn th => rewrite_tac[GSYM th]) >>
  first_assum ACCEPT_TAC
QED

Finalise ext_tuple_payload_mods
