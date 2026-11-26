(* Execute one saved word at the reached ABI tuple head cut. *)
Theory bodyAbiTupleWordRowMods
Ancestors
  bodyAbiEncodePackedPostMods bodyAbiTupleBufferStateMods
  bodyAbiTupleBufferResourcesMods bodyAbiTupleBufferPhaseMods
  bodyFullExtCallDirectWord abiEncodeValuesWordRow abiEncodeValuesCode
  exprSimAbiEncodePlanMetadata entryDecodeStaticProps allocaSiteResource
  bodyFullPostsMods bodyPtrDefs loweringPosts loweringStateRelDefs
  exprLoweringProps compileEnv pred_set list arithmetic pair

Theorem abi_tuple_saved_word_source_mods[local]:
  abi_encode_saved_row_mods lo ce cx sa se e saved v si sm ss vv copy H ee G tn s /\
  ty = lowered_value_type ce e /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  (!l. vv_operand saved <> Label l) /\ se.cs_next_var <= a.cs_next_var /\
  wb_frame ce ee ee se s u /\ ghost_kept_at lo ce ee se G tn s Gu tu ==>
  ?tag src. saved = StackValue tag src /\
    eval_operand src u = SOME (typed_val_to_w256 tv v) /\ op_taint tu src = {} /\
    (!x. src = Var x ==> not_fresh_at a x)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `abi_encode_saved_row_mods`
    (MAP_EVERY assume_tac o CONJUNCTS o REWRITE_RULE[abi_encode_saved_row_mods_def]) >>
  qpat_x_assum `ty = lowered_value_type ce e` SUBST_ALL_TAC >>
  `?tag src. saved = StackValue tag src` by metis_tac[] >>
  qpat_x_assum `saved = StackValue tag src` SUBST_ALL_TAC >>
  qpat_x_assum `?raw. read_result cx raw ee = _ /\ _`
    (qx_choose_then `raw` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexistsl [`tag`,`src`] >> simp[] >>
  qhdtm_x_assum `vv_holds_mods` (assume_tac o SIMP_RULE (srw_ss()) [vv_holds_mods_def]) >>
  irule extcall_direct_word_source >>
  qpat_assum `compile_expr _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `compile_snapshot_vv _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `read_result _ _ _ = _` (irule_at Any) >>
  qpat_assum `wb_frame _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qexists `tag` >> asm_rewrite_tac[]
QED

(* Only the 32-byte reached head window is written; no new allocation
   site is used by the word row. Lift that phase before hiding its endpoint. *)
Theorem abi_tuple_word_phase_mods[local]:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  h + 32 <= capacity - dst_offset /\ dst_offset <= capacity /\
  ci_mono a c /\ window_phase ctx func a c {} [(pbase + dst_offset + h,32)] u z /\
  abi_encode_exec_frame func u z /\
  (!x. not_fresh_at a x ==>
    FLOOKUP Gz x = FLOOKUP Gu x /\ op_taint tz (Var x) = op_taint tu (Var x)) /\
  tz.t_mem SUBSET tu.t_mem /\ tz.t_stor = tu.t_stor /\ tz.t_trans = tu.t_trans /\
  tz.t_imm = tu.t_imm /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)) ==>
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix c z Gz tz /\
  abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset loc
    a u Gu tu c z Gz tz
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  irule abi_tuple_buffer_phase_mods >>
  qhdtm_assum `abi_tuple_buffer_state_mods` (irule_at Any) >>
  qhdtm_assum `window_phase` (irule_at Any) >>
  qexistsl [`explicit`,`PG`] >> asm_simp_tac (srw_ss()) [] >>
  qpat_x_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  qexists `hz` >> asm_rewrite_tac[] >>
  conj_tac >- fs[SUBSET_DEF] >>
  conj_tac >- (qexistsl [`inst`,`root`] >> simp[]) >>
  decide_tac
QED

Theorem abi_tuple_word_row_mods:
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx sa se e saved v si sm ss vv copy H ee G tn s /\
    stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  shared <> loc /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  compile_abi_encode_value_rows ce (Var dst) cursor h [(saved,ty)] a = ((),c) /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i a u Gu tu /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ at = vyper_to_abi_type (get_tenv cx) ty /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\ off <= capacity-dst_offset /\
  ty = lowered_value_type ce e /\ is_word_type ty /\ (!l. vv_operand saved <> Label l) /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\ type_memory_bytes ce ty = type_memory_size tv /\
  fn_has_code a c func ==>
  ?z Gz tz.
    abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix c z Gz tz /\
    abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset loc
      a u Gu tu c z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot (SUC i) c z Gz tz /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac abi_tuple_buffer_resources_mods >>
  qhdtm_assum `abi_tuple_buffer_state_mods`
    (strip_assume_tac o REWRITE_RULE[abi_tuple_buffer_state_mods_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s` by
    (rpt strip_tac >>
     qpat_assum `!H. _ ==> abi_encode_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace` strip_assume_tac >>
  qpat_assum `!H. _ ==> abi_encode_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac abi_tuple_saved_word_source_mods >>
  `abi_member_head_size at = 32` by
    (drule_then (qspecl_then [`ce.ce_struct_fields`,`ce`] strip_assume_tac)
       entryDecodeStaticPropsTheory.word_type_dec_sizes >>
     drule_all_then assume_tac abi_encode_translated_head >> metis_tac[]) >>
  `h+32 <= hl /\ h+32 <= capacity-dst_offset /\
   pbase <= pbase+dst_offset /\ pbase+dst_offset+(capacity-dst_offset) <= pbase+capacity` by decide_tac >>
  drule_all_then assume_tac alloca_site_registered_below >>
  `ci_mono a c` by metis_tac[ci_mono_compile_abi_encode_value_rows, SND] >>
  qpat_x_assum `saved = StackValue _ _` SUBST_ALL_TAC >>
  suspend "execute"
QED

Resume abi_tuple_word_row_mods[execute]:
  qpat_assum `compile_abi_encode_value_rows _ _ _ _ _ _ = _`
    (mp_then (Pos hd) mp_tac abi_encode_values_word_prefix) >>
  disch_then (fn th => qhdtm_assum `abi_encode_values_prefix_at`
    (mp_then (Pos hd) (mp_tac o Q.INST [`env` |-> `get_tenv cx`, `b` |-> `pbase`,
       `cap` |-> `capacity-dst_offset`, `owner` |-> `shared`] o SPEC_ALL) th)) >>
  impl_tac >- (asm_rewrite_tac[] >> conj_tac
    >- (qpat_assum `at = EL i ats` mp_tac >> simp[]) >>
    strip_tac >> qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u /\ _`
      (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] strip_assume_tac) >>
  qexistsl [`z`,`Gz`,`tz`] >> asm_rewrite_tac[] >>
  irule abi_tuple_word_phase_mods >>
  qhdtm_assum `abi_tuple_buffer_state_mods` (irule_at Any) >>
  qhdtm_assum `window_phase` (irule_at Any) >>
  qexistsl [`inst`,`explicit`,`PG`,`H`] >> asm_rewrite_tac[]
QED

Finalise abi_tuple_word_row_mods
