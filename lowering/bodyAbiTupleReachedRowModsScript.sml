(* Generic reached ABI tuple row, using one selected unwrap endpoint. *)
Theory bodyAbiTupleReachedRowMods
Ancestors
  bodyAbiTupleWordRowMods bodyAbiTupleStaticRowMods bodyAbiTupleDynamicRowMods
  bodyAbiTupleSelectedUnwrapMods bodyAbiTupleDynamicRestoreInputMods
  bodyAbiTupleBufferStateMods
  exprSimAbiEncodePlanMetadata decoderGhostFramePtr
  bodyFullPostsMods loweringPosts loweringStateRelDefs compileEnv vyperContext contractABI
  exprLoweringProps exprSimMemDefs venomState venomInst venomMemDefs
  finite_map pred_set list arithmetic pair
Libs horizonTypeLib

Theorem abi_tuple_reached_row_mods:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM owner (fn_insts func) /\ owner.inst_opcode = ALLOCA /\
  owner.inst_id = shared /\ owner.inst_outputs = [root] /\
  not_local_ptr ce ee.scopes root /\
  shared < loc /\
  MEM cursor_inst (fn_insts func) /\ cursor_inst.inst_opcode = ALLOCA /\
  cursor_inst.inst_id = loc /\ cursor_inst.inst_outputs = [cursor_var] /\
  not_local_ptr ce ee.scopes cursor_var /\ cursor = Var cursor_var /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i a u Gu tu /\
  compile_abi_encode_value_rows ce (Var dst) cursor h [(saved,ty)] a = ((),c) /\
  fn_has_code a c func /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\
  at = vyper_to_abi_type (get_tenv cx) ty /\
  abi_encoder_layout_valid at av /\
  LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\ off <= capacity-dst_offset /\
  ty = lowered_value_type ce e /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!l. vv_operand saved <> Label l) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < 2**64 /\
  (~is_word_type ty /\ is_dynamic at ==>
    off + LENGTH (enc at av) <= capacity-dst_offset) /\
  (~is_word_type ty /\ is_dynamic at ==>
    ?E0. get_tenv cx SUBMAP E0 /\ sfields_tenv_consistent ce.ce_struct_fields E0 /\
      (!t rt. evaluate_type E0 t = SOME rt ==> type_memory_bytes ce t = type_memory_size rt)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx sa se e saved v si sm ss vv copy H ee G tn s) /\
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
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      abi_encode_saved_row_mods lo ce cx sa se e saved v si sm ss vv copy H ee G tn s /\
      stmt_state_rel H ctx func ce cx ee s` by
    (gen_tac >> disch_tac >> conj_tac
     >- (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
         (drule_then ACCEPT_TAC))
     >- (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
         (drule_then ACCEPT_TAC))) >>
  `shared <> loc` by decide_tac >>
  Cases_on `is_word_type ty`
  >- (irule abi_tuple_word_row_mods >>
      rpt conj_tac >> metis_tac[]) >>
  qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `hz` assume_tac) >>
  `!b r src u1 G1 t1.
    unwrap_value ce saved b = (src,r) /\ fn_has_code b r func /\ ci_mono b r /\
    abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix b u1 G1 t1 /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i b u1 G1 t1 ==>
    ?z Gz tz first last.
      abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
        shared pbase capacity root dst dst_offset prefix r z Gz tz /\
      abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset loc b u1 G1 t1 r z Gz tz /\
      abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i r z Gz tz /\
      expr_val_at ce cx ty first last ee v src z /\
      expr_val_rel cx ty v src z /\ ptr_val_ok cx ty v src Gz tz z /\
      expr_store_bound cx ty v src z /\ (!x. src = Var x ==> not_fresh_at r x) /\
      (shared < first.cs_next_id \/ last.cs_next_id <= shared) /\ last.cs_next_id <= r.cs_next_id /\
      !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u1,G1,t1) [] (OK z,Gz,tz)` by
    suspend "unwrap_rule" >>
  Cases_on `is_dynamic at`
  >- suspend "dynamic" >>
  suspend "static"
QED

Resume abi_tuple_reached_row_mods[static]:
  `~is_abi_dynamic ce.ce_struct_fields ty` by
    (qpat_assum `at = vyper_to_abi_type _ _` (fn eq =>
       drule_all_then (SUBST1_TAC o ONCE_REWRITE_RULE [GSYM eq])
         abi_encode_translated_dynamic) >> asm_rewrite_tac[]) >>
  irule abi_tuple_static_row_mods >>
  qpat_assum `evaluate_type _ ty = SOME tv` (irule_at Any) >>
  qpat_assum `vyper_to_abi _ ty v = SOME av` (irule_at Any) >>
  qpat_assum `ty = lowered_value_type ce e` (irule_at Any) >>
  qpat_assum `owner.inst_id = shared` (irule_at Any) >>
  qpat_assum `h = LENGTH _` (irule_at Any) >>
  qpat_assum `off = hl + LENGTH _` (irule_at Any) >>
  qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `hz` assume_tac) >>
  qexistsl [`vv`,`ss`,`sm`,`si`,`saved`,`sa`,`copy`,`at`,`hz`] >>
  asm_rewrite_tac[] >>
  suspend "static_callback"
QED

Resume abi_tuple_reached_row_mods[dynamic]:
  `off + LENGTH (enc at av) <= capacity-dst_offset` by
    (qpat_assum `_ ==> off + LENGTH (enc at av) <= _` irule >> asm_rewrite_tac[]) >>
  qpat_x_assum `cursor = Var cursor_var` SUBST_ALL_TAC >>
  irule abi_tuple_dynamic_row_mods >>
  qpat_assum `compile_abi_encode_value_rows _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `owner.inst_id = shared` (irule_at Any) >>
  qpat_assum `cursor_inst.inst_id = loc` (irule_at Any) >>
  qpat_assum `evaluate_type _ ty = SOME tv` (irule_at Any) >>
  qpat_assum `at = vyper_to_abi_type _ ty` (irule_at Any) >>
  qpat_assum `off = hl + LENGTH _` (irule_at Any) >>
  qexistsl [`v`,`av`,`hz`] >>
  asm_rewrite_tac[] >>
  suspend "dynamic_callback"
QED

Resume abi_tuple_reached_row_mods[unwrap_rule]:
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) <= capacity-dst_offset /\
    hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) <= capacity-dst_offset` by
    decide_tac >>
  irule abi_tuple_selected_unwrap_mods >>
  qpat_assum `evaluate_type _ ty = SOME tv` (irule_at Any) >>
  qpat_assum `cursor_inst.inst_id = loc` (irule_at Any) >>
  qpat_assum `owner.inst_id = shared` (irule_at Any) >>
  qpat_assum `valid_horizon cx st0 hz _` (irule_at Any) >>
  qexistsl [`vv`,`ss`,`sm`,`si`,`saved`,`sa`,`e`,`cursor_var`,`copy`] >>
  asm_rewrite_tac[]
QED

Resume abi_tuple_reached_row_mods[static_callback]:
  reverse conj_tac >- metis_tac[] >>
  qpat_assum `ty = lowered_value_type ce e` (SUBST1_TAC o SYM) >>
  qpat_assum `at = vyper_to_abi_type _ ty` (SUBST1_TAC o SYM) >>
  qpat_assum `h = LENGTH _` (SUBST1_TAC o SYM) >>
  qpat_assum `cursor = Var cursor_var` (SUBST1_TAC o SYM) >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `!b r src u1 G1 t1. unwrap_value _ _ b = _ /\ _ ==> _`
    (drule_all_then (qx_choosel_then [`z`,`Gz`,`tz`,`first`,`last`]
      (MAP_EVERY assume_tac o CONJUNCTS))) >>
  qhdtm_assum `abi_tuple_row_effects_mods`
    (strip_assume_tac o REWRITE_RULE [abi_tuple_row_effects_mods_def]) >>
  qpat_assum `!x. not_fresh_at b x ==> _` (drule_then strip_assume_tac) >>
  `lookup_var hp z = lookup_var hp u1` by
    (qpat_assum `eval_operand (Var hp) u1 = _`
       (assume_tac o REWRITE_RULE [eval_operand_def]) >> metis_tac[]) >>
  `ptr_covers Gz tz hp z (abi_member_head_size at)` by
    (irule ptr_covers_frame >> qexistsl [`G1`,`u1`,`t1`] >> asm_rewrite_tac[]) >>
  `eval_operand (Var hp) z = SOME (n2w (pbase+dst_offset+h))` by
    (pure_rewrite_tac[eval_operand_def] >>
     qpat_assum `lookup_var hp z = _` SUBST1_TAC >>
     qpat_assum `eval_operand (Var hp) u1 = _`
       (ACCEPT_TAC o REWRITE_RULE [eval_operand_def])) >>
  qpat_x_assum `ty = lowered_value_type ce e` kall_tac >>
  qexistsl [`z`,`Gz`,`tz`] >> asm_rewrite_tac[] >>
  qexistsl [`first`,`last`] >> asm_rewrite_tac[]
QED

Resume abi_tuple_reached_row_mods[dynamic_callback]:
  reverse conj_tac >- metis_tac[] >>
  qpat_assum `ty = lowered_value_type ce e` (SUBST1_TAC o SYM) >>
  qpat_assum `at = vyper_to_abi_type _ ty` (SUBST1_TAC o SYM) >>
  qpat_assum `av = EL i avs` (SUBST1_TAC o SYM) >>
  qpat_assum `off = hl + LENGTH _` (SUBST1_TAC o SYM) >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `!b r src u1 G1 t1. unwrap_value _ _ b = _ /\ _ ==> _`
    (drule_all_then (qx_choosel_then [`z`,`Gz`,`tz`,`first`,`last`]
      (MAP_EVERY assume_tac o CONJUNCTS))) >>
  qpat_assum `_ ==> ?E0. get_tenv cx SUBMAP E0 /\ _` mp_tac >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `E0` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qpat_assum `abi_tuple_buffer_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ready z Gz tz`
    (MAP_EVERY assume_tac o CONJUNCTS o REWRITE_RULE [abi_tuple_buffer_state_mods_def]) >>
  `stmt_state_rel hz ctx func ce cx ee z` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ z /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `local_ptrs_reserved ce ready` by
    (irule local_ptrs_reserved_next_var >> qexists `se` >>
     fs[ci_mono_def]) >>
  `pbase+dst_offset+off + LENGTH (enc at av) <= pbase+capacity` by decide_tac >>
  qexistsl [`z`,`Gz`,`tz`] >>
  qpat_assum `abi_tuple_buffer_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ready z Gz tz`
    (fn th => pure_rewrite_tac [th]) >>
  qhdtm_assum `abi_tuple_row_effects_mods` (fn th => pure_rewrite_tac [th]) >>
  qpat_assum `abi_encode_values_prefix_at _ _ _ _ _ _ _ i ready z _ _`
    (fn th => pure_rewrite_tac [th]) >>
  qpat_assum `!D. gas_origin_ptr_path _ (q,Gq,tq) [] (OK z,Gz,tz)`
    (fn th => pure_rewrite_tac [th]) >>
  rewrite_tac[] >>
  irule (at_horizon_named "H" abi_tuple_dynamic_restore_input_mods) >>
  qpat_assum `expr_val_at ce cx ty first last ee v src z` (irule_at Any) >>
  qexistsl [`tp`,`saved`,`root`,`prep`,`owner`,`len`,`ctx`,`capacity`,`enc at av`,`hz`,`E0`] >>
  pure_asm_rewrite_tac[] >>
  decide_tac
QED

Finalise abi_tuple_reached_row_mods
