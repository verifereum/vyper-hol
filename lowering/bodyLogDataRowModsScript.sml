(* Specialize the shared reached-row encoder to the Log data allocation.
   The cursor is the output of the loop's actual cursor ALLOCA. *)
Theory bodyLogDataRowMods
Ancestors
  bodyLogDataRowSelectMods bodyAbiTupleReachedRowMods
  bodyLogCaptureOperandMods bodyAbiTupleBufferStateMods
  bodyAbiEncodePackedPostMods exprSimHypsDefs
  vyperStorageFootprint contractABI context fragGasOriginPtr
  compileEnv exprLowering loweringStateRelDefs venomState venomInst
  finite_map list pair arithmetic

Theorem log_data_row_mods:
  rows = SND (split_log_ops (ZIP (saved,atys)) flags) /\
  atys = MAP (lowered_value_type ce) args /\
  LENGTH flags = LENGTH args /\ LENGTH flags = LENGTH saved /\
  LENGTH flags = LENGTH vs /\ i < LENGTH rows /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    LIST_REL (\(e,sv) v. ?si sm ss vv copy.
      abi_encode_saved_row_mods lo ce cx sa se e sv v si sm ss vv copy H ee G tn s)
      (select_log_args F flags (ZIP (args,saved))) (select_log_args F flags vs)) /\
  ats = vyper_to_abi_types (get_tenv cx) (log_non_indexed_types flags atys) /\
  vyper_to_abi_list (get_tenv cx) (log_non_indexed_types flags atys)
    (log_non_indexed_values flags vs) = SOME avs /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
    abi_member_head_size at) rows ats /\ LIST_REL abi_encoder_layout_valid ats avs /\
  hl = head_lengths ats 0 /\ LENGTH (enc (Tuple ats) (ListV avs)) <= capacity /\
  (!j. j < LENGTH flags /\ EL j flags = F ==>
    expr_body_pre_mods mods ce cx env (EL j args) entry /\
    ?rt. evaluate_type (get_tenv cx) (EL j atys) = SOME rt /\
      value_has_type rt (EL j vs) /\
      type_memory_bytes ce (EL j atys) = type_memory_size rt /\ type_memory_size rt < 2**64) /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (?E0. get_tenv cx SUBMAP E0 /\ sfields_tenv_consistent ce.ce_struct_fields E0 /\
    (!t rt. evaluate_type E0 t = SOME rt ==> type_memory_bytes ce t = type_memory_size rt)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM owner (fn_insts func) /\ owner.inst_opcode = ALLOCA /\
  owner.inst_id = se.cs_next_id /\ owner.inst_outputs = [p] /\ not_local_ptr ce ee.scopes p /\
  se.cs_next_id < st.cs_next_id /\
  MEM ci (fn_insts func) /\ ci.inst_opcode = ALLOCA /\
  ci.inst_id = st.cs_next_id /\ ci.inst_outputs = [r] /\ not_local_ptr ce ee.scopes r /\
  cursor = Var r /\
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    se.cs_next_id b capacity p p 0 [] a u Gu tu /\
  abi_encode_values_prefix_at ats avs hl b cursor st.cs_next_id slot i a u Gu tu /\
  compile_abi_encode_value_rows ce (Var p) cursor
    (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows)))
    [EL i rows] a = ((),c) /\ fn_has_code a c func ==>
  ?z Gz tz.
    abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id b capacity p p 0 [] c z Gz tz /\
    abi_tuple_row_effects_mods ce ee func se.cs_next_id b capacity 0 st.cs_next_id
      a u Gu tu c z Gz tz /\
    abi_encode_values_prefix_at ats avs hl b cursor st.cs_next_id slot (SUC i) c z Gz tz /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `h = SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows))` >>
  qabbrev_tac `off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs)))` >>
  mp_tac (Q.INST [`t` |-> `s`, `sb` |-> `se`] log_data_row_select_mods) >>
  impl_tac >- (asm_rewrite_tac[] >> simp[Abbr `h`, Abbr `off`]) >>
  disch_then (qx_choosel_then [`j`,`e`,`sv`,`ty`,`v`,`at`,`av`]
    (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `expr_body_pre_mods mods ce cx env e entry /\
   ?rt. evaluate_type (get_tenv cx) ty = SOME rt /\ value_has_type rt v /\
     type_memory_bytes ce ty = type_memory_size rt /\ type_memory_size rt < 2**64` by
    (qpat_assum `e = EL j args` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `ty = EL j atys` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `v = EL j vs` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `!j. j < LENGTH flags /\ _ ==> _`
       (qspec_then `j` (drule_all_then ACCEPT_TAC))) >>
  pop_assum strip_assume_tac >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?si sm ss vv copy. _`
    (qspec_then `H0` (drule_then (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`copy`] assume_tac))) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     abi_encode_saved_row_mods lo ce cx sa se e sv v si sm ss vv copy H ee G tn s` by
    (gen_tac >> disch_tac >>
     `vv_storage_live H cx sv ee s` by
       (qpat_assum `!H. valid_horizon _ _ H _ ==> ?si sm ss vv copy. _`
          (qspec_then `H` (drule_then
             (qx_choosel_then [`i0`,`m0`,`s0`,`w0`,`c0`] mp_tac))) >>
        simp_tac bool_ss [abi_encode_saved_row_mods_def]) >>
     qhdtm_assum `abi_encode_saved_row_mods`
       (MAP_EVERY assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
     asm_rewrite_tac[abi_encode_saved_row_mods_def]) >>
  `!l. vv_operand sv <> Label l` by
    (qhdtm_assum `abi_encode_saved_row_mods`
       (MAP_EVERY assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
     drule_all_then ACCEPT_TAC log_capture_operand_not_label_mods) >>
  `~is_word_type ty /\ is_dynamic at ==> off + LENGTH (enc at av) <= capacity` by
    (strip_tac >> qpat_assum `is_dynamic at ==> _` (drule_then ACCEPT_TAC)) >>
  qpat_x_assum `cursor = Var r` SUBST_ALL_TAC >>
  `compile_abi_encode_value_rows ce (Var p) (Var r) h [(sv,ty)] a = ((),c)` by
    (qpat_assum `EL i rows = (sv,ty)` (fn th => pure_rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  irule (SIMP_RULE bool_ss [ADD_CLAUSES, SUB_0]
    (Q.INST [`dst_offset` |-> `0`] abi_tuple_reached_row_mods)) >>
  qpat_assum `owner.inst_id = se.cs_next_id` (irule_at Any) >>
  qpat_assum `ci.inst_id = st.cs_next_id` (irule_at Any) >>
  qpat_assum `compile_abi_encode_value_rows _ _ _ h [(sv,ty)] _ = _` (irule_at Any) >>
  qpat_assum `evaluate_type _ ty = SOME rt` (irule_at Any) >>
  qpat_assum `vyper_to_abi _ ty v = SOME av` (irule_at Any) >>
  qpat_assum `at = EL i ats` (irule_at Any) >>
  qpat_assum `ty = lowered_value_type ce e` (irule_at Any) >>
  qpat_assum `off <= capacity` (irule_at Any) >>
  qpat_assum `valid_horizon _ _ H0 _` (irule_at Any) >>
  qexistsl [`vv`,`ss`,`sm`,`si`,`sa`,`copy`] >>
  asm_rewrite_tac[] >>
  simp[Abbr `off`]
QED
