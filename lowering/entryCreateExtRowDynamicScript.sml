Theory entryCreateExtRowDynamic
Ancestors
  entryCreateAdminSequence entryCreatePathScope entryCreateCompletedCut entryCreateFocusSpec createSizeCutCode
  abiEncodeValuesDynamic abiEncoderWindowJointPhases abiEncoderWindowChild abiEncoderWindowPhase
  bodyFullExtCallDirectRow bodyFullExtCallDirectState entryCreatePackRowContinuation
  abiEncoderChildCode abiEncoderProps exprLoweringProps emitHelperProps emitHelper fragExec compileEnv
  venomInst venomState venomExecSemantics list rich_list arithmetic pair pred_set

(* Setup and publication are straight-line even when the child encodes a loop.
   The list equations below refer to the witnesses chosen by the joint proofs. *)
Theorem dynamic_pack_prefix_code[local]:
  abi_encode_child_prefix dst ho cursor a = (ops,b) ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
    (emitted_insts a b)
Proof
  simp[abi_encode_child_prefix_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  simp_tac bool_ss [GSYM listTheory.APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
  simp[frag_ids_def, mk_inst_def, is_terminator_def]
QED

Theorem dynamic_pack_suffix_code[local]:
  abi_encode_child_suffix head cursor off len a = (out,b) ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
    (emitted_insts a b)
Proof
  simp[abi_encode_child_suffix_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  simp_tac bool_ss [GSYM listTheory.APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
  simp[frag_ids_def, mk_inst_def, is_terminator_def]
QED

Theorem dynamic_pack_normalized_scope[local]:
  fn_has_code a b f /\ b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
    (emitted_insts a b) /\
  create_operand_at a s /\ ~s.vs_halted /\ create_operand_at b t /\
  run_inst_seq (emitted_insts a b) s = OK (t with vs_inst_idx := s.vs_inst_idx) ==>
  create_operand_full_scope a b explicit ctx f s [] (OK t)
Proof
  strip_tac >> drule_all create_admin_sequence_scope >>
  disch_then (qspecl_then [`explicit`,`ctx`] mp_tac) >>
  qpat_assum `create_operand_at b t` (strip_assume_tac o REWRITE_RULE [create_operand_at_def]) >>
  pop_assum (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >> simp[]
QED

Theorem dynamic_pack_prefix_scope:
  abi_encode_child_prefix dst ho cursor a = (ops,b) /\ fn_has_code a b f /\
  create_operand_at a s /\ ~s.vs_halted /\ window_phase ctx f a b ids outs s t /\
  run_inst_seq (emitted_insts a b) s = OK (t with vs_inst_idx := s.vs_inst_idx) ==>
  create_operand_full_scope a b explicit ctx f s [] (OK t)
Proof
  strip_tac >> drule dynamic_pack_prefix_code >> strip_tac >>
  drule window_phase_control >> strip_tac >>
  irule dynamic_pack_normalized_scope >> simp[create_operand_at_def] >>
  metis_tac[create_operand_at_def]
QED

Theorem dynamic_pack_suffix_scope:
  abi_encode_child_suffix head cursor off len a = (out,b) /\ fn_has_code a b f /\
  create_operand_at a s /\ ~s.vs_halted /\ window_phase ctx f a b ids outs s t /\
  run_inst_seq (emitted_insts a b) s = OK (t with vs_inst_idx := s.vs_inst_idx) ==>
  create_operand_full_scope a b explicit ctx f s [] (OK t)
Proof
  strip_tac >> drule dynamic_pack_suffix_code >> strip_tac >>
  drule window_phase_control >> strip_tac >>
  irule dynamic_pack_normalized_scope >> simp[create_operand_at_def] >>
  metis_tac[create_operand_at_def]
QED


(* The dynamic row keeps the concrete setup/restore/child/suffix witnesses,
   and lifts their empty-mark scopes to the enclosing saved-row interval. *)
Theorem abi_encode_saved_dynamic_row_scoped_from_phases:
  abi_static_row_restore
    (\a b u v. create_operand_full_scope a b explicit ctx func u [] (OK v))
    ctx func ce cx st0 ee DF lo explicit PG d se s G tn
    shared pbase capacity root dst dst_offset prefix saved ty v ats avs hl cursor loc slot i /\
  abi_encode_values_source_side
    (\a b u v. create_operand_full_scope a b explicit ctx func u [] (OK v))
    lo explicit ctx func PG /\
  abi_encode_values_suffix_join
    (\a b u v. create_operand_full_scope a b explicit ctx func u [] (OK v))
    (\a b u v. create_operand_full_scope a b explicit ctx func u [] (OK v)) func /\
  ~is_word_type ty /\ is_dynamic at /\
  fn_has_code su en func /\
  compile_abi_encode_value_rows ce (Var dst) cursor h [(saved,ty)] su = ((),en) /\
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix su u Gu tu /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i su u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  MEM cursor_inst (fn_insts func) /\ cursor_inst.inst_id = loc /\
  cursor_inst.inst_outputs = [cursor_var] /\ not_local_ptr ce ee.scopes cursor_var /\
  cursor_inst.inst_opcode = ALLOCA /\ shared < loc /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\ expr_sim_inv ce cx env ee /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\ at = EL i ats /\ av = EL i avs /\
  at = vyper_to_abi_type (get_tenv cx) ty /\ vyper_to_abi (get_tenv cx) ty v = SOME av /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ type_memory_bytes ce ty = type_memory_size tv /\
  value_has_type tv v /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\ off + LENGTH (enc at av) <= capacity-dst_offset /\
  (!bb j. lookup_block en.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH en.cs_current_insts) = SOME j ==> en.cs_next_id <= j.inst_id) ==>
  ?z Gz tz.
    (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix en z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot (SUC i) en z Gz tz /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) []
      (OK z,Gz,tz)) /\
    ?head offset tail prepared src ready len encoded u1.
      abi_encode_child_prefix (Var dst) h cursor su = ((head,offset,tail),prepared) /\
      unwrap_value ce saved prepared = (src,ready) /\
      compile_abi_encode_to_buf tail src
        (type_to_abi_enc_info ce.ce_struct_fields ce ty) ready = (len,encoded) /\
      abi_encode_child_suffix head cursor offset len encoded = (len,en) /\
      ci_mono su prepared /\ ci_mono prepared ready /\
      ci_mono ready encoded /\ ci_mono encoded en /\
      fn_has_code su prepared func /\ fn_has_code prepared ready func /\
      fn_has_code ready encoded func /\ fn_has_code encoded en func /\
      window_phase ctx func su prepared {} [] u u1 /\
      run_inst_seq (emitted_insts su prepared) u =
        OK (u1 with vs_inst_idx := u.vs_inst_idx) /\
      create_operand_full_scope su en explicit ctx func u [] (OK z)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`Restore` |->
      `\a b u v. create_operand_full_scope a b explicit ctx func u [] (OK v)`,
    `Child` |->
      `\a b u v. create_operand_full_scope a b explicit ctx func u [] (OK v)`,
    `Row` |->
      `\a b u v. create_operand_full_scope a b explicit ctx func u [] (OK v)`]
    abi_encode_saved_dynamic_row_open_side) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] strip_assume_tac) >>
  qexistsl_tac [`z`,`Gz`,`tz`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`head`,`offset`,`tail`,`prepared`,`src`,`ready`,`len`,`encoded`,`u1`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  `create_operand_at su u /\ ~u.vs_halted` by
    (qpat_assum `abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
        shared pbase capacity root dst dst_offset prefix su u Gu tu`
       (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_def]) >>
     simp[create_operand_at_def] >> metis_tac[]) >>
  `create_operand_full_scope su prepared explicit ctx func u [] (OK u1)` by
    (irule dynamic_pack_prefix_scope >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  `create_operand_full_scope prepared ready explicit ctx func u1 [] (OK u2)` by
    (qpat_assum `(\a b u v. create_operand_full_scope a b explicit ctx func u [] (OK v))
        prepared ready u1 u2` (ACCEPT_TAC o BETA_RULE)) >>
  `create_operand_full_scope ready en explicit ctx func u2 [] (OK z)` by
    (qpat_assum `(\a b u v. create_operand_full_scope a b explicit ctx func u [] (OK v))
        ready en u2 z` (ACCEPT_TAC o BETA_RULE)) >>
  `prepared.cs_next_id <= ready.cs_next_id /\ ready.cs_next_id <= en.cs_next_id` by
    (qpat_assum `ci_mono prepared ready`
       (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `ci_mono ready encoded`
       (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `ci_mono encoded en`
       (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >> decide_tac) >>
  `su.cs_next_id <= prepared.cs_next_id /\ prepared.cs_next_id <= en.cs_next_id` by
    (qpat_assum `ci_mono su prepared`
       (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `ci_mono prepared ready`
       (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `ci_mono ready encoded`
       (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `ci_mono encoded en`
       (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >> decide_tac) >>
  `create_operand_full_scope prepared en explicit ctx func u1 [] (OK z)` by
    (irule (SIMP_RULE bool_ss [APPEND]
      (Q.INST [`left` |-> `[]`, `right` |-> `[]`] create_operand_full_scope_prepend)) >>
     qexistsl_tac [`ready`,`u2`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!bb j. _ ==> _` (qspecl_then [`bb`,`j`] mp_tac) >>
     fs[frag_ids_def] >> decide_tac) >>
  irule (SIMP_RULE bool_ss [APPEND]
    (Q.INST [`left` |-> `[]`, `right` |-> `[]`] create_operand_full_scope_prepend)) >>
  qexistsl_tac [`prepared`,`u1`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!bb j. _ ==> _` (qspecl_then [`bb`,`j`] mp_tac) >>
  fs[frag_ids_def] >> decide_tac
QED

Theorem extcall_dynamic_pack_row_from_scoped_phases:
  abi_static_row_restore
    (\a b u v. create_operand_full_scope a b explicit ctx func u [] (OK v))
    ctx func ce cx st0 ee DF lo explicit PG d se s G tn
    shared pbase capacity root dst dst_offset prefix saved ty v ats avs hl cursor loc slot i /\
  abi_encode_values_source_side
    (\a b u v. create_operand_full_scope a b explicit ctx func u [] (OK v))
    lo explicit ctx func PG /\
  abi_encode_values_suffix_join
    (\a b u v. create_operand_full_scope a b explicit ctx func u [] (OK v))
    (\a b u v. create_operand_full_scope a b explicit ctx func u [] (OK v)) func /\
  (!bb j. lookup_block en.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH en.cs_current_insts) = SOME j ==> en.cs_next_id <= j.inst_id) /\
  ~is_word_type ty /\ is_dynamic at /\ fn_has_code su en func /\
  compile_abi_encode_value_rows ce (Var dst) cursor h [(saved,ty)] su = ((),en) /\
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix su u Gu tu /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i su u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  MEM cursor_inst (fn_insts func) /\ cursor_inst.inst_id = loc /\
  cursor_inst.inst_outputs = [cursor_var] /\ not_local_ptr ce ee.scopes cursor_var /\
  cursor_inst.inst_opcode = ALLOCA /\ shared < loc /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\ expr_sim_inv ce cx env ee /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\ at = EL i ats /\ av = EL i avs /\
  at = vyper_to_abi_type (get_tenv cx) ty /\ vyper_to_abi (get_tenv cx) ty v = SOME av /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ type_memory_bytes ce ty = type_memory_size tv /\
  value_has_type tv v /\ abi_encoder_layout_valid at av /\
  LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\
  off + LENGTH (enc at av) <= capacity-dst_offset ==>
  ?z Gz tz.
    (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix en z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot (SUC i) en z Gz tz /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) []
      (OK z,Gz,tz)) /\
    create_operand_full_scope su en explicit ctx func u [] (OK z)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac abi_encode_saved_dynamic_row_scoped_from_phases >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] strip_assume_tac) >>
  qexistsl_tac [`z`,`Gz`,`tz`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
