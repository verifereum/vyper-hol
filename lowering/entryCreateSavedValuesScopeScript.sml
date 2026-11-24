(* Interpret the accepted saved-values fold with the actual operand scope. *)
Theory entryCreateSavedValuesScope
Ancestors
  bodyFullExtCallDirectEncode entryCreateFocusSpec
  abiEncodeValuesRun abiEncodeValuesCode exprLoweringProps exprSimAbiEncodeExecFrame
  stateRelProj bodyPtrDefs loweringPosts loweringStateRelDefs fragGasOriginPtr fragExec
  abiEncoderWindowPhase exprLowering compileEnv context contractABI
  venomState venomInst finite_map pred_set list arithmetic pair words

Theorem abi_encode_saved_values_scoped_from_rows:
  abi_encode_saved_state ctx func ce cx st0 ee DF lo disp se s G tn
    shared pbase capacity root payload_var dst_offset prefix st u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  compile_abi_encode_values_to_buf ce (Var payload_var) rows st = (alen,en) /\ fn_has_code st en func /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
    abi_member_head_size at) rows ats /\ LIST_REL abi_encoder_layout_valid ats avs /\
  hl = head_lengths ats 0 /\ bytes = enc (Tuple ats) (ListV avs) /\
  (!ci r. MEM ci (fn_insts func) /\ ci.inst_id = st.cs_next_id /\
    ci.inst_opcode = ALLOCA /\ ci.inst_outputs = [r] /\ not_local_ptr ce ee.scopes r ==>
    !i a c v Gv tv cursor slot.
    i < LENGTH rows /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo disp se s G tn
      shared pbase capacity root payload_var dst_offset prefix a v Gv tv /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor st.cs_next_id slot i a v Gv tv /\
    compile_abi_encode_value_rows ce (Var payload_var) cursor
      (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows)))
      [EL i rows] a = ((),c) /\ fn_has_code a c func ==>
    ?z Gz tz.
      (track_frame ==> pure_frame ce func ee se v z /\ wb_frame ce ee ee se v z) /\
      abi_encode_saved_state ctx func ce cx st0 ee DF lo disp se s G tn
        shared pbase capacity root payload_var dst_offset prefix c z Gz tz /\
      abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor st.cs_next_id slot (SUC i) c z Gz tz /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,Gv,tv) [] (OK z,Gz,tz)) /\
      create_operand_full_scope a c explicit ctx func v [] (OK z)) /\
  abi_encode_values_path_laws
    (\a c v z. create_operand_full_scope a c explicit ctx func v [] (OK z))
    func st en u hl alen ==>
  ?z Gz tz.
    (track_frame ==> pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo disp se s G tn
      shared pbase capacity root payload_var dst_offset prefix en z Gz tz /\
    eval_operand alen z = SOME (n2w (LENGTH bytes)) /\ op_taint tz alen = {} /\
    (!x. alen = Var x ==> not_fresh_at en x) /\
    mem_bytes_at (pbase+dst_offset) (LENGTH bytes) z.vs_memory = bytes /\
    (!j. pbase+dst_offset <= j /\ j < pbase+dst_offset + LENGTH bytes ==> j NOTIN tz.t_mem) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)) /\
    create_operand_full_scope st en explicit ctx func u [] (OK z)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST
    [`R` |-> `\a c v z. create_operand_full_scope a c explicit ctx func v [] (OK z)`]
    abi_encode_saved_values_execute_with_frame_and_path) >>
  impl_tac >- (rpt conj_tac >> metis_tac[]) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> asm_rewrite_tac[] >> BETA_TAC >> metis_tac[]
QED
