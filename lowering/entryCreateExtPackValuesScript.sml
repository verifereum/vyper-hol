(* Carry the actual direct encoder's caller spine through its row fold. *)
Theory entryCreateExtPackValues
Ancestors
  bodyFullExtCallDirectEncode bodyFullExtCallDirectState abiEncodeValuesRun entryCreateAdminSequence
  loweringStateRelDefs loweringShapeDefs bodyPtrDefs loweringPosts context
  entryCreatePathScope bodyPtrMakeArrayPrimitiveInstall bodyPtrMakeArrayEmission
  entryIntCallStageBuffer exprSimAbiEncodeObliviousFacts exprSimAbiEncodeObliviousSimulation
  fragObserverCodeProps ctorCallFreeABIEncode deploySymSrcFrameABI
  deploySymSrcBlockFrame exprSimAbiEncodeObliviousContext exprSimAbiEncodeObliviousCode
  exprSimAbiGasBridge exprLowering
  entryCreateCompletedCut entryCreateFocusSpec createSizeCutCode createSizeEncodeCode
  fragExec exprLoweringProps emitHelperProps emitHelper compileEnv fragGasOriginPtr
  abiEncoderProps rich_list venomExecSemantics
  venomState venomInst words arithmetic list pred_set pair

(* The finish cursor is followed by the request-length ADD. Its installed
   fetch is outside the entire encoder ID range, so no constituent step
   can visit that PC before the combined prefix finishes. *)
Definition encode_in_band_def[local]:
  encode_in_band st en explicit ctx func a b u v <=>
    st.cs_next_id <= a.cs_next_id /\ b.cs_next_id <= en.cs_next_id ==>
    create_expr_prefix st en explicit ctx func u [] v
End

Theorem encode_in_band_scope[local]:
  (!bb i. lookup_block en.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH en.cs_current_insts) = SOME i ==>
    i.inst_id NOTIN frag_ids st en) /\
  create_operand_full_scope a b explicit ctx func u [] (OK v) ==>
  encode_in_band st en explicit ctx func a b u v
Proof
  simp[encode_in_band_def, create_operand_full_scope_def] >> rpt strip_tac >>
  irule create_expr_prefix_lift >> qexistsl [`a`,`b`] >> asm_rewrite_tac[] >>
  rpt strip_tac >>
  qpat_assum `!bb i. _ ==> i.inst_id NOTIN frag_ids st en`
    (drule_all_then mp_tac) >>
  fs[frag_ids_def] >> decide_tac
QED

Theorem encode_cursor_init_scope[local]:
  emit_op ALLOCA [Lit 32w] a = (p,b) /\
  emit_void MSTORE [p; Lit (n2w hl)] b = ((),c) /\ fn_has_code a c func /\
  ~u.vs_halted /\ u.vs_current_bb = a.cs_current_bb /\
  u.vs_inst_idx = LENGTH a.cs_current_insts /\
  run_inst_seq (emitted_insts a c) u = OK (v with vs_inst_idx := u.vs_inst_idx) /\
  v.vs_inst_idx = LENGTH c.cs_current_insts ==>
  create_operand_full_scope a c explicit ctx func u [] (OK v)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_op_same_blocks >> drule emit_void_same_blocks >>
  simp[same_blocks_def] >> rpt strip_tac >>
  `create_operand_full_scope a c explicit ctx func u []
     (OK ((v with vs_inst_idx := u.vs_inst_idx) with vs_inst_idx := LENGTH c.cs_current_insts))`
    suffices_by
      (`(v with vs_inst_idx := u.vs_inst_idx) with vs_inst_idx := LENGTH c.cs_current_insts = v`
         by simp[venom_state_component_equality] >> asm_rewrite_tac[]) >>
  irule create_admin_sequence_scope >>
  simp[venom_state_component_equality, create_operand_at_def,
    emitted_insts_def, APPEND_ASSOC, DROP_LENGTH_APPEND, mk_inst_def,
    frag_ids_def, is_terminator_def] >>
  PURE_ONCE_REWRITE_TAC [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, is_terminator_def]
QED

Theorem encode_cursor_finish_scope[local]:
  emit_op MLOAD [p] a = (out,b) /\ fn_has_code a b func /\
  ~u.vs_halted /\ u.vs_current_bb = a.cs_current_bb /\
  u.vs_inst_idx = LENGTH a.cs_current_insts /\
  run_inst_seq (emitted_insts a b) u = OK (v with vs_inst_idx := u.vs_inst_idx) /\
  v.vs_inst_idx = LENGTH b.cs_current_insts ==>
  create_operand_full_scope a b explicit ctx func u [] (OK v)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> simp[same_blocks_def] >> strip_tac >>
  `create_operand_full_scope a b explicit ctx func u []
     (OK ((v with vs_inst_idx := u.vs_inst_idx) with vs_inst_idx := LENGTH b.cs_current_insts))`
    suffices_by
      (`(v with vs_inst_idx := u.vs_inst_idx) with vs_inst_idx := LENGTH b.cs_current_insts = v`
         by simp[venom_state_component_equality] >> asm_rewrite_tac[]) >>
  irule create_admin_sequence_scope >>
  simp[create_operand_at_def, mk_inst_def, frag_ids_def, is_terminator_def]
QED

Theorem encode_in_band_laws[local]:
  (!bb i. lookup_block en.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH en.cs_current_insts) = SOME i ==>
    i.inst_id NOTIN frag_ids st en) ==>
  abi_encode_values_path_laws (encode_in_band st en explicit ctx func)
    func st en u hl alen
Proof
  strip_tac >> simp_tac bool_ss [abi_encode_values_path_laws_def] >>
  rpt conj_tac
  >- simp[encode_in_band_def]
  >- (simp[encode_in_band_def, ci_mono_def] >> rpt strip_tac >>
      irule (Q.INST [`left` |-> `[]`,`right` |-> `[]`]
        create_expr_prefix_append |> SIMP_RULE bool_ss [APPEND]) >>
      qexists_tac `v` >> metis_tac[LESS_EQ_TRANS])
  >- (rpt strip_tac >> irule encode_in_band_scope >>
      metis_tac[encode_cursor_init_scope])
  >> rpt strip_tac >> irule encode_in_band_scope >>
  metis_tac[encode_cursor_finish_scope]
QED

Theorem extcall_direct_values_scoped_from_rows:
  extcall_direct_state ctx func ce cx st0 ee DF lo disp se s G tn
    shared pbase capacity root payload_var selector st u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\ 32 <= capacity /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  compile_abi_encode_values_to_buf ce (Var payload_var) rows st = (alen,en) /\ fn_has_code st en func /\
  emit_op ADD [alen;Lit 4w] en = (len,after) /\ fn_has_code en after func /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
    abi_member_head_size at) rows ats /\ LIST_REL abi_encoder_layout_valid ats avs /\
  hl = head_lengths ats 0 /\ bytes = enc (Tuple ats) (ListV avs) /\
  (!ci r. MEM ci (fn_insts func) /\ ci.inst_id = st.cs_next_id /\
    ci.inst_opcode = ALLOCA /\ ci.inst_outputs = [r] /\ not_local_ptr ce ee.scopes r ==>
    !i a c v Gv tv cursor slot.
    i < LENGTH rows /\
    extcall_direct_state ctx func ce cx st0 ee DF lo disp se s G tn
      shared pbase capacity root payload_var selector a v Gv tv /\
    abi_encode_values_prefix_at ats avs hl (pbase+32) cursor st.cs_next_id slot i a v Gv tv /\
    compile_abi_encode_value_rows ce (Var payload_var) cursor
      (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows)))
      [EL i rows] a = ((),c) /\ fn_has_code a c func ==>
    ?z Gz tz.
      extcall_direct_state ctx func ce cx st0 ee DF lo disp se s G tn
        shared pbase capacity root payload_var selector c z Gz tz /\
      abi_encode_values_prefix_at ats avs hl (pbase+32) cursor st.cs_next_id slot (SUC i) c z Gz tz /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,Gv,tv) [] (OK z,Gz,tz)) /\
      create_operand_full_scope a c explicit ctx func v [] (OK z)) ==>
  ?z Gz tz.
    extcall_direct_state ctx func ce cx st0 ee DF lo disp se s G tn
      shared pbase capacity root payload_var selector en z Gz tz /\
    eval_operand alen z = SOME (n2w (LENGTH bytes)) /\ op_taint tz alen = {} /\
    (!x. alen = Var x ==> not_fresh_at en x) /\
    mem_bytes_at (pbase+32) (LENGTH bytes) z.vs_memory = bytes /\
    (!j. pbase+32 <= j /\ j < pbase+32 + LENGTH bytes ==> j NOTIN tz.t_mem) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)) /\
    create_operand_full_scope st en explicit ctx func u [] (OK z)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!bb i. lookup_block en.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH en.cs_current_insts) = SOME i ==>
    i.inst_id NOTIN frag_ids st en` by
    (drule emit_op_same_blocks >> simp[same_blocks_def] >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     drule_all fn_has_code_same_block >> strip_tac >>
     qpat_assum `!i. i < LENGTH _ ==> get_instruction _ _ = _`
       (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
     rpt strip_tac >> gvs[frag_ids_def, mk_inst_def]) >>
  mp_tac (Q.INST [`R` |-> `encode_in_band st en explicit ctx func`]
     extcall_direct_values_execute_with_path) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (irule encode_in_band_laws >> first_assum ACCEPT_TAC) >>
      map_every qx_gen_tac [`ci`,`r`] >> disch_tac >>
      qpat_assum `!ci (r:string). MEM ci (fn_insts func) /\ _ ==> _`
        (qspecl_then [`ci`,`r`] mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >>
      disch_then (fn row =>
        map_every qx_gen_tac [`i`,`a`,`c`,`v`,`Gv`,`tv`,`cursor`,`slot`] >>
        disch_tac >> qspecl_then [`i`,`a`,`c`,`v`,`Gv`,`tv`,`cursor`,`slot`] mp_tac row) >>
      impl_tac >- first_assum ACCEPT_TAC >>
      disch_then (qx_choosel_then [`z`,`Gz`,`tz`] (map_every assume_tac o CONJUNCTS)) >>
      qexistsl [`z`,`Gz`,`tz`] >> asm_rewrite_tac[] >>
      irule encode_in_band_scope >> metis_tac[]) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`z`,`Gz`,`tz`] >> asm_rewrite_tac[] >>
  qpat_assum `extcall_direct_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ selector en z _ _`
    (strip_assume_tac o REWRITE_RULE [extcall_direct_state_def]) >>
  fs[encode_in_band_def, create_operand_full_scope_def]
QED

(* Lift the encoder's existing opcode preservation to its own fragment,
   even when the caller's entry block already contains an excluded opcode. *)
val encode_safe = ``\opc. opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2``;

Theorem encode_recursive_action_safe[local]:
  code_action ^encode_safe (compile_abi_encode_to_buf dst src ei)
Proof
  simp[code_action_def] >> rpt strip_tac >>
  rename1 `compile_abi_encode_to_buf dst src ei a = (out,b)` >>
  `code_step enc_safe_opcode a b` by
    metis_tac[code_action_def, code_action_encoder_mutual] >>
  fs[code_step_def] >>
  qabbrev_tac `sa = a with cs_blocks := []` >>
  Cases_on `compile_abi_encode_to_buf dst src ei sa` >>
  rename1 `compile_abi_encode_to_buf dst src ei sa = (raw,sb)` >>
  `compile_abi_encode_to_buf dst src ei a =
        (raw,sb with cs_blocks := sb.cs_blocks ++ a.cs_blocks)` by
    (`a = sa with cs_blocks := sa.cs_blocks ++ a.cs_blocks` by simp[Abbr `sa`] >>
     metis_tac[deploy_blocks_frame_def, deploy_blocks_frame_abi_encode_to_buf]) >>
  `b.cs_blocks = sb.cs_blocks ++ a.cs_blocks /\
   b.cs_current_insts = sb.cs_current_insts` by
    (qpat_assum `compile_abi_encode_to_buf _ _ _ _ = (_,sb with cs_blocks := _)` mp_tac >>
     simp[] >> strip_tac >> gvs[]) >>
  `emitted_blocks a b = sb.cs_blocks /\ emitted_blocks sa sb = sb.cs_blocks` by
    (rpt conj_tac >> irule emitted_blocks_append >> simp[Abbr `sa`]) >>
  `frag_code a b = frag_code sa sb` by
    simp[frag_code_def, emitted_insts_def, Abbr `sa`] >>
  qabbrev_tac `ids = MAP (\i. i.inst_id) sa.cs_current_insts` >>
  `LENGTH ids = LENGTH sa.cs_current_insts` by simp[Abbr `ids`] >>
  `frag_start_oblivious (compile_abi_encode_to_buf dst src ei)` by
    metis_tac[entry_action_oblivious, entry_action_encoder_mutual] >>
  `compile_abi_encode_to_buf dst src ei (start_relabel sa.cs_current_bb ids sa) =
      (raw,start_swap sa sa.cs_current_bb ids sb)` by
    metis_tac[frag_start_oblivious_def] >>
  `frag_code (start_relabel sa.cs_current_bb ids sa)
     (start_swap sa sa.cs_current_bb ids sb) = frag_code sa sb` by
    (Cases_on `sa.cs_blocks = sb.cs_blocks`
     >- (`sb.cs_blocks = []` by fs[Abbr `sa`] >>
         simp[start_relabel_def, start_swap_def, frag_code_def, emitted_blocks_def,
              emitted_insts_def, Abbr `ids`, DROP_APPEND])
     >> irule start_relabel_frag_code >>
     metis_tac[code_action_def, code_action_encoder_mutual, code_step_def, entry_shape_extends]) >>
  `EVERY (\i. ^encode_safe i.inst_opcode)
     (state_insts (start_relabel sa.cs_current_bb ids sa))` by
    simp[start_relabel_def, state_insts_def, all_blocks_def, Abbr `sa`, EVERY_MAP, mk_inst_def] >>
  `EVERY (\i. ^encode_safe i.inst_opcode)
     (state_insts (start_swap sa sa.cs_current_bb ids sb))` by
    (qspecl_then [`dst`,`src`,`ei`,`start_relabel sa.cs_current_bb ids sa`] mp_tac
      (Q.INST [`P` |-> `^encode_safe`] (cj 2 outcomes_free_abi_encode)) >>
     simp[DISJ_IMP_THM, FORALL_AND_THM]) >>
  fs[EVERY_MEM] >> metis_tac[frag_code_in_state_insts]
QED

Theorem encode_rows_action_safe[local]:
  !rows dst cursor off.
    code_action ^encode_safe (compile_abi_encode_value_rows ce dst cursor off rows)
Proof
  Induct >- simp[compile_abi_encode_value_rows_def, code_action_return] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields h1` >>
  simp[compile_abi_encode_value_rows_def, LET_THM] >>
  rpt (FIRST [CHANGED_TAC (simp[code_action_emit_op, code_action_emit_void,
      code_action_return, buffer_unwrap_action, buffer_store_action, encode_recursive_action_safe]),
    irule code_action_bind, irule code_action_ignore_bind, conj_tac, gen_tac])
QED

Theorem extcall_direct_values_opcode_band:
  compile_abi_encode_values_to_buf ce dst rows st = (out,en) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (frag_code st en)
Proof
  `code_action ^encode_safe (compile_abi_encode_values_to_buf ce dst rows)` by
    (simp[compile_abi_encode_values_to_buf_def] >>
     rpt (FIRST [CHANGED_TAC (simp[code_action_alloc_buffer, code_action_emit_op,
        code_action_emit_void, encode_rows_action_safe]),
       irule code_action_bind, irule code_action_ignore_bind, conj_tac, gen_tac])) >>
  fs[code_action_def, code_step_def] >> metis_tac[]
QED
