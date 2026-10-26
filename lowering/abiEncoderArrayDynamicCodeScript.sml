(* Factor the actual dynamic-element body without changing instruction order.
   TOP-LEVEL: exact phases, trace and containing-code/counter context. *)
Theory abiEncoderArrayDynamicCode
Ancestors
  abiEncoderArrayCode abiEncoderArrayTail abiEncoderArrayAddress abiEncoderChildCode
  abiEncoderChildContext abiEncoderCounters abiEncoderAppend abiEncoderResultLive abiEncoderPhi
  abiDecoderContract fragExec compileEnv emitHelperProps emitHelper venomInst venomExecSemantics list rich_list arithmetic
Libs monadsyntax

Theorem abi_encode_array_dynamic_body_phases:
  abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz =
    do coords <- abi_encode_array_addresses ip src dst asz msz;
       ops <- abi_encode_array_tail (FST (SND coords)) dyn_ptr;
       child_len <- compile_abi_encode_to_buf (SND ops) (SND (FST coords)) ei;
       abi_encode_child_suffix (SND (SND coords)) dyn_ptr (FST ops) child_len;
       return (FST (FST coords))
    od
Proof
  simp_tac bool_ss [FUN_EQ_THM, abi_encode_array_dynamic_body_def, abi_encode_array_tail_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_encode_array_dynamic_body_trace:
  abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz st = (out,end_st) ==>
  ?coords addressed ops prepared child_len child_end.
    abi_encode_array_addresses ip src dst asz msz st = (coords,addressed) /\
    abi_encode_array_tail (FST (SND coords)) dyn_ptr addressed = (ops,prepared) /\
    compile_abi_encode_to_buf (SND ops) (SND (FST coords)) ei prepared = (child_len,child_end) /\
    abi_encode_child_suffix (SND (SND coords)) dyn_ptr (FST ops) child_len child_end = (child_len,end_st) /\
    out = FST (FST coords)
Proof
  simp_tac bool_ss [abi_encode_array_dynamic_body_phases, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac abi_encode_child_suffix_shape >> gvs[] >>
  rename1 `abi_encode_array_addresses _ _ _ _ _ st = (coords,addressed)` >>
  rename1 `abi_encode_array_tail _ _ addressed = (ops,prepared)` >>
  rename1 `compile_abi_encode_to_buf _ _ ei prepared = (child_len,child_end)` >>
  qexistsl_tac [`coords`, `addressed`, `ops`, `prepared`, `child_len`, `child_end`] >>
  asm_simp_tac bool_ss []
QED

Theorem abi_encode_array_dynamic_body_context:
  abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func ==>
  ?coords addressed ops prepared child_len child_end.
    abi_encode_array_addresses ip src dst asz msz st = (coords,addressed) /\
    abi_encode_array_tail (FST (SND coords)) dyn_ptr addressed = (ops,prepared) /\
    compile_abi_encode_to_buf (SND ops) (SND (FST coords)) ei prepared = (child_len,child_end) /\
    abi_encode_child_suffix (SND (SND coords)) dyn_ptr (FST ops) child_len child_end = (child_len,end_st) /\
    out = FST (FST coords) /\
    fn_has_code st addressed func /\ fn_has_code addressed prepared func /\
    fn_has_code prepared child_end func /\ fn_has_code child_end end_st func /\
    addressed.cs_next_id = st.cs_next_id+7 /\ addressed.cs_next_var = st.cs_next_var+7 /\
    prepared.cs_next_id = addressed.cs_next_id+2 /\ prepared.cs_next_var = addressed.cs_next_var+2 /\
    prepared.cs_next_id <= child_end.cs_next_id /\ prepared.cs_next_var <= child_end.cs_next_var /\
    child_end.cs_next_id+3 = end_st.cs_next_id /\ child_end.cs_next_var+1 = end_st.cs_next_var /\
    addressed.cs_blocks = st.cs_blocks /\ prepared.cs_blocks = addressed.cs_blocks /\
    end_st.cs_blocks = child_end.cs_blocks /\ end_st.cs_current_bb = child_end.cs_current_bb /\
    abi_decoder_operand_live child_end.cs_next_var child_len
Proof
  strip_tac >> drule abi_encode_array_dynamic_body_trace >> strip_tac >>
  drule abi_encode_array_addresses_shape >> strip_tac >>
  drule abi_encode_array_tail_shape >> strip_tac >> drule abi_encode_child_suffix_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >> drule cs_extends_abi_encode >> strip_tac >>
  drule abi_encode_result_live >> strip_tac >>
  `cs_extends st addressed /\ cs_extends addressed prepared /\ cs_extends child_end end_st` by
    (rpt conj_tac >> irule abi_encoder_straight_extends >> asm_simp_tac bool_ss []) >>
  `cs_extends prepared end_st` by
    (irule cs_extends_trans >> qexists_tac `child_end` >> asm_simp_tac bool_ss []) >>
  `cs_extends addressed end_st` by
    (irule cs_extends_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`st`, `addressed`, `end_st`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.SPECL [`addressed`, `prepared`, `end_st`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.SPECL [`prepared`, `child_end`, `end_st`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexistsl_tac [`coords`, `addressed`, `ops`, `prepared`, `child_len`, `child_end`] >>
  asm_simp_tac bool_ss []
QED

Theorem abi_encode_child_suffix_zero_phi:
  abi_encode_child_suffix head dyn_ptr offset child_len st = (out,st') /\
  phi_prefix_length st.cs_current_insts = 0 /\ fn_has_code st st' func ==>
  !bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  simp_tac bool_ss [abi_encode_child_suffix_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  Cases_on `st.cs_current_insts` >> gvs[phi_prefix_length_def, mk_inst_def] >>
  rename1 `inst.inst_opcode = PHI` >> Cases_on `inst.inst_opcode = PHI` >> gvs[]
QED

Theorem abi_encode_array_dynamic_body_child_phi:
  compile_abi_encode_to_buf child_dst child_src ei prepared = (child_len,child_end) /\
  abi_encode_child_suffix head dyn_ptr offset child_len child_end = (child_len,end_st) /\
  fn_has_code child_end end_st func ==>
  prepared.cs_blocks = child_end.cs_blocks \/
  !bb. lookup_block child_end.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_core_exit_phi >> disch_tac >>
  Cases_on `prepared.cs_blocks = child_end.cs_blocks` >- asm_simp_tac bool_ss [] >>
  `phi_prefix_length child_end.cs_current_insts = 0` by full_simp_tac bool_ss [] >>
  mp_tac (Q.INST [`st` |-> `child_end`, `st'` |-> `end_st`, `out` |-> `child_len`]
    abi_encode_child_suffix_zero_phi) >>
  impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_DYNAMIC_CODE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder dynamic array body code not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayDynamicCode");
