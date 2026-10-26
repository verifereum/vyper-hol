(* Actual body execution retains the parent source and registered loop index. *)
Theory abiEncoderArrayBodyMemory
Ancestors
  abiEncoderArrayMemory abiEncoderArrayCursor abiEncoderArrayStaticIteration abiEncoderArrayDynamicIteration
  abiEncoderArrayBodyCode abiEncoderArrayDynamicCode abiEncoderArrayCode abiEncoderArrayAddress
  abiEncoderArrayLayout abiEncoderArrayPrefix abiEncoderMembersDefs abiEncoderChildInputs abiEncoderAdmissible
  abiDecoderDynamicLoopSetup abiDecoderEffect abiDecoderContract abiDecoderReentry abiDecoderLoop
  fragExec compileEnv emitHelperProps emitHelper valueEncoding contractABI venomState finite_map
  words list arithmetic

Theorem abi_encode_array_addresses_index:
  abi_encode_array_addresses ip src dst asz msz st = (coords,prepared) ==>
  FST (FST coords) = Var (STRING #"%" (toString st.cs_next_var))
Proof
  simp[abi_encode_array_addresses_def, abi_decode_array_head_setup_def, abi_decode_indexed_coordinates_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem abi_encode_array_static_body_index:
  abi_encode_array_static_body ip src dst ei asz msz st = (out,end_st) ==>
  out = Var (STRING #"%" (toString st.cs_next_var))
Proof
  strip_tac >> drule abi_encode_array_static_body_trace >> strip_tac >>
  drule abi_encode_array_addresses_index >> asm_simp_tac bool_ss []
QED

Theorem abi_encode_array_dynamic_body_index:
  abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz st = (out,end_st) ==>
  out = Var (STRING #"%" (toString st.cs_next_var))
Proof
  strip_tac >> drule abi_encode_array_dynamic_body_trace >> strip_tac >>
  drule abi_encode_array_addresses_index >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_array_static_body_memory:
  abi_encoder_static_leaf ei /\ abi_encode_array_static_body ip src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_encoder_array_memory ei asz msz F ty avs owner_st src dst sb source_cap d output_size b cap j initial /\
  abi_encoder_cursor T ip site slot first lo owner_st j initial /\ j < LENGTH avs /\
  owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= st.cs_next_id /\
  abi_decoder_budget first last b cap initial /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_array_memory ei asz msz F ty avs owner_st src dst sb source_cap
      d output_size b cap (SUC j) actual /\
    abi_encoder_cursor T ip site slot first lo owner_st j actual /\
    eval_operand out actual = SOME (n2w j) /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id owner_st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_array_memory _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_memory_def]) >>
  qpat_assum `abi_encoder_cursor T _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  drule_all abi_encode_array_static_body_context >> strip_tac >>
  `first <= st.cs_next_id /\ site < last /\ site < st.cs_next_id /\ owner_st.cs_next_id <= last` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `cursor_op` |-> `ip:operand`, `off` |-> `j:num`, `s` |-> `initial:venom_state`]
    abi_encoder_cursor_bounds) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_encoder_buffer_pre (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size b cap initial` by
    (irule abi_encoder_buffer_pre_mono >> qexists_tac `owner_st` >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`p` |-> `n2w slot:bytes32`] abi_encoder_array_static_iteration) >>
  impl_tac >- asm_simp_tac (srw_ss()) [w2n_n2w, Excl "enc_def"] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `abi_decoder_effect first last st.cs_next_id end_st.cs_next_id owner_st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d`, `end_st.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`, `output_size`] >> simp[]) >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `next` |-> `owner_st.cs_next_var`, `cursor_op` |-> `ip:operand`,
    `active` |-> `T`, `off` |-> `j:num`, `sz` |-> `output_size:num`, `owned_lo` |-> `st.cs_next_id`, `owned_hi` |-> `end_st.cs_next_id`]
    abi_encoder_cursor_effect_protected) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `dyn` |-> `F`, `k` |-> `SUC j`, `hi` |-> `end_st.cs_next_id`,
    `lo` |-> `st.cs_next_id`] abi_encoder_array_memory_advance) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_BODY_MEMORY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array body memory not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayBodyMemory");
