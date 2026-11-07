(* Counted physical execution of heterogeneous decoder suffixes.
   The quantified cursor permits recursion at the actual child endpoint. *)
Theory bodyIntCallDecoderCountedMembersContract
Ancestors
  abiScratchDecoderMembersContract abiScratchDecoderContract abiScratchEncoderContract
  abiScratchLeafEffect abiDecoderFrame abiDecoderMemberInfos abiDecoderMembers abiValidMembers
  abiDecoderValidContract abiDecoderEffect abiDecoderReentry abiDecoderLoop
  abiDecoderTypedContract abiDecoderContract abiDecodeRanges abiEncoder compileEnv
  valueEncoding vyperABI fragGasPath fragExec venomState venomExecSemantics words list arithmetic

Definition intcall_scratch_decoder_members_counted_def:
  intcall_scratch_decoder_members_counted ce env sf tys tvs <=>
    !dst src opc base_op hi st final func ctx first last b cap limit_st initial
      pretys bs vs B sb d.
    compile_abi_decode_complex_elems dst src opc base_op hi (abi_decoder_member_infos sf ce tys)
      (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
      (SUM (MAP (type_memory_bytes ce) pretys)) st = ((),final) /\
    fn_has_code st final func /\
    (st.cs_blocks = final.cs_blocks \/
      !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_decoder_members ce env sf tys tvs
      (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs
        (DROP (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))) bs)) vs /\
    vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) (pretys ++ tys)) bs bs /\
    abi_scratch_decoder_ranges opc base_op hi src dst B sb
      (LENGTH bs)
      d (SUM (MAP (type_memory_bytes ce) (pretys ++ tys))) first last b cap initial /\
    mem_bytes_at (B + sb) (LENGTH bs) (abi_decode_source opc initial) = bs /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    abi_decoder_operand_live st.cs_next_var hi /\
    abi_decoder_operand_live st.cs_next_var base_op /\ (base_op = Lit 0w \/ opc = MLOAD) /\
    abi_decoder_budget first last b cap initial /\ first <= abi_decoder_entry_floor st /\ final.cs_next_id <= last /\
    final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
    ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t n. tuple_in_memory vs tvs (d + SUM (MAP (type_memory_bytes ce) pretys)) t.vs_memory /\
      abi_scratch_effect first last (abi_decoder_entry_floor st) final.cs_next_id st.cs_next_var limit_st
        (d + SUM (MAP (type_memory_bytes ce) pretys))
        (SUM (MAP (type_memory_bytes ce) tys)) b cap initial t /\
      t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts /\
      ~t.vs_halted /\ gas_path ctx func initial n (OK t)
End

Theorem intcall_scratch_decoder_members_counted_run:
  intcall_scratch_decoder_members_counted ce env sf tys tvs /\
  compile_abi_decode_complex_elems dst src opc base_op hi (abi_decoder_member_infos sf ce tys)
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = ((),final) /\
  fn_has_code st final func /\
  (st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_members ce env sf tys tvs
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs
      (DROP (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))) bs)) vs /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) (pretys ++ tys)) bs bs /\
  abi_scratch_decoder_ranges opc base_op hi src dst B sb (LENGTH bs)
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ tys))) first last b cap initial /\
  mem_bytes_at (B + sb) (LENGTH bs) (abi_decode_source opc initial) = bs /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_operand_live st.cs_next_var base_op /\ (base_op = Lit 0w \/ opc = MLOAD) /\
  abi_decoder_budget first last b cap initial /\ first <= abi_decoder_entry_floor st /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t n. tuple_in_memory vs tvs (d + SUM (MAP (type_memory_bytes ce) pretys)) t.vs_memory /\
    abi_scratch_effect first last (abi_decoder_entry_floor st) final.cs_next_id st.cs_next_var limit_st
      (d + SUM (MAP (type_memory_bytes ce) pretys))
      (SUM (MAP (type_memory_bytes ce) tys)) b cap initial t /\
    t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~t.vs_halted /\ gas_path ctx func initial n (OK t)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `intcall_scratch_decoder_members_counted`
    (drule_all o PURE_REWRITE_RULE [intcall_scratch_decoder_members_counted_def]) >> simp[]
QED

Theorem intcall_scratch_decoder_members_counted_nil:
  intcall_scratch_decoder_members_counted ce env sf [] []
Proof
  simp_tac (srw_ss()) [intcall_scratch_decoder_members_counted_def, abi_decoder_member_infos_def,
    abi_decode_members_def, Once compile_abi_decode_to_buf_def, comp_return_def,
    Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  rpt gen_tac >> strip_tac >> gvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  `vs = []` by (Cases_on `vs` >> gvs[Once abi_decoder_members_def]) >>
  qexistsl_tac [`initial`, `0`] >>
  gvs[val_in_memory_def, gas_path_rules,
    Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  irule abi_scratch_leaf_effect >> simp[abi_decode_frame_def]
QED
