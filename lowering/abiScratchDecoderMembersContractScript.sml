(* Physical execution contract for a suffix of heterogeneous members.
   Source validity and child metadata describe actual slices at every cursor. *)
Theory abiScratchDecoderMembersContract
Ancestors
  abiScratchDecoderContract abiScratchEncoderContract abiScratchLeafEffect abiDecoderFrame
  abiDecoderMemberInfos abiDecoderMembers abiValidMembers abiDecoderValidContract abiDecoderEffect
  abiDecoderReentry abiDecoderLoop abiDecoderTypedContract abiDecoderContract
  abiDecodeRanges abiEncoder compileEnv valueEncoding vyperABI fragExec
  venomState venomExecSemantics words list arithmetic

Definition abi_scratch_decoder_members_def:
  abi_scratch_decoder_members ce env sf tys tvs <=>
    !dst src opc hi st final func ctx first last b cap limit_st initial
      pretys bs vs sb d.
    compile_abi_decode_complex_elems dst src opc hi (abi_decoder_member_infos sf ce tys)
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
    abi_scratch_decoder_ranges opc hi src dst sb
      (LENGTH bs)
      d (SUM (MAP (type_memory_bytes ce) (pretys ++ tys))) first last b cap initial /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) =
      bs /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    abi_decoder_operand_live st.cs_next_var hi /\
    abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ final.cs_next_id <= last /\
    final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
    ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. tuple_in_memory vs tvs (d + SUM (MAP (type_memory_bytes ce) pretys)) t.vs_memory /\
      abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
        (d + SUM (MAP (type_memory_bytes ce) pretys))
        (SUM (MAP (type_memory_bytes ce) tys)) b cap initial t /\
      t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts /\
      ~t.vs_halted /\ abi_decode_sim ctx func initial t
End

Theorem abi_scratch_decoder_members_run:
  abi_scratch_decoder_members ce env sf tys tvs /\
  compile_abi_decode_complex_elems dst src opc hi (abi_decoder_member_infos sf ce tys)
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
  abi_scratch_decoder_ranges opc hi src dst sb
    (LENGTH bs)
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ tys))) first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) =
    bs /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. tuple_in_memory vs tvs (d + SUM (MAP (type_memory_bytes ce) pretys)) t.vs_memory /\
    abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
      (d + SUM (MAP (type_memory_bytes ce) pretys))
      (SUM (MAP (type_memory_bytes ce) tys)) b cap initial t /\
    t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  strip_tac >> qpat_x_assum `abi_scratch_decoder_members _ _ _ _ _`
    (mp_tac o PURE_REWRITE_RULE [abi_scratch_decoder_members_def]) >>
  disch_then (qspecl_then [`dst`, `src`, `opc`, `hi`, `st`, `final`, `func`, `ctx`,
    `first`, `last`, `b`, `cap`, `limit_st`, `initial`, `pretys`, `bs`, `vs`, `sb`, `d`] mp_tac) >> asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decoder_members_nil:
  abi_scratch_decoder_members ce env sf [] []
Proof
  simp_tac (srw_ss()) [abi_scratch_decoder_members_def, abi_decoder_member_infos_def,
    abi_decode_members_def, Once compile_abi_decode_to_buf_def, comp_return_def,
    Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  rpt gen_tac >> strip_tac >> gvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  `vs = []` by (Cases_on `vs` >> gvs[Once abi_decoder_members_def]) >>
  qexists_tac `initial` >>
  gvs[val_in_memory_def, abi_decode_sim_refl,
    Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  irule abi_scratch_leaf_effect >> simp[abi_decode_frame_def]
QED
