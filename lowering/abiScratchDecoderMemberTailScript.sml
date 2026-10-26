(* Execute a member suffix with physical framing of its completed head. *)
Theory abiScratchDecoderMemberTail
Ancestors
  abiScratchDecoderMembersContract abiDecoderValidMemberCursor abiDecoderMemberFrames
  abiScratchDecoderMemberFrames abiScratchDecoderContract abiScratchFootprint abiEncoderArrayFrame
  abiDecoderMembers abiDecoderCoherence abiDecoderTypedContract abiDecoderEffect
  abiDecoderReentry abiDecoderContract abiDecodeRanges abiValidMembers compileEnv valueEncoding
  vyperABI vyperValue vyperTyping venomState words list arithmetic

val member_cursor_rewrites = [MAP_APPEND, MAP, SUM_APPEND, SUM,
  GSYM APPEND_ASSOC, APPEND, GSYM ADD_ASSOC, ADD_CLAUSES];

Theorem abi_scratch_decoder_member_tail_execute:
  abi_scratch_decoder_members ce env sf tys tvs /\
  compile_abi_decode_complex_elems dst src opc hi (abi_decoder_member_infos sf ce tys)
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)) +
      abi_embedded_static_size ce.ce_struct_fields ty)
    (SUM (MAP (type_memory_bytes ce) pretys) + type_memory_bytes ce ty) st = ((),final) /\
  fn_has_code st final func /\
  (st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs)
    (abi_decode_members (MAP (vyper_to_abi_type env) (ty::tys)) bs
      (DROP (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))) bs)) (v::vs) /\
  valid_enc_tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) bs bs /\
  abi_scratch_decoder_ranges opc hi src dst sb
    (LENGTH bs)
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) =
    bs /\
  val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) initial.vs_memory /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. tuple_in_memory (v::vs) (tv::tvs) (d + SUM (MAP (type_memory_bytes ce) pretys)) t.vs_memory /\
    abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
      (d + SUM (MAP (type_memory_bytes ce) pretys) + type_memory_bytes ce ty)
      (SUM (MAP (type_memory_bytes ce) tys)) b cap initial t /\
    t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_valid_member_cursor >> strip_tac >>
  qpat_assum `abi_embedded_static_size ce.ce_struct_fields ty = _`
    (fn hdr => RULE_ASSUM_TAC (PURE_REWRITE_RULE (hdr :: member_cursor_rewrites))) >>
  mp_tac (PURE_REWRITE_RULE member_cursor_rewrites
    (Q.INST [`pretys` |-> `pretys ++ [ty]`] abi_scratch_decoder_members_run)) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  strip_tac >> rename1 `abi_decode_sim ctx func initial t` >>
  `abi_footprint_disjoint (d + SUM (MAP (type_memory_bytes ce) pretys))
    (type_memory_size tv)
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    (qpat_assum `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`
      (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_ranges_def]) >>
     irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`d`, `SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))`] >>
     RULE_ASSUM_TAC (SIMP_RULE arith_ss [MAP_APPEND, MAP, SUM_APPEND, SUM]) >>
     asm_simp_tac arith_ss [MAP_APPEND, MAP, SUM_APPEND, SUM]) >>
  mp_tac (Q.INST [`cell` |-> `d + SUM (MAP (type_memory_bytes ce) pretys)`,
    `restsz` |-> `SUM (MAP (type_memory_bytes ce) tys)`, `lo` |-> `st.cs_next_id`,
    `hi` |-> `final.cs_next_id`, `next` |-> `st.cs_next_var`, `s` |-> `initial:venom_state`]
    abi_scratch_decoder_suffix_preserves_head) >>
  impl_tac >- gvs[abi_decoder_metadata_def, MAP_APPEND, SUM_APPEND, Excl "enc_def"] >> strip_tac >>
  qexists_tac `t` >> gvs[MAP_APPEND, SUM_APPEND, Excl "enc_def"] >>
  simp_tac (srw_ss()) [Once val_in_memory_def, Excl "enc_def"] >> gvs[Excl "enc_def"]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODER_MEMBER_TAIL_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical member tail not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecoderMemberTail");

