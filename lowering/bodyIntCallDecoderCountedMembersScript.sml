(* Counted heterogeneous member composition with physical sibling preservation. *)
Theory bodyIntCallDecoderCountedMembers
Ancestors
  bodyIntCallDecoderCountedMembersContract bodyIntCallDecoderCountedContract
  bodyIntCallDecoderCountedDispatch abiScratchDecoderMemberCons abiScratchDecoderMemberTail
  abiDecoderMembersCode abiScratchDecoderMemberFrames abiDecoderValidMemberCursor abiDecoderMemberFrames
  abiScratchDecoderContract abiScratchFootprint abiEncoderArrayFrame abiDecoderMembers
  abiDecoderCoherence abiDecoderTypedContract abiDecoderEffect abiDecoderReentry
  abiDecoderContract abiDecodeRanges abiValidMembers compileEnv valueEncoding
  vyperABI vyperValue vyperTyping fragGasPath venomState venomExecSemantics words list arithmetic

val counted_cursor_rewrites = [MAP_APPEND, MAP, SUM_APPEND, SUM,
  GSYM APPEND_ASSOC, APPEND, GSYM ADD_ASSOC, ADD_CLAUSES];

Theorem intcall_scratch_decoder_member_tail_path:
  intcall_scratch_decoder_members_counted ce env sf tys tvs /\
  compile_abi_decode_complex_elems dst src opc base_op hi (abi_decoder_member_infos sf ce tys)
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
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) bs bs /\
  abi_scratch_decoder_ranges opc base_op hi src dst B sb (LENGTH bs)
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) first last b cap initial /\
  mem_bytes_at (B + sb) (LENGTH bs) (abi_decode_source opc initial) = bs /\
  val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) initial.vs_memory /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_operand_live st.cs_next_var base_op /\ (base_op = Lit 0w \/ opc = MLOAD) /\
  abi_decoder_budget first last b cap initial /\ first <= abi_decoder_entry_floor st /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t n. tuple_in_memory (v::vs) (tv::tvs) (d + SUM (MAP (type_memory_bytes ce) pretys)) t.vs_memory /\
    abi_scratch_effect first last (abi_decoder_entry_floor st) final.cs_next_id st.cs_next_var limit_st
      (d + SUM (MAP (type_memory_bytes ce) pretys) + type_memory_bytes ce ty)
      (SUM (MAP (type_memory_bytes ce) tys)) b cap initial t /\
    t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~t.vs_halted /\ gas_path ctx func initial n (OK t)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_valid_member_cursor >> strip_tac >>
  qpat_assum `abi_embedded_static_size ce.ce_struct_fields ty = _`
    (fn hdr => RULE_ASSUM_TAC (PURE_REWRITE_RULE (hdr :: counted_cursor_rewrites))) >>
  mp_tac (PURE_REWRITE_RULE counted_cursor_rewrites
    (Q.INST [`pretys` |-> `pretys ++ [ty]`] intcall_scratch_decoder_members_counted_run)) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  strip_tac >> rename1 `gas_path ctx func initial n (OK t)` >>
  `abi_footprint_disjoint (d + SUM (MAP (type_memory_bytes ce) pretys))
    (type_memory_size tv)
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    (qhdtm_assum `abi_scratch_decoder_ranges`
      (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_ranges_def]) >>
     irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`d`, `SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))`] >>
     RULE_ASSUM_TAC (SIMP_RULE arith_ss [MAP_APPEND, MAP, SUM_APPEND, SUM]) >>
     asm_simp_tac arith_ss [MAP_APPEND, MAP, SUM_APPEND, SUM]) >>
  `value_has_type tv v /\ type_memory_size tv = type_memory_bytes ce ty` by
    fs[abi_decoder_metadata_def] >>
  `val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) t.vs_memory` by
    (qpat_assum `type_memory_size tv = _`
       (fn sz => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM sz, ADD_ASSOC])) >>
     drule_all abi_scratch_decoder_suffix_preserves_head >> simp[]) >>
  qexistsl_tac [`t`, `n`] >> gvs[MAP_APPEND, SUM_APPEND, Excl "enc_def"] >>
  simp_tac (srw_ss()) [Once val_in_memory_def, Excl "enc_def"] >> gvs[Excl "enc_def"]
QED

Theorem intcall_scratch_decoder_members_counted_cons:
  intcall_scratch_decoder_counted ce env sf ty tv /\
  intcall_scratch_decoder_members_counted ce env sf tys tvs ==>
  intcall_scratch_decoder_members_counted ce env sf (ty::tys) (tv::tvs)
Proof
  strip_tac >> rewrite_tac [intcall_scratch_decoder_members_counted_def] >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_members_lengths >> strip_tac >>
  Cases_on `vs` >- fs[] >> rename1 `v::vs` >>
  drule abi_decoder_valid_member_cursor >> strip_tac >>
  `abi_decode_source_opcode opc` by fs[abi_scratch_decoder_ranges_def, Excl "enc_def"] >>
  drule_all abi_decoder_members_cons_code >>
  disch_then (qx_choose_then `ops` (qx_choose_then `middle` (qx_choose_then `end_st`
    (MAP_EVERY assume_tac o CONJUNCTS)))) >>
  `end_st.cs_next_id <= last /\ first <= abi_decoder_entry_floor end_st /\
   abi_decoder_entry_floor st <= abi_decoder_entry_floor end_st /\
   end_st.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= end_st.cs_next_var`
    by (fs[abi_decoder_entry_floor_def] >> decide_tac) >>
  mp_tac (SIMP_RULE bool_ss [LET_THM]
    (Q.INST [`ready` |-> `middle`, `pre` |-> `MAP (vyper_to_abi_type env) pretys`,
      `ats` |-> `MAP (vyper_to_abi_type env) tys`,
      `vo` |-> `SUM (MAP (type_memory_bytes ce) pretys)`,
      `outsz` |-> `SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))`]
      intcall_scratch_decoder_member_body_path)) >>
  impl_tac >- (RULE_ASSUM_TAC (SIMP_RULE arith_ss [MAP_APPEND, MAP, SUM_APPEND, SUM]) >>
    asm_simp_tac arith_ss [MAP_APPEND, MAP, SUM_APPEND, SUM]) >>
  strip_tac >> rename1 `gas_path ctx func initial n (OK after_head)` >>
  mp_tac (Q.INST [`hi_op` |-> `hi:operand`] abi_scratch_decoder_member_after_head) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`st` |-> `end_st`, `initial` |-> `after_head:venom_state`]
    intcall_scratch_decoder_member_tail_path) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  strip_tac >> rename1 `gas_path ctx func after_head n' (OK actual)` >>
  drule_all abi_scratch_decoder_member_effects_compose >> strip_tac >>
  qexistsl_tac [`actual`, `n + n'`] >> asm_simp_tac bool_ss [MAP, SUM] >>
  irule gas_path_then >> goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_scratch_decoder_members_counted_list:
  !tys tvs. LIST_REL (intcall_scratch_decoder_counted ce env sf) tys tvs ==>
    intcall_scratch_decoder_members_counted ce env sf tys tvs
Proof
  Induct >> Cases_on `tvs` >> simp[intcall_scratch_decoder_members_counted_nil] >>
  metis_tac[intcall_scratch_decoder_members_counted_cons]
QED
