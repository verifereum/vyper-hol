(* Execute a DecComplex guard and all typed heterogeneous members.
   TOP-LEVEL: abi_decoder_complex_execute. *)
Theory abiDecoderComplexExecute
Ancestors
  abiDecoderComplexCode abiDecoderComplexGuard abiDecoderComplexHead abiDecoderMemberInfos
  abiDecoderMemberCons abiDecoderMembersCorrect abiDecoderMembers abiDecoderCorrect
  abiDecoderArraySetupInputs abiDecoderArrayBody abiDecoderArrayInitExec
  abiDecoderDynamicLoopSetup abiDecoderEffect abiDecoderReentry abiDecoderAllocation
  abiDecoderLoop abiDecoderTypedContract abiDecoderContract abiDecodeRanges
  abiEncoder compileEnv valueEncoding vyperABI contractABI fragExec
  venomState venomExecSemantics words list arithmetic

Theorem abi_decoder_complex_execute:
  LIST_REL (abi_decoder_correct ce env sf) tys tvs /\
  compile_abi_decode_to_buf dst src opc hi (DecComplex dyn (abi_decoder_member_infos sf ce tys))
    st = ((),final) /\ fn_has_code st final func /\
  (st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_members ce env sf tys tvs avs vs /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))
    d (SUM (MAP (type_memory_bytes ce) tys)) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))
    (abi_decode_source opc initial) = enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. tuple_in_memory vs tvs d actual.vs_memory /\
    abi_decoder_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
      d (SUM (MAP (type_memory_bytes ce) tys)) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_complex_guard_inputs >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_complex_trace >> strip_tac >>
  rename1 `abi_decode_complex_head_guard src hi _ st = ((),middle)` >>
  drule_all abi_decoder_complex_code >> strip_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var /\ first <= middle.cs_next_id` by decide_tac >>
  mp_tac (Q.INST [`st'` |-> `middle`, `head_sz` |->
    `FOLDR (\(_,asz,_) acc. asz + acc) 0 (abi_decoder_member_infos sf ce tys)`]
    abi_decode_complex_head_guard_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  drule_all abi_decoder_address_frame_ranges >> strip_tac >>
  drule_all abi_decoder_address_frame_source >> disch_then (qspec_then `opc` assume_tac) >>
  `abi_decoder_budget first last b cap prepared` by
    (qpat_assum `abi_decoder_address_frame _ _ _`
      (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
     mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `prepared:venom_state`]
       abi_decoder_budget_transport) >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live middle.cs_next_var src /\ abi_decoder_operand_live middle.cs_next_var dst /\
   abi_decoder_operand_live middle.cs_next_var hi` by
    (rpt conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  drule abi_decoder_members_correct_list >> strip_tac >>
  mp_tac (SIMP_RULE bool_ss [MAP, SUM, APPEND, ADD_CLAUSES]
    (Q.INST [`st` |-> `middle`, `initial` |-> `prepared:venom_state`,
      `pretys` |-> `[]`, `pretvs` |-> `[]`, `preavs` |-> `[]`, `prevs` |-> `[]`]
      abi_decoder_members_correct_run)) >>
  impl_tac >- asm_simp_tac (srw_ss()) [Once abi_decoder_members_def, Excl "enc_def"] >>
  strip_tac >> rename1 `tuple_in_memory vs tvs d actual.vs_memory` >>
  `abi_decoder_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
    d (SUM (MAP (type_memory_bytes ce) tys)) b cap initial actual` by
    (mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `final.cs_next_id`,
      `next` |-> `st.cs_next_var`, `child_lo` |-> `middle.cs_next_id`,
      `child_next` |-> `middle.cs_next_var`, `s` |-> `initial:venom_state`,
      `prepared` |-> `prepared:venom_state`, `t` |-> `actual:venom_state`,
      `sz` |-> `SUM (MAP (type_memory_bytes ce) tys)`] abi_decoder_address_then_effect) >>
     asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED
