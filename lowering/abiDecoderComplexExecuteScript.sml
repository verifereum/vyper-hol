Theory abiDecoderComplexExecute
Ancestors
  abiDecoderComplexGuard abiDecoderComplexHead abiDecoderMemberInfos abiDecoderMemberCons
  abiDecoderMembers abiDecoderCoherence abiDecoderTypedContract abiDecoderCode
  abiDecoderContract abiDecodeRanges abiDecoderAppend abiEncoder fragExec compileEnv emitHelper
  valueEncoding vyperABI contractABI venomState words list arithmetic abiDecoderMembersCorrect
  abiDecoderCorrect abiDecoderArraySetupInputs abiDecoderArraySetupCode abiDecoderArrayInitExec
  abiDecoderDynamicLoopSetup abiDecoderEffect abiDecoderReentry abiDecoderAllocation
  abiDecoderLoop venomExecSemantics

(* Actual complex-decoder phases and canonical inputs for its head guard.
   TOP-LEVEL: abi_decoder_complex_trace, abi_decoder_complex_code,
     abi_decoder_complex_guard_inputs. *)
Theorem abi_decoder_complex_trace:
  compile_abi_decode_to_buf dst src opc hi (DecComplex dyn infos) st = ((),final) ==>
  ?middle. abi_decode_complex_head_guard src hi (FOLDR (\(_,asz,_) acc. asz + acc) 0 infos)
      st = ((),middle) /\
    compile_abi_decode_complex_elems dst src opc hi infos 0 0 middle = ((),final)
Proof
  simp_tac bool_ss [abi_decode_complex_phases, comp_ignore_bind_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_complex_head_guard src hi _ st = ((),middle)` >>
  qexists_tac `middle` >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_complex_code:
  abi_decode_complex_head_guard src hi head_sz st = ((),middle) /\
  compile_abi_decode_complex_elems dst src opc hi infos 0 0 middle = ((),final) /\
  abi_decode_source_opcode opc /\ fn_has_code st final func ==>
  fn_has_code st middle func /\ fn_has_code middle final func /\
  cs_extends st middle /\ cs_extends middle final /\ middle.cs_blocks = st.cs_blocks /\
  st.cs_next_id <= middle.cs_next_id /\ middle.cs_next_id <= final.cs_next_id /\
  st.cs_next_var <= middle.cs_next_var /\ middle.cs_next_var <= final.cs_next_var
Proof
  strip_tac >> drule abi_decoder_complex_guard_code >> strip_tac >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  `cs_extends st middle` by (irule cs_extends_same_block >> simp[]) >>
  drule abi_decoder_members_extends >> strip_tac >>
  mp_tac (Q.SPECL [`st`, `middle`, `final`, `func`] fn_has_code_split) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_decoder_complex_elems_code >>
  simp_tac bool_ss [abi_decoder_code_def] >> strip_tac >>
  Cases_on `hi = Lit 0w` >> gvs[]
QED

Theorem abi_decoder_complex_guard_inputs:
  abi_decoder_members ce env sf tys tvs avs vs /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))
    d (SUM (MAP (type_memory_bytes ce) tys)) b cap initial ==>
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb + FOLDR (\(_,asz,_) acc. asz + acc) 0 (abi_decoder_member_infos sf ce tys) <= hb /\
    hb < dimword (:256))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_members_relations >> strip_tac >>
  drule abi_decoder_member_infos_layout >> strip_tac >>
  `has_types (MAP (vyper_to_abi_type env) tys) avs` by fs[has_types_LIST_REL] >>
  drule canonical_tuple_length >> strip_tac >>
  `FOLDR (\(_,asz,_) acc. asz + acc) 0 (abi_decoder_member_infos sf ce tys) <=
    LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs))` by
    (gvs[Excl "enc_def"] >> decide_tac) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  asm_simp_tac bool_ss [] >> Cases_on `hi = Lit 0w` >- simp[] >>
  qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `eval_operand hi initial = SOME (n2w hb)` >>
  qexists_tac `hb` >> asm_simp_tac bool_ss [] >> decide_tac
QED

(* Execute a DecComplex guard and all typed heterogeneous members.
   TOP-LEVEL: abi_decoder_complex_execute. *)
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
