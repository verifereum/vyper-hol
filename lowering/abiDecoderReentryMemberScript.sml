(* Member navigation preserves observations when decoder temporaries are reused.
   TOP-LEVEL: abi_decoder_member_pointer_reentry.
   Helpers: opcode certificate and fresh-state sequence execution. *)
Theory abiDecoderReentryMember
Ancestors
  abiDecoderReentryPrefix abiDecoderReentry abiDecoderVarSequence abiDecoderVarExtend
  abiDecoderMemberBound abiDecoderMemberPtr abiDecoderReservation abiDecoderContract
  abiEncoder emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState venomInst words list rich_list arithmetic

Theorem abi_decoder_member_pointer_code:
  compile_getelemptr_abi src dyn off opc hi st = (member_op,st') /\
  abi_decode_source_opcode opc ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')
Proof
  strip_tac >> Cases_on `dyn` >> gvs[abi_decode_source_opcode_def] >>
  Cases_on `hi = Lit 0w` >>
  gvs[compile_getelemptr_abi_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, abi_decoder_reentry_opcode_def, mk_inst_def]
QED

Theorem abi_decoder_member_pointer_counters:
  compile_getelemptr_abi src dyn off opc hi st = (member_op,st') ==>
  st'.cs_next_var = st.cs_next_var + (if dyn then if hi = Lit 0w then 3 else 5 else 1) /\
  abi_decoder_operand_live st'.cs_next_var member_op
Proof
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >>
  simp[compile_getelemptr_abi_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  imp_res_tac abi_decoder_operand_live_emit >> gvs[] >>
  FIRST [first_assum ACCEPT_TAC,
    irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var + 3` >>
    conj_tac >- decide_tac >> first_assum ACCEPT_TAC]
QED

Theorem abi_decoder_member_pointer_sequence:
  compile_getelemptr_abi src dyn off opc hi st = (member_op,st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  (dyn ==> abi_decode_load opc (n2w (sb + off) : bytes32) s = n2w payload_off /\
    sb + payload_off < dimword (:256)) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand member_op t = SOME (n2w (sb + if dyn then payload_off else off)) /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  Cases_on `dyn` >> simp_tac bool_ss [] >> strip_tac >>
  FIRST [drule_all abi_decode_static_member_pointer >> simp[],
    drule_all abi_decode_dynamic_member_pointer >> simp[]]
QED

Theorem abi_decoder_member_pointer_reentry:
  compile_getelemptr_abi src dyn off opc hi st = (member_op,st') /\
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  (dyn ==> abi_decode_load opc (n2w (sb + off) : bytes32) initial = n2w payload_off /\
    sb + payload_off < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    eval_operand member_op actual = SOME (n2w (sb + if dyn then payload_off else off)) /\
    fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_memory = initial.vs_memory /\ actual.vs_call_ctx = initial.vs_call_ctx /\
    actual.vs_data_section = initial.vs_data_section /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\ inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand src (abi_decoder_prune_vars st.cs_next_var initial) = SOME (n2w sb)`
    by asm_simp_tac bool_ss [abi_decoder_prune_eval] >>
  `dyn ==> abi_decode_load opc (n2w (sb + off) : bytes32)
      (abi_decoder_prune_vars st.cs_next_var initial) = n2w payload_off /\
    sb + payload_off < dimword (:256)` by
    fs[abi_decode_load_def, abi_decode_source_def, abi_decoder_prune_vars_def, mload_def] >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var initial)`
    by irule abi_decoder_prune_fresh >>
  mp_tac (Q.INST [`s` |-> `abi_decoder_prune_vars st.cs_next_var initial`]
    abi_decoder_member_pointer_sequence) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st')
    (abi_decoder_prune_vars st.cs_next_var initial) = OK clean` >>
  drule_all abi_decoder_member_pointer_code >> strip_tac >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  rename1 `abi_decoder_vars_extend initial.vs_vars clean actual` >>
  drule_all abi_decoder_vars_extend_eval >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  `dyn ==> abi_decode_source_opcode opc` by simp[] >>
  drule_all abi_decode_member_pointer_allocation_shape >> strip_tac >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  qexists_tac `actual` >> gvs[abi_decoder_prune_vars_def]
QED
