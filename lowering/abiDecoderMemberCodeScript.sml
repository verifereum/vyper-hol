(* Connect actual member setup to its containing function and exact endpoint.
   TOP-LEVEL: abi_decode_member_setup_reach.
   Helpers: emitted syntax and initial-state fragment. *)
Theory abiDecoderMemberCode
Ancestors
  abiDecoderMemberSetup abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderLoop
  abiDecoderContract fragExec instIdxIndep abiEncoder compileEnv emitHelper
  emitHelperProps exprLoweringProps venomState venomExecSemantics venomInst words list rich_list arithmetic

Theorem abi_decode_member_setup_shape:
  abi_decode_member_setup dst src opc hi dyn ao vo st = (ops,st') /\
  abi_decode_source_opcode opc ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\ st.cs_next_id < st'.cs_next_id /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    ~is_alloca_op i.inst_opcode) (emitted_insts st st') /\
  ?rest. st'.cs_current_insts = st.cs_current_insts ++
    mk_inst st.cs_next_id ADD [src; Lit (n2w ao)]
      [STRING #"%" (toString st.cs_next_var)] :: rest
Proof
  strip_tac >> Cases_on `dyn` >> gvs[abi_decode_source_opcode_def] >>
  Cases_on `hi = Lit 0w` >>
  gvs[abi_decode_member_setup_def, compile_getelemptr_abi_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def,
    IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  gvs[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def]
QED

Theorem abi_decode_member_setup_from_state:
  abi_decode_member_setup dst src opc hi dyn ao vo st = (ops,st') /\
  abi_decode_source_opcode opc /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  (dyn ==> abi_decode_load opc (n2w (sb + ao) : bytes32) initial = n2w payload_off /\
    sb + payload_off < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\t. eval_operand (FST ops) t = SOME (n2w (sb + if dyn then payload_off else ao)) /\
      eval_operand (SND ops) t = SOME (n2w (d + vo)) /\
      fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t) (K F)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decode_member_setup_reentry >> strip_tac >>
  qexists_tac `t` >>
  gvs[abi_decoder_address_frame_def, eval_op_inst_idx, fresh_vars_wrt_def]
QED

Theorem abi_decode_member_setup_reach:
  abi_decode_member_setup dst src opc hi dyn ao vo st = (ops,st') /\
  fn_has_code st st' func /\ abi_decode_source_opcode opc /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  (dyn ==> abi_decode_load opc (n2w (sb + ao) : bytes32) initial = n2w payload_off /\
    sb + payload_off < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. eval_operand (FST ops) t = SOME (n2w (sb + if dyn then payload_off else ao)) /\
    eval_operand (SND ops) t = SOME (n2w (d + vo)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_member_setup_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial t` >>
  `~t.vs_halted` by fs[abi_decoder_address_frame_def] >>
  qexists_tac `t` >> asm_simp_tac bool_ss []
QED
