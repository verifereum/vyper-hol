(* Execute the actual ABI builtin header in its containing function.
   TOP-LEVEL: abi_builtin_decode_header_reach.
   Helper: the pointed header fragment. *)
Theory abiBuiltinHeaderReach
Ancestors
  abiBuiltinDecodeHeader abiBuiltinPrefix abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderContract abiDecoderLoop fragExec instIdxIndep compileEnv emitHelperProps
  venomExecSemantics venomState venomInst words list

Theorem abi_builtin_decode_header_from_state:
  abi_builtin_decode_header data min_size max_size st = (inputs,st') /\
  eval_operand data initial = SOME p /\ mload (w2n p) initial = n2w cnt /\
  min_size <= cnt /\ cnt <= max_size /\ max_size < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\t. eval_operand (FST inputs) t = SOME (n2w cnt) /\
      eval_operand (SND inputs) t = SOME (p + 32w) /\ fresh_vars_wrt limit_st t /\
      abi_decoder_address_frame st.cs_next_var initial t) (K F)
Proof
  strip_tac >> drule abi_builtin_decode_header_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_builtin_decode_header >> strip_tac >>
  rename1 `abi_builtin_prefix st st' limit_st initial actual` >>
  qexists_tac `actual` >>
  gvs[abi_builtin_prefix_def, abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem abi_builtin_decode_header_reach:
  abi_builtin_decode_header data min_size max_size st = (inputs,st') /\ fn_has_code st st' func /\
  eval_operand data initial = SOME p /\ mload (w2n p) initial = n2w cnt /\
  min_size <= cnt /\ cnt <= max_size /\ max_size < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. eval_operand (FST inputs) t = SOME (n2w cnt) /\
    eval_operand (SND inputs) t = SOME (p + 32w) /\ fresh_vars_wrt limit_st t /\
    abi_decoder_address_frame st.cs_next_var initial t /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_decode_header_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `~actual.vs_halted` by fs[abi_decoder_address_frame_def] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
