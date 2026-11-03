(* The actual dynamic-array body loads its cursor, then computes the child tail.
   TOP-LEVEL: abi_encode_array_tail, its shape, sequence and CFG reach.
   This phase follows the shared seven-instruction source/head address prefix. *)
Theory abiEncoderArrayTail
Ancestors
  abiEncoderBytesPrefix abiBuiltinPrefix abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderContract abiDecoderLoop fragExec instIdxIndep emitHelperProps exprLoweringProps
  compileEnv emitHelper venomExecSemantics venomState venomInst words list rich_list arithmetic
Libs monadsyntax

Definition abi_encode_array_tail_def:
  abi_encode_array_tail data_op dyn_ptr =
    do offset <- emit_op MLOAD [dyn_ptr];
       child_dst <- emit_op ADD [data_op;offset];
       return (offset,child_dst)
    od
End

Theorem abi_encode_array_tail_shape:
  abi_encode_array_tail data_op dyn_ptr st = (ops,st') ==>
  st'.cs_next_var = st.cs_next_var+2 /\ st'.cs_next_id = st.cs_next_id+2 /\
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' /\
  abi_decoder_operand_live st'.cs_next_var (FST ops) /\
  abi_decoder_operand_live st'.cs_next_var (SND ops) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')
Proof
  simp[abi_encode_array_tail_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND, abi_decoder_operand_live_def,
    abi_decoder_older_vars_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def] >>
  rpt strip_tac >> decide_tac
QED

Theorem abi_encode_array_tail_sequence:
  abi_encode_array_tail data_op dyn_ptr st = (ops,st') /\
  eval_operand data_op initial = SOME (n2w d) /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data_op /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. eval_operand (FST ops) actual = SOME (n2w off) /\
    eval_operand (SND ops) actual = SOME (n2w (d+off)) /\
    abi_builtin_prefix st st' limit_st initial actual
Proof
  simp_tac bool_ss [abi_encode_array_tail_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op MLOAD [dyn_ptr] st = (offset,middle)` >>
  rename1 `emit_op ADD [data_op;offset] middle = (child_dst,final)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  `middle.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= middle.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`src` |-> `dyn_ptr`, `out` |-> `offset`, `st'` |-> `middle`,
    `s` |-> `initial:venom_state`, `p` |-> `n2w slot:bytes32`] abi_builtin_emit_load) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_prefix st middle limit_st initial loaded` >>
  `eval_operand offset loaded = SOME (n2w off) /\ fresh_vars_wrt limit_st loaded` by
    full_simp_tac (srw_ss()) [abi_builtin_prefix_def, w2n_n2w] >>
  `eval_operand data_op loaded = SOME (n2w d)` by
    (mp_tac (Q.INST [`st'` |-> `middle`, `s` |-> `initial:venom_state`,
      `t` |-> `loaded:venom_state`, `op` |-> `data_op`, `w` |-> `n2w d:bytes32`]
      abi_encoder_prefix_eval) >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`lhs` |-> `data_op`, `rhs` |-> `offset`, `out` |-> `child_dst`,
    `st` |-> `middle`, `st'` |-> `final`, `s` |-> `loaded:venom_state`,
    `a` |-> `n2w d:bytes32`, `b` |-> `n2w off:bytes32`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_prefix middle final limit_st loaded actual` >>
  `eval_operand offset actual = SOME (n2w off)` by
    (mp_tac (Q.INST [`st` |-> `middle`, `st'` |-> `final`, `s` |-> `loaded:venom_state`,
      `t` |-> `actual:venom_state`, `op` |-> `offset`, `w` |-> `n2w off:bytes32`]
      abi_encoder_prefix_eval) >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [word_add_n2w] >>
  irule abi_builtin_prefix_chain >> qexistsl_tac [`middle`, `loaded`] >> asm_simp_tac bool_ss []
QED

Theorem abi_encode_array_tail_from_state:
  abi_encode_array_tail data_op dyn_ptr st = (ops,st') /\
  eval_operand data_op initial = SOME (n2w d) /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data_op /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\t. eval_operand (FST ops) t = SOME (n2w off) /\
      eval_operand (SND ops) t = SOME (n2w (d+off)) /\
      fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t) (K F)
Proof
  strip_tac >> drule abi_encode_array_tail_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by
    (gvs[inst_extends_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_encode_array_tail_sequence >> strip_tac >>
  rename1 `abi_builtin_prefix st st' limit_st initial actual` >> qexists_tac `actual` >>
  gvs[abi_builtin_prefix_def, abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem abi_encode_array_tail_reach:
  abi_encode_array_tail data_op dyn_ptr st = (ops,st') /\ fn_has_code st st' func /\
  eval_operand data_op initial = SOME (n2w d) /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data_op /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand (FST ops) actual = SOME (n2w off) /\
    eval_operand (SND ops) actual = SOME (n2w (d+off)) /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_tail_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `~actual.vs_halted` by fs[abi_decoder_address_frame_def] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
