Theory abiEncoderChildPrefix
Ancestors
  abiEncoderChildCode abiEncoderBytesPrefix abiBuiltinPrefix abiDecoderDynamicLoopSetup
  abiDecoderReentry abiDecoderContract emitHelperProps exprLoweringProps compileEnv emitHelper
  venomState venomExecSemantics venomInst words list arithmetic abiDecoderLoop fragExec
  instIdxIndep rich_list

(* ===== Encoder Child Prefix ===== *)

(* Execute the actual dynamic child's head address and tail address setup. *)

Theorem abi_encode_child_prefix_live:
  abi_encode_child_prefix dst head_offset dyn_ptr st = (ops,st') ==>
  abi_decoder_operand_live st'.cs_next_var (FST ops) /\
  abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
  abi_decoder_operand_live st'.cs_next_var (SND (SND ops))
Proof
  simp_tac bool_ss [abi_encode_child_prefix_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op ADD [dst;Lit (n2w head_offset)] st = (head,c1)` >>
  rename1 `emit_op MLOAD [dyn_ptr] c1 = (offset,c2)` >>
  rename1 `emit_op ADD [dst;offset] c2 = (child_dst,ready)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  `c1.cs_next_var <= ready.cs_next_var /\ c2.cs_next_var <= ready.cs_next_var` by decide_tac >>
  rpt conj_tac
  >- (irule abi_decoder_operand_live_mono >> qexists_tac `c1.cs_next_var` >>
      conj_tac >- decide_tac >> first_assum ACCEPT_TAC)
  >- (irule abi_decoder_operand_live_mono >> qexists_tac `c2.cs_next_var` >>
      conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_child_prefix_sequence:
  abi_encode_child_prefix dst head_offset dyn_ptr st = (ops,st') /\
  eval_operand dst s = SOME (n2w db) /\ eval_operand dyn_ptr s = SOME (n2w slot) /\
  mload slot s = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dyn_ptr /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. eval_operand (FST ops) actual = SOME (n2w (db+head_offset)) /\
    eval_operand (FST (SND ops)) actual = SOME (n2w off) /\
    eval_operand (SND (SND ops)) actual = SOME (n2w (db+off)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
    abi_builtin_prefix st st' limit_st s actual
Proof
  strip_tac >> drule abi_encode_child_prefix_live >> strip_tac >>
  qpat_x_assum `abi_encode_child_prefix _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_encode_child_prefix_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op ADD [dst;Lit (n2w head_offset)] st = (head,c1)` >>
  rename1 `emit_op MLOAD [dyn_ptr] c1 = (offset,c2)` >>
  rename1 `emit_op ADD [dst;offset] c2 = (child_dst,ready)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  `c1.cs_next_var <= limit_st.cs_next_var /\ c2.cs_next_var <= limit_st.cs_next_var /\
    st.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`lhs` |-> `dst`, `rhs` |-> `Lit (n2w head_offset)`, `out` |-> `head`,
    `st'` |-> `c1`, `a` |-> `n2w db:bytes32`, `b` |-> `n2w head_offset:bytes32`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_builtin_prefix st c1 limit_st s headed` >>
  `eval_operand dyn_ptr headed = SOME (n2w slot) /\ fresh_vars_wrt limit_st headed` by
    fs[abi_builtin_prefix_def, abi_decoder_address_frame_def] >>
  mp_tac (Q.INST [`src` |-> `dyn_ptr`, `out` |-> `offset`, `p` |-> `n2w slot:bytes32`,
    `st` |-> `c1`, `st'` |-> `c2`,
    `s` |-> `headed:venom_state`] abi_builtin_emit_load) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_prefix c1 c2 limit_st headed loaded` >>
  `eval_operand offset loaded = SOME (n2w off) /\ fresh_vars_wrt limit_st loaded` by
    fs[abi_builtin_prefix_def, abi_decoder_address_frame_def, w2n_n2w, mload_def] >>
  `abi_builtin_prefix st c2 limit_st s loaded` by
    (irule abi_builtin_prefix_chain >> qexistsl_tac [`c1`, `headed`] >> asm_simp_tac bool_ss []) >>
  `eval_operand dst loaded = SOME (n2w db)` by fs[abi_builtin_prefix_def, abi_decoder_address_frame_def] >>
  mp_tac (Q.INST [`lhs` |-> `dst`, `rhs` |-> `offset`, `out` |-> `child_dst`,
    `st` |-> `c2`, `st'` |-> `ready`, `s` |-> `loaded:venom_state`,
    `a` |-> `n2w db:bytes32`, `b` |-> `n2w off:bytes32`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_prefix c2 ready limit_st loaded actual` >>
  `abi_builtin_prefix c1 ready limit_st headed actual` by
    (irule abi_builtin_prefix_chain >> qexistsl_tac [`c2`, `loaded`] >> asm_simp_tac bool_ss []) >>
  `abi_builtin_prefix st ready limit_st s actual` by
    (irule abi_builtin_prefix_chain >> qexistsl_tac [`c1`, `headed`] >> asm_simp_tac bool_ss []) >>
  `eval_operand head actual = SOME ((n2w db:bytes32)+n2w head_offset)` by
    (mp_tac (Q.INST [`st` |-> `c1`, `st'` |-> `ready`, `s` |-> `headed:venom_state`,
      `t` |-> `actual:venom_state`, `op` |-> `head`, `w` |-> `(n2w db:bytes32)+n2w head_offset`]
      abi_encoder_prefix_eval) >> asm_simp_tac bool_ss []) >>
  `eval_operand offset actual = SOME (n2w off)` by
    (mp_tac (Q.INST [`st` |-> `c2`, `st'` |-> `ready`, `s` |-> `loaded:venom_state`,
      `t` |-> `actual:venom_state`, `op` |-> `offset`, `w` |-> `n2w off:bytes32`]
      abi_encoder_prefix_eval) >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [word_add_n2w, ADD_COMM]
QED

(* ===== Reach ===== *)

(* Execute the dynamic child's address setup inside its containing function. *)

Theorem abi_encode_child_prefix_from_state:
  abi_encode_child_prefix dst head_offset dyn_ptr st = (ops,st') /\
  eval_operand dst initial = SOME (n2w db) /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dyn_ptr /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\t. eval_operand (FST ops) t = SOME (n2w (db+head_offset)) /\
      eval_operand (FST (SND ops)) t = SOME (n2w off) /\
      eval_operand (SND (SND ops)) t = SOME (n2w (db+off)) /\
      fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t) (K F)
Proof
  strip_tac >> drule abi_encode_child_prefix_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by
    (gvs[inst_extends_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_encode_child_prefix_sequence >> strip_tac >>
  rename1 `abi_builtin_prefix st st' limit_st initial actual` >> qexists_tac `actual` >>
  gvs[abi_builtin_prefix_def, abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem abi_encode_child_prefix_reach:
  abi_encode_child_prefix dst head_offset dyn_ptr st = (ops,st') /\ fn_has_code st st' func /\
  eval_operand dst initial = SOME (n2w db) /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dyn_ptr /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. eval_operand (FST ops) t = SOME (n2w (db+head_offset)) /\
    eval_operand (FST (SND ops)) t = SOME (n2w off) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (db+off)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_child_prefix_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `~actual.vs_halted` by fs[abi_decoder_address_frame_def] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
