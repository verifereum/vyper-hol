(* Actual length/rounded-pointer setup and return-size computation. *)
Theory abiEncoderBytesPrefix
Ancestors
  abiEncoderBytesCode abiEncoderRoundExecute abiBuiltinPrefix abiDecoderDynamicLoopSetup
  abiDecoderReentry abiDecoderContract emitHelperProps exprLoweringProps compileEnv emitHelper
  venomState venomExecSemantics venomInst words arithmetic list rich_list

Theorem abi_encode_bytes_prefix_shape:
  abi_encode_bytes_prefix dst src st = (ops,st') ==>
  st'.cs_next_var = st.cs_next_var + 4 /\ st'.cs_next_id = st.cs_next_id + 4 /\
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  inst_extends st st'
Proof
  simp[abi_encode_bytes_prefix_def, abi_encode_round_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND]
QED

Theorem abi_encoder_prefix_eval:
  abi_builtin_prefix st st' limit_st s t /\
  abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
  eval_operand op t = SOME w
Proof
  simp_tac bool_ss [abi_builtin_prefix_def, abi_decoder_address_frame_def] >>
  strip_tac >> first_x_assum irule >> asm_simp_tac bool_ss []
QED

Theorem abi_encode_bytes_prefix_sequence:
  abi_encode_bytes_prefix dst src st = (ops,st') /\
  eval_operand src s = SOME (n2w sb) /\ mload sb s = n2w cnt /\
  eval_operand dst s = SOME (n2w db) /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ cnt+31 < dimword (:256) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. eval_operand (FST ops) actual = SOME (n2w cnt) /\
    eval_operand (SND ops) actual = SOME (n2w (db+contractABI$ceil32 cnt)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (SND ops) /\
    abi_builtin_prefix st st' limit_st s actual
Proof
  simp_tac bool_ss [abi_encode_bytes_prefix_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op MLOAD [src] st = (len,c1)` >>
  rename1 `abi_encode_round len c1 = (rounded,c2)` >>
  rename1 `emit_op ADD [dst;rounded] c2 = (lastptr,ready)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_encode_round_shape >>
  imp_res_tac abi_decoder_operand_live_emit >>
  `c1.cs_next_var <= limit_st.cs_next_var /\ c2.cs_next_var <= limit_st.cs_next_var /\
   st.cs_next_var <= c1.cs_next_var /\ st.cs_next_var <= c2.cs_next_var /\
   c1.cs_next_var <= c2.cs_next_var /\ c1.cs_next_var <= ready.cs_next_var` by decide_tac >>
  `abi_decoder_operand_live ready.cs_next_var len` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `c1.cs_next_var` >> asm_simp_tac bool_ss []) >>
  drule_all abi_builtin_emit_load >> strip_tac >>
  rename1 `abi_builtin_prefix st c1 limit_st s loaded` >>
  `eval_operand len loaded = SOME (n2w cnt) /\ fresh_vars_wrt limit_st loaded` by
    fs[abi_builtin_prefix_def, w2n_n2w] >>
  mp_tac (Q.INST [`st` |-> `c1`, `st'` |-> `c2`, `s` |-> `loaded:venom_state`,
    `out` |-> `rounded`] abi_encode_round_sequence) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_prefix c1 c2 limit_st loaded prepared` >>
  `abi_builtin_prefix st c2 limit_st s prepared` by
    (irule abi_builtin_prefix_chain >> qexistsl_tac [`c1`, `loaded`] >> asm_simp_tac bool_ss []) >>
  `eval_operand dst prepared = SOME (n2w db) /\ fresh_vars_wrt limit_st prepared` by
    fs[abi_builtin_prefix_def, abi_decoder_address_frame_def] >>
  mp_tac (Q.INST [`lhs` |-> `dst`, `rhs` |-> `rounded`, `out` |-> `lastptr`,
    `a` |-> `n2w db:bytes32`, `b` |-> `n2w (contractABI$ceil32 cnt):bytes32`,
    `st` |-> `c2`, `st'` |-> `ready`, `s` |-> `prepared:venom_state`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_prefix c2 ready limit_st prepared actual` >>
  `abi_builtin_prefix st ready limit_st s actual` by
    (irule abi_builtin_prefix_chain >> qexistsl_tac [`c2`, `prepared`] >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live c2.cs_next_var len` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `c1.cs_next_var` >> asm_simp_tac bool_ss []) >>
  `eval_operand len prepared = SOME (n2w cnt)` by
    (mp_tac (Q.INST [`st` |-> `c1`, `st'` |-> `c2`, `s` |-> `loaded:venom_state`,
      `t` |-> `prepared:venom_state`, `op` |-> `len`, `w` |-> `n2w cnt:bytes32`]
      abi_encoder_prefix_eval) >> asm_simp_tac bool_ss []) >>
  `eval_operand len actual = SOME (n2w cnt)` by
    (mp_tac (Q.INST [`st` |-> `c2`, `st'` |-> `ready`, `s` |-> `prepared:venom_state`,
      `t` |-> `actual:venom_state`, `op` |-> `len`, `w` |-> `n2w cnt:bytes32`]
      abi_encoder_prefix_eval) >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [word_add_n2w]
QED

Theorem abi_encode_bytes_suffix_sequence:
  abi_encode_bytes_suffix len st = (out,st') /\ eval_operand len s = SOME (n2w cnt) /\
  cnt+31 < dimword (:256) /\ st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. eval_operand out actual = SOME (n2w (32+contractABI$ceil32 cnt)) /\
    abi_builtin_prefix st st' limit_st s actual
Proof
  simp_tac bool_ss [abi_encode_bytes_suffix_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_encode_round len st = (rounded,c1)` >>
  rename1 `emit_op ADD [Lit 32w;rounded] c1 = (out,ready)` >>
  drule abi_encode_round_shape >> strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `c1.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= c1.cs_next_var` by decide_tac >>
  drule_all abi_encode_round_sequence >> strip_tac >>
  rename1 `abi_builtin_prefix st c1 limit_st s prepared` >>
  `fresh_vars_wrt limit_st prepared` by fs[abi_builtin_prefix_def] >>
  mp_tac (Q.INST [`lhs` |-> `Lit 32w`, `rhs` |-> `rounded`, `a` |-> `32w:bytes32`,
    `b` |-> `n2w (contractABI$ceil32 cnt):bytes32`, `st` |-> `c1`, `st'` |-> `ready`,
    `s` |-> `prepared:venom_state`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_builtin_prefix c1 ready limit_st prepared actual` >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [word_add_n2w, ADD_COMM] >>
  irule abi_builtin_prefix_chain >> qexistsl_tac [`c1`, `prepared`] >> asm_simp_tac bool_ss []
QED
