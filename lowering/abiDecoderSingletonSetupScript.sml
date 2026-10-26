(* The actual outer head check and pointer setup for one dynamic member. *)
Theory abiDecoderSingletonSetup
Ancestors
  abiDecoderComplexHead abiDecoderMemberBound abiDecoderReservation abiDecoderGuard
  abiDecoderBytesBound abiDecoderGuards abiDecoderContract abiEncoder emitHelperProps
  exprLoweringProps compileEnv emitHelper venomExecSemantics venomState venomInst words
  arithmetic rich_list

Definition abi_decode_singleton_setup_def:
  abi_decode_singleton_setup dst src opc hi =
    do abi_decode_complex_head_guard src hi 32;
       child_src <- compile_getelemptr_abi src T 0 opc hi;
       child_dst <- emit_op ADD [dst; Lit 0w];
       return (child_src,child_dst)
    od
End

Definition abi_decode_singleton_setup_pre_def:
  abi_decode_singleton_setup_pre st src dst opc hi sb d s <=>
    abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
    eval_operand dst s = SOME (n2w d) /\
    abi_decode_load opc (n2w sb : bytes32) s = 32w /\
    sb + 32 < dimword (:256) /\ fresh_vars_wrt st s /\
    (hi = Lit 0w \/ ?hb. eval_operand hi s = SOME (n2w hb) /\
                        sb + 32 <= hb /\ hb < dimword (:256))
End

Theorem abi_decode_singleton_setup_sequence:
  abi_decode_singleton_setup dst src opc hi st = ((child_src,child_dst),st') /\
  abi_decode_singleton_setup_pre st src dst opc hi sb d s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand child_src t = SOME (n2w (sb + 32)) /\
    eval_operand child_dst t = SOME (n2w d) /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  simp_tac bool_ss [abi_decode_singleton_setup_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `abi_decode_complex_head_guard src hi 32 st = (guard_result,c1)` >>
  rename1 `compile_getelemptr_abi src T 0 opc hi c1 = (child_src,c2)` >>
  rename1 `emit_op ADD [dst; Lit 0w] c2 = (child_dst,st')` >>
  Cases_on `guard_result` >> gvs[] >>
  qpat_x_assum `abi_decode_singleton_setup_pre _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[abi_decode_singleton_setup_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`head_sz` |-> `32`, `st'` |-> `c1`]
    abi_decode_complex_head_guard_sequence) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME (n2w sb)` by metis_tac[] >>
  `abi_decode_load opc (n2w (sb + 0) : bytes32) s1 = n2w 32` by
    gvs[abi_decode_load_def, abi_decode_source_def, mload_def] >>
  mp_tac (Q.INST [`off` |-> `0`, `payload_off` |-> `32`, `member_op` |-> `child_src`,
    `st` |-> `c1`, `st'` |-> `c2`, `s` |-> `s1`]
    abi_decode_dynamic_member_pointer) >> impl_tac >- fs[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand dst s2 = SOME (n2w d)` by metis_tac[] >>
  `eval_operand (Lit 0w) s2 = SOME 0w` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 st') s2 = OK t` >>
  `run_inst_seq (emitted_insts c1 st') s1 = OK t /\ inst_extends c1 st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`, `c2`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  qexists_tac `t` >> gvs[] >> metis_tac[]
QED

Theorem abi_decode_singleton_setup_shape:
  abi_decode_singleton_setup dst src opc hi st = ((child_src,child_dst),st') /\
  abi_decode_source_opcode opc ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  st.cs_next_id <= st'.cs_next_id /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             ~is_alloca_op i.inst_opcode) (emitted_insts st st')
Proof
  strip_tac >> gvs[abi_decode_source_opcode_def] >> Cases_on `hi = Lit 0w` >>
  gvs[abi_decode_singleton_setup_def, abi_decode_complex_head_guard_def,
      abi_decode_le_guard_def, compile_getelemptr_abi_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
      emit_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, is_terminator_def, is_alloca_op_def, mk_inst_def]
QED

Theorem abi_decode_complex_nil:
  compile_abi_decode_complex_elems dst src opc hi [] aoff voff = return ()
Proof
  simp[compile_abi_decode_to_buf_def]
QED
