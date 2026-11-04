(* Execute the actual singleton setup with its decoded, noncanonical offset. *)
Theory abiValidSingletonSetup
Ancestors
  abiDecoderSingletonSetup abiDecoderComplexHead abiDecoderMemberBound abiDecoderBytesBound
  abiDecoderGuards abiDecoderContract abiEncoder emitHelper emitHelperProps
  exprLoweringProps compileEnv venomExecSemantics venomState words arithmetic

Definition abi_valid_singleton_setup_pre_def:
  abi_valid_singleton_setup_pre st src dst opc hi sb d offset s <=>
    abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
    eval_operand dst s = SOME (n2w d) /\
    abi_decode_load opc (n2w sb:bytes32) s = n2w offset /\
    sb + offset < dimword (:256) /\ fresh_vars_wrt st s /\
    (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
       sb + 32 <= h /\ h < dimword (:256))
End

Theorem abi_valid_singleton_setup_sequence:
  abi_decode_singleton_setup dst src opc hi st = ((child_src,child_dst),st') /\
  abi_valid_singleton_setup_pre st src dst opc hi sb d offset s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand child_src t = SOME (n2w (sb + offset)) /\
    eval_operand child_dst t = SOME (n2w d) /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  simp_tac bool_ss [abi_decode_singleton_setup_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_decode_complex_head_guard src hi 32 st = (guard_result,c1)` >>
  rename1 `compile_getelemptr_abi src T 0 opc hi c1 = (child_src,c2)` >>
  rename1 `emit_op ADD [dst; Lit 0w] c2 = (child_dst,st')` >>
  Cases_on `guard_result` >> gvs[] >>
  qpat_x_assum `abi_valid_singleton_setup_pre _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[abi_valid_singleton_setup_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`head_sz` |-> `32`, `st'` |-> `c1`]
    abi_decode_complex_head_guard_sequence) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME (n2w sb)` by metis_tac[] >>
  `abi_decode_load opc (n2w (sb + 0):bytes32) s1 = n2w offset` by
    gvs[abi_decode_load_def, abi_decode_source_def, mload_def] >>
  mp_tac (Q.INST [`off` |-> `0`, `payload_off` |-> `offset`, `member_op` |-> `child_src`,
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
