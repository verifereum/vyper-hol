(* Bounded member navigation: the emitted pointer followed by its no-wrap guard. *)
Theory abiDecoderMemberBound
Ancestors
  abiDecoderMemberPtr abiDecoderGuardGE abiDecoderGuards abiDecoderContract
  abiEncoder compileEnv emitHelper venomExecSemantics venomState words arithmetic

Theorem abi_decode_bounded_member_phases:
  hi <> Lit 0w ==>
  compile_getelemptr_abi src T off opc hi =
    do member_op <- compile_getelemptr_abi src T off opc (Lit 0w);
       abi_decode_ge_guard member_op src;
       return member_op
    od
Proof
  strip_tac >>
  simp[FUN_EQ_THM, compile_getelemptr_abi_def, abi_decode_ge_guard_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_decode_dynamic_member_pointer:
  compile_getelemptr_abi src T off opc hi st = (member_op,st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  abi_decode_load opc (n2w (sb + off) : bytes32) s = n2w payload_off /\
  sb + payload_off < dimword (:256) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand member_op t = SOME (n2w (sb + payload_off)) /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  Cases_on `hi = Lit 0w`
  >- (asm_simp_tac bool_ss [] >> strip_tac >>
      drule_all abi_decode_dynamic_member_pointer_sentinel >> simp[]) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_getelemptr_abi _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bounded_member_phases, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi src T off opc (Lit 0w) st = (member_op,c1)` >>
  rename1 `abi_decode_ge_guard member_op src c1 = (guard_result,st')` >>
  Cases_on `guard_result` >> gvs[] >>
  mp_tac (Q.INST [`st'` |-> `c1`] abi_decode_dynamic_member_pointer_sentinel) >>
  impl_tac >- fs[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME (n2w sb)` by metis_tac[] >>
  `sb < dimword (:256)` by decide_tac >>
  `w2n (n2w sb : bytes32) <= w2n (n2w (sb + payload_off) : bytes32)` by
    simp[w2n_n2w] >>
  mp_tac (Q.INST [`st` |-> `c1`, `s` |-> `s1`, `a` |-> `member_op`, `b` |-> `src`,
    `va` |-> `(n2w (sb + payload_off) : bytes32)`, `vb` |-> `(n2w sb : bytes32)`]
    abi_decode_ge_guard_sequence) >> impl_tac >- fs[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  drule abi_decode_ge_guard_shape >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `t` >> gvs[] >> metis_tac[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_MEMBER_BOUND_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI bounded member pointer not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderMemberBound");
