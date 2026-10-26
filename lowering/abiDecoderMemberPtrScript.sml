(* Actual member-pointer instructions on the immutable-source sentinel path. *)
Theory abiDecoderMemberPtr
Ancestors
  abiDecoderBytesBound abiDecoderGuards abiDecoderContract abiEncoder
  emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState words

Theorem abi_decode_static_member_pointer:
  compile_getelemptr_abi src F off opc hi st = (member_op,st') /\
  eval_operand src s = SOME (n2w sb) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand member_op t = SOME (n2w (sb + off)) /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  simp[compile_getelemptr_abi_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off)` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  qexists_tac `t` >> gvs[word_add_n2w]
QED

Theorem abi_decode_dynamic_member_pointer_sentinel:
  compile_getelemptr_abi src T off opc (Lit 0w) st = (member_op,st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  abi_decode_load opc (n2w (sb + off) : bytes32) s = n2w payload_off /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand member_op t = SOME (n2w (sb + payload_off)) /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  simp[compile_getelemptr_abi_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [src; Lit (n2w off)] st = (head_ptr,c1)` >>
  rename1 `emit_op opc [head_ptr] c1 = (offset_val,c2)` >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off)` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand head_ptr s1 = SOME (n2w (sb + off))` by gvs[word_add_n2w] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand offset_val s2 = SOME (n2w payload_off)` by
    gvs[abi_decode_load_def, abi_decode_source_def, mload_def] >>
  `eval_operand src s2 = SOME (n2w sb)` by metis_tac[] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 st') s2 = OK t` >>
  qpat_assum `emit_op opc [head_ptr] c1 = _`
    (assume_tac o MATCH_MP inst_extends_emit_op) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  qexists_tac `t` >> gvs[word_add_n2w] >> metis_tac[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_MEMBER_PTR_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI member-pointer execution not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderMemberPtr");
