(* Actual method-ID address computation and full-word store. Only the first
   four bytes are retained before the recursive payload overwrites the tail. *)
Theory abiBuiltinEncodeMethod
Ancestors
  abiBuiltinEncodeCode abiBuiltinEncodeFinishSequence abiBuiltinPrefix abiEncoderWrites
  abiDecoderReentry abiDecoderDynamicLoopSetup abiDecoderGuards abiDecoderFrameCompose abiDecoderContract
  compileEnv emitHelper emitHelperProps exprLoweringProps venomInst venomState
  venomExecSemantics words list rich_list arithmetic

Theorem abi_builtin_encode_method_trace:
  abi_builtin_encode_method_id (SOME mid) buf st = ((),final) ==>
  ?method_ptr write_st.
    emit_op ADD [buf;Lit 32w] st = (method_ptr,write_st) /\
    emit_void MSTORE [method_ptr;Lit (mid << 224)] write_st = ((),final)
Proof
  simp_tac (srw_ss()) [abi_builtin_encode_method_id_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [buf;Lit 32w] st = (method_ptr,write_st)` >>
  qexistsl_tac [`method_ptr`, `write_st`] >> simp[]
QED

Theorem abi_builtin_encode_method_shape:
  abi_builtin_encode_method_id (SOME mid) buf st = ((),final) ==>
  final.cs_next_id = st.cs_next_id+2 /\ final.cs_next_var = st.cs_next_var+1 /\
  final.cs_blocks = st.cs_blocks /\ final.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts final.cs_current_insts /\ inst_extends st final /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st final)
Proof
  simp[abi_builtin_encode_method_id_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, is_terminator_def, mk_inst_def]
QED

Theorem abi_builtin_encode_method_sequence:
  abi_builtin_encode_method_id (SOME mid) buf st = ((),final) /\
  eval_operand buf initial = SOME (n2w p) /\ p+32 < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\ inst_extends st final /\
    fresh_vars_wrt limit_st actual /\ mload (p+32) actual = mid << 224 /\
    abi_decode_frame (p+32) 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_method_trace >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  `write_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`lhs` |-> `buf`, `rhs` |-> `Lit 32w`, `out` |-> `method_ptr`,
    `a` |-> `n2w p:bytes32`, `b` |-> `32w:bytes32`, `st'` |-> `write_st`,
    `s` |-> `initial:venom_state`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_builtin_prefix st write_st limit_st initial prepared` >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  mp_tac (Q.INST [`buf` |-> `method_ptr`, `value_op` |-> `Lit (mid << 224)`,
    `p` |-> `p+32:num`, `s` |-> `prepared:venom_state`, `st` |-> `write_st`,
    `w` |-> `(mid:bytes32) << 224`] abi_builtin_store_sequence) >>
  impl_tac >- asm_simp_tac (srw_ss()) [word_add_n2w, eval_operand_def] >> strip_tac >>
  `run_inst_seq (emitted_insts st final) initial = OK (mstore (p+32) (mid << 224) prepared) /\
   inst_extends st final` by
    (mp_tac (Q.INST [`st1` |-> `write_st`, `st2` |-> `final`, `s` |-> `initial:venom_state`,
      `s1` |-> `prepared:venom_state`, `s2` |-> `mstore (p+32) (mid << 224) prepared`]
      abi_decode_sequence_chain) >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `abi_decode_frame (p+32) 32 initial (mstore (p+32) (mid << 224) prepared)` by
    (irule abi_decode_frame_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss [abi_decode_frame_def]) >>
  qexists_tac `mstore (p+32) (mid << 224) prepared` >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >> first_x_assum irule >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_METHOD_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin method-ID store not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeMethod");
