(* Execute output allocation and its first data-pointer ADD for either prefix. *)
Theory abiBuiltinEncodeAllocate
Ancestors
  abiBuiltinEncodeAllocateCode abiBuiltinAllocationState abiBuiltinAllocation abiBuiltinSetupFrames
  abiBuiltinPrefix abiEncoderBytesPrefix abiEncoderSequenceReach abiDecoderReentry abiDecoderDynamicLoopSetup
  abiDecoderGuards abiDecoderContract abiDecoderLoop fragExec instIdxIndep
  compileEnv emitHelperProps exprLoweringProps venomState venomExecSemantics finite_map words list arithmetic

Theorem abi_builtin_encode_allocate_sequence:
  abi_builtin_encode_allocate outsz data_offset st = (ops,address_st) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ address_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st address_st) initial = OK actual /\
    eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+data_offset)) /\
    fresh_vars_wrt limit_st actual /\
    abi_builtin_allocation_frame st.cs_next_var st.cs_next_id outsz initial actual /\
    inst_extends st address_st
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_allocate_trace >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  `allocated.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= allocated.cs_next_var`
    by decide_tac >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `st'` |-> `allocated`]
    abi_builtin_alloc_buffer_frame) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_allocation_frame st.cs_next_var st.cs_next_id outsz initial allocated_s` >>
  mp_tac (Q.INST [`lhs` |-> `buf.buf_operand`, `rhs` |-> `Lit (n2w data_offset)`, `out` |-> `data_ptr`,
    `a` |-> `n2w p:bytes32`, `b` |-> `n2w data_offset:bytes32`, `st` |-> `allocated`,
    `st'` |-> `address_st`, `s` |-> `allocated_s:venom_state`] abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_builtin_prefix allocated address_st limit_st allocated_s actual` >>
  `eval_operand buf.buf_operand actual = SOME (n2w p)` by
    (drule_all abi_encoder_prefix_eval >> simp[]) >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  `abi_builtin_allocation_frame st.cs_next_var st.cs_next_id outsz initial actual` by
    (irule abi_builtin_allocation_frame_suffix >>
     qexistsl_tac [`allocated_s`, `allocated.cs_next_var`] >> asm_simp_tac bool_ss []) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `actual` >> gvs[word_add_n2w]
QED

Theorem abi_builtin_encode_allocate_reach:
  abi_builtin_encode_allocate outsz data_offset st = (ops,address_st) /\ fn_has_code st address_st func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ address_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+data_offset)) /\ fresh_vars_wrt limit_st actual /\
    abi_builtin_allocation_frame st.cs_next_var st.cs_next_id outsz initial actual /\
    actual.vs_current_bb = address_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH address_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_allocate_shape >> strip_tac >>
  drule_all abi_builtin_encode_allocate_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st address_st) initial = OK encoded` >>
  `~encoded.vs_halted` by fs[abi_builtin_allocation_frame_def] >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH address_st.cs_current_insts` >>
  gvs[abi_builtin_allocation_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_ALLOCATE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin encoder allocation not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeAllocate");
