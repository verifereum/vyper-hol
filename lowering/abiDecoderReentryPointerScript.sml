(* Dynamic-element navigation is safe on every iteration, including guarded
   memory sources. Only temporaries allocated by this prefix are overwritten. *)
Theory abiDecoderReentryPointer
Ancestors
  abiDecoderReentryPrefix abiDecoderReentry abiDecoderVarSequence abiDecoderVarExtend
  abiDecoderArrayBound abiDecoderArrayPtr abiDecoderReservation abiDecoderContract
  abiEncoder emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState venomInst words list rich_list arithmetic

Theorem abi_decoder_array_pointer_code:
  compile_abi_decode_dyn_elem_ptr opc elem_src src_data hi abi_sz st = (child_op,st') /\
  abi_decode_source_opcode opc ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
    ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode) (emitted_insts st st')
Proof
  Cases_on `hi = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, abi_decoder_reentry_opcode_def, mk_inst_def,
      abi_decode_source_opcode_def, is_terminator_def, is_alloca_op_def]
QED

Theorem abi_decoder_array_pointer_sequence:
  compile_abi_decode_dyn_elem_ptr opc elem_src src_data hi abi_sz st = (child_op,st') /\
  abi_decode_source_opcode opc /\ eval_operand elem_src s = SOME p /\
  eval_operand src_data s = SOME (n2w data_base) /\
  abi_decode_load opc (p:bytes32) s = n2w child_off /\
  (hi = Lit 0w \/ ?hb. eval_operand hi s = SOME (n2w hb) /\
    data_base + child_off + abi_sz <= hb /\ hb < dimword (:256)) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand child_op t = SOME (n2w (data_base + child_off)) /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  Cases_on `hi = Lit 0w` >> asm_simp_tac bool_ss [] >> strip_tac >>
  FIRST [drule_all abi_decode_array_pointer_sentinel >> simp[],
         drule_all abi_decode_bounded_array_pointer >> simp[]]
QED

Theorem abi_decoder_array_pointer_reentry:
  compile_abi_decode_dyn_elem_ptr opc elem_src src_data hi abi_sz st = (child_op,st') /\
  abi_decode_source_opcode opc /\ eval_operand elem_src initial = SOME p /\
  eval_operand src_data initial = SOME (n2w data_base) /\
  abi_decode_load opc (p:bytes32) initial = n2w child_off /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    data_base + child_off + abi_sz <= hb /\ hb < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var elem_src /\
  abi_decoder_operand_live st.cs_next_var src_data /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    eval_operand child_op actual = SOME (n2w (data_base + child_off)) /\
    fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_memory = initial.vs_memory /\ actual.vs_call_ctx = initial.vs_call_ctx /\
    actual.vs_data_section = initial.vs_data_section /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\ inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand elem_src (abi_decoder_prune_vars st.cs_next_var initial) = SOME p /\
   eval_operand src_data (abi_decoder_prune_vars st.cs_next_var initial) = SOME (n2w data_base)`
    by asm_simp_tac bool_ss [abi_decoder_prune_eval] >>
  `abi_decode_load opc (p:bytes32) (abi_decoder_prune_vars st.cs_next_var initial) = n2w child_off`
    by fs[abi_decode_load_def, abi_decode_source_def, abi_decoder_prune_vars_def, mload_def] >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var initial)`
    by irule abi_decoder_prune_fresh >>
  mp_tac (Q.INST [`s` |-> `abi_decoder_prune_vars st.cs_next_var initial`]
    abi_decoder_array_pointer_sequence) >>
  impl_tac >- asm_simp_tac bool_ss [abi_decoder_prune_eval] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st')
    (abi_decoder_prune_vars st.cs_next_var initial) = OK clean` >>
  drule_all abi_decoder_array_pointer_code >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st') /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
     (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  rename1 `abi_decoder_vars_extend initial.vs_vars clean actual` >>
  drule_all abi_decoder_vars_extend_eval >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  qexists_tac `actual` >> gvs[abi_decoder_prune_vars_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_REENTRY_POINTER_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI pointer re-entry not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderReentryPointer");
