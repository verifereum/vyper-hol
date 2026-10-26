(* Execute the actual header followed by its output allocation. *)
Theory abiBuiltinDecodeAllocation
Ancestors
  abiBuiltinSetupFrames abiBuiltinAllocationState abiBuiltinAllocation
  abiBuiltinDecodeSetup abiBuiltinDecodeHeader abiBuiltinPrefix
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderGuards abiDecoderContract
  context compileEnv emitHelperProps exprLoweringProps venomState finite_map words arithmetic list

Theorem abi_builtin_decode_allocation:
  abi_builtin_decode_header data min_size max_size st = (inputs,header_st) /\
  compile_alloc_buffer outsz header_st = (buf,allocation_st) /\
  eval_operand data initial = SOME p /\ mload (w2n p) initial = n2w cnt /\
  min_size <= cnt /\ cnt <= max_size /\ max_size < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\ d = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (d,outsz)) /\
  outsz < dimword (:256) /\ allocation_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial ==>
  ?t. run_inst_seq (emitted_insts st allocation_st) initial = OK t /\
    eval_operand (FST inputs) t = SOME (n2w cnt) /\
    eval_operand (SND inputs) t = SOME (p + 32w) /\
    eval_operand buf.buf_operand t = SOME (n2w d) /\ fresh_vars_wrt limit_st t /\
    abi_builtin_allocation_frame st.cs_next_var header_st.cs_next_id outsz initial t /\
    inst_extends st allocation_st
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_decode_header_shape >> strip_tac >>
  drule abi_builtin_decode_header_live >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `header_st.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= header_st.cs_next_var`
    by decide_tac >>
  drule_all abi_builtin_decode_header >> strip_tac >>
  rename1 `abi_builtin_prefix st header_st limit_st initial prepared` >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  mp_tac (Q.INST [`st` |-> `header_st`, `st'` |-> `allocation_st`,
    `p` |-> `d:num`, `s` |-> `prepared:venom_state`] abi_builtin_alloc_buffer_frame) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> gvs[]) >> strip_tac >>
  rename1 `abi_builtin_allocation_frame header_st.cs_next_var header_st.cs_next_id outsz prepared t` >>
  `abi_builtin_allocation_frame st.cs_next_var header_st.cs_next_id outsz initial t` by
    (irule abi_builtin_allocation_frame_prefix >> qexistsl_tac [`header_st.cs_next_var`, `prepared`] >>
     asm_simp_tac bool_ss []) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >>
  fs[abi_builtin_allocation_frame_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_DECODE_ALLOCATION_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin decode allocation not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinDecodeAllocation");
