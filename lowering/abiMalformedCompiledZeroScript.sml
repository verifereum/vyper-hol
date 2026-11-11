(* Compiler-facing empty traversal boundary. *)
Theory abiMalformedCompiledZero
Ancestors
  abiMalformedZeroTraversal abiMalformedRecursiveInterface abiDecoderLoopEmit abiDecoderLoopCode
  abiDecoderRecursiveLoopEntry abiDecoderRecursiveLoopLayout abiDecoderArraySetupCode
  abiDecoderArraySetupInputs
  abiDecoderContract abiDecodeRanges exprLoweringProps abiEncoder emitHelper
  fragExec compileEnv venomInst venomState words list arithmetic

Theorem abi_malformed_compiled_zero:
  abi_decode_loop_prefix ip src MLOAD base_op start = (labels,st) /\
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di asz msz st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) MLOAD base_op hi di middle = ((),end_st) /\
  abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) end_st = ((),final) /\
  fn_has_code start final func /\
  abi_malformed_entry ctx func cenv cx es start sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  eval_operand ip s = SOME (n2w slot) /\ mload slot s = 0w /\ slot < dimword (:256) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (slot,32) /\
  inst.inst_id IN sites /\ inst.inst_id <> live /\ inst.inst_id <> dstid /\
  fresh_vars_wrt ceiling s /\ final.cs_next_var <= ceiling.cs_next_var /\
  s.vs_current_bb = start.cs_current_bb /\ s.vs_inst_idx = LENGTH start.cs_current_insts /\
  ~s.vs_halted /\ p+32 <= L /\ abi_head_word (DROP p xs) = 0 ==>
  frag_outcome ctx func s final
    (\u. (?avs. abi_reflected_prefix env ty (DROP (p+32) xs) 0 avs) /\
      abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid s u /\
      fresh_vars_wrt ceiling u) (\r. ?v. r = Abort Revert_abort v)
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_loop_phase_entry >> strip_tac >>
  drule_all abi_decoder_loop_phase_lookups >> strip_tac >>
  drule_all abi_decoder_loop_phase_containment >> strip_tac >>
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  `middle.cs_next_var <= end_st.cs_next_var` by
    (mp_tac (CONJUNCT1 ci_mono_compile_abi_decode) >>
     simp[ci_mono_def] >> disch_then (qspecl_then
       [`SND (SND ops)`, `FST (SND ops)`, `MLOAD`, `base_op`, `hi`, `di`, `middle`] mp_tac) >>
     simp[]) >>
  `st.cs_next_var <= middle.cs_next_var` by
    (drule abi_decode_array_element_setup_operands >> simp[]) >>
  irule abi_malformed_zero_traversal >> simp[] >>
  goal_assum (drule_at (Pat `abi_malformed_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >>
  qexistsl_tac [`st.cs_current_bb`, `start.cs_next_id`, `FST labels`,
    `start.cs_next_id+1`, `inst`, `ip`, `q`, `slot`] >>
  simp[abiDecoderExecutionTheory.abi_decode_position_header_insts_def,
       venomExecSemanticsTheory.phi_prefix_length_def, mk_inst_def]
QED
