Theory gasFocusPlainEntry
Ancestors
  codegenEntrySim codegenEntryRel codegenRel asmFrameRel
  asmDataSuffixProps unitShapeDefs symbolResolve

(* Recover the concrete entry package on the identity-finalizer branch. *)
Theorem focus_plain_entry_rel:
  unit_shape_ok unit /\
  initial_codegen_state_rel cpl vs0 /\ vs0.vs_inst_idx = 0 /\
  vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  asm_frame_rel_tail [] prog vs0.vs_data_section es0
    (entry_asm_state vs0 es0) es0 ==>
  initial_ctx_rel_tail [] cpl prog unit.cu_context vs0 es0
Proof
  simp[initial_ctx_rel_tail_nil, asm_frame_rel_tail_nil] >>
  strip_tac >>
  `?fn fns. unit.cu_context.ctx_functions = fn :: fns /\
    get_params (HD fn.fn_blocks).bb_instructions = []` by
    gvs[unit_shape_ok_def, entry_fn_first_def] >>
  gvs[asm_frame_rel_def, asm_evm_rel_def, entry_asm_state_def,
      codegen_asm_entry_rel_def, data_suffix_assemble] >>
  simp[initial_ctx_rel_def, initial_state_rel_def, stack_params_rel_def,
       msg_ctx_rel_def, tx_ctx_rel_def, block_ctx_rel_def, blockhash_rel_def,
       asm_pc_to_offset_def, CONJ_ASSOC]
QED
