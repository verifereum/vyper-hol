Theory abiDecodePtrBytesRuntimeFrame
Ancestors
  abiDecoderBytesPhases abiDecoderBytesBound abiDecoderGuard abiDecoderContract
  abiDecoderGuards abiDecoderCopy abiDecoderComposition
  abiEncoder emitHelper emitHelperProps exprLoweringProps freshWrites
  abiEncoderWindowLookup venomExecSemantics venomState venomInst venomMemProps
  compileEnv words arithmetic list rich_list finite_map

(* Runtime-only boundary: scalar operations, loads, and bounded memory writes
   do not alter the rest of the machine record. *)
Theorem abi_decode_memory_step_frame:
  (fresh_write_op i.inst_opcode \/
   MEM i.inst_opcode [MLOAD; MSTORE; MCOPY]) /\
  step_inst_base i s = OK t ==>
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac
  >- (drule_all step_fresh_write_op >> strip_tac >>
      gvs[venom_state_component_equality]) >>
  gvs[MEM] >>
  gvs[step_inst_base_def, exec_read1_def, exec_write2_def, AllCaseEqs(),
      update_var_def] >>
  (conj_tac >- simp[mstore_def, mcopy_def,
     write_memory_with_expansion_def, LET_THM]) >>
  simp[mstore_memory_nondecreasing, mcopy_def,
       write_memory_with_expansion_nondecreasing]
QED

Theorem abi_decode_memory_run_frame:
  !code s t.
  EVERY (\i. fresh_write_op i.inst_opcode \/
    MEM i.inst_opcode [MLOAD; MSTORE; MCOPY]) code /\
  run_inst_seq code s = OK t ==>
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> simp[run_inst_seq_def] >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK mid` >>
  drule_at (Pat `step_inst_base _ _ = _`) abi_decode_memory_step_frame >>
  simp[] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  (conj_tac >- gvs[venom_state_component_equality]) >> simp[]
QED

Theorem abi_decode_bytes_memory_shape:
  compile_abi_decode_to_buf dst pos MLOAD base_op hi (DecBytestring n) sa = ((),sb) ==>
  EVERY (\i. (fresh_write_op i.inst_opcode \/
    MEM i.inst_opcode [MLOAD; MSTORE; MCOPY]) /\
    EVERY (not_fresh_at sb) i.inst_outputs) (emitted_insts sa sb)
Proof
  simp[abi_decode_bytes_position_phases, abi_decode_source_opcode_def] >>
  Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  gvs[abi_decode_bytes_head_def, compile_abi_dec_addr_def,
      abi_decode_count_guard_def, abi_decode_bytes_payload_guard_def,
      abi_decode_bytes_runtime_tail_def, compile_abi_decode_range_check_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, fresh_write_op_def,
       abi_decode_copy_opcode_def, not_fresh_at_def,
       ASCIInumbersTheory.toString_inj]
QED

(* This observed-success boundary requires no ghost replay or input validity.
   In particular, it is usable with the outcome-specific pointer endpoint. *)
Theorem abi_decode_bytes_runtime_frame:
  compile_abi_decode_to_buf dst pos MLOAD base_op hi (DecBytestring n) sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\ fresh_vars_wrt sa s ==>
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\ fresh_vars_wrt sb t
Proof
  strip_tac >> drule abi_decode_bytes_memory_shape >> strip_tac >>
  `EVERY (\i. fresh_write_op i.inst_opcode \/
    MEM i.inst_opcode [MLOAD; MSTORE; MCOPY]) (emitted_insts sa sb)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all abi_decode_memory_run_frame >> strip_tac >> simp[] >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (drule abi_decode_bytes_position_shape >>
     simp[abi_decode_source_opcode_def]) >>
  `fresh_vars_wrt sb s` by
    (irule fresh_vars_wrt_mono >> qexists_tac `sa` >> simp[]) >>
  irule abi_window_seq_fresh >>
  qexistsl_tac [`sb`, `emitted_insts sa sb`, `s`] >> simp[] >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[MEM] >> metis_tac[fresh_write_op_simple]
QED
