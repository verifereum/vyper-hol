(* Effects of the fetched bytes decoder, on the given chain of ghost states. *)
Theory bodyAbiDecodeGuardedBytesConfinementMods
Ancestors
  entryDecoderHistoryFrame fragGasOriginPtr
  abiDecoderBytesPhases abiDecoderContract abiDecoderBytesBound abiDecoderGuards
  abiEncoder compileEnv emitHelper exprLoweringProps loweringStateRelDefs
  decoderGhostFramePtr ptrSafeRun ptrDiscipline memSafeRun contextCodegenRel
  codegenRel memLocDefs venomMemProps venomInstProofs1 venomInstProps
  venomExecSemantics venomInst venomState fragExec list rich_list finite_map
  pred_set arithmetic

val bytes_inst = ``\dst (inst:instruction).
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  ~is_alloca_op inst.inst_opcode /\ inst.inst_opcode <> SETFMP /\
  inst.inst_opcode <> DALLOCA /\ ~is_ext_call_op inst.inst_opcode /\
  inst.inst_opcode <> CALL /\ inst.inst_opcode <> DELEGATECALL /\
  inst.inst_opcode <> CREATE /\ inst.inst_opcode <> CREATE2 /\
  inst.inst_opcode <> SSTORE /\ inst.inst_opcode <> TSTORE /\
  inst.inst_opcode <> ISTORE /\ ~MEM dst inst.inst_outputs /\
  (inst.inst_opcode = MSTORE ==> ?a. inst.inst_operands = [a;Lit 0w]) /\
  (inst.inst_opcode = MCOPY ==> ?a z. inst.inst_operands = [Var dst;a;z])``;

Theorem bytes_emitted_insts[local]:
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var input) hi
    (DecBytestring n) start = ((),fin) /\ hi <> Lit 0w /\
  not_fresh_at start dst ==>
  fin.cs_current_bb = start.cs_current_bb /\
  isPREFIX start.cs_current_insts fin.cs_current_insts /\
  EVERY ((^bytes_inst) dst) (emitted_insts start fin)
Proof
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bytes_position_phases] >>
  simp[abi_decode_bytes_head_def, compile_abi_dec_addr_def,
       abi_decode_count_guard_def, abi_decode_bytes_payload_guard_def,
       abi_decode_bytes_runtime_tail_def, compile_abi_decode_range_check_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, is_terminator_def, is_alloca_op_def,
       is_ext_call_op_def, mk_inst_def] >>
  fs[not_fresh_at_def] >>
  rpt conj_tac >> first_x_assum irule >> decide_tac
QED

Theorem bytes_copy_write_range[local]:
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [Var dst;a;z] /\
  eval_operand (Var dst) s = SOME off /\ eval_operand a s = SOME src /\
  eval_operand z s = SOME len /\ w2n len <> 0 /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  FLOOKUP G dst = SOME (b,cap) ==>
  b <= w2n off /\ w2n off + w2n len <= b + cap
Proof
  strip_tac >>
  drule access_ok_write_site_bounds >>
  simp[mem_write_ops_def, source_memory_write_ranges_def,
       sized_source_write_range_def] >>
  disch_then (qspecl_then [`w2n off`,`w2n len`] mp_tac) >> simp[]
QED

Theorem bytes_written_bound[local]:
  (^bytes_inst) dst inst /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  access_ok lo G fn inst s /\ FLOOKUP G dst = SOME (b,cap) /\
  i IN written_taint tn inst s ==> b <= i /\ i < b + cap
Proof
  strip_tac >> Cases_on `inst.inst_opcode = MCOPY`
  >- (`~in_revert_forward fn s` by
        (rw[in_revert_forward_def] >> strip_tac >>
         drule_all revert_forward_at_opcode >> simp[]) >>
      gvs[] >> rename1 `inst.inst_operands = [Var dst;a;z]` >>
      Cases_on `eval_operand (Var dst) s` >> gvs[written_taint_def] >>
      Cases_on `eval_operand a s` >> gvs[] >>
      Cases_on `eval_operand z s` >> gvs[] >>
      rename1 `eval_operand z s = SOME len` >>
      `w2n len <> 0` by decide_tac >>
      drule_all bytes_copy_write_range >> decide_tac) >>
  Cases_on `inst.inst_opcode = MSTORE`
  >- (gvs[] >> rename1 `inst.inst_operands = [a;Lit 0w]` >>
      Cases_on `eval_operand a s` >>
      gvs[written_taint_def, op_taint_def]) >>
  gvs[written_taint_def] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  rename1 `inst.inst_operands = a::ops` >>
  Cases_on `ops` >> gvs[] >>
  rename1 `inst.inst_operands = a::v::ops` >>
  Cases_on `ops` >> gvs[] >>
  rename1 `inst.inst_operands = a::v::z::ops` >>
  Cases_on `ops` >> gvs[]
QED

val bytes_step = ``\D lo explicit ctx fn PG (u,Gu,tu) (v,Gv,tv).
  gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (u,Gu,tu) [] (OK v,Gv,tv)``;

Theorem bytes_edge_frame[local]:
  (^bytes_inst) dst inst /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  FLOOKUP G dst = SOME (b,cap) /\
  (^bytes_step) D lo explicit ctx fn PG (s,G,tn) (t,Gf,tf) ==>
  t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = SUC s.vs_inst_idx /\
  FLOOKUP Gf dst = SOME (b,cap) /\ t.vs_alloca_next = s.vs_alloca_next /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!i. (i < b \/ b + cap <= i) /\ i IN tf.t_mem ==> i IN tn.t_mem)
Proof
  simp[] >> strip_tac >> drule gas_origin_ptr_edge_common_fuel >>
  simp[] >> strip_tac >> gvs[] >>
  TRY (qpat_x_assum `exit_result _` mp_tac >>
       qpat_assum `OK _ = step_inst _ _ _ _`
         (rewrite_tac o single o SYM) >> simp[exit_result_def] >> NO_TAC) >>
  drule_all step_preserves_control_flow >> strip_tac >>
  drule_all ghost_step_non_invoke >> strip_tac >>
  `access_ok lo G fn inst s` by
    (drule ptr_safe_step_inst_ok >> simp[ptr_inst_ok_def]) >>
  gvs[step_inst_non_invoke] >>
  drule_all step_inst_base_preserves_alloca_state >> strip_tac >>
  drule_all step_inst_base_preserves_fmp_ordinary >> strip_tac >>
  drule_all step_taint_nonmemory_frame >> strip_tac >>
  simp[step_prov_other_output] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def, FLOOKUP_DEF] >>
  rpt strip_tac >>
  drule_all (SIMP_RULE bool_ss [] bytes_written_bound) >> decide_tac
QED

(* The unseen suffix of the containing block is never executed here. *)
Theorem bytes_slice_head[local]:
  DROP p bb.bb_instructions = inst::rest ==>
  get_instruction bb p = SOME inst /\ DROP (SUC p) bb.bb_instructions = rest
Proof
  strip_tac >>
  `p < LENGTH bb.bb_instructions` by
    (Cases_on `p < LENGTH bb.bb_instructions` >> simp[] >>
     gvs[DROP_LENGTH_TOO_LONG]) >>
  gvs[DROP_CONS_EL, get_instruction_def]
QED

Theorem bytes_slice_chain[local]:
  !xs s G tn t Gf tf bb rest.
    EVERY ((^bytes_inst) dst) xs /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = xs ++ rest /\
    FLOOKUP G dst = SOME (b,cap) /\
    RELPOW ((^bytes_step) D lo explicit ctx fn PG) (LENGTH xs)
      (s,G,tn) (t,Gf,tf) ==>
    t.vs_alloca_next = s.vs_alloca_next /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. (i < b \/ b + cap <= i) /\ i IN tf.t_mem ==> i IN tn.t_mem)
Proof
  Induct
  >- simp[arithmeticTheory.NRC] >>
  SIMP_TAC bool_ss [LENGTH, arithmeticTheory.NRC, EVERY_DEF, APPEND] >>
  rpt gen_tac >> strip_tac >>
  PairCases_on `z` >> gvs[] >>
  drule bytes_slice_head >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) [] bytes_edge_frame) >> strip_tac >>
  `lookup_block z0.vs_current_bb fn.fn_blocks = SOME bb /\
   DROP z0.vs_inst_idx bb.bb_instructions = xs ++ rest` by simp[] >>
  first_x_assum drule_all >> strip_tac >> simp[] >> metis_tac[]
QED

Theorem abi_decode_bytes_finite_chain_confined_mods:
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var input) hi
    (DecBytestring n) start = ((),fin) /\ hi <> Lit 0w /\
  fn_has_code start fin fn /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\ not_fresh_at start dst /\
  FLOOKUP G dst = SOME (output_base,output_cap) /\
  RELPOW (\(u,Gu,tu) (v,Gv,tv).
    gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (u,Gu,tu) [] (OK v,Gv,tv))
    (LENGTH fin.cs_current_insts - LENGTH start.cs_current_insts)
    (s,G,tn) (t,Gf,tf) ==>
  t.vs_alloca_next = s.vs_alloca_next /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!i. (i < output_base \/ output_base+output_cap <= i) /\
       i IN tf.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >> drule_all bytes_emitted_insts >> strip_tac >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `LENGTH (emitted_insts start fin) =
   LENGTH fin.cs_current_insts - LENGTH start.cs_current_insts` by
    simp[emitted_insts_def, LENGTH_DROP] >>
  irule bytes_slice_chain >>
  goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED
