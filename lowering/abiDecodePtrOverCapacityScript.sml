Theory abiDecodePtrOverCapacity
Ancestors
  abiDecoderBytesPrefix abiDecoderBytesPhases abiDecoderGuards
  abiDecodePtrMemberInterface abiDecoderMemberBound
  abiDecoderComposition abiDecoderRange abiDecoderContract abiEncoder abiDecoderBytesBound
  emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomExecProofs venomState venomInst words arithmetic list

(* Source-opcode generalization of the calldata-only rejection boundary.
   Shared calldata theories are not task-owned and cannot be refactored here. *)
Theorem abi_decode_count_guard_rejected_sequence:
  abi_decode_count_guard opc src limit st = (count_op,st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME p /\
  limit < dimword (:256) /\ limit < w2n (abi_decode_load opc p s) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op GT [count_op; Lit (n2w limit)] c1 = (too_many,c2)` >>
  rename1 `emit_op ISZERO [too_many] c2 = (ok,c3)` >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand (Lit (n2w limit)) s1 = SOME (n2w limit)` by simp[eval_operand_def] >>
  drule_all emit_op_GT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  gvs[w2n_n2w, bool_to_word_def] >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  gvs[bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all run_inst_seq_emit_extend >> simp[] >> metis_tac[]
QED

(* Only the length-word window is needed before the rejecting guard.
   In particular no payload bound or output-memory premise is required. *)
Theorem abi_decode_bytes_over_capacity:
  compile_abi_decode_to_buf dst pos opc base_op hi (DecBytestring n) st = ((),st') /\
  abi_decode_source_opcode opc /\ hi <> Lit 0w /\
  eval_operand pos s = SOME (n2w p) /\
  eval_operand base_op s = SOME (n2w b) /\
  eval_operand hi s = SOME (n2w h) /\
  p+32 <= h /\ h < dimword (:256) /\ n < dimword (:256) /\
  n < w2n (abi_decode_load opc (n2w (b+p) : bytes32) s) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bytes_position_phases] >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `abi_decode_bytes_head pos hi st = (head,sh)` >>
  rename1 `compile_abi_dec_addr base_op pos sh = (addr,sa)` >>
  rename1 `abi_decode_count_guard opc addr n sa = (cnt,sc)` >>
  drule_all abi_decode_bytes_head_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st sh) s = OK s1` >>
  `eval_operand base_op s1 = SOME (n2w b) /\
   eval_operand pos s1 = SOME (n2w p)` by metis_tac[] >>
  drule_all compile_abi_dec_addr_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sh sa) s1 = OK s2` >>
  `n < w2n (abi_decode_load opc (n2w (b+p) : bytes32) s2)` by
    gvs[abi_decode_load_def, abi_decode_source_def, mload_def] >>
  drule_all abi_decode_count_guard_rejected_sequence >> strip_tac >>
  `inst_extends sh sa` by
    (Cases_on `base_op = Lit 0w` >>
     gvs[compile_abi_dec_addr_def, comp_return_def, inst_extends_refl] >>
     metis_tac[inst_extends_emit_op]) >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  `inst_extends sc st'` by suspend "suffix" >>
  `run_inst_seq (emitted_insts st sa) s = OK s2 /\ inst_extends st sa` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `sh`] >> simp[]) >>
  `run_inst_seq (emitted_insts st sc) s = Abort Revert_abort t` by
    metis_tac[run_inst_seq_emit_extend] >>
  qexists_tac `t` >> irule run_inst_seq_abort_extends >>
  qexists_tac `sc` >> metis_tac[inst_extends_trans]
QED

Resume abi_decode_bytes_over_capacity[suffix]:
  drule abi_decode_bytes_payload_guard_shape >> strip_tac >>
  Cases_on `base_op = Lit 0w` >> gvs[]
  >- (drule inst_extends_emit_void >> metis_tac[inst_extends_trans]) >>
  drule abi_decode_bytes_runtime_tail_shape >> metis_tac[inst_extends_trans]
QED

Finalise abi_decode_bytes_over_capacity

(* The selected tuple member, including offset selection and destination ADD.
   off is its ABI header offset; delta is the actual loaded relative offset.
   Only the earlier selection underflow and length-word range checks succeed. *)
Theorem abi_decode_selected_bytes_over_capacity:
  abi_decode_member_code dst pos src hi (DecBytestring n) off q sa sb /\
  eval_operand pos s = SOME (n2w z) /\
  eval_operand (Var src) s = SOME (n2w b) /\
  eval_operand hi s = SOME (n2w h) /\ hi <> Lit 0w /\
  eval_operand (Var dst) s = SOME d /\
  abi_decode_load MLOAD (n2w (b+(z+off)) : bytes32) s = n2w delta /\
  z+delta+32 <= h /\ h < dimword (:256) /\ n < dimword (:256) /\
  n < w2n (abi_decode_load MLOAD (n2w (b+(z+delta)) : bytes32) s) /\
  fresh_vars_wrt sa s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_member_code _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[abi_decode_member_code_def, dec_info_needs_offset_def] >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `z+delta < dimword(:256)` by decide_tac >>
  drule_all abi_decode_dynamic_member_pointer >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK s1` >>
  `eval_operand (Var dst) s1 = SOME d` by metis_tac[] >>
  `eval_operand (Lit (n2w q)) s1 = SOME (n2w q)` by simp[eval_operand_def] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sn) s1 = OK s2` >>
  drule_all (abi_decode_pure_emit_frame |> Q.INST [`opc` |-> `ADD`] |> SRULE []) >>
  strip_tac >>
  `eval_operand v s2 = SOME (n2w (z+delta)) /\
   eval_operand (Var src) s2 = SOME (n2w b) /\
   eval_operand hi s2 = SOME (n2w h)` by metis_tac[] >>
  `n < w2n (abi_decode_load MLOAD (n2w (b+(z+delta)) : bytes32) s2)` by
    gvs[abi_decode_load_def, mload_def] >>
  `?t. run_inst_seq (emitted_insts sn sb) s2 = Abort Revert_abort t` by
    (irule abi_decode_bytes_over_capacity >> simp[] >>
     goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
     qexistsl_tac [`b`, `h`, `z+delta`] >> simp[]) >>
  `inst_extends sm sn` by metis_tac[inst_extends_emit_op] >>
  `inst_extends sn sb` by
    (drule abi_decode_bytes_position_shape >> simp[] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts sa sn) s = OK s2 /\ inst_extends sa sn` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `sm`] >> simp[]) >>
  qexists_tac `t` >> metis_tac[run_inst_seq_emit_extend]
QED
