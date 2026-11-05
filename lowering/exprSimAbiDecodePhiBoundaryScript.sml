(* Internal nonempty block heads determine observer-function PHI prefixes.
   Empty final blocks still need the explicit endpoint premise. *)
Theory exprSimAbiDecodePhiBoundary
Ancestors
  abiDecoderPhi fragExec venomExecSemantics compileEnv list rich_list
  exprSimAbiDecodeMemberExecute emitHelper venomInst

Theorem abi_decode_nonempty_prefix_phi:
  isPREFIX xs ys /\ xs <> [] /\ phi_prefix_length xs = 0 ==>
  phi_prefix_length ys = 0
Proof
  Cases_on `xs` >> simp[] >> Cases_on `ys` >> simp[] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `h.inst_opcode = PHI` >> gvs[phi_prefix_length_def]
QED

Theorem abi_decode_observer_exit_phi:
  fn_has_code st last fn /\
  (st.cs_blocks = last.cs_blocks \/
   (last.cs_current_insts <> [] /\ phi_prefix_length last.cs_current_insts = 0)) ==>
  st.cs_blocks = last.cs_blocks \/
  (!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0)
Proof
  rw[fn_has_code_def] >> gvs[] >>
  disj2_tac >> irule abi_decode_nonempty_prefix_phi >> metis_tac[]
QED

Theorem abi_decode_to_buf_nonempty_observer_phi:
  compile_abi_decode_to_buf dst src opc base_op hi info st = ((),last) /\
  abi_decode_source_opcode opc /\ fn_has_code st last fn /\
  last.cs_current_insts <> [] ==>
  st.cs_blocks = last.cs_blocks \/
  (!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >> drule_all abi_decoder_to_buf_exit_phi >> strip_tac >>
  irule abi_decode_observer_exit_phi >> simp[]
QED

Theorem abi_decode_continuation_exit_phi:
  fn_has_code continuation prefix_end fn /\
  continuation.cs_current_bb = child_end.cs_current_bb /\
  prefix_end.cs_current_bb = continuation.cs_current_bb /\
  prefix_end.cs_current_insts <> [] /\
  phi_prefix_length prefix_end.cs_current_insts = 0 ==>
  !bb. lookup_block child_end.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  rw[fn_has_code_def] >> gvs[] >>
  irule abi_decode_nonempty_prefix_phi >> metis_tac[]
QED

Theorem abi_decode_code_context_exit_phi:
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
    MEM i (fn_insts func)) /\
  (!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  abi_decode_code_context func fn st last
Proof
  simp[abi_decode_code_context_def]
QED

(* Both the loop backedge and static next-member setup can use an ADD
   as the first continuation instruction after an empty dynamic exit. *)
Theorem abi_decode_emit_op_empty_head:
  emit_op opc operands st = (out,last) /\ st.cs_current_insts = [] /\
  opc <> PHI ==>
  last.cs_current_bb = st.cs_current_bb /\ last.cs_current_insts <> [] /\
  phi_prefix_length last.cs_current_insts = 0
Proof
  simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[phi_prefix_length_def, mk_inst_def]
QED
