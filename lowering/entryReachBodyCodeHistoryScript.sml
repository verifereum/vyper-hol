Theory entryReachBodyCodeHistory
Ancestors
  loweringShapeDefs actualDecoderPackaging abiDecoderCode compileEnv emitHelper
  vyperCompiler venomInst list arithmetic

(* Unlike abi_decoder_code, this certificate permits arbitrary opcodes and
   ALLOCA sizes.  It records generation history, not decoder syntax. *)
Definition entry_code_history_def:
  entry_code_history a b <=>
    a.cs_next_id <= b.cs_next_id /\
    (!i. MEM i (state_insts a) ==> MEM i (state_insts b)) /\
    (!i. MEM i (state_insts b) /\ ~MEM i (state_insts a) ==>
      a.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id)
End

Theorem entry_code_history_refl[simp]:
  entry_code_history a a
Proof
  simp[entry_code_history_def]
QED

Theorem entry_code_history_trans:
  entry_code_history a b /\ entry_code_history b c ==>
  entry_code_history a c
Proof
  rw[entry_code_history_def] >>
  metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

Theorem entry_code_history_ids_below:
  entry_code_history a b /\ abi_decoder_code_ids_below a ==>
  abi_decoder_code_ids_below b
Proof
  simp[entry_code_history_def, abi_decoder_code_ids_below_def,
       decoder_code_member_state_insts] >>
  metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem entry_code_history_suffix_inverse:
  entry_code_history a b /\ MEM i (state_insts b) /\ i.inst_id < a.cs_next_id ==>
  MEM i (state_insts a)
Proof
  simp[entry_code_history_def] >> metis_tac[NOT_LESS]
QED

Theorem entry_code_history_initial:
  abi_decoder_code_ids_below (initial_compile_state name)
Proof
  simp[abi_decoder_code_ids_below_def, abi_decoder_code_member_def,
       initial_compile_state_def]
QED

Theorem entry_code_history_emit_op:
  emit_op opc ops a = (v,b) ==> entry_code_history a b
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[entry_code_history_def, state_insts_def, all_blocks_def, MEM_MAP,
       MEM_FLAT, mk_inst_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem entry_code_history_new_block:
  new_block label a = (v,b) ==> entry_code_history a b
Proof
  simp[new_block_def] >> strip_tac >> gvs[] >>
  simp[entry_code_history_def, state_insts_def, all_blocks_def, FLAT_APPEND] >>
  metis_tac[]
QED
