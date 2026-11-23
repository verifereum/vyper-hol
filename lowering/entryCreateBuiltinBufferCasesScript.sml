(* First-exit and selected-cut facts for buffer-valued builtins. *)
Theory entryCreateBuiltinBufferCases
Ancestors
  entryCreateEffectFocus entryCreateAdminSequence
  createSizeCutCode abiEncoderProps exprSimHash builtinHashing context
  emitHelper emitHelperProps compileEnv exprLoweringProps fragExec
  venomInst venomExecSemantics list rich_list arithmetic

(* The suffix starts after the hash argument has been evaluated. In
   particular SHA's STATICCALL is not a Venom INVOKE. *)
Theorem create_hash_suffix_layout:
  (compile_keccak256_bytes x a = (op,b) \/
   compile_keccak256_bytesm x m a = (op,b) \/
   compile_sha256_bytes x a = (op,b) \/
   compile_sha256_bytesm x m a = (op,b)) ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\
             i.inst_opcode <> CREATE2) (emitted_insts a b)
Proof
  strip_tac >>
  gvs[compile_keccak256_bytes_def, compile_keccak256_bytesm_def,
      compile_sha256_bytes_def, compile_sha256_bytesm_def,
      contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
      fresh_var_def, emit_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[is_terminator_def, mk_inst_def, frag_ids_def]
QED

Theorem create_hash_suffix_cut:
  (compile_keccak256_bytes x a = (op,b) \/
   compile_keccak256_bytesm x m a = (op,b) \/
   compile_sha256_bytes x a = (op,b) \/
   compile_sha256_bytesm x m a = (op,b)) /\
  fn_has_code a b f /\ create_operand_at a s ==>
  create_operand_cut a b E C f tops cx st0 source (es,s)
Proof
  disch_then (CONJUNCTS_THEN2 (strip_assume_tac o MATCH_MP create_hash_suffix_layout) strip_assume_tac) >>
  irule create_admin_sequence_cut >> fs[EVERY_MEM]
QED
