(* TOP-LEVEL: exact allocation and rounded-live-copy program emitted when a
   bytes/string value is materialized. Helpers describe its six SSA outputs. *)
Theory bytesSnapshotCode
Ancestors
  memoryValueSnapshot abiBytestringCode eventTopicValueProps
  stmtLowering exprLowering context compileEnv exprLoweringProps emitHelper
  venomInst list rich_list arithmetic

Definition bytes_snapshot_insts_def:
  bytes_snapshot_insts id names capacity src =
    [mk_inst id ALLOCA [Lit (n2w capacity)] [EL 0 names];
     mk_inst (id + 1) MLOAD [src] [EL 1 names];
     mk_inst (id + 2) NOT [Lit 31w] [EL 2 names];
     mk_inst (id + 3) ADD [Var (EL 1 names); Lit 31w] [EL 3 names];
     mk_inst (id + 4) AND [Var (EL 3 names); Var (EL 2 names)] [EL 4 names];
     mk_inst (id + 5) ADD [Var (EL 4 names); Lit 32w] [EL 5 names];
     mk_inst (id + 6) MCOPY [Var (EL 0 names); src; Var (EL 5 names)] []]
End

Theorem compiler_var_names_six:
  !var_base. compiler_var_names var_base 6 =
    [STRING #"%" (toString var_base); STRING #"%" (toString (var_base + 1));
     STRING #"%" (toString (var_base + 2)); STRING #"%" (toString (var_base + 3));
     STRING #"%" (toString (var_base + 4)); STRING #"%" (toString (var_base + 5))]
Proof
  simp[compiler_var_names_def, GENLIST_CONS]
QED

Theorem compile_materialize_bytes_code:
  !cenv ty src cs op cs'.
    is_bytestring_type ty /\
    compile_materialize_vv cenv ty (StackValue ty src) cs = (op,cs') ==>
    op = Var (EL 0 (compiler_var_names cs.cs_next_var 6)) /\
    emitted_insts cs cs' = bytes_snapshot_insts cs.cs_next_id
      (compiler_var_names cs.cs_next_var 6) (type_memory_bytes cenv ty) src /\
    same_blocks cs cs' /\
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs' /\
    cs'.cs_next_var = cs.cs_next_var + 6
Proof
  rpt gen_tac >> strip_tac >>
  `~is_word_type ty` by (drule_all bytestring_type_not_word >> simp[]) >>
  gvs[compile_materialize_vv_def, unwrap_value_def, compile_alloc_buffer_def,
    compile_store_memory_def, compile_store_bytestring_def, compile_bytestring_copy_len_def,
    emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emitted_insts_def,
    bytes_snapshot_insts_def, compiler_var_names_EL, same_blocks_def,
    DROP_APPEND1, DROP_LENGTH_NIL]
QED

Theorem bytes_snapshot_straight:
  !id names capacity src.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (bytes_snapshot_insts id names capacity src)
Proof
  simp[bytes_snapshot_insts_def, mk_inst_def, is_terminator_def]
QED

Theorem bytes_snapshot_length[simp]:
  !id names capacity src. LENGTH (bytes_snapshot_insts id names capacity src) = 7
Proof
  simp[bytes_snapshot_insts_def]
QED
