(* TOP-LEVEL: exact five-instruction program emitted by the compiler's
   runtime-length bytes/string memory copy. *)
Theory bytesCopyCode
Ancestors
  abiBytestringCode context compileEnv exprLoweringProps emitHelper
  venomInst list rich_list arithmetic

Definition bytes_copy_insts_def:
  bytes_copy_insts id names dst src =
    [mk_inst id MLOAD [src] [EL 0 names];
     mk_inst (id + 1) ADD [Var (EL 0 names); Lit 31w] [EL 1 names];
     mk_inst (id + 2) AND [Var (EL 1 names); Lit (i2w (- &32))] [EL 2 names];
     mk_inst (id + 3) ADD [Var (EL 2 names); Lit 32w] [EL 3 names];
     mk_inst (id + 4) MCOPY [dst; src; Var (EL 3 names)] []]
End

Theorem compiler_var_names_four:
  !var_base. compiler_var_names var_base 4 =
    [STRING #"%" (toString var_base); STRING #"%" (toString (var_base + 1));
     STRING #"%" (toString (var_base + 2)); STRING #"%" (toString (var_base + 3))]
Proof
  simp[compiler_var_names_def, GENLIST_CONS]
QED

Theorem compile_store_bytestring_code:
  !src dst cs ret cs'.
    compile_store_bytestring src dst cs = (ret,cs') ==>
    ret = () /\
    emitted_insts cs cs' = bytes_copy_insts cs.cs_next_id
      (compiler_var_names cs.cs_next_var 4) dst src /\
    same_blocks cs cs' /\
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs' /\
    cs'.cs_next_var = cs.cs_next_var + 4
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_store_bytestring_def, compile_bytestring_copy_len_def,
    emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emitted_insts_def,
    bytes_copy_insts_def, compiler_var_names_EL, same_blocks_def,
    DROP_APPEND1, DROP_LENGTH_NIL]
QED

Theorem bytes_copy_straight:
  !id names dst src.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (bytes_copy_insts id names dst src)
Proof
  simp[bytes_copy_insts_def, mk_inst_def, is_terminator_def]
QED
