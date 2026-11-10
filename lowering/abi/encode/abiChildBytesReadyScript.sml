(* TOP-LEVEL: actual bytestring child calls retain parent head/offset names,
   protect input operands, and inherit their memory precondition through
   the dynamic-child address prefix. *)
Theory abiChildBytesReady
Ancestors
  abiChildCode abiChildPrefix abiBytestringCorrect abiBytestringCode abiStaticLoopCode
  typedArrayLoopNames ssaOperandFrame memoryReadProps
  compileEnv venomState venomExecSemantics list words arithmetic

Theorem abi_child_bytes_input_names:
  !arg_op var_base.
    EVERY (\name. arg_op <> Var name) (compiler_var_names var_base 13) ==>
    EVERY (\name. arg_op <> Var name) (compiler_var_names var_base 3) /\
    EVERY (\name. arg_op <> Var name) (compiler_var_names (var_base + 3) 9) /\
    arg_op <> Var (compiler_var_name (var_base + 12) 0)
Proof
  rpt gen_tac >> DISCH_TAC >> rpt conj_tac
  >- (mp_tac (Q.SPECL [`arg_op`, `var_base`, `13`, `3`] compiler_var_names_avoid_prefix) >> simp[])
  >- (mp_tac (Q.SPECL [`arg_op`, `var_base`, `13`, `3`, `9`] compiler_var_names_avoid_segment) >> simp[]) >>
  mp_tac (Q.SPECL [`arg_op`, `var_base`, `13`, `12`] compiler_var_names_avoid_index) >>
  simp[compiler_var_name_def]
QED

Theorem abi_child_bytes_saved_names:
  !var_base.
    EVERY (\name.
      Var (compiler_var_name var_base 0) <> Var name /\
      Var (compiler_var_name var_base 1) <> Var name /\
      Var (compiler_var_name var_base 2) <> Var name)
      (compiler_var_names (var_base + 3) 9)
Proof
  gen_tac >> simp_tac bool_ss [EVERY_CONJ] >> rpt conj_tac >>
  irule compiler_var_names_before >> simp[]
QED

Theorem bytestring_abi_pre_memory:
  !dst_addr src_addr bs before after.
    after.vs_memory = before.vs_memory ==>
    (bytestring_abi_pre dst_addr src_addr bs after = bytestring_abi_pre dst_addr src_addr bs before)
Proof
  simp[bytestring_abi_pre_def, mload_def, read_memory_def]
QED
