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
    EVERY (\name. arg_op <> Var name) (compiler_var_names var_base 12) ==>
    EVERY (\name. arg_op <> Var name) (compiler_var_names var_base 3) /\
    EVERY (\name. arg_op <> Var name) (compiler_var_names (var_base + 3) 8) /\
    arg_op <> Var (compiler_var_name (var_base + 11) 0)
Proof
  rpt gen_tac >> DISCH_TAC >> rpt conj_tac
  >- (mp_tac (Q.SPECL [`arg_op`, `var_base`, `12`, `3`] compiler_var_names_avoid_prefix) >> simp[])
  >- (mp_tac (Q.SPECL [`arg_op`, `var_base`, `12`, `3`, `8`] compiler_var_names_avoid_segment) >> simp[]) >>
  mp_tac (Q.SPECL [`arg_op`, `var_base`, `12`, `11`] compiler_var_names_avoid_index) >>
  simp[compiler_var_name_def]
QED

Theorem abi_child_bytes_saved_names:
  !var_base.
    EVERY (\name.
      Var (compiler_var_name var_base 0) <> Var name /\
      Var (compiler_var_name var_base 1) <> Var name /\
      Var (compiler_var_name var_base 2) <> Var name)
      (compiler_var_names (var_base + 3) 8)
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

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed bytestring child preparation: " ^ name)
  end) (DB.thms "abiChildBytesReady")
