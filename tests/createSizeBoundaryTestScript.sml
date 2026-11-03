Theory createSizeBoundaryTest
Ancestors
  vyperCreate venomExecSemantics venomCallOracleDefs venomState
  asmSem emitHelper vfmConstants
Libs
  wordsLib

Theorem create_oversized_does_not_consume:
  exec_create (mk_inst 0 CREATE [] ["out"]) s value offset 49153w salt =
    Abort ExHalt_abort (halt_state (set_returndata [] s))
Proof
  simp[exec_create_def, mk_inst_def, max_code_size_def]
QED

Theorem create_at_limit_consumes:
  exec_create (mk_inst 0 CREATE [] ["out"]) s value offset 49152w salt =
    OK (update_var "out"
      (FST (consume_create_outcome
        (venom_create_request s value offset 49152w salt) s))
      (SND (consume_create_outcome
        (venom_create_request s value offset 49152w salt) s)))
Proof
  simp[exec_create_def, mk_inst_def, max_code_size_def]
QED

Theorem asm_create_oversized_does_not_enter:
  s.as_stack = value::offset::49153w::rest ==>
  asm_exec_create s = AsmFault (s with as_returndata := [])
Proof
  simp[asm_exec_create_def, max_code_size_def]
QED

Theorem asm_create2_oversized_does_not_enter:
  s.as_stack = value::offset::49153w::salt::rest ==>
  asm_exec_create2 s = AsmFault (s with as_returndata := [])
Proof
  simp[asm_exec_create2_def, max_code_size_def]
QED

Theorem raw_create_oversized_total_rejected:
  encode_create_ctor_args tenv tys ops.co_ctor_args = SOME args /\
  LENGTH bytecode + LENGTH args = 49153 ==>
  OPTION_MAP (\info. info.cc_size_ok)
    (build_create_code tenv RawCreate
      (ops with co_code_src := BytecodeCodeSource bytecode) accounts tys size) = SOME F
Proof
  rw[build_create_code_def, raw_create_initcode_def, max_code_size_def]
QED

Theorem raw_create_total_at_limit_accepted:
  encode_create_ctor_args tenv tys ops.co_ctor_args = SOME args /\
  LENGTH bytecode + LENGTH args = 49152 ==>
  OPTION_MAP (\info. info.cc_size_ok)
    (build_create_code tenv RawCreate
      (ops with co_code_src := BytecodeCodeSource bytecode) accounts tys size) = SOME T
Proof
  rw[build_create_code_def, raw_create_initcode_def, max_code_size_def]
QED
