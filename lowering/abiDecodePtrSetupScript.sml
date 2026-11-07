(* Composition boundaries for the builtin header and output allocation. *)
Theory abiDecodePtrSetup
Ancestors
  abiDecodePtrHeaderLoad abiDecodePtrLengthGuard abiDecodePtrInputWindow
  abiBuiltinDecodeSetup abiBuiltinDecodeHeader abiBuiltinLengthGuard
  abiBuiltinPrefix bodyPtrHashBuiltinsAllocFrame bodyPtrHashBuiltinsShaAllocPath
  exprSimPtrProps appendStorageGhostPtr bodyPtrBopScalarCompile
  fragExec fragGasPathPtr emitHelper emitHelperProps exprLoweringProps
  compileEnv freshWrites ptrDiscipline venomState list rich_list pred_set

Theorem abi_builtin_decode_header_trace_ptr:
  abi_builtin_decode_header data mn mx sa = (inputs,sh) ==>
  ?len sm src sb.
    emit_op MLOAD [data] sa = (len,sm) /\
    emit_op ADD [data; Lit 32w] sm = (src,sb) /\
    abi_builtin_length_guard len mn mx sb = ((),sh) /\
    inputs = (len,src)
Proof
  simp[abi_builtin_decode_header_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED
