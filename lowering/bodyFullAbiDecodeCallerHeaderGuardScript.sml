(* Scalar certificate for the finite length guard before allocation. *)
Theory bodyFullAbiDecodeCallerHeaderGuard
Ancestors
  abiBuiltinDecodeHeader abiBuiltinLengthGuard abiBuiltinBoundTests
  bodyPtrBopScalarSeq bodyPtrBopScalarCompile
  emitHelperProps exprLoweringProps compileEnv emitHelper freshWrites
  venomInst list rich_list pred_set

Theorem abi_decode_caller_length_guard_scalar:
  abi_builtin_length_guard len mn mx sa = ((),sb) /\ len IN A /\
  (!w. Lit w IN A) /\ (!x. x IN R ==> not_fresh_at sa x) ==>
  ?B. bop_scalar_seq R A (emitted_insts sa sb) B /\ A SUBSET B
Proof
  Cases_on `mn = mx` >>
  simp[abi_builtin_length_guard_def, abi_builtin_interval_guard_def,
    abi_builtin_eq_guard_def, abi_builtin_bound_test_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, bop_scalar_seq_def, mk_inst_def] >>
  simp[SUBSET_DEF] >>
  gvs[not_fresh_at_def] >> metis_tac[]
QED
