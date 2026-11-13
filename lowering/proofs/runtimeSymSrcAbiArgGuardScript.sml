Theory runtimeSymSrcAbiArgGuard
Ancestors
  runtimeSymSrcEmission moduleLowering emitHelper loweringShapeDefs venomInst list
  stackPlanTypes compileEnv

Theorem runtime_sym_abi_arg_ptr_guard:
  ~is_label_operand actual_src /\ ~is_label_operand parent /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_abi_arg_ptr_guard load_opc actual_src parent s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `load_opc = CALLDATALOAD` >>
  simp[compile_abi_arg_ptr_guard_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def]
  >- (rpt (pairarg_tac >> simp[]) >> strip_tac >>
      qpat_x_assum `emit_op LT _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
      qpat_x_assum `emit_op ISZERO _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
      drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]) >>
  strip_tac >> gvs[]
QED
