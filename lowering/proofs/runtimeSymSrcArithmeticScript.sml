Theory runtimeSymSrcArithmetic
Ancestors
  runtimeSymSrcInterfaces runtimeSymSrcEmission runtimeSymSrcGeneratorContracts
  runtimeSymSrcBinops runtimeSymSrcConversions runtimeSymSrcLiteralEnv
  runtimeSymSrcNameFastpaths runtimeSymSrcDynarrayPop
  exprLowering builtinMath compileEnv emitHelper loweringShapeDefs list venomInst

Theorem runtime_sym_addmod:
  EVERY (\x. ~is_label_operand x) [a;b;m] /\
  EVERY runtime_sym_inst (state_insts s) /\ compile_addmod a b m s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_addmod_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[] >> strip_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >> simp[]
QED

Theorem runtime_sym_mulmod:
  EVERY (\x. ~is_label_operand x) [a;b;m] /\
  EVERY runtime_sym_inst (state_insts s) /\ compile_mulmod a b m s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_mulmod_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[] >> strip_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >> simp[]
QED

Theorem runtime_sym_pow_mod256:
  ~is_label_operand a /\ ~is_label_operand b /\
  EVERY runtime_sym_inst (state_insts s) /\ compile_pow_mod256 a b s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_pow_mod256_def] >> strip_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >> simp[]
QED

Theorem runtime_sym_math:
  runtime_sym_math_clauses
Proof
  rewrite_tac[runtime_sym_math_clauses_def] >>
  conj_tac >- MATCH_ACCEPT_TAC runtime_sym_addmod >>
  conj_tac >- MATCH_ACCEPT_TAC runtime_sym_mulmod >>
  MATCH_ACCEPT_TAC runtime_sym_pow_mod256
QED

Theorem runtime_sym_expr_primitives:
  runtime_sym_expr_primitive_clauses
Proof
  rewrite_tac[runtime_sym_expr_primitive_clauses_def] >>
  conj_tac >- MATCH_ACCEPT_TAC runtime_sym_literal_vv >>
  conj_tac >- MATCH_ACCEPT_TAC runtime_sym_env_var >>
  conj_tac >- MATCH_ACCEPT_TAC runtime_sym_binop >>
  conj_tac >- MATCH_ACCEPT_TAC runtime_sym_invert >>
  conj_tac >- MATCH_ACCEPT_TAC runtime_sym_neg >>
  conj_tac >- MATCH_ACCEPT_TAC runtime_sym_type_convert >>
  MATCH_ACCEPT_TAC runtime_sym_dynarray_pop
QED

Theorem runtime_sym_arithmetic_name_fastpaths:
  runtime_sym_context_clauses ==> runtime_sym_name_fastpath_clauses
Proof
  strip_tac >> irule runtime_sym_name_fastpaths >>
  simp[runtime_sym_math]
QED
