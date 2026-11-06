Theory bodyPtrPopConversionGuardBoundary
Ancestors bodyPtrPopClampBoundary bodyPtrPopArithmeticBoundary
  bodyPtrPopBoundaryContract bodyPtrPopCompilerBoundary
  exprLowering emitHelper compileEnv venomInst list

Theorem pop_guard_suffix_template:
  EVERY (\i. i.inst_opcode <> SUB) t /\
  MAP (\i. i.inst_opcode) t = ops ++ [op;ASSERT] /\
  op <> ISZERO /\ pop_boundary_clean p ==>
  pop_boundary_clean (p ++ t)
Proof
  simp[MAP_EQ_APPEND, MAP_EQ_CONS] >> rpt strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_boundary_append_no_sub >> simp[] >>
  simp[pop_guard4_def] >> rpt strip_tac >> gvs[mk_inst_def]
QED

Theorem pop_guard_short_suffix_template:
  EVERY (\i. i.inst_opcode <> SUB) t /\
  MAP (\i. i.inst_opcode) t = ops ++ [op;ISZERO;ASSERT] /\
  op <> ISZERO /\ pop_boundary_clean p ==>
  pop_boundary_clean (p ++ t)
Proof
  simp[MAP_EQ_APPEND, MAP_EQ_CONS] >> rpt strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_boundary_append_no_sub >> simp[] >>
  simp[pop_guard4_def] >> rpt strip_tac >> gvs[mk_inst_def]
QED
