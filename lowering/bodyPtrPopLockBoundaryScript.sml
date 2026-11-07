Theory bodyPtrPopLockBoundary
Ancestors bodyPtrPopClampBoundary bodyPtrPopCompilerBoundary
  bodyPtrPopBoundaryContract bodyPtrPopGuardedWindow context
  emitHelper compileEnv venomInst list

Theorem pop_lock_template:
  MAP (\i. i.inst_opcode) t =
    ([ld;EQ;ISZERO;ASSERT] ++ if view then [] else [store]) /\
  ld <> SUB /\ store <> SUB /\ pop_boundary_clean p ==>
  pop_boundary_clean (p ++ t)
Proof
  Cases_on `view` >> simp[MAP_EQ_CONS] >> rpt strip_tac >> gvs[] >>
  irule pop_boundary_append_no_sub >> simp[] >>
  simp[pop_guard4_def] >> rpt strip_tac >> gvs[mk_inst_def]
QED

Theorem pop_compile_lock_shape:
  compile_nonreentrant_lock key trans view sa = (r,sb) ==>
  ?t. sb.cs_current_insts = sa.cs_current_insts ++ t /\
    sb.cs_blocks = sa.cs_blocks /\
    MAP (\i. i.inst_opcode) t =
      ([(if trans then TLOAD else SLOAD); EQ; ISZERO; ASSERT] ++
        if view then [] else [if trans then TSTORE else SSTORE])
Proof
  Cases_on `trans` >> Cases_on `view` >>
  simp[compile_nonreentrant_lock_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >> gvs[] >>
  irule_at Any EQ_REFL >> simp[mk_inst_def]
QED

Theorem pop_compile_nonreentrant_lock_boundary:
  pop_comp_boundary sa /\ compile_nonreentrant_lock key trans view sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  strip_tac >> drule pop_compile_lock_shape >> strip_tac >>
  gvs[pop_comp_boundary_def] >> irule pop_lock_template >>
  goal_assum drule >> simp[] >>
  qexistsl_tac [`if trans then TSTORE else SSTORE`, `view`] >>
  Cases_on `trans` >> simp[]
QED
