Theory bodyPtrPopDivBoundary
Ancestors bodyPtrPopCompilerBoundary bodyPtrPopGuardBoundary exprLowering
  bodyPtrPopBoundaryContract bodyPtrPopGuardedWindow bodyPtrPopWindow
  emitHelper compileEnv venomInst list rich_list

Theorem pop_signed256_div_append_shape:
  is_signed_type ty /\ type_bits ty = 256 /\
  compile_safe_div x y ty sa = (out,sb) ==>
  ?t. sb.cs_current_insts = sa.cs_current_insts ++ t /\
    sb.cs_blocks = sa.cs_blocks /\
    MAP (\i. i.inst_opcode) t =
      [ISZERO; ISZERO; ASSERT; SDIV; EQ; NOT; ISZERO; AND; ISZERO; ASSERT]
Proof
  strip_tac >> gvs[compile_safe_div_def,
    emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  irule_at Any EQ_REFL >> simp[mk_inst_def]
QED

Theorem pop_signed256_template_boundary:
  MAP (\i. i.inst_opcode) t =
    [ISZERO; ISZERO; ASSERT; SDIV; EQ; NOT; ISZERO; AND; ISZERO; ASSERT] /\
  pop_boundary_clean p ==>
  pop_boundary_clean (p ++ t)
Proof
  simp[MAP_EQ_CONS] >> rpt strip_tac >> gvs[] >>
  rename1 `pop_boundary_clean (p ++ [a;b;c;d;e;f;g;h;j;k])` >>
  `occurs5 pop_guarded5 (p ++ [a;b;c;d] ++ [e;f;g;h;j;k]) <=>
   occurs5 pop_guarded5 p \/ occurs5 pop_guarded5 [e;f;g;h;j;k]` by
    (irule pop_guard_template_separation >> simp[]) >>
  pop_assum (assume_tac o SIMP_RULE std_ss [GSYM APPEND_ASSOC, APPEND]) >>
  gvs[APPEND, pop_boundary_clean_def, occurs5_cons_take,
      pop_guarded5_head_nonload] >>
  simp[pop_guard4_def] >> rpt strip_tac >>
  gvs[mk_inst_def]
QED

Theorem pop_signed256_div_boundary:
  is_signed_type ty /\ type_bits ty = 256 /\
  compile_safe_div x y ty sa = (out,sb) /\ pop_comp_boundary sa ==>
  pop_comp_boundary sb
Proof
  strip_tac >> drule_all pop_signed256_div_append_shape >> strip_tac >>
  gvs[pop_comp_boundary_def] >>
  irule pop_signed256_template_boundary >> goal_assum drule >> simp[]
QED
