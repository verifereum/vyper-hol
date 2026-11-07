Theory bodyPtrPopAbiDecodePrimitiveBoundary
Ancestors bodyPtrPopClampBoundary bodyPtrPopCompilerBoundary
  bodyPtrPopArithmeticBoundary bodyPtrPopAllocationBoundary
  bodyPtrPopBoundaryContract bodyPtrPopGuardedWindow abiEncoder
  compileEnv emitHelper venomInst list
Libs monadsyntax

Theorem pop_abi_signed_clamp_template:
  MAP (\i. i.inst_opcode) t = [SIGNEXTEND;EQ;ASSERT] /\
  pop_boundary_clean p ==> pop_boundary_clean (p ++ t)
Proof
  simp[MAP_EQ_CONS] >> rpt strip_tac >> gvs[] >>
  irule pop_boundary_append_no_sub >> simp[] >>
  simp[pop_guard4_def] >> rpt strip_tac >> gvs[mk_inst_def]
QED

Theorem pop_compile_abi_int_clamp_boundary:
  pop_comp_boundary sa /\ compile_abi_int_clamp v bits signed sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `signed` >>
  simp[compile_abi_int_clamp_def, emit_op_def, emit_void_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND]
  >- (irule pop_abi_signed_clamp_template >> simp[mk_inst_def]) >>
  irule pop_clamp_short_template >> simp[mk_inst_def]
QED

Theorem pop_compile_abi_bytes_clamp_boundary:
  pop_comp_boundary sa /\ compile_abi_bytes_clamp v m sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_abi_bytes_clamp_def, emit_op_def, emit_void_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_clamp_short_template >> simp[mk_inst_def]
QED

Theorem pop_compile_abi_clamp_basetype_boundary:
  pop_comp_boundary sa /\ compile_abi_clamp_basetype v clamp sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `clamp` >> simp[compile_abi_clamp_basetype_def] >> rpt strip_tac
  >- (drule_all pop_comp_boundary_return >> simp[])
  >- (drule_all pop_compile_abi_int_clamp_boundary >> simp[])
  >- (drule_all pop_compile_abi_bytes_clamp_boundary >> simp[]) >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def,
      pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_clamp_short_template >> simp[mk_inst_def]
QED

Theorem pop_compile_abi_decode_static_boundary:
  load_opc <> ASSERT /\ pop_comp_boundary sa /\
  (!v s x t. pop_comp_boundary s /\ clamp v s = (x,t) ==> pop_comp_boundary t) /\
  compile_abi_decode_static src dst load_opc clamp sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_abi_decode_static_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
         first_x_assum drule_all] >> simp[]
QED

Theorem pop_abi_short_check_boundary:
  op <> SUB /\ op <> ISZERO /\ pop_comp_boundary sa /\
  (do a <- emit_op op args;
      b <- emit_op ISZERO [a]; emit_void ASSERT [b] od) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_clamp_short_template >> simp[mk_inst_def]
QED

Theorem pop_compile_getelemptr_abi_boundary:
  load_opc <> ASSERT /\ pop_comp_boundary sa /\
  compile_getelemptr_abi src dyn off load_opc hi sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >>
  simp[compile_getelemptr_abi_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (FIRST [
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_abi_short_check_boundary >> simp[] >> NO_TAC),
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
     disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac)]) >>
  FIRST [drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_all pop_comp_boundary_return] >> simp[]
QED

Theorem pop_abi_two_bounds_template:
  MAP (\i. i.inst_opcode) t = [LT;ISZERO;ASSERT;ADD;GT;ISZERO;ASSERT] /\
  pop_boundary_clean p ==> pop_boundary_clean (p ++ t)
Proof
  simp[MAP_EQ_CONS] >> rpt strip_tac >> gvs[] >>
  irule pop_boundary_append_no_sub >> simp[] >>
  simp[pop_guard4_def] >> rpt strip_tac >> gvs[mk_inst_def]
QED

Theorem pop_abi_two_bounds_boundary:
  pop_comp_boundary sa /\
  (do bad <- emit_op LT [pval; src];
      ok <- emit_op ISZERO [bad]; ignored <- emit_void ASSERT [ok];
      eend <- emit_op ADD [pval; szval];
      oob <- emit_op GT [eend; hi];
      ok2 <- emit_op ISZERO [oob]; emit_void ASSERT [ok2] od) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_abi_two_bounds_template >> simp[mk_inst_def]
QED

Theorem pop_compile_abi_decode_dyn_elem_ptr_boundary:
  load_opc <> ASSERT /\ pop_comp_boundary sa /\
  compile_abi_decode_dyn_elem_ptr load_opc elem_src src hi sz sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `hi = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (FIRST [
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_abi_two_bounds_boundary >> simp[] >> NO_TAC),
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
     disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac)]) >>
  FIRST [drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_all pop_comp_boundary_return] >> simp[]
QED
