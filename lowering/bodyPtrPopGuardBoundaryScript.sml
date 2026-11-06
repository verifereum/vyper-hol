Theory bodyPtrPopGuardBoundary
Ancestors bodyPtrPopGuardedWindow bodyPtrPopWindow bodyPtrPopProducerAudit
  venomInst list rich_list

Theorem pop_guarded5_head_nonload:
  i.inst_opcode <> SLOAD /\ i.inst_opcode <> TLOAD ==>
  ~pop_guarded5 (i::xs)
Proof
  simp[pop_guarded5_def, mk_inst_def] >> rpt strip_tac >>
  Cases_on `tr` >> gvs[]
QED

Theorem pop_guard_template_separation:
  i0.inst_opcode = ISZERO /\ i1.inst_opcode = ISZERO /\
  i2.inst_opcode = ASSERT /\ i3.inst_opcode <> SUB /\
  i3.inst_opcode <> SLOAD /\ i3.inst_opcode <> TLOAD ==>
  (occurs5 pop_guarded5 (p ++ [i0;i1;i2;i3] ++ q) <=>
   occurs5 pop_guarded5 p \/ occurs5 pop_guarded5 q)
Proof
  strip_tac >> Induct_on `p`
  >- simp[occurs5_cons_take, pop_guarded5_head_nonload] >>
  gen_tac >> simp[occurs5_cons_take] >>
  Cases_on `p`
  >- (`~pop_guarded5 [h;i0;i1;i2;i3]` by
        (simp[pop_guarded5_def] >> rpt strip_tac >> gvs[mk_inst_def]) >> simp[]) >>
  namedCases_on `t` ["", "j rest"]
  >- (`~pop_guarded5 [h;h';i0;i1;i2]` by
        (simp[pop_guarded5_def] >> rpt strip_tac >> gvs[mk_inst_def]) >> simp[]) >>
  namedCases_on `rest` ["", "k rest2"]
  >- (`~pop_guarded5 [h;h';j;i0;i1]` by
        (simp[pop_guarded5_def] >> rpt strip_tac >> gvs[mk_inst_def]) >> simp[]) >>
  namedCases_on `rest2` ["", "l rest3"]
  >- (`~pop_guarded5 [h;h';j;k;i0]` by
        (simp[pop_guarded5_def] >> rpt strip_tac >> gvs[mk_inst_def]) >> simp[]) >>
  simp[] >> metis_tac[]
QED

Theorem pop_guard_opcodes_separation:
  MAP (\i. i.inst_opcode) t = [ISZERO; ISZERO; ASSERT; op] /\
  op <> SUB /\ op <> SLOAD /\ op <> TLOAD ==>
  (occurs5 pop_guarded5 (p ++ t ++ q) <=>
   occurs5 pop_guarded5 p \/ occurs5 pop_guarded5 q)
Proof
  simp[MAP_EQ_CONS] >> rpt strip_tac >> gvs[] >>
  irule pop_guard_template_separation >> simp[]
QED

Theorem pop_unsigned_div_append_shape:
  ~is_signed_type ty /\ compile_safe_div x y ty sa = (out,sb) ==>
  ?t. sb.cs_current_insts = sa.cs_current_insts ++ t /\
    MAP (\i. i.inst_opcode) t = [ISZERO; ISZERO; ASSERT; Div]
Proof
  strip_tac >> gvs[exprLoweringTheory.compile_safe_div_def,
    emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
    compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
    compileEnvTheory.comp_return_def, compileEnvTheory.fresh_var_def,
    compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def] >>
  rpt strip_tac >> gvs[] >> irule_at Any EQ_REFL >> simp[mk_inst_def]
QED

Theorem pop_mod_append_shape:
  compile_safe_mod x y ty sa = (out,sb) ==>
  ?t. sb.cs_current_insts = sa.cs_current_insts ++ t /\
    MAP (\i. i.inst_opcode) t =
      [ISZERO; ISZERO; ASSERT; if is_signed_type ty then SMOD else Mod]
Proof
  Cases_on `is_signed_type ty` >>
  simp[exprLoweringTheory.compile_safe_mod_def,
    emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
    compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
    compileEnvTheory.comp_return_def, compileEnvTheory.fresh_var_def,
    compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def] >>
  rpt strip_tac >> gvs[] >> irule_at Any EQ_REFL >> simp[mk_inst_def]
QED

Theorem pop_unsigned_div_guard_continuation:
  ~is_signed_type ty /\ compile_safe_div x y ty sa = (out,sb) ==>
  (occurs5 pop_guarded5 (sb.cs_current_insts ++ q) <=>
   occurs5 pop_guarded5 sa.cs_current_insts \/ occurs5 pop_guarded5 q)
Proof
  strip_tac >> drule_all pop_unsigned_div_append_shape >> strip_tac >>
  gvs[] >> irule pop_guard_opcodes_separation >>
  qexists_tac `Div` >> simp[]
QED

Theorem pop_mod_guard_continuation:
  compile_safe_mod x y ty sa = (out,sb) ==>
  (occurs5 pop_guarded5 (sb.cs_current_insts ++ q) <=>
   occurs5 pop_guarded5 sa.cs_current_insts \/ occurs5 pop_guarded5 q)
Proof
  strip_tac >> drule pop_mod_append_shape >> strip_tac >>
  gvs[] >> irule pop_guard_opcodes_separation >>
  qexists_tac `if is_signed_type ty then SMOD else Mod` >>
  Cases_on `is_signed_type ty` >> simp[]
QED
