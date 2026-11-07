(* Proof-only boundaries for statement shadow compilation. *)
Theory gasShadowCompileStmtBase
Ancestors
  gasShadowState gasShadow gasShadowCompilePure stmtLowering compileEnv emitHelper venomInst vyperAST list

Theorem gas_shadow_inst_terminator:
  gas_shadow_inst i j ==>
  is_terminator i.inst_opcode = is_terminator j.inst_opcode
Proof
  rw[gas_shadow_inst_def] >> simp[is_terminator_def]
QED

Theorem gas_shadow_insts_terminated:
  !xs ys. LIST_REL gas_shadow_inst xs ys ==>
  (case xs of [] => F | _ => is_terminator (LAST xs).inst_opcode) =
  (case ys of [] => F | _ => is_terminator (LAST ys).inst_opcode)
Proof
  Induct >> Cases_on `ys` >> simp[] >> rpt strip_tac >>
  Cases_on `xs`
  >- (gvs[] >> irule gas_shadow_inst_terminator >> simp[]) >>
  Cases_on `t` >> gvs[] >>
  first_x_assum (qspec_then `h'''::t''` mp_tac) >> simp[]
QED

Theorem gas_shadow_state_terminated:
  gas_shadow_state s t ==> block_is_terminated s = block_is_terminated t
Proof
  strip_tac >> fs[gas_shadow_state_def] >>
  drule gas_shadow_insts_terminated >>
  Cases_on `s.cs_current_insts` >> Cases_on `t.cs_current_insts` >>
  simp[block_is_terminated_def]
QED

Theorem gas_shadow_compiles_get_terminated:
  (!b. gas_shadow_compiles (h b) (k b)) ==>
  gas_shadow_compiles
    (comp_bind comp_get (\s. h (block_is_terminated s)))
    (comp_bind comp_get (\s. k (block_is_terminated s)))
Proof
  rw[gas_shadow_compiles_def, comp_bind_def, comp_get_def] >>
  drule gas_shadow_state_terminated >> strip_tac >>
  first_x_assum (qspecl_then [`block_is_terminated s`, `s`, `t`] mp_tac) >>
  simp[]
QED

Theorem gas_shadow_compiles_emit_jmp_if_not_terminated:
  gas_shadow_compiles (emit_jmp_if_not_terminated lbl)
    (emit_jmp_if_not_terminated lbl)
Proof
  rewrite_tac[emit_jmp_if_not_terminated_def] >>
  ho_match_mp_tac gas_shadow_compiles_get_terminated >> gen_tac >>
  Cases_on `b` >>
  simp[gas_shadow_compiles_return, gas_shadow_compiles_emit_inst]
QED

Theorem gas_shadow_is_memory_view[simp]:
  is_memory_view (gas_shadow_expr e) = is_memory_view e
Proof
  Cases_on `e` >> simp[gas_shadow_expr_def, is_memory_view_def]
QED

Theorem gas_shadow_is_empty_value_expr[simp]:
  is_empty_value_expr (gas_shadow_expr e) = is_empty_value_expr e
Proof
  Cases_on `e` >> simp[gas_shadow_expr_def, is_empty_value_expr_def]
  >- (Cases_on `b` >> Cases_on `l` >>
      simp[gas_shadow_builtin_def, is_empty_value_expr_def]
      >- (Cases_on `o'` >> simp[is_empty_value_expr_def]) >>
      Cases_on `e = MsgGas` >> simp[is_empty_value_expr_def]) >>
  Cases_on `t0` >> simp[is_empty_value_expr_def]
QED

Theorem gas_shadow_compiles_declare_local:
  gas_shadow_compiles (declare_local cenv id ty) (declare_local cenv id ty)
Proof
  simp[declare_local_def] >> IF_CASES_TAC >>
  simp[gas_shadow_compiles_return] >>
  irule gas_shadow_compiles_bind >>
  simp[gas_shadow_compiles_fresh_var, gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_emit_local_alloca:
  gas_shadow_compiles (emit_local_alloca cenv id) (emit_local_alloca cenv id)
Proof
  simp[emit_local_alloca_def] >> rpt CASE_TAC >>
  simp[gas_shadow_compiles_return, gas_shadow_compiles_emit_inst]
QED

Theorem gas_shadow_compiles_declare_stmt_local:
  gas_shadow_compiles (declare_stmt_local cenv s)
    (declare_stmt_local cenv (gas_shadow_stmt s))
Proof
  Cases_on `s` >>
  simp[gas_shadow_stmt_def, declare_stmt_local_def,
       gas_shadow_compiles_return, gas_shadow_compiles_declare_local]
QED
