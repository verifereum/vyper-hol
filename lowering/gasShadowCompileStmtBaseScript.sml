(* Proof-only boundaries for statement shadow compilation. *)
Theory gasShadowCompileStmtBase
Ancestors
  gasShadowState gasShadow gasShadowCompilePure stmtLowering compileEnv emitHelper venomInst vyperAST list

(* Statement helpers that read no default arguments compile alike under the
   shadow environment. *)
Theorem compile_log_saved_topics_gas_shadow_env[simp]:
  !cenv topics.
    compile_log_saved_topics (gas_shadow_env sd cenv) topics = compile_log_saved_topics cenv topics
Proof
  ho_match_mp_tac compile_log_saved_topics_ind >> rpt strip_tac >>
  once_rewrite_tac[compile_log_saved_topics_def] >> gs[Cong MAP_CONG]
QED

Theorem compile_log_store_data_gas_shadow_env[simp]:
  !cenv ops tys buf_op offset.
    compile_log_store_data (gas_shadow_env sd cenv) ops tys buf_op offset = compile_log_store_data cenv ops tys buf_op offset
Proof
  ho_match_mp_tac compile_log_store_data_ind >> rpt strip_tac >>
  once_rewrite_tac[compile_log_store_data_def] >> gs[Cong MAP_CONG]
QED

Theorem compile_revert_with_reason_gas_shadow_env[simp]:
  !cenv. compile_revert_with_reason (gas_shadow_env sd cenv) = compile_revert_with_reason cenv
Proof
  rw[FUN_EQ_THM, compile_revert_with_reason_def]
QED

Theorem compile_load_tuple_elements_gas_shadow_env[simp]:
  !cenv base_op tys offset.
    compile_load_tuple_elements (gas_shadow_env sd cenv) base_op tys offset = compile_load_tuple_elements cenv base_op tys offset
Proof
  ntac 2 gen_tac >> Induct >> gs[compile_load_tuple_elements_def]
QED

Theorem compile_log_save_arg_gas_shadow_env[simp]:
  !cenv. compile_log_save_arg (gas_shadow_env sd cenv) = compile_log_save_arg cenv
Proof
  rw[FUN_EQ_THM, compile_log_save_arg_def]
QED

Theorem compile_mcopy_guard_gas_shadow_env[simp]:
  !cenv. compile_mcopy_guard (gas_shadow_env sd cenv) = compile_mcopy_guard cenv
Proof
  rw[FUN_EQ_THM, compile_mcopy_guard_def]
QED

Theorem compile_internal_return_gas_shadow_env[simp]:
  !cenv. compile_internal_return (gas_shadow_env sd cenv) = compile_internal_return cenv
Proof
  rw[FUN_EQ_THM, compile_internal_return_def]
QED

Theorem compile_assign_value_gas_shadow_env[simp]:
  !cenv. compile_assign_value (gas_shadow_env sd cenv) = compile_assign_value cenv
Proof
  rw[FUN_EQ_THM, compile_assign_value_def]
QED

Theorem compile_tuple_load_all_gas_shadow_env[simp]:
  !cenv src_op tys offset.
    compile_tuple_load_all (gas_shadow_env sd cenv) src_op tys offset = compile_tuple_load_all cenv src_op tys offset
Proof
  ntac 2 gen_tac >> Induct >> gs[compile_tuple_load_all_def]
QED

Theorem compile_iter_elem_copy_gas_shadow_env[simp]:
  !cenv. compile_iter_elem_copy (gas_shadow_env sd cenv) = compile_iter_elem_copy cenv
Proof
  rw[FUN_EQ_THM, compile_iter_elem_copy_def]
QED

Theorem emit_local_alloca_gas_shadow_env[simp]:
  !cenv. emit_local_alloca (gas_shadow_env sd cenv) = emit_local_alloca cenv
Proof
  rw[FUN_EQ_THM, emit_local_alloca_def]
QED

Theorem compile_return_unlock_gas_shadow_env[simp]:
  !cenv. compile_return_unlock (gas_shadow_env sd cenv) = compile_return_unlock cenv
Proof
  rw[FUN_EQ_THM, compile_return_unlock_def]
QED

Theorem compile_internal_return_from_env_gas_shadow_env[simp]:
  !cenv. compile_internal_return_from_env (gas_shadow_env sd cenv) = compile_internal_return_from_env cenv
Proof
  rw[FUN_EQ_THM, compile_internal_return_from_env_def]
QED


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
  rename1 `LIST_REL gas_shadow_inst xs ys_tail` >>
  Cases_on `xs`
  >- (gvs[] >> irule gas_shadow_inst_terminator >> simp[]) >>
  Cases_on `ys_tail` >> gvs[] >>
  rename1 `_ = is_terminator (LAST (right_head::right_tail)).inst_opcode` >>
  first_x_assum (qspec_then `right_head::right_tail` mp_tac) >> simp[]
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
  >- (rename1 `_ = is_empty_value_expr (Builtin ty builtin args)` >>
      Cases_on `builtin` >> Cases_on `args` >>
      simp[gas_shadow_builtin_def, is_empty_value_expr_def]
      >- (rename1 `MakeArray elem_ty_opt array_bound` >>
          Cases_on `elem_ty_opt` >> simp[is_empty_value_expr_def]) >>
      rename1 `if env_var = MsgGas then Env GasPrice else Env env_var` >>
      Cases_on `env_var = MsgGas` >> simp[is_empty_value_expr_def]) >>
  rename1 `_ = is_empty_value_expr (TypeBuiltin ty type_builtin result_ty args)` >>
  Cases_on `type_builtin` >> simp[is_empty_value_expr_def]
QED

Theorem gas_shadow_target_to_expr[simp]:
  !bt. target_to_expr (gas_shadow_target bt) = gas_shadow_expr (target_to_expr bt)
Proof
  `(!e:expr. T) /\
   (!bt. target_to_expr (gas_shadow_target bt) = gas_shadow_expr (target_to_expr bt))`
    suffices_by simp[] >>
  ho_match_mp_tac expr_induction >>
  simp[gas_shadow_expr_def, target_to_expr_def]
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

(* A compiler run that returns an environment, against one that returns its
   shadow environment. *)
Definition gas_shadow_compiles_env_def:
  gas_shadow_compiles_env sd (f : compile_env compiler) g <=>
    !s t. gas_shadow_state s t ==>
      gas_shadow_env sd (FST (f s)) = FST (g t) /\
      gas_shadow_state (SND (f s)) (SND (g t))
End

Theorem gas_shadow_compiles_env_F:
  gas_shadow_compiles_env F f g <=> gas_shadow_compiles f g
Proof
  simp[gas_shadow_compiles_env_def, gas_shadow_compiles_def]
QED

Theorem gas_shadow_compiles_env_return:
  c' = gas_shadow_env sd c ==>
  gas_shadow_compiles_env sd (comp_return c) (comp_return c')
Proof
  simp[gas_shadow_compiles_env_def, comp_return_def]
QED

Theorem gas_shadow_compiles_env_bind:
  gas_shadow_compiles_env sd f g /\
  (!x. gas_shadow_compiles (h x) (k (gas_shadow_env sd x))) ==>
  gas_shadow_compiles (comp_bind f h) (comp_bind g k)
Proof
  rw[gas_shadow_compiles_env_def, gas_shadow_compiles_def] >>
  qpat_x_assum `!s t. gas_shadow_state s t ==> _`
    (qspecl_then [`s`, `t`] mp_tac) >>
  asm_rewrite_tac [] >> strip_tac >>
  qpat_x_assum `!x s t. _`
    (qspecl_then [`FST (f s)`, `SND (f s)`, `SND (g t)`] mp_tac) >>
  asm_rewrite_tac [] >>
  Cases_on `f s` >> Cases_on `g t` >> gvs[comp_bind_def]
QED

Theorem gas_shadow_compiles_bind_env:
  gas_shadow_compiles f g /\
  (!x. gas_shadow_compiles_env sd (h x) (k x)) ==>
  gas_shadow_compiles_env sd (comp_bind f h) (comp_bind g k)
Proof
  rw[gas_shadow_compiles_env_def, gas_shadow_compiles_def] >>
  qpat_x_assum `!s t. gas_shadow_state s t ==> _`
    (qspecl_then [`s`, `t`] mp_tac) >>
  asm_rewrite_tac [] >> strip_tac >>
  qpat_x_assum `!x s t. _`
    (qspecl_then [`FST (f s)`, `SND (f s)`, `SND (g t)`] mp_tac) >>
  asm_rewrite_tac [] >>
  Cases_on `f s` >> Cases_on `g t` >> gvs[comp_bind_def]
QED

Theorem gas_shadow_compiles_env_bind_env:
  gas_shadow_compiles_env sd f g /\
  (!x. gas_shadow_compiles_env sd (h x) (k (gas_shadow_env sd x))) ==>
  gas_shadow_compiles_env sd (comp_bind f h) (comp_bind g k)
Proof
  rw[gas_shadow_compiles_env_def] >>
  qpat_x_assum `!s t. gas_shadow_state s t ==> _`
    (qspecl_then [`s`, `t`] mp_tac) >>
  asm_rewrite_tac [] >> strip_tac >>
  qpat_x_assum `!x s t. _`
    (qspecl_then [`FST (f s)`, `SND (f s)`, `SND (g t)`] mp_tac) >>
  asm_rewrite_tac [] >>
  Cases_on `f s` >> Cases_on `g t` >> gvs[comp_bind_def]
QED

Theorem gas_shadow_compiles_get_terminated_env:
  (!b. gas_shadow_compiles_env sd (h b) (k b)) ==>
  gas_shadow_compiles_env sd
    (comp_bind comp_get (\s. h (block_is_terminated s)))
    (comp_bind comp_get (\s. k (block_is_terminated s)))
Proof
  rw[gas_shadow_compiles_env_def, comp_bind_def, comp_get_def] >>
  drule gas_shadow_state_terminated >> strip_tac >>
  first_x_assum (qspecl_then [`block_is_terminated s`, `s`, `t`] mp_tac) >>
  simp[]
QED

Theorem gas_shadow_compiles_env_declare_local:
  gas_shadow_compiles_env sd (declare_local cenv id ty)
    (declare_local (gas_shadow_env sd cenv) id ty)
Proof
  simp[declare_local_def] >> IF_CASES_TAC >> simp[]
  >- (irule gas_shadow_compiles_bind_env >>
      simp[gas_shadow_compiles_fresh_var] >> gen_tac >>
      irule gas_shadow_compiles_env_return >>
      rw[gasShadowCompileBaseTheory.gas_shadow_env_def, compile_env_component_equality]) >>
  irule gas_shadow_compiles_env_return >>
  rw[gasShadowCompileBaseTheory.gas_shadow_env_def, compile_env_component_equality]
QED

Theorem gas_shadow_compiles_env_declare_stmt_local:
  gas_shadow_compiles_env sd (declare_stmt_local cenv s)
    (declare_stmt_local (gas_shadow_env sd cenv) (gas_shadow_stmt s))
Proof
  Cases_on `s` >>
  simp[gas_shadow_stmt_def, declare_stmt_local_def,
       gas_shadow_compiles_env_declare_local] >>
  irule gas_shadow_compiles_env_return >> simp[]
QED
