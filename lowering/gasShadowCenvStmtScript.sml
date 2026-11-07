(* The statement lowering under the gas-shadow compile env: every statement
   operation but the expression compiler ignores the internal functions'
   default arguments, and a local declaration keeps the env shadowed. *)
Theory gasShadowCenvStmt
Ancestors
  gasShadow gasShadowCenv gasShadowState gasShadowCompileStmtBase stmtLowering
  context compileEnv vyperAST list

Theorem gas_shadow_cenv_stmt_lists[simp]:
  (!c ops buf off. compile_log_store_data (gas_shadow_cenv c) ops buf off =
                   compile_log_store_data c ops buf off) /\
  (!c base tys off. compile_load_tuple_elements (gas_shadow_cenv c) base tys off =
                    compile_load_tuple_elements c base tys off) /\
  (!c src tys off. compile_tuple_load_all (gas_shadow_cenv c) src tys off =
                   compile_tuple_load_all c src tys off)
Proof
  rpt conj_tac
  >- (gen_tac >> Induct >> simp[compile_log_store_data_def])
  >- (ntac 2 gen_tac >> Induct >> simp[compile_load_tuple_elements_def]) >>
  ntac 2 gen_tac >> Induct >> simp[compile_tuple_load_all_def]
QED

Theorem gas_shadow_cenv_stmt_ops[simp]:
  (!c rv pc n ty sty etys rb.
     compile_internal_return (gas_shadow_cenv c) rv pc n ty sty etys rb =
     compile_internal_return c rv pc n ty sty etys rb) /\
  (!c vv ty n. compile_revert_with_reason (gas_shadow_cenv c) vv ty n =
               compile_revert_with_reason c vv ty n) /\
  (!c dst loc v prim src_loc ty sty da n.
     compile_assign_value (gas_shadow_cenv c) dst loc v prim src_loc ty sty da n =
     compile_assign_value c dst loc v prim src_loc ty sty da n) /\
  (!c elem item n loc slot ty ety.
     compile_iter_elem_copy (gas_shadow_cenv c) elem item n loc slot ty ety =
     compile_iter_elem_copy c elem item n loc slot ty ety) /\
  (!c ty sty v rpc.
     compile_internal_return_from_env (gas_shadow_cenv c) ty sty v rpc =
     compile_internal_return_from_env c ty sty v rpc) /\
  (!c id. emit_local_alloca (gas_shadow_cenv c) id = emit_local_alloca c id)
Proof
  simp[compile_internal_return_def, compile_revert_with_reason_def,
       compile_assign_value_def, compile_iter_elem_copy_def,
       compile_internal_return_from_env_def, emit_local_alloca_def]
QED

Theorem gas_shadow_cenv_target_root[simp]:
  !bt. target_root_type (gas_shadow_cenv c) bt = target_root_type c bt /\
       target_root_capacity (gas_shadow_cenv c) bt = target_root_capacity c bt
Proof
  `(!e:expr. T) /\
   (!bt. target_root_type (gas_shadow_cenv c) bt = target_root_type c bt /\
         target_root_capacity (gas_shadow_cenv c) bt = target_root_capacity c bt)`
    suffices_by simp[] >>
  ho_match_mp_tac expr_induction >>
  simp[target_root_type_def, target_root_capacity_def]
QED

(* A declaration in the shadowed env yields the shadowed declared env. *)
Theorem gas_shadow_cenv_declare_local:
  declare_local (gas_shadow_cenv c) id ty s =
  (gas_shadow_cenv (FST (declare_local c id ty s)),
   SND (declare_local c id ty s))
Proof
  simp[declare_local_def] >> IF_CASES_TAC >>
  simp[comp_bind_def, comp_return_def, fresh_var_def, gas_shadow_cenv_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem gas_shadow_declare_stmt_local_stmt[simp]:
  declare_stmt_local c (gas_shadow_stmt st) = declare_stmt_local c st
Proof
  Cases_on `st` >> simp[gas_shadow_stmt_def, declare_stmt_local_def]
QED

Theorem gas_shadow_cenv_declare_stmt_local:
  declare_stmt_local (gas_shadow_cenv c) st s =
  (gas_shadow_cenv (FST (declare_stmt_local c st s)),
   SND (declare_stmt_local c st s))
Proof
  Cases_on `st` >>
  simp[declare_stmt_local_def, gas_shadow_cenv_declare_local, comp_return_def]
QED

(* Bind past a step whose shadow result is the shadowed env of its own. *)
Theorem gas_shadow_compiles_bind_cenv:
  gas_shadow_compiles f f /\
  (!s. g s = (gas_shadow_cenv (FST (f s)), SND (f s))) /\
  (!x. gas_shadow_compiles (h x) (k (gas_shadow_cenv x))) ==>
  gas_shadow_compiles (comp_bind f h) (comp_bind g k)
Proof
  rw[gas_shadow_compiles_def, comp_bind_def] >>
  last_x_assum (qspecl_then [`s`, `t`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `f s` >> Cases_on `f t` >> gvs[]
QED
