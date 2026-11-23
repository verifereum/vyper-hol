(* Constructor boundaries for the frozen statement compiler. *)
Theory gasShadowCompileStmtCases
Ancestors
  gasShadowCompileStmtHelpers gasShadowCompileStmtOps gasShadowCompileStmtBase
  gasShadowCompilePure gasShadowCompileConvert gasShadowCompileContext gasShadowCompileAbi gasShadowCompileArith gasShadowCompileCallSupport
  gasShadowCompileLiteral gasShadowCompileHelpers gasShadowCompileExternal
  gasShadow gasShadowState stmtLowering compileEnv
  exprLowering vyperAST list

Theorem gas_shadow_stmt_pass:
  gas_shadow_compiles (compile_stmt cenv lctx ty Pass)
    (compile_stmt (gas_shadow_env sd cenv) lctx ty (gas_shadow_stmt Pass))
Proof
  simp[gas_shadow_stmt_def, compile_stmt_def, gas_shadow_compiles_return]
QED

Theorem gas_shadow_stmt_expr:
  gas_shadow_compiles (compile_stmt cenv lctx ty (Expr e))
    (compile_stmt (gas_shadow_env sd cenv) lctx ty (gas_shadow_stmt (Expr e)))
Proof
  simp[gas_shadow_stmt_def, compile_stmt_def, comp_ignore_bind_def,
       gas_shadow_compiles_bind, gas_shadow_compiles_return,
       gas_shadow_stmt_compile_expr_env]
QED

Theorem gas_shadow_stmt_annassign:
  gas_shadow_compiles (compile_stmt cenv lctx ty (AnnAssign id vtyp e))
    (compile_stmt (gas_shadow_env sd cenv) lctx ty (gas_shadow_stmt (AnnAssign id vtyp e)))
Proof
  simp[gas_shadow_stmt_def, compile_stmt_def, comp_ignore_bind_def,
       gas_shadow_lowered_value_type] >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_compiles_emit_local_alloca] >> gen_tac >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_stmt_compile_expr_env] >> gen_tac >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (IF_CASES_TAC >>
      simp[gas_shadow_compiles_return, gas_shadow_compiles_unwrap_value]) >> gen_tac >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_compiles_return] >> gen_tac >>
  Cases_on `FLOOKUP cenv.ce_vars id` >> simp[gas_shadow_compiles_emit_void] >>
  rename1 `SOME loc` >> Cases_on `loc` >>
  simp[gas_shadow_compiles_emit_void] >> IF_CASES_TAC >>
  simp[gas_shadow_compiles_emit_void, gas_shadow_compiles_assign_value]
QED

Theorem gas_shadow_stmt_assign_base:
  gas_shadow_compiles (compile_stmt cenv lctx ty (Assign (BaseTarget bt) e))
    (compile_stmt (gas_shadow_env sd cenv) lctx ty (gas_shadow_stmt (Assign (BaseTarget bt) e)))
Proof
  simp[gas_shadow_stmt_def, gas_shadow_assignment_def, compile_stmt_def,
       gas_shadow_lowered_value_type, gas_shadow_expr_can_mutate] >>
  IF_CASES_TAC >> simp[]
  >- (ho_match_mp_tac gas_shadow_compiles_bind >>
      simp[gas_shadow_stmt_get_target_ptr_env, gas_shadow_compiles_store_at_loc]) >>
  Cases_on `expr_can_mutate cenv (target_to_expr bt)` >> simp[] >>
  rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_stmt_compile_expr_env, gas_shadow_stmt_get_target_ptr_env,
               gas_shadow_compiles_return, gas_shadow_compiles_unwrap_value,
               gas_shadow_compiles_snapshot_vv] >>
       gen_tac) >>
  Cases_on `dst_loc_opt` >>
  simp[gas_shadow_compiles_emit_void, gas_shadow_compiles_assign_value]
QED

Theorem gas_shadow_stmt_assign_tuple:
  gas_shadow_compiles (compile_stmt cenv lctx ty (Assign (TupleTarget targets) e))
    (compile_stmt (gas_shadow_env sd cenv) lctx ty (gas_shadow_stmt (Assign (TupleTarget targets) e)))
Proof
  simp[gas_shadow_stmt_def, gas_shadow_assignment_def, compile_stmt_def,
       gas_shadow_lowered_value_type] >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_stmt_compile_expr_env] >> gen_tac >>
  ho_match_mp_tac gas_shadow_compiles_bind >>
  simp[gas_shadow_compiles_unwrap_value, gas_shadow_compile_tuple_unpack]
QED

Theorem gas_shadow_stmt_assert:
  gas_shadow_compiles (compile_stmt cenv lctx ty (Assert e a))
    (compile_stmt (gas_shadow_env sd cenv) lctx ty (gas_shadow_stmt (Assert e a)))
Proof
  Cases_on `a` >>
  simp[gas_shadow_stmt_def, gas_shadow_assert_reason_def, compile_stmt_def,
       comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_stmt_lower_value_env, gas_shadow_compiles_fresh_label,
               gas_shadow_compiles_emit_inst, gas_shadow_compiles_new_block,
               gas_shadow_compiles_return, gas_shadow_compile_reason_message_env,
               gas_shadow_compiles_revert_with_reason,
               gas_shadow_compile_revert_with_custom_error] >> gen_tac) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_stmt_raise_env:
  gas_shadow_compiles (compile_stmt cenv lctx ty (Raise r))
    (compile_stmt (gas_shadow_env sd cenv) lctx ty (gas_shadow_stmt (Raise r)))
Proof
  Cases_on `r` >>
  simp[gas_shadow_stmt_def, gas_shadow_raise_reason_def, compile_stmt_def,
       gas_shadow_compiles_emit_inst, gas_shadow_compile_revert_with_custom_error,
       comp_ignore_bind_def,
       gas_shadow_compiles_bind, gas_shadow_compiles_return] >>
  ho_match_mp_tac gas_shadow_compiles_bind >>
  simp[gas_shadow_compile_reason_message_env, gas_shadow_compiles_revert_with_reason]
QED

Theorem gas_shadow_log_snapshots_env:
  gas_shadow_compiles
    (compile_ext_call_args compile_expr cenv [] (MAP (lowered_value_type cenv) args) args)
    (compile_ext_call_args compile_expr (gas_shadow_env sd cenv) []
      (MAP (lowered_value_type cenv) (MAP gas_shadow_expr args)) (MAP gas_shadow_expr args))
Proof
  mp_tac (Q.INST [`sh` |-> `T`]
    (MATCH_MP gas_shadow_compiles_ext_call_args
      (cj 1 gasShadowCompileTheory.gas_shadow_compile_expr_env))) >>
  simp[MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss] >>
  disch_then (qspecl_then [`args`, `[]`, `MAP (lowered_value_type cenv) args`] mp_tac) >>
  simp[]
QED

Theorem gas_shadow_stmt_log:
  gas_shadow_compiles (compile_stmt cenv lctx ty (Log id args))
    (compile_stmt (gas_shadow_env sd cenv) lctx ty (gas_shadow_stmt (Log id args)))
Proof
  simp[gas_shadow_stmt_def, compile_stmt_def,
       MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss] >>
  Cases_on `cenv.ce_event_info (nsid_to_string id)`
  >- simp[gas_shadow_compiles_emit_inst] >>
  rename1 `SOME info` >> PairCases_on `info` >> simp[] >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (mp_tac gas_shadow_log_snapshots_env >> simp[MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]) >>
  gen_tac >> BETA_TAC >>
  rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_return, gas_shadow_compiles_log_saved_topics] >>
       gen_tac) >>
  IF_CASES_TAC >> simp[gas_shadow_compiles_emit_inst, comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_return,
               gas_shadow_compiles_abi_encode_values_to_buf] >> gen_tac) >>
  simp[gas_shadow_compiles_emit_inst]
QED

Theorem gas_shadow_stmt_augassign:
  gas_shadow_compiles (compile_stmt cenv lctx ty (AugAssign tty bt bop e))
    (compile_stmt (gas_shadow_env sd cenv) lctx ty (gas_shadow_stmt (AugAssign tty bt bop e)))
Proof
  simp[gas_shadow_stmt_def, compile_stmt_def] >>
  rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_stmt_get_target_ptr_env, gas_shadow_compiles_return] >> gen_tac) >>
  Cases_on `dst_loc_opt` >> simp[gas_shadow_compiles_emit_void] >>
  rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- rw[gas_shadow_compiles_return, gas_shadow_compiles_ptr_load,
             gas_shadow_compiles_emit_op] >> gen_tac) >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_stmt_lower_value_env] >> gen_tac >>
  ho_match_mp_tac gas_shadow_compiles_bind >>
  rw[gas_shadow_compiles_binop, gas_shadow_compiles_ptr_store,
     gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_stmt_break:
  gas_shadow_compiles (compile_stmt cenv lctx ty Break)
    (compile_stmt (gas_shadow_env sd cenv) lctx ty (gas_shadow_stmt Break))
Proof
  Cases_on `lctx` >>
  simp[gas_shadow_stmt_def, compile_stmt_def, comp_ignore_bind_def,
       gas_shadow_compiles_bind, gas_shadow_compiles_return,
       gas_shadow_compiles_emit_inst]
QED

Theorem gas_shadow_stmt_continue:
  gas_shadow_compiles (compile_stmt cenv lctx ty Continue)
    (compile_stmt (gas_shadow_env sd cenv) lctx ty (gas_shadow_stmt Continue))
Proof
  Cases_on `lctx` >>
  simp[gas_shadow_stmt_def, compile_stmt_def, comp_ignore_bind_def,
       gas_shadow_compiles_bind, gas_shadow_compiles_return,
       gas_shadow_compiles_emit_inst]
QED

Theorem gas_shadow_stmt_return_none:
  gas_shadow_compiles (compile_stmt cenv lctx ty (Return NONE))
    (compile_stmt (gas_shadow_env sd cenv) lctx ty (gas_shadow_stmt (Return NONE)))
Proof
  simp[gas_shadow_stmt_def, compile_stmt_def] >>
  Cases_on `cenv.ce_return_pc` >>
  simp[gas_shadow_compiles_bind, gas_shadow_compiles_emit_op,
       comp_ignore_bind_def, gas_shadow_compiles_return_unlock,
       gas_shadow_compiles_emit_inst]
  >- (Cases_on `cenv.ce_ctor_exit_label` >> simp[gas_shadow_compiles_emit_inst] >>
      pairarg_tac >> simp[comp_ignore_bind_def] >>
      ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
      >- (IF_CASES_TAC >> simp[gas_shadow_compiles_nonreentrant_unlock,
                              gas_shadow_compiles_return]) >>
      simp[gas_shadow_compiles_emit_inst]) >>
  rename1 `SOME loc` >> Cases_on `loc` >>
  simp[gas_shadow_compiles_bind, gas_shadow_compiles_emit_op,
       comp_ignore_bind_def, gas_shadow_compiles_return_unlock,
       gas_shadow_compiles_emit_inst] >>
  Cases_on `cenv.ce_ctor_exit_label` >> simp[gas_shadow_compiles_emit_inst] >>
  pairarg_tac >> simp[comp_ignore_bind_def] >>
  (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- (IF_CASES_TAC >> simp[gas_shadow_compiles_nonreentrant_unlock,
                           gas_shadow_compiles_return]) >>
   simp[gas_shadow_compiles_emit_inst])
QED

Theorem gas_shadow_stmt_return_some:
  gas_shadow_compiles (compile_stmt cenv lctx ty (Return (SOME e)))
    (compile_stmt (gas_shadow_env sd cenv) lctx ty (gas_shadow_stmt (Return (SOME e))))
Proof
  simp[gas_shadow_stmt_def, compile_stmt_def, comp_ignore_bind_def,
       gas_shadow_lowered_value_type] >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_stmt_lower_value_env] >> gen_tac >>
  Cases_on `cenv.ce_return_pc` >>
  simp[gas_shadow_compiles_bind, gas_shadow_compiles_emit_op,
       gas_shadow_compiles_internal_return_from_env]
  >- suspend "external_none" >>
  rename1 `SOME loc` >> Cases_on `loc` >>
  simp[gas_shadow_compiles_bind, gas_shadow_compiles_emit_op,
       gas_shadow_compiles_internal_return_from_env] >>
  (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
   >- (IF_CASES_TAC >> simp[gas_shadow_compiles_return] >>
       rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
            >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_return,
                    gas_shadow_compiles_store_memory_typed] >> gen_tac) >>
       simp[gas_shadow_compiles_return]) >>
   gen_tac >> IF_CASES_TAC >>
   simp[comp_ignore_bind_def, gas_shadow_compiles_bind,
        gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_store_memory_typed,
        gas_shadow_compiles_external_return] >>
   IF_CASES_TAC >>
   simp[gas_shadow_compiles_bind, gas_shadow_compiles_nonreentrant_unlock,
        gas_shadow_compiles_return, gas_shadow_compiles_alloc_buffer,
        gas_shadow_compiles_store_memory_typed, gas_shadow_compiles_external_return])
QED

Resume gas_shadow_stmt_return_some[external_none]:
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[gas_shadow_compiles_return] >>
      rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
           >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_return,
                   gas_shadow_compiles_store_memory_typed] >> gen_tac) >>
      simp[gas_shadow_compiles_return]) >>
  gen_tac >> IF_CASES_TAC >>
  simp[comp_ignore_bind_def, gas_shadow_compiles_bind,
       gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_store_memory_typed,
       gas_shadow_compiles_external_return] >>
  IF_CASES_TAC >>
  simp[gas_shadow_compiles_bind, gas_shadow_compiles_nonreentrant_unlock,
       gas_shadow_compiles_return, gas_shadow_compiles_alloc_buffer,
       gas_shadow_compiles_store_memory_typed, gas_shadow_compiles_external_return]
QED

Finalise gas_shadow_stmt_return_some

Theorem gas_shadow_stmt_append:
  gas_shadow_compiles (compile_stmt cenv lctx ty (Append target e))
    (compile_stmt (gas_shadow_env sd cenv) lctx ty (gas_shadow_stmt (Append target e)))
Proof
  simp[gas_shadow_stmt_def, compile_stmt_def,
       gas_shadow_lowered_value_type,
       comp_ignore_bind_def] >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_stmt_get_target_ptr_env] >> gen_tac >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_stmt_lower_value_env] >> gen_tac >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[gas_shadow_compiles_return] >>
      rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
           >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_store_memory] >>
           gen_tac) >> simp[gas_shadow_compiles_return]) >> gen_tac >>
  ho_match_mp_tac gas_shadow_compiles_bind >>
  simp[gas_shadow_compiles_return, gas_shadow_compiles_dynarray_append]
QED

Theorem gas_shadow_stmts_cons:
  (!ce lc rt. gas_shadow_compiles (compile_stmt ce lc rt s)
     (compile_stmt (gas_shadow_env sd ce) lc rt (gas_shadow_stmt s))) /\
  (!ce lc rt. gas_shadow_compiles (compile_stmts ce lc rt ss)
     (compile_stmts (gas_shadow_env sd ce) lc rt (MAP gas_shadow_stmt ss))) ==>
  gas_shadow_compiles (compile_stmts cenv lctx ty (s::ss))
    (compile_stmts (gas_shadow_env sd cenv) lctx ty (MAP gas_shadow_stmt (s::ss)))
Proof
  strip_tac >> simp[compile_stmt_def] >>
  ho_match_mp_tac gas_shadow_compiles_get_terminated >> gen_tac >>
  Cases_on `b` >> simp[gas_shadow_compiles_return, comp_ignore_bind_def] >>
  ho_match_mp_tac gas_shadow_compiles_env_bind >> conj_tac
  >- simp[gas_shadow_compiles_env_declare_stmt_local] >> gen_tac >>
  ho_match_mp_tac gas_shadow_compiles_bind >> simp[]
QED

Theorem gas_shadow_stmt_if:
  (!ce lc rt. gas_shadow_compiles (compile_stmts ce lc rt yes)
     (compile_stmts (gas_shadow_env sd ce) lc rt (MAP gas_shadow_stmt yes))) /\
  (!ce lc rt. gas_shadow_compiles (compile_stmts ce lc rt no)
     (compile_stmts (gas_shadow_env sd ce) lc rt (MAP gas_shadow_stmt no))) ==>
  gas_shadow_compiles (compile_stmt cenv lctx ty (If e yes no))
    (compile_stmt (gas_shadow_env sd cenv) lctx ty (gas_shadow_stmt (If e yes no)))
Proof
  strip_tac >> simp[gas_shadow_stmt_def, compile_stmt_def, comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_stmt_lower_value_env, gas_shadow_compiles_fresh_label,
               gas_shadow_compiles_emit_inst, gas_shadow_compiles_new_block] >> gen_tac) >>
  ho_match_mp_tac gas_shadow_compiles_get_terminated >> gen_tac >>
  rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_return,
               gas_shadow_compiles_emit_jmp_if_not_terminated,
               gas_shadow_compiles_new_block] >> gen_tac) >>
  ho_match_mp_tac gas_shadow_compiles_get_terminated >> gen_tac >>
  rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_return,
               gas_shadow_compiles_emit_jmp_if_not_terminated] >> gen_tac) >>
  IF_CASES_TAC >> simp[gas_shadow_compiles_return, gas_shadow_compiles_bind,
                      gas_shadow_compiles_new_block]
QED

Theorem gas_shadow_stmt_for_array:
  (!ce lc rt. gas_shadow_compiles (compile_stmts ce lc rt loop_body)
     (compile_stmts (gas_shadow_env sd ce) lc rt (MAP gas_shadow_stmt loop_body))) ==>
  gas_shadow_compiles (compile_stmt cenv lctx ty (For id fty (Array e) bound loop_body))
    (compile_stmt (gas_shadow_env sd cenv) lctx ty (gas_shadow_stmt (For id fty (Array e) bound loop_body)))
Proof
  strip_tac >> simp[gas_shadow_stmt_def, gas_shadow_iterator_def,
                    compile_stmt_def, comp_ignore_bind_def] >>
  rpt ((ho_match_mp_tac gas_shadow_compiles_env_bind >> conj_tac
        >- simp[gas_shadow_compiles_env_declare_local] >> gen_tac) ORELSE
       (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- (rpt IF_CASES_TAC >>
           simp[gas_shadow_stmt_compile_expr_env, gas_shadow_compiles_return,
                gas_shadow_compiles_ptr_load,
                gas_shadow_compiles_emit_local_alloca, gas_shadow_compiles_fresh_label,
                gas_shadow_compiles_fresh_var, gas_shadow_compiles_emit_inst,
                gas_shadow_compiles_emit_op, gas_shadow_compiles_emit_void,
                gas_shadow_compiles_new_block, gas_shadow_compiles_bind]) >> gen_tac)) >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (Cases_on `FLOOKUP body_cenv.ce_vars id` >>
      simp[gas_shadow_compiles_emit_void] >> rename1 `SOME binding` >>
      Cases_on `binding` >> simp[gas_shadow_compiles_emit_void,
                                gas_shadow_compiles_iter_elem_copy]) >> gen_tac >>
  rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_jmp_if_not_terminated,
               gas_shadow_compiles_new_block, gas_shadow_compiles_emit_op,
               gas_shadow_compiles_emit_inst] >> gen_tac) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_stmt_for_range:
  (!ce lc rt. gas_shadow_compiles (compile_stmts ce lc rt loop_body)
     (compile_stmts (gas_shadow_env sd ce) lc rt (MAP gas_shadow_stmt loop_body))) ==>
  gas_shadow_compiles (compile_stmt cenv lctx ty (For id fty (Range a z) bound loop_body))
    (compile_stmt (gas_shadow_env sd cenv) lctx ty (gas_shadow_stmt (For id fty (Range a z) bound loop_body)))
Proof
  strip_tac >> simp[gas_shadow_stmt_def, gas_shadow_iterator_def,
                    compile_stmt_def, comp_ignore_bind_def] >>
  rpt ((ho_match_mp_tac gas_shadow_compiles_env_bind >> conj_tac
        >- simp[gas_shadow_compiles_env_declare_local] >> gen_tac) ORELSE
       (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_stmt_lower_value_env,
               gas_shadow_compiles_emit_local_alloca, gas_shadow_compiles_fresh_label,
               gas_shadow_compiles_fresh_var, gas_shadow_compiles_emit_inst,
               gas_shadow_compiles_new_block] >> gen_tac)) >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (Cases_on `a` >> Cases_on `z` >>
      simp[gas_shadow_expr_def, gas_shadow_compiles_emit_op] >>
      Cases_on `l` >> Cases_on `l'` >>
      simp[gas_shadow_compiles_emit_op, gas_shadow_compiles_return]) >>
  gen_tac >> ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (Cases_on `a` >> Cases_on `z` >>
      simp[gas_shadow_expr_def, gas_shadow_compiles_range_bound_checks] >>
      Cases_on `l` >> Cases_on `l'` >>
      simp[gas_shadow_compiles_range_bound_checks, gas_shadow_compiles_return]) >>
  gen_tac >>
  rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_op, gas_shadow_compiles_emit_inst,
               gas_shadow_compiles_new_block] >> gen_tac) >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- (Cases_on `FLOOKUP body_cenv.ce_vars id` >>
      simp[gas_shadow_compiles_emit_void] >> rename1 `SOME binding` >>
      Cases_on `binding` >> simp[gas_shadow_compiles_emit_void]) >> gen_tac >>
  rpt (ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_jmp_if_not_terminated,
               gas_shadow_compiles_new_block, gas_shadow_compiles_emit_op,
               gas_shadow_compiles_emit_inst] >> gen_tac) >>
  simp[gas_shadow_compiles_return]
QED

(* The same-environment forms. *)
Theorem gas_shadow_stmt_raise =
  REWRITE_RULE [gasShadowCompileBaseTheory.gas_shadow_env_F] (Q.INST [`sd` |-> `F`] gas_shadow_stmt_raise_env)

Theorem gas_shadow_log_snapshots =
  REWRITE_RULE [gasShadowCompileBaseTheory.gas_shadow_env_F] (Q.INST [`sd` |-> `F`] gas_shadow_log_snapshots_env)

