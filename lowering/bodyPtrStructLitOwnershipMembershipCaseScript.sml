Theory bodyPtrStructLitOwnershipMembershipCase
Ancestors bodyPtrStructLitOwnershipMembership bodyPtrStructLitOwnershipInterfaces
  bodyPtrStructLitOwnershipStructFrame bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps loweringShapeDefs exprLowering context compileEnv

Theorem alloc_run_compile_builtin_dispatch_body_var_membership:
  (op = In \/ op = NotIn) /\ is_ArrayT (expr_type (HD (TL args))) /\
  (case HD (TL args) of Builtin _ (MakeArray _ _) _ => F | _ => T) /\
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (cfn ce (expr_type (HD args)) (HD args)) (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (cfn ce (expr_type (HD args)) (HD args)) (\v s. T) /\
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (cfn ce (expr_type (HD (TL args))) (HD (TL args))) (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (cfn ce (expr_type (HD (TL args))) (HD (TL args))) (\v s. T) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch_body cfn ce ret_ty ty (Bop op) args) (\v s. T)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_builtin_dispatch_body cfn ce ret_ty ty (Bop op) args =
    comp_bind (lower_value cfn ce (expr_type (HD args)) (HD args))
      (\needle. comp_bind (cfn ce (expr_type (HD (TL args))) (HD (TL args)))
        (\arr_vv. \s. as_stack_val ret_ty
          (compile_var_array_membership ce needle arr_vv (expr_type (HD (TL args)))
            (op = In) s)))` by suspend "dispatch" >>
  pop_assum SUBST1_TAC >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def]) >>
  qx_gen_tac `needle` >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_struct_child_frame >>
      qexistsl [`internal`, `ce`, `\s. T`] >> simp[shape_stable_def]) >>
  qx_gen_tac `arr_vv` >> simp[] >>
  mp_tac (Q.INST [`rhs_ty` |-> `expr_type (HD (TL args))`,
    `is_in` |-> `op = In`] alloc_run_compile_var_array_membership) >>
  simp[alloc_run_def, oneline as_stack_val_def, AllCaseEqs()] >>
  rpt strip_tac >>
  rename1 `shape_state start` >>
  `fresh_outputs start` by
    (qpat_x_assum `shape_state start` mp_tac >>
     simp[shape_state_def, shape_base_fresh_outputs]) >>
  first_x_assum drule_all >> simp[]
QED

Resume alloc_run_compile_builtin_dispatch_body_var_membership[dispatch]:
  simp[FUN_EQ_THM, compile_builtin_dispatch_body_def, comp_bind_def] >>
  Cases_on `HD (TL args)` >> gvs[] >>
  rename1 `Builtin _ bi _` >> Cases_on `bi` >> gvs[]
QED

Finalise alloc_run_compile_builtin_dispatch_body_var_membership
