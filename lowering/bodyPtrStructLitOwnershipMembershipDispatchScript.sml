Theory bodyPtrStructLitOwnershipMembershipDispatch
Ancestors bodyPtrStructLitOwnershipLiteralMembership
  bodyPtrStructLitOwnershipMembershipCase list pair

Theorem alloc_run_builtin_array_membership:
  (op = In \/ op = NotIn) /\ is_ArrayT (expr_type (HD (TL args))) /\
  2 <= LENGTH args /\
  (!e t. MEM e args ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v)) /\
  (!e t. MEM e args ==>
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) /\
  (!av a b elems e t.
    HD (TL args) = Builtin av (MakeArray a b) elems /\ MEM e elems ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v)) /\
  (!av a b elems e t.
    HD (TL args) = Builtin av (MakeArray a b) elems /\ MEM e elems ==>
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch_body cfn ce rt ty (Bop op) args) (\v s. T)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM (HD args) args /\ MEM (HD (TL args)) args` by
    (Cases_on `args` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  Cases_on `?av a b elems. HD (TL args) = Builtin av (MakeArray a b) elems`
  >- (pop_assum strip_assume_tac >>
      irule alloc_run_compile_builtin_dispatch_body_literal_membership >>
      simp[] >> qexists `internal` >> simp[]) >>
  `case HD (TL args) of Builtin _ (MakeArray _ _) _ => F | _ => T` by
    (Cases_on `HD (TL args)` >> gvs[] >>
     rename1 `Builtin _ bi _` >> Cases_on `bi` >> gvs[]) >>
  irule alloc_run_compile_builtin_dispatch_body_var_membership >>
  simp[] >> qexists `internal` >> simp[]
QED
