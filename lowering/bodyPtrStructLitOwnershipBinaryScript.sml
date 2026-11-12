Theory bodyPtrStructLitOwnershipBinary
Ancestors bodyPtrStructLitOwnershipScalarCases bodyPtrStructLitOwnershipBytesCompare
  bodyPtrStructLitOwnershipMembershipDispatch

Theorem alloc_run_builtin_binop:
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
  Cases_on `(op = In \/ op = NotIn) /\ is_ArrayT (expr_type (HD (TL args)))`
  >- (irule alloc_run_builtin_array_membership >>
      simp[] >> qexists `internal` >> simp[]) >>
  Cases_on `is_bytestring_type (expr_type (HD args)) /\ (op = Eq \/ op = NotEq)`
  >- (irule alloc_run_builtin_bytestring_compare >>
      simp[] >> qexists `internal` >> simp[]) >>
  irule alloc_run_builtin_binop_scalar >>
  simp[] >> reverse conj_tac >- gvs[] >>
  qexists `internal` >> simp[]
QED
