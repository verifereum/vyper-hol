Theory bodyPtrStructLitOwnershipBuiltinBody
Ancestors bodyPtrStructLitOwnershipBinary bodyPtrStructLitOwnershipScalarCases
  bodyPtrStructLitOwnershipNumericCases bodyPtrStructLitOwnershipEnvironmentCases
  bodyPtrStructLitOwnershipAccount bodyPtrStructLitOwnershipHashingCases
  bodyPtrStructLitOwnershipCalldataSliceCases bodyPtrStructLitOwnershipECCases
  bodyPtrStructLitOwnershipConcatCases bodyPtrStructLitOwnershipSliceCases
  bodyPtrStructLitOwnershipUint2strCase bodyPtrStructLitOwnershipWei
  bodyPtrStructLitOwnershipMethodId bodyPtrStructLitOwnershipConstructors
  loweringShapeDefs loweringShapeProps exprLowering supportedExprTraverse list

Theorem alloc_run_compile_builtin_dispatch_body_cases:
  builtin_arity bi <= LENGTH args /\
  (!e t. MEM e args ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce) (cfn ce t e) (\v s. T)) /\
  (!av a b elems e t.
    HD (TL args) = Builtin av (MakeArray a b) elems /\ MEM e elems ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce) (cfn ce t e) (\v s. T)) /\
  (is_extcode (HD args) ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce ty (extcode_addr_expr (HD args))) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce ty (extcode_addr_expr (HD args))) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch_body cfn ce rt ty bi args) (\v s. T)
Proof
  strip_tac >> Cases_on `bi` >> fs[builtin_arity_def]
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_len) >> simp[])
  >- irule alloc_run_builtin_calldata_len
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_calldata_slice) >> simp[])
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_unary_scalar) >> simp[])
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_unary_scalar) >> simp[])
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_numeric_unary) >> simp[])
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_hashing) >> simp[])
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_hashing) >> simp[])
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_as_wei_value) >> simp[])
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_concat) >> simp[])
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_slice) >> simp[])
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_compile_builtin_dispatch_body_uint2str) >>
      `MEM (HD args) args` by (Cases_on `args` >> gvs[]) >> metis_tac[])
  >- (irule alloc_run_builtin_make_array >> simp[])
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_numeric_unary) >> simp[])
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_numeric_unary) >> simp[])
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_numeric_ternary) >> simp[])
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_numeric_ternary) >> simp[])
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_binop) >> simp[] >> metis_tac[])
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_numeric_unary) >> simp[])
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_numeric_unary) >> simp[])
  >- irule alloc_run_builtin_env
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_acc) >> simp[])
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_method_id) >> simp[])
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_ec) >> simp[])
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_ec) >> simp[])
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_ec) >> simp[])
  >> (irule (Q.INST [`internal` |-> `F`] alloc_run_builtin_numeric_binary) >> simp[])
QED
