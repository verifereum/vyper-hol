Theory bodyPtrStructLitOwnershipAbiType
Ancestors bodyPtrStructLitOwnershipAbiWrappers bodyPtrStructLitOwnershipAbiStatic
  bodyPtrStructLitOwnershipMultiExprs bodyPtrStructLitOwnershipStructFrame
  bodyPtrStructLitOwnershipSliceCases
  bodyPtrStructLitOwnershipInterfaces bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps bodyPtrStructLitOwnershipPrimitives
  loweringShapeDefs loweringShapeProps loweringShapeRules exprLowering context compileEnv

Theorem alloc_run_type_builtin_decode:
  (!e t. MEM e args ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) /\
  1 <= LENGTH args ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_type_builtin_dispatch_body cfn ce vt ty (AbiDecode unwrap) rt args)
    (\v s. T)
Proof
  strip_tac >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_type_builtin_dispatch_body_def, GSYM comp_bind_def] >>
  simp[SF ETA_ss] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ value_shape_ok s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_struct_child_frame >>
      qexistsl [`internal`, `ce`, `\s. T`] >> simp[shape_stable_def] >>
      first_x_assum irule >> Cases_on `args` >> gvs[]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_unwrap_value_frame >>
      qexists `\s. cenv_shape_ok s ce` >> simp[cenv_shape_ok_stable]) >>
  gen_tac >> simp[] >> ho_match_mp_tac alloc_run_as_ptr_tail >>
  simp[SF ETA_ss] >> irule alloc_run_conseq >>
  irule_at Any (SRULE [SF ETA_ss] alloc_run_lower_abi_decode) >> simp[]
QED

Theorem alloc_run_lower_abi_encode_ptr:
  alloc_run fresh_outputs
    (\s. as_ptr_val vt LocMemory (lower_abi_encode ensure mid src info maxlen s))
    (\v s. fresh_outputs s)
Proof
  mp_tac alloc_run_lower_abi_encode >>
  simp[alloc_run_def, oneline as_ptr_val_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >> simp[]
QED

Theorem alloc_run_type_builtin_encode:
  (!e t. MEM e args ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_type_builtin_dispatch_body cfn ce vt ty (AbiEncode ensure mid) rt args)
    (\v s. T)
Proof
  strip_tac >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_type_builtin_dispatch_body_def, GSYM comp_bind_def] >>
  Cases_on `LENGTH args = 1 /\ ~ensure` >> simp[]
  >- (Cases_on `is_word_type (expr_type (HD args))` >> simp[]
      >- suspend "word" >> suspend "located") >>
  suspend "tuple"
QED
Resume alloc_run_type_builtin_encode[word]:
  simp[SF ETA_ss] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def] >>
      first_x_assum irule >> Cases_on `args` >> gvs[]) >>
  gen_tac >> simp[] >> irule alloc_run_conseq >>
  qexistsl [`fresh_outputs`, `\v s. fresh_outputs s`] >>
  simp[shape_state_def, shape_base_fresh_outputs] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_lower_abi_encode_ptr]
QED
Resume alloc_run_type_builtin_encode[located]:
  simp[SF ETA_ss] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ value_shape_ok s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_struct_child_frame >>
      qexistsl [`internal`, `ce`, `\s. T`] >> simp[shape_stable_def] >>
      first_x_assum irule >> Cases_on `args` >> gvs[]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_unwrap_value_frame >>
      qexists `\s. cenv_shape_ok s ce` >> simp[cenv_shape_ok_stable]) >>
  gen_tac >> simp[] >> ho_match_mp_tac alloc_run_as_ptr_tail >>
  simp[SF ETA_ss] >> irule alloc_run_conseq >>
  irule_at Any (SRULE [SF ETA_ss] alloc_run_lower_abi_encode) >> simp[]
QED
Resume alloc_run_type_builtin_encode[tuple]:
  simp[SF ETA_ss] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_compile_multi_exprs_frame >>
      qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def] >>
      rpt strip_tac >> first_x_assum irule >> simp[]) >>
  gen_tac >> simp[] >> irule alloc_run_conseq >>
  qexistsl [`fresh_outputs`, `\v s. fresh_outputs s`] >>
  simp[shape_state_def, shape_base_fresh_outputs] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_compile_store_abi_tuple] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_lower_abi_encode_ptr]
QED
Finalise alloc_run_type_builtin_encode
